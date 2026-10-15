-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3989
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:15:10.115806+00:00
-- url     : https://prove2.me/submissions/285fb9e2-1051-47f3-8fdc-466d547d689e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 717266187 ≤ n < 717446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 717267437 1250 717266187 717266191
    0x70b031305070f09020c0c01033309051003061406060a031a100f18080717031603031d0106030c060509060403060504060501031a06010e06030603010e010507020607030c05091e010c0b 80
    0x909194041b6489690a00400406441301e42c04e080800c4840481512645c004540e5913044100c0b80c20101964001c000007004e01000b81800c90b003c110a0601c00e0280390b00050510003900c6940c201490b0000c50500e0024007409050010002807400c0000ea00a2b0042c1c0754400c040b000020200c2c03005883c607258064240c11300900c0340c3e20403443c103200c440050702d000242d4010780c880c070a049000317020001b0005101410364a441c06501d09000440c078117245580b05a00b50100300c90788201840c42056016040704d0703040c2d0380c0c9400046074040e00e43d420508136001c91001908800c4541c108000b52801703a0700400c490300b000b80401e46429101e0b2a10400c5da1403c0e20129145584c0354010401d210114483e41e07203410b09401103009500340000024026440500c07030521503c8000041521a6000d5020f1032200c84440000e10030707032800c9000a5120801183c100004c281444401c101c8944680c0440c1c10040005000c0d566090a030f02c2c050624003100c0c1c40e81c03410b01084a8014000c00c65514200d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 717268687 1250 717267437 717267449
    0x90d0618050709060801021801110a06060f03021e180c0c0a11040e1504030e0604091b020c010e0a03080c010e0304081c0e0d0308041506060302090909070b031305070f 73
    0x1002d6480c22251a00f103031000d603c80c1030310780d205000000c900d040030002565881000d103007400d0229160b55040b41055590306000f000b59290050003d40f00324440d95050859000300d80c0d4821030b0b072902002c40c2000c0101401d0399840f80030710054001000240c0d0707886402802d80c052843c1052034070f40c3c1007840d004200200340c0d0003000b65541044580351074003510030102042c101900302c0b0640401345034850701d001f03003000307040c45142c8004a1940d254032065400034940d10005001c0740031940541002d0884401804005008030950a036403035000e1150004141c0014204001162441c0c440301400d402400c1020303515500e80010300d98680042010f8000780025002030814280c102412401c855120300b03243d028000c07907a62410041e41c888605042c1c8540505044500342d071907242c010340004011091092044c5011404a10183e2642c040c0490340c1d025981b1107840d4585c0e030308040e0f0350707641c0d4824149031210400010701d201e4202c16080343e01e203120320300712039145841d02661035000e00660000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 717269937 1250 717268687 717268693
    0x2030c19030605120105060301110405091602211306030e0a021516052503030f1215061205010e06030a0f050c0301050411040515010807051b122d090d061805 69
    0x20164508d42031103401072118000c40b4541c5450710300030100b20580c400804981c41022034288500c46a402030000840441c00751000070031b52010403882d803032150000b1074180000e50b01510f000c1051400f0348100302d0ba2100c8900145203007400c60342000301e001440c500300881d4480902801210040c007034a040390307581c1304201804081c202412a08540b6801d044c3c0180880c034507040420100c2d0b08034050031007603045407400100501c00050418047d21036035500d0580010580f00c00178045070300200c80724030300f0b841003401e0010766078803440505143c03c1654440e926401480f00040000c02d8a508500a00d00c60307000e031460f1861110001c0d003112412036060700c240c8811001580e49203440e01c501c0394421108580c071304000104900081c00c680c4006c000701c0034070800107032001501b400e0900c80802c0c044110119881020340140190042d001400c102e43d81100c440e0541a4032400c080e603a000548168940c50704101da00c00070050f5a41c0d03400400e07100350399203d41c2400e03010808503200c2c51050090b802 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 717271187 1250 717269937 717269941
    0x1270f020c07030b0901141605211611030406051c15181811031f061a0a0806040b0d050307030c0b060109050f090a021303061505010302030c19030605120105 69
    0x11004c80b03000c00814584080c1d151401040c002010a00516040b41e245048020a04e4156000b40c8040c402e25028014244880300a902d550346548180f5200b07d12846d080d2000c80c80361101501e4130740203511030450a80040c042449100c0c800c0d4060188d032104039041d80049248c488030202140c040400d842649418002e00344150f984a40c0e00d0f94000700a62400c00c0052202a44c1c40340c1c404005c80e008042c004901e0f0b00039002e607010013400e0265110040078081c901d00c400e584000030501481034022103450010749404003130440301075802000c8192147c110954801003008020300c0b040943c1544003009003003240120707404201804400f0300c261601c0c4042c1c0c85c0e6042c2490a168000c00c40c504100c1c0218041c4103c1d103500a51850303558042c1e6281c011303603c0c0e11369010060701075092081c01d042070080000044c09500d42103104030201c42180d4610b0180ca540045041e0301c07040b20080742290b030801c0710807070400d8a00c00bc174000e90807500d00007454540340c0c00056522041109000840c1c2e4503081 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 717272437 1250 717271187 717271193
    0x816030204050a080607020c1f0c02220b03070905040c0b090102120a022104080a0303050a021612090603052401020c060315040b0f031c02070e0c030103060b030601270f020c0703 78
    0x461501c0748c250494a18074846164102d0101c0e00d0750010500707042045032071000301152100494465071003241910400681c2d50b45100780000d01403a000307103201e84507040001440c0780480c41158044c6401a504141c2c050500c108802554011240300381103224205140c442030409c0300140c01c11030f2680c2d018000418080c44581e42c0400207075031b60301640104000801084100052041d5001d60508003c80ca0782d64000301c01c0020b000b80011140c0320700c0700304031840c1044084406051841e06a44800307001c55291803086045501c103e441001304102541d9500500c2d40b13002c00210035440510489241801460100d0000e8200340e84504c0c0032416280e070a101884c040c000c0791001002031350008c2c0100c0c0e4a6001a545600301641c400c1070b56402080130390664401e20201d00a40320b00d1406050317908001800d002e050b8800d21041d10700b14904075125240349004034019048074000044200074100715556044184104c14007580c07010307076403d03d04040072910b00141407151100009803000c43d103581 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 717273687 1250 717272437 717272443
    0x180b1305130b01081501050c0f060108060a02131206090c060e01020c06071505040f0605010e1e0424150b0424080a0906060e040b04140a02010816030204050a08060702 73
    0x1030724400395401c0c020400c1036641d10a11255200c25a081e9803000d101000d001070303806120300d119006150160907160032281c0b0740003484074100d8416400f120300300d03030302c015041d8200e01856548400002c0115020045100400019020a4014080050148065510100805000e512440100c1e100b60900043c56070140300b003107030100040e9200343c80c0000030307941c081e4000e03403ca1050030b82d1ba82d54004103042c00040391141c0111380d4800f400700190350310350071078035058401165140500055101c400c907246842c00c031540e020316032210081c02100320010240502074001984074014554550740c500244c00008031502c014002c0240d101e60f22401c0c00c003104807800550102800d032485501903000b0300c9d81d0003189190b000132580700c00a101103903868040050f0510303912014001c480d020031702040c00320004e122350089103d6845840142e07a0b00755920b40f281d10004000e800f0501540010f00512880030781203000154034600146000d03142c0000071010001900052440e40c0704100b00600d5a07010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 717274937 1250 717273687 717273709
    0x30b0907030605034b0a110411070f030e0310140402030607030e10090f0b070314060108010501020a03050306041104060206090111160303020a230711120d180b1305 72
    0x71400e1520004407040300174502c3d03050340040d0000140041d02085584580802002104d0498000c0e03c41c3c90140307090243c9001c0500a82a1165203028001c1003070260310303000c4600c46a4040e503108060b940a4400780c400c4aa0940305a426000d414003080d800b844510511350605030f0240b042070103040a00501d481c11000501c80d8060614000d040384800c6030001d1175141c009401c20001c80d0200c12850318800101c025000144044c6000080c443e80b581c244d004008000c01000b40708501c4e954076001118030300d00a10a50703004d600016018000b1902c5203000755481300b005071012543d4011030307034004400c1d40241c5c840c20040e0000700074044030140c00e0007940d6a161031407610700d0500c1c860242040401c2d81512005041c0f43e4002481038107180540c40c1c82c04682804517200702d4114180c0c01c0f1403415404151f040342d00b8170b04455222034525140074a151685d0034039006110050031907406440791104408040320b0700f00d903e440002c8450400000f030a840554404828800b480d1038140302e100b2943d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 717276187 1250 717274937 717274963
    0x2130923060a0f050607081312110103050c0301060e0f030a03020307120206040b010626070f0e0a1802030705070b0406060e0105030c03060a02160203070905101712070201030b090703060503 83
    0x50301044a4010500d880c0c05907541113030606d690f1039240c03604582600c1062042081500c1758000007484012040405040d140519580042940000300450444004650258070315109000602c0100d02c00e410b40350041c000a050054105000400070340f51444000c0114010781c40040c0307440410151700b011102d40c0c4102d0005052506056881c0151003105020380c008101c41d1144900c045035010781c20b003806205c20024826075083c41c1000070411515407132000d01103141c0104400141c00e10403008411240401000e0079a85140c10b5010041c3d03001810400407c001071201d540800c048600d03050040340709a10001e0403914103030f40600340040591105200383c0000342500121303103000c00d4281d0b0100b254000123a91700d060b01021901c8090402d00030303406124240d0301059004103580030760f004034402009034514594035221010800b122864040803504450800d80807050036001a242441c0705050205080c1c3d01e80d40403e50b1a64125840030000e5103480c0d00300700504080c041c4140d0303881 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 717277437 1250 717276187 717276199
    0x3082214070f050a12020f040b0d0c0f150c06020f04030b0a0b27270a0503070b01090509070e0601030906020d0507031a03280c0b030702010c0c020907030213092306 72
    0xc0f4021014031110070811000c3d01981244414107c00c0eaa6580600c1d040031008054420750316180c101601c00c0d0310b0b6409181080c21400c82c1c00708800c00702002441d00705509656212a0410659485005c0e4000840c2c0b02944001480f01100082c0249042032081000c21400034140803800e00708601c4541b007030303401d5607844101c00081c005095428140e40c1e0145060b00515588c69641d07102807046ea9001d00c90180b640a04001d01c810028080f00814805d40110003095290742ca0b024a14221030b4141d8031046d0366804100100412000e100d14640e110354141000108000700d9101c1d02c00380e80c0001c001100380c96a400405c6051034240c490071040d1815800313140d00800c2021b0100c3c4d40e40c102c2c200244030f1511983e0044411401e0103908044203580081d0820b011a80d85e54905c00301c0c1c00c00d441e014099400e2010301916944109444800c06400030164585a11502429002540001c001403210101d444020541981d1030240b020b601010542c0309140f080e0400b50320402c450042c007032500c104c0b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 717278687 1250 717277437 717277439
    0x80a0f050c1b0f010c02010f1d0a12020f03040906210209011a0903030a05070309061e03180501090c1818062703020703030807020a03082214070f050a 66
    0x29151400d40c0c0c24040807610b08041d40410006a41c41c1484000c07003141e9a41c2040080d01d810fa606411504044185e018244031404068103e0041c04c8062105100e0540c0714401000110380b81d171440d000d01502ca07005894541c00c00000722030841c5e029808c1101d0311610b544003080018480114098102c01ca054003500050850740007580340794040c400c0c403001100f0ba501035605042a101160400e80009045a5031a2020140a000b80e00301043c154041a06d1036400242240103804600c81240c0e00c600f1900104068801580149181e61151082135001041d075000104c0c24460099401c0c0107c520b03030b1041c0d140000f295400142c1000b0303401d81901b480ba4212400c807080461403150355100c840820119902002c1002c4181c0403683c0500003224500304009041e0040340c144290b0703010395a00d1066550f590000da0340c4011a140084c00201c040740001d4110020380002c0c03641072145148100d803e801d9489004c0c01c43d0103901104140d07007001c10200f007000c10034141d14004140c04d4840c48526 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 717279937 1250 717278687 717278701
    0x108010b0c0a031d0301090c05040b0306010b091c1505010e0702071404051506070c090f111902030c010c0908100618050c0f0a0c020103050901051017030712080a0f05 73
    0x412090b00024180135a2200703903000b0404c0040b8076006240082d00802000c602e608058569000d24820140100d00c4d002c4040014140402e10f54180c460b141c50b23203490700400d0303014014210031240c80d01000104032409440044c12040c1d41100090302d060300840c0550401c00345142165010f030524095500143c8204100070910890802588040b03500003071950390105040c410721410700c2002e5004000040310310420880c0521102681c1c4081800c00c0500c1500202c03800310f580400c040039a52406000d50300191500b0040d01c80a4002c0e48141e03402c1408003e142800d55003401c407403401160801ca0280845181001155142c050061081c850b903450440c2504042e0050700140e45445c0c1c94400003485403003031008850075102102e13002e655070907480ea0003c2c001d443c4603004a0001f0b0a0401140c1c05220500030240030b070294020b00c0d05110326004030130b40c01680b45083d005150205208100124160403c4614070a0307050b00c40c1c52040c0b401d0b036581000c60b80c0f82c18102c50428139007024000b003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 717281187 1250 717279937 717279943
    0xd0f050109150c270b28050a110c010509060c070504020c0708010b0d080a080c04030c030602030f0f010e01290301090c02101e05070507020409030e040e010b1311190e0108010b0c 78
    0x3205da0044a080d81e40c215410f83d035003140b468610807440801c90b040704e1080f80c1e611600814030070030140d8071700c0064074103141d5207911180d00c01c0030140014800e00c41031105180c0305005050b484144400c44842507520000b040607038000991075901600180c00c05c2200c460280200d25181c2c5040b0383c0c0c51016503c96580c3c80c914003e1502d0a002c000b1080d0000f50b04401030030445002c1c580180306811034a07940d1415070080d40c421217800c041100780f00c0105000d0300740544283c2c107030b502c108218843d0b0781c20f054490320f07034502d60006001c6611941d035850710348052210045001c3c1c07801035000b00d9013400b11b10010340380890141c620f084991605003840940d160304840080d141fa10490040b441d5255010300b203410b030090090103507100789402c840d003003003540110450040a60540d0207009484034094118200d900d80039215401600f4078460f2a2051381c1a030000d084490a0b503500e47c00c04012160328410000107003d120701080403100c40301d64a6800074040740c0101100381800b0301e000010904552 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 717282437 1250 717281187 717281189
    0x4150c020319050903070305060a1508061b030601020304090501080706090506130320100906080c040b090402030402010908120d05060a0321210b040b0d020d0f050109150c27 76
    0x10040080744e072002c2d030350741402100003c0d9085012103031141806140c02009011111001450401280c00083c02031070204101d1301c110f4249000344105110140644913950000384054118041008046003001040c400da9018010b0701c0f000301100d03420140b0241c81c503185c5401c40f81c070445e020300445072031082c1070b6803003c107403030f44208000705c1d0011110a04650b402c01c1414141e2041d00800c0002c87c0c80d42c040032440881b01c1d29a9032010648480c001c1100c3c03403146001d0b08000600400404503541081c1c0c0096800ca84107140050002c0e584407000b504100308901007074051000050705001c03003c143e01801e6004042194070080e01861071b40d582201c020b59410114000e403448001400b445d0140c20080440d115680c1d650f0f00b100000300b6840028466a620701d44564500609503c0070f091800d074041410b58060100c10119506844512030403614040881365503407200c1c5c075040040c201400e4048040540740010454070160107010300502c03403541107410600d40c84600080d840511401100c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 717283687 1250 717282437 717282487
    0x13170106090525140a02030702313603080105040522020d020301180309080d02060f1005060d140f1506090406030c0f0e070e1f0309020904150c0203 65
    0x82c01c46010a016107100307020100e40c6550100c082170500051381c0100041c060144202e0f541c0d201503610003030900c840b504103c01801d00c1c8a208000c0310300e010059212000716070107050041100700e0211104a0410644501e10001d4805000003104164111074011701512080310b00f8840da203440c1c0903006034211004284e00042040e215484155118592000d40c07294014009001107008212071002404d0080003c03400507880241c00101003c01081c22034444070300e58080c1141f51207810075907000b100042d0002103000d00703801c000503245c0d03038507402810844882030010814614940307803401d440100802490523450300108108501510903101c5072039110864603551260620b0021400904060f080104008030b43d80021075143d4006014034200ca50902c0c3e0682c49594a40007200e0b040120540e69400041c20030201e941116a9400303640c050b1068030340002d2800f156000640c2000d800da40a443c07296491a103202d802c01c007801074a0782c0850700c3c0000c1d40341003a90750301c058441e540f81042e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 717284937 1250 717283687 717283741
    0xf1903031218080f09040e0d090b0f030610050409090318080a020109060f030f0f050a0b0604270f141b0702060301050f0f090f090c0a0524131701060905 67
    0x8107644200c8240c455510005d0010411200490b0130a50707032309403000070344c4086a1070207000901c01c81074904841e00b850100716a9400c42c0c0382c038070903c02c40f900e8007030522051040620000c508620944194482d00780280c0d2028510318000c40580c00c1551690042c60081c0c101940003030151b42c02441640482d0450b01d0b000780d0020040c001100103044804510410310f04191682c9811002c54001d14013940c142c60303040101101400401c20544141d101d00319016406140300c4c02d00d00a00583e0460500c80c2d010089203090140940508a031700280c9844003502d800018080c5640907000196904010380c80e01601e403813065000100c00e8001449400c1c41607120509024982d2162181c1107a0400050400021801c0c041108c0403500000c5410100301d12074401c0451701880c0c610304080031160080c10442c0ba811880412180380c0d080c424454105090030440b07540000280b0301030200801018200e10420012600c0c128292103140d804126200c1c20801400409006051600c031300070541509 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 717286187 1250 717284937 717284947
    0x180d080907330315030605280903020c09091009022809110406090306020304230f1c200f010c03050a0b0108010317090f190303121808 59
    0xc524503129281d00509051103940000302910a2500410640c0c00d0311601c4444600c105001c0881c11101c580c1032810078000f900000304003140b481c1c0d0010781c002044996800d4190290012004050301029490248aa407184e0302014140e0500610811200403514446142002201e00795102440305416072140d541d00710500856441403800041c03c0b241d91305c902007000c0c480c4024564074145200d18620796003000384040000340d44c04211019908581c444035556800d68541c81c0094000600c102c1c1c00c4420140c544c04018040b0184d8606180f10000038030b130038200746650a04082941c2420303042c01c0c9921440c81c6101c0c0c0c218044045110b85082444452424072404928148110040d2016946001c8220000b558103030860b034880c0350f105006104804d120b000450f201e81c024407001d0300c102000d140c44a19200da039401414280c100425100d020401c620001c0d89040d01c0c407100390b49440c4502d1041040541150724015001c1581c0c900f0440243d54020100c00c1680f00c1c0c50041802c403001031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 717287437 1250 717286187 717286201
    0x90c010923031b03210a0c060b1e270f060607080310090b01020a05120c01020403060501090f0c0804210338041a04020906091c030305180d08 62
    0x6034030000c0c5030060442d0002402c00c3c40c140c0481e254800d20794064050007003805111a1844950955803050490b107601d80303807a10408071410b841488045800035140c810010882c0c2d6851000312040f81d19110b040c05c1c2030a04420850a4649042e0860260a0300146040781481c4040230903030103845151a18000d0781e0f01d00c0054410b219542c0300170000140442800060a07508058200703075040140c042040766404801641e030364030303145001845c42e401000c43d0590721908178050415213203000300242c1099103a0342d400060301c0e0260014124240e8442076485024001d001d408c3c80d4900c642001c8540341072a4454a107140d103602000b513a80c0d12520180e5415500c241d200303401c3d90300d4a041d2050b1000b894206a8001500c0b440510198551a80140d49525003446001a88848059680b43c580c11040510010b90417032609141d218003b0f011b0b2004c292a24a94801c00c600b140450f4521091180340c0942143c034084d040402040746110540c181c80b000250390620b1521609218140c0d54440c6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 717288687 1250 717287437 717287489
    0x2280b06010c051e12270319060203040c0f061403090709230a052205030c010c180b0403080a0e04090510060e0f04031b15020412020108090c0109 64
    0x5500900704c0c8650503103101082d1440701004107600c0100c0c265203d140003024040c0740f502400001c14001078100303d1000082c080c003509a000802e010341070b140d40b44c0c140b225450714201c41c80000d5421540001c101300401c030211a64030060074110300c010000340d0410030000c0400b852075800c440308520000100d002d420b000c112400c01842541c00604c20010702d503c0a202d10010079400e074422000c000003240c4d0f80c0203a4040c1910606031109007030782d03402007a9000741d4022064401503e003030000f0861607000c106c0c21300460201014984813400c0c08442d0407a06203000c0c1440e881040500c100388010300c0007400d10800c580405800f4a0203c0c10100048001002045100c0c4000c3c0140f080022083d402c9500d50004800c075104414131049660301c8070460031004004841c010001911900440d03000904038510801c07803405100026174914500b07041c40304030307403143c1c008401c0c50307541c074082d00f08660b071144140707500200340c81c090410000140000b81920005024040d450044070b000d8030f038054449 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 717289937 1250 717288687 717288707
    0x302040218090703053d080c03070e090601090905010b132405100c0c0803071104110a0903080a020c06030a0b0f0d0b01090213050d050106050102280b0601 68
    0x90045694400101820202a1410721401c0c061803508001420041c0070707105451045940c070040c0601c07081c8580d555002c01252600c80c0130110407003141e2a082c0300c01c8440d8480a85000001801d000005400701031400000d5441090b4618850b42040708401c000300d0f00b681141c0d0071070004151180725203083c60142c40004002034005141c080190201d09441d0003c5d007070700c00c0e00c0811250141c001c417100d880d5241c2c1802000d802c40000f280d1000054441c50346013035600e004090300788185455102042c05c6a0100d401074038a0000403103120759524041c454010b01120a13104545440b40d2032102030141402c80c4030142400b0000b1941002c2d4500a105404402030014049a524500000701c0002400b08603402401000104851405030401c4c030602641c0e00e4101c0142e4100d07078a820200000707540b2415180a241049040000d415200d00d04a0320805103c0e030008a1303124206800245041d5550301d031090409041d4003940c0c0100b8040004110035278000030101025521000107960510740 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 717291187 1250 717289937 717289939
    0x1050d140901050f060301180b0604060f0308040f0e0f160509100915032a090302060412030e060a090302010e0d08040e10050d0201050307110a080309331603060302 72
    0x240c00400c0400e01040d031180d40300f045402e01001c0d0355110700c82414200c40058814080e00c81c0c3c80140040826070900450b540310348001e0002c205151226101c0d07400c110260301c200d48040c0007140c14000c10031181e020034060482d00701103030b54a00d010a019404424041c10f11682d5484041c41450254411000c60703038140005080d900882d444998020309808d06441004030600008c1c1500140324800e0041c1049914a18100610050501c0c0d4070011801022125018000c03a01000001a03e4180c040c000620309d00c0080103183c4814100580028181403a00d2301c184c904201d200720700c603002030641c0141c0e5020b207031540314904240042500348240680c060709180003c03c2c00240600044100c23842480c07680c034088141d65440043c01490350780b20380000c0c049103040c400503480c28403482c00e19040c40c0803076085a101c20f480d51a03240e05030b807003540c2146036500b0410b1109a80f00d01c40008130b0441c3e440342d161841281441c2d8024100140c0902101d00c1d4241d04c1c074002130340ea07203e50018005550 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 717292437 1250 717291187 717291221
    0x105091807081e010912180801051501020f06010608070339020d0c0c050405090a0609060c0e010809070312050d0606080406050718030204050703020705100b21030901050d 75
    0x1848205403565818100303005000c1c50101e0f20001c11102040c02810704140d0f0245200c141c1003030055040d40c02c4d1900704c4000345002c800640015039100c00b405414080d00900401501000342c0d8000213042040440c1181d0b2568032034001088821b6000704d10350350020851400003a82040080021203c1e01c500550f030b11000544400040d030340310070001138940e04510ba000c8942503d031290f015110900d80b03c80c050003841800308200080c1c1080d8100c9940304104c01d00395007180c0c2c4035545034412150504010341c0c1241c0c0c0c4070b4080036081c0e00f001c030010905500342012015498003010099480d0714a0000070306070001d034100b40444a004105840c58800c40a50505c02a901c03444010f00d000c00880303017520040e0a01c004600c032076002e1210b500803100d1001c4d1490f503860541d024003014003000b07040f8208040c0d013045040045a0203000100081c1c240700f0010980e160108104040c41900c0c580e90040010f079000d05140000c000003c075404110b01f030803c0c13515403207a45c03880c0000702200840880110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 717293687 1250 717292437 717292439
    0x1050c010e030901030e161202010905060a0914121b03010603020303030a09060c0507080a080702071d0a0b1009270501080309032a130914030c0609150105091807 71
    0x51010024103c902d900380d908101c040300404106030b945080072650440d0701410007042c4803283c1000c001c03040c014010f042440740031b80d036040845e5035a4000301603200050303901e400c05d1104003122060406c200d541100c866201070705c80d400c0c164a80f103564000b0000452074a032007002e1510207420913802150000e096903201e00e8a181c490023b0f0291901c00c552103407818010000d55400390054510701c41d005540f041c04c08140380001d8540c0f620180140096215441c000100c80054940c94a0010718884844c000ca06000005805030b070960300d000c6100700501245610407030351118100084800740301a40c10900d034112503401000700c10074086030000c1c1c00c080c0003082c0b900d400401807042c03580607011505102c03210300040c00b51406030b501400940b11150514102454410480703070a00b144000000f80c04150390303842c80c419681500d41c0d07400d607400c089221940700000340110780e4081441e40c041d01b8030f41040b034503e4041c0c400500a0791303c20780c850300124000442103481c1000c00103041e412101d83c0c0e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 717294937 1250 717293687 717293711
    0x106030609030f2d050307090503031c0605030304050f060a030e010527060106050a050c03041706070206010e01030f1e051b131104050f0d05011107060609180b0601050c01 75
    0x2102220800080751104104d03503118503041d00c1a050a042509030840341000580d001c42e51a44083c103d0801c02c8504000845d0950701400100700c407400c102c109171040031288904000780d4481e42d0215100b50402d201c208400c2d1503104507004c4169044803000d540d95820041500181a0051034001941c680320030030040c50154000302d40240c8020250f0180d000780070300c12030f0f0b81e99001d0003001d00054040c020041858000c5005c4d2801c1c0748001c00752400e29444a8003160344015407030050040c1d50102051000d403d03010700450340909001e10039215150b06688481002160991000382000010002c2490308084111850a41c981c0003050302c41c04031a18070442c2c550440000b820b845042c550038050383c141581d1090411042c0e070140d403036041510701020090389052000c01c05412550400ac00d03400100284a4450140701d0800c03003580750169810044100e82c00340e04542c0b0740e5407401c05403040322403580c5403240a542d80856103020325500c07400100c1c0c135030003407020022040d800c040c4002c1003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 717296187 1250 717294937 717294947
    0xb0102030d0603031808030316050903010617010204060809060103031d0607140c01030b041521080d0606080610080f1017011b08240a1d0a06090b031905010603060903 73
    0x4607201c44007105ca49984900a581c0c492005641d4404946041c13000307404494051000341469540c0280002485940d4880710819102504514a8240d6000405021580d00220150740140030900241115070456030017411a49400d40050010000000240e4443e40c4000c122210b00364040100811003100d00d80d4107a8a01e41c454003140801d00b007000450f29802c151042c824526980c40422010328a00307640000c2e0031454084602617030254084038004294900c0042c003c1c0101d14200044081c07502200606c00740d80500072a215807180030203001103e61058401e80c111502c102401c150b6118910104a17a036070940c0144c004ac59002281c4034084819801001d61082101c0843c1c0c1521024000b182c881e2000c480c444209180c59803c0d01030744643c00000540c2d007801500c503403074003900c2d0b01d5109803100e4045004003a83c00828108404071401d0b00404005080b13142c014403055010f80e000030f03143d2070203da151b02d8508560380104280142500548001e50700320b04101f00400c254180185 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 717297437 1250 717296187 717296207
    0x4150f1a0f0d020c0f0615090c04051906090503030f030106031a13020a0905090105061e090d0606030210080c1e040306060f03170301082a03010e03092d040b0102030d060303 76
    0x40078000c01c105c610300b085010070401c1c403c18003820107c088484240c01c0101000b00a000030300f02400511010800307880e501e000b207000c40c10b00d210002c0745510f03000d801000b08459030412806070f00103100c81c0340d42050702d9060302e064500c2c2e8100880ca00c02c02005010802d44090411540119500c1e5001161090382d03004050100340c0e5a0360303450143d100c805224052800788a42500204100002e80003031004001c044922030180a2191400c06110000780355070346080b40980b40159035a10030005c5141c4284109445070a9051811551906010007003142c0203a181c0400903d07050b06040e210200890304540103198020401c00142c0d40f0358032155503400c5940002c0b82c10007044541c1c42d40c185001c4098904880c0820010310a00788a4048a14000c0030000240c032044184800c0c036400755005c0c000d1340c85552003030004586a500b402c08009400016110440c04108000080306518107842c1201e15511425075010402c001c010004034950712901c80070041032032400174040101980218240 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 717298687 1250 717297437 717297457
    0x6041e02090703051e0402031213090615031b02060708060f030304030602030708061207120c032f012f0a140a0309060807020c0f060d02070803040204150f1a0f0d02 72
    0xe1410300341041c084045c01002d540295040c1d0110002074a440c01c810020702041c205014103401c0b0a94403840602501d0280d00900030070103101d0069031200364584552040f128400c0306001c1c84401c4414040e46442000e46080200003100d030005003184c0750741c0071445500c2d00182c00c80395510380d203080102c0207401c2580c0307000c00182100b0108855103401840e10065045403c050702c6101d00e00150103108140c203a02c00c980036441d10400001092a8492044c044070000d22200070f585018041d21400e0485d50300040d052000c801000f101c0c601d403042224418440d412142c40c0705440854589103840703000e0358003e0070030003080c01c0c808244501081c5400150300ca034540d02c01c259150f85082c3c41031001100c0e90001688011540a07181c580380c11485060f03030f00901131034078120207200380d070f0240e0b400ac4100743c6600300b002080c841141858424400c2c07a0152110700003c03035041100700c00703121400d40b081010703410160802c420395400c01400c030381170b1b003142a64451340c520b0244203000194020364021 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 717299937 1250 717298687 717298711
    0x2502070518090d0822030e041104120311010b0a060f0f02030301150c0c0302190513021305010c06140112050d02011109120a080a05042606041e0209070305 68
    0x400394195251907090140d00e07518058403c107030f60b001c1d00301d480d6100140204101848a100440140141103102031882e0082e07503140405007003142400306480e91500c00e22413105080004125002224480503405030303161520450f40441d44c5c10590260005154140d40321003840340000f191501304520b44030260740c175182c1181a242d4440b0070398880c0001d00c941e80000420000f00b8500a10601580c4980d03485181c10408041e20794021850300e0042c40d026801001280100b44150300d060a0300000c806c0301c414066107400f102d4541e9511001062203014107001e460b1550504020541d0081c5514a89144a1010341d6a41e000c00d03420b400051001079455000e0503c0100c1c4c00362041c0201d1200784e0903400f05514003c2d001c0280f25101c0030400b621f1041d4022040741000141c0e0313200c0100b040401e10340d180e0341c66906110800b81560b140c100c500d0200480c8000101c0030a501049450f031050308560140d8101402078129407008151580003544040b881c0b040000d1150980d01642c065079585070380e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 717301187 1250 717299937 717299959
    0x20a090803030903031b1903060f050303190c0c0e151203090a0302060f0c060108030d0c020d0c03080408040e1e1605040e180601031103010b04180b25020705 69
    0x255260702c000e803070541c655002080000c1b41c020741080d4064090200000c02071920f088102410b140312010b4030705000203503c401003000844650300c0104084c090413801380d440c100a0118a0700c9100b00d513034800c030034024040c143d001405a4014690020b0606603504a21450002d40c1c00d0700050902094510500004119000c05040002a140c03101400b4099820712400c5408001e015000361701c1100c0421410001c2042103032040c01114001c0007003600664646071401080420b45480c01300040455200f8041100b615901c030308030001c21601030500a040b501c8604199a241c0710b0f6400440e80003646009102c40d8a4142c000c45446031028107c5407036a1311404d40c84100c0b000c0c008801400074105010034000c2101400b415504201d180002c80c204038030444403607040503003d0340182c9001485d1900050b49050038041c20b215180210b504011002c1d01912040501c0e665940140c454500c080025410211a48001c104251400c85500082c83ca42400a55880d954001c041c00b030000681 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 717302437 1250 717301187 717301199
    0x150103051902060d09020f0301020d050906011e061805060c0c0103062c0604060e0405060f010902093001110711060708030c220f0905090d120b03070e0a020a09 70
    0x1540e06207168020100c6103031240f201410350240034401070513603000030b140303400700c010b5a000d1005080c85610704c4c001152601d0141603075070900c0720507400105414103000c1021428600c1040400945000b41000100707410b40791107403000200c2c1500150380200000901100b80703500086c071780080003c2680d0900c00303e604c41c240745a810740350100000303410340b50807403201007800d29035009984420b02810002b0310321340c1d45400d80090325040c0c906440d1a00414140841e803850034407424094006c0301419803400720180007003507440c0c609508405c82d41114240d0404a040b018404040001c20040207200300c078042d48280030300350301c0198200e0f015044c3c107585c21140d0400e071003035500d119080489a0300b10755035602100000d5204045081c2c2c204505030003009001b10114031100504005015003090b6070609880000716070300640b0100c2076500a401100c1c00a0348440400a036809004012030000030000c0828a440502d400110b503400396001006100b402c1c540c00380110498072340c1c4803002c2a036103403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 717303687 1250 717302437 717302473
    0x114131d060307080c0d02011209060b1804030906050d021b1b0f060f03190c0210050108012a0513090902181506090a093305011205060402070515010305 67
    0x4c46180980e42042c25000040c0ca4602c105d81400d40c018102060388141110b00d04044854041c401c540d840d545100700184c604041c450400301a048800c0f01440742881e4034080c10240e440e03c65001008000185081d0892054040e0303080c15040400c480071140380e0324070315629081c040040121607440703801400d045207060f000350074007910041e00403890300f074fc2100c02a0b0303503520060440c14605021350883c01501d1180c4a01d910031900e0b54082c0c00b4083c041c038045d009481c0c0603407011207140c0c10100f28400b81c9044070710211115240b100140e4840120513010382e5035024020101000f00071220b40003d82c0000d542000d049181301700e900c1400504180c6101c00302010603585032044d81e9212207142c41a04104006219503080104150880755a6410140641d041451350700242041c851600b01544c0c802501d010548409c003070110340503420b020000740b00001404640544c0740e211408a03425460f55412158129000070039600c1a0f4041000b40c09501c03c02e1204980c2d0340300740460410f13802c00d89 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 717304937 1250 717303687 717303689
    0xb06060708030a0f0605030a08070b0612060712060503010e06091006080a0303180b0a0e01060503010b100810030506041415010501050712200106030209011e050114131d060307 77
    0x580c0c507400c5441d07021241d0004c202c11030f0715030111552000c020680380d07010401d8242c80c91152840700d03550845450690711840016082c14050403100107110300901700490420303408820f0f8685148040110175160b4060310a66001c250994684070528045040115a051196100c60110f50f090129002c00000f180c801d480707200515004000b03d600040c0c07003900400e104058100f02002c20704a2a1124400c001096800c5040980e840c0c1c0c0021001000f805410001c2400300e0003001070f11b1244002c1202c4600c9403030100c0030441c045e4000f426403201161124082e58011040700c00134a00392502c030f0f60000e1500d0b01050031b41308510180d013440200700610380c142c42c41a95501d0500d5000d550712516205114144018810b0f004060504c81c05815080e69202c510f1700c002140c0c040c614011720509420681040d07104820140000c8a020540c17400038084032030070728202a02e469409102c032403034040d02d80c0d8081840000c050015010600c10704440808504e107451680c0340c3c660408160740d800603 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 717306187 1250 717304937 717304943
    0x10e030415050d06090f0203060f0f01270b03040503220b040e09012009122a01110102070501020306100203070201120b01090506070f03090b0c190305190c0b060607 72
    0x110700c4000700c03901c100b000d0500800c21003004921251100d130b05100341e45160003c0017a150f408401c200c147e00d80b01990024156090318001d10018031540000c1514000c040382201d0036000400e18002a07401050020050080820003a200d013028030b8202c2d10f03503000c011103011896043c0d004888003241c201d4110115140500403d183c83d25182d1500c1e489240181000c078255a6030164140b41c0c00e0354810210701044042980303a480500604101000c603000031500c03034aa00c4185845030b000c450300614480b582051114008141b00c080c0101c40750711070b1494030b140c5940046086010428150040c601035213003203504c22001080520209e98a00503000040d00060003411900d024003800d40c0b0521400c603043c036100306e05644035404102e8641c8541c5048400d5a04403442906255200310204007809481591914007440c003040b007035032001c14400560032000d8003481c200800d40613404035428080c2030700c4d00c119840b1203c1c038041c005c002c2c4a4800d40c0c1c003125001c0002c3c03542c42c2074801c54242d154 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 717307437 1250 717306187 717306209
    0x1703030402090709051c0b09030c0a06020705070f060503062106070f032d0e060123130905060906070201150e064006050f130f060b0a02010e0304 64
    0x2640d078080082d000c4015010343c050113201c10f00400e19413107032050700740485031030010740d9483c0c1030518080c160369000070304555580d00184040c45400d080460185c40c0320b0b030400005a1580490b06206042c461a64000007a401e141000010b04541180285115080440e24441000059580300704490310700c008034050f58100e0780c00110b856000c1c14034040c20007407500d0001640c1d24058040060140d00d03165088007910650141c001205160140c010f03034a0b040c0c0701400b101e514080750409442c052490f560010300c0c03d200eaa074001e40364812a2040300400d82c0040c494600c2a060040d2205002c0c1c2d4465600c1c000c5100190289005010b1070a845034046040c5c50464941000c100340c012028040d1030b841400180c007021051980061460440c0350310741c660141c0c0603c00d007a55855560303124922040c41c01c1c224108000d0742e522600d030f02c3c06e110540b1080d00f20803889202d80c00a207000c000c201c141e10315100000c01c19940c00d03405099154459002081242c0340c5200702a82e070b009900c00c1e010304d00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 717308687 1250 717307437 717307441
    0x206190912031505031b03100b010206040308041a100e06041e020a1106091c140a0f0e030a06020306030c12030301060c0812090a0b0c1c05070e03070f030606170303 72
    0x24820b912000e1145101035480300c03c181c5400000717080901c1c01000c09103001c101026500946014440a91146480e2108014068500780042d482d2100100042e0600c00100c0c0010140401c101003110301004502900c0c54603d07245c0751401078140744d4006c09440c8401c4200103001e07400c140c442c0480c9034181030b001d0842180b01960340c00c040d50105031903400b080380301d04144140c100d003003003e20702800c40080580503c103a05000003240c2d1450304103010400202c01c0c40500c1250510007141da1b031010301e04d0649001d5641440c02d0320010f1905c29900d030144540314010341400410f074059809910f080b001c1c1d5030204d0300c7c601003120b40c00036032815a04c00d8104000401c052400ba45550340464030807100365051907100e409600c00e41c20100e42c010f0894010403068410001100002e5901c820002e80413810058406801001088842c100042c45503682002c9034241e8000e4140d110340490040450388000d483e4040c0340c44070683c43c401241d03003904140c000b082400c050b013107641018211800941c119 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 717309937 1250 717308687 717308723
    0x8030a1707140c0c0603040605040516031203051305061f0807050f090601091a0405040c1e030515040204090e0607020106030314030714040e04110913080702060409060602061909 78
    0x59112030340364090b82c842c04404e80c85030340324000554802c0b80640c40014942c0b51505145e4140799585c4100240058269418000603683c0e100c0b00702000082e1900051030b591311034800c001d4080c59000980701d40308020401c180714520054072038040c400e08188600b0f00303950300c45040c0c0e00c001030700456610001071001010b41b81865240c407070b4882c82c14500350319900d64800d030100312801032040741030341d0b034000180c10300103030402c0d010300381201a80c2e207001455000c1000d00c001f02400c81e064000c0c03c060b19940803500382c0801040e10b201c503001c01031045640704d03982e111500023440d4400000b000303402018002000c0c0d0340184510f004803601070712140900d0740841c40c0b003001c540c00189070308144002d04028514031183e9070060400390a0b004c1c003d03889400c1608001e00002c44000c6401d201d151400c0810000c44156406400501d501001850300c458152002035217038000d94001d80c000d00e2900304006a8580d0002c3c0c824080c0300340000b0461170400440b00b01c0160b450700c8402401d00f0080c1010301002d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 717311187 1250 717309937 717309977
    0x30b0a050a1e0e0106170601080f0a090510150504050c0f2a01062d05030709021e0a03051e04030e0f0f15031e090c041805060108030a1707 61
    0x150b442d1054071445080d02c800503841c03405030a0304410f000800001110309114041203010340c00810900384180b061424a12203002d41d00c000f480700c1149a01d94181c0304c20030900304002c031040a000c40c4140540104014844420011841040d10640c00c003000305a80b000a041241c10700040c4910b41880d001000d140c842c1003039100c0386a0150303450031401c810500741e003e204040c090855035845400000c8008000f5058100c1d40c0754600404883c0d00301080f01c2e03603001030a4030885455440c05030719203004004000c800b00d82d00080034007560000031034001e1550300d03501842c4106441090031001c451070520407060040300f100c000b00841c102c0c1c400b18149280801e4030300b081a5008103123000020f5070401244c0340d0466095031100d152004014030a10605000c5441c8054a814080304102d24100034100d580f41140103460303000c2c030780d01d190842006182c1003505000c41d07044000c551b40c030350303440e80c00c03135540e03480360b4030103400180c1c0c0a22001c5140b40e50710b6824010441e540d54052124800c2d80c071010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 717312437 1250 717311187 717311219
    0x110c030d02160804180e0c0a0501080907030204050405030901020609060411010e15070651031209060e0d0308040b0601120c05030118050108070e1003080c0a0201030b0a050a 76
    0x245010700c2d4841000140400c00400203001e4401d50304100328240c2001c00262041c01c040c805458009201071209078a50008007022600240b0303100405860710300c41503003401a030b500040e40090400701008148200040141981b21342a42103403481e907030341e10525031540e070145d40c0284844140c101d4003282c0d42c0300d2080d0020b18540180150004509600d00c2c117415070281008640444d210020645285041e115117990564201e2036541c0089140401c880030f200180408010713a1113110b1403080403085098954040d40e800b003079078410009441c1001c0e015581074811000000d084c0710107050142406d4104a9415a06480748581da4480359039000125400605841c100303c0c801c54601c40c01e085034002c114085401c0d4444594a50406c90884c0080107240c440d000214180701c010007100c00700180181c2184c1841c0c1d40440305d6180c03201c41032524130055101070301000300803d41c5100403501041c00c440461007606d0070002c003402d07402842000c520901c5902c1d44408800e00c10000c04002102000d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 717313687 1250 717312437 717312457
    0x6070804031b03120e0a212106090c11010609061d0a0e0d090f05030a0c060507051501060305220804050f0307080a050f150f0606090d1502030901110c030d02 69
    0x1101c2210030307080801140c403900b0340b804261b071040241005105810006416803101c0c8101815103900051001d400c42c4480071040c551090101201c0c00300007900c2d80003401500c0f500c0e009004c0310040e204020800b00561894055951034044000398188191107102c08484012a042d217100c5181650410000307401041c0305e41c042e0322604076165401c0240181003003c041a180d0200c52802d011903603844101607007203070317000f6400151003c002c83c040c024075004403812031404a41e582214504507080000951044812244040000c04d095403d600954400c502c241c40340000400d14145600d200030302e0440c042c0c104071b020441400301d0f042c01c000c41840c64001900301e58060381c3e00c401c8070b881c05a0010f0140e44907086885084810007051000101220900591103030b1828180d000510842001d8072482c840c420000e42e8000e240c031113100c0340a5160308036007082c0b0524500c01e4500e0180d4001c0318016040c0d40703801301c42644846c0f81c0042e10045a030b035400544c00c0030100f046103002948004a05 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 717314937 1250 717313687 717313697
    0xd02040209182d101412070303020c04051f0608070302070206040306050f0903030709060818030307090609050324060402070f0311011406013c05040806070804031b03 73
    0xe408011020204601074000703014103190602c495030180400000d5100886403c52140e03003405a10400141d2200560b800c1080c48001004800001540c5062a096145071070080c203100005041c1c020032040544902a80c05220580d510003580c401c50309003204000650b85c2000c000c0c04842c1c0728010481e031002060400503d0034046030001440c5800c15402110402d440b0303410048200700c0c1206031074010f80c50700000c50450424110142a841c81ca0085a04001151000518070b40382c441164410311240c0c8152070340c03070900040040410420b4010070022810340100000c8500300010b201280f41034030140c242e1481c4650590301d58040000e0681d5034004d07000c1c400207002c01c4800c0c900a954500c85e4844c280280755118256081d12260404440c0505020f010810307130ba41c0084000390941080400000b0000440c14492032003100b4803840c090116011032500041900100148251560301c0308442d1142d0720707010100e070080c5007264000c00085401854004c039074008510013a20700d100b4180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 717316187 1250 717314937 717314959
    0x5090915030613051507090f032105030609190b060703030b0f120304060c0c0b0418050a050114120a05120702041a06040611010b09190c09083c15150d02040209 70
    0x900341c00c0010070707001692074064000d400445000180215025154940bd050342185009000501103100040a6448025040141b1080b031030b502c1c0d10080044000400c0340d912840d841c18020004d025800c222400f580701c484042d102840c0c0161100c0388040080000c2d481c0c80d060500c102e84022907000100d500181e1070f2008a41c0d4122800a00064850810070707007a090790307072944001a00c2c8054103044c200d614000051140b102c9883c0840d02c030280c10f499a440d100c10895019103400200744000d4810702502590091500019009140250084800340040c126801c1000d200c1482d01c4946580003000f00002c0003900e016202c501e42c0141504000948600b143c0302148401108a0344140f800c5100038201d180082c147c49140054812031510360641d41c14000320694032180c4012980d400c080c0710101503041022201711441d0360488051071268621220861940c547e51039180441f840280c400245c074030402842c0c0a0f0340b0300c40080c294400c110b02a0248070080d40300101d015002442608 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 717317437 1250 717316187 717316199
    0xf1203011a0405100e01080109020a02060c0702010519030f0c17131a07080415090210140c0f031312031205040c05120f010507030b0d0209070509091503061305150709 73
    0x54108400d138003e0300c900c81500441d000050084505812101d0110302c184180c8031200da00080940d03005001c03a81c01e03646c9002c00d00040e15140a41e0203889145d045090103608603a5040e0050071003680c9084040c050409103c0c0d081d64050003440071805000d651000149601c8001742600000318081c00410709200e001c2001c910824030200d81c1b51740481e45440c1440204084402d04c49141c007104d24042000094030344c00101c544d03c89907400010080480081201100400211036400c00c07541d0072541c02101902010703440c0e0b00002c3c41641030300710356030300015111100114411441e44c107a6400c80310380c401d4005a001040d0107082035030313200d01c4d595000c191070316030341422404254000e000f400b0602868800380e080d10402400ca07020141800c3d1480d8075911811000042ca45c1d040760b107004181d40d10f001c110b840740101c200031503108180300709100c000752034000700420310031040d030554455079100d18250010240424005182d03500c55140b4110400040b40f4858101035586401e400c9666510 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 717318687 1250 717317437 717317449
    0x30610051c0b030d2f011107150506061204030c11270903090105070201051e0f1308121b011e020c061807051201020706150501020f1203011a0405 64
    0x700364100c440340d031400003070140c1c54204000446595240341c40c0c10084207421011000c24018135a403409030007070686268140c031007034010300d10f030840c800c0c0220307101e00075400c00e26218502e981401c82c440f454100480c5441c00c1c440c04607003520010f41d00c68141e9803240d5500301c40482d000300c4203030783c0002102079840c150b81e542e107009610003445000044070902007006221340000064048041a4001c00104142d07903081807d072011541c09080c96034075060824103a442c3d4080514100c003564100043d2007550740c52001c00307803000c8a1210722120009441c1c02c00075950311782c7c0e081c420751881018004170b60b0000820110542c502500d00001c1200e603860b2104504840d2041e4001c64880c1d00800d400c2241403003003140c0341c1d112201c01c0c0c021916a9120b48041d482e480c0c5806403501400036a0200c43e0504002d40480302290740c082c0b41002565440240001c0d00c190500406006002d816484620340340c0005a010804500e0360100d407840e403900d0440f1111240d041e141c201da40100340310000d80341d80c0318 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 717319937 1250 717318687 717318727
    0x2040f09060618030b130203070906260a0312050c09130b0f0109050906010507080f0c03091528031d0a0c050307080a08090609130608010612050303061005 68
    0xc000105041c1d04041010345a00c0d500c9603e91107a6002001c100003092880714816007016007148407201d40412070020a0070079800d5040071000904062000902c202111410711b28940c6c000c034a87d031b1900c01c00744120303152015150050000b90815072050041c0b00160f0040382c002e540115903910f09411a030100305805128810000e84a40e0341c402e00f00141042e00707899440000919042d003001d81000c001800e0110007420040c100311020660804119040044402c000c0c41d080d5815220b03540395804a644e944030501d168091100344003003502200b0404140c4520130103026528694810f00f50f029070308000804510360402d516904c6496840e1a02c040c00c090802c4060040d1030402c03820b05280030101090382c0494004e41c400c0c04104240c100c0403a52848107644800710959890b001000101c00d40114a00d4940c8003a0041030941351480e1548240c045540c80b01c0280204da54552650001081075000074046810800003d151450025550000e1200a040c02803c3c104554440d076079410031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 717321187 1250 717319937 717319949
    0x609120b011a190e04050c0703080c0a090f030b04031e12090201020c151206090c1617030a050f01060e06040603021c05040b04031d1c1a0c0d050c0909040b0a02040f 72
    0x3400c0b0440c0740d0341001d01586e603000c0f40050072986080b031180d400800c4044010012484c58401103030002800348941589001030480080caa008580c40341041c8009450680b03049010400d03a4081940040d03200340806040407498440c94105040240c0c0c000141890150886c11800707403012110965482103150081c030220b40200c03a0319890031098491000303201400701e9110340719600030000c20f010302608450510f15261021031142400d4600101d5100940944101d10540070003002030076501580300d0380c410b2100c50f240e09103a0360f03100c0080d43d440ca20030211680024040005100d80d5019800805120140301c24090702000402000e0342100c0056070200c2c2c25441c120705020901d64424100c03049115400107a0705600f12000004500b206504100c1c0043c45c0d81031200700901c0603502c815a481c00c4c40030040e0000745803000f10200a50310036030516240d240b40c10007051040c070543e8181d03220403d001d04002402d48035030300c0380c0700761510050030741a002d0703001c10011408401001c01c81c0e0090807 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 717322437 1250 717321187 717321197
    0xb12130c0506090d12091403010603020d0f0812040f050d09180c11011802010f03051909020319060c0306140d031413030b010914060d0803091204030b010609120b011a19 74
    0x10401d1440800e6012070fa03c0b02340304c0d0381840c0040c005030b65042020f000d2030307500c08401c2c040d030089454280d1207130088001b0302800f94154402c00051120800080e610144104140d500010300d89130f06030303101e108501450b40c0c110003030302164404078169401641b20020604017890450a11030246e0300b91000b0340b0f8020341c5040503500c01c10865800030840c1c420020b060030701340003070700d0316000c4650101002d1194215064075003c4020954a040c0701500b6030101d0081301012620440c00d01e00040c0c81c0b030344d0030040020316003d40040d20704500a030015803503c00802038001008281c8048400d4101c84510455002c42004240111425025000011031240c03541403010361419200380211084036943e00105101001085003a6407002c03210040a9404071807583c40740c44503041949041801c21540c480103c1c001404818440d21800413070480306a13503240703400503403112104262840d01700001020200c02d0b030018850b000e031180d6004542000484080c0c1841215501500090f1040c1c04c2d42d00418 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 717323687 1250 717322437 717322439
    0x50604080c0706050a120908070515010f0f060c02090406110a170a020c0307060f02130f0302030c01030c02030a0c1a18010509121c0609060b12130c0506090d1209 71
    0x1c681484824014141c90030700c1e604000c2c000c24007404452000f00c0c01c469541da560908400c001c0f001050303503107598010040720001882030720307103000e00340c000e00171107904600941000442207041c0741c0b21810307a040c964074110307204460340c2804400400603000b201d016885025400c1003103800805000702907619510880c0c0c078209001e03c156200c00280000401d58010004503501c9403002041712a41c5511000016a034646141140d00902416040068000d01c100000920303004001e4890245e034000c8064440700b1000d08015412034143c1d01c528409a00140030700710381c00d401803500081d5980502000706142c500d03800c03079105030201140d4229814031000d0000020560034030950f944049080c0c02010280c2601c07507480a5405000c0c0392400b040c03440900c449000a443d0880001086050000d028041e02c1c0c0506545c1500020342d04007880c0c640400142045055110074001c3c5604072510440c0c03641460203019090b0f2010780c0c2c0c240c200d001c0c0009600040c1c0d0140807422240b080b41c0e0340003001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 717324937 1250 717323687 717323707
    0x102070506150d0309050d060b280503031e070809221b051b1f020405010f2625030507230f0306030f07031109010509041104150305060408 61
    0x745a0b190b460900521443d1490000280c000014109840c421500c0f44070f000c82030300c0c201002c3d1070540616030b044524500c248400441c4400d00c140369468200344001c0c02500c85050607528000c0d560581014040426020a43c03004c082c000e00040303008494982c58805060049102d800c020a02d04403100c00d60036100040304443c5c8103002e807150316646524a100c0144070010554007860a030800500c91580c2d082412881c104021942c0e40c05026820112010004002e0003d401030700c25203000c82c0d9481c0c001300d4000d2050710303258400c80816003c2c40c0310791220318824030841c600401c5d625040000030900e000c21f0042c0c00c00c0c8103000d5081d5401003201c1c5005030006006050810f0a41100c101142c8520503184551094500e04800140107680700e58829001902c0c005607000d01c00980d01071204007106200c0c003104850110841680c0050b1566628018401050b0080754060626130441035031076074501e45500440a52030f01c1400021009459844143c24550140c1c1c040702c1c0d4134030000c0c0300740107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 717326187 1250 717324937 717324961
    0x1a0607120c1718010503041227090203040309051516022d0411092817030a0f0e0915060f0406021513050d080712050a091407050607060b030f0102070506 67
    0x1c3e41d03000780780207811800c00b5a80c1440b003844044500050094900211a0881c18840000111229603a06c010f819a80b0316400707009510648060340010b5400c0700c040341d40d09107140842c00385c0c8041c604552808061100d071046040303001d030040b85d00c640e800c03809959030000305a007040349011a000d40703604c800c001b10030041103a81c00d559402007103005100ca5541030b60f880381028004034401c2d050902d000209003502c030500809404c18006400c021039101020400000604400c28540e1209103810300316040650350040f25082090f03010941c00700248111072141031038034070040c018000c0c42c200482410046800d4119400603001a0b1200380d01010256032101c141c0d030072250341000301d00e0f000c209448054503490038501c0d00d8240001c400224628070712990140d003080c0e11400d0200810b08203514210090708440c2416584140300c1c10f011413220001051040444d030005000c1c0f8038080301036440d60060700000038140e6040c007640448603044035007030000344a143e11130b5000d041c5a2802808102c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 717327437 1250 717326187 717326227
    0x210204061d0306070516050a1b1406090904030e04110a0323091e101a0102061f1401170103080318011b031e06080f011a0607120c17 58
    0x4480d034040014002860703040700c101e03a5085800301694801081ca41417451030480c3c2c0860041039a940020040f500c0274985002405640d000103841c04580d001c081002811701507401560f6011090b0408a00082d000e0341c1040141c800107040419814207071002480150090229500469192000c0002da009070101000c00001d5032080701c0344604110170b001d9035464102c54a81c014845448844048000800c407c000000c1e020a0070f0081e2002c032007000d0b4110700011304140c007600c0f6a001180c11086075030362129450901d5050080c145140c00015041200b0410499040c0080c6a00d2200304070b01d0000c259000e5801112070690b03d05040c0f0b245c411021888070011500e03407610420140404422103200801d0106207030205682042c003c03460246408a0025240e0a26141d0005104400810030505041850000f0040512524008140f91070301c450040d40c045d408000c0c0400150540d020303007000e03500030310340300245443d240c2d01c501f04a001848108040c3c0303c0440e10305142a09200180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 717328687 1250 717327437 717327439
    0x20c03060907030318090213060305070516170c06010308041a190f051c0e0c040c140705030c06090f0c040b010c020904060b1315050f010f210204061d 66
    0x2055901e0405001910707a10705010003001c00076000302803c80864205a0a005041106030841d60341c48807201e001c2003190a44111b8010904000008041a002d031059619001d60222410011840c0c0d640b011004483e981d00303883d01500501c41501c10b4802005020b010f944614900c1e0b40d501e007841c0d0888c50011030307035203500b0380e6200401501c1d018003c040d00d511072021850504074035004c2c0e041d0040c1d0361405000c0d218418a45034010b45403903815180c200c00342081c106025986c41c82c20690500060382c03010030401012036200d00740b00d410581102c0c001c04080e4041d00a0b20300f40702c00c203030709582003400030380390101280d1211440400d0041c091010400c174440813241001417046440010309040003184000e4841c584e10320010341400761a801c20751000c0c0c0d00511010048410080c0d8400030060062200802c0c2c031855004034807402c10040e0109425016154501d54003103100045600102c29003103010300c019003035206519020680041c001611164840c007001c0d145010442c000c00f01164059 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 717329937 1250 717328687 717328693
    0x30e1e0f0609031206040f09080a0e090907060e030a0503130f050301050411130912030c0e0a121202070503060c1b160b0705070506031302090a020a120b01022506020c03 74
    0x80180703a2000401ca840c2c41e1116199180130340e503038600040c004c2c4161083e40c900a401c0c42441c3d802c00400303500604101e440c540319410340400c0381e020700882c200101c0c0c091400e2341c8404020320215001e91159043caa00042c100c40351b134809507640b941181c018204900c19900200c60034051141803101c108080c103030a078000c10080c03800d83c0360459852102c0303c16078020141540484021483c541040030b9164114820010f02c0000c200300500030400305548900151002030320410300e24000c41450102c69202c00f1880c41c2c00d010ba150803029005540e0380205600c114540001d290b1001c0c0070b00c2d403007203d10000c5c1da51201c0d00c0e1038417501182920386010320aa081102c0e9810a0f10711b00061a060b0780b2000720031903d5040030b1401510b018565004180e01c01408030800034038888141481c1e250f24400d59050a10f1340350404007106038061114030b1004a9005240114007103150b5000d131040020501c1100d07040341c90f00d404c034000c64071000c550300e54251543e00c06207e269010000c44254041c00d8000b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 717331187 1250 717329937 717329941
    0x8070b010b0f0403020f12010606020601140a03050c1512070926060c0a0302070b090f070b0c0705060d090b04060902040506010c030c080d02041701060303170c1207030e1e0f06 77
    0xb4621403180d400020300c600c140c11446403050312030152800e68080c80c04004c00061303464103400b0303603503070000d01c40c140800d8189103c9000c01e0808a880d0411079a2080040640d13040008c01c0065000114104200c020403d0122100303410204e200c0c28021000b90703c55210160a0180b44003419007090b0303064411000380a1040c0a02c040060226071003001c0c0f11505403909003001045000e440f4030ba201400104000c420300580c0100410030030080304000b0119149181c2d00d8101e022140500040d9601a421810f0204004d04103113004090429003080001500280c0795a2070311a01010358058030800c3c1d4034103c0e10214246481038079040902428119000c00c403e5070000c09200c0b0750b01000f031012a02003041c0b42240c419405440150402041344d141c0020030001540c000c000d07030320040d000198a44a494007079201440b040b40a01c03c0348c28202c1c5414a545020642408003a147c0380800d070342c1d9128040050010b02c40780d040c2840c8452444c2060100540e0185041060702c0b19034103035040700302 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 717332437 1250 717331187 717331207
    0x160b0708072c120a0b0603071703120705040e0106020303040c08030412062c031e0307080402010e030705040c0e030705040501120f0f1203090b09061005060c01090f08070b010b 77
    0x181056902c81d168441541a05400d0042200301240c0765210000d4400c2980002c10049041c64440c4100c100b6012142c0090303542250141c0c5860300c002c050710a402c10040441001c0403086107580c400010300704145040e9070b4000c08000407109900c00001070b040441841300300700ca001070301c10060500c0c134019030411782400491521020700120003032010365546405001020070701e540741402d0031071003614460b600600d850740d900d81d4005804420002105240880c501074110300f030383d0041c03125580e07070f200e03681d5558010740d166075422040325410f2144c01d200207150b5440c4e000d10b01d03000d1003627500d005201d02e4000130b01d45041119080304d84550705040060068103803000c0d40c106540d4101c1d86139044a40c89050903640000d1120001d00b000000c503c0014039030341c0582105800b58802c0340013200c036036070740720f03845841d900d0a8984a1881c001910108894540318014204420500e400000c10420550304e02d50a014151011203807500e01080104c2804842541c5a005051842c07245240c6142c0e03031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 717333687 1250 717332437 717332477
    0x1a01030e0d2a0807140609060f0903070507080705040e0303040506040305090d120c030f03090201021507171518010b19141c0605030d05030c0f160b070807 68
    0x40041000c00c4884128004800c0d8802c5030032800c2c030b60891034000c10210506207034849601c140c1d010307245140001d0300c100010034002600743c440c0d1305800103010309840b074031b4200c40a0031014041a510b440240503a0f40440c0003440b60700300a14580340105611860981408183d034004a102035103070304140304100100d140400c030f291b4442e91501e0807030754900200001070601c2669040142520328407400d030310300c03030390700089031111041c0a5100c0110f00070744240102c0c241c8800b050028010f170080c12228500d0b20071389031803d0f00a56a0b0400c01f281d0100001d42e0203e000d011200c24414490035001c0b0440c50918100c06c855030b46141c140c80030303d5810240b180c0d40c0d5200c3d00405966400d0b11079103480f543d6214003d40340c0c800040c0c0101035035904105078021001402c200d207110a4034a0800e00090364507000640304403044183c2c482c1030556a0344414110316401401c15081c43c118100080c05c1a6880d0040b404030700e51048050f60a58100302c5001403481400521a00034850a03507004921030b5195 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 717334937 1250 717333687 717333703
    0xc1e0f01062d0f030302030301050f10051e04082415010225030f0b04060b061e0903070302030d110d0509220902121e01051005090403140d1a01030e 65
    0x20034100c08444810390b00c500602110b0f82c464514040f841c03a02004241d4003000540c12140d080f41c00400f00045c0d00d0030000000042d251a0011581c02c0200303d070302c0e00c0c605040c03c0b00c03020120005401d040c1d41d044082e0a04944045212000c054100030321a04012885007540101e00144080490603030700e00082d580307180165604000c100c20003103440b1110300503890b03a0003030755002540226200c80361910340004c3c0c07410f49003103400900b8000041d00b07a00b0420141c0300714a08114141d8500c200d4003007420b1aa0740301403049034143c001e80f40003002684081002e12a026000d0b03482000349010607040300e0030543d0100b080f400700401007046c4404e03036542d43e4000384444d600e840c440805042181100004048246000f03400180004600c1102c8201080c0c030410b50b84c000702130280301c24198940d6030803640121101150040c540e9030034001800e0130781c50150300c1071090400400c1c4c8410a6040e9125070400222800032580724810300220701142d1139000c80303d64003800c060050004c0600d200f0744a03825 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 717336187 1250 717334937 717334979
    0xf090e0d02150a0e07061e140a050f0f031f06020105060102030f3618015a1d01060f03110c0105010501022b03020307050c1e0f0106 58
    0x5400882c1555590f035100c00e6944001c10b00305c4010703960300d00c0c01900c59415001c5100075400c7c80d00c030f0140b03450b0041044002c00320100340003901e00300340108196140d030070000141c07806e0700051180c0104054210020b5001d020030911240d00c0c0c040809a4003c6803940340c11180440e41402e05005140c1d0f00007007031b5031759140f01d103a030b003030300d0352000c4034420080001c2100c054400100e500703d0001344a60340441441c807a01c2a20300c8210341d525000a413007203100070b10a1b0f440e08010311818040c6d45002d0308007404001c01c16542030100084607401901c02105c000c1c0032041c1e185201041c0d548124281e00c2c04001403013800b1100102d441400001900013505200e1001800055060041703070521a511880b040741030003845589607201c0181d03a0740244001d002e118054400c154a0040e001c1d05000c14481c400103c01c03d043d001e1214210481c081d400c0603100e8010b00130180301807101c00d003050010213841e4222000e003c80400740f2005051a14101d03c0350940710f0f034900702c0c0074055185c0100b400000412 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 717337437 1250 717336187 717336223
    0xd020303130f060c0905010f171b0403081209060709060f0f09050a09151707032a09021305041503020f0619050c070b090d0201080711070f090e0d02 65
    0x141040c03100b08001c5900144880d1030b091281440e6a000600001031b10420380c0c8401c160107001e81306580341e1184a514030141a01c0a00052007030408274000401c02d10316044090400d580e96032030760310b2500104945c0130100c034484100000c2010030085290322040030700e041e03a0402e01e0408040c140c0c08024002004000c940300010804c00c2c052034011006103030103000c11079165a2a000c0b08010068686620b030100551072001a400c40006172000f05da484140c054011280f031036907400c100d1075003e40700c006203a80c08402c20070b0440c0c1031046500103000c4010051383d190140644107a0900c095013003648070b58074000c2a00f0812076402000302c2525410f0f980b4041509001d40000d880f0300440208000c1d44120f01c011307100f4a6440009002d805c40e4141c1100c244507210003041925019002c81d580c1c21030341c550041000341d80b023001e8098110141e42030038440c0410b914070035820007440383c0000e10690707880081000745050620a0f04400103100016258010030080c0094681c8641340e88102082 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 717338687 1250 717337437 717337471
    0x6080103060c08010312052d07061d031209010609020301030c0509130818060706050a060f1410030506040f09061b1103040302010e0102120703032a140310081b040506030d020303 78
    0x1a02300700b048980d184244e0940d1120004075040342c0d466038000c00084860781c1c00c000c246564030325032528400d060821200a50304180002080c203444001c000c0040099640b16100040da00c02c1a100a40c040c5015003d0000b80508000c00d010f080ca1000d800c01340c056268118940101e0401802d580c0c80f20b13110702c0d600b24101030b108002600d500601d40003800c03082c40d00c02481203241c1c1d5544858119900442040c20180e55a610032a074500b03800202500000303d02c2481805130b110f60300455118400910005905038010404011116038100c1191110360361105071800400f0410707100b4200781645030a0016916040b906a100c2c0181c1c84000e0600c000007002c189a6130080c04800800032541034a1500e4070454200100902018401030350b506940d80c01c071507880e803503880307000c43d202d002505c0301105e0b041099404000381d40300500314190f1040c6c2807000309810a0510441802c80071541c07a420541c4000010401281d4001d061244240c0c0a880c6a0b00d800d5008003d9950101c0400b581541c41 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 717339937 1250 717338687 717338707
    0xb1f0e190b01020a021c020a0803030c0315122e0207150903261603020906070f11130b030111071e0f0212060a0b0901140f03070f06080103060c0801031205 68
    0x504074030402540900702d0b101e4250351b103041c9440000528001c40340a4816503032851030750344a210a6600411a0104000050445194020000748018054031f0898409c181d1900141091003138411020340d1007600c2002d280c04a02d444080c1c1e5082c414080852828025544d4662a68407440c6020342d801d480f0345121041c0b40c024010800301d007244c4400c40c80300b04413610342424000c0003190b0b040004901415400d031103030700c02e1080d9010301002501c201e150a50544669400401c59002100c140201780300c030620307a885243c10005010007495001c0340d125001c2c1c08042c02e5943e00101b02140240c1800b01c1d00205030a10032a0000644001690b4418172250821854040321403a011350800100e8440f0010154000307140c2d4401c51110104000c182c0c03000c01000340c22002131103285040b0300304481200b214a0030780603102c1080c0005040f550103690f00c649040602c82d0075801480440c030250010002d0100c43e0041003e006902d140c100c1c4990305594840517000c0780f41007244200000410341c0141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 717341187 1250 717339937 717339943
    0x30212010608072d0e040f0f02030d021e060403141b03040608160c021e12191203050709170c03060f01140301110a030c0207030b1f0e190b0102 63
    0x9011401d040e10b04403a00d0700d44130345203121480a144e200750035203003038040424800001281030780c01d4408004665221600d41100b072409043c0c069800851024a44006a40420a0401d40a22a005460301d000f074429101c00010601e044108660011020000000e90010380d03140602c2c00c18283c15140c0124021440103c0c515074401c20184c071000501081d21900590040d1041010501142c0655101c8200712011024070500035000003010320b502007101e4401c1c424280c0804040c0500d0743d505251584180780203001c0342020b4201e400c045004c01030040810b031010000e070580c141405203040490004060300881d215010510500759405a03000e401401b40304a540402412203070304d81040c0c10031a01c18942032081880c1020b000740412094281809800142c8a5804c00300b0300f403488614054000c1c24860004100718020190040000381000300d840703024204609000d04030700100a0100c040d0304607038022581c2d00c0c6a80382003144c000015145640000c40d100804550912100f0060f8a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 717342437 1250 717341187 717341189
    0x10b0702040c3b100c110f0406031208073f150612150b0904060b0d0e1005150d0201180803090f0103020c03030f04050705040c0203190e03070302120106 67
    0x200741554180c10400340d0f2040c0100241d205019944200c0c0c00f0303850b004110a0b03014000e88000030035100c40907400490380c222140c1a1780c6070b001d043c40c02c400e4014400942110303101d400881c1c006000000c0c0d003013050b03403226a45520401c1c0c0d080402e075040203e02c5011203250500c40311300600403170044c00d800300d00c7e60050150310440789020601280c5040000101606a1409580c00144402004d82c000c6201801a0480740d441c01c160f0b0b854140c28082d00f610711f50701280c02075410031340703034240080c16181d91401441003c1c00502e000819000c050a002e003007080540c20502d429041105111841d1508041c00404444c00c40340355003410010710040e50300c4a03000c4d000b0740f4102200c201c001400f000c080b00800400784102c0c0c0801c010b00320f440040d800c07030240e1488041503a00600c0019038590078040c115410602039412134840541d550006070a0300c602e03000e500b005030130200d0145540101c06c401408a56400c1c10081100e410340c00219548010910010f48074441c495401c610300142944540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 717343687 1250 717342437 717342467
    0x7090203060109120602091c020102120f040303030e0a05030c0703030806060f030a05040327030203060606030f0601081b0301141c1e06020d090c05210703170919080c030105010b0702040c 82
    0x12103003242104210b00d0071181023030103902600800c403015001440b02c030100d41e01f03002c03002c00035800c00d821920f04030001c0c11690050b64081c880e601411002c60000c01c00b03401550074000042402c0c0d411450014031580c806442d07940a030304240140c4407200148001e40b54000c920120016040c1d4850a048800075038801c1c480048001240c030488040b240008254252030080d0103c0c0c2003519240c4c28400244021a070030301144072154017003103096100d2548560060154a440500802d0410200700b9030343c42a0b001c11541c5034903000c3c108071802c00040c00740450300c10410103d20b60303005d603c90041c1e2400c0201e44190f81030303900780414104040340d0f0503901d8035905810200300030311443c901302880a0f03603405a04d100c2c541861900c0244441c20344a014070004650107000c4592466403200c049a1202c105018a2801880080900c1d11004a40b450007626a410051024504146107082118071a0781600990400c401032250701c0100007101c48079039040d90000b4000c07030301420407546620107030194 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 717344937 1250 717343687 717343699
    0xf050a050a051c02030901180b010510090e010902030708070e01020606190b0714010e060103031b03030f140103030906020109110d1103060103060506040501150e01140c0d030204080709020306010912060209 90
    0x443c0107602d594095403003281000000c01400c0900305a02c0c1e0034a4031021300500001c180e43c018003503428854140680040c2d00c2c03c00c00040c1ea103a2400181d80c0c50260410f69806501000704000341380e00146558101106082182c8810440c60000f915444010201ca005c0c10009242188443d4800b00000051a1b43c0c000b85d07490b02c00900e04550b481c08a480741410365230a022801240036804644241200d6260b200e03480342c1c1d040d4482d035a003090a086001e03020b056440c01044902c1c1c1c120f000b2003c050001c00c0349000158107600c1c0250000300d85400240031a8540b50102c07000541000000b40d0403401101d5824400e000391402003401e002c25407543d0f8140c06582c000004205054000a01411007140c050200c0da807a4103400c00015810004000014009660040702d540518040c00c81100d401450350310b08641000203a2401a8003000306000903030000c1c0400044509000b00310140c01a140c0941c41c42c18911300090a1480c3c0d4001e0341e41e6114400341503401c01401d40e0446903c0d0401501c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 717346187 1250 717344937 717344977
    0x3030c010f06140a090b01020328090614121305010e0a110904080a1b0c0605040303031d21071205031e01081e010b090f04120f050a050a05 61
    0x5034064084480403022880c1440750104021403203800043c5012405050184071600d09002000036105a494260660004000000100384020007000e100801c4072541d030310380c1141031030090600206500c4607080000d0b04164901502c92001101c8a4100e0020403143c03685a01d080c40c1105120070342c0090480d0301c1c0504140d440701022441003a000e000d4224281c0392007001c800d20260320300c11980104414400c0024024140c001c40000242e05542d03000c142e191012039484200e060410b8000101151002c41e0410415a0600403881d000c01003c2c1c1aa40d110082e0010503615019a809261604004a541800c0c0b20500c030030380310782d1608240a00d0142d0f07001840501582d20075035075108003000050518118403000080c190484480350700800c0c0100c50b080e030700e4502010340702d1108980d5480d2803448c501e9030b4412905900810040407540c52038181b41c645040e0220741e00714503005100c081c02006c0701003600b1800f92210f0107450300b040b1b942e40403003801c101d80c1e5101d0f10303c1482d104100100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 717347437 1250 717346187 717346207
    0x120d0f050a1a19051005210f01090621030e18150f03060708060607050118110306070807030222092304080304080a0302040b0a03060512070f090b04020c100e06180a1205090303 77
    0x1f40250040d80d0980310402d150341c075604000c0030390312203000d035510485400008210b442c10759008090818024036082c80c0e156000c0c0009000d8012030032820344612041c20074005906652b140f81540b01c1e0088800301d404903ca217000c641ca9510082a103000d00001c240021025207400c0101c0380d86603800b10080004440c0d48880d0800d102410320291102503a44040400a040008500380241d00a4442e50b10550b19440101c01940c440380032441c041d841003010074550501040c00c04040d1007440710201d80031000ea1888817a01900128444a00d503044040c800412a0101243d4000c0d801c1000380341d0710441c902043c0e0180c4605d5000242404000a005003050f0381a80624195001101d10b03418010758101358965600d000c0c012030140c1c031000941045007854a510282500e41c0140c405401d004e4045e9010381001020305c0d1441d9100e4031000c0c2d05001d09001e1140701d510044030084c40b214129062240c1d607642c04e20b8000180350082c000300000135903014a060742d20410005040381d43d110384600c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 717348687 1250 717347437 717347497
    0x1201060206010810050903030a0f060f0323070302060307050a020c0a1d010902040b0421051e12190503070c0b010611060c090102120d0f050a1a19051005 67
    0x44516032090083d800000002e41480c005c07240101100c600450a545443e01880001c4c883c0c441151003a66540000160f45900f140c0010025802a03160300380b00e40420b4044416465012a1070b103c43c0c2040381c0900050346c80728107076a000b891a2501c40d40300c51780340a0582c0750006c490740055001c204031900007a05501c028003918000e00140050096990700c140010590207030740110441c0e444240024026440750740215090f03903103180e20207c0c500b03000e911000d0030854220340501c00207040420842070b8034800c22411805019940806140001c3c592a202008150364450020401d0010100d8031961151b00c6118940390010203091813565076050240100b5225160504c1c2e42c05214000b800d1061410151501000103130003402020b0b42102c1c4060503544442c5e14008019a40c280d43c441c00925271240d1481030070a001c0020300000980802d2003400c022200e5984225440f80042c0e6414666800d26001c07200c0544a00028840c0643c0568450180c440403202020034508001c150300300d00c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 717349937 1250 717348687 717348689
    0x60403060209040b122e1401050117070903080304050a050d050d0e07030b01030813090c170a0504151a1c12020a03090e07110d020c091f1505120106020601 68
    0x3c550400031300040e403041c44201c24440180d046260006000c3c444000d150b1607640824124840350001c49042807541801155490b4040901c82c20340d410044c882175030002c0f050319040001c030100794080c0c50801d03030091041c20603000c010880c100220105040150411182c107015500201791401c58010a50040094020100a007040d5051090041040001090b91820750350007080c4511103a0864840c20115030000b880c0c00d940c04045880025031120905c42c00c0d00e41983c41c3d6500505840e10907501900803009403004c024076240c002400001742c115108001c6481241d04081040500c24110300c02000551003e01d40203802035521814002c584c80d21405d07183e21640b020b54a40f80c0010040fa500d00c1d81d090000e0108031800400e000d880c05103010294030030110314001c1e14810156404a040c0b60f1039040480c050380c030100d0520042c0c5032040b100d961089003104214014a95247d4a00041d0120300c01c4116600002d2240610180318500312003d540010041859550b56130a0082d80c070311003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 717351187 1250 717349937 717349939
    0x1030b061c1e031803020a0b0c070518011d070507110102070b0a11010606020f0a080904110f0c070503030307020d030e03040506040806010819080304030e03100609020d060b0906041211060403060209 87
    0x44410361411510f80013990a0035683c01401100300141411003002039031340b01c0c074104082c2d4890325000103010341c0d80000c1560320080c2c441107500c0c40d5141c5080701d141d8451000090341c880341490100110f6642c050143e90300503412581245031004680c00503802e1000781c0d0000d25071003400090102c19a1340103554200302081c010001c101caa40c1c2c508049840300e031400941455a044840b2020100c2c1000d0081c08105200070070000b51034091540044040e4001050f0400d12030000c114844404c030240302c2c10000306015400365103145002d0b40025100c0c203501011205140d40c42d1400040040700b041641d014041c007500b4a543c0e180c1b281070465076190300741300740007041c4648040307141d03100c04080400c0d52503980031031000e06580b11582c01f690349014440130a070b054400c81041e41c0c2540014001d440c018040d1940c010b9132620114000400d441e000d030170071444080200082907094481104450413a203080e8800903c0382101c0c9400200d00e0750030020326901080100340401400055402080e030060 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 717352437 1250 717351187 717351197
    0x30a110414120708070b0c010605030a060b04052401050c0705090a0b1306060c082b02090102120702090c2b1506080f240d11150301030b061c1e03 64
    0x3140ca811103030380b440b003402100130f039410440d420401c2181c10006000c4d40701e0340100104983d07890b480407034600380607075800b9248070b900c0d075810200c1030820707110311601303c90010544014100300c0b01d080980c0100b00494207040210004600c00c5044060101c000906030051040d0001d003482401c001c042c0c8060f0101a214039201080c2c4040c4461a00c85c40d000c8900689890740002c4140e221103400b40c000b04048030000880001d5040d94a80e10103104900d0700c03481c0d03001620307400c00200092030702c000400e018185841c108902409a41c98418951b40150003495043d40c074020f4640d014030010750720380710f540d4100803861907000304260381d00906e652102088986403100d03681c480072101d01e001560b103100583c54007004035000b1000a0121081c1c04005900c0700503410241010802d00726402800fa02c00380340142e0051200d01c2c103a90360582d02201c80600d54110350460322040340d5008080e0140e0700c07450b440070300401112250041d07076101c1500208210074a02000ca042e0400380c0000104800082c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 717353687 1250 717352437 717352459
    0x90f0109053103030f09032307022b05030703030c030b0d0f02040f06050d060f06120819170403050a0e03030c030f072d0605070e09060105030a110414 66
    0x12940c481c1d14040b50402c166608030101600b040005007448050003541015103031009000c9400440c0114040d191081d83d40080d5500725514410035440d0012954500d52002c206400160f82d408111210301e0841d00417104c6403d100300042c03000c0c0c40ba4a80001e099020120301d1302c05058040d40000822140c035102404150015010405070320780402c00103010406000140d00036007000e6000490b01070240c000000d140d51a5070000e1182a1002d03000c4030465282c00700185000c603240a154018080e480c0304640030541c3e681e4441c00360145405004441a07100c095280380c91290010400380311901d4691b983c241842d090080a030782c02140e0750070210780000300c030340e0040c14004200e86281e42c0340d1018505098000d01d00c14580e900500d410348805402c0900078078442c0d01e400c0c40745200a015000940d1381c0c4042d180c20000d584000b0702c80d40600111641080042e2100307012650f2040342481c0480e07903643c0700b401d01c9000b0300e00d50004002c10701003ca80400c202e01c015207561074000e01141d0f022030607 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 717354937 1250 717353687 717353701
    0xe040605060d0515130b0420030c071104020f070605060f1e040f32100501050304030c150617030f0a080405030c1b010e0316030818090f010905 63
    0x6589503100e0241c200104010360a81c0c014180c3c8920740041c4a56103c1c0c0307800078254000389a50405488291069980d20500d4050340740c03070f10691212458091001d2000d242444103500c11340002000c40d6120b210000b50f0108000c5103d91110710702c0c0000344110344420382012040788541003005d046508074a0301021179001e260400c6800086a00108844209440340000c2100d40c2d00541800d500705445104a90790310320940904490340d10000c3c1c006180c2c8020000c00713100b500d80c2109a403110300080e020b0159a051b40704400059400a0810650725151440c04039140d0512080241140d8000514044142d800e82c010400f1200d0300c01098226050700c0050076140d115002801c400c08000304488480580200390050740035008609a0b428234000e101c0752801c000c00119140100d110f1240c100c42507681220b40400d40d04001e900810780352420b907808010721202800090882000401c0300c290a400320050400302c0c07100a00b029006040800000382284800e000750541d07141404009075503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 717356187 1250 717354937 717354941
    0x30f080d050703200a1b05010e0c090c04060e06070212060103110f060403020904050a0507080c042a2f01020d1b081906031403030402011d1305130b090d0e04 69
    0x410710b80c42c2d895050000304020b11400c0d681c09205010203100c1c4900705031b81d8140c0c0d00281088018090740c00403500b0500a00345078100321386a40410702c40c0c125001031140e00b0384c61900b0349040c0c0d2200e04040440920b4480010010700408100079400903180c10703440070b0510049207041c12130348101103002d60800302e0002c0182801d0000074090b0003510612003003002d0300d001e00a20390094060740658009203182d84559041c81c1003608154081d61202c01e00c5a003a050a101c0c009901d50003429201c0c0200c4c040c4410651043d2407000b0b13000704602400101c0000c8400a510382c09060306120000f210120319a5460103500004a03000c3c1061130304001c601c0d5001300340c4108908041c0c03641d81c44010f54501000c0485100d0301820994060b0303840342c01000054100d05a403022580320f100550720f030f1905200040c03401c80b1001d074103403c62101800c044001e40720030b0128500e40c11992000300f0305139200c41c1c00c030b480d0741000c82c0c000c0c10903146a03061000a00300890040c124030700350342e10104030300314070424481 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 717357437 1250 717356187 717356201
    0x314130c0b1e090d050a08030f01050109051302281d240c03070c0f1418060d03030b030d0302031b030717040f02041a011215140a030f080d050703 64
    0x842c1c04a04000002c00009810041482e00700007000c078003440440d030f1a0301e86044000711088a000c0310002c01c0c400b00e92501c4032402d00409091a21039103481c18503022498050074003490700308003070700400c80e26032a00c005c051040c0081958400c0e02c001c1451000e004211007000c03003100015520800060f84a82040340010034001148401d00d480e40344100e0400a0350307032040b60b44c80600d000620402c000100080c03c80c100500140e280006e0b80c0e8148403451861880030480d0502c11f010307107200c843c6103045950405610103400c849941040a090609030042d048021081d03900d400350100300b02a1a4250340510f00806001540c40b0070f00d200e090702c40000e844145c0300384c0c2c007282d5030700300039410b41103079040382035000d4860a404241403000364003040079030b0558100c1d001000d09030164210342c1c5d41e10210000a0b040380100501007030700345828801c42c0e452207014110070324070b1101c222411601c507051602c005560082c5003a074451081c0c18080f0160b0000c40500300203600348404140c04500c6030198031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 717358687 1250 717357437 717357457
    0x330903031605180909071d060405060d120e0609030102190e0d1707061e0501170c09041b08160305011a1c05010b040f0207020f040509030a0f0314130c0b 67
    0x3d80d00c1680d0310b0402564004c0100200468840c000c0041096600d110303070703011110000725a041103810244108010b5a20040510f4081e000500c0030501141060000d2403801c00c0b1420003051035010000441c0d41d92042040346505507000140c0060800080805030904042d1341da035490b03980c01b101080000c5c62004100c00780103d612840303611080c1151400411100d4402d407000a464180502c804409881c01d0802010349965280100300d00c18201c4032000c00d003111000900a9543c2443c00107100840190002c1c0101d46640504a00d840c848290040030786039900445095002c84105245039100c0c80c08101c401d0f50800031000e40e0080c024640100c0f00301c00521400048010603501c0080c11010101500c15640786c850003011600c643c86800c1c0084052440035076591024010b122122090940082c061441c00c400c120441c0008400d5880c041000d180c4060005100c41048015002a14109940c48024011300441a11504600c401c0b80d22030720b10104e807595034802c0c1d4011802a0a80d070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 717359937 1250 717358687 717358717
    0x6010b0f0d0609060305030a12060f0306110d06030c080c0114090f031e0c0f0a0308030402010503040f053f090f0d0b0a0b130b03330903031605 63
    0x12000121a110141031501e1074030000140c0d031a520f5003000113841c9140c2c000d031001e070030024444060a510541506060881311414000c0b03914185944c155810680300140c0b46d2581c0c4d0442c1414400000104c03a80040049010f01ca0940c40341050400071007544549101f81c070030340e4071200103540600c508110f0068110300342c43c20104100240a064441c218209500d4003849070342d802c01c20524455038641c0c4464000900e6025010401d00c45115024141c282c81400d5505041000070700074004c4070fa1041d428a1b0950710b075181d5240001d48030100c08402410760251a481c008180b4508401920914003200d00b8484c5520f1030442035003980c0c441c80402c04000d070030015014035092180c2822640a400703401c031441a452038541c0da40542080d02d0038a196034454000341d486140158118080d0000c0400401c05035840d04002a038541d22030070341c003409064642c480c0c0c0b0003d014080f001c80781c50480010215500e0071005003a140d6100b120031041412020342e1002c05c0314410401c0c1c0d01000d003e2094 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 717361187 1250 717359937 717359947
    0x906060307060804030522090f090209072006010b0d0f050402010e060f0c0304120c0803160f080708030702010b040609090b19021c1a01030212060f131406100206010b 73
    0x854a50f00c0c0100203405202040110040325040742d0b086141000001290000c920305001114090310305090b042c0c901d060400400c41c0c0540d481c070003565005501e6050151481040c2002c18918046900c0c080101d40518000080c9810001380241a80c0c402c080c01041215002454001203c10940c0c000c0d000070000071140c1e045040a10051040c882c00785180383c03c100351004640e00d103500c107420841c080d00c41c070000c4004102e0811700b82001390004001850134010504101e81642d410a42c0141640c102a80c0c0d06080c80310000c2241c055640103446036030f40e452300396006030181c18002c038150b000d207140c4403002400103010301c01d0440103580314214400310f45441607102e0300084404020680140d08000b51088002c50b8182c10f072204110640c0814090b450700d214503141e081103142c1324181401080340080350703040e580602d9440001265020780500030308000c0740012a014080341d40030b80c0b0303000385003045c4030402c000544101030880f003a10080607007201c100e03121002841341640088043c01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 717362437 1250 717361187 717361199
    0xc0e0c070b07050f0c0a2907081f060c0b1005030a11210616020c0a0303111c03060f0f0323010908070b160305101701020403150605090906060307 64
    0x1101e5508982c461074501c2c18030b0400420141160702a402d8210a0ba11409402c0c081020110310340c2c4084400070401d8000b812440b845480ea40e0f0014814410410080c0c00070b00d5039130a06400410340104a103903500d1081d154900a8000c401000c01aa1300312810750010700345114130080541502d4015001d8050790085070b88419110b012042c10316409861040444020310902c0032440d01c10010800502c0380b402d1200e5000815000c500d005011900312018070315490301c0d42c400f0b10080705c0c1e041c5000d5410b62950001207060110b25484446210f0110052150f015810b4001c9010741d01e00c1314246002a41d1480e85441c0c5a106110046c06000e071070305440d03012024890004410855800046400707000ca907501c4115520844013194180d412078203000154102500780380400060b8201000b030790904240e41d11120603184954030303160b910f40c401e0300110361003901a58001c6900001d900c4021010b0170b41d4034041c00850103894051528080040c1d80281c0c001040ea02581020303000e40060b6003803207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 717363687 1250 717362437 717362453
    0x17060d0c2303011109010f050a0c0f020612010f1404090c0b1b1203070801060201180b0720030405032e09020418110306130503041811070f0c0e0c07 65
    0x1959440c015054150481c100381c41c28003d5500841c04006415902c0061800160040070a203880508001060040810f80d81d004030040e00195040141d0074071025051000a05910a10380c103072010310030080002600b0340c1e80c0402281521000c0b1704e01c461a41d4020203110490b01c00030300c00f40c40031804850070841514050020b11400d800001e00e12030740d2001c410320500d0926004110304490400104000301c9940c005002d41c094082031009001d841c944030740d25045d44400703030b0028040c03920580c003294225010f885000480b80c0c640702c610080300d40441c101a100e4000c2d108590080c0103083c1400130320080c01e0610380200102c181c1c07c40710810440c0d40c0030700926440780d08030b80055a0303803070801c0300c0d000f07442e08101c0c4544180e1005550483c0714045c5814000060400c03080104401800000a400803090750305440952003c0c030344208100fa80003001c1c0212411042181600041c0b6406001c200c01a060210b4000c0d080d10500b1591a203203401c0d5048203c52016806130180900d20014a1320 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 717364937 1250 717363687 717363719
    0xc0b07020111030a0c06140106021c050408070305060603120310091806050a020306030f010c0215062803120c15020309010b04050c0d0e01020a1b0c080a0317060d0c 72
    0x40c500140440b440424051455008200c0740300483c80311200303101000706901610046584003045040d607540b5001c00a0754070000c5a407040341e0705400700d0800b402c0600c42c0042d82d00910300c91044804080d42e0b42403d940710442075503a14001d0140d2140c5809204620301143e024000c5032102e0140145411600c1000301900040c8071030b54200d07502080c011500a019150003850345440040c0d490034100c040600d0702042e0645d1481356410075510402c5e450300403c0b900340140ca10041e60649580b090001074242a405412044122100d0010180c1110440851090741e10494a400c2981d42821003503409a01c074100040002c5c00b0682028401d00064010f190081841320020950720300d140b00050503100c00b20f80b080e100c098042113144040d1290300079020b60b0449039008510381134003000c006044c0d6003490030700f800e1542d980144d4002c2040c2c0d11039007801003c0c020283e034891051860020103103802031419010a16411000c07031100d107004078005139a07661060f03826880502d083c860501322495 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 717366187 1250 717364937 717364939
    0x30c03020a05030d0c020c121f14070309120212040b0732010f050411090601090801051608071106010311010e0402040e09060c040e1b0c03190206090a0c0b0702 70
    0x4041030340001802c2040500078010792200003090306404a50000d10f0301100b05800c610800401c0c05504801e1000f0070a000703403401d458204500c1a1f0042c044001410740321045202da06444010086425413592010502501c112003403900c0a0b42c450080b41d60300c851034031807501c5a108020800c080c081d00c01c010134102e80724544402c0c00e09032041e00702241c0c2d80407204e4841410140d00041051100a1088424404101d11b04200b0303420151030f113100b2104402e1466004084903c08548a40c1c091400480180211170081c409403405540010401704000100c0303011940c5080820081c5000c1c0403803411a02c0b0000c014103c80e8615107401615075403003240c15060044440800000c0d8413580010005400b00030000406c90402c06413241c03400c9002082c25182842c03d00080c010200101040c9030071005404c0f00440026000902d11014071072804803e005200c000b8007207141c1160300684000218554007900c003d0358030001400c0e01d800901c90018400000c0c400c0a1110907440d001034054540 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 717367437 1250 717366187 717366193
    0x90f0521071a19150510020d0206010b16021306140604051305060f2d030d020d12110c01151707030f0c0503010203010618060306030305090103180204020d060617060a03030c0302 78
    0x10f900c0c44a604691001e41d681c4036000c0f40074020b1159003041700000d40c00400713a02c01000a644000002174071001d06000313800c0381e0a80040c81070303a5045113900705002950014410344c402003074021504c006000c280700c0d8500c0602c00080790038040c541002030303d0032100046d080c241e0360505888d040008200003400070b54030a0700454062459268001040101c0c10020140b42038444220381003a02c042c1c1e00480c00d4440c0c0e00558501c2e04169001c62a0301c07130082a803c0c582c4521006000c400040d22805a071881603a2010a0805d00c0c400705400005d1155041780c0705030303c2c040d161a1480f52580c001d080070100da9000b040100005680090f0902c002070142542200d0641c03103a0000b42a07078000c0e8881030000b10104410300400f0701800300f04000f08500c1c1010000301d40740d80e07805401c40c018040701505050b5920300c005c414071400305003160003a42c0100219610301144544200428082c02054001100c40400754100d45000c0f50940c0198002041510003074a169000c86e010303c030300d000c1142140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 717368687 1250 717367437 717367471
    0x32a030f06070c020108010e15130f020f0406080702010605060f0f0f030f060102071418090102280e0d33020c010603030e0d0c0902030901090f0521071a 67
    0x100c424040c0c18003901c00c6950f0035650840900004001c0740041e080800e8180d90201806501c0f07044032541c0c030030032200b035410040f10f8041c01d9200c00144504a281d0001070b00006200d80c00140c1000100b098a2386070321903807071a45500600300e013202c076240986034015100b0002d81450a20b0540034000713060594038260b140007400d54030b001054106507080b0780d150074080f061100c190b8041c442d0002130001401c65800d1103501314005240d8a0400142c2c3c1416020030740410f011940c04c0d0110303900b035564444041349182c40d400c1c07210001c2442e444643e0024001d500039030000d14084280d600610f0b0048142c4410b12004010928401121401e01c421000c0e001c030002c241c0100c500140070340071000c0340006140c510710b040140801140e1560b85120b91042041d5400141038074008009607015000b00580700c3c0c0c0c400d2541401080100000f4240c2c8050540c0c5c241003020000d080b0150b01a0b01c1c811001d010340d04492844203002c1c100b070091009003042c21410000e120b032030304c081c2d0020010130120b5100f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 717369937 1250 717368687 717368713
    0x2060a1b02121312060605040c081302101707020f01060603060501090e0703180c080d080c0d05091002040b04080c0f0102060c0a0c06022a03031b090d0605010b03040c05032a03 77
    0xb61104c264122491034a0700420400d5241c24480c00c00550540e0030040c11070324002c0d40e41d6485419920740244141450303400c41032500d10844010441b1410311035150303041d043c98440030755190220000724802d07608181001c2016480780c040ca108980068440003502030502c00d054100e10001014803080580d02c0c8145a0141d009800c2c1c19242130180480055440c280703c85941811003800300039007440120401d00c600006910300320740201c40174400004440e101c0c0d000032818412403601030700d4040d0001c1408541c0458000051003120707902e00c2119880b460210510502e201c219403070f5030161300110b001408240c0500000e003000c0e200b914000058070702940e0303200c0480e0812201c90713041052015040942202a4121948a1005000035401d515042c2030034102c0b0581c00c070f689451400d0100301c200351512480c030b601c1207050340054103000940e12440c42d1421904205e4041e1140221010005114100880d541d41b0070021811445c03c8404818507003201c1c103604c0c80c05550144100c25020902d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 717371187 1250 717369937 717369959
    0xe0105030405030c0607090807050405010f03140a05120a030e1912051309061e150516080309060f0112210c05060a0c121103010512150702060a1b021213 67
    0x7140e040c0340c94107c40c240c20000c41074940f5205030007040c01680792100511a4014200c401022a40e11040080000b54101ca0f100d0510160490040c0f1512a06d400c4500e0381c4070300806083c0045103940c00300100b05015100b1541c40301502c1c148605013a0a04000e03010940c02180d80c099814241419854498a0f1052a541003e1070b800341950940d11002441b454201c1c1a01100201010618000e950b003041600050300907044038045c00c0c00000601c05d1b454a0b40403402e160100e030000302081d16490114600c03900c60310b08490404111560f040041a59200380000074901070300403c00c10301415030190009000da985a81d64424040703061044000610204400c40c030800304201c0210300d4034a8441d020f4148035000d4076011020342044001184100c0d2403003520704491040301c040d580f9640045019041c0f15507250152000303d4154100812650000340c900e00640c0e106001b0000500101902d03612000315050810050300850400244000000043d12903c2c00c01800115025900c01000310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 717372437 1250 717371187 717371191
    0x105120c0a09080f01060f080105060a1404060302060c010b010f0203270109051f0305091225050303280504110904051204230a03030906080405030918061f0e0105030405030c06 77
    0xc00d42c0d1901e03018442c00c403007d1f01c40703c0100300c240024040c03030501000003a003014041c003070400c201d41d012400c1c4805507a99000040116006000640d80d00d5203100030502910326a085035010440a072001e804080c40002290100c0307029100703201600e030900f10070340500706848440c1410854543c00210b915511041041105008030ba500d9005034050340010342514030080407440141c000c240040320641e03d0f6000c88001441110262401c468010203417500710003901d0019082d0700c808800c010400c44c1001c0d6032101e0f4094072401c2c1986403c80b000c060151501258001c20a028030300d00f1044a0910500e000c2c0c0046c4200c099a03640ca11810907a411501310341e10145d080c0c00c9400c4a4070750311101d03e10391892500e094888202c081d046440217420242e862142004000e900000102840001e00c203075072050800408440301091018821082140d0988255104422182d860444054800300c80d0303054032001d0710b940c0e04048200c030055405400c0240151414082040034012842062000314 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 717373687 1250 717372437 717372463
    0xf092202040e010906050708011203030f020408070e07023d0e0f160807030c2303010528060501080112080c01090305040e090304050d060207140a0c090b0105120c0a0908 74
    0x1132120401e05100b4259107000e0019070501604000510002c01c0d540c1d5003c800c20b030142804110509200711840091059900a0b080b0b03004401c0041841c0b52034440c410f0140605508648003044248210342d0300d40e408800c48401e010603c2511016840075540e8980d4940b001500020990035080d60103052104403025119160000c40c041c1c1594014050114040c1c512000108043d60856882d400e610407980180e4001184070702600c00c4207003120381410703d4140050001c1c400c40c1001c41c11104002c51001300828028060700b00544103174007a120750000c8400580d10305409900c0c0414804480580850694168804101d101c030008002d01034203048a1003a602c9a646034a0b10032280c81024000e01a00190780040200b041140d549074085041640c00200059a8880d01c0c904050000e0079400c0072880c43c000d2010840034406e46400410840384892070602a0044840045516100d070024100b80c0694220100300051024000b80030f0000e154140b1a4500b512070100601d0b00c00c80318561 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 717374937 1250 717373687 717373691
    0x909050126031219230a0b030a0807050d2c061b0a08030f0c04060e10050408010c0c02150a0203030c180a0b19090503060a050702120403200f092202040e01 68
    0x213801040540d1107522408181c40c2c80c81c60f6107114002d070340303249000081c1c1030040294888200460360355080c003905060a81c08543c07507944100b40d1804680b2131248200c10004529074428004c88810140c41e80e003940a003001040c06c03014041c00400c003103604114084005178548541b411004002089010000fa0041d070680e9140e2034540841c0b2182c040007044003140e01c0c02840f080020b981c011030120920b107030840f0740c0d943d114043c100484050080b58801c940560030240c01d07081d1250018134081d0300d80d00070341e440c41180290415142c0e0ba8860803902c2401039208100003806048000e000c1d20801c0d4192a46c44009946023000500c0030945410065601c030340014078400c200d40c400601c0410710307420b0400c111114607180009450f0840101030341c0d1096165000224030600c240a41c2200004101855454035180c1c00d14140b40010b04003402140868803000c0040341c5804e440081106800600d5868282e071861044031031402c1003807641260422401040d80143c0da42e008020780360b0001000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 717376187 1250 717374937 717374971
    0x8010501210209070f120501060c11090c0d090c351f020304020d060c0203040e010f0b0412031407031205070e0102061807050d08070309090501260312 66
    0x808801c1215800c1241492000104280050b00e8030100e141e406516400d00b004007680c50324003551780c151b11919000e08070345028000709050b600003004c0c00d00b140c000d103105482082c80005014800c2003d950301d10201d4814403078844010395130b400861850384500003503c10960b88a10880d8019400c40350350380b5908202801e40300c05134406100c0c04034260726034020946024180002104012003942c0c242640340c0000006081d034803180303400880c150740041d04200490441300025103d4000c0d0060700c1c0030000c504000500e040214400c00c0c1500c242e12000d500d400d207400300b00340d091540b2080480900000084000301c0046140180c60b400b8040e40301c0100c0c0c483c0380091042152002400d0b041804004000020540d9000036442d9006403004440d01e050006403100c107203480d90030f51040380d2082c40364554404005000000c1d00c20203210b0f0f00c0c0e4101142d00c80599a00b500d0007405096101e102c03101c0c0000f0217100c0000c10400001807442038a1031715000c0700790210030110440f02c400b08180d807400c07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 717377437 1250 717376187 717376199
    0x406051b042c040b090f0703080915130b03010819020f22021c0608030316050915070f051e101505190821120a060e040b0618042f04020408010501 64
    0xc1134040c1b00e4004d4000c0c024a07402c603076484034203000b41e400880c05030f010b00c0020700c41c180c5030604485011501d1040000200d5440e003007100715038002d0190024070300460421a078000c2c0c2055030b0039182c0364001c10040c0c14020400c00d2090000241c204a152125842d071051181e001c0c610041c10080d104c03d03145c0082075000520442500d119030700000082d0320400c1005a90b0a540e02000911242464015510145000091002030001114000c0d44100080d00000c10804030a07242d007103445101500c80409202e14041d040c1140c07070802d40f4041d0402da2030000340000c0b43e4000100d484400340340b404d80030748900108a0181c07c11804244900c014078050007420310410003050a0404500301e040008100d26000c0513a000301c8415600c0c050311a000300d9028211074100c840508408540c0301c1551a041c10b1100380c0071400d98140b801011113806a100c14040c55200a00c550780000d803464034251001032800902e0b1449802c6034802845205403449c075a201c0c00140300920916001048550400c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 717378687 1250 717377437 717377443
    0x60a180218060f0607030203160305090301021305180105030d12150e2a0a051606090b0a1401030f020918070801021c0204080a1511030c030406051b042c040b09 70
    0xa10b034188201e90174403a51002030b6000003290000031484402032001c1d01640381c2a42c1c0341c0a059074599144d4008192803400d04403c4200e00100d61b400c40e09001c0f2078043c4388240c10b0070002801a075030541c110110300d03601c0328010b9a5a0341c0d103282c5d01c6170000f1903016050b0703800715140464000a00c008043d0040c010118000c14015000c0441d40e81100700c0340c2a101039100c2035108829192050080100f404814980b0006204a940e5004038050021f205580b825042107501101e01c19001403408801150343d902c40c441584c10b0780d82c0f20a1800303841c07202d6001c000003c41d00422508603111141519009010b09000c070740c0080014600143c0c894081100d40104000a629150042c0344140700800c88410005599040d190f044241c50b0101d218200002000c0c10b805455016448000400e11a0840d0300030001c0d4030541c005e003c00c004907110001508030381c100440703480c030000d0b0041c0320a02070028010188109110f280c0b800303951203040842110903510080b1003e450b000003100401c50002024 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 717379937 1250 717378687 717378709
    0x50d05070b18030a0b070f020d1d041113150f09031e140102130602010b30010c09030b0106020105100b0a0302070f0f0203010c0503101a0405030f01060602071205060a18021806 77
    0x24000341c1101600808020107149401844412840c060305c0a503400d5200cbe58012441d07054900c00040d6075001c140207c8074600b40306d01c14090b0403941d603062101c1c43d41c4246000d460001c840e544035442030b840c41e02d1340a81c9401c1c001250345040c40703d564000000c2e44d6040481c0610f02007200260311030880391041013501d0fa650340b2400a40e4105803208180360344202c4240801070550145100c400c5483d0300d11207042d000314181840b103600c1e042d8240000c980100c4142c044070310400e8038080c560b888400480c00c1e5041680da4aa080303054000c1070061426600c05810700c1c000a20f001820100c0c540c0b81c00b010140706040640788000c00b40c1c103080c2982000c2c000d00150550034149039195041800c8400080540c034800c1000458110701303034071020700546040b50010700d00101280e40100e00b1045450003086548614400b42c860100002914128a040c5002168114003c1c0c500c941e6800390b02e1001d440444480c12101101030f88a000503528120050005158551480e059140881c144000c1c8419 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 717381187 1250 717379937 717379967
    0xa06091410090216060507051908160e130905100617070e07120b041112270309090402040b060301030503030a18020f1c080408030a0207050d05070b18030a0b07 70
    0x10844c070083c41359580581c80c441544100000750703940e5501800c5896001c2c034154030140e0450441e9400c1815030110304640640a0841c6140141e020b107a0160b900d040014a1a600100d070380d07184603d03ca42035400440300364040c00a0f200000c2c440c0740100b0440d9242d804c40c904101026a803081200f00c20080207016110000e90019107041c1150b002d02007031206000e080d03032107489044100c41515160030004907461b10b9403170315450b540041c41031040c0c40c00803210503e050810950341170175000e1003400d411400170820701540c5402c241fa402d01c0050304009006a030402d88607480030101d602c8807001940294019400786842f030416540007015628200d42c0ca00390f5200008074070025a68440d03030990001c1d0103c5601c8180b85400104036007081003079370084c0c200040400d000481040c080010121601c007070742038945036905d940401c41142e202c00c00c050305d60350142d00305001040c0d41000508140e42c800c6c480031029290080000d180280c00303042100c0181681c002c0c001c001d50001018001d002d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 717382437 1250 717381187 717381191
    0xf060b03100519050d0f0302060702010506010f0309060e060c0c0d0c0b0112031b03090504060b16120908032101050108041205160b040506010e060108010e0c030a0609141009 76
    0x1481d03121550362140c07500407280700b007403040c440c2540800b080d8100401040b020348031181280407410041c00c01404084160094040d0b031000448061040c4206031007010141c40390602007502c0c1c1c0b002c40040c07155160803151203507100c030f01c0e038103201781080360f5442840d910000903501c100520842d410803503411110403d000c40f07540c040380000c0c503e20965064500044100001c0d03058ad0400f2034584800b00301000351048200215002c0c1940462440d0565005a07030602000d03558460341e441500c074a620003880c0e00d89442001e80011000001204c01c1c42d981e1410140b100d40b0307500c40c03a0869000040280d962080c4024408800720b28008403801441e003400e181c680c0d40382c03d481300480b032070442c491441001400036005800052018012600b00d80020b2261a41d18140c80d0040e41da031002c1c05140510101107002482541c420041681a034107521030102451710381c1c00d4200002d400282c60018211b40f01d00000c40d80c00d01c14420710611300c80205407182030b410203031303100780b8614030030342246070072038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 717383687 1250 717382437 717382441
    0x915130603141c0905040216020d0c1a04080a060e0a0503031014100203071218090515042c070b0c03191409010813020a060c03020606030706080c07030306080f010f060b03 75
    0xd4020321100221792003075a002d03980c0c845400701c114118850480082d4010042c807803103004c1c080070305101c80550320205030a4a0300b0022699031035803030245200d500e440d6030141405d440015450f81201c09400e01342000c46011440c9655001d046810464088181c4000307003800300264481d03058040340d9818103550a4100c089503507002902e03482a80c0000e48250882007e601e0454812030303201000800300002100355a481d00c144802401c82034400140c20102e40c11205404d240c00c1c4541b140380c4144941c403c600d00c18054203602c003030010002e0310303409005602c80010286002d034020300d00d0743d14450141d0340e20103042180c0e921540210740d41004001054804113484000142211000f41090803d06c04503500c16580c2c0d2491240b02e08000d400c03c402c000d00041305600030883e45281407194003501c9840c1c0d00c0c0340034159950b840d4425030001405440100f05040208002031030414040e1a001c1042d580301d400086c03900c0c5000382d514107240c0d500c1c1044c100042c150b1042c100a0140002620310314 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 717384937 1250 717383687 717383743
    0xf0106080a09051f0b03010b04020f0912070b07121d090a0b060403060921050306030a0305030910050f0702070906081c020f0703030c020a14091513060314 68
    0x1002414403210740e80c0c85000006000007000b130a00e15400c040207000d4480d00654029024003e0040094025030030011000c42c21f2510780240c6402c4803a00342164103000c111000c200d4582038080044215004d500d00c0030500781303d81002801924003822050100044001c8020710a00e880c80200050008141a0400580d82d80701825001605250301080100050001030300c075201b1503100512552820766060308000340c4691403c48181c2099000300c0700c81490b501900e25100c1103d45daa810f4019140b0000001c0c000c0c0f0141d80c0298040742112216a000c1002030101c0300b056070b0001d5545e076018200811554100194400780c041d02c2030030302150303142c250f006503541a0320b002048408009a104861248200031481d50342d1403c008032054159282005003030031125035020303409144007541c049600c40451980c04981c6d40080c010301426038985251011034102d02188c2907006001940350384020500c0d015010145008203245a40c0031081c82002c0e2401c8000322024030000079002c420040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 717386187 1250 717384937 717384947
    0x110a091812050c0a080306120304030c03050c01020f0c0d0c032a1a0702120f0d1701060c0f060f0e0a030e1c1a04051c020d121a01050708040801060e0a050f0106 70
    0x826036110142c6500c03907c606000510140001c0300441c41844081030000c14050303a6020501145c0c000c1c1c043e00c401c541110012030f21002c003980e1030103040e801100740c0181c42c18030242d030780d8055010340f051004241d12076a0710349002e810640fa5840c5092940300d4848803030002c00b400c0b0010506130942c00301c054040340841406000f200c5c0082c4c070421041b0091300e0750b12020702114a400c04940184c940100c601007001d400550320300c010030303e000e425000101e11113001d40002c0102c242c1091814200740015520720003c0d050f910301c00481c0d10341350703406419170200030010310546502c240c0f01d6100f10300142060282400c80d407001c0c04400138100e0002008620301035120100c01952141c444001d6030390741000d515101141c905c00c0e1860f40039190580c2040d601140101d4104d00541c0c0b10480c403c0341810303100075103044054100b55a0b1303020300700c605103602450081c8039082c0300e1751500b0b00b041c1e601e007010b03400c44020794480900b04080004001c01289188181644060040802c0ca240d5060250040c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 717387437 1250 717386187 717386203
    0x180b04151404020d1407030b0a060519020a05071503050c03060603060d240b10030c0509010c03031e050711030403050303010e061f050c12090d110a091812050c 70
    0x503a00000d042030182501e0b9038045030051650500284019050800e41e142e80304da003100c030b40001a01e004c05000c518076002c0e849008440503641e5080c104001c00d50000440c7e04490146001c1d440790f00034400c001407040c001640280000804081801d20880c405400c7d00c60042c07001d40007420030004c000d06903031414180c0f504024103445a5945098510745882a4001000f04d940e804000e4050b10300100043c2e00913448224050b40c034081418546001a000d4688444580c00824418802280154131900c5594001c070300070b19012a9215042c00321400c0d03840d0300200100386544860410005a03001050410b41280d00002585464a15192107440c0c2c0810f0182108031440740d4041265603070b0b5902e004264800780c04540c2d00c031003c8a00068120b030b0102001112501441d07088152510300b10098071885c04000c0c1c0350301c3ca45a050341c0c46e2084103010010300c50317009521100102d40c1c40d03a10720890108645031464101c0814260400440e4041d03119014020003000b048030003100d07580828144 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 717388687 1250 717387437 717387449
    0x40510020703051215040f05070806040b180c0409230601030506011202030906060f100e06071a01060507020f060a0e0f0303161a01060903020a12060f06180b0415 71
    0x181c60324498039040300ca03485928800b030f000c02130503024040c0e200b0041a4460b0b4440c02120700704400310140c91202c0c15180c0c200c580034007044400340003606508040d0003240e89000000c2050140742b442c0d044000d01e0107000e94014103032500104081c0090380d0540304080e0281c6452210003280c510120903203032102002001c1d00d0401d034540002c0780199000d800921011040c81400b9503c82ca0807810043c2d03605011180d0794460101950300000b181080803a000f5004250341e80d54225000080500040340c0c4403a10448110941d140030b02c2a5010311819076010304855540d2960314100f600400c0319402800f800c86200c0c450411042c1209a041000c68600000c2500c04540c40c55030100080d056002d0b100600407008442d0301c4280c00c0200f56040c15650320101c44003001141d8940608883e18002404002c0d0814030001c0107100080307400f0010030086100302c0d0007180104440c500d0320281c5d402540104000760342130301002d0340d0b0b280a000f80710780c03143c0c240c404000c0c11240c11701259035800c842c8903030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 717389937 1250 717388687 717388691
    0x10507050d210207030203090406060e0d06022107080f0f10060e0a030605070e1806010c02061c0c05032d060609060c010c05040509090606011403061207151106040510 73
    0xb0205001100191504a8041100854545106040282d03c991056006d0380c817030341c5001004182103018522001e10703054050407008803841c450b0785e03800096210502d0960701c6400202401200103050403041d2140040e40d4a4400500300030354036101a4001a24103891100305004001482c0340c813011000071203405281c064044203099002c00e0010440e90800307000141000104110f40b900311083c5140300700c0c2980c602d070138164005c00742c14001209496240c000340b54003175214050701c0c02001401c4807460402004000003140b04025085543c060702c2007021030400310410000c0203140700c41c0c00e103081c17280540340130300d4200714401c04030418000e00003846001e001c00c02494540b1400c06075940400d070b9038020491b010404401800f1a00103103e010700c625003040001c3e05034200850403038042d800c1a110388582c200311890010540d04002c1c041904200180c0750311040c060b041114100928880d100e510000356041d00c01004905250004101d40d8004014400021000940c966602403d0100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 717391187 1250 717389937 717389957
    0x6050a060e0a3602090109023f100b03280c020c060307030609020309030c0c12030702130e15041b03050307120201060b1b0d0827070504110c01050105010507050d 71
    0x7400f08111001101075000802900081941502a4000c2c1560940030340401808010712101d810f01e85000810f2800c200c80d10200514610555100306801294035091b0400e015111f03038041c48242c00883e08040d52241044400170390741560100080758240303404051120200c1c0e0720001c2c1d03544141094950042c2d80000010311054400d03400301020340720b210010741d03807401d042c40529620f0308800c02003a560700400ca0b11561619100d45d0a80d4a01082001703182030882c40c0c3c08000840700b01d005034904003a11415000c004100500c0300308102110044821880d08090520382920007000001c4038800007169402d00201e0800401e64a0095100d0000500c51b468464100d016098641c000608100045181451a401c1554135040c01e840d01c01280d00110406400f01c0300480143c80e00c0e00c800000074111406c0b4106164245a1144440d0895800a6981020a04440c4400c58a01e0142000315443c203001c1420b000301030040009203006404e10000742c40d03407510350200410030710500044440e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 717392437 1250 717391187 717391271
    0xf03130312062417010b18090435091315080a05120f03060f031204060c05060f070e061b0304090915060f170a06050a060e0a 55
    0x41c544a00201c45009100300d60b6220346a00d880701202082003d1800742c1c40e00025014410a0901350392000c01d00b00d244c1036444c1c04140003c543c400651003140c0460f42c3e80c0d02e12151160421680500c2c0f18400080c481c101c03030340c40c48455418200481180762210f50b00c4da01c1d403020302015181003040842d10380d91481d82c00c020050007058100031f5450034040822000944c00710214035500424020070a07103443e2380c0401d01040651050110010b030744c18040c808150941449107600f00c0c2000d01804484105908140000054000d0b902040c00103070083c40c0388041000512499400c036403222a030100c07500746008054403c4480d43c80c154018540450b00f0030704440200e8179100346491450960756125211900100a0442403006450b052682c03071b0f86514202c041d1091700121040303500f013030383d2080c00c0035403030b51007140122568100c40c4121a038078408621184200c500078000e001c40000c2252810001c900c048900800089000d0711b030110080c50110303002d0100413414080c48880c5081d0709055 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 717393687 1250 717392437 717392447
    0xd170114040f0c02010504050d051201060e0103021b0f010609050c0f07051e060604140402012304050a0f051503070903080306060421061107032c0613030b0a020f031303 74
    0x2c0b40350026824024200324541c2c06501580c01503020f84280c54041030741035001e4505100d046180c014160500c401005103920802c2c0314441590305150161038034a000300203d803c2e00f18001d141000750482030404003500c000344940801415441000c0c0030714640889002d02500031800d41c0f04020000003880707403c11a0a12103c800d02c1d00600e89900c031042425030960f518a4115086800741d49094100709140d001e001d15140304a42c1659084d101c00d0740c00412280c6205c40c03041c031442c0d20700309100c003007070307075607035440740718042c204802c04030510625180821201980b00303041b00c000040d0410a00c43c0540c4e019140b41c050729040001c0c240c1d01d4680300e000c00e81d9072081d07900041ca02e0b4040f00d00364841c41050b0055440e00e500442d8280000104c030f0030500c041e4441c0190040104400f000034040e01d940c2104401e40100100350202c041c1340c0820042001a40b2000d0903440c1c1400c0c001d414000c0218180e00507811041d030500440c182240015040c92902c005000203040050071020315007014811 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 717394937 1250 717393687 717393701
    0x20609060c06010e0a090809010c060b18061f020a0f020d020d0b0405010c02010507120e0a083c07140703080408030a030506030309030705150906030f0106020d17011404 74
    0x50320240e9500700440d9056200c40c400c3c082d00901501c0d20340800c0c00e0038004d00034045981c0c1c10000c020300d400c03c54001514000440d00f0304a40316515100408402e56400a001000c100345801ca18610b19046041041030084100741c04510040b03d00c0a400d426070003d2240d2041d64025080c456a0895000082a242500c10700070f40c400b0200c8030f40d0f020040c0080303c2d02d016503c240020b0122000c614810ba00361802241c8482c00240e80043e1000c03803081c2500054400c400440541d203240c560b42e1680344442c1c1c005260070010514914050a065880b8400400001c2d0700340d621416583c0d04103809030b4a803280103005001941c0c08044904003103814040f4070011680411581d82d5030f99214141a00e9401c1540c076000400e140500040244c100481111600072001b0040d1800c0c2e400c2c2010401d001040104240600d2020300030f4543c3d985a990040d402103203c5072400b0001d625101000346007c050b01d0901c800c120101d44c0410501d075103e80c07540d064030000b425030f181c20740600020400500038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 717396187 1250 717394937 717394939
    0x90f06031a011202130e030f040501030e0a08030a180f0b040c09091a18010f0c0212041422090f060e16170a060204090b01080106080108100c170907080607091809020609 74
    0x100023141d108040681d40140100c80c0207880030b20080c9000504203440d800c2d041c0014041020810001c3c800d2881d42d0b201800c4c1249407a12151040c0407034039162140c01e101c1c00d04903040e0780d103035041c0310078460080035040040920420510441c5121381d1102d030a411a450a4525082000003081e441e8940f212818002500d5000800c4071417400c44146019083d00c0300194094002e0b030140d444100c07226001c950a4400380b0506422041052061040d0b120304100c0d9640c02541e50300342001c4004080c021204003501801051251700410304159003190285405041140d01515240b4481ca92081442c02210002104c00d10240d00e000d004a040c1403101c44010040c51001a003c108a0080c0d4040c110070030080c0d84495041e0380302d100c10ba400920070b000b503820a52141d5800028030030203800c660100d4019285c900d29540c00080300303003051041903412052a1b0026042031002240401c4510f51007081468000c04407441c0508880d2500d1110300e441d01d4598407140020155280c030000c0719030038a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 717397437 1250 717396187 717396193
    0x809040f150f090209030303041b050d0b0f0c030123030c10031a0301021c0c05070218191814161d060d0809010c020a090f06031a011202130e 62
    0x20506000305501600781c0034041ca204140900820126014030945000707850260042d4655115500c1e003402d40348554809203010b10406030086456124007110303080e000d1082140c46060f0400c0200028035000040401c51807407405d02c0108081c41d4500c0600c800b440b2040c0041d0341500c0c86801080c20b0901036159560880011400700401c244c0c542d001d907c00304e4000c3c0b1000c105070f211808044c00d0f0f11a2012f448440400b07059000303071401280c0d014805020003030408a25080700766001c1842c10074081100301d03104401c1400c104100d06100c41103030712980080400c200d200ba9008284241074103640024000b01c0f641c446500c500e140403c2500c007104050108030900c030380e580342e50a511003100117101c42081c021030045201e074140490124a0280d128102909088918004460740d11180100741d034420b56810001034280c06500c91032000e9074000e60085a0ba9086040c0070070b208100341444c1002c1407240004110800002c2904c84840381e0440380303100b0212102e081030029084040d001401d2740 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 717398687 1250 717397437 717397451
    0x60f0708100e0c0702030c0a12020108090c040f0f1802300f010507020f0a020603280c05030108070f080709180c080a02010923040e0a06050405030a09170304030809040f 74
    0x1401a1000c4c0104903c200d048503000c0c2e100d0010301c040c10307070030344500c06080f0a1800d0080c01907000c2e210059219021074102ca012400c040f0019095440f92a034141100f0307902c045504101c2c813240030f01c2d1007282c1150b65041c1003030040d0340881c07080d002c50071911025516149072002c210491030090001d40d0070321803c2311101c403030301c0203028020042514100c0c0035100e803000ca02c010072004070701c0d200240d800404182c1141c1e540e21101c0244480c03007407481045a2103a031744504c45a1a4031415954a080d65191074480d0b0500c000c0e50b00d04101500101d100d1510400100400080003d02c0c5090b0ba00140c0085421813000e0468920032a80c1c0d200202201c0000344003142882000a003150814001d0b81c0350300c0c2060342c030250003040d4820150364004240004a6010803401c268201044003980131301284c480c03044984501c41251001d49046541b1b410000302c968920b41e015903104081d000c603000f000c40e0000c0802c0e100d5920311a03444024000302c0b010401845640d6103502000403d092000144030300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 717399937 1250 717398687 717398701
    0x15110c1023041430030406090b040f031209150f060b070f06050c03131101110a03050301050906010f0c0f170c1f060f0501110a05070b03090f060f0708100e 68
    0x502816041101c0e512420311132000d10080324400030542c0e0555030700401001900044001d150740020015100301e03868500020001c0d00031003100384154000c0d10702e81b814a07140d2a00400226850300907000032400e2070001d00101707070101079032070f603140c0503000005400c0c060b002440080e1015902ca404104404140346050040f8084d40404017482000200311664951303814810a010030f4400a180350006100c400001c0c402d26124402010141001400c891544540c0c40c41c15070002004c4002070004401000340e41020107d241d00048242822441d00340702c200c0c000c1440360607120140c4034601c142040e8080c4400c008054916420890344150b448800f4072100f40c1c0c03114640c40c170120b41030b104c031883d003034002d600e02c1003d0030707640c502100050081c6444c00441d0a0b060a0103040ba081c001c072101d07400052070400240e0024000401c41039164604040e5060401c00390089000341070f02308904002240c1c3c0d50b910010380c000440c1c2800a8151207030582048c1800d0b10b034004c5007000440c1400c0c4110 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 717401187 1250 717399937 717399953
    0x604050106050912250914070e0f22020a1e081b1c0603021309050726010c230f0301090203070e10090906140f04020901050706060315110c102304 64
    0x80da48204010f000c8050031948107c06017004880000015000e0a84800c1c80d01e801e1481c0c2d0140c1000034941c011868803800c441401c000e40084419220ba400251070002980200c549400311514004c42c5048011550f0f001d000383c0d0000300441481030741c1c1050a140b0b1304070358007076803048001e02c41d4032100d40303d550b9a0f04004000e18001a4072846c208034400c1d0156403075010303d1020030390103000742410628168010341ca0030310081001400318510442082c0c2d110007482041041080d941e9070b203003102a10014421040c40034082d0024010f010010394040985040c204c80c115400050016981d540c0d011044885050000da0700343e0202c410401d801d4020342c000210380982d240443d081000729036a41039003010f0301c2485003185c0c00500c03000001c0407529260707028002414040c18880d1402080c0d82c0d0362000c80d1829001104c040e030a105e41d85031070703204e6032042a14216030719408501c0d004101e203020703030b03100d0902032000c03420380e1164207039100803d008030758030b00c0c840c8003a11900c26400c1c54500201c3c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 717402437 1250 717401187 717401189
    0x30a17030f06091506180607060b2404030314160302150c0903060402090421020a03030c033e16110607080409020d11040e040605060405010605091225 66
    0x2200c00901c0000c606545880358206006140d0180301080301c031900d00603c025500b12441c00110840e0007641e0048544440c802804014803607400003c201200d0802c01c01685010042d00140080028040c0407011030312080390180c0e0307090305200d5800c0300984d454228501c241e0a0024004401035511420142c0000b0000070800100c424040c80d0341d80c146c00c4140c2030103a0030403d0b0b815800580824003504011205a40180c0940b200b04034840205110b4151108800d02450059102000300024181e26205031541103070549805d0106c0b08051820301004c08220354601410143c07000035411503000a005001e00501c0701c02019100c00d44070380b40c00c40c880f000c10303401d0701c1300001c80b0198203144c94413004844c10242d000a50700d0a050604801800035041072000245e840e6a80008036015007011001d800206080408551903141c54a4240b0654502406480c011418100103101c4940c028007500d030b0b16035007942c840105281c1803c81d03610700140341248000c00240250660240603181c02d1900c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 717403687 1250 717402437 717402451
    0x7060b0108010b0a0c03080603010e010903121a0a05040b1807090f0e0f0f04050708100204051201110a140d0c0903120806060f28090503010608031e09030a1703 70
    0x194441c1ea840707140c00c50350312400c88030400240034524417400084c05030170880d40004001e4000546030700720801c0303076003110080d020950100391351911031490030800340100900c1e40c014042180c10004d8401c08142c40e1196070050910442d11000e4000990311160965007400300304030084403550412000c060f04815441c000e003050365081001c04aa0703e0001c9201e1802000d042c0c009a01681d0345010750420044081c1049907940115600050703610401c0044800e841800c02d8010303a00c17460282000110f1010201403170369a410304065203045e038070180640d8100f000609041804104601c000c2c1c0b00c910882e000e500341a071070022012041c0d41d0154562007a284036012800707034540c4162058500780c000300d0302558400b0003040850800038440020b040c41d0400662004001058101616403004d04d03994184001220820b0400103031409000d40802003080f40040d500e400d44c483c0411512018140c0120780325200025407000b02e890070000707017080d80c0d04081812098060b0561100c0d5079402650a070f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 717404937 1250 717403687 717403697
    0x10f05150f0a0309031205010e0a0513020310111b1b0607122015090d0905060d0b0a21050d0f021009030905130e07060806210c0607060b01 61
    0x80c414a91400040310241101d01d445641400c600746411009008600c0040701002011008409642501e00455010b48142842c0598905d070220141c001c40b80c1c02014151440041803030a0007613140880c403280003110040c0081410045408010381c03520030b841c0700c40c1e220607280c00185801e03080403400a0713290502c0c1025408961a080070004180641030010b000d00c0341600707000c01c45c02e0251105d1066010340881240034100d29000e000c3c100b40007030095041e180070600030820025414002d54114072100e06240200505060105145008403040501c03415030301c8295041c10380e0b8205603080104490055001d0511201c0c00311100440c00c01f02c2200d80d44200e003039031400540110040903482a03241d0003840121000c1d04090050000c0140503801d00a039810045040c1d16542002180a0034560005c104103030303c164080d02e4180641c0c00442049104030034009203613612108070500310300c6901c0006114000c058080c0c1007100154640d40e11450020345c000c200b00d4590840aa0048241c8035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 717406187 1250 717404937 717404959
    0x50d060b0301051305100b031204060c031707020c120a050a0c1802180112090512090916020c060a140a11100b030606040c031503080301241e0201090605010f05 70
    0x130b10805032010340d00052007034210481c0410038070140d40c8070760038441004003100c110104885040f40940d00582004000400c9601450141504800c504801c8444800f240a0351300d0a841c0003500d80303424102280c46501209100c682c40c5a0401c202c03500b00e82c1050583c4c50000f0705107803d04802da114800c8940266140e081d8403118403061007a2507a050038030092564003c6130340011150781e5100703400710007141d6031010700c100403a804010800c180301400b00e8250781c4061841c00c20203420030050000020b24a50003001000f2a80810400c501041c192101911035580340c50075034406107000000c0126030000300d054082d00d94420003030703030304400c1060664460980b03410079403040e6441c1481e9590140d1150300412140d05181e4050b10802c10700d4940041c2070072042c840c10140e44500e174000d41c0c1034140480180018003100e2481d07a054158040720705c0c1e0010030b91a01420b001111035440c10248040042a1003582c000e400007200207500c80c4d0100000e6841d412420f001001c1801054010482910 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 717407437 1250 717406187 717406201
    0x2a150c07050306090c030d12020d1b1206050d02060a1e03090c05010c020d0b0c0c19060b0307030b0705070c050d031d040207030e060901020a1203050f060904151104050d060b030105 79
    0x165035070b80301760090090300811898000946046039401030a584059082041704c2150300c440c841c804401000440f24200b00c95103076401010160841100294145000401c10496480711000000c0c00e5044c2e034950340f21079140c50140e8031140c00907410340b02d5400441a000b08264554085001070703210303003e03440c0c2c0180c4460045601081801c3c009410482c00091440030030040c903000c0d0303842503081071060f2804080c03003203040c02c003268401d1020549620364803060400c800c601845d0064281640104030a45c6191034988078244090209000d000d40011542c09004206030000301504000d04a41d18450052030010900040e80d1510010050401150070891426008498940740c069490071607102c850307000c010159010751446c506521401040d42e0000d68002010350300d041a5840014032441d05805443c00782c80010901031080c00c68104000002d21074010b401c0458542220009540b0725101c5181d140b4030541d0400c56001d8909510841080030580009199000c01c4d002400541c41e044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 717408687 1250 717407437 717407443
    0x708010609150516050c0406060512060d120c0f140a060516020a0312060f0e09010b030102190c03092d050d020d0f03050409020d0c020f2a150c0705030609 68
    0x2c40c8000142c040115404080c4040c1c4000e00d841c0c0038500f582c0561901100207822a01c1940c4040d003c5200461010391080c00c100810b80e0190007039810710015400740d07450100000540281b10103100c1d480c0c24640c2030001403a5440005940302c001c07080c00864076280107a0341c218503001160b03c1802c00c40080e66421000724246e04404a5400500084200e550300380c0e800c503462201d4a04040d03503898001498008940c0080051104030683c800c0381c100056a9400d642580c4502030080e8010070188051003104c03e0b0340c2550307034500d240c2054030344261b2404440d03030242503100b90980380144801d4808101c041540058400e83c0d00e030302e401900c0d600d6045c8003907607480324801380d4405500706054003c51130b07100c201c1e000d0a1091410602d015158071004040303810042050200351b50702c0544611194040004034018000a0300600c0036040c05000941e10003d42c00101200c0b4148030074120341a200c0c080d02c2c0a4a00100d4a000d8540320401600c907514801032254510030300c208404191a50004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 717409937 1250 717408687 717408719
    0x6081f080d0c020402121003030210020a02030306041d2b090f0915080a0312050609060a090b040204120510050c0c1b0f0402120604150b03010e1e0708010609 69
    0x444003400707030441038000580b01e002c0c00742e006a030031a40801c40c501c842400f041c001c034429100740310001103840c2107060092a08080b140f024082510401c105080c0b1500007003030b01c0d4440c4c4121780c08603159803444402044c9115400b1001102c0c410340413408500e000d003140041144840141d00d04100c00d07440381c1113da010451280c1d2450802d14003060000039a15009680168040d01c104444580d44091051810704081c1007500003944004901600f4081c0e070041d10303008174048032880042e0628500081d02646103205100350103644250790429034480d5010340300200b841c14440c10652032641845902c60102001c1100007500e0000040c00c40d00204090790840000d10f8000c086000d010040c006680c2030762400c4039400100d10743d0840241d07990303000801000004425000543c2800800e11080d1500103000e0402041104814425402d17000140c070304603036400c0001c3c0d001c1e84580030116941151781d012009200c102c2002c005900303412054981c12110290743c3c0f19005503031550304d1541c000a03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 717411187 1250 717409937 717409949
    0x312020f07060e0f0609060108012a030e0c041104030c240503060f100201090c081b091905040b0114030606131d030408011a06040617040f0b0106081f 66
    0x1003486481c001c281039511822245100c81d0440c3e491005403070110740350001c02c803811038581d801038005000c02202030184220654450007482c48907150703441410103211250070050304055548030301c1086c514040102c0c89a20801034000c01619071a200b070036080d03a0290105840e1301090905c0050356408040905114004056000d914400d001038101c81d5580301500d5694041c8281e603501b540c650b2002840b02c690180e035000010750b94544c0c54500e002d980a640501c001c0e40200d141442e5207036200c06d8131003285108480c003400c50754851008001c800c552020302d0010624101c01c0004000c1098461070580304e0a000c031918191800f030402d0b944030401c031000d58220401e4003003210b01070050b812041c41c4810080141140890440e042c0d49103070015030000209a4551b02040111540c44185400c0084295001031429007020005080c000e01c0700d030b07501e1a08014400180c28041544450b0320508c0e4800701081d081d50b5a90300003444408290303071503000c100552242e00140e54411001d5422901 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 717412437 1250 717411187 717411217
    0x311030a09021f0c020d11150901021006050108011a0d06030507030c090209010e0603041a0405250506030411120d08010311010c0b070305060d0605130c05180f1801020c0a031202 78
    0x15030345c03e00c0342c0c140031404211421646180001710720b80d40d031020010849140320103c1c2c1c85841c070600080c81c20704010704a00c080c0b40ba1003402d00c5142d030320030542819a201c0401e900c080e00c400824254440c0b003007120f112107652403c2c034080b08120700400d0000c01c4034003486818000795222480c80d0102c0c85040d80850100d40d041c00003004901713002d00559442070040310010721841d240e02d2007201c1001c2c116400c07200c1e504138140d17020140403451846c01e00880c0354510740012030f06020118030b0341e110140c006440321010321128a00e0340c0ea4842641c0000041500b40ca404070b4503020b0144c0f0811082c0005c0b070f0028401005038611794451602d6124441d00302c848041d007034890305020740c010030000c0c00c3d541d000034a030041440440c159004190080001c140368000c402014184090032201d503400043c441c0e004500e03440464590030801c00d8110607406d4004800303481e400158102e0744400414071b48654004140380070404000b1800d4004203000e600d5858000005200e81012031213041c80c2e040b8028 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 717413687 1250 717412437 717412457
    0x4020a080d2a050d0804020405071d0607050106030f0b01031203091a07090b070c1401030c0237061a040b0a0308030c0903061006170f160311030a09021f 67
    0x407607001400d003845803402c0104070201425260b07241040c45403d070300310105d0003400078041142040d01c00caa5010b003051805104a0702e13244810440c02c01980107217031042101283d0501448003e501c00b000031548a03000c00f40151162401b48070b030030b40c240f005980142102d11441c078618060b00900440c1076020f1050034034240020b6904d031928401415900070024103060204040c01280010a400741c05a400d02c20001d1905a5040e0120f51b0070102c941058185400301c0400307900011000d24071105004555074140c0d05038000110348942c040300203480190501e000c0103000b81c0713500510001e0001451840380e48111001d100960f0030741c41020303800c0000e0394420008110040c1c007845e040301d03500440358509200040000e14004c010303100d15041c1c0b26141ca00f00b0034140c110403030b40c48107072314004098401d00e00280440d48164008040380d84141500200e258118800e90002c00388014042d06941c41b810300412040041c09645800c03800380341204032611000103c18003c41c04101255100d41c00a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 717414937 1250 717413687 717413717
    0x20105030403020f030c010902030610061b080f0703110c1503010b0f04050301020a05250f02150909040320160504020c031b010203071b02010e010806060c07030b04020a080d 76
    0x550008000382c04501a00491000081041c001032840390080800441c00007807a0042504140700a0401c0712000524481001072035041306500c102c0c034400e0f1202040204440c10004181e11a80742d20a01e00300f000075065040541000b058842011010b048681d44021030041c01844a07040a007a04d03001018001002180f200c0002004207011104040b4209599400481e080e604020014030226001107003440c2500b0181c0c0105e20301d5412144005500c000d15265448030403801304000c1e00540310044c5c410b00300f0310321101312001540d01400280c541d141909004006601074841244079004d02c5484070511240080c46489106182c02c074201c0a6243c4400c0100135800603042089500007882083c0900003041c4200f00010400f0002503940c0c6040c4400404100500d80b00c822440c3c000c408031000b41c0d0f40103045200c4001c082c203080d2419102c40c00003600714064485094001e200302c48010040111840c0d4082c0242d20940c0c103100d243e600c50421646075501d0344610000500c1c400096581 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 717416187 1250 717414937 717414947
    0x3160201180b0702210c06071418040b1f110c060d330e0a0204030f110a0812120a0b03062e0602011b030c050a030509120703120b0f0a030201 62
    0x10b100e0740100c80c0800403401180504005001c002c84c2d080c174012640014205c1d09224050b40042c240c034000401c480e01e094580f1f6036010301d6200c2da003099101e01d403900b010380b103e910012080b14002e20801e030a0000b040071800e903000d98866000054a580c3d03e0000b5640700003011811004024911400c000d03a1a04040041c446408004c408000e000d29502d6841c894002941c0f415080d0045089a5414009603040c0850040d10b11000c2c50320402040010440c10600a05243d601c40e1078030418003034000003c4c94048081c0c02080d461b0055501d41084205028010b0911403240403141a040d0f40e813804c064200c035001da80d040d405402c00740000784c008841c0746188041108203000300420f40d0030003144400300071264001c200541e5440b00a1005802c54130180b030951192460f06101c1c07004410030040007070246600610078540c0300c0010907003510301881050b04030b960011009403500c0c4141002060405000c40400e1814581064001343d4200500c0c40e940c42c3d24080c017158606451a801122 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 717417437 1250 717416187 717416191
    0x3180111030709031403040b13060e15030a1a03071d0a0905060705071b092406021209060f0a020a0b0f06011d0102010e011a041a030c040209010c0c0b03160201180b 72
    0x841b800300700000f10300000007074058419072002c41e0031400e0789030504401a210403902215180b00e1b144201c030080300040688102c992042c5880e001040101c50541200301302e03d44151802c0c4c0c107024ae088080b0340c2490760302d411354126603038070394085603500c541e0800740440d8400b01c070151090300440c00040099000f10003e14003144600c0599400358046200c4540212258000301c21194850030240c01240ea5244540310340484074100012032442c10350b000e9501c92031402a0146010046005107141d621201038034014501c0000d0035540e0314607400c0094503808940b034121082c0d500c200100f01d5412034048014451041038507804020300d83c1d040040444040c0700c896504540d200c04510414460078050651100102809401d0010141040005480c0303030f0501141703109401348503110240e900255880352254103580040c0c0c3d894011b80100c40c4204055000340c03038100c00c1000010141a0103004511440b0548402c030081044060100c2c2600d18080201e468000c450003544c0110b00f410883d51303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 717418687 1250 717417437 717417473
    0x1206060409020c01020703091706071b020a03050f0d090f03110d2001030b060a090308030705130b0315010908150a0f0603060b0a0510020604080706110318011103070903 74
    0x541003a40d5126020300343e07030000703150070b882d65000b1a10404040d004045a40581036849446440e100c840c40c510380d640300b008029804009120700154240b001051402d1000c0340c0107080b50000c3c9450341421030341ca2440d0a54081a0311500032101d500d00c0c843c501075029590000d40c02e41080d4035640701d200e18460700040030795101e002c00703480100181d80c44498118481c00080c42c0c0018426810000d02244c580680c0c1c0381c02030707004202c20007200e41d100c3c42d0041501d600c00792040d22501d42100441e80303070007500207a1140c0c0051800201d004007001c000380d845400c0189888000340100001111300b00f585100c0c0302c00a5012103148841c4003c1e040500d41c2c0900c00000000b200341c06224028184c501d50760083d140c80e981c80501c40c18505000052402402c41503a0340e084040798200000c0d0781d8840108003400d501c1c1c005c03840c00304100d0940c03c00040140300e8040940c99080c400c0292907004ac1e44100c81c0c6466180000d802080448101a01c2c4260055200c00720500e00e07649400c1800e0090110203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 717419937 1250 717418687 717418699
    0x80a0b0f0406180501090213051201090f1a0618150d0c0b360111160b1902060c0a0f090e0109020301051914060c0f07060f02070f0b1206 60
    0x40c04250311a44a094000c00030411080e10314101258004122803061304903143c0103004115071a410f08800368800110744080d070b98411440c3d120440c140c0103012024004021300c100490020621101752071074014a40c0c50840f403090340e240c190030015000509001c005902d1004e0300003400c6141132602901e049000506020314801741c6a0350072019801c981c0100303048020225028800035241d9030120300003208407110030201355a09055000b242c1101c5a4181080540348174071034840001c3c000711100b29850311210400790340b190380c584103a030010400d000c0c00c1080050540e80d0f1b00d00c0024400c0c0629402c4d40c0981c54070881c91400c4a01405030103804003440b46014000505161440c0214000d00c1c15110040e142d5040204003c038007512122441040d0040310070501030051001540d0445120449410355030b0084407540c00c1c20003005411468050095201c00600720760043c4030034003031703201c01c2c1d09440d481074a0345182842d0132480d00840401e000148604280c0e4054164000d401c03a00c02012 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 717421187 1250 717419937 717419959
    0x10c02040c230c0f1501030204022808010302012a12091d0108010e0a0804181e050f13083007020a021f0509040507050c0a0c03170a080a0b 61
    0x2046070729400c40840c080300d0000000b442c10303080b041800512035035519413015000c11a444810402a0303030b81030001a2107681d000900040404401600d00d0305c902480300c1c05100860200c00107424000d0901c02a070104440d80310380040841c0500d00004008840d00b9000b5032000c20387c503a00403a0200d201d5036018491001400308a044203200025a040c0c00ca400703105042d810500c1040c00d44280600785059a4409140d00b000144d0207015181a1501442400307904e11118602030040c0c5010032207070070200c3c841d1a0f80d005081d03c58000b81d12442e0640800c0c030170340c0c942e0a00c07461038405642c00900400750501c075001007004070010003507203415003180e120782060020400d0000d1010903035030b1201603402240c88008609014072480707046c0941e21b0501c0aa20101d010103010392260302d4a00d441155aa40090201d038052010b0b541030055031000c139140e01050b490310f2281c01c41e00d0301080d14102c03071407007031403900815000480e031003030302903a88492040d2950344084003c0c0c40c025000540c00b000f0030301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 717422437 1250 717421187 717421217
    0x501060c23010f181202010608030a1809050a1a030313031502090909030d0614090712060e0106120f020306030d0c03170a0c1209080a050717121e06010c02040c 70
    0x25640c2440c035000307035100c1ca03c4810b2034002800b80e505c0c2000c0040d641820020814400040161240241e080c280040b010420b0410070010180a4104c040e40d14a880700340110710fa41507100d941c02c40711140d40040c441003608109556030180e605801d450101c1c07403100744001607a09103501a00d110520015013414a132074000303030400e481122110340a51000c40c101c40010040e01501c001003419014034840e000c40c1c1804205108002041141845004044050414126400600206a842c807030702d82558444000402d0144441082411241003d03600d8140103858400c680c0135000050080201242400041d240103d07031120640c14003200704907821310099804131440c410004400009885000c0c0340014016130980081502c03101d1818190340e00203400d200c121011060b281c01d160b0780b02d00352494141e00c0c0d0f0341c283e000382c00c203140089109a41c0380081d09540e405042c15240d00a520501805e4125a1031021601d5070b0000d07904060030fa025042550122080814501e0300134172000c5030704 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 717423687 1250 717422437 717422441
    0xc030611030603060a05090c0d080c011b0908071508040f06050c0a030e010c0804020415050316090e1605040203270c100c081801020a021905040501060c23010f 70
    0x911414180e0000400c1000c140380c01d00109074850a01c0004001c03c4c00c0030010140c0d03802841d80400d005202d600420401c1c001c9003010b55414118140003440b003d5102500c0c01d09101c0914a88804610701600c0170950102c00b0801c0d0041c1c2d890310709820601060280c040302c0c411005007055038072440040c0d52030042142e601800707103e034132038003402c903691440e0f038000800301c4039071110b1903040307901d03003140f140700594030141c00c5400540449000c200c00c4c6c1b51404c00300c034080c86a40403580c1445208600c176540d141701c03a2510100c2d41810000c100340050400c6541c0c0b10101c2c0c00c1c0809000320010400e00c401d00d440d90145401040c608850041222400940c17901c9454181c10761100d584130a401300001c0c948102c02c1c105c8007400386024085401d00d90741c3c00000e1702490005c00380c1c406150b80304d590564800c00c03401c041c203a0020541415400b84d000031310300d8040d1074010940a1070601001003401c9000346181d103103156103d03c060004905011a110400c40e85406811065480b09a2401440c0140c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 717424937 1250 717423687 717423701
    0x20c1009020a0f0b03010e0f04021c030e0a140901150504060c030302041805060405010b0c1005061c1a0c070804090939091b180f0e0f0601020a080a05070c0306 70
    0x134003c0309070f40e5410100107100c00700f4001c1c00708071006410420040141c46803201d07581100c141c10514040e0300704500e001d80e43c0a100020094101c1c212260002c2d2000c5e00d0004000880c0068808100b140d0f204c810902259000d070f8024070100f941040104003451040744d248100a000e40b400600300340e02d403401c203001c0e215a00d40307925030283c9540500c10b6518181c03103894014030321424094900301311600e41c0303511441c181c0c0750700d40003540c1d542c0010015100d018a052090b984591100e14608072031400c19814450b00350f400c0c0d10300000500280350102c900c421a0b02c1a074000075001c0c101840c0c400d410010700355000045614084001c00120004000003503015410170441807440490101440602a0b03800341e400f418125080c0361401d00000c4a0082c4032060849502c0c160025280c51440850000600d034404544454404000102da4041d01c45003400b60503841c40d140c00319101c004c01244d58011a200c060000f120030400481103034001e00060104c2481034210305025a42c9032110f10858000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 717426187 1250 717424937 717424949
    0x30a230402040b0301090b060409050a050709020318070e010510050d0906020408160f090203060a080604030518060913050a060f03050d02192d080a21020c1009020a0f 73
    0x1018148011494140074028081d40150001c1104240980701c0c00620b41c4094450750146070307103890217170900c082840b6042003540c01c02e00720350f202581c4540e401c00075401101c19882040800303024903035000020030207400311907461184d0300859080034200131008150003869428001f0030480480194007a000e071020081c0150401a140e40c0703401300c640d0030042c0e040120b510241c281310301400b00d0010291141c05541100400585a41d100b10104218034610740000c1054410801044201584a801040742e02c03000321100d440300c02144e0500000e0300a286200707070f200d00010548100080c1e40c0d03000d02c0d84194030440100301142d840d0480c1d21011400c1c0c0044e01c10780c00c10f102c186040ba404200740b40c00c004024000107802811915000100b416454800d0880041d000e1900c0c00b5149084407a4010303070300b00c41d8103540d401481d0405040c80f07890014481500021813807150200701d0b01c0c0700b030310018024480501441030985d5100f900900000c64100e030302c507a40d00c0c1c0202e14010030404602c00303044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 717427437 1250 717426187 717426251
    0x109021b0109051c020c2d03030706050a0c0302030405030d200d060f080c0d080309010b1e030f12072603090d03290d031403091b041a06030a 62
    0x40d5200c400748025510213201000c1d035002011401d06519010074584c9a0300040080050b10400112880030b41e030a034111690707062201056910610580e9449140102e0140300200b2030b10382c0fa2442502a4041102c0180942c0c00a000e24581d41e110354100109a8200e920400728906c03030a900351009800c901c04e0311580643d1050705001c8101150400341c00740807074200400d021110600041c0d92025000b4008100e140f020000c00c0c454171007500800d44808008100084050700c1603a04c1c00340d041e1641700b45110344960701d41c0404080e00828108000380035180054641040c071744aa1407130380d500500e001b08080b03c00720b0802d9101140c2000d50f0082d00c00303602400c20b03039440a0000701540c0c9007031400625018070040503500c46071400e40046501c50191900c6c3c0b1115220304040d2107007000004100001d40c2c00000704a080b5102288026604880d501ca9642d5041c4020a110450b8110801040c1c0206010095001842d107000610740c0406d01090102d404801e50b281140d015103200b001c00b403140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 717428687 1250 717427437 717427453
    0x90705060a0302222d0f06030b040b010f08060f010e18040506010e0115032c030a020111130603020705031c0902121c27140a0f0308030109021b010905 66
    0x92610306580424500340c1c0305016428200b00c1000d50300c4449800250740c41001400585282820503c030344010706282020180c1207646a6001c8d001d01140b5150a2207645410803264240d80600081c0201a40f56071b02d10b5019640c8509000510320103086442c140480002000410755901c6080b41c201151005003240505040c80c100e407070010306170400c108492284005028014903904001c130365035090314000c105030540000c40c0e05603410140101d81c120640d0909001c96840000090034100b1581c0e008000001d10107103852250302643d03104050202e880c48040000354440d402502080d8020400d81c1c3c90240c2e1290102c080d20001c02e080118291191614025882d000901d00410b034400005804644189002082c00543e4445a1402d0000c202c03501076039003030005800e4030224503100e8400c0c0301c2c0707803549030310040b600f80c0000040c4545403880010658207000c00010003160762250710a800e6900b003104c0500650443c5802d4941c080b812505070118032004d01800f40d01d20700400c06001303e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 717429937 1250 717428687 717428707
    0x10501180e030a0e01030903030b0913030905061305130b0612040507050f01080a0504081605061b0405063403050a0305060105090d0312092109080105060a060503090705060a0302 78
    0xc1c41c00007200329426001840f8001030f0942065a446000800346070008034a0300710700e400e4000703103e50347c02560031107500e500300801c80e1320342800c01c88064083d859481c00d143d83c9100300301003407103401510b0441c64001d01c000c200c1801c1c02100c480101072071620128075194800085039054001c41030076500e81e101c1205002c1404000e0103000003401098480e40c1080781501d002a000f44405810800d5069a03140020240100041615441c00d400c001000501c02c96040c0f29030b4907481542c0300071480c00007001c50440c00700c00000f01d8007110005021241000c58291000500d00924020b400b00381e40b2905002c881300c8500da80c4c408030f26200341c03940c03511450140001400c91ba401816541880020040015165940d80325451440e07410714280340401200d802c960060080c8807030040c042000080c0c000e0340c4545095010380380702e900b03980740403607142e8502266098481c144c8040390081b40c0d24109212940c480d100440d80541d0b050200c518a43c0d980020416079880454070303400007940845d0385500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 717431187 1250 717429937 717429941
    0x209061306081005090612011d01060e0f06180901151706130203061303050f0c06011502010204061d010c02090403050915090a090c1824030c080a0e030c01050118 71
    0x10f0381c24418094650902d00440e40107400a01000d10074502d042807080c03111000d40000803400b0030790401c3e00c7c5142c0000d400074080c1000d40540c1600c045200000342c60545004800c5200d010014013011070800c2076070000340c56150141408410303548545140c0d00325419051604014000704425039180b15560340c03003a05000000d081001c01141801c10000540d80001d9000c0d0040750707445908103900c040346002ea8052040e821350506401010403024051100490403a040768030100c2c0d01c002110754048100e08070301c510300a502c040b9a903510000901c403071495038140002810f043c0385070310a0268001451500089400b02c0016200080b6901c00b405c0000b0000c8040b08009011420075110100184074102c44d0302942513040da031112140d0205d80300c0d4800400082c144110340d0f054980340d042d4401800028100002d00c1541e1802c210a424400c0c41070858844c129541c052280d10f41c07044050142004800c0ca504603c400c1c401c0c2d10074440b00b841114000c0851003800f0140c00a00100041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 717432437 1250 717431187 717431191
    0x1b0304180b040b0d0605070c02090c04030b13080706050402060c0a0b180703051002071a01080a02011e0f0804021f0504171f02071b060507050609121c020906130608 72
    0x2c01182801c0b68800c01e500c0c1e401c0080b40060384410003203002c0e50740410803a802000034030081d51100c81c0e081408805400031000704240c80c02010054207540d150403500000040300d00c00100381c00c00411040300403c11641c410360b000b070310040c41546085070b1801c61300d15020301e0110981c0d440d40b0782014070002c0c2903109a0243c143c070007100a8244989542c03555929403058265007142981c00090400401110354100c0d880070030001c5201a05503103c003406556058880000c13404554100c240c0d40425450794258040182203640c0e100300342131009003c645d0401e010344102c0c0c0050304044426050340c0c048402c9c070501c0d8800c2e42c40760b80703e6180c00d4401c101c461440c00c0b00301b656001441e02c8202800c41c0c1341d1031120a01c0010300540d0701d04403440c0c403d100c10764288583c00700c03011241003c1a5142c0c030400400202c2c1c05001260000d858503a002a00d41941060301c0c2c0c0303440d10401a500000000b00d00040b04104070a400505051000010505561002148041003c0102c009105581c1c01c000b40799 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 717433687 1250 717432437 717432439
    0x506040b0307050109290f0c070b030c07020609010201090503031f0f0b160311100f051f12060605091003020a0b040e0406020c0309040903050405040f0509030f1b0304180b 75
    0x450010b2a02c00003801c00c5d0040d0140300c0c44071820300217400c0640408010580e0540c1e24034100c907911083d40d25104e405401c030b030380582110300940800048807803c0300156805041081440c500c3e01681c1e41c200304075a400305550505554a540e0103c02040e03003440514400e000e9a240c3c5100d04030300609a020200d02074001e4070070b00f020342d0070621203001d02c00d00395840740c1e40316011001044110304090700c550079030075102c041500c1440484a8010025044418404080e031030903c940c0c1c0743c00304010f8600c29403590124603a00c1643c3d041140440d003d880c0748459015000004000c0d80310804207000c4a822104107618003d0b43c0340c10030440c248880391000605d048100607042904081d0513070200007015001820050300414105030980091044500b0301000a000b00403170451032a0140068001d4070071944500e02d0080c42c180c40c1040c1d409000d00c0f807880314000e58503140030144041020307040200300401840e6905042580210108000c1c0064204500c1c200b01118209200307000344c0d00ba509880e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 717434937 1250 717433687 717433693
    0xc0c040212060904050a1407050103050114030606060a090b0d0902030c010f080606280903230c151b1c0f05071527050706020705090a0b060403150506040b03 69
    0x940c4580c0440c0070510303004501202d4054540d203484c00e1641c075011118001808151001b1101400300c180000c410040740d80a032001d22081e80e80e0030b003900604181d204000d801d90070280c00140c4c00e24110f401484040a00d007480e2000c2903c3c1c21540c03545820070b1500c01c0c0c41990710704120080d450200414540c507002440e14034109000c0f154008d05500018004500618020840040c0e5090b100900313005030712584003910a030fa5400380b00414101541c80300352040c400c49400408002d41c42d0b4940c40003a80201e00070f0001c50495014002029032915540900c408244030b00c2c0500d420550b03800c060f6100b100c0c0100170005507049805444210000d0711010b01c1050b03100d9400564004081c2c40c81030303400c21142c10700c03c004010305c80050b100204121a0100d034002158040f40d5480c0380d64541d4034000c004032207801c0d80316107090b650780f0410301a55901090501c00941c0070f03805a0011445284041c0581c1d040590f25652010140403d080e01e101042c0c45074200500342c10103101c2e140c50713060200c0003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 717436187 1250 717434937 717434947
    0x110d0f051f060f1b051e28060b0a030f170304030c0303150510091e0e01030f06090f08091309030503180f03040e07140a050904240305030c0c0402 64
    0x140300d44510700d441594184050086803030841e50048400e20041c041c441c5091100714494038285840b000000008084020000341034804d03201d001413080c07059510500c4c0c0254a00c000070031602e2500858a084801c01e446005881981c6c596080c590020b61003420700010092139860100d443d01c1910b407050020510500c10400426817044d0b06894603030f01400c0024504402e40c0010094050743d8000541040802c600e100005a2000a440480340d400040c420035840d038210140704800d4074440c20178101d09103001400031640240d9104c1e00ca61090f080000e442c440c3d50b541e402109071011050300c0303580020480c80018180340c000c401009003c00d41c10009401c0980c0d015100e800043d0040e140410702d11904101d10703500304443d641c92412001184c2d00c4640c4d460750030301450b008540a000140c200c1a4400440803a54203480300d00d6119122941400c0d0303100f0500c0000d0038800b41140301245400e100c0020407202c401c004000e140280090f40c0d40d17202411071a441c220322108401d0041d481044 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 717437437 1250 717436187 717436231
    0x40c0e0109060c05100f1d0c01030b030601080606060f04030c0b0a030e0102030f0c030a02070203011406010915120c052206020613210512070503060a05010507051b0103110d0f05 78
    0x2460510140c0c03c00c43c002540c86911407001e00815815107080080030600e04903100c7e0b80c000003900d040c04031090340c0500900b862142855112142881180082d60010010812919101020f0711184c06900502414140c1d039072289c13030682c40c0581c004000301c0d00004203000c0740c1d513041c0605000050f10717200070340c91401c0c40028119102c40080081e261030101101251036912103404480038143c00800900a81c0c0500c419451054000e943c0c043c003041e2441c03000910604420703681024148561101442102544998009008400030750030412408001001000800900d140751840303402120b12049401c000c40a40f40c260050305100b011081d03e030068002601e480782c41c0710b42d07032480c00b0382850a198020003540d650054111000c21010035004110385564482c018502c1290704130740c0701c006650b95100540d501d10440704040c10541101d2600302c0c44850310032141010141c103240005080d201c4510080b003a8024030404495039407150a02c20300f4034550f008090300a00c0d032100c0c2c0084920521 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 717438687 1250 717437437 717437443
    0x103031209080910200309040b122e0614090a02040b041403030705240f06090a0207050708060106110105181f150b1b28020a0302040c0e0109060c05 65
    0x1602640329101c0e4014030640103100e84401c081c40b0000281444048200000c11912034004460079401a427030b010380514149041000e800c400c004007000743c41d464180a0f540f07441c01e01c2c031400082e04c00c41d0088030502000e9452083c04020030b19581d032401c070394050004001e2290400307483c0c2e001c03203401030000b40000303900c10342200e084038801d40c1c10307882c200791000200741580103016000d41540144008441a40c80c05d034210010f0740c170350301e591601940e140000e60b52141c10075171b40340d50460030748000a00412410790040c43c1c0070b4001c0b82110f00c80340e90780358020716041090300000c00240c228420464400c2c02401120303000011900b28000704690104a00d507a1019080c0b0492030f00c0b09906445d81c04030545d40007426110009146aa600c3d0329220001242d5010b19404d0078a02c0744800d040c5c040500219000300d8400d00d0b24410070540d5144d039110881070340040c005076071010a450700000103981d14421003400403ca62100d081c1d02c4500400544003020326400341e000d0000303651101e00090004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 717439937 1250 717438687 717438697
    0x115090807051c0b07031d2103040609020904111e09040308251815170c090612041101110a15110c011a060f190e1305010303120908 58
    0x25100c0c104501000d000c203d1104540e040c000d402c01c51241d05100c03102d64190000c0c4100c18006210b4a072102090f000a0341e511621143c22807454a08240504880c1c204001190820b000d40004243e0201036000074000d0801a2000c40d00c09102c0c4110a6150a100e02c00f5910701912254411110882d17101241d19004020002410408e4070000652001c03076090100d8100e98040008280d0003c002d0805098045500440c030211104281d001032003240da803820400304040d5607980b220b00e00f024a821200b41c1c1c2d0240981442c44d10038809403e03903071242c4014000c0d000d20725062980078107045c2400301503016a800b0040c10070115512240013140009211103006501c0720f2080920712944100c10001c0c90600028002803200080003901072105400500c1e40c1c5400d208508140840c5104200701442225001120b80d01c0901990380e210003c144003000c401c0706420400d85203440103000800c050292401610042e42e550014014140d05c00e80506041030702c0c0e41c042140c4403d9440c1c08200b8065 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 717441187 1250 717439937 717439939
    0x8090a030504031101020a0f08090901510c17040b0a0f1806020a060f05070c06150b030c0a0813020d02220203070f120b06070f081e03011509080705 65
    0x20a1360441a907442000a403000b0341d0000702442d032903401d601c1c25200e254407808600b80f00303038000030012520f50707080c502c5006180d02101c00021903a1200c01c90f403940c10000c81c00c2002e00e4058041156030380e0324541c64680700700304c56035806a00316801d00d001d08140c800c49070402c3e6081400c2c48144042c8130b9501c1142c00d814118100400d10040790b9100700c6825051980030841c5450a50b00000c12503000107101880912610303040c01802c02041001c01110012103445000805003041d0f0030204040c1d52100c1480892014405401d580300c80e07403100c00758000c2d140c004149000203840c150720780c1d008900a030422100c5c401040350350030b80e0b00020152000c1d080d01921604120948803d103444c50f000203010200c0040c015500d0349041c4501400804001c40210049020708241010181040c0b00344418030074028403c90074920161554802c80a402e00d04880e1780804000040c007010091004200114654494a0f03917176050041c40e2440014038943d0105001140300180206038001c10810706443d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 717442437 1250 717441187 717441203
    0x41101050f07060603030c1101020f1c20070612051b0f09090406050916030f0b07050c07080705012601090b0d020402130312090608010b0a1101140708090a03050403 72
    0xc16888001c07041d10625000800361403400800000300b6401001c488210f42c003524201c902c91099a00690b00c485101c00c20f80700a8100d08801c4c42074400c1603001e030305041044d1400210b00d0510000a0300f01014040c0c56410544c0001c50401c0740e01e0784800c400b2004841d1540034800d90801404600000580611107030f00134002282c41c64604d03210600762103181a00400100c580d04041c1000d100030304060712480c4243c00740d90801c1c0f4003100c140707445500300c82c0d0004507a03005107142c1d21940704641d005810401040300030003d50045184c104080341c003a1002d0704c0501007032494000003601355180c4418124240c005c801e10030400441c00080a0b04440004102043c00102c3c0c4000800c0303100030902c02503009201203200001802c0071403c40064174480c00ca10400000d000d1419a001c007503d12415001a070398800502411440e20060442d0a08500305900302003205207001d42074448500b0044441c203440001c102e440e9a020054980000780c0f00c014080405207500c0081492050740409000e000e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 717443687 1250 717442437 717442447
    0x2091840020d06050f041203141306060807030501024302062502040c1e030e150a050907090b030a1106090a0e010602240402012106060e01140304110105 67
    0x7440c0e0040d0b01007030381d5100e04200b00310310b04000305048002050381e003038484043c0601008180750080c072a80480d8525000351203056130313440404032100c594204089030042c2d141c100000d24440d007045034a0155100e10300160300d80c0301b070040103061450058068000342e501403a00b03482c0c55103c10341550401c450244100c04000b0507001003481403203501d00421503c00901c80c115802d04503d040300180510883c1c090214511403c81194881c86440104003214412030220030628080d41c0711030201e05e490419a20548000460000c0801c3c04542803d65113841d4010055400410300c509000340070108410414116030300f0100e56a000c465000400016808003840e009554403800d450b02140000e110280141c5c42c1c0f030422000010030b1007001d01510400000e11030408040307010000408800080601c1035540c1c3c0c004580b94500108a045018501d596140c0c00a89034000e02004d0300d8907444035100710074150300060108880300640c00c490700c03080c030078000000c1942c0800142c4007001d01e8455140c0d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 717444937 1250 717443687 717443689
    0x5030735061e1e040c08030a03020a091a2b020703031413080f090f13020403031b0809040c0e0901240503040803062701030c050f031615030209184002 66
    0xb98817103801c2010a40f2000c604242c202c0e5250f0000c15010341070703686600c2002d58038600e0007010890018081148a0180402c0b11480c240c100220b9011039070b901800240b401c039102080482e405480250000b80d21a02c1c4c031001ca0f03031440e018075002651411040040110380d183c0801a010703003240701d030b40c0c102d000400078039694642c0101602030400810384c003402e0b150110101c000f1350091004030045800f00008010f03e8180c803100343c000a0b00242810300d8421b040c4100001403460f600343d4030610900000c201200c2c0c4a110482e03010340850160765000c248540b130b00401c255030060790074040240410800002a450780c00f0342e900304205644800d1409210a881007007681c8404441009510000001041c440700014202c00c1b0f803400c1d554042d00f031021000785915100710307540010204400002c10802c441002c1150001c010440c903005051207001e5001a1141030048041040441ca240074044400002c904442c070820221040a480400400715005030541408005000344030441540082d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 717446043 1106 717444937 717444953
    0xf090a0e07330c081303060905070e01051203070609080405220c0509030a0b0a06050d0b22050703030809030409181a0105030735061e1e04 61
    0x4100d0503625512402d5100040085c16050003400000200309988103100302c0034401c0300a000d110f032400030b41201840040c0c21480c450314080d010714029007c00811148400c3c0d0008002c122112a4240301c0c102c5c0c01340781c0c041030300701c1000070405440400d11806441040c403200030400111072306810855180c001c041d80c0350b0b015404800d01002040c0d03001c0030181c0c410f850503c08107510f0348540110b603000b2002d020407680c4440300003d000b441e02035040c91505803010801001c1004510780c85950342e51107280300150900c03080e04040b82940400788221005441c801300244182e04940c140d0b1000e60500c00416940412040d030001e95400c002d040c480d0488170010018a04c59090502c003541007422000c0440f6103000b20501c403c036010165130400030480124001d09210314200b04030218141c43e071101612482054030030012076842e08404801d072140d411100445642c0c8610304414 = true := by decide +kernel

theorem cover : BRFrame.Cov 717266187 717446043 := by
  have h0 := BRFrame.cov_init 717266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 717266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 717266187 ≤ n) (h2 : n < 717446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
