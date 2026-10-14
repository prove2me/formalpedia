-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2602
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:11:45.185264+00:00
-- url     : https://prove2.me/submissions/dc3790eb-fb14-4d7b-b269-5ec37a8e9495

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 467805755 ≤ n < 467985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 467807005 1250 467805755 467805769
    0x8090a030e120a030801030b010b0702010c080901110a080c060c031315091a06030f0102121602160f0911040819170f12060102031216030204030c0b0c0d0e0f01030b 72
    0x1140c4002d5000340380d2220205a000b068003410b03039110703825a82c0507030388075800744509004074040a40010b03c0c1100810109115000900315030780189000d071485150842d000c1e18103035040100700c038500f800140504000384c050003030380e03003200c01c0000d468a5810b00b14580544c114500d40003a020780500750340242c0802071640325440b05a07100c1842c0c0b6110804c00d42407482c1310001c0316614000d0150101600d2840410303c2101c040410352040c1030120748a40e40b402c074220284105000541c420800010900132400078250000c002018003007a625082407000d1059503000c42c441c82d001c000500050092201c0451319407040e0800f01c0c220148540c1c00e051008599000c203a0450b81b58400084844221507040024410b48079075240c00612901c5074401265170341b05603100d05000500705000700d8282204e14280700c607101d40764903000d42455201c1d02c6101c0c5806080c0e1000d1500d0030000b81da840c000740c080c84006c84100c00c6050440c400d00384107002c036100100c050308490415986954004090356100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 467808255 1250 467807005 467807029
    0x70f0302120112020406061b0f02040b0909030d06081c030e2803030b09040f1202010207021c03110f0607030c1e0905130c14030601020a020d03091508090a030e 70
    0x700c0318921650b500c040040243d40b6a08040e80210709003070000c6803a41c015200000d00b08074503c51743c0e000c240da07a140d4000e070b1242e20404030303071240d15140451025900d1407150740c001c0354000701840c0e541c034120080c03030100d6030980c0c4590276a0308444000850103c808041c0808280103007008a102d2620020f0305041221009503907040c14a0301c0801d0012403003a00350202a240321707860170807103039401508100084070300f12801003294025286001c00a14460a0104c21400500000d4140790281d40019618480c10340703031017004c580108a40e01416440302111034204207040240114801e00c030760380f42e22203100522031001d240c0c490018011980c0300d40d040408034801c2052442043c241508014806c0d035087c400c031031040d442031600122006091180348245452501c41e0101505210b842c40b40541000b000035041d40100c17108240940c0b1584c000c0700c500d0381b2a55a150100c2e0600c07020525501500145d201003084000801001000002d00001100c1d054180318400000b81d40014040000c00b07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 467809505 1250 467808255 467808277
    0x30c0d180516080a20010909020d0212010b03040f0201080c091f081b0403240c020646090c0801200c1504051006080c0906030106050603070f0302 64
    0x5415050078000c001c60310002d00d10302000d0001c1142d83d40c0344683d030740b82c0c4803040240c060034a41008210000b509655031300d600d501814850446555016944200d130032030030090b40115000110554040180e41605025009120f401421400c243e20350105a40000b98003c0c1405064008200d0082140f8140d851030700f0010481404030014a031621505104002e84c400400c01e070001051041e095417031961510f2040c02409400c0c50b01e9919049a4802c40e0340e0324000c0e100171600c02e0f00c940c02c0540101843c0b046a034005081c0e900700803400b110799401d542c04903000c00f00600d40c608440b9440c1449019003064041c0c450601d2102c0a160701c00800420400414420402c14005641001074000b00c9445030044000795210b01490080c051500c904884201d03079400c140200c49041e2152512127811034041c004071426991105107d0b4111507194016a803e0351002d9480c420a161111440c2d9101c00141c1c02441074a10f4000400c0715400064641018440400d0380340049610aa05444000c46a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 467810755 1250 467809505 467809541
    0x1509080c0109110414070f050a2606011409030a110f06070b040c050a0f0b1b0129040e0a121214040b0f0c030105044802070308030c0d 59
    0x1940c0740c15008401e0041403e405141854548403800700e42d00403a0784640c0d0503881d5841208003451048801d6408240044140515a020750822050707a0040c540c00140303e400d0100d0302e082c1712001409805c40798100d1072100004001c8101c1d1500d0104d058041e10b58031031030401c605491800010003450031000d041d070300b20344045000824030840800c01401540207404110714103894000380800d42c8928000c8c05544d1912041c20080010303110003c00c425009500080421086590801d080d5a100c110b01e10b1480c01021004012105150340004c00801c12142000441d030003034401511a6809c030000fa005c0c4403115100303182d85018505403544030814182c00c0000342602d2501e4160540180c6041e107140d0031140002e412030014005142c001c00ca9001c8050540c0c0c80c0c14101b0020300b5910f01000d45048070000620111904803203d1500030402a0321180d0b080c0807107000800e84d80003c070040d030855005c28410404a95803400300ca0b00071448200c015a03800b0003030955005410a1a40d035030443c08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 467812005 1250 467810755 467810771
    0xc0302011121090303130b1f030c051207051f050c06090106170f060412050d0509030d0c081302090a0b060d0b0306100501120203180d090303020c0d1509080c01 70
    0x2d141401c401c500780c0c222092240d40740c6034500e0790340703000032140c03003042240e50004180828980034100d036004601c180030329011030f4030b01243d5503c5030059204490703a00007000240428a012a90954440e0324000109105450500007950703400c3c1031405210301c1c80c911000b03520014443e40c12103618030303c0c2c1004c450b050b06020412500a10740740c4182030403a021026010360921000c00c980801c00c1c01c11005100c15111030315990142c030381008580b01030207000c2001140d8060307503014551003650b40c6006580c035910010704a801380c0707503007000076010030103120104041c600312000d004013900c1c0c06644820382590b801207131000404034250002c0d40048081241c0c58211441e40040c2039104c016010360380113441c3c1840710324207245103002d00c501142c03a1001517107401103141c1c00755511201c0e12400b80c0c0d0307040022101c10301340880c2e0140e0f140011030324082402419010007008000340010b86402001e000c0340d481d400141110014000a0580c139002408240001c18060320141502c80000b084104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 467813255 1250 467812005 467812027
    0x1703090a0221060a02191215141f02060a09030315030602030a11040501020a02012d02030301061d0a050f01181202090a0902030c131103040606181a010c03020111 71
    0x807a000348089814403400001a0b0700401340e009a4501901984407003030740c014082c5040d43d100751145c01c3c00308415500e12245049000c00400c40d4000c00128543c0c144841e40b1505020034004d52001c005c0c41503540d154440340050f400900180d000d410346100203447d40e441c7c502140a0440c03110200d94138640403e011003480300c1940114000d40121904111700c3c03c83c0c0c6c01c0c400c001c1c003491245c6d5001da04880c91040c00b5500a20b4143d04d01100a440c00901d44600502100440c0c00c0070003050059101200500055400c000845011000404451450360f01c0300c00103400101e1a008090181c1c8a100904160b64010201c80c074054041410b0301d04519100c00b9481074403001e0303200c141d12072400440454095540381c4251014070741c02034060050b02c10004140540c8036550b00c6000340b11a9261074114a071400c0901941c015845410042141c519141e001e070807201e104040001c2e210b10342010300d183d0803001c1c0b00c40c2e1a01750003820038078860601030a0690041080349002000c442d00014294414 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 467814505 1250 467813255 467813299
    0x23090f01090c0c02242205090a020412030509030f0106080c030d08092107080a02100501140a0302300a0309080d0912020f040c0e0103181703090a02 65
    0x40d8204110400c6042000708048840849914019401c085c0340041180c8061840c0500704800101021103071800c4000070b41500b21070341d108013682d0407040c001410f210394505071340101e412440950065040900300f0741031400c46a00c250b030041c188080090005003980b0240a0f603048030407800000c210a942c0c494040d615030100030076503031080c00b0b181d04503c00640200d13100e5000e0a4420f00607c500c641c4201507100700800603803c804e0146007444200d0000e424080100b1070301181d6400340c4030380300321090001f05840041e0007448098100000000540d155000400100c980484205075189084d03102801401913040301001920030080c5103405100c0b000031400341d071074403036507a42d5401584d030145c003030b01d555010301e50070b00007071099504005098999000c098101c1c001801c011035000f4600c0090120350084500d030303001c2210751220000540c1c00d4480c0c142d00b0102004143e40c000c4c6e00d9503610115405a4060291481c804800f20305400d80801440d2806035000e004602d070020241500890 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 467815755 1250 467814505 467814509
    0x605010504241b050d140f0f0d270c0f051e0a05150301050a0b0a0c12021c1806030b130f0e0d1101060b040b070807051f060e0606090a23090f01 63
    0x115102c101c0750b006c800e003d442143e920b900c6000086080101a1004000640c02090b5944c282070b15003400d400710b41103151080019010030031070400341c0000c5240401d15031920f13a100070802e0014807001c100c1e5495818407004009030442418100119000c00503180403000e800ca1134014050703280181c2e0f0f01d0a20801941030307520464130307204031503a143c80a8000f4400c1040f06400102c500c41498001211400c041241302d045005031803c03080702e80b10a002c0c41c01d003a03050b00005115089100c50080901145c0e002402d8149800c1c00910440e1001c00c00b8403141d60803a0340c00550780c01044980385030541c00700c2c0c18600400d081d1004492607080040c4034095020f040035055282400020712031400b0360445048031240081103080c6401910703910b42e00c3e00204000c3c0c41030b01034401a894040981c01111403640c0b03100e039000440504100e0048004080102101d010302001c0000d22801e559a400c50000c5903100d1000c0d100f80050f0603a10b212101180d24001e400c10b62541c14000c0c600210152241 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 467817005 1250 467815755 467815757
    0xc02010606020c03030301031e210305041104200d1104080102031e011203030c210218090c0d05280b1017220213020d0605010504241b050d 61
    0x100003d100c204040e102c0c4400c0c0302c0107004084a40742e0184814240c0789900c940c030300034145160042200c5285200a0b41b6003d2108002a42c40040000300240c4154002e03419109171410003c4044a2280318409001003145d0f001d60300c400700341c02649030403d8200260303c107800c56495031980d98900c0c00078040d420036030305007448183e0030b91420b650900e400e180c41e0480d401d903000c104900450f518143c000300035094001c0300700804840c282018588030141120b40c0420b09500507074860014500c030f98902c0400500504c08c00404080c0207003a251001500c0c041d00d8660b8000415031105800d80c03e13800fa804407040320640c0d107001e130030a080d442d81c3e00c4040c0c4500144d81200311713260b108200305c40788450100b062071420010310200d0f00ea524059030500202a00c0e442205041d000758001a00e02d01d04031038400c10181d0006001c0680e80b00c2c038042c5c0c000900007801c01a05040c00c143c440c0d44070070329011f581034036800840880c5600c24812030800511110030b601118081000f410035546601c0a0b200d000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 467818255 1250 467817005 467817013
    0x20d060302010e0312030a2705100c020c060306040b24090907050f0712020f1608010c02030703140705010b040e0a03021218040518070f060809011107030305060a090c0201060602 78
    0xc001414080b400176010141c960005145a48030b940e164010310142c004c100008032022544ca48845070302d030140e81e440f030048d002040308042c002c4040c0e0988094035480300440d04603030141c49594072400b096a800c150b04560200e20740100720003080c0e41d11450a20600c44140080d0310341d40410110005007000e15040c0d4441d000c0d566152003e454034841d2244103104501c0402c0607102141c1d4029280d40e540e92640b065440c41008907181a280010031100340444090303030002000f082c0310901c02c004d0900f209002440c01e010b000e0310060000c5210079554810310500081d00c0d81001400e50001000f0f22008004100311002141c41540da5661024210b01500c04d01d22000c15010106083d504c1650740f0411000c0001d0101e0240805000e001d00b180360501b082c0558004089001e21600010b01120040e80c807401340b6040c80180902000f40624005034508a1000c84205090b802c4952503a0942004201916030b5008205a030016134000100140360492404200c2d45c10740142c801c85485608403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 467819505 1250 467818255 467818277
    0xf060606050a0e090f0129030c0a030b03060105010509010f0207150909230a02090102120f030601090b070b0a0b130609020a020706090f05010c150f05010e090a0c0e060f04020d06030201 81
    0x2c031202c001e0590341d0804442c2605c0c01082207901c1100c00c82c5c0c00003810110500102d1081140724215081600e600410403004100345a4103034ac140300f5002e525100303d00500280d4500b50020701356124001805041103648078008042c140200f080800500c41044034404000001e071004100e10702500a44400c036041510585003410307482c04a403008030844c0c40c20501e9490b00c0c0700080c000d51002c403202d4154040c3c107207984590704240014003002022100219520b2810300001040d0724169000005400c001380112400705103514170072607104080b0f40001504030441000601010409083c1400041c00e1100200c0c00c070b03103690081c150b640500c1d021189029114981510346000703130301826409600c002d108100c190320489100c01c0440c043c940039044512080a07020594080703101e000c400d1510703980100f00c049032110106921850510240600b4400340d07403418060100c41c419890032078008400b00d004d40c2e980d01c030301113580540200119504c0c0b10b00e805110240c81c1510043e80401c4061030a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 467820755 1250 467819505 467819509
    0x40f0c0303080132100e0915030115030b040b1e0915130201050906030c12150a0501030c02030a0c02010e06070c051302070510020a0905130e0105090d020a030503040f060606050a0e 79
    0x40c504044043c0b44d401d0402448881c00e008000350150310b444100031401e112411280c46902c0001d005054038641c20b03041110020915094034084480c401e081085018104049110760601c680c100342d103d2192022511140384802c481b9244250300708060010100703103c00c20f2000550002c840c1c231006409881039a40c2056403002135840303040071b404100100b01c500107901e44078005541c00400b500ea40c50134100320201080300c0c1c000880d40d02e510580c030556114580e01c0d006200b5401440c00f40380234040c3d1280320800a450303004402c41c4c0000d1003a2401c0b61821603028030000302940c10b001c3c01881d1507900c1800c1000306d000541c41030500400c5026a04501a0240d0089515068000c0014400300050070b415200a502200c0c2690401c03501c2180416a903a8903042c8505d0350780007140124001d020400c3c21070840e54041c081580035401907001403007498020558000c81e503054200251a55200c0c1001009039440c5040140711600e05000414926013040c09000000403640e19892710400390b0b41 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 467822005 1250 467820755 467820809
    0x14010b1c02011706060a081f03080a14161509080309010c081f060f091a09041503170a050c0106030b0405070807030b06040f09051204140a0b030103020405040f0c03030801 75
    0x500107401c250100301b03030311b4054018a041500b040c82d00382c030401c00440c40701c07020384d00c65225041103c0c9050005020304aa41d80b04c6811201a80104600da00d082c20071792800303c002011420040280014a02440642100b5406182c281e50807101d484d42c0c80c900410498020103e500a010110709440d000c990040e203040504140f01c0c08824440030034509241003520071428580b040410481413007404283d021a8251180c17298049154542e00c0301408020881611103007040040c1842540c4801c002040708404190300c00c0900e1041c5955503010b04d01c0450b0207200d04074480c89a9820080c0020030403210302d070403070302c66402030095038503081c2c6503080c8544943c1c0501c801342400c11130302c01181d840e203010750002401e000e910100151310040c0f562141d05002001005c000f504002013401c016101c50b28203072100c065400c94056051a0404c07001404901044c000a80075994070030010701040950b040541695401c009a81c00c0c80d5500c2ca40200050400d0250785d4100341c0f0a490143e041c10710718 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 467823255 1250 467822005 467822011
    0x303090301240602010e03071e1703100b090a0302090613020c0d090e0705030a1a123d1a0603040f110a05010c0f080d02040e04060e0307080714010b1c020117 69
    0x2000307180382c0311151b1903500d503a1035000f41d84140c00e271076108404005008610a501d44901d10ba400a4903890080380f03034a10849240c1c0240c100c007000b004040c03540e0303a90100000c15a603046526407516150500420b049602c00000716241c1840011246400701c400517201d0400000c643e100810180c4540e10201d02c04015100040400c81c18408150752038072a41010316049081194407071001903007000604002c85080a906030350701701041064040c1c40c8024203055402d08044a49040d05c4c00008150080002500300200d090ba250f0200031000506001040000801098161a0708003400c080c1c040c07001a010031038190713604068003101400c01c00800000c0b200143c64503e8110b82c640c891442c005050141101c6a010402103201001b150740b02801c0500201040500c0500d844e01d004400c488410030a010668030500400303000031340a00490300c000b5400401800c0013085540e80da0701422400c15040d074021200702241751001c0c07a5160810800d4000da940d41c407032608070f51404012010031307 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 467824505 1250 467823255 467823281
    0xe0304050a030f0201020c040c050703021e0d080910060b030a05060108010e010e091513050708030f0f0a14030109050f130b060105070f1407030c1403060402010e030309030124060201 80
    0x7080701000070840010040300c4190060065491864125000804680f14102e440c0081500842d50724249681004400210500700c1c81c0104500c01c0c0f04041d07a9600f20700450502088000400100c81d075805200c8007200481d02c00c014086e503512082c407041c00c0d81088602c0c5609074a03202c006003456104042090407130310401152812030742844084442400300030310b54440ca124509503c480488140c0b800c3e446041c1021132141c080c1510301c1d055003806810ba00ca00740d280e10501a01480040d440200c8503003c9690088540c1e81e2403c003001c2e94100d0802ca01c5030900c0c00044000a0340c01c800f5000284507550301c004074540c50703403107500d100d41d80801101d025000b50442c0000807200d5000f00000c0000c1409200b5000442840c0c4e512550003500300260050316401040040041040480d010300c007404441d2400c03a90742c2c500078040380e0f65082c018070190400c0801d20400b501520180111504a10050028426443c41494080c00002280105a8190100e000000d4a0352062048100350090 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 467825755 1250 467824505 467824519
    0x110304050f0d020d0209040b070207091413050f0f01021902010212041e020604170f030304030206190f05070914040207020f12010b0303031e070e0d06050c16080702040e030405 77
    0x1000620040b1148090100c1c1c1082e5264144005680ca41c42400c0c812882903c0010840c0ba11880c000d003844601d604c0b0407261070400e1000080c3c082e401c3c40c01544240e5444c1444c4c160f84060a100386406403400e03141c0740ca4000e0f40c05044440c2410b40041c00d014a01035101c071045400000d08070b08078030546541b00010103800c0041400109108614014000e005000b222024001d4002514913031240e400300c124890b10f400242c461401c10f002803210b1003a000051419441c040e20065214000148047d40448205242c981101829489000c0c100d1010004125130b1500ea00060000b400600983c0240c140d0f42c01c003540030345014000c6030503050b03000e131120009079100303004c0c003480310199680c2e61115500c800d05041203450800141d0301ca12080d4200240c1d03110004400407244c40301074090820010085040d030480e8a5404c0a40c40342a0300c0312000610b9074600150220a00415140714060b102c5085110103102040c0c002c4c0c0b562500845080209a801040c00d5690313118902c40d59400c685 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 467827005 1250 467825755 467825779
    0x61a03041403040f06020f0d05040308070b130812070905030d020c1302090907090906090501150c0c270e01050105091305030d05010323062e0302030609010c11030405 73
    0x9111001054007458001c40c0e082c42d0b00e40d0700b01018407a00360480c800680c014000710101c036804101d1032000e1800d41c10490f01c0d00742551681a0248110341002e00007246030004a00045c0c80c00001c80c03010382d002030080b42c40e20103001c1c0c0c0301202c200075902c02c800070360900d0020400b4500802c003071210b400c01390007e03c0c42c1d42e494421b00061130480043d000001d6402c0c003e02e01c80307440301c0e102035214056507603912022a007064480022144580c015414151400f0010f01601000412280489903581070028450b00d6a00d00080c10980a070071a0704060301403010001c11031110959414503401258003404028252880b4508a910901c103903948200e45801142162114440d0141c0341401074094a1a0069842d60f401c1520710a0f4800c50381959650f9070204008130032080701c01e040780102d01801d030781e04018114200c074417291101000352801c15000e40d000104103000c00e500941d406000c0e204946482500745008090629903040802c507124403c440c005000300454050321401064410305038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 467828255 1250 467827005 467827013
    0x15030c121b060d0207050d081b04030b280f0e01021e36150c0a060f150305030307031b050a0f090b16050c010e1c050114070e04061a0304 60
    0x1900078207520380001c41000084000b202c14001010750502600013486e243c8840c910082c006200280348040b02d0708e00007041e00007029507008640480c0c1d000b44100c0d10790307140c81c136a094207409240345e001d0178045442e220f0200c051442e0000e81c100b82210b18100600c60001038160309034810240e440c81c00702100d4a02e00145241d5401030f2403604c0e400c980b0046400082d52858102c98031844100074410444000034590b480c01c8001d102c40301210a044c142040502c00305039549829240c8002e200c1900e03110403044401903648a444041510026404010307540d003015600c0794010355104001a00741000d450340c0c015902c0110b8401800380d0f541610348280c200e02100d1151003600c100040000e031820025440200f0700142c82031000c4885822034007645860320621302446480d116040c04990428082c0660701d0302d1103012030300403030340500c182c101d490b14110b8010b01003400100241e03040141884042079001c0c0c185400c03114203a130104401a2200c1021019840a526a0f0103410040001500213 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 467829505 1250 467828255 467828293
    0x90c12030509090a14130b070f0e1c0b06040510120c0302151201080708190809490204020d090b28050c04030b071715030c12 55
    0x2080c0280382880c24000c0442c00106404015500002220b44517039401428140d0b91201da80c11080f100e60760195020aa600c4803004540207003640e09108410008020143c00340140503640e81000700024100810400b62a6011500c40c5042d110038910a00042c07075410701c2d10816000c0c04070303202444192498462500715241c03a40c40101c81c08004100000700681313515180314560591140320350b07114200013012004645050340603d000b40c2c810700b1f0420203082c0108114000c09052001d02c00c03852400d0500c001d41d80b0500e941d003034200c41e56445821115500c03510402610325810003075508d510038241e14145034001c030410320025668144170080140761560085c003d810044002103a40451030301c541c881040201d5a444403a00c2503180d001e072516100c0c003c1c9041030586c501c104528100f6105d441c0c09030007180070040c480c03c01e003000301d024903010360380c0700307089032480300021800e4500507041542a4000c1c40d2200c0c002d00c03500c1072010181c604440c60380c3c11150000700501c4000d050065801c49 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 467830755 1250 467829505 467829539
    0x50c07080d08160507080d0e060a090309060509060c0d090609090912050c0f0d020c04061e050d1b090b0109080307030e090c040801051005120d08040602091201020c070302010909090c 80
    0x18090300300705205c0011800e030050302110811100001d444440b1607100b90030040000c0c1141c01c2e151410003441c0c00203421003e00000d0703c80310320b400e94840d5001008620f2520400721108428490050380c004220f501c07421070001d82e5055a5001d41e819a2a0150341c03c1e11980b004c010b0828241245800c109446000030f0501c405001040703403581c00444102c0e90825000303404907401030b000403040580302e0a05024031002004e04281104e20b1045410b004280180ea0307000d400e01c00d0102c403130078406001c8810740c440300516190000516150752256480014107078503100b1401709104c004005128840402551084d50b01515020f540f8820b88003005002080140a41c00c2c044051101049501007403080c584103401003040204103509000070411424460840600c60341c1c484c440025040794045115074100c0d6000c0000340e2107400810000b041c945014102a10300d42c404103000090f2140081c441040f68002e89810324101e40b149041030a0381c050030390240212048800070043d07141d4043c00c00403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 467832005 1250 467830755 467830757
    0xe331e090a09020a02060103020405010b040609140607020306070206010302040f0209060a110f030a03060305060127022b02071b0b07140114090604050c011803060507110706050c07080d0816 83
    0x1016929600c082040343c00c402c0c1d0840c01688906c0042c0214100340c480d190141404030300c140d04061070110000c2c90600d140c0101d52a0a140c0703001c2c6d210310340f02c1405940300b0b190700800b0340c0e000e86420a0000d6a8550910050748141d0410b0f08224034003445200302c84120002418940c41c00d0910781c02903c0340181c40c1d042030030902c43e10a000c02c42500c2800502507500c4907507000704600b0b2660034031918044040c2c0001e441c103448154ac00d050703d800400802e10303440340b004000d611184802c9607103007400e9451648415070440c0c101c0140a2019640c01810068410110b0901c5801d10304d4855011840c98000c08030201000c00c10038001c6803403260a110b119100900106802c18240c0e203142004009484e05001356101c0b00a100c2088803d102d449130005080c640003200e42e03980c03801001d00410600c0081c00b62030355000400d030b1040c440c40740303950f581d0400705c210756442c0ea4900f002007065010241107000c50090003c04215490f000c145039031407004503501c108143d100c0541b800c4084c40c031100c090b8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 467833255 1250 467832005 467832019
    0xa061d041b0f0903031b0c090608030406091a04030212070803032508040507060c050f030a0f0813080d110702090c09010e060c03040b2a01050106030b090402150a0e331e09 75
    0x448c1e40c00c600400c00980519006113031038900d04200900001c606801c042c10b6582c0440b03d0208000501c0c042d101100e404880d2400c0755201c0100035420141180c100074240d01002027004403118480e410005071081400f545c031380244900c4001c42d5a400151002010b45c1c01400c4100420f62040842c090050300502c103540030403190b41505c0d0b255600c074924007808100c01c20030083d00035400988942d80810301c00c1c000700940d0070a680d88800b502c24000550b400f6607455012144500c603480580e06029806418074445042505c2c0c150003e40004c0926800100b00028596032411320506655414500c0c500940c1002e00b000842c03002d80d001010803503449859000383e1461201000c80c5030402c0b09074800006559410320400a00751406200324502810b60441800010307128041820206400c3c4001140c0380c8900000440b015214030032000ea11480c041c1c81864a00d0b5980c0712000c050302c01c42c40c8801003074089410344a407402441c3c41000129008401d100c1c04e04025802481c580400030050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 467834505 1250 467833255 467833259
    0xa02031321030302130815010609080f19080d090b0103020a05120303192003070807030902180403090b1c050108121e090a031103070501030b0a061d041b0f0903031b0c 73
    0x583d20709070784010151000c01f44000104441500711396400d002e000d1072800340059201c07400d0b041d60358400c400d1841d210041c030b640850061080c0101507403660a0003c40a100c41c0c1030f542804290f0040038042039100e0714000000091a00c1c20301120241420003601542c1175036a214845030310380101d43c2c2128032080c0c44000c420034041140d000d00c6500400b907001e454990801c03410081c185040100f80d00b003490314041550b00580d44034107100d01805150300301c00400c1c2d9120b14003299840342aa1124001c10000300301440070b00c800382e8500303410008404c0c0402070780e0ba0b02d010403030b501c03440c12458908600c800c001c180352079840850341c40d01900b0843d1846180102040101d0f2006200f58402c0d00c0a520f100190b00552a061200e100100310034607040c004c840d03003000020750a40e81e511800b0144010540d001c0c440b44a2448034007084500203008006241c0f192121141c12000054200000346030005644812070040b00344000b960742540c0c030390410440c0c2c4c3c120180e1904210b0000d03254a0902040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 467835755 1250 467834505 467834519
    0xb030705101205061206011d070305071b050f060924010e010b0307030e0a0303020a11070e2a0c030702131103010e040302100504240524150a0203132103030213 70
    0x2014001c08d28140c40c404070952111401031400005041682098181428030040c554059695408031200c9030b14454880700915140d4074200f510741d0303110040e001e41002c10907007420101302c01ca094200704601007044038a683d8036100c0034409000d42c5000202d001e006100124990010715841091410000b9406040b041024945a50040c0880010390001040d243c1e141e4400380c0071010780400d00052810501300b09003407454a0700109900f0300e100a034845a4100000c5103085098407800c0c104841e41e90020703c80d42612540000016401040d41d0500300320075131000d100d82d141c0d0f11210180c0078196420325050740f24501c0042d005402b144175010481c8072604451186500461090b400116800304440040c0784009118a841d08060b20b018100608105080048840050a03a288000d2411804002030015040f26603002403040c02051307050f01e19030000014848214443c1c2e0b54002540e581281080080c14119607210b001c01260360640000e0087d00980a03281c4000a000700700b030f481d000d0f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 467837005 1250 467835755 467835763
    0x151808030327010207030806040c1701090507030516020309010c170c010f110903060f070203040b0d0203011e23041e240e0403050c07030b0108010b0307051012050612 73
    0x441c40700749060b15002000c00d14a48070701480c41d000080080d400c2070300c1c503100607100c900020107d030b0003151240300c401680c5100d2103411120b449541c1800e082540c4807040d500003840112071003070100e032230300c40452030150348041461240c4c0200d034015072510701941c00444092a00030001c4846150410b180e941442c0084054014110f18000020322800010704c2001914021011540301c0364040040806a440104030300d40c0c0002e02201c1c104403520781c0b1104900d54130541c1d01480120700c0224a80004130b401c2d400641c100e510520784010038003c3d003409002043c0c01486907041c113003102c44039014400b0310341e800e0f503005400081000682140b80f070030300051601480d00c034100540d41c030341034a85007540210a5100e01060103040c076001904040c400b40000c2070242014052150214140421907030400c5040c0241d940001c0480165940f444090b004e045010b201e94868010740602150900700012405410181d5559490680107464210070080c40060402758100011301c9a82c00b91200c100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 467838255 1250 467837005 467837011
    0x2030f161a0909010902130b09060f090a0e0906070f1b030e190b13120206040302060c03070623070c080307050903070302090f0f01090501030206070b07030f0c0905010f03061518080303 81
    0x45c0c096034a14941003182c3c651991600300e58010710303041c01498416102c20094850103810054020390b01c0c04860005403064003681c3c0100d40842070001004003603240841c0b00780c0151020384030150200150901602e05000c4044c1980c2602035048039403000c244103c40030f400315940940841421540b20020071020860381d0400010030304c00040f4446214050b8034054001c050581c41a10a00d04943c0003d07564413403440003a00c81c180210b120b8a1540003402201d00b855803081c81008480aa42c0102c0c07011a034800303102d0301501c0c40c840020041802a00842d8040f0f80c845205440e50b0760320501654107402080d01d1310781501c5082c0010006171603c80d181740c018204585038903a20724160400c1ca0130000142c0103151590b08200040006881e01410b40345000d91040c0701c04402d540d03462085000344526030545001d182004039078403603603421800c14012b460080c1d07a402c003601c2401234254182c0d40c29110b0394801048420f01c08045511030ba01003482074122146c00210b8569401900786550401c0d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 467839505 1250 467838255 467838269
    0x50a1707030606200a08090a090204030609060e03090f100207080a3c0b0c070b1819030e0607020402041716060c030e041a0a06050702030f161a090901 66
    0x2410b41072041c41c0c2c104e10008114030031494008510761190800640b10000c9510003000c1c401c0c0824030b00420381c4c03140c0c1842c018081c0070b82c0c00c544866982c28142c02404a01c81c0555100e440c0070040c04060390007204850203840064800840c26a0392030038080c00d003a4a400010444c044c0c44004600b51106100302001a03000d103842840000c090742071400b154400d031181907107600210540c02c0350b15554145800c400e64124501003642c0d41c85200c421428454000011b181c0c0401c1c50410a560305e0466801307440c8407921f411201d0607100105080c41d115688074028010070315407424924245040c40082c81c8440c800b90002d07080ca0341d21403010302d461480c000880ca0070380144030b00c84818030383d00140c1303402454a442c004440303000903200600040c0f00110f1b400c0c0035503120780d5040e0484104a002201120000c0c00507049150350b400c0041854020030004c81c0b1030700070b04a01100c1600300040d224003a030014039844488501d42482e44102c41c0010601c5600c000007801000c42c16600d400c1c01a000f0020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 467840755 1250 467839505 467839511
    0x210f0920010f020601180b0d03020f060105012f0307020604120308100b0901030905011e0c0809010507050a0807024314040e07050301050a200301060f050a170703 71
    0x104404140811042203030a03810444056660441c1d0360307001804504603414955400c0c440d02c1021001e10140c5003481d80701e900100030154480816500040302c0e656a00c0c5007007500d42690300e0b2001141e5006810300e82000104114040110842070003413003505003109481160715001c5158080f032459007003a80243c1d203096140f0702c81c10600d5001164290b004070b44100041c030303ca0800c40195814001c0e0b040c1d580c1095511400001045000d5200e800400e40c014540f0402c609403a41c0741e0702821401340644000f813061350206070740d11414028103004082c03a4807441c1c105030109100700c03403210008224100318400d0303500c1e180300402c210b0200c00502c8080c000400d51150031302c4a105d48412800805040030b0601007003040304030884001050744480813100844c10940b00f04c4000d103400060b401c1243e06501c0c040601404600e40d60080101c9513180306199800118025002d41c0e6000034403604012a05000700303507004c20300c01c070000d080c00c07500c9050118451030940c0da02c95071000e0442da12004666 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 467842005 1250 467840755 467840783
    0x9040602040e07050c0703061109040e010209190e010b0f130b0a080612060105011101140a09060b09010b0706020304020d0b090c1c0201051b010b0607081207090501210f09 75
    0x102c0782e01d2082e4010b00320f082061411080310138084d5034810a10014103c00d903500c06160b04121301d00101ca07400d0f040204181311010720711101c14000e6000400320b520800d06c1703041c4c0b04001d6605010040403130f9000128400749070f18102450180f0b500140361042c0d100d004100f42000302d044000f40c100034181502c0701e1511045040c801400700d42c8042c2c0b955100766241d52428030403010004006056a07820b18040841c01c00409001c0e01604003a10b00c1041c104c070138410060340711240d0f40301055240c000d12080c0400e0744003109000b5003034020b001d00d2009020401411003c1115a002160030510240101c01d40401caa110200c0e0030740e00703580c200b14540160301e50b260903240488802c007000c1c6002c001d988050045900203400c500c207804900c05d540c80900800c816229007907024011303104010703040650720381181c58118480e0f03100c1020010658107907804555185d00c200504415284180c41e0354045044281042480c88040c040c4441207070740f102d40d034405a8101d400f5520000c3c1c03040311610070000d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 467843255 1250 467842005 467842019
    0x30a0906180b1b0c030a0b040c0603050c0f070f08070b0421020312060301020904060305030a03050c0301060c0f060f020a09050f06090616210528020c010e06090904060204 75
    0x8600c064251010010518042c030114124008a0b954104403001c03211942603030700301c00e60401c109260115410f005c2c0e540c0c0b41060025682446100c1c0d8842d0a48020b125140c8102380c0c00ca0b0011b8070805980c0c40148400720044d4407050061541601031134102940e010140ea4502d030a83c00340030100c075070303003244005c0c007003000084001a9a00c21140c41301c0e00c9500c01c1c0210095490140301c003070589070244100480e40c1ea0b00d0a6046441116000d03206202040d141c0c217010b540d039440600c1041c0000c0c03403c800201d0550002042c0d1b8180c0e1000d507107985000d909500d49000101501344180d41c040d45d0b82009003c40d812502c02010f241800d52a42d584a602c0c150030840362500110103135015001c1000940c199980e401c04480b64124100c2410412100f80e0070030b110a840200c0c0d2401d00401c0d865a80924940c01c44060403455410b5205000e506111215140c2445000e000c04070250388541c2c81210250701507590360120840152405040405410001d025003400340c0d000d803002c43d40018184100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 467844505 1250 467843255 467843267
    0x11b020312180102010905120f0405060409050103050d0c11010c051005010608010504061212050309030d1a0907030e0a1214031008010506010c0f060c0905030607030c020c0d0b0f06060903030a0906 86
    0x2402d0240020845001e10780c481c6901c0b035440c243d002000c00c60000b141102e0250481c10780700a044081d052035221512144d044004000a0000703642138030407038408040d4288a41c014407002584440b02c000401101c0c801558501c0ba10300040340c07035004035241d0381c407110640e04c80e290003800a0340d45c18030740c1d524000038032049030400c2c0c002041d00703203007485c42c500400e00c48034404940d03281a140082c1d9130740d40c101c042c6096004045907484a9420b141d1464141054031143c0d45006004640486007511400e4003941152000c0000d0100c0d604001441004603400446612012116040040460340381c40c242800135881184c04051524140307030140001e1409110f01c943c0031000f030034030200d000d000340c503030548540d410f68000300841e8a8903034401c0400d126400c4080182406000c6070314a0030500c0e0702901818540050038014442c80b5220b96091804401781c000c5103130401150202038540c0c0114200042c4010a100d400850410a40400f510200020061a1407958640d0250350400e1001004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 467845755 1250 467844505 467844547
    0x207140d021c1404150c020a0b030601080c0a12053c01060203090108041b0b16050f0c130b030c0603100312030603020a17150907090e03030411011b020312 68
    0x200001c90003040c03504481082102c098174010a04c1c09030304c0c50702d40030844544074410300007900150600300018481610304061030003084244c0b140c00403603854a84925590203501d800400040c55403450582840c0a984655001414151558030440002c1101811010300c041c02c01c00040d0b1154401e03480c01304103040c690241010f440558a0008148002001081c001c1e02c0600346004e409442c14901948103640f800805103411000e483d400c007804481c80d040040708065465004102c0c484142950110340300c103a2075002000342941c881c1d00210307200140300c1940c550750144100c0c680e5141903070318000514441e4541c031041c900d40505501e0101c420f40e00c074000d8003050609018081c001aa910170b501c0007902d003043d02306220501101403075468244c203007120442c0300c400c800c1401083e901c00307d00c64058940660040c0000580c40c0040c5070390740f0003150090048143c174494421250b01c10100755019100c844041182c200d807a030002403d02c07441940706110070100060003090a81c81c01c000040d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 467847005 1250 467845755 467845757
    0x80a051215030a150e1603060e120f07061107060e07080114010302132409060b03040f1209080d0203040302010305011e09020a020f03120403022b030207140d021c 71
    0x185100100c004640d482d60603d0f002011907125005500c04da01090f40000c1c05590302c20121900300d21480c04060700c101650106070340580c1001040c040303407600010041c0091103010043c0e071800c441d10070b041c00c03660011602103031902d4039800041c038580c00385006003880728000c020004180002e840d00c1d614068940e4818441030b41003031910024450040e892604490b01903551941040c0c00004480c018241c10021000b0141461b8070710460520303020340d2006491102104200c010b44568209940c0d020848006241c50112030368040056420042180500342904040c09a55100d01c8640e080140d404070a00043e88007280810a5690602455004140311030301d06031548840400d141d039000150003131074515500000c58191140c0f08014908008640c14140c944804403903860941160041d1820340040c071512a40c54041c1c5640317680451b01c80c10803155070f038141040c6c0c4016006500900c1d0241c0b80744c1e00381c00c141d890300d003002d10840d00940c0140e40509802070001d070310400034a4500700840 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 467848255 1250 467847005 467847031
    0x20f03010f1d0606090d0b1f06050f1c02250203100506010509012708071406090d061104050a0e04060614060403170705031b072705040c03080a0512 65
    0x104602c5910315000c0d42040080ea031160381c031000040800e0f01c0e803042c00c0340100600c1401c1e040007030340017903107690304225044450340080c0c25540702011107140c055102103202034a400c000c42d00028585201c03403000d010303800c44050f08040d40800e0380038102491500141880245058440c2180380038000d81c28081c140b041d00308494141000024000e02500380e0b8503042c00800f80080b405900e507060b0360000d46511281034001251944842c5840d50150310a6840c0c1000c107413044400e13840c044050340c0300c811020740700c42c0c0c16450944440e000b810b0202013454192004000101c0c20351524081c0034003400300c004000c0e05a00346494601d04031030243d0301c1007030541c142d00002c03a1035907980e1341182d00f10f0350411015132000b607001180f01070700e04c60300e44010110700c00010b803801a00140060f942c20380d0560000e640302d95641c1c1d0b0066100b882d42074074480c1e001d045c0310054504007820b58407140e0464001c3c8c20f0300d030700681c4a41da140903d5100b126140041400400ca060754030403c258000d0717106203034401c10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 467849505 1250 467848255 467848289
    0x103030e0d1101030506040e120a02060609150d0804051c03080a0c1d0a120507050934122d060e060607080c1b150c0d080601090504020f03010f 63
    0x410350a056500b001810142c6030408202c02da07481e504180c8404005400741c03502c03110520081d90055018441d15005030052200040051500403081841103003000260000000e0280812141c580154000c58103100c09200201d01500c42170401242440c161060307020446590802030940b01e8000c015001301d60815034800e621942c00100000d4044003442c0704070954880d5000201c1400a60300002c0308032420984200600c94000340101c00c40b07401381ca64408544488010007094282d90321408601481107601c55032601c80220382c1e00c410b02d80342c0341c03030b100416034080b1900680d40760820340d6001c2d442c51034402004100d072540b1491858044a41040407500d00404140b01c0341d001059244294000300e03844003840707003000854000e5030065095401000c14007c084405242c8826524003d80085054000441080040310603400c146802000300300d05124003280d03482d400401d00d504014600320002019101ca0000d08040361814030826107a44c10280b481c06021065400040101c5440c2c0c0c135 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 467850755 1250 467849505 467849513
    0x1d040309171b04090204110409060807080c01051b0307060f05010501020115030807030903020603160206010902030f0412020708071d06150a0c020a0b03010303080717071d031002120103030e0d 84
    0xd0070100710300101c80e00c1012080c02c40018002e0000d50701c00381d046428038014544244040e401030041d1207894200300042034803084403d682b55031a014084003a8403404601f1125800342000d040c8541c00c10046a0340030503400b440c01d0035500306a6048800d20303200c00310b00d0800d900798040e0601402c401e01c02004000745042c20a665201684405030032520300050341810705205a4428000d10b8014046507500e0812403040c510007812008070728010700a82c0700118030b0704903500840340640450400c1051070340340c0782ca030050b54502100004055114038039000408500074403128005100740ca5050340081c00305011500d0418005144a02c80c1403020088805140c8a030300707a030b07c030b0455440c10700303d100c07043c0c4042449000305401c0b034608040048000400c051740500600d124414580d290020021a45600c4a1215098540a01042c0d032440034210501c00760320b0341c410700e10000301103502007035122010700126070000071081e8841d00350000500c14160403002000f003c2130195500300041100382ca03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 467852005 1250 467850755 467850763
    0x60f02070506130807082425170a0e1b0108190e070b03010303020d14030703020d2901110609120a0c02030105100914010506030601050901091d04030917 67
    0x907441c411030001c5480400d03d150b01c440c1401500e07600c8220340c480d9480e800c1c0c00d551441c003880042407501d001c0090465002c0c1d054250303030140700c055a40c0e03000c40341c28819002d004041058100f0410606001c140119041d210086000d40d03081702000584014061025061401881d0f007840c0c886625040440240d911003191a80104080c0d482030180c401fa1113403c014001042c0c01501070710464201240703c1c0b41041c001c40c100d922036000c481040c0c0c1e0140042c0c0b001b4442403040c074901d800a20005201c0c40c0030b50000c20440014882c00a0100c15801c2281543d04400c43d400183e9410110b020700d465820800da41c040804500040545107454003c0c1d6a913100c0d0213074401c040c0b03e03000c42c02842460092680180540e0300400a220628114290081d000210311440c0d00060078040e44003400c0ba00450044e0503504060502c0c7e241d0354800d001074900c0d41c0301c201ca541c10413640c103000103080b80d0b480350341a19a04100d08140c6050815050040c1010003907004207410300007140240c4100f0320005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 467853255 1250 467852005 467852009
    0x10b1c0b040201020a05030a0f1b030f08101707030c0e040b010312210c0e0d020306010e100308030708011e05030d0f09090204060201050426070609020301020708120a0501060f0207 79
    0x84090606640302e00c0104c3c2407041c41d040091a91101040c020700c00b5802c540410103c500b0f5030b9604001d402080e81c504e0449844807000740104140560440c41140300744c80460703008150100c4030141581c0c6030007400c20700004030003a254a40002c1402e01c1003080c0e04203000001c00b602c4840c00303064203094690b80c040b0807040c400105a043c40c240c4510895015200c00b043d10790841000c038a2070091049070001030302015440c140042c110350002c050920b46440554503c540140040280380c1c00c00c0030f075001e00d9001403c8101d1035100018004000341d401e8006501c50303240c82d030300c00b01a945801c0c085440485440040c904000b2034860611042e14000780044252241d49010904020b0f1000281c3c3c4082e4281c02c6414a5400001d011445079015002140542d203d40d030380b080d0300e1b5500403c0c441101c2d070322425494060010010744d00403e201c0d41144940500080005141c01c5e00c42d990300380681e1264117441d84049000d01000091503013441894010400e0b03003080d001d0f00c0c9a07902c1c02502c4481c58 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 467854505 1250 467853255 467853263
    0xe031b0127031b0f06110d0b09010605070605130501021309050f04080a1d130c020f01050c03010e072106030b0a0e06010504020a050c1b1e011b0305090306040602030603010b1c 77
    0x4030b03c0c0340d0300b40f21504024040c800c3c0c00c044100500c90365000380310b42c0d5612184200d02c4007810600e0745110f42c117129a81c030b4102c07074150344e07042c0c104034095450318007820340039105174130403040d031011500030400c00c0c8020f0078918406100000c21914000b01c038016078000a0030090356110301d40400c00403540c40760449954620514081c43c0802d54082590001e106592409400a541c0c4003c00018400c0d5800036603a030f00c0710307001c85111502c51000d00303080c0c540c11100c1c815410300c2400104004e0711050a42500710402d410314411040000c03082c5001c0e020031028101e4841e4480c2c0041080c08010103510341c0001c0144010f1140e00304403081a0341e50074041c481d940c0160742c006204c1c40f4007481101640d11000080003650080f40c03000c86501703001c480c10070349288225100d01e05600c0c0701540940f81000302d101070311340241501002e84250700f0341007841c1c41034060041c00c01405e05695010311141e84160b224030001a121700348070040c5421249100081800380c01e8242d8192158090742c09032010890b80 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 467855755 1250 467854505 467854547
    0x1e11101a01110a0615091a03031e04120b0f010b0c1513050304030501050403020f03040e150a0905090604060f0b0321040e0108060403080a1109040e031b012703 70
    0xb142030a8038080c08042c0241507a450328075000d4920210000c13080c2110321034081845000ca1a1340000114058007840d96072544c030401c5450510104156101c0007103111030800c41c1420f0780c1300711141c511075441001f181c1024079102048040c0c4a4a020030380034001c0400401d04140095000d9951221202d150030040d001540005176400f14039941c0d0b2906561000c103894503a6a2480c08a020b0541980c088000d40550003a0405503c0300100369011910302950000d001d80b2648100c1803074900051541c0e0300310030022000708205030b85000e01401020043d004025a10b040c1c00c0030822504001d084109003403c2003201c1ca6117a80015041c00c88810141c00d1412144560104048a00c43ca511207a817450708240001000900032072042e1095000751a541c045a540d010300c1800c481500081e07101c0034906100c1080c2e03d0410750300c80554a000c1d68110392030300007004088010f0345a040c07462102691a1810414030158200c02e07071146900b00e094440c101183c0b17030383c081c101c501c410303411082c1c0d051 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 467857005 1250 467855755 467855777
    0x60a051e131106040f03110f01050c1b030129011106101a0403050a050706080108030f0d18140a151808070606090903112a010f1e11101a01 61
    0x144070360444c0d000b05405010b40640e241e0f2450200d5082a865050302d2046d1102c01d0031601c90f500600440c0c8901c6940c401a051039035450801c1c201041da0f83e52802d42540d69a41c40c18180072000345054141d07030060400341c0003406103100041c01490442001440341e00700e901402080c0816824503000e6444643d900b640380056019017521a005550003e00284180034880301485008100c8005030b40c516a2034807400c0c0c2e20f40d514103580b8805c1101e244c0071104100402403140d03150341c0c440070401400d44010083c0101e56100c0c8000b1120310b95410381c0d2a00090341901c01c000d040d000c94180165101070074016488080003240342c0c40101c03107020b4210280000c0c01420420f250b804200030f010030800030800d01215043c0184440004a44444035101d0000400a200125045600b5031901100e0b00320108002e0390044400c50070200041c018060400c410381d540b41e03040f0000b0811810786550300441d40d21880441c03031070303c68030802e03640c0a030386068507081184c941700d41c00c00e00700c003000e00309034050718 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 467858255 1250 467857005 467857009
    0x9070b04180b180a180507090b010816080115030213092c06131403280c020a090b04060b0301090c020d11071e15030b120c13050702030c060a051e1311 66
    0x213840c0361001046c0340580311010a0028440e440440389000030399502d44140e5138402103012075804011004089042c1200422400c2c40441e04e1110401e200c1c5000350034010b0f0400301042c0110317540c0001780c5094807192204144008180646071240188030840390000c42e41203010749440d405000c21031110b9401e0600d100b480f0700b0b010b0741000002c1520840e81c1d100b4007042c000506c00c0302a030307546003149101441002c54034444d02060010940003480946014900202c050042100900864003d038607004001103d541040145008103500500818860721b1034400a05040311030310300900340540c0c41d48441c00c141002444105454440314011a10b100681070a28103059540c405001212811040440c06e6072540140c2c4c103d55003501c0221003600744c03c0410f5200c1e0f40c01c1d182642c0020640007068442c1c00990001070b0045294015030b0310340f02e041c458040c1854421524102c03211b8890742405441d0401c640c0318041c005080041105d42d06201f41d94140111040c02c0292601c1d016582d020101c0e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 467859505 1250 467858255 467858291
    0x5120615160c030c2c0901060506180a0b0301060813060906051504060611030708070c03052a0303070f151104060201060f09200309070b04180b180a 65
    0x11089803200024607403010b02d0b00c1680300480703010031941e2020b162400141e03520b60b01c44854040d45111340722030800d40c400c3c1100c0760070440100380c0b00481d13484050001c1d40380c44000042512011600301c0c0c00103041d0398001d11101800702e0f402240d131800204010400142d0103001d42d904101511041090340c03081d4105500645238a0390042c0c2180d150400303104248100c1e0501d010040016141030000f6030ba00c10046d01c0b503003449010052207400800400c1c000401400040ca070040c400c01c03e1080d141d44984403545001010415242d24405280e24410300c08501c040801ca590f10840c02035142c8013141c0e8804041c1840b1200040c40031040344802e4030403241c03641291503450110780c911521980d80d031400a001c0c0c62140704440c0c0c0c1421400e0003141141c0c007401000c21880d44030b83c81d9404c4880d0700c1648165544010f04010f101e00400c000810f2584d80d110040005000304841003c581416400e903000f2075a81c1c051a602c10b4948821140004202c0d408966010f40c0c0c0820028481d00140806101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 467860755 1250 467859505 467859517
    0x30403170706020409090201030b09151201060803130501090f0f0b0d0e150604060f0e0708041502160b01080102072f090a020c120307050708030a09120c03030b0105120615 75
    0x8203d0012401040d07076070071a030001144034001d90741840030307216200500088200603903c1121411445000c04c0320ba0030041c0020490640309000010420359a8040074215003000f0035080c01c00c2d5040c3c40c100515a4018441c0000c0c1480b0180c0269440c50844c1c4032500000910400b040400042001100380c0c107194803014000349450240c80018112614541900c901101ca031886a8501031010884114007c58442500c101c00f104ac40252207000040d41c0d5140000c00c12a984101c4110040c58100140003502c40100703c90140d02200c113661800c07901d4082d058001c9040350b80b051041c03c0c0820f400c0ca02c0360001203603008040300c400042d0440030342c05003003c03046a82c006452030180308019002c2c0c0d0050040c044c3c00c400780e501844400c0c000c40c1d9244030586124000420030f02c1307682c010440007401503030031a414a90020300784065558110040c00e080380c120f000700700c1242c841e0080c950140180c1c14100c02c2460914607010180c40e40d260301640152141b80140e40101182100c40180400c1302c0c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 467862005 1250 467860755 467860763
    0x1e0601051012091b15080a02130503070803120a0e0309191a0309010e01020405060a0e0f0d0f0506010501020303010b0f0313020a240e01090e100e01060306060e0d02030304031707 78
    0x1426040c1010610703400c4401903007804d030325014030000d030804a0119108841e4455603910301c80e519859500c4c40690002079401c008141190700006a9650801460700144140e0015689078281c1034406140e039000108280081800d2081e542e280306004000c03100e21110807107201115407020800e842048030a50071100440f66208003003d60900386201841c4940c2d16913000348442404245240d080c0d000b24481c1580290781030100110180c0142c509501d0380c140030b0401c00040c82000300190f080c08140000740c8407149000300e09014004140012809400280002c5182d549080d04407481403040740c0700c1c102a890080302103104d20002d240240402034005181c0102c4a80783c00c410041c03160b070a01400c0000c40b01d05104a1190b006000080c070010050f100c1102091802c0d8142d44400d0300101640d240199510b4041030709000200440e010b00701c141d8000a1160500c40302030100b44002c034982d0310411540c0d0814005030340000403a0142e80d48080c0c0002c00d16400084205c00340076601c1c0045c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 467863255 1250 467862005 467862011
    0x10e0603090a06021b070519030b180d0503061c03050a03110f04143c0301180606080d2c010c0602040308030402040c030e10020a0507020301150302031e0601051012 72
    0x322145c80880000d010340d0000151071070300d503650040040503600c03030200a2490011402c104041803a00044a41c00f5284080710940003030325000c128203010700c042411001c101e000c000e02c1540d0500d040101510300780c220f01e1000c0700b030707164601a109004180d82e071410140c5801c211040000c00c0011f41c1c00d50441c41c5140781d1509d44800c1d1540350000dc0813441c80c00341c0782912400314442c92050f2045040d00042000c003200301503100c84e08100c0c84500e030076660190340720310071030002d0103801820424044c02003e0002d8110306001105040905c0b41030250b041008111810100c0c0080350140c0e0311030b502da041c03c032150b0145500113031400810801d000d4002c600c0441d00000b8403d4100003948918800c80302009100000034040e0100d906120018449600c9054210051601980280300c11800ea007452070410702c09a00013400c3d5401981060f44c1c94243c007074100f003141030400030b03403020383c4960b0300c07c4055407907026402d6a81d8005100300b40c4100079045103c09254025480002c00500d407450038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 467864505 1250 467863255 467863267
    0x1b0a0309050f0d02010c17010506070602120a0b031e102003010303080702010612050c0f011809020903190f0b1909030e01020c03010e03090402031e0112060c05030105010e0603090a0602 81
    0x160f190750422004002550900b10804071303503880340349002a0305030514911740850342488240521a0400c4004445855080000351094584011000c0c0304801c408008169180b024040c1400c285422401c06003c0002a02e14600b0034008075070003d4110b0201000907a001d03280c001c0080090301d450740e410700800000008018107038481d000c14460005900207010283e504c0b0362003005013862400c041d1003a0081001100985045060b83c00e24400516020071504a0944007000205155001c240001e40c0003030f28180504050040c0c038400e68500900c0b40c50741c2d00715100d00d5242c00310628010702002c50080081c1e000d0400400312024064458010001180a458050405070004c0c030114058850f070a41c2ca0070501d030500403840b11182ca1005075041a20407002d11002e904051b1040401d5081844140d03408000c0440e070900a1090859003a02c4e0ac240303090403000c4500c241f44001c00c00100f04011300003641c200060001d25003056504968036510741d00c5003410501150001081d45000241c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 467865755 1250 467864505 467864533
    0x1030b071d0906040f060f1514040501080c0c1f0c180b0414060d0c030516080402030606150912011a0a030b07080601050f030a0f050f1b0a030905 64
    0x20152240e5410340300e4100c1d10800084800003841c07814074003940110710b500000c0e09418550800d143c141c890a00101e06070340c55400e00c1c0c80340c07205500503040500702c001400800c0f035071024089143d000b480240d00e280508110000701248001454a196040002002000307030004000c0403080003030030080c01050004420406000c0c1005802803030021300b030924501d0800031600701480450746a00c0c095440d1a14005008400c5c0001c0c0d10682e521a80500040101c41c0c4140200f0341c01c1c404542d00050203150100d14009000c040001200400016004201c0161400110903070007030821500f000c1c0d0302d043c4201880c1c0c1445007001c0d00b9004a03035a51081003000c01500b0010300301d2000055040b01c003c411080c0b1800301e0103840f020345104030880200340c5450143e60780c160032400600d801c3d850281c0802c01002590700640b04030031000d5507168107001c403988501c17a290b00035a0a00b0b03003c099042040030b030b4416500d010034180a031070340002e84d03140c240d000c0e9001b030044c15800002c0d01c04403d18001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 467867005 1250 467865755 467865773
    0xb0c07081002120f2404090807081218100f060b0711010e180604090c050306010609080c3c03121e0c060114220c02100203150f180103 59
    0x40302e03409612110f0045202c41c042c5940051180074808011044004800d60140080305c042108030f0b00076603640c02034030118030410010b02e02507000e68006a07030b400d11075000700070300007008000c40041c101c1d1890243e00b0000114092100c1c0c000c110b40440c0c0b03051505005070040940b41e0042c02e00e2280000c03c0710800c00c449400e400c1002d001d0700d40c910b40500150a000912003802c003200c00c160400300c00604280b0f040e50007900554000d0303c540b24016250f03000b19203850401c4c0c200c0c06c0410703003400301001000700400c4140380e01d010642d00c94101e002010f0000800348180002c00c00b040d4103c400c51054405400c40074418403100404030384144403402130f046040d42c031180205804c0340064400c400010790003021580c10103283c0307000740400ea00c0d040a4041c1c107a030008001e40d2041c00d5500455080040b4281e104110a0750380e0002600342c1b8842010340307400ca0ba01c0c84014124018401c126034405103840d404000101600c2c03000100c1c04040c001040b100400ca121040600b41000100900200f10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 467868255 1250 467867005 467867017
    0x905040c0c0b060a0506070f05010912110105010815012601020a030e1513031d09010e011e0f061407060612140601030c0302010e040906091220070b0c07081002 70
    0x802c8034030341da251030307041c40400010b0780601c54100c1c00411078440003400e45003000a0240c000c0c00001010f000d01c1c2e403801c9218482e020244001100c039150862101400c0c80b0f01801082020006c1005c0700c030008121402400c1407144401001c0742d0346241c6070341c0042001c000d01030b03d2080006c542c0c0742ca11400103401404500d80c07001581c440c2022140d0302c16002c014050042c00c003c0745c60b00c1090309035a400c4601c464201150501d1031210307420002c107034550300105400f90400725000d00381c540c10a01e0307089503800581c80965110b04042410083d5074014201c2c1000c2d58828501b280342c1c50f0b011081001c061288000091201c1e02d03100c000186500700216202c1464810304d00a1128941d01801e29076078442800043c00401c0301d50010001503002d040c004140440207040817840481c682c032403104644040340d09403201030100c02c140d5a0103500510488071452450500e01c102c046da20a402d9176642e0030f02404070111000200050700c0030081151000a01d6178004030751502c1c0c81424101c010790081 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 467869505 1250 467868255 467868263
    0xa060521090c0a150e1e360403030c0807090501030c0e030a050304140d08031302181e0a0c0207121a070504060e040203060102101119030b03060108190308070905040c0c 74
    0xd02020305d040c1c5040791000904104110141001e00c3c24401003001101211001c6005028080100400e80c4d18551200403403003c0d0401001252070b0a040143c2943d19070b010300380c104618481000340721900a205881542c07820f00e070000345903251080131b854040da41c8520645c07510039405400304000b4008000c0c001e45400c900e41e805560114000d02412090900000301148824000580351541c490102c0f00400d000030403505c280c0300720203002c007001030301550104038801030f01c52701e040c03400c4051401315000070440c0e108002402c0c020800039112030050094981210310701c0c052800f4001440c0c3c642201001c46001c10007507041003030028041b031780203124520202c0c010210410f00381c40c1c80c1c82640c0c411101078001c1c040c20348560941170024050210416040d803001d03c44441c41d80301940c0c08082003402e81d20000390500054081619205050f4071800c400c1c0e11002c582d045500303003040854681681800c200802c0e4581280584101c40c294000743e4200741341150b07518260b079000210b010700c9030103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 467870755 1250 467869505 467869517
    0x203010e06011a0a0219050d0806010509030709050606070c120308090703120f090810141003022d0d0b04200603011802070b07030b0a060521090c0a15 66
    0x1803a20025103881c1c00f4402c280c641c240100c2e02c4801c0001020080412141d0361042d950059003429040c048880645001e440c03075030000d200c211203690000402d68111209003001800c00d0410b1001035a540b0300303400340d080215203d00c040340654440000b03441c081c0b980300481c18280c588500c5101c0e0b1074010705005600080807400440d94148001c64050150b0360000150450b0f20382043c420345600c154140088100011008002034018091016100c5e1010056002c204150300a260900c0030902801d1004006c000c2c030000c02c0142ea40e01c1d08400c05007900c032540a104600b400a00200c030400008984d000f02d10484407000300300c018000b4901c13681c801d4090420b03008000c411036580c8044924003c1d0040420170041c407040707564020724801d060340b1074030242c03070502e841d41c807103001034416200392022075100c1000d00114138119102001420700d44c0750003420590f002205500d000c1902a280303000420000108076500b40600070300301829000b4244c00b044030341d158400c4031101440303c82d190014003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 467872005 1250 467870755 467870771
    0xa0603090804030b04080705120c0d030608151f0e0f090a03321215030f0304050d08041d07031506140a021e0a03030501050f090f040204111204020301 66
    0x4064403410210315007151040341041e081d5914240189009801940c04540034021240000c0c020007000025008030500700c0c2d1110711400d001c030b02d42844004202c0034141441400c1c0810f41e40082d140c1c101c664030490300085070b01c41c0c0c0290619403912072044d0b42076144904000c21040012100240035070799044c65076410b940e40b01c0c041e07a200c01c8130180003400070f084904012611100c91700046481c0142c40c0c921100c04c040c4103203080741503026580c042409020305040000c640140521441000d10a4000c0c00c3c21005030300d0070307948070b1045010329885201020a10424060402e007600d0107002403400c55442490f6032108214407880840d0b403c80003034180031003991a1041a04040e00b21141a125070b551119403034201d00f01500480400d500b14402c41c0c580c250320307025141814035468000b1003d05030051341400c0003020b4941c140c200038010f0784e17400c003501c00d103880e01e040300c40d0b10041041ca45040b41c1c66910001b00507104041009080701d00104661840b0510a02c0c05400b8510840c020401d9078 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 467873255 1250 467872005 467872007
    0x6140c1611040e0a0f050d02010509061308040b0705010207140705030c010c060b040606090f0803090607060c0221040e0a111614100204090c02011e0b03031204110a06 73
    0x300c9400100048405140c0161000405921a124407080c00900114103600c101d15003074900440c680d0203403507150f01100e00c40c040c0b010a201e6460032105910003800719241045090340d9600000c0c020302c20b05895110b0200074054a141920082d10b12200a150342e9051403c0080c040d410281081cbc400700100303030340c0092000001030110102d170f0002d80504032110786e0800545c0c82071441c04082d034000d6150883c0d16229551485a00c02400700c6842d5014018208103001004481075000307248141d01c10440c910007586c40301e05036a001c0b40c0c0400d0100f01c607400c0340e2042341482c1010180340140513048604194841062016200762100340c2e00040180d55100840010b40d5880c400720030782c542d01000040e0050842118020220f8003c6501c0c941250301e99611a1514024481d690030700c03907012400784000c180e24001e081d1348040520003030006501010840301c2204070f0400080e0040e40d6144003036010749080c000d60305484254402c0a60300c1c0342c0350500490704104440f01a104054042e000b003109 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 467874505 1250 467873255 467873257
    0x15011b11150d2c0a0c05130f06030336030b0c0c060115031a090408130b070b040204050a0b0906090711060103051501082404080904090606030b0606040e190204080a06140c 75
    0x20340000c00780d22111b1614080c003c4451b140420351a110341c80b04100144c600b180c0c040c0000861103a5101000329a4800022603800d01000700504402c10280304030391142c1340c03a1540b4041c0d94200418080d252501d1920054074850524000c031540104000000c52480a400c000c001540e81d46052203103240642e080c0e1071802c02d68040607071200d8540e02090114692070060549042c807980149005511403211300030360b03080058200e03040c185000c100070071401c2a014058100349020402e101c0c41d0204000a40e98000040c2214055010240040d00c004e12504080d42c0380311380501075580950f16410456103600503102c1e80b601c0070383c6a000000d401400000cbc0081860205107090180201030310601c00301c0b07030f0054000d44154006100b840283d03179803441281d400745d1190200264651131440c00c1004618000c0101d0b22a041c03e200402080007480c02c0c89500c1107200130b00c1071491440e208000b0003801a0f8009180314400c1c1060300c0d0802002d41c1c0040c801000070f004240d8641d844940704811 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 467875755 1250 467874505 467874523
    0x5040c02150703180b07030b0402090f09061c050f1501050616020a1d0a06140f010c1e0807030e0f01050406030e070b0315011b11150d2c 60
    0x5070301c040340300c40e28a400d15107216000500c62030003290b03045040440903007004038500255030b210901002d100c120b981503c50640c0c039620640e029814800310000080c441850503113010301890900300080c0480d500c0e085805180110280149082c0406042c56591105d460340848558440c02812000c1406400c82240c100c0318000c0c20145072604c0d242c0c0c104c0b02d40b041d02d00c08a804c6009000042641d150031003205501042c803140b071200ca868003540352407d64406500400b82c12840350300c0900e035510b51007003d0507150303420300b00311a20340350034a0a900082c50701e22152030b904c6c00010b0f00c6030400c4601c0d401401481d01903902c1c0965000d03000c1c100204400a5019240403480403c0704000082c002c1c6c0084403d0350300141a10500340d5518a211207a03801240c0c280c1c444400c1d0520040f4940e000610f2880e400c02048091010002c01c0d9160031041000c02c00c200d118042200d84190b00c421400101c0b0221136003004140700f600340c0c201580705140c03c0e04040407044031b00c0c070b112000c0d044800548020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 467877005 1250 467875755 467875757
    0x402040e071809060603020c15010302310504050a0c0602010614130e0703120f0309080f0f190507030305010806060d032111070323030c091807110705040c 68
    0x80c154403420303400e0311001c0030095618a403050400c1c000443c2c00c840c3c441c2c20300805a6407130259464141d01511424241d040500c2110103200000500c05a1038000100101300000920002248105071400184113900fa644601c494201804c0108101e0045004c0107154400d40d00d5800280c0c80b0340c1d00342d003a24554000c1d501d02c00c411190007059403074868203e2041e0510316000103164800420320700d0a001040d0811f581c5a80405d00000c002a0700000b5642c2c00da403140b034100220661545d980e071a0748900120403810b1400480c90322146103000c0111010180d8804199149400c500009440c6d500404000d07008245040b00000704c01c20081040c51249030000c2202441984030347d800e540d615180c0d41c04034280b10b14071040c0701c110591441550142003c400029480f1181486c004103c0c005100040c000114000c0c2c0f8040d46902450550b9008071355844101d071908186070120b0f07141101c0c405920311f000c0c00c0302c09000103e60003100300d81201d000b841c00d44010340d44400500c825503c3c0c4581d01c80c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 467878255 1250 467877005 467877029
    0x30418090209180d03020a0e09040c0f08030a080408070507051c06050c03041a041407080307050f010b030a14010b06030411010f031a0118090c02062232061014040204 73
    0x1200c15100c6d038003c1000515605004a014030010080f4001c036108981c201c90742c1c0025a024032403040b04a41d003c00500081d4019440c14288040050800b07002410041203800085032800420034244031a030050308001d07001c1d0792a18018030608c1451040244295050741c645004034221040d000200c1e441103810035524042840d0b00982c104000700010001d40b100402881d501d41b81e2001800701200603c41c41009607142e94141c20182e0928104400305402c0368580400c0e4a41618041402004c05810014134201caa0001d24150b01520b00d200030b89a2142d0004204410081000142c2d0011442030341e4140108041c0481602165029480040040c0051122604d198820032103080a081d60012980c8519a1484428261a1052880005608070004118082d0000d90b5451044010599017025095103902c070100b0a11603160310381c6000e0741d90740c2c03240c040e00e4004101401a540e03680840e90546000c0758090b0080c40103000c0d4480341d1040300da00081514050080d1007d40e02034013850 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 467879505 1250 467878255 467878273
    0x7150c030c0f0507030804260610050108040311030706091b0b1803070504020d0204300b06011e020c040605060702030309040902011e0905090106050304110103020c03041809020918 79
    0x900300180c000304440380c0c81013400c003100140780200034100a00c2c0c09485c40180185080c140d00111403030051994899008804004401102c0c6081c00105d40c0203017014406034840b82030072505561245402000c6200000300300301005403030340c0022841801a0940c808a804074050035141501078441c0c02500c00f0203116004c01000da82860b09500e1400904849001303994601040a98101048902200d41e001c601001019038103402d400001c239811001907441680303400c0240c200441d000001e411100308000044480c0d001e01c0b14507600003d4552500d0b09290345d901c0003561011401d100600903030a06200003002d042035400d88031000c0d4000c019500703024080003400020b100d44001a41045402d20540307000c01034440444055400d01d9443c0c13400c81703007840b00b4030000d080103a2045003004030800c10400800c20982c000c00b0480700c240b0380507a403620344107403162440c040ea8000001d142406a1500c415058030307030024207420710a82e0007640c20364079204826a100070a4940408981068410b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 467880755 1250 467879505 467879513
    0x40212010b03010501030f02100503090604080307030605090f19200a0c020a0b0c0c010c0201020a110f060c010b0310060e360c030c09090a0201080c0c060907150c030c 73
    0x1204010840002880c02114000030703080d01d800380e0003070b5103140d00b0742502015424402c240d0002c1080c1800d00910318104000f03a180e4806008201800442000c00406d007000d01c031703810903001000000c0072000d09042c0f5240000713011000303441c00030545c01e50803010440c484060188480001040405217042c40219810040b030380c2c0078101d80310400c061001c400340140d031404446400303843c1c1c01b8100b54840a82c210490307d030082e0441382505000021052400503a40007a2101d940f80e480003c4003181c030507040201e400010321b801a107502c1031001c00e60300101c500560200d62321800880072545c0c41520340444400300c0e0094011900d154644d603000a005211006040310000c0051007015500c0d1560313802c0e41d0300038003400c44c0c0380c1042d0852001e1100c40c0c42c0c01c004800051100319607a50090520350b03041c0d5074442500c50002d0501c02c0c4980041da03c0e07071020781a502d4600e650801e507070181c44d22040040c0c0310007007801503c0003688110034001140384245c50540c051941030301e4059600b400c50700d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 467882005 1250 467880755 467880769
    0x60f05030a02240f070309060512010b0d0902101211130b0a021906020403020126150f420906091c0303020405011b05060c090a0806090706260402 64
    0x810b160a6100140e0540360482c0c0f41d4002d1100601400080d5294211450f0013421303004164480d0701041001d200102c604440030341705604503040110784607902c03018406940c1c0600780d0440040c2d1701841c00303600e40c0300711500400900740344c0e41c80200c10007540e40c0012080c0000d02601d5424504541c00203001e01c44400400004c200403000b50048503c80222030b07410030b07285401507004030b4915802240810865802101000002d482d0700007495082041503001604200000c260345040903110418411645036410800c21140015000c00003252040d00a001c4000c00e1134442c00702203904440b022101320000d494107000c08040030141d482d0260300740401c0303190740100000c144d00c4000001450054540d929505443d42c0c8692405038503a441c180024041198941b0000011045410b201e00019400b04020f07501c903000b42d1450741c40707140c2c1d0004110750000ca600410400d214501c00d105001c41c002505908484140d5518413245080c035250320311086200071f6564a8024030008100145441c02c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 467883255 1250 467882005 467882029
    0x803060307030b10031518080a0c0b091c050c1504210f030e0c0a1223150c25021513050a060201050403050a03050910061701060f05030a02 61
    0x40880e141d464580d2118000300106486400400050304020002c10410145400c0c428410202c00c01c00003800703c0c480c6500380503602e00100014000074480f0b140b0b03401000051300071604114181d540e03242c003003051641c41d8030303c00310502c2e02001c440141010511603c100d500d030400140292005540074072040c04054006002195083c2c0302c02c00502c0d80c1c010710381c15440750310490340e501488080580001f808581c90100b20440350b0300400c2901c071040d1259211340c4100d89855886951140c868104082e048565a41100e10700300d110041e050200c100003407825400c810f15a040c241a1a0220307018100e109006c00c2c403c7c00c01c0008021000981041d0400d2800c034005400c0c98144086030b10380f1304c46d030760055148191484540c88207002904001901c00003070b11450000b0401800c203503e001e00070b800ba0b000440d04058a490000303c0f8100140003a0301050003a0342c0500030316407501d2605a44c3c248003890000303113600c0c0c150001409480c00720044126803020f405454440c030b1540038041000e02c04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 467884505 1250 467883255 467883259
    0x1060b040b0d090b1f081623030f0321040b0708040201021501080706080901022104060b040f051801050606041a0702030f07061205100b0a030e0d08091204030f080306 73
    0xf04400d0011510303612a00e44600074180541c0002d28104000c3c20800c11140c200c22a103a100b2400000800c420000f2401a10844030f910100c3c007c080001e40f100111b0014829018000c503800091000b00000c0500001c000c10070780300104c290700606007040e0b80c50885000e0420900340b000325182900807095581c01a0040c0f0568034400b110303402d42044100d080c0e0003460503500005080000650280b078040c0c100c03101c40002e5242243c050944081188030305848440098660040340c06c1140d02d5001c05000c94024100384074800b07110300f10400a0000300d40c905a83d60010221402c08541840f4091040c140100a242000e0a268540800c5c0030501401134400100300b2080025a0342042102404210b140c01441880d0a056004100c0b0107240b1050b0344043c2450180030200d003809180070240c801c2046015260200c100048002e0000300708a20541d0168451803640b499004924621070980c0c241181c400c21410001381015206910010308480b0000d58004001100c8500441d080a00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 467885755 1250 467884505 467884511
    0x20c0d0609151119030b0f10051308030a090611061603020c07030f02011e0c02090705250c0f0803040311120d02030c060f0103030203030a05041b0b1b01060b040b0d 72
    0x850003200311480d1142080440901192413000f00408410800c0c260401e450184070140b908070104400701c2184000c54842d4006244110b510b03489030003595040d11149074020350f0f56903200e078240d07242c1e070260040c030b400100301c50303001710700d086c0120710b01100f441708d06000307000b103030b90301d10503940200041d00c50902050f400300704400b03c40c081000f9040143d8041c2c160842407809510000d414000044440000841c07c05490680d5540050b0080d84840d0113854124041d503600c54125814442c004040340c2a81204014030280c00b5441200100244241c00d000b000030344518000080c0841841103420070780c800c000620008542600c1c090702401302030100c2e00081001190075080c19514000c03100181c0c130110b819018906c0030003080d50402d0008600c15015415602c009441c2c8c40001c000102c0309441d440070070108650420322411610f1542c42030500070fa15000388100035032040c8043c500c504042c9030f0068184e0300c1849004116003441042525251900a840040d6000b00c1c0c88403005c280d07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 467887005 1250 467885755 467885783
    0x6182003123c070803010e0a0b0303031503030f0c0d0e0405090717030405060c1501050603040b0a0510150c0c17071e0e010f0503060f01060f030905190c03030f020c0d0609 75
    0x45410042d001d080c0c45100110384035810084107d0000314028004d100391400c0c080e550005481c08011030303410645182003014400c801c1400f02e4170314418000726800d0010000340341c40040002258514140d20740c0d60b00c800300813901004010035210141c5a104041c3c1044104210703c100d60f000000404007207c00796800c10355210001036242e004082e0320b0800e900301c40758100040c80901e540718054201200c0840c00d40c142034a44032188207005102c10301940d0f0355008102c0481d10f55096030000d04090046010100310307810010004680d83c3c2c030440c1c803c104c031000032501488040c0c4503c1e40d010750100522070640307803541300501010000d410220317000e207001000c0b48050b200c44105010702000b82519280500d02000e25161900003440900301c00309820040c814a0741c0304400903106030b071a1401148a107500d040103810a50048018000050b5440100701045240260041100c4c0652141d054807000f8105c280d89400703511380c049178421030010380c038030020b1002c1e4000300d6158007503190284103007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 467888255 1250 467887005 467887117
    0x6030c04092105120907030503070605281d0714010c17030702011b0509030a02132c160e010b0a0311220609030f0618200312 55
    0x110b80300035240003400c0090f4202804d80d568410b503070003036032a0008146c4c031803030b580b941070721f034004c0b0301006100d20b0316100071620507903c1c1541100a400d00c61a1a098141540c64240007400800414281c001220300c14a44a240101e00207040b64845451005c914000c10011100f00104503021101c9001350034003440b855110002842c8038404a0f0000684c1442000340c1100b002c016503030410400408002e000400d40b00031904801b21503042d60440402403135203202401804c88149481c0d210001444401c1400c401948408040b6481901741c6010408000c0408a101c0c0c8500402c24280802c030010011408002d002b0004040285000605c0480800c900e00352680014000e0b030040d607440003120380c200400048480245030f2401c01102e124919585d04070180341b80c40c0e000d090141c0d034200201e0a000760a00301c2c4091713684164050301c144030104c05500200c0151352528080d1003044110f174049840403048034004040e005003081d84450010b00200c0055880102071200f1000c0040c2030022 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 467889505 1250 467888255 467888303
    0x312030405030f16032c010e01111b0405010b090105040b0a0224100e1501030221010605130510050d180804061d060a050702100e0d080904050603010506030c0409 71
    0x211920210440000381e42d1709000740389050902d0048100c509100508001150500c000c02ca4014213003440400b0240180058804c2102c43c01901303440e004881c1090988800341c511b0031000941218100100d90700c802400017540221070159010270307030400060101040d04805490f03601c4491040b50360307601c2c0c11060700310040d2440580c40820b03490202030160016001252a0280c42c00d829541030510f080304183e8803c1211075031307041c145940095540d4840031300c00ca4a2a07121200e964070180c55a4440000741194018034500b01c65070300c940350201744c2e0701d08401da1913003405e0242d613000c0c04c0c0050b100000c8014040c45000386092a011a0448001a01c070000b503c01080c094846140b240e0344d005408054861032400720740b01d40c03000c203c45904140c101c0181c400d4150140c458054a00e607002090320061018a44643c2c402c020202c05000c1101d4000101102c8905a5042c0300d10b1300c0302414542628400d0380c04540c140c029014001c50380c01e1540c000c03403070f040c060090000600c1e08109913580c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 467890755 1250 467889505 467889517
    0xc0a0206040b0c072f040c02060c07080c120307021b0d06020d020702090c09191a0a020f062a032401050f0f07020a0b0f0301090b0111100606120204050312030405030f 73
    0x40d4098003200300e0460313030171103c01c2c0805040d5424044e4107000f401c000d40321200240803400030342002c03c40750300b40300c1c20201f030f0b0f060b00506c00704899070003545210f1001c0c00e4104807044801440b03000c0721010100e44031a10951614030207002201681020f07074400300607400a03900c1e941e800380d0901c1104050b0796601d001038020710b0003a2501d80c4c2c40c0340040c240165003c4150070744861031500d040c10001034406e218a50b90340c03942041c40c40c0c6c071401c08003c2242170180200d00c02c004c80c4030b00024086000d2516020403190f0006050003030802a1a0100c0200e6020841e541c90041c68a0918866001d0202c556510721403070514003186040c448100089843d0858500307240f4004002c1221021410004824800b405442400604008042c014a0000c0c4014003c02c100aa00c50900d0f1000d41d003c0d11104000c0c640714015607842f0f00064041c1002441103200702c000050b0140b40e0422111003038400c179001c0d0368010f40a04009036651b84a100c0551000d00308884a100c10050f140345509100e001c4c0c50 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 467892005 1250 467890755 467890793
    0x1d0d02100314090102070b040b040807020d030915030c050702131104090b19051f0221120c03010602070302150904090b160215010510210e01050c0a0206040b0c07 71
    0x1610201c1e802c03040340d0950b000b8940b00c5945c0c41040307a08041010f5102e11580a544000040220340d15454611014019203c0003500804529a02c20806800c02c248405a0381c540d003c2c9504018a55402c4042e0380000310b440010500420204000d8100307c1c40d4401c0d00107116401040c46c050711402c00685034000c0c0e000d481085d543e403000e50901d142c980300c1079101c65000390480c6c3e01e49080000041276000c00c05c0700c031041141c2c04030794501e86500a11002c60a2141403405192f041d41c1c8042d6501d00b0b034414522094190151000500d9000500040d40d0603240326070f00030002c080c150b80c00d00c075034003180e110219924039050010b155150b40d24011020000d2007540584000c0c1030207010194102da01118140942d00f202800c44512104450310360b0440341d00725a00d02c0b041c1d80b80d00d810b035400c142806010344900c2c01801d00b40002401c13070300700c1c11052500b0b600030082a43c40001110650003a08646401600241d01003004541039440e1342d078100f40348a805500e042c1040e40c8800c5c2c52942e52407185 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 467893255 1250 467892005 467892011
    0x90a0e070b07030207050303030f0f090111040603050603060a0c2f010203041b0801050411040b0f0409030207150c020907110f07031208010b07020a0e09010207080c0105061207061d0d021003 83
    0xb000c143c0d05001030001401c1c184c00540c00d42c200304080c440402c8000308040c0d41c04510f00000344c2072100940009011140b401e08066944c0c1d200e240003030140c403044079814040c0c8078140205400741c01a202c1d45081e402c8550f9480490a105420b424440320215030a03040c072240c80c0b590040602080c4003c50083d4480c20001d209030f1040d080c0380c4050552540049000d03413500080001103000030400d84000302044900007181201e820000d40500d407801e9510390411f2070705034180c0401d500099060140c4019001c50504c801d4003500440c3c5501c90400020340028151000c60951401354010a00c00401c0b40d080c1c8512101c0d89040d0b9141280032740c800d5509844aa000c50441034114052a004d4405884407920780703074958000c164100503c0c4a1480d00e24405000a15820001c0d41500d004540c4a2040c0740d940301080c06e014040c0006a9099214003c0403105070100c5c03500142140031200103882e0030100015500c2d00d1061039044014044c2c0010004250100580e41c44a00ca001c0b03c0180d1000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 467894505 1250 467893255 467893267
    0x10e1906080319090e0a0209130212090c03010b0303190903050f061e090a020f0102031b0105010e0a0510061b0606080d03050a0b030c09130212071a090f090a0e070b 72
    0x56141c00210024030040c0b0401358814441c000840b4602035000803803060150344e80310640e010a01b2015000c0306035020318808a0000181d002501c803150007225200d08845503103079040101401c0b5443c580c0c10643c1540f04001d114101d49030401100300d07001450170100e003141d0380d0b070b140c141c10048141c80c2420590011410003018607007203603120701114100c922524031460440502a034900c0d4128012b40b04101026120344260720030001c540080428050422051140950980c0078140c00e014600001c4854400101c00c84218854544901c054041554a081c5443d40c2900c0c44078140000094898a10702c80b00c02040150041c0e100514a08006191003905031000902302c9801408480b02c803414404600039580d4006900312400c2c00407101d202d9030b83c0f1903016101c3d0085806e00001c3d003041c2c8030461003200c0d400c0801d485d02150350201c1e103445920340498200026116100003a54080340040030368140381003d0302825070140d000d240004403800d44403030151415140c0d5200650481001480c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 467895755 1250 467894505 467894527
    0x8060301150b190207060c06051503100903022503020d0f02040513230706050f04030615050a061b0f1e050105060a09060e0106030903020a0602030f10080c0108010e19060803 76
    0x1803500c00324501c042c00c17126040c21002014500d8002c0007611154070b03540810500e920110002c0781c0400000c04984405c800c04001c030707014205222003076000d40640c10700d0241c60580305515103104288050f00041080c2541c1c00c0141b0b180304107a003030355029461030700b00e030058840384110b500a90350912058000d900914200700b400520030003800105510310022540d0b8030340041c1c3c3c242030b05c5c1c07142415900c0e4086020104c03203034066540003402d05400c0148000302054030640c5078007980c8082d1607610303110b51104804d50324480d40074901a18070681035134000101e0400a074211926101d00340c0c1d10b800e000507a40e0101c00014069080e01c150b5924410b003c41454107a800c5401084401d0040c44110720b060204140404148588014103448a0aa0741098401e00c158615140e1042c1c0454aa080094060542030011104203042105400010a9000780003500e2088200140c2d1480c09507800c0c04640d5003901c034050f0081c030708500480c6084130750718028000c0d81d000c0c29207117000f1034a50a200303407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 467897005 1250 467895755 467895787
    0xe0a0207110303070209060105090d0506010902070c051009090b0d0b0f07090503010b060318030f0f090301380f040c02010b0f12150408120a02090f100f08060301150b 73
    0x2189a02c6036100300724200040e1a90307a081544540f00342481922450110301080e45104001401440c50082070004640003c0540c00340009d00c0c011200e4548268540c0240000c43c2c240da8940c1001c1460750a08204c010810742140018a40240091700e64004a55613031440c031138251501e05182c0c200e001044180c5611420b070790000d000031030003031184061f44070200f03849110140600c0824041030b0760b100c0501c3d00400413114016045c11506554240072420161796401503014035100303500b1f1000c9440c41c81c90307050301c1600361800080b084921500a19260803401c0041030180e8000800501c0f18070107a031684542420311607203400200f0104491010070207544059006540b1458190441040800d0001010022001c01280450403a141c501f03200106001301c004031a1400109001c11140c03d40c940c000e410900c02c20b58002420f846000c00300903103400030b034040400056005000c4208a840780007110b40168025000040040c007012499080c0300c83c91300140805440000c4030504802988 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 467898255 1250 467897005 467897033
    0x9150510031409030a17150315090609030a1e031b03020717030c250501020723060910090804090207080301060801080307150c031515180e0a090c0e0a0207 68
    0x401031860445074075006081c01d06098800b0304072140d0b0600041c507c07401600302c25440d45008040381d800c0004c8000c000b0425000315030000b41402960085500e0345000019600e001c41103442c2c406841c41070040071803415104000c030804141c0c0794100e044600b03a0100103982d58450a40c1e002d40e41d01494245245034520b07800303c6503400c0c802082080031840c0d4560070355100c20050306862110042507442100803c1700b488010705154400519842042000c28200c680c000420030682610142c041a09840e16821103404c030030340d001201c40101c1440f00b54040501244a02c0d00d1750304054807240110100d0300090800c0b03483c0000000107015060704100d645006108000080d45031550b5551144400b44a1040074021142c403034280c812020b01a400c11900c1011076002c1d89030302e99840300003580200c001d0601001052184880701441800350307000d881903510364250580180c0780c5281c001c0041a00210988068500441c007295051200000070b0044c403442300c0142e00c49489080c100078041c0c0503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 467899505 1250 467898255 467898271
    0x6010e0a030302061e040809150708040801050103111f0f050403060501030b1512030a03200a0e01030507180e0928150e060a0f0216060203161107091505100314 70
    0x1c0b00c10030000030080000c542d2141c07000e49d000c0c4002480070303183c1a41ca01486000500c0341d00081408240d900301544410b048a0260010914000141c0b0a01400b90986040c0d04810105a21034a403540d020f8591841002040d2030440c3c5480d41d65224003044034400e80003241d4810152040c003400a41c2c0b021700100e100421504504210f03200e0444d56628464017600740140f68460003444101040c0c002521207040031401c2030f5540c0c080d50103000b4200c4c4008182c150200345800d010980051250403040101c00c0300302031032444941004030070040c41c84002c02000051040c0b038050302180d01000c0e0003229804020717100b503c000800d4500907400e10b02c0a01150444c03460100c40c42c0c90702c0000114181c1001d50441e00046801c0b0300c44010002c0d1144d0384c2c4c40038209004c0324049003003010310350083d4030490040c0140160200c0080044071680b0400c03400c0350069022513020300a0070f55580c044840b209840062174403040d51840410300842c041d60303840c000f281d40c0300c0c6943c0448110050469228000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 467900755 1250 467899505 467899561
    0x10020a051b0d030e1c05060402040c0e0303040501141603090305060f0f010b0304020a0e0106090302040f110318010f060b0c0d0908120702032a0307080d0c0b06010e0a03030206 77
    0x18403070100340b250440100240420080010403940e688071076502030b40601e00c0c103592142203041070915999036481510100d010310321345090b0441b402e201714010054020300030003444ca020720f004011542c02d140701003148084c0b2820400c0c0002211700030040d20920b03200351116128140b440c24500c2c20300500401c02d0080d2000d49040150341c44503001e120703040d40d240000107500d03500c80c0d002255041280340c101d504d0080e10080013245454001c01100100c82c401c0300c0610000c501d0000c0e00c0141c880202a40c501a04c0900c0418a5500d80841e0725401e01b030040000100d45005c0703819607082d01d50743e80c01092285000110511035007028000c5484518080c1448000c1a04e4001000c2c4d69082c2c8c0f000c20100c007140400e00320119034041c01008284503c02c40b1a118125105142d15003004020441038803d02c01c2100000c0c80c4003001c12581810450368580480e044026180c62880b081c0041ca01c40c1008081c4801044942d0743d50f4810003c0e60081d4001c000900d40f041080300e007051084445a450301c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 467902005 1250 467900755 467900803
    0x120617060a0902011e110a110a24081b0d0c0f020d021203060409061401080717030406181d0403030b040603170a05040512010207120801050108130c0510020a05 70
    0x6004940070f055403d1782510110aa01c62075000c4030a2241015640050b020b12200e00c070501041c0c030002c20016004941c0220b40c5940c030440c9064154006c00030511035982c410308140e8250203207650f103511004450690005090044040865500103000d8100c15580d0f5401c13084015481010301d41810000c0c0000c2065000c4e640010b56104940c4070410a900c400100081c020781f684d0700310156199100a007408814224182070400040900500e4058451a000060006400c0380b6454040407030070059071509007007200444078940061010318040c00700520000d101300582a14540e15014008881500c1c1014903005042d03d40e0b01c07525611032070804005101280001000700e000c02b130500c00140d5508061041501c150040d030b0300680e8004030000c41114401e60640040500304c1c0b084d54007500381e844020058810042c20f0080d240014105030010f42c10403c100180c0c001d0b10b001d11145400240e44800088000f100d4543c040016080815510200030081000042c80c001c0031300700d684010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 467903255 1250 467902005 467902007
    0x1125050a03051009050115030c080c060f0301150306051309170a021002070c08070b190302120604020c0c1011071202010e090a060e0c19080910020a120617060a090201 73
    0x401010507800707015500d801c0c04c0100902540300000c013060840c0110b5026230389080030295207410741706188c1c05002c0c80c16408441d24124080702c0070036082c103c4142c1181d00305058400703030304560301d07071842455510700e00442d456036404ac2c01e5494403012480401c9003202460800c008041c00c81c21131030b920509102c940d204503008502842d10403a649401a120011418a8900340509502c003c4c0c07039000703814001c100405007100400d000b031180652803030000c4000790110100d100b00c44a850001e0031403004100c2601e081e40041604100040460b000e44419200044041c840c800e41c1c0740c04201c0700368299540d00800e001d0f1400900d0401d181c1d000102540e00040c0000240b52500b500c90035030240042c1010300943c0c850009000321484840e42840c28003000f8005901544a00307801c0c0c80d20b1080104c44d5403040003624030906000d0090046507000000c03110280d088403040c481444485101000000ca10740319500040040c0d010484a18400e0703034050b03081c0003001c1c000601c00c0742050b88140150b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 467904505 1250 467903255 467903263
    0x6050a0516090b09062a0609060c040302030606010c1a0705180102060108060402010315090501121505070c1209050618041103042001030b100809011802031203071125050a0305 77
    0x4c90103840e000e03522070350300c0da0f1061040402c41468200c0001110084c1282c41e0010742548201ca59104841b41900e42c5075042c202c0c0d015070302c0000d5150384002c00040b040c2d441400343c500c9661144034840c09880d118a150b0851150403140b06c3c00080001c00c41007000c42e21581301111591003070000d4000da50401280c03075140ca02c0104046c1c18140c03211000402d086240d60500c00400c6800800c20180d41c59050701c001c03048140c04155401c0240d2124148150003610483c0d00401498940d541c02c180540d8521b0b60b0086180c665506106070365000007000c1d1100e80c0108041b4110070000c240e4500808200411914891050956114280200400120240c01c07400c6007130310482502c01c12156030700048014004020700c01d90805c49401d003011145400800250003040d128000b40100c400f002c4005410703c5000c14080d6155000b080c003d90725030307141e200031500080319140040880a01480f10303841e020030340c0000d144451030003103507000f0922242521009080102c0d006441a4656100d0640d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 467905755 1250 467904505 467904517
    0x20f071d010e060a0503070b070b0a0b030303070e04020c01060b19020f070b09030109060c110c060306151e0406020303040c06050418021c05100609350a06050a0516090b 74
    0x403610b0804a0020f54a01c42d42a004190080480300c0c02910740c0a030360425040080c088803c0b4111001040580c0c3c0c0c680154030004c84058015800c1d5610003004803072000e1071280640d0010750800007508114402e000d000e0181c640c500b42c0c0c0b0342d0740104086040a0004c5040200c0440d004045041c04404011070b00314100c1d980c5851094942c0300500011340100002c89008118903d00660008116000222100f821880009842c6400c0141c42880b005102c00c40319154040301010500d050782c0e0300c3c0d4000c0c048151100c0c640003050144401e01c1c0c003169019030403039005a440441040100040c10f00c48102600e024039000341803620f051803d80c900300d0b412445201494012440e04004069084208440080c0c1c40f0188814200004e00c05805020390054a0009614a001217411030002000d0b0601c40c0503a6a00c84100200c0350032411401d00c101d0301070703219000340902000490200d00074507028488041d0000b03120305207208640208444280058203000f100c02041180c407180c2000c0d180 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 467907005 1250 467905755 467905769
    0xb0d02060c0f0312090123011a070c0308091c08030103081c0f0f060f180915090305180306060a03060b030307140106050319080a030b130903020f071d01 67
    0x1840e001c440242604103410460b580b9103a1001140c600d00030425156803500801d00500200b00c0400340340c0101070f0b610710345030031850f0302c07441c4400410942e0180c8c0d00e81034021180b25940c2e400d0014075940e620654545074003da13180e1070081482e20003445d0807090891041429040003120070102e590f80c0056000511018089c0c00703021a10341c0851090225003c0460f4103050b003000160242ca81003401040709180321004146410804100d02c03290041c0b00040d510a0003210b018a03020204003405000c01d00011508504c004d5411a10030035240200b8482c903200f9107910781c54000f20690000d0300303800310800b10707c258401c0042c1703c45030f00e03a10031040a0301c0e00128041507a203481c01c046841c40c03091003801429140c41e402040c4682c40190b02c19000d44104505680703000c1301081000041c1180c0743c0b07010740322560402c00700c0003650103a44401030161010b8034104038518900c55032412160038070010f601581007800c2075901300a0911038100030380301c15052000080048a403840d000141401000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 467908255 1250 467907005 467907007
    0x1d0a02040b0607050f071806050102030d0902030a0803010906080c0105030c03040308280608010b0a080709050603100218010210150e0402030a0206030405070e15061611060d020405010e040b0d0206 86
    0x2001c54942c1c01c00c4480542e046822590380028100480317039200d02e0740c0b01e45000001240300d03422090b9600e019041c12220144d00445c00c0401032140d0030001e01c280c1008980c580303c1da0300001c0010301100c0c0658000e02e14484001042c40c40c2080c0541042150002907041100400801c40d0121b01d01d01a00e80064052909070819502e100300240e402c2c40d0700300c05602c0741100d050496004450f680005003500c0c1d04000030700048050200b0300c8840d41e25805280e04640016800b070205000d258801940003200600b150407490b910100d66089a200904100071101c42c85d910800035601003103504400e00d16070000700304000d07100081a0318981140548801074004001140540d9010000c03441d065400521855072820a80f820a0faa0b0149100e00b1f00340f1a151000106000c1c058903844000403c081c0c05c9510700401490519001251170b1000c9031800c0041c000e5150b40c1c6c40365000381022584d1503100503520b9080100140406103014034131842a82081d0030440342d9140d88803a035071031030780c180e0f445 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 467909505 1250 467908255 467908271
    0x10303121515091505040e0405010b09190507080103030503011202060c010509060f0f010303050a0509220c0314010302061206010c2a08011b0503180a0c06031d0a0204 73
    0x40d40207001c0d200a0322040051007000891141c149000300e40351284207840b1101901c0d59404514146a609200000403a07018001000f808140c0070810f1b0b40030348034800018040c0d00e410001504000191040c0808a4040202c51948185032085d203400c403d0710304142c14950302d1650014070ba444140180c3c8031f0701d4074003030500e800c42d01c0f00701c10385d40c020113524000d100500c0c1c1208400e554101c100c520181103072841d4041100c4440101020341600d4141d92100d103004500502a030745603010a0b0f00e66002060305001080c4ea41c0216400ba40d2900c9958000c00e000f41e0410006043e81c2c0e128501326a80e02c0f5600c01080140c5c1c810b4121035400d52103510b21841070b03548a0069441d00030b070b00006000202d80c0d14019262080944201c4007010100070b1804d581038550203140c0c01c8850b01c4003030386070700c031140c1c0001c8200d54052800380d9482121019180300c4500c0d29810181010000c0400302c681d5012440c0c2804526014000c0c0b0800d10102546074008402e0581c50755902c080790700300603029541d90041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 467910755 1250 467909505 467909537
    0x717210c1e0708070308031e0106050702061e0705100501060f0215060303090603100602100903080a0b15180f040216201509011205070e01083402011112010303 70
    0x2c0310740182040400d40c0d200769074a09040d4080e5004440040002401000d0410380308080098903041e20705039543d0505008840e0700b17100035a481007640d40c03d40700d40487c00d5441100e440000308406441480034180703c4500007661001e944068214205000c66a07059401c450790003d020b90113800490f40450082e00d616000c0303030640c41850304841c0c00c110000300301711121041c02d5055049038040e0782190000d21a620000701259544035008000030740700c401180c5161916041204018402440300d51078070350481e120f80e0780f548420b02e14440c441100c0003424041c03401c0c02c006080303040207072800e601c0e01074000032510b030484031a01c1c003c3c40503105079054440d2802c8100c58000c0301401801412510941c2116090240c222000d20f900003001468030039104800c5004941c05418940c9602030b0480407480103440e0118024a41d03145000c400c042660600c110088401402c00b200c800c019944452500080c01c1d10312002c0d18507031003441005400106050300c41806e0442c4d4051408160b020090a1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 467912005 1250 467910755 467910763
    0x6120a0204120f030e0d110f0102011103151507170f04050604060909050a06031e140a0c030b07050f0a03020a050702040516030b03150a0209030717210c1e 68
    0x2850b050803031020b0b0102004658201d860200d0f00a455900d003140d002c80030819080a4002d0003080200d01c0c9030203e1040c02e14090340c4c600c3d071005000114000910f04a0101c4681048440b060445a400c1c0b544c1042d081529606800045c240961031034900240c03540c03810b140d811214498404000240c46841081c1c9509840180c20003c0205075640e0307481e400148541414028000c409282c400450651031191068100300c80c0c0c44802c0c0b0040c0070f0200c01600c0d00110080c8159480c00e44144282902e2000f44010901c1c2e501c00e01c614513800e030441c00c1c20030300c4100081c0f030340d010302500304055039090381c46505a5020747e8092402513920107820a08640c14007650038020b402908044c01c0c40b4258080d006440050300843c1c4e01040a928000c0030584c0d078001c2e084010b080803100e200828140c43e81a0020000040040c0c216281c442c4d07a80c07490008030629520f6a415500030100e402a010984000400034550004602d0300340980e202000e501c2c1c11401c01c6003042160070762111454100144 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 467913255 1250 467912005 467912009
    0x1302041a0c280f200616030e03190503030403020705030f030904180203060a1b0302090105030a0902060702060d060513050105090613060807060c02150309030412020609090c0d150506120a0204 84
    0x4240c91200440034501061109a6010542d20465012100d41e004e4186481914548030b03551702d01b0113807140310b03031410395000294095168140c01005c904005500c841c0012282d400d1084004503079078942410001c4c1460516001141320380c1064001e1004e119000050381c1d14118201d80c0014211440c10700f44083c9024200000c0d0180580010001c5503000d907031290310902901071403200018001c5508604900c82c804503640407072010b00120744a100c059001140b0329202030421807500b07501d6000200c1c1500301a010020494803580b09000b1070501004c08002800348900070300455041100041351540024002c40c003500d6902602d80180183d0381051008181840a4900079600e81034010003001c00b40c0402da001d1100e84104a2210704ae14044902c03420300c001c091810310342000034608640d260721100366409441070003a110540e407469501c2c1e00602e110600c41d6502c21b45480640103450801c10207050070000d0700c50800407a110902151002c801040d81949142e07101c41454000b80a65 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 467914505 1250 467913255 467913263
    0xa0c060209041811030606061309050a060305071e0e060a03080705100501080f060105091b1b06150f0f0f04020706091a1b0301080706050a0e1302041a0c28 68
    0x244600050081003000c4d80051070040e42940c1d045d039508000d1201c284202c028120000c02919020400324140340e001079040f000f00c4002195040d9030707445183c074016041d0040c0d81c40c3c0340c41ca40b02c050010b201d40d03010801042c0c491010800b0b3720702003000130f15898840c480601440c070009103480c10040c040c40a02c445a144500410007542c40d18016a69880340e10030450841c0700d00000800c403850107141c0303d40304082c212042c1c2400c01484500840a170000384d18040240240e04414960074000d10005200701e83c0c0c0c08590520500301c20400001400d101e40881c0161190b03c0c8004198460030001110900203940c0540d946010380f0b0320030700504180748042c04039038601e1800e800711410841c519000d0f404698099075002d8110340085050303c003e00c6024101d50088208015450040000e00f000d000e15040854545804601003a42c003004000401d100325400a401d02c075020314880d041c00c000c003c11820700d052901e100f8480d955800e0f08501040c403120340480d986c20540d1303007520b410001e40c4c0c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 467915755 1250 467914505 467914541
    0x812042d0905100602030702060a030e0a0f0b0604050c0a0c0206090a08011404060b1c17040e090a060c02012903120d02070c090b030d0f0210020a021006050301020a0c06020904 77
    0x7460703002100070a0181e401070741800d01503000041d07040c8004241c6050b1600104001e10300150a08260000c00407050003983c0e43c09100c86e200d0220340c020025444c030500940f44014180380050420040740c0c4010b0101d03258640901c150600d260740034014000007941540c0b90f03542d8401d60000221245503650046810758201a004100c04480031409401140315034000d00c1080c01207401c00c020030480100005420080c049044003140010000540b00640b402a4602d05601c030124076001e6041280c40c66015480b81207070750100040c9110300c1800101510081200840d0004565003501d1401c0800c0f135040e40d00c0341d4285059509201d042c2140c0003130103405680c1c9581007082006900880e005940c0228800f600050002281c000c03000ca001005001e46407146180c0c4041c1c2d000c52201c050001184280c8804100b071000a100030030b5005803980007820801c1101c46c412046d2103081d00702c14003e90050201b00311041d007003040a2451580f000c4007503210790810b40410001d041c840001c02006103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 467917005 1250 467915755 467915759
    0x1608040b27030405030d0801030803040b041e03020a0b07112e0203040b0411030a0803060907031413150e0c1003150e0f090105010e18070506041502070812042d 70
    0x1c000018011150264107842d0013001510050380c1e00fa40920002e4900081000010001141110380c10b80c4036100740307160503c0e2141c20605001494031450201c0150707222846000510698080300d661207540313494610002d2001c450b8550b1180648070421507104800b5008200313102c003420414801c8850300508545a240c82d041050b0007480c180c0c0e050314080400007050007141801300b074891145411003850791550b21450705005100e1001420801007540c0c0b401c0380b0418107900080c0502403000110490002d1016041242d0303c01c43c005035147c0241c0c9424810300910402044100c100102100c140c103041200d075009a0141565549010088424030b6001c1000a4018022030080c0f00c0a249503c069854074401801c0780c0c0c080c055000450454400903980031400078002924085038000d40303550641c0c3d180410800e400942040c2141c141304900034441070ba041000000078a40340000300400201c505240209109500840e00072006000e1000410200826110100004101c05c0c01c4815 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 467918255 1250 467917005 467917081
    0x30a030204050907090f060e0d0b15031005090c1005040e01060f030f0c0c170405040608010e060f0f0f041713090e0a1e020d020d030e03061608040b 65
    0x161050094512415901004c0381040c1e10480c1020182c900c0382140081981c202641a07411040c40c900780e5501c101501034800c001840b10074241e00518070400c04c0404000017100301810700c02ca41e01c404112601d004200500c1840001d84081c10319415249403054442825003102c3c1849190080110000444000902680d00490760750300c0102c01c1c0d408000503d040300c08030040e5014012082c00185201a41c040840d900413540642400350640d11391800380d40e20040390965a07150301041d800d0750350742c4090034018000c2c071000b80c1c00003c00300c20624501c4c2c2100410f010180c040c00085900ea1500006420481501c184010181403665030303a0b1520000101100c0a420718082d0300c5c5403d08042451070072120010f0099019a488440701542a014200030094020701440599201c2901c20316040035845003480c82000380c1c06603a4041c8550262018035140071009450500c3c031040520151840a0744054074907042584490f0100050722070150740c102e00c440c803c0c80343c4005000e0840804c452 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 467919505 1250 467918255 467918257
    0x150103110f0d050c090a064109072a0803060406150e0d05071d0103210c1101140313060605030109020315040f08070b0a0e0610121103030a0302 63
    0x54100e81074481c1001c56010300c8a070704100e0764010659803180c008070706a032801060440d8002c04000c00001d00e55526403002c0034000d10034203110600d104402800303c484030719454007041c0591641403030146465650200d0001080108048100202d604500340c045040d00c004a030240200c094064221110f403c0055159206449452050340341c4200080da0000d0801000c40d96a078507111991900c00031030030b101c561f151440e4215038900680401041781e8811840348a0b41c0eaa120080d61380560461806459001d01403003044400700f1942c80b000b001c07542c03064054500c1a40310070040201c0a04070010b94080c00c82e09160b004021001c410007446091078064000c11a01030002480754503a5602810300721040810042d401d600103031200b00f0840000c0c04d00f190000d05c2455081400e40103500e03040c285411a0400f26441001031052213003d041c64020020f07000268800b07044a402c5c098290f82500003a0300c00c102c440d18111450b0300034080701074031481000700050107803650352100040060003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 467920755 1250 467919505 467919533
    0x1050d111306091d1e0307140102091201050609130609020a03060b031921110105150108060f011205070e060304060608070b2704020c0a1103060a181202150103 70
    0x2a084c0b81c501003010100254103082d045883d01c60240502c40c400407402d980c8025400c4004200d48810004440040d0390800110b020100c4040010380340c2035030504100c007a1400700b038101e0450303040c4014401107944041800d5045440701d042401007048038a8000301400305650069401001d01c81c4c004103021550300102c0c1442e004034146c81e1588990400f0301c40a552000020340714814005400c9041d50a552454400001908013107044e1200b40700d01a0a5850846010004140000c911030803541c024902981103502220880100c2281100080540314600d45421a60b5128004a0103090040d0030004401c84084c059550302c1c90103040c00c2c80a0059445048000c0c401c0030b40008182000718207980c000991504180340b9908c2424204030f001c9504180c0e00d60246c0d00f00305d0a00d075100104484c0c42054487d4140c6e2102c0140e210802d410900f008009860240c103264482d00303032b024585040d080e001e0348000303807000202100c0c104901d4030300350507480c451704550b400000c002e1104004040d04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 467922005 1250 467920755 467920769
    0x4050a0b04060f030b0103080d1b110d0e010813140d0c1205070f120212030a140106110c01030203040602040e010b0c0d050a0c0308040f0b0106091403011401050d111306 74
    0x14640e41d8005000315600766120141105e200007006000250b010380003044440072010022030070054203015a1400da07122100540400c07010a14901004414001c406101c0b045081c01c00c580100c0d0400a021813400800c481d1a101102d00072004100c213510b010f655a42e15141115070102c4504d00241001d51301c0030040d1100c401c4000c2c5130080300d2281c000c80c0e0f200c65010b048905140119514004160090040c2c1d6007980100c1520701e41c046c0076003010754460404020b004c2200241c8001c40d0200c0705060f0000000c108e803401024110400024103080b2406003860016981d54582c18a40000e01640d041821410108000028100c2ca0380c0080c080e518103034020303590749001c00141a03403a4882e500660001c070b00340400c6003000c80d000f02c0c0c00a0340180910400c2490801a40c0c581c83e5a460903009400401d40003a018020801015502c110004041e8000c0090700400586d40c1580b0105101c3c2d079200d49102c00c0f0003410020819002010310b9409081e5100a03040869100d0140605004690f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 467923255 1250 467922005 467922011
    0x3110408032101050a030209040507030501050705071b0b0f21040606030507090204030b061c050105070909060b070b040809030f1221040209043f020c010503010b12040c0504050a0b04 80
    0x242c4940e042000d114101c1c0d00040c1180d042c585103509004c0f00e40390040040d54640510800000421070078050144554420360302c2036501d00e246e14054080c03001200a51808007240c00082c030016000004849065610031100d6441d680072030402c05d652000020b17140400c0890b141807004118483c2c0045090324403c40c16118165100c01d074003c103d028078030010f0100f04800001c074101d03003010a0003111206003001043c441e1492078031881e0a40d4429142c07003001444140e02040a0300e01d91103104040e08078803647d145807800035250b40b070740002d0207440134100d010002070081042e0340402000e2403403440c2e00d0644a08030605100c00995410540318401c0f461040141500c408042c1c000d171500c613a03801071500a82d42c81e01d88807082c01e02030115204490f20781c40080d03c040c01b01d20505011442d090028800c503103100780342c0c0080c1030852981146040c02024001840000002c800b9500940410342121800d139489050a8080e07841da940300030303003103498441801800d15050700070503000d1100303035818 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 467924505 1250 467923255 467923297
    0x8070309081203040f030905060703080615070f122001140a0504022218050304210503070308060a03060c081005030c151e030f090c0d210311040803 65
    0xa900c80b45000014042c0100400000300090480c410014449000746400120980c444011074400e512020341500890b691104000c21494070314480b18101c00344200d91400d1014659904000c004541801441f203c200c403030003681b892044c22041a111241707940c04203481040c49800f4024081c00030062009140c00c2c0002d07407024618020540280e50240c5010611071034484004094121030596250182c0c075444c1500180e00401c1c0d00c1c04106001e0030107940d40750b00c0d254060082030200054494883c140c03c2021003c124080b0513154078030f030903041c0714089950381400a400300320190401132100c0e00d040042d01100b5170068089206803c00840705109035152020103559003010300c0c0301135025403010542c0100741c1c01c01024189090000b15141e000101001203140c180c0c10448840265140407000c0051207202000b00184101040c1c40b405882c0000342c40b000d0900003403400c1c400c2100902c40c0e10018440c0300c2d50090313108400d018070380c944882d20340309020346030b0388072206201aa2100e1041e1b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 467925755 1250 467924505 467924519
    0xf0d17010608070503070807120c052706070b09010207170904150f1401050405100c052b0804050c10030b0a0902030907050d1506090c030e030a0e0f030f0a08070309 72
    0xc1107010b2030584d1503007400c40da907880080341d2810000b000780381040031442c551001d408080c0a10311000e00700380c603810b40b26180750306400c0b00c61600552034501200740b0030702d421342d64440e4012259035503000340c00c000d02581c0d503892079800380c403c5201c01409040808a20402d6041c8103000d8272245200301d80c01d00c01405104000480e4061a0084103078120040030104081e254440c420804c5003c103040c5a41000e64420003d103003248031a0590000c40c0901d104101045001c4c01200c01b1825007001c03240301c2c9a20010f550b01c41c07400c0b1000880c01d00040c000403070b0910004204003404d410340140342d483d00d011281d40090140c00b800c0c2030709014800000c808a81d4481c14020b692117a1145402047c000c0d1600d0100000040d1145055445900303214031718289440c50b0203400050005010302040902090000404948803007140285540092051a83c0c041d444614000c10003001c507041800c0e1180b900019040020b45012a135503441070415900420550501a21030b03240691203c501066540f90 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 467927005 1250 467925755 467925767
    0x14040209030d030b010e0607050d03051f0b0d0f0e0c0a062d11030d05010513091511090307061706010509090708091509030306041109010f110f0d170106 67
    0x10080d0303816007200d08608002c03031003940320300c50788501403610621100c42c3c82c010400d070781e010300720170380d0f044d080020795030126505809880d803c0a801020703032f02a482000e410040c0c03c0030a00501c81e6a813000113022250380b0a0350072401c0c0500381903004100080740400f0b144d665240760103000c1e000b0310980c000011094000c00b100e00d05070805954640160050710801c2c0300c0a0303813458600f814800300c08450305c40003400300042c00e801030111200281c203504150802918014804210517518108034a1000050341e4080500b02284003000c00f082c1d20001035a0403040303005006c1515010300c00d0a000154650f8051600c050403e0710074104101c0303807180701c01114144502c0021075004401440880c1c3c0447c40b419445601200940c152101c4a40c48640f90741034400650300441542c0c808030a021151070b051081d0104603260b03105041c64090018000b82c000350004440780d0a00c07011442205505d00280640c014045403101a180e00402001c0701503c03a1401c01d8420004c003410400200e02180034803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 467928255 1250 467927005 467927017
    0x1e030702151e030a240306060e0105010c0803060307170309040f0509030a050a020a0c060903120f270302060d06030b090313260a03081e100623040f140402 68
    0xb003900c01403590308060402d07548040c001d07090003a560704603030f014805021000701001150020082071a842c0d4200b040c16607030b40e6003103040d444169000400881e80c0102c0000b0325180e21114950304e982e180800242064056400301d44034408000744407200e202c0c040b004102c0a1401c540420041800d02e803000100e4000b2035502901d03604c02c0043ca00c2484c0034034040e007032002c5a481200c403042200d90380c5030070b0002e15600c490b010400414041c03003000a20350f00c40354051840e28150610441d0007600a001d16640301c8042e00104011440c801c241c40d04c0a006009540c0207020a81e841c0009085200144010720040c0d84805015000c9004010301000304c401d80c00401c01c1e484a40d90410b181c0b001c8150100e40040280c1030210011140c1d00814030205800c1c174020b031901c52007494030207116000e0185041008a0b2030b40c0352010480c5100f4442100c00a8582900d0700300084950b11040e41c1040a5040e020b40740903401090000ba4014181030390420346550016a141020040080c07006074001d070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 467929505 1250 467928255 467928277
    0x240501090612020a060302090a1706180f0d0f020703050a1a07170c0d0204030b070914270a0e0f0c040c0302070f03080a1803050d061212080403021e03070215 69
    0x9000c041114606c250003902c0c41c001c0040024151565408001c071000300c590780d1000c41d0f03410041c20804c0e0110040d425110308401350001d49600d841c11207034261182c2c20350000400b40100c0252340351586108100860140d5445401c8985003091814009454000e0700c842c03007524001100011006445145c030504407144080b4500d080f512040d83d000c025800ca02c0301004503940c00d00c000000329001c6d00283e8010041031311000d0f019424015640c21980b14404040d00070800c1c240050040000c501d40e1a240c02c0e0017108071078442c0c44440410700a4103241400300500e210f50340e140184004082680644004110340070843d010540c10254241c0c0a90704018141082070300c99500400d0013503070b02540c0002c0f61880001c500052030315110005c21040b4082d000100f01080200410b89076100f0702000c3c0c0324281c545402403c0e00d580700301070000030160f81810000c403a008201094020044c501d480d49400e6030807048881f80d910815a00d801120382a4820a140c21240d0300c19140c2504603441300080d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 467930755 1250 467929505 467929519
    0x706022d0708090102030d1a040c1103041206020d0204080f150121020a080718050f090a080a0c02090f07030f0c08070302070512040f0302030d02151324050109061202 73
    0xc01e84400b11030f81c004440c1a815400100045411600180310f00001001205400c0041c80d03001c005020071145040074200501428080111801000005440c00c44800340b4408000381c92514020019016088410890380e002140208003900046002205000150221041d22500e2804103074015403e2080c01441c5d6a90901002c56540c050360500c050b40c005880800c0480ea902100c925001165101c0e074156600c8046001e59031025004150b0480d01c00540300e80c550030011030450f00c0b481c000c08000d0184600080e8214442c0c0521041c101c00d070780003800c1c41c3c900d24001c091001c0030002294024001307460301d000143c0c7c0ea0030078032401e10340b40b4042d95200c01c0e694a424064000354801c440940300ca03c602c0d0212907589442c02c1c002c1000d8500c4820841c0244d00d544141850a00030746000b00554108050b1107400040c0071424a03440b200046952501c5e038024140280d115210407812402044c40b03404880e90041260440c504940030400c3c01c01c08a81c1d144003403070031540e10310002980111 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 467932005 1250 467930755 467930767
    0x6060f0309020640170307050c061c0c02060f0906041208090f01060f06021e0307080304020d151a010905011403091c030903090f0b090907140706022d 66
    0xd0396008980c43c000400c103401000c4081c20046440c50304140d4140980d0150405d00c0441444101d150302d4140c039200441c00c0681680d242c42c0c8504c041400280103120100d014900d0050b41c008500a00d150004200a00b28145200a403a040111030101c281426540130481c451800180144079913008040d208500040c6a421122141c0c040d141e08005d200c0c3c440c031214580c030300307104200082a055286110140c9400400782c10448a40b10361054001c1b00e201105119101200300e901966005400c1540e0795110710020308409500030001d0400c0301c58141c0342e10b030b11400394000600368684c0c407041401121200b004441d00880b80c080c0c540007da045a000b00e008079107101550300700000c3c0064400700f42004c2c0b00c8480103000d00c0c4050307000030303240c502c2002171540040b291409040008864120182840400c801d91300c207090700603001701803400003d03045074412007507195550316081c03050703540300072504209029400040c0d09859800d4200d489001c01c0042402d2012a603910020b41c0341051 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 467933255 1250 467932005 467932027
    0x809040b18180c0315100504020403030906050a0201140901090b09010608030d0b0d06180c0b030f06010e0114031905160206040b0a09020d200909120a030f0f06060f03090206 76
    0x102403090b020724039108800031a080c41e9800e000d41e1125001015910640e0b01d07100785600d4050450b41d216038000e5104010074400319511030f840c4030a031851414000d51301d000e440700480c01415110111f00b01141c281003801031881703041d00104080d5004480000c017945a007080715003201c0c4a485844074991040103451100012501314208440e40144005511030702ca488500070303074981c43c00d44481c0f02c030a81144400c00105022000c090540d0000c1d00d41141303014280281c0c04003010b025541403100b10511075030aa0f118150402441180d44d0403a5103030308041c0c00c20041d40000d802541c80440c10880041d40001903006403480301c045550041080f038072252603c4100250103025028400c1d1210030060250321180303a0003075510311440b140c0e0f0188500600c041c1e141d100b601c00c403500c40c541100c248007445000043d60054099031a44035a86c48181d20f1040c5c00400b10070000401803410008400842604c0c2d5108038200c8043d078075408020324005004808a41003490004c0d40f1000c00d0000c09400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 467934505 1250 467933255 467933281
    0x10e010b0a150c17091207050108070e03011e0203100b0306090a091a040b0711011a0613180c020708150a020a0e0d050f0d0c080d021e070809040b18 65
    0x410380c207007031001141c24142c507048941000c1304d101c00d41c6030b1000103401d5aa828035464403403e203241e102c058003003e810200000c01003140a402d03c03080000d1001e01001d195400e61100c4040c80708d0384041440c010741c101400d40079400860301441b2070b2820070400229941c1c50800ca9100b2034000300240c41c0b613683c1a10700d8000b480803803030039101009110301004a801c1c0360074446008a0160044509628220074001c10700d030106861030426034180241c0306500c0c03016a8952071350140c210785140d268080e001071851107001c150f1105180a9010010001c189110342c005038800800e503090b20826602c412840b55551010030403811110208000510b52456550203808003400320314268581041000010b9a1200030800a0b00d40d030300070b21807444a15404104c2100400c809080240b12403d850720390304150701030f241100c502c054000034440002001c002440d000392030440205a02d82e03080c0d00b0b100b8500c3e080009920700840ca0101040454908031000b02181741b500c0030650303003a548500808086c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 467935755 1250 467934505 467934539
    0x303091502120d200d050606092d030d120c110601140f040c05030a0b0a12030309020d0210051908272802090604052e030807080c010e010b0a 62
    0xf450b90f4074641c0e0f004107800801d611000425485454864004410a0b42125009070115105400030403101c681c6407a81c004840b4003451040103180c8641411801c040b4600c16040c8040d41030240140850b00c941d004240c2580c0280c0040b4100071058443c1c0094481300d41046083d40e00c2d52046004001406020014000100010b40814141904240810144e0300c0c2c3e10704240100e080441000300b950410310405c104004111900001d9500e000ca400382341e0845030b100501010b03219141d210039501c84140c40300c101a405401002c51011b1464000d0454100442c8034000948500d13410040900c1682c02034012a5483c0c0d01d41044061040c4241400c1e224502c107085d030303005880350b259891030307a9940317501d40040c0d698582038121000c1c8100106004000d04543c4220314105c20b12034140e0400f0f030301154200c01c1141c2505020030703802400d29502c1240c2d0004007001d2001a00008210074031014002501241d002800b091944c000b84c1401e03184410400e40c2c0108101e24104080091074581c0300c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 467937005 1250 467935755 467935777
    0xa051002040e06120304090c08160c08030a0e0a150c0906020115060f02010f0e100b010318020d0311030313030305090a0510110403020307090c20031804021210030309150212 76
    0x81b0b05940c0301a90019a8480711a03900800c02e800c0030040c0c8150082e000c0700d0904201d00e4245850401035840711080c0c040504248400c941e070b02c40d4018103040c01c010355000160040c025400350030074660400c015007000015800000e840c41400a51140140507043d014040900c03044042810b0610840d182c2c2c0e14042d2700380441d0b4980440840c0c81449215a0201004810240100070303402510242901c00180382541007506c2c00818441103844000c00a03031544c1d044520300c072845507a05044a10341106102e24100c1c0c04004103002c1c2011441c2002d005403803086d03c0620490760744040094482d80c0c039080241461300071802c0c000c4030303461030b510445031414124811030502c0e07229000309207045103503080007000c00c2c2e03201c00e60901140c02411682d01c1301e00d050b4114142c181d48403c0940c40f4000c61070500c000b100b90310264200f654854040d5800350407041504442c0d8605281d001135000850710040e40854a01c410210b4110619544205802e890390001c0442603040660015142c0c070204001c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 467938255 1250 467937005 467937007
    0x50a23010501080c0712112401091112010f0807090606051c150305030d050f0c0a050a171e0c0a090e090f03030c030a060b070201080a02030402041d0a051002040e061203 74
    0x25078520112071030340e80c0b99440c51f0103600704045540c40c104c01c1d1031100101607000f40c4c0f40d100c280b1b1001031403410341e843c03518041030020010116241900902d00100758440d450300c0041100180441d070001150f2100041742c02041c2d9804852080380d500b80038a10000d0b10803c1200602042c070400180030441d40c1100040152443e6a0025001000d400484098000152101e0030401c14050160404c1c0c40c00b9400134103050048114029109001c1c43c0d205100f0085103142c10300d40581100f45550300c500c51640914500a0004054002d4200441c181c00300d52401213030400e0099016920b640c45070b61210364501f803c2550901900c0b40040120700c19104200d0000c00241c0c0500140d4041c03446280348036101d0426200794812381e0300e2504283d180c02c0003030041d1405030703030710144450700000701003401641d94450b030021030f0261181008028466015040450501c0030005035150301c207008000b5903c440c64202c400009a00c0b0703c0c810001c00741f0801001c181d080c40c0840b28080c12000303d06c01c403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 467939505 1250 467938255 467938267
    0x50c250b18030706030b1206090c131407030204060813020604050d15020703020304031712070f0e100509032b05160c0807030209010e091203060105041701050a23010501080c 76
    0x183c0780c42c809070061000039480342c0320300000c1e090240c1c1d81000030348100d0180c802d620b44200440e03907a03501d213210244110740c8506080b140800d2607010500543c1c4400301a00d451600e000064041e5110344121070002d000c1c1d03400901c040751b1580300380204540c002d1030745141918100401c020803410120070b46407840740d4501d000b6110118401024020f100b6009191544d143d805e0051541c0c1c001c1d403807203038503041c2081503201c22020481150b0340087da03400e15589070074007000e08407040d0442c60a840d130000203c145c800b0390550010007070700403850100d08a580000c0b884280c0000786919902d18000344c85c1c445400c40c04180600c000d421140e203500c0c01d4511a03c601d44400040500131b074850b0580e500109020320560401d21800b5000d032000c61142c00075410195a442c0e5550856003d00ea00400040003046640e031040c011903008106010406459880d0703204224020b00c0c081e41d4103041d85181010544200b191813203850011200c1e60400b103140d03840c180c010340300c481c002001e80210030f00c20400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 467940755 1250 467939505 467939509
    0x6060f09041508010b010f0e010c03110a03091401031a1003090b150108150f0d020619200c130906060306021206040c02061512010e010c050c250b18 65
    0x7040345000c45a900703910558a00303120b86003100d1740d03904101d040041c6111010619604000f068090780002c2c64040d0250050742012544691784440794030481c00740140f45014154004403000965402c8100d148009039144015402c56070440428810b0020341c0d480107107103180222010903644410304020440d13512907500da25030004101c17034100c001c9424003000340080d640002c465502c0003145441c007102c0c004410004410248160403180700e46140720340f190442d11044242c6400131411545a000000d1204000c0c145403220144070a1050300840316802d103e20009006007801b0000d41203200e0060380c2618180a8040c44106850007510342c05c0010000c0c450388020314120301c0c0c5071010303840360800702c0030482554100c4000604540c001800c0c4005103a102440d101c40d00022601402c408d400c6000e4140902481070507800654070b4045115010340c4c1000041c111140140c084c4d402240d8020009000720b0840950620790307505a11051081c0250344004008030a84056181d00406c51500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 467942005 1250 467940755 467940761
    0x80705030d06122901050d1104110a031a01080118090f0605060907030501050915031501140a060c05030a0509041805031c091a060d0507140112050f06060f0904 70
    0x100a00e6100c101195000900814980301004000c00c1d20380b220405404c2d60818409482c1802440e03c075010b071620100400000440c201103405020b4000d00580711503150303112a03500510441000b090411450144c03c0310301706d01c2c42d820ba00e0141c681d40216424501038220144002c858050b41a58812511000c51f50403119544100d2103100045040e242c0300007403101c1d04101911106c2418186801402165160f261486d03005409081d0200f0b43c0800c000081d2514140220740031703a42c1101070020840f00461500741071842e900361401c10109594600864280150708405002c82c1c205108075806a8030801c000d105942c3c1c014401302e040403003115602010005a0707401c40d025800001c8404076101c00301d403c12850144481e0400c000c000c25146d440703040440700f01801510308040700184003071b62105017400d001e503000707001c07a0801034503156003c03800b130012400030b40400d2482c2d03100c0043d01703980c0c0116445006000584102a11050b042c04203c3c2c0140c1003400d500e035030a109141070b0382c442d84 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 467943255 1250 467942005 467942009
    0x203120408010204060f050a3f0902280e040c2c010906080a080702210304050102060c28020f030d050109061d180a02060f0d06060912080705030d06 65
    0x24001030f544e501c1c2002c0030b400080200380380c0b070510400707102005509030080040022945c10320454040022001102c2c0304400c0b03032408000d0180401c00314000d252410390f00c070361610340c03017940d10148014102e40b4016644504040e01158100d4802091021a0640c4540e0303130001d11402e25403887c40e80340c8151002c1007032058060131000c4440040d8240c1c0c0019030f12484d005040c3c294003009141e0900c14000d0f100c2a004030090901d20707000072001304640710745084220031003a56100303100c0d10b45219200b6480c1e5200f0301c201c90040c400c00380442c00c2884071030102c0e1015040b01002d00c0030314111108141542d0b001415007420b502400c0015250040f05000414001c0300c020780000e0300750304040c2d405c0102c03000c0b41c0100615040101107065202520506903810205070941410014980b642c264945884103400070341024022840c0240751031054051718200300103003070034084240c8403042110700ca442c5100d004804002d10921201140c2c41b0b50003401d86031301501c00c0e60b150a11940c1e146040d14429 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 467944505 1250 467943255 467943269
    0x220314030a020909061507060228180603050105130509010f02041d090607020c060706110409020702010320161b120b0c03010807060e130c0e130615080402031204 71
    0x2401010520f004e8460550120781210702d0b007802038501c0101801805910802020180d00080b0b9540c0395005220101d164640e491680d48070b100808402070481305c100e108001081c03068040841e03103d000b030060038107131200030300701612020f0000301c180c0c080c20000d01022040d550300c030700000c41460580004c0c40034041d520015400d11007895003180320b51400038000041d0307030803850078041169400b0072003000401d0300315525500c0f60602e0400a004101c0030364003184001002400041e03010040c0c002c0c100490007624100030200c1d815141c10f9482000c2030f9403404d41101001080303441c01c0c01001d1aa1041d00400002c0321580700c041e0f05801c000a01e800c9840d02c2c910154910302084507482074594440c000c1c02000f400d551510908954455150083d041400201030100314140c5552024003a8002a1242440641031054014003c07000d1100c116001d09011030700000b00d083c1a000c0c14086440004141288085c40102205d070013502400407031b03060141c081d80e02d00213900740000c0d00140500d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 467945755 1250 467944505 467944507
    0x21110301080d0507050a02010804020112050702060604050702010e0c0103050c130909050c030313050f18070c1511030c0d06030c0305030909060901031e080f0c160806220314030a02 79
    0x10690154541080034400e07100f007000070403030351000800200d003003403c1c90303420700b0448415151880141d0389a5140190340034210714140c10407005a6000034018080c200541d8204401c0c2c5846504078260780300d0b44601c2015a2200b1000c510552013a401558401e80c0452020b082c25209400105c001c041507110701185500d440c1d610b010302000b0f000b070b1114904101c0055140082c0c03062050000d21a51080d41d119031310022078000c032034680e01c181100420700c042600c40300707291103a8050444502c07050152074000c002201c4200c0441540b18014401d55031000485c15a940c5d2801c000e8103500c060030f00c46155840743c800000088211a0000c0950300c184061900c948030352080c480c41800c0107041900c68100e0304010800305206071403451882c01d030030001400c0840e0504002c4e006224107108401d4440340003c005517115004120a05602e0100034944415641d80e0001c90390388200b44c1d1014203082c4002203805041420a40030044103200341440000c1a11820001c20240c0040718151607080d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 467947005 1250 467945755 467945759
    0x106080111090d0308060312071202100627020f040f170a0c050d0203330a0608070b0a030e030307050304050d0c0302060a1d070b04030b09010504030c020121110301 72
    0x4028010040c01d20140340080c0c0c1020740702c1d800140c20000e004005000d0203411404109a910103122071041140303a540c50f43c0d40c0b122285054000d0103400100e500050182184941d02c0204a00429044650300f00910b140103980407035000e032032340e040440d00804683c02c0105c15605d8841c20302410007481130f96400c0580c0c5240015442d601d00b81b085005030306801c00302d00c070740c0000d4500c0d0160058034001e032022000d0760703e40e01c003191914243c40c44500710900c0c08403041e00700c40100901c040250b40304500d00d622549450000000b6a0300e40e00401c0d119412000043c040d105840028001400e0319103008140081c0040502d070455009483c610000381000081109005003046018842070881c60711217101142502c00030749484000d0248035081d612072810a0025a080881c0120706034103206450766155075411040007544544070490350010a40b001802c0600103104842c0702c4c54040d210650704080c203600464040700740c010851072060300400d043d082c4101900c10165002400780703150f40d60b54 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 467948255 1250 467947005 467947019
    0x61203040e1023030303280e0639030c04090f0603060b010c0b1b040b03150a23060f04230118121e0b09030d0b0a03030804120e04020c0106 61
    0x210f041c0e00d04100201080b0207000c1d00e00004032a4090078202070324003140c5107080713030304920080300311024404c604007080000a02000705016000d9085184200f15181e441034040d4a0f034018035441c00350500480c00c40f80d00e00b8040e0402180d1006075500c0300e624080c4c50302d134820200d0703850300300207451180d440e1014010002d40d4420b40c0f618000900f8041c2c40468660b0307034400101801800c0c103407500f80e844102460b04031200150f6000e00700c03040c0959120300c0c0c00d429000749000221800c0e44104401c4400051401c81d040c1c1540d010f0042c0401c5502904a82c020301c0059401072201c200ca5070010400001e1527015084880c02a1076101c1481900d042c83c2c000041801d134820301d0304901a0250101000031407a2100d4025080e580300031140c09200760540340c14460030914801400d08220ba070700f04228410003100605601030042c00c100044007020782802050f243c0e9000040116103488042400f0075005001019080ca0714980103528101400104059800c00c40103111aa91184000e00443c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 467949505 1250 467948255 467948279
    0x20d0f080d0902150414130b06070602092713050703020a0b09100216120f0836060901080907180903021908040302090912070f061a0306061203040e10 66
    0xd04a001c1d43c0750305080c1480200d5115407003c606c9188140b5160429184d04161034000302694040102003a803290340d90306004003c0d5100882a03481400c2c880c55120007031903115050b24140100f0128142d0a58403040d101840c0401034a007074034180b00c1c91300000010ba60300280e48000d42082c030740260701c7d0f074004010301c04401090102501550400419925181c8035180780030b0480b81c9410002070f90604a041c807100303e65550b48054004000043c01c212800e140c03240911418a11103000d00b00c80d9880305100e903031129054035140d400340f0100061016584243c21540c0c010031404284c51780c4595400020044191328606005120303103910800042c076030103025413028110a0444c0a055508580d03270300610380303c0d901009108528080201e1100f150402180110a0f1000c41c510341e200c09508250641d80e092000071107a080c10111400d0022401700801c3d141d02c07001070014a400d40b141410480c4003880030207203902e40d01c018000081d20b0a040000c081c0150000c5041c119018107040680c585 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 467950755 1250 467949505 467949529
    0xa090305102f0706020c06180a0c0b07050c131e1b050a02070b03071205010501031415060f130311030601080703380708070c0f020d0f080d0902 63
    0x100d03242c010b42640c804240815000003080302c0519015001004041c18168090001c0240a040c07002c2a000240000010034500548204042c24a0703100071844a0760345191041f002002181000070420003040c042e805000c00c80e01c0f44041d030304128200800b00d000c0754460481c01d80d5854403a601184a907603441c900900c0700031454020300164a032142210840d14541520808001000850140c16803003405100d010388150655290759083c5101d0041c1014420036981c0d8a5501d420f0002500f9070180c0300f030b0303988205105110072850b07650741c2941c0c640c00140e010603034200703900300540380613031184000401c009a0b414503000307a51419800e003580130821500206000f54401e50050000b44d0000074800c0c102c0343d20100d14200d80c10781e4000c01c4128090207006c070080c0040303c041008258048514a4070460142d0744010035960b078824226544144504003601d08881e4642035005418494030366002d0902405410540540e141d4900011340e020b54080d518040c1d031441010210305c1c03c0110000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 467952005 1250 467950755 467950783
    0x10e100e040b040b0603040b0a09020a08030d0507110606010f14070b09010f0608150604060f0905190507050913270c06050906090904051509010204090f180f06090204020a090305 78
    0xb00d04c0a00114000703200280001d44101080703400200e8125003a045508000e42c050118080c0607654082c140d542d800030740e801c02d203060030a0006a242440394041100d139403480c0c0000c4c0442d40702d84005407009003240a001c1d040060100040c19040c40b1407009201591090600764120f14103036803020f084410008403031008500f0a0704c01c02c004200019001450940310201000e181c07039020008000702000e40c4080007400c5103840005845905600880c4500e10082084101034410895035007220011030740c00d40816001d00c01c42000e820709801c100e46d0801e8041002031440f8000781c14152442421482c050303080002e8a6034006c201e00400c800000b484d031810000c1c2400070000020702e06014082d0482d004089000c00201400400c0040b080c04510715251103145040c4144018040d41c003034010301035964145050700344036040900c60303825428203100c1c0000da803413651303a100c1c80701814075101598003544030700200015071340e903100070a0744180c0f940b100d0710300614500c0c080c1c0c14402c0d0940995 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 467953255 1250 467952005 467952011
    0x703090503030c1e030706060605180d031b05100e010c091e090b03100c11120306090103060b1302040902040603060b0c0d142a0624060702010e100e040b04 68
    0x8883d144000ba4100d500c006610145440140d02c01d03031306145000c0c4400c083c00ca05d061210000798960450018040d41514220b86210000300708148400c0c1c0e5250003005000422846105085180040411642e5031288040d00c4c420080340103d84c0507100c05459841c0d05035510020103400c15002a0414001c19034140e1041d0329000c0f401100001c030180344180369059032a0086c5003c141d805202078030100382c11107420080700280c3d4800600101e003039084070701503205001d400c1203c1518282541c0c8035a41c01030658039141e0950369254003034005070307003d0764004034281e4810701d00410a00150014198810006031250b01e0920000d00343c81d010ba20203440b100041260907100d84d80858104081e0130603080c604440690803400f005207118440e1003143d040311001c030803d8800ca014502c00c1100f0038400880b082502c90060070005101c107174004207407c584610001001d400c2c000013802016005040105074a40140041002404012801d4000038640d00c0c4654980c6018030443d00c102c80192810 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 467954505 1250 467953255 467953267
    0xd030e0706080103020d140d031a04090510090c030b0708040302070b04051f0e0d05150114060301060f0203040e01061e030e0a08090d0c0303050301061e090501051c05010b070309050303 81
    0xb40c0300201c107003c00390203030703400441c200c0c00e100d2404140786075603d0180c12240200840301c0014010015115603084a01d054074140c403041c070f002d0150b0003441d5003100c090009080003640010040400e010216184841d010000010503214280544582c1158031420075500c0c003854000e0910075150810410214244070a1003151143c0110214040c8041031a0301080c0d440e840c191112400c46c90a140c0c004038000c10303007080007800b1510310341001448a20b03400700e91300ca450300368103400840c40c401c1d040302c0b0900040115620504624083d1511401540e243c00e4803400c203c0440b0400340c0006021030355081503c1e00018074052200d6010300c031490704000c1025024403161310ba013550000906008000305448006549807001c0d403200b140e02101441d000c540c4c0c0e04e00a0069002445260003207030605400c0c0c0d41c8a904070b041c0011100c1d441c6e4400708150300784001599681c22000600c5c0600c071091403692020441840380300c0c003a15804e241c3c40e40b01c14407450000c1800c01e043d0030150113038000b0301c05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 467955755 1250 467954505 467954507
    0x10e01030c05010809070506040602150a0c2f0d0306150806030304150e040c030e15010803030a0513060504060b121605011b05121e0a02120a11010e0d030e0706 70
    0x140c16a602483c101c03220345c030307021759203882d02d65144c0100790b00040000b40010802d400140c40c029542d00c1403114111580e41400ca0001c070398400312a40f0218412070b21184d5495612a000001107050114406000f400700307807880d103440c500f1802c0714042565401c0a010701e803000513018010102500d4a0b072207030301d06080800e03141d02885c440d030f40844180c469210180c074000e40481002c2c070000b800420420005550040c05080420300040041c0200640d0a0100140522550584040000842c03035511900003c0c8001d201c000c221078204180d41e0044d20000314940603003406140205804140740340d072001086034100840358042d40070707804601021100700710004c02c0421188242440380707603540c1351400901c1e46141c2ca100200540030b41c0303200c8031500c19903802400304012140781001465420400c00e00c101d2056080e07000240e407001003224100c1d2242c07401420120900e1800d441c0c0700140c01400c40c2520410b2000c40803e4024175031000c0e9141d414400c516424039140000c014491901074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 467957005 1250 467955755 467955773
    0xa02030a14190b0a180203010e0c0406090b0d0f0e07060e030d0801030b0601110312150a0b07020d081306031b020c0a18150e0a0605240310031712010e0103 68
    0x10201200c83d00c40242c101141e480c000b01c1d500a15101040c1940d0006541111000394000d0080c2c04680710702c02c0202d18070010900585080d00c82031344441101c0c1303061040c00c48103900702c0948240481d03221940568070301d00c0d5001e000a440c82950080040d14100007001e0403847c903201841e40203078070120580c124540d2142080e81180d4000300c41c101c031602ea9100403106075080c030500301c2061200107031000d0140007012900d84244040c590308107207c0c458500700f2030307040000d204880704200c06100d03050151510354440e081640c480c5a60610384a803e5031410340c6031001d5070200d408240c0e0345109017042c6004040211072107200344007400c00c41308003c0014055041602680084031040c07244030182907a65486240b135014002074000c12180e072502190208038048880c458200d04020300080c2030f0030042013455541010a154118040d00740b051802160402449200d0b0000800c100002248940c414032000c1001d8000942d6200c1d00c035102004403100c183d100d040e40071980d200400c04120048 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 467958255 1250 467957005 467957041
    0xc0301020a0c080d200304030e010e091602071e03051605060a14121005120619090201030204030b130b1b0a03020703030b121c140a031e050a02030a14 66
    0x20030455102c40c500d0304c0d02d038001e02008500c1604600300c5442c0c02030095241c4c02652041c2e2190303aa55006542d440011200300207503030401d0790400c0413900803420030340344818118111211071045902c00c903078464002e05442c2c510303030410048100c3d0007414001d00009000120f01d40643c881c02c160f16034a0040400c070148204c502c00d1041154180702c0000c40750700c1c84112212480d491200032428103044209608140c4140b00e43c601c41d070000c818030400400d0100d00c080c8110516019031600c68581b800b80d0024004c1640100e04042d820440400000c0c160a00340e4051201040d002d66a103116148c902030036030000d03188204400070b0008030800c00307440d00e00316003601111345000341c0c03169914642034000e00164011141e1200745031b0003a903c03050300001c1d5140c4100c0c203e140790518407010360094501d4045070320455207080041021a017110300a40045070b0700662001c00f19400154114180100e42c001d4900710845500001400380b4030b80d40d4050144081500022100d007401c04038001002c0c00015 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 467959505 1250 467958255 467958263
    0x40902060f09030703060504200f0f0f0d0209040b0a050106050408061504110c01050a0c052a070b1204050c06040b09090a0608030c0a0c0603060608130c1212020c0301020a0c 76
    0x1850102c0740e181446039400840d0b01150900c600c0c01d1510348114001c2d040c040d2040010000b520841742460008000c001ca000d01074108510310925100740502c0e05503c034011a00708800040c2540140c648200f95403195009040c2c142c1c0900b80341e6070940a8034070603805181044024003080c4400600440d0690b0040d201354400c04001140d080420040c21b036a031124542c2000c0402d9800ac03415043d04443e101d08140d2074100084032084d0415907a501440c0002c0110500e07244066001c03005403158040b46920581c1207540c0340781d440c0b00201c103503800940c04100040f5004244001c0107410441a81052000c440c5e0b1424242030200603213480c05110000752040382000082118062503901c420007804900e01034a55034413400070300b82d990b1441e81e80b0450b4518000c050016185210307101b103900351110f50b60b6504a030f0f02c8601c0e24032420380200c441964050489071000420407442240b0351a4a80305440f070f84845070040201908140540b0721041c003c1e4010001e5960303003a44241e07064a09548 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 467960755 1250 467959505 467959507
    0xd03050901060906030602070b100f1418090a11090103110409060e07080c1203030124030e0d0c0b09010e0c2e0504080f0712020d02030a0f20040902060f 67
    0x64240c124007502d035903484015400d103001c50101c20320842c6d400900c2e055020b020811400d864003058441c07001786078803e005100d80d018009019003408060283c41088004000d080c1020154200c803d4022054812011a50120761103c0c00c00c4031103164110000002ca461340c0f040d41c555200d0456500b0207240440c441c1c1d50303990014003084904e03482340710b0746148482100e503503035210303180039603107400c15480e1b14851400501c0c1d8800088001045a060b00c804c1d40c540d80300307000820a1501846d0541080005068079401c000c410382504004820720035205079a11683c404141c108031400200160518149074104110090001800118001c61180c180c5540c00c9060105e6402c151500c9002c004600e00a8920603510403c0d92000141099907120b00c20f5801b040e2000d010303103944110310f200309007159045040300c6c4003524001001c2e1041da400642a06c2443e5540c5d991002440c2c801e000443d91000101604001c82c0031040030074880346030a4604001c1c01091b0307000101030f07000d4480014103900c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 467962005 1250 467960755 467960761
    0x3050403020a050715110c060a0302070c08030d0c0f020a050a0323030a1b0804031d122b030b030601091d0604030509130629040b0d14180d0305 63
    0x201c20007200c0c2c50941c020701a1841292103050b0b03030100c1000702c219000010610165052402e40115889406c0030009140c903150000e4924150042d41040d04142c1e40b2034001c01e000910b9620a1006091400c040c21000910b40c3c3d44440103041150000070707070802c43d80b000708101d0001e20002210301845401d424071049040c4030170111108090801c1042211080220a1140c00d401c0d640040300c03070541c600b92166002542d0001240c07041803c0350b015002400f007000422802204141c1c01ca40200d01511924044440121651401740c41c914a0340303618001c040440f14900750350030303081c41010440c9024400d501401000a80c2c0310418082c580d011980c0d008034644040550400c910000e028905032600b91815080c0544103030004004240189113001902ca5100031034881d031000c0d2000e000132440207402c0d50507014003040c6900340c0c1e00e604810401012420002020141180c030001800120301c40b014a00072059485c0d000e042580182201054407145a0340481d8040d0f01586925002805035 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 467963255 1250 467962005 467962007
    0x302091e0a1e06060206090f030c030d021c060e18071508060a080a0302160608070c12170c1c0501050904080705190b0702010b01090f18150f1503021903050403 70
    0x124200d507002da0010300c3c20000062490300403c109114107111001c0c1c071826455a0140c40d180d1095005250098008009003034a1444590103018200b00c100580c10b50f0214107610301046480680258440445c980c00b000b04c5501001d0003e407680b9a142c010344022880c0031418201103461301481d40600a02c003001501c1c035141e6400940040c43d5903811102c0d5100d55040c0a5180c0799080100000b00c14080800308941c3e00408041e8041d0250f41e640703100418240e1034644d40c94280c882201c04000103e900b03214440d0000c401c00d4010960141c00355074070040603416420315030303508003518066070400d00100880d59403001c00b41c4e8415002103c01d81d1360a80c51a21506002d0f290307440084a05c0c500100c0d8050090010900d4400c0c0e01e660001c00c02c3c800d10304015100782c4582e118802003c94000f6060117000f907041200203c1d40b02e038400118102030800f4085400c09001e42101c0c0d100132500000300280480300300c908184801c3c50904514099118403044001e850705e8602034281612140400c0c201 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 467964505 1250 467963255 467963291
    0xd090602100f1811090f13020d0807120e1309080d0e0f0613030912050d0f030f050a0b03010b060301060503010b03070504031a0906070203040807090b0f1003060302091e0a 75
    0x2000f014038500c1e614501c500c1c1a0442103c04081540140110f07000203aa908600c41c039140901c110f0115454014031aa00304002e8140c000c1b412108030070306202e00800074419090401c13045802d51607a00e00760301c800c0203120b4811000444422200c0c10f1175254070204030201c0403513440030078a0358041840400716070701c0d5103021001d2800d024244501410070994880d1a100f26596620996a126109550b043c1c403d82003d18100c0181050f00003440103046a0f01400002070840300b24200840c1c101102a00001203401c01c5410100352925080090304600d02881004604041202c245003113504000c0010144d0105000c0c01c1c403070340f00004c08201c0f240e0060040c2c5000f550301440001455900740c05000400005a0b0030b6031084c40340c04007184800780048181c030159000c0100826520b407a000d205006010006089a08500c1c049100070298407000000c0100560a07207000c14110301c0c1d4814003604100c020a1030071303401c074460b0721a00755984d41d481050f0003019000001ca02510702c10345800b02 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 467965755 1250 467964505 467964521
    0x41a0915030712060e04030203090d1115071505160e15030a020910050a14070c03020a0e0403021209010903060b03101a0901080a111509030106030804080d090602100f 73
    0x44188044104508950701c0741d166032440f014400103000295592650258585081c0c80040140c0c00a01c00b0243c1801e009000c14646d9005269010780f850f00e04d4081041c5d04030624280c4e141000005582040c003a50090040030740c0c8002d41c041202d0b142c0039010384000007100034040200000c46408540c0c075a6245200f08102e41d50400c1c0c1652824070003d0351009502c541c070350b00e01640c490b2801c0d4098500031015615010030341d4031078118000ca05104801c040c0c0c09102d003180e80e841c00c00c0c40840980c90b4500395101501c6040d1300e522983c1072505019103010003414065040320301c20000011580d9000761200101ea80c041c1c0082030901c50180003c2c01c200c0c1c0ba440e003480c001c1c9000240c0903d425a140d100072010815034201007140d0300c0d00c40043e15484034103c080e000814102e600c44a50500381c1080051445541c03009040500402c0000c2c255504c4e903005460b05200420140942d80c800e101c965100442c0b401c1c2204128a0408082c1d2203290114880300410754411780b04c41c04844035004524 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 467967005 1250 467965755 467965789
    0x3041505070c180504060e120a0c06090803040506060a15050723061f1409011403030403050f151303090b03100b0708040602060c03091207021203070303050417041a09 73
    0x1c0e0910800d0760f9200401c1d00300e0b403e991140c03c0801c1500d41000102d948000c600100b000300740f03016201c90060318404c0c5000c3c000c46080b0307501c1c0340b1a03002c01d00000c040c0d070150b880b910240011b0b040c000204031100c0781d907801c50002040c60751401c852041d0480201c0c3c1060358400110038800016010b8800940d10052805105001d034008020000070080e01d509802504610b0807400304d40c8551103c01d2000c8541082500070840303100500c405400700741c102041b0080101140d150580f00da448609141c100c81c91121298070002140007951a44040d081c1d00542000107400060720607100142001c07114070440201010000109080c031080f042284094001b85054964075913092a0240340c96006104450050282c400454840f6030030b181200d010b450004000d1400710300c0e002141c6603561001c0b1040364000c1c001907503038141c15000e1000d403000a0003501c0020b4186031600b4070039035011140d10b950b094030030108000d110148440ba4000d0100f52062005038076611407501140008204407507640d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 467968255 1250 467967005 467967029
    0xf050405101206060905060417030702031510050108090c040929190c27050d050a0209010e1317070203011b030b0301020f0d1e1506020c0303041505070c 67
    0x101c1040e002100c40c855045000c03010045150b0f118011a042d4559014050744924104030400a4060b5801c41e0207611421409491402d42e656002030324181662a2410101c2c56401c10880c0c0801040010710080400303092844141c60100e1109403105818008030f0b20440c0c2e2004102d046c80b40c0000b80e0083c0440780d03141001400000c0301c0503580110304603000c010101c0d01c801e104201040038059101c0403803580d12860783c0c41121584041c03d21482413100781c08020b40000024440d5a010383c2545414090405400e2030007042c01800300454050300008649045401408030ba00070784180e00c58481c0d004001d01c45800d100b848604218030034008060b500d07600302082c002c0c5095040c81c0c0030200c000542c50407c2880945401d150a0740210300f000348070b1300030a11078911307103206541001e0140028000079044226000c042c0030100c446401c0d0000e2080c07002c0c0405e0000c04e404110304026003008030b00660610b031803c00144080744035000c0040c1000350204115003000740310700c06580505400810700c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 467969505 1250 467968255 467968279
    0x40308040b04060917071509050a3504050f03010c05030c0a030b041127090708060613081b010504080601060e030f250603141803070501090f031404080303070f050405 73
    0x1650094104546c242c400001c0c1d9126800c0402861181d40b483c1948400905035003c49603c0380f04c02c945401c1e4507514821902d028100d2001e601c0b080307516400c841c4a0340503403128146010b00c903408040c003040600a03850300d9000d80c0c1c0540c01c40103503a0b2003a04403c0496603411503e6044014020100b0302d242c01030b040110120800ac0c1ca88083c108600d840d4031301c545407140f04229081c2c2006800b001c19007003001540800c0102d44941c030225803214000e4120b0346440040d1100400500d415446010190403040350752610607041003081106000901e821030805041c02504c1d502c0d818180b080c00240700311040b040c031058038203000c200c0e52701028106a032803140b007250840103164100304004140205a1741c010882500911403000c1c08450070060130503582c0c500c946180b4000c00440c030a4080c0c031003031201e4000940c1c2402601e1985105a040e010742000604e0003900102c8005a9840356010500060000d003200005999101905141c0318582c10085807080e03031944201c3d0403880d08451042d0766 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 467970755 1250 467969505 467969543
    0xd08070b060301050f13030804031b03020601060201150506040e22060b0102011b021b01020708160e1605030a020f071205030609102303031b0f010c0206040308040b040609 75
    0xc400c1c0716600c16002400243e541ca43c030600414070454421303040d4000040810b0100388900801540700f4407038109194020100d0a00503450706000504030016030080005010031030342030241c58500100c04922044503800d01000455501550094007180410b00001a00c046040414052030900ca203d002e2a501c820307007811230107022078400441c0590b0a1502c0d81c0c1740740070480c50750402428907501601648841c2d0410360030680035924403130304600c1808404251711308140176800881100c0b00310040050300d8041a04000b650040c621080c0510055002c2d00558005e01200e07401840d80390010b80c3c545140009035818041c031007001c1d2005500c441c4001301c20b50420015805031504031074200c800c1c0c1d54200c082c21010958026000f9141090388c80005003149039800c4003079148010203907400c0c080480404805040810342c014031640c403850303924209040a2240d95200c010324030150911b03203042d0303d018161040150008000ba44100005000d00030540d00400030203500c026100761003442021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 467972005 1250 467970755 467970773
    0x111c020a0506100e0a05150907020d03060e010806160c0507030b0a050a05060609150c1603020112020f0a05030601110d1d0a080c0418050a081309050708060f0d0807 72
    0x84221400d200b404041100050000d40d5041140d410303540601003540c403800000c2c054038002d00010741400030303c2050700c04c83d55100070321449105158014226030140c1e04004080d69126409a55010510300061040d03420110710380381d118001001010444003168412075601c100e8020180c81d50181d104080100079a401d000c3e8000c0502c07820500c0643c44899113041292026100950b11250800403029682400140c0c0307440d00c046a4074160070a07440542650030280703000d001c0844015400b500307004640e04480355800c0d50007161801c40c18420003164103090340c03003111602014000302000290703045e0311a007000c0040028100541c0d80c802050302d4081c001c400c0c0010407d0345144031500f048440c0c200b880c14401118a001d0040010360702e00d0f81404020904460007101d1600a030003848046001048100c0000d4803071403140340d46a00c204007100380c000e82a0450f400c4142841d050003600c0d644884456005082101c12160709040d000000d202d0190414008200050100e082020303c50004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 467973255 1250 467972005 467972023
    0x80703141216111c020c04060b0306040c1b0204091119050307050d03021504060617150708151216081609020301050907030207051203180f06090a03111c02 68
    0x202c840782c8503204503001961941d0b80784655220302da2003040c1c40e00c4070415115219000341d0150041d6210061130300046000c1d41c00c00d410100155a001080c041d16003058030442c001e410107480c203071070350400340141c481484244078000b81c42281c0b030321416014000c81a44c40031003600c2c0100006400031180d541c89415065038403980b4401c0c041c0712000612414042e0305126003a6040c0c4c0a03180c04071281c0d04000f01140080e00a842c050340d682c43c042428052980342004180c465070050002003031007010300080003001044142000381080038880c86503155400e109030118101c41d628101148800319074900803210015000501c403110300003a9102e004202c00c9164540c41c1e03030039010783c6d4442516070141d00c42072141e00c8d0402502c10001e4000d501c030b07a003d010590f105a065840d158000c2c1111003032504150340742c2490080c44000c0d00340c5d5200400408001c0c0c2c1d1a82c01074056403505d010380319103401c110030001e01400340301440251448020312012a50f00031800800e402c2c04030405d0001d42d00d43c103071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 467974505 1250 467973255 467973271
    0x151902070b09060f03090a060e0f12160b191b02060603010c0503070804050a08030c09120703030f0e01090906060806030d0e06070201050a0c15020c0106090501030209040807031412 79
    0x2030101255442a80c8110380c08503001070007203450134507141d08402483d40010b10382002d50154600550004185005540a40140100410140ca2100c100c3d6092082e9040000c45400742048040c54041d980d049410050ba001086d0b0ba401d651090b01440c41d000c0c017450b40c0c80c0003600d0840c081d104100c440e444038143c1202c0d0703822103e040d65842c0500d0f00321a010700c030603030100302d040c000511500e1140010590151152094078a48201035498202903042520300707509003c400f05029a16080002210341146101001000003070b240d40c45c083c0c143c4114032550800c00c2a19034152615034020440c0100800c0610802c1114a42d0f81d000180760b1074099030705511a00482c00150000e074482c141d00c10701510b005040c1031a10405500654440e40702c0c1401e00140706025180102086030200022034080141d440940d840d9071840d9042c1c211100368001d00c40451401c8010b1002d40c82c2c06501c2036002d0f0748040c1c0b0954650450a06882082c1d051120501e4101d0010341e00300304080005049006000c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 467975755 1250 467974505 467974513
    0x60906060e090c030f0c070b0c0d1a0a030b0601090e040f020103050915070807110f0604140d12020c0f1b040605040c050901030510080102070804031a0f011202151902 73
    0x1451080102c441801d0380c1d00c1d142c02d04180b0204602c03050444050790414260000320b4503000050761040c02104003100c0191500310701041911b0720444c030b809100701660340310500c00074064205000543c40086404064482441c00d0000740e003e0b40228405400761007100400c1d560b500d460325200444060008007240000c0c2000041070300740000152041260038000d40c850002c0d92010401c40b48040010301110401c181c11003851091101403246244803014a00a0440c0d85410b0034a50701c0d207124541003013020390105034500d010315030100c00a0840d0a10000259540c0444144240341407400c0610319914001c0c0d00c0c4a04240000700001003680f02e00f030300c0c1070004690b2001080120b8407000000c0d804a42c082210b000705611075840785034040d081e01840303080140c40c0c0802c242240c0102c402101e440400040a109201640840f0700e6119880100d002552801d111150800729062003101d4034003105d40d500c00c0c2159600c2d20a81c0018003031800b01622000b0702601d041000e0107941100016000d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 467977005 1250 467975755 467975777
    0x15040f050415090f03140702090f0702070608280b15120f130b04021f020a0606082806060b03040b0402040b0d0b0718180501170105010321050d06090606 67
    0x2d460040e100610b81010b03103032818261325107080c0c42010b6481030803481d6038000c0090400680e03640c0020f84c000e502c0c034140d10109191201d4040e24200315600f04400740480c070020004150020b10520300a10307400340c0d0020121000c5250803020741044c0b02d40f03951140c88418101c042241307010180c5048800c4d081c5020700c80d21070f0302254007442e00680e0003010340c8200ca090100440c00300302c00300390410700c00341401c0030a0b0b84d200034220701551100c50110041e00306094610500c51366000f508040c0c542c410280a040710a00903490702c0c404402c40880035540c80580820034411a54030a400900b1402c94071652880c00740f03440300c030510040710308a00c84ca00c3d01e800c101080c108225010301d19540706072240c000d5100d80300140d41c3c0c041c02d1156000b40f1111054081a410212406105d14120340e02e4023090550500b050150704151094118015a02d484c0c0104082030003140001540c04842041141d907201c810002c4401e44624840501c601d400d01c00c000883c03600c02e50000045400d070741e07507008000c5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 467978255 1250 467977005 467977043
    0x41d0715091e0605091c1511030f0117030403050f0d031404030806150c100903020f0a0309030611040b0c0a0203060714030c0a03020c06150a1202090a0515040f0504 72
    0x181450b099100c0039804403005201d1140901c0c018a03038100000c2c0700000d80c0009801e020a4155031590403249030841001c2c42d04056824020107000302042c8801038250701d0b10742c0019540716014400c0250803461103840e0a42d0403018012200515081001d65070801d01c40c410140e607820040c00791400180c83e2031a03226102c42c41c10702c190b00030f9034180e8441c22262140c0040040113500042e0190340000104100c20032524104501111090755100105034201d41e4140070341000340d0019035114581203017111000181d4027004c0c00342925802200042d403003442106029190150750800d14082200044416000800241d900c241c0b80c400c400302d0340d440e0358061048420680e803004a0740c1121040c0086201303a0043d1018000c0c1002900e401402c003450b050300b0b40d04c2c00c90151142c0700e0000341c03030001e0020340c2400c814006c06402849850034685003150302051410704001c105921803682c85000c11100211400e68440e0880000d0040c0302d08591000c110009100c180c03011175118000941c808000d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 467979505 1250 467978255 467978279
    0x504050106050d0b030f0d082e031e0210081b04080a080d0b220605010228020d050f01061809022206091a10020105090705041d071509 59
    0x1e5252903440a051400012255010f0f0441e0b0020903031502400f40601c0009008010100391005165203021090600380b0700c044c040309844015202403030080180c0082134a484080400710b13035004602040172090403003038038456040070034000e41c080c620541502d500799105c0d00c450b006800720081c0f62020a800c1c3c80505480c8030302d02c10408103402c900c103808049680c0c0809081b00b1000f0701030100b8204e880a0020350b58050003c00e4160090700c1c00121422091184614005003400380000d0072000700310041d0416030003500002c00410401c1c1680041191070b1540310420960348130701120b080a0b032481000b070103040035025440702d403482074003401c1c0030721098003c444041d50090206640000256420300c61029040610301205485400018030281c03c0d219014098500446001d0003090031401c100d190601e1441280845e070400c0c041c0600c0001c0492101d044800c2200c00042108811000c08900b61059540c0b916134010f80e0b0000a04030421480840b490080742d07203516250303448801d00001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 467980755 1250 467979505 467979509
    0x30f01090201080c0c0102040e0a23060108010e04020d0606090b13150e072d09050f090a180212100b010c1a0a020f16020103060f0b030f0c161a0105040501 68
    0x1d030000000c200540132010050007042c90940015140c030b500c03906c1c00006181d059a604c000300d035a42c0d0100701202801704e008031400c030030440300700814108a40000c01014040c0502c028108002c40420210341d22208040c2078268043c1d4240b250300e6640c65408010700b07541720b01500030b4046002c4094020018403403c940d0302d20b07a40700403034181c0c1440024150313503100801d10001c1c024003001400400c40700c0711204521400c004103420550030600001400e242c0e041e40705038010098401c0310100d0355110b0082d03651140c2c01120026141c00c9901803000311610350440a500041074111903540e0090100700b24507503010300c11b4140305040c0b42c003004554044c0900c030041c001441c580100601d20602038000c5801071060480541031090340b030503078a10355109059000760490045030013021540c01d4018200244180342c070b07070b0701c2c1d95291040012840c0310080002c1c55a4104000082c0c58250071010381b0100301c1d0118405006808501d02010007048a0250340004032141c00000740928180c001c00381 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 467982005 1250 467980755 467980757
    0x6050108030f0d090206040f0b0915040e070f03110403080c0f030717030a0b0a090e01050c031911040f030c030303361a070e0f030a0309150c0f0c0302030f01090201 72
    0x116060801070f070300c40105501141280d205404010016414120701e0698004d420180112590b40b442501007185032244502c182500070000d002c00c1001d0b56104034501d42c4215903003804948000007070300850041102600c1c0346036100010401105000360076000d0b042d0569414100d5000f10320514a050380c82c081c0d42c0c0001d00707140b03642608d4981307603001c40c0c050b42c0c20954140c0003060101c0381e000042e1001c419500801c03009907071020441644035007401401d400442c010340c0b0900d541000b88400303481403460303800042a5503d54410341f4000c00071404480c003d06e141046d10315451780380c2c40d040908080c50b2206800203410140c00c8842c035101e80307044070120703030b222540b05600d280c064541002800c004c043c01d580c40c2440c440b10710407040c43e0804062186659a070f07a070304495601420003025280034150280a58840d0b000c80d000030340c010038003809481c010110381c03034040d008580032112144032a000500d11401c85440104002812a502c01a02d1084054070050344145041508031994010040c2c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 467983255 1250 467982005 467982007
    0xc060306030d1101020d02031e100f090908120a021905090109140f0d0606050a121a180f070e0f06150306010e1215010b071a13020315010306050108030f 67
    0x400b100e0041c03d040154008900001d410038000002c800c0032a0011100302c6070008985180000315440802001c0c0d01190810340040c4080c2401d0080070030016500800c00c15a540742c00440c1401280c4c0f05442e980d1200490161451030b0002060700079401000d000700c806440910030010070b6015105607a1041010380d05d512006141c00d03d484000041d4050035034102020640d004002d450700110618840c4c02076070040760031454a07061002038881c9a0001400c80c03004500440020010714100c80c9203403245030202c1e00743d2909040d03060036110003020b10580703114281c42110a8000895180112040d2400c5400907541c0e00100880304401100c0d16940301003e02000854106003401035900008185442e402042a040201d441c03880102c0090200b5400b40c642d00c070b491212860309a01414842d040f00c0d0400700d140e038800c118417207602c0c40c0c1c3c1511002c0000250500d400c0e8100344109680003411950503481c41400191182028002a28211f00701000030401600000c100c40002251111407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 467984505 1250 467983255 467983273
    0xf0303070e040e1b1f020c12010e1e0d0e030c1003060b0c0303190b03030a0c030c0f0803070206060423060f030708030d0c02070302150d0f050709080c06030603 70
    0xc44400c07000203141d641c000d5030f810308451082e4080000d40400c50402ca50002488200420040340d51800d40800140c81540301c00c02d4826503003c00c0c00e004402c41035070580c204001a041c5c01e409404800503680081c4280c0041e042e80c1d01c3d440621401da51044401d481c00880c42c400c04035042c00c4001170154141d40300003180d02032428440c0000c11103601ea841c00245143d114541e00c8559800080e01d10440e900220502002c09200c1218240d0300c8686407003003000c18000d502082c1c981c040d480c016001e04c01c25016010602d401003602a12716988000800010000743ca01120039400035203802d4018494100003416500b4907104040f1030024072010203096090000c043d060070700e00145082d400100103040d182e12904c0400040d0041c2c40c8640141d82c6030b0715100b8401044803500c8510b1b10856010710000c0025031a01c00d90800c004c083c031603101c0d690742140e41d40c92020f000c140509042c20b9161004010a07d58007082c03140948421784151201c00829404001c201e00080e9440c55240c1c10086207 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 467985611 1106 467984505 467984507
    0x1005011d13020d02310501061d0102071701020d020c071a0405100c08090a03051e01090b0f09070f08010209010e0405070f1d040e0c010306080f030307 66
    0x8415040e40582c000404400380044003038050520303800700c815000b03806058034541c0070170580c0800701d00505928460042509204180000b0030b103244020130328102c41a15004284d05a004041d06410a0036021440540107100c410039982008480c4148010340040c0a10340030303000c09401981e107018000840c03411040c184500b0842c0411003800340359180c040d280e030041210b18002110094a10300301e4854460107a44603031000d44c054000041180000e804403c02e6200d0300d40004400803403160b00d0036524031070001003081c041c042c0060503200303180c0d000c00d520103a4401110002c03542c1381c1a240d81260b89800550305070f50002805000c41d60010f000209400c0156420081d03450030ba07900810b43c8104a01a074201300d00c070699408080a0086100c0302d84100400402c00c540307410030f141b950703690701550450120b402c055002425003000b241d154916420400914619660844 = true := by decide +kernel

theorem cover : BRFrame.Cov 467805755 467985611 := by
  have h0 := BRFrame.cov_init 467805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 467805755 ≤ n) (h2 : n < 467985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
