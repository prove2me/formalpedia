-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1780
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:38:53.339628+00:00
-- url     : https://prove2.me/submissions/cf57b70d-3930-4aff-b7fd-5741c69c3683

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 319964028 ≤ n < 320143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 319965278 1250 319964028 319964033
    0x60c010609061d07021605060a03020409020a050703110604080301031e050d1d0d0c14030f010603060b1c0c0b03070e060c01140117060c211303110c0f090901020405030a 74
    0x140540383c07080081000d2646071503651049840381003a502d003100f6580b9a880038015880c2c00d200400c0216050306005181c0f43c1d0b03030a500410303a00001070110101e0b802180c0320080c5904468103074520f0030000301070052444c1558079041a40018040600368011000f1948000500c02d288083d20903000002c44a1211030424001e03c41007181c0501201c480e00d407000c00da40303030401600c1c2e25021035000409003405400c2072080450b43c0c0c161106180d06106241c0300c1c4494240030f2140078040c5001700780118880030910140210740d0f1001003001d15101e410804a0302080554011030181c906203c0400c0d503a07250850115050300343c0800242e88158000350000c03842c0030541c01804060300f003904c00c61803070303030380784504445400b030322105200355004880025078610a401c01401d00c48400c180c55a940c4806090380603180c1800c40d44200602c1305030511400b8190011008508403050100a02104000304007284e9150840b54000b0300402c0c8034000310f03d001c6000c3d01650040d00e009812070303c0e05c000e9030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 319966528 1250 319965278 319965299
    0x90609060334020c1e0a09091205070210080702120c03031605031303030b010c200102070902040b09130e030c0615040c1d031005010f1d06090402060c01060906 70
    0x48551600c02e018191090045154801e1207038910b082680280040303144041c2408980d15490000200360098040d131040180c0d25008041d0141804c1280000c2401140c070346050165050074241c01888814031450740148c0c2d9041d5403e000c40802d142000c0182c56101040c0d1400d03240b840484020100450f41d44200b4000102441c4200030030f11108500c030200d140d068400b8481541c502c100e84080525401c040307030290304101212941072401e55a1100c1a44444055405645a4100c29002c06030181025a8100310710780c041c1c0f802c82c0702113181c9850044151454400c0054590044140e40900d125020842d808140701141c504141e0340d441203000c610030b46400c1c048079200c00d00180c83d001c2c140f41e814036100303e14607080207031520903884011121040b0a100405401545445500241c85404215001d024001d0034018900c01e0440d04241e90a517681461900c0c6800140007a0308000301030303581440c0e282d00160159800780e514000c10000da80900b145810078012141080000508148034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 319967778 1250 319966528 319966561
    0x9150507031e0902011b11040914060711030d0b0d150b010f050906090114091009060e0904080a03090f080c060a06090b030d1103070b0108070503070608010602120906090603 76
    0x524100c074007103001881400b02141c1000d03030b0180c0040d150a00002101c008032111991150040d040001b00c80a0f00f0b001a0270380320209070480301a00311250070021a0410041550072a415080c05a010544ca1200590fa801405150280707161105950405034a1b40c106154029400c031000a09600035006014050440d0455076400914a5601030000324032400658480c100001d000900d85036101004442d8240a00400f06051b88200300209241c0c1d11500e000ca80142c1544980402c64540300b07000d408803404a4003240500c41c01001c000001e445581112004080c5041c0002c034000b65041a0384900303a0f4402c024000580001c003005595000103141d40706130380704202030000684400e103050035600084085038056100151640c0d00c2d50241480311425210982124204019500c440488180a038022030180c3c0165200303100c6405d0a01503240604803c1c280302240f5490490001e45d20444003403014036804010070b07903e0260381e0385000c44241d000c00400c0e20741c5070f08021941c007050607030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 319969028 1250 319967778 319967801
    0x622061419060507110613030203060c090105071403040b0c010b130c020a060f020f0a031b093602040902032401020c0f030a0c12060605090105060304060915050703 72
    0x200c0d50488403515010800710100640e901880d46400c0c90044192242d82220701c048a0020506110883da03845000140091694403006040090315600500d82440c02c0602482c030050380810009009136000821121829800012442d89044014144c0c1c00e5000740d8110b400e001074006228003100d00c0540052802040490380641c1d600c0100c1d1079102105d400220b02405070700b01d2603041001c98030a902000c00e14080c00c4002d40340012450005141d80c1c04014020080f9035100480002ea92001c1c02c0010081418100003600f10709003c0c0b5110503480c075100c0c00003074180761040c0d91881480c00050401001c1011019502d5540742c02c0d40070040c0d003049400c804810300c2640c807080d0112641c41410004141a00500305507543c1c08103110309a0b0340d5840494051207002c0c031100c0001c0c5080d0241c4018002943c1a0810144d00d2504206070380c455440389225140020051100743c0c1c82e403046036040703030b0302080004850000385003c4460400320200e48410b40d192008000e0707884d0301504020500c41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 319970278 1250 319969028 319969049
    0x231909030f03050c04061e0e13270209060907110102070309181b0c031110020301060801151b0317100501110303010b1603020304090903032c0d08062206 67
    0x195501000c4144d400385200d1680040c880b0b00f061115081100084000c101a51402d541341d022504049801030940c4002c561032543d40b4441d18000950b0f140c0280000e01050201c0b20300b80c481d9400003240d419000d01040d101d500c486010541c5039000d040a1b142403041203000b903490b8039450070b01400008603803040041405054589094090a522900604405d603541140203080d4403802102c140b00c42000440034002075a0034880700080030801c5944040031280007584d25814030400401d001011380c06041c240405c2608064a140c03c0400d09580c0721160a04480c0c1c42c1c040e090403929000c4269107015110600414071581c01070035500081618030a0b29819031040442c0000b40e81c902c003d100e0030743d11120074401209580340c2540742c04d8806000344100c0342032980b9108201c2c2181c40c1d2140c124046587c9034441c1001d02412b140440542001004407400885140b00441d250306000144408014181001070819540c00541a01e098804000310701214802040c4000909580c0204100700 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 319971528 1250 319970278 319970281
    0x5040602090a0b0a020a0b06060d0e0c0a06050c0304050607060204030210080117070e1305070b040b030a150e040f150f020706420b0a05120901231909030f0305 70
    0xf1500032550b404d45558000c19030402d0a40303807854850740240500358402010132140983e42c01c3e501540055050500140418035154000c1050a02c01903004000340001403240c45142c80c1d001c0300707070340499006495403540c90a80b4038000e40284910341000b5444880b84070159092a40603420343c1c1695040c0c1d0050a40303012146820351b840b806442502c144040c06000a9030a800c008241c0811610510845614507111110341800f50480c1d04411000c00300402008144111805000716509011211f00066420083c10034007850000b4405464810014550000c2064500c001d031200d00e54a8010014018043c1400010394403101c0300b80d41980c2400b201e00c08a801c40f84030000132600c031740e604001e8038008034112100c0a560800c0801800303808038000814202040062400300c2c4160b07591966105204080e0000301070240400600d6071400c030400c0c821002c0000d140c80c0d100170349a4039400715690918049903101d00b6040c891101410032010004041e000409603450340116141801107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 319972778 1250 319971528 319971539
    0x3120c0a0506012306250b0906160503060618040204181d03030f0703060e01030b160e01051b100906050402090a0c1706040b0d03050a020f01060b0702091905040602090a 74
    0x16075040440741c83c07003013100005680b514a07011000700700700a804000346c0240c50014034000340841c5a01c1c41501c1350101c2c03004000d8210414021580d01c40883d6010683e502c0d017200008200380001030007280203e0000800001e1000a0980310102e030710300400955035141c440c0c912403032500034030f07511420860400110000c0020341d81c18030440080350000550441d9502c10500c110184040c080700c0074142c0d100d401003840000d085805020318051621840c950918203440445100c09070100000c000802044198507030703102c2e084038611240c1c011082850703112110f241c0e0520a50801400300c90740350141a004110854200c603100703a000300c2c0c2c3c4d8442c80c0c6d210040d8100740c9204038403c00014150034041072007002036480d0540c0222010307100243ca80d1000d00820071858404005030041240441c0c0d0080c07950b030410100303e044044c0402440081d03c2c1856035401401541402407282e580c1400240c1c006400b10482210800d64a20500441c00c0c9402c040f402540440c91160141c4011103001c00c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 319974028 1250 319972778 319972799
    0xd050f1006090e070e040201180905070509010e090601090e0a1409060901060501080708040201182c07030903050405090c0c07030c0501020106050109140f12010911030712080a050903120c0a050601 86
    0x2110b50031a1000101e0386c50341d004594051203066003000d00a241c4402061208640c40b800c0c0c801d00170368450a0791042d201c00090511050b0a8115105040c1384040104131b0341d02c80c6007141100c80c106c2119503562100c1501c0405088289600b0400d00460010441518800a0b0250003003050324000c00401e5201c7e0011680c0032411542d0501040704007000c01c0c0194484d0300181c0c02800f201100c0102e40382c5480e0300f510213501c0641301d102e012074003020482e04580d00d142c1080c1c104081e402c1c1080401015600503010340654820184101000800610780c03030f52030401c0b42d08152050040d5464240c1b80d14141d200c1c2c0302d00340581030040d032030048041050b50240503510250742c541c41d4110800b9034982c08104e88503452075150341d00041031030981010440c007402446440e606c142c1040e482d04070302000345031074060350b0b0740440c2c0c81141480c610341c04900d030001103039200301103490480d0751815408003103850a50102002070b00036800003194501c030000403608212151161055403a56640c4005010703 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 319975278 1250 319974028 319974043
    0x51809030c100b181017070b0a080601090f052b0203060903030117012d0b09071706040615050c010b030a060203041505060619090b030a061d0705090d050f1006090e 72
    0x503900c182c02d10042c400a000032408106445100c01100c01c488c0d240c000c00384094014030202c01c0404d010300c0500c02a5030300141c11030080d106588110f29000e00d01000240604280301880e80c0c00303007058070006890104003000c82503854001d01201c2c00c0703080c06880d0316a254400d1089007a8810001905021120180030341220840c3d0f4240c0c0c0c00c01742d0100001c4000220030005020703200c5039207a41c030038055121507044a20540b004c3d201c4505c203003a1580c00130032004000b80781c00d102d1450f20034140700030700b80b00c81e04d20f10a10951a00035129051202d0480c018840d654a42c1d170b2510030703580d03c90100049030300210700c1180f180e00350703d004904410008065600136500e241c0d02031000c0c4081c226480b0303429030140d600f4009162041d41640c2d074222140e0b0030350058565400391521204180148807003d81c600d0407400d00c42021501d60b181c403a100414034090f50712002c1c071400d49074151500b8403100300280c0c4291214030b4195401200595021402000c540c402c41080c9030400601400200c40401d805 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 319976528 1250 319975278 319975291
    0x1801090926210f0f06010507060606020d090b0c0d030509030d1a120a0b06010503270a0c0f06050712050d0f1a0a0501050d02030603030f2b0501051809030c100b18 71
    0x180321584400505420130080202018104081809004040380203406100b00905c3c0c10b8000c2c00258004071030042882442d40c22404014000b003111101a01001919160502e0140703800680307034403070340444c40c01e610807409500030450620607888054401c14900844240c03003165004002100c2c803800a80311915120013030516034103071001585079405840215485007a04080d84490244001c0781c500424621207031943d26032086924a04003c00703540b031040a44002c0005009240c0761000050180c40780103001801180280310700708010780103d05550310583c0d0340400348904811080d4180041010030801f0041022655809040342042d80c07019059900694400e840d110344003003180061f500281c81c50740c05200400140c000003080c8000b0b0096103840d010004455503081030215025001400100b058500e04001000165101c1130403030080c007020001c3c0c0049075510b80709030341103028517035203802207004643c0314501d4441254010050100c0c01c43c0e10354006946400d80c15904041103880 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 319977778 1250 319976528 319976551
    0x714161409060904290f0f010f060f1418030601050609031005100b0c150609101205071a0c01110702010c03140c01020d1a180109092621 60
    0x402d1582c1441030036141c0c400d01450f82420541007100c1180b9200c55904c1359002403160300d80512400da0085050150440701c1d103040e4400950400b0301586600c02c2900c034150034130901c5c201d818200b900411310591040c01c03581d00c2c1901c1341001c90050f0b4001944403000742c4240100c800100383c619249043d00c2d51808050001c000b00129003c02c81c0050a0207051510100e0349101c0008002c440c5000920003003460401500d03512a1351160312212560145c249880350940c9010080354a80005100003100e034000041c484098041c03c1407070400380c1580080188600605420094500c04d00050044d09003402c02000142040d15404000f13025002000b4001742c3d4071281000401e00c10014603a80341480d84c212454a02002c1e84582260300c860540344080d902c80500c030b040b681d1141101da5600000b03440441d00c48100e9184d0425010050058031900d070360394240c0c007040c0b1040b03109000c46c0050303044040c060700b407424030707800c1650f0800c80220358418000d00c24001d0780100e8080c1d1a000b0384040703c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 319979028 1250 319977778 319977781
    0x12050a09031a0411010c4e0f110606010f1715150310030b040201120203070309060e160b030c0403050a0f050127020904030c020402131a13090906020714161409 70
    0x202d628815000e41901803455881c0422400240510008000380d0011009000400455228094030f0014440d00034070078009d60b4140700903e4600465542d90010303003481c001c0084242d4010036a031f226a0403141e140c103000020108003150100070300744411a48205e40c0c00c0c8a204041c0c1c501c1e101c2d48070403100217002c09040391041000683e06c0162540141c41414104102a0030b038400300704907001243d180d0006510340c034481c0144911849292008180c80019200c008014024441034110b10311484940560010021303c20b900e050013580d01456010054406881184c20a6415041e0712501078405502c0c14946010150760030340c80f20040040e010140003000c82035020803c0520000700240c1c14043c50f801480d005030740d50320041c0540b1000420710454581489018108054441900e85100d80704000c40d60240104070b401d8022640c11100116046120389042070103801031300d07c010305107900a10804c24001c00412040c0020716040001c000d0141e55184142e03027210201881604083c1010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 319980278 1250 319979028 319979063
    0x90d0c0f050f060406201812010e070603021e0a091401090f090207050606010807050412020a0e0103080406030506011701030213110406030204180912050a09031a0411010c 75
    0x4400a032890254041d5503901d050708030614184102107030111280e80ea1001c01e40060003075841809040004008044d0500c0b020003408160102854041c510601300150004082002500841c1030600701000392004a50b41c0c40f0054041c1d000500648515024074420030440768187e000c0c0d601d100d80d01e90710f0b02da6562810045000d000c5880180c0c6040000108002c100700780030f501414000c1c0510200141da42c0d25500b07080f8100400548901c0c104560381060050301d6500c801540c098030f90004422107954030034070015021050640c03140740191407410002040c0b0510601400450703215840521440d99003000440d03035003c001c941d005603d05070030018000b505100c2000c88510f2540500041c0480e01c111000308981c015500c20380009400240602c40c12440444244a41a60340c1007440418042e81d1544401c1d29590104420884080b40092910b403140b85618021030700406822406481a40541c442c0d0310101d4068400741d4443d07404000c554898400c20a100d50850f109805464001c1d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 319981528 1250 319980278 319980293
    0x40902060702010522060f02010c0903111201020702100302090909030405030d03020c0109051209030106050406080a060203040305070f110913030e01030f0e1213080a030c02010c0309080109030804030206090d0c 92
    0x282c5e900d003d400351010500410031010307100c40003d40b00036203c1c45540b0315a0b0038000c0c02d49070100041c8041240030481040014110707807502c40c24190403100e00c0340a00c911a007080c0240240500654031075140c0b4502100250568002c1c000740c0000d9501c04407039035a01c58055520f10842c81840c1d090f901c4410004c030803a200c1d5025001034041c84001148440180d00c440303207000c01210078004401000200782c103103490f00b4440d002c0144400d035010b0100522f05200d49403035003441c610180c03985800000040c1014850030403038810580c0000541400c0a041c2004c000210441108a0080c5084004160480807503000c00301195499a83d468131f40016400440207085007507600b14015403102d0804001d10024059212296030702e4031071584440380d1030ba80070352500550303000100d0fa0700710300c5410003c6030740301e100340d81d400f902800c1100d082000d900d82144c2ca10f01d95804030016520780083c00b4201544240f9180c001c0b0300980c22228a61031302040181c1303e43ea0503c0c002c0c049003100403a000010046d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 319982778 1250 319981528 319981537
    0x310060c0f030305151908010501050109260c150408072312100c0305090c040b0604030816060606020d020c191205030705030c06010614040b070609230307030e0409020607020105 78
    0xd9100101e030000e010101d8a08102800346c1e2840d0b0003000014000c03510240308183c0108000d02e884007961340b0b003d00d500e0004181006c0245001c40c94a030400c802003041005c5085614040c0003001651500141f440f9a42c0150140312014001d038500000d2490840011b582030441e02c0030040c3d512039030141001080940904507405074001d1100101e6038041c41d108010781c07a000c5450201c1ca600c4d0074142c05007001250810307544918603207010071450b40c88410070741d0240d0f41d00c00c00e8987e07105081d4460b0000a188144014203160610781c1c0801e840341d000c501000101d0083c0c003120590b940307d0040200d1607103010f00b4a104400040005c11071000006503441080d03004100790f031705c1d040c0d140c0c4845040d54050400940283e0100380100421544402d069000402084c41030341001e007040c2000881c0d1080200c0580b00c503449007800b50601901b02155a01c0920703403280103c0c0c2d100c24401c15500e03a000702c00e050b4007146240c0110783c118140760003040704060f4024940c91408401d0350054589802 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 319984028 1250 319982778 319982791
    0x40504060f052d0106080c1815071505150d020f030f01060303140c1009031b060605011101021303060e0a170417160b09040e01110310060c0f030305 65
    0x1141c601045034044a4403842d400307609400c0c0c90501c00f9410b0003d40034681c0e0b450705544542000d2400411030300e40d0011000f9001500c0360ba2043c0c1d90a43c000c22040c141e0351007075207580d0068280c041c85a43ca00b071200203141c114807030100c800001c4951510f0400301c441c00c8660125a03d14400003024901e001094141d410b4401041102d0810601e030100e450440301400b181c1c4a42c1d50741c5001c1c014590441c0c0400c56454a908000d0300e00611285540e03140c0c4440c1c0144e1403c103444618503030030107029142280c050301c11030012500070f16003800c22201500d00e82c0f1270301d0f0210b8110308112040e40c006008440525411900390b0041c02e20b503580b41801811a1000f0107141d020750246d040014001c404a0898011032807140c0e41c41f0f504001d4540026800d04180492590204180e1541018444080d4048030307160118241c51340403580100b0080c00350540842d42079444d1a106c011541029000355014810050740801c6c500c2c4c81c2c8400361203401da8060003510b003601c402c2140000903c25004282c0c800c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 319985278 1250 319984028 319984031
    0x80a031e030908070c051206150103090f0b1f0801060501080103121b08040315050103050a0f0212010e030d060506130e0a020f040e070809060c0703141614060604020a0e04050406 78
    0x200182c4030f60f20b0540001c0c3c804c540c5c4030095a0100000e1410500340c40155501c20054503c0d801c2041500e04101400c2e100b40e0b051640395000c000c1480111200540c0941c0c0006d4040600d203860000306440840030403401040442060010407001c50500c9004240c0f07406851351500c3d81d0a5840b032601074132211881900b0850f401e42090011644008015582c51041c841103807200e04515280f0500f00a01d941c0d9441c05180c4401000840c50001d6050402900b241940300710074003d002040b00c60203554a2298550709022040840c0000003008020b404c4002004101c0e90380c403003007041000c0c401c100d2611410050b008050001484010744d558200c010035034010711b00055182581840e400c240d010301c6155404038200108282c000c3ca109602c00301d250007804540c0740c803541101e164003a0090240030005010309000502618000b01c1c0c8420920305401080b0741da15141141c003031040510800043d001e1500800c019041500075918208420b85540340007240746c41c10f00c0005c04005000740c4e6000e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 319986528 1250 319985278 319985291
    0x40e0d0c0311032a07210b072c09100b09280b0406110606010f0507060b030f0a030906030c0207050f010c0f08030109060f0828080f0301030b01080a031e03 68
    0x41098503815551180500e200040a800011115082c441c20758007560811031144540b030500e001a05e0300064259010203103900c5508e074101b048800215a072138010f80b0440300d035066000d0403111400c84084183c2142d034a0010761340d004c3c907100c01c02c0c0580308100c0600424840c0042515045000806900e0b01c200380200310600c91098940b500d10396406000e03d29000075051013415442080080c64501d004c000b020305003800c000007420525880002d90030040c0210707043c800c018858226441e244001402c0754000c040d9100070540b100382161044000c56070000001801a0290040c1074111016802034800245041c050000c0000c082d00d40904100070003400f000003400503507081c172105002e80f45268407503040444c0070b001c0b10030701c1d00b0885a201c000c1c0c1e4204a0324800007125041640300c100326104006004844410200400d080100100340c0410000043c40020007e94101c82c05003400090350f0340c0e0f03414829240d1000500180002d000038041c800060b03000800c8130402c42701c2e40b6000405 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 319987778 1250 319986528 319986547
    0x8090f0307060203070906021603240f0b0906090114150f0c06060f0f090402130908071209230111100f0b09091906051909080702040e0d0c031103 64
    0x40d540404000c880d99a070201c180030000741e200031004058407207800108405061a0002c0e1040101340c88018038285030070751200f9200120101140100715042e4050061040e1703000c1c1400076003950f80c0c540d80500c0e00000020001d140240200b412252011410032846404034240300790781041d0072003620b07440420440f984c00303156160001c22030f801c154405040b6a05000e000c1014080100801c2403040010841d001c031155900d090756608150f040700e801041d03d86030701990024011280000d00840c002084082c107228a410209a64001568406e61400d444001c1d07000d8441c006481c1102030841500056150750003503030071407101c040200445d0380b000070f0b0310001000d81d0140c120082141d601d42007a4852800c0c01940c1c10381120304000038144042c0c08125001c603e0725418000ba02c126114800300e0081061304410803003150b0b0101041c802070717003103060100c030365030054204902131031070203c503c442420089118103800c000b903a00d1414400d4140c4048030703c6200c1d9101c1d0358440c0420032656a4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 319989028 1250 319987778 319987783
    0xc09061503070323060f10050a080621060406060f0e070c03031b0207090f0506090417040347060409030e090406090b010911192c0a090b060304020108090f 68
    0x541c4204404c000c50030b840c2c0700c800e11504180c094801e60040d00d04a040c00b58054018040d102d41003064a0170b00210380e11200014401908041307051180000720b05081c0781b180e0f021a40c188510700500090241c141e0300c4004030b01e942a144105000c1400d80f0001c80d010512409000b0f0b040340c000d01d008140d04000d04d080c0c500d14500c60202c9005a407201e141080588803500540c01110f402c1c40080289180c40d00100d0800c1d01c00500007003420b10f659840480c691035102c15100915000040507080082402074203445246844528040e001c68100a1460f061400261840b420752008001019100c040034440640b80d0003c040b82070100c0c101c0309040603252103111510a50003001d021454406d1400c0c03d440c0454180c00203401c40c0c2c100208541c00c1d45203441220220713812140c91404030145002d0480e0303217401803100020340745980c20b1034500400a0503450403000b041140c1c442503207039030f4030820b008549000c085160408824400035000d58003c40d07015900c044020140d40610008900490 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 319990278 1250 319989028 319989071
    0x20a1203020313150b011103090f011803080a0801030c05030c15030c04030212030d06060f2715120513020108010e060102010e03190314040803150103060b0703110c090615030703 78
    0x4502c031742e103500c108202d42e841500c411207480a040075518010702000821040e001089000703041c40582d04a1400b0341d4200c041c203000840d00400351a44034214884000d254040a02c001d9a80130490b0101091a10b00440c4080e81d84000a10310091807034010181509a0401841c001d0300b6403080c0000409a103585001280c40103000c030141d680c52095400050031500740e50018410440d0600da11606a60041000b0180075020300d200042c104c1c11640903541d090190f08a0309440149060311500c0d540c101141101200203c1002d100d40d58901c0c2020741500103101c80640003d1101c0010064045142c0b5010f03007210041c0300114549036144080b40c5141d014000345002c803114a8100303280d140e4180709640003084800c01c0218141011b846680041c007015111000d02c50280400392030070b80c005d40c405d1004010040402e0b850f08407c8c14050b1019489690944d00d6000b498280c40076803414404192290600a0020044003010700a030600307904010501030500d40d03904459098924101d1112 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 319991528 1250 319990278 319990313
    0x100506060903160f140303180301090609030f030c03021c1a1009030605130f030503060f09010f060207090c0c030f0e0a12050c0315060f01090509010806010e07020a1203020313 77
    0x903034900d44114801114130540c001001c0f000c943e00781401c05c1d980801181d4014081200f82c0c1a01c00300c100000740100508000282500c0c5012030502c05c140c2c2100c44a01d8030b0200d902e0422010020326001c0d41a88650b41c0303003c00f030102031a881134101c0b80316400182e0304034003180c041d20700710100b001061a0018240300c01c00803d04005040041180c03500507694089400b0402c2144074546a40700c00030401d003402d00405101c03011002401c0c41c0c0310806080c81209000300403002c80d507503400c00b00d02540c48500903440140105200843e150f0700d81e01030241c00c401e1a540b02c041559580d02c04407401ca23082ca0003541000341c0f010310085540e03502040709014042c0214a99090156480d01610703140c004900c80d40a9040900e482e070a10300d04044043d8000340644084040d80300d2400100c90921180c0c04c1140d003c2c98000021803400320026004c0c1c1610603100320550551600403060380d55800c0c400004284002095401d0341543c0309030003440c0c01641c0403e90583c3d1040f180d5403800c0400b9516160b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 319992778 1250 319991528 319991563
    0x30c060e010527030406031a040c0f020c030a150203071211090112050f011404060308131a0c1b010504050d03080f100f0909030c0c0306091a09100506060903 69
    0x703000034000188500c18143c4004510b001c02541100c80d056203030b005038401e04c418196140000c04084c12004481d525071a4000e004201c946084503001e016903032280c0110005100c1c0700211519420000b8030700902c0340e0005440c0140d404d0000001c1c3c003940c03008043c002002000340042c000d801c118061301034608001080a03807101d01d040c000600c00d290341d2650000c26420035081c00410b000c442845410f6070f20041850250510034000301e005011981c0c030080003042c0014001320300745100812002584d425444c074072101034030505a00094024449070315140d41010208014910002c03100303a045c1c0f80181041818030b50794400240b02c00e480081c0941c003041d10041004100045c5001083d40581105036003540c3c2070130201a0b088954403400303410951542c0300140028140140c070017002c180d0f80a00e11082168403841c11502030b0910020450b0401034207000d4a080f00b658446c0da600c191801c50083c050b091103c015000034040c09030086420203010407954505d91000c1c032000c00c95544240c1c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 319994028 1250 319992778 319992781
    0x21060a080d0f02120316140f0706090c06020c031203090109080c0d021006060f050c01090f0503040e06150304020405191a1c030f080414030d0506030c0a0302010206010b07030c060e0105 81
    0x14040d01300390600b01030620300d007410020489441d8071500f100110303440c145055400f1844807082c58049200d006185204c003900418240c0400100d50480c00c4542d01c280d0b04030041c2075580384240d991725000d002c865030540241a96200031410103020b1540000304400124000340b25480700c07515a4070a854040e030f10780155071056240c0d90108050040042e0510b4100445807800c08010601c6110f902d0880420000107200d120031042504038600403074002000c000c25120b1071070069074980c014854060740070800e01c001b500a28240c05040b40080741452413070700e150358039802c000042000a010b011440c50400215034200c3c650700c00d200781c120030001c1ea95420b180c80020011000312000e02e03120401c01c0541840c0000390720a442e1402d240060a01200d151114500503076402d0946656284904c40804e27590100e100c9508428080c51099041c0c81018070b6810512480380458007010f8056400f14004100190407003008190050007440e010808070500c3d6501020b590340c070748220015039100c40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 319995278 1250 319994028 319994057
    0x4060b010810050a060f030e0f0f060a05040b010e07020f01050c0d0605240c19030203071e0f02010e030102090d0507050a0503060103031e05042c0a0221060a080d 71
    0x7908103801110040b540c0c8000ca00d480c00003101c0201c1c90144c601000003502c00d0480c0305010b074014815000941d070584401c1d915074559281e40d0300103405c1e1007125118a00100324480d070036220b56070040790008a00d0b00d0f44da080100c543d10719280549450114403441030441140c00b001e20446000b2000142a55520210b40c1080c10030703200d4030b0300414425506001c010100c01c1c40c109403002001e195460341500d88100b542d020341008501080340803901c1c0048022410182d02000522205110f219001d000000240642c107440040541c0184005480069540558020381e00b08540700700050000d0314040d61880070501c1e01c1140e034021107083d032004134107020b10b1401320401c0010300002c2d4010040d661440d1001405156061107030341d900c400c1501d4000840307120b00c0c00c80303000d068201c81e00080c41981d10360034082e0560000d40f020a412076400401d50a162500072a0503110001180c80c440c0d60468a50045036540070b089180e000b42d942d8030008801070144142c10404181c0d4a40100040780c0c0d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 319996528 1250 319995278 319995287
    0xc090a0819060f0e190f0512071b050f01030f0f061d01050d120309022e030c050906180414131709090f060d050f030a030b0303041d091504060b01 64
    0x80ca00d9403c80d040c0309064188200018055a50040c0030450b20032000c620704140f02c50820821000d410750140c1041d0100c1503000b400101130b02c0d88503020400c0303410103c5055803401740c038500030280c2c0640640c4c0d091f03100c4e42c4280c001b072002e090503100015117a07101d003945100302c0702260300c04040c0c0051a140c44001110040d0000d00502003034403600f0395100d50b6a01c9a4807003038105141c00a051392208610195150742502c41c0440708441881200d0825650b0303229034007074010020000081c24172030700309c090600c00c1d0185c6031080c1000c0d09160500c0c0ea40d201c1100d40000e0101096001a560b001c04c2800300800401240505c2108401c00c070040031030b090019111038210340b10070a00000304040007040d00c4810f8807581c01452120001c0f26900c50100242500c504104003404610036401c9c00282c058001c4020024503103140c5080218000c0703507090544034055889502c10f40396034140c1c914211041031203010b80c4040008295051008440c0140c0220b0205940c290b500c55694404140b095801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 319997778 1250 319996528 319996541
    0x3091204122d08070f0f0f06150303050427020412150b03060610030e15091009200a0803030403080f06090610050c0f010e03210f0c090a081906 63
    0xb00c0ca928803120007281958070399003030080c050b1100080f03040900c0800c5611000d421380c409481502020a800c1c128441034110400395005440d0049201c00405020041e40899901d81c40b42402c0518142e00d50310518200d60403400144425580c1281e4076101e44000c0010f4581500000e075203409505064030180c03d4203441101d000e00e425000015558001200c035400301c01144c01241030024124202d001e09500005104184203103240005545a404071441c41a903540c4125031100e2051602501502c0920002402c142564800c0c001d443e0551680b401501102506000d841582d61400f41d00d994011141078000540c0702044c45075480409008607001001203840c4c2144c1c2c201400000c00002044002d0f005000b00022201c0f41e0210601a05824500b20030081040120741400a070b140e5009494100c00107075808041c03d12a4204c501c1c490040c5405610100300d50b450340c0061007a41c0c442c00718035511100c11030001407940810030481403a07080f80c4c024800c0303070a0103140c01c5066980 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 319999028 1250 319997778 319997813
    0x40503071202030c1515060d060602010507020c060d051f17010c0c05150615070305030a050903160b060a090c0e01020d0503150f15030115180b0f0309120412 69
    0x30851407039001e01c0092201c5c036500144207481950b031200519811a0302d40807100d243c00000102d004220151650b0000d4116055070f00288019501d00100b240c03200e80040071941d1294003401140c00e160041d83c0400e40c84124130b941c3d241d000502006c0542594215403003241c1c0c5088522990207886801c0c0a2244a00400d040c0994600480c0d501d09491351a50021008020396802c0090710566032100b500e04800010301320240e0302c000e281001042e6038012200c49140030305001c08514a4a00041100c800205680d00140315250641c1e5000c05640080c0030300c6c2d4421400072022a145070780d841400d201001d6a206c0f0b40b80c80080e0000603042c0703600c4a102400b8440d0500800a408910283e007480c440c038101c0d4400e0802c0c0754180020650700009030444083c040120003c0380221100303443d1010032203a500c8040d04140b40030340000d0120b1203405003050618061145080d05a0128003454008903880d0903118800d880c403441c60b100340c200d60700c000382011480d0402c80c1401b04400742c0380d56000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 320000278 1250 319999028 319999033
    0x12040c1a0a080c030a0605040e030c0c063603100903020f0703230f010207121709150903090d0c0f06030204050a060c03170c040e070201020313150b09040503071202 72
    0x7020000c0c0140000030070710b02100b00c0000010b400030b01c143c0c0c0040060035000707104116000b104102250b0f03a41010f40c404803030b40f060065140c1c0ca80b030001e084c1c54201f46440000d2090300150300c4d0724028446464000700120541d103082240c80d50f402e000030307184003692410000c0c210000d410700902e4140d00000410705500000c2050012610560004094034208803117055100070b80a0241d240460052411b0321b554408a10f140030004220580803181e41c90f0b5a410b0303600d440b00c003040c3c00b00a07429525944607510141084010980341c50300e80384d01049050a99081c00c001d00041880282c52103012600310160403400e003c00f200c0b086100019003418076085045c1030422010440317214060007010244002c040300758040510468048148200e0440c000700d050408141c0c20880b0b402c5402041501c02c00b500c0010300861052003901e01c12020000311401100964481d18081510002051400c6458110240c001d0303d0301d40c505401148503400440c1d495440742002d00b044810442c6440464 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 320001528 1250 320000278 320000287
    0x2030613151401022a0102010506010f0503010306110c011a040c02010c02070314120409020d0f020a05121906170610050105030103171614060c0307050f0306040212040c1a 75
    0x2807105408081a1504500040000c59411006030320340100441c0628032441c2034141400c810058402c800c030f403508280c00038485621200d0041d03a400504a8aa2001950600040002c18100d80120b0031440d602c0802034601040420310509485070802e004101c42190460170450307007043c0c403502035030000e244020030264032542c2c0000c0d1662080e1002811500481071150702c0d0700800e112035194005030038202d66450f5a240601e0029401c40c0300303441600ca00d80412200148150b000701c42c3c0d0003071955202d0346882d044c507003540450030707002e00000410094030000804d282801c0c0710300c0c3e0142100d5020341441c0079842c0201d5207081d00013028025020301c0d05a0420003660400180c0e415a584100c0121401100c91501c815500881ca07000b0b03183c00300c800f040414401c2403034103d0000000325003611705943c7e0782d0b00c039280e03184019601000002c00400800e180d042401c4051a041140100003600e0118002140120800c0540b01607c8030b5540a004000741210240c102a01c0e03007941c4801402c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 320002778 1250 320001528 320001551
    0x2220f0b0702010e0301020d02120f0a060b09060309010905060c0d0605060c0706110a1a010e1e0105120a0507030b161e0503091501060201020309070f12260d02030613 73
    0x2500400c0700003814400100010105680c0a4068403042c2c02c0ca100300711b40b20b1222030745a0351010819034424007070100310b6001c035030349181c240503105c01e5403c2003901b64642041e64040c056150700060501715075550b54100303540020f600f03115031805001c030340c1c140c1034840485103010011591568040c520800007048401402e0740e01007594400c1310402c4c145460314402c291121800c004545000030f004014036520f240258039400380c080e05841841d041e56604c1d9440c403081c011400c01603100700052095440042006103040464000e207000d1110036504a4241c5a4555240003800c2e00100c500b41503003c100451602e0810352405140314034a01400c61088240c02c4041c1c043c000540e0500b00840000040c5d001902040500304803c3c11322060401580d44200090007500305640216550048880000d40901415190703c2990064003800b01303000ca25984040b014032801c0d00c005845001d4100c268200d001840242c1f600445204001d0703503e06d8020104994070100d804a41c0b0f2882c6000407078041c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 320004028 1250 320002778 320002799
    0x140c03070e34031104080a0605160203030f01030b060d17030402010e010f09120602090306090c0102010b0301111903150b04060e09010e0609040305222310050f0d02220f 74
    0x10305000034100081d02984c030a0200c484c52140e9000055a4401d0205181c108821940705c540329000840c100682e005100e84100d80301c2c4070030f44600014903444001030000c11101030441e600180c0c000d1450502d10705c2540ca0382003003001100048000180402004107558201d1205038400e0002d181004002e4990140039103d0850f90085204d122091007481080200c103130f04490035208010112001d500c0d1107021207a4501100d01030900650030182080030720b04050040e091782d058044034440c140300d00700051031918840001444201b54640010400301010342c01c460010b04200c80101d5a21414801c000c6c01c80d0f0307a4403100351301500507100100700c2045220300c0c040d0010403c440d121110340725418200c40502420040c041f41c90a0310306450503560610309100101c400100c40f6248050640b940c003100c90305800141c0d50884800d4454050340c030302c107400078000440188090390a040d5007000c442c0480c1c0007006d2811241c071120107143d86980e881800b031700044c0803280ca02c0750031509049803201c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 320005278 1250 320004028 320004121
    0x162703030c11010924120f0b0f06041406160c030b0717070c03180306050a09050f010507021221010303030204082a060d060b0f09100309030c140c03070e 67
    0x10482e18008010040a1080501400c122050b01c014003447c2198090580106212644548180404e500b211580c0c103020b410344049a04134581d000000001105000c4182d00c00c903999040d41080c6103079400041c4d20424034602a60103410400028a0300b01c40c0680380000205080400540e004100304195600000d284441603240c23502d1004114900d5400380700720041d0700014451803c00c0b0030010389016070b9120586c031034015001c45001403a10b00149007280c106440f07400068011001201301c00c03026200400851001040d044903410f109281ca03006c3d0b140070307001100081d4000400300301c2d00e80d0401ca0f5600080c00c4d031408070b40030b0b0300c0a81c480e000701c520207000754002c520114020440c0120b5a008200801c1040041075481c40c151184034a60317031040d400580f098031804040b959441c4244070351941d4580c1920350041132011600e45450340307682040503440313500c5000034400051301d0501040000703182d0800c041940f41080c42013000d0121450300c604d468a62075000c9541898000c09261 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 320006528 1250 320005278 320005319
    0x5040506070c0201120c050c010b0f0604032d031d03011a01110f01050a0f14011217090d0605090d050a090e2a0d05070305162703030c110109 62
    0x4110300042e440161401128040048446460148280c40c0c0c150001d006040c00c4c043c031002002061071013800c001440301c0c280065a004141880309000244844000c5040d6030380c40c031345890072415010510b5041303000b50b40d030072000074540060a1920003040324050504c0d0004070000d000d10180d801c010803c00c50420b071460704210701c520305585102e80c01d020080045540c203000340030311714119112002400c3e02c00c0d050940359250410f6541c05c3c8034000b4a40341a200030340c001400d12000740e212000e0605500e544041d0a16040010106654446804444a0b40708400209992815031b10150038409201c10340f806001040007000e8105a01c082c0f40829507010750101c0314561a114545c550510150440302954106100382030b09000000001d4403100f0340e90305e8280030503a15000100d06a50301599403e0010140480d22100507008201c4c1e4522708409041c0b01c203254040c00a9180010103a07402034000c17500202c1c14106102403401e40c0140d0940c00c2c00c109800c640b400f81144207a80291548 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 320007778 1250 320006528 320006537
    0x3080a08070e04060605040305070f050d14011503031101110f16061b05070b06010f0e1e0a0f0302010905120607260c09011d09130f17040e09010504050607 68
    0x90384240c050000d0703a020b0320018004001980c0c450f100034003039501500040e40c052007003000020308000003294a2094031005400300e851400255076401c0003010b0200f42204e55500c0720100c03503d0860030076094004601075501c0308449040a0f4006084401c00002101c08130000c00449803403100c407108550101240411101000b403250400300002c0c14040b5111800690107085000d130954008090304805000740d840c90000d8503082c0040d1462050003003c4004a107040b00366071014907101e02e000c1003012001c444032182c4040100001c407040e0507a08042c158401d242414400e41d68401604e0300a07140540e80032203a40f2410b5442991980b001300928100905c40004015038005140c031054000c428540310140c0d400d04420425654201d41401c0340007030300c01001c0c15122480d211090502020150801c1aa0744235a21000c062540400054803030b10340307040058002a0b038108a03c018068117200c1c59031180e04081c0d0281000402802c80c42d966030500c410b010210304d01203069170704030b0704a040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 320009028 1250 320007778 320007781
    0x10906050d020c0105131a0118020f0c0607030204060e1509060703091d061c0c2303120c06070c0c091a040f050f07020d050d020c0102040f1401170103080a08 69
    0x110031002c0c1c45481802c1d0001d50034402442031858460301d0201e8000c1c031601015401c02c20b070710020b0300340840910442140785501250680075000380c1e170040892001c0c154400d481c00881e0380c6401e2912009072080c1001075800901040b034a944074040190f102c000300d80318840d00f0010406141c0313600428006600c103c000040d51000c15020f042204000c0185100780301804485c0030801c8103160702201c2040c003a00d1803d0440075200c052094105005610201010085003410548245000d101d5840301b0307450b0102c1c8206280d81e50400100c0f1034524040b0240750788d0800000360a04000010785050248080000d001001506030100071058035014140018211610401c01395018102c4446640162404000b01c005154a0708860710541d01d40300c4118503522422002c0781c4d035200d04d286031000901d06100c00e840100c0d050b0018a000034000d0005400e068445141e5501c00c0e0840e8002c0e007501e201030303002007019604291003030f400c0e8500260000d83c41d03240d034980d90803a00c81c003140001001102d0b0b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 320010278 1250 320009028 320009047
    0xc02010b0d0b0f071403180106050a080313050102280501060e0f06040e0606210708061f1d130201030608070810050a090f170705031305010e0108040201090605 70
    0x52000391103040003405140c1241003410b04901c03004050310100c20a0091800091039240100c0d0030045142c1441c09140c1b855480c00103202c3c0ba2600003200345200c0d52203a4000805540c1c3d0143c41014108500203541c2d54a844048030484000d2684000c0c150f400004c00c0380d29024000307103028440202c180c2100603081c1517151260041c0203540003240a01c4112003484a55014029854412001034500308005004075038202c0d07450400300c4841b64041c1d201c01004001d000068061001a003241c0121036140b134540c0c00b0b113404c103001210306050030b40784912034070001c00d0443d40e03010041c00c05281036031042e4014a4031021b108801090306840043c801096030441e44031354042d400a01e80002907c440302c0d24de000a40c1c440c01081000d2480c2820308c800320300307194902c0c800d800045a01c40c011040d07040d0550b407000c00b03030f0089039034a44080e4024070120300800c2003400107107083e200d00036070f80e002c2c0b5040100261404080c003828904000c85041000300503604459000c05507501e070f040c0329407038040c0803 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 320011528 1250 320010278 320010281
    0x303040803100b030c0c15061c05030915091905101d0307031214030115110f0303010e162c04090804030602040311030d09050105030408070f03020a051c0c060c0201 72
    0x40d0321483c609003000040006030f510880c098020340b0080380c1030785d00a40030120307001c01d042029a0040d1340100d0340700c070620440d01440c800c0c0c1003961103503003682d05007218a40091a4480c5140d041c0c20176103000640551750707150401e00b070494003aa408140d1700107070412012816503074001100b88240840001c002134040e5a41e242083c00240081c1155100c035240d150002840440b40481d601190085290b40040d8a040d029241a2049004000e480000426044030482c941c182178105034041d1088520b00301ca4184021800b07807004080c500e00c00d040000346510145070b0b024120080007940440340e8254104c03100a110f11303009502c004159014040c0004009001048000b4105400000d000040001c15006001100d016039151941c800310807051544071802104040000340b00d03100c040c0703c0d66000303030059900207005e50301190522616654101c0b01003501101540940c2c0035480c170340200801045240c0600500c0071041296174000540070f040c50011b6030004150303d4a4281100640f0700c01d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 320012778 1250 320011528 320011561
    0x803070e21070b0717090612040501140f04020306070e15130f080c0d0605070903060f0209040b010216060c020d0b07110c09100e0604060f1e170303040803 68
    0x4003101030307010301c22080c1c81d04084060401d451502030307420009040707842c0e0003d0780c02d001e4000b042c0ca102c41d4a030200300a00750b445454034961201040c01354002c2e100030300003990303c1103108400000d9650761441c03104244050040c00c5030681001c850400005860125007142c000b0342d181420a00e082a880018550110009600388103500201c4d1031006403081c1e150300307421200041582d046140d00d4181c4640c03202409903400d40c02c40030406650000030f0f41c1e50721155000c401c80c0340c94007419469580d07000c1a14039000360000750b0754020842040c1c51610344030391100074600740000c103500b400b070042c1540c007040e10344920810b021419050901b50345414845005255000c03119070b145150542d0090200d80c4100c174207001c1031013100040034150078491a424020384454920080c1c00c1d2070314112414504006000541040d150240082c03045049610720300075080449100420600642001000910039803082e030140c9080440900112004070840b5089504100710700e41d20b94640c0c00050380c00e440c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 320014028 1250 320012778 320012807
    0x3030e06061f02070806090a06060b09090c0a0c0c121101030b0a0902070f080a0f08010b03010f052b0305041e12080702120f100f14150111030d0902040605100507080307 74
    0x158401c10111607c049607a081242c0b181c0400c0260503220412a5090302a44041642200e04040490004d00320580a451343c2003452405079400111541d501e010781c1c03a10f90200340b02803045019003081200ca04541541200c0a1804100c00ca0040d00011030010040c8504810790303a0020f800d0043c88407e503450680359030490b0849035101c403078440042c01d84812000107000aa0020000308000703a075a0200da040368a40c00520840a040404002c03043ca09051203150b120310801481e0354401605100702e032094040d454182d159480c0040850300030590400d103d41b5051400828041100070440c0c440d103031a08014556150000d42c03020445012011005a01070302c281e04250f42c0c20000080e040c110407240306000c0c454014000c684a0550f140c04204545021544001488034102c070700c1020403a40c41458644815103d9a0041d030440d401968510100303a2507071002015400c29024002c001d05060b200c5005200d00c2b000d004000707024011000307000400000100341c2c1148100e2003284220b2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 320015278 1250 320014028 320014033
    0x70206030f0a05070f020d080c1c0c02060105030703020d11011403090307110a0509130501020f0c071e12110406030c06030203040b160c0602031008011803030e06061f020708 76
    0x303240300d041c00c003154101d84400000b030806000445442c0705031001d6443c41c400380c004044e00706c90300d0740c29104040300070071100b07196600707009090028890481c242460018030500084112103481c00a04050301604200c1c06548590300800050311550500d49000d40c0000d0454a035200f5400101c0313100100000000b440c50000c01400141d481c044010181d039031081024200c40304180c82840034101091003610f42c41024040050381030401412a040c210344500c00051034840d80d0510719030607811404200001d0346c0411028800702e1540d2000105000c2c145e0f9075800c0140c54040300754455214010b00511b01103000d480c0c00d0850301d442d00100e014550101d0310098003511020700130001d41048500b505e540ea81340300800d11308041d22000d410715041640e1501c0c0f40415503140d01000c0c0d800508030704084c200e248400940d1b10b00030b1203185582560303440210f090351400e081c010192400c001900c06660000c10500c00ca079500c2003600d41080c5904699244d0f2000102d5003642480350039480440e02d030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 320016528 1250 320015278 320015281
    0x8031e16030207061b110103050a0905070f06020601120503041505040503060c250b061e09070804140312010501031a040908030919050d030207051903020d0e0618090c07020603 77
    0x10380200f0007405480190f0740b141942201c0c440d03907014802c0c10790710140001104490f50400c0754803c0c3c0105a201c1444c45000c14441c0c40c82e0b55141c41c1081c0350b48a164815040031061001560520040340101080d0802030501941074481c9600c1c0d01c40d43c41291100000801c02c507810034060f0080e1070040034000c054442c1071521b10301d032907120b41c0b11201104c0c11a420b036050400b03100a03000c101c400181c10507080c000f555030700e400b4055012100d40c1e2100c00440c45815000c115502e0620071403062401c1e540700c00c82401c00b4640340310440c2d5200b1506035190001e003e07441810b100e1054080c111042403070701007010b000c00120075403948000500d89030024200447c803400e120540d8000c5010b100c03207004485010b6054015508580f0002c42d0040154108007001c1e03120030b1098015106540c040e405440414035a5581d41040ca07c0000080380940c11580380243c82a401507011050303140143d41c19490810f003c0107d0740c0d900030130121302c0e1103110420702181d101e101d040d054400d002c0d03014004960340d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 320017778 1250 320016528 320016533
    0x2030303131b09020417161809020d050f0d050406020c0613171f02040509341707030501080c010f050408010c03060f080109020a0b1e0d0207060509060108031e16 71
    0x11754094081d4901d502a220151445114001441e9000301070392048030040d903082403000211441102d400c0c10300d0544031686a400750340c0d401a682101445000200341c044d130700020140c00c1000c4400380c0c01c10b1002c144801c100301c9801080300004007070708403407843c0c1e546100982c110f030401c6190050b40e03850500b501800451100080c09580400040c4000c1403001100d814842c16403103140500758100c801803000c83c0c50545154200381100700c2810750380748066100c100c1c0803400d809208140d0002000d4004441d41090810000ca400050ba480c05001a43c10807104540c1c4910303000d00039040284a200c02c0504610502c282c070003074a0190000e0080e030702d41400090150416004040c003445070403200045c007640500c1441c804607805042c0c90000e41c601071504a0940240d44001e0314200310080306414905400002c094041c01c81d0320041c1c031001103092680442da4020801c011030307800b583c010301c04c864000098480c3c0030000001c40649408030646452a400780350041c131b001c04e80700d042980c00c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 320019028 1250 320017778 320017781
    0x8130b01120314030108280614010618060503191d1f0509120a020a0b01230409050c060a02070e040303050910050402010e09060d0c1e080a02030303131b09 68
    0x2078180c065a2202e03481c0041500115803844280300d200301341c2d800503d0804503407007400700c0845000c80c4242c030141d12040b5038540b10705403108440000e0040401500600186401c0b05070b40500001d00400b50f00c01ca41401005042c1c0e20015001500031000000d100004076001e80120805e0b072120024091244901462682d80e0240c910039400c640ca0b80b00c03000c08080c440d511a051040204000406d11250800f10b04600d40c4d001900c81c2046016030070610740070654490340d0034020000c4000c0451040e00b00c1b0380c01c2480400d1385030708500c00d5051000325000b0610004141080301d904441042ea541003081d0117903e0049160b101280b80c0c0c00744020030051540581c406449990040c00f501c0415256401390800c548040b10b00034040b50714007006500b5030801c84d038201c0e8003140c080c2000f1366041490b01c550130161420741c0000d00400c00118140100038110f404030004000d07200040c42048010381c0000d1303e9010040540b4050445d0340c644000780182004030080c03d41ca44443e55170b60036241d140440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 320020278 1250 320019028 320019059
    0x905030d0e1912020f06090c1507050c01030b060d060b0306010f02240a1d0706020c010203070213020c010b060a0203040302030106270506010e100804120305041208130b01 75
    0x880c640c0c81c01e95884214080800c00d01030080302255414002e40c09a9501c60701c800800030300d00c003148100c80c9554440f2070304200c41c500510039800207010203401d00c42000300701c4201585a081c0ca94042c4069000983c002580d40902c823001d09010035040e0001001c14514020345503800400c50a00d800000c200707200c0c0e0011030240c0001e9171905070300c0c009142e041c0e0307030350b804281d50101c2660680c0c543c8074078038012520203804c01e40540010031315080c05c01400c06041c020044c80c040340d4105001c01c0010320b40410100e16000c000b80003441c1000704a030001403861520b0449103160039000104d40c94030200c02c0d406030b8003498009041759161080701c040255070741c10500080303009620303111005c100c0c0c02c03001000303c1d03007015050b41600c20403409a80c000080e200190244e41130048007441055140c0e40c0c40d18401c504810b650340c200e45480d15080181590103490181c105061810042c0400b0a20030302c04040c20070b404e0b0901c07000c1e54540003441410b000901901800c400412400071a940c4981144803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 320021528 1250 320020278 320020297
    0x903080a05010504151505070b0421030e030d0f0f060e0f0603060f0705090d210305010504050403200c0604090203150906011b0503090603100609080a0b07030b06070204090503 77
    0x1040709a0700e4400303200403240d403d140884244000c9004020508003814110303102d06151a0840c00c1c2007003035480000280e010b036403c40715101e1500806103059070300118045034002d245000e03c1082c00c4131000a40300e11484000c1a101a110070204568000c1c5da0040e107a040f00c460420840b541e66031241080954081e10941d88072105603000ca220b618000070854003e10140390360003140d4803040030540341c0e42d001d101040d411010b16281e01c000b04e82c0d1418103050850501d075114940d003120107001002c580741600070314411440c1c8003d1001190344003503103a405e441e988011804014100b14110310b843c0012080691220700010003090710702c0c2d80d0300514051260f0310b0761481300e50900001c100e1900c80485803980010441440d0264550000074002c00140c010341c00d80745040300750b20100d1540d50040341d0b00480c1f224000000c0104551181d4040300508084024003000803182e901d850721600003070f01c045c08240c0c403090900c14554680040350b0280d03a0041c0302f0400ca0020303260a90300c0341c0088004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 320022778 1250 320021528 320021531
    0x1801090503160507090c02060606220801020d0b0306090a0206071e0602091e011205070516050c100801030b0a02031909030305042a050418020d0605271902030f010903080a 75
    0x920129140071b1441020025005040039684c1d034814001d16070000110000343d9100300c0100144040c01d404444050000c0400150742d80c0003602d40340c1c003624030003a5802c1c003035801041001200346000c104401c06940c103d8245581d0009400d00c2142c0d1000042c800b1984015640b0500070010303203078001e02c0b1070fa9094650400d41d001510714103094040890009010076004200d03100e44c1005a4040c9600ca5260308005040400d05010b0301002081000f0440c0c40b42d002448203201480d01c48003038101082d0328034118200e503045995807134070200c004c0c04290565802101044650340503059422a166800c0820010f2204c1410002e0240000f0344049d900f100c041c0003034640d480070140301c5001070f444020018001514202c00d200c0200210200b0b40074101c2300a640d0801a03803414540000940200c03004500c0c1d080c0441c006180a6085080200003160301d102c000400c04085003035480060074008181c2d80d000140080381c03c181c2c0d14111440207500e040d4420042540041c01540114245d800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 320024028 1250 320022778 320022793
    0x203070b181b100e09060114130b12010e0606120403030912020d0e040b060403030c0203070906030f031b20012d2012160b07030c02010b0f0918010905031605 69
    0x342c0c4e100701032a01c01600311511000144555010b80070f00c0c1d0b40c50600d0303010546824050340c401903400c1c1c038507008085184400500c5002c051182c202c4580504400440000340c1d051040018515108219181c82140d415000060506001c2d80c03092812540002d51035481c800c00b103200a44490074480c0042c003081155890b078050f0300300351140a49184014200c0c03480c140c1035403001d03079400034405c80407641131050079004585222180100c1e0300461040b010a003840407140340290a611920003500c030101040460a03000c0794000e1000c45400300c914451402c451106401260420070031a101e144400d9890b4210703030201039140c2840c90741c9419984007a591744854880344c004180e11548145540d005000700d50049403150000c20441c040442c6260388294140da0307904d1201e00c112562400300b0380c0d440841b0b403030540a01401074401310454107080c0342c45910002400241c0082d006401d104c0c44000da14010b003109500c5110140d0704103040b0b9490ba0180c2c900040c0e1041001812501c42c0039910 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 320025278 1250 320024028 320024059
    0x1060e070206090c010e06071401060b091503040312050c09090f060406050f09010b0a05070f030c06060e0f0403051c0207051e0a080913020904020a030504061a010203070b181b 77
    0x180102e60008141c0d11501032006e0442003040c61741040b2015101c104194401e00155042485030302d0041c90600c500f25142d03200c0300c0c2042800e420030b07c40b024025400700700300000254003510400c2c0500c040c0e81d00141c940c03200100707500c0ca0300400001c207070010780200c00d00064200030008030340709041c11181400819181e5041c80420701504071100d070004030400c010720111a0542c00380850140034a81207040c032026803140e80c842c480404050b00480d000c40945420711031240243c0014010100b9180083e00f8a60002c0c424054010406010008007003000280085e564920b402c000c00c0090095403103c0290424603110418510301030440700340380b0a00606082d01090444205401503002e9081048010900000c440c0c10708440c000641d003041404010b5595201402c1000034a580016180c6428078140040b262145a806260400b04050301e01c107a03800003c5900b00c1c2da0064040316292580c00350100c0070390600348940e0706809240785060081c1c3c1006251058410202c40c001c10382c1d002103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 320026528 1250 320025278 320025283
    0xa3218010603030804080a02010b0604090905061b1813150509060f3f15010f0b0703030213080607020616170408160506090c041409030301030f0501060801060e07020609 74
    0xb4880100411402000540400e20007005001843d100f400007003045030998001a096502a801030004c5560300e581c0002400001c2041941c85407014140300300c2d1004440301400035000710b442c260840c6100c0e03c8802d41903101c45500103000c40d0500f10500071410412481120380c0002d006183c015a0203034002101ea00e0000011580ca26000d00481c2c00d03412030440c2c8460896680e0f6040f140700008410741400d030b5029030101c690760340042019203100c03490584050b8200d8010ba014030412044824140030383d041d20001c4400440d0302d4180140d8a50b000c0e515804110b0072940100100e00680c2c0c05c0104040e00400c40320b20401c03018540003501c5000020960310082c0c1c501d40e0b80203003d0080001800280c0501c01000d051041a014010b182c04960f552494042c0c1191403484540140e0b0240c045410075002c1c481440100780500101c40c03812440184e0b0743d0205100150110303603500804400c0c4502940100042d0913640024881c99403034814070005800305441540c010b1240000151204002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 320027778 1250 320026528 320026541
    0xe070201140c131208041d07110c0a0603020d09050115050a1e0e06011e1e11030d020a0c050304090501050f060c0c06130521150108060a321801 63
    0x84407022400f0381c100420070054090303080d011669510708000109440c880e07042c1d1726501702140100c450161170806802032440c1e40000860400d0ba10203c0410a0366441102030019181c040c500140ca503204150194082c14086030007034841c0d46800e0440b0f6013420307400d41d9801654425a0500c0c0013940e2203403c080c40b400f4500e1000420261004140301d10810398001540050b0141740180300010014801d0301c11240000000e4045080c03d84407400d41200860000c040ca2007504000e680d440d00e07901102e807a0b218403503111843c26400160f10305072a000d6092011200e03040701c1181d4640d41c640c40315900138a000e00905104c1d40202244043d149060300495407400c01060180c01d04280003011302c082038115a071000418a01118042241c0d181c80303513041ca0381000d8140104420104040c0c141c1021011488410341c1030890340107015204d00024016041004000c0001c2c0b5441040049032001c4800300f0b610765580318400c0988103114200080354060302d6007180d102d03400c095007070801d070880d00b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 320029028 1250 320027778 320027797
    0x1140d05150a020720030607020102090306011509030c060e03011104061d12010c050315010206040b010608040305070804141002060105010f0509060904061d100e0606070c0e070201140c 81
    0x109000c1c1080c095041c00c0529000341280201504162039907551000341c48180140c0748588014a40c1c00140745001c0000b1600f10748140000c40c5011141000b03e611200140108021500418070070800c8900c1203142600950708500c00e426503c1e01d960307000306208d0707101c00c0302440b079800c05a800204013146406c03902200c40c0d0b83c0301d00100e40000844a22400110081d165204031440001010b00000f805aa400c4140302d81c0c0d941e943e80741000e0055070303c10400300c510381194461001c1000042102c2d050a0644510b8202001140d8403850225680d202e440002040705a020030005604a20034944103140c02048640d140402c141010403681c0e4607091186600003401d02140c00c0d03086004d10018070910f41c010309480d14140c0f0b654040f07005e039659a801105041e20500006180030724415280750041d040c420400c10303c4c5c0c076014001500c081d0180c003403440b0f8000000c0718005c201d91005800c00500e03a60320002c00c6483c252001a0081c4114500e41d0040c005140000300c165070303c03100b156071544 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 320030278 1250 320029028 320029033
    0x5071e0206011206050a150603060513090209010b0304151b080702060f0a020a0203070501090f1a0609040201030b03010b10050306010f090e0a150902030c03062d060a1809020301140d05 81
    0x14059140c1d40060200a41120041991004113401200d041f8403031102500711500c0100c0e440b45404180300340c4c185010341f0f034036515251101110059440c0010740b81154103038114284c8076100c50400410f181e80d40200350030304034580780080340c600316543c0c2c9035516060b054503141300c0340c0d55101050b611004d00716005c000c1c9c00c0d20307400000c48940080d400340030f05020620440381030948039a0380c5030855039240d00944180045606100400020b076072101d8484000e122500110b0600b00302003200c40b00040e20007810706840d00c0d0788880b151000d6004040e01d140040421026000c2c00e08040e0081c0d0080c1e800d2030014090749a442452401003900748115542e10112800980d84c0c00a00c1000340007014100d6a2180c2c800b40014410300700b4009140240b40c001c0e40301e41d59040100410600080c1c80d000044d400c1c1044105400e9021081e0150760142000e4402e1541c0e8824440c040b50907520081080c0c083c03140c60240480e141102e680518165100040c0d0212500a14010443c80940040c0d0041655 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 320031528 1250 320030278 320030309
    0x1e0607020604170d0f0204090e03040b2a01020d06090b240708071b050a0f050d0b04020619080402122b05090a090e0d03050c0919050405071e020601 65
    0x24241d240c0710040200140912411302080130089003d44140400f65584d164001c1401d1180e40940d11170210620302a00c01036107014138001d811045806899440d0350072200c180c900f288a50340c030701c200c0c07201031080e44001c5640310b0390303058600002c0c0501e00030440d866282541d03104a5007043c003004800f211078404420308840501c000d0b16005c1c7c0c890281180c08907014002a00001c03002680142000782d19040f1241090401c0d00b405624201503015500c6c07100c01442c00c00241d00e070030000a40792a00251a000256124000315900d0310405070818100c50000c6219800c1c0d90384604806c2c001e920850b196007000700c800407001d950308100b40e488425541d05640b004591b4080e401c0c0203c2c0c00d00315040003400c062501c000210384405c1c41d40616441e50321145903d4600c4030a02842d061080242020096403d02c94480300a03030083c111058090461600c90400007800302030140014200100240314503c0c0c2120000c10010f60011500a803107801d0500b440d2090011406a05032002c401c200c0303020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 320032778 1250 320031528 320031533
    0x12050603031b120c060910110a050c0708060c040504060b070b010b130f15020d03112703100e0d110c100e10050307020d0519140f0301081e0607020604 66
    0x980103030b940011110f101c1c1018618802501d0340c050038440307914001601180c41e100c1c020038100b10303042d00c899103480c0c6803034401130b0401c001c5420f803480341c1047e160040d2074504413024140f501c0c010740c11001151066101700802d200c00c540c01401514402e85090080d995215034111040c02001790040003c41018018030950103040080e10321010808070030b0720300540ea031241d041c0d1800c068001d902a041040100741c4041c0d010410000c9003c5145402c06c40c0148065103000b00303006440101007030000c603103550021600284800f0280e03036001000d89040940018274500103082000c0040481d0064901e10300105003d403481c4070fa00014000a0200c100d144010130622a5140b003a800c01d00c1481c00354004192030b130042004e2a03074100d48075070340e0364148500080c0c9418080c00140d410040f081005504000500c2d040010100d15400c0c1005000e01c003c800d4015400380c00f2031404243e01c0440000f5000e0320005040038682610f9085070f203400032410f07040307444180455503080540c2c00703100030400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 320034028 1250 320032778 320032807
    0x4052701150933170327030a050105090303060315190b1309030c062f0310270f0c0503060909010f020a020705040612150506010513030308071205060303 67
    0x4002d4030a548602564440f58080034210a5907031216aa48a40d043c184420418414101d24103c3d49100031030418402c40d10b4140c075000c103078076001c04c080c0b51110b03000340584003081148c000740d500c140207000e14035003c013032241d5039001114218800d11403006084c1001500040da0350040c0c42503098003903050b20400103003001d8018201c0c540d8103c0041b08181d24034000510a0f252500d10941d11284440362501307110741a95545075072101c8800c079606103c0d00e105070002e64a0340354514041299181d40c0c1d1000701e00303c409170750b901207240340d0340b200740365800c0f82059404010440c6140e00e0411106c04400c40801c21540b81481e500d020840030000b0a5031403800c20841a8030000f08130012552140a0340760b401030b0b812140804001d68000310f41070240d4581802940045c24034007800000b4440e040d1588060b403500f4681080c00340743d4410104415922800480b02030510f440340d2042140d45d40d180003062040f08650340e0000800718103070818800c5240c00380c07601910004000f541400c0e0450b41880 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 320035278 1250 320034028 320034041
    0x303070e0f0a030b04030e031b040906090c060206090f030906030106320414030c060f070c120c0603050601020129030a151b02030918090309040527011509 68
    0xa52118840251140d9592602d81c6a0007a41c4200b207034491a050500d00a4820070110f00c580f0720982101e043c0520481c00c0d44480c010f80141100c0101e006603090600c50014000c0c90303005480c420301d620703000c181c1a8000840310700500300481168444266154400d8890096510075640b00390200300400031107119540f0001c06c1c0c0342455910003c6402c21665440c9002c1d420004641c0d10350115042159044605100c2c942120941c0a011000da02e6800201c8600c9002400100044007141060a10000035540000340052404403c0c58054900340410f0740c00f4944115800070341080e00182c91944180144036400c64090241c0c81600c1c0710800024600000424407900361081d420700102081c81015200f00007601e41c0000110a000313100003032a0046c0703c0c2004415544200b000c00b4040d02c40805000303080c55108203000306034540403c0355045205d445002544a4203040c2440f1a44c00d01c10801c01c6800c0004041c40701c0913406030807042c01c4e150650b00d0800b006050360000c1140301a01c1e001074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 320036528 1250 320035278 320035307
    0x6080903070b070e03010e06070305010f080a0506010302010305100923131718040510053604030e0409150c14030103060c0302090a06030504051e06190e01020703020f190302030307 79
    0x207d221b4562924092910b1021129200081c0d1140c00410030000f1708416140a4868840a00601f151540707480b6a20b09061100070b041540d06d1000610985098881402500c0c9200d0203115030075a980018800303500451021138070391040004101c8030021007641104c0135501501c894024003411503025021f8004007101c04603880f90300d40580d025980ca20800d8810510152801c55840c24001844804540d801145049013070800307400c0006226054840354090138110300d01003d80d22881d045900d00c1010000c541c01034101105182005003140c1da405201c1800340302009101c0c1012400c595408018045400902040005001294840d00400002c038880d08015140034240d1003c102034a003136621010001c1ea88206200412000380700740d201910340320b2290403a00c1d614440690700e81d440a09101034020791902464102d0302c2613044030006581c510021511490030381000780d11040d280d1010207082c0a9104004a4034540303c00c551038030b68040c1d0095040d640d42030010750300c4c45103003000d6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 320037778 1250 320036528 320036531
    0x305011d071b0203031608040f08280c05100518010905010e040506240a0908010911060c0c1f12090309061d0405190509070317090a090609050106080903070b070e0301 73
    0x10303480000c4010445404c500c9161540d075541d292109019004c243c40c5c1243e0081e81060500d50b160b852030040c0401e0030054bd00c9404407072422417400661000e4035900880e04041e00d41e0408600942240240c0307044844212020803008404004658205241c02214045a00c07581c98101505060303102c585d104401802c26150362515205105680e85030402102003c2000203050b41456888070f40034004041020083c03001006c5a075540d03038a414103110090140402080d0804198001c00a041001c03001030300060f02d04600f03c0c5440d44000780d000385040418900c40956009849504c6003400058043d42e0303030341103581880790480d80d10014003a1083c55910314108407010359240c0c419680100300d42100f4004e40c07004100201c0645800428581154000400801c08180e108042080000304002d00f15550800c0c140001c0154805802c0144228904040804c40805551095040c0d1b0f00c6a291f80d0425520791801e543e8070310412238001c0042c20000f000ca07190b079018801400341114010700 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 320039028 1250 320037778 320037787
    0xa120b0303160c1a03040b040303020d060b0421170f250b0c1912110705240c070803151002010902010807020d051204050712030305011d071b020303 65
    0x41d1031a0080c4410201860118031504200b00e400d15016004281c0080450000004190007030414040144013400c3c0340c10081c00903003094840da044407910601140c0400c2002d4503003002500300c0d00603000300e9015016594203203a489c252640c1e01c2a080c1da000c200c41441c0090070b205c0700781c00d4014a04100c01c04c2c0c2e0500898009404810042100e540c0d06036407800191401c0c20500183e15020307040b02c0b4019400c00c0030b100300b03c3d440d0321201c980780120b060012141282204050013054440e46612026002107074100c108400460325202c20f00c51840e080c009240c200d843c160251000755a00d400312181004840006109038001d9070b4044180540e251201d041c0d0004543d45031090316a44d00140d5580d5491001c5603004021305800c103045100074039980d101c50780e001d440c078401c0d00b1202500c1d035a20300001d1b081040030002e03000505038030200702140408501d405006490b080c092220000c1590540002d106c2c90140480c0c410000f55983c4854400140001c40c1d140e48070640a80e0036000400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 320040278 1250 320039028 320039051
    0x6090d080d02070507060f1d150409060f06210e03040504050901020309070b03060a0302010305040f0501020c0f060c070305070b04060f050711060a060302012a0b071e02060106050a12 80
    0x280904040c80101c0d10141c0e950302189049070401106803c440c0c00c2c4802a0686000f19520021070203140003032102d40440074061100082c41e0001c001c2c41c40326904800a8082840c0e0a00d80202045840040e08603094030b450708410307a03111308000d10070504210307030011a003036007035070381c0c02900e2920011030540e81ba140d01c4001140c1601e0080300d028465039000010b000840381d04021501c000e0200103090350442c1022400102584034610020b81059202d1b404601441503403180d500000b90720030000c6644610111405841e851a000c0003030302d5000e28000104402c0e81c240403240f4042e0b01d60741c1e85141140c0740d030301c12881c03480107803007a9296640c0300c001c41044c1207a4802d2a015a0715521241c03100d600d00ba03502c601c1c0c07043c000c281046541c10320804000507600180f00c50140700103501d5408504500001c021488043c502e4040e07c50600d010501c4106504200019100c00c4001001c210703080314410142e90707491b028480c110000c0c80400603070040c140b0a00c55101e030309004003000716091741050f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 320041528 1250 320040278 320040293
    0x720030d0e190b0a0b120a1a010602030405060d0f02130807050a21140a060504030c02011403070f05031803120601031404050303011208090910150e0d0206090d 70
    0x5042114080d5036400703110440034104514852042030307400c4120503907460380d641c00d900c1c2c601502403080c05440346895105c0b90745101d03078a0599032981c01180c1c11002c0300e003443c1403004410382c420000d8a40d910008030380c451001c01100c0603900e02900d02d030715058080c0040070084c0300321000901300d9503080c0f00c452001510101e209009000c440001e040090402c1d00300826840759911034802120341c4003000c4e84031811741001144180e04003034030803580d0241109060a155000f80e009104514142c20042010382000000d40760354000e0340c95066540c01061207000074070003520070b4000304071810505451030b0312a00007181c4c03140c405840c0c4080310001c00412071440e007201c0c02125224030500100708182d641440b801d040c0385031050000c4242c9c01d00b5115a41c803480107000d40e0400502080881c000d100350300c0b0031103083c40d201a00c0c0d910750b4508444100006007542c000d4805003083c060314510794521664070b075500540000c0c00c414100131942e08100c4641c0c0b0840c0000c1c3c11500e020880404201c28 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 320042778 1250 320041528 320041537
    0x12030605061306020f0705030c040e01090803040b250c02090c0405030a05070e0703020f27060d09030206070e030d080907080316030908031c180206030a020c0f0106060206072003 78
    0x803840c40100d524203004002c0c1c180b617000401c218059121030403c001981c2c000441101b11102658001110504413480c2400b618504801510600d800814001040350b03a0712030f18840d205034441c0e0700042400686e00c840401e003040d4910000741030150326001501c1d00c404a00d40000d00c80c03015a14003503459000c641814050703241562560001581089000c80d00782096074080828a003c600d46090500852000e010300c5040320340c4e42c103540304141c0898200c80c0c00000c290030300400b040e440d46540c100a1018042540007203005025803000300300440e0060b0f83d45031401000030050905a4486c50b0115104400106200d0040c4a510300005d19008180000d050180c00d9030b00c845683c070424100580b0841807a0b210080561003003201d002c894905001c45110980241c502007607480c1f8040080040d0891003101940c4024000207115010a031a0b00401300f0340c0070307482034548043e4496034503402c0301c446100b8840503070880300000311858030812034200039a1960304000b4843c3c0382480701510390b400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 320044028 1250 320042778 320042797
    0x230301110a140705151003021804110406030c06050901051306020f06131208090f0106082103060f0d0206210106031b0c030f091211090903070503071203060506 70
    0x103200410194002001100d07101d0642d00c0b580b40803920365a050307544484117080710b40105402d01281804032200001001550010411020009003005d9040d1512041c3c50031a001400080010030505003800360303004a80d0000700e0705a4851501c0c4041d41c56034081f2046504000c2c0800419200c01d09040d40800503000c19802408030204000080345022009031102c40078810007003401000940031070108050f01081d1400403401d44400084500d481a10460b2580d15401d01402160390301c00044c2d00c1c00741d6200d80d402150301e40c0203d0008012031105441d40e82d080b540458011189080010407242e280344050804d43c54841c0c6901440300b82003180400100a030203000040010b0b580c1805008955184030000c4802d9039480e0f40050325080d24607030300405100880c25040c1c1014001c0d000c07680280244503d000c5c01e03210a02c0d202c44807142c0149a01c0c400c4120b03c0204044840c00010394102035441001107184c0801030b00c030318507241c1c44410a00e0400d500c40c01d000c90b494580364090710200c0d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 320045278 1250 320044028 320044061
    0x1a0705040e090a050706020f0318120f0606031207050a11010c0c03060902030615241b0a0c08060712020d0f1a030601080d270f030507080105071404230301 68
    0x2883c41e040d0300f0100254806da085511481e108400440080119407501d05042c9528424211800106d0366110603010240c03014042d03900c04140e0381b000807035900d205007400c5081d0342058204050b103030b840d4060508040c1c600d500204415000895600c920700043c081410144010800f40e030352044c0115464108079051501d5603d040d04508040103242e401003100039441505044000c0807032482d00d04592039080c46107080c46180401d401c1c050440300c00e0301c4207030400001d501442020650795a5250401c0310341241c0d00c00009a6280040f4006000300701c2c0e640d8991100c0f0b8071540c18000303504024038400c00304ea46d1b00d207080f00c82181486040400c070400007a200c401c0c2d441108140c10008140e10038040c0b5040006240a03242e80300e54040310800c071601410300d9000d4032041850342c024194001c3d0b0810021408040103100c00040c50034200ca030b6100c000e21055070b803010300315450403c0400081c07110800380418044040202401c1068a1450300110f038210841ca00017400d660700d00c5618a50304 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 320046528 1250 320045278 320045293
    0x72a12180509011406180301050702071706010807051005040b0a080601030b12030901050f13030b100b04300203070609080115081902012102030709121a0705040e09 72
    0x2101800200e0041c0310480780c1c101c103907240000e010722000301559014414940010089401604040580480c07540039008000394542060040d41c1c0d004e0b18054090342c0c9034101040d0b801c0c804c2c0010010306035403440c005448401c0c81e00e4180a02006010143c4091010a0002059184d108409800b1100d03ea40d00c84003a803c042002404903030900a540340a028a20b180c1e2044444c00002c48010401c01c3c070303046d541c0c0c00d40801d085186001c0c04d06064829425000004140107041c1e42442c0214002c801320313072032242d54641148051041d482003503903174840b03c012034005c40d2803240700c01c9140c0318407010300c0d41c084120750000e41450007941091000c03403400c150601200302c09120780045d610b58141e00074942820041c0701550b031000d003d845003030304100406440440e4402c01d544185221286105881e01c0c84100c8260080d400440d09140050040039002441f0040d40405244c2e5a4111181c0c02c00c031518111082c2c0c44001c02004482408000c1000080e20b40f404c85c282440785003110080c0100307 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 320047778 1250 320046528 320046557
    0xf09110f030a050a120305070c12140705070306020408060c0c0601050f1807031508070e040b1e010b03070e01170a0905010b0a080304051503060a0b0c0a080a0203130e072a12 76
    0x1c87d04007070900020044907180c18800640d0050103180b5001a03030500d43d003215402c07007d0906520440c240100940900c0900008010007034014005407424141611219554101c3d49041805070580c0f50b45140d00590041099080c10751803c06c4401010300100c1c2245159081501c00c64010f4039030300c001a81d54105120302c0d500001c00e24015100079409800c07030610b0300c00202200700020b003002d044071500303002050300c14814100c0707000d00c00580010f0f15010340c0c0d1107100e01e095030012500d5001041d00320f00400c81643c41821010030045503200c030031403075460f620302d01002030070101070880761503582d4030004285650301020b600007480c44000175582c1720b081806003d588904092480c001000034020311045941c1c003041c20040d20050341e60141c85518100481d850410610780142c410b4800040c200203a0354048001c2a280c1d0059050050040d501c0c1003030890b01104807a860002000042c001ea203d500080c14114411040110607c9104081c0c0314482c244000041d040081810b40200c2c608 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 320049028 1250 320047778 320047781
    0x807080c0c07090203090304030501091b1a07060e0a024501061809020301180515011e140307030501060f05090307061b170a030f09110f030a050a1203 66
    0xa000c11444041410640400e901603601c2c0e515000e10390f0116000700008420510030402d440045030440e00a214102650428071070104072001d484c2e502c044100b070302158a80c0c2544182201c0a04810410728150694484100400000c54001361038010802e9801c00741c1c1d00c0c0c0100300e4120302c1d40824400058102c00c24003101302d940c000800366011030343d00c0c03542054008001d074a0444000d03080c111900b40341d200c101c0c0e2501e5929000b080c411407000c000429403242c0304012400d2041c070454204100e840d080507104070000310354006800540c0080100300820401c948180c1d2a8a86007040040c0441c4182e00382c03a83c0e00100ca81c000025901e4004009090340034807010030b403030b00c0d506003c0d03e1701e0b0004020946654480c0990810b016484c0da2090400301003a03103895a02d608a0b60340c44c1d03021501d0b180000d4541c440760001002070f0802d20900741c0081c0034440c0070140c661140c00c06006110110901818001024840380d050080c62280300124000780150249075115030000186070466100260 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 320050278 1250 320049028 320049031
    0x1e020c0d020a0203070b03091f0b2d060d020904090822180504031707020a060c170a180f1a0c0306010c111f02030c06060108060319150903080708 64
    0x82107501c1040c40c0303405a100400d041c401d5a0200007880d07500c1d561480010314001c150200240c20b00702750710b03003090030304510b41c003003442c224040720301c94041c1150204400103801c599109210110350801580c4052030000014100002220405400c0c0b081c1c800004044555140050303561500004004415800c41390241c06c41007904904401040d0810f2018031610300d059154404030f139651000b103005d140c0640049008503594103a921000d01c1c0000000391a010161000c07107500e800c080008810500844011156080c015103100d01d0b9070350300c807425002e8082c10340070602100100c1c2690740072034114103050b600e241c02007802c0c035178040399030038041211440180384e65000e2206000784410b070780c0d02290b00c082d4542c0080351286101d5068001480303590302503096140700d018000c3d40080042d00400540114054207080c0c44c0141d640303170010f4420020854032190b060f00803500b07040c2100320b0f000d6580c440e035010355074511044610110240441d90348110540c0450943c004024a00d94480804c6 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 320051528 1250 320050278 320050303
    0x18010e0f1003080904023106140d090206070c23030a080a11150112050c0301150b030705210405061302010f0c0213090812010b0a020705010c061e020c 66
    0x3800e00d807850000e01514810700000f48030020000e5501803a580e103805803525500d04411410440c2082d10301f4840354040170b0140300c0c00440d00100055014040d42960242100540c076043c0340502c0125064000e00501d07004980c071640034030200700030138900382d60324001e400b07555009201e42404400c00440c2030040e4110364071030b900042a4400144242046d103948040030300340440340840c0755007000d080050700300310440490110f400006e9011a001c000345191401801139640ca000030005045c00da030000ca40b040f160340242c080402400d801c24004540c800d24170320b4440d050104019098010281d0b000389001081700c0c1400b4001403200c1840810340010100015401d5050039034000783c00341d400d508005050006e05410082591102c0e50000080c0448581c10880c05401d460b009503a41c102d0464880b842c000700340046207400581c42240c80e852440c2c0c009201d91403814004407401101e4000448800e038035070805010702150900d000d1070041c4003060242c1c468000c600400e281101c0300234079 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 320052778 1250 320051528 320051551
    0x501030c090c0f0e06090d030305100504050606030103022b050c0109151e110609061806040b01090f060909060c080703060f090c1107080c0108070c12030504050c18010e 74
    0x94070760641e0400310110003c2c030740d030820041d41c0046a000407046d02452082d140c1000845811200b01503050b80701030f2040c0f0702405291551916035050104465044403e240c201d40104014070152520307090000f505024100c40550045280302e408810301d286180807907041e8411840401551703000b280c0325000e41004066030b81d80b001c51403802010850800d00004041807184170a80b02e8a1140c40a10f444418800c115402420894a0144e403094101d511f40c065049521100003d03602c04a40c2e5409550818210251642088140d070020f00480c8598200f20f56214000a03004001d4000c280e9142d00400b03001840c1084003c01811603e4000c00c1d0104161412100784403403541541104152a0300c05800a0716100b80d810603a101482c1940c14401d030f100c0ca00000810346000074006404c008281d94840b5540c0b510718095940413500c0c0302c000c5c5a02084248000018800d41c003481c0d0180c00348003241d44008080c00451960408052010703078114040c001440040c0d4a086242c0d0070001c041035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 320054028 1250 320052778 320052791
    0xa020307050304120203090a0b190c05030a050919270203010513091703040b010602240f071202030c12090c030a02060706060902040b0415031b200601090501030c09 72
    0x18010218070000f80014101c00414081d0001244200191441c01c1c0e0098410400340791180c6140da040d82021282c0b00e0201800800c40080c18415118501050381c424021800c03c0190141600d090700840011074009a0700c1e0813032200c522855514900910070402030809030510703505045030b800c0c003050600a031680100300400140d2101c2415203188102c65000140414944c9040405c602e0180054900d40e5008402d01017481070b840140c6049484030b8007160030b141c400c0d14148421b140b800b03542a44041c80c240008076846607a411442d8001d01030319148840d141440c002100701e810075104403c003d030002c00d9204a001001c1400340d00404044018040b011070300c40083c1d41c4144000000f0300031304001c59200100b03e66074010201030302500c04150344441c1c403403400404d0b0360003510030890302e030171101c400188150003440340858000411141c0b80c0c610b5001c2005a5015030001488500d00020841c80c240050003400b946010300310042011806515504116010351900c3c0c02c0464018074244 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 320055278 1250 320054028 320054041
    0x60102060f06010c110d03030c0815010c06050405191209050d0803040305090607060c08160c0b07030e0a0c0f030506061905090a060b0313020901080f0703080d18050601030b0a0203 79
    0x3801c96a11050074030f070520680c580e9150040d603144211181c035802c00c01d40d05c1003100b0150580c020001c1c0c0c100c190346003003059990009159140794001815808a01c110170b090010450f2904960350107401841201c015260303d400e442c003058203004064403524114036808480a50181400008000840c0c14100ca60b800c0c0d11020a00d11010b0304c000c081c4030340080d1880305a2690070590f42403a4114600300411425114050b042a80803502c42c42d0080c3da44072400d0b140c9000e40318003443c59405c0a07081c101641c03000310542c01004200380c030403154460300c0707030880c0002d103040c8040d0050080c2c41c0f08541290b195290082ca4944054100c84c07007414440e040703441002500300d120301211070841d200e00c843c4d120007e1071001052250032400b00d144001080210107288928540c612031303c2a0381000013681c0c5e0b48181d40c2c0325021002d036403031550800349003040456070f6040503107944034000b40001158006001280141d44a81c2d00880d4503400140040081c000c001d00c41c0c0768481d04c0803074194510718044 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 320056528 1250 320055278 320055301
    0x80f18120d1e031e0c03050a0203041e0c0b07050102040509220f0215071410110f070c05031905010e280510050c090f0a031101050304141f0506010206 66
    0x1454010300d42d01d102802c41e4865000b01c0c3d1900d2583c61500c064809600c224405801200e0001300800e0405002c54100c20742c0d03200f220303c0b403a0000e1801e1302c080ca2601580513510b900d040b05840c1c1c149000008604c920b140d04c000c0034054400c0f000113942d40d181c4000d10005000041c00f00c411038081e1800b8a141c0c40c101803000341d0f4950321481c05d401400305c503c0025480340030b00108240d02d20000c44c0780020441202179160088070418100e603060341e6403403109025901d10050103000b150047c00b0210b00000ac4201400502d4481ca4001300d103141c03940c0205e850301280d88102d20072100c1441140701400001c0c0304001300640c84038042c0c07081801401c00302404008540c2000c841e400c0ca010200c051200c28416149190302d40d900074072242c10001c80701a49034108030781d178901c11503041803018414503024800404807944051032400e040c12032801580d150308024010b440b650001c0d04050013114040c000d803d44030074100c18020f894080c03500f546080340c44c004c00c4141598055020300c80d40c01001c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 320057778 1250 320056528 320056547
    0xa15060f1d06070b07020a08072f01120b1201090b06090f09060c03040f060c0e101106010509061c051b040c08061504050411040501080705160807080f18120d 69
    0x1000c4007008584420104901e007c3c1c80d080c01170b0003228081356150400c1801d00b0300f0241d1480404405c0c0303950141c240040241c00c0044400350108207020442c003102d03141a004450100d41c01003d45003d810596940d50070b580d0010030440309026400200b0200749811001740d500059100341d5200e80380741450040782c1d200400780104e81c0c0030700c002c0f0014041200112405c582681d001d0014403080600d041d02500000c42105c0b0a40b24040e4551b06030500c0e40b0510221800b40c080c04020101c0c0d920300014005014406402035401401c030f4050340801c050302d00010b540d0f4601c184000e2020a0319501c54008800e4840005d91003541401441e00450f584003401a402c41c104440b0104401071503003034540d5a01c280e9004070f400609000c007190320b1140b080080d00441d0020b0300e0b5119039998400088900d40b1a000c1c2290f480500300b4480404200c0c2c06024044007403140030580d24011000c0c084020b2034101d00b2618452048009102d00d013410031142c1c0403488140100242000185c41c5030180c000d184 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 320059028 1250 320057778 320057783
    0x70305090a0f0605041e050f06090f0705040504050a080406050d060f06050a2a0b090c10091502071701020306040e030a0e04021602090f150f180a15060f1d0607 70
    0x201c1d07a0206051005040321380501d81c00c82504003031b02000d9490b01036112150071050064600404000030300c55071000c01d1400c42210303072801800c0083e00740340410004000c081c1c41900d00344140c10f8102c002510190052014200036107845890f070202c0708101c010385071550041c01c0f840844e07800030400260848155071302c61241d81000520038181411040101c03018461840c4840030785138048082c800b50345040b501484c116820744100c092404c09126040900d03602c414001800403400300720001d148094120400890320541e24007660340c0d4005818007140f00d040007160f950000c20b00c61503143c14403440c544600f809000d541013024421024040500d0b060708640260380000d00d098941c0320401040307600350750040c030b40f040500f0144910030050604403115048282003d80c035643c40c0c87c2c041c00801d0440c000900e5060391461500100100e07190203402c0c03581168642d421202140150800e00c409048142c2d2450031130240104020b20340d09084520001c81502c01c4142103803511010225440c1c180c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 320060278 1250 320059028 320059031
    0x80c06070b2a0405040609090c0b1605100e0d02070303271d04020111150103060b0627010207060305010e040602070516120b0603150a050711060f070305090a0f06 71
    0x10307200c0b0280e04116110610b9410b01c0b444150850301e40c114444054003d1300d609580400c0340548544241013140d200040141c1110280740040028686840040020b2804c0f0214508005255900c040c0b0f800c851000b03844270b1517180c5980304040b4a04102400961116200404a0607e181c038081c2c032030380051058040703844482ca4001c0c0b501600c07446c0c7c0c1004012403c101d0740c3c1c00400c6540e400d044401950200d0024404c0034201c07084160001c1c840014200e031a82c0c00d001646540d88401c02032240846142d000700040c401a01120001203414004803030601081010000300720009050124a402c10024940b80500502030241d00d24141c9174025449a070050740d80030305090042ca0b0004240c8100301d00c0300322840108405000600032000944241408a8103444841c105a1910510520b11031210700150000e08407a61980141b50405d41904024038046064070400c1c0c1000c40490321322214200030424842c415505100d4990301c81c00c02c0c0e015040882250f43d400298103034a00c8082d090a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 320061528 1250 320060278 320060281
    0x60c03331220010c03080c1e03040309140d031706060c07090e1e0a15060506071b050108040b0a021305040608010902030106140f060f160308090601080c06070b 70
    0x5005a45240000d09a00d0380307540100300341c81c6082401861262040c400d8518044500051540200c20510070154152907400840c2e1b540500080b940d0030507162441d40034100212555003c0c007207002540294020395130340d0b540e542004000105450040405030050070f44403242c8020a5002c005c500d1142d00e078590310500c81e160b0a0018049000d80040f41040d4080e01000041004060344803068144e8000c0035108907441004030780c03001c01c44405080310b168014074407980c0000d1803884850303800c09851000244168032100800c101d0b400c681000c071f80001800c107a590070800005220710080c1024a082015450640d40760464210027070300c50181e994002c6083c1c4520407040340c40e00040c1401400c10405150350f0314034180600385219040e4000d52806801081e082001d03c01d0742c0382060003400801c1c140c1901810300c1050f52104502c0c21100d0307000d0100c0c501702c00241c100186203900954035180103050403a8101d08207401a405626658000049001240c486e07000340c40c0304940180035441c05 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 320062778 1250 320061528 320061611
    0x114130e0406020c030301060c1b15050a1e020106030308090304061707030906140a051f060e030f0106031103060709060e010c110a080f0d0809100506030a1707060c03 73
    0x82e0084c4020208940004000803651030340c86907160310b8560041e0701d012034031550108241c0b420b10490181c4205c0341103500880b41c149000b603000740034400451601a140040b090300100742e01d40a1450341006075154041082030503800700c3d1554100c10500040d43c41c091078110302030320030f062a48081c1c03500c80c2c1040000d2101401b03640101c050307540040d001c0c00704c5101e61911125603103044401c500f01d1031030140461401005030400182c055050000345035814146102550f42c40030b0382e014241e0500c80d4100d001034241c1c0a00030840203510448260500102c1c00c8201810300d900144174204000e401e103020404641d000d04004c0390300d0f500f0f0070580c01441ca282001d1803031a1480c0140343c2c02400441e40003425400004101c000b0b6401030381a00c0f018581510201d4603440207507184d50903030344090072286422003203070300550f00060000d0841b0140b660301d50b5102450a6107801128100c4008241481800207078000d07921284e21038503081051007601d0414040704001d1541440682c003524500144 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 320064028 1250 320062778 320062781
    0x509040c030b0319082502011b051f020c0708060a06050306360105090604050705031518010b03100b0102060105040915091403070503071103190308090106030c03110114130e0406 78
    0xb50601981e111046d04082280440d280d1002a412400600d9283e00612004010701d40e54440562010107000d6600e00c1d080e07040c584810501d041c003101036080115042c1c41c1001c1040031700400320407007c0e1409103410346015080720719540c4400d009801050402901c5507007018200301800d10500c407400c2040200030300184501c2c00801c0b0b0b900310340c40e00040c40884200003d40905c80d42c418011961a0340e00c0d0024140c3703402c4080003510880c019403020482d60311080c619012040d45000000030003010400c0020b1400d105082132503503c80e034480c0070b02d2295905100c0280500003c0e0780500621030796959006420203581071690909550f42507110401803410b007a0b501962062003100e03240c43c0641401a10b0790721104003180d6514403161031402d1030401040d910148001a69550211849610240e0f09510014840702155683d1400440082c0360034000760051030183d484401d4003c00240090a6920507809203131201d40240105034050400c40d180009450021008640ea501c403441c1890 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 320065278 1250 320064028 320064037
    0x80a0e0a0c06020312060a061409120a0305031e0609060105070c0812040914011a0c070503030a030203010612091205130e040803040b0705030708011208070b070509040c030b031908 79
    0x801d520600c0000041c2143e001000d03103420100072681240640302d490401c8040c0072980701d2000800c030485042701902a618015149045002e803610505242d21081542494041c280840c081140032051000031207600110002082e8545a10112414080c000406898004020904100000802e0001c0004404d1184002d0061000301c40c10040b5841c002c01c1160068041c4036401e40c0b90681011940c11a500014100d52040c000c08181a00000740f40000e6031014450448a118923107001466860400043c131600707106582c0140c8a50410600401d00725420301100301040c01c100089020039401200c1100f103c00c2820041d40d1101010303207084180c0d180b42e0110f00b01c44000400c010034020074800643c400ca10800c640943c603038502c2030913503450005641801c0020301031001031102e8aa045217010525000301944c606080059480f000d4103401202c0c480c0000d103021480d062941440d0240c07281c0c56410b41401d0108120080103e85e445070311403440c0c08940a10342d80340042c011520105c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 320066528 1250 320065278 320065283
    0x911090910030b0f0f0f1f080c040b090c041a130e0604050901051b130b190f02031216050c030703030903021b010c1106160609150501080604020906220e0c040c080a0e0a 74
    0x1f02d02540e150402600d41c0d016441c418092410400d9440c0d403483e200c40040d200d006a440c415040c24205031015419040305070804000300c404004111030000b210241c00014913036000308072030741d1504405200c1682c2c0003070003040c030580c18242030064030490804111340044003608400d032034810705c55050806001541c40003201c08000200c00c88880200c10000e05e80d0320b0a511001006400d46004994a220301e030301c605040e034a50b1020490030250055031034480c000c00e181260805070010003150566114000440200f552002c0702e00400d90140310f075040102e16803464010b694201400a800c003d80043d00031320240e204074070596180d680d0b405540d180c140400024482c4806450a10001c044094003510115450100d9040701c2d8403d0041c541a100d42c480504055195039080c0050020302524081d07001e580240b1110b00d400d0034050001d2103242c04c12020848043c0c54880f1410b05220281c140d0003141000000b0803032a41004400d42c1165500c040028004080004d01d4140b25455500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 320067778 1250 320066528 320066581
    0x60e0409020418111002120a1101150e090606010809192a06140403030c0f02031005100905010503010e031204030908060412030c0201060305070911090910030b0f0f0f 73
    0x29810f0040000303480d00c6444c3c042d03411001c1544020f03001e070303a00c5e100142c1c0d21000700c2080040040c12481422198010810113002003003100d031399175008001d400d403030300308503c24201803082003907042c02000f04682000782820414002c0c14900301e5540c840140b41c81801e80340031405c94143c1009021120804d2042844003621002500d80f40c00c034008015a01c00c0500203240c00d0520036802030b80314222011650b06444400c0c0b5510aa0b07035180480c9503c00c0c0030703a810b00410113141402c800c14012148a0540809500c40d1241804031030303405c444041e0003460007a8940542280b0f040710000848802c2d00706002c404080c0c0d500d0f86000c892081d0203801100700c1d405500148000c016aa60301586002d0098070184003802151001301c2c2251400e02c0042c00710f40c800c40b01000b4008007580440c0007a41c1c1da02c00c031890280a02d01084c2070400590300b808003810340440030400c0c0880c1000c5c041c0c0002410004155070b0501e407256950898024048250003454107001c03e0801c00d004440105039a402481d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 320069028 1250 320067778 320067821
    0xf040c1b0c03021224060108130503190f0f02010204030b01032d200d02010f030e12040e01030204060501051c4a0a0c0e15090906041b060e04090204 65
    0x20080d4407034100d417050710320011440310000100e40180c5625403107540e041e035401406946894020b00f0803185458140d44902080052401c054104890a10810780f1601e80440160319244001c0c02088003140f0701045910511042c000920403030360543c11a600034803502c117455041a554580c200300c0c030f000303c2812010982a882007200c410105818901c004506a00d041d8810f0300b44102c076040150000c0c001505200b010741071074082d600180078091400c1c01c9a081500e80703a56030790a41d100381c2202031825a040c004008515041c0204c001400003072030a241402008244400c0d18040300d180800100d07180c8000d0782c02d0b03030304459030754815400740a0304200c0c1481c060001404118660701d47d0b042104d00448288150344005001c01e03d0b141c1c00b420b68803102e4034200304261206006000d03104544001c00105000b075946411082c0241e042d003018103d1400d01d8074000711000c01d10607000040300e5228204010b0340760800024884c403202540c0228042e0094070000780205006150b501e0380c2a003102 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 320070278 1250 320069028 320069059
    0x140403030914060a020a030f0e06040e0901050a0207050d0c031b0602030714036f09060915040e0304030314161401090501110304020f040c1b0c0302 65
    0x4802214001d25040c2c502c003218034284101403080c03801010160b48041030502c00648100d1031201c034460310f0729105403480d03512000182554400d07841803400c03d4040d000d01c0030b0f00c0310030b2142542116078014110301d412442d0f604d40b40c6800107400d0071010702c10074000c0001454015050740c6060f1000f03442d1071503203203004d103441b8000703401c142c0d01100090464030910b40ea21040c201107a028101e480c410481e4028140500a2142280082203180d190001008200c4c0b5598030100b600003683ca06030f9030140980c281040e0750716020b01102100601c1074285490450f161000c26070307044102a511121303581e580000f144004020b4522450f0418900b41058a00340b03404405001564070980d00ca82901844c629010010f000b0f400303820131851405a10000000c02c440d2141001011290005c071307403c1880d452310340c21180784108200c14403600200300001c40c50807004441307102034112801c00c29148142002000c0e218a4a000c0c414001100510310500020560705402182d004241d98074a450b441c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 320071528 1250 320070278 320070287
    0x70602070302100506060d022d0901020d050403080d0e0309191401030b090630070512010e28060f0c1106090c090705090d0b010602061e0103110114040303 68
    0x3081035005004420440c401030005010b0300e0f0141c80020509810204100c010400a6204090b03401c5400600108156005090880c0800c101040c1202a48441180b40068101842d880c259420002c0070041400041c4a800c25038001d480e10307480c0010000c0d01c40d50141d24610940901c1d40c2d005d41900510901c00080108580c20303a09102c00030b0110816400041d020350f070564030455402001d1000003000340c18000400383c1c400e03c51300240d102c0c199011141c0b2400c1c102b41040300f01c0729003001c1414025402c3c01c040b900a039400a00081102d520740f40c0c2c0036600d401260969807518014030f200e0780e03540d0700100840200e00d07800503410070810000c042d0030300003041c0b40c0174000b0109402035020960a100802c40341d1150310400c3c041c00e0425040410810031f40382c0202108240041407090010607151420101d03140d40c82158070500035410b24901a1800a00400c0c000410701c5c51142903084d055400d0700344c2c2c1126880009078040581000060702d14138006881c0d105405c802080000906502 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 320072778 1250 320071528 320071537
    0x203180a0c0311040608030f0a0203121003060b120a020111160b09040c020c01020a0305031012080a021e150903070b090304140d12050c0f010507031e150b0c12070602 73
    0xa86070010f200b4030640d040c04142c4890307108181d290b070400d0100c140d5010060300101100c04051065915049861404e0000340800317580948880514140c14010855607100e2090031890450744041c952075400640c1e692001d40190090400007021045e042291040004403540680501c42d840b0722510741110031540c0c0c02900e007492040d0b0a110102c2d52035400450b40c0e107503210045c1e01818800b00c039620f095801340c1c0003410b00f100350b0f40015400942070320347d40c00c04082c880c42209420b94a00c20b1100007403425569182c0c010072010f00b02e4098291100025080c0c254901c1c0d526034186039910403034030f5030450280b401d01a0140514400700214140040000d005490070340c0b51810010301c01c1018010040b0700c0303840041c21200c0940c0c04500340c071700803406804c4081c6080110707401404202e04042c00c2d01d100781c500b440800c2d111006540448041c003800110003000d0320041098056007600c5028900c801c6c0304076a0000d0002620105030b0b4402c9c4800c81240603006011075480d00d4034504140203500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 320074028 1250 320072778 320072783
    0x100c050d02011a240307021002040314010b010806030d26040b010303091505160204290a0519060f050408010501061214090601031403090315150607150203180a0c03 72
    0x200c030101d9400c0c40c9840201c041d40f44070710b02e10640c2c0304003210130811640e60000d01030b041036100c1d20110200140c110b0008002a52040030442c0c1e00d0110f2120b03003400d41e10080000c6040c00b03042020000c0ca600c0018565658003420701d820703151541c0850035101d9400c0711601e00c080040c0b80070f04200c140421a8805412240700b6035810041e1a681c40c030009224540da64040009801040000d5205010143d60780c030b2503000820000d501c040903142e1201008a03906040014444898100e92134504514824014030055030284040036299880a001503e80d020748003d000905604100840c8240d094034040c00c1e20030020821540c40314000b03880002c491500320141c038241082d45869074001d85150b4090304608008009503421690784e850a0002041800c40300d200c18131001c90983d0702002000030400000170701e1106420650780040300345000c1c1c4070b6179010f82c004110085c00a00e2a080c01050044014401a126210305503280700e40095001c10311030522035002d10205203d05400d961085a2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 320075278 1250 320074028 320074061
    0x110d0207050d020d0507030509090411090a0b0103110a0207180b0604030b01091a032d0706050d06082409010609020c0c04050105030706050927130b0105030304030c05100c050d0201 79
    0x20013610080301c042c0300e078400040001c0c200340590f01c5642085012180c001d4401c000100303001d0040d07008208003503802c846010300305840c0c2102c04c0c06540c16100d0082d054070f21058551821205000180d611031041c4120300801c00700410080b510001a03025070207410004010b580c0c0d544e40c9040c280c01c444000c0c00f1f5445620310b0080f007285102d9045030303910100403000d000ba0413524060700c1c0e205220500700c013002c8120f00718806861841801070149401030003158440719180c0c210801a9400c845160300315200076400390155a00071158100030140321400008072030103c0e6155102071317000d801e0a0741700341c070554004140c4000c50b02020800b007052143c107487c1049103a80c0d4100b0940c1c1c480d014401c480100d8410046002c240c04c0c41a03078003c201c03002042000d101003613028180c010010864410302c600e04c02d200070108015a8071456401088114021410903040d600c800c01105c0d42d03441828850802040360300010340c000d0b03824036650303070b040026543c0100000b600680a0501c901c011000070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 320076528 1250 320075278 320075293
    0x12010602072103030c02010b030102130e010509041718040911130b010e1225030b0108010605060414030a0605011413050408070b220c0e0c0307020a06110d0207050d02 73
    0x4039001c88402d25128040b4400a00365191600c095004080030001c4804654039030b05c441c08191401d0000b019500c011000e10a01d1500c1c100e114008048181c004c180300d02c1305407041c000414035880c414034030402850b16103945e880401340c6c1d0079980e00098039065041400d2000c1607081c41a1a5625418180d00380d46403034803d142011008102d440560b0b0b01400b103940c50304140b0490a21340040214102200d04560100304074140703821410110010301d00b0340a0400c00c0500410034000e0301c0e00d00500c2e544000b80306c62410440000d04030700481c02100d81c0441484800a020360f000c008425113035030003a40420a070f584031001c12680031200c3d09035034005c012124052503c11a688111445550810b0341d40e420201241e8a009807804080e190301c0384aa03a604400d00304400c520b07100c945843c400c04030310300000d2a140d1600149000108121181c2c0740c203004003c00340d500817400c0c00255a1004000403650384039032244115000c0c40700c44080340c13803000c6440b00400000244100b0b80440903022900d06 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 320077778 1250 320076528 320076539
    0x1d10020315030a0321021b0a0501140906070c030306031e17040f170106030b15090f130b070302160303061404020702010c08070602041a090f060a090b18061201060207 73
    0x228080c43c40e000300091404103000000402c8000741c00380c0303054811005407502010ba8442c02d054070107081040e92640010040c6402c21000f4070500003452441c5d603450405180c200c05203505c0303803001800f01c03040c404801400402c052199010401450f400352000d070009005030421040c0b20181041100c0307280b840303030514418041d2002940c084980d00c0d0710350001301d805d200704c940828a4401c1030540540d03d451010001400110791140304a010000e440d0b208000101003202000d406070559102101c0c83c400c1c0711011115955903403450380c10008481091f12100f104800074400c4006548409054412100415515411900c01c032034a00529124401d1ba0340c003004100d11501c0030080c003041202070310302c000403c4800030704600c900400c001801d0641c0c2c1d001c0014403c4a2604c40c080c58880001c62602d40e00d0030380309400000b45c0540d09903041c0b8058080280c0880c05a001b0320b90f04540219010b000101280c1038172408050140203d5281c5205e65072020302400c082c06450090f001f160404291b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 320079028 1250 320077778 320077783
    0x11a04020c0d14090604180f051509070207030b13020901170303040f0309050904030915110d180506040e09060702010c120b06070204050907150509060a031d1002031503 74
    0x30a900000307840d4000c144441500c8200500707210420b80355061104c0007699603600f01400042c01c8550508080125141b2104122156000441d203903070b1400c02400080c0d90500208005244107031420411916003000a9280c091681d100403d0800694200002d080d28000c0b4126464400c0e5102d030f100c0d9880c1c0b400c446100000b0708160f0001d03881400002c000c264108000307607a440c020304210042c3c0d601c1c1c501140d140301046400707401241c82840104031500310310498587d142e01c0d500d081081501020b40458644013140d024404210240d202c044006001961b400004e00e801016103a0f91a03981003039055012040f10a001c560140800040c030480c0180900b4512100c00d80c0d50304180301d01c3c0101d000c024114001105d42002d414000100140c0f914421140200b182d60001c1214500e000000001c1161205aa40800000b4014445107840d20010345020030300038107004c41c40703040d2400a100c0c0d00c034a014041c1424814410404d00408055000354080c200c584070810031040c1c503c05056 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 320080278 1250 320079028 320079037
    0x1003080406120f0c1e1d09070c0b010b0901110d0c06020d0e03041202040605030f060106081503190b090a0201080112081c02071b05010503040308090708030c070f06110601031401020d0e011a0402 85
    0x1601820070031586c00b071829000155000005080900408015480300d55894100741c00c01d00c402d40000691340300560304007d081c080c4034640002400801414407000701a05014500101115004509a00b4952583e00981c0c0380721000c10849807680d9944822501c0c9011004040e400380b4580070300405c0038200440c0c9100c030400e640005050726480c000040f100141d009048009540000c3c107a0f84440e0341c10701222420a00c003035000d01d21860641000c03420510041d200c00310300d41c4003441010060b600b2001081c110782401c1c50004048441e07041441b118461141c1680d0f00d1006c0290114029145501821646010301613281100c04a2403105d41c106281c0e01419010440071310001303000034880c2c0300095001071b00900360b81d803490382d8285030b61540d0030840020340325030480c100c180400c00c20040341c48001c0042c3c0c607240d01640280c4008646402040c04041c0c4100e10a0000c5840c030780c006d404494105c828807504100401d01b507049140241540c0c205125031000c1c44001e40054034243c001d0380d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 320081528 1250 320080278 320080307
    0x40b0f01091206091a07090b18010c020312130f0905060904020904030e0a0603021b01061a160f0b010503011404020603070c0515040b010602061003080406120f0c1e 72
    0x1500e00500b4007418507812502030408072540b980300e40e5860000303000c00800f5a40f40c1252011042c260500b0742004c1e083c1e8460341c0040000c04818884400829110500100c04120a003000050400c00d80003103400c00c0c0304103103000c90b0f00c240018000120704d0300c24003030070464407451500900151204180c0b011707114103691040d070003140784001c00c0c00b40c6006503046401ca0300c2420001c120b15640408110050309560110021940c046107002c001c02a21658542c00303c10307003000700300d001e043c2103011001184045009408a0b000305e00ca5914226006c00c2e00403498014004101503141e61504410500c802d0090034005d50034405d248105010804101e0700941c0c0c014401400d66443d001c0490340c18035861710646441c840d2072803e03a030440d07a10103800d002d503005a846100641c10500c010b03103465001703481c0320440c0001410410219031a00260380507a0024a08610f40390306400c0900003070b044d03d00c40340b0180ca15060111144d04d800c041e0b411800b200c964201b01e2001c6414609440321035000400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 320082778 1250 320081528 320081537
    0x10050408040b0c010906050906150114030a020a090b0304060209010f021b120705120a020f06040b0418060305010f0c18030c05040203220b040b0c0a020319051c020306040b0f01 77
    0x140702c854a03910143c4a02040c01e0000180070600e62283d0040d140240c903400c016410000030300000002c022524020030b0800c0c20001031448a0800c400e406102c002e002504a9a000c14001109882202540000c0a42034042c0c0c0e00c4e82001c0c10104025440403100030b02060920550800e241d001143c147c0b0b101e01000c030f00c140c00c4024017017405060a0400d401c084140161080800c190f0380d03c2040390324100325030000303255410031807062000c0c20410340c00c0c1c14450a421312082029064480803141540e181fa80200c5504214075090405006a90001002e80d424840c502c03449201c10341c06002110100e80c2c80302085440c13003038034621031440c60001810728500c68030103203d1410503070011a00030016135400a1101401d2000c1e1080c08240c0008454801a250a01c014444103042c1d07581c206840840d200d14100b003805020b0b640348500d050221044140e40e072050003060081d42640d06000c0000c81003141548507032500d00c025031080350b1030b900c52864100c4100da2400c1c101258680d041040e1075 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 320084028 1250 320082778 320082787
    0x40218030a1b3302030405180a06050d021e18040807050606040b010903060522050703031101180b040507031712090f15040609021008040212010c02070618080f06070210050408 77
    0x16000403d6040291540a512080000241e1512100c0d80c0c41801c02c5030a190ba540c504003d14058155030255000521030006c9042c00350145c0c1d5642c1d00036401c03c01c441402d00c091400700010800d071040035840f00d00d80c3c0c2d840904110a0050580c01012031b50300c0362041c0d5072903079114020082120b9a024159001499205040c00000c480b80d0045800001c2644850715051700750100f544007a440733400855003030b00000300c00c004141e0003003c0c865580381200000c0c48004114000342c895001d40303030406000460710300c020034140a42404150059504101d000218081207030041002d9800703285500780c4100d0360f10000d0381c15000440d180841507003810103400310500d41300c803070302d10349001030000d9850958503070a20b401691f0b4580310b08003034441602c0c1e807a05450140100700705500d11907aa10381d10b904080303c06400d80c2d4045a000700395022414004444100000c12069000c0e02c1e422114803031094502c511441040040c0c014440c1500f942200d900c5030b20508010700350351058a00070f03d5a0018003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 320085278 1250 320084028 320084099
    0xf05030a0f14280203060105030411040912030c0f052713140402040506010509030d031a06180307050303040602190204020f07060c11011a040218030a1b 67
    0x80181003100700c04640400c21103124038040071501002d0720200400900421001c005041c810250100302110341400c6086180040018050748401030004080c250f4103035940d2090780d11075000e8078140780c0000e844500006c0d401f0b0042e006040080300c030000f180d828800d00706424864022500022810740d500c20341581d8007440b800484685180303a1340c4c442401450000b044500d4401c800f580b1000f07204c6d401041c2098010b000460300003030086030412004000254003610009800d04540100f4a40091101c0d0140c6521106820040d0956403103100084c40241c03500803c011076001e0702045003500d003413a90350001c05507a44500d20802e800345e04a8000e5003021104011000602c2c1d001910141c0f810710308210102c01c40c3e0040504a881c15510040c4420f0b00da270000000102c0c00302e5030004c0000d1015840c594821b000d00403415445250000f1341e41c520b02d910005540f502d400c0160403180c00c50401e240094074a4a00d40300d004d414500303d03500280b84402c0c1015032000140c200141030095154030b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 320086528 1250 320085278 320085281
    0x7080a1511071b09050903070209100f0902040e07030504051b060712031b02211333080403090b0703090b0c010b03100507050319060b0a0509010e010f05030a 69
    0x10190120455460301021030141e441d000a04020b84039580581c0b0f200009000700c440c0600d140c001d03000e44d0346400100502c1d0407000048514454044810301d9036543c41c10041700c0c0100094016030034440d0304080c0000d44542e241c028106441c07103000004819603030028120201c0c2c00c1180e025055a01100310b2980a450002006810343e101400480c5001c41a89580b40502650f00d6142d0011355514401c5103c5c1c1540400d0146040280c0701510704021112080400d00b2010300050040e80c50020320420b0a201c404040f800810440d062410b240d5060300c0c02c12020000c42070f0304584d940300d0313012013000c0364803c120040c455a40354513048802c508000d214a1240c006010840a01c104608003091941c00318010300a148000000030902080ca01d0916040c0905091000140b500308400d0000854000c000d40394094103050b032080c410404d02c02100060903556109480b0901c4c0003601c4c4c442c0a90050061210b04000e1b03d940440c60600c800468042881e1081d50001503001d10100d9400c822a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 320087778 1250 320086528 320086553
    0x309150705010b1507020f1f121b0519091a070204020c060127050c0406030b01020321070306050603091005090f15040b090316020402130e0a05100807080a 68
    0x9400010f502d0209002143c3d901caa2054011003100d40462600114606884800c50000c1c1c15160410945141c4031002106201007521109100d02c5014050001000360f0001c2c0c61a4504400074170142501301002d4081e500c008807070703100444090f007840348450143c4402d10031148031100c010740300d50cc80a4580995000030b1812640103800300005040d0407400c200480c040c1c90007017003c0107034128204940b226801c01c0c2d02d902404502349030801508030420741c10b480884409040114020780c103000105d056100304c0d41030102c5902c02c0078606c90440d042280c5280b10702206d407020070003951500204149404112015031481d80048060000c0e940181c200bd900503441004039401e0042554925040c48000034003021842020030400091041d0141d429400c09d0805018500d003000c06d1070340c3d0840206801002c3c2c0103c0c0c00003020800b00511140c2e4000801626102c0d045505140141202a010a8800090803d881c00e400304a500c40460444201e803200700c0149100300070380c0d80d2004210309 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 320089028 1250 320087778 320087783
    0x3030c0f142a1609090510090201020c0d060f0605040902030307030c0821090c0904020a0611070b0c0a02010f03021312020f0307180c03050f0c130b1605010e03091507 73
    0xd00540391009400080000c0120b0400c00b80c80303e192640203106103500207500c03080c1c030282005003000110704086240380c01c13604100ba0100300f148103800142c1c500302c4880c8071640c020090210f0401401442d030300c555030054940ca4188115656081000107070b6040c160060b5054200b0403603a000680140001724013a03100340c00817800e000404c2019503282e0b001c0042c0040030358041081000315003083c0903103445d07070802302c07240d030b00d00d042640100c1c080a40501421050140400c1c001c019680d04024510040c000c40c10f20707540d00e0440c0135069480b4a030b0b03002d089020461000703018066a009009a80400f07864040d4107a40500d004114800304e18111016604010b40100e500d08644091103c0c6014240c03041d014803000e070480829104441c01001d52008040c50541030000561000780ca00f0b8001c00403681407a1240807604d100038000186a2048600090025800e1500c0c00a03901041d01d180c0140003c108407491294026180d10402c4038869000c500c490381090000501c0024200103030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 320090278 1250 320089028 320089057
    0x140f0d0902040e01020d0f020f040312020307050102043017070206070f0f0b0f06060306060a1e09052b021c061404061a010e06030a0e06040c0303030c0f14 68
    0x95481d00414200c4501d1510b00d01265000213014284421034095440050b248000442ca0010380008101c02d602445c04001c156004601e04003007201e20800c01e449a05800c50021941c50340d40700084624170380041a081c40c1240042c1d5042d4441e40c22070112400d03540c01c190500c07000081201284080e07070000c0d000b03d0744407200780001d0002c142036003900c0ca98548506a80b05070f003c21400d2089214070003d103403000102000c030810625880768019a50400310a90f00c0a80390405681d0079626640c4800e000701458840d888030b000e0859001c41400222541a2001c00101aa03030560b00d1030290301c011900610840c626600005080c19080028481c000a260b410101000e41d5200f0588003005000c0d8800c0e801102800240320786885038140c0241604d5555061080c0c4200107070038009039102582c882c400100009800c1c1c1200c0c0c2010001500783e030f00b50b40b001e14003481d06050041041c04180c00283c54180c1c000c01d2203005440600120825031118240780a1542e48010b496000001100303506 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 320091528 1250 320090278 320090291
    0x90e0a080304060507080c0a05071e080706090318080705100203120f040204150602060f09010b0a08010f0609060b04120501020d06090b0102012729040302030d0c140f0d 74
    0x500100c050350040784181c0000c04c60b401c0c0a10018850303e400f80449085a008006000c5095000001c85001507400445201c0165104c410004c0038090640d003e8480c8200103070b5401045555448004098440e40300d1701003290b100d00010700082c40c0e034002c080703455002e0703541800345141096100fa0380f0f0711688100c900d4007181c0710024001c0d6509848120007503043e0004e0004500d014080c20305812012010714403e1450181c00030340d00c200c0909064049040e001c0403030b11001c801c1d040703143d0000003c3c04101115030b559000c24020015004003020403885d2020200e082003890044600325a0164206402c1504207a0802e241c10700340102201c256508100501d500d4001c0d00504004140d1a03000145078003019002a0a4545484c04402c1a50114540030700303900f1003061404101da00161a040c0074013103007441d4046560718a0311002031444c40400c02c402c055000006061200300c10100303200c0f0340703540d80e41915990340c9035090701c83d038400500c40060624080e50141100030b000c1000840c55 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 320092778 1250 320091528 320091533
    0x9020d020a0609170d0909020c0a12020304090605030d050306220501120210030507021b04020906040f080d030c050703030509150901050106021b061801090906180506061201090e0a 79
    0x1c07842d41c08100412a4054208803500c21000030542901c2c03010301400311110010401402c00d400d9000d81c402603980442d01c031f03184501c2017158042d0540d02040d1042010418523000e5580d0300a440303001e4140d0308000012490303003070200315006001d00315101c617820b5454640801c1584e10034a40c00c1000c604070841d5180904e2514041c450090030803a098148840c418014002c590030300380b41d1002850b081c00d080c03044096001611441640d03250034085011100840001c02034400c0d140d54641c003a901040c041190b0f00721f0404c42c022540f03140100c0d64041c03003090007a030550b0352200011010600501986001c03d005e9086280e2204000050300e061084400015403007240c19148181035a41d130f54014002d194041100c40e06942c0d14240041607420120300040e04d511071214040300d5241c001ca0320005990041c00010060039202000b03010154540341a055003040c86506050380c5401c00707020451509003001124070b1000e808400320003aa080030364010280505812101c0b0520445075001302 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 320094028 1250 320092778 320092789
    0xc090506121b0108060d030807050c160902030115090303020706140706020a02062a030a0f060b1b01060f060e040e19050c0405070e0306150d0210021c050903070909020d02 75
    0x8040c40c5180c2d00356084001000010000b0900500aa009003408244038010036041500705a00003840e1070219655507a00c0c5000d82170081c11041603c4140d140000802e00102940186050f00c0c0040420210400c14403011140c0f00701d1444080c0c0503800c214410f0012074402d503801200c02c051019050b2030400903903200812a4071401000005030800000d00588601c0014010b00d039003003000d114400c00650200d855001c0c84050a040b48282c0d1340d404d003400c904043e1700101c0c02040c0c0c001c02c103a03c80343d5410075001c80c5182c0d202d03070840c0c84d46855004034002a004c1400c00964034a5900e0b1101000da14007400000c00e910007200c451842420f8000e02c030800000e103d50001d80c45030b0050170b2801c0b072500500040e07880c050400b4003844a034524505030b503100040c10381c1d44050101440420044c00001240d10080840700103504841045140800c00b50000340c500c05100f1805803000c1c154240481c01c981a01907203c4150707140d0480d1208111140c0903800c00901c1900041200c0c410550070b500061 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 320095278 1250 320094028 320094043
    0x61b3d0209060d021206060901390309030b090d0f030207030c121211180d0c24081032060408071814010509070c0507060503150301090c09050612 64
    0x20f100e541c001034003c120000a000781c940000c010385250741130408100018000c22907203120310310045035404842203004280020251802c03071950000000030868100140070030041c0c00286c03101240400071a00040d000076004003c0240b039620b0031450000544118069800414280d0030405080c1012002c6055440c00b550030b0152138503070405030100d50041100b9285031741120300705503206018103049420040d01d01c01180f00200c5001142c2e242c00d1400700e0840841d60402d0355060080e0021b410340050900703210700350035010780754200c1d01d030f0f200207112404408a029082da6401d0b4078101d2408a10180508140d5462907945018400d513910b0118501c0e801c10360102540350302500c800c00076080d2214001038082203c641c14080d09500b07120a41c42250b0601c50140540091800259841e100d0980c110200e40c1c4541a01d01e141d41c1c0300b40040494009807041094022046802005441c051080c8070a03c0c2e80521007116152501c1000001404001c29007600102901c004100030b240034001903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 320096528 1250 320095278 320095297
    0x20f0f010c02010b0312090d0c1206020310050306090c041a06030408071b0605070b0a0e010f06050108010506090a090b01031e020d0c1d040506030c061b3d020906 71
    0x1d108414440700a00759406465094000c0e004401200600040780c0201e131030614043c1e541c01000141454a003c10f00c1940d4040c0b4000140415100300308400385c0c00a5000d81500140132118946807030405031a60782c00d0791104550350180081c8881820981c211300c055604a8010720192011103001c41c0c0d06510442d01110000000078030901000300341044054060030301e2030b0000205041c568041d1491040000c041c08034010b01c80010129105504802442410240240000080740c0c8100c409071185004082c0800e1100380049510304280003595078440000780800081b03494851908000d1440c0196581050b84911148a49200000100e1040080b803000142e81d95020b0b0400000c441c05869030504018400300e18800c0c6c2d009021700d079446d0400444000076992102d0f0002440e000c1034500b0250401c0300403070300c0700194040840a550b461071843c1528900d0307694810a80019405a03070303000c1c00941b40d22100801e083c05008001f05615080401454024450000303049030b0400c04e0070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 320097778 1250 320096528 320096531
    0x1030e011103180303090607030e03040909030509150f0f0c011808180a030c0513321506310e0114040e060a0216020a0314060c070c0b0a020f0f01 64
    0x5008606103000c3c0310000c00304104000e0b60031420101c2c045521104098444820161103489161050710144101c0c0d00800004104004000d2503190280c081d400c1051040c1c480d81c84010310200c9141150111a80040c4000f0200c1c41d0400d0074101e0f48181c0c00c105c5c01202e05642e40d100f40015000c050384690f01c8a4099540315458507420f450714400d080005101034000d015a0b1310410005142d0181181503d404503611185101a956680d0082c003042803032811444036425510680144400340002810349108551007903074a40d94103001c02c4640491043e081780d0200414000782d2000003040104400403c3d84080214170607507001800760142c3c10000c90b940705c81c0f0040005545451000207440403c0c1c806001081c0303c10506a02c58200400c0d20410b190001450120255910178000c0d2507540180407545140c0c40f0705100410380300030007030f0405a1003241701140c00c0312440420f580c0d542d0352110404031010300340001a02e05810180342a0305500c5a03110340142d620b0b060064490003480c8500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 320099028 1250 320097778 320097781
    0xd020102071e02060403121107060e01020c01080609040b0402060c030c0c1206040b1602010204090f02030103021915050d0b03061f050a060207210c0303170f0c070f0201030e011103 79
    0x90441c0b034031000380480114001000702140040e1505404d41d400c03070b5000010500c10000b208416607a8072850304014031207000c0d181c808100e407a001200e43d1411007007a821101c054440c41d006481109041e991168000d4580c0c0006000454071241c0c198024401b07001c2e2420030310129452840c41d000664503002036013140d44400050b00f00000c0594420708000001d01050034280c1300c207180360310302400b01003008043d2002c4018044c000d404540c004c1400c100100692010701c004a4002d400030700080740301c0c54043c1c02c5071742c0000c1108034004c00d03202d0340140c000035071584190640c2c1d00d601100420703c0080d1036070801d2086560600c80d05108101050404417030405019200868003070b20340086d0300c211102c00701408403a90026480050f81c01c3c615031084a409103501d4011080b06012006102c10303c1010044101540810101c4007404c640040b001e07036031102c20805040040898956820350028007044001c00e007a903c1c441162030040c14001121841d4010490a4034201804011007140000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 320100278 1250 320099028 320099033
    0xa1406011502030f07020f0a06080f0703050f06010f09050a030605040c0b031b030a0902090a0203040303061e0e040c05040606050c0d09060f0503061201020c0312090304030308040311030d0612110405010e01180b030d02010207 98
    0x2801d4cd4840d0444c50300300200c0c64644035807036103160082e02150400548501502c601409540028080c1c0f20082070034039030301d64903c1d14001400c81246c00f22400b10684400085c080303c4042900c0c0190300c0482071030038203801440c010303803c0d41000301413542040d122400c000241e00c03010030680c028901e03104003580d28036003810003070f0940780e00d980004544207074014444c000c803042111400a40c0d03a11070000085440c1e508040314060081d410140e0f01910704400021403d030401d0041c0825003a040960380c150010a40590b2070840c04d100e400d02040f040c040e2544070310300c038200941d40803000802c81c0215242200420342260000c1034603103510760000401412110700340c4e940c81c1d0301010500c0118a0a41969401440c051001d84002c09110a0702e1070545441c1050094841c0c8800781801002650384d07a076054068502809015595514004504c008908050182c2030580d14000d50b0200141d203448411011b48864601c82034200e80c0d10820b020032580d0510080482e80d1155001607120081c50 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 320101528 1250 320100278 320100301
    0xa0201080457140d080a030506090c040312080c0c0111030132060705030d0e07051512061003020c07030f0311160e13050a1406011502030f07020f0a0608 67
    0x203030400000561070368074440c44082e1100407000755640c01151035014079030300c00441d02c0c0c0c14002c00001c000040c007040020f400b503416400180b00d500221404800c50720740c00b60381d60541c460740c04007900c4110703039461454040e4060300100790022580c00da001d140c41c031900030300382c04c503042c0383c0121158002c00001000501480d4003c400160000200c0c02e4811302070140e04103007010801400d40c040c010116120301400000c2c015192a4099680140001d11078908055101c2c0600e00460f403080e2500580b9005a901d100c0174ad800d401c540100300d00c050348031142000b400c001143e00c6841099001c102805d0182001d20103c001140706580300314501c032003454040c01044002d00b00ea002540011032595040d05030281c1b00045480440d01d000190325502e030203102c82400d0900261251007040700e01001c01454440031074100c20079074282e451990b00c4660982c1c02880e490584801a40144106903801c0702980051100700d1005011140710072110300032584440c420342c03051021441160412034001c100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 320102778 1250 320101528 320101643
    0x8010b0103150905060103022809170a03080c0415020c040e030c0703080f070803131203020315090a06150906030f05060a090906060f09020d1a01020a02010804 70
    0xd007000e10040c1c4003006011052001c522901d50481c1d103400106031141d0080e81192045008025484050654803908140c00c007185010000060100103002030710003994048001d0700c00070b4030080e110f002038170388089a41c5040074242c081d0b041e508210004109900c00031108040c8010b4002c0c015080c0315204010840f01707820f0b03198042d9041000300d103003621008145141560740c0700c40d03071544600c030b125605a601e00412500502c90080001400381403401010614589440399000340306d00c00103080110160f0000361042c80540030003261808141ca0304034589540304140c00303800158156211070306424840a01c0209020921014040c031005a05006198002100d003c0900c10740c01c0c00c0c030104400c01b9491040591a56403801074404025942e00810010488090784454040d15020500000c0d40f01e03241c2d49510760314000300f4103c408040c240c8120030b580c05801500c4010059001510b1424000b8004c0355842e07080c845d111a01c80c5400700044482c1414142032808107aa9050326140410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 320104028 1250 320102778 320102801
    0x209041d070801061d0f07050408070b040e100b0a0c1a15010909020301060905060702040b0d11010908011e020c030c0a050d080106022e0b280e01080d0507170c070801 73
    0x581400c0103103402150300d006e802c480c41165460f007542e07a1110889440c011a00b20303c0b66402510320010b00d580c0c0c060054404c5c1c1e83c5810600c55103456020031740704e901e041407040d45810320080c840e00c400720780550013003044107004000e4900300c82d032068031464550b1000c480201e01032807690f10205140d41c1c000500005800c0d40c100440c6103505040c001740c103084051103418894080003a804046440d0382d00031034007a00c40503000c41c03c1032a0910b801210004040e54250004404480000303445034140188002400f011806998003403000c61404041c2d84480001c080c244800c020800d0448000c102e51005903014001138554109440350007410400c041c1c1c0030800715031141141d019102c1c1038500c40c0042e44000e074441803034101046010b8028080f0105220392004100d4a242d0010200f8803481e21514007138000c0801c40c58813a084414110003c0c000c2407103503130094404d100703443d004100414a9030700a080441c03451404c250760300c035030307610207000d80300290414101041485006d0180520415 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 320105278 1250 320104028 320104049
    0xc0c06010e090601053705040e15040b1503030406020f0d050301080d210f020702040b120601060804050a0204050a15050a1401030f0f050106051b0c0105030402040209041d07080106 79
    0x2442c2e09580da40702c406000e101d01c81d0769806403101c1d283e40d04a00b0500000c001d00c9a100c0300c00d40e003803010500883c4500c030300c90085061074040c0c0380600000c69049541507088044202e591a5030b200c225804030700174217130a070b404006e50050600d560100b01410003800658000c0c07003d600c404245900703029050100e5810701200b44010710206202040c0b0781b03142c480e240b41c20402941c40314040c034210510311230140c94183c0340c10340900414003260011f0100368000d460520480d2036800070312542506024211145030060001480068400c02c2540d80141c0940212110412180c0009081313030401d07035104021541c1c035803000460f02031003940c00b8000c02e000c5810702000351500740d404544011900400381050741c2c4012000d4410219404031041189251040144c0d40e1105c1b0302800c2c50340400c1c0d0490f004105440c005691400008503030a9120707040e91224150380b242d40c02e000107900301d82801799000e9142c0065511a18011101c454507004d40d800415070203251549841c21101e46822400494 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 320106528 1250 320105278 320105281
    0x903150a0b0906090c0702040f06060c03080108030f030f0a0f0f060519080c1c060504111e01020a12030209090a15050d1e0311100204032010031509050c0c06010e 71
    0x507501d5010480c5d0204070b4240c519a1584140b000400801c41d5030200c080c207500d0520701161447c2d0205200010f94803e071650038250341c075003680f00d68070702803071070043d4401008200242100d000085d03401d0b0000540b2602045016001c1c48000a40f507800e001c401034103035a0381c010040e40c600040c1111109401d44500b4a40c1c2e07060624454a80301403102a84c087c0d014602503a0901301150b45003000c00350012020045820940340480139005440d4a052149110601c21460700c44500301416030088143c00030000042c542d40d03000e19152180c0000014190309000c0e8030416210f035580680305101001c800240e6040d400440d01030228240c009034000d110181216000034a043c140300f03a480001c410071204c1e4410780c5000c072005096454641a42d014a001881140e5419009481621702c20401030014064055400614103036461140354002a1041e0022a03503000358014032180301107208000b44191201c2914043c1c0b0b6080e11480700d00000010140003108040c4052405001414030720740c1c09 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 320107778 1250 320106528 320106541
    0xb07061e1a0402090f0310020c0d1706100903080c0d11210d110706091505070806150f3c1c02091011070b210c0903150a0b09 55
    0x20000c0e0301c00760500907075000401502e01d42c0c442189031806240181161a4050b4400d4218003075040702e03a884c80745200d0000180d500ca4000d41100b0380340800307201005a01c2e5182e0041115101a901205007840444400440405c503003200814041250100030081000b0b55a8003c1281c01d80301e80064607a0412824019028405a400105250303004122902d0f00206545500240316016075504241320014041c0100714164000001c12170241c28101780029158a902e4141c2c0c0d004c0b07542030700003080c3c1000909140382c040311201c0125130015111741400b44440300d2000c0c1c0d5004002c64a103846100800c4800c050710071614070720040b001480d406140544210b9403001c0e02540204000074428405046568482941510481400102400c402400c1c1c0d59016160072040600842c9900400c01d02042c0701160004807001c000b064450101001141d03114054120000340c0a4a0324407410020f1549541d0100b2060401c064801900304103400c252030203004492200e110349015118602c1005007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 320109028 1250 320107778 320107811
    0xc1e031d090c120a0b0301060f062c091905071809060506071202030903030d0b030610080c04020a02070503150711010507020a0204020d02121006120b100f0203040b07061e 75
    0x1461120803162000f685520700c2e40c10140498105c01c131307010340c41e00308006a00400003c680003101c00a03210384150305085640c040ba081c0c3c802202c204071805000c107800650518924940d441540e2400340c05180502041446c2601c800b40c0d0003500246004551085c0100d00340f1085000b0301c9401010000e84d8a801d0218200780900b0134040c12101c040d8aa15142d40d000744215000d110004082c0da90f1082d03040841c00080c0004201c480c028825a00000d45c0e40c0210b44000068038491801805c4c1d02c01400104400303940700c1403210045008001b400150b98504000c1c0848440410403503600d14604240c000303100d1036034820402166810403007884115500407403810301c11174054902580e680c0050b03113980e029101c0ca1761303900da81c0b400640800c40171032814003924060701c1080e0398400c0030081e900d500106880943c0203c9030712082d950310f0801428000c0d10800b49208540c01076a0a02c0e076203d440300c105400c1584169011611044002072104c000445001d010440410401c40c40130008802c10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 320110278 1250 320109028 320109037
    0xf04021e070507080111030a11030601022505030708010c0216030b040303091e0311060601140f09011e021b09011212090b1810030b060a0c1e031d090c 66
    0x440c00c0c030001a52400d014060000310081c000507070082c41080700c018035400d602d0740103c035006489850075020fa4a04026102103a00800d0141d0040c90306041201001040401081102411000150f00001d0548091140320000c003000000051140740b00040a0304020b40000200c0740020440f030300344009040c84941c20b42084d0141b9001034554001d2404508103204070864032410507040d100d490070075070f20000740000c8007514010f0310f600f80c0701d0b90b006691540808100107060315040c04110030b03038400d180c040c0080d41014074020710300040c0850042c2e0300140d01c0f084400181c00c55492014000050301d4101c40c1900c040e1076400e02985056000501500c46a00003810102043c0030940e00505c6500850040c02140c80d003540d0380c0b04e0310380304002c1c11000089428004e00300c0411000c00340d0700903c40c00c0451000a40244d2810141c0310341240ca00c3c64020b8100c1b1440b6200445150a41e012040418542e11a4030f52164903000c1007403c0c2c1045402c2c400061140e8030300e00c1041070fa190320301c0a90f0f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 320111528 1250 320110278 320110327
    0x31b030a1d0102100603050309010f09080703140304050d0f0c05100c0b06031f20070512160c09050a0b0301091509150e0c0a060f21150303020c0f0402 66
    0x501882030301c00100e06002c0354600030056241010400310a00c00088028021840c003602d4020f0440e024200c00d0790240c0492080d10307000d400c010010800b0411420071000882183c4060724505a129000100441001035003610000741e21081d56081120945a15020749000c40b031102d503440d40880014107081d0688001030041340d20f030000c5103d44c0c0b0108510b003044264008903c5488102e4031415008010780b0a00049004652207007028000c0c0b04011118040d4025025013140312004101154a910521410b085408120901d001041c2039103180350207030203818008145401c05845410517203040841d01c61003a403420880c0c60000e0050060ac8050a821110201c0d00700018203000c000030700326117031789000e2034184620010403201c0420b04030704a8400700c0e040034402d40c03034210440d50a00901381c140003107440c0c0ea5840030821800245115070307215007800410026401f00c07010600100c1c640c4110096840030080d108585404500380d501008140c40c114100008001c1e070544c44032918603007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 320112778 1250 320111528 320111567
    0x109060513170a060603080c0d080c0d0504140106060c0326191d01060603060e13060203190e01090605071409090402010c050601030b01060e3304090608031b030a 71
    0x8040221000b40b050400340c41e00008100030345075030390404010239408120307000807a000d454440d4040c41e0140a030a070142039606e80070b03070801000900442c024000503200303072403088c5100840d0040b101c00f4003900015000035030b1440d01ca403455140103800d0010b011102c1c0c2c007100f401d148000c2240344480113030b5840051958564810510703041d4204c0100001c0c41440301907000c40c0c045494881054000404445e103660301003040f1580d44102003a0118113942c000402c00000a445001ca4420340203107404c158142d0450000068401800c01214503510160100c4e075180e51511050040764030820f42d000a0741d050114210300310003084407640c417074644030510a09400c1c0c00300701964840d0506c40700c5250b01008459255031203082c000f00402e4248078040018004504506440c00c0005070785000000404140c1b96110780c038944c043c00c950841840240c0008140000252241039004500081c100e0f040515030394082c050b0f001d010303601003458800d2203520070041000d402d41e004440242849030f2051 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 320114028 1250 320112778 320112809
    0x406051c020d14010e0a020702100305070212160b010618030201271e1d0103020108091011092103030606130906060f031409061801290109060513 64
    0x35210300030300070341002100311498640d010704403c1c0c066422505a96030070003111044d03a1040307000010303846008002508450141e4441000b18001c0d0001034000c81c0381d0041d00c54800c0c0300107490f1141e8110040280c81c4401031013615080c030118450039405890541380242c0003c03180c41610706010801d2000904010140078a05003a408101e400d20030040403c00002c04c40e680c56541d031006004004281780e041c0c1081038000b60800c1e0004000d41ca41c05a07402d1a040c80c0e20f19001910b417000018141e0703240340035104d0550310308080e5110320161000a07a03134035520740300c070320040c00300c06080459100c03040d00003601042035103580003055903031100c0112450350f40d40740403420a0f40d01081c0c90344540e80d041e00b817004c041030b281c3d00710000c0c42c00b402443d1750402903a00c051140b070031000c1d4292805c0f40340d60892000310300140c4514400e0300304032442e0400403595007446415480c0c3c843c070150030822040c050301100f001e0307580e00014100082140307203030503130420054480e0000e02c040c5511480c5541d219014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 320115278 1250 320114028 320114077
    0xf0f0412121410030201110c0916050c01092f0303040902030705070804060e04050c070c0509060102010908190f021b0603190c031d0a03050f07030c050601140a0b040605 74
    0x4000040c0d411400d4100b03455030802449003034100c041e03400200c1c0403a2942500a44046c0d000030407512509000b0240f06180d1100490000c0c044502906802044810054201850400d00500c07000701c0c403800c44241c10341c0c42c03000700880f0760000450002c4d008030007056000003581c0c0042580d0a484d00c5510059403516401d800f40e90b01c3c4034581e00148101c00100c0c0015291b5040000002d902c2c0e0255024811542c880c0302c03459461244010051400645c0308060029003010400107a10803010300002841446641728000940c21010304401000c8001e82c0c19419642d00c400390344210a040e000030503240040c5045951260300451055000703000c0400007130b000d0044c14412074110840400200010034038a41c000f030240c046801c2a02260362100810301d04114001480100290181c1d43e1a0800c807510106110035440394000390200404207901d1004500140083c2e8002d00055910f0403d0b040b00340c041c48038060300ca9005150007481403000300610f1307030008101e0b4044105161003402084044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 320116528 1250 320115278 320115281
    0x9020f03180c030d0c06110f180415030f050708030c0a030804020109050a0801050a05010b0418020d14091f0903081504061518080601030305090904140d080f0f041212 73
    0x40b62a41e143c400c0001c5a1025a000b40d203408240d4021402441f602e401d244031110300d84121000c2c240ea040341040840750034944000103121507840200301261916070004150114812500150341e00318121000b036042101c02c10020008124080c00b9606003c00c418485480f0b0985034005810711000000043c11a84142102009040000d04250321581c90f40c050318000c0c82c0071900c1e02802c03032034034001186511240c01660110342030000c0380190600320000341740c00384d009040e403075050513240d0003070201001312640e40300d200c5c40d41c1c0401811800e1301886485048820001d511150b58030701040e200c0442d5000e8038050f03104103818800740b084c0c0e8050000c034000744510380c00f141010000c00c007440310030395101140030205040700c4c60b01c9101d252030340c00c20380d02c8200070b101c0280850300030030624090b07080c030b41461507009000d0500914a031180009040c01d01c50042a0b0b82c0009119000304a04205e042d4041c030340060a60a20661b546840c0e070315440412030700c04c0c0301c4051081058902d400c20505 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 320117778 1250 320116528 320116543
    0x10c12380d2307030206040915090c02030c070605030105060f1b10060f0501031506180317030403080f060d02120327210601060c2111060109020f0318 66
    0x50724044030400345003014080860078142000340b0112041e41c1e482c080500250314400da81e0024240b81c500340c07800c910304004101d510798011404040c0e040006d484216841100071001e01368014540e00d0701c901a0003414060a90041414004140018030aa884250940f03c01c0184420000c0c0d8030507988111035680b01120304003950620861042705031840035030b0881c1c0300700c86a200f20000c09544403001501580e44400c40c50854a12031345040105a11403095003014840b08009401e140303840340c8a81da1042022060142c003a10b001003480100b6030b00c055429405603280c03051100c103040990004074428840140a403041c400440101e103c1c80042c02203c0c03000c0943c0c070300010522458103030094043e06480307000e8412001041415111218040040248031440001c0c0c4543c1e82041010354580b18060b80a03100d00d010804210b4803c0c4020610a5101621341c994080164013108020724110058004a20481c0140032100121840000f600c3c0c0000c03500300030b802c8000240800c1440c0440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 320119028 1250 320117778 320117891
    0x18020d050d030c030207020102101104050603010b090a060c0b0f0c040b0406020f1006060c0b0702100f09061b050702090903071205031e0103020d0209090f030c010c12 73
    0x44000590003006400101111105070544060119003050300042d401ca00440390048d001da0000450140714641c1daa100f9401124103600c204d06080d29080400c259070000d03013010428120005100707a040ca040c1d42c0a6000b0115071518000d911016a12040e1909000d4000548403000346c003c6004007220b181543d000d0300301030003d151203e5070340500a69924094818800341e029550311140540c0b100d0003940299101c1d500c0c2c800c100fa441d0313a102240000d00034004070850180b540c1104030810207004050a040954801155248050404100302d42010441801c500d04504060180503040302c1910b14444d0100d92807081e81d50395440b400d066104002c0006c140c0c2c1040a07000e801181c00c14081c1d4060078190030030324410140002c150700050820700010350b0140740018080018942800c1d1070351320036959410740d40094140c1c3d01040c99078102c000301c0700c00340e51102d114800c056417016a21503680b81c042e10900118403802500741400c1d003401c546040c4039050800300300c280c80c0d1031220101d0030390 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 320120278 1250 320119028 320119039
    0x9020903070b1908010905090d0c080c0304060c03021009050c06130504060b13170c04020f1b0d1409090109091a0a1505060702012001090510090b0c030c0a031802 71
    0x3c14030110000307001c40110300f10010032250000440e2003500d510520b8811018030000b01103c46203030000780d8a00d90100d404540e07031103080100704158001403029000a0042e40c803100c9026100d4900a42890405a9044109858000400040380d0005181da804c2d00040d10304035500c0c6c10300002c052a030302c555005150454144180014081b080b80c00428400209441288000ea200c54080c8100742565026600d00c0c0c2c8001400a4207150580c001e14114011010543c503110b02c1400745100a20700c003c071100315403c50714000c032040c1c1e0444072000d41080722941c00b6217012103030400522040d60600030220b00315941e60015040040040f040a503e00d1034507041c801520701f0090340c9000c5e101225048148030a541c01c0001e580c21f0510603900002e505131104a04003400c081d80c0703e5540303410a0049040d648074425070303010540900c04010380c80648900070031090140e041100310864094a41c0121010030010400f1140c100c4050301c0803861186030101d1011100d088412a4108081002c1e40c0003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 320121528 1250 320120278 320120287
    0xb06150c0d0f05160b1302120a03030b0402120f07090b1204050d0f0c0627080d0506030c1003150f06050a0201110a1b08040305150702070f050a09020903070b 69
    0x203400150030704080722036565040c1e800e12600421902405049181ca0024040c4512000000d1640b1302c003a501171103041c1c0301d0310392049503000aa400e040e000150111600248104014590306025501c0240415502540b8000c00058548000c0c400204a460b0314058400401c105030311502c030000c0107041c002c504a8480151008114a8500c05d460031191403142c1071251024600564454041610716141c0d142034521540b5a8005050f4007250107100251502d907070061501c5645400b00d50a0064151355140c0e0014a404411650050041846a0b10000c030641c460794807803501d801030805030301c2d020a40c4201d15514254020080d0014021080a25004500e2070303071010182c020f107400c55000340405408905501c1c0c0310701c500b0b004400000d4142c41101c0591fa01ea280c130405140c810441c5d249003e0740ca4584e14109025001041d0754041c442091022040e4100007030405410300590341e40502c0c0c0b4100008900048038400d41650580202d00810782c1e0303034144180c0008001540401d44d40703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 320122778 1250 320121528 320121547
    0x20906040f06020d03140105060307020c0901063504020d080d090b06040c0906050a140f130512072402010b18011a0408030702010804150e060711190b0615 68
    0x81c0285405200010310581014900061280c01002c4200c4051800900240d080c08240085540020250415880780200f501003c2c1c03140c442c00da0092120780d89004103501c2403103003100700600c01d04415000d1031500c01e45200410001011b1034226038103c45941c040606407814900300d00807d107101032003d2405503583c050000030600b242c0f0130081118100301c9904084030507a81d550180c00b40d5000681c050140041040c01038607004500d00c44101201e081203445000c803003490b0701c48007190b203501d110340303204001909107842065000f00e03c50016040180c2400d50a41d00900c1800040180701041c05000c0520fa000798000794200c1405032801006480c03501103510490002c0c86100030b0300c01500d070840390080b415016507081e540d038400910719001d0f15400440b030410b0082c009481d0f42d8181020b014004aaa100d401c05040b8907801a02d1286064a000b90070740300215040c1542d9082504550490070313500f403856924560010000d0398589a090103d100000100300801140c800011000781 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 320124028 1250 320122778 320122799
    0x70305070f020102182202040f0314030a080a020d02250209010920030c0c07030f020f152b090303060e010b04080601030b0703020f12041b0b04050103050a02090604 72
    0x114030300548880700380c0c50908008900b02c4c8100e20081d50280442081e0701710a1030081142030200d0210b000500c1100840c40669040742d100e507020040d034500e80c1c00308004000bda91103c052003a40d000c00f6501b402e00b10030010b40010720040c00f503005181e00141403d500383e020350559008108800e100b1051000d840c00c407403035003109103606922640318100001804440c601403800032101082d6000340102030030740b6658998102400000700b415040c000d00003c10003c001c2d0400541c09495005650031403070040c04245c10301030203050b000700050742c01c0121b0035000c001180e546840503a01e800307030200b0074104180f000d40a4005001024240b040780800d041d4180c00000039a07080546410880c0da0b42c40b8810000e00c102e1003100352540100c0010804140301c6444544c0c451018140580307801e4000c281442c184d40100c994010a07403d06041c401888074114111640c1002d490701c1a030214100b003d20507203401188981410180c07034a0000d10004440c2d01612087e60000e4541c9480c0d03900d4000001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 320125278 1250 320124028 320124031
    0xa061406010909110a0507210503180303150d030e03010204060e0a091419090b0103030c060c230f09120303071707080604090201020c090a0f18050c0d031205070305 72
    0x140003400d0004040f400c610148101c94501d1080c81d09545004824142a1620742241c0000d4031480c0c0005804c6460b803007412070182c403081c10b80d13482c1e80c2d0ba031500039200d41c10140e6518071000300d9441031003000b038409107682c400b030b525040844282d0400a501d142c00c645045100c19420742550000c2400542035402c401113031140101114420400d58845d0058030441d0b417420140c0b00701d0710040c400300b00070500b0145224450031603000e02207030042058491404000003a4411000600007030311200038400d06200d214034501c03083c505080f003408081500030301929a442d0f200c09024000484249040ca001c04544840034054480b038041c0c112402859281d0b017044850002084000124181424089444500c680708a0311498555100c1c0b8080c8030040240020490542c403e6111880555649400303186c4034040314440851014039003400e09007542c0c00000d01b031400007603018108000490201b08070b01a980143c410340008025420100c4541380c4000c01110454a40400e204060342c1c1500042d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 320126528 1250 320125278 320125291
    0x5030c07090b010221090402030415110304020406051806060307020c0301051806091204030825060903030c090501170702010618020429090f030309061204170c070909050a0614 77
    0x48496500b101c103e805c659486259644125208010b0540c0c03034502503010b103400a00541c80102d080301015082c4085440841404034911000320401003146000c1c000c40d0302520083d2281c00c0f1418081c0c40003807000070064907451090001100081889108124141510318001d00038000c90a000000089076000b4010041007405804c0006602c01c100081503248070b000d034a0028a05850758864281c0c507044140b4012030751884003070704014010342c01c188039079007409a58006002012458060300b01e035140390815041c0724a543d0204401c4c0e0b080b0010704001e0380041080034040e07440c100308a00503c03440d046000c1c02d250401c581c4107401c0048d030151054034624408010f604800c880c000b58a0095620300f4442c10008103c01c0941e81407211440c40007510140c2180d0400d044140000c2464101021a04e840389901c400c2000340190b020300101c40501044005141240701c1014039180d4485010786150b60362a01d80d08030401c0420001a1445600020104031524003030350411864030302a601e4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 320127778 1250 320126528 320126533
    0x103271515060c08070210110c0f060a050c0106050a03081206030c10030e01090b01141f080121080712122714060109060302120703020a03020d05030c07090b0102 71
    0x1000c0003a80e403841690901064040e641440301e01c0c0c41c42c1280c1042c1d0450341210401000d2180740016100c0010750004a03a090300d0360f11502e0425025546040d1480401c140305c0c0e43d0801240c0640e844000845281007070070f00d0f045503130f03c80c01603002c0d000d45560350106410074145040001803103c003c001c0c0c140f44140005000e03203616410101642ca01118420030f030312520f04c840040c2058008e500603410307078064000124050507270352200c5400303081c241d010800360036034000d1120991404003489800d01903071403080b0650030495540100014014080e40d113000c1c010100c008504a016401900519072040d40d46680e00410316140307001d0001d980d6200c000c1110302e50514a00c0e4074a0103114001390415001c03001c41040c1c400d80c94020b00441c80700390303054a504040e12078641018408070307002e0080c07083c01203100380c03462040c400306580d0f54003d25120f0304040414001079551146107011a40c0494441911003201d06049003076115103c55211581301cac03d103000074a480303650004a520707a0b00741c09 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 320129028 1250 320127778 320127803
    0x1a0702060910060608010e25020f15130b041403030408070308090a44030108120309030d0c03020c0f0d020c060a050d050a02070506010b0913020708030a0902010327 72
    0x48090f1030003402890085130380400180a061590094207038080b500480d0803490441b18041700c0f24249000d00448010303007141c1408002c018040210a200c500d40b0401c151803403074100819540c019810100608100000c80404c09004462070040300b010310800642e0360b2801c0500e8100540e03400454109d0218000c1f038001842400d0115034003406503000309501c0030010441885103d40410000004901035948003564001a607091001108070f002448941d9654101099940380c40349511f003c92a16408104028500c800481a11504007041c503010480c42e8403503005038043d004041c80800c03507110f240e00c0d210b0b4507100000c2d01107400609400340c6080511050500081d84240502c05001c50b40405c01554017038030b07651215610064a1030014200452903a07424101b820030f0b4400242400082101c1740b07689000c0c40240004003902c1300071407401c0180d650304610741c00001c0c4626100c60752501d68000b56402030b08121500c400350902c2e10f0200705564416041003142c0b100582d4000304040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 320130278 1250 320129028 320129053
    0x30915031b0503041e170a0201051005090c04090209010509060711013e0f07080f0c0a030c030308041b080102040303020c12070302100c050610140d0201080a02071a07020609 76
    0x411280203581102182c032403405c044280d98a0341c620043c2c100c5d4a090040c030803680e15180c03000981444141d50b4004541420801082e614800c5d0a400c401e104017001c1041c09050003e00040300d040b41d24000e0b0150715600440c00595660041200e142e03006580022107004000f140401c44a85490988840e040138410306010811209442601c242142c10500d00e40d06080c460020f01410200309011207403030510385a160f0703007807240962050b8030a62010140300d0340d0820034800290a880155030381d0043c98a036443d2001c001c0014400903040c0310b152804074040c861000000d414590034850f855600340ea840a21600035405841b00780c0040c0582075600d23000f440c0c030354035154103800c90304020050103003141c0800c40c41400ca9040041441f408a0040002440601c0003900c64103010141c16509407404003071300c8803c0420a080d910800c9082d01c4a80181c0c2c12041240c1c1240e02e1000041c0c5a4009207002140300c110100880003d15901c000c01c01c42d03940c0010014443e459110503503109100d03a2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 320131528 1250 320130278 320130287
    0xc0a09020a030f1a1c05010c03021b0d0f1d041113050409051e030c1b01080c120a051008030705240c0a0e040605100905092809030915031b 61
    0x11820100c2d1001c0303110140342c00b858001000400c408002d1040e0a070741170281c0d41d050031118000d8407100829004034402142d020301c1d16226002c510081c001d403804034032031007000b040c1340703008007286040c004440a10340c84a2180807010b8044200500100000546206170381425007140814101682c00140045a83e0415020301414298000000e0041b01c0340d40000760703a603c0140e0301c42d900501c4240080e17414003c08100d110a0102040d4812403c1c1c1078044c00101140c1000b4145028003c0400580110380c2e400488542d00511000c80006c960315681406058410680d02ca041903210100d03a08051010100f07507044100c44410060151400808080d12003440c220b4410f11008424000190800e001c0c1043c685220401000020b00a03114000124030003079203050600001d05c0541c0500003814034400340b58004852403004043d030252a006c04401d0222030b10700a281c10b4070380100c1d40030103006550a40282c031002131072003005c04510800078000c1c0741c80044480e82d0603943c00700180e100e000303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 320132778 1250 320131528 320131541
    0x60501140301060311042301030803011406251b09050609090c01021902130e060403020c09060a140406030b010602060403031406131a220b0406050117090c0a09020a030f 74
    0x401175400a440c800208002452040290b08045054441d0844245a15208036010318851940d054580d410301407031544c8005d07040c1d4054000da4040011101010178540915130412235100e005903584900e15004244014860505a5107a2142004264484d8a811040c03150b001a50406801d64a40440c80d54805d03c0c010000d0242c4c11401e000c0c4e0303040a514203107114443c0060702d00407924042d4103002088906c9030b041040260452010b0008056050210340c010f84d13000c4444a0741403c040340001d9140c1c40700e100745c02e407e04420001201c261200c0c2c008100a5030444032804039982c0d601000703501d440c0201c4044001a18145100000002d0180c2007400fa40b005001d43c081c000c1c803180d848c4003d14a0202c0c200703030000005204551551144c600c0007010000703c02002600000c1284141a19440407500d03109504180c4244610b9034009014403001c038801c2d400c00c0c1581c41c3d4508903810590441c08040e004080c035000428441d485800501a40610355001c000c000c440441324400c440d203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 320134028 1250 320132778 320132783
    0x3101d160312031806050103020414060a050d020d0b01090c08091b060f0d0e010f0f05011203050a170405070510051606020c0102040b070f060b01020d05030c0a1b0605011403010603 79
    0x14241014070101d160000704803040205401e00113000180009074000071030030400d04481064a03800140214103050040e00265900000488414189100082c03500d04060007164090900000070005540e5540308800740c0540009410145507140c45122020f481403903480350200e4400c00200b09043c000180d10388482c500b05981c103801c02607001c204900ca601c00e00440a0000050000802c05400c40c4600d200489120b130002800424168684d4199040d802e0400121271510004010000c00c010580044950614220360f4400000300c0542c2c2d5018080c1244150140b4a4104400c0101c001882820f6078002c480080c1c16014550f000c9620744208030300c0340a4a1141320542c40005c04d250054009494038200140c10517444808140c2d42e90000e02c0244d0300a921885082d051110602c40c0c207030703099420305c050000701c4000da0010b082d41c80041c04450b6104000540300700c0700d912844e001500c80380400201075030280181040c0018120a0146c4082001903402159540c50305204c0d040840e903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 320135278 1250 320134028 320134063
    0x1080c030a050c01180806190c032a14030702240402031c1e0203091c0b0c031e0703090308070f021f0204050603010807030c05040507080103080304020a0503101d 71
    0x2600300011605c210286030200ca02c001c034000040f990706c1c802c2c40b005200b0030005201042c4010502144400e50b01e815010b403040c149011041a0715000c220441ca5900c0d81120703403c1d00c140340f460000c030350008500500f08156031020007805007050340824028100008009440e00030891405040780c03a80b02954001d502d58803e50141c2d16080700d0300860340c00f09109082c140e81c810300d03441c4249803280c040d40340300005800004403803100d4501821340c6500a103080341c4000514543d942c9007c0200400342500000300004400515505040e050000e0034404030246e1034045d04046c2c4018001d0031640300102c0208040c04001688244105450200420154000c0041c6601140942c00443d0600f016240c466000c020100710780c0c0352940110300808104000b003601a24500f403e414103075664001a10540c108010b0020681d48000420f0540b50840325550342c03034440307200089241140d40c0c009601802118030402051010b64031240c59100720303020510007404002e50194a83d2800d464551941c1c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 320136528 1250 320135278 320135293
    0x30219080d0314181501090b0a12080318010b0a03030305060f0d030f0e0402160812150105040512010b03060103080903010e2103070c21030c020102190513090203040b01080c030a05 79
    0x15003080d80c1343d210b0100e4401074842c10031002041c886401801d81040c0616900c401440e466403c003610518005c2a007118024400304080da47e0710f0f01c41c4005813149980c0c2e00c01c1c00310181461030a5204500c6000c00909640302980da034600a4040c000856415103d0f0000f10840411428142e407011500f41d03065858025416001200f51a4044610346c0c154001c4c3c1d003800f944040040c00d039000307141240a07811075034071525648100d40080a0050960720b6000e8207140785d0039a81d07005801c0e2022f0b02c1049a08502d441c5c0e26100701070040c482201c0c06c69051080800000502c0f42c0035001303080d090000c1e00207001000101e0b880036a5010002a0100d00704100e61200821306248800f07190801d011303207407a0000b00070a4540030314969038601c0401d030800c25250044505a05842513207941112130009500381114000c12101149819000100b40803000172038101041c032443d001005048030fa1011034490505040007a00391030f090040000d5407150103002d0b08140307000034440c1d15443d0b001004000c1c6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 320137778 1250 320136528 320136541
    0x20c01080a0204090906050103120908120a12021602030d0f1b0f05030a03020a0801150806010c06060b0a050403170301030b01030807030e0d0501020c061005010903060e0304030219080d0314 83
    0x203140004042008956007480041181206401540c41d914010b030004107455041d420f107161801100444a014420680400c10400c1d90100d640325441c181c0c400c40070380311140d00382e003a6204051500c05951091001608040125111032524040c0d8001d504442c13004030888400e50307100643e2641c0b04042181c02025003005131004000b41e42c418400c070804480350941d5501c281c5182c02010514020a40103d0010986030380041428010001090b6109044d0070642c5d0142c4201d40c042d0006040009070b0503084280401c1d5003000c8010407800c06c450760341d400c10b00c10081c02c6070010b0000312603070440c4031410302c0e0340104402628140c940103d80303005664038666491105501136803080341404950807103861241d80300103041404601135030000d83c4d10500c141c8d03900c0c101a0014200d80700c000174680144100d0742c0c00130f44001580c1c0d103e000026481012006107155000c1da5100960014510390075003410500740f0003500c1140c0710202160f18000004400b81c06031100340f440115081d64a40c0020b50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 320139028 1250 320137778 320137787
    0x8070815190212070e0303090d02090702071a0d110301050f22060902070b090601080309010e0406170a0302062d04080d06140f150703081f060e0f030d020c01 69
    0x100002004001c4090300845103811003a40c1003421020404044a020031541d503801462813070320b01030b04402031850408424001600886507100280c05060030100003410f190080000c10040d02c2668603251a0160140f00030304643e00100030081c86604000012042800e40c0c4152416500014854003812500c101405010900122108a20844403414040c41c20182c46030501800d0090401b5a42d0002400c182151000c0035008401690103900108180c0e440803082d41d007009400d103042d14a8040d0000010b000e4221030f003103280145c0d50920f041c4030400f0005803004d441c034425001d540d00e0f65141101211400184004490441c009018a0300c1c2800040f03910350340584145000d505004c43c1190420031980c1d80d401200c001e11981442602e2450464403004018030101c4648020070390900422105004001006080c44a41c07404100f2a60400408030502034880e0420301e8042d6072a01b00610712034600100781d0003250500680754450401256000401119400800c003007801e0000448 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 320140278 1250 320139028 320139031
    0x1060e03030d020301092a090515040810020a180602060705030c04080a05150105040204031e060207021305160e2d040c02060f0708011a09041401091508070815 70
    0x2541400208204a86140b40f88040c60180200c044001070804400f5802d00041011440e40d26202850040c0c09a40c1036010311100140d0b903003981e0540c02510308008080c05801142c000d6030550040259504600d084c550142081c02095a9202a20010b844103100361181a009002c0107801001c0086c07030480c09070000b950400c40131050396151079600d40e0010b044c10041a401c03959500251050740300300204581503409450100c40441c034040ca075aa41450800030881c00e500400071600500062100990584030490307000340007090302c40c4000c400c000061408443c114010011040072802d12441074020020521000d003041d80990703580540c001e00d401e14004040e1215580302d0702441c09844500450050031b0140d0010800703030404800d070042c41000103041340c0c01c005410340104540a0005c0300708140c1c40082040ca42c0d41c9505402040c040c208114001560f0250280000f909006507070004444002805008621a80750740240b40c5582c04d42c0320300201580002c1e400101d444000107101d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 320141528 1250 320140278 320140307
    0x10050a0809240403021e030a110a0503070c0801140403120209030f030c0703030206010b0901140a0e0d240c0e010e03070801060e070206090106080703030507080702041103090f0f060106 81
    0x120b688010005507400001808420381248441c0e09007803008041e010805260341c0340200c610010044910078180e540d03402542c0020041201e503503086120010b007400031a803d2500a42600c1d40c4a4540c01c000c0b60401007846040960761816500000780d0105814041c069640743d901d040d58a14003822500c00b94100ca4051541400340071a850000d140c100300504e0300e040f140c0c000e45001403540c10041c1c28120142e2060700000810002c070741240e0323403107800ba003c80e460500340c031904c409009030215100c105a5403a6900007001c1d003c00001e000c1d0582803101c84c441901038000340031b0382154215060340c581807400f10110b202d2020b4900c40d503000c0c1d0080703041c1e47c001500301c510090352202001d007503d07040c1e8454180b6420078024040301036410300045621149c030130020712400c1d2500e81100e0351103030144805030030004049141000c1112034011603500a80040080c020703110400f02c92500341d03005a462490071710400a04910301c2c800450030456a08202029020030381c40d00300d0a4485420310802c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 320142778 1250 320141528 320141533
    0x403020c2701080d120b0f010503180106060c0b06041a0f281401170415060902130e0a11070b09031603020c090c18130f0c0c060b10050a0809 62
    0xa241c9140781000449000340320200c01040428524000503042010b207060360074006040600ca14015201c401304482c42ca1002e00e8210380d03d98031b04c450300b842584a0480070300c00b9401d00c400092040c1e84001e611100070b0007140c1000c003039150882044226400c4540c00043d02c4019480703030006107024042c0351010701c1d0140c05440000300070001e4207e0005602c034056980a61361805111080741c502940300c0d5910282080c0f1000d410602002664400c000d100501d00d140900c988a1800c0c4590040e030018071561005546481d18192000603061250142c083c03100d80f10b0002410140b0380740100d21110410720001407801c0940c0e2601d000d8840e000701800d685100401c0260440305202c129484a03a00a80c040c101c5410790070104076403010090020080044180400310b4980c0703048143d0740282c03074221001201c06819840755405807a41ca00e89981140c60035481c800701c2500040e10401c151700c181c1c0100f010310a400308026a44c1c01e800020300001d101031103a15062801007210f2504a21100b04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 320143884 1106 320142778 320142829
    0x5040e0406201b010510060509040203130f0b07020c04050606090f010c02030102040803040f0506070c050d0c030602130810050103021c02041103010920030403020c 72
    0x4003411456550400002d900d22080400140400000419072102c0707180d00800541003800241c001e041d42040000340900000c1c0c203403081a13a07100e031031703950509000e0780a0200039000100405800e03561525040007141c41000c41000a0380300300c09050007443d006100a003051510314581c6e0107a418142030010503540c6070b080d07640d140c4083c1c4403c103c0d83c0d11080101d844100d9040e000e034041d440080e000c281d00781c000c002401610801411018040d55030401d1182c00d116000c005444880500c000703010038940703c851410102c1c01040b40d80c40315912500d5410880c1d02024a000b541034154000f004040c2c41031003080d050100300c10040016600d15004140300340000c03003096030048038031702c6850215955503001441d04140a08010741300c1d81c4686c050002040b44081071180c600d2248a0080c03207440035001c07a0721460303065020788402a443c001b400a2100d16029013000703015481c1c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 319964028 320143884 := by
  have h0 := BRFrame.cov_init 319964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 319964028 ≤ n) (h2 : n < 320143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
