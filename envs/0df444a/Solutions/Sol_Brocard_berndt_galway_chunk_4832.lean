-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4832
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:53:08.405177+00:00
-- url     : https://prove2.me/submissions/da3d8582-ee8d-489d-be2c-d352a9d129f3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 868884892 ≤ n < 869064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 868886142 1250 868884892 868884899
    0x72301090503031201180b1305150a0302010f0e03101b1818020d0b030a1101090e160f0504120308041415011406041a03010305010e0303010803090d06060b070b01 71
    0x61000e200c07900894407941c81880058411110404a241556030300c582c103d00140a107140240036040d0f072030001d82e22088860022100f99001e900141c40784168013060300441d206803092142c4c00c040c5001c003900040d4007800700518540240703603881c800300000c5c0450f03005a403410010780440300c62171a40100c18481e1070461078410362181c0c070129500741c2040d0140580d03141280c07203220070003804166010300d600829140220a07259001c03000d102006810348801511601e1301c4840c80d0328500341300d40400c960303403030100d041000c44550a11840305c10f02c0d51801c0d100a0a001d441c1c02c80030f1a6020100881044007040d2100104840c00f0300900c2500c0d407100b5402c003840c02c042c100c01240c0d18209107900c401004407440d05014240b50442e400c248280341501e107484041141403040da008981480321001100d004120420010740c1220302030300c004c12800e1185103495850341300a2048401c168414428090280750485109020a100302400108107a031480c107595142c0050b501a03401c400d9440040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 868887392 1250 868886142 868886147
    0x80604080c1501301b09060819110a030206040b0301060f0c030c030e040b0301060f03060b0a1d0c0415080a0e0102210415090f03230409090302072301 66
    0x10b100c80040a00d0392100d6041500100d02c0d034410240b50401e090030340800d0400f42550306195060706030420002040890155580c000d100110f101d140440303450644002070038600425001210044100c2442040c19103440703440500c0f850501565020024160000060b9107110003000109060300b1b140313859624150019240203407524a03001401070390003107040042e600c000c04640240e0305040080506140b0000f040040c240d272010b0907019860600d0106400d100c0b60107200480e8492001032028035500c10502612800e00c1c4124200801d1a0b104c00b60269401c0082c2076015414084860901c0e595210031121140d0102d01c0101142c1041c0c10300000513818007481304015030f610000c0d4a03000c10340b200c00e5806400c140055030b06112200201d0708001c1c0c076028004103079019201c00c0c8000681403c04915517035030700034210b0124068103000c41c1e150040310303c1d0702400d50f001111a41000e217072940c0300010704035181c01141180114040071880308a940700e0440c3e880203400c091201d0313440d40d5001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 868888642 1250 868887392 868887403
    0x90d12020d080403090b0d060b040902071502040305070e090f060a0c0e030a080a0c020f100206010e150315040609120f020d020303011226280509030c0415080604080c 73
    0x3070080104a0781008003080d00120014203c68136400c6941d669980703840000c0081c032050b007240020210001d40020203101a03000744c08403a00440485103100c03000350b400d02c1207220340d100081c950b4010341400c2002d40c02900100350b011001000351032850214021544c20040d0845615504554450f40c602c2010780c044008402140158018800180191100d0165014030003940c000c001941129034115110003a803801c007103c01030100e06150b1540b02d4003030745564090040d075440c4441040042d0303600c006010340070752025001e0080c106010352141e000c00d840000910940d0b18545403407141c00003c030b403070124003056071040d41c841030741c800c000500a050005031022001158018401800902c2c042c0c944443c01071703404007103a100c203a80c06110041004107c0124104200040754002c81c80d032002124071000060420f08804071080c01c80d05480601455082c02d400d030b40030240018082c00c155000d52030b000c801300e0000345015640c02800e0711701141110102e8042c0800300d070075146440308012 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 868889892 1250 868888642 868888663
    0x10c032a030314060109090b0a0305030310050102190c05040207030527130903021905151008190b070305150a17100903300603030309210c0204050c090d1202 69
    0x262a0f8403404c01c0c10000b003c5142d00d000310034542c1d80c5ca2150200c81d581303800290b40255806026240c0b00c0c50840480d440f00e50580c40b13100c0c09400380700d10700940503050728202c020843d4400711b141202410a4144002500114402c40c184441008407640c1c041ca40f0580e00d840121242c10403107604040402e1088042d28038400c91003035410000f00100094021400390303100fa6020081c4d050045460410510704103074240c50b484616620b1080c0706000d9440001070065806280458420840c02c08051010780a9054082d055955650202e480d0754402d03002107810540b0208051125000342d00011074141042e445800e000800e040805075403d400c0c01000c062094100c01003122000c182c4020340000c1c20194010070810a00364040780f0680601d00c1604d02c1410100104800c40d100d16016000705080041541c540300480e00c000d0544244444c0d910b08015a907445c400e00140a41c2400003074080a05080c1d0010410702a2120039120390400403004c50282d104400701e4104418040e08110200f01c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 868891142 1250 868889892 868889921
    0x81b0c0a060b0f060702061c0606020708070506070c05090711010507210605030c01050d061e1805010b0901030905071508040c0807120b04061b0503190b0a05010c032a0303 75
    0x41c083c00760744e44c2c841030f00d10241c0c064400a50b101c8203140082c1c055840710b803941c50703210b241102c04181541d00146050035240804100c8110a4840b401c110140c000d0441c02803886800e070704240400e0174208a03043c1c0000290800110010010181c582902c0003100c0c00c00004801002e81c510208045240581d40460680100300103800c2201207500d440e00d00940310b050100011320b8101c000000d038002c50041898250910391000c545000c409600068822084a119601c141e00c140b9a1503100320345c100c500c0c0013012803828031340c100150094000904c00740c43d54090004001104841015403c07080c1c1e1082e0388840c000d02c1c15150066124001e5000070080d503201c20024405207044080070540560842d28540301c030f81e078501d440405040c088141d00c1c4210b04440224100a40020185000d9161083c070f0345100944601307101d003121000c400450303001900d03403000c10107940549450f03c08140640f41000c1c00907542500d01411401c9522010078540d010600b00e02410782c14800c00b001e694401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 868892392 1250 868891142 868891159
    0x180c140a090e06060609060d0c020c0108070f2a060f050103050f0307080d0518010c0e0a120c1205120310090609020a080414030c100605041401050907081b0c0a060b 72
    0x4032100b03694000044c80c45014010020b10011343d50741e00390984e020785000c000107102c07a649411000b901c807500da03510a40800c0107030020400c0c86010744091040f0b038100c7e07514903002c804030600f1aa07000141d241c042101d00303c1c40e42001c01062640c014807070300000410004c40d03254998544149002800000c1d0300c45900140120b8000403641030807640e1041c0240e03c085802e03110384420582040c407600d2214142e40c0380c008070080c0e2913000000c0103201c4c8011141c20381140d81ea00e400d040400c004900082001c450010700740b1500c0b002d00c00d070511541c001c8044036500c00808040003402d40c0140c41c444256514014108581c5056000300000380044180039401c0003125000504a0100074000034800e40c03d0329614a269081001039a19404c120f104035426a1408031058004011900031103008a045c026000083c085142240d81251750150041800b075075104001c4030302c6800500901940c400d01d00110700d5841c00c00028188242116001c0e086034429031500e40c04440c00c0001d000d020319402c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 868893642 1250 868892392 868892411
    0x703021201090b031204090c0305090f10020c16120606080c130c0c02031f0e030c030708180907080f06030a051f0f06090b090f0402090109180c140a09 66
    0x18810190454101c040b01103030800340000064107007401d48800080340c010100740024400c0303540d0004881c09126403410051901d03a81e040c0c070344480c40d0040410b80c0758002110840c090003a5070050180b03011200c1500c000f01d0f20b01b00000e00102c6240d001d43c6601d000e1103030410030f01c02c01c1d200303000080024200408140c8030490200300c5041c00fa040c10566259924104540c06010f034000180c180d9008080d85c0d15110380c00507503807402901610941856142c03202c1f4141005000007103441c0004120015410007a407551002002c0e0722400183c18141600c000b1200c258403560402c900580706501c82e8000c03498003044114090900030100c502c40d1b40005183d10104002017100440c140b42e40129203aa032645200c108043c00f02c55038550200b51410100148841040c0d00041107140e045504403d6034a8140720f41d220540c003560041d50054017080108940f2240340d000f02c1d03d140c1c503010701ca40c00302425162400c0c4510141d00000f00c84900c3d8030008440d240c0582c0c080040c0040b031200b0085000c0c07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 868894892 1250 868893642 868893667
    0x616080318010905070b03040f0c06080a06050103060317030606070501020403031e0c02240c1c020114010b030f040f0b0a1b0f021c23190804020607110103180c0e070302 74
    0x5e151080045420b800004a814081c00004810341250000c51a00141c0c0d61010010b0560100700d91303980e400c0c1d00c1c20300c0c089070540c400d0003108101c0c0c0d005001c00329078900c0380da0400825400030b841e065204004004450001d102170002c0d00045029849041030115103585a01082c0d00043d10b020400002c0b410344401640d8030460a016603501850703100e9440d00c048180030b0300e07101e441315100d882e104a01c0b00c442602441e42d4204d1140c04540c1c000e00000812400400040c0c4083c0908080100280001081c42170340c082a5548079005420130007070100d0580702d10b0140881920541c0229450f003100030380000a800740c0d85000c00891500e10107900d55104000d44032107041843c100000b050060400707150348548030240f100400702e10003101401c0d45408401865000b03d1040840954400c440c071052405a540140b150781c024040524104071903907101e02c29078089100c06c2c14980d41e582e20035500c0c1c40d41e2155a401d50b00c110414403c041c02d000701e004072a040205070008160040003070011122 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 868896142 1250 868894892 868894903
    0x70f29060d11030c150c0f0f1011040f06030f0c1b02010804060b15030109050a1a0103150f0f031509050c0d030c1b180902031b0616080318010905 64
    0x94202c000c00400122241c00641020a02070351030740d00801c440c02d52086048288010f1640151b94011194480d40b24489503484142a103044040e0380c00c03007080141d80034802e402810040d119460454905900d580070304c0d044124030f401c02030009545484803084144c8034410001141080d081c0384410055964800c59039052080009040141700c401007420481c460b0001d90200782c0c0200000d40503d4400c625652a030402d11800750a1414800483c0102c1d18171310803c228110300841000521850100640207000850500f00d80100360810004441d1800884407000e003050f40d1645007036501d5418982250070346081040503240c68844041c00090b80090800300003101920000c1c001e228504054989442d88500907046403d0f00c40707180c3e07428890803125003c1d5100c0d507007141440071400b00741504440c41d00780029010780c001d4060000d00800c01d0329080b180c06008244910380302e038410400801005040c8116013140c40482489401403880d400403016a040600802c45011b09880d4580d444 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 868897392 1250 868896142 868896169
    0x2010501030b012106020304060c17090715050903061f0e0112060c141c050915010b1803011104151103040308030402060919360c0302070f2906 63
    0x1280300003d20066034500390006213000e60010011500c030b14060611501906018400c200054600c00100c0a64000f03050030074010b80d1810000c0190b0703030134001401e03500c200380580842404401e00c0661800d941c01c20019110700b14161400d002c5203200000010b0840198210b011204070110043c080400b480f8111201d040d0080301c085015440b546d4269450614442c60302180b00380080d054009200c406030840203600000810012507469007501e545450f04c0304d142500e001c40c103000401203c502140584001d1103d003c00c2c800b90310442c800207085814030100051040000f0500300700700c80d51907004a000505900b0030202e400f1a10540545038072407404020300c1a20040040340964607800c040d24912030014100e20f100000004892210782c0381403141003100601c00f065514421002d1624000003a09030045070301d80800f40541c20003408030340c8201401c02d6400e10048001c136203414900000d01d8042c6081c0300c0d60b080e400203050151032800c8640c148800c0c503181441502d88511601442c032 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 868898642 1250 868897392 868897409
    0x3070809041e0e160506070209090c03100e0c01020a050709020a03020702040906021c0c200f0a0c06082a030a290f0a031e0302012a0f02010501030b01 66
    0x110440c00d00000c005207500c0c002c1440400341000c0c5614200001d80c07102041d401110219098a007484e010001d51495601642d90000400d00044c801170908951050300120140144c4c1d10320940718001c24a010b103903201030050140c07107000303801107860280b0903007400310002c3c8082c145c07014154403416621021841402c0300c046d4001100003420b4401c1d81a5044076600900c2409500b01c01e0078004080e400151443c1c000d814400c201c03000072000d9200d0710300411420745030600031000100c000e0070601a420320f4840c8501a2140103800c44905208404400c0d226008803601d40e0304000703004003040e1000704000602141c0c2e680d150414034400e034000f004a41085039840e902d40da1949005c1c040c000720100b089002611800c012587c1902c2900790030101015a20300500300c2c007017400c102e100483c9100c01b0700104600528502c1e41084020706049207802800041403410340380340024000c8904103e10080000803049041070f40340c1c440001e403201e418510090000f0f5041d92602c400b09031042c0719000d03d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 868899892 1250 868898642 868898647
    0x703020a03021203120a020403031b2003010e10020a11060112080a02030910030c031a060a0305090a12020601261e0114040605100e0103030503010608060105090907120f0c02030708 79
    0x3c41c0300e401c004440044101c21309040c3c0600300260924007035005400214041581090011480485c842c8129a0143c0085180d110702401d4004000415512800c40c0d8241d500e8056550302100c0802c003081c071103040c01c500140c0d24072109000a12842c646450401c1507088100104007080c0c185801d4007215400c01c1c42c5582d56800c95000380d26501c2a1500d141d0010341c0034000d03d0035170382c01d5803001c1c00c5490161028071035940820b4441c000e801f90441101d9002d002885000c081038403070f5120a510401680441c1c6515402c0c0d1126006014580c110034010791181005100900400303403105000644a11103e1203145c0c924002030301c0304001078010403045290745455075454070075001039075160a0a0120505400e10b401c040020f00304c01c0721091800425448005000c400d00d4400c14126a01691440c2c21642000c03002c43d4529000b4146030704004080c0004a110f589583c1030704d014001c00d45900b1030542e08082c440c0140d90380081c940318140e1511020031440c030303004811600c2c547d0b40f02c0394040d07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 868901142 1250 868899892 868899919
    0x8040305190e101701050a050d11010504051e040b0607050303070c23030c120f03010326030901090201080903090325032319020f010309140d03090201080105030703020a0302 76
    0x550b1441c20ba80740c964840300c080108030305250885009040e036001c80342026000d82e2120240021f05045200e000d82200802e511701000c80c01ea030082a0b68101c0514100386007507503680008903010700320500ca1000009036600023040d0710305449000e81100068940c0307800c00c541d40d22070a03120300000304a10306002c845041c40d010004c00c1c07440c5140100660301000c3d04031040c611040d540350440c0c86c110b1414410100c4606090001105a80110007951005451682541d0f62803c02408450307629510991020041e41c212003140007441c0318400d002e0000860300640e0000400d54140034000280c55002007003110102d071804a0240c54a00c004140005245250300d4000003401340c42c3e202400e80c2e0b502141c044e01c02621400c2c10b10b080702d5804201c6142d0032801640c40b00c00260088001e5000700b8400d036035113032075009070403141007240a046401e001c1c490005c11f01d030410139002d403440c001994031508001103680200d2540e000d0081030b0020450541958040341e001612130102a100703c03002074264 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 868902392 1250 868901142 868901147
    0x108040b06040e0118060b09060306041b03080403080a020d0306300f1a100803090d0f0c0b0d15080303180a061104090c08060906100306030602040f030b070804030519 73
    0x1d00d0328251100082086046402064041c50380a017011143d075800e00c0b0fa00c900c203180500c0094010000240034203103548499032881c01690804014490a81c8030031000000306100c000034100440c001c2d03066594900343c0700402820054508252070a05142100038000845400c072030401c0410381040d0102c00c2c104c0904c404400303900860009021001450101040003284440b6224944142d02051402e0300e41601d6a5505a502d02421010350320138013552000d80f41c0301101001d00c81c020004040303184003e49400580300d03096081900314403800076040d0031000c020700c02d000364921064003001080e8244410305d07450380f0000d0104519403c89858451070510700380140c1914a5000c0d0f81041094240d006403d0f003a00644290b040d254034000030f6501d041e0290806922540e0000e2401d015075a0f5081000f00c00d02e001c071404030805544e5a0003000040d964401030020700b400d001100740e0203266141804030044014a01820010000c041c0710000b42c000341520142040950740c080e1103100d10808 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 868903642 1250 868902392 868902401
    0x3120e0c060310030309060219030c170a030e160308040902220f0603050609040b18100c11010b0103020705030301210b0112200607021203120403110d030b0108040b0604 74
    0x3095021400100b84011540503110910889109850700d4501640d681826a00c13100810302d12401102d00700040c20010344190072107007295108900b0221074000d01d4103450032541005110501082c4e40e0314140c207103140c00700710313103c0d840d140c517170603000b5032070456803000d525020314410a80d00075000704036034082e07038441000c0d480f0715084070803520115a0382e0540b02c0c004c403105104500110b0301d0000801d00d0340c02d00c1d0b01122b00c542c1e001602107441c0d4070740482c0701e0300320641060440854041d1142500c401084d07030094410503601d42d9103040c15644460501800c480e40b00d038807541070510401c0701000040c800300580b411101080708448649001007003030918412100b40017070901441c9400440c0080110010b6080b890181c00610303480152441075103400c00084500d135500000601c841c000501c1d20352200080c02803035205581c00d0290104140c00000415101200803680181012522900420607440c05590a02c1e050162001200018200307650241016200700d41c01c400060315525035411 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 868904892 1250 868903642 868903663
    0x6031b1305030111040905061507020d060f060609060908072603161a0603011509020703120c05070512030105060403080c030918100902070503030c070f080307030204031403030403120e 81
    0x24040c2d41c4c0c0b00c620012942d80107000ba8804140307050b01049007414100070383d460350001c0204043c54256a60200031404143d1507085500766100c1900d000401e4060081c42c0080045031034601c08942812009070254460b9002500168000c900412240300d00c014a0300f545d031001d220324201c0c0b0742c8079400c250071071080c1480000782c40c41d0781e04424100700441482c0d4600b0074004213601030b2916103400301401d031040c03a000c09400b941e08a0042c0103108499008182c1c2500c01d0510998941c400c02450302034502c40348000002c14001b088031410f010b8240030143c10308000d04132161030b540c18100050803038021030001400070080811045981c110070001c0f101c0506004011801a10b602c0c50351b021072a00440301d54041c80085000051900254001d0300c0d000796000c405941940d444040003034071a04140400c0d203c01550303160300404038140034020750044c1031070b030380140c1d581d0304506205107154291002c440e042e9000304104004039a015282003496080340c400800d800664000480c50f10355000d2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 868906142 1250 868904892 868904899
    0xf06070e1309051c021c050a030e010515090c0c1b040204090518160b070b100506120601030b0a0e24100306080c01050301050603010b070302070b0f03060f06031b1305 73
    0x11526800e1080010316400c0e40c05462035103511390345040300126207401148240305400c040d401c0c412260580a04003401c0c1e00c450525001481c100c1a0316243d003074503001d48440311140c00852002c0c510f4105021419441140108001d24044000c41d9a82e96441142042185510040d6200d4040d40e91501111b00900e007a0740140220704085d175170103d100803e160060054481c400540d000020034800c00350032500314050790f5003480f5158aa903448000d00610b45841f00125003400326066540ca4040c0106049009803250b041c9443d40014040f03821404100d88508c8441d030b810098080c0d207a1aa950019000e09401e07407540c070030a00309110f2003080c8602540040d01a89440840398142c1c800f00454100500311458045913070010340f8a4407081c082c02d600301c002000140200c20b0000300400030103200348121140503585510014854120360006201a5030000909c03065151484480800c004200d52003455420014a03700d182421010110030014000c03802005034210062008010880039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 868907392 1250 868906142 868906151
    0xb030304061d1e180c0d0207291f0e0a020c010b09010b0a080109020a1b03050c07061205090106060e1908102405010f030203040f061515020f06070e13 66
    0x3501d21800c01494283c80790180c800403074030242c0c404034020810300421182c080075240408418501003e03511401d001c3c0c81c00c2044018540071888120403540d442c84095000540d9401c2030242c206405c1718517640e03e500e044002c1c1c421711000580c070b1000e03900600408001a96840c58401c42405070005034441ca82c4048840c000080d0b50744d0240c0204844440f945c3d0340b05180c3e8032607034241d04030701407501028009090045030300c001400c6d5400c1d4000e003c0c0242041400c0841c03054070300d4a00707000c1c0e4102c03000041000d04840b2200e00b260040c280c010705000000d01880f8280300009024009180e40248912451501c84034040c1ca01c484440142c81c55005035100c1e0160a420607010b0f00c10f481c0c02001c40f4108042a040141009070b0712415910305a6a04a142c8a142c0c1d04402a410180c001d1320803019181c5130000050313032480b0f074006281c0310b0b58840b491103150814036203e08d05584032407000d540000070080d1818001045035a803085050a00360030441015000c541c04c0696482600300d500d140 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 868908642 1250 868907392 868907419
    0xd031d011406150313020d1403180f101202160506012301090f05010305070e040507090503070f0e04060504080702120307060b1c030809030f180a06030b030304061d 72
    0x401d8401c40c81031500b82d070000c0c00c0c5581c41502028500c0202c030241c8072401c20901c8140103141c2094421041402010200c03450808400e03824190791151020301c0c40280908107102042c14209030070511800219190800b01590040c050003403038818258900045d800103006e40307890146244c0b01c9000741c0050849040b50b8440e20082256810485001d000c0385c80115100c03601c1d03108007552010341d07c12900d404016490400150003909001e01480c003840003007400019903450300e00c1100c0c421460b654030a80120f240c0000c1c541455083d810074590301030b1005084c401110841444d64026a000900240e00d548a0038005542d0144000095000d80e10702030b614020138001019183e80d90094000f000050001e60802a544462010130081c1310529100000400d01420419910464080c00d036494028140c80000886e0310003245a001120741400e00d20050810182800160075903003020800c000341e00300060760340c1c0101d205143c200b083c076004801211407003400030054160007070b02c1414407200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 868909892 1250 868908642 868908671
    0x80c01170f250203070c050d0c0303050c1e0c09011e2d0b0c0106060816050a0309150f140c1209070906180b03012901270510020109050d031d01 63
    0x83c5005503606d00305180040f803d807511b030461084255103c1c00080c2201e255540a80d07080c0c00a9100355554090140c1d145c140300c0c03100c0c800d00e40031004480500a5010a9010843d140106030007000350030030300e14901c10319030103c51100815207080e03007507040201c4600c481c0d201100300030002440da005100b500c00114200351f00007a0a0900c0c0d0b40000b806110f07101c0340100d49a400840d802c007070b4000d40314042d140042c060307030042003448104d103404a03071100140c40e2040100d030806001c2c11400d9607035250408000e000d02c0394020440d0341d004c07810b04900340b01144503094050b262706030001544120110b659840b04101c1c43c2c5c0101510742013840307299603d4440019101c01c1c1d03040e401c003030760078004141d60520f018841e0b02c2201132406001c0b0802c0180c20320594082107a0003401c2d0500010b130002d0310740019442d074800550070102d983e04241c18144401d01100d2403000d81d8050546e0b04211442c00010004100c04103100b0680c44c0000305030356911084100c0c1e00350201448002d51a042c5140900007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 868911142 1250 868909892 868909897
    0x40f0602010516020604080304061a090106050d1d0a0215160807020a050603060a0306020901021e0d110a08030406050a090204090c031e0507090b0d021002010501080c01170f250203 79
    0x300304801400c40402481c3c000c4ea120501201c00034000c41080002800181c0f080d44180d695058030341d0107150084201c000301e89820001c0e0001c20101d03c0c0072500154072500c60291080c21a044d111002034072004040003a0740701301c1c0a10081c0304860041d00504442000d10a0301c218200400c0305000109a605112840d0b1f1b0203510180d007e0301c2038002c04140ea05000045078001c200260005899038a10340f60308000350003008180381140100c480844141d10b2184100006a2105000d4031040342a0f45c809007022078004403504098001c114480e000c11f110317a003929442504804003244c1640d5001030140100808040250f10914000c1c40ba8248a218400602501d224814902008240703006840b4007800b1aa802801e5612201040c410340000d078000c00d08a40b4050183d1600340c000b680060042d001071900c810041c1c0d92030b00100000c040800c0048281c5d071081c24400c10041920700f6103c076040c0010980160764a00401040310030404030724003044003c90300c02001120f01d940b40025141d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 868912392 1250 868911142 868911151
    0x628060914010807030e0304050406060819090b07030c03090c030b0f0a020c0d03090602091f090b03060904060504020d05010c03020406030e070506070209071413062d050c03040f06020105 82
    0x1401561000c200d09070021401011180c050312500c02c00d03030f01c0d80e00c220040c12416008882d503000510000403030307032a107001b2007025291a4955102070b01d001103d1181070316441410303c06840c2000940c901055600520641010a81c03901140f14084444142e01902413903030003c0ca0580307102000070030720200c1d0311480d00a2102a111400341d440e4034a104050307005800400009400018070214110f0081c1e010b0101c5621a00000d41001002400250340c00788203003188162414021405405c0b80e4041d0004015100c2242c1c410b003942016800300c3c04507070000b00020314583e60750010905660b075496410746071560240090080804004009020703410600c12100464186001a102e43c01c0104183d410390f04054021410402203800300600380601078498420300c81c140740302000310101d0400904004102180c03060070f00c0c1c0340000007400c0c00c801302e54610244200645140d80c8045c1c6407400c004c0e0341218944507403164201c1c1c614900311311480c1c3c4400e940b0f101c0c5120019040350103400981c400d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 868913642 1250 868912392 868912397
    0x3030503040804320307060e0d32060901180602160b040809210d0f05190e28050103020903010e0f061602030c030f1308031606051e0609062806 63
    0x582c90380405060b51b4101e607000b060085076059106015900b441c0c2c1d88054260301a03c000e10b0499072456849921a00390031a4040711800030302580c4811a0801105411810032030003005982440c0c5a6249000d0b181c450040525400007000c0301c0f00d08003d03441d2411540c00071300400c46424103141c54035a6a11081405014003440a00721440301b40e20603421004591240c00f034603034600c012404540d040882070550341403140a00c9204410021030403600c01c3c038052520b035a04003400080410103104100314403d41016501040130040c00301c0a04650205c0f002030038090f072924401c40000340500f0600d071032035070144510581688264000554907000d5500040324101c0c900d8000c034201d889105050300a045984200512010082400002c144540b0008404e0480c2616400281d0a40d072007004102c806204c1500050144074652250b21340003130754214000c0c3c000f0305141c0703071811207000202420301c103804a00005402d6203554656103410218440d00b00d244c24610038040803060918000d2000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 868914892 1250 868913642 868913729
    0x603060f1506030c051207170703051512030d0b010525020909010e1b0105040902030406020d0c0f120b04020d05040b150f0906060c0f1006210c03030503040804 70
    0x202c1d54000e00c1030720700c0100181c3c0c4851404400031741002048401801718410840d62000c409810034006460500a1245035000303d8141040c802840c052428034031054440c5c0c440b440a106040000001c482185c403078007101240203514800169030a000e01034a0020f640b101a018080014442240040c11442152100d2407a10703020052422214062059046903101c1d40d1440314103000326a414101c0441450954034064840d80141c00366082507030101c0e907042d008681d081800c1d0003030103502007842062401c40104804440010080308e00c500301755580d07542d64801c04045031920b404071050742107955400d1000f401d1900e403034400b00804807006140b5064a0764060b460340352182d030400364000020640c58490300c030042044440c2d07000b6001d9803028400d010001c8a040414040c48050700304a540c0003c005240803480c11f80b201e0600d4040b210281000c54410009054512a5043d06e07007610b00503449580d01d1406480c1441107400c180880d40d00303689030480e80d180603c00780720112684801c490 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 868916142 1250 868914892 868914899
    0x60e01180f0501032607080d020a0e010e0105030a0e01091b06080a0203090c1c06060801200708030109091b0b03150306060a140409140a0210140d09060603060f15 71
    0x702220028013000703044c0032405007600b107074101c0e4120300c1c8003005200e180e151414641c0c1e6681c0e10180c0c04410017401940d0082a110030700c0380c0145410310350752001c4c00d00344201000040001e002d0300c001820210b40d41d0b81d50041103c044c000350310040342c1ca5031103806184095659500b0300121340f00e40c81440d0004141e48005028140240252405006031f2030060000c00704007820007844045c1c2d26140c041c800c1100c003c0b01c0108905002c1c110082007004000034041c940b40c1004200072482024003d035180081012000240384107048a045130100794001503049483d24180f9405401800650041035031104007140455a2000642c020503448950091450207041890303141c0004441e403543c8007400080c10419108188105131440d0002000004e0a601039610041d004e070ba042c600d1041503000400240c2181016910034120314050b04010040741007500d000901e600c2440140d03440591666288010005590401001f40d6401041803000b0251450003800a208800c0c5040d0103004285001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 868917392 1250 868916142 868916171
    0x100b040609050904020112093207120503040e0a0b0f0406030803060f040e01020c0309120120070804030b070203090a09020906090f060d0501150306080d091701060e0118 74
    0x840032a54240c403001c0c809031801c010040e0b45000188180d041c00810010826204101d21078840d23001e20480d050311828030410400c81c80e154001039907a1117506040d04d170a01c006c100285803801c031401c8042c0c900700a40780b45005421030165500604000841e101400103c113050303001000e40074400c0d1070610441c0750010401040e50000e20018088503420000708002c1d080003015001240d0307024002142c0b0f00110b49400f401c99000207489040c54002292100c110310f041c0d013510842c100c50100174403d41ca5000d4881030200d1f690b030010505000006510300400035400192401140c111180803628545020080d443c1c0e405009072074032a0140c1a0301186c2310380d0500c00c3e15280c07040a00f0300360400c1e070450705010a9155001c0d01039403001017803007183c0a0424901034a4043c08619181105010b03001e1405400d6482c0c0c1d820188468200d0310700741e152503500403161012240c0d1861100545207020980a0050007035400c0442d010800c08004141100a03c9041480c44154607081005030644210b1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 868918642 1250 868917392 868917397
    0x60b0a03020d060506030a08160327150e060a4a060903030304081b0606010507081c1a101119031202040e011a0315120c18100b 56
    0x1c1d40803004425034800f0412580c4110350005005d0b0844c1c580000c036450f1a660743d0001520b0002420703407003200c4010141d000516164444280c1180414a45880c2c1915400b01c260b000720341a0b6090a954400c0c058401c4801400c0b02a0207450507035143c100134130092002071802c141081a5081d450036160520b407180c0c02c815a055000d44c454125070115041c45580800c03101041c0e03103d9028080c004855800740001d50080c1d10403004255a00704202003081c0380d01c503001d148283e40c0c01680c1007002d242d801c0401c807402d4a0344001610750718081d40322440307880030400e01c4144005290aa400d141c4041c043d40580707030024102e8007044200301ca0041118480001a8168034540001740605200c0070845080d0742d05e18445d0920660005102190408036040b562041e18180c0e01c200042040741c00c00710381c04030340300310590740249146090758400c0c0345405540c0c0b90901640300c541050000c954140681c5400420051070055010b0490030850624002681c4180d507640042400041610f6680d04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 868919892 1250 868918642 868918649
    0x60204150e0f0f030a02130b12030a080613090501020703030917090109120302010219020c040606030b1c1502120f010e0f2a0a1d09150f06040305060403020307060b0a 73
    0x1404807001c02e40801d00035840110400c1a0f0507129a00e90fa20042c0e55040c08003150050196000480e004400200011f0340c0c60280105042d41041091a003801d5020784c580303510400c1a00c084692a2956124000402c081c41c0301804035407000c1102c00030982e054001100c100d00820300c610788060100d41d10a4180b18582d030341030100d00201401c0090201442031651181d0181c000142088031203202030760412103001d001300044e00320000024092800e4803550700a0440d51038204000410700c0041000c946c40d03100740902c6040700e801c1c01c0081003000b00d03001d0200d10180c042552124235211400015007001e84501e803101104500210f800d1018410fa94403402c44083d5416142c4c80e6010032a000784113000c00008402da224202d4410400030030003d0005085075980c0e13003401800381d04001a4410840c80c2c2c1071040d0742c40b4050201e001c03503012844840c45811541041904492000200b031031045900042690049070100020b1580100282900034060402809103200c00410001440054003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 868921142 1250 868919892 868919899
    0x605100b1213021009031b0b04090e100f09110909190c24120b010905060a030608010603080403022119020d02090a1a010e060a0807020a0f060204150e 66
    0x803081e60011030030600320b40c10050040c1d00e044a515280c012841030421092400301160403010108100200b142c0c042e0389a102c0e00f0500a2002d00700f41c04100c09105031b10840b1240d584910001504000901c02c00c80fa4410f101d008000c00c240c603500d0b4a001d006404015030304a45209200303c0c80e42029a14288039004020207080144502c541c035040300c104001090381d0302078001d1404242049907c10070005110440717681240003801540c01040364103c0222806824181869003a0381e98010840106844046440035119101c01000b00d00a00c4a07501c040900d43c248a400414484428000d00c207590003950f90580d4900002c4c0c4800080c840784d00080040d5020b540c2c4410a4641103004014080c0300a00c0c5007038840d010f400090480d60140c070010790a41e520440313940758031030075200101038100030308020306204451f60014085019406100f0240030704c103800921101c0c800c0c4000d405203a40820324545240080c18004000d41244c050442c50003403081a000000e400b03010307001c0c072400004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 868922392 1250 868921142 868921147
    0x2802060d1104120c090e0a051f0908160201090b030f0403030b0d0b090c0405060d020d082805040e0615091009090e030c0c091014010224040605100b 65
    0x81580034018204803205203030700d4009200204061600f140c68800c02c0c0e001e101e00084090a2020b0366080300c0300701d00c0c425000c0c0d04c85144100056004902e50034110f00d0700030b405207001402030300100a020a814000c201d0704d40041c00c00128219091061800340c003e80e103030b0240e00e07119032400340320344015520701d41003020b01c0c000500044c0c0701e40c02202d000707800601511a540310565450356100800d482e03030a0b482e080841c200c4500d040c644180e503880f54003100d03d0440840d498020038038031001004040c003103540000d8180e50a1b0022066810949048200080c5212000c0c80c01086030700180a584021198000400c411389094210700869105122949261401c1d03c82003201c4840840c43c1403003407104810000841c40780b103200d050002200c0b8070103540d590010404c0f09042c05200407682e440380300e00c1c07024000c0b0301c001c2054031300079229943d0681c106403c1c40345c0140d10304404109044c07072801e00100b00d08003100040c18014019072044509000e81e8560075550020241a0f0042c52001c0009 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 868923642 1250 868922392 868922407
    0x40804090c020a0c030602090108101a030a090c08030705070b03150402090a0312090f0509090c010807020c102109052e05092103070504060e01110609280206 69
    0x340d4855010303925a4011240c0c0d440403035540d00c1ca4816241e02c2070310b042d0b5001c540420296000000d499006045d050b20350070203410b020001c003880c4d090300a40d0700e00ca41d01000040c0101c10907841141a0381e0410080d0b00000c0e50f03140c1441d6641d0104400b1102d50003421400294643c090b8241c038081c840d2280c0b2070b0200801c0c0010311000f9040700204035401740c505c01000000c1184070700d4840d140c21441e0340d0719030450b0a009507404100002d0340840d000b1100d450030000105004903d0200782502440c00c4502912905000c80c07402c03001c004030070b0348007030540c8108002e150840d2098007101c2e4040901201440045400340840e1003180340a4940e40021041c40c842c0150b680606040e100c0741e50700c16000b0040894141e084400481d40071155a0120a54030081c0d402124124001200c940c40b8610394901440010450300492165101f070204c210b1054800b68002d517800d141049403d81120501d01d800c10655640b0101135666040c0b0409030b50145803524040010350020740d402a100e180b50a84c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 868924892 1250 868923642 868923659
    0x405121207110319030204090612122001110a1106040b0105010f12060f06021903090504090206090913060c0203070807110406080d03140f13060506190603090b010b03040804 76
    0x2880080814501003000001c613407580080ba102112410799400684850900c50820100e8200390002c0094404010810001940500c201480d44c10303107161103d00d51210202c1d000c020704107800c0d060015400c100f1000d05010040f009014400c5c034591b14003403000e0000324900d803100301c1580e0240c081c400e600010700c459405003050515906a41c81c050f402a0030404078070303044031007035003040d5088211030f43c00f0428282e0403c805a4680c6070080107080b07851032650040c101a9040c45198052612961442c042d9a84d80d000c1c0c446a59014005c0300709807412200c500a02c42c10390100700c039030751320700030b0842c4560348004266503207150701000003442c2c44440d0f11840c00320344006041341c6d403058951001003a00707007043c0311000300b64480e610301080170b0b0402c10b0000e981103c02040c207244041c450b01000000f405100400b1b1030250400d00004484e01d41e1004150120340a03151140400300079103000501a5040d030082141c580074154800d9a41d032501051241444299405000c0010500080c44001d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 868926142 1250 868924892 868924907
    0x3010b13050a080a0212070f240302250203120a0302070209240f030703080a020f010501050f2b0c0f090506030c0a030b090f0a0b070810030201050f0a09120b0405121207 74
    0x1b003a010448040d1170b07a40b0240b180030307055608051349808920441030041542e140c02013141c08124101507003040500540343d41d5200c4841c1c2105034200d008851074003903442c01e01201d1410300c007040c4c802c0d030f64800300240034000e9400b447c01240100c612000003030304800c2c1d00c0b407001c0302c00750100c1942003038a20281c100300b00c1c00c8201c011241d06000d00340001001403100d400501e40c620040d0098180e0b8000410359500311141644603a01800c01c1440c01c40c00c907500e11503564190cc0c240e112070013044440c0d40c0030281843e0300200081602c8214940811088100c1000301c08492803042d00707010680e40d207801d058680c0f80212019801c158480c0b030920002c1c85140000d039010800c1d4080b51108000117001528189d4101c00070745010341e1060030310070556030125403503a0140c1c882038894070551039640003c100e4460340c0003109400002091344c000c210b2066080e5001030141d14051041c6403041c1c103101d180018203990440c0c451150161081511900340c083d01c102180c0c10f52000300c07a0307482d2001950140f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 868927392 1250 868926142 868926169
    0x10170c010e061e0703170109060b0301121a193602012109021206071d0a0305010603050115050a1a0a1106043509040c020c0603010b13050a080a02 64
    0x252000000482c0c1c21008030302130001d0758065a50502411111000780d0003110042e001042007a0408100b84283c441030000c980c1140c90404001050400781e040c0111002c40f5500700703012030303107960080c004000d9500198998155510314204881c005c0000c0491411880309142d800c0d110900703400c211983d540b41d08074500c5030700604140a1900c03054068241048107030441c0c0c56141d940b00041015400d00b04d41c520110041c1030000c0c40305e030a100030090020507410008002d120001c1c5a20903054441d100144020341d031040003803055907124903140780a000b080034203420010141c5000240e40c03074400b81000807a0303000c80c00d114642200001d00d86450340007012203404c0c0302c801240c82c01c00980030400c280c401c074012904401660030300d1844808920510f001d11111140c82d00070a014001c6031411202d01c0241100e000981c100c04d10400e9007000d604025a541c400d0000c0b00005e41101040c004000000c0011822520a80c80e403003000549005030080c0c0031198032000502c00142441c41c4d00f84d100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 868928642 1250 868927392 868927417
    0x9050402090609030a0c1e05030a1511040306060810110d020334020c040227030705032407020102040b0906070218011203020609070e0613020d020310170c010e06 71
    0x10302c500e030008685405e081032030450f0780c0c0c07000380d40c100300e0700600a039240000246841c0b1a46228500070001e40e07242007441e00900008014a202e0203542c0c503940c0882520714060784080c1c2c50780d9403401e001004098900ca04071407070159107080341100a5034410f06842d500400d05503428980c010360003c0c004e4100401c441225000102c4030f0b50070200800f0f8101014402c14005404d807200c0f43c1c030090130902c4e6042d03964051401440409803000219200008821091700300703034800700381200000d182030aa80c0c055134060003158440a070241c88068094401e410710002000c1544030034008074202e124a100f42c800c80401440704040310300e451401413680718001014a03444040d000c007404401c040a1f484142c0300e00040090404068051000d540c0c4075409401404602e850020103c1c001100206200c0c410a50140040030820842d030680355102d840c41402c545900c0d04d400071188800a41c0516090800310034484540014001420303081020f046e0b566030070708500300c0144a190b8100442c001c92 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 868929892 1250 868928642 868928647
    0x5030106050306070c052109130501210611030c03040507081204030b09100c0302030a0605010c0b06061b030a03060f352514060304030e060706020405100c03030507030b01090504020906 81
    0x1e00070742d500900782920040d0050b88c0c0e8264508201d213480c1d0802215041d0342c2031000412000c0c0541840401024800504030000b10aa02e440802444803c015100b40d8001105202100d094030018500c1030344928210b83d4220344800d25282d641540000f0030441c2c01d01040300380001800c0488654004075030750101ca0051064241e080c0a0b1800c0c000702c40002980030040001401060090000601080c203041e9000c2d50704d500c1d07080f00d4002c01071000d4040c10f40000e1103800d061900c07024100c00000003003643c1c0c94002c00c14000300a4800b0344075081c1c1c28440d000c4080356504050f044014205902210840440c42038056160541c841d12410b030300030300815142802002410044000441c42a9480c0f5445810640601c01d011007c02c1081d000b6601441040002900009034040070441141d500d61280c1c0246021000f81c803540c0c205c4c41d00420550940040c80b81c00011401240344651018001c0760381c0c0c80f034100c08841990050500150301002c0801140c00c2c258000c00c080e0402030040d51 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 868931142 1250 868929892 868929913
    0xf03110a032103111620060f0c03070812010302040c082a0d060305030d0c020a05032b060806071403100b1c0501080a17070201120234050705030106050306070c05 71
    0x4545c0040020420391030140200300d00700500d01092000c00080302d0b29003240e080c161800700e0b40c18010391f619000b68050001d0345d030b003481c2c90401c256403000b41d2200c0303d543d691081080c96090f8000a1000300d001301d00342000c0c1e4205501840b61039105103000010300e150304d407030042040c003055a140d03044203002a0401550510417182c2c02041701075402400110b0752003108450303100885900884100471508801c001c840080c0020048071010034840502100d01d17080f02200600362010004510b02030740c6000d0b000120201e0126070b4504c104601d0712100d42c10031054038091094403088481d95030490030b0304414045454144003801c0300054581f043c913044811a20580215003081e0002c8030300358401450202004900280069020340c5c41050609101c03990707001809408a03058020340050700461b41c0d8a5241210300702c186007403500d4003024409080315610380200c4e1104001034a050048000114140c00c0501843d41240d0000d0010806030744c5d5005d003280c54101c109012911405101c1020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 868932392 1250 868931142 868931171
    0x2031c0b0a091112011a040608090c1f0e0d1101030216020d0320150609090316031d04270326160f09060311070c0f03110a032103 57
    0x502604521065903803034074a90311841c0e0104c168400004102507294103243d11191009542c00c03070b01281042091600c0c0c02d0401410024103910158000000c8000c025103103c00301c035503800a10181c0c5a0800c2c4506030400d024482200000c0540032105004841003c0d511950080122082884460440f50314a42c00110f41c200100302c00d900042c240c54139412440d000500040705004841c1c020194a404080c06035000c1e00c0051030603101d244d80d030700051103d107020b008585c10320402c1c10f88041144480c1c900070305200814060001d450701410602281400c082c46240361611030320031702082031583c1e041c1411040d14000801c800308a800e608510760500c800b2031002c0c082c91081c07a9000546040c0103480d00d40c00340c418500e4208144c00b11014459500494003d0607145a403801040103a4001e10f44405403040c103c00508a80c284600096200900f07030a0005481c842c2c00e5400744403038041c04000290300d2a000c0070b000c03094000d54810480f102501c150000c4412410301254541d4040700c0c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 868933642 1250 868932392 868932401
    0x512011508060601030501051008041101050d020c011a010309020a050f060c07061205073e15010f09091709031e01020712260406020f0301061101050702031c0b0a09 72
    0x1400c05030b484081800030a603018044d0034050882550fa040000c68460401014a0005000070b0f044103460a403c00380d5074410380450380d03400084c40041d03540c2d80303000d14414000e01010307440b15070b04903121207242040d61003402103441301500140500103c604003020011a00b401541540d4020b4080020702211038060001c0c9008018584030b05420151070f107030050540c1c200a0480b01005412001c0395804d00c10038050703201002852414800c485c015842e0580c0d43e904c05005800135203d0656003410b040446030342079051310002004115580d42ea0641c002c10398034880c03c0201038940c2020394804a0711070b9009000048001030403034a11081032812401c903081410324650460750001400d07018006c1d5035a05242500c00c915110f050a00100e52400c08258140444035a07000114085001d001054055510301c9000300021680d0303503034560f00640850140415007041c0c0d400c090000b040346001006407400c281048103113461206926031000010203040ba246607110325034000214540741944074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 868934892 1250 868933642 868933649
    0x60406120309080c0a0e040809011701121a012403090b011d0f010302030304060e040e0f061e0f0c0912061503100209031b0d080c0a03032405120115 65
    0x1202c94007103051000e0581061000b0302200d0050b180700f8020040031040901a036070184c1c0015039142c540c0700c0b140048801011010389450030b00e0805001017460209050b0801003140320310030486298092649424199100744201486a440d034103511840300080002c1c41180c20403071400150f0700b01c0b641e4810020780c400781c1107991a02645a400ea641d14080b864158020a401c0300b0b0905a40c51a800030b0398a02c11406030000304900c2401c1c050305502d8540100f2101c107003601c1502c842188503000181c3e110b03011690f040419503070032030030016172010011041c050400482e810405076540d200b90004e80e404088c3d01034200c00401044100540180700844c098032004280902021401081503c0d2040340d6415050752841000080110303940087c8910010446802030800c4e01064000940305540100c0082c0444500161a0345036420100e10380d0440c500c240c13000c02c1804040d03140903102c07a406c00c90b10390b5144c00b443d40500ca58502015100c0322545100008580c640c84a2194100c0b1030440c4d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 868936142 1250 868934892 868934897
    0x908120406140703090209040201031e0f020a14030106020c060702120d0306051e030c240708090a150c060e0705100c02040b04180602090102100e0309010206060906180604061203 78
    0x28604801803008080c550f00b00702140b03001e02940c403260300011800c4070b004d080241419580c0000c0348010505103070b01e4150640307402c402c0200071442e1801001941c0700030221000074502c000d10291403c4240c09803030680d00036900500c441c04c040b000f0700589a0043c40c042c0c2c0e00c4070780c1c0184101d81450801000800644a69000c02c2042c07600d41403043c1c1c681c90700300c003404501c054840d08500c0e4a0019040c4020413088805980031440b004158010b50030600c0d0091034104000b49260506c445e0100801c1d4090090340c01415140e62203200e4001403811550b0740c40010941c0004002007109608000a06901d840c144c3e64455035401c0080c040307000950340180400c503072104d00d00c15807510b4854042c4102d01610180103104c039241042e0300e9032510b204000c01d9254041001311044e4403c0000340c1c07170050003003030420181d0b800342e0416540b07401c0502c020f801803052000003506400d0580c1190f001d0000030b40a5907020141c0d070703034212000e0001880d441e00141c2d216400960b034000700c25030037141c80c0241c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 868937392 1250 868936142 868936151
    0x703020c0f01030c0f051e03040305071b0308030f07020f010513030915140703140307050d05090a11041a090c041e050a030308040303090b0c04090c0e03060a0908120406 74
    0x200180702812056640711818545042c42545601303802c0154203803c8202d0f03240c401e0340d500c1d01022494010320b0008658041c800007100700010141c00000900c00540541c01c00111400c0c0004000d40011040c00700401590082c00418a43c1c80e510000366000111070044d50425000032641d0b608482e001c94001c402c65000c5a220400d160300305045101400640380f5403c02080d41407400303402500d61920700c2048460004400c01454442c0013000c41c03450440565940d00e04281d00004d100d50003428140d46041c3c503102c04201e400000243c07000041d82c2c050015402e01c01d260042100800351480c1081141e08101c00800441e62100b1030b40744580f80c41109244c88604012894130f10295070465001d00c46c1880e03c062144c1d66a2000ea401100c3e0b1615010409a85610341140500002e078402403441d103840d020701c229403040310081c10070354880d0101080010404070086034142244002190103410003c0840c0c071039895074100108072405001d040d45400e2038100381082650302100d065900b107695 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 868938642 1250 868937392 868937413
    0x8071b14030a0c031412040f0303030c020a050604080c0307050a06140f0405060105090411031e010b0613150311120a1a01020d0f031b0c020a0605160f0206070206070302 74
    0x84500040c0004040c1d009028507803440e41c8000412090340005000c1000e58a00ca60210368208944420695500c0c0101d03150781e513031410004868181d00040300402e05040b4481d0400c0e100103005a030241c1c11100400e82e0b5211521106840c0d4002c4250301d41d21300007005203901140c0c0410111550a00c510300005802013040c0b42160001406003a82d00c050740d0907018400401d41c000340050549000b11200701842d01d4030318290041400008409801d800340c0071140522440c54800340240650f40c2000707020382d000784010848148501020f440304107117607003000d01116914003103402410a1a00f030000388180c0b200c0c80b8030b0090b0042d00302802c03221207040403c00500e040f130007031030540001c1e4840204c9917880900046e44600d0700b03140300010001e10075800030009209030000c18181a80441940180074559801800002e800000364040d04202400080c81440fa070115124800d4030001e00c3d4a02e03d95560340c101c0b11620310001c0c1d80c40003080c40b0080260f60354100a00c42c4507c40d03001000015403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 868939892 1250 868938642 868938659
    0x607090905270316200f03150a0204050d030f0906110a060e0a0507031b0503010204060f052101090c021e0a0f1a130201020f12030a0b031f021e0408030a050708071b 72
    0xd00c0c807a050090701e040c41b1040c0036403000600c41c1c0300d000040b1110003507565088000b40080c02590700003a841607480104405041e08004a13684200e02ca6440090307143e107a010541d000d541c60105680164800564040810b445500c02c020080251041d100003170340c65114140307481669001038070b1040708646441054000c64144000414040c5c0096081c20324000d0f02034002a4101d03000350601c00d0007c0d82d0050300d00020381e160085405800700070b07a5541c50721040401040c1c0400080054414040c1c00b0014201e0b4002160501907140700419601d01c1d543c1d0f034612485402c2c5405c40340e00f0345080e007450003407003c0c0103400c2c41103085800b0581c281140c0d000083c0350182d461350b408035a400640d289015464103c08480c1d0040c030b07101d40030854050090200b440d007800b8040441941491816101d8980307080d400502d00a80c48992000252400100e200c480780314920645000354800c0203081c60f0b490241025051403070144028505001c4182c0b03e40061820007401c908128103e03c50501c40e910 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 868941142 1250 868939892 868939943
    0xf05180d0e0d060506060c010e030a0e03060402060415140c0a02130203040f12050904090506060a0e010e1605040801150303030606050c06011221020607090905270316 73
    0x51a920348000010706500110704a0824010040d090036250340c002241a203070712003200c007001c0c40d0000802403c070b0441c44042d02d82d045a0340d8000015450202c0928900c2c00041c040c2c02550014422031a00340b13400180340903441c42c043d114040c00941300c1a404542075680c00352040010704d4001d440c00c001c091041100c0380f02c0c440745241005206100344000305140c410100031041c0d10149001029040000131b9400b800740090300e59001d030801071100104140420b140d4080d000640741031000703540f150111120001c00740201d00d101c01010300000e420b024800c0c903180707031045503040c200c0c0f5140d20707201072901b503581c01001c202220403001c20410800d0342c1803203980014202071030410b041c1002400e20b2a20b0700c00c10701c41c0010240c1c07000b03d20300030301170cc0311082e413050044040324507844460003501941f01c000448080010440502000a41000901070b00e40f15641c170340001194440301c80429125450400000040c0c0d00c002e020b01c070a000501d0b03014580c00c6005411039403050507001c9400b480c04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 868942392 1250 868941142 868941163
    0xc0103050c03011202010c02120109060f0c091d2203180b0f070803090709150f0e060609041d01060b0c06130c0b0f0c010606121803020616030f0518 65
    0x741e4100010090030418001d500d506960900e8182010301d0140001a0040b00e1840f001085520b000410320030000c081e84039907103101c0d8541d41031007441d01441d4241d544c0d80c210720807810042d000030083c03251754900c40203084d07000790035035a80b54040f0440001801000806281200401c09400701c2150140100244c4002003074821500c1c4c0c900740380c1c903860303030b1070b501600ca0024070001011011852034041844480044c003220f5004100c144000d290740c0140c0f400d9446404044021043c01003400214640550300ca8400944200e140c084800103000051540d50a0a42014081400c1c407032800000c0c007518006006106500d034031181d020700c0450600001821150f01410480307540710006000282c907204490301104516114103810780902d00c0307446240c8000701c0c503518100c4040b4507103820140703a404103c0d0040d000c005402d000d0300204181403204202401507801240018203c0c44c101c81c004950701d040303150215100000041020684d601501c2048040c00504411501640c0c10000302d000d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 868943642 1250 868942392 868942411
    0x6090201120905370503041d0c04030b13050a03030e0c030604120f050f042301212c06072613020d0b091b190e091e0c010305 55
    0x707020701e035603d40e502c41c80c14100d4090280c1c1001c00310420b480c440040070380070405905803007103800310b4078225413654068011502c00845056800c0e4011084103101c0788284d6080054502d060b0450311070100c4484011b021103205e8040003240000601c0510400e243c8911a49000c2040c5034031080c0e140c10480c030000b200380280e1104003008040342010049214075005406d10200110701c6013070072180c1d44100e07100c014501000080011f0091011240c841700103e54104505510100600468410014204e01708800641c1e900f030350085070f030a40c04010440c04071040c503244c1d80d07090611200030145543c41c410b52604002c08101c51543c00425542d401d411040006041c80b079002e81c0966820006016030305a46007100300e02007103403504440c114203640c020343c4103038440c6001c098440c0d4a200410000003c04502501d400183c1800480b641c9014000c3c0111019242400076001001000602c1c0c614548103101c50000c0c2041c000c1c045013090091040a0001228100c00260a0ba1009401d03101c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 868944892 1250 868943642 868943651
    0x9110a0c111f02030c120304030225180e010c0201111e0714030a033c020d050c03160203040510050714071e09090803011205190609020112 61
    0x48154000c100208080e03210305003003850394141001c02d15207151840d41ca072001030442d41480c84190004050001c941480080b075202c0451050240d44501082e00c0040150f40b0070f468900c01c01703000c042040b00300d1240e08800e0310070940d26041c200940a1050b00510380c242d407900b5181e030340802800360701c0c0843d0f00ca000038448041c004018104c0352141382c1c000300d2440d150b44140740601040d9001c03510280d4000d031400d01c108140c241e038580c03a603012200250110b071501300c2d1110502040103e090604100144013401c4513031004042203000381101074207400a50802c074903074601180e032003a0350080480072041d0340c0301e1401e11070600755102400b800906561050100b0401aa125241c400da104030514226440742110701d44010400d1f4842e0190f4100c0c0202100420384032101c3e00740c00001c006151601944668401e5460202d54042d000a0004036003000180f2044030031500440f40c103441901103c030b00000e9600b80c60401008210101c2d80d450706d4020714070640d070b4007000d41e0310500e01c0d4280400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 868946142 1250 868944892 868944907
    0x305071e030606081e131515080f0f0706030c021e0c1903120c060f0c180f140907020f030703080708280506030a02030109152003152205010911 63
    0x100354100050500c00b1060383e86101c541000000141200d0b85a02c541040c0011006c2c0107240c8e0940d055401000307154402c101c0e055910f41c0000400ea0709103400b0202130011785051040807005056204d0040085d8420311a24918007400c1c1c2584044035440d020141101f400b4004c00c00c09001c69058080f403c1020660045c800314142038101a0361001a040c40505c1980603e4203001405690350700c0c503c072900d000312408429401070110500380200200304941c0e152a024111200c004d03d024141201d1034194000215090050b20290428014011203012800f20300340c151540d0302046007200029000018007000740c2e0841c00c3c02d600004914400644200c000404e4030150745080d000380740442d110380100700c0d00d0300d007400124281c3e40c02900a001d183c00328141171a01038400341c1d040210600c2c14601d11030040e00f607070fa20503080e000300841620b10740781d11103902d481040320b03206164045a00242d4000b480032030109441c16008410010501e503140c1745562046440504002c2d0048004100c0f18 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 868947392 1250 868946142 868946191
    0x4030309060804030e09090109120203211003140d02010c11150c04050d20060c0a030c0c0b2802030a0c02061308011404062a0305071e03060608 63
    0x50079241c0324901681c1c141c1d0780c3d0030101c800c240d0381d0002540000c0f2613402c0c007001394810740100c0c40b0380c0e0003410442c0c00030003220022070f0340b481403840803036401a9411684100c0072410504503001300003800240742064a03612901048507403144c40041c1681701e030427001d000c0b41d028040d000e66009507092112444c4c5e181c0c2c0d180b5854140750310701412864040000618840b100c003050320f002d00005040c98017105214585003440100b0080c01c40d14682c0e04a03009100e03450301004680c135170000000500101c0c007041d0303030540d0300e10001c10f011200d94500002c0456100d20041c060b100b61440c00d1030413100030241c0f03c0819900c0070307005855000c5400800001503500e4100e100681311070360683d16555610300145456042509580000405509010010002081c6a010306000d60f000e00000c125a01504200f08440c81018189510041c9040d07804045031f4040d81c40301f41c0c03101d51801c2c4002d14641e0451940d0601c0d241d00720440c0829a501014440142d00c20305480d44559060510790900b040c15069 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 868948642 1250 868947392 868947407
    0xc1e0206040b0a0c050304080d02070e04020607201f08070c0b1302010320251509140105070908070f05060f1c050c0d0c02012a0c050303090a0b0606040303 68
    0xa0103842c1d04001404030945204604041003a81c01400341d075100d035203c441281c0c99061606110f00148034246e008568400001d10300c5006a0740208294a000f009075545280e18a920140102134802000307054030356160745001d40c0003030761504040b038221032040340080c200301d501070a010200424040740c1c00008100c8841c0e103800503079144100c41410403130301c0101e0251003581b20103010004114070608903030200300e015000b030985501420701c00740075941c0440801d141c044030140080214030007440561060340d000d0300b070407401606400c6030444058403443c2555002d4540a0020788140020802e24806110fa07401400050030785003c21450035001a845008000c10709482d031100043d0320f616580305c00c020400040c105901400185040d080a078100e41040303100ca642d880c180880b90304510300c1840f5940510580051020034210400c4150384282034000b00c0100740441c00d108500418410006540b08501c6840145071661007031609546005000d08924004c1000740300510019402c100d6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 868949892 1250 868948642 868948649
    0x20601060e030a0203030c07051c0f020904082502012606100207030c06020105090111030105010f032d0905010612050d03020310240809070b0723010c0c1e020604 71
    0x801c100034100300e100080c242032044100a50506c00000d0010303071803034007182d0002141c1040b550340600503805180e0032005034402400078030300c140245810740180303000c0c80c03041c0d0054040c1030280c3c14111190304e1007101411143e0190004100381400b82c04560780414054812603442440c5c030a0400b002d9400444000c020f4803080c807644448507000e40d414820801c441c0195003010101401c0c503654400070703000305400c0d966080c0d10b50a00c09298020400241264106c90f410f9540e01e60300100840d0883c000d0007410b031065203440c40c801c500b0303542d01c00698054004080c0d20702d0005001d03240d45403050854032264810f000b84110600c02d840480d0307021400345201102800c02590302c0e504c003000a44424586d8203c46459a101410075401200c0716510807208141501c4400f155200d04504503030b50039081c03150f40400c001c200218000603010340e01050541800400203100700c0450319000f0b09443c0140ca00c00001105401884184400407616292501c501c0d0341c40d48030399000d5000320300c80b48203e01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 868951142 1250 868949892 868949897
    0x140415080705150d060608090f07060509010e040b100e01080f0903040e0406090c060c02030f01290a1d06090f060603061c050703030906020106141e0303040e09010f0606050a02060106 80
    0x1031106141d10040804c0310919503107072030b0800c920ba0300d45001400e500800e0301c0c01034503071244c030700038074401e508c0000c0c441d05031651a1100783c100302c2100d00441b0464036440e906600300e5111400c5d06095118001e56040b09403103506c40c900700c3c4405d5000185a10401804081c12a04003818450f074604084100d03000e88003e12026a80740d40c031400c1c41e40252000c0301c0f0003004119880340c0010f1950340b2000043d41240f0131000ea6030740a801017006400e0305c000e88500305140c100b20140d000c0d1109120900c100d86807003e8501c0c41043d503034a404e00039102d2a40c42003400710403404100005458030801d01a4000000f01d013440702070070700100dc04d10a010082045001c1c4240700943c8021902030040303200d00a50001c112000c85860389401888003090344180f002540c207096003ca10440b03184200443c11102034030300450704c034990100000c10494101402d07018082004042030303030808a0103003845104c268001160880d000c03821075040780d00301c0e444003080000500403152a203a010071485d04503101803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 868952392 1250 868951142 868951159
    0x9010501050f13180c0e10050d0603170309010e212104060e06060109050f040f060e090a030f1d0d06022106040e0f0a1e0c140415080705 60
    0x9107942c090b180300304a21001c03c3c0000040000d184c503492804440b21410b00013007032040040643c000d0302c43c14011024a54441440c0f400094413500c40d201410244080da000450074565a071214010211061007444e0107840001c200590000c0034007070b4000d050105001014000c0e9041403181140400d02d00703076602103100080b20b51030003080c550b42007410807509095025a08040c5002c10007801c44010480e0940070b50300c0000d40c00e6001c1d40382c41d0216000030342501d5001807510100700040040131000011550b42d8000842c80b8248006a1442800100c0c01001140854107002c1c2c134000280102a007000b80355144100004510b00e08101880300a0381c1664042e070507031514002a02910603e814003200741c0c1c00004802d20300d84100e90240109580400141007005806529540c0103129507109a000da0413900002c1e0f05800b811100010401c1940020129503a134101c580001d0391003100280c0c01c1100c0308106103041d115402c2400d241c25000000c5074903114100d80c0b00c114511890303101d101c40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 868953642 1250 868952392 868952407
    0xa0207060509060d1e050114130905030705010c180f05010e1905031f110f0a0c030e1005030703051609090209061612080c070b0a050c070605090705100e0901050105 72
    0xe0f00181c40f041c80e40350205210081c02a01c0d502c01711902c882c032500038030b828800009011050710001d1084160013618500c140e504040101000d41003042085401307210402c4200701060082c400c4410002040c1d0714851090090440340c0580321450b001601103025240081100783c1e0080c41c0e9130400f0b40c05984030309211003103000640000400d5441560075010310700c500c0a0307155041e0084240c1100100b01000394011040c150700302c41c003a00300e085003074040401075608080c0c02202c0000c01036120f4a4400f00316000308000c6800304c140c007840d001c045034001c814094150f4245c01003941c05820706606107040c03158040000c1c007041140c481c080034103500007001001501d500c0d040350710700782600501440812482c80c00300e0540b10140c00d4080000e40d18070205000e40c4114003142e0703940c2d41003002d16203540c440e20100e070000c100c050100e04428100b003003060b000030410301450b48505200740140007914500030500c221180c1c9503c10700100300c0313812034802003a5640804c0170306443c400e01c0c2003030b143d296 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 868954892 1250 868953642 868953649
    0x60f0807052710031b0c0804031401360b070203161104050c03010b03010e06121c0806010f050d0b030124081209180403021c0309050c060a0207060509 66
    0x54aa00203210000115400b003070400c4018250341028080d540c02c004101c010a0490480711640203050032001008203190040b403160729008082406041d24624185d901d076075078140d0034811184c0c21282e94546076581419880d080782d100214201140040000c5038074000ca03004080c12950081028101034040351301d0714800c2050343c07541d44818001601000c200d04001c00490424000340e4856418500001d40616104d41640d040b5460b503515241581d091604002c2c0002d0020102c40e003158204904c42c500e15410003450300001b00c0888000c4019800a10013050b205008002ea0f040c081c01285840d296644142120320903106170400154010280002078054401c250441c501c4808005440c82d0703c60640703d4940440f6042c00844540b4004c0f28120304882c0100030002d035200c0340194107609030690190b00258070138800e00c1a18907600b00e42c0c106207090981000e0500003c2d80e030303401080070405d0800c203455100500f294818181403c2080017565642240104010820085000d104946 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 868956142 1250 868954892 868954897
    0x604080c01081909050c03240a0207020d0206160203060c0313030c0c0b030709060306231e0909030a030e0a053f030702010f0905030a0c110a06020601150207060f080705 74
    0x3081a001880300f0101410056643c03c6898041b81c0f00303010300b8101c2c0001daa11412800000449070b400c4044030769138650000000c1d0003011050781c00101001500d001030761070340002c0280410307104610007142924014146802801840905a40000c00c1400306c80075680007040800b0794145000b80720062146841840301d001640700310800c85011050100b903580100c80c1d4002d0355016902044100c0c0d8035113204c4010031050704100b03001800c05501209600303280c0502444402410340c0c0303c05004a58022030406a003c9a08641c15040482d0a500c02030707050007000f40907050307a80202042d62150300e803940c9900d11040104a016546480540010511004419003880d00081d80ba003209041c5000d90107a4001c540700d0006500c1c4c0b030003100b101105032280c0d0600ca40c04c0002941041e0800c43c0c01d68281c503440d1402c1d00e00c00321005040d441075450040c101c010f0841503000c2c003050f526040110b0500c14038600b0b8003041d0b402c19103050082c0b99000707442ca610b0a82526040300580c655003000d4440e803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 868957392 1250 868956142 868956181
    0x130207020a09020a0e10022e0e061f06020303010515070302120d021b0604230c030a0f110d0503090d030521010302010807170c030406140114040b0604080c0108 70
    0xb038008a1100a920340040500300a0441513401515120321100c0c22615040c0f0440031000a500f11106120b01c102500003030265402d61080020f01d21007081d40b040d207056821100c00d0407034130300c01e684801c11042c11a1041c00510090008506550500b0002100d4a8100610f0b6104000c0824550181442042408805c1070000701d0503540355034a0503218007030741c021680c5c001800c4003403600480005000403018419074000d20544042d6031603500f0880c607410720016141c3ca601c0f0b80007911095507001d00c18880c02610940d203001c5000c80c240381c4149000030f20346100d840f0f0074084001102249011040703405190040302c0b1000c0900300d82c5000d4451b0700800850398010341501c5902c8031000300404500741600d000f42c0385c80a8540e9220802c40d03e040c10342458458103440c0c0000719207003062400196030401c0c4604804110045004c80c04402250240d014031419071004144000d80e0a080c071421120b45000e85841c1e1621f0306140c0c6d0581d540b2041000075042008000000c0d46001100e02440d520303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 868958642 1250 868957392 868957409
    0x21120115030605100e031b2112040e010e1003080f0702030a0803090607030e0f070608040f1b1a1204110120010b01031b080103080a090b1c0b090402130207020a 70
    0x3031003542d40c000f0b00d0101922482402485801c10165041d47c2e14040140e21b80402840c4440d10040da19806880d02c0c20208540303007502c0364012200e0038070300550140c4042c04200100c22020740c9410302e44182e04001600a031f1030460705030824004205008106c1d10760003202c000c02540c0d40a5072020916040410001501c00c55010003800030041e404280305000780426035007032001c6116083c00e00d841e8041c003070304200c02703920100c401c0003150b0040910980c0240503082516030048152154503040094500740c042c3c0e905800c0c0309211841040d620032a0070303c280d43e0142c1c20701d03012105007090100082c0002e4441c00851449000d0341c1c1c8541401514008071403240e0300d50001d0003007c14060000480800d01017800e009408404e00084080c911803091140c2d00c50101c0d910b1a15080c0d502c1c0d1000140d10704000908001040008050004001130001411a10542010414800126002401c00710300c155407502c1030201513074a48030307a22015040000010ba40d01098400210714070300300c0d8003a100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 868959892 1250 868958642 868958659
    0x3081f0b07030918110d0b04060305030313050708060402030604110607240b090c09060304050a0c03051c051201060f0903060609020d18030507120c0209040521120115030605 76
    0x100340d031080000c002c0740c1c01c180c0441040c01c1084804c0060f43c0c080904207410070010b0100c1c1d0319401c5203401107043c00703030041e1000036520345a8031500c3c15580200c510383c00f80c0701d100441008100c41001001c00500b180b40280c809801c00c2d0340002c2e1281800340004d41801e28440c4941501d0381c41008039900203920641d500400b50200341c489050f0314000700d0b19031160b4680340b014a40c60603d04a11031040014201092504521504016a0340c2014005407541c2c49403003c1c140c001080002d504c0003540c00f500040c100d003c0c2c000055294a5818003c41003000780c1400846100d00035008014195100c0d802c104900c500014411104424282d00c040c01c1b0b1400c1400c00210f2029541c01003410108101c030512146d070781c0c0210760005641d04207005000a804000c01008540525000d0302e6890440c6040e101ca02d0f01c0d9000515040c00550b003c0d107040c0c1104000e080070550000e0340401c80440e00c0328407410210300360176064210318144244814403502484848801d4842d5002c00d01a2000500a82 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 868961142 1250 868959892 868959907
    0x60302151207022107032d080106020a0c030f0c0e01030f110409020f0d020609040926090d0b0411090108060f0f011202010c020d06140a2a05090f040f23010303081f0b 73
    0xf200068105e4402c020492188c00468030602c0070520010301c030703008000c8080041c81c4d56a43c8480301e45071302050b14007032003103040400c01100409213a8002c50003100148684030301806c141000340c1c030030304075640701c1d07480d2540650058540d4461200c0080088400801001960000c504944580310b420342d4040d02e828000000c101009104000034941c0d40e18507131800c1d2511000b41c09a1241d603108540c896501e4400f80f0001d115181242e41c40783c45041070480013008400801c1d50840d00b0b0708009200d80101040001e0709a46d2034a4952000c55000e042d9402e5240c5100502d00d07203040c100207410020030b2400e08007035441e10f8034641280b50340010108640d51201c48a440c608205842d80540c035828410900c2c48110210308000c00f0305002d040c4846202070104080c0d4941e408014401d030000c101100018840c0d495110340039090781c84007804250000d202c100d058040740441c2001281c41104030040c0b0120398880d00c0035610600ca0300a0f03010000e417a109000b641d602c2c50b480780e1a04a400038044 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 868962392 1250 868961142 868961207
    0xa1e150207090b0303131a040503030a120c1d040f020f0706060f090e0d0509130509030d0b0402030103050303070e0a090504050a03092102040c0306030215120702210703 74
    0x25012180301e000d00300110460603007010380702c1c0304100c201d4401030200311081c4101d001d00090511f00140c040440fa141596400109045801c268240b101042c0e01031150082545079000d440228400c1d882c1c116030900f0601c5242c0201c070170742c9442c5402290b0b1646100383e0098950b04a500034110f082384103803624000c4c5049400b50825000b01d5910303c1000384009024411805810003500d510001782400f0061864101c2d91361f00400c96141e80800040c3d40060102c4440c412940981ca244010b1551501c0002e0711805503146010782c503014500c10401000443c0d0007000780c139004680c910304842c000e40d004001030b4818249400c110b84d014a090240010440300140e18542544070ba16460a02969210706180b01d040b03240c045000c5000502c420310043c0303819400040a40c440d414001685900c81d004200518034058400f00c40700c0001400c1c0001c41c000c86010f942c00000f41c801000100c0b0300461601021144c0d452502c0c0c40d000c085500c10416001e0001240305810307016085030300e4103006150 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 868963642 1250 868962392 868962403
    0xe0a060209130f020901021c08150f130501050a050a03030203090603100e01060206011526060114161a010b120907090504030513090c1b06060b2802010203060a1e1502 73
    0x49000d84501c4000c9840c0c0c2d50b48c141e07146c00811180d11064403a03a03924007400300340c10503d0542c40e071011090094040c19614180980e20690070300d40e00050303540c14041800118101340d0045171146c07110100400000341c3c0001103640c0b4103402c1d038120342c60342c454505020b0400c0d0203401c20342e00c50b000400045480355000030424100c072407107100321451340c511280030344598000303506410741111001c41c00c101d482619080c050f00810189000c2c0c0c281c2421000207a2541c101e820781c0d1800345000d11800060100c40300c2d0101d26040710f60601555549411100241ea120710713030f2904c11219503800024182d001c01e2290358010300240c40107002d14905407600403e190310540c150800242c407418040b610000c144102a0034000c152511ba04014182030400d8215a80345800c488080e114900480d10700e29803c05400da02c0106821010042c4000f070081015074201d09510003168414001c0280c90342d2051307514421100500420400110b07800b1007880030302040e401194a14200203914800198009071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 868964892 1250 868963642 868963657
    0x20c0709230c040e010b090f3034050d0605010306181e0809040908090a1d07030e01020c1e0115120201052a030310090e0a060209130f02 60
    0x78104a15035900b40018000d00540c01441d50010441d00140207400d01c0d50004c0000c003070010309180407064141e0006840551405003404202c5120f145023903081500301c0050440c480400140141c41000451540b95000220030f100081843c658090604803000c00394002a1130054028034400700c540c106400603107230a10003241c40900c4c040a071603191840c031801110880c0d000c0c084104421542e1805804913000c8003054420341030400c410206a1748911590500900c180a420f4540d40c085080003250030f603075404190310150710716124150701020700ca050303845615814000749002034400d401d802401107081c030208500c2540240214020f11070403d0700c030783e00014028000310401c58204102420244241260480035889210066004070058070250070070a414000c0c1d40f0100703c40c2039402e100700404c1c0700283c0000050010091100b003810004e0702e1800e805003e400f401082c0e19030f5071132940601030071203540030449031030326a42c1405030750700c81702038640a10100e090588201d009500a54 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 868966142 1250 868964892 868964951
    0xb1e0d051005070e060a0903150204051801080f06090706180e150307090216080c010e1207030e04052703040f0f0f0f0e0f1e0c09030705030c060d020c0709 68
    0x286040101d103050030891b445280b1a03920540303038610f0740c1e44072051184901d8011940c150240000310b1b0f0f0781c80301d50302c1003007041101c0025512945490f0110b42032034005c80d00710b070b000c0d0000000c001e0440e000082c1d01c421501d5a10300100c0c4092185010301030041e45802c400821000941408498060301d007000308940c0c805c90590700380031343d2001a54100d119584a80208a07098405080880c24000141c41520900000800c1185400c40003a041400d0b002b00501c42e01d07400b241c141c05041e0f000c07449154141043d2004c04c41030031f00700008010901808215495515040c420241480040c825540100800351080455541320320f18080d000649009016030301e40e00c002d00190096400c0641c10488500c400d0a6910352030b44c1c4032402014100a084031004440451a491b8040d042d51040d480341c41c05070403a50b07c404402d02054140070003980524401c0d801707800c0c010415603603030003100c1c0032548543d00140d413008021603072414000150f1049082e20f00d000840101c10302a500003000303039002c10 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 868967392 1250 868966142 868966157
    0x180f020a030911061903090f0b09030301090b0a050a05040f0605040e0a140c0d0312150308090306160e1002120309071d130b0c1b011e0b1e0d05100507 66
    0xc024854540106001e40c2000b560302d002c80d00b541c5d400396010f050707404d0003554840045036050300e8101800f4000d03605c8600030307800040104802000f902c07030b06e20900c0c1304a4a00e15403501d00000218202c0300c600910340300360394070201c00c81901d1a82d8000e00007440b018205101c1c080301003a03d2038603100101d1041d81c5880d889400505407500101d0180d82c0150000e0200c01060b40c42d407011184985c42e007503400c2e81c03140d840c040d841301400c0403c2c0301c070019842105510364942e06181030600301403000d00b0041c41b08980500c2015241e8100141d0003d0040c26140c400c3d0b030a080d903408910b007599455003010001340000500075100c2010a00e00240c824030a03d201d20300c854607000580c800e200721703180d05000f0000414000050101d0301030582248504541c9410003280e55480a42c084c41081007040366035580d1003a02181c1c119180d00c24060041000030040070040304041026605004004040d0304109405400740d81d952421062566070050101d45196281c40c1c15600140340c251048000304000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 868968642 1250 868967392 868967423
    0x200619050402030a030c0c08032206030e100f06170105060102071a030712021c0c030e0a030905150c030304031d0607030f0806040e1f05150901180f020a0309 69
    0x1401001d02940d0b020b4010851280e25032402c0b180900303000300c1120a1100d05c100081c80e0720381040a0061003000394080c0b460383c1100c010381c14805001d5403008062604003100c0c189891800b00300400405080f91020811003202e40c8544028241604140120584c446070409010015408140b1400007a0202c0d003850f0340744d1300107801c03c24600d0800b00b400c05c0200700007003110f0300c42e0f0128030308a049104054200111621050020405007614804265440041c140f001d585030040400f0181d541c000360000940300d8400505240e140d004160080c2006400c1140c0f580d100c10840d40108210000e407501d80c00c1a141c010140b241c615200e034401c46c98a440302200e45414412a0012030303050b224140150b10f5907405840031f14004101c030741e0081d43c0d0b043e08410440700b409031403001319202608082d5070030b03049148011610090210064010700f4111813905848038600035042d607202500c000c00b448010641500508408000d480c40d8a00114020fa103481c3c040d0402c1340a18480d900d0700350301280 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 868969892 1250 868968642 868968691
    0x4090b041d060103080903150f040221030d02072618030c0906040510030c060f1206050d0b15061303031d06041514030f070801120c0302102006 63
    0x10380500d481ea15003001c1c1c010000a12284001c00c0880c034050103803003403007030240d030003414190048850003007060355102040218a0008070340b02801ca000610741c10f06050b690519a40c0e4028140701c0c0c81c400b5400200796040c0b09003881002180746804441e10300c04821840030400ba034010440004000c64914900390344c0346008190001c4010f400342c05505d03c6ea841104001c0a0310001e040c1d05582120b03054044086000b1524030400780566032141d496030070f000c0d1402044808074036400340c402d91600200707200a58654564043c1190808410069030301c0d8108c41b0100091000301c0c1c1688850b000982014451031104944200c030b010f40c54a05c002c44c440e0010001414801d050b180c2e1150041100744982080e4076120000d4044c1480c00f00700d441d040f03898004856105132841008030001c1c10400c40201e920022242c0034200440420f45006000d90380d001c101203d50000901c1603e003d4107005e1464030030300b40e4a21243c2e068495031200d80306154959211642600d00b0000c2c00101c000c0c80c0f0340c440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 868971142 1250 868969892 868969931
    0x30d0c021207200402130e0907081b040207032a1205030f06061c0f05040b070930080d24030b0f1e01030b090601060c0320030f04090b04 60
    0x1904180d180300042418141d0f00b007840140403060f0340c440d41c00c1c48078082c40c0c0014100040604140080b41101d4280390314802c0c40e00001c1d0380140642d0344040f0310b1040b0140d50844409925000751000758440d800e514064907240a8000d401020f00101138079000ca03241408944540d1601446058007500e21507182140d86200032105c01d04401200d40c0803034600d0800ea00244851110003007461045919404544140c0d00f030000e010382d03040d40b0b8101f4001440f4a07050880d4010f040c906081c00340c6450113004425420401e40c13a00103505008020175680da07a40b20015200a50100c1050b66036501c0c580241d0090542650307009a46d4170050003420700c0c0a00301214015280c00070001c0909a851140c148486980205241000e02c03080004402c60036600ba843c2c3e01943c442c4009801610303040d0b11061404d07005900c01c5080019900b003207008240c108100c2020000741d119505107180d0001140f074614890702c0a07440040e00300141c00212084c2561001c0160700080302c1c14010800920351415800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 868972392 1250 868971142 868971157
    0x12050a03050a0b030606010e0310021b0106050f030d110a140a0507060516080702030c060c0601031401090f0204051e01140102070b0c03040e07120504150b030610050112020705030d0c0212 82
    0x160305c001c0104040f5030040d0b0b41c030a6040401000c403550302900d4101c103410f80e000303c190b207000f00e82c00c02120780b40b0031428001c07103000d40800c0d02d4000c0110782d40000a90b440c000405240c09003c868810141d81000a10003080b17050b40024641001d030141d100010765032101d5aa00355000c6c007c1030341c0860310034440c00803903030003100ca800b6421000303007281c523850800e034031000040384d03d486100403809003a01c45802030902230005002401c800e40c0f450034100403000394020703003d00d42e901d800c0a88000860780050038900302e806442c0010349680344081804a0030f41c100324000d8045550300001401c010035060030070f109000b81c0c25130780d07015a1000c01581d2801a041c4400c8603410520007408584082c0500c1c6501030300c00e00c2c090541c03c240302c600300200c6009860a80360751000c84c000040290340c80c040c00390019030603801000c051401d1101c4d098850356034010b283c1005030303802d0764084000c440c5c1c06841c007880e008403d59980d1240c1084500c000c1401413940005402200c0b00122500c003050181e5100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 868973642 1250 868972392 868972399
    0x60302010818100603051c300b030109121808210d020403030e010f0c0b0c030c070501050f0618010803190302220501120b01051c02040312050a03050a0b 67
    0x1030b911884049900002c00c05035984040c41010319040f1844603d000d00f40085016001900d00050408001d401e072a00515186051240d03124102500c1c2d14180c0c0214102c2520940c81c441c040f6401c2000c00c083c00f0302c0b6072351590541c2411200e4007845504041c000301c080e1561903108a418007a10031052a096512400940f03400291075068200001c82c8841c0b0b050340c0d14004285040c0346202210103c1c1c010350410340020b4001d4086144030758100c407044000c0102d40c00e0000883d00a6500d003103800700c1c01031a00c45001408070100e070344400c4131420340d0130f46513011000b03201e1032804600c00c0041910480e4042d00c90044980500546101c410788281681c00080295260803aa142000005181420148105942000740210401140c08401c1d1401032004003200524a010001032000302d00131030141d1004d10300350040015a0b0044102c2d0300406640011083ca0800c800c0b1850090240740d01c00361401c44418601e2142da03038090010806440e480e10100059210b04052800b1601410701c1c1f81e41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 868974892 1250 868973642 868973657
    0x130b0901061d0904051e0610092c070b22121505060d021e100519031e020415020d090312051303060e032106010c0f0f020904030c060f06030201 63
    0x340c5003443c0c082e20303a1050184007100d030740d9600428510141c1100010040c0c1e2a0080000e02c6010103041400c100144204902030120340e02c0340680c0002d081102410910301400b9983e8001c402000303102c00300051940d80241d64a898001d951070311024000c415198240c0140e6002041701249a08081d240c282c204c1c03840441303c0014019003004280260400d94480e00941d40c001c0140d45000204401c001300001032101c610401c028802c0640020325800140310080c0400c00703060b2500c5011640a4a03e468007240303c02e0601781d520080d9a0710034900e40b1503400010041902844640108007000b40e5500f00c03407030a801030780100d44074105404024461402c0540c02d900542c03040c800751400c0a051000c40d81d40543e640e958504803035850b858161940c00c00310b14441d0080c96a604906001c00c0c0030f0b00b8207000e251010000b0004070404400400c801c1802404105100446185c0c80d03049038042e014031403906003400d005e441552030500072078025080404000c40c0403100e006820403241d040e1100c00c0c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 868976142 1250 868974892 868974947
    0x6090d0528020f04060308031b09040507050a030b03072301030e0d0201050106020709060509010e060f04091112010e15070c0503120109111602062d03010503010c050f04051905130b090106 82
    0x60340f035010165092100c0ca000c0c040003000340e855120b41c80c014043780d00c400b6624040c809011701510131441c3c0191207904050820010342e503d059446401c164014042c041815040d40181d00410210044061a104241d0f40082032501544201c1c1070352481c1e000c035800f00380c1d41c01c1c940c001d030340c0c9a0041541204d440b1004002c2c1001151101d500f05400405001000e044040810100c80d44200117480c42d1034040900d041600b8200c06003651080240d0080c02148503200186a0365042080322095001c3d2240001d2951841000202080340d0f00005880da41d80311004103824010082c050f00004c945480040c490fa0208002103c2102c2c80189001d480c0c044c090302009820307005043d6a400006c1600141e000481d42210000482070110503895140c0d4100010b040c00c48520801100920034100f01d000d06088024090341d044500499a41003c0d0040542d141d1223010944d00c081d421903078a07030500003070100c950003c6001300d00035910701074035070b0383c40d1030031a18404440748103c0e80c19008074501c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 868977392 1250 868976142 868976161
    0x30b061c08090109120c261c0e060307030e010614031902150a050706150303090b07030302040b040905160e1c0c03140d090e0606090d0528020f0406030803 68
    0x2c107684581410030307101495a9424100b01150356040440f204034041c0b2003402201a4242800307425990302d504441d0070a1805051695000c010900d1041c1c0302d2451502600d10744100d072414a1400c01411882d124240820060040c094a071480d408a50030311501080003561006210400c181c0100108030100c10440024219019018280d800011171034501d025003070300b07074002d0043c0b5080c0e580c4c0e40e9803a10f0500b80381003140c00c00781c07162a407040111010008070b039001c0320325000d40702580c0c4017540d110614a01038000b84900d9000b64605100070400040d840640d80c05140305107007801685080450b004011200c41c088160110790150300d180305200701c10041c456400d00c03075118000e9044450744903140c100025121508500090b0f020182004110340e002103114000c140c40c650120250500c140014242d00940c03c0d442d000714661500402449000c208003044905030801f070701e0349410004500382c941c1c401c1c0e60003130340251860402c64840d4201882070608481d0014085825070311460440c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 868978642 1250 868977392 868977397
    0x40305040608190612020906090103050a1e0b132108070c080409090c030c082109030309100e0102150c1602280e0c210a060806040c030b061c08 63
    0x1000300800e143c03195075006150b0f0300c540300150801940c0002c141440d4410402c030b1500080c001c034096409500100300040001a00ea085654840303601d0684025a11180803440c0700c110300603260440200500c07040d04480056418800c0c000d21941c803c504112003014150340c0c5450b241d00c005521040040c61192094000314805441078101e60320301903a0744280130544204001c20b684040f032040080003003013500a013200003805040d000d40005103242c0f6405c804811010031415070100006071000041c2c0d070500403607144a030010001921050955001007110280315480e034003602c6403156440f043c0420100d501e2181140f02c1c5918900220b00c01a03013081100750508a0300405107050b500101c00c9118a0b010b00203440c46055486549490721a200030000907040c0070303900c41c0400006c002070440c1c0708001108076803140450350f00e80369480031078010310082d44000c9841c02140c1c180400c000c1c2d5400ea420842c1d008440d0100c60b6100c4108103e00d2a21400c0450016241e405480340028030f003030301 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 868979892 1250 868978642 868978651
    0x3071d01020a020d050318010207030b01090b04020d1509050709080a1101030905120304030e0904020913051e370314040513092006070206090402091504081203040305040608 76
    0x540d10b41420355030100d4032803502120f08881540001c00d121b0920300740c030980c4d0104800b00b4801800c0d01c510710b49070382410f08018080d628400b5100c0028a00300d03100c0d5012a1407140d050f0b1030800800c42c0904000f00804842c0c011500e825040c000402e284521032101c02d400d803006140504680404d030381d1510045200025034a06041d01e8103c590f010076018041c400d4040c10200c166541d03842e2a1038010880c1800c10320051003560040c080c0000340e15103a100c560b01202d0014901000b042904285181c0812407501c880064002110a0ac40d0700000c80d420350340603020405e200100440f98546003c14071440aa40c00d0401d00384c505402091203000d06240e40103410014a2810b52207502241c042e82c0316407400d0325425102c4a0050420005281c1c16141c80300100800044180040000345a8850500d0103441624045030f05099540e40d90304039406d0020041000c1e54809401c01801ca40703802c5441605c4160244006106801d40d440044922550345550352510f400c0c105041907607079801c050b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 868981142 1250 868979892 868979897
    0x303031b0e150c010f050f01080c010c0c09020a11060a0212010e06010f050d06080a140d0f0203041206140a0902030d05030f0402040f15080618011a01081f0311090105040203071d01 79
    0x1180e40d0850300c102c0c030504d0700589034007034101f00325030401e1040c03860180d0b03800f49181040821460b01010400c9076601030181e42d001100540e5540c098502101c04c0b051882400c80a4000d00c0c040c0300c8804010741c0140007440b1034140000c40b680ea00c0d540e180e0319880482d0030902083d010790f5180059807203000142803107001d80c100003550540f02c208880c9001c074044802c455811300c003031081c440301c0d1040000c1403469400e890000c200e04000790000b900e0303003d184a40218540b0f1110810100005a0004010b0680c040c402d00028541521808007030503068005074024091600b51604040c403e10840740b013920110b581c00407544656007800001c10b2402030f4001000c1c0d442400c052500c50f1405040700600705100109110f04028001c40701e9500d1404031481c480e894081d01d0001d1802c3c5c101040202c8500b407c050b030030b5685910300108601903071541580c2e0041140d501204000513010148041c51301910303c0f001503070303d0b0000c0c0012444280c030f0600200d11005d8050f407140c030503004d6503801d100040c0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 868982392 1250 868981142 868981151
    0x6040e19020304060501090b03190308072303100506070b042603040302100e01140a2a030f11070803060907021c02210a080a0e0c0a0303031b0e150c01 66
    0x4a800c1012600156030880d4015210801000700c095140182c001c9000114060070003006001d40401c01c001401d1001070620040000140d08280034000407508000c241000d900003400f204140030380c0e580200c6030b100500da0102800700b51410194107035000c40d0f902004d042c61a44564039010701034500c51088480450300c1a0320202484009009036005511a400900d00c1500c1c40c980c0b0401d44003041c840301d0503685030003001d2000501106180b90050a00e2000140000301000040e24807070840c1d1091b080c1d0707140032420b806400e80c50b60182d03d102c45115070800024114901c1920310f84694000682072100c18804903c4d45d1038a51040c81e000700c46401141c1c00301e65080d40e0003034001442d5440d00c02580103080b00c1c1178000100660b1548140540c100c0074904152030700b01408091024000c03407599540c03803016a128071000c00c4603171050200100101c035071955a2130000e01500c0307680982083c08210409038800c9601840c8028202d100040c004014030750b5403041c2c221a50080e041030a050f6484 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 868983642 1250 868982392 868982431
    0xb0d06060f0b040308122a120105101b08091c2001050a030e070503120c010b09040206070b2802030103060c020109050c10090905090c100f020325020a0f0f0501050906040e 75
    0x8887c0042c2076101d103007844c5511080710040400c01504160320840c054440d105190941d03a80c0a08c4610310310711203081d80400c00d00305003442000c80c043c5003c01d9400440c46509641d40c80c0c0a00c209a440d00e2280048000c0f81162805210341c60602040513800710303000b03000c07401c052402a044204200007100032580380f50764030700000e86080d40640680300070304400a400f0850702828090304240450564102c07034241000c1e40172039803d10810300050000c01000010038150420714444256680e0002e441c2c0080001c045500b00003075000b031200b222158601006404143d006010780281950030402034003e0020312000d000c80b010543c1c050804006070700e02c0c00710b68540e240c4a091f016105600c001d1170015aa442030290354104000c0c8402400104040b80d01c2c1240e0001c220b4285144000043c01c1580e0121a440510015108000d5014242c8400416018000f80b120300469038848c0d0340010859036800191010320905410b580c006100b0042448499408443c542d08611901040c5010344907 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 868984892 1250 868983642 868983691
    0xf0a0f0203150703050106120603050a2a14010801050102010b0a090c110303010b0705011104031713030803041407171506030a170a0305070509220b0d06060f0b04030812 74
    0x4085030f07148082540e0384014040f0aa2203080152080d020000405c011403c3d51545c540d42c0400d800010040780700e10501d00f0317075018036030020001d10f0745802048620903102c00c511602060107804560004100d40c000040e5036205010342645c550001d48090072207410b01017094003034488a100d62051007140d0005002d0a44204010f600074280300000c0c9480306c115103403903425a800000e403608409801e000500201e420400c11080b081c440c2c03401140e43d40c1071901c0d5000300140d643d001400120021040005103d5034100d61050f1010032015580c225444401c0c556546d10341e540680c0d200d034841a80050703803816249020750850802411038807800700c030b552100c1103485901070281c10325901244130181660103004480c0c1140243c10002e0600440c0c41c0890590384030f40c1040e0070b450300e07183c0800c010100b55034030910303511501500a44101c141410000e0180140380309044c0300248420300000c00041c0b907c182e8003601e520520840c50002190b07900302c003545010745115851421071556240064 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 868986142 1250 868984892 868984933
    0x30b030f0d0c200918101e0b0301051308131220060301050d020f0424030317100509040809130b0f0316050d080412060902120f0a0f0203 60
    0x766507685941d080e800340d1074521202c0086903400c07400070318900007084456031000300c003d03032042d18a485e6000c10200800c0e480c1c602007542c1901800f8603d494511406900d06c807021440110090009003e81d800140500d8201c40c0211403100150000e40d810400085004004016a040e00c00001101d02c0d03d58140202503070003c1011652090103401e046800351400708800040d034001c650031400d641c0352074040358036068900c4009109000003000007145954030340c80211648001500340a4170150200c04a00030403190100f03030040382200e80844100d800021110780300e40c008480f110740302803400c0c00b4040350341e0010f402180c3c8070209000a035501e4039030400008040c501200007040564250042c081d82c0111410683e0003604110001d8044d00c1c500015003049510540d652220481c0314101154140549d8000c54803041c40ca03072030310091129581080e90600d0086800f4021010507410b610340d58400f540d00301c1003e800452181c804180148040d0b44c0d69800641555001608806045000c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 868987392 1250 868986142 868986163
    0x10020d0f0b2b0f050601120210030902061b1c0e1c0f060506030f0613231b0a0911040905070c053003040309080706053c04090903030f0c0807030b030f 66
    0x2c0c1f01c1c1854032081d468004070341c03501940b10b0f0508000125954003c1000b034070504400d58460b24180c2d03840c03007801d1010803c226140007001c0d09004c20160b400030050408602001c1184503c0d000001c00c1400c0c0b60460169000e20b0707101001486030f20065445402800b001013265625001e071610348160410b05100c0540325488102440740303030704030302c0c940403190190f003136811810104400700d0400094000111810070000800000e000d42080c2800121440150380120300900c2c1062080044c1c51300503400f400a980b483c1e10140031503502c15400322002000c0e0440900543d000c40c4214400001c4502c228604101140d600210f00c0444058042c107a44261000c4000400400c01000b1560040c011003003d000980b82c003500d4452030f950740c00b94031803030700c80c40c0402c015040c42c039205042584401820b1015400b035115032955611505000180117502081c3c0100e030400360041080b1600d8403416426411702d8450400700c2e120000c0c120024031820505940501c902146620b15070303000c01261564 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 868988642 1250 868987392 868987409
    0x21010f020a053a091205030f040609060b060a0302030a24090b010203070605180f0c010906080603030d0603030809011808121b0d0e1902012010020d0f0b2b0f050601 72
    0x300c80d050300d0000303017003d00740760020108181401403101900050001640164000074041030310701190400c1c01c000c0441d8544a80e2082c00016900c0c03450350950080c6201e054009010003541d401c20741c54481d5240502c142643e1009400070602503001d180d03000030300044040c41207034140900381d0360701da003150400e50300501e40360140345054420b5039042080c44d0100c550b0703402a28010b50090000703841c003001b0f0701444007402030100004442d5142002a1842d4140700c0324188504c980e242406081c4031b50560304d040040d420602d0300303414104680080c1c01120b5021b81d0039850020008010328809402808010400c04c500b42480048074060001c0e204150300642c0014400c03c1e00c000700c602d095800d10819515444a40401c40580c0e04044da105104d030040c071310080c130004801c560900f0300395200e1011a2040c80422070f0040c40c2c501d54010003603104d140c101000340310310342d204101c4000d00c52120100007080e0400c0c00e05409134402181645241310308121b400040d0f0380c0c0c0c1d8440c2410b000f44c005404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 868989892 1250 868988642 868988651
    0x151807151e0c1b06080a0905011b111b0105030411120111030a1d0709020f0c100b010906021506040f0b04180c15080c090109030221010f020a053a 64
    0xa10005005000d14034000b0f8141e500c41d14a030504c041d00f040001407010b108956506900020300c03d080d00300c500520201e4480c100d081d0b401850250a05814070303c90302c03c0d071081c40c4605c072000090700312040da05101612203906594441d034030164010071203500e0350341181030354803800e126038002d00615010030038640c0d101c1d4407032818280c460100d401030007510703807039000640450742c9005010030f104007504d6233440d0140c1e44403001d4000c0c5a080c410040c050605110384800700304214529400740f10510030136601c01042d60754a40e001c030f80c0ca000380480142058550300100d02039181a900c054880d0300200008074081d00f041001074100c1d000070082c100483d0401d05003204000c0010008800743c47e94902c1c2c0d1414204400005003200f1009015203c0d00c0300000d19541140e00a681d46001164001d02c0e6841e410302e1a205a02c02c0e131541e10040884d0340c285804420911458026104258819a074641c00e104c17903090310000b00840310b00d0070713010030490002501445e0b2420340c0700314040b0360b40400440d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 868991142 1250 868989892 868989917
    0x4210905032d01090804290c011a040b0105190e12030c010c020a080f0a210f0b010503061027171c0e040b0a0503030c151807151e 57
    0xc0440141001400059240152400001c3d00400659007500e2200000361005025040742601d00807c244070050003050210304400103480540207030481c49400306130005241043e030140800c0d541d220f03003114045203061110481c1407460847d80c0d01d900300c030303450104003a070b004030042003034440c000101c074043c0d0300001458103036080701b401481c121030402d10003000f0104035a00c070040701d40540b00710305082c240000740b2030400d2441450000d18030381010940c403802c0c5440784c0880004140c49400e4180080c20411300d480350303600500130303a44100c070050140180421061030480741885203c81a8441034a501030b10900881000000c2c001340800309205903050380c00f49001494441c0950b01c880e80c00300e000901403a542d41c0144410414002601c0200d007000e0010002050300303056812aa40511000c1201d0a03e0f50001a1240c41201000c0d19403410b510b03590445038441704800c428072810341c000c600030000002e09d1400074240f540c20345441c2c2898512401c090880c0c50b440e07940440040c62540301d00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 868992392 1250 868991142 868991203
    0x3030902060f0901171b310602010c0309020901060c020d0c030501090506100b09010807030f0504051608150408030903070605010807050a21030e010e090c0318060421090503 76
    0x10044d00a9000745c071051460300188075400d003030800b41400c440c1c040100e9803115500003408030004040c00c0b02911a92200c401c0510709a1400724480d9900560800741200d807480d0081c4100d00081e40c002d000c40030b20360b081010546284130030b0801240c11002c4540240041014004000f004c3e62040c2c0000c00c06e4420350505da8a00b0718044c2170050403420501c0c040110340000d07811034807201c9003820188103603a104402030340106030b0302200c500c0450030402003004000000c101c4000311100b10701002c1110b42c4803078406541e800400112560101604085400305501d03d01966018415030120fa15019403a03482d0401c1d50400e900c55140350788a01024001c5282c01880340000d89000003660700842004090b81e550098500070180c1400705110b00040c403039200700402c524140c07010f8101c85950801400d00702d27003648111280781030702f41c5180d988504588040b031007600964001c001c0d1040340b0f000714154149101004400c030203215414000190584082c070100c04100c2c40101024409020300156 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 868993642 1250 868992392 868992407
    0xe0a061d01050f0f07030b12011e0c090f141f0e100e010c020112110a051e07020d030806061207020313082d10111b031309020703030902060f0901 64
    0x3c803a004802c0e0300812081c1844080c02e198010968600400c2d444e541b540841e05103022080081d1255003000c50842c6001030b011031030801c14005030703020400500b410000302c0760104107002c0c01c07040541d006e034101b1500e8120740d021184060000c0401800700318071101002e22140721070346180417a14040c80c100143c600b03000444816055410f1160f0064034280000b040111900002030500c14100d10b03e8801000c1540b0508030400540e110b1542c5031038004015040e82c0140c41c42c04014415044000100340c80201905d00c413035030182401811613119a0155000c003001480b840d044a4203110520311034541d08026402074100360007030760365804490044c4040d034541ea044030403540c1c4800156020961558114150700f110b00c00a20304d03112100702210b09050003105d03404580d07410844106114030b0781c0c9008058005020600030348140107184815182d0003041840480b40e442503008200c100311039001000128421b02c0d0020300e02c015940040c030741d5041080c00390140100400e49400c2542c10500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 868994892 1250 868993642 868993651
    0xa051f090609031e0510020d0911060f04051003020d020a03020702180702030409110d050103110102061014060904090c030b150306041709010c080a0519031802040e0a061d0105 77
    0x5005510900350740780c540d04188034003404c4851146040c01001440340901c18445552442e003c00d5546403030711114a809010003100645809a83c410204038503d800800c954564500030b540ea0300309890107003080000d4403049002004e05808000c00356a100312403000708040e0503181c50043e200c17001da0051205c14403400d5080b40308049901d00303000c031464000040d1400c54459110206400c01d120394541000c1c014201c03400038041c100380001c81002400d490482c03030f140007a03007100c40c956651101200180301922422811549111855806080c52401021a00070190003c981c1040711340e43c510301e11602c0c1c0e0040d1400e06940060006c1c040c0c030074500c05400f03035007140201102e00702a120180c0500100e40d0305e02c08942c002407100f0b52640643e0505600c070713401071101c545505103844050300d1603101540c08041c101d01d924104803030178001d21030020103e107101c21070b11140000741d00303120052205000100840c8a0b4040400000d289030042189441d00322000c0364401c6074040c08075096520141 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 868996142 1250 868994892 868994897
    0x10c05010e06011820031503010f02091c260c0d2a02010e06180d0f020307050a08060a0c02120c010b0a050306190903031b02060915090d08060a051f0906 67
    0x184171075910b41d100420205e003149414140c1d40c0c4e07100d03441c640040d650915000b5030103500380000c000344c0145036400f800b1003290a030f075540249980d0b160011011000c0b58002030140ea8050005282d91105000601d1101001181d80346070652400d92941750045c02604100019406000180c07155518100406401c40c4c4440c503100884107980068110201b20901d14014100412500400400954180f0f900b0780043e1480e860044141031092a05140d444d050340a845850000500c90520f04014000c99031100007620113520b9000a10014102c2e40e4254011881100c0e18040c01d044900c0050040c038440f140009244404c1c60309000300d036031042e0b0007140b098202c2c10400ca5070211501000d0981c00e440306002034003040d80d10f4240e0040c44901ca81c0c00341118041000d064441c1c001501ca4064900c40c812030300b240c1c1c070f14903088950706030480b08181c4640003c42c851130100d000b03030441034100100a1034486640d0710341740030030700300442e41c0c051a2460310010740b2030b00010b400054075006842c262 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 868997392 1250 868996142 868996151
    0x90c0212121801150e04050106090e101505090402060c0106080105070504092a14071a180c0f060a0e090f2e0e0403180e0105041d0a0f02010c05010e060118 68
    0xc01d130f140c0c810b0702520880e51840b446100103030400c042035100c0000b03407130034203020403c0a860b059060340c0c40844448140742d09281c01d000c41c2c07000210b070660078101d510080074085280d55a50a0041d147c100408a010540d21020046900c0b1001c4c060103100780c00c90b82d47c07035448514002c032040a403600f2036100c2403d82c00803401010038100004580744d5400190901c542e030121040031505451042250190680d00c4100806c031111280c80b0b20307280101c080002d056201c8221800c850f85032840f80c401203074491044003c1c02654200b05000d001410348a06004d00c2d003481c5200414aea05908440782d1700c40100290802c07800c55680c508400500c541c05140001848a107202c40310403840d14042d44012941c064002420184902c4640a17481c1001c4500214036550b1988441400c80038000c1501c954100741e000180f14407080000c1050199400003450b05000c076484c1c52800856941059041203d28120040401c100340504d6500c0c000c00e800400c01589005540d4038510801523404499a013030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 868998642 1250 868997392 868997411
    0xb090f09011116030c0804031a1b13030212010905070e06011e050429070f03020c03030702150a03092a0b0a080406050a0b1302030f010f0b04090c0212121801 69
    0x90002d210f20711549030824034407a10031818442028001d45c1d02c0107000f15401102082d00948519042d8000c00d420014004000c90340450303001240034010000095002c1100d081001d490030080301d1140d45000707800068260300b162144e6041009981054140c9501201031090a59105c0c0e07003d080c1c00213494200041d0150070100600a1090b40b045003a1040b000c01c0b00c40361040d114407040c0c01a581005403654a042c146040502032503075440580142c01050b0f09401c843c200482221805a0300a002003c1c00d100d0954034003203174208003c81000c05990750709007000620b0b101110098440e83c0180c50440030805038912044101980109603005d900b8004071360001e81248146802c10b0b0b01c24030214640c1d503500c1001c401091841c0406030b101c0c0003034044808024041e80158022101d00895601603030721844480c00d0340c3c032988035220418404110070005411a5840381c009090148151494041c01240302c5200340c00c150807444000100d481403000000511001d1005007074004d000380a6100e1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 868999892 1250 868998642 868998667
    0x60512161b030513031103071e0326130e070302040b0d050414071203030e010c020c011404050925033e0a03140703061503020a030b090f090111 63
    0x111552005000c0088031903000c1050f004009035103a0078415a01d0607099580ca06140c9296104142014002e0040740004190540c5903441940503c0c80030042041d2a0702d10f0382c50030540fa6024031010302d9021001354503040703402c2e05c400822004802c0183e140209080c0302001d4030b03e00e0041d10480c03d251041008008001c12074041c0c9a001d07440540016940d5168180066014014a0350201e18000c0c41408510040400000d11505002c0d5900f0080000316600507406c0340c01c0000c5070310259119800c009400e41c0320310380440200700c0303248155090580e1000400c480f10001d441c0d100035440400210804000f44c161480808600c80c54140801d40b860a0b00204440c450804004210000102544265030209031004040d0302e001e1440d039502c91800300140104149070403991910446000309818038402d000d400700b603841007210140f4901c0345030f406400075031080f8100c4040c103492b200f142d2015598100c249204170b01c002e4030340f8880d280c0035900c6070845060059000c055241840358101c280e2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 869001142 1250 868999892 868999907
    0x10906030207111f0320031b0d050705040608060409020d15141005040c2102030601031803030f06060516060504060e03130e07030e0c0f01120606051216 67
    0x6516040069880440d4101001c0f900f104005180d0410a809018100c0b14000d01d0a044115050b40d02040b031005904007085120740585005040707140c060010a104000e021024182d18803803841c49403801001541403010f403003048a02c44081100410100600d5821600c25680200c040f502085802459400a0904603a20f04050040d148c204210f04121941da48210740703191001a1100e014501529107020b01102409554012424681c03400381e11130103181c00c61038590050280c41a007a0112034040025000100ba00c5d04040d251004030780c16082281c40c10125501982d0040303280d03000f02d21000165841540b2860400804008628103c20052505130304c40d03a05c000c02040f00d44490070400e015000d40002020705000001d40c07015004428803401c0c085a80000307480007141d030388541c2a8112110554081c0d0950490400460f092408041410305107005042103aa21805c03010704e41c0496042c0e800c06000f040c40081d4075142c9408101c11254041851001e420303a0040300c150040144 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 869002392 1250 869001142 869001149
    0xf0b032a0403210c12050c10061401031103040311120304081308060c070305160b0f070210140a0902150f13150207180612030905040e010b0f130f110301050a0803090109 74
    0x1941300305c1c014200903102e00102c80c1e01000e080100c1e0302c03000488403c8070081078030348510112119404074011083d4000c0c081c4240c184070f9401020b003940d540d03850aa07502400f44250600c02e0051440500e41241a000998041c42c06505000e485846460f403490b4202601c0d0001852603101404120703d0070701d1001202c180c982c0c140750541c0c581010702e096003411a0843d80041c0541c40031002c2128001202c0700440c4100b80719401c581c603452010705100c08440d504031071008440d58030000500c2021b0300d038000c1c413652031001c1c088100d80c0c810321000e809281c11100e90204201e10000303941e4081c4c0c00c0d40c800d4601802c407034086070342880003518001e596010607200f025241c05012442c0c00308107045e6802032008114104c03030350040c1c1910f490010019022406030b24400c2e490540005840d540500c6812622140030b094040c000342280c0400012038102c00d041801d407600d450002813406158040c56030940c01064400e0384950401e81003144000c255000b640ea19441440000043ea074080d211900300c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 869003642 1250 869002392 869002403
    0x303022109031e0c0105011d13331b1d0a030b07020304080f03070c21020114070c080c01020c150f071a0f070e0a0f0b032a0403210c 58
    0x443d01160520002c03409041800f04c0c09510305000050f40d8011200315004400c0e074215010107940d6030000402d44141340103005050b555003000840d000040105098a264040b00c503404008104c0510300c0040d1203850210219601d2025294844c041e0400c010100300210b28204a25014401c40420703540b2400341300180141000c180400d18660080c07044030702401c14601612a100442c11501c2e6881d8001c1008a4034540e2014001038002c1510368110181141d01c620352003807101c10f0300115008081c140306111440001c10001c1d00085d80006c215000300744210280102c60714450029040c2a002c804150255410300311190780c0f450800202c0300079001c01e2503450f40310400c60a011910440600c2c20758195081e60082c008030400292195100b1401030b982c1d215002c10b284140a412050b5110300300b94494042c40900806110002545c0e01c02d18a41040000b2002800010b040c00403411074802018800070b810300500c1000c1e400d5840300141201d0650b40111800801403400400143c080e01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 869004892 1250 869003642 869003677
    0x1005040c08030f0a1e1215180603060b01030506010f0f091203050904050711210c0105010f0603050c12070e041d010c0306050d0b0c030a06050301020304030302210903 73
    0x401551410300d40203481410210303034507840b02c40e5031803400e5070041801c2d002003001101e4440c86950b5003a00850404099078480d5802c4007040c540002500c422029a400440501c1022525103403c464800c40d4980300a4042400e41c610b041c40c1c800c4030182c1c08058105420081003182e2030344c0013402202c1a540a01c2c2c2110a42402c0c2c00450b100b003e20b40001801c44840001c100034154803201a007000802101c0801064841d00800e80c0c03201d503050002401038001d1102c0c0d501a1448504090f034006481c03c120340b421600c40c0c0028211a400d030040502d10700f038400e051209541c107104240c3d20000340c003102440c0001d408052407110900030700a008100c070f41107450300c01e615181c014030b211070343c0d040d011402c8010700d03400c6902030a244c59800001a00d031080c0058146404007003a03d072590020a044a5070b00c6503008003036a64001030050307154070740360b0790009a107440c244015442a802940c006884120b00c0c3c8c0424450b6080b454042c26140c0034006121703110700c0202c2119040350001203090b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 869006142 1250 869004892 869004901
    0x9120301210b1e090609210d0905010608070b09060306100e03010c2a110910081b0111010c170a061205070911120c0f040504020a0908060a0603051005 66
    0x15030940e00000c005100010312014401000c43d030750303a00b2003841c01000c2c0350921079032070343c0185a42c0c801c00c0b07411600356442108002e0300882d22000c44420801d061280324a04108182000300742c404030030003220715039901e0804100d048014003020f40540711440d036503842d090044002030460301025000c039100700c4120f01402449401029144541c0070081c00134080d00d404400040e00c0d0b001989001c402034000112000c2d0603008032024036500c80e6102010101c0000048103002a020000b0965814406c0180300420702450401001c601c650300c510540e50001010303000188031030070900c00107100e0b0381820010b05900740c00c110b00b122803070040b00402079a40e81d060a00409401250302403e00c50024101100a0090200d62102903030800c2805000c1d601a0307806a42c2d5612030b10250110510301c020200b60012440d8004228600002007410b09154944000401302c1e80103910100c0441d0444008004003001405400da020242001c00c011803032071511aa5100d45403030880d00c4510783d90f88000b8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 869007392 1250 869006142 869006189
    0xc080c010c080703082d07140723160f05030111041d04030e10050d050609061005030405210901090501020f070b030619080a050f1b090a0f15060809120301 68
    0x40248948130090204500c4c240b0b02e00403d410b10585d50140042d08099810513008c01303007812100c9441d406000302c000544141402c4481d00c1c0c008250382028003408000c2c1d80422644881030028103c0c0540295030f5906e400c0030142114002102100658428002000405044006a0310040406101d40c109548914040721302c043c0240348980d2210503100c09807009035000c406844159542c20082109840c6c0004100f14800c00701c13541584414483c0314003040078400d0780030315040340c840c40c00c6800d01101d0303906907402118024aa0f4a481c440230640b80741c40c1d83c0c40b504030002840203001401402c500480d126484503007900601f50110800004203010f501c4040d008080d491440031008500c81d2101415601c41c0e861103000d0352244103000400d007840001242a204044001242d016900d5020b414810703407420041ca001240b65852100308107400d041e000396810380700301c2000048424101540607001540c0a000041790f580300c0c00e06092030f2520345040f40d040d901015002e202449061070907 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 869008642 1250 869007392 869007421
    0xa020907050a03060b0a05120f13150f05130b1b04090c0c0b0903130b09030c01030903110d020c0a060302030c0a200a0f021203030906040b0901180c080c010c08070308 73
    0xd285c100000340300303181d80b80c2c400083c00c0c4e046540210f109031a100d00142d5440118140c400c92208100c2c81389102c00540c6000018118040541002c1100003141000d102221012209080d43e44c00901c0d00d003082006410b440d5905c00c0e08000300c0c21510344203011901507401540900491a565080a0443c0501500c00020940d500c0b882c3c800300c03450900b00301a00c0350040c04074021824607076140406e001c89050280d03a4070240240003426001c0854004401802491383c0a4045c090054500044490280240d8421140c160021715000310050240726122446078429000c2501c1031013408201241c4030221200746440d4644241001c5080d500e804848241c0c801e446800e20039a511a001c021144010b804058000c030350042d2100c0b02080d803a6140c0c44100c0c0c4158240e0000e80000700000d4031240c90300d4000401c03030000241c0c1810380640c05007001c4600300c16248650b00c01c41c00c008420080009807400102842c003031002031065580e40c40d8034041d90b503004003800420000504d1881c0c0e2001c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 869009892 1250 869008642 869008649
    0x50a0c0615030b09070915080a0b130b34080103080306041d0a061b050313050106150e030601060207030f0803041b030819020c28050d0507170a020907050a0306 70
    0x1e10b8802030400c20300041d44c030010f500c034084c19681040c07903060031f840c010205039044038012405000451260303507454603500c4000301455098845944400045569000c01d070344a44018405400100201c040403095107102039030b0441000444048800d41d554405441030449034458142a281e40f107820001d07000d4030401910800000141d014004c030901d00050305d01d405401104104107541e424040d0b500e0080d0b018101c01c0100d076041001c1000075000c4c0d4603043d1618003c100004020b42c5071807000c01102052a0032500007104564292298901405948e00600b1640028100545942e031074590a0030885009440210040001810702c8240504c600d0701d01c040340d001c0c0e0055030300e901c0c2050182d0000707880c07005864508020f105405d40001000000e0260080014409010001904100c0d0b0301104071403508000c12a00000d0740c2e00c82d9200d51000034815400780a006003016220b01a80d5841d55084c007d0b0351140600f2409621606016030704540c2d586800e0750b07644140c08042d006446107030b2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 869011142 1250 869009892 869009903
    0x150603040c0e070507080a08040201090308040f06090905070e01052110090e070609170a020a0609031502030402010512150a060201050711011119230415050a0c061503 73
    0x100010000c41d0a084415100340c6400e0b072a9a0301c44030f0341201d080c0942000188400d8081241c0c140040c001c2d29000d601c40e00c1451b001c0b900a46982e03507090340d41c00c20f9000003190200404240030841d00500e0510261114040410462810000c010308500c481044641030000018071000481c20312140c103207641c01442001e100b503017080d40301704107401e100d407146d03008451070001c01300c40041003c6050313400c460a540e5420005800c1004982a80c00c240d2310307504552243e0300c144401030f2a2040c00c18018000c50b142c044405141d030078880040b01c80914080000b6104004200043c0c1c1c010742607600c08050b50504000d00e43c0c03503907140992905150301e160b92090900e000011099415001548516110740e9180220446000c02c0382c242c811700f042410b540036080c0003040e4005400003e00313251400c1d0b0700c3c0c00c01000c071002c10840450342d00c040054005040001d070901080114a0040d0340e13600c1c1c0ba03d0140d1138030b03400c0c90f4001c044d20804031000b010345071505c800c034950f10400c0c0c20040143d900113 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 869012392 1250 869011142 869011147
    0x402010507120c2f06032a040801060f0b0d020f1b0d09060f050f2b060618061709010b03030c010e06090a15240816090e0a03081506 58
    0x40143c00100c1900c412613003611403030580c50820000c0800301d072001e2000070078620f00c148408100001504000c201c61800010302c42c41001050010000040d19441c62981940d1b4a05040100e403c0d03440b1600050407481c4184400c00c00c1024910480e090000b00c0200140c8900300c005003ca241d10075403142c4051015080044d0301780c56000b1401001c00c1500d41c403113130551a55003070180c4000e500e01c403003c00071550900a50f864641204002e152200d8108108d002d02180108500c403e84004050221603d5032000f09004290300203d01120800d540306290080e1882c1c41c82c01031902600c148200300c40102c0c900490103800382508801b043e903070300a00703070b986480c14660030070300900c07100303600304098801c0344089498a200440c19000c419000010001a500130440030005001811440c03441c02e0030185d4040c401c120041012405030060310040d051211040340c01000d42c400541090001c1460000102114100080c200114640c9820309032031680e20310400300c002c1c0c2c8440c803a254000100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 869013642 1250 869012392 869012423
    0x40e150d030203030a05060405060315060a0e04030f110c06040302060912071d010e01080c0d031701030f1a160c1e05030306090108030a09030f051606050337050402010507 75
    0x100c09180f150385e0780301040080d80c0c1d40e0003c000541e0030a0b43c500d130f0590400d40c080c448421880002c0c55200101800350901d0a684280c980c24860040f0b6040c0c000030010b002c105c04665002c0c020942e50100710b0000d1403941d014100041851250380702c000e201d000c001234141c03215210104000924003d150644107002da4841c0030060805814007840c40e850301390703c00810fa40c01140400c1d0306a841080051014015840901860744c1c1c91120035014445441d125105030070704030361313814082d51145680003481e60303003454040103031002e1103204071114000d00100324040f00b100c81100c07840229803400039001000d6042c0000c84225035207031355205000014110060001c000300840c02074000b9641001540c0e45c0d11040d44c0c507401045102000600e621030104040381361302c80c0e50710741c450040040d80c0c00604014080910035003c0c1c0d010001062001c4200240b603000071051483e40b403107640300d84a0541030b901c0c080420400c04448401199a100c010805592045094404032944215400c0c0710010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 869014892 1250 869013642 869013647
    0x50f0f010605190e070309021f02011409060f0601050a0314130c0b0a050415050919030203010c020304050a180209030a0501141b070213110724060605040e150d03 71
    0x2458020700d401101000341500003103c00384800300807601441005441a20743c440220081d00c84606c0c141d038821400321581c5510b00f030340200041490f981d034000003110111140c5044480d0801080c018044c3c1140b4100081d00c02da020350035a000c0b00903e002983d03084a0ba4064000313060080c0680300d80c51a8104004508001d0080300300458019000585020346c0c4040c0728a5a02c00d5540c4580011030501c410000358030f00ca0200d00f00b41040d4200f03076041c01c500030042102c801d0320003441c0a019600d00000c1056007030038480c1d620800b00620140d442d20742031001086083c40140b080d90b1010940000700011004194142d0703801002c020183c1d1344010481c2400c0703003c0c0041c00300300031045170000c020420501811040070381d01e003511303c0010b00b0400c45400b00301f00044082d110348801916000310200000c0743d18000c041c45807013a0014440000124104590030b404180712000031460f18005026064104050790220b40b445002c8286913a00e40c0d01112540701c4010100d900902842d885004254 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 869016142 1250 869014892 869014901
    0x403080910090822270906140a0b1f0c05150906040515041a04020d020910030c120203032a06010e15010c0201120917070501061707150804050f0f01 65
    0x20380340c04128101e1042580d0f00c8901380c00303500c40d040a6442071500700303451202d0b10250719105541003400044061440d141d48050f0796280c50034203882d1482d402003001c05030300c6100e00c2904000c180c4000020400300d049141111143e4200710b400e00c55481c45c01000c0001c00c01c84940b10600c2e003d00001141130032408213685150a0307908032424094201010b007015400c00702c1e42e224981281c1c50b0031000d02c1d00c0480c4540150007500681c0c101148490402c09a11503483c01030046014010401490b0720758140111820415040620407840707180e84c0802681d400001d840c03110715082c1c042c0701d00042404200c0101000c040346040f890058000002d81440f183c0e1006101c0d11000c1c1408030801070382c40044441d100300d800002d0103e4004005c0c003103035007210ba00494000c0d129410a01d50340e03480a000000c60703040b02008030b85c140e44a0006000c1c04200e000c10040c214007181c002d00c3e60700d08048070071441440958000041102000010381441410802400921842b80940c0e400c002c80c01c0506c0d020700b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 869017392 1250 869016142 869016157
    0x2d0f06080f06160224090c030a0302031801020102090a0e060d060c09060e030d08011401121107050705120604020d1e0b04110d05120306190f0f1202010804030809100908 74
    0x40020b0030718610560020440e03a0107540c80c0c5558111010313001c1171207000060003416054040c8100b441684042d10301304240b0807a207029400460715a81141d140c000322002000302e040c1107900511070b44040c0e4440d108000f09441c1c48540680d45540c0b66004210682c1004001804050911010640241d0055050b20664155a5542c06140605000c1c107030307149000c203e198001203682004201c010502e02c00c0c040d400c6014982240314040007075044064a4920410340c2e1010000200c2d03804101d001c101e00720040005a60000c0036000e00c2115035104c0c0c400800c00386c042c840b010701583c204080300c0e09401044d00e00b4183c840f5114428141104201400c5a00f01c40c1c050001503040c10721300d050031400316071b16031120061000311000c034680e486680000e050103410400404c2c0c40c4012262142c80f100c0603100310f14284414034505010802a01c0456001c8620280c030180c201c0090703640403061552090301401e204400f40c0b51450807a180c0100c0d40030741c40440d894072801c0e40c01c01148900a0926 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 869018642 1250 869017392 869017411
    0x90408070605011208090904060b0607060617120a0f0c0c03150506061c0e07090207081e0f040603090201090b0d0e010b190521031803012d0f06080f06 66
    0x75a1300c40001a1440403c0880500703155024070481e10380c0d240101445a100384a08004070340041e4110100b210360300500c0040f19000d450320003d002d04a04d00c54003880381010750000701781111703511400c543d803403081400c40d104100f005070200b10f100c1d0244c1600752041c0c0d0710504d0700a43c04c2c0d480c205401e000007405002c1c11010b0901c4c0100d4610f142913410b5902182c2c02d000c044141d00c104400d240010a04000030440602130003100050ba90070520151104c1070183c0c1c00c1940ea04000382c441c07405200545039075420700d081445190307902c800762800d80703041c0d9400e802c0019501032603000586460015510040d1080c000003104408640c141e00707c14032200c80100240011100e41007003000c2003001480e1083d0040c00070b0810059846c000820321820004900000b03036910b1034034451030031a8000313040c00034012040651210541030034412a20b02c0302591246100e281c1d010030b83d0389148101161003c5c48180c075419031009000302c50744540010113201048a0800640210b8280c071000d04a900404 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 869019892 1250 869018642 869018651
    0x80c01050901050f010b07030e120c0a0621050a090f080c010c0801080c091b0406090510020303040308160e060403060b0108010e09070603110c0d021501080d022a0904080706 76
    0xa40c4141400f6081c012001803520510aa00f00501e0324a180c11000d800c4d410010400948038071a103c2d2014817403006407500240c1040c81065050203030680441e40701d5002c205996800303010043c8445141425400003800200340d0f03444100e4108050248520003805120340000b8400030040b4a600410303c201454000380b00c00c800d03620301a030720b010003481a81b0003500100f43c401070a141c41c00c5032035480480c80d0020304660f0502e549400080d089500040003081c01c1c140305000c981b820784501100e4030020710086145143c9568000c2c412880508102d00248050000880b40c82c02980c2c451007010000c0e0000ea00c1e82e0381c0b42000005084100304e0640440c041d1800400c0d08042441041d1049078920001c0121601d0b0600880040c20070403040c0c4d5600b0824006084d0900f002c0c05016480b400c0f50b80188102403041d03503110f03442201070303021600b10b80c44007041c015041d4010800030651400a040c401ca1440320030701c201003c0141440351640f00900e2401c2004000c8540c0c0903001c05405204c0800 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 869021142 1250 869019892 869019901
    0x1031d0f1006031502070203010917040609051c030f020304122402120106050d0209040e0303061203130e0612010c050a17041a040606230306060a151416080c0105 71
    0x1002c8903940d000140441140240c042d41c040c109800800c0164401b500008000000d40c0b20000c1100069645111140000600300041640400c401d03002c1c0030112140785500e44001404080403d18940040900c41c4241803071095600a0094400400c81600c0d00083c083d920324204c0a1284540016201c9201400c05050000c1d1688241c44c2c180001c1d0703d9860859080001c10303182c1da00200788500c00c5035000c1221200c02c0d155402108015541e0000450301e83c03c10008100d00c8100e1181c4106107a802400084004080d42c8010380450303828004850050b140c020110700106403607500c5040e00d42c00d000c200b01089074418003c11042e491566524181104d02028610000c0c01303440207031004d1500e1013210140d800020101d0380007441034400140e45943c4800f00000c07210b1101c25a442c040e103210721048541818482c3d031fa4080c1c000c881c58900c640c02c1020710008045080000030402c01c1c0c046039411600d40351002c0740c18100144600c500500c1c4a813600c1c103059400222000c08030350802c00400e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 869022392 1250 869021142 869021173
    0xf04140712051609030b090102041203030915050c091c0803010303090e01060215011502190302070513020f0708070c08430504021c02160203070f032001031d0f 70
    0x42807211096a110740c809451754503030703040b03070800034045240a550030840091041c4001d4143d030a49440303034801043c0c4590b20f00700f25034004c0145610451103424101000512002001118508541252821080b84510701c0f1688410300b100350060513542d0010001c424140c200c41d8107022984407803440302c0985c0e2901d5040b0703120201da050021508400c140103011911609078041d040d11f29501c100e8400501e02e001c400d0084244034015800744e000024180424148610901d01e410701e100e80035072610421000c041941d2164103030107440b003a4080741c03600400105051000044c180703d0304030f440821240b0300d900d424100c091800c51031420004a01c012950501c083d01c5000c0000d1075100c0b45180c900000e05c0041d5203d240c01d0341c414100c000c0c5030340b040301851010b85030840c040704da00b0303141610520606141105a4102c40042c0c400f80c402080040c0d00340103035281885200420482c06511080107170042e1455000f00404045000300c81c54040c00000303400354011020200726100d5560b4010072 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 869023642 1250 869022392 869022421
    0x4050d110d032307030b010305090304050307050f0f030303070201021207031419150f2102280509010e0f06010e010210150f2405040b03060f0414071205 67
    0x1425401d0304041090329695019501515010b945140c0064121802014090706000102c40d10404a030362212030303d0003940d0510601d50702406c0354000b90f20700350a150000e95103c10344d101d614400d00581d9079000103a2140445050000703c0542180d4903800c0911010b8040d41005101c1c0d00300884400c0024195880790142c405441c0ca954400030b00768a40d40802500749600302c11481d030749900c800180c14003107280d0780540010100e0624000446082c40454071141585003c05855020170400394170145c2c0d0342070050b00c0c082e4241032640d1010f603000e08014440c1282540182d901c040d0701000000e0340542c8400c0e1a124100140072800c0716501c24005403001603c1030700c01750069010007070f16040c4a420350b1000390b0422400030b41700340c12560348501452100851700528452181070b00000946504c807410b2825000e65400c1690800f420903a22403450b0000a02c41441400743d01214904ca48846d88854041d03962030008140901e000e00000d40b81120a03e280c0900740e00e4080003424549102d0030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 869024892 1250 869023642 869023667
    0x108010e010303030c2109021c0c060c151b080609070206010902130f060e030f0c0105030408160b0f1b090f0405091501030f03120b0f0103050702010204050607050604050d 75
    0x40038103a400c50310200c0c000c1949084280a00445aa000c0d2800301c0c0c00300220406c00c1019800301e080074091051000310244c6800c4000e518a20b5100392000030582c04413507003602c040d0328280940c032a050801d01c072000121414003400030f1400b090341110801c1c003064410820b200d601e1707040c0c1c56100d80c8148920600202ca25400680000006220448107a0010400400c100142c0b01039036485207407044881410798080c10100e000b000500402d401c083c00754138034040c2d0041c0644012603223040081c101d848000c0000300602c0700019248140f00203000010034294000c0c001004d1071420000c41c1d10040d2007503400100705071050503800951521101201e000010150014500024a800b80030203010f0185c20b0518038040d00301640703810203040102034021800b800310182c000241c0c2c00c01034880e004800101510320300380184c001141d00c0e4500850159202846d000540d50ba0307001003240280205e030407041e88900f00141c1c10082c4100013481c036003c1d03409031080c0c0f24802e008190a6030780000c02d54 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 869026142 1250 869024892 869024909
    0x504061a03031c021b03030f090f07030b0f040804031a070207050402091e040b09070c020f010e010f080703110403050c1206280b040908030f010b132d12060b010801 72
    0x207100341d981c0c40903130060180c084181e6003095643e1580c00743d56085d07400440d21002c40550410410055250401c800c008400d07585d0302601e065419620b03000807201c2c00171701c0d440d0801e01820100d01004140c608850095030840003462098806080c000203444095038640018450f03031384c0210f02c91809100325000060300800c5d150051101a100498030000c9000003540281d6500c00000c540c2c035189611482100942e8900100303500500c10000719089681c8214100600d80d021040103980101442c80f907101c06007804030003a60740e8a03044014000c0d1003400386003010045000010044002070f840d5020804440c001c40b00043e910613541e580d0401caa42d20980c00c006040c412801c85080c07100400d0f11462000812294504000704080d1807014904840c500400001c000d541c0f404580100c1c0501000030a041c503181000420102a0865008070560750480d1504c044e600a511038292400c8400a450800c0d0607590340011255410b0803a0140d0f021401c2c42c011707284640c13081034000e040c0d80540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 869027392 1250 869026142 869026177
    0x31006120c050a1809020f1002100f0c172a04050102060906090601050d0c050301050705221a18090708040c0e0c0f18040914010e0a080d0b130504061a0303 68
    0x900f8400540343c5c0200503a00141c0044412070f268907a1003c803280041550001e2008100c1c12030b0381000c90303000c48507841001e4548120302d1502540141082056884805c0901c1e05448240c016402202c01003002c9040c40510b02c010101d4009440c09070080355004d800703a4103180d40d0800d120b511144129070407119900500c0044c811031030001d190f0700685000c0c0420b5000d00d911038004c2400c40e00241c815802252010406641c16042c10001c4012210b8805d41c080d604c9140903803030050b00149414608802c000400c2a4003213400400180140d28001450802d03a410076030000b404002060b01c00b1ba51107441034a0120741d1184010070540a61162003449240c0401242440c03c103800c6070780001c2d09000100082c80095513140110f45085014112169021803004101800c50301c1020804076140c00c902d50410100d00e501050741c0368507105003000725130300700200000780c0d07490240460000c0280c50081130100b8022181d00c1071410600e0155032803d5401451304045da82c2c040c070520f030881d140c110f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 869028642 1250 869027392 869027429
    0x16020c040621080f0c060124020604170702042c070311060a11010e071e0b09150c24100b0319110706020702130e030414031006120c050a 60
    0x8030907020000707004504150800342c07811040c21540c0e01c101714005942d0f100100502000702c402507203003402c462003000000712040e0307800d01a44481c0000c1001d8548445041304440d12803541c1c040740c04640d0300030010400d0105d804090f450300440650303280c6030150070084c00da910700c800155040c207403500030800e058000642c802b006901d5102c00310f40f00801c0180044400e540d4400d0180e201011b2081000e04550b90616034845030703100b0380ca922555800480d80007008100705c203004440c0a1541a07810f80b403580c10303130052030300c842c49280c01c140020301c500d4074032041d0116441412080e561411440c0d00190300c0d090902042021140034003d1407480800200c0d29011000000004041032302c100405c001c5a4060b1440003038100b400d0684e04140c00240e07072003c514040540d0052250040c2c8100620b6060500d042c0d9603024502601708210241013107540b0f50ba50800040703901035400c910501c0f0003a210340c1d89240c01e00d0120006c5820460f020400300f0701e440c08071043c10030f484c40d14400f400d00269 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 869029892 1250 869028642 869028689
    0x60106050d0b01200a1421070501060b12041a0c180424090e0109081605031303080909071106070c14060a050f0108011407050703120516020c0406 64
    0x345a076a20f4103003c20101d01074051300300700e900400950400d0024001568050400d0104024410344090094100b101d02c881c8a5003012052864049042145a1144040d1400500504603600546070907640440c01807028180c00001c0ca100b144900f03c030256481001500c0d110400d001e176074a10100790b040c0306109000780348801881007103c0c0103102089000b9603a18103050303406040800f07442c01c00c28174424400c4201c2c40c00751900307800010008001c2c806030364503420301d24005c58032010300c12118100340e8024840208151054000c01e5500c06400c0d0703682e85000d400550004101c076026900200c000399004d801200400d801b2441c0c40044d10199644070011540b40c80480307802c450382004030841a83d9001c0400516104003082400010142010394010543e014142d12145c0168100000c495164000741d003c3ca40112080c01c14680b41c0b562032500380d030040405070640f0000e910345410070400c42c2070301d4900400340d0900c0c0c00f41c9406100701001d100c1550b21b6802900c1c0c1c1c041d403256000900d0304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 869031142 1250 869029892 869029901
    0xc0115090b06030c03130f140d0c0b1303021002030a0b0406120b06062a0120270a03150b0a0b1611061309090512190c0507051504090b03060106050d 65
    0x6c4c4c110340204460f56541d1001440c204d884801c7c0c44036030419800618030b05042044400c094100c0c20000b070300c0c00c0c20782c1e940c042050004101c1020a0f0001c00b240c030416008004009a43c0360b4032409540702e01c0c0c400b06100c02450b818180c80e101c4d60030900e0010315401103a100c0c032805604212942c03c9a41c51100340000c2d50b01c400008040d0a001c02e02c1d0030b103441e1604588000c25100000040385200e0300e4a481c0e02d420540152200365a50108400c0f180500701c14103001c0c512100e200c401d140d4445400c00a5885004c5034805818504c0f0440418101c02e1641c1c011162006c04640c495000c58585101c807a55005124260f080d600e80440380360003150020b4496109864001d280b20b140009901540410300300301d0303026208032074865004000b005018040118a041c0d01c40c076140c141184052001c481c003900021200510848080303a07010700c682400700300003900c806041c4d02c60310781a041c240c50716a4410310030381402a261000700941d918002c69243d048a0855850908280c0c0311a644d00041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 869032392 1250 869031142 869031151
    0x181710050910151e03060e010204081005061912050105010f08100e0c0d080a031415010e010c060c20070e040803100807090c080a050f01060c0204110c0115090b06030c03 74
    0xd01c18014002124038130005140c1d4500c40c03100e5440381da82c0ca1450144243e03040c810001a80364010f0101340a0301d2300c00101400c00c002002d2012600742c40305004100b04403020740001051003d050342c0030500c0316240c004d15000b035104200030000c5a0340c40e06261400c00081c010710046401c861022509040745800c21403160302c281040c0c8245002c000700040d0007020304041290448404a40100c00076014402d10b03900190001d078210300303850902210b9884135185c90310a0305012500800a50607481007a01400c2c8175400801013004090162014000070100300046004178194103140c80c413800301141341c00841e203d032a0000c01a440e0740d51144403680000f4075440400584080009091800700000e80082200840c002280000c1700c0000b4101c1c94000e0034010424100418420001d0900150300c2c116442840d00088208141c0b0000300034042c400c82c1200b40c49400b2802c125034610651080d010801c40748220038006070f03941000c400342c0d03501c2c1040d180c0c8444240f0009104101d08401503034807 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 869033642 1250 869032392 869032421
    0x1051b01060503010510241709390d0203060423011401090c0c050a030806010c020d2d210903061505130b130c181710050910 55
    0x122620759003c41d0071694100c40000489902080420507204000c281e40300311100a80c045500b1030364240d010b4035800881100412210300e410001d00c00400170302c1107400005001c016024144810803980d001c0840c0440d10910541186020400b9460103034000c49440f54050003511403075640da16045031001c24102001e4400440340140c0c50719800c04c7c030420b10f40c078960b441c031072106504015003d0120785901004105102c0007040c498046980054a1448c05901d85815101d0340d9030000100d84d003a545d00b02c001d4100404407403031820040554418030070008800382d10846000300528495408070b0201d4060440c04c10601e00285441c601c02100c0e00c214a2410003c220b2079480d0b03110310441d810ba0012003940d0500010900003458843c1044002400d40d110601c855030565002603400015134400c1d400b030594682100f24441d0107400406101180e03d182c540100380e0b41c110103000103945001e1041c56010f48074007ca1010342c144901c501480034040103010b2140c596075080d000709040350804a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 869034892 1250 869033642 869033651
    0x30f010b0306181612032c0f060f120103050c27060a0302090406020c0705061c0209130606110d0f09030f021219050c0303030705070f2402190e01051b01 67
    0x1525100408810082c600c0c8a84881003200504009002c10350351100c42d00443c01080310300c4100d10349103448000c5c02030304823204010343c1d807128005039040c0b003101c20400c4103034404181c00015401c4220b255041f80e0183e81585c902501e100d041048808030a040c1a240c1c541d40300d00d0034982c0384c0440c00a91f00010103005800070684a8001074075090048504494a40e0009141c803a08201448107900811080e0350403401e00c011082d66640b44003007100030300b212075808603a0244980d200880c0609104080604008003502d17560010100d00300c85c040c05030133102e040c400c180011312404200702903102c26560000b2881c2103940e00010981c01200c2079901c0395a4694440d08250140414696980000c101d00004240340c0b80590501c01b524041a1203a003080c801c121940d90014111940c140d4000c034050f80200c45032521045001c01c0f840300008410b1880307452111b00500344c0c020300c0c0012420b000c64012005800381118001d0041d106113002601c01e01c001d0303414049402d50111008400400421b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 869036142 1250 869034892 869034913
    0x9040b04080403150b1f0212160c03030c1a1b09010e0315070e0a0e0601081b1309182001050d0e0601030605160509011b020d0b06030f010b030618 64
    0x441d6400f013030903c041e80303641d245540c0c4120718050344c01114075009a404c0885050490074060740700e030f01c0389280203403a450010380000544000c44103596515441030800344416100d0400501601c4d9035182110702c203d03580e100003e2810700a03c1c1502c0380210a6030420b42c2000700c4510421500170b06441030610261100c400003950b820311004401c03902083c070141a904d04114000e002d05e001e501154094150107500740045a0ba8060140c0d10031020700f405942074840d5406603d00c0c05243c0d8204c0030860780450207100f485000e01000c030449400309802d0081c01002c14007445040e84016004180100324040041e903c406589900d011410504282e4200b498110b02c2000380c440c4204500140d400030300c010700070032000384100e40e000307203034070f60458042c514401d0040c00314800c0c140038a0600041194050300d80c1d00b203218112240e035014145920040051410069451007562501d01c28003610140700c0b6502c0301481111079500009005000da41c0341e0151400d40a040c5925000e4603000341160710 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 869037392 1250 869036142 869036153
    0x2d06060a14060a1b0b070f030b0604170c030a0b01081b030d0f0306050307180f060609031b0f0e0a1d0a2907050a08090c180a1d07031b0509040b04080403 67
    0x1400304d8040c2250503003038546110010070302030090000805142c81c0c5109000207440b6103081d54107488042075140700702401c055006151200e00d0900e55858422540003030704005080d200c041c120f4107250225110440a02c10a90b224403034040303e02d03015480b400ca00505103103c0d070702e0501808800e0030002440c94903030010909109140c0c12504400390184205801003c1501c98800e6403508a0780401c07809013043d40061045560344070140111007440c500c002c03035460081c03028006010b62604940100d03941c1040008010b01200e4071540c061404150100040181c1040100c50032480054010348065544212410ba410100c01310300b419545001c152105007165105d005050035100c0319142c550410000380300f010001c19035070068020030a51140ca455202001700c0e510007803078001d81c699545c050041c0c000c008011010200c105000f010301c19555000c00c2001c240e0b4043c5260401d8070511100c903400700215803299542000e440400540070030101107a041d0030511903185140b500d85e594544 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 869038642 1250 869037392 869037437
    0x151d0a060c0201021204080a02010c05010b0409060e0c120309041808030a05061c0507030f030c0501240b0301140607020307090203040606050406080105060f122d06060a14060a 77
    0x403004034107040010800d40d82c040199410f503200b06000d4a2420342005061601e032126090002d060110780610042080030a411030000c4000c0a0010803001400d4200400507000220f40c0e003501e4051103c0e201a50305160241c640d000d60000021494505101d080c00700030f000f07007003004141030160708072040000c80c0803005500504c110361002c01e55041690400c0040252416101208400d8100b00c42c00640081212000c5a802c029411140411400c06403813041105100816551910070704444207618043e001c1c200440010740c0ca03007515218500400644400e001d410b11021010085200078900350006280d0b851000d0300395544a84c0d03c444d840181c0c0c02c00d840484410791640c030305009600307045c801c14004182400081c0130500300301000c03507400d5514118450081c034010001180303105c020024000a15090070303407400c110102001c040a008078903c0380c60900e0140d40c0110710705240a01c0a00203843d1003144031000e243c4007a04102050b0f2040f13003d0702c14011000d003000d0254005c0e100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 869039892 1250 869038642 869038649
    0x2318010905010b03010606181214030a030504110103020901021b0303190507150218041d030403030c0b07020601030b0f1f12050705190902030c04090216120207151d0a 73
    0x480c042103c0300805095581d10b4104800700b10710403058000750107207100110f044581c10070171144618002c0c01d2003041070880e80804c8115220020361441c0f0598103900051003280511070350b11203640ea90700114203901c02e0a582c140180d00240035070348207481003010340c2c070840c0c0c001b42241d00e4401880c0d402c03c01c100c1000714640115601043c07120903c00c0c20321014100005a0000314074080308140b02e910081b461081c42c82c011552040b021420500c1d00395841a000615011642c88131399030b140c01071042c0710440c021a058891200802e08090000903040e0580381d1000d014845641c41d040b1050044030700901602d2000c2d400030b44140070014000050011702001a045100030005080640c5480d240340d0065004140004c004000c0c412444c4500055070302001d00569203403150b064401142c0501c2d044007015600c00514509000d0158620701174080c81b8980400e0040041403041c1e803070701400d00c611000101d50701020403c3c07910451000f10401044005001e5200e520404580101c00130781 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 869041142 1250 869039892 869039903
    0x1b020f0f12060708060a210213110a0e040b100503040f0c0b07051e0c04150b040b03010302100e090406020a0c0b0f100b092416060504030f0323180109 66
    0xc103020038641c1c0040b244d41e0000c0c060ba08100703407616010071130009101d201902012030005520358000c544e01d01c0410b10741c0e030705000740922055041c400c0741403e071741c401c146803004602c0b00b200360b00c102d0800d4000c01106e20b4000307100203000c0039078030402c2c0c400d0380c0700800440300c0c00041010354001a15111b040c201a00303010380e01c0c40c0c503008286007982c90034150406500c02c41c4078122008901e5a00000e00c0e5503d0716003920045035011014006122080305600411014030010401044445040b0060f40c1200d00032280c1d085001c1548600342c0381160070443c202e41001a00ac0010085035040c0c004100c01032181c64a00b0041050361038004604105842503076424a14100388040c0c0d8285810880142041c12001c61403e010640041d0684910001d03410b255140b621142c4e1418079000300f900c0751800700ca0224001400381d840c10b5001003008860440225195401451649120b803040c0302d20001c28a170950a20020304150612416000b001480c1250301c003040402d0205080c000c2855461056 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 869042392 1250 869041142 869041153
    0x10612080306150d2a110c0f0a03060513030f090f0e1b0309010c0e0a0605041502030c0613031e0e0415080d080a050f071e020a0f03020606101b020f0f12 67
    0x1794003c55540e5541c0c0c075104101c90000d051031402c8020596070784403142240d402226030070f0213000c40d81e41ca00607840948500c0c0340000300500c000c2c1075104005400d20a603500741c0e130000119003e84520002c0e001d00b85100c61400f40034424080e24425403030b0084062074540b4040d150120300d8010300d6000311651059a5160407846a60980165604c19004c2040301c1c4c1000c62820954020610b000d14465503115400d0f00510100c4e2500034021925882d1600e429120140303428080d0601c2101c800c00210f00080c0740c915030064000180b0b010300c0084e0f5980e80c81e5002d50040741c041201411403461001e4607502d5403940040c880c6c40c10004400502420749490326107140110001e0212040141200703d444495070401c05c00540c454403940a801c02031074410005004020101c1c03411512135401042045a0800142070540000d20300d03104e02821a20381981240034030f0300311016200405c41c100f01d2608001000c0c0146018410b00f04206409801e0001c03a1070020001046800c0c100d080900030b4200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 869043642 1250 869042392 869042441
    0x2070209040501090201143f090a0507091503060906110d090209010923070201060f0909110d050d030209030114010e090d020604050604020d030c0605010308030702010612080306150d 80
    0x52141f210302c00072250007d00709181000010b42900d68400e0300c801c003070941d01c4101181840c00d0407411070000c0211964079140b030070142c0706a0720820940c0c00da485126041002070f0001250103081742d489420002c156140c0e156903568009012101c50031101581c40b07c101c082c40400c41c2006d004940c541071004145810580107004503860183c010172001824191807070301401c0010280700a8030b6a0070741000140d611084100e0043c00141c100c42c0006403603a200140840080d001902c1080c001d04650032800c0ca0350b8100300040100400051003074110205c69849540203034007500480e4005000407070754502103201192030380000d8100c181d004c004541401142041000022007030041800204984c0c2420b840e001c1c1d1f02d081c01007009104041c43c0d01c1340400c1620a100a1819035403018090089503101d00e8640c540f600121003800043d0307e410320000e0030410075904064415080764407030307183d9280c80e414845209165040c01a6a8100300403c969002440c40342000101181e4003900c01400f6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 869044892 1250 869043642 869043647
    0xc0d0609150c1d060301170f01020a020313090b090a15050a0b0d11030c0405060f0c0d08012c0406020327010219030908090d05010b100819020a0f0309030302070209040501090201 78
    0x245204580c80c414500f05401c640c5480c0c040850b4103440307104a108164600810150349003190000140825500224500401e01e80010162802d0000b1840894030b40e5180c07482001100c2100812540c01511000419010b40080d4000d00c0252815111051017079290004180740c040182d11160001c500018041c1c10144240700e43c2180f294408501469030030513a402c1c0302c20340641d0198070311505000400314480c1c1c19103421144162551007d580f218401c442010308046024820140c0c0d40100c69100400c541282e508500d01103107840030543c49403959110340000b5003004107100c40803c41c04c1d44100480011003400542428200b0000d6a11920720110001580242d0004400c0c1402c0c03920b010001071811056807100c49041d11404941459800d00c140903280c2d2083d100d411584142d002042c40d130384509418810101d1b091820515411b548032102203204852624000884400038002c1040c4241c0280b043c240c041d2a0241c107001d05900010360001069030100c411f40e560b20f50030004c558 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 869046142 1250 869044892 869044907
    0xc020a050615060d020c010204120602280c0602130e180c06180909011113050405011203020703032015090d0e090a1509020a05030108160303020c0d0609150c 69
    0x442030b00142c810780c00c0020110729070340100d00e5400f030301c640c010a10160000f000d40c1500c00070282d8101d1621401042e081031402036010440c06241d5038064410960110800003c2175901d0109507075903140312581d81c50b00720081d0810f003940801d0350140600002c0b0030583e0315186001d20528a500c1c08080b604d0035805140440305006640501340500c41c601c0070000c0f0401c0c4120140e0150341b004441d9403220363f00d9004048a00c2d038040c0e948000b0440380d0329901300307015803003e40c0c8080c0c504128698039001101d0303c00f41e584000600580c40100140000fa105a5612003040c0354070051008401c1038100380c50920340000c5029441d00c81c030404101c1c012204015841c0c0c0e0001d9402c00642441303003900480c610b640c0c000c0c4881d0109451300c2c0c0107050788690311360360b00c000c2406020464a940000400401c1c5900a02c1118050b100d00d11309040b08246a1315214100d0782e168005044e2a010741c0107100e03460380000300071b0340d50651381c581030b001150040400c0355030b04519120009000007005800361128 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 869047392 1250 869046142 869046151
    0x30c0c0f0604030f030e19060b01090501090e0109090309031226060a090b0604050315041208150f1c0c03020a060302040b09191208040e0c0316120f0c020a0506 70
    0x241c1c003880501021130340140d690050307140a0302e404a21140188240d41c81e080e458405148011341c0384180f501130000d19801140d540384240d940000141d6034400460303803d200c5001708520b85880000401c004001da90200d001d071442801e0081115560381c44141c1da200840d00c1c508045458400c0024a14094440003002c1c10701022101030281461808a05084024050150703d17a03503403141c0d40003590360f420603940200402007c85210309a0020b001e0310f0b81c5010356040300c6030b440e0081c01e440424001e4011521031607004d00c04400000e6440104800850340003140c0d41c011008040c0f103484507489419540c0118020303018881c0061449c070500044040c1580204101031041c04180001e049410458940c3c4504441000d41050052404800311034070364801c04108454030704074004c02c003441000e001100c034180b115182558454880c074549100071142001c5510343c0302411513480d80913145545280d4418035000514085490788401221034410780500564001c12a440420604100b0075034030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 869048642 1250 869047392 869047423
    0x1504080c1905061303090b04060201021e03070507030804150f021207020102180d1a010f0f0f0e0604020307230d0f020a0c0b4c0e07110304030503030c0c 67
    0x54160340c2c40c0e003902c03088050116200790750700c00014800d26120b0180703480602400501d140c1c0d143d81d07a40c4003a00070744c440200c070a011603c0c1c900c030407051300b00002907901c206c04030b841d821300c0c0400d60341e001c6801b6a4001c0085811541b0b440e4140c0b241d070312612403000c0c42c3c104002c005950b4026400741d204040d100520610443e03004101002804010074800203202d101640c100076a614980740c02881c0c0c10110f402d071300c0c9150502c00002100700e40c1d250203408035501500b07901c51060b110300c1081e06803003140c0607000f00e00302c40e100071680e02e080c241d004541c010307024030301503c1103a0a100490f24481000130035045156010450322054525846030b8160385145480031450f001c1103103400b40140080d0103010f8500301c617000000d001321f002481e0161490900c0070321007213803034115081040d40036a402d1031004800d4613484045144204d00040b48107440041000401581c2c92400850300900a1410914240000e100000024400700040c2d4020540c20002d40d40341d01c49981e007030345821b1402d031a6070803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 869049892 1250 869048642 869048683
    0x302070302010e391e12210325020303090d0c1e21210e1b030705130f052404151d0117010b0105030c0702031504080c 52
    0x40071030045803600038030f80310b482e80c0c00405118110740e1814003200550351a080682c05000d61710116280c4031910820700d044684210901410b003450f9584c000744240c2181880321100c50400c0c0e10b4010002d0340d401002c942c800c0100d2203482c1080000c2c19000ca8000015900100600012140034014081090341a180812484c06252965030412800e080c0c181812a2402d410384144000003845940c041d1803207203104100000080f00500c1e04011100410307480308001205030350203e55002d80784c81c043c540d0005004503104902921034054401c50b1156041c800d070a0001031980b1900d207200f07542c895090307000170f4226600f23012805032600280b08411424820001e2640200c003206038282c0c1d12426640000c211a840c00071001d2110585c10118810401c0c0c0051000302005007461810394440e01180c0200000101c03455090382c0358030840c14041001030000401d91851b4201601072540002d0460b40701c2d10081e502e0000e2850155400c4c1e508120008183e403641c00c08120100089001d10b09200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 869051142 1250 869049892 869049913
    0x10050c060403030522051c30021b150114030606090601050d0e0114070903050a0305070f060f09030f020105071413270e160306050a06051e1201060b0a050309070b0304030302070302010e 81
    0x4108c920801c0c1d84419103000700d14506020000d81d06454038040480400c08451610b5030704995540039400a03828007441910011810418650029a0065010700100041d446450401c8503121004007000d0401509102c0c100c00d2088a0081054140d0b03080f0001405007410240381c1c8a4182c000c00042c1070120551003000095000291240300715010300c1c1c8980c60783c4544c5010011550030710307000b40102d070402c020b00c40205c0c80390344401a041c0c030030b84a00400344c50042c0e00741e090b514204c2c2e0b8000800c501c11805d00300060560010590707400309441a65a544d00e65800566104980541d100060369031840c2c01e41c1440903100b030b51004a00ca50041c6540711a45170560110f580c0d41c00018080790711074000c200411100d800480113400000d01001c1800c0c00e20302c00030b54100c28080300c1e0380b261440b6220909a50018465201a500c0b24240540f40209581d01514190301c081e00c181594860202c001a03612443e401030760003103120765805139031003c580c10024251041c0c0070412885410070304210 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 869052392 1250 869051142 869051177
    0xc030815010c1b03061d0d0305060609010e060c06090c100c080406120b090f07031a18040f0606030f031d03072c041110050c060403030522051c 63
    0x41031403988900d68066400000140b00e880412130343c40203080c1800d11801c550790f0012032940c00c60200c4400c08441c0b0342404e0846c102d0036101d054a2442e003000081000700c00c035500c00d810b9100c0c08000906010315098202410f1480c200040b170350046039410112403800c01e8a01092032034801d5030a85084482142c40e52205015849148140018000c0514941c103540341540c2000350219001411469285090b0980c941050700880d6040c0c00079240100181400540c0800c000c4a82ca018091008070342107a60040c03160380020304141d03018440c07252100006142070085001461003010034990524039490b02424155410460041d803110140314a6280c0c0c44c0080c541013200c108112503108054070000c0440741040c034505078120100c9400800080c48904080c2d007660910a0314a0291f0880450003182c481c001d0000454058010034042070211b032081d001660000a00c25a142c8212020200c1c40400c0044003021601038200000003104440c51018080040d0f0b02400c2100c41d503036584015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 869053642 1250 869052392 869052407
    0x90a0902090f3c03100c020c1008010b09060c0607050403020405060402160b04170f04080c09040507060305060a09050403080411150a140d0203100807120308191b0c03081501 76
    0x40d05039100d1035000101c1c9100702c401c40c3c00c06550b03000d030030781e502d840c0c10b07020b51000780a040719004094428580300071007508002e01880804400381d40c0e890050390800c02402e60b59400401002c0e40058248007001084805000e020700410281c1c9940340e03110316604c1840180c50008040d548958810300c0743c03461803011401240c08050340300368409903642d510300e0104a001c20b0b200003035400c0b403c08502c001200107031038000d00642d0400c404035031286044404001da042c1d0304480041107500101410405640039811607600540300030025000240c480780410304a0344121016030018100310180818440030100204a400042c0c1b52a01801d0088170082c40a22500702c0c90800c00582c0c808410b00c880090b000e4a0845113181c0d420b640c0c07401c00114010340c00750f5034003c201443c02258400a2145002c01d5401312045d8140c5a2000c03559030f072502c500740114407080b0b5040e1507482c0d500c00441d806003d401801d41c012a9280c00013400700904008021440c01082030020b0301c8034000c0f2110581e0400c02 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 869054892 1250 869053642 869053699
    0xd02240415090213180c0801051b070f1506060e0a140f010203070209090606031501270212100815090a080c0a0c060f2a02011202090a0902090f 63
    0x1c0402c4100c40e601c0881d45000080c030054400c6031030503001d0101800e08100a8002c01c1c01442d54140c40f5440d58503003400c0b62000c0d243d00d20240e414401032241c500f1254050007e0500031a10f0100020a548940f4041c00382c141501241ca5905e5400348002d5400603400d031070f10f14090f82d42100383d82c1400c0f0342003080442e007401c90744240e040c00780b4160141c1c8200b0880d42103e502900c3d5259604140c4141541da15041e50810311a00801da40784a41c06501c01046040303400d03d03048010300d180c12403590611220850164141581c00b00880c82c410070700c1da904940910389610001101620341003056061400b08900c6100d80301015090120008000505074034198008014030b0ba50105030100764504010184010802c841c0800b00066803a080030348100e02158548031640841c001000b1090310801311000512400304107400000903510810f0409840428803000515140e031100015840180d00d40c08917403001d1f0005641040340c1030608040380000010781d00040707810009007465500c041d5404 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 869056142 1250 869054892 869054933
    0xa0b070f031b06020c1b0102150601080403300b010c02091b07021e1801031a090106090e0f071d01031709041103071e050d020f09030d022404 62
    0x1a01c410080419010300d030302c41c1d80c842011583c400064180a4032029420a40341480b83c04241582040d400410341600d003052800c011100381e61140d0054601110141081c0c0030003030405a0640181b088000c2044000c001d400400380c140b80501c80c0a080d40d07000500340d4100300c4814100740c0140c0715540025005454890f624845107002440a401e40c000d00707070046d60218045001950700c0f495280c030349000c000c0c2580d00340b4206a03043d5140c080541c0c01e20009100b20600800580301da05101e9200790003042c2d4034000b0030800d0340c3e110900f05482d040802c01c5800d41100c2030601418808206c58402003640d400b2070352000c02c0c00f101661003180144400341041410010f44803401100700122503a10030700802c00c05c407266022840180301d400c121640c0021030280300c1c1d0000340b004d10580300700c4440319a6507081d16040b003001085010303411680c1500700c101400d2161800aa60a011400d2612400d07401040c03203409102000640f540c10348580e8440300c043c502440049050521440031145540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 869057392 1250 869056142 869056157
    0x7020c0607350a0e030a1b03060506100e0d03020705040e070501031b0c0f03020307020a030311010f110d0c20030a0221070602090f09010e01140f030601030605101a090a0b070f03 78
    0x1021078108040c0040061956034164040c6070001400800c05023528003484017003111707035680820300c00c100000c0c010f600c01044100340030b09124900a0502e410951007441502c0e5110b0345e40340880c040d0340c030005c40000e103170700100d07018085075a042c85040d00400403003e565012220080002e469862130b89805090805801c54203014903000b00f04940820b1303809804800c801d07549040040c041444509000342070350032f00c0c054120300340f0382d400f070081c09a20309050710b0724002d1030715501c8004010001c8542c052000049405600d00c207201ca00c1040d0451000107513070b5401410300002c1c200506102c00c49041e1009100e00f6a00c40381c2034041d1000c090380140300603552002c180008408031044868280c0c054203032400800c0000081c8000c5040750041343c40946202011000c0090f0498080c80c6a40c1550002004001050b90740d00250340001600c045400c06a031201901800001c10050f070480b0a00005244071440c10070440c9800140350382c6000c2400c05203142d441c00408001514080e0030444003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 869058642 1250 869057392 869057417
    0x120c100807091a0910020318090a0608010e160509280608030d0f0507020307030c06320411090103051c0203090604080109061d030301030b07020c0607350a 68
    0x20000e44000c0e01c0060f0240a016514072a442c1c4158080d481c1e090150600210360107045000005a94480440741481840460315409100c2100c01c014020f07407a00e610341d036000440050a00c6042ca0001042e40940840c050046083e0301140869000a001d699140204501c0c051181d5000400303070000404840000000255000645002d4000b40014080024011095186c0b0380c0000140c11000c1c900380300f256510101a078a81c001c00d88050081080c0201c0240001c2903940051400240c00350302e001101558208408545107a002540e0001502420311003441042e080d0081403000490b03c000030381d8119511241c54044030f09124020700c014460142c010b6000380155800200044e0840d6150740e510004c44d406010306e030105483e803510340345c4e81c08501803075503103132000301d10a85000310f1469107141d070344850207500249244c3c1140502071400b50540c0c1c1d00001000720a008540c0100461207040442e074041c0b225513024440122400d1060175994144020b940c118005424007100780c3c4c4a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 869059892 1250 869058642 869058647
    0x1c09020414070e12030406120b03070f03230105160e040902100201021222020909010b0901030804051c230a080c0f0d1715010309150605120c100807 65
    0x4011007a01d2040042400700141582d01a0940c440d0103400c540b501100c035003829446880e841a40607400c00070310f0180d44004002001d0304a001c0305000941240d10b04e0342d0705c28103003100461a800c11506034801d000820910900a502000e00100340c200801043c180001400042040103020909000702440540d205680b541e201e24001a00681880071603555000000d00039801510000b50031000b07031001c50504444d0641003451068161008100740700700f034003001500000146480099900d620503c081034a581d403c1034001c0d80f04002c910b40350390034441080031980200221140c244001d5080b080450209004d0302412281018200c0d4030000761084203050040681000c1e01982000078841c20f04000003039600c40c104011015101014200314049030481c45443d40d03c1480c0000c0c401142c1150018040860140014100010b44102d1650307189034100484103820003461703039084200304c00d003010f28520156603820f202608008a00a000a0701c400e8034641c0c0004000402c00000c108030f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 869061142 1250 869059892 869059901
    0x2030a0c0b04110a03030e0112050907050904140a03031b0c0218100b0c030a090503070f060f2109020103050a0213150507020d06091b08031b1e030315061c090204 71
    0xf8405050a84d4032030316401c0140075582520320403400200300c00c40b0584110309a11030302d0301803810764001e844946c2c40c11040022904001d8020350344003c50703a4a000c41c01c0c7c7c0070401e00e20300610030b4a0200384c09032800101c1200c444003900d5038003030051510040c401645c9012015018a1568042e0310103516004401d2075110169000045041c40005e55144c401a002010748804207195840c40c41c41900e0b6014540c03601018410700040c008001d0f802c1c4681e5018a01d0080502500d117801d8440b0324030000c1325901c44c1041480028500d81e5019400c09550307050168030b40c02066108254a4148104070006246070b242c8504441007031501c2111883c10b200300100e44150b80c00401c4c8407482c07030050a00d0401003580c101d08031010940007007c0251006142d40100484807410b01039803c04801c0c90703c21003407520031031300c4000700d00802d0044000000c400d03203007081c0005007400541d203902d845c24513244106503021146200d039030188202c0c0b22007503000ca05d070807204000b1a4041000c0c0f409101250140 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 869062392 1250 869061142 869061173
    0x50121060204091103160507080d0203130b0426040803070f0c09050907090501061803140a020a06030f060503030f091e03030f0703080f1006111507020a1202030a0c0b04 74
    0x1a0030944c0c5420002c0c100c03805103000b00316100b16440b218603061001d440b42c2c802c03130030002d021400500c564000c107102540555403100000c0f004074111250b0b9a25103001030001c07181107072070803d03444107218484000740082c42c90945000d581490035040c4845d695481c060403200401d0001c0e0254200700300000c499a0780020154803809000782d04003000400d44411560040100c1d80e4909000011a180f28082d01c41f5601d20861100241c02d04dd80c46580700b1f40e01010943c0d04034441c2c18482c000580301d404c0701c50003d007202c0d03070000b0383da00035049444191030556112034800d038420300130b0101c00c000e010212210084c04440000c043c548550b24500240035803840150305000200790f04283e420803c2c000c040c0c1034480e99603d00d5540c2c4503003072492200c1040e079494000d0388540f41c0c02d0081e180107540540040c0d00301c20440b2641e49545554402035001100d1030b40040e00055003040800070301160a40700600e1600103941441b4080c5002411440c40145c050300c0c004071140410705001d5201d000381d000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 869063642 1250 869062392 869062409
    0x21b04091407080a020907090e01030f06091709030f150a0c020a080d02030708070c050a0204020a02030c0a110a0b0c1b0609091006180b0f07230a15050121060204 71
    0x900e6588041d1a200c40b101c1380241d000b021007034000380469204024074230544030719441d0360310103908580364002d4041401e101160b10325698148134020490410201e688000d142c0c0707c1c0c030ba468500b48249400d01d01c090400f80305560280110b4020045d6074a002d56116450640000e0a0b001c401c000b00e19020003210087c10a2100240b810384400c000e40066101c0c01617501ea50560362113150084132002540300780a802a0890200e45006103003940081007580d40382d1045a040034448000c0a0410311000d0382110142518050755000d03007005a0080010004803444600386241c00320300607140d6102c03071901c0e00145070060f005001c030b50b1020207036a00c440010340004418503000721160303004480d502680d000704d07002d50a0345240b500c2c00112001518540c5402604201c8904280140c07600480c03003c460341c01c0c1c1d40058a0551074003122910204c141000100000030301802c19541e520320050100f94003d01b014014000c0c0d15400329122401d03c40c40101091039102c6d810010001e004030b40207a8803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 869064748 1106 869063642 869063653
    0x1050f01050d0615182003130f03051c0e060604021905090604091107060e06010f030f0311010e03091203130b0d0608070e0a0507021b040914 62
    0x30101c0054520380506a01c40072046550603060017603c01c06992070f400807210419418216991141c010340345880c60900e04000852007a42e010041c129101644003c003c061040049a00e085607024411100e0081c2c3c010300b1000d0110f245074240c4a104d21008140585428802c0b078544011880a2624509806030240c130b45400c41e200541c2e00920520001a40c0c400d40d00541c40e540c0350400220fa030302c1c2c40c54038240301140d00101024881d41c1c88403006106c010f066824400c1501e80191031130094a0103850200c900410f00c0401604035400d1070920b503603140d40000540b40c0c410044030050948003448826982d00d00502440d40e0138400ba43c0010808440900010045000380100c00700d060b98507101580e00e000003507844013148541d40300401980c180c0d41d01c070715a040055407000d03000904846c110382c42c2044e043d142c0184aa07954524040800482c41811030507500b0540640b076 = true := by decide +kernel

theorem cover : BRFrame.Cov 868884892 869064748 := by
  have h0 := BRFrame.cov_init 868884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 868884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 868884892 ≤ n) (h2 : n < 869064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
