-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0757
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:36:54.452135+00:00
-- url     : https://prove2.me/submissions/610c5cfc-7558-4d77-8600-8cd66e6b8ca1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 135971223 ≤ n < 136151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 135972473 1250 135971223 135971237
    0x201020c0a03150c030b01022a06270306060d0b0c0d02031504050106030e2512030804050f03190f030e010c030603060b060f0702090912070609110d030206071103090901090606 77
    0x2941e085d01641d11400c1c1c40c0e0301680000c00000ca82c41082462025884940da20104001499400051a580040d901c00c9030b1061031000300b1783d1002800300e0030b96003281c0c11001042a40780010008166180c6000011300483c0d2150102e0907902c0c6010554240040b0500d06644074501205100d10a010750f00130940b20318100000010b100e0300074405c4402c40340d80d000150986141c83e01700702910650301d00c4c8048080384a203400040c00c001d028014a0382c544039541d95142e038205810b0481c5090700070400150309400400148840104082a5021444060070001071104002c03106400800c540403a5007019402c0403001c4062607415070000d01600c1c850303130042240700890014003525000d6000c09002c50034081050784003518142107031b40c2d44507082600701c820807411004104403a42008400f11141c1da202d0740d21500304082d001042850800c1618008044212500d0080d87c0358400340042e424081d07903131541100103000b0710840e10070003070103041d01c0392650f07695808a000785028800c500004501c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 135973723 1250 135972473 135972491
    0x10302190e0c1240020301021206100305010f12060905012409020c0d0e030f0a0615080a02010801180b04050915010602030406020c040b0a08010c031a030c18040201020c0a0315 77
    0x1102c8030b0101e5100c0070810b2854402518011549640c1010b00344c0741001044803003500c0182d90134001000d81c802024000400c13803c1030800d110846005000d5101850f050000601c250b0340030742c4040007100c403c582228a4007540b410324000510003513002601c25424980808042c105040c8801000020b1500500c60255603940300403c07402004107010503900310f40c841e200305911580490000d440020140c1d0805048541c5040c9400c441071421100c131a100c0301c081c2e80d01c0129000003401040044082e00980c1034550001f0041343d014064400601d0304070041c50f07690b0304203610038020413101410400240c02c0002c9060f40c2e0703141c003404040c5402c403481d0010544500c0401900c0c11520700b500148a20300c01d1004000c0034041640d40c880d0854245c0800107802c0d54240921004000c09440004116404001d2042c64009108442d0b0081c2c4c807030502840992108440d0049003022050032030625152440107d05220f58001d000c2e40c0520783c0c81c00031091100c50344100961041c06c540800003244 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 135974973 1250 135973723 135973741
    0x209040f200f09040504052a0301050601030204050d150609020c070509161e0c170c0f010b0319080409060b3001150908070602030909130209010302190e0c12 69
    0x704950260b05844000d00c602e00440c24a40c11050b00a485402a2030480708010311041144106104007072440d50120140440c0d42801e11459402c503100b860154030703050134030303001c10f0b03400580c8840100b180c1c4c2d40300201e1403002c003141d10030b034003400e104001903590b094a24107055031124140140d601c1100140c0210346051034002200c80300c14029203400b00c850003003d490703442c08ac81e80c140d1002031001048500e00000c1d410140c130074003d240050341a4030344c940796040034505000c1c0380f140510f580c5000c04641903940c00048031000390780f402607050002089443c009407540a958000350009040480c040352100c4040e0141400e020002080310481072000901103e03201d81000c9500281c100000600c140c109142e6920407000d858202407211594900c405031a1509035481280140c00c0454503000f1807070042417070b41e00702d490702c90540303580c0b56650000382c854241840002d102c2d50b51117205449402c0c0c801c02000040c0001800305c010381c540301c0c424074000d601c04084c010409995000183c1126 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 135976223 1250 135974973 135974977
    0x9140c18010e070c050c04060f0806160815041e0501061101020a08011203051201030308090d0201020c07090209190e0105040b241809090703050708030315060307030209040f20 77
    0x92451110580d81d072102c43e0b054a20094480003941d0900803d010700c505034441d4080c0c007004003001a07088020900d4045d0031410a13001070982004001309001500d900b40d8024522500083c8851410504890a2001030000c12182000d8100031b140f0140711342e1200041c1c1d200e81e040740e0990322202d0385080003c803451300300d114a807264004912040b005111400f030b005442000e0502c80c1c00d1003460309403007861020080200b42e04c00c80c0024040020010b0743c034400d00c0364810740d60042c0000d5003801e104810207a03c03004a40240c41215a0200300c840d21999a030348840300c0b001305120340082d020b0300d84442042806090154a029501303010541c1c600c5d0030040d40000e103401c0003e46205209406207407456030380d402841c0c0a1b06a84640040d2000b90b40e0362541c040c01103045400806000740b07149445401e00f281c5030300041c203940052003040741c020ae4040c1d1142c150f0104444c05550790f500c0700001d8000f03000c0c07140c6c582d800501d0319500c04896100795200094024071203003800e00d404034106d110800c80c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 135977473 1250 135976223 135976229
    0xd02040504060f0c0512040308070c0f061a060702030c060703090f06080604060b03010608130512040e0402090703050603030703210906020d0b03010204140f0d051f05010602070605190309140c1801 86
    0x4503045000900232a2140b080b40350020050701e06044241c82c0c2d030300c4003800b403001e040040d40c07519030f03500710b602520440c0c0f6083d4201000035a00c0300e05000032070300045d483c2d0f11a8484607008404c00501c030f4040602ca400480040c145004055070125141d0b4001407032070808940850046107072000229458490400784d030304881aa0b51407078102e940c0c1106d1300e441178040c000101c0f102e01c2640020085040840041d102400840014a21602e401d0041041c4458040c1c81003052610300320911829490200484e5240c0d50141007101c0c010303c41c0c03203600f0b4100c04000c1d45042c0d200c0c0f03405010010414290000c003290603040d88c041c0980d0841c141050b080b0b100f5481640000043d0b00440c41181c2400213030f914108400428004001109442c1c103420250880c003e089506094503084070b443c0c2d85031082c64007601030b92005010380d500b80039000d401c500c500c010110540303903591324070065030b8803980120310200ea2001000c102c12109529890f030b602002c610840c402c402c5400c00b9541220020909412 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 135978723 1250 135977473 135977497
    0x902030a0507080c090f0a020703120204150806040504030203070210021908040815010e0601030b03010603020a030c08060c04030506181e012c1c02191505070302070507030b060d02040504060f0c05 86
    0x350300d1f20300c4400c00a500c4086c088003801134403640e42c28992282c0c40070b44000c1c07800719140583d000c48110014400341006000c284200d160a00340404a6400025202042e506803880c24072041d20000c02c0e840c1c03088807000b1003c0380340503d81001c200701100e8098401c40e402c2808407072800e1055007150405603024014040c0465955001a140f907201c3d800450740050007400000f0260380302d03004189100c4040d0416120054802c2040000340410004a540b2450050815061a0440d81d42e81e03250400644842000c000c4120050380641c42402003c0d80c180c900c05403185840480304005c5e0180900b040e2403c650316001003c007007034809484c411070740d28214a0140881c804414504881405510745420031840340401320a044001503844200320342c000d005550900c6d0b400500c1405a44004004504050041c40154001076001494100f03aa501003a400600d0340d9102c00f0801a20400f10007070340c810b040809000900505610012111084481c20f10000b41c008505503030510840c9410301c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 135979973 1250 135978723 135978751
    0x2180103050601020c1c06020c0105060a0f12081b0102030a0912020f12031f060207030215180405040303020f0706090c0b040609030602030604150905071d130f0902030a0507080c09 79
    0xa191800c4190005450210b0342c444401b941d1076164101203800c0802c6260240c1c1d034801c180917451900f5012a0300612411900780308030340c208a94044c814856107002481c00602140004c068419100003403815035110008646902d40460701d1030140c9006a0305981380c00903040c01d00d4900e440407811340c5c20700c20786000501494040740c0c4603040c02da00060240d0041e42c44203046100e032042c6045c0c0d41005100350b03070003003501508600401221681c0074003422000c1c1000c00050800c03c8004812400840c02103500060075510350500790040c2c03254a000384243c00c3c0010702807007000143d40c061a246e0740268403812178540c880c41d46034a00c0c86103024820201c0c0d88920b042000503015001550300c40d6019101080c0f80380b04420345c02168a1503007140031034136150310401a0060f0300c0000f04901040503500d601c0c0c2402c0450100b89200210074207201c00a4541d24410300484090704014031007903000d41100c00700c80d2241411502d944e40d90280c02800d0081e65000100b901d081808940035484a0200b40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 135981223 1250 135979973 135979993
    0x1090c05041b080a0f110a0201050702011a130905010c20060618040c0803130303110a08040504090611210c0901080601030911180105011b050d031d030a030218010305060102 76
    0x10f124410f0080204550301c2d00c1d201e140c09600a0f070b0040c07a110151004040c6d482d4540b10b10301a00b540c40080216046a2401c840212888910740c241c1200d01c0c0f06407507890703501080540990142029410117051582418001e018180e440103410f009070a0044100c2c04002d1940c4c24140c407540e096603d554400310f1070100002840c40c1e250141e800c80e100d88001011a07a0703554000c1d05640000740401e03412519400100145030b0881008029111881c016080010681e41d072101c16000398061075008580d01c1706a1401c200459201a9207807480c1492a52154195020140c040720110b00c40c0100d401c1c1d07200482c01800207241501c015030016101c040855503903000440060507592001e4905108454104050351150b0041d5040b0b4011040c000c020341d0705040000d070070070b0300e0740c41481545001e41c89600046140802c3ca111030340b03464500812042d0380080c1d8064400800c0301d18403058000016070840c55905940102070408444003e05000c082e42d00043d41105c41c200e0386240541c11401c048 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 135982473 1250 135981223 135981227
    0x81503061017030c10020901030b0301140a020c0705060f090f030d1704030e0d030e011e020703060e1c0507060b1e01030b01030e0d080105090a200309030f070501090c05041b 76
    0x20582c0c0c01030b54040320b04011820f02102d1404c401c112601c0d50541d0300182d495200c1d6854007524400440503002404641078100d801c1100f050020120712800313901240f0080303511828061a80104002009242ca0746400c4841c00c425600200100d8411001082104900d090100d4641d80c02c0e03250303490319910050200240c420a030340c010011010040e02da03040c2805607a400c861000e4050184d0390340742070800c2481c0050000302c403e65488000d040e1740f40c111081d036980040c5410540360700481c08200c2601013030b03201d8a04285d40e001a54851540400c0f103580650000140864030302522060010040d500c05014074181c23801660508501c1e4400300903180d50080c0c000508141c010f15001442d0381d0b809a440b030038030062034800310000d040e40c80100841d240403580f464200d01240c008102001188080010b240700b640d181001c0001c2c040009458401d007401603c01400d400c40000740c2e02c03089454228020400a0012030780207400d0203000c5030074101840382c5555004450f48440d0031401603282 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 135983723 1250 135982473 135982499
    0xf0305160918150f020d020c061b090118030209070804051b0a0303051309061d06060906030103140a05060a06090f1406010e040603020d0309150302030603120307050c010c0815030610 80
    0x303c2c0d514191030b8440c200c40b00f4803620050001e100c1003a00103880708aa9600c2d035041800c06843ca0a100d203901c04040c5400d103000c2d0480701980b9003401d05028070552b10071b07100192a02d90744083e6000401c1e00c10000704035040480d940c8554462420303581a10b40e80380d070907000b240b01903d205400c61a10310081c8006405a0014100701a03c107000180c00da56400460342038900700c2e04001c0003248040c00d17141d1503c2160a0399908510100c035000e050005447c08030301e060005200141c9258258022102da884050111500198111007900c580d4680541107030043e100500ca50304049140099082c503084040c4a00c0c180480041c61100164841c0401100c1c0b500d600f00342d0300d42c000c3e51140b0000050791400340c91441d151081c4c4070000701c240b402200388072142c44080c82c1000c0c14010030420201b0f40d4042440c404c0d035094241c585442c0d444030281241c81d805030342c00d1041c2c65860318958001064124130442c0c03107401980070690080c209602459200c00c000d40c0c02d010320f8400c0c40800c0c0416809861 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 135984973 1250 135983723 135983753
    0x7020607140a03140907050312031e04020a030807050c0909031207110c0d050d14030f0a0c030207080714070501020f031c0209091e15030303060405100f0305160918 72
    0x24000c01c1c180c4900880013003502e400d0b10703d1010b40d80941c41c01c10460809104000041405105040c1586081c41c032802a00345910224070100c00c1060020303086580705500c80c80555048002c0603150500340c60201d03503d04500c1a5140300300541c3c07001803002000001101e0b00c100390944c040c9550b0301c41940569028101e21000c0030240150072144083e45c03503080404064034000c8000f03101c00c400d03030400604a001081c031900031000c0100704001141d00040c05030b40e000080c8140000301c1a001d10380480c004e0054410042026030001245400e100c40d060b02e110740350a05c1da095590080d910401665030b0002540c10310031541050050340402820460001e110366582440507107050030046c001403207041c01326180f0303180a00350075800440c80003d184466020382c98180c141002490703100005d5682c00014801f620854498000481c0d840d45850202d004000010000006644030718025450703804141c1580c0104960002c0040c05803101c0c0a140110384a196000000c03c1690300c03003403801c800d006 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 135986223 1250 135984973 135984977
    0x806010207081005010f0605070515040f02060c01050406142e0816090f23040f05010e01020406031107020d08071a0c0c010b030703080d020d060e01030b0402010807020607140a 77
    0x141000920074003d2006100d07211042100082d01d41c140b010f524458405900840c040002c24003040000420001e1402e04412400c1c121003a25611890544544074210350000d4010601003000301d4184015000503002e20b1103000288600401603076840900c2004450601c80c0399001112a106507041c09440020340c4d10014698140340d40310750390b03a40f40a0b0060380100d400e0701c940701c042040035118416400f040008000504c409000002d13282c4280500d034000284000301c0c400494108005200c4660010764000001d0045210200c6014000d4020b48143c1d0046402d00030b0074a0303200880000c84450303507402003842a10f41d20a40301c1e461580c1000300115002003001400600110700b1105a074414807856034115031b1180101e03d03003400d582c031400c03d07980258000a418000182c05000351400503800080041e00e801c820300d400c0c0c018111780d6002d0109000c44d03038004410b1088078400544914003e0b04c0710010f0784c03142541260745075400c840c03446c001611020020300c1c0a034030700014200ea00c0c1034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 135987473 1250 135986223 135986233
    0x907140906040e130b07050f0403030e040b031203090d0509031504030210140103020a0605120604050a11031e0c0a050301030b06010c1b0906080309031c020313061211070f0308060102 80
    0x2e1183c000c245481528404030501c40704402504100000c0b050950203103c41c0b410300c1c1440401c44210101d40a2804014203100080c61440040e441e95400018503140050803680c01d41045075041c4079690060762624018010040b81086650141c011902c0c6100c01400400111176910604039900c40c024000300c045020300303803070055102c400b03008a45485501c0b92844115500d184108006c85800343d000704144001480781503000c860030444150710000990300842c469480548140040c0813100503240d15403404070038000604907100c2040c010140c402005000c50311094a69000d41c090220b10320001201040103000162000b685e0a42001042c10106004d14050f605c2c080380c00d0800c42e4096040010140404c902c865901600e0000c10442014601c3c00d402c0d01c0c04280c4a0034030704aa8036040350701e10040c5002c075208200700c4500300c2c5441d4070303e02441c0d00c440c8001c2002885242c41320b45d060030070f51080040c02103001291222940072076803005080296a0a40302004010451170540c022 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 135988723 1250 135987473 135987479
    0xa09140c0a050f0607030e031f02040f050a080307260c010c031a03070b03041a07020303070f080f040f02180c07020429130213140f090714090604 64
    0x8402164a148601102500001004906100101c542a0300491207442c900400c04400c0d121081140c0c00c050b00f43c80c1290f00061401c011038500b1580d407109500c186800503014459201e41e90140007529800c0c200540e07815612402c11075441194000c450761904200080c00c00603041c0400318032110116808203200540019101c190754008500c1028140d44840021401d0f9901d4401e42071814180e45504034886110000310341e80d181c00c1d0290200d41c19000010806201030003003004041e0811040c08403092034055030080d03c0f07400c11396640c400300e1007203d600c4805500491056102c0c00440200d01c000b591035407a1004400340c2000c0c00e80c1c000200200104417072060311601c503c14460070230910b80e0703041d59105000449140c040f139081d07110341314050f120083c081c0c031a6a0b082218126642401a000150710304000d200303501418441410b0000006400e101c102000449188100c0b000c20b0380e41d1000c002d00c403003610100c4150b40000c1c45044044120b25401001c5e0000f49005444207041a807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 135989973 1250 135988723 135988733
    0xf07020f0106062a1707021807030912020d0e150c12040501090e06100509281503140a020f0c1b04051b0307030506180a060e0c0708120a09 61
    0x101c42e0300801c0000303603010880e000100c1d1904195002c0c102004404c000f000d1a40c0312150880049515020107050026109065584440c02661316039007005290302c007820004005070041080130000c40b00038800711980c42d00640003180e40b504d140c00540340c030307940c5010020422180b09960402500c42c10790500c4200541c1c0410801520303092100b0000541d5039041500252611b505980070480d00c418000c00c01019403103103c0032a40d991220b0810316114a089400035050355404030344000c0c9000b0555500d0808010140f1039400c640001c0c40d81d046a28500380c00310151410502103495000c04500031550481d069401000005003d802c0607040800121010b404c05c501e501c003100c0c1f005100c1d41101142c4c503081c403c454100000070002443c00c0c5a002080034540401000403003450341e0b40c0b0004a084d16140c40c9411004400a50001a0325000a820700189128050a0351580381480000c14100d4000219a44950031054a90402d64100545010180000c0c0420141500c500a68000913 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 135991223 1250 135989973 135989981
    0xd020d0f1e0c1208090105100501020309060d06080a06021e09010f0f0210020d0e16030203060a0b0d0b04030f1107051804050304050a06021b0405010f03080a170a0b0a0506120f07020f01 81
    0x142260356034802c0390a000c400c0741e087d40e00c0541f00c0c40900201314420483e903078002040342d03100c95040d0f6002d40c882c00f01c0e08220000f0311329030f446001207019603459035040208a034000c000d40c0c03d010394800419001d14040142d14090481103034046a6200248444c0500400c1030702c0b28003034144100c500306400f80000101b0790f041114000002c50700d07030280f00d07003591040c0310b000e030142500002c4800f0145543c00095139110058200d504040c3d651000d00c241340c45c2e54a00d240a250441142c0c0c4003403c0c1860b00400e500000300c41e80f0005510304035406070480c804140300d0100c030300c0200721100d103001781040070300202e0019104490610007000000713203030707103442403a071000b450550041c148502c40d0311424075510345505c401d80e229500e840014441024030808101c242c0350007801c03c42d2507032820305081c0e17043e08400c0303682c0b80d0b402c203000108145003203ea0040100b07070506a542604060355001170107280e020f04074031010140001c0700064480c59110700140d52120a41c8101e8501401c5220703054212 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 135992473 1250 135991223 135991253
    0x604050906030c060d0c0e030f031207020304081507120603050601051903050f03220608070f0c0605180d0201090b130c0e0118050601020313030803060f0a080d020d0f1e0c 75
    0x255103a44184940076001f21807580e8104040d0083c0c2800780075401015240c1c4a000b012104034004c0102261585100b0000da0b40500100400c4841402d030280d0100148101140c0c0d07040002d486040844010496000d94021a03a0000050400b41d0800c42080304034298a02c6a100060300c052b00007020038020000740c000041c1c43d2000e5541c454007203500c200e240300f07204000180210043c208101081c0d009520540c07003121403403c440c400c02141d404850325002c8003c080c021a080005000600c4c560003107074580740725554102d0f646603c507194181d090b580580c40150a01106c98005000245c81c010007601262040302c0070710840e5252a0340f001030304002e822010301d084400c0c14010078000c862082d290016400d000a504080c140f090003200c0300b425000c0100175000220124000d529a8011000c00000082400c9182e548030700e0090364be0000e848800e001031040e41c54141c09240124003002c070020700d540ea40e13030382c00a0b0461102848140e101505040001e12a042008103810454600c1303c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 135993723 1250 135992473 135992497
    0x709112701052104120f0c020d060e010c0305090d0c020d150612080720030c01110c040903030212010b03010605070f0302100219020705012111090312040303020607030504020604050906030c06 84
    0x21410517042c8000e171840c41e64143d50070321200d002c08820054120101c45820380d4111000134500c801494080b01822100503003032017940c20204514651901500054401c1c0c0c0b86008030b5480e0061068100c03181030132208041d4120038401010800b0514500c42c44001040040e0041038140ea00d01103480c15032660750099802407800301d1400c00f00801540340c01c0c04140c03401c50005002c0030f00350000352520f07180725591303040c440c60b02c0c01541001003c0c0702448450707400501c2080068024100a80a0341c454101d200c4000d102e00300101d82e002c1000c00b964169121640d540c0d08102c0c081e503130000510404602a01035101d00b17542c01480a03080d000a2115101c1c5400010800c0c201d0300002e03181c80110b40102e418420303508100c20348d09500e5417141c0d0080106001c0401c03001c00200d289480ca100c0c4c015101d030507004806000d504100000700800c11607100fa8221449aa1001d50403070031a0b5098400a620240401c010085442c04150464101100405030703050210004c00252080c2c0c000c0c0c030b011203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 135994973 1250 135993723 135993787
    0x103030503190203070504051002010b19030303053d0b0301030809040b100e04022a030c060109020c0d08060105160b0106020c0402030603030403031107090509070911270105 76
    0x2c0c1c12240300c01d51294044150800350309604012002402e580198015140192901c14203450210710075003005004001c090450b172469075005014402a500034001136022a05103400b043c404100d41a034920140728640494166030b4401c410464509152001442c3c3c44100d00030106601104400441c0210310402c0c007070359a4141c241c24070082d0b55080c600648180c07490708251500b81d0300040d003500340a404460059503044042a007003240601c0d0304038054601c007624001d40003002c0020041031030400074000c276080c90ba0307a00c81c0c01d0f0a038810a490a551904004000103c03107000382034058104605040290500002c0e1201416030003ca07403081e19407007082c00c01080a9601801002d20707004045d507040d4039602e01400441d50301d104034131005042101040141d541b03180148144000b070041c182c0144460300344504660380e58072160185004803480e0480c0302545114050440b503940e00410007260310110b01b0001e0310b03c01e64420b080c0b20f0601c00c0070000f850442c01c10705880b0742c80c00c00d045041c203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 135996223 1250 135994973 135994981
    0x32703070b0112030e03150714041d1807141003060b0a0c0c080106060503040215040314010504170903150601050f13081020070203120325140d020d140103030503 71
    0x18041d80c0c8503000e0600a400c0b0b00c00c100b150518007587e40394080c12038100102c4082500811065603c034503405480c4008030302880003a40540c05500f0340c0035082003444503003034800c161059510380c00588101c0ca030000e07040b6005201c90820398500c41d804603d9040000d25640c0e1407c10802d01e91003840094000f940c0208402e080000003407114001d0500c030305c001c02c0340ca8200317a0f018100e880054406842507002400c0341000c15824000c880186500805040c0c101d5100102603010344400d40c0c089800d20b00c1d50140800030355150068940c21000240181443d040103004444106400340101c0e0401908002040c800d8030280b00415503850f03c103404002c45850040c0d050700349155079402015150800e08911b1440785000380800c42c48161002c2c490b5940c0d03d51001910b4100820000f40328101e020041001c00b40003a80e60524030352828011013036001080c4c4044402410303581c03280d000003400380281508069154050130b80804480d40006201a0141c880c04402800341c0c822000108004100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 135997473 1250 135996223 135996227
    0x190c0c020a0e160507080705070e0411010309110f0a050a0b1206061303080c03040e0114030f06100603111b010b01020709060506310e0105040b0303032703070b011203 73
    0x40c0e0010550003207044581e00f440888011001c110207041c604101d00030595005200542c1c0071141200c5d0700c1310480780c166a50318441401b1800c00c680680e805000f41c041c102032035020740a52070302164001e980400d1350a101c0200300e00f400440c0f0860f0f421110540000c6420b80301e10b000300011380390940c040c58071401141c01410604c0381c010320090145030180720021119003000e41440030382e07907c15106516000c0c400c00f01c1c0e1560049500c1009407224000000800da401d0300c0850036001707c04d405031001c803104444015945c610503120103c000d081d04900f0131800b48a81e000210450070420b0076480c140c1c0300703481c60030303072070b2131f0410b9035001c0c2e5134520b0302c0f07c0a50707010000c84000700051481070182c98501000114603014031a40d4000e800d101d000042c3d81d9410114065014603501c01e50210210b80342c00040562000c01d004850045141010160a52038000196445000502c03000182c2400c2c290341c1c1d40a01070040c1a40c10988024070030500064605203240303029225000381208000b07407601300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 135998723 1250 135997473 135997489
    0x901080c0c1906050916121211011a0f0108040c05060307111b012604060f1113060f090308030103120c02090702160506180d0c0801020a0305060a0801020c03030a05190c0c02 76
    0x5c00c0b10b846c80044208140460002d83c0c0005540020003103c140c1090082550000022090b00343c85500e404c801c2944204d102920440780030055480c8080101c1e408011749000360140c5003d0074641c03800300200315a02e0220019070b4000d00030310f8000050490440074502d848028a0b2102c00038080024408065034410302c480030005c0345904104050380c9008690507a418017030009801c07541c440440c0c240300019904001607003e18030009580e43c0c40e181444804407249030080030006009403001e66400c038490004407080c0ca411200c1146142d1855642c5055110301c10209001d0100081004015a071191080340c8030716400d03006010440403090241300300c01e0031500202d11030b081c00c1c404d8001400c4402c56100b13031004103a680b0300360140181070961603510f441d40404103560000440c0720010b0340c907410990103801c040e074102074000c1c0c85d000000d090380101608070300c846d0701c240005440c100054100c04c1d0401485000908440141c03c442425100010303282004190300c10310400171402c040751 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 135999973 1250 135998723 135998743
    0x20030f06031912090512100507080c09090907090e0312090327010c08031005030c0f030d0f0c060903091d0106021b030106090c020606150901080c0c19060509 69
    0x809482c69200c1e8129400076001115005400e42c01e000e400074940314000d0351440094130000701151901d039070102d00e0030354070b46421120103101410030020604090007102c103c0e000324141903120342007013a0072061052070240201021014070032074a0004200c08070f4855040503400c4180a07607910445c0d54180011303104082c002d1401c0e40d01c1041040140c030308400b400c2c0c0008040d2900b038054160903400490355644602806000050004203000103101820f4569044480c2134007a6003ca10040d020480381240342c034006034251704001c1d02030b480c07603215243c0d41c01c010445040c0f0000031f111076103a0004844c03141008030080382c0818010700c0300c540ac1d043c01c20049540070040c80000d6043c44002034581e006641c002d1a070104203010f50850351780070342110700506886941017002d02c3c145940295140d00503201c1c58043c00c1c0c0000101039071450041240c41440040e10ba9800580b034200006805074002c6aa9070031b180144011711840c482c0e1442200c0b007d41c003a6002003554144655046c0c100b20a80c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 136001223 1250 135999973 135999979
    0x81c0204030308011d010504050603031b0f010e031303060e070f0e1509090c06031e1509060a0305071211030604050a03110a0b0a090302010216030f08010b18040c0320030f06 76
    0x19017480122034441160f1410358205690110745902c60b00c01092031030003001c0900700d03002d100b01d410310050100003c00c1d1a9440c04d0a00a100040526207980d450744100075084450b202120014804100140c110598001e210411658544d1b602d80c0c2001c2b003148250007081c264a802018404140c10803450600c025004482000580c104081810307138801c3e0050000307002c0d002c007000281c1c10900558404080003581080e00d59a07140525800d080c0a41f044403051041307050320045865030504854510540358032000500025060822115070442161b10403180d0800000d45180305480510149000700c1c40350005000c2189140b401801070b900001d19032040341c0c008a10100482da08182d03403038000c901c2441c00580256281001c0740a0f204038101040151075803c4541c041640c84010710038007884940c2c030f1280d03d1340c0300d0f61001e06034850303442400d0b5071052594036100680781c103030300000291940d8240011401180c241c910504d2041c8480410002c81c01700412001030484044541d01440131 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 136002473 1250 136001223 136001249
    0x92907020115081c02010b0a0e09010c03090b0f150a0303030b010914060d020f040b040303020312150f12160f030212060c2a010f0903020d0306060219081c020403030801 74
    0xb201d1442d0b03594890781e404403042004c51020810690003135205c65480440500f03003290351a1140350700c0002e204140c901c0d1a481d0718209070103034828464460084d00c00e41c0440b990318140c540d244204e25280000c1c2c21180b008501c1002c04150781e603280d02c0000114402c2d100810f005041c0300014210445641c03003d400030826550007c1140d41d40c20440303d40480d1036134010b8945401200d65185030165400c031650300e480004011040c0b5800001402031001d0700c8246020383e5036400070003810040589081b81d00a5140d040d19286441d050404100d09040a412a0385011240d0807690880200f6480344230b00c500301c0c40b001c0c4194104106145004040a0000c00041c00c0c8114042c50a1084812028070750802c15410540c0090302c4003100c8a0b00c07000c0b4024803000b22406002c00041401801c110098031800210841c100d0084c003550049030328036000381000882d01100b161500f298180d0486080130100103801a98442030f0010b640c42112101c0107845c4d40c15072a010386850010381000d5000d0b954 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 136003723 1250 136002473 136002479
    0xf050108010e070312050d0902060414030706050c070302091503010c031b0302180103050606040906060201050a0e0d080106050901030f060803041d091b0a0315050a0605010c0312092907020115 84
    0x181c01c800070700035400d1b441d000d5900c3e00034003a0709004119401e00250305c00d000040004000d41c10030170083c28160304406940400740e664400f80c40c0d61081104030b9810313030490b4000f0809132900c00512540b08124140e1440c3c514254030009007140d030307405004d00110340c0c0c6400310310030f03004542281c0d10140d00d00d003811481c0c615178103103262007050903040b0a4101a101c40006841d5100d21003a0340090500c010148000c5844900c041d01070071044809003051441d028000440001c000303015520314119880340506a420000126010b0303200751002c0c3e06041c0c4460403c041d591080c402c0b0401040342001031b40d1079500b00400d80c000c00000841c00300300620fa000c2401003a80002c02c003901b90500180b50900400e840d2004600004640d1f44040c0000c6a91a001091505a5000310b0b11034440300a08108150300c41005460100b035060006d000140340403118110320045038481c111041c020039280e40d0401490140f40207078200b8a8200b11020b462605102c41c1c6502401030421301003000b40c81d6982036003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 136004973 1250 136003723 136003733
    0x80601020a23030c0f0c1903020d0f1407092a0f0804020d140606100f0c0605040c0e0103031706010c080a030f0e01020c0304050316061e050d0f050108010e0703 70
    0x25150400d02c1c11240c0d844000100b03814104200c035040c2032044240d502e0180303102d604940b40c480382d4580e030340a8000b5140b83d960000300031081806980d401002034618007025201c0c244401000d14007241c2560700301e495800610002c2114800801982c100804d62001310b4400701805040030741e0406403400f011701a20561074001c0400c40c4402c9080c9880b040c3c550f11400020100c400100b00585900141c60303031031300129004904e4610801040d6404103010910400803603640d8603c001000016085490113400103c0b103070025900140a0b4884060f00c0b516500035903a01ca00030303881180416041082d449242038561081c079071203602402c20811085031903c62107100d11070090a0030030140c0e600100c0d017260141d580a51480b0700821300071500c405100b131005559500c45d0140900c2840303008906801d0b084002d40d00010b44405584544a0301c003c0c6413202d031100701c904245400d21409010885851055106403200410b00000210722035245c06492400c50301181d10980490b007000f02d0900c0494 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 136006223 1250 136004973 136004993
    0x507030314090607030e03160f060c0314120601180b0405130216030f0311031b0f0d090c05100203090d0b0703060b070501050a18050d0e0604180903080601020a 70
    0x10360507040082500c0075284506803144282d94109900c6031022801c5410b0584c4420b083d48049803c0c0c08a8041450810805803802c0261242544424a8400510000d4444d004090429100c0e003800414200c440c900d50030123412148803074910300034050403c0440d40c0d2003551414003480b1550601051410100c0d00407a23031045020346409104150032030b03900380c81103078100e03180d00038034240b8613003004111714000b025000c01c88503000010342001e440000e030001c42e03011640105884560440078020704002c40c0002d402081050f40e02d44402d1080e01e80c400e0341400780d8070b405845102c0074925036007880104912250102c011104541c000d0124a01c50f480f00c0200c1d5403213036044400081c0503503030940114040e0903079402c0003d22540108600003040815001180661940c500c03e00c02c03000e141008018440511030040c0081c9d104075020501503003d412014090b98002e4246483d0070340f00d01001c80d101401c001d2076002030750782c0d05c1740c4014183e004170a180c11500c00d00c05000468180d4440420071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 136007473 1250 136006223 136006229
    0xb120c0a0e1c060207050c03010506040212040b060301110a020102040911030403020d0c0507090911030c1203070602180603130210030c051c0e2d07060503010902031906081006050603040507 83
    0x1920700b464101ea44540c280b090020442e40300b001959900301c5c43c5016a194401700100900941c00c11002c1441403805000f03446100440300703084602c0c1d0b40e0300d13200d4030b4410344c002c0d00c1c10f034040d582c640c0c120f80c01040c444000c5c4080b0138070740c00259440e40f80a40143c102d60004e555903111904c14810f00000a40c003188842c209062403808000791812030800f2810000c0642c40112000d2804488008024000c402041062011025141c0d90200b00f801c4c80445100c03e0070000d0f45410411a009c00990942d0140010800d044404484895107501181d190380c01030715243c4003c40c0c0f041d03c113801c40c60460010a00304045181c00d0240f07411069016001d401050144920f0801c101424049460300e5440740401c40d5aa100716140318160b1000500c02c1f0311100801100076a0209440e0012a00054500300300c41d01e42d44e4442ca103a01e0b0400301d0000b50006444618240d001e6042080302c84480d02509020b818050040c2140b4030003001c4e84022980541d11180c040c00040c802c01005ca600441c0c06021 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 136008723 1250 136007473 136007479
    0x403120309050c030106180501080607091205101404060f06050a092003041a07030506030303040b06010c0b090d030e011b0e03070317090901171b0f030303010b120c0a0e 74
    0x401c0916050b4107082200f21031540643ca400c074005000c102400514101c8502000108003503620f0307500582d201c040803103c0380c010070050304017040824084040002d20a00038000d888420362160079182c161912340428400c00e07074150041c0320501819205550b07004060341d0040058030b03c1c01010904422181c400c0f240d1080c2d66902082e40200010459021721601145d80da590b441c083c904075560308210880050380e0505000010304c150700900c00e160056100500035411a9130307070707554194081d500800e02d5041240748840e0400144001071518051030191014203100e802c10a0001c0803182c8e210100100f5038100a40112131901d80011117550b801c1070319148003c18403d1021074030b0851b09134001010100b403c0c1240152602400240c1180002103803107102a9a880e54862030f0507803100d25005e07141c1c00c00d240010000011203000007607100e000e00381c096940d40c400000307810350f0801d0780000c6103024001580c01346213012000d2160701c00c00030b42c007043c1465214940240440c01803429540 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 136009973 1250 136008723 136008731
    0x90f040309030803100e1914010305030717090607030f080703090b0103020d060e07060203070506074d0309121501060f090312050d060e060d150209040e160b04031203 73
    0xc0c414040000000d02515080c9411b0f6040041d0310320071584402d100c00a01c18500511804103050011035a4101ca40180056080032465140c3c0f014100b6400320003200384004100720300c440d484100140c00a02e00a44403580c580c2d0040002130300d034a02c020620340805240c400d10000050a0301411030550350195110442182680340010080c6001e0f0740d403104500c40e4007000100d4590002c01001c4944c482e200359041074a91800945001642080440b0401c40c1d05d207482060280022240381e640c0071001d0003030100c048000c0d403100c1c495046104001690400900c0050038140038020780688a00000140260522080e582d100344030180074040401a00201d00c0301c541f407240135808091030304011a000101107000c405895544041060340324035080c010001500800010f88910542001e00040780d550410707074441701201000c00088203034941c01c1c026400740c0d031200d10481040180000080c841503480845c41c4c5024030080d03024a00824003003006200045801d040540340c513940d810046 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 136011223 1250 136009973 136009981
    0x3040303080c0412300906030b0409150608011109010804020d21080703050a060b040b22030b0906130312051312030213080313050118080106060305010302090f040309030803 76
    0x42c03202e200300d502500d070b203036000445803082c0005d10b01400d000e40b01185c05001026404c40d881101094040184004140e1031602040403070300075000701100d0345d80144005405180ba0365050400680300300003100d036582d03402c002d0003912805d1190b080389082e03004103c0e080416040000700344000041c002805201400c04850800c0101c584015803e5408101d20940c50401040200851401c03201c1800090a0030081801404207100b0441a9901307182c10728585814181004a42c6d8006940c444140f000d4803400080c84460348803190143d40320b00c9003007450b400d045107500e1900d034001e0000805020304003480070000e50440055002403000042c00303c2e0541e18040301401141c1d44900140c0108888a8145241d0354117900900c001c0f40d00518403914191a8511075039280100341c070100003900c00306403c4c031144d13008441000c9480c6402042c0800300c1d40355100a42552625401600400d440e0401401185071003041e1030784c800b901403122909450702d610300903c0d01940784406004408000042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 136012473 1250 136011223 136011241
    0x3020304121b0b01080102030a0b0d02100f050c03030115030e0303150f18090604030305071704110f100306180513030806030c03030c070302120a0302030f0a03020d0911040b0f030304030308 83
    0x40b111003a0002c00403a002d6960b070f94a24080d600484c0d61540c8689810745414880ca403035803a02c500c8a0300901005440045030a007079407940d10421022017484801d010904410100f040154080d02c0349091b0409101c14026004d015039589002600c12a0000d004004002200722421582400101d9440e10b88048070000714209d03011042c10741100a4601e000c005d00d403040041d0f8580600d01caa9010400350b55003d8045811043d031160000c41c0c00c0000d070105000c81d0b09490003144c2102d00034460b078003c5202000103002c540c09665140082510388a0070070030041001040025584144024400d0745032080e88120303070300b190020007810b028020012607001d440c00c00064004a201404481d80c5900158903990349802c14407041f88290a44d1100aa200c0f4012948001c2594140c0045040072015808034071580c00107100d003010168240301407524099207006880c039860241c40d400410400440a01040d200d41000c490701a14010303805505c3c41c1ca0020803a01140d80501d803848194680d5941 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 136013723 1250 136012473 136012517
    0x80408130b03010905180606031906140405071a0a0507140c04020c010e120a0215041a070809010c030b010806040b01030b0306090622050d11010207050d0908010c0302030412 76
    0x41207010500c04000450344035843da120318020446030700804014401d41141d16500c000c2140d045030960040d0078110f82c0c6030201c03003038411818070400021450072408030140300307421380c101c400341d5517503004080400c400f00b0f0403111525140d540100580c503041c0020000f80151080c01c1c4020010b003802c020900841400348100018a440117000755901c501c4c40c15010301078907030301013991014020030b02100b0b41031403000b04480c6030a219801403d86004800c0d28a49c4a403070080068484090450390019100c10103000d41d8030a04803030b218000141000e0300003038211104206060f06044ca0408182080c0c1e0700400382a0340b0142c2100d002c12030403505d02c012000340c248203401d203030544141410310a0600c40460389c2442a005000d01d60103202070107c40362025150351002911680100c641200d00511600c00d00c0508024030f0005417405400741e84591401165024110004040d51010b000c8400207024405031480c0c645030a5095080c03640b2080076111111010b03c045c00080c09034400880501e0034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 136014973 1250 136013723 136013729
    0x50703050c190606140402031b0a021c0c12111e01090c030b0108060606070f06180219080f010221040203070810050a0b0402040b03040f08090d030c06060b0a08040813 73
    0x195588109442c0c60f144001d070405024810649203811000c03001400c09100380c0f4410381e05003444030b05021a440d044001980990210021801080303c1080920b03031542101b034a80000e59603183c0421500c3c2010341c2e104c09005498410056512021481940001480c0041501003d00408500c440345440ba00421408800404002c0321140c00028400452909812038003194195525a920038003040440d214400c40108002c062600680100740d41c1c0d40300700141d088004400b0100c6403680c0010b5800c003500c0410603a1070007107190038080a04244002104035100d28029400e1040c048180840070560b40c0a0800c0d508421001805540d0104140300052401a09a8800d2a421101c20380a017074106e4989030781c1420940341c02c09605042c421602240c0c02d10394441d040d038546542c0c0c1d008581224000f9038801f102404040403075030310300400c884d4651103a19121403510300ea103015020380c0e0150380440c3e41c0c404140504000585c1090348568007503800f4080642d2a8108a60b043c20030480e03070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 136016223 1250 136014973 136015003
    0xb061c150f060c0c05090112060b0102070506030f06040606080c0703030b030a080c07060207050d0b0103030e010c06110919080750030f030a12062d15050703050c 71
    0x740000918a801100d800503590007020303001e2996843d2418040469070030b104051700300101c408500301282081c2d0000030a424144180c42c501a83c9000203591600161440c040440003001806043d142078800c0c1c10007400241803102041c40c050700c16841d80d002c2c111000d414107448044500c0e0390394040c01340716aa1540061141d49a14040200c1aa121024081c0c2d0003d4424503201151034078000e4400389a040e809814042107a0070b55504545d142c500e200420305000002c2c80c200c2c0000c60a014820744042400109900d5030000e20800c0084000c0e001d0380241500c2d0314009003e507690124183d01a00c00d012410405a00c40010031a6030781c07040200c2c07009000e03146031044010f011601c030402600f40001c1400c0381600f5900101601c03840001d9a03003800d136004000b400714490065240c40c200c407002920006455a46000c4801020b24403510581006c0c0989108001c01c000d002414001e07184201030300c40440c00b00314000c1c02e2071007903031030242c2440004105041c803907808010b200c7c040c00f528 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 136017473 1250 136016223 136016249
    0x1b13110a020102070519020d03030c0c0501060b03060109060306150c02030f0106031a070503070e010f02030c01050c0406090e100605030a0605042c0d02030702210601180b061c15 78
    0x1840c0028001d4201d2501151540542400222040c112140110482e03400821000768500e460381d00798010000d007c40f10040c8400c400380c0c080824020310540c4014003215465603668036012000415028080c0c03c4502030628111081c05030000c01c0007000c64540141c00c0041441c005800028a001101254a21150300f03158001c000c100c01050219030b2404881d214041076201c5260644e500d000c100d4141c00040d03543c0d002039020f5881a101d10803510f0042c010703685850340c0c12102c1425034008484400c803d110019041198590000b120402007001d02404d200d40d0809019001c1c04440d1441268204040800800d00d80746469020400401c4028010404009082000002c1c2d17221500c07004c08140344002e0544c0007420103e088945c11040d6405180b800101707900f04481c441c050104500780900ca88100410311904000c91806403407240702c07080100145607201c2c810b4442001145000b624144950000541c0c08020545048aa07a4000c154581c00d500b000d900d45000394000810110a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 136018723 1250 136017473 136017487
    0x2404200313022701060e0f09060105040f0320010e0109030f020f10020f061027110a08150a0518060d060c051803010e0a030f110105041505091b1311 65
    0x982400c15100f14070404141d03600d0380e038416064a100c6549080c140e0812200481d0307081d01e103040108190711500c141812820103403100f28202d24021950012036044d40c4141e00b00103144c4030f11412038502442440e10b03883d808804000200161807e200062814550002d410219510075031000d10b1680040e005035994080003500941d54124070000d04164003c05000c105d02c2613484442000b9940403140080821100000301c0c10404043d010700e0460700d9540c600c0250f103080010040840c0e4145a0b600181d038104100c1007025204c0744108940315079510b000030482c949800345410034101d0311202d0f07208103945000115004980d8104001d00c11803400d4500348140341c101c4090414944278200000281d400c0c1414142241c680c0000a0700700d6000f05420f2001910031180c141030027400c1e150004880c040807402d02d094070780030f4034100c60140745d03a80040e071110201d1040f00d50142c0031a0007031403104c1102c446001c10f002200c0d43c3c180200840f1080110b500f170a0b0304107910428144e071200760f42d01a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 136019973 1250 136018723 136018759
    0x705010c03020711090c09150910080103020112060e131b030804090e0c03031812010e0601060f020105070c060b0103060b0304081206030703080a0305060d0209240420031302 76
    0x1200c60b104852607000300000604d41c1c2081a40144110b60300b80c906480d01d0348010070401180d460b9490092205001c100e2018152649024100f0051060300d52991650462002400d44a0350003845800f4602e052000c10101302524802c0341c00c42d54903511150482d0207403c240c18640d41401e109060140d442c40008108000030000f4411074440b104100a4040f030741000741e0315403281058555150b070040c00031072142244150151059500100075040d4100307600051420f4541000000c202c1c0c4d0484001080b10540100103406150420710080005203040500a012402ca250020340055901c50300070310284d02980c0450b028140042c800c40d182d2030285415800d69000342c054030049494a404200c16003400100c0d0030a03a0b92120000c0d0030b10100c0707442280289001041e8a92010940ca510b00160300c8500c600c9000c0c50001901600ca51000e14801480c0c1e04c180d40c015000c1c1d4036120a00d1580c8000c00c0c0c0c01141088002c048030780e03e4803011203403141240007120103980603143c3d0300c14080d120 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 136021223 1250 136019973 136019977
    0x2041505010f0e03281203050402030c0103020403030816110f0c0a08070308040308030901110705030d0c09120314190f08150a052e03020702040b06130e07050705010c0302 75
    0x600d0990728400c900300c480b0400c9921801201000390141e0200011043d4440d00d40c0205460400140c80721782c942c030080c0c840c00c070444504040400420341e600280001d40c02c040c4000b507034100b0203090945c940744c071395540204900002031525000d48084841800d0f0588240504000c4c2c0d80c909003205c0705800500307286501d0740c6413035010600c149031600001615183c040303035030b504494118107210700301441d40c2c845030345560000b07006204a559607010009a00b200700302400107240904015520748240c012200100c80b400d0100300140102c1240810604ea00c1c1d14100c0c25150f898546603c400d1005180c42c1c0c00e0340103c034000f01c03000d24600742d220612030b030004000c209840c681d6202109a100c0c1c1c03480d90301c00001ea41485400003100c403014412403e0804441d0100266a41e01d00140e402d803010204541842c2c0208000003a0000340d47c90075442d01c0e004403103050204503079461401050740703aa2410f044a91082e80c04003c5614000b074a20b5006606440c0c04a130020001d008825030900010029 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 136022473 1250 136021223 136021229
    0x10e0d020c030607051b07050d060b0909151b04050301060e0403090905100314031905180a051324030b0a050a0b0d0204050a02070c03052b0c11010507020415 69
    0x107210764403000d02503140000ea164001d400c03d8640a140c1429074001d402021080003a12070355100c6d88400040603110840c0345904c040c004d2100040945c910010415541c00160528010760300074403501803a201d480d00966001101c05198071815031040c1183e07540c600907580038a90552030207000040080080d114180300e103100f035035145000381d01c45460030101c1e402680c0d01c440302d1089a105000290602505505c038604e00b404481c206103601000026a0000e0240040091808a541d450f580c07240b034109032042d0760459003035110f2814030340803980c04000c500c41000300301d440d802a0041d00d189074031582040700c04152016401901ca041c4800020320030b449041c1c0840c070f8080091048902c80c804c1c2408030300c000b84440c134000702c6602000041c000240041c420103508000d0500010001c2213408000c41c4036030301618207010b40d517541192442428003502c015400c412402965290701240e03080d003040c0e0220300010710040180040307038103018001c0000c1d009407500c10001d0040840301d003c1012 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 136023723 1250 136022473 136022477
    0x20c010515010207030b060904140f070504110c150a02210411090402061c02040b0d090b070f1b05010f0c030e0d0e0a03060e010b0303120702010c0309020a0501030c11010e0d 76
    0x14074441d60300482e502c50380ca00c0040c05070602d01010074007500d00803034541e400c14010228503188030103211280d420848190302d50881d41d03015007003c00060409002d40301c2001440300b5000e046c20303041140c2c3c0c0e4680b0184d100459264515500203981d00c01e16a060740d591005907403048000d00c840340014240f032042503c081d9002400c02c49100750a1070200d411503c9140d01a0802e4108010340d02c18141c60750f01682c842c0090f913000d0ac0f01103402000750014000204620b0780204040140d414041c404400c041c012100b000f2109490304003060f000510500408d1759207036003c0611945041580c010910031641c030105a007000d200c5081580e254004806c040103c2d02070303401c190660300040c3da10980003411290803c0401408002040c0c45612550410402200124150780e9081c0024207507030203880d01d0795254002c9010701c90000c0e030911505290260381d0404000c0c1c41a6600041e5003100315100d054101611022102c149500c200940d10060b0003a00090000c0c1000e40000703078407082000300c8200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 136024973 1250 136023723 136023751
    0x2060a050609100b0309070e0702150a06060203310914071d01030b030a08040905010f06181206090b010b09150712080c0708030705040905090c15030601030f020c0105 73
    0x400c1c1c034061820900840f00d440400101e503141100182031600000d0042650b405403c0000418141c000c0c62984603e00e542e02514a0f0000c1e04a0486160070140611424503c1d0110500400340c00204490b418241d45034105008007003600030b0344600030302c2030f00360950350300c1e007500004c00c0d42c2c1a0304800b09000203202505507603680c480d800c48059003000783c0e121040c050b0090000480d40607600201d1544400f400b070364a09401512696503c3d81b0030360110345401d40d0b4038010000142c0d0ba130450303c041d02040c0750071001c820f0b4900700c0104960445c00386080120712444da001c101b01803a848111f503161b04c00031039003503981e5620000500d90068503c4c10700032051901191a000d146a0072906020390040300640728855280049400c1680101650301d96a0704100150228502c41c000e03512030034040d6200e0750388a0905c00000c1c04c0c3c0300068004003140e4010310049a850380c0790043c0310881c0c01803004042c2c4039922000124050320600f0300e940d06c2d851002482444c40c81043d040140b00f0546c0c109468 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 136026223 1250 136024973 136024981
    0x109060309050601091e0501120204050f01080a06020f0c0a0f02030106080c091306020c030f0a020705150a1409041a040c0503060a0603050c0f0d0905100c090e04020604030f0302060a05 81
    0x34003558024070000382950000700041c00f036600700c1c0d0b1100300c9290021448154003a908408141241c5080e0006540c1c0c6e443c8000f554214035050140076404411003911400c0c41d40340038001e654170038024038010080ca0700822000e1101c4401c1e01500c120700c120b0380450304008a030303003044d068074103000c08240c2c06135080202c0821221400a06a0720950014102d4880d95842c0c030007096120340740c039504540250302000001041c80c0100041c20f540a07040068a68804c2030080282c602119030b448580a103e10000442c40d010000d401c0e100e10030342d1400c158460a07004600b40100d84502d48400e80d01921f000c0d040d191155100f41100584003081e1020405410146820f82e90340c00101c421640c0001c0c6030342d06000c880c4c402e401c11900010252021410551100c61440068100b503540c03450903559030f04000c041c0304003002009840381c1c05040801046160150090100320310703000720a0801d080d04003107021074895808031401140c0102260803a0f481902c0d00079181c510644110b41d2150414003c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 136027473 1250 136026223 136026227
    0x24050c0903060c0901020714030a05060403081e07050d0504060605060a050409140115051e16030e010e0108070c020d0b0406020306150405060409181719020102120103020913080f09010906 82
    0x4c40241e02e05800401c081d0b450008101801d40d10200f030346415016005400d030004104110942c00340b8441e4583c0d500920306008449418540d480c104800098400c0c1841615900602243c01000c12a0004219596140bc010019007035607800950803ea001824403800c540c4413020300240c409050050001e40f8400303040c034035a07040a000b401b4210042c50382465044d8041c0e0014800c2100004441907402c42c2c0d40e20000c0d454100010326407030101541803020030140c2c001c98400d810442420081051040980005c05685c0014564824008100e0b40c1d0810340d9145002c0204856010003080e40300d2600e860000041e40050351580d00540301d2200e03403d10705025500303480940d003014140d60700381481c2100007400340103001c01d000703003074000a0005030100b4000e80385001000090801d06540d50035040e8110604c41102e0146c10031079105011502040c0c28401c102c2e4110b0703404681900c8a1740761100b002e02d002145a0006052040010b90900030010f103030040c1030b07100f0702626a80911a0703580300c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 136028723 1250 136027473 136027477
    0x5070e030105100e180a050309010305010e040c09111c091a010b030c16150b010206070302090a050f061c090b131101030509010f0c091412030724050c0903060c 70
    0x110f009640003248240002004403000c0c43c0e1201400c001d100080d03034160f640c0d605008081c1801d80d0260800100b000403940c060141600400c1048082480752915403a50b81d0001c982c0d010310318250707460f0079401c00c214180d0810f44000c0340c0507403110040d40003044007210060019900448407a41c2ca01000c242c030400c0ca0003900c0c100ca82e0105014030310b07502d646001e0a1030707100f104494030340c0241016050120380110080700b01e081c0b000c8000125081c40c030f00064504500101000101401005412850b40311109091f0403240c043d6100d585070400100001c81c103000ea01d03101d078007a003101c0030086000c40c81900f0621081c0c1c041c0c03440303403019241d0302c01c032152802003444e001d4140341c5907082c0640254420790116a20000c04400081c1c180d84049086e070589041140c0031000914040003440001d1044500a9800c082191144407141141425544130f020b0040003070059506980d5072035246159406c0c000400414000410036490a9900da21007030300590200d0780030384100e0703001034003482070001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 136029973 1250 136028723 136028731
    0x304060f0b0306150102120d0f200a180905040807030311090d0f020d1b08060a0c170408040504020301180e0a03020712020103020d05010902090111060613020313050a0605070e030105 80
    0x400f0701200c1d5101414040d114424401e11811440348680c84440954054058004030030100c0000c14149180041d243c2030384d003c0e0040d0150100d4427a00c00600d1400a404c6807130003e01d5040c105681000f40003402504c01442d0f01400c00740e41404100300400008000508806109403410032041d50540740004c0c1a0060054603900b102e10000c10b203001c50a130b41d0480d481d1520041400c00c03652041d0740c0d003010501c2400300341c1d203c00349410018451000c05006d06c80d800198403801b0004080c91303030001052010481101c0c0d4000c400c000101d02400708200480d0042c10001e0800d542d00d503506c101c2350024480c200c560580751440d050450054400200340400026016030051080d2401d04007800560401400128141a4200440c411481450081a000380315003400182c40c3c1500d60005080c0d100c1100e01d1144a4005004005013640c0d00c2c00703840010007800200503203036620b8004099208110840c0035000384140030009080081e142c10543c45000306a0301c190071071204000349030998070165 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 136031223 1250 136029973 136029979
    0x9081005130803060f100f030c02060c0304080c0f2e0b0a09050703090b0a060f1208030c0703090b030f10080106030302190206040f030c0f0b0a0e01110c150304060f0b 73
    0x8200312010414100280d508007130010300031030041865a0000b1000c0179800d10b00b5007c11400c0da54018142c3d0148100b020302002400a005940390101c03a0010f01d20004000030302d40e0f000495801c074a81820080c005d25040b8410444810800f000c24041d24468102c00302c81115200580900507a030341170003031100c040b6010300740c822910b05004241019000c0184100c0c00c02d17554096440200c1e401040b1207004540e0f03ea0000703815806e002c2d00d4100d11107076802c1010540a00013501002508400489a000c0000004203844c3c13040e51900b02e40c0120b486c0e012440ea030302d006c814400c5026900a50b58090b107010003020883c55a150f0666090701c1c194440500035801c8861071a070610003001004090a100524131460b082d183c41500c8cd220219030030546608900c2c0c201803105402c91112640034000110803903040407000301c0018032606650440b181001400340482d4080c400030013120100c080000c2840b11207480095681980c1c2d0001c0380d094480c103041c01d007031ba04101c543d48603685c80c0790030113 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 136032473 1250 136031223 136031251
    0x509010c020d0213063003051b0309061c06060908031602120601060522030b06062a0109020109090c0c2d06090b06010207050a090f060e0709081005 65
    0x240c08001a1420b0800e0a9030008001050700c40b000300d0b584203210151070f00c1c5c901c10680b00511000c0446282216000d80c88010300c0782d01010220350490241e0300c202c120880e41d241c0d106030002c14241140100c0840642012001c545800030300c0100c8080043d02e01c1a00b4104115607449204135070907055803043c806150020080064105e20740c00e01c1c03e040380e00151582c2c01c0051040220340c03a04009070712100002d00081150034250414020707204000d84c02d16001209182551154040004040c0502d441103000190761144500c600c0d155540b0154182810987c014816140340d0103003e50a808a0000703405170300102d294186032080902804880e62500b00c48a850398503100c2c0c4008141c0c921540301d181c145000d540380e40d00a511075030103114030008140c107a114503011082e5080070740100d056411400052000e625582d0041d81107604860b8003050000c082401000100721903002010b5400012040120b291f82140040b0102d811440841c1c1041c1081e9650a0403603501b60b031003141c08202 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 136033723 1250 136032473 136032497
    0x3020a051207110f1f09170708070e09030d0506040e010903030b03070909120c03200109020f062704090f142404080a090e070c0c0501020c060f1b12040306060501050901 74
    0x1803624001d81704010706050900d03c0e12038000c00c208003540d04100741507901c1200305000a00301031110000030b25200600c3c80c5282010605140c9134001d81c0c0150809070358410006001d03a440340c010707551344007204000f00301c044824180140a40400f642060003842154400600e619503807042002e0140c1025401091050008040307070440c1c06071109504000381e03098010004200c070349030b11f0480c0403810f00003e000d94070303481480351454208144901c0740001b17201070070003141403542486d2000110440390400c917556000082c011302540d9030150002141d60701000400a0b02900f4007809003c2c2ca00325091514a9490340e02d803811480b0602044214030404140010502400b4220402c0c03c0e0401448054490406050f820340807140d400001d4042d00c24241400703100e020801c082c180c284060481e151482010603850b02c191280480070002c002340301c1d10050444018101c2c0d01411100b1741e07466401100101c03170a40c00a00050311041d00e01a4005210340c000c0085610941d010384a590341400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 136034973 1250 136033723 136033759
    0xd02010207140a180204050301110a020d0c061b05040e0f060a060c0201090905072d090e0c070204060b031801050103020f090406240e0109050f1303020a051207110f 72
    0xb10394240c02d42c210320003000100da81001c1c1100740303244942c0140d0050301d03249407804050a40d410710008601c2d80400308185400c1303070350220341c41034038601c0fa0414940069451411400030152140150100d2030349410700300301a940900200120341d0f03200314140140e00e8840e0421001b0405a4510b540000d407003c003001a01d010f40c0a100c013881c01410700280c4990b50f07041c0902a55021500d801c006441a0500e1700c50802c20402e0404402030071141c1c1a41e10340d00b40000d011203005014600e80c000d88080090440080d510444bc131050340075006010941d0b50b58505400b6030070942d820220b80180130704d1396241000500c5001d04a030707002000c1580c850301d0001070007504040508141c1e64aa1241204600d0a16003800b0310b18054080010810141c58281809241001038000380720ad03c1c01d001c1406944a440c521583c0c1000c24182c0c0c0c1c43d850041c0d854141d2a010902c0d50061090180d105c141080303040f04d0001d40070041c090700c2600107216046041242560008000740d500040c0032421200100c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 136036223 1250 136034973 136034999
    0x803090d03030213030614070206100902090d050f0309090f1504020307021c0203130b0f091c0b0c1803010b10030513020604171c05040e06061b0a0c050d02010207 71
    0x5009090041c90510428034000e03400b10a07810941b00c1a4544800d1410203146480d195070100c003e00c09030041d801c0c4103c03610802500ea200b08013100d500400c3c80c904030f270340e41c000100140e42c2c0700b801c40b0326000b241080c068403900a100d100d03105840b000000380c03a0f5000240c00301c1c441d48074120110303042401802048001c0d000a07050008600c1840030032010000c03150060b2260308a560000c40d00d90346d1407495540d000d011900210402e5105210304c40040414005444803401c0844061680c00445103980120031600303800900302c0c40c4040309000d08202100002c0c00307a044100b00405104942106060036190b8018445070408004018018658400d5002d0707038102c0e100507039003041e000d01a00051415046030704034030808154161040070a60b03080100c8a40c4880ca56140c00550b030440002a1050103144200c050020081d00024101c0e601c4030304541c0700c2046040c204941465000d10147d8400c1c5503403003268000804100800c5a1622030710311410b4a90585c000d01d4a9814005144462 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 136037473 1250 136036223 136036249
    0x1020c0607020c03120706150504051005130b0102060c0d0908040905040606090c050a080c0c1506121f11040b22060201021c090804083304021305090a02030d0504030b0c0301080309 79
    0x244a007440c040b2786907480303000c2d65000d1080314040039102c9081c00c0070803a2003c42a00c404400c54588000c08109903008549254044c5a901d0036a803180b00c00c0218101030080c00400400c0c28000240200d8101c0f8a544194016409110100104c645418013141100d02c04c03201000401c2d4244140b14805101d5111a0351001c0480d001c68144811880c4442c500b010402003019540344600c104030392410300725944220b030103c2e0f00c02403074030f840052940840c4901c258104070000d602c070204030114103c0e0408544c0105540080c03180d4505040341c640040c0911681c41403501c480301200014054414006d40d50795030000500308c1c0c3c18000103028072000708052282280d081c0024880080c0c5982c080c007803030050748640c0c404406090310508412071903002c5020100c3c4054411300074070003d0f880712001440000311302c0c400050b80340c90345209940b41c004032080007545481070300c5c503031518290700001900890340700d107541e24000e8a03608080d06440c0001d000b4440b00e90300610a100985ca000e8030300f1a20 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 136038723 1250 136037473 136037501
    0x1218010e060903121029070b1305100b0306010506090109030606030c05030f06130210170c0a0e030a051903050f070b0411090906070f0203040801020c0607020c03120706 74
    0x2440004400c0e540c10103608440308035007a08082080d14440c00d403c145250b0040c1c401d10445903450034000d5000400f032607881c0e41c010b4841c00300848880318030000112840503810140540342d9203000c002c80301601800e40350840d01c0d03018031840300c0407086032805030407a1800010b01400d182e0f802d1a0a100c21a040454098100b2581850001c041485845950007460141400b2111642400103062516014024004195015004008d51126003804000c512941207440e10304245190200701c0f240f00e0700c41e0203000014101e81c14000207880c2d00001b040416943e80b9049842905442010380b00d0340160005005078006c5500028542224042209054840d00b415414071500c6090fa42c05a000343c10100d0b07c8a6200b824032060205a01c100c0c590b406048074141d040c0d240000c081c540321400685240e0a11030f4909240c82054028425103010f098010000c40d201d500c030a6140307a68401c07d923610f1015000d0b2480304d1207541004140c48600d4400810b440b840c044007a42d812000b041d0161340080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 136039973 1250 136038723 136038731
    0xb04320907090f0608010605010903030203120606040504020c010c03060f08120d020c060103050f06010504090f02090a0204050607031d01050a080f1017013908040f0b040308070207050105121801 85
    0x5208941880380f141e00460030300000528034140395400d0b007111903d030480b5040c886080380400000307600201301c840c0b40900e2100001a0744400000c5050380c0074540115a00c5400803070130150f00c040540c0501110002d03541c040c0101030340c0b107008031010801409005c3d41c9030445082803d00308048801403000441340500149401c1019000d90b01305107007a082122075421101401c40b0040c1c0c1008035030702404045030104401c425a90b41e0080160f940c9000a0240c0d80034000210b1175040e560644004000140a5a40d21011071500809610781c101248201200c0c444000c0d40d903502c00d8042d030b0003076811134480d9101c0c0e455500070213801c003800070b10103c5d02c40c02000b408110010f10b0000d1400b2400c90b08008206c2c6c2e00c0315064400e0303100d60101048403038a612400c58a0070000b01d2070110f000c410909041109441e1410104240860035402402100d5050184030030180c0c003100312840b5180715402e642020340c44600440e158400c5800c2d9061404840b00825400e41070900305504140002c00002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 136041223 1250 136039973 136039979
    0x10051b06040c030c08030f03130c0810091e11060c0106051503090c1e0d0606091d0d0804080406030c02030c1b040b060c030316050f0d0b04320907 64
    0x6103056821a021650300c21046000c00403c0528401e60014020020107141001c034030f170b03000e0b00d001e020041ca1002c20b403504d02c10b91400d0103002200400030300021415110f0802c8181d2800e806080e00220464400c40c0d500400c880c540b14921111a442c2c1c0e101c04c800382c0065025003049050f400a02c0a41940e550320400003410b0369405000001c1600300b510540c0c1c03240362030841d01c1c0c2400e1000010031b0040c1e03c2141c14035140c05c201c0e040141c11050403100121103c00c0c0d800c205004104940010000c3e0780b03010f911243c22901e188c440242850a5001c0305d00d641980b400c1201c01e240150b400900c010014072091007241d0090f00480074442640c030440b410044211002440c01194500881d2070200280004505040c580501c2508a00541d022898441c4030282c4130b0f624031008005d24110309201c2010040c2521981c11101725200540010344c54041e81290200108414940d46225516054203030024014400c51400b000403038000d41481508208141100b000380140984801d0081c11408 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 136042473 1250 136041223 136041277
    0xf0d0308101d070e0d030c0210140c010e0606101409010507021003050405060606120a0b010c0503040803030603010f09020913050f0a1406090604260706020409050417091005 76
    0xb0107408000d281c050250b07003860030015094a240904840c081c500d0f00d042c40021035044140700c00d00c07075810766200c0d050382c0282e4005c40d030b040b500f11800c442031075001444065084054004000e046421005e950080d00c0d20410004014070031065030300420300c03102d0b80800290004010b80310824060401d6440c22000f035000a00440c6404498000b10381e41d00e0901c000d1000404c00158080320a4a2041c9405054403420b00208401030044010503220800c01005901c1030006c1c2140513407043c1183d40341e070b8070707042e04a0306c0341c00071149140a5031800c041c05c0b000c0da8850103981880381d0048c00d03203642a1960800c00100c80c80600b016902031181c1d4800c071356000c608110810910b8000c59440000c0d60f10504800d05000014200019076840502440082344440c000c18205400303011002c0b0001d61000805540c60045000207000d040c400319000810100e01c0d00b0141c1308511900500d007080306c0300c1c1c0b030100d160701130180b0540e00041d58001c058001e0380a07000802c281208070711400700c0d9401e94461 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 136043723 1250 136042473 136042499
    0x60a2003130b06011d060304110a030305030a050604050105010f30060302040e0a1a0411030109060203071b08031302040b040c05071a0f2d070806010e0f0d030810 71
    0x26050462041d9016052014a1503002e8011100f4a421048203040825010b018841c50394900d03c65030000001c20200445104605400d0381c01406521100d662418040c1683d0400c4619a05041c140b900003076040c030b072504c9000c2c1607900507100e0039001e4100c1601140d40200c0303000e0040d000e03200d04610340f45a8401121122559501c03903000b03e41581948148006d44014800f01c1c8042d80c8403054540005914514005c4100e40100d00400e041c2c9d51801c02c005c0124140c46425055403070310648000b4051190015442544a511800e820358941045a00e80d00320302e01005c2d00230a01800810280c10400404101850005102080344044071002908603201c441000c400300b01c00090340c4040006040c506503041c1c9588034001100e140410041d0000e000007040048000c5a1a40c89081002851810341d015a03494400100314a04a035000c0c028072015680c85000c5400c25500d1a01c0b8030301140d4121180201030700d813a4401c519a607003610345c0b250203060f17480d20941c0028049a000040c41e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 136044973 1250 136043723 136043731
    0xe01091a1303120e03070506030f0c070b0c03160512041401020903070b090a061715060c060718080a03090e07020c060a080718140f01020f0706020c130608060a2003 72
    0x2090380c0103801c3e402c001620b460720400426001e074100b032004200558541c4142d075800b40e140d80c1420141e94580e0310005181c490084001c050500d544184a58004440c010710f1041c0314441c40420300428014040d03916004d0203065501840c1d0b40400640000e41c0304150307100305e0172090009400c010324007000030304004c00da4100d580c0030314000c6400f64461502c1c030101e500518883c10824404076800039810044600203028030702c8400521007140c2c80da103d05044603c100711700da00b520464240070310b000782212841c00852170403074140743c0b0115032801c0106502055981c5520348581d420310b44807014640010040030340095000d21100610103440311001043c602180350303030b10380d010314010601410300700000400465509081006010020180249500141045808203010000320303004034a07180e68505880e94031300402c8000540140c0008201d050000c04940f400142c10100010340115142c5100307044950740600b0206000011951100540b10541401e40100030301d20045502c0540c0141d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 136046223 1250 136044973 136044983
    0x1060f0b0720122109010c0305070f060501090b0102010b01050c070905060d120503070210090c03030c020a0b040602030d050f0601020706050a030e030a090503010f060e18011416020d0e01091a1303 86
    0x9240c0d260f4084124844140d2440c102c213100d810200030200081c269020910002c0504c000040c1e58018820000c030240105503001c6400d110030b68440400c0341c0605006084907004d58204010701b6010360255041d2407103d80c0c07140c0200b041600c0c04a00034050007016015540052460800402160820303402000c1e0758415100d1540d80c2c1804000240b40240c810007840f180d13441c10600c0c2000405960303c8004513900b514040460761503a00001c0c81e01401c95103c070592050024001401c190044040c100c030200300341c000c100f00c0c6d80f0000c1540c1004400c9070310a0050b081880f05001035401400540b8411980e8030340000c1e0308048130350061860740f011024501054070140f0420041c6000d000b015030a000e07512050014600d081040000d48102500b0041c500c2807044081c07902200c25232003080d42900300c0001b1200c608202d03054034024020520944010301440301184d61250182c80310614070030043c1e540c0304240d490b0034140241048001e0300981a45402c0005640400440e0450170103103000e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 136047473 1250 136046223 136046233
    0x2040305120406021506010302161212020c10020a1b030c210e040b2404030c0f0602060105040207021f0831110301060b130801060f0b072012 62
    0x160415524104450901040c1e0700c004000c14805203601040328000341c1c0c901e52111000b42c0350000107038064003405030716010b42e00c011401541030141d0144101c105004588402049001160984050340314a6049054036840410070028500141e4020301840085e0f01d40420310342c080c8401c1401c10380c5c200c01c1c03e07800101165690014001c01420380c064501000c07040c01d40d031800100010304070301099411144030b566a00c1d0a18003546400310002040348041031075840c0000824054111034101d40000d071845540c40c40041200080c003011501910542e4005100d26032800f02008060760010b40200d80084041584008032030719000e4142c03115210380c942000900d029a2194040503032401c0086035039107000c0c5000c00040c0c0c0d8025141d241b80d00240d4402e02284248042805017140b1341c80750b00138450000d08031000506c45138030036069480040082c00440e0741c3c1c0c22003200340b41d524050040018000c00580000a12100008141d08510f12038100e42080030f200007204c21555400010a507000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 136048723 1250 136047473 136047479
    0x3060209090606090306040209150a081006090903020330090607030b1f0503100f0f06030b04050114060c12040803280f21020d0606023d0204090905010204 68
    0x6400e020340c0042c05a40300da0600c0003034030020380d0f10b00019001030b024000440c0850700e107007081c4042180320303c005044090856600d80c80942c1d02c0001038000140725203004400b20310380e4454050721142da80c00da4015400c0041401c214001c05a0842da03a00090441c00c40c075080c0c3c2641c07005860310940201015000c58602040702900341c03584040c1c02ca01c50503203400e0b40e60010154203112010344020f8136080d900e07903480c2c1d801032950324030542050240020040c030000300c00b480c0182c520140d6010b41d60a00c041c1942505003c1a15001e006580301080020040e109a003007080c054654421540c00b1685010600300b40700c00c10b5070250300b00501d140c100003030b1a1070840201c401254036440707000d4458181842d14400800f030b80b200d0710340e0a082080c400e8120b1041030300c032608200083c0604000715034810074202c4060040c103c51107074074050300500c0c132151314240c111500c0c198012a2004008101e10101c448140411460102090352903030030300012078041203038031032106542c0c40317a8001699941 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 136049973 1250 136048723 136048729
    0x80901050601030e06070e010e04050a05040203101e090203100501090c1d0303040506030c07050f06011805060904020103020903010e0703080d29040203101503050a0f2a0e0a03060209 80
    0x880100107505042c00c00303208804d41c1100146065001200d458103c1b40c1c00080780048401e034001d0107030300d0b51240c1003009020700c01089a000c1400342c3d10031422502c0d030b008450850000d9511200c804814680348054241001d03007650484180c00e88000d05884683c4103421540c030841e502038000d82800340d514000c160015030000c1070740484103c0541800e4420200c0c40000b0303964410350250350702502020021401400d01c51098a01c100c2d4408180c0d910004001102c584e50a424450050f10100154101d44020b00c2d51060a001d258050700c102215525074005502079880f1203032080e0190340c0e505001034001d0050042e403002c1e6101c0c1c0101a074803800d400d507000503200e4692165150b00d00c09104030300c0c1c40390941030712800003105130782c01350b166070780c3c41802240c0e000725612002000d904560820743c070a030315038451b0748201201c4500304002501040484200c60801481030b21845806400ca404c212051480101c1480b6078035085191804100200350040d0183d0b000719505600425071900c40e103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 136051223 1250 136049973 136049981
    0x910050702010204050603010b09010c0b040501020d0b0f37091505030c030709180f11010206180d030e010f0c2604020a0e070c06110c1c080c0f0415080901 68
    0x10300e40e00c029801c040c01c020008042d48410300c102500d00b580040c6260301d80e4002c240888400c2d0b002008140c0d80e10706130402c1c40c041e52001100e01030842c50801c8080083c54080c00f01214260050220110005c416101d4908115200b0f10f6800c00505110888c43d196032409480001d050100404500d8540c810782d2803108106542103a132094000c0d5900341c00503140081c00b00c2c201c42107000c0c0804c0c44580c500a58040c802280c1c40903110b00c149800803070502a80d8405182880c4c02070b42150b105683e0100d0a8070055404000c000c1c041c1c1000507040c039080c3c426082490120f0301c1d440001004c0b00c0c5005108200e81a170159500441c00000c00c4c13208000c0200220607440c602e16502d004030740f4180d40043c07550303030050003504d0b0800030640106855a208034001c151035030b03100c0003c105a0a02900000454101800200c0c1c54811341c603c0c40800800075181d030410044689039a1180d498a041c440c1658101000100c501c15052000040e140210840040785040c1e070740320045c160408480c1e03035082d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 136052473 1250 136051223 136051231
    0x110d0c02100c02030a0c1e0305120a0902090606211317030105060306061b0105010609050a0801060806070804020d0c0f140108100510051209060a06060c08270306091005 74
    0xa86003020864002e80c020089500d1542c0318500810b03180d4580c41c1c50340841c0107031076440218200c1e2240e450201900a4000c00800d0040070381841650f43e400032003000c0d2404000020f4020304014041011400c0401c080d026035402c1e83e072034900721a4400300e40c02001d0001c403600709034844012240400d000007a0351502d40c1103042d040c2c03145107604120200340244030141c840c600406001034208069414140c1c1d0349592508080240300950b5a61001041d404a50040601c0b403000340c4000250080148602e034102c030081d10261000e566409816912540000c00c2a41c0000140361002c3c00504c0742100d540143c6140d846141e5014244042d002260b03010000040c1400200d0040c094114003e14900c02181c108846800803640101001c503460300070603001517101000310041c0581d488010072070a12400ba480342c10070145559200440c4c2074407006401800c1c2d05000c1005001e100352002c080c6208032052002d40d1422048500400d161003000c8500400b00e81040e070303103031000740c1481c0105500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 136053723 1250 136052473 136052503
    0x3030b2101051503030a090b0a03061d06010f0309200616060e0114060603042402040b040e09030703091e0e0702010c0206060108071715040612050c04180303020c01110d0c02 76
    0x1000c42441001c7c240c80d5007400307540c0501c600404c22020543c4250400000b0b03020700c0034506600c4400040051040100303590b1240400c1c07481e4920160a40b00380300c0c104802d03810144c00c044070116902030504c0b40c6490040c050700561f04120b140105800642c1e8040c03160300c05c0600040b0541d090515508507101044034500d070a44110511025a9407081130742c1d00143c103c4400005040c0013080b402d9605002e0740c0000d0f0b85400803a00144945641021700102d42050145050580d2810680d684034464802c0040106a21034010303c041d00003403502000d980291014442d00c19101c0c844611010300484408005039103461460003040d605200c059045082800c246a07079080818014003115140711040102e91144800100c0390808480486040b141c05017042000b00e4584440081c0c0605194058849226030280c91580341454840c8007425090011003500074081550110081e5001c80c07000c61040d900c0391044500301045400405206910000c0050351851001d0007a0a0008900c81094 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 136054973 1250 136053723 136053727
    0x3060e0c0904060b0f03010c090906080c10050703020f0a0c05040b010e010f0509030a080a020601081507020a021e04110a02100b030d03090302030f0f030105040501080a0f03030b210105150303 84
    0x80c99481e01c80c191600b080d0300a40c00300e101c03090a000f203014103840c10380440d815030030b1110303131911541c05c004d00c0000e40b41e81641c14481d1a031108241503031001c0701081150040c259900c0307403040c0d51203070000e00001c83c031178415101070740303c0824941e162510750392080e03c1140a540e020003041c5042e100751190100d0170300b0407544011043c0b0001c0d105030b00c450145002c1c0b00b0000b0345a03902c0d0742c0a100d405844c1c4e520070401a260010104001c4d503800d824050b0f20303020302c19002100d29000c0c0448149125508540c020140f00d2610f9003484100d190313a01e05001200110320f920080e5a070380e400b485a004403030455040c1c4800d00040000d1405020b0203440d40220f190010480442d100800d803d4820301c25403d0110f105400c91500300c4c0303148908144044900b00204040c41c94500c0702c0004e60480b58115000c0c40b00ea601c84104548605038008000c101a004080c1c1d403001a0003500a00710100c0b0003403252908894140080010340303200400001265940c0040000d14082403a1301000360b001600158 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 136056223 1250 136054973 136054993
    0x306140f010c08130806041101171b1c0c1d0406121707020603040c03030e1f0807020715050d0c05091e03031b06070e0301110a0c02031c05030103060e 66
    0x20b4081507202c4000f401e80100010790002c00303000700c103c6000908800c0c084802e1841c11b03080c80383c0e1404000109034000343e0640c8850222500203c3c07601d024450100d41032118202100d0b21010304d074007130310170440a40302404e19070417001401d1280304051a42074039141c2c103400c0441c00307240d01e0f03d000d0528240710b5440c00b40d00340003140030b442001a10a46c00300c2c0b100c0c144884030b010809a0302a8480003940f145002082000b009100c04603101142d02c0313500c81c541800002810030550f2000000791003a1601c1201101c40c1d0030f403095004a400c08002e00642e0030154440442030380112920b44054040799001902d10a9404184103a02d041141c516040b0300700290301c0000303081c10400c44003085802c8030340d400301c141c43c0d90f0601c2151640403142206109100c0c00d00c8080c2e894510866002d400308041441592407410306008400e04203000181203407820b900d8403400d8070400c8124800343c2e0184100c80f003000e00000301c05002c3d0750041e881c3c0c0301c01e80c0300d6145140c094191100c054101c00b517070300540740341 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 136057473 1250 136056223 136056227
    0x91a090f101e062102040f03051207030c0f061d0703050c040608070e0411040615032009040e0c041103060901060c02030304030204021605070b0415030b1c0515070306140f01 76
    0x816143c15140c90800010040c40114110769081c2104103024800900000e543c0c1120142c0c50880e4401d806807a105a61803c02d5640b500605c84007070089040428280009103801e41080c654510403800007c0e1120100304810300041b9008501c0991390141000740240311040052065809048905003c0a400e0022076521101581b068529030203c1c0008a41005810b091307101000b50042c10070030100b0756810019403100143e0340908082413400900107482d02d200408851007104071481c0511300116801070000a01d00030891014501403a12003c00c0c0d9a16405008190f07408603030040d4407418240c0030480780c000f069024a00340b00c0c07286040b0700161170210035901140c3d0121001621080540c004816080140500410a0081c4500801c5c00b07003c04018009403040d040c440390124000078800d40480d80300350281a803180091401040800c0b90010074a542031148041c1c0340060010502d4030580c400607561385000c25150002030200700301c0787d4002001020119450010f0785015000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 136058723 1250 136057473 136057529
    0x105090c12010e0d05070302070902160b0c03100e060d0f0f0302070608010305070905070e041e050a0b0d080f0708030f06031504080d0c0e1509041a0a091a090f10 71
    0x158805204001c60305405050003444204010081c2b41415513560310b4441c01807a0800c1c4240c0300f101c22baa41e200c0860b07403200c1400241c074030031900f06410b6240c050a10720080000000189000e03441140848103100144d0109000d5100510417041c040300c1c08028074029081404030f410131781c200042d0780010004280c001501707000725010207200268986510608890740d00098020b03581081c14404401103640f10b00b80182401c188030b003000c00054407004101e0b001d985a064003d6804088030180c41c0110340100001d000d8280d061440d00c1c50044541d031071450325001100c0343c0c044a40c48074200032032400c003803090501d09190078080340305900d426a25642c2a001e06983c0821082d903c0d808140740d540544002561420001c2c07c6a07964483c40d04010001d030b124440103070249003004c0b0050a0004202803601c040000100382c6061541000a480001c004c92002c1d0002e440c4801c00303040c501d4907840c2c200c41c00741c0030043c00c1400f10b150000710000c442c81243d0180030007044078a254030100c1c0800c12 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 136059973 1250 136058723 136058743
    0x6021207020c03190203071d101a070602030606041703131e06081f090f0609060b0909070903080406080103051603020a15020a0b0108070f060804030807200105090c12010e 75
    0x54602c13043c419400802d140c88120b402807040100d0b039018117240c8910b20794001e0310070300c2810f0039040040c0c0c6034400704502100154512031499000d111203000078521740c001c0c4d0362160019210130b051075512030740e6503c4006044415960713a000003c61080104103440c081020b01130541030080040241d10701000303c483c062181d041004021408034080d503125039207805c0070841a2080004050310303000781100130250003505581c41c80c9080c400140350740d058003078141114405100e01d030034101b60710140311401400a2141c0f0421811050110000d038408001d0000b81050340d5404041c0c0d030562506500d880c03861200c2c4614007540031410001645d800c207204042e9005003036042078854913500140c0c075100c03984800400e48880c1c0300c004980260300080b9481201d20950180d00c5141c0e854000742c03543c0c1c40589024002801550005071883c1c003034080c2200030b030242d040011400090041c0c1508541081e1143e107025040422031a0b490300d0031034143d18040d515417000300030340c542c2075100c0c0d6070703840d804e813 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 136061223 1250 136059973 136060003
    0x30312020a0e09090309040b011722060e0d092102060c010f020403120207050909030904021303050a0303091103120706180c0b0a080109060b0318010608070306021207020c03 76
    0x249807001c280c410356070381600a0015000c4201401c0403110340791290003a90f10300d070003145044618400e81d032203031b506026004100700040300640c031003008141100c0781c0e10b04031340402c0c0c0c10b0001e01000101c1c588070340f03052010a040900745503403402c00e00406040f003a60100251a07040e81c915035041c90701480015159a0486660740d840000c54091405008800d0020f40d81500c01324001060207500030b00541842ca20fa07007030f1400c1c2500e8900300030011307405131a1080747c0c3d40144010301e6681051783c01030941c6801d4408001c0104e650f9078400349420400c41c001ca0002e5125a00381c0100701c982c0120081080e022405001c0f82d440140650b120b900440102405643d1610030300d01c00ca4131040c10b00002c1c2a00b001c5901c0030185c4400300c0d081107070300081800d00010903440000580303d1251045200342c51190408615503140c0448100c1450382d00812080207542c0c0b4880020194410000e800003940304003000750302e0f0440c00300380c0c0184030300060001055401c0b1642040c6282d4020511051110b094 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 136062473 1250 136061223 136061227
    0x703020c0d17070c030605010501050f04140105040b0a120b060c0c0d080409092001030501210309090c0e040e060105031207050c03060f0a0c0c0803010b0f0c0303010306060e07080103031202 83
    0x1410000700452030040150b0707201c8000940c00c000d1200000d107641c1034034040c43c020300459076a82e00440d9544507200c10303907140e041c0600c401d0100c8014a0070301085142d0514020b814542c491541900c3c0d94070030f030600c0020420030a040101c09007207000c0c002404204688180c20b2a81d65410240ca0340781c0040d050303200300346668040080080000c2514050080351408111500c0705103080c0d00300030001400740101c408103001c441d40541c824052a4180d444000070701400c0c2118807508030380e40074408130403001d014500c01c001c124a5028070444c14034410300c1e0744001c0c0d120007907002e000803503510020010464004100600043d100049e0380d00f60801030038021a503820490504a00b040c82d41c0310b456605016034018042440040380035030380100b4101c4410006100c0c0e1000594406180d034000034580d600510040018020541c0039201c0700c5203010b001454a811410107500710745c0b0907041102e2032960354100703202005208600703550182060808e24a20750540d24054401300c034601c03030241d03d5500 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 136063723 1250 136062473 136062499
    0x5130503030c0903120f21010f03080f0705060709051003020f09010f12020409060501111b060c070f15020d090e040204020d0e010c0e0f03011a04090606051002071503020703020c 78
    0x420411440c9001c1e00717002042d120452045101e034945c0c03000311121104091120002101c59611404a04903148407080d400d245c1e00c1c0d9554001250008010703400c801d80700303101b00c001080c0148400b41c814121996201d031414140000c02c100c800b4140d503a1004c00d44144000f00180040e00b0440c0d12041c2c003402c00d01da4035481400212600c109490040040c1070020500060400c0d990304604252030090300e401c0c02c0c0c403000814040d40c80d00320003074141d010032003907203011a2420710380b005000402a801c00d451840d03880d111400b00450255100b420040954110242110b0f410b04c00400d103290030380791039180305140900c00a0014805000a4421036000503100f803400242c4c0e1114104c240107130001d000c100c07035400000e00b52800440c16640642c13958581e0101500c0c047c42811111075814500b080700c910f80c0002d10004000110007281c003140c0e152004036466850903009000b00c0c00e43ea004111031400d11503030001c041028401002410b0040c040d0301c00003900454022940741041c6c425100b0001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 136064973 1250 136063723 136063729
    0x2030702060313020a1208031504180b06061e09030d0804020d240c0509010e040507050406030f02070c0803070c060c0f06022b0c030e03030c0f07110405070806030105130503030c09 79
    0x9201ea000b0310750451b1658013801040840009940310311016600c0c0a41903101405110544002c915910242120818140d0020348414a100d4010101811030350609403002840f001907010f00001c03002821000c82d4411b0940b4003000310356441c0800b85040c4140307080c15800b1a00f00c41a03098010721001c0c11000c281401c2000508039074031102030f02414082c0c2500c070b5030050002e0f44881881d41c00699042c0c0010443c1c1024040c0d540a008166680e03890301c3e00d08031045004003004aa0b000c40643c0070080e201c08180a43e4800c0c4c0540403e80107150780e40c4c42c03031034502c00c0781c0c0c0030354003440900c210641c210003c10680a122188960044401f6a4801c441d003001d1401d200154001141e1080f81b0310000c40f81d0180307a114440d030b03d865807800c01015146a00160307881c002200c034419a20300400c41428071001001c0038142161050108840c02e42c0b115000400ba1071044036860b000036080010044d40c2d1900b4082d168202c00103c1c0703110326844541e00d5658407480010212035a11400140d035a0241d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 136066223 1250 136064973 136064989
    0xc170c1509011b0806030c0904030e011805130c12140106050901050d0e0d03060905010509150a090c050d060608040f03030216020607080c06180a030c0609080706090506070203070206031302 83
    0x3281c880d148000c0843c210340c081c02c981015204135010748509100368149003441068140070b0707601920b80444417200d41c80110f90203268160356601c90741e419100000c86444414904003548840316000c540da516400004000761040701045000a00349000c18907404080c14800741074a6861400341d5076080e00700d0040e01d040c420040c00d50a414604802c16540394030205a000000c41c103550280040c2d5510403c4800741c60085c0240c40d8003480341804202010011540c4c001c01300380243c4007006407035584043c94219085520690045000058000341107141d600c147c1c0c0141030305082000380c6040a440d60400000142401000c1c99400102502402e07001c560089034960700601a5988a1042c5070604564028040001c210f02c22900801c1c0403034582651500e000035103900074060301000e601d04480c0050483c4007a2050360740e481000010803070f0b800092003114060341002c82d102096250007458007030010809000c6400a0100b00c00698500302101e412107009051f4146400341800011140c07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 136067473 1250 136066223 136066241
    0x304021504360603030e1003060806070305041a1501030b0301020d0e150f160305070504090204080309011d01050403020d020f030d0c05010c080403051c0603120c170c150901 76
    0x1c452809003002c42d0b91a1042e0418084401c1031800c0c6829403115003001c107540c2d00b804001e01142000e444650740c0d05040c00852a001300c28030307005c0344036551013040b142800703001c6d192440040e40340d0040105024640c2641800810b24020072002031620340264043c5403159000b02d810103445501c0c080e07455600750140d03036021442800c1040030b0b140c8690826942e50428001c0c5141449c9640002c3c074032510035034050b1044034101c0707031740702003401c850b0041f0001e2030020200b03414090140004a035014492000d04060a074100045a4035102c2500151228800e0b0603100154008440300614607680201920200d0780c0c152030842e005d4490344001455084607525898041c49020b103044402c3d5408252080780b9400340c0d00802810400384812030341010200d50207404107008000040c6440190280d1505510285034001803003601c0f650391002d4512415140800600c1038080501403000c00982c44c10301d20319440026140c0a1f6400c4050707140c0e4800c0441701c0c16406120300083e41070000707402404503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 136068723 1250 136067473 136067489
    0x3071d04110a090b0a0b030705030c030c12010303050a170702030d20070b1006110a08071a0703020c250308090d080c0303071106070e04050702070e010b041401020706050304021504 79
    0x1250303880f00c0c4640020f04400161611407000644000745010f055011a4083d00666444504d076503610400745800b0343c40038000e44070030b01d401c00c0f0508010442c031101c24040c510a96900f0340d80c81070180300420448581c5a1034230082084000d10401540000c101c1c2c95406942d500480c14089400890702c010901c000e4101c43e112780098003800704581c1442c103901c200a2039a00000b01c5840d030034122900c0c13a140d80b41c1d40c142d5101e03a0322800484d27013240203004541d102306108203012740307481c60b040c6101501f901d007080401d17004155500704040c103200c0700310040106686002024110b40e48003c0700d0860344005006c40c1c0c00029401e0b059201c0d0030341e40c0c01300c0d0b410910680d692825010104e90765070084a200c00040c580c0d90b0681c044090200c0c0047c0621841da44000b00d18a903041000000d02d00a010b040c1035109810380003800301035102c540350007800607202998481d843c102290915021051101c4e04642002000740322060f081003e90390400e4060720600d1190a50354403403110f9201e0341d048081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 136069973 1250 136068723 136068739
    0xb090424020f040602070f06020d1b05190201021c02030304080f0909091606030b2815030f1505060406210207050303090c0103020c070506031504060312020c03071d0411 74
    0x1040b40c941001402240c0322030b803c0385d28003a40d40c011a500030b00c0324042ca400580215200e002c84900c038100391070480140d090401b090001907a1901c1c5009103e01c2080c6007990072041301402c0d981c040c41240d0f04003404801e08900c1c180c0d1a0002502e80c40300400003814200007140c600c0c9500040e0040d507440c5940540b841a95040c0102c045a480310a06144142a2041c1c040810341921074041c1d06a01c1d0b03400740003280c1c045140c00520115403a11500c150400450860000d5010440031046585406030740b00050203044907840e1030190381e008c10001c01c40340e03020842002980c440b40c1c100e030211810b51411030950112320100206030070407085106261400483e400080c000040000d50003005150102c8800c14890300054060780140908283e0341e03040240300304518141107006503440010f0781000b10b0706428000008003181c8580d0405d403404200e0b858014400b54041140100350f89086000b00900b0b8580740041140352507981d03000502c2400c10340801c0070029005894800d24a00030701c0f03a1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 136071223 1250 136069973 136069987
    0x60a060e190e25090f0501120f15030b060a060503060603090a0c0f181e0e010b04240603140a1d0106030b060102010c0903020a050d03091208030a0509010b09042402 72
    0x203034000c2e18039104000128151040c3c0c20f001d401040314404032030f0311811108403d8640380c01510f000d070b141022401ca03241c4880140915260301d10500d18203100000250400c1421400c0000034020b006000c0741c010443c4400178045a81c11400384c9a102038202c6201d581da03a250500c06090001091005010b410074650118a800502c203107403083d506200d41c05011407035219140d80503100e5082030101900c508415120420758a50031071615142800c00105a001090000c101203170102100d00d0a00b4002c50900f0000e1190410314200900e4585024000304150020102e19050050311121903d03580c3c2844d2444085d452036806a150307028002007015641d0f034100462034000854855005528015500340e5041c0982070080640341c000d401c40340341c50308007802d00240f841e2495003a000d0000480c0c0000d10290a0015290140c0c4111800c40e00c070b0034804020808d403040600384402a90402c0e204125540768041c1c1c0642c0283c11517450185641c0511011100702c0107400c0301e141c51400043d00c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 136072473 1250 136071223 136071241
    0x408030304050d0e010f08160201020913060504060806040309050d170d092d0803270304060318050615130212010519150509041104030b0a05060a060e190e 68
    0x40440003c15803905490740760301c80011209a0802e6450f080070032088004262004000034440010200e00d000044c90a80120005980002d84484a0078815210007045c80281401c0c01810001c00001d001008642840c4c0d401420303819243c098203028148801e5500d003800b14031680000d1250440400c9039a030b01d41802c050380030340304401d0151095141d0b500d082c22a22036800480391003034207001101c000d180b001c1d0388801c9203a00251039602840520b03807182440e60354920005505a1222004603941c038074140000c3c01361921103604007681d00082140f03c02207403012903825803240c0030050001c0c031090100009034136200351070303105a045880811040429207c9210780350507581c003111000c10b0040382909410320305405014000c0b150420040e030080342c50181004e080041c0000f0400314408000c1d59142c10b40344c1150f4010b4031440104401e000c45580c0600c40c158104905071750540480c0c1c2001c001400f400c421202c0305016041040741b02165044010381c0802030001400207050307070f050070004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 136073723 1250 136072473 136072483
    0xd1d0616170901021b040b0a0608010801060509041a04150203270a05031b0a020301090614090c03120901030e012d02030103020906090c0d050903190206090604110303040803030405 79
    0x445400700d054103080003441c1caa409076010040d05078020100c5180c00c0c0045660384621078022504540c0395001d08115965110000e000383c4842e50300c80300c4943c580010785080d210568007442c0515007040520010034005000c04486040300903c0c114113884a107060000c1c0042d044d0020f000600c0402031101140c090311124100428213004682001a003d0705585c4590300044020300700e900030422821441c49018024810b51206800e0f42ea05c2c0419802107400e5031600c0d038040391002e543d46110004060044035003504054914001c2c40580544800b190750388070259455285800003217000c40283e8880c2d04401c290b0580e403002401031088074211492900c450400358a43c10803200e108020030466071080e80e048907002004015551034030028041c0e0031320007806c1c0c981c4500c2d003004140301c030a1003030040c14059040c500081d903645a0306280081002c1805081c1401c642103101072001070500040c08036001500004515100d4404000180c074600c030b02e5000c1c205500020007000705008012030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 136074973 1250 136073723 136073767
    0x12031e050d060602070e0127050c0d0c020303160318060f0507090b1c051b030411121f020c03040f0303020304050f0904031d030705030a1b060206090d1d06 68
    0x5400c2c801a9152082039846400c14000e20440c5c803000e400402071010303940000c030019500c01071104e031542c00305075101d130644508907440b034940000001c500c200c95646215007002500c886c40658158100240070f2100c0005000101040588641020000103004040111900d900403800c1204540340d11849004e41000c13241032000c41c4880d00b001a03480c00301012a9014034529141011b40119400d00d000180405420881440c1c1c80114041010304c00c89c000718003a50003507400042081c80c2c40e0410240b00000071400103036412110019003203000a13108861640c40360b002c05600c5103143c1181038a140a180c2c41048000e0003104000700b070503004001041902e0050383d464042c140e0780ca060101c00441610014002201c3c4c2c1c499400380259076648041c1c14100a0541e41d400b903031140041e24155080500380c645c9000d5540301820801d18111042c001e00850020b8482c074a04211510b440312207885005040c0070b151604a0500544070003c02ca80743c40043c0740380d845004e20311420051024001c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 136076223 1250 136074973 136074997
    0x618060617060402061209010612060b03010e010b1804020622080c1507020603060d0b01060e1207150807050409020d0911031b060f07061d1506010912031e05 69
    0x5021001100004518544919005402c552a02a845066191010f0b001f080c969072550b96440102e21607039002120000e0394003601002c6040110300c4101030031102c45008464090385002029030098a401c50501400307203101c4900d092550f04c0c1d00200d0307140d12a90890030b4584006219024041000c10a41030030b40f160388084541218684003031002c40c0c150b00080354401c040c00d010000040c40c10800450344601c4c060b10307000344818296140000c085081e040a4081807080d20380c20100d08041000030072400c0c1c40d50060401900e444510910114903402c110100060500080e40e003034004c0c0308483c01401911021980c90001d00220ba00400510a00700c0d400303080300640700307010700d8001480000084010030425020010000700f006070741c81451282d8211200b44034a03070109102d4840c1000301c4c1241c0640d1514000b007010b2040c200304901000d06845080c5c0c209010342668403203420303016a85550503102005801d4101945d0300720704540501045084480f00b11345140d444409091070314010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 136077473 1250 136076223 136076249
    0x60801060203030c2a0f0d0315030206030109051e01031b050103140708091014070801050a031a0606091905120111070618050d03060e0109020f0904050406180606 71
    0x103808100d8a0344010340d009500f260b0248400140b503003121000625001d1103803007003256007501c2c0103200c3c1800442916110150828a04a000b507a014042d0b813007250145845403440b1421540050b04601041c01581c425507982c40009000e06150054507140d03509024551000350b0352407500c041c000054070200c1d04c2030a0f042d500060603500074001c0b1601c1007011010703404569940b613022185210014100b041c3c82c400d1103944034080b591031050709914451a0703207050039403505013009008120107030700060141e080c80d01c040000c20000085a0b00c00c19010f0004121900d03203500041d21406954259a03002e541c8401c603c80241d444903108045900554030604840c0200c50a1400c89000700321102020401b00003186c00a007855200d0840c2220403034488003102d9080d2a0640740c40b010200340404a90358107024020800e070000001c1c014102050190f1500d50719030313441c3c100c50280d02400c40c001c40e01e41012a0420240f5000502081c0481030b07020041c080c1801c0481c003401c2d1901c11600f8680319 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 136078723 1250 136077473 136077479
    0x3040503040311060901050901180519210b0a150e1302030c01050406090311191e09060303090509060a08030f070b0108010606050307140d050a0603050118020a1403010b040207060501060801 83
    0x4c15000d44000100c16140d41d824060040010340d5680b10f4100d40900200705000003182581c1c8482a1503881d04441d031000302003e05062030418120303100d440000b62440701008840000c3d00c001c49240c1c0c00141c903000495401c032064541c0c80030020317940141c0580600e441c10440d295941b0120001d956000324100d55400c580c0c5001594a84594010100003a20106091011601800d502140c7d5140a04400d9500500181c14180031010b074004027620741d01c07044420561103003900041c016050050342000003920b9507174090401d0a032031094a001e10800c000180d443c2c1d0f10f40903418020300c071100550740e9498001804800d030341e100f034800b01d98007081c102c004101c465052090b1401e941c0113454580c0b450702d400101f614486140d01d0400c1400000300302c0100041c5040c0076290147d1401000440d400d42146851829540010000348601000c81c0d0a4005640d0780cc070a5000c48402c001c0f100e6501d0303100c03400309003d8445600e20743e80007800059240c04014044d4421412621705503511092a62 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 136079973 1250 136078723 136078729
    0x304061d030409201818010e0612010902090a1e020f0a0c05030c0a0308040b0c0a120b040f05040c0302090c0a21140403020a030f0c02030a150b0603040503040311 71
    0x14985030000c800780d1050006004404881e0301c03902c10040101400c00003a0046101008142e00c10f14030b115050480d820301da55a4106a6945005200428401541903050480031000d01c100140810701c5200e241a441149410a41c056600c6640103020000145841d0502e030000d4103078540d15072600f40454035540c00302e6100340300380d030062102052890b01d400500d180031140c501144009035480e0104000511541104101c0c0104c0944640c4131111207281500b01140c02040041c0b011020460070000180d410307612285500d2020404080040c4090551004c1b80c0108211260340100c1c900e414244418081410518030407240300f1124071245580f450f42d512403501070b0400450214542e1810710311103a010742c24241d0030801b00301000074111451140c10b034000705d00340e80980150300044043c0b0207160f400307264583d20344514107007146180303115800300e540d41c0903404d005460340d85429000c03800000780d604211400030000b0000c80d10b9042a05185031640c0c080d1004546008115850202d80c0c2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 136081223 1250 136079973 136080011
    0x40302150c040315020d0e071403011805151015050306040e0c0109030602030415060b0306030c010327051c21050c0313050a020402131a040503030f130305070b030406 73
    0x2980c0010004c0701d501c428400c840107500240d41c12405252540d08030712030400100428002484048031310503400c02ea00040c54210750510b00c11081f04209100a01d022450026440318903000c180758038200b83e6605800700e041c00038242c11401d40b03119030b1700c0070302c0b01c0543c00f0000c2c501902c4119410014809181031080c2d036113030312800c510701051200381e041010402580c080d607132183c0078041107040c0300003024a240454009411031030500d240801804440d0404100b800d148500a08040000c6080c501c92000310300780905242c1200c00d07000c03507202c08110040c04446a01c5100403075040c07035a10a05006841840791405d6140742c1050903120490b1030045004a60064041512603855511245001d0b80d0702800c80c60181c2d80380c0309100c034200050716a8070041030000c02040d10384a080e07003072006400000f1005500560310210500c010300c01c50b0f501004451501640d10b4410342c0c2c0d00708a03005540e55005660024003580a007020008592150000541c81207100707142c10011030000402d07c2000d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 136082473 1250 136081223 136081229
    0x307050909060f071101050709030308060409021e0102011808030601080702011a01030b0f150415030509102d05070801080f0c010f090e0c04060906260c0f03040302150c04 75
    0x1982c44180030640c000c000f441c5568010344140b40890500800b4a02182500d0342605c8a000040ba081400c10500d6401583c1d5908464200c400380603003116a000600c80383c500c0607007050220180b18000201d81c0c002d40c4032802d40d0500040d10342071799183c0c1c00c05c41c04681003200c155003c40d00300400601154070602c6401182e00800c00c040600210b500011001401840009600090090000c1c40c0540e501c1c0315a1044016003410680d5a90420310100c0800d00d81d040700e90140750404007403140f07c031004110102003100d04d40f800903d00349001c455418002c0c0760300d00004101e020780d080c01c540341d140e03808c610b1185000c1c1d1181071041e6612034030984c0d13920850700003c050390020740303904c1c65640c85032040d02d0441d000742c50140c44041e202d10200741000300950780000d09800000301084000d0700000308900030321050620004c182d80480b0121010046ca079048c425801000d40040c0300c0e201c0b003406071200b14107004220b03034884c41c0902d0b001c1e50f01e1b5407210110140d440c15100040011110004580035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 136083723 1250 136082473 136082491
    0x6020a08070204021b060103031112031311060a0305060414010503030901080a02091309060c02070e0406020903120a021501080616140c03130906060e0d03201b03070509 74
    0x44050300c0340d00403600003a400b268400d400300030101160070104000e03440300d160391000c0c09095141d45000f40041003443da4403c400c3d001203122041d00300100d029640d00c006510b2040c0f03140358091401e21460389110360b00503445000450251596036255205a20440064604104080d0304800d405082082482600c4e40346e4405c00c0b60050300d5104800306900105a010003609040d0360700009100800407044024906550701074800c28049203000300c4805c940b140c000703050030f00c0c01e02c89236540d140001000501081c1e000103c0c490b0603202007021307203205038501d1182d688614641600a45550604641040381140c507000421038a00200341507025000240c012410512505421741ea0043e00b240d03000007400c0180b000d00300c585814401003602c40d250320071940d8a1401e02d5000c0007101c1940d00035008100009804444035150300800d0b428198040c1003204074019a000ca00c0c012461403405000035004524a860019202c0762000c08044070840c181c40b01561502c00380002d060381140e00080c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 136084973 1250 136083723 136083733
    0x1207210b0a0b0a05061602042f030105280b030708061206010602061906050604032103020306030307020f130e030901091a040e04260307030c0c05100b0a0503010608010501030b0f010602 81
    0x841441d2682c01001b103142658040700400b4040c0d0000380480d1030708404c20240380f0b00d03492042c4e40c400010b00300d507000c0800c5100440c115414100465400041201000e4070031310300c8488109540602e02d807074401445410001552850300300d1006004680540300c0a014071043d26070316490040118605050314002c2d40101034565400c2c891020010b031100c1c0c0c0e03070030495072224046403035141c031002840694003852000d440001c54209450004440c006480205881801030100b40d6030040115460190102d4640341c607400000000ba642803000700c3d0f640a1a4136006240102c00e2010020f80402c140c2621009001d585e10150845028100038810350f904d6400c2109000d002e455a40c51034125004e940f41d400030360b0400c0c254000351010350148008082c07020040180d070561502a0403810f2000303190a071840b80c80c40d0345044d5200c6000d01d42c01c040b1600e480c414401502c81c20341000090100400a1003280e6031030f07015900819007804190b83c40c4541e10700007001c100340300b00c01074104c80b42da134002d00c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 136086223 1250 136084973 136084979
    0x151101020c1b19080303070f080708010b07080906070606030201030e0a0201200c120705090c040b030a1e09030305093007080708180102070603060f051207210b0a0b0a 73
    0xba14021506860f5030024400d0b9028243c01120441c4501600019005598a0800410140141448072a42d004203e5060100540c03030b0740c0000440e0440e0300c0801c80e26100d04140ca0041711900842c0e40c0c0c00d8101d400460803c4c28000c50b030308440d0490307000380c1f020004d403003400d480503441e200e02d600e019003ca05461000c24060550000d84610080d411081c0c4015002d4000001c12040b40d042c41106690300904083c8000d14041c40c106801020300b6011070700d0f20346400c44012803400300400c00144a40d4032000008003468030070b044450060100b5080109840e60701d030280c000c20040c0c030a80e6881c0300f980b0742c0c00740300742614046492100104000e09542040741001418a41c480c643c101c80030751052081100055800014001221202403d10481042003000a24041250340070390300701418503900b04130340f1501c2040c040c20b9580a03201c80c00826900303540d4278503082d0140d01000620404c00d40e07400c0504824101969402d11034943c9000301c1d00e503c0b030102d059804628490fa80000c03000d03810 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 136087473 1250 136086223 136086253
    0x1202040b07081309020f0403060501050105030412030b010207030212281a0c0708030c0a020118110d050a020a0b0a020d0504060801090b1206090601080123070c0206040906151101020c 80
    0x1601c3d014149029480f0880d841c4d9580000342d8000c1d008802019001240910420035980a0326015213000c0c41c0150561404da122109402d203031968640900d69a9100e81c1c4080e40309211000185801412084111b413940200c10f903299005403035505030050081400e000c0b629101c0b20031000da60030210054002d440074079424000c0704040d00b49c00044204001480000d51910003651103100c4041e109511809040c3c400313070a5400a41c1c0307045c558811074131070500042000260811010096030007441c0600300e803911524040c003248010350320a01d008800116030764000010030301528542d00f0b54419640c90001501d09003d42c0c040c00021a03075a0780103000950103135000740c856050041c074405100600c0420281402070540b84c80c503135504079800521002c4400d01841466a021103913591005030500e040303103c00c02010303128408016041f00b5400665545a043e18082d00002d4001c01801ba44c0c0d00803000380a8400c0b2245000c110f0009041c44a07030410301c242c03160210003201900f1562402c984d9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 136088723 1250 136087473 136087477
    0x30c06040509250216060e0108010b030c071b03051618050a0b0d03030501151803020d0501090b090c010e091e070302190806041407020d0503040302030d0509030a1202040b0708 77
    0x10b030501a03801610f88040048a26082c042800c5850700942100349130380c0b807810a4000c2039000f41d024844122007017180e41c0d0b44851000d0442d00c0107000d0350380341e41740d08031004100d20402201400300d85080112800c1815444401c0088030b00c200704a40315071900c00010303502c0d440144644040b046509241005d50203450f044164092034104002030b01c609140005140703040c01100a070006503031880148414400d01039205402012424014214800c40750030512036411400005c1c010760300101d00c8010000700350820040141e00005048491610090030341c1e0324a0070703081e5140040c2210a2060150411500680c018030075a041e200580600f0502c5410214001e0454802c0660811102040310900c0c4003034014406c4d20740c1d0b80c8505050010801054070518400c004a4044075418410b41c01e07000112182c900c900360a0880e03da640f1418240d045000300703a00e00034454184010403101c5413010004049284864891080c1802d00d904414201d0095010350300e2210010000e1401007491200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 136089973 1250 136088723 136088731
    0x406020a030b0607060507030605030111160510020c030304050c0922140706032a050403031404260114070206071107080f0604051b090c03040206090d11030705030c06040509 76
    0xa001c504480301c2d8000c1241644901400e0310700d16030380e0061021296260103130704004c00b4207c0082c8030380f03008404041e9032441051520004007024803010010030000740544800551041002c64641e80c9a0301e8885d1a580103c0d02203c144c0500454512289091800c59008100800c0041c4291201505240c0044500f03002902c030302c0850107119403229810000f4034050b00480d80e000c5480100320030002200038110082c8909906040b0b00d0404a546c040c2c140c40845c1e0f0185003050245007280040c12031840750790442d80f411402d203004240c0e1120a007103902d00309640000200082c44190100444036142038400f1130050700500d001c2203501e0310418118410203420350550718003d643c2c01400e498116040c0c07000f440740d00020104000e10205000c040701800d01024941003190440340002e0b4050300007412103000e40740110101c0c0035500c400043e00c6800c0030281096074807812608250040080301507199219108001c40441c1505011604100504001c2c024a061605110803c0b1103568010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 136091223 1250 136089973 136089977
    0xf06070e061c151a0304020d12140f0a091e03060f0e070f1a04150305070e060309012903030306040c020f0604110307090507050304110f032b020c090406020a 69
    0x99031484030340c04620035480d0048055445009113803402e86940b861300260100d40c0c0801c5828400c00001d602c038010b400d070b92181e00c4000c03080f005481c403c007560049a0070092000c803400c0440c28a5210300888000c052148090b00d600d11201ea48003131aa0020b101c104035030400b02000c80d81000060b031242c1001403031121392140410340540c4c600140349402c0321980104c480300c03034040e000c0000448101076030038a0007246031300901e00b0382802d1082550752841c0c08102d0800d65240700095509118500c29050b03603100404450b81c03400c2028405019210030001d03209034103144403030300c41d59840c0c4003112241868080c0107141159200400c00004040015a4030103501822a00541d0382c0424402d207440b4a00c07034003003150041002014186881441c0d0403141c0d10a181109201c04c2c01d0304001034030781c440d62002e2100035030700c1e04202107840001da00c4411307900361107080040b0f8000060310607203070b5212030300a840c078860840e1004202da4646403000c0343c40d0458144004500850030940060000d85114 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 136092473 1250 136091223 136091257
    0xa0917061f080a02040905010b04180b061903240204060f0f020d0e012d0206010e130b060919050a060612060b1b0703020901060c060c18050d1104020703020102040302030f06070e06 79
    0x1d0000c5020780b0700d150031003113080be0003680c408200091003285a41002098a10500300d10941c004802d1a10480c003004e440002001c041d8600124454000000305041c01d0055450765a07070038000c0c01d401804031a0f14082419841d40f60b501c28800541054041c40c640ea41e540351b6002480159814a05510401d040506c1000c0700012942c407812114410407440e401008207601d408005a01298007402e103145a01c030081400020446003000aa0000c01c200c62901d559140ea0b80120f6001e0f8030707001c4a0004605001c00c002214007551711100444085480e800300004500d130121045580d54080c08024580038040601101410140e40e154091940e04407400d039502d03034001078000700c803d92000002408030107041c000c110150050005544050a10101c41c42c440e45004540c0501030042c0ca014010900c40c2c0828414941d005510705c0300042d02c00c55a903111410b00034081e42c4180000e0307000e4895856060f040c8180051482e100c0e40e1135644a0207800107980c1000750365030024048510f8028a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 136093723 1250 136092473 136092491
    0x5090a050a03050708060a0b030a0303022203120e0d1509030908010e0105040212030a020606130906060b040314030406080601050a0e1c02090606040308030a020a0917061f080a0204090501 82
    0x48801c0480514060f40040c0682c40c03030984064a80f02005114956560030001c50b5241c0d501c0000b1807900441d4181409030300c40c0c1c0100c4584000c07030112886e6005100c459000003080c000c080300000a07405603070b914400c851100390184080b00e400507400510200206d110000181000d40c01840d040d0310901d011215181c0e10741c80315094901103032110505954800c144021451314141d42c0e4403951082003d103040ca251034502a40b6131900074003060042c1200d0040c0c4804400c280c1c045034006611690400010b52140c05060b03254000d808100c0d9104500c82c098440d11000009690445181d60f60384107840e501e15004662603000a170740c03102440212186000359585032031100c0c1442e41222000c10745070385580100216980d000d01214040c542c100001e1020610100031280c1c40540034901590700e02107108200ca55181a60080c1c00140c0c81089042c2805d03408561103000b0180b10612507501410b40200e1611500b07a40711342e103120743c4a6004c80c0010300b41500800d150398062000081d11100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 136094973 1250 136093723 136093729
    0x10206151903080d201e09040908040302030d0806030604030c0c0e0a151406070f1b08061006090b03040b2e060909050103170c0106050301090c090b010206060a0605090a05 75
    0x4040d80007103030521800304408070441100d21a000780088003170041c40c0c3c001c040c0d03041082c680c480c007150604500d14070000c0c650005180c0080b111074a0014000b001400442d041c00c0c1942c5c0c0050100700d10900070b901c2462005403141400b1805201d0080140c04952215034043d9041c442c20300c000c651500f131210001030280218041148104d075178402c003003510380c3c40e50b1700750f03600c05050b8200c3c920b5210b17242004000c0ba1125402d503400541d01010f218401c40711414400c451946c40009021840d0780c04002081b1000080780c4036014a250b40641c12040da100e80060301c0510203070260131096442800010042002100340742c0d00040c440101e00d020540c5050000b81384c7c400d41a11407014401c3d0042040a65400860800149124a000c0040c0e50440e40c0c4c00c0c8091007002d0b02005044400706540c9103150007940300500600004000f0800c051a40c41c1000c000b0702c26200740d03000c0d285000c009181950002c1501c03440f444008190546071410b024095810b0381095800c190000d000c0e01c408111a1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 136096223 1250 136094973 136095019
    0x6040905030a180b030c03010e041416030b0709060503010b0d0204050a141c020310022d0301060f08010810090201170403080406050106081b0a030603050f0f0111190e010c0206030a0c0e01020102070201020615 91
    0x300801c3341045405040d4144444001c00103010b10040000c03844c401c0040c0da5005041d40c0c15280b00400d290348e1090104404406405160002540000d40f00c50006606869403100b0303c0703043e0f00781c8080812040208840850781204000030790150400c4030801144095075004085107031150b640242506081c40c91010190083d4003418507580000006010241d0040c0900329a550140341030134081d0f050020311910340b0103550f0100c08607910740c000c0608582c0900c0300300e1885070310080418050b2900c3d04000b4030581003924141c1e4110f2030b14001007401d0344070700070040c801c0c0301d0790307940c05080f000803c8220b42940c00204401c08060342e50f0b201200044003030081c9801c0045480c002c00110510100b13071401c585094000d040c044030100308241c01040b074011421020000b80c100500c0c0c0c41c20300ca00580d081c5010b110000c2d4080400010040c03258407030780c040038070300e15030b599004541094030005a0803031040306000303409640068002440030301c0c8019884540ca201031310000250f210615991001c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 136097473 1250 136096223 136096243
    0xf060902160203010506030102090a031e1a0105010f110c010e1924030c02070b03070e041d0d050301060c020904060b0d080a0e0603041a06040905030a180b030c03010e0414 75
    0x7299240e859281035182c240105600018224021440e0409040024050044511006102c500101d007201070600d50240f0714241c540d0080a0549030342c0c01c03000946d0080d4024025a80450402c001c10308030300e4883c85002c001e44820200074a880c140c1c200c0103480c551001d0400307a910401c14202c048164012300b91a00c010710459000700003900e100684002075078000b88407007040515048801a003103500003203883c00c6030000b1191540e0303902c07000422641001525038142c1c0250612a00c1ea043d590f10005020b003024644065508405100f030080710b442c8828454030001400031030402e005071400d6804160030910400c400510b0307011040c0440c480c505282c80694803003034041244951f0940042d506034a80c0c0302124070310b2551506540e000c102204030004042d00d502d5160015407252150313072241418a403c441181e4031a800520004d12420580114550000610000003410342e0f04038141c0e40590101e03c1a2410343e0b0a24012100f81e03d8000c0c801e4421607803404102216650078040101c0e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 136098723 1250 136097473 136097497
    0x40822080f01020d060504150308031510050408010c0e0a18020408120309070e0f040b06010c0f05160503030306030c040e0709061203080c0a0f1b050f01050f01270f060902 75
    0x7200c804400b1401110b8146e0301c441c0c05142819044585c01e40b0040c4100700303495008128070b0f00d036183d5800c03000184001e001c0a1313811070035401000102035003010150040740d0024000b0304c803440458408480340381c0030381107141d00500300c3ca9081c440302504903620002401d00500040c20316076500780b2240340031110743c0d5041e50110300006001c12040d06100042c013800e404000b400039801e042c41020941c510013800509028482c1000c00d00a81c4100c031202e000a400410b1504d80460030301b89540c58107404011000b41d0b200035000041c407810702000342c0e03104010080150040c3c040190500014041d900203a02d1640225103020452403400c0c802c80001e0091902070f821101038038500940030784006004416104030901500303c18035031000c4204100340d000c0c44d2020400728a06a421551402d000000380a80203202c5115060801540002d102d900e01141107002070b6a98100c03100c3c000240845135005203501d420360480c266480d00b0a02c207401c00308000241060b91035040004030f8024402d0010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 136099973 1250 136098723 136098727
    0xd030807021f0605030c0d05060403080c280201050a1e020304061407030204030203190819030f09030e09013c050d030e090a020c19050a02092a03040822080f0102 71
    0x815401c0802c1075118111b01a03912100c05801601c90039034941c4010b0009080007500030014120f451254140d17550b1021540402c0005555034004c0300c5141c1241c2e21000041d845c00c00008c40e085400c0c0038980808a84407081c160300001280304c100071303500041c42911141d844280031008500c001c10100e1090400b07a50050b22603045104250070031111903c080c41541d44074510700041500c5a00b1185c80005440b80402c0c4241ca4074000e40250218010402c01549003290b21800e240e044103186040d100c0446402c050390781c90f421052a0201441c04440501c00c086041c04001c60749501c614080c01c60006442c0d82c020b50740c4c00000c40300c00d00d8010450006041020326051420700341c40e030039002462a03d003541403c8501400d43c1d43c9070800c6441908054002001f08103014050290300342d103a40240c040c07103003850640b201c41040b11000d11420b680310071640e8079056460880c000d81e8000c0307520a01151902102003d28140d65811601c1c0521400c1d500c00000740480040088030396980500700090303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 136101223 1250 136099973 136099979
    0x2041b050c010c0e09060d050f010f0e1606020d050c0f0a060e0d140a05160b0a0204080609030a02030a030e100905070f0501021b040c05070f03080117010b0d030807021f06 75
    0x16003582c43c0540584240000710440c0b9106503250000304c4ea001c40262454418000141405441d284442e03031540099441d002d00c554240c811604980c41d090826800c031524005814210705065031544920300c0145c001ca01c80100c654030800080c022548200d044810300482c0350754007814041c1a90084800325642c80c010300c0d04103002e0188100b1b00041d07003000241240c1007010402180701c0d1450800400a00050742036044400410700300c0950f402c1240d042c002c0c5451035240e0700030351090041182c180f04090000b800f0390400400c40ea41220154042e500388009003a00380c003d00864290032000e40181c440818000324030b4400c00300a5030058005007071807898051070b200c8641c1036400c518115001040c800741091507480340c0075040d9100303440004a0243c0b41008807154028810028214030024182c6403c0c583d1240041c1c2c1614080c410b0741d01000b1003c5216401c0f5030048081d0380d0003141420394040030034060310100e540401345005440c0184407004444144000c00346000c054555141000c1c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 136102473 1250 136101223 136101247
    0xa0905070816030c09050907120e0c09130c030b060a0503031218030a2f070b0d0b04060e040620040906030c0e010e01090209041401091a04111602041b05 67
    0x414482d0541d00b4100030b01076030110300800d0343e009402000c0c011003819020503079039445030208140040801c00700300203c2980310802034864a07610b00789480b41e2518404200880407040c4130405040d400101c61664920b0343d034442d00750340ea0007080264420340b00000020151018001042c04101c2a080c00c4413031700c2c080ca0301c5032070b40c03101550a0005600500c5084152500480b529411601ca4406100801e401c0000040d4144211000800c80d02404400040380c08254002d0640407040c881c2c00d00c00b0000c110244401c0702d02500c200411600ea900104011032030a5024a41c1581c0c140c0c200d205502000241d010f0315801359001e1000036503104002c00c00e101c0708480030400390500a840c03101b25490048031200030303030b0107000300c1c01c040341c2c0000c9200c4507558645c80542408a5454485215070f52040003100800845020904401841101d039005103418440d01c5141d86517803036442d00300091300c94041c1800384c4491080303810a03a26600800c043c400c00a449051620310b980703440d514034115a0b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 136103723 1250 136102473 136102501
    0x5010b03090f120906250506102103051c1a0312090d02090916030c140102010b22020706020c0703140c010f080c0d0c020102091908100504020a09050708 67
    0x44021941000840c810320401c2201242c6101300d00301c5900751107102118200f500c0d0344200350303442d10f08005108004100140410403601c41c500c158081d0900c140d07907103842c1c485030340300c9075030891119400ea20340c0000034014406001c1c0c0030440392030003142c41c81c11040c032030803181d414401415090702c005071001e140c0360400440402c8a0389000d030030305104080e004100342c0a081040248600c00ca540040c07090101085074021030743c401d0700791408107540ca0410864440d2140560b03405403002a180c800765500500910b44010000703026a40e010800c5070080454010003580080c02c2c60b000c0241c400401c0380c50000c2c1c800c03203c50724007400c00c0d41c1c40d5160800c3c1c800481c4803100746c190855036444200ba80c211600c0c04800516080c10000c5568005e00c40384a841041540c10405241c0070b4460506503055000c0c02c0705010a030780c900c01e07403201042403400d000d03030f58480d102c2d80b603100c440d0280304240c01d600041d4101c0d10142c04500e0b110341743c0303107400165a03044421000141d01002001941501c01c90 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 136104973 1250 136103723 136103743
    0x30a1e0501091e0b0a1422090303140f010b090604050402041d071128080712081e011701181104060b040302030c01080c2106030706050301051c03020c0405010b0309 72
    0x1402c004c0f40c803001003ca110245240304501c2122403000d41d50015484240d000c0b06c1d14034803480e0010f95004031030800c2d0010440c25009500113440c11016051031b9280741141ca000322040c20302080168680706411020358401103a01d07402c10800c2c407000600d52114000f0740090802c0f4448021000c001c44203030400e00704000c009504001100da0769180110010403401130b404088490204c416101007400c0000c0c843c00c010003044c04000050b1807040c4846039030781c1c2055044940d036483ca2502c079130a15007013451801301356180c0d1252880041110700840d0280c18400301c0984008240c3d0140b44041c401841e070340000941e0110092410312403c0c1c0381034400c004c0540404060349003006c3c110b4000c01e80e58141301480506000c0150081075504a00030103568071405000c078078920f05020a03070b40c01c03014034054075030b640244510032011030800d000d042602d050303c101404501e051103a958920044500701c8070243c00f5401140444000b42c2c445000d03490103000142d491980c1c4e820514400751410395020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 136106223 1250 136104973 136105031
    0x60d0605071e022406060d15050a080606010207080c030d0e24130603110304060203100f0b0406021501242d020c0130110c061801060b030a1e050109 65
    0x131041022554601040c0c40f0040c0702c400c0006039841d00156180011070030341e041540c3c4000301c2100012407001c0012114424502030b403d807450345540302045655018490500c2e581500203a00c1c040c0c0c503a2050284116a860082c1546040c01d10b14100c5001c91140c541d0030915520009440982802c21488400003803d2900c0c080002c51301c0c03c2c02041e59400054801030680d500000030409a0502c101c110f0080d10417425031804e0b481e60ba09034440c00d41e2082c421003015000e96481021200003102034241200c800900c152003030040285104180d040030b00c460300a200e81c0c1f040c407048120241000d840e8445003541c0c1140340f20f0b003403040640780105450740c0504022000202440050511010316200146031a0140a44031140740310b0012f406010034030020100040f8222008010002d089800303001108510300c4030a0301c11100700e003030f01d11500440b6515142080411500915a48000035400004207081740005100444600342d60080c0c1c0b00c03005194441100b110043e800c0c01d21070f52110110303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 136107473 1250 136106223 136106293
    0x4090807050f0304081c0203070203120c07051e0103050702100606030c0e060310060302030601020a0203010510031a10030305090d0b10030c14010c06021b06041b0e060d0605071e02 79
    0x86902c5170340300030306880310001c111b02020954696000b002601c15075540141518150030070001003989580040317105200c4e0340b0400200141ca410610741016110b903549112302003d050b243c0064015000191502c4111312a50f020820685554442d81000c1c049650300850910030308800102000f018180030b9100320710402c1481040300030780d4035900403205141005601c0340d0702c0700e0040c0d06061031110069019406e001c20401c0e401a40039801059034844c3d84100286024550148003009003100d59094101120b001880800e000d0b001520f40050021300c00b90103400c10307a0340c510411105482d05403111840d4101842084400c05450028101ca000c0c02c00940d40780c40c000030700017000e8290191a45900080c0c440c581b1459280404030110300904503103141c2400c3c030740390821604d407003005203125001c1140813606240030801203004040040c03003880c071811a6102e000c02840003809090600c2061048900b001104d00e0041070000141d0f0045c1034041c111000060800c501d8500c150070248c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 136108723 1250 136107473 136107479
    0xe13020a0e060d120e120303100b040303090e0c04090905010c030c03020c150402042a0908011b03020309010b1f080105030a020d080715021605010e0d12091104090807050f0304 77
    0x2040904642183c01c22444c4d40d0600d00e01c2c1040d0350301a2480c10945e0002d4910544070114003002000798014440745841f00409503a42014003000d0280303020003000148441820002c80031b441c0e0f01260000140b00e009458140d0341d110000480d541d10f18122500e94407000d40000703441c0c0603c2150b0030a0700e02d045c190716054170b00100c0c90b101c0188482d288000f8032240e01090079901c0e25842005002840303091190500c0c04a000007079407019030840400094112074010800c8038040c0070303910302000c43c1d10750b565001c0074241040e8042c0d04010b0941f4020b640ea03c0407610195500010050064004072403560142c407005c0004185e108160080c50085d445404a0340068071508079440f01950070070800340c3c90f480c1c1c0d841e10805540050140c2104a400420400348034110301301e42100051140d0006c001401894001e640c07200f0500007940045030748210100c03141102d5070403000c5003510072219829054850000101280d440c1c40c1e080d6203500c404940042003050400c00751202d002114002c5040601d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 136109973 1250 136108723 136108729
    0x5010f030911040216050d11060106171305030702301c0f020708010c0e1e280902040e011a07050c040c1b1203050c040305100203100e13020a0e06 64
    0xc0c070084207400343c1d82c00100341c1320313040d10400e40312106a03000042e10541c3c540c100300204640801c0000c94854000c490000510174001d0101c0380c044140a550815143d0b40d80c0c107440d9841c001d400059500c0e0008001a5005a5a035020929801030b1f01c1d000348038003c0007650700c0c1001c5422201ca81c4442e2322408050803010a070348800700902d0007a2a00c03114500c4403003012030910759113074003080c0151f081c805010b8005400c801d2410301c074001a20505031103040f0b00c074070200c110300901c280d94208011042d64161500c0311702007030030f40500c0c00c0401d2300c51540e00d01d00c120813603006620100355021400300600000c3c000c84030f4200c4a04e1f204400600b845440d4458544804400f940c1c507100e5960349130000301013401890700c0703a4084d01e03415042d80e00c80c156042c400c2e0b062800524841c0001d103884006041500454103032001d80341c020740142611951041504000d50011b8001c0c00703048111980000c1c02caa459107003521503428078030a03404826040c0305221001541d0b130800f5406040700010004591 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 136111223 1250 136109973 136109993
    0xb011e030c230303040f091415090702160b0409060506040e0703180c17010e010516181a07061b211b0f11030702032e02040e0105010f0309 61
    0x40541220034091128154515100001c01c1e2650743c06001c081800101c41181620400480780300c414184040c190100c444500710390111850b0821440390040c0d1030b400d0030451006071b030040c1c00340101c41d43d010079030170701103170554155102000900300000c05014141c0345001d210010101035450508290a110311405190401481181050713602d5000d1880c406042043e10200c98100000303116003620344400381c04070200308645000035804d00c2007100d118441481002d2095900302002940369912181c1112095100c0c0d0309807001c0c282880340030600881c81c00da40c02a0007084814207694a22a00c8d110b02a44c00050501e598503c0000404100715003104055a0702080140004002202d2841000082600340b058259100c00c2054815959400610309030f42c13012192101c9107041098414545d8038460550029099000303103418007a4050f00004041032201c0d602c110070410720720700280740300b00e0300140d0080309420305510042003d541c0107a105400d0b121240b4042c094070a40b030b19039803110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 136112473 1250 136111223 136111229
    0x6040806060126043207090c0c0605070f0908010614011202120a0506030c03010501080c1020030d050a0e0d050903011d0604030801120507030308041e0b011e030c 71
    0x40460300c80002e5003034014442c540c0c80400801a04100c0713051909160404c00500c04c04000d00000b000d80c01c51007406800c048072149114500104025410443c050014205000410741400500004070000941c60301466203e9001d0b84d84014940310b0140c001002000b19a001007200e902d0110103000e002d0304015111040340c020708160703801e454882c03003000c004c2c0701e0f004080e03200c0310300e21045c8408a100f54000d035000e040d041b02200e4059122030101422a070003803144031602d600588454540381440311180350707141e203135003003c40210301001c03502c402c00070000510843d81c2c1c0001441d0a4002c0091044680244181700304202c103140080c40d9998030082c0070421824440049103140e0f1690b0250440c0c0c1034032400303030060311128440c024840e6a841c0161400c80120380e84000120300040c03104007142059030000018910309241d528182d406d100050030560380410710002000740c144140408001030751051005504541c5002641c411410346407c82c54404450b005040000c031b01c0e0f40d072606d415 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 136113723 1250 136112473 136112477
    0x6150e011106040b1008010e0f0705040e060112020f030609101a090a0504110a030309170d14071104090b04061506120216020a181109060301060c030239060408060601 73
    0xc680c0310740b05d002a0000580d4410601582005c811500c20040072a0401d00c400400742160f2601c3d44030010402038540059074914540d0012004115401201ca07008812a00141c41c502c10100e5803030103e4200641111540d1980d4454801c6080d404040c1c801d00404c00c038444400d840096201c4002030300c00002412011580b900c42c4003150034001a403413802c003032030802410400f0065982c5000341c03c3c000b2520501340000b0520100d079241503404103c413000e0300e02564825900d007a426414810b99081500181c0d1001055090b62441d912079100341c922160042c10142400c1c0f41c54604081550401242c109030243c0100c8104a855000040c551a0040d82c040260b155100e10001c00031304071601c5000380d44a40500400265250501d00107680d0100024040c48104036280900d141807213005a95a08103408000401c6007030300c1009082c003010300c6441a640540b00c518401c8446e106041250b201d50380b800c82e0058880403108904a0414800380c5400c0d003460310f032200d0142c403000f0007014241 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 136114973 1250 136113723 136113743
    0x9040b06010e0901121709011b0303020c03070303020306190e060f03150a06030314070f06090305210601020d0216030b07050705010603080910030b0f011b0606150e01110604 76
    0x240316801540032402102000d4140d0034290380d01e4085c194410300a0800341c2c0c074400314900310441550368804950b95004182c4500d41f04554004038050250311000e429010150f0034000740c43c0e994010300040207101c0c0256409070301d9040c16400c120003144241c01a218042880c80c04000090b0394034002e42e8464000c6a490b10b5012241010a050071400c4902c107482601c054200030320000c0da80d0041058902980d103044003855403900307600c4a44510704000d061140d17122000c000188035a009824a240b1030714056050105d071004c0400003010041c282211620703401c1c01c020095074100694180e0111610040402c2100300301030300311202003404040c0c110b4442100069181b03005008807110b1300d5005000304131a42ea00d003002d190f180c0004620034800c950010503001054481d02500701a00d000506499145803400c0c01034480600070400c40c608244040100f0010501e40e100700001000340740e80000c8440c1030142e0040410319941084c80c184030040c0c2c00035508010000c0c41c96030083d40845d03028 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 136116223 1250 136114973 136114981
    0x3030c250320010207060501120b07020a05030d0f06050d061407021204030609020307150206010e071106150f04230a150314100e15090d0f180b031e090102070209040b 73
    0xd40617126281d800307860a41020000940039460480e03a40455000c0d40c040701180c0c40d100c40413a241e001824015191303500a21072440383d086550b011503c0c0d407207148000545203030350f840400c004a1503100305882c1c07542e03600d000c190441064000c903940203e05d40301802c8070320159180c04841e8000d030f01010b445556505405011918200192005403840070707841104070404002c002d50707900c800d010308c00840e6011808520b6090050010020304034000e806007143e9601c0d981c0203d9600a1004803c0d40300d50b03610381e014829145e070b00c10520801e80c140c0300492012500c00441084c400c2c0500f400b808640760281d4410400070700000303901520740c015080e1a0b8107035400f01d01072401d503210401443c0c0c40c0c40c0c905204102c980005a64050034426501d4a20666030105a942c031031881109010215400900d400041441440b003541d100482d16840e18000345c80d0507030716000d504101c815071016400c0600003080307640d1941c0d5050340300301d4240096142903100d5000ca4190080980010a00005070003c5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 136117473 1250 136116223 136116287
    0x703030f151a04050a0e1009020a05030a0213180204081513080d1103010f0504050a140604090503070b010b09011812150e0d02030a120b0a030219030503030c2503 71
    0x103a000304402440e04921710b84900c40072009002c10f640701c00716455000c000094050300e81c02682da00140300c0e01e865040d0350390ac0d003000000e035019000c4464183e00300c10000c5800d00d001b46404080b01410b410041c2c5841c00c0410f4036281100c81c03a40c2c070351106440d00400c000301c1035900c8001c00c01350340220740d03649419a01125001900070b03a404014a010044004103048007000c0450048070012603052000703440d00c600e800115401070041c00400158100081c2d80c904098020414852044e42201d05e8102581c5422204580a80254000c01d00c005250904d660f8072804681004c180403002e54041490000554060700c1c11003002082c01c40c10722041005105558048107510b01c102c41920190241684029229848840340c8408a410340d070008c555a489403048085400b8043c04c05100f8500b19020803020b03001e8890000a664418000400000c8081c0003440c05035407100506031702c1d41840c0d4400882200060f51111b41c80d05c1c40880344c00440da1004807501c900c0d0707485d484d100c4070345803141da4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 136118723 1250 136117473 136117477
    0x406390309050f0303160306050603150f01090302130903090501090b12070302041e05100507050601050609040207020a0e06090c030f130c0b1206040b0a030c0b0a09030c0303050703030f151a 83
    0x1128444c0c040401006046a003050780300000c460356540400072a51100100450790000b0703030b03554420740782e8003015110b5410541c983c994540f0050400c0b0b5912a601d5001860418006142d00040d54684c0395500805030818010f002500003400d04041507401c11a6044403406501c0704080b40b1140c810110319514026811140a40102d1103222038103260003a0b00007a8120a02c13501d4020404200c1d40b00d8864480c00554200607400006440716905c0c1c4001c101d4203802000d2120b42c041c0e030070030601006941e61241c50008185102406485103020b87c100000218010a14010030000300204880340922845181d44800301c1c2182c030742000c0369410080811452600104540c84001403080c149084625245100c0e007400c460500500c1e00c12001e0103040302c40b41c400100300403890042446140d14040181103503103030038540030250b11f86d81d071075000358541d10742d00640125100040072028164580641c1600c0b000400d82440071000752005880c0000e098412012080d040e0481d03044076240600c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 136119973 1250 136118723 136118743
    0x6020d0605060d0213081c23040f080d020a03050703080403020a0605010906050f030d020c011202120a021801030501080d0e281d010302060909040f0b040639030905 72
    0x40025260300e003c1003080000d6008006019085200c0c62000840500004e1aa4441114011140100c6200c00b0741543d802c4d16000d10f081c4d254002c0c06401942c81200350141c0300034030310381094090071450701c0c5072681400e0702940c003201150040d0312040d011035003100442d5480f031341c9458601d1315503039141412030801821000c001e00481c28000005078141d5907800a10a603602101d41511744a0f0f1305c0205955840080f5055001d608220303020441c1c0d6020b03134060b818005c401280545441c8803000d003885000c1c03040f9449030601b6070116000b40001104504010306030700038201084654181000d560759452a10960410054a03240081c8161180c06006004034003510300c03804240c2d200940e0041508650192840f012005000141e00200340180b813412213401414840c81d1138814014020501c10040003641c0035a004c40c440c2000441c4010520700c0386004410010340018034450030f1a081c440300e5424078925400d004d21503288280c3c1c41010115007228100028103840342e00c0c000d030418110f11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 136121223 1250 136119973 136119979
    0x801030b0c0912030912062413020c010515010302090307141c0f050f150a05060105040302030a050106180c0503060d0c080607020f060a02040806070c050f03040b1e0403030203030406020d0605 84
    0x20324a1504200000207012034440c11507010511b0900310200036a964011525949040d17804039030700d02441e0f8250025a80c250019042180d0a034844c0d08c42003d90b8440705210b401c5a64940c10810080c0502d00603401a010910702036103461000350019941340503500a01801038010231103052150713a000710030110340b00b41c008241010140c41c02c250075414417240d41a1100d00407884020903141011441d140942201c0300324005e00c1d12b0342c28019005090041516040c031004020200c05684d04208000e8001d114000205049061144641307010b04515529981d40307003003001c8505002c0e0401c00f82ca80c800307806e8809034810452420141608482548035408600802085c85403d0707601240b00d01d401144801140e0891321400303040f000701d01c036034801c5503216000540400c041500c030300110f07000103000d0b0040b580e1001d0035840c070b00d0542c0d005a000b10000c46000541e40c81014610001115002120a1450405103107480c06502c0b44001480280816400150503c0301070321540164040c04c806 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 136122473 1250 136121223 136121239
    0x10b18041e0626100905120414040c02120d0f11040b030702190f0f030201060810020901110d0c1e0b0415050619180e0a1b0909030801030b0c09 63
    0x310000340c018406400b5040c86120035100c4420b9000c1c9242c42101080e1190f0024000074581c80700ca40010651410121a1802071000c094818548040541301400c1710b12500b03208003041c181000219900c01c1c00e000250b410519240110728103513010798a11400400010903901911443c00000781103604e1040b2146c00c1c0410081942c052500241d481544c0c41d8007100e18126207103907810b50510a43c8001024110500d40940c0042c201c42c0300c1001d482d00ca0700000c6003040e02c0f00001800d2101c0d02c405002036035404a00c0403581d683c030101c0c4403034150340680540141e420700f0100418605140401901c0940c00c1046003440f640949101d444884d003001418195050900d0300441c440f6101100e001703201e0a250100e0001e2074002031180c07080c0380c3c2c01d1031300800a25042d40740500c03100154401056a545101c0c40e00300383c0041c030680172403500c60b44005209001c0420414500d80d40c0d50850082c2e10315002c041e50000350058030782d5041d25004118030301d070355440c3c1031a41410320030803d40356003226031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 136123723 1250 136122473 136122521
    0x120906020d020c19020303030a02180d03110705060708030f0c071a010e0603241807030b0609100602070b0d0207121e0c0203031b010912020d0e09010b1804 68
    0x1d40c0c05000c3d20600c10099421076810070405085003100100081e42c90341082011948912050380205840f4210140c070b203000700c1045002a40b400220803050300401c140441c0c841c0004004d005010140c0b030111092402d01c1d040b6200c040c0140002082c480c244601800861058030300c5100b6180025804260000d440e22100307108000342c9000c0c45490703415403060005c5612841d0110320040c4041271076200001c1c00032020304074444000f0141200b900c4541030012100491014842d4502071400f842851a007420481c090145071078005003000c020100c00c074030034001c0c0707035001c100c40f004c41b018206174035224892120380c1c8000344070b04400140075140b840d140000d0940c010300021a000420080d40e00c0751415943c00796007508180710000d606400c1000580c0c41002c101500c10100b42c0314000001e01e0020035500c0c0340d0301840880d2540c0160380a43d03400c40b00c46a020303c0e42c2d0383c6032074256914942c0d9407401000400e00e00070180d8401400c490750180410300e88aa40c44444401281414100c2502e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 136124973 1250 136123723 136123747
    0x9260a11010305010b0c06070309080408010603030e0f0108040b070503060a0b0307031a040c020705011101020c0102211b04030201110c15042904120302070b070602040510090b030712090602 83
    0x40d40c5044502103401d000001801029000036103030089000d40c041c0c2440e0395004c50450050060540441c4c3d105400d010105500800348903000c091846900e8480c0c1d407600020030400b404080f10350a904020402d01013000081800220a800c00c07501e0900e035449459940010740044901e410580240c20701208120a00d5810381110354032456280c100b54440d00d4403400d000545a500c116640545e008410811165126004014040381e00c10001400d000203514406e003a644425101c0412803191400896140030505500340c100d4850b0001d0041c01d0400504607545014612020341400150fa014003100b40041c0003484a80200034800d00c0054030501100a040d0018002d520302220b601c00030f03111504207a12080409a003842805007030a280509000c2545270300201101180254440058900d00c0c0c170300502845071007020050b80b150300780170074405403545040025003008561041001000548012203800c4086450008600001075803514041c0200c0c8400501c401e00c0001e454130025 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 136126223 1250 136124973 136124993
    0x2190b0f0601020f06060607060b0301020403050c01110f10050c1207110106090e12160512030103060f0912030c200d020606190e061c0501050105010908010c09260a 72
    0x5400c680500040e200c0400481c0d80d52000161401d00d5809800440d00e285030a00c00b40000302c2c0f0484010031b1030341c040e0001c030742643c1103a030084526034401c0e40c0c20b604568110642000c03e10b18500180f040010022404d9981c0c0b41d640d0b0480f40e0f4a94603001725034080030810490340c010180340c01c001060f0a104071f000342110018880d00b8803175480c0803000310307000445e40600242d800c980c2d00109200c130304080710b580f881d40c810202050000c06000008000400512004211400c1884c10395120740c550b041c0503040e43c1000e0300b01000140740c07604e0a40090391140992520b00524900051203e540321030580f0f601d480b1429800e9982d07070900e42d45052900002d0790010b6680300380c0c03d981454945206010031b94001c150b070300c2d94481407101d081c0541c6010000c655404200103021074100d4075060303035905000000003000d44503a5161030041c049540c0003403d05001b000e242008215132900408020b01e1100c0d00d0040d019170300440c44100c01d800c8c6401c000e040310405000f040c0c0703045140c01e152201c145 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 136127473 1250 136126223 136126231
    0x100311072a0807170109050d1812150b040204050a08010e0d030b010816030216050a0b0105030c010c020405100302190f0b030613021b03210609040f03080702190b 71
    0x48540e81080d03241d050900c0208088601c2c5500802c0703030604008036402d408007640c621040070341d42c0c0c0043c980801d20801c82c00c0e58841098444980003005081000e510100765000084945c0c50100100c00150809150f100d03c500d180c100002e600105400140c003030301c22640141e501c16203100c0c02150014041d481500c14001036000c82d070b0f403481c803240e055042d50440000140491015800900300c6452001201c1446040b40b40040c0f4098540e1542000f50940f0315041c0c074a0b40c482c80448080103500c03da00e50242404500400085114500003048400c102d000280100d450b0340c08101c60001c6201d881003c0e50740204440b41c41081401c40c01c01100e40d81c401d02040070460800000d5001000702100c0c044e880160003982e200030075085800280d407141e420940e000c0c1c0c6541071a0b504d004107201070202d401842101c0300d039034110500030942c050009001e0a00c0b490301007080c040028507071a01401450350508108005a6640f80c0c141d080003414031043c0c03090380c445000c1c40c080004501b030840c41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 136128723 1250 136127473 136127513
    0x10020a0212010b011205010f030209070504030f030f0809060118021b2b1115040f150606030e01360b01080303010509090f060411150c0f0613030e10031107 68
    0x17645010036800060302c00070300c1602400c80e1500410700140c18241d080c1a0f01107444e09000d480c00d95650340788100c200c03540c401036002406d9103600c0840303580d2207600079400003000801032106504046515420001081500040360b1780000c88080c00e000b82442c03141c1090554043e1209a0320750b00c510005074480d80207144801c4c03107108080034900c0c0200b07680c8002144aa000f040e0050040950300d42c0c1c40f401600650300540081044130000312001143c10f10440d00403804202c00d89408805002d840010b1501c00701641002880d81c00c052040800402e0000d10b03240007607428140c1c0140000c0c058520034041d00c4034803400008507480d24004011412140300b524040626901c51404a40b03640e03040f00c41d400ca982002c40032501291915001c01e2a107003000380140b800f94508844201c00b81c1c005400034010b60001c1f00c80d00100b18090000720b6000e4903d1321680314410441d035008001e0180c920301148111a410602c0038100c0c481c0d844000fa054005a105a48032910f0808800e042c1d030007820126 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 136129973 1250 136128723 136128737
    0x120a0323011a030411090c0702030105040311070807030510020f13080d12021c0c020c031009050105011403060103170d0606031506050c07170c0d0c1a04030c0510020a0212010b01 78
    0x9000b00302c07807080c0e8002e030b80c3e4421505058200040d510b03000d04600c0c6420818000d440c05660203200f610f0140384207803076188070109004062402e05040b640300c011540c000349410000704201150200c0095968907005a031400c0319a00c000080c014014400305005246402082d03500740011407a40d0360160f42c48003a0a82c101118050503482070b4409440b5110f900c80c07680b40b800c4011380181e00e641c580c40c01501c900a902038042840e0543c4005145002d5454408600900200388501c501500540d0617400d800c00003080440c0d5100380c10f1200500d00144020410f4000d04258242c50007100400004c1c0102a0b0303d09004025100e0400d1404114840000004080b40102c0807100a004000c2c0501101850014141ca8541d007e940c6510366000e040d02c8001207544d0b600d1a9600309105100c20400e860622502006285241c42c42380c4804038104030034404910310151880c21143e08580201004242e2030049040001c0c1140094000d1204080c404081c181900f100d1500002070303a8141c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 136131223 1250 136129973 136130009
    0x8120301030b0a020414040f060506031504050a0203010509070c060e03120708060306070212090f0402070f030f02060c09090403021e0c130614060a090e0c0301030b0612120a032301 79
    0x202c200c2c4035070304c940c06c2d0303502959801c1c004504054200201032440d0b10800680b4507940c001098940d0701c00c0300d0380101510124920700071858107101f119000701c0b050303100f1030540d81407c021800c0000064079207030a2100c12032650040000302e4002514070303e2424190380d114140406d564580900961741000890308910004009040c00120f0320300c01d03c0e8550092051900800c080c0103940d02414541d500304413128414105c503116800200440740c03284100404580041c04c00901102100c0c2040046400240c10301001200c80b80030380381a0101101c40c15101c2e2218070707080c4e2401c3d0b00d4429401184100700545058008040f918044e4001c050b03488007803043d07030200030900b290b00500510740910040c0c8864000c0b8104803014002e41ca025080c00c1c1446603d5241d417183c442c0c0112404500e80c4800001482080489282c05410100565041c290303440d1880010b5156075800c4200c54140c0401f00381e81603407911a42100613031002060b0300c81c920201e0f03000c15410743c14090080700d4004484020070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 136132473 1250 136131223 136131241
    0xa0f0c06020a02010c0212010b030f03090102010e03030c0324030a0605041b080715020304050d0c080d050304080306040e1002160b01050a03150b04090b07021f060b0405090a0608120301030b 83
    0xb501e03081d80c140e4030041d8042450342000321500d004080c6490540da11403000d00717141c03410802100c1080c5124021512114031100090035114080040d9406d40c1041c005d000b54088120192900510f0742041c07040c0003005911a80c40d84c082100811364144180d50b5082c1c1440b0980d4031031030240707000b014007601d107445948118580b00207510640010740e0124008200010800112401c0300704948152813409941c1c1001440c295000c0c1c1040d501982d40c2c4a0421548500304811864544e05040c128218a05034a0b102c0082c040103101c24000d5880c0c1625042c03a190034824448102d210120854079203c45550070b036100d40404800300c40780c008040001c500c5181440d80301084070380c000110300000781e8614801000d2b0a100b0310b030302e0b000f036110054031001502400c20107125000c01e40c02400071082c11407122407454140c60300b40c0e074460301d030180a005807a804003c035425a5004c0c0d0311589192281142100141007a9218030094000c038200640b050b50484015812207000c1c00c2c0740380c0c0f5900c0300042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 136133723 1250 136132473 136132483
    0x51215040c05040b0f180a0f0905090a20040b15090406140906011d0a090c081503070909080f030a0b09091501050906010c0b0c09030f1c0503060a080a0f0c0602 70
    0x21401c00580170b014102d444200840105802c14031006030443d003130303010800f103280c2100341e8016040490f000741040c440c107203c510445500035015001801d101642d9119001642807006601c100e01c001103042c3d0318140c17100c2d006540d10316005002c46000b03801407001e010b150307004099024070031400c2030310000f0196800300f440105000001d01007403113a262840103441c0c10700d102c0a14614414501c5400d40daa86e41c1d00c0103031000b44442c0101040c0000d0401c4001c10241b0300429009001c203605400300d0b00303910005042000c1e100740010002e070b0542076061907503041c010f040c80e0009202002082141151054101c078000010a503010f00c0503444024000351252503100c0c0c0c00d02d1100302c01d40104003500d00009070381d07040b1406060080b000b203c142c46503000742c1c1003100d41c0841c4680028040b10382d800e0800000e00300d0001c810252407942c02200751096510f81c4003918608100d40400890b806941e110364610090842c4c07004c890001969240c1010305422041040d18021610240014941e0001c54 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 136134973 1250 136133723 136133729
    0xc12060c0f030712050408030f0105090f01030803151201060f0b12040b06040b0306070804030207120305090607170304050c01260a0905070504110c070605040510050a051215040c0504 80
    0x29645050030001c5055000940009005104100f00031140550400482c86590300403400340d00301d19030301d251241d0045079414060b40514000c40c1c0150802c016849070318103160550b503220704107960720f4860b800c0d1a14005000c801403640b051101200300880c44055000b0f80803282a041c0340301480717540700c2e1090118002c1602503103000114800090010b0174240c406980202c3c000d0001450446070408a40751000464040c0301041c2a02c0a0005064040000400a04d90f0f1142034103540388540e0014014003ca6205901603400402e00c881040b1580314120580c0e0381c049041c0c0d803640b41604240303945600c040c400354042080c4082e10308000c941100844400c164406540146440360354200d8002c003985001076482d80603c08002c1200d039030f42e000709010000040c50440e201c0d000300c542181000c0c1c5a901c0582444404c01042085da01c50027440b050b5402c075818015101c1d88208010303290740c415500300024005c004020807403c0e0750011624000c0f8034007990100003090840c0300c25607191040340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 136136223 1250 136134973 136134991
    0x913060b040b0c0105070302031e191406011d0a170a0203031c0501090209090c0304061506090302090604061a07150507120f09030806150f07030c0b101a030717010303020c1206 77
    0x500081c0311406407401d4000340b40000e0603019040880820bc00c54060b10651100510040c0c2400380560340f086642180c1c58101075450210790049000440b201010300c07440541e40c9510210304000201070101c61210b50b000b41c00c1d282e4405032910740701d0801c80001d4501c0c00c95071400e4000b01d100e403c00e200340c500b07511000c1d00c0b142083c0c440800400e02500010001c440503502d0fa0041287c078082c5000250040c2a1503d0320302515066104202031040e008003854060303494107030b0411032072180029613442d0243e603044850b65585e0b80d04203450f140441c0304047c008030f8184000d00080e43d0748014001e40c9000b00107001c100020750818404c0a4800e81c94000c2e0000d0034400c0443c0c400e2070606448001015080d82e0103180c41044644903070305030807484c01078002c07440311882c0c0010301882d0294558040130060000c0e214a061000e20040075515501203082a1001720010344258020807558030907100b00c6556400131342c1d49280080d510b4040680c0c850051402854916504200042d0745000394103034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 136137473 1250 136136223 136136251
    0xc0b04050114090f040e160e09100b0d0618031106090709150305060a051005150a081305010e0a02190609090c0309020a060e030606010e060913060b040b0c010507030203 74
    0x10942d40c40c5a070410221a0b44c0640300769000e2038141c1e00ca1088401d6224000b0143c000c1200074010b20000500726405050000f15000801c42512404102c00b000005001400600380d5080400f2442007160002300511951401c405440d032041e4480404c41d010340710341e50b990201d4412149281c0c4074003056408006a42c0100014403903030540750041c005509408070070380e480341e680e0b40340c680c601802640d0040c02241d649090283e0550b0035038040d00501401e440d16500c1c0e00f12100b100c0520b1058840e414101b00c150350202c1d050b07008019003c41210b420000a0003020342c0c80040544070000c1d10812481180e15801c1c0c15850480d00c80190b003143c485490f030700555403501840c40081c0000301c0c01ca41c201583c5445100040c0c0c0c0d900351101c05480e0943d504007075180c0c00c00505190820103040740341400000d01d10518661740c5c810442d0048407080d202c0060712403585910f0b80140145070004095040080b6000c11400d8102000c0d10715444100c0080c0200c1d12241e100341c040348010f440407403d80e10f40c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 136138723 1250 136137473 136137497
    0x103210e01020a141903081005040b03030a03020306130e010209180601090302010e12031902010c090b04050f03010e0f1605090112081803030301060306140a260307080c07030c0b040501 81
    0x3450548450704c0507100150392170a40154241844070410040480210314048240412003521045a4004d418252000c00c14070010600007130b0349004d29949501015000000141c042c4c45401100420ba603102c001031203c110f01c018002e02035002154041d000f05130762000740d10300307006c0211614010041a1101c4400d40c5c115001103c50701071500c4215000028180c400d48212020002090721903a0900005d002d0b40c08404000d080d02d202c0c000540c100506403805005400400d01210112142110001e00c108102030120f4054a0f000d0140015402001603451060001041e581d407600d003101d031209000c43d19076081020340d002c01c1c0546020403580c40e031030a00194440000300742c06804000e40030036065205000030315541c000d82001c00029126801000686c07200141d000b1804000c4400100150520040b001d00c100d0800c60021500100d0209070700b01d0000f80704850419803c24082030f91145c0241015595416602c01200c6c0003290300c00000d116802c05041c3d600b5203405a54900401701c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 136139973 1250 136138723 136138733
    0x2418090c0b0a0302070203061602060c25020102100501150e180a0c0c060603080904050108030a0806060a09030602040f050901060912021e030f010e0f01061226030103210e01020a 78
    0x10b00340380018154200098005a5420889a44240c035041d41086044625a0000382020800380c040345c00900d090120940354581035a0231703910000c081c02c114030480d0207800100d00c5c0a0090b40401000c500e418008547d198540c0c440540400c080d40790304001d550200305015112100c14801200030001401281d180700c0c076508400100c01d0145040f402580094a400e42214401d506c00c80c2c0c1400c00213000c030440d0815000b85030050030410040c0d803c1000c8034501078180da10081c07541c0d200d040d000520920590050341e880d030246412080c11501d4a40320308400c22040e900f401442d11070700d40c1c400006143d0344101d10100c03d889100c4020310303e01541c0c0d4203000981c40403403800d02c108242e1450381c250030b1f102040b141200185110000c604484c1070580d5508254211b0000701159040c00304c2070129909410606034540c0c0c3c00404c51881110f507640802100403080014038a04a00100010078004840000710180c01c000d1800410fa2044c0801a52420140198280980c2080c010840814 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 136141223 1250 136139973 136139977
    0x11409060706091e03030c030209010f08040303061e210201120207021f030203070906081e0c04090c1706010c0b060603040215030a09052503152418090c0b 68
    0xb4402c10000c50746241e5a61038011541a1211544644203483c0e0014107059150040603407010300360030110324000d0060002001322841c0d41510041c8084280401d003010312945c0031200510041c00070307040d80880c5641c00c0d0002002071084001d400e030800c00501e801a40e01220300e2a141c1e05031101b031804164801c0d0b00020b5002001d0580c0d2044110746c000b5404680c810340341c8a001c00b02c0e0380042c2d90703203042ca0002e0f06107401d54100408200c00c080400c0b0700d0790300001d0301107012121001d100758030781d560000481580c802d81d001140e120382005014200aa0001c0e000300407070120800410310781da1070308c0044a0507811413201400d41100d50000c20040e0070424010364010303002400e174464900400d007004440380d00c1551200303c09a503503c0400244031741030104101c54a8403922102c1c0052107020004c442c1a203a01002e092201d0900310303801c1001340c030360200900c0111001e08480202200302e500001580c28450381d16500000b014207400b04000e482131941c0c4c1c1b46e102c0340382000f2a00b0140024195 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 136142473 1250 136141223 136141237
    0x2004062012030c03010905130c180e0118210206040204020708090a0623040806040201050901180306061d04020109140d0b0f060a05030303151012090b060f01140906 72
    0xa0141c650a26036440c0e49100440c03044180c407500554a514001d05101103440c0141201011001c0303060b9040052030f5030f00c6110465006d04e041d0b024040380805484010420054690165031811420304204150b2201ea60b9403103000e10340c6540900c82c091402c4180c0042c00f090800140c002c4000140149007560241c49200c0c0200901d03424080c0140114210001a4110300007196000c4103180d91046102c0030b1050111811203000e040034a0318a81d15030320312001e0b0009040c0700020a00100e107900c10700c1c405001005074410700c02d0099403410408010241401194002c0e0510b41d0011b01a03424650202c1c020341d41a0340e00046107160030148800e840501141e1035010710f00c202e0250109645510381c44c000c0d990445989540c3c200b100800400c150b40382c0c810f038041c4c0c1081c81003000c10404152250f540450680d16440c80040e4280101c55081012031240e850381d1911110605100400da443c0344942c1c42641c04085810f50706005461200c05003161880e0090300300000c215506000024000ca = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 136143723 1250 136142473 136142537
    0x301120308040f050f0a120c0b15240306040c08040503070308250e31020d021603020f012007110607050a08030702010c080103120309051609200406 65
    0xd000c542c0d603926003800b045c8001c030072256108500070414400458021180303044c403401c18454404c1c480d07441d8480341d40700500301102d4000c4840c4d041d01c547c41d401c50329000b1309080017490303400083c030744614940c60b04180e482030f009510700141c84410300d0044d03420074066500f00c0c0085040503901d550071901258010801c1038407c03032020a500380d20410121310394540e1040c0d00d52524072000401404082c96204408000c5031030103041c01801000c2c010701000d4080c10480000d6901e000a100003806031003410041241ca5030404e0180c018154041158000c0f0010300d0024002d50f81c0300c0440c1401d000c1c1c444074200d0a61020000400024135020800041c1c2e103018010600300200c0c1c0c1c651504022140205440d4170900200700480940d0a1240f01850002401d100d400380d410f5031103481c200c8050303100c014280340d51981e01c00180f150070044410101c001c1c59005039620384400c00800a06541d1010051320064446121071001d54a801c1e40c01350386a1380d80d4000703111203c07910010304520444070152 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 136144973 1250 136143723 136143743
    0x206040b031905180f0705010801052107120203010f06031509170d020a11010c120207060f0e01020d0c0c0503070b0c0f030408030613090515071701080a0b060105030112030804 77
    0x100040b50003154801c0140c040b800b00120718825101e82481d06040120200340c105520501243e81c10400311070540794203440781410180301300c40807444519017a400c2c0c8124454000300040c03441a060084100a100390b0092001c0d07101e62031080295545804000d056014810303100044480e69401260b541d8000d012215510f40408010900c2d580f2201281d02c0c0c207500001c3d41480c0a03000030130b140b030f9949001d008001e845001c00f0002e2120300c5024041c902d030307500020a0014800d458100f81c1e21806c201c00200a1075070300e60704c4c4d14002d6008010300200355003000500203841d07000f0304401580903044400b8501c0c102055480b038018450081250000940a1001450b014544000785100d00e01c80d0342401d40d03d040071020401d40f420300c0042201058100b0280390f001403030101d01071a07000300e07042c1ca0780c900740c640480551300d0340003216070840d000004c0400040d03131500000e4807500490061007260300130f460b1030b001100c0f503100034020807160302403490f030b100d00103407080c0502d03035015001e070b00414 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 136146223 1250 136144973 136145011
    0x31407061b0e1002060a0504111009060801090204050d140304180e0601050906031b0609030f061b0f0f0702030c04050f0618150d02040605040c051201080304030206040b03 75
    0x300c21210002010703514070701c80854140e207040c1c018401c038600c0102202c0d40c0709003071a5018003c4d80d4000c000c050758015074503030003c0b0f400c01c10022003040c40e12230001c1c241ca2141c14444030003800c82800307100d540f0010f100703c6d0000031600340a00c02c441c00d4810141204800d032050362aa5050132601a448200d1844100000100c00d800800c2103600b0000484002c00d072030661601c2c0502e07045060f01300c94440c0140301c0034414160b90004001c2c007084c5030410010b000458503000a07151340100046103425010b000122041e184011902c0c9200b000c810507000d03260080154050a00c2c041c0d400f48900e07100c010000280c0451a1401402085100508540c1c880110b4070100b0140c80d02941e2000850b07042c0003c0c044203161801c402c0701c6000f64a02c40340f00720714001c0490703400310500083c0980111542c0710341000795111600104040d04001e04240210003070350748010035035446100c451422005250022035241b601000300c40c04c490b0020502e0b81443d00305000804a540054961002481249509 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 136147473 1250 136146223 136146233
    0x31220070807080f0738040c0803031306050c0a0207051905041d06060111100e07080303010b0a090602030403030c030302160609030302031905100b07050f030c0109020a12050a031407 80
    0x10b2981e04c81c50903400e521125607150005814808114003954210812581e1000f80f444110118070010068180041602c8509050090449582059507240000000c000407511500310070040144554800c00c01c5540317420f0b502e90705000d00ca5a200c0103802030001002189008003283c2d02e605031980c41c240480e070342d810014007204c9a221030a8904400000820960403061000540c094005c0c20103480c40ca50b034848894031807045c03254050100d5510382082c03007807900402070080176000c0b61080386d40d25610f400785518a03411841220001070034204000c5480703440031080d20304503a49600c1e425030b0780d2500c0c2e8080d0040d4020700040340051103091303000c03008584180125403045010341c4005a1368100720000c4049440c58003129031000d403c0c003082c4095a00d00c440d0240840700c4203028152901100c0c0f5210f82001c511501e079a0300d81c03201280b9070780740d2441075104081152003103511548290f80d550301c1c9004035052510243c00742c0c121003680e101007030150608030010f2207200501c030700c0d25440e036a030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 136148723 1250 136147473 136147477
    0x5070e0a0f29150d021602120a080f0f0c010c0c0203010b040605030c090a0b030708010516030614150c0f100f02070503160201090302090f0403122007080708 69
    0x200241280c071040003858020075803240301042c24007007000c2404114039503030030000890244a1140503441d403008030090309940d00309403014840c903c2800d40d42d8210624481c1e049a0341100180e101d00380144800030304040004848880541c40003501d410301042e103400c0c51507508501208244010208484501d510084c0306181d0396041c2a1915828130145005140c00c541a403620f0078083d601c2c200d400e100d41e913400a40107550490840b0306401e0341d5100a0420060106507a4280c1c00d1b01c903a000104010b1410340207684540c03210365070b0f60542c0710b403010304400b9a0040d110741e642c00351344c400741d0845038100f90450391403c3c1a01c28007030b89400042d0800e00c1c0341090b804070414968214071040d6910300340d82e000343c10034441c0303c0c0d0742135040c6951601c3e102d890313100c1c2440c242103030549010700c203045900440c19400159001000f0342c0c2c042c40c1000f8013410041c0e007150103c000403d40d180400211000744611650102000a00d26a01b000948010303041d900042064484201c2803040400081d41c80700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 136149973 1250 136148723 136148731
    0x50603070510050a110303070c02040e1617010506010201020f0301210b07090e01120c180f060308031510021902040213140a06080108060408030a0b0904080a12060506031305070e 78
    0xa00c540e600c0113600f030003c0c9210440d075009185a0410001c0c40354284d8000103004a5079012580040c2640c04801200e192103840e490340801c10b032081100164174003103950259044041c0c04001c0c0016031750107004a0807072059035007110804000707100600c590381000000559180c603040740381d08100110348826040c0034013220014006040c0c40410301000505208150041501c4a110340d0100210b903a40e94812400b8004d40356803d48144503610142c507240c20442500c00156810001c0c0e58030303801c20050315030040300d1059821032007416a50241c1844000e0300e60b64901342c0d0241c00541e20301d0400000c2201c186400340d90003a000c0c003d00004505100d9890300a004480e80190314074031110601010f5609a40124207001c41100108440e140205001c0d51080d0b000c1ca4050b6603646001e82c0c0c000408004002c41c4c0c100070010100820052444020101840c09844e15054803d00d20074920a0311002e0207110340220050020a490b00074010f0b40d6040c2c0c41c030820903a80d1490b1900d46070003c0f280c0840d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 136151079 1106 136149973 136149977
    0x522020a09170d030507050903060c0901050c06091c050c030307030902060d0c0906031104050f090907051203070b0106080106020a030c02010516030509090127050603070510 76
    0x4005400034010303400300702101200340403202d82e0707031803103c40400c01213441c01011400c004c2c01081a51400440180100a140c0d40d401100300550091860141481024001008075200c14001284030303040781c030000e0054824803100442010f44590380311082c030104010144222401004a86c4c0c032680038140890454a01c0c0302041c00f0b0b01c20201d48440440ca055138507280584e101c2184c0c0215912542c0501142e90b82c90aa800541704a20540350720040354004d4040a040881c5070950007200a800e8030f2030b0680d0341c4003046012030780110441d40c2c0d4200159510402c2403040308140908820729080c0f0740d035814410040d40d280c003003140240c28001c604000c4011684240304803031810090910402c40b04120f464040c009810400d0014455828100049010340020b240510410b290600d001c1d0031002c0d0028160007040701411403905400f405001240c3c0c1d8542604c2c8105042c200c0d = true := by decide +kernel

theorem cover : BRFrame.Cov 135971223 136151079 := by
  have h0 := BRFrame.cov_init 135971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 135971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 135971223 ≤ n) (h2 : n < 136151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
