-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1201
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:44:14.033329+00:00
-- url     : https://prove2.me/submissions/54dd3073-a289-4fce-8879-c4cc68e0e0b7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 215827338 ≤ n < 216007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 215828588 1250 215827338 215827357
    0xc0c0708071508010e0723030a0c030501050402130501050f0c0d051903060e0c070302030403020603070e101103030610180603020a030e0601210c0306090f060605040b01090905100308 80
    0x12021091000070307004916003110140500c3c00c0e9086516056082046000140c0044c2c20031000018804403038000c4200508650511a2404da40345040100b0b10001c01c50350f00c0e000c0c002414003000103040e180500954070100d500e8070021507002d00c0d1000544541e031181540001c0800141319076506598140038407020001a922100d580c1c5100c60b500070b031026039081e0040181440e1601c103000985900340c0303407a0b2100115148582e650001e00781a0b245000b560b00c020740c440070001c1000306156000c0d155060002c07050302c140103401071183c070030b80380e0024031101214958024400280f0a2074000c1840c42c95401c0c46c10040e500843e040403011081c502030704020b000c40d80011303a0804580d40b601c00c0002c031003031020103442c1035410545043c00b590045000c0d081e08101600b405800c1c043c5200131200155803001082103c5a458508070a0324148101c041d40c08914000340000c0700e09003801050106401650b8840056003404000001048003401c0420501c0510740e0100018040348001c0c003000c030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 215829838 1250 215828588 215828593
    0x10e040c03080301080706030b03012a020304180902030d0512070804060609180519020d020603040c0b1b070609030b161b030305040b0105060a0f0f0201091a07180b090105030c0c0708 80
    0x10b047c010042c0a0750880030011307000380c0c50300307201207603034044d045808c80ba02903548106007000305c00c0034080f480e50040d5004420300d44461034802c0880e544590054404910960a41d00d80701c036a58416074035806100c3c610740400303885200103a4000e100d2000300d50700900c6200005407075a02c9180c03c10449100181c4c0558000c4400141410b1180c1088010300c3c40c00040d01c0003001010035030215a10a40f070b070500a00900c00400031030200654925004081c01c01d1409864176080180480c0444184d13041c055102c501580d00c01280092003510f0110541c1d802030404c100c2e5403500d44903506400f00c224a100100720800782d1081050041d0301240d05440c3c001e82e0b000c1100c0c1441d0071f260714490b9042c0d00a5224040400000c0c01a03504001008880259410000c00400c52808181c1c09803108600041903800403c1500c01c11031182d03e0031500031a4103640d1611503550380c0c4034000407103041d4042d41c01c0c010b8092151201e150f10030802968401c25103103e80b0704084590700f115140082a4121040d940c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 215831088 1250 215829838 215829853
    0x303090c1e0b091302030c0403020414100b031b070c0302100e0414040203060c0307020f15190504030504051201090804150219030801150e090a0203090705030a0209010e040c0308030108 81
    0x5a04400c00100a803040203500b9107480f0200b80000d4480d030080c005000e1842d0040002141d0030904011b0740c0055401800c24804000c01c100c080d910548200c0c0c90090350301c0c1c890320208000c4102401e59120700315425490105094080001495400c01202269648400700c400b00040e160051122440c0ca00c544031011811208410001959100601d43c00540d29110400c0f0161b81c00180072a00010a490255641d0310b5400049003007072407a4480d072210b842840c00f103440c05044250498402c11070020010700070460b505480084d10070550b80900043c0c001e110502003450420710543c5006244000016048010b940711410ba0708076912418000714132043d403007134450b014401142440c1054040483d04c41e501d40e00030307081c038106014200e820f50400e000c40c9180c07401200048100d840040c110891032400e805464040d5008488a83d100e0080c481e0025a81c100060b0300c034211a4001d1680e41107a003031500c000380f5020b0080c4144ca0003082d0800000c041524140110301030041c150240510 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 215832338 1250 215831088 215831129
    0x9180c0d110306040e0f0a030302070f050d050315010e090703150915030203070807061d01050d05040507150216210210030218060c030904050c0c01020a21270303090c 73
    0x1250084140c66081e80c12032021011050001f04a5100d00ca500d818010f817100701a050909484440007001001c52280014000000350400041c52140b0381640020582c4845000112909280d108510360401c0d0703484080f030604e5000f41c10013018206000f801c90500396032403046a094031140b441804c44000c1040d0140290b04050042801900da494000d12001e8504200140029034003203020100c261101c001c038041e0382c811000c41d04c181c4444907080c8a41d0401c0d09100b515444d9070b109120104011055031a00c0c50300200703000b0268500088900c001074609241c80760b502c140d101501002041907e810001a07484e038008030000c40c0350780da0050303c40f50010f1700c4070592419241c08038852030b0240b0004160080003c115080e101c401e032000326141e10384100c1081c80717000d104a40c03a40e6500120b40703c14056401100354110002040504990b1019110100c00b281c12034002190021061500c20203c03608140100000f0361180c60300184002c4036444000000c405500103a880c600e4003001c2c80d40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 215833588 1250 215832338 215832341
    0xe21060705030c030705090409120314010801060513050603010b060c0a050607020307120302090a09050a14060907090302011809060f0503160608130212030f0c100209180c0d11030604 80
    0x90129160822514506100850383e034036000080c291010803d0008202040d6105c50300075510315507104514034408059030801901074510512909070390f49108000007100d50050044004a60f000703002008102d05500200b0080c00005040c41d41540d2180d21001070340d1030b508020001f040000d4003511401000e890f2050506602400b060110b610030f00000c0c020915801145c050b114041c01c0c01a65540c0b0070000c51403005060340410705161810b400c03c41854010307000307810b5140d4030015080c250340d110001c01c1718405090342c40744006403c22405100650050510b004000c1140c07001d10316580d0780740700324000e48d441c0380c0000600c611103200400c401c2c00d040062001c0350114032a600b044a0074400000c2c548400248001d0300e10310401c4071201507448051403060b080c40c4000580b542e4018844000c80f40754014440c0c102144100f4a203004181c480303209940044a004140100000700c03200f4495800e4000340440ca00d041040040780c0b0b1603417640c03140304c591010050b000c2d42c480ca0b18404010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 215834838 1250 215833588 215833591
    0x6030e150906071805011407031209030e0a050a0e06151603090f05030c03061f0317030603160810020702010e04020d050114150316020703120305150a08100b010e2106 73
    0x240744d004400e07050041e17a812400075501000322070549501c42415040803500d0b9101080c0c00c2c00128940318440f0103050348142c10172400c02c02a142454840e13a01c41c140981c001c0c1e10721556859001980200d0b25900e4000d0ba2000081441500d10341031182c12a5840041442001c0c201e01003140c0001c1002140341c6210103c00821080300640a05021040802c0d00c030000104404d0014660f0344110860314007485240020b1034009542d510303110b100c4142d403201d0703a20a0325454481e2040d20504015450880e5010b005e41d00d010000d0318103005409503d101035000010220f06100b400707107002c90561298800742090340344859010665514205045400f45014201e45000d45d240300c802401917909081103030707004003503c0710240c200c0c1c010b210100d09000090b080282100243c1a10940311035154201e94040c4242003038054001d040319007000503c140a218040440e04003140002d0703581c0190307000301c501c0c00040c18040c51286c040c4000840041007026859407580c020705408807006c1c0e00f044a80d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 215836088 1250 215834838 215834867
    0x90703050109061a09010f030e1002040e010807080a030530040201030e12070308090304050411040806010b040f060503180304060f08060f0a0512070b0307120b180106030e15090607 79
    0x900129454814554415098186d05100e40b91840301d105c14880d50000c00811000d8055030212848000408040c0d849441102400c07030f000400822404408280e0500320740c00b00000300710160315590305072000d800c8140b40c0c05020030344025200c85031802c801d4071030b0801040d20038400f040c41d09200150442d41c8030320a032141075024204100e03a0981030400c440c0002e815090000c1c1d40d64a08116510794812608000e4100e070402109030b0701016800d000c0c0c030644003070300103480b81c0d0381e2900c250200a001c0d80c45409000c2d42c020300c3c2044400d00542c02142c200700c2074200003240400d00150a40745034420703070003080000c5044141031612030f809000d03260464070440b0418100850700300014030704040b0f0702039244103001c61000403088640030000c8800915110200948915184a002c1c01140620783c5c04032000d03040a0f200e08042c0390169604150035020048568181d0801208400400d515043d0010314411190910101105a9280da00c80c141e40700042c034051a04c2140100a501c0c0003104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 215837338 1250 215836088 215836109
    0x110f06040b060d02060903120403300e040902030703120221030408031e150a090509100e01060e041511070c03060c050d0e160b0a021c0e09070305010906 67
    0x80c4000240c00503601078100d00d0455800d0410081800002c4035440390340202589840381a1615110148a002400840340591214802c280341c607400644c4501c402c1e07000c00803407600001403d1880b40200030543d0390041c00b42c000100ca13041c2e50b01003031a1444d190010f4a6000c2c00c00041080c469040282c1d45075544144109000240845d00410482c0030142009001c1c45000c0b0009000f10039284100b41241800c4030f0b400d20b10706004282011807030500c0401801095001004508560745004d01c501400800008100f000b50302c1036110300400511007075000b207548480b0001640b6180180450050b401000c2d0410040b5004c03103003108968403400000c002039001d001800100e0180140c00045035000b80001c1103124a501003100d007881065030b103444c00d0b41f804480390001d64001505c0c0504401c510341c000812500c8a2001c08a80100c0c01d1023801030740106088030244807035401412004503681009034030048000e0002d04010011100305c0c4c0040e0340c480040010704000d004140081603255034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 215838588 1250 215837338 215837341
    0x60f06060c060203040204022215050705151801020c0c090702070317180901061115162102120a150b090d020a090e03070c08060c030105011419110f06 66
    0x2405049111621405402c2c00c1e8084002030940d141c61b011034590b140c1e54826803400c1c07001600d0b0102031a080b40a03911b456000040c85041c01c3e0700402c1243c014540040040035200e0101c1144003d10708000c082e180300740d0700c0d10011180010300340041e052001c00328000d8000011a8030612600d0000109501c0c21540281010804200b00c012191070410848800c1742d9101800100d1000409444200c06d07000795880f0000030301c827940910043c8540fa24a420f540740542004459a2101c034181c03480750041c00700003100300906000301401e241c150546811002e040354040841c0007240c01c0130501c0340c00241c00108001d54200240b24104803081803c54102c03181c1e0911145003202d010781d640003401121824004420756580c036040100030003040f24188030021840c210617859130020300741151011703501e040105003040f0210340548103021078200c1d00c0c1140c1ca41401110060f074120725500b00c0c400d04021840c0c0c4402407040358108034000d07842e100440c0c003103c1d240c180340c01c0c20341c7c22a5005401200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 215839838 1250 215838588 215838599
    0xd030f0b0a1238060910030c05010507050109020a0e01030510050103120503070507050105092d060402011b1b0f170717010204090207110a061d060313051504060f06 72
    0x10b10003104980000ca030920304100d16004480f80225410503010080c100224482800c0d404030071603105010a07504441c06440d60030920005007281d002c01001d05842c7d0701c0500c00d651144002d04003ca008400103c1c4039080c1c1d40101d1194201c9e0780200040c20040401030060100400400300000c0c03981d002080503614544910b40303109901c4042c417080050001c08200b00c1445103054824841d0030000130400390614682c040e5440c0c109a0420700707041030080400c3c041030080b0210205154603075029013a41d951301d40c01156480301c40c1c0d41d03d6241e00c1039814110301054a41d40b0907400003004860b01548141062142c502c924110740c00540c440e5010b1007040390400c8086101c0d400c941c41032051842c9034084c40c04490181c0666040300403c1403001c076036001400751925010181c0301041c4d9052071090344521040f60b00c0201c83c40001c0e03150094110f110a80d00348403009540c0305804120300074000d44d2550351a070070000303c0855040c41c191102e052200b800b00318070503003d4a039081201088072506d4039 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 215841088 1250 215839838 215839859
    0xf030807020d0912030c0204050a200403021c06090f06020a021006080a020f04061a27030601181103090c1f0e011215031a010b0f040b0a030605030d030f0b0a 69
    0x103004404d000d02c01008400308150049082c2d404c10780e401402400a4502010040000c2841182405032514a4400315440501920456007a00d4001e40341c0451100c0ca1000400d5044a000c81110311036075078007038040807950145202c843c0c7c501c691005680c0c0c0318602c1c0000d10301507018070440d6500d03240450400c2441000111200642c0c0e0580b140502601c1c8500014010304c5994001c1080c00e014016214038404060001d208a904010303501080303000e100c100c0b60401301d1605510341c055200718018813640300d8000000c0300c010003072000070820030003250710601ea0340c00c1500c03070341c3c0365600900d00082c007072900701c0b1003a0801c6001c2044110031180ba02009003aa048141c085043c00700d9180007180808140c0c00100c0503d901c0c0c802c500c1256603d1528800c080e1040142d01ca698000c00004121b8901c00011a056a0700b848a403170705081c1803005450704d55014013010340925950b0940040c441d01c060003030310010141d6440014206040010308000d643c001206944a08455201030082074100b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 215842338 1250 215841088 215841107
    0xf0d0806040501270f1d15101a07060938162c0307080c0105090f0f0406470318030f03040c060c02010e090606160f030807020d 56
    0x7a0f01c00080032003081044c0d4000f010b04584001800c2c2c281898045c030b03801c04038002c84012070140210754090010203410461000c090f68940b261002c1120100262500c400b02c0400e000e42d085091441c7c5081c0740d56a904a40d205401191485241d001d283c5101c00071814241044c2d050105c41c500300c1c2d80702d41d07071400450030080440c0b40f5004049002e520442c49415001c0d15580700565054030206945010288284030b58100c6100b881174210101c0c0300000491000380800060719954240058441000488420070507100e4001008a61072001c030b6665008000040440307002d0f100081c2e026145c0010302800450490030032011000441c1110003035003001c5807800d003540b00e036140c481d1216400070100601c0340d4600603440c80b020805404400701c0100450280740304500e1008003650300ea20a856810907820040d000c568684121902030810403400c1d68400300041c419480c0c604008081703c55813141200039551541c1d200100170406800c600c1e0241c0140450008104001c0c1c88400280103014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 215843588 1250 215842338 215842379
    0x726190213032a0306020408011d0706050307050c010f0b0f0a0501140f07081908060d050a03030509030c0d210605060f1602060a020a020103150b0406050f07050f0d0806040501 77
    0x1110b41d00c030481149030003021410f00704a411030080c01d903507410a1400b1f90010f000307108603946001024810b8000c502d0307450701440c08100280417218036180040d1070035000104104144901006882c402030030030300ca0356001c000d96040006826442c5002d001007403103030307942d40d0303002e24a9003009110b20383e040550341d0102c0c0480000c46503114a0084107603014001d001006215010120300580488142cbe4101c4180295640d0342180517501c245c02c006001c082e82002030825001a00d000700440d00ca40c001a500c0095501180d05d8034030b08640e41841d01d0304620f9581c0c002801d00705039407680c481d1a007500d0764403041c4507410703c21181007400145039803041c83d00442c507a40d000100c00380c510741c00d4003075400c4540c0c00529443d2503032903440e40a91100ca000608038000382ca4502c0003150301ea00b1803001c6c0c0650b42c17011001c5c0e041a05200b8150f030a540604410404950148400c10020f80100b002e03c00310380c4110080c04004003140c00c05411070340003414991007282000c0051000b6410b200302c00c1c59041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 215844838 1250 215843588 215843603
    0x10c120506060405090f0117010209010c060b030c120f01140903030105130b04020d06030b1008061815010b071a1905060103090209010801061d0c0a08072619021303 72
    0x48a001c00951144115071216400840803810001c00c850f101c01154122000200300d4205206124410f5080b0300c43c00021601184402308110f001c0749aa500c00e1a1184018085900c1e2080d80c0001850104c1480f20710301d40f030f5201251944240d2401e01864109115110102c6624248082004e4890105008003409105c820301402020b003419000b443c0b05000c017a0086540c0c10804200002600c564003083d228025201c000c60708100e10b4006000440380c228001c1c204c582c6502040803100c9044a2008019103d0600490144107580001e81c2c001c10f800c9400680d180a58549000b52102040c03120f03c104401404100544d411985452202d00f44a000010590f49100041e801400700c00740c003a401c581c4420012580001c15403129044c0c9181c0854010b448480a144021992049945c03d0400c5014403883d90254007880c6070542107130070790405e0499080265002e0b0704034952120ac40b03d900d800340d0144082c2440303030310391031007000d141500945c03501048884ca04241c9049200042c800d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 215846088 1250 215844838 215844841
    0x9050d0e0303070c06090f050117071d03030309030309011d030301060309080d0504060f2702190308030405160e040302031905040b1201080d030e060a0f2a08010503010c1205 76
    0xc0c1e40a104403a02654000c2016400c141c507104028a0282d2901901c03401d010303903032400b203080d41c00390025901407441210070103072580e10740c503040b12005441c1e2044110b4a0741d00342c030780509903004d1000d503110784c91803401503071285000c65145096840303103122800d0201400103043e084d8180070080f40c2c15180e5a060205542c074841c60020410300c6441040d007111841d1000380000c0201d140c00c09011031060b00001d000303982c0f6501c0ca281886804c140c1700031822000880c03110060800c1038840030318138410019029429565211946070750b1080350304031480c0e009043c0106007040b15800381c402600c1e11040d0b48046280c540e07000b03590303403003044101c0259003002c00303840282030700c50421900501041400961240340744800038a40300428040d107040d03402142082d4070003500c01d100300e089040c6000b00514942c0c940d4a4110020100d0445902805031200b0011040d40a48400c6904145101c4000c0240302c0541c0002800d55606030050b61090f41004554848207a0205800c0300344900303180d0000741c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 215847338 1250 215846088 215846117
    0x6061b0312011502060a06140118080717060c1602131b09030c0806071e03091b050f1806011809090302060106020d1403010905040204021b0601050f0409050d 69
    0x850103107095100c4080e564100201d04003071280700380300c4030349a42c2d02100c5641d10350070400b41c01d455081c014141d0134001104071071680d41c40390000150401200e50005850390304c039800d180c02d00315507410911628510018035081541c0402c003442d40b15141e0007a250a14907640d41e00c41d020b511007840644190011030514408010720f40c419410303004d141540c04c002400e10301000d40f90f00c01178030044e6402070803040006018030b400f00702603120302c1c0e03243d0355070300d4240890200c0d071000300a4954032000c00d540c6120810028552489150401940f00c25109402d49413608101c403084060b006280216881402e4007080104408880e800c0b85090030900c0d100c181c0400214484061540540d201c2400c000b01182415008601103043e0f408941c213030350a05450800549000e118003034404004602040100551500380e0b03c0250014401440949020300c0d101741c3d240b80b82804210b501013900311030010880342c54400c1e241c81d60f08c082600e0900086110b07880701c0ba2651020808081070081c2050701604 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 215848588 1250 215847338 215847343
    0xa0509010209030a03200601030503030609071403090102120604020702150f2503020105181b04090212010b0102071d0a0504030c0c08070312080c19110a060f110306061b 74
    0x4521006004c03030300d08900034240248441003101c201d903602003c54103030512054010a00c00e060f01d400000852540d1201310510061810007401c100400035403000d804403640994000b14060f8000074009611241c08622100034407001401c8503114600c10001c40c001030300d80d03528000300e1f8048204000e4980c640b1a680241134410410080080380e440064401580c40a001d1b11564034040e40c004c00156941000c0c042c4200034580161b03615600c4024074004100383c51781030405200740070f403000c200322126601240105240000c0e2514a9458102110071942d0412131383e0000c151000c620704100180d914032150102014060000e02c0b0b858400080a050180051ba801903900c00c8004102c04d9444070a41d448628a000c102c2d90310300444000c0e0f0520b8881d9000f18001c8100b0100e051410340b180e10354100400484a202050001911000598110a1200e4000340340503620205501901d01c2d20f05044030164202108a41c10030320a00c80c940d01d880090f140f07080c00701c80c49a9482d1810304100780c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 215849838 1250 215848588 215848597
    0x40309051021112a0106090204080604080d1401080a051b010903020609040209090108030304060612020616030c0b0115110d080705031e010303120c0c021c060e100615020303040b0a05090102 83
    0x104854408241c45045a109504200c404d0800300002c02c40f80780c07075412081c1a031046119108090f0300c480080307070125954000401e003c402c032000011f8089481103404458010136400701359980c200c0c40560040c08400e010141d070741c4010103180b41c080020100083c016804600020307005007008522018591111341c11107400c02c0c4010580161503944544560752603208a50440707400e0300b0008002003c0860000b5a021582c1c01400c0b503050400381d450600210880280035010800f1000d400c001150380025411f02070880d4104d01c04407480310304400381125401400f0f01c2c00c0d59005c1c642840300145c0c0031008035040001450000d40e4dd85861483c030900c07003e82640c000046801c00000401c064018a1410303800f0050501800a080d00d88802e40e5520740303001c0042e401c03040040042002c10014041105964412003000030b8001c004284146080000020707400280c0c0c0d1440240021a180d5004d05c5107001c80d81b00640c5503140c00d0b60b9603c0c94000c0645070304801501c42001c59800c03002901941c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 215851088 1250 215849838 215849857
    0x7031e12180603111303060c1b0b06040c030207200102070806060a091e0c020a1109090a02040e01090804030c0501090806010303050909070c05031314030316021002070e04030905102111 81
    0xc0c03849600e87c03c03c05c0080400009007400300d40740142020a10a00048050442d03401800d25880e55807403c061001800300002000f003010b50802114000400711040c116102c00700b48c1c5007a40c010806000039103019001d4001695a0b4052402c02107280d0b2307458810825240300000203d6189220548142001b56035008544403a0030506904400d690014210142d1801070919101604070601400107894094034001c0260b003000500c1070241c02c06822104801c04070400001e030f0211151a000c469401a400403110046241e108000070341e4000c40c03500182c14900d001d4030555245daa405015480b410320680c4c0110b414100103450103000e0010079848a40040550341d0b100c8030009032140200345030017400c1100c4040c16a0300460305000003924003078400c14851085501041e0200200c504020f02d24404510540b4000704000c11840f40b094007840c420b440304400b003803c0200b0400c1407082e6550540c20008102e0340c0d681320301c0e004040001010120a00029010550009520944151b00c000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 215852338 1250 215851088 215851117
    0x30209033712030b22151205030904051e0a1503020a080d09090605010c060b0406090e030c0c0303180108071e050408192307031e1218060311 62
    0x75414014a61a0350448960070381e0200320700d40c03141c0c04201188280e030905481804129100c01c1c030b20b1003598008400c54170810034948400b652024441d1121075000c0b4122a1504041404101e81c05c00780035094024500c050849040c1240844200c0701c3d12008110344060754a60340025103c90f02c10308ca240207980c02078400c43c100e40d00c84036415038880e034000800c1c0006200c600c0009080080d4400c0c502556030582d204c00300d003202034032104054020046050350150b0b40307500006480f2240e21480c000740020f6009540c503010740c2a80340d42030503000c00045000e500104201c41a40030380f817583c01c801c0c020034205510203480b005000c0f1001e8440302c09000c1941003850b0b0300d00c2800e8000015204445540e800c0781c001d284040c3c4084405d200490005100d880300015035030300d051030400c1107c0060381c1b18044445665a03511420022030382400c05180c0f01243c3c03006a0709000640d04018889521402c12220044680409241c80c040e1442800101039990200c003103400e000c8001c903078811108130396 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 215853588 1250 215852338 215852443
    0x605030c0a09080607030b0102150c1e13030b041b08070303210504060b12012901021906020d05010504150b030a1503050606100f02060408071e0f1203020903 69
    0x140038000340028410b188c0503100705a100070f95403000305045031081c44840c45075401c1128000403485480400d0501c651b60500c00d00c41c144601c00d03030203842401075010f2180100c160a1508011090583c52084200702481982c02484901c0000440c507080780c0d494a48140f07060111000304203491352100b41070513414107000038003050107442d81192030034010458201e80e011072022482800c03504542031010066264407940381007140090340d2050b8005060050314044c3d2510206000c6030840b108085541c544e004c1680c09503000e00340300705400b50805070b50030800410001844042c004542c400c0c814444800000281e0125541d080f141486a0003461003018584a00d0025117541040380c010740601103041070310a8003446003040c4000001c82e9006050075132100d03182d07039807141e0101c2001e86e061800c01c0e100040315060f41e0704511b40700b401612100940c4030b0074a0316802f50707404c55207405e04050040c4034080284c2c1d4013181907c844c1901e805d0041d51410300b09046880700880504003950700c400500b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 215854838 1250 215853588 215853601
    0x71712090c010201060501050c0703060e071d0708060609011e09090204061119020d1205040b0f0a02010606110c060c100c0507030905040912030504050708030c030d0f02040605030c0a090806 83
    0x2010607807118260020700000e40c031000111024001c90151001c285e000440c01c00c08105d040c2d0141410500b8007003602c6e00f40d515000c0828424002c030000c0d00b4170001030070411031031980c061440d40d00840304980396403400c150440001d184100450030607803440c100d8450410b800d4001c10345440208484917040d5142c60351500003500d07094480d91a1011409240d4500301000c03810340e0b00c0074295500070070304420b580b00c0fa00c900010003441e001d00c40c1070007401c110100e14009514064056141140855562030b0087c840082c29035189074002401d106400c00c2e403410b8103101152000c0c0547d0280d500c41d48900e079a40c4a145040200c0707088140032403a14446804042e40280203000b6140a6115604d505945009100458101d181d01030680c07164080303100000d0f0300ca5007101d60094004d41c00c43e0410b0f9143d01240c0d0541d0b210340054449507000150401481215009020a00da001501182450b260000180c0a03100c0103000a042707800c00905214070a01a0b1005d801070301c080e2046841030725040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 215856088 1250 215854838 215854843
    0x21c1d210106050406082107081303020f0d08030703021e0412020909070b0306010c020d0501051f060806060405060a090801020409050f060303030402010c030f0309020d0501140105010504080307171209 88
    0x10400c11060350070041e02041c03600303060165804550703200c0011700c02d40c004c054580002400b00190244455010400c240225510b080a00301c40c508002546880c145580304101d11a1030000c0a030380100d20200506011030b5003001581e5207c04541009a92a1094080f40c00e03600041e40756240400070200d40484c3c1c0b592500c15010303169200f0764a0404e01e80703c3d25800b07503072283c903840b5000c6031401c1007001030341951181e200c0040c081d1019222003444030306c40c0c0c0c0b140d00f515000c4a4060458441110300c51800c80d03a000000024641e81c200781c2c00c00d0030254041000361185010301c40c0518130008034581010303c01c2e004440242004030086442d07d4a886070100540020b03100140c0890f880000f003451417501100301c0c0e0199505845422001700b0560381a5104240316080c0400d155850100d8070145e00e40d00c0d0561030030751003000006403215a07401c02c2030400c032060300003504010081c001440282030000c121a24103030001800c08110410145046184c802c4150b002d101d20a41780c107002d25910f00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 215857338 1250 215856088 215856139
    0x6020301090501080a05060a0c0e09040506041b05090c070f0b09011e0b060909090f07030605181c030e030d060914010501080c12090a0615090507021c1d 67
    0x3071220911a07640d807200c590399034048001e000762880e00080082038014065600c140d00440d03260034181c880c0500c079400910b003110f0454080d02c641c1c0010b0200020010100c1c00050801200782c44200000d00b2700020450004000708200504c100008240c0b080c0310750310506000c0f01e5440001c08640380340404c00540604a120702040ca1462a650b01e02200222070080a900c5503018110a05042030903081180b90710b0064070f5203446000e40d04003411441800d21418019501800001c2000e0400600f10180b0000c6c0b234102c90340940000b005000d219a55212048080c400ca15010030701001d040e0490f419441411050382c21a440d107140040c2c541d0242d08460f941e040481c07901c0002d41c1c9d070350005644001084503402c00c6103800300003c20f440703070b0010003103904a039030802101c03005411680da0400700c0b0035000015490301800e5801304a048820300070a54000314500c0035002126901001401310700202d5000414006004c0c09610400301c030040388107001d04010081c0e00c04901420380e90041440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 215858588 1250 215857338 215857349
    0x406030c140c0a02041d010e0a03020d0503041101080615030112030905030d0c080a1b0b09011407020c010f0309201005070203030a030b010e0a0902030108120c0a02061c090602040914040b0f060f0a0306020301 91
    0xc00c0b096410837030045081d24495500301c552200104154001121001cac0e004000300e9100307070749140741d00000b0021000746000e0316020040c28103958050601030a00581684454840d030300c02c0703005940956110540c1d500e215400b151968545041c0c0c0c00c01d5070341c48001c1c0e4405611141c51081030040c4101c4130307034172400b0b42300140007041026560078120102c25003c80d00b9a026902541451000c0e51007803401c0f64506003580f0f000104151079540e00380d18160f400721002000d00c0202401c40d01850181c00c00e003070259050500601d04649507000c640c49001d03508903441810f50742d8820a290303034020410041c4003c4003e003408101030311604040020b420a00a0300441e1150401d211030384065070302211030400051004040c007000a5003046640d034000e80c44035072428414485041000b0480c0580000c007840b400d005030301c036410200c2d40c0c030441d00340404030480034051409200c007041d210410f554022038010b0324603840350b45070b80c007003010540b00174849074106002c1c4000006010441e40954161075 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 215859838 1250 215858588 215858593
    0x90c031b0e0708070c02060a020a0c09050702160e01030f0c1d0a0b030c0114130b131401050703201e03030f13020a06230406030c140c0a02041d010e0a0302 68
    0x211075800072543c3d60000c9805030701180f465000c640151501801505a4020900c110340c0b9031041139680c2c4071404415404000c00c1900e40c021b02404503010301c00407491000140d10006000c1c43c06070702d104900c006100240c40001143c0350b54080c0200c84120301c1c05859144040110110840c00c1200f003400101d44540000e4544040e0510701d140118043e0040e1505035504103a42404500c15035580c0c0c030010b8000705030f00011500054804004010700a08940b18900c2c2c003000e481d1503504a440f8441c041e403681000410490300300001c0d00482d49507040f11603607808220922403241c6051428242111042c203c0c044041c001146c8600003000b54445c0381362a00c00380c0240c851488540c0000c0c891640290302440352a01400b101d0b203e007805401e03961100c3d440310200391340702d01140c0d081d40c07041c1c02110000c0c1d00c596500001c560800080381031a203145241d03e2602010034040d907228152036000a22541c3c407000c1d18558901580a8600800c134014020410b00c0d03a03c482c0550360740b081e4403040f005030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 215861088 1250 215859838 215859841
    0x6041404060b0f040b0d091a100602060f0a0b03070509010f03140601060e130b060403141e100e030f03010b040e07030b030303070309030c050615040f020418090c031b0e 74
    0x114107807030540320920b000021407410a410007008544070b806c6113050302c032042c6c0d548810001280c0132042c04120031000400d616810b080802c0d5150414450790000c00c2554400028010080170300c1903059444a0000c1c0b0000d00c90541100180c20606107038030499024006000110b109603081d00d0040813644940a003405000d11400444c0e11380a0900c40d00c000b04403200003854180c00c00f4240c0d5000204c401400060540710300000640c9500141c10a41d041c0c126000901a044001c00071030f1490002950961725060f280481166110003450038a0b0206440b4000307090034040c200309407800d079041c62640c90744030f40e190010b01809803c13520030400702d00038030030115103210700070f00c01d40095034000b6010390324590b58140141c000e0100b8074070403020401041420004204240a83c90249c0061700660350841e1506041000b607880ba09010f00d84107104010030001444480322280d01602c150070040b400040f1b40c141903034644000d62000c4e00e01000440c0c0d03080748158111114080d11700184150403d0f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 215862338 1250 215861088 215861099
    0x7050307030b030a050705091009020a0e040b0102150703020f092e210506010e0d03110601080f1b0102010b0315010501020d0813020d14071e0b0304051207110604140406 74
    0x11080c10440145c81c9400c26482880300381400241d0990120780c094010f4162039417441460701304d074410303011407000402d10b410310300c803500e000d008400708500c8c00d100034140510540d07002c40009401a14210506500055400301001c0c41c40580c0d44625008000600e801c40c0007840c1030340540c0c00c01002403201f010408114085008a440c8500004560050b00d00c2e000302c04583d0004040143c421414000e03121181d10705680c03003140c054080c40c403990311045d00e9030544960a2030020b041e0401c1d8215048030210043d941c200150b460011041030700d401a0604006006074014888600d8458041c080c1a44841101d44840f207014100c94081c1e0031070340505c5200700219400f41042e00ca850058030b20503540e0000d440c05c201d1030410240580754214100110392206480c101e12580103c0402c4940c01d2007601550003625400c0040c2440b45501d4518546580c07060b0300c841d0b0059800c0010b10380400d0380030a112202070000010350015045599540d1242540400045095003051069090120100d071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 215863588 1250 215862338 215862343
    0x2011b0203030a1116030e0109121a0901020a020a3206161b110117090d03060e06030303011208090301051024050d090620040e070807081303021507050307030b03 71
    0xf1450305c10442c40d1a9240035542240d0051007513440c41d042042980011444405d400c80d0300345120711940c01d804510012070300051002d04000d1454102c0e9106100700c4546540120711003020700e610888202c194400c00150344009000884010100d4060f40f114035414900064524010302e9503261480d45c80c01c00c00401c841541d2a00343c544104414900090000341500301d03c0d0b0054034050504442400015100820500c0300302d80da9010f503031008203a0301c5016014031038400030f095400c905c850146000008071f99284018417515214103030083c1e00c1c0301442146001d5511141d80180284568106600d40c0c4130501e2040c0942104100300982e42c0c034003032403203101403012440b0640302c0c1d50404c495000343d08020140c0f86410380da60760721141a501d07610035041400840c0d244491015440c1c50810042e400f00040c014025414002800f06000c045900508803a034819603e44c03086003c1d0203d131a0407400c0206007040304594501c40c8042c40007a5070040091846038980d5a0b0400100c58410101030307 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 215864838 1250 215863588 215863597
    0x50606090f10050103050c0c0607031a18060f0619020a030e030316120c02040608060417040819110607031106060a0b040e060414010902031f080c040c02011b0203030a11 74
    0x50200b20031000400075540690441a0f000310542c10484c2441c200b2501d032810200704884500020b03070303102102d644200da800407844605205440103d4140018805040144000b9200d24031881000e440707201c4640d41d0b030003100c5181406901014000c4e840000c00395440070b410a044011840240030200c2e41d080c00019a500c8520304104011a44d0740340e11594000c00c1401031180030032016034110350150f10340303015560051145600405039072400d8181980700e005407046811481308100f008100400c1c0c0028081e601c0390b15410b2000411800d840d000d40c54140b1241d0080d0000b1b00032542209140d00302003075000d8508030b40240c443c2e90b034498040004000e200c0c019020360460600091004d060b084203456032141d03000d007002506500d0142c55142c130b56001d03403000c0b034801e40000402c42102c0c0d03000c55540709800024400300800b810245020b44800c1490403c9000381e541d04980c1003c2e41c401d4012800c40c004c80c07006000d0410041100030b442c0ea0040b58a81d41c1d46040910704a0004041c10444 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 215866088 1250 215864838 215864851
    0x150f01090e0606010c020f0312031806161d04050a0504020f092413050103050706031a010525020a090902150901020a1203090506010b0406020c01020a11060d140103050606090f 77
    0x2042d460342c0700300055a449519040c1607070450542e0890354403d803002c210202812841c002c40f941c481c41c018240307600000c5444a1010076401440a00c1400349c403400038080f0640f00f900344100d43c0c550500714400202c00580e540c5034480c4c24a82403040c110781c7c3c2c2d44500c0c09070340242c0c0c40c070a80f0300009003442a0755006840e280d041e0002881c4414804008550007050010003c04610503040c88400302c4081d0341c070030b1300191155008100d08001d0139030107221780094194a105a01901c0503542e00182040c02090700c0650a00e400f20b41d00075140482c1281e004030160700422000f50146c481e441c02c030082007120002ca008108070612010950540c038256107800038140e006100034101030365032940e05c0605402d500c06040d101c250981c00201c05102060103843e00d04400f81d1110304e080d46c000d15040f0380c82c01e494159000345856201281150381c805407004816510b2907900c4a404c03202900400030071094030114880c07140003008201001c210180190801c0b100c0506c1503c480714801d040c80f07000c0d101c0c0e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 215867338 1250 215866088 215866093
    0x30207051605130b030c13050603060f0f01030303050601030905151b070b0c071e0b04030f0513050618060d05011a030c030609041505090f0d0207061d04090203150f01090e 75
    0x4001e5901494000c040c07810702c0601594840500d81b40031500d559882140400895240c10400c0110300b4100580ba034400c080b0740c200030081c2000402c00c5955501804003608060701c1c0c40014840364080d070440c09285500104882c0010134907080d11030807010a0329400384591840968216200f40c0320300f13440c03100303401c41d0914200380c94441c0c403841d00d0741c8035170001c60350800e03088600c4be85160305194003600d4a02134090610f00e450980782c010284000201d13413074203000d4180046030750000c01942c0d5106550042e02d04564800d59030100e12050080e0803d2503910840008680c40300c54099040103041703403a107a440c0301d2500100040b10003180011549424442d42c01d1001880c2454a202c075541c005010b5002d03c240703220402200f80580d03a045800b16a180e00c03003020035003400000c1101110030300c441c1c40905070540c03e211008040003640a8440142e0081200c82a95075a03964094110703658010211404100c501c50502c11500c0b041b650b0b580040c060f8800000c429180c3e0285001c10f103a481d02 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 215868588 1250 215867338 215867359
    0x708090420030406090c060c150506120a060204050f1c060c030b0a0b09010e0306010f0b0304020310050711010e1f090501060905091f090302060f1b030106030207051605 74
    0x51100404a10403500e40c007452041c00244a4400a402540650301806010605001a0410310128201d5510010801401d4900000802c03c082c1c82100748440000c00801e00391241da0000e00d08502880b81c919503400b44d03606107010071075a0341c010011128240c0781c0c0c3c5c428541d0303e820842055149a0f503030017151418809075000895a510000c2249024100000c0c0140c03078402003a00403155800c400d10740c0c0c100142c200d0140d0381149081441038421401040d4560402c000c1e40000c81862090700c040040c0440810115901408600001014400c08025600c1e1065004002a48001c0314900035486c0c484481741c92480410a030700100720b00c61042ca43c142003032003984c0050895100c20380d055541d604001c030300703c1a24020640105402c1d00200780c07486080741c031011858000d0b5a84200d0381d203002c000c040040d8001c03070a160300800390300710b0010940c0c80742440c1200544901840c0c1032954000008260705070168082e2a140d40100100c400c7e9400002c45c10001c440e07140940340c1c0c401c1c1400c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 215869838 1250 215868588 215868607
    0x2031611120316090305030f07030e04050415020c010b18100602010c020304210609050303061201150b0702010903170a0f030c08010b130e041115070807020f1c060606020607050708 79
    0x4180340d0f0b88150519000821a999850381c1e81181c01040600660703002c009540001c0c107034028816404450101c404014500305a501c00c1101d0a40d40e1794100c2c071580102c1c0d610380c00740c400c2d40142c801c17039400707441784000c5c24188180c0e81400c507040b00c05d0650000101000f1400382c2c814800c4546084080e0011443d00d03042c0a01030400d1100c0307100c01d02e82081c100c0c559200151050058900c0c89114200940e16802c158080154000b080c0b89610110703898003c0500d44854084442c1c8201c43c4502c404642d41d0806000490300f11040303070001b400c3c1e181e05c40e45400d40071a48100504108240c1d559aa003403001c9020100c0903600100066400203621130010b000c81c034241c500030051640001404142d0799a51101e020266030200c500380c441007074807508041c0314244010711200700114110403500d004043e0b9100e4071180900a03020740074800e0f00850103035944034400d09544500045d65407d20000715454440060f00b1a40900f40043c010800840c005501503001e481000f90704c10400b90904c60180c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 215871088 1250 215869838 215869861
    0x203041a1b071e050a03090e150307090902040204080604050304031209231f0905040f0e032209050c090307080601080a0611090d0c09180308010519030501020316111203 74
    0x50303c00e402d41e400b1140060340010000c12241407241e219494000c0b0315883c10540340f001c0100140642c00780c0390b070316584100690b40480d0b20015aa603440000170551006d0010500900030341d00010071b584a841c0034441441030010290048a10802d0701c01004503600b80e0446070400107225105c40c46280b1954282050300351075950340b9020010301001c811205c502c501c443e44110103401c08021403100c1e40188002d0526005080360509203010500180c00011129982e034445c040c5c0f10050503560011b8003055005a02e40751009192542d018011801c103181a84216448121840e20078880c00c50000740c85840411560304030350801028210750b203515203914000c2c2c040f02854800e52001080980040da60706892002c0c420301615402c80d40d20700b4115068215003c040348017544440701d00c10b8000103513100560606449060325a4181403c000034020400c1c042900700800c50b5001004000f014100e048032803030b0b007003240e949a00440104044c800c1e221a564016290030030406c100240405181c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 215872338 1250 215871088 215871113
    0x607020d030e090106031a03030403080909090c0a06030506192603090306010f061101050c070f0201030f1d07050402030906220b0f040b0609160813060203041a1b07 72
    0x1e080159402150b880050070310b032000d07003203c8041381d13551110304121002c0c90203401a0f0341e0150000c6240c14159152047c950044d0300ba20b502c43c401c2c200010f00340351428001100320f1040a408600b0164a40760003030b02401048422030b010f8030310701c0040d442400c440000402142d902c424000c014404c001100a407200030384c61000818030080000c580b40751801c1013910700900c8455481d1858605081d002094070071040490b1b807080e814582808820007840e0102c1c1d4001da40404540c446013010310040c2c0c050140c0c0f406610b0090314041900543e0001000001c0c100000c020a880546403076030100012400140c0c0d0303180d840d602c00400210016010b04c1c00031030a690075150f4800e190b1107961160065103040b58108210148601800108000440072507040242105e10001d54501141c01c10b041900c201100d00800001201040780c2400e0a0b4104281d01d8014800790360780d140070304000259424a0701c00024031540540040e00c2c0e0410b4010052490352400791302071a00303240d80c55030322840c5074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 215873588 1250 215872338 215872343
    0x30615140f01140d0e030f0d18030212030403030e01020d06290301030f051e01022a030d050411101d01020a02060f18090a0b03071410051305060a020a0507140607020d 73
    0x584680713220708200708001a00c4d105c1076207d0750f81d075510300c4241050b0696030a403003800c004502c5000c0c80070000b500420b0790041c1c0c0c2c5003052590386903540d40c14200d02070a15210080c1c5035510006020050784825003004080e60b0906c507074840c1c0b442107080a905054150100200c109030203000500c002003a03491a0300016000700e0480b0000c0b2120604141411005040344509030741c00500030600d14400d01080c00c089050407000229240c079405015201e2007002e109000c642d40d900002000c000152070310f004010000303013481e285c0560a46010706408001ca01c00081c090712401c4c40ca203158030020f4080700d51607024103410300301b0f00280181c0c1110740180c0c250740e900d0442c40c0c00c48200790715102030441c41615004c80201c0c458450109044c1400f071310707401104202c506541079400c6915025a11400002d1074a40b103aa5114141e40c072130806040d03600002c2e0300002c000380b8800026400904604071a0188069034881d50355840442850662205910b40100f024801d040241c070b02510400000750 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 215874838 1250 215873588 215873591
    0x1b0702030705041503110f0105030403050306010215070c0317010501050406050c0708010221160503060f01020a1719080402011b0302010b0a031425091104030615140f01140d 76
    0x5032100d0003c0c041d54040c0042030b425094501c030030001e0000f141400a900703401690110403198868000030190b00c8020f2001d81440300c00004141c69900c01c0000407000c04101c284d000c6142000c0c030008090010342d00080e070000e118a000305d1800c0d070a82140904071081612400d151914003c0d01340c40036007103400c068100c4d000381c020000c1c00403020b000610995107184201c1c05000109121041c203440c0203044c481c0c2d0480e5007001c00096070707040740480350040303002c461910b0720620290040749071800b8036000070110000752250a100f50045400350040250304041c00b000c40004200448041004440107400178020000586107814844078660341c0d00d0180c0300106001c05644007003124901c3d5a40102c40e098411884170354159420301a1900792012111101c0002010b0f031406031998000d8000d1301119680d0f070003145c0c1031000c1c280032100210703480101484100403c41c04544100c12500c0313000404e40303240c8284400e501c0c1412210b0f120020503103c1000710403010b0320410b801e0f0040d9400718140b6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 215876088 1250 215874838 215874853
    0x4050307170f0601080105070306080f060a05090313301707060204050d1203050c0a080117150405070f0f0b1c0605030f01090218190b01020c0d0b09151b070203 70
    0x144020f01843d400307404900004a01e0f810b06010040403580140c0c8200c980350800c442811485e1004101c80d900002491400b1171151201c29500c1c0c218803c044030212001006980081c0c8400c0000ba48048054040c81030380a5252586000300100c41205004200500d03030881c81c1744211200018041150060701d00604160301c0b600070803110b510081c02500c01098035040540b003a41e060041680c0601c00801407400c1071800c4030042d16554041c040c051000c1c030196801505c0d0001000b2520100704030110340d20f105d00b460305189845001c036000b0201480b4841c0d50109400c10300040038411241700d05051032a043d4004003426907034224140b401c0c861921408000341a58003080348203035a101e000300014030a0341c613104101003040b8840320b0003d020b10890400913803003103080400004000c0410082a41d64804004030304143c4401c00c1d05074841c1d03045001f138041c0811002c0081c8103d416404442681028820500003c2000c480070500c9410082840c0a0607144002801080e803020342254104e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 215877338 1250 215876088 215876113
    0x513120302160807020a06021605040e0109020a1d2d0604060806010914160e0d06060f0b03070e01020c0918070528060302040e01090b06070204090c060e060405030717 73
    0xb0301031044000c1d00c840c4000310303000c42589403c2c200c0500070107075070004000d8100120f0702400c41e185544102d038400e640d1046c0c513601c00202134010289240d4014420180541c4484503028010401103e0900c56401036001800420070901080c0c0c9008007450f108001250a549995002c00c0082c101500b242d140c02d00024007400030402e4a019145205021508411002012404500c01048182529aaa20914003c036046062508039142c191200c0507a84c005051801c094407282d4066450308011107800500080108003440c00381100ba9521000c180004004a96407020355510682c000c910340003046004410406e0024005c8d01b04094071100707941c480000e000f041d50092450400b18040c0f040802c1d114581a08202a021505045090071300704910105e9450701400382d14001e940d200d0309107009543d010242c560480d030040040c401e048a40c034207840c003400544250408030f5042c0d200c11100d07251180507202a01e0024004100b0103103080040d40300d042c5c20000c0c4200d2400303141510000b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 215878588 1250 215877338 215877367
    0x402120f1e0d090f060c1e050c01030501080c01080610030906020d02090306060d0308071815090306050105240a0c080408010b150c060601120608070e0a0b03010513120302 75
    0x2912112545090840014115090308060b824042c03002080080e800c1404081c1448a80d0000d448580c41c01a0008072607103040ca40100640352840704000360030083d60304005000a101e88911800e980a201d580d83e10494250b0300c841240310b2501150f420000502e245c1088808000741440600c4c010400b80c815480303d4040b07900c40e5000e0310741e8036000540080703242000c008070f64001d901900c401503001c140c0d440003000708001034040001c01210b0103400c0d40c5a410414840060110007a1403899032040c0e11000d41320040c5484212079071800e0000020b56440c0c04001e019100756030b416010807509007104105065402808031506100c10a07010a0100b201c080c042d202a00c4503400010700501d4000800c14003000e03101d000d010a10041045c4550340c0740100e070013074201c035081c20000240b0819000f0304010f00303403e40046400b0311034403400240b6401c059046038002c244003a4200552841e140c1810700740c4c1c10171100c507060aa01c1c5d5500d0400a0740c4d010126501500300d250040c03c00921000082 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 215879838 1250 215878588 215878603
    0x9040c09050306060f180a0908041205010509060c040e100b13080f06060607030305060a090e0c0f03030414060f120a0c18030c0506070303060b0a0305011701020c060402120f 76
    0x80004101060600c90390608001c07443d0481380c21107410759000881c2000902071006c1911240039031885801040b46502c041e04454011344c0d0280900f91213a4565a402c0c4090703006a20030f031410340c02c08c004200d500201003107481c02031806009062a260808500620b41d0750b01034040c45078581c41000004201c030050002d084200b141168500c1d2207032a103050f0b40d14001c0301c200c42601d0750308035505204165130ba0400700e6000990500380403c0640c0d4280000300d442c04141c0c01648140d082100106800300041072203d41d50408484101d04444103a09240e80da010754060526404000444140c244c582480a404004070881d800d5241c201102c510012030042039030b01e181041c2e183c2d60240c05107a0001c560140600600b5032035070105181d45c40c0d9103862203486c41785900884c400603403001070502c80e421180140c5203400080d41c0d10800400c2c02001003501f40302d46000180c010444108c900f8041c000c03101400c44d04401489076485903020040b1810803142c40b4241c0d84115004074091713007004e0105a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 215881088 1250 215879838 215879861
    0x307111e0a020a060f0e10050702030d110d0509060f031b0c0304030c050f0d060b03010e0703050c090705070804140126010906350a0516030510060b07060c050904 71
    0x1080703401e000780306102008049400c040c00f48074211030400f6141e030303000e01010760484003150102000070746110192200d2054220282d014022405110141904a1145594160351508880050041e039000321044d008901ca050ba21800400407454048000c801450f0403c1d40d070b80c0020403e140e8400d484103590321041070761340035400c0810304109103c1124030310801401c06840706089282d80d840007444400c0010401080c4030b96800034030903351801d41c0b2103902d54104408480c00c0907101d0810340d40d02e030380558110348502c0d600030005204620541c19513020036445821203082c030341080800041051921111380c1008500300080b001c01051161082203207150380d0901095504082921098131100d4000341c100740200341090200b10035428203080e055954051301001c0c400560301e104d00f006c40c4040040d0582c4100440c00c485040302d00100c40031a4840c2e8211403408060700c0801003600c119204140d40c040040c009030f000f040564000c0700b119041460480d2a01c0510400101142c0405022 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 215882338 1250 215881088 215881093
    0x1503050a050c0603071b05190b090f0d020607140910030b041a010c03051b0303040308180606010905010e03070b0f130b1204020d06110f0d18080307111e 67
    0x8650510106102c040d002c0c840c2a244145140303071048001c0e01380e40c9007198222648000d00f8220080c03000030303c080ca810017608440300310024100d052903240d00c0c406451054550007808220201c02c1e20004010403c0d4010b9000740c0140c2d0b840c45800e503100c40b206031501e409414204034001c4590f503694101d0032200210b07100000c0300000c08080c80101c0b94034101d503c0c1d03d005007425800484c0e80204c80398442642c103150083d40c9840708100751000b503151003c84141440040140020550000c82c01c0c0c0c441c1050708003640c03501590f00b802581c5c55100303584903404a400d800c414807841d4400c002c0c418403400050104e9090f107640c0c50501c40d0540c070000c1c03143e2944d000822640c3c0000c1881c2183e80050454507c03103414207602c2d01040c4290800507100074420103098840320200200b2f90061080204580350342912030b1001007100030f040c3e1025180c03600480c070b0007210710312100c000800c050540d40c2154400b4110381c0d13003071010307202400810961a036911984044000300120889200b0526120101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 215883588 1250 215882338 215882353
    0x206070f112e03020c0f0304150e0d060b030309130b010e010302071a04050708060a060303030e1c05030601030e010603080c010e19030c0f060207031812020906040906150305 76
    0x10503403012169107400724030844481e4036074400207400004000b03900b44840c201e100120a501801e60080c420300d40c100d00d0354060741d41016030011001c030180044402c03620b50300c1000540b5050032907071750348401d821992110b5000c644602150301c030707400324041c800050102c07440c140c86c1030001481074802100c1007050a0302c4446055027541c1c44400c0c0072583c0310a09003903090000d00c1d940c80444910b40c0b00d66140e020b41c001c0c005018000100942c100922508065685d641400315506028200170b01064020034104500e07406400c000007910031207400c2c00d0300004001c404001040350140d201821081c10180c64000504200340207202e1800154410f9090342e035190302c0e04011600b17484603149400540d4008901150702410840d9030401d410f07a02d40340801a00b40c403450103a410040340a0003604091020074413104050700a5208201143d0a13860703403071156650500c903203484000910013134104000c080842c144c1d0401d500081d1001d07108000105050581528800d060106507005860301c2d441081c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 215884838 1250 215883588 215883593
    0xa201006080a08070f03020c09090312070521100b0406120f020703080106270803130b03090c0d2607060501050406030f02131d07030308060405220f0206070f 69
    0x119110040034641c014080b810795548403603415010b10140034210252441c2e003142050320a004456100307030000c2c080e400c541402ca80260b03482d0440c0c440100c0a03400719004c264210301507826561280c8581c0f000c5003608080c0d480101c035404015001040c890098400828954505005080580165964403010b00045041c8000741c03103861a14544440c810070162010950040c181819100e060030001040f5114440c0c5100c24003030001031b03000e0b00715106d40c04102c450000c0010300f030007103510034070300402c1d622800f440a4030310094134811050791006140d0101c5081c4401e8045889014401d03003042581c00e0714900c407002c030340c500d003040c0c4c203d000080c040e040003464400c260140400382c500304010350079982d5141401c0c00700d0300c000c0e00c078800501e4030751146801da401004011202c80e81400c6d02e40540c1400300e82d1501d80340030440108192100040d100d0030a07100d1944100124500c0541031492400b5000c52450100c0044d501c1641c119102000360b21040b00a1a8a40c4100c1c00c884404e1041d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 215886088 1250 215884838 215884841
    0xb0d09021e150909040308090319030615090b250b01030305040617040b070e060910020309030111090f010f090e0708010315051504180b0405011416090b0a2010 70
    0x1c091182c0000c1041c03000035003030345607240e03074075401940760809050710386900300d40702d02d5400380c00609240f000503100740f604803640c10f80001d400c4070080554400800240101519085070700d004580b0301c10014424100c407100c4440c2d11842c00c100405151000c0490754541c040101d009030030603000f140700003c00f0450250700c60300c00c1ca444400300800e91a9820030b40d07541324a501340945540d042048008010115503102402c54803901c0000b01840820309000e2406910307031700b194222a10070f500c0d00c002d450003018803104076011f18100921200761070144000550f10051080031101c20801910004a103400c20324403940c0c0500416102d004240d0301d185003411040a074081220203060400e81400b011510405c1700505400c0d0495022130080000d0f0313108950355142e038030301030a10020501404103012041d8400740c413010103420701c16015920040310b10a00e0b941401e1070350005407005402c02034590140c01030081104145850300600403126070352624200072403144070190b0065001d10148601c00d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 215887338 1250 215886088 215886109
    0x90e1f0b0a0203040303030507030204080607090801050601020a05060f07030608030406110d090509150f0604060c05070e0c04030b0a110304060f060608010614030414030a050c06010815010b0d09021e 87
    0x26030340061401095a10080d268080c030301c001403d00d07846402140000e03009805039009420504c00701c070030f030345819400106030103030502c00d9000b5542b800000c103110307500c0886c2c0e503a0301c0e9822100510b42621011108030751540b00030076550400d80e4446000c0b803000801d1000307100901c030740c1d500c2101c0003035450501814811102c00d02406d011a0180c00c000c26264070840c03e0b8003100c0341d10841c00e070b58901c03004100555041c00d10386500200010740814016007000b01500100d029004455090b6210b8100c4201d00005542150482d01d0900041000030000555564071864044d004180f0b480e550300c1c0c418954100351000c441003a290b550000100c1000c0c0315107001450145030841607549031100281401850380000d40303a1080000c005400c0c00b0380d60b80d456074000490307811039a407030306101401450380d00680d01c0d0340f038140a80000000d11000016110000042c0d03100f14400f1030340380074400920307a44452580781d00c01c5c0c0c56000c1030000d0f90b1598640071041140f511103124043c4210304001d8035805 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 215888588 1250 215887338 215887349
    0x1b160209100f0605030f130606030602132402070e1911030406050708100911040803040308040f0e0103020f04050414070b1b3007060515010f17041101090e1f 69
    0x141407041003600001801b807290800a1503d000005087c1130401c0342c05007400340c1000d4403050000401e01000d20600e20504100c848660001d6080900812108903190100f1002c00041c0d110304070034405003040b840000d07001114502d03418a28400120000c2c192402c51000070146440801080203000b424001c040c0e00c80c6c201c0c50aa0070310718203001546110002402841690f90f40c40d890101c295207181c0484001d00307088000c03a41c0300c0b680e0f4606041280d1043c059000d03860581070000490b8624207849a040e40d500030800e070b05807a0f4980500c8010300004100f55007100b290301107280380600c14003156020308000c0c000c00d66500d4002c0c40d203500d488862103810380545d2003180140c00f165800ca040700b01039041d89a401035040705040310241180a500000703000903103070809100940c80328202d2240d01c08420388400e95030804048042c0ca4031560041c11941e90441200042c0000c1c1c0c5004505003064014100301595944488514448802c11641c0c601560307641d441e09035480d80a0381401d8001c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 215889838 1250 215888588 215888597
    0x3020318150103080318060109020a171504021305060a0201050402030601150909090827180f0a050406062304150302060f0d1d0109020112051b160209100f06 69
    0x41d001111000c080d4052002404451020000c1800402030380d0790b03800800d09500842d2050b503121552100294003581d900320104a841a200f42d070640000352840c4595800d0010401a002c1c520900010f940074025003400c101941e04040355507550240600103440a65000148510303082c41494036003081070f000034604000810000040e107034400061000e861520501081101080c900010680246905a100034a405040c1140981154141201c80c441100e80305da114800c49100d00e00c030b0b0000d5403000c0d58480004000f850806060704019000b0f8400c0b03800188071541e0f0a00080701040300314056103400034a00f030402c0607140900404180710150056100c01e1455a40021420b1203120310480b42c2d8640824030800d000d04540c80b21044040001403e006154030000190007000f20307190482c045543c40c07158002710b94803881010f10842010110103886500f071291500160841f011490314168088603642c0140c81e03c201c954000c4003d01210300d07200741041d0243d6841500c0f60040c81c20407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 215891088 1250 215889838 215889853
    0x110109060912030b03030f070f02030106050a12061a09010504150b0a0c0c0b0f090d03032a030510050a14041118010f0503070e090426040602100603051c18030303020318 74
    0x10801b0307000c9950056008500d2000d401a510203340907110681c0810380c04100c0b00310001300f1980303805034688a01e00c1944208407041e841d2001039130020000340c0b0181c100000c0801030081d81000e41c000300c6a800d03403c58126110b5aa0400340c4455405845203500040709101721008100403c01c550000d44100c451403410a203c03020030941c0d03801040350461003003c00c0091241818041d90105c0c4902510f610440e480e8071040002040340c41c0a80c2e000000a80b6040028180441104410b800e0307807002002017105c68940f83c51002c2103918140364690082c0e991101c50703103000380c41e8001c140c001001c0401e1828002050005400d551401c9074007418084200300300065143e000e041c950540208889062040c0c485040103001c6403d81059800320f80003040403090201c412034090300482c1e940d9400c407a8010313a40c104010a940151000034050b131f02464517224007082414041d50b0f40941031a180f403035031702c03000520050341d10260310682c04682d001042c0814040c10844005a4048150041856 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 215892338 1250 215891088 215891107
    0x21216020d0305060612061801120b0612070501050d0204170c03060108070f030813170105040b1008061504020910030509101a10140a1e030c050a110109060912030b0303 74
    0x8901c02c08200521a06c00400001c0d8142d40740b0b061559080e603018140703141903031030b0343c030f07613030f0710075180303078081d128600d20100160b4207140c1917841d40c2e5800002000380600d18903210054a080c2c000821100c1c5c6103800380800314500c0001d401c644e03420030690008020700110315007458280601071300003c1003030308003130014024802c0020001040300c1d0700106442d030f0b41c101d001c26459100c5050300503c160300c8181201e065001c805401ca5400386000d5140c00c11103403a0b080350301256100c54400c450454100c51f0014a00e20030407a00d410001001800151800350081c0014150100201c2c410000c00d031380c0d01c2030102d00801040241087e0347e1b802000c0100c41d100800c16000564184001d0b48208224500400d01e1071003401c0c030100074a601101c03540c031a0042070001e00303104a1080302078000198483c0444a1034404c0c019585001c0c6191522840c011103040d003156600030f0140c50341925901c5540c1a000103240f44900c0c5c0c441c902035031038041c400c81c003100002c00342c424001c6450721950082c0800c184 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 215893588 1250 215892338 215892349
    0x5120c0f04120305040b030406020c0d0e30030a0906021501050d02060901030b0604080708010f091a04050a020306070314090c09060409021305010e01170304030302060105060d021216020d030506 85
    0x142c902160006508021515003103d8920650704101c5c014600841840700304081070b0042e10401040506440c1084648002141c0c02d10040d020705074171014442c4116801c2c0d890400a540d141e0840318461004440120401d1860703010400c0d02c000101800420086e803030f03050007801c43d005800224080c6551402c0d0005406640c29a0040d100e40700020750001983c1c00b81c2d01401900d00c0140c41203444030b0340d8042294441e9150301c2a80769a500704010092054028890358000603408000b00220511708029903c10100003401200d05103d072114070001344c0d03001c2120030b11840503594046140742600d44101d100034000381c003800f883d40c0702c5102e000b111303a24140080e50002c0103070750000780010701c0d0000036400c1044840700d0762a00d251400106860001a5105040c1c8001550051481e000d20901c590b5034415403102500680003074005000030700e00080148041c0c8100c40025003400010f0290b154200c00540d2154000c01e00025610310254060200c0c0c59001113900341081246020710204030b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 215894838 1250 215893588 215893597
    0xc220204060203191b02120f070311120c15070f05030f0304060c08060a03110409061107050c0a03111011010e010b0f010f12050a020c0d0e0906090610030504050c1005120c0f 76
    0x2445021f540a0002c1c180380208807041d01c034004501101d03107083d40e0b414807404005c1c480100d01c0c00381d43c803c6a5448616000110a285030402400d00c0380c1b40c40b41ca0140d1038068100e07400c101e03000341d802114000030483c2080034102d404814040c6e03503564240791902c035080f00d48034010300d402c3c0315906003007088540d280f078000c0c82100d400c80c00c4100c010a00400281c004c161215000304014030f070018142c0716101d09406021013520900844988842c0c200c00c01421244a10005244000003030011640c1c1c1054081c07122038080c41d050001d050201200d02074292400349001019a0795200c200380c095280c0843d400616030420b00300000d01c0004140010002d89142414049080e210400308400c20110340c100c030a86840a01074540e44d2990f48001030050b41a4981580704054400100c0c0503031401d050458014100107115042420a244081e000780c00000c00a40b001d015445440c145521200091040c4002d01e5954664a40001001c180c2107100900ad106051006202e10281c5200340402c45 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 215896088 1250 215894838 215894843
    0x30203030d0518030c07030b0105030106150f020c15030a0f05070c022806090905010609060c15091e1533030c090902030f0a050c220204060203191b 65
    0x4500e90791882e00a100c002910f85083c501d03803000080c2020560408034200d025203226089904460b40d0b10403c0600780e8056001c1c00c48405050981c2c0c0c04458010081c444c003ca4450040d0380d0310300003034000684040855481d41400d080c0c00000c02440c0c06841c4100d58081d10b02c000c04001c981020712004001c83c20040e4024010f1785e4403c405c0c4484a14094140c5501c01e181801d184050b40f1030100409100f8544582c90071507041000114546024195881c25100c1030f0752225040c0702c842e1100f0070605a00f252030b003030481e9030b2102880403030840491302c9a0300c1e80d0320280c04d415406030728000ca80001103841d007101551902c1d1440c1120003050719910840101c1c0068440c650341e100f000403448800c5944010710300342206100191203440360704030b111460b008405943d04195602c0ca669100d103081d45000b0300c181c001c040300807158603100445e032046c21039020382c0603403545001078100c00f243d016400c2000943c0c004034408400f0352101040100c8800c035881c203981c1541c8036072140c0320705159103d0300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 215897338 1250 215896088 215896091
    0x1d0d0b0a020906071e0b10080d081504290105090a30120813121b050304030605060a080307030203030f150d0f050d050412060e150403030204090b0a030203030d 70
    0xd2105580e80c00584004c4c0f40c014580a10003005100d650401c251283e0003210281031110000754000b140240300022501c050014090740500b80504480d05900100850007641c082c0b1038401c15515280b14620701030b4580040e43e414401c2c011742180010303030604034140c104a400c100211003511814040c034101d4400041c5502c440e2010441019800000c42060107001d030700c0c4050105000034034580c9103481810b91510700302d90f00d40300803019803640c804401420700c100504085000c02c2c402c00e800b41e40344c2c4110307030f8109141d0142d50307a050071903000d90f2058031225142c000784007207490100100b100518000c0015850304840b030f40e01a450340001004a01d05403140e100103641c0808007402140310326030003802005090064070385524031900c59082a9020301c41c00d914049080d01030b40445055910008610440050700e81c0c0b13000c003506d40780396004028081c1510003030403d0165544035000c3c2d8030a072030150307c890418018104540100408500c500d201d040c081015880c04402c898518150b200b0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 215898588 1250 215897338 215897347
    0x51008030a0905060c21030406060b03060f120f0106180b0316090f09121e0504060e0f04020d0c090915050a030303091704081b040525020c030303071d0d0b0a02 70
    0x140c0320b08080c4246d0801c103a8403a8501c0704810805400c000b5889148a060308200c469200c40c941c0c64207000484109801c0b4031500403000d52450a03104048050400f0f0302105c400c040440441404e4941503881340481c1d01000c0342206101c95075009460300100294010b00226414400c8810110500d2260215443d0f560342d8250214509400009041d904100400700800c5078402c006e08014150300c841002d14503040c1c504455910480840301121002e5a61040980c02c0c2c60400044105000c507413a406942046a410f000e00315010316400e40d481c3e03450301280f05144c1a085810b0320300e220304d14400c1c00d0b00c00300107101d03a60b40d90410742c080e603815140014a120f200d28000c4030f000ca4011042003a507001090029014100080ca070840e12a4407581030310019801081c00103840051300c00d030101076186000e82145204403020314441c4d05036481156000a02100400c0c11075009a41c240006006840d40f1380d0440b080e01000326046c003040d24000c0346036840e034940301240803001c2d04400f00d0302d80004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 215899838 1250 215898588 215898607
    0x21024170a021e01020c0a1a30060112061a0c0102120114040f18020f010c1a06121b0f0102150a14010f120f020a030b0a051008030a090506 61
    0x1020030140c0c083c0c2500783c4541c546408041c00700030988514010300c02d09000d520b4a06101e030980b012a000e9210051203202c1c240d070303a184603410000301440c1c0c040c0040444841c01810010506524400580c903144a0400c1c000040c0445120f155603400c01c8d08003001000304481160070343c0b62400340800070320344600c0c5c0e400b8000c0c0a449145040c20380c44401d1070010648181182c110103a940b41107904002c070041c0329018005840382c08403001c404130501c00240300941000c2e4807000300c100e014500502d030722000b0390314034640c0b602449280e03000c11032541c104011030500781c42c0445021840001400c0c098001e140401d41110035160a5010380d0000343d00c074006900070020040e244800072404140791a003074180600804843d506400e01400c004000140c1c42c8440d0a044180c81c1c015520110300d01490301c503c0086880b1040807608985416170003c0890348618120380030303103100c0002207058107041ea5503040710403035a0400013507a0070402003030b00000d811440540480d9819280140c0391180c0300c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 215901088 1250 215899838 215899843
    0x30a0e0a080604050d0207090e03031b07020307030f0512090d02010e0301020c0118050705010c02010906030216080309030a080604050105060406120f020c0d0801060c0b3402102417 79
    0xa601c522050310455050204000c0b02040c0040d0341100b076421140300d10b42c0e412500e0251034098140010542080006c24400585032501d031106001d100e98071843c01c00143c0c00f0038a00300455100756440e000c0342071403e04105060110058008017800c5403410304c4303004e5001031110403a03c18006c0c14010a01154403041e1005e4041d601a424108001c0001e0162030307161820080f0042c00c11a11400f034003101081c150301640640b14040e4043c1e503054000c40c1001030660007540300c10711107903021100e82c0d00c4500250b20800110f1048800001442d10303401201c0c0050107014001d0600703440365080c1320050066850348000e4400f00d4105103000114004040200c000a00b202c0814405240c00004d2018180701c002032280c0c0d9450980d51140140c0c0e80c0c60703030112071100380d401e0020320b00094107000c20481180c0b12044000062050f40310780e0084042080d01d81c04500c8180ca4401680104590508156075031049000528460019061003260000c0307442c4000710f02d000d120070202031011500c1c82d95504 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 215902338 1250 215901088 215901109
    0x50f0904021306061d0a060e090a020d110904052404021c060f1703090102070303050a02160f08150405060a0c17070507061a0a180915020406110f030a0e 67
    0x3166010849662103010082070300034446844506014440c2d42c0c1002d40c00c6c040340c00f408862007a81d401d019401e45c4000c201c003548015141c005040e80900c0b240350896414800d100300c903020b040f040c0e80d541c8062010b100586000810382d0102103002c60904000c04100244400200c0d0115030059480c4038501c680c01d2192185107201324098644480880c00850464001080c0d40082400c04103480b0181d481d20303901d126032112a130040c0c000c0700c410400240907201825068610307006484a5081030411a41001142e0307002e001e04101d201002c0180f11010710050341800300c00420b40c0300314039150701c806031307580c001515901015660740d000440040c424108200d180407002e20902260070080700c014000e40000100340c50540c0740200031441030880c4400c143d010f10300608010782c19890401c45159110302140f09410540c0c6502405002030000d001e03190302880003141c016161070900d10002c10b100100e01d20044240d01841c96450095000800d0b60309101c40e505c2d100c44000007000104895408 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 215903588 1250 215902338 215902369
    0xc021b040b06160b0105011701030c03021309060203130c0501020c03211b06090d0306030f060f020417010f15060816090302130222060512180d11010b010306050f090402 74
    0x28009030f40c007001030b1040d180341281d1003640c8030620709545d5041407400200038480240a28054401040107041044440403007581f030340000214207441e40c94a01c20b036442201d800203480784826038201048480b81241c03014140038402010b1426040c004260b840041c0d50003035000c0103051203400840c0e906a412519418661221000403101104d0307140c2d41c07908103452580c65800b540701409005482840b50741e017240e402c01c95001c4442c140751075841c0103040d160322403074485400b000046000d45a05000d0021040344000002e6142200f0b0b2117035044440c80005070038002d001c08404c108096010440981081400c804032143c2c80d03203940c0070742e071000590340020740105001150008121541d805003504141034844280c03000703040441e2031f010b480d8a0240b040460b80038071100100e0b02c125440107030300c803c0d040070b8445504d051810481c58900a9109400041e94046249007451070070300418800c00b1080c00c0a01107a0708000028840c2d4110304083c4d4003e192201c001070655031950b081081001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 215904838 1250 215903588 215903617
    0x1e050c0705150d0f0c080c0304020409050601120201081b0702060c0f011515020106180e191211030a0207050603040305120903040807050f060403030f090b0d0209040c021b040b06 78
    0x2248000c1416a0070008001c4002132914842803225800e82c0903041d18124190303100391996aa04910720301039000a407040c2d8201c0e035603009031400210104100e9010f0700243d03490300720342082d510006110031001081a00c030307121221807000c8504c2413201911001c0b40e045807200d8407109040700451405011201d5a080b0b9800e00010500340241c030400d40d81918140928048034000440081e8280d8025101f81031041d001c803295120020341d26800040f03680160700035981455494405550014520f070010303500008884524090b030313a002020709086050140c099410302011050182d00c580c074034828107000d0600080018201032080c012143c1640c0902d10190a03801c01d0b2085139030342c0e001402540c04911490b0300c00726440c80d14184a07150804010002d900e040d0070b41c1d0f82190039201c417000000a02481510120360035030b103500505510005a01c0c01600c2c2c1c0c0c1c1b94402c00042d00c40c1600345009540107841d080e003080d8640f102000e1724203410349000c255016064042030003441034030803441400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 215906088 1250 215904838 215904859
    0x10606031a04020a17060a18020306031c09090218060c0703030210180f05190821090607031d0304060201091703060306040303090201030f050a0c0207061e050c0705 72
    0x140d4255122001250540038050484003245041c0002c91241c6003001e00418151000202080700308540e5030b41c00742028103103c000613036500c0c020012403800c0209142668000c0204416801c04220b0040c001e04141c43d00c006c44030581da005041d0b04c1c40c502840ca038070383c2c00203101014414003111700302180c00090042e541d2980819030035030710341401c0c0c0407c0740140500700d50024814480c1c0503038900300c1800ea440c00190052035560a9406001d18021202c1c0d026500101c10a1380d4080100c1001d24051360415035103030f0100306910b8800c0d0800441c1c1d81185441014001810070014425500c41c01c43d00700002e41c006075400341d03080c0302d003814040b0b64288400240481e100d503041d0803428181e84180d402e05c5412001002cbc82046010032181c0c00d0b01680700d04000790201c2c0c400d42007007a42070300604002400072401c080d05030039200c0450b00705161544400c40c100b011076040020030010700c02d0345000d100520340c40c0100f441e10001c1d039040700c0c01c000c00402c0c18400c032003041c042c03c0000d080007840308145 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 215907338 1250 215906088 215906099
    0x2190605070501050907080c21010513060c0f050703030b040b12100605030a03021c23030402010e15030115020c041410090903080a24030c0510022a120106 68
    0x8581c8400012100c2c1c2d401c1c400412104040068101d0a4860f43c2e00604101c10468050103144030b10312541440b0040040071407450700b8028070620740512042e500b03042c48016641440c4056680d100011410010040061640c40f40c0c00402da440c250390600c1c000c40c1c6901039400046c040c01035514001e5101c26547c0301d010702508001510f125003825100184a40382d0740f18201602c4101803003025000d60008001c45401c0114508428030ba810681441d40204944403036116842c3c0140c0d07040030f4114400410310041d9a00300c000002d25460072078584504507400040408140418856001c00b441080c03030ba00181802440b0f443c2030703a03001400c10420501000580c40c4445403e580190349230040890210340386040e030044c054060342544130b00009072500d0000000600c0c24182000b210300d200150601c83c10703240019a4002d50007688490125801d00c001c0008254110b050b075400c2d9441255a00d005010844c60400120386140800000880c40e80200c0c8072400403507180f6a09502c0e2a4001c00c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 215908588 1250 215907338 215907347
    0x60507031a09090705090c0c0102030109020a08012c09010e060906010914090a03052803090512040302150702030c0a090e06060a03241b0903260304030c021906 70
    0x8121108011246007040c40c80c24420380c120140c40c1c40e2550340064205001c1403c15050a0b500300c030020041030724100c00c290a123070032070b08203030400c55030150005401c107031155100500c1405401c44841d1000c0216400100d01001000c004121880030b41c60400124031100a622885080e50728005480c95490101d00098640b1000d010b0702c2d01d10b0349024518545000d20440141c0b050340032800410800407140c9080c0c4a5070407000c1c410318035502070707002088014080d040071800c0c1680c980b004240c0804618205041040030610400f85ca0010b200c10001f40e40d88400e035280070f080d490801907a0710501d00109040c203000745000382c0c001c100c4c0d160015480c0b000d03601a48448903041d040e80d5035502c500b03081040341d003040e210141502a4146c6c0303d00b5048034104034994407c059880010700c00c001d010002c540070900110345401310b60090130401c2800040600141c400c41b0a00415111080b22800c0059601024001400300b0049115640440d1102c0850301c0c14001c1449502180607940d450080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 215909838 1250 215908588 215908601
    0x608030a0e120708030f091c030c050c030c03031c0f060e04050d1403010510090e070f08013003050d02070f03030e0f06160203071707140703020f04090f06050703 71
    0x2d0003540e59007280e04064402080341c00964800780d000d0f514018400c15595555044524003503800200c80b103204c86c04692103055030228600c0b0303071110340c8001c03a00c2c14030380e003085034009105000750002c221400159801100320b4103d1002c2802e40304905c540c5030200c10042a0307116502c00c80350f103080c40104d40c40b80c10054240c0710b41c0c4200b0031500901425242129001074240b1020300361403040c80188828945015250341d40e600c9860701401f215614a010200c1603000c1e91102c01042c6c035a0780c00c842c0b83d42d100640b2405003e0f0740d85440c0c4009c41280b426241240500ba0074140b01c8030458001d030405128400311600780c8100d40c810b5486141a0514405030322030094100c0101e403070158203601c89031022416a41074000e00000e84410344d68a001d010007030108141c045e0450000300484400240700c0d20a18000c60107540005444070402e281075401812210101c107003503030100208200607034504c0006451488191408108090b4502e0811010300318100000c00c910b0811081100040d41a84000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 215911088 1250 215909838 215909867
    0x1d03070305012013030b07020f1005011d01030f110604090e07090c03050f040605090a0b0a061509030506010501030b0406090e0c090a06030305040506181809060c0301060f0e040608030a 81
    0x45100320110380200c1507108004d02440141d442103030410100e1042c0c0d45190f4010402c1c01940c201c2c848490b9840d003020002c2d82c042c0001c03503440d00180050006210500308085003401500c40c5541591155000703580b282d1070080804007541001c07403607900c41009880041580342c400340a1a104612020340b9105030b4020044214505000c40702514400d00645000d0b05200c44001d615803503a443d40000303450300900008691040c00024000101c0070240c66101d1100c0c8a130004482c0c1c20503000ca5048203504010404000a07a2000c2c1b000c280003240d69070442c1c500b400d0024960342000045000b070001d5071300140c075191803d6484000410003003403410741090100c501030180e82e03500505004a800b00d000c0500000d0090005120500304813000b0805800800108410203c0742d03000150508240126814240c40840034840c148508001e46a00140290b09490035581480302c01454841189540400c005809001481c961556400070014090003001c0c2c0f0782d103010211f0f000d0946400180c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 215912338 1250 215911088 215911121
    0x30a0b09070603050c180f0301180f1104020c0304210b0109142203051305030f0a140d0807050a140d0218100c080705030c0a0b040b0907151d0307030501 67
    0x1891017001c00d01160302e514000d400c0c6542e00c80c003000034000c514010146482d0550358030204401200178107000c04003c58880d04080d00d19000f1490203181d600000b02c80c00780224014400c20442a0000c402d50301510101c03001904008103a4200300c40c5182140f03400381c0f40060850011960f288180c00054a200f12051107240903160b8a0020004004140e5000290182882800000781c80303640102041c0c4500410550125121400a4240100c0c82240c1c1040d5000241c010200300350300c60650654100100030342440d040e603a4001d840003000508a00400c10005000c0b005580100404040701888010b06500d48941d04001c9000394000000140803c0f08007070100071916254034804c1003030f01999a219545001c560b41c20305c142c1c0040300111200d000a200e4032445840422021150074003440320400c481c10541000d031a208005081c0b40c98070f41101d81c0500000023103522030030507100315107400c82c3c4d003ca8003281d440b200319510741d0b015031500403451300006101c4150401f94060446840 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 215913588 1250 215912338 215912341
    0xf08070b1305100e01060512010b031b09150d21020f030c030d020a050d05040c050406092309030c0724090e07050d02092d010509010c11030a0b0907060305 68
    0x255040301e4651844000e005500100d540c0b101490a07030801c002040b91400085102c1707442d100010002034800340b0902e016955500c0000315450304000401098140d050f80c10040e5500c00702154601000800b4104540e9072004400b0b050746030100c0a190182e00016032403800150512040a1799907200c00200c014451007200741e6140780c0110445241c00440300045280421485511000c0e4004084100c01e001301440841c0b100c0b040c40c0545840390f80f06007542101182000c00b00000c44541c1c1d0440c2e0703001ca141c203940300c0c42d800f40d0b0f40c403403001414602e00d1038410b91b4581100d24907502c0b43d0182c100e02401085e400192199a85414002070701988400c107440f018044800ca40300400c51180e110140d99044c040340d804d5000343e0042c96021a081d001520700249200824800c1007100e094403100c204000240c0400c4c0800300003071038055400d10300903150009200000701800401c120241c01d02088039058241036808200b1408216404820700421785450a40c1c161108003601c11007020909100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 215914838 1250 215913588 215913601
    0x607170c151609030b0c0f0408010507090b040608041b0902070c03020f060a020703110303072112060803040b030c0409060312020f1c031e050a060503300304050a0f08070b 75
    0x2d5407903080301890781e2072820301c0d803660b104d21010f00000317881c81c810702e0070401000e0b842d110900e0007000a0312088002244508100c14020320803072003607010380b20100c0d0a000c113100316030b4090340d10764205c0d070400300390081403442030480c3c202c054266011034900e030b2002420900304003280d100700c1c04490089071001000600407080c86102d10600c0004001608a41c10a000040b451140b19004c150094200e0782401e08581d94090300284440300d80200340ad003c205415855404000c28035001d0b060070043c007a081c0740c0001142d51340180d00607042e40c0324001c0b000070310451401044d030b0001d14881c2028011595641442c00030814448031050060007110310206441000060107800b5a184124806007495944800c07001050520f1440d2114042140e9080001a9502416000c0c0300301c008009421481c0508051528000180c00c803602c41e003680e60b40e00708150307040f4481307031316070b41038000740e80d203940f5854594140a101c12000386181c042e88600030070302c860240a4404144034040031601919440c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 215916088 1250 215914838 215914861
    0xf05060402030f160509090f090607020a1110030209031203010513050903250c0305070602071a1b070b070308040204050702060415020a09050d061a0907020703020607170c15 76
    0x44481e05500e2540c80049180450a121380c84816619031404900300340d9000300284446ca415990340040f10102c209100b8003e50900400e0380081076400103118500701a40e6803100f9504444c00184543e18007002c000c1524080d40403640d4404000381580c041000820198103035400031f02425003c0c0341e103020444e04800440c0714650244040100840c1400740301080c0f29030304602c00895425400304c0d802c0c0e407000200109079850207188074201030710741c1078207010000f840d1050941c0582464840100703440c540500637002c40d07500801c045080148124030f14005407806000da40066125040080c0440c24584d00881c040d0256100b107406000f241c60b00b010490f903c12013501c01800c0c4026414202c0c03907910b25580202070001683c10a060000e41e54400500090041d02d0182c4000380c4801c03441c07528000c20003180c2c0310702e44102c500313407800d051495009683e4a480d003c000d004910010302c2106100c900504a0b0704991041c060780c0c0c0d180850b4002079210403190300c00e1740503600d0703400c0826281c07941d0303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 215917338 1250 215916088 215916091
    0xf03010f081207200306040c150c020a0506070305130b0408190302032b1e0b0904031407060f0606020d090609050f2710030b06010207150e13020c010f0506040203 71
    0xea85030b41401590b40320b040440000300455001c8800c00145084d480e142441160f10982c000c030b0890400c0b914100d0700900703004500d10440100b007544100c01300182c1e101c17240441920401d5038980e032600801e03c0d06a960307215512030404003140c0d060000895401c20350040003915030210540721400b07207030702c21862024020f1038020f0158100340b1141010041090642c43d0b0b1682c1860413006808030b840411b000c4458411402e01d5003c4107510b075802402240c000d203501c10038192840e07141440d064400501c000c5440400600c6210700240300d0045c00402d4104055800f000714040001c66a2400069501c1d89010400004580d6440000940c01d01070240001142c03406000e00e0111000a800c100d56001d0302030b140710300d511680c10924500000c02d40d412341319240301400c1501d81410343c2000d1001120080201d8115802000c2c04c0c4500051841403508010440c14400140e80c82d400028231341c640d42a10001c8001d01c04200c9040040054110b1085180c020308100700700d0700c4480c1030000760b100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 215918588 1250 215917338 215917363
    0x40204230709270f061502010c080114010c140a0c0b09091b1801090801020a08010f240c14150a0e0604050703030c08040b03040605060f0409020d02011809020f03010f08 74
    0x200c904090182d06444c1c0001902100d80c030000910305440300d9540e0756075244130120000503999030190341045074100140c0c0740034080400942091904200008240c4a14000c0003071031420395680c031014a4404014800d201580105035114150311081e69210ba07070001900b01e44203000003408501381601e100121902660743c1141245171160400404003048080b0801c00d04002100030001104c51080c8003071b04c03e610069803070900c29450405c00042002540e00070349495425860f40c1d201c21040e0350300c00020f49415040402e2408001d00f0140c1d0070740c5000380040301600070075034102061040011024403038a101c0000700007032990401099520300341105c00a08940c8070003070601c080b0b80129805041c0501c500017032840d041d21540e100545801c2598112001a282d0060116518000d002440610401c3c3ca007009544203540000c0c010084460000c0d045c080d928121000005c003080301c1e5000b0344035034041076581e400001503042c6643d00910500c04540100700c40410305ca540869500100d49 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 215919838 1250 215918588 215918639
    0x4150f140a1d2d0102070315240602030304110d021206040303050901150e0c0903030a030e0118020d1407050301020c0a110f092e06180626040204230709 67
    0x15900e25030f4083c1103028a051a0540c07040035000000503c2c2d040c04029038080b0950045480003810242d03074400c214141c02080c41d200b9074601408810ba0000c00e0781d6000c3e8021030f040200c40c0b00f40340842d603100c0301c00a002c0d4104860b12a00068001c00049441c0160312a5074200920b641d49071409089030a10007200c00d6010b0840020040301140c1c030036081e0080121a415454020b10100107895640480c1d6041c0119403100d6100703d280e0020310801e082c00104160704521000c10f5800907289100d1000300500f503000d000c0e180a0708401c05c201400181c0b02c007034021541c8400482250382d8035446018110303500149800c0c1c40b0100d0900074107030000200080c280c06000d80701c0c1075409a00145c40c4900031400d292014904034040030a9440c03000034001c50312000380050032110303260a109219088402400401901c00c10181e81340b08209110601d4a4401c1105440d244001800741101504e07040540300000c01541c0071280021205001d21000e84034140459521415800d0740342d201c10545081c071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 215921088 1250 215919838 215919889
    0x90102100b1306030b040506011a030601030c020106032306100614070f0807120810050f13060b042c1003020405041103010e0705010e040204150f140a1d 67
    0x84000307400c160400c01008201d4500c4416440d0382d0701c1140c6050b0b0041e603141c2d07100b070144006d0107010701041d80980182e0892055640c0d82080d030440c184400b0740641c3c1015592059500c003d403003948158042d5501c0300105c411300900402100c08442d04e14520031182c0103000100d42c070401101c85803011140c4075152007101c501e07104400c1c4120b4003d218203885480780000401e0000d045c50008201d05441210301e00766030014a01d00408000000704102503603520000c040c425076880c0e40d1103105105089900c1c4000c0c00381074010801804550380a4003440b0341c08940072074174401983c0c8030f01c8506010071944015414401030501b14403005c1c0c803c4242c4904d2003a0a0000d81000c1d040654028081e0010107103100d003120110b03085a09480ea1a02203400c4030b90300b8003496074890f24404060a08030707020340c10a410041040510b038159002c10301480402244403903002d0060b64000081550120219103a00c0c09580251107040f005c01d40895400400180c400356140200d02a0b2003a650741c0628680c070b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 215922338 1250 215921088 215921113
    0x504050604020402090d0501051609050907200f0f0c01030c0203040f03080a1407150b06070209010b0307020c1207080c060403121409041d0f010236090403030903080c090102 76
    0x175400542c006400003200d0002c000422400d0040c2030050060b01c100704030a0340310800050040c109600443d100304580070a201416034000d074200000750548042030b042e0703900d45116615164120502001c580506400c2034400d07540414940c0d22504203032014407000b54044e00480c5c40e4404d42c0940355210300505000d1010600c20b8018022005550501d00081c65541c03044120300c0c2c0114508603110303410840c842c10500303503d0040694105065544034140b80555000409402d0b05000d00c041d155004000506030380c2c800c0160400d1540c0242c040c4000d12800d4681c2500c500c003d00481c00c10b0301c650080c0b1610390a00701c0803141101d41180344c0c0c0c0e4402028510071282e030001d00581550096082c0700c141441e0b911803181c1000000084003c000030400040c489090080a902100281c1d105002c88050501c1c50aa4849081000e032900d5103101420301111484c01200610103402181010402c010140c050340b000d0103c80c0a9124031070640c1e5900b240da9064450240701900507049400120321 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 215923588 1250 215922338 215922341
    0x9030d030b010519031517010b01050a05070b1e010f090b150a0302160204020408100b030102030c030610020f01020a030501080c0f0a1a0c0102030a061a191b0b07020606100305040506040204 83
    0x10780f13280034075000c2a810400c0000241d4034034140c008510700741c00013503107440ca03503400d100304a00303520282001c504151000c48013802034066103401400c05400c80d00080d400ea04410360003031a600d00c0c000800c48658560524240604041c0200580c0e5464408004064606508044a10300706441142c0c544290300904030065042481800400c102001c21070300140e4550001c0c002410b0104000c10068040d101880b058070081d204450080e4270410500403c0400401102d602c07060a0781da0040140685804900e004440f00100b4129407010030000e4a20b030381500103904840e03072042141c822140c0c1004000d1040c00014840f680b061200e5020401100c05140c000c9619940640d01070400c1c800900c1c40c2d00b664012240e000c0300700da07101c3c03007402000d12495128a0803c0d242c910942001101031182c1442d42d01031803008240300d80b610100d420b54171404841c1549039032181e50201c06082c43d86c0082e5803079a0548000d4132601d00f00380b01518181c8a4400c00384615000f00c002d006503202c0da002d020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 215924838 1250 215923588 215923627
    0x2d0b0604020c0114040302030a020d0504030b04021c05120307080105030c030a032712061404050712080d02190807171603060f0308030601080c040506030a050c0d0c020309030d030b0105 81
    0x400c079540784e4107041d01c0b0100e5820090700c505c0c082e030081e6a4520540400034140b03034040f1120b10034017100384000d02c00710b106582060740c010750640349000e2008440e2a803241c141145000100940b248010b1040c800c2c00102c082c0d801390340b00307403100702c3c040c0d0300c074030400d80c87d40b0f040b03409240c0542c0148041c170082403040c0820703240420354804641448030b588650350000c02642d004130103c862a005179008020051040700207520142c00984098140356840d5030b211822407107901e403a0014900c8510038040001c1c102c038814842c44c03c04540e50301c6003510f080f0707049a90796600408984110001803850740110a072108240700001d80d4803542d41d502c1c02103142d5540008000c42096038495020403868a4124580013441c00390680984034a40a8001480150018410040e2500c00d0104000a440e180c095a030014541c0001280d1a23940403440a000c2c000e070b8155404007800e060030105050380200040821380c07030a80a0b10011045000f043d42980c0b10740300d00c5400258108100c031011381c2c900c2da421 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 215926088 1250 215924838 215924857
    0x1905100b070f02010917060f0105091006050915120610030c020703030c08090307030302030d0605030c0f0609040f06120605060301050f130c090c080603010e010903020c01050c07122d0b060402 84
    0xc03182242c40e042c0f04401e08001251b0318202d43e2124060041c1c10041e42042401000e08a0398200c080ca46080415911665480392400b8080b02085802c801d5456080328000505d0a003c066258920b4034500390300c1580c01c0d1000c5010f902440c14102d1092301c84c0c010140005110340003008521702e103680071208001c8840003034459141c1803100c1981aa003d11800d8011400790703004646030410515803001301c80096201e03a100358046c1c401010140c070340036641618064111192501c0350000d00100d4050200c462100020030f142100104007400f0300f0740b54a20300c0e030186004000c035136110310a00d4225071050b5400e055054aaa00050511201c45075501c80030307116025a0b0070190351201200306581420f01e444010130a210100491400d0920503010b1421162000780100300c1d640c2c0740a901d03000840d41c03007410050000340b120b110510400104000f0144913013820494241824440c6003000030020220803037410450301410340e52440359500070240c01000701c82c51500c0729000c01c0001d50028408 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 215927338 1250 215926088 215926097
    0x5091306030825050d0c1208040c0e0c13060f020c0d020306060f121501060e0303030f07030e0a0b0a020307110d02151008060708070201050a020c031806121905100b070f0201 76
    0x400003601c28006000d00d41000c5c1c8803100c01b1200e500c1e0840d0304058007122402003190b803400300008104042c0551088440120312248c054903034100348a41441041040c00104d1844400040e92990002004003401c0681e400e65010110f603000300035950000b008003a606900c50400b00d00c3ca032504003020552141c00410640e444030014800c58181542000e41c18401c0480b01c004004183e0402c45440c40188200c000d0f514514007600c4040c035440c07015207540d00700350750390b6100030008904000d0111000d8010f401041185407600e03040c40030f50b1003124a1800540319201101c0058400078050200c2425034026155105030b150420101000003417120755031104910000503000c2c418020140a40d10547d584002071600d000040d09485003e841d424040740304000780031111001005940000b1b089101154a010355080055540e0003180d4a0800e91154082801801c00d803000b416044520140018810340d6941180c000e02e9001303600c0f5040202c9010042480001d500010b05814203205040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 215928588 1250 215927338 215927407
    0x307030f120e120105010303120b01050a081b0403061a06040f0905130c0602010506010e032e11120a0c0801140105030405150a0c02010e190f0c0504020a050913060308 73
    0x3810400386a00f0112181c4d56410042c414183d1100c602001010a00309c240b0480c00e820f00001c040384903030a91403003002404004a0b400c03594041c40302c945503100d403458a46560302e905086000744007544014014001401c6840040e090102c103032001c440801c03a10464036864681d541000c2e02004107010712005500100a00058030b010b00d20019010a90000a052030948009000c0c00004884e05100b540036140c07601c42500c062495624061119502082c2d640d1f0b800c9224019003404240404080404541003901158040c1100c0c4961043c05041c822004022400d48100b0400c3c0145c6030840c1341c0c01044411075006000554000d84200100d5511840c11307450029091000c4e80c1d01e410386511000044226542401600c210b80e24950203890101c11154000d0780b0f00d4900366001b0512002031240038240304039803807030800030503029100750750380c640110008040317034080d00f40d0900c619428844607c1840c03107441001d00756580140320510b840c43c0b0310075007918800390380f05000500e40c1c20340 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 215929838 1250 215928588 215928617
    0xf09080102070804080105061207150c080a180b0c060a0c020c030a06020405240d230c041502030c0c040f090c0e0a0509032104030e031c09050307030f12 67
    0x3006040c920700503a880b54485040c401d1450a40d8005403e1501c50031680c10132102710780e4086500401c584c0036003020b90b000b500c400003d45116000f4030020304106004108034060640065203031803019200d840021840340c50748040c1926014441100740542e00c00000507165540f203500c40401c1c0c00c02c600455031540c030020002031501d008410300300d07080c540202e000c0246091807020306408a9580303103803901c00c98004c2c0c40c3c03000a000e25100d2201c1541ca40c10010850000e108c0120410506215452030b0742c905550b11104607400361003500b0b804850020011349181c030110a07580840004406014010690310411028041c0420200b1101c0e58400c0c010001802481d03030b0300f0040a84800310809880c1840d105003c88400803e04240c1d03070400c000960039003429181010382c680100a40400544907420110340c081c4050004039090700c1810081c1c4e8920030b0789000d084808507070369511701d209519075007419144c2c078040c8001003148180d041c448001405141c0c08002510843c9881d102040048 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 215931088 1250 215929838 215929841
    0x90b060901060804051c1b03211103060f0402130803071208040b071202310b040608040b090709020315041a011b060e0616020607032d0608120901020106080604050703030f090801 78
    0x3e5100300c021616440a02d440312580d2701d11098580d92001e400c00c1000c0303940444200038480240b0b014410a030441d1083d160b81d039541c0c152111450300c2100080388948032244d403a0741c0d50290380152034000794001c000341d05c06c2c842c148044c492540902c010042e03072610320040d12032450540c400c0700c10f1343d024851082d401410705a4206118961400d151481a004407030816490301c981013450130380350400c002c0c050190003080483e04203900a02c40a101e542c0d918201d420681c040c0c02500c2890700000a0080c50f910030301c42c80b1608141200c00300611a03114458001d0050154442404145201c200300311100c1250820010a0700600d0041260b04540403805d00f420700441c1d0011480c010502890481c6030b0400203141c3c0240242401c003d00d01e10503d0700c908903404030091002ca44040316055403000c0c00c0b50030400081c58050f003103441101a03143d41401941003459494011340c038225000501c41c800040503402540c0040151040d00d00f19181113a500c0710300c0e0148010321040504c00208070409 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 215932338 1250 215931088 215931137
    0x20d0615060e0937090606180e06180114040803040c0902090310020f1c05011805010e06040209011e020a0c050607031e09030204090b060901060804051c 67
    0x8064103030304050505401510001100c449640200320001c10810203500c1031070500345940c03610280750401c09240030680c0d40c0c0b540f28143c044116003080303911020402280c010303200b5148075054031140858403241400499800032590704199019202084101c0c0703001c2901c0010042c0758001060a0600c0010070000c5901920110f1318020008100400d010f89181c2c004081d10500c68154034010607000080c0d0b503408081e11b5042c520b503000800f02a00129501142c0d030203206903501c261607068488004000b4035092040320040e00401389010100407461040b01e0590b1921a007444083d103944060000039000070312054103000312849070390450708061074698040026030f40203149642c40c52500c548001c4040e407013680110803c3c0010320001c5d80102e14400d41103841010011405402c100403640342020780e002940203490040d01a00f84658603041c1031055105030384a1f9001c1e42d03034071001c940303001007200c01404030741203620003060300029a000290303105403900e04142550008201c130050900b0303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 215933588 1250 215932338 215932361
    0x12090c1a07170a0e0a030f121119020a0602030c0601030f060204030b01180f1a130204121a0105060901120504030e040c031505010813140a0c0b030f0615070303020304020d06 76
    0x2c0120700c90032520750001c0191401e2000b6102d01910501d5544d0305d1071020b0405030010558001e0b00542c070074040c49107541807603580443d002c8a0404e8a4031000411a40080c1e60990081742000004a000c4d400041102e0070310941030010300303c6038a161142070781510751110848500d6020003000010030450082140138000750000004008051030f586400c58080040c1c402c081420a0441c0c1c12070290b641d10503842c44070540302026000301651000000380b0070340c2c0241c0866040803100c2d4091001070030070aa011004440a482544d8a880402c4141e025000c10203000400012006054552641009820511a04180b000b42c540b606c0000c0a0b200c2c01c02083d400259180b04c1c0541c11665403d070900144405e092070581410f1405000442c0c0d14500c40203800199214440000d410003084504121600485c3c51030700030b0340341c00140216034000e4400c40c01c070051f035001045052074041c03049111070402c108060326024042d41c0540203500010000e0780c2c01040c100c1c0719070100e4407901990300c9140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 215934838 1250 215933588 215933633
    0xd020709140c0f07050c090711010f1802060d09020603040b0613050c0a0c03110609160902030921070212030406111902010c02030307080d060612090c1a07 68
    0x80c203215541049030040050340c4454110103050209140700302080310404000503c2c00c075550a0340e414040c3c64049607011070390b084481c0404000c0d980390320241000c49001c3c800020f0000b055050540b00a9840d1441c0300e91503505032200010061501070300034040104207c0d40407030340503829000610642c0085805a801e4280c0e0703410820b5074a4980085401212aa1010040c0703080c404010b4a5600542c6120700c240254a0000001d050055041034100081c0030300b12500d51608102c440e896846103a6400d4144c1411403002c20702044034000d41348a8905807009001090706040004401c600000d03040402942c104070200c0561902020382e210803000c030004541d580e240100007461140446014a0507070840510881603203501d1009204080c0c091812071724504050000904610030240018600a400142465a006503801c114102c40785500d409281c1111468400182c840c3c41e80014150030708041c0600042582c0740c030003040c010103002002e0802440766900034584a00004410451 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 215936088 1250 215934838 215934853
    0x50d140303010f180c0906030e070807090e07061e050a050913090b0604060501050f090312070308010503011d1509070b0f0310060903050703030e01020321040b060a080d0e03010b030d02 81
    0x19848013071900101c410f100002c201c1244082070007400400c01d8060f031070030580c65002004111038100507942c040d00416043da2580c507901d0401c24000c01654ec1a00c0c0c071809084c80c00101180641c681161030004005070340d18402c540c80007200d042d8040c0e0300f000d0500c081032249407900c0e200c001c01c0b81c00d02c407089000000c0101c09810020420314005002d94412400c044081c04682d80c083d00342c41c00004414002900e0740d100c080003e04126a203155803410480100b030341d009160b44001090304032681540200080301c01310741b0b4a01d640c107224203104034580c02600c038038900c0d009001c070842d403000030310b41503807000f6480b0000084168402c1c0301505560f003020040c072103d0300410b1888001890941003201100d40b030740d0b03103d86c2c039032100303120150502c4020311200e4181c1e4002d2003200c2200407030b200e2540d01d0b85100202c1d503514203820360342034079003090714400034800c0c0c07c102e005441500c0c2810300500034100c0410007100d4444034001416019500c55001c0d03041610100f05c4c40050200e81d4001e40f148 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 215937338 1250 215936088 215936099
    0x5120f090609190204090c1203051903090f0f031103030903070b06040213060503092d0c0904030e04110702030307080c0f070605040521060a02210f01050d140303010f 73
    0x20003402801c2011643c00c03c0c05880204198208a0000940d050700c010880c0300090034400003217078032540007070782408221485808065021000344138101e070000c003114129418401c110100c9411002c001c10341c034003000180c00072600c842a00440c003440b034580145c20600c6407070f900c0e05541041d180440540d00c08221070f41004003189040c0d60286041e02c0840c02d003c0070800ca611001038a1180e01d00748503000022519501041c40154004040640c200c507424000002c0800c180c0d00c0f140160480340112036880c03200d0718040540e0342c01141c00d90703030b1020280724100c02c200040c0450650b401c2c80440410100006860920107000349900541417140c480b00401803c508088000d005200075402c007020500110382c00005403400d48406842d0200032904513000c5404008001c030003502248102c4c2c0c1000b42a40803500188030b207030110302c20b00305200721a600f1034051304010b86d4a06162800030006100c0e0303041c02c110320715115019440800031051071640450030756000f80c005000c100c8050b07000b48038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 215938588 1250 215937338 215937343
    0x2190509040b01030e03030a0203042303040e1f030209270d1803031e0912061b0c0203481008070f140408250801090b010603020a05120f09 61
    0x40c02d882800c05114004d01402640e40381d00c0014244c01c0c8995001c800300d014080201001d43c003401002000e60440090324900581c3c0c0c0d00144500508030009400141000c85182045080b2690000e500300c2254290b03170820140001c010404080351507400002c1000d00303010002e200d110f03242d07013024180d032071180680106155070020031100e0902d4041820000294000008111104001c13446403071010150001c0740d2050700d80e445010b13200c02d07403c44071040c0582640309244410075a05040c021074080242070300e8030444080085c1d4560024865030001c07005016104004807502050010518000f01f145044903500e0f409107200700c040314171110f40c141440040704208054906024000b03161aa00041c20000b00c0003070001080640044220303040c1c02070064402402490003512142c1c00303202e51254803002030032204c1c024602000300000d1126018815031154a80022415000f82c1c01c095094002c4c4d1301070704440d010081308000d644561000981000d00542030042b0104c46030505004292 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 215939838 1250 215938588 215938601
    0x3190c0501022a011808010c02010528050901060f24020a08030117160b091f02070e0c040306050a06060810060f140408010516020706020f070b0304060219050904 71
    0x241598000700c041c1c120402d50074003412006406943d085001120180100e500030080c400b15601009400c801140c003001c1900880d0380440603031300030000f40c0e40e2014003402c113149000b40490290309080e008a200e90441c3c022545c0140c3c490300200f180caa070355256603038541c026880352006c2ca021038074602d481e85456204000c50b0f02d0030b1000340390244a80d100c00402d0701c810b03c01c40449464070b42840248100500200c009880500403044d403c55551003940419400b94205c240b003000c0d049031130100110700502c1600440d0f055402010590308004801200c010054088100d401e414040000007072124041d251088403682ca000c02d41500d0550080c08070074001d03040a0310301ca040c040c103122682d4840d0100c2510f00291034600030380c4028034183d5105209641141e0300300c2d42050708011840000c0b007006400d441c400c0c2d007122500c5641305000c9851300020400060700b900042001c00003070880c8009150024000c500c014602007034901c2011400c81c401d00d0300700c08158041802099840d0610861 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 215941088 1250 215939838 215939849
    0x130b0909120306041a0909031306050f03270d18050108160f030e0604060605120d210b09090c090c0705030306040e01180b161b0303090302030903190c 66
    0x285100030544403a11000c2c0001050b03540207907922035908101c2980c102c02600540400351041c401ca0504400540e00e99000c2007038001c0040b20142d0014005206000300c41403940e4060b00b5500b1a110b02c001c1c0c001c502500e9441c100c41440c03441c1600003005062058003491007044e16a981960b0180303580e01d00c5202c10380c0c896818007500d9000c124241c45410301c00d03495035905240c04210b541d10010254004c0c8020f0140302224450041000100b03c8641e00ca50240e0740c0441d02041c284aa040782c0581e60851b06010398000b0380d01b20488101404040e030040382c1c0c8070001c000420400509000701d4035128048828002d1035000080c45c11080c100030103510340214010f80000c3c60081c0c55100d03540c0e24171014200274065030740c0ba0714506403850301b03501c000b5031404c2c10b0700000425402820400500c28043d12024840d0000060f0382c10614041d8a5442c0e54281e6244103050240068800340e00134103890f00146c096000030844140c481c1d4017842400d42004540e01c02854144107402d1040c101103154208 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 215942338 1250 215941088 215941093
    0x80d020105010609050a05061815041d150303071101020309041109040501080c0102070e1b0a050304120903200a0b0309280201081b0c01020a0e1f0f0f030b130b0909 72
    0xf1f00803910303200121402d01e0310b40342010300038a01020211307442e8284260680d904010128000c600349030300d030b0183c0086480310862641641c9581100130760240c0c1c1c14516a50560040082100160700c0e81e030f4400c240f41050040d40d007054040b00109042c0d41407103004028101c000031b265a11890940f15180c0500040c40041c007004c080703800080e40c2c980d403a000d1141c182d00c41c600050840c40c01d0001ca034103250185d84103291100044a000740c4250819101110800b01d001c0c1e0300091548103e01138000c50350000507240001c58644001100519440011500700f80c0080000c2080300e0040021401207810030020110414203290043c18202600c80c4030b502030481c20070410140c0c1c0e1065009410495000124101a03440028500544500f11003240c0399400072a00d146507540114151f8403407442503130007110340b002480401c2c011002c114260030104900c0c508201c9814807400714030281d10302d10301f03001a44404040000d107044000c260b1103902caa8544503c40341074104414150b42001c0d00000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 215943588 1250 215942338 215942359
    0xc030f0702041b0f11071503060e0f1608091c0e0f09040c0504150305010c0207061103031636091d0d050d060306090c410307080d02010501060905 64
    0x2005200c540050300d00c900f000710720700f0307a001858014031044004095a0220400c1c0300804403002c1c000d0050751241000b801d00000c0011803007101c00354070343c0c03207030525601e03881f481c9012100036511040c0103000240e403032181c90724000c0713f014508198029420107403998100d05070708004001c00722015a5a16009440c02c009002c002803040080e0400d8641c1201d01143d0421040625000031040d0750000c0d00d07a41c2000e00000002c1e07004a0b0310000e44d495555000501da910b400150ba80340700c2a02d6280030888501c61035640684a22040c12100e01440041c1140400f0405441400032030a80c4002100c1e03540f0200300300c00300d1240710f50044004828424804071481001c00e544800e603200700b000034444001500a90711142ea40f0a46c0035682c8050100681c03610b50a01c41e104169030300134014204080e000180c9002000301c111342e4511091703180c1e1549404800e2001448105650500e6054441c010002c25403913011f1201641c0d001700795000044079890414014811f011503801980110800f00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 215944838 1250 215943588 215943641
    0x120203040c091a180601020a0b010308090901150804020f04060b0406020f0c0d02010f08132a0905160309050a05030c16050f0607060515031e0105060402030f01050d05030c030f070204 80
    0x101e80c42007062544c0d800985a42c1c40c440140d0034040c0c450401042003000a0002c010040b43c00e028166032a8103540b03000c82607032541240741c0c9000582d45080d000c1480782000500620703241c841407000c800e0240c00828056940d00c00c0041070341080e0002e13400341e04102d518a2250038200400e802510049503e9200c1c440710303400190403000046114010800780a00242c01076000c0320b15070105540c001500c02c0c414540300900808180075054041e028203000c000011680180e000d1076005682400900c07518035007201068000301001d0004030b50318001c455015010600900c01703442c1c0070440401904d900c04d10441407169550503034000c0d510581e00883d40d104941c4490341074501166120704005800d0b11140003501c1c800032080741003030345446580b840c06601c11744468010320210f2001e00034400c6403a44010001a8041110407182c50940440101700314942440040b80c40da02480541c1e00e00382407080207506590011038444905240010804114281441600f006210140c001c0d0328009030300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 215946088 1250 215944838 215944849
    0x17040501141608030703110714060601031505010c11090c03010e0a021201030303050705070f03050408010f051302210a0605060901051c06020d060f0807080f07061e120203040c091a 79
    0x319015011800c08800684071601947c0425515500c4e8086c1544440062a01311344031070300b0b100a46e84c14043c3c440420801c0d40a0300030708200550540740d022010b4100001110780281004090303956901a4100000719280c2c1791170315010320b5607000d15581d40d60400b4002d2480c2a4058108080e66204012100207010380152190640c1e40c03615001c12991100581150f05010b00100504000701d0800c0754000c26170010300404c1154580402484580580c5005030b048690071100152010708d18004000140381c50405074440340420648288101d0703640324850b1030000d000a080318525951402e00c9081d16250030024014401210a01122054600d4401d50170240b408000d1055401181540951300141c0241c0054065a105d00183d50b9a69944907a1818103204240340350096141d02401c580000c1204015601c0340c1d03e94821112032100c1179038002014a0501042003050020307440310360f0071800150300070b60003088802c4500342030860120898a08051201d2040b2000042d03004540340c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 215947338 1250 215946088 215946127
    0x112080313020402070237060e0f0619020d140702030a1103100f090606050f06030c0a03060b1b010e0102130905100515040819032001091704050114 65
    0x281d1800d08084922480418040d02130910002e5000409001403d90011074011103e212a8818084d180c04121484188100b90b0345000b0f002c0005e01c0d4a80c02420780c188088805038802012304800c0ca0000c00c10b00e0f0011101c2000c4403480143c002001100102780c6c42410a0120112445c0f524503004403640003a903074040400c0b0080110707500040703040f55617805001c400540c892080090110900035450300c00100361281007192603614188010a07541000b413048031001d00007810042c03454580d1a00b0301019008901c0c0c0504064031101d01007a101c40038005002d1482a20304403001c2da0030441e82c0f440c00c5d1000007810440390380c8140498148011450400d4007112600c3c3ca0010f46515818003104040e003281c1c000e540c0100500110003c0761400300000c000326075905050356424a1410100300e904810030304050000340541b001c1480b001c6506a00c20b00c01c0c00c0d1440000b418a00326a52252407200d00310f0040e00e41c03140854200100d507000b40c884050005400c8100e8600304500c0c0d00a80700c4001d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 215948588 1250 215947338 215947351
    0xe0a1b0f0e0703060806010605070c09060308070b0c0403051f050a11030a090318121208090303040b0a0e0a0320062e0e090714011106070f020c0603040b0f01120803 72
    0x980007142d9168040d40c840da000e01801c0055071000d44c0c4a290241c01c541c450f01d400c41d01003044180001d080e154500c1103800381d80d400200246000f00503215015403641c042d22001446204000010028404020540501102040c241080300046011100300d03600100f00c443e040d824000003040b40f619000840c0c5c3c6c0b01d140303100c00066510b03490404403409810360341c0709034203241003500201c2d003200c80c6d090001506110302c074000c02541d0080000c8031001410380b18008581d00c144003060008404009641e40301000301c5002800060040c81c580c03038400d00640550105001e054405e210300c9804c1e0b803942e0800701c000300034201c034142440007184042d4250351401c0400b44200890280b0450112068014402400343d2121400c02200c134544a00141c800e010b16400810506581d03540101c0840c822a1901030240c62244d513001425619103400e41e2146c406c5000303914040f00642e481101560080f030081c2d206054178030340441440200300c4107130000d003000301030b031105103000801c6242100d030b0000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 215949838 1250 215948588 215948609
    0x90705011809020d06080c010f080a02096a09081e0607031a040b01090803120108010c0e0306160909060306020a0f033803010e0a1b0f 59
    0x1441d801450107120aa00030040c290700001d00c041c80345689802503000e644019040d01e0302d0b403120b02c00660301b0342055044a03000c07503c0600050040c00d540d5001e0890011702804206a0381003040d42d1b0b452600400095595507102c40408100c03400c480d01e18541ca81c6800b0b540c01000650f08140d80e50254540b5290326824191281021501445103850320000c0a00004640d01c04e110195200000c02d0003409190780e5114001c0002c3d08248240503902d0286103001c11003487c0d6000c80180700151003185d8485e03044c443c0100c00020b800100f0070080c00d048040040c10349895040c5152542522100c0414604100324524800859900800d101c1d8001516417040e09040b1440d6400b0313180036009910801015203041800800c2c07207102c0d0010b088092843d95441e40c0e0403146d140507401c55003c1640c5085003080c0e24422440c1c0800030301c1941001c1210b005030b41113120380c030000134250742d0f07207203184522030700310100003030812a2494082007503420400b017070032206040c0384071098000024841d10710a003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 215951088 1250 215949838 215949857
    0xa0c0c06020306030703120f11060708161413030614061f02010b031204031112100c03110309010b01090914040314130305030405150f0304020609130608060106030b010809070501 78
    0x40e40c040290340c1c01154000b005c07c0111000f000b019203c0041e46030280080b9681551812081c1004a122441008161240041503c17412081814940c5d03510400341444100d410514420507000060040111a11a001c000c1402c5280442c241c400040000c2400c900c85401d1000c5a65481481300f002040494005440f015041080b800f4003808000c02d5014003684000303200c0f031450040241f040d64000d25098a2039542c0c4030a0002d02d0b4500050000183c200e5a600901a100b6400201d0036040c0c1d07180101d02903e841100000e20340c401d41e2410266955200010b42c41e5812003605001401503010070412480350f850707a0405000e000b440201000300c0000110016940903054481401c4901000c1010707035140c0c03401075600e034418050544280201c0200f8055808800c048440072302c404507000d421515540d00b4440306e07812048542d0750003620900c50f404a4086403042c04010301980300200400e52509102500310383c81e8038855030400c0030400400062640010740c06e01110000e181440c240c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 215952338 1250 215951088 215951101
    0x50303011a190f0f0e0a090e01020c010e0d14120c071e05010603060509070b04150201111c060e150f0f040207050109020306090312010e04020102030d0e030d050a0c0c060203 76
    0x19120b180b00c0204600c02c020003081d4034540c410789408041041d901d03501c80d11030500c0030941d050382d0b0f00403480d940182444400d000b403032a240c0048490100840000d400c0000207611242035617034090030441c0769441240320000700380d84506818112512040303500d2030110000c044860105004010208400c00024100200204900c510720646c00b41407007200404181e1509a019102900c010703101c0604200c041610755002040c000200c81244520600e454503102c40c114414490610650965586030b00000c0c050002c1c00080101c0b903012014030f80d2400103040250221001e603040050080700100401c06201086506000f80740320840c2c520200003107020014040d002a089980d80290020134410100001500070641c098401c406803900b030b035100c212132656805603991143d004a035440042001040c941c081039045401881600e1411102031550707020b860000c0d101c20a11750001400140c07040c11846038a401824840081c04a46801301c03000782001c030880c4000d07005a0740000400e91 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 215953588 1250 215952338 215952389
    0x306010e010f0311011806050705060603030a1d0a0e09150a0c090b16062301240c050309041406031e03030a0b010e090703020c10050f010b160501050f07020d0206010305030301 77
    0x744880c0041b00c16140c2034648000800503040100103d490780301d03107000f107440e901d03020003510340401036036903041c1e8262401500c0c035012140300350f58141c0002000c036011800c1c4d008910707014402d10400004000141d0316860300071880c0801040b5100f520f2802e48202800e40e40007022804880d1140d0f681d0341c1b00c81003500c0c4110480f11440b4024042032400c810880700b0b0451010041d00d440c85c41000c012660390751030044400641140000b280350110150b00e569050007003030651482801001100d0408201c0c0340403030122842c0c0f8548541d007c0d031120402446203070030445039204c48801402d1400d20a4804003581d9a0b00001c0d0910f610152144042c406d80c3c2d00c248054800c08d0401080b01110b410925409402944043c00861980c0070345c03541c5c180e001c0700d030f4000c2901170b03414a01300781004da290406100b40c039000307114038020780c84030b078000500841c50274005ea074040e0350140da005030070f8103201c0b10280c9008000c554400664010a0040021900100680703046603000d174451002250f0002c074010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 215954838 1250 215953588 215953607
    0xf0708090904050d1106060d0b07050708030405011b05091012090f0c05030d0908070e0a0f140106090503210706020714070e0109020403150f1503030804020306010e010f031101 77
    0x25007207814001048207101002888200900c0c0d103440c0d015101c40b81c400c0c1e803a00ea0804640264114078020f0003400011001900d0540c0452a440e000341406551b5131900710903401550b003502e46a444000d10100c04083d001209541d0b081400e2040c035110105021848041c1c110002d242440b90308443c0c074403410b045401c1910b82590000d135048844150346024840c00c402e43c090749019104040300c01d01ca5034040d041e25002d480100004050b40c61400080d0040c1c0032000301019001a10788074601c9080506004030501a002c1c007503464a03a6050513002052030109a020603c20b901c03040d2010400e20b00c401422580c1c40740e4840c03060741e9440c0b9003001c90180c8102c01009018100d1004506285a40490094140c98031104c040e580360740d85121170300c103900990001828158251344001c02034039aa0f4003124aa4060190105400c0f00c1c01440321300100030380d4400e50128a92a041208600c0c0038003240d0f003d05202e0480036044e50610000c0050321240e400300034003c001c1030f400035807140c2c000c00703440c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 215956088 1250 215954838 215954857
    0x90904150e120d0b060304170f0412060504020312031006140405090c0406030606021b1003060504060f050103050a02030103052e02040f090b0901050f01030f0b030102070f05061503030f0708 83
    0xa44820742c00c0c1a900701d03981c1c010402c909185151051001880c580f02080b607004940010503074161000500180945500c04403c134400810204030000d2007441e00700e110401140940c4001402d4a89401410709200e80900300c0c4030300700810001c000807100280000000c0e03031071619160700c07006401d1780100181d2003540c114a6000c40c00001700f040001d1268010800d503141d80d03070140011070380c404043e6942c0c02400c40ea02007042551503800d03014204110703101541c43c5030349004924296108045400c43d501034000c401c121480720303824040c9503050b010301d0703410441c0240214550b40c075584850b80c0b030f00d46501c3c800c1c0c1c3c68040e10600840f002d20009080d440b40078642021559a03960f0416900705001c64826600128248508054649450040d0324100c402c050007410b00040103800440c02020894100d424842ea070300d0304240180c400348003508403548280169100024a8203019141c08801840580303540d0400d8855156618003200781c4644100c090542500d4200a02e414032050041075202d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 215957338 1250 215956088 215956093
    0x106051309120503040f030f0c021005030108011103010e01050d02060d1401030c09020a02060606090a030524100b040317121003020a06030e060c0c01060305030d060e010b090904150e 80
    0x24980080326404104040d218820510410096580540703e5003c02c40e0003031321180f841c00c0440301190007190f0800d843c0002c3d2500c4500002c440e40015424090f069010000070700100040c008101c0900c2440e0420f52070540d414103561502c01030680c902c0050103214007480b06008444215110b201c242c07180440c03100000d00584803941e00502c418803091200f0307602c45443d002d0000d03039000e091080f900401002d501402c4503544c1e0b10180035243d84401c7c1000d822036949500000030030000c0c484c411065060f20382e500000100c6201540e854000507000c0e0f10f031340e050001d081043c2d07c01e00e0221000c503035000517103807030ba584505003c013280d00030041d0044c000f001c1d01c003c00a00b01d114919010980b4800c6401800860b01c4d01b000710200e031692070002406900c8100410003450481000e030480146007000800c0c0651a0ba0ba400d095400078030a0702d801c1070310f8000501071034091030000b502400c3c000e540340b030030f0800301c00000d9010000907102030040c3d26901c0401c0c000d503042d5000303100d045041104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 215958588 1250 215957338 215957359
    0x6150a0b070609080412050607020d1b0b1b070c14150403030f05040308041403010c03020a140306060f04060807020106080c1003020304061b050c1b1f05091e030c0a0e0c070203010605 80
    0x10415200d4400711021401030048481200200d409007000303336800b0001b0581c0341c0c00c9102503990740340d401c000585211078407a000e50150b08118040c600a0807564401c2915001040ca4401c0006e080b9094940e40303449507080350b120b0641c16a10806032021031350185032030400822083c0c01030710140304940001e041c5040000b00801d40464482040002a20940003008040307445a0102c049002e0601041c00080e428a9030040302c00169029641107500102850b02e803d20315004c150040c1c0c0700764030040100703015004010302e098080c07052000a10001d0090050207128000050304240d014011000381580400810f060143c203074010703c0e89c0040144104a000c0c4c1c00e10000d001500326064402040c81407012100d045917200341e4081841c00d001d004a030220351030665010341500f602d4802e6040101c00d100008240d03589805003001c200c0481d80d50307d0b0402e8080107260404440d400c6c05070103400ea0040812030320b000d4080f82a80500e00c8407800d515002c891000030b0240072164030641d0300072010759 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 215959838 1250 215958588 215958593
    0x1103070b010e13020a140117010806090f0604050309041e0507120b0303040b03012d0f09060b03061e0d0506240d03080705090d080c06150a0b070609080412 68
    0x34414103075042e020361034015030383e0302d04001d05000b400c5000035004842c9100c20003070301480f8008a0700408050502c1c4040c80d401e00700750246108260b1000700181d0080c0288000c046090020b902c6440c001805008249865140c99649108070306a00740501d0f990000b140d5a9282d50320340100410020005100300e0402c002c0062035009da0081360405649030032914495803900004880844000307035040780c03c42e032030300d4070502c41014080d0810000e0145c174005000354400c91400c4030040e02c65a00b81003a62400d0003481c108843c50754008241ca104100180541ca40d42c2c0d08144420000002c1100c4086140f400811504d48031f221000740a84941000d10034550400ea1181e403404c2400004561001c0c00e110070000c0550703a0800181c0407a407010003180100341300b8401008459405824082c0c204110341c1c0d111196400707100c014400d81c01000a0004078894030345c3d80080380030201c411001d141d0620161021901c20f00c040180004d43d588620010860031409941c001c150b00d005a00d5000b4950 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 215961088 1250 215959838 215959853
    0x903010203070306050307090902150f0403021302070302010c031a1009090c08180102030f040311240708070e01020d1112040b040e060409150507030b04020d0603110604030f12110307 80
    0x74001c01b44640071340040400c40350800c4c030800210640091125424003250715445060b07a1004551885110341000b0120240c3c079142201039a04c0064100160b41c1c0c20f0600b8001d0071078040701c0300e50041500389282e40d0310380d8144020301301040e8012101d0301604a083c0505854922596102c14025801c0880d043d0b2082d80080b426445180601c40c04240d0450701034043d801c0b0f2004440800e030500c00ac070041000300707120b22421828445907208556038900c0080d09034180002e00d0050a5400312070000301f10046a1185209820030b0150500507103402201002035140c050b010b0f042410800180c0c2a0f08103070f0410404c004032540701e0911290741c1c603100d200f9500b19034401c3c0100503000c00c130540440c009003814840c4180040c3c2000074210007905a09c114405002c02030b1048040540390b4002144503501c0d803004050440031100d0001d1060703d1486c2c44aa030180d01407900307210300d405110400124880b01c80c000c842c076901c402c1007000c1c86580002030390b00042221001155101c0400ca150800050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 215962338 1250 215961088 215961101
    0x60f0d14100f0f03082506050c1b1f0b030c10090e0c0a0c080d090203060f0a060501231b030a080403200a080d060b0c1e0312011a09030102030703 64
    0xc065054807a82c1d00e0380038a40b0100f40c240b2000b17012690400110f0245030040c2401c9240310400c0d04400318580386919844280d0b44162441407118800060741215074814090807400e40e140040509480183c0e010680c002c80820f42d81503940030b0700c402e44408565414041401807040007003a0301224200c00800070003020031402050b03410407440c0040b868500d020400d40d0011b25590761350b1102c04106684124880e04499100741c06030741c4072492000103a405011a0348182402441480310740f44c083c0720001600d02c16800907040c810340c0c1140c0011151a40d00c07516442081d40d001c0340e0341d2080700c8a0300c402400a9054280349001c0800c0c0100c800b640101a03500550203903413441401290030860120401022001c100c01b54409121600029800006045c2003400c4041c00144543d844a00213a607601c8920070a0142e044020400d10044a0413400e02c242c240081c01181400d0401000340314252040c014407080d25001101070484100d04411100c80c045c0160082d0345a06001e0b0000d00079040c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 215963588 1250 215962338 215962349
    0x1b0e0a090605060a0806130204060b0d0506012007050f03070e010603020702030106061b0213020d0207061b081009150302040903021b060910051c060b0409060603050105060f0d1410 79
    0x2004003240030b44c5070000b5403200b5108410302800701ca4070fa8010303556a8040d00002242c006440781d600013168851200508101c42c0d5036580402d0b249043c4000400c00540100c0440c1c0c42003c4c0c94802103a40d1780040c05006590b0191407001582c2106c0c0002840c00c1c626501441000c07800c94004151583e041e000381c40c54a10a400070310445071240e005441c80c0c007494010215010744281203102600c0c1942942c2d410922440d00103182020749001002a0382c440f401c1900c543c0d403600018842586c096052007110075491a0040e40c5c2d003400c0c02c50100351b807814413030000060b850b4045820000d180d000144011a401041082080002d146c0651640075940e80341c88000c4036508010f030181850011542a90402881058038210750720702561540c00004200902160b8030301103daa41030b03103101c2e44014200716502180c031249020300007002c0e1101e540181c400c1500b8000100015140c80c01034891790741d0401100c1d5154412484004010074008078400c0406501e1802c2c003850b03803824044c0000b940c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 215964838 1250 215963588 215963591
    0x150408010e07170a0215090d0501050106021f0219050a030e032701021b1903050601090608061803070b0402420705030d0c0207170105010e0105120a1b0e0a0906 70
    0x100310900c54480105084c00385d08441a0251140e035581110001e044915000b001d844840ca4207484130703421100301360010005a030003a408a503814080c1402082310030201c2d8000d40c0741c240c5412801d480c4c1711002c4119802d1201c0420212480c900a4100e401f041d10914100c03501c62900849840d00b03030200303081c6030b01c41422081036100c6951020a0b65a004801c00341d504110ba241701d070a0041c40c1c1c85119480348184141c607000f01c001a010701101e03008014280c40410030300d00b080e6050341842c002400e00d030701c00e01c00103d00d40c010100100c207545101d0303040720310304003960754500100d03141002c061905c520104050000140c8407440b210f00e050010103c0e4130900c082409412001164814090007a145500910803604101c0442d0801c10308100148140c4010951305c400040040d601d9042c034036240e94581c0f00500c001c0b20058502401003004031148040d800c403440d09540c4070303040d108010300107001c00c01c01120940b440c028000014420300400918034034200e960b400041400c0b0200b202c500703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 215966088 1250 215964838 215964869
    0x80c09040249020a0506090a0306022106100f030908091011010b01020111030411220917160311010b19090606030e06010918020d0317090d0e150408010e07 68
    0xba840c004407880643c2d8007400d4901c01c9402c001c100615904001e10311944041e41040100000789240060001ca01e110500c40003990000d0101c0c8104e03803001081980a42042c000c0d9900c1300768048885400040c0340d040000350303841c00f820102068881e43e4002c5400204c407141300b0b01920b9100e000381146001e0070008204c0740c80064012403d0b03a00f007000f401e100f40000e00224020401246010b40301140052030850801c007800d59200300b10445080c003050156031891000140070304c005030041454111641246003078001d03c010240300554490280400c0030101c0048a01c800c04d620116603d000200003500e45062070f050740c1348200c52409002d20840c1407090003d100c134000e005400e88440504040c2c09240c0c20708002500400450315000d414043c881c9807007001d43c49180300c102034240203036507040581e41c0c44c40002c01c03c02c0d0007500f040e40326400404c41901213944403108422540d800c5500b001c0d09a8110720100e00e5001e140c00810030380d46803071a0a030504000003111001c6510418800010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 215967338 1250 215966088 215966209
    0xc021c030e031b01020919080c010503060d12021e0d02011104030201020c090a0618050411030c0913020d06020408010605030708030913020307170c0d1104080c090402 73
    0x19a440e81e0419603465100b4412462101c42e6154040140c0407080001814148210005121404c141e144040b08142180082c440a0b505011905085100303082c880d155091a2001c581d0703d0346050703409401d0410103c5c0365011540b080c8004440c04003020350303a640c088070404000d51981002800c00300035600c0c0c4814000120540d0058508603034058002c9c0250200210a02ca20800d001b4040c00074142c0d0f400c00800c1c400035401d01c03110748125a0b0070001d40c80c54680340045540894901c501e101e588400000034595460040959215a5030b907040f00400b0540e20200310f02c5403442900900300c80c00410041510701c01548464103c0702d0460840c2c000c0d0742d031410102e8076445030134543e507082030540182c4124070605400a580110007882c2c0340c9500080659082100701060341c69100355800060809448080c034010100301c0c52504015920f8075240010136642c400c1040c040358001c12154001070305554510841070019009102440d0103501c1a1012a45044954013034040301d04000504080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 215968588 1250 215967338 215967341
    0xc140103140105100c0302030f03070c0b090303040f08090d0f11011403010b1206010507050a0b16050c0c120c090406050412090e070c05100e0c0a05041814100c021c03 73
    0x40310005080c0c20800034000c1d004581c0d404482001b42d05602c02003100306031121001004612900d010703914264640240d26004059007005041140203034014414040829850110442455485108203550b466410040b0325295881308000c0d007441490b1041d2030520140d0755215010080c2641c4040d03140e0340007000100240800c0c01401c0001e00180070182000d204d503000d81ea000001410320f03c0c10611266180303442c100c200788048030600c00e00c605008001c454129400a4166581410303400c1c84560392405584856100403a84108226507000030f0840e001c0c4942c90411801030035008240c6400d0500c48041c02098408032180f1004201c04031f5014402c0300c3d42d409030f44001d80340c190f040c0c60750b034003c440002d400d08041d20340307024000c00e00c0e03440216813044807544000407014140c4c1003030315801c10084c00040e070f008500603402c004440c442c401c4101d540e13840c0b0b50f134448020b03c1e0000c244040580741083c1c801c504880d0070b2510b00162421a00001c988003010b6a000142c1528004036074104c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 215969838 1250 215968588 215968591
    0x19080a11040c020f0d0309060605060d150906081911040204080d08010e040308040f05120a17010801111903020f030c0403020306090706020715050f0d052203021011070c14010314 78
    0x11054000611008559110740c01520340f1f00e008000101d5060380391400030316a03900620b40c01941550740c40c548100742800004400c000c1003207900c100541c510305000c030380d2120b000010884205551414410070414074140709443c0f04d0000d041151281c1d11147d101d036860038200c200c00e000c50030344d40c000034012030080d0303800d8070840d4503960301112034446a9a42c122030620360350461f801d0090aa107111400a00c030301400e031551295441400c2082007403c0b080320040180c124080c00d9041441000b100701c0140220342040300c0380b01034680d82d003071901d4045009028400e0002c0208200000348190041c8000291050360b00841c1a04c013a030b15161501d0350390710310380d01c940400750700a00010410744400c24000303200d01c4030b00e041052034003d0503018101c070f0b235100e20301c2000e00c96959001c1c0001304100b051841803050420542107000e00d03da45010b0341d1b500243c2402408503031a444401ca500e4005401e64017074035070013031040590940707030300c0b00b20402c4042442140c00207180038201d0380401851401c030b5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 215971088 1250 215969838 215969863
    0x21509010c06020a030905010507020723060403080307091701200c070603020d0b09040c1a040f150309020607060902091608061c0b130203070e01080c19080a11040c02 73
    0x464807408982c0c4280c040d400c002c40850504d550b07030a602001ca802802858440d0856078040c2c0300d0141814500100c0c2100c00d5424030108400c80581040d0351120001c9600f9a600021031503101d6440d03c03022240c5040b941c00c010740c40f02400795502407002d0150048102040b00010380c1101002509044c19079000d00d5041c517106a210350401c00926000b0303130041151f0764007030300c001c6021601c038808541d456106490440701d4069400702002007990065000d40b800d0501c1c45100c2ca01071820405140d42c0d0940c1c09040c4d0345900069820705501d0180e4014004154040c01c503070b03115030f0340d4100380d001060514000e0740071b4061113001617040071034901e022581403c00d4542d030100b0f4841c2c509120303401e0140940ba4040c240d411240c200800c498054051007180c0c0c29180d50b000f0580d6106240c20000e0b541e00c0043d0011039800140000c05000c0f4160307648030000e6034440c0c40c44420349042c0c000a000c0b6400f005c62800f91200180520408404000691070300303031010b11801c2c036890003ca81c1c030b18070701011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 215972338 1250 215971088 215971097
    0x90e0601050c030d05040602160f05190807141606021c0f020d030207061d030430030e0307150e0415120308090c0a0603020a0e0102070e01121a010603020702150901 72
    0x80510300030704e17503001d1500940a1900107040142d446035110780d104040009a0703281c1036980d100d6081040c00c00a500308070038070741280e40b0340036410781c1e403c0a00d0240180003007080d5850820007001000c01c002d10320394181c4030302005150355910400a920341e0b046940750003407002480220741a5078080e070f030740389000c880548c020203480380d666100314001d4102e40340480707826440d010030014a080f8502030640803180100515560380c54405041600c210b4180030f220400e60344124112032070041c211480703005800d41041050713044184002030600034503400c41c884007440e24004400740d0303601200c828205070041c2c0c1e041106516a00c100350b85c0e144544124048486807c0d840e4001a204118042e0480d00707940848513944000000a10003256a8000c0380c002070307001c501c840007039901a08042d14982c00f80060803040d81017603144400c16405000d403010500341c0900040400c15031401c6d1038510700128810510b50750f1a844010f0180d442103609a105400011203202802e9048044504a0405866 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 215973588 1250 215972338 215972347
    0x806010906182418120201030b031515010e030a11010e0d06020301061715090a05090f0118020306252618010501090209211606090e0601050c03 63
    0x404541081c0c1e0920b80324100700d41c01e0000a911011801c5215a02031140d8185180c0301e00010003c19540e1071a40da07089500000c54108214034000414402d019020b02c0d010404d040900301082c90190f10400d003c04110942082150412249051103186c0c20f007640ca64004000c1c080070503a6a0981303040103840d80904041071901d0b036003d200310003800070000c1e02c1c0d0080804c1a40381c042c12a0000d9103d1070100300610101411042100a207581c13100708028498107240c1c0c40d2003c03845800005103055004d50745c5201080740c041c400c01c000c4050241d00700c0240143c40c1304104d506034054805808034000d20502c808600e4030740340b00c2445840d9070050300903092090005003003101c1503052403002c00403c0040e00521200b00c4a41107100d072241c81d10703121004411904074030a03800c65205071f200070501413041c003240b102c561300c1c2e0906820784c080c0c82c4101403510900741c00d15401c4c07900040804240c0d8039010000510681c0001581e405c40300c0400c0c100106984100055515225000f2103950300d803c20403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 215974838 1250 215973588 215973599
    0x106020d03020a05270a030b07030b0a03080a03050703060807060207051002010b1e0d06020c0115060e0f150c010903080702010515010503040212010b1003140a0603030801180906020711040c08060109 87
    0x1036889103d826600c03100e20b0381c0c03444880400e0341b00001d80c205650300c4c0f41c0602040075040c0c060141400e502000d9541c13201040c510303111110708d40a203042d40c00401d92901d001c02c0076207101e43c12400c06401c4000640319080e6803910080d40d80d05991280c580102c140244400e451070043c401d07100c6401c405080300310030441d403091042d136100202001d10b82c031002c01d00b01ca40100b1094030181905807165000011031a040031784280b24400c07981c0c4000300300450140d4139000d0783c07540c5414000810702038079804500b0032054450f0845015144508000d0761074501c0341030071b1681c004150f5010381c0c4140c00070495030b00c40c0e0018001c10460750800c10b0104600700042001414070b43c05808984480e1000018030f04040d0740003a41030a100503045000903196109408103080a00c50300e600036503045410000546503680141082c00140b0500307180701d03d0301241c07000d45c034041d4100301052a40503004641e940c1d01490300c0003100d1214805a0301036481c05000c080668040c0100e079004801c16111420034a00d010f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 215976088 1250 215974838 215974867
    0x204081513080a0305060f09040305220308030c070c0803090a030308041b0602060a1508060402060f070606120c050d24060815040b0601080c04030605060609090405060106020d03020a05 81
    0x1500044407045040303000c2010480d9000640710310903840e90042507031300f41082004a103181c03209481d4803408013081400000781d0000c0c11200782c204448428100090064001d03206081141e00c09001440004100310450034140010612203100c0c001e04682551205020303544e07070045a0b019600300040350700502c003183c040c0d0580d0340e0091080b90300c012030407903154034020400520343c400000369000c0801e00025a5082c022180c0281811080c01d47c02494440503540d9108003500103405a540094100b0f50b44c0d98030350032201d14a4028200b03203da1030356010642c480000000c8142c40141d201e1402040518140580950751500088a0210141c04440f05524104000701c40300449644101c0000c0c0e401c0140003104c900c81e6821078a00311481c1a050160000710001c00550411526908115101400c10240c1d0700341d03500300c034001860b6034584020800d2031180035102e0351b22140c50400c202c100200003404034142c1386c16500790703001c000e0b0443c01941a806090490700c0450002d1210315918000e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 215977338 1250 215976088 215976091
    0x1060803041a0d0b030f0c0f10081306060e0906041a01060c060b04060f0b120109060501080a090c1a0c0c0102070b090f030c041b0e010207030b0106050d150b07060f02040815 76
    0x3d0000b404200c510300003454180507000c40280d90b08500c02e403d1035883d201110705000081603449243d5004548401404240c0c014200c880440103140544123105843d400403000d406202e00854245c2040c42501d85d0b0f402e41100c3c12121901400c40031088114450b03091030498840340c4482d0900714403a55424080d005026501d6000382d516040001e01030882d00d400c000a0080030090741e542c2c3d60740591002d4140050700803060726420320b4001c100030390307009000f2948181807060002c4c1c4003501d031420a0079408550b00a2040380c029500c03400c0414041801040c030344520b4403c403010304060388016038031594148955528050305103d000c0e07041c14600104070f0b13215802000e031002034600000182c100c801100300d8601201038180781c80364194101451009500c42400204400e6246503101c2082d41e005008510030400e01103905429201e03550807864810a83c0721040f80c43c81d464824100281d009003209580076424001e140091a41620880b4240c0705010007428010119200c55420142c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 215978588 1250 215977338 215977357
    0x90b04090c1812030e06040803090108090109170a0807090506040b0a12020f0301051806062502030d031509150303030903090e0c0a031a010822050604080c01060803041a 74
    0x105601000d003000380b681440001e81440d88060342014081c2c20000c10343c2c00719161150007800104014009080c00005550b250329003460301650b03655680500383c7c0945040d0300010901c1d5003002c68480a20403600180030290b00c00c0d0358012080e0b9850341c0440c0c80440d14810140c21140c100030500103040204010b0a418600c0d00f00503140d510b440031014103d91043e10041d14500c40440103000e40d00d444140d503924502d001d100401c15041c51000181e4600c079011718a401c0e000c00d000703840200004840640d404d0340c2c00405a41d038000601402074080c2c4003050010046408040001c100c41000340301f0755010300d41400341840c1d064296a002d50040080002c180c05112410700c0000e9804a0b40004a20814034030199584466030703003602806803001c42c980391503120b5002d0a8030030a0390380681016840003801171602008900000c1c6030607031011403031015207135010701710412060204440080800020b072100030440681c0d20f420b001d40324055402503041d002c6518441500b5031203150013a260656 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 215979838 1250 215978588 215978597
    0x120403110102040f0b04080c091e04061b030903031805060417040513020a090e071b0606090e0106140d022101020f0a080f061c030525140607090b04090c 67
    0x1900c6031310303081888050754455461510000740601c0b0301c00c810310003030003880c0701510f21103180e05015091003030340ba00c100640441042c49600040502045400100c11540b2101c40c1f4500958108002005440d2585003600402d05003014141c0809654000100050700300005d0103441d11560744150000254042c02d0411200900c00400c40381e60b40f80c14030080d070788450350069072848030384400350528406a00403041001400c0400000036086240c0e480c80488103540c082c4408143c0c50503000500403500111061442c2c0403822005942c150b1255007a5100c1030550449484100200b0514440c000c60080d0044011701d078064008490b850702c00d13202c019040000d4103000744180a41e035590040140f842c0052580c0c0c042c0010014200e0001d41c02c10400c0d01d40703100078024046d0490720f80d0407000c001402c00c40300080300b04005c00107100fa208500d240b05550950f10343c450030808001b00d5050a103802c00c2c0519804606100d0241a102c0d0440d80c07140c02d00785c2010b203402e003410005c0081543c01410311 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 215981088 1250 215979838 215979847
    0x1103031005060d1506080a0507050406050f07060609020f0702040612030f08070207050d0f03080f0103030e0114040b1801080a2c0f060702030a1101090507150507060e0303040303050c120403110102 86
    0x10044c080c44080500b0699690440600d4880e440c1016200b0151454082c01010031081c4884e66002d001c0b1100c184480c000c01d55603040301c1c6400402424540e0141c2070031071002c81d801030075a45d000010818107000316010b000c03040c1c031445451500e01d42010020045160080c0e0001154082d20342103a01c0082d80c016124596640d9021074a1400c40c15400c490f12800d603000402010b0300200c02a8010000460042056046590241c445000d0501890600001d206801c140c4c1c0700342c0e022a005410419601c1e43c0303406480640d4150591140744450100d0707007101c0018840c50240c0f080548900c480112021100c2030fa4031340300300c0d0240312180302c802405000c840c034006004c1005118003c0b411030340115500e402030100240140c59605418240d83d06241034000803610004d0581c081d41c00103209001d040a100c01c2c1501c0c0c9105140c0010555070920365421880c06c0b0110203544142d00a842c18009070741d410546080500ca0030298a181e00e07200004030340484d1140142916002d2030f503000500c2d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 215982338 1250 215981088 215981111
    0x40509090a120302120a0504050a03141e09031c090504090609121112160b060d330b030307030f0e0a0909020337170c01020306011103031005060d 64
    0x14200c0480b40e00040380e000194603041c240900c00c1c040d44800c0380c0400700201d082035541c0daa150780148101030104840c0c0324414401003146401c8034180c2e05c0312084107807070551181e84c00d001c580044e90340391302c68003c94007142400078005005500319134045d510802d5482c20801000010400c840b01a10401e584000b100700240603d030491025143d20780302c0742d01300160306c18050301c5d100d0903040c4825844d800740441035038403a1580090615990002d0380c000c4590b20040468190001a2009055100614202580e55030f450706030045100c41094908031100303240f103160040c5c40c42616000d800d54010000c442c0402d03c14900400d4090302840d041c030340c442031a0f0000303140c01c1840e04100b45040d5030742c1d00306045107410020002281a1000140310181e40107407070030145000f001203003581d54150003400d0108804030030742e10042d445541000741c4034018901514000d4004454460208400030110380303405030b0000c2540d1094081e01c55283c102d90405040c07011940041007100704060300d5040803d04d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 215983588 1250 215982338 215982353
    0xe0108031213210e030c0f10050304050c09181005010f030f0c1e0806090105040309030b0c090301020316030c03060b04140a050603181c0807080603100e0c04060506040506040509090a 80
    0xb803d80715640c100711003840004242c10b08281c1d00c190b922032412607003031008645a82800b0f841c08100e50600d1034890b60342d2b04003d4189083c4203003240d4080c1c5400d0070054205515011714002003400d5003180e841d08540f088100c200d43d402e025203212100016070410008980500c80e40415105410016005540d80700c41902083c012602c10007142c903081c1c00f4800f5400c2008401d43c8440d01034000d12003418245c4001e4000440303030202401d5440b0201c00a0340a486000031078030104809002190780e480c241c01e007400714410200070140001d05200204240b684070f4001c08043e40c004081451601c1d01d804900302050440c1c02c0c4083c5c000781034290002c4e042c1e0311940594441d4040136610141041d01c540040d0420f440203248500172187c1807100803070158841e400d030344d00014a0804900e01d0311884002441c6c000120707049248a814103091440703805021038400d81c514400e40f4107001b010b403205d0401455000f42d00a8079042181800208601d01c0c1c646a2160010005000d84144070003a03240c506 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 215984838 1250 215983588 215983643
    0x120302010b040509010204080d020102070b010b0306010207170105040c05010503040312020307090b280903170d0e160f05010c03050910030207020a030f0c0902031501110c1206010e0108031213 84
    0x44217135070228082002e03031000c2c000c0c2c6502d80342a10007103280210070398500c054184103001e8812050710110020321103900822408015086002c158029030300f14880c00c0e40070301422a0111482d00781c1090001d665400f500079079000b0759043d15498101e04075000aa0000c0d003004001d003040000420000850b41842c400030026101201407071909040e01401c25210f50070311a04690800c80c00000070000301c1c000300e401f51940c0801c501d031075039280ca42c5090640a400b16030501142d5000e40051000c480c01d01504e4403044607031000207800c907250b03910019100d13a0122000580400c2007000680c51f076150202440808029504006043c1106038011409026031900304880c001c54040071301c41840104040d040041205010540c9180340500100c1803002171040e45a061010700d034500070841000b4003502102080c0079107101405800340030140e588440a02c103541002446a0020517a40300201c110360709810342c603e80381c40d140c407003a164003150502c107041900e15400e102d410603101c150f420b5114 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 215986088 1250 215984838 215984851
    0x160602030d0b0a0f140604050402040e0906010b0a09051c0b04030503070206060d020d031803060f061406040e0615120a09050d0201050f06131d0109051b0a120302010b0405 75
    0x31034403140001816022549407140c8a48141484401009a1000882110203644842e00250070411803440032803003e01881e04465031050011a0102d59240150f0b42c440c03003668640101da503107990751002200c080c41003007805c1c800150a00c40502544c06c1c418001d840104400c140501594050b88441e201840c0a4070708900060001090011042c2c0c104407642c3c00c43c00442d40c1c1520002c813680020488400c120009003403050f02c0128150001c58022480011504004240020115029000014603060159080014012591006034280304003500c00740c810704c2d40c02e2b02150702e41f8030410000544078174a50341c2c0750b50104102c0d064404481c106034004c2c80f0300f400101d21010305107031490601c030178041a6021603241c8402c1101d0110000082c603004103054036001d2100c070700302c0003c0e0040d00549125003001024030000d0130740359405510000341036009070f01b51481c0c074240d00b81d04d489448009221a130311146540080c410001294000565075100340000111a030b0104089016aa000c91f00c0e0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 215987338 1250 215986088 215986093
    0x4090c0306050c040f08030c06180309040c020f10020717030c0c0109060603030f08070906080a0b0303040312080f0f01030204150e040c050a080f03040b0c070e1801180506041202160602 81
    0x200301d0403100f00c0301207002c5d162030400303123041c688001481c035560306001701003007102c913114481031015400a008540c9c500a01410074010102d0640010755240101641b4000502c2666880c03001110640309490703030b0325889007200041030700c1c0e282114203c3d04080c011801da90742c00c002c000d4495009120314081d585c858200400c3c0c15141d400c01a00c3c00110038000024401c0c48420018480c5d444107034602602c29070b0a1889040e110301d4800001040c80044164161100103004028802c84501320685500256140c104698410001e0032101030305481e1082c2c180c4020005000501e1710360000340151014031440c40b110750f41c8462039800700106030b80551742083e84000c10300c060f08080c140c0d80d000e0452000180540d550b4608441c2e42d038032907841400d68440c0c0100c1e4420340d459003408010300500710002c4103911400c0003d03501d04050300d8600811169031034107941400e100411544c4c0c0c140ca54100c0b000c0d050340d0740d40e82c4602400e00d040c410a002107001e503481e100b1701e8960a2079400c0c05882213900 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 215988588 1250 215987338 215987347
    0x9083405070905060f0a1d06150a08041b030305040e090102040e0f041506140f0402090307030b041a0118060501020109030e210d050a0207050409020603070f0e0a0b070210080103020f04090c0306050c 87
    0x5940b01f110801800190058050310b201c42d019841d80402c64110b150640792401c1243c0d500d082c4241828001d409a20203a40142c41c00024540c0c0403014005a6505010300b51298581184c1c4900301d10662107212095401007000582518600d40398651103401100f03c106807000c0144100111001d0350072a94a0110041c403c850504090704030002c0d03d4000d50b0308502d00640c640c0020740d109424440100741100300800038080140e0185544403d0092011020141d6183e0410040c190b000c0b00200d040a49051070000380c540c41405401c0170760f90143c0b680c00781503103034070140200c084070004003015010400103041c0704042c08201c0301c0c0300641c0c6075031044d4540130344100c000c7c20640281d0106219034202015100540d80303240403aa003040c5103062405091480300b00680e00784041d1088c2a030700c8440c1c0140066080301200080841c0b030b10031a0072a28942c032542c0d0039101d215003800040d4120340d400c2485c02040c109917101104460054003600303030540d0f40340d0300c1c0e106a07401120400701078240802c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 215989838 1250 215988588 215988629
    0x8070318110d02010201020c01090c05090a061805250e0f0a030b0703023103061d0d0e06070804090b030f07030308150409083405070905060f0a 63
    0x1161000c54008125220a11030240e2118107610300040041031046035512040c1c81103a0003581103a0030302c034000000380001100c0d41030084c0300c1034039032007070b24003800c0d40ca400034000f801a0701c00c5005494104cc851000d0741c0301403403844002c120040c04c66446a0340b84015002024030428000300000769942d505440302042d070b0503c2048000c1b402c0d1a40110980d08082c40003450114125500c0030782032900503141c103e01452001090008000082020080321002c0c01500122500606a9026090601c041308a0240d51310b400010080c0000143d040601120341c19807060001070880400102900c0c1030003440d03103c55905903c1680030040459640035111003504050000e02d50528507107000c1c1c40030614544024040c21030041c20b1030044803050080101076a15584030310703115900000b81a8460b40001d0010306055041802500241c0c0500c503030300c04601003940c118003620350010250003040e18003c0c2c80e9020b4070018140315409170b840094010207440f85044140140300c3d50b610b100f4440c1150 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 215991088 1250 215989838 215989841
    0x18090601050f060a091e0513090605150306060918030a0201051509010e19020706020a0c020109080607020304060c11030a121704080403021c080f0702090f04051e0c060a080703 77
    0x5103003405494280030303480d00c558000c2d4080048800d0144d00d1140f4001c01b058810078a020754000e180d11810564005250f0240c0c1e50050b61298440c140c10000d03074982c81c03c6191112004041658142d110708002141410320541440e0001c1c41c02c80005210100700c450182150041070001c1d0050b0b40d075204110500994142038103104400740c56003022941064240303500b40340300400b200350401683c010880940c0403541200d061a400100441d100e207060344006010b40f001c010706070700003801c0b45804125000c011455501410040d00103515040c60a50182c1e603030705035154107456402601022071030584080c400110300078072030030211505040941002c0c00f2003103659820000e4010031020400042d04480c00c940075643c040320318406020580200030040d202004000f840c00f40049100040704140d00d0140100f075200311460401c0e580c60403007000c050740701242d0180865000072801c06801e40d00b143c9004442801c80c3c16a107a182c40500414480d44c025400394000440500802c062564507 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 215992338 1250 215991088 215991109
    0x30c0c0a0e0903030c0711041127030705010c08090d0c15080c0a050c0c0d2108130809010c0c080610060e010e0402030a02071a10050607030813021809060105 69
    0x7410100641044001a41c0d42c1c04010203150030354400042c410180841c0c1c3c021560f26078001007007803100e62a104061031641d00501c1c0d0f0385100d00d907289594968202c00100241500902400604545141c000111003000303904009454424081203440110788625005c250040d0050040c40c0101d0314000e45143c0038150312101d20b003000340c444240280101080304a0700119001d140603034603000d07070111040c104140c19549540c040421810310f0300700034519007603101e40350700c0e044032440208803180f069405480488242d03d41c04420444000003401c0790000c1e0044090601d05901a0002569001d0071254140c2100403598404800c0141010201c01ba01000d004549015101c2d00c0c82c840001e0240490100000c0c400c507000310014890006030741c140d03001c05401400340e19040311401c2c0140308600c002d40d100303011a03d110a0100300f03130400c00120342c512681507460286640d02c4101c034041280c01c16908070703030221002c0c079541d0031501085203050007104c03100090720340c55140800308141c0b07440c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 215993588 1250 215992338 215992349
    0x501120b09030a090b09151c1b02341d150f04110c0102040308070605010812040b030403050417060f070905030d0809240708010f0b09040b01020f030c0c0a 68
    0x100101000c03a503002c0f401c0c07001c1700c0034000d556454500700e030001003503200201410441420041151082000725180f406420f1022250400400e44501040a09040a0903a45000d64080e180f060f41c1002115076041440402c5880407059002120248203040e501e07a0203454061041090111301c0c6608044a80e0011241c115482d813650030300d40401c610502d90314903541700b941d0b80c5c0b4900100a12060032151103004500085589644030324280340542c0040d5000e642040c54100007291141d40000c40107031823402c1038052428946440d0f00303000258070040c800c508000091100040c03000b42c00b100c0c514801a0407003d0110b520782182c4030310814500078001000c02508a00400c11030724003160502d158246860100b040d650b40c807843c1c130300d031071124400e54000e00c1d04000000280006080f03418068402c6990f015042d0340da0300020f150055150050040301c03039040121101c0d92030280d102045000c8180140ea0980405110050854200030301898064200e580300ca0f41d10310f440e40d001d401a09 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 215994838 1250 215993588 215993593
    0x513080604300c03080a0603060e251412010605040f020315041a0d030201090203060705040812031005010503130c03080a020f030c100b0604030507090c0e0f092202040501120b09 78
    0x7110790344000d026512a10000c4c0c2030150751400706410000390b030045005582c116500b84a80004100303a16502c0b003400400081810700c00411200481e0a8151501154901c500907041814050204440d90701880398800b071035940c850000945440764050440c107220580401600c0e880c201c1548a1503460305080c03076124902d00031041214550800c02c44002c1001950b0740e03081c8912a00e4280d0050848a030b010398148141810040441d80c0307c4005c00940f450b10094402484001c4190002800309407480004030f00c0c6980c3c140500c0d40f240c0065039000d00c402079682119200740c0c46542c03040003690800d50b003001c40024040c2003260100152603900c020000254074048903803c600c1d1715440d00d02d5051210a854091501440d41e644080d14080c50300402918040c0baa03407540c3e00300416040040d00d02141d22080c4280d51864403854802170414090a11001c0750b0702c4402d00719940c1103c420681e840741d8a81407140140e2158400c86001e1305824114900194040c1003007004032034020444141ca9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 215996088 1250 215994838 215994923
    0xc030b100203070321021c1d06040c1211121c0c020a0b09010c1403131505030f0601090b0403050f0c091e06010311030f16030203070e010513080604 65
    0x13030b9101204d880443c3d20b18010350803058815001300702a1254040c1c4414200031a031420740504100d0780b2681d0990704030840c4078038142401790f02a03119801118040d0108401420401011500303115a151107032050b0080310080440000140307400d80000c5503d02c0e903070300500072100c004d03191008001c072195203400d0035021115070f50f0001d40300f032015005e40751703007004007107440000b607409220b40000c000e921440d148800505100742d540c0c1c03600585000c00b80c894554a0001d20061035028043c1092601d69415185641d0031040703c0c83c4190162000341003010105002a4100b418009040518800c0024142c0b0b040c0e0041c0c20340c48c0010481010f0700c00d82070741e418000e1710075180c0a00a46441b62440c3d0703004644d60000140e0061080d6040c4402c0208c000041045c0c500900e1140c034821126600250203070309649004900b02d0204803a054089500548100c406c0d601036005842c0c40e030190003003411401d8490034040d0030403e0642e41122110614040041d9000071030f00c004910720501c45011100703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 215997338 1250 215996088 215996093
    0xb0f090c0a06120b0301090803090705011d0120060a0e06010f0501021504080d020304120201050a0902011b02130606110708190f030c0b071d0a0f031b03060c030b10020307 75
    0x1001c540b140310140000031401d114189400d800c49640100000c0082080d1440342c1862039050380203e0300c491041c095900042450760046103e04107119102e00b413001c105070340000650381c81440e0225407105404080c0080003402c0c042140501c1001c0070320000c2150005244101d2a100301a0001a075107000000d06106a036400284c50802e210001803114492b1a103092042c0300b4880d0480401803a03000008003c18044080c41030802c9031490381c020051b0344d40f0601240c080301d200480c024001440e00544001e9018603c210514041c00103000c0a2141c424038400401c0b203280794001408656a1014000080c0060000b40024001600074041000225443c18284030700743c02c00410451010060388141441044008495541301090b11034604048030050025082511100381107174203c1c4000c4014108414203001f21b404c5102202d2156042d80d0300e00020760004030300c042c0c1074180f5550010114440d130080e080d55991a44000039486480c106206c180740a240441c010340d4004c00000c1300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 215998588 1250 215997338 215997349
    0x111b03060604150b0a0c031e0e12071d07140301060906051303051516031404060b030102310b0705060a0b01020c03010207110406050418170403020d0b0f090c 69
    0x1400407040780d000a090b4900c2400403000c0042c0d4200640312130b004074900305295004420070044501940310400e003410301480b0707141d22015010b42400010144041000d140c201000f03100070035002282a078a8564031195448400c6c401c0d0105c140304d900726907040c00b06240d080303105d20f810307070000740003e81c036640c1480340c09402c1c1c080520501c0100035002994415105842d00601d01940c2d101c001c0c0c90160f140303510701005000381a504e20150300e40f00e4002d80501402481940518000700f04030084540c1e4031345403100100700240310207406540800c00c210400d002101c1c5210480c0c4d80060521841c1500343d56500c291281c0c2c1c00040111408110f403c010513400150b040d40311f00b00800100389103030b44900407400c1c0b6408180c2aa019800460060300300700c03c40808a80c485020788080007071a603144108010b55859194404110305461800d001040380601c11050184c1040303811460325540c1c2d800b01d0f1200100ea20140d4083c50310f01c05020100c502e43c0c001d0b5400501900007403080c1a07000700000c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 215999838 1250 215998588 215998591
    0x11091c0b0708070c140a02090f07020606010e030c1c0803160f02060705090409020a0f0902090301050a020403030c02060f0403020306040b0f070903121112041214031804020306060702030d111b0306 86
    0xb0700c0713258217078030b2501614400c0103100d8040368060208145420146800b42501000b0b86843e03000d4000d980000f00e0303d522402b60101d040f00000c0040241503a00c07030501c0480400c1e41c0102540024050140c00454003c1008500602000c60200e0348001301460051060b0281c806982c2150032420074007042c1c56210041c0c07510394000b1240080d100d00d1610000300c44400326404903600540038600050303040d02c654054400000300381c000740030680d61080814124859800300402203181411030102605201d0003800f409916010228681926600040c0c9810310072101200d50200c06004c01001d8143e60000a401031194104aa096800e542c0c604403c60105900348081011805d24015209420800c0407070046594005503034540e03e60709004681381803800180d940a017408140c0200a000000b220480d540070740c0c403000700315045010003000e5030000d8070196002c20f0900c8120b0150382c040c8110788a412242d1203450b94056510030303c0e4200801650381350041900c449084600f5180030940b076 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 216001088 1250 215999838 215999843
    0x1505030c070605060105120405161e060305061c0b01090c0507050705010809011409010b0108010f180f0b0316030b1605030103060906020c07140406090c020a020411091c0b0708070c 79
    0x803c81e551078400498040c000d1a10314050081d8610a0109220300490750304121002c1c100c0c4003011b10b494a00c10003020f580d44c294000c44d909600da0410031140300b6480b49c0c1d08541300408622070045581c1d4192030702c0f401400156010305440b030041000480a1040d4910310500d400c140b4180b8525440d95174480c110381c483c1034140030018000440149007035011248180d404010040c0034244600c1150080c006040482d000c21560400451050044400300707003143d440000340182c00d86080d1fa201c028005850a1402407904e60400180c56a4144141086042c600f40800125455800e204014080192248240301d41c03c40242030b105074400102c03415260081c00c041809001c9180c28402403290401c10929401100004500b4004100c40501c2441c000c560038403845803110781035030071109810520005a400b944c50100181840c0c2c02086100144040c040d040100e00d80102d8070300c66841d1390061003024201074201c00c02c40c5540c461034100c0d215140241443c5407070100509080401d0002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 216002338 1250 216001088 216001091
    0xc070f0602101a0d06060305010c0c0803181606050c0d0929070c0b04090b010f08180a061517030408190804080a080c060a0902093103091505030c0706 66
    0x15411030520f80e030b048002c2400d0182c4101440300c003d0070108014065070004030740550030f1402414000d44030328000c1000642040313819142d030310b0308100b500c6a021007021a65082c00740da502d503e600d20002e50f41e240106003035256140d48481004500d41049441d181560134804400000c1c4181031131200ca81c01d510900d400c041004540c40c9c0480c103003a019414000703101418114001c604088604040c200f1195400d0061040305640c0b00150341c0446101d11080004155a001032246e400c1070840d0881300220406440c9202800c0e201d06040c2e46400020000c079001c080003c00c400000079084880844c0d2040c061801c05040114131611010154950000604078124001c20b0080003800c071002402e42c0d80440300d44d68011310f4100c6144c1c0000c1c242000070b001d010005881c01d1894003881c40c503164020103944040d5914001040003200e040380d40b64480d04050b0050400400c460b180f16080e07070184d100c0802840c5481d2600e000c0303150032803c8504100b8140f05010040101400b44e0715810343c420310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 216003588 1250 216002338 216002351
    0x9051906230a1a03010c0504060f090b0703140d050106020d0e030319050901021527060709030605100801060e060405160504050f010c05011409120406020303130512030703020c070f060210 82
    0x1c80e44803d4a0010031a51551074080d50129040d000b10043c0126072258941d001000d15140040e42d44400764031510180f400c081025000292144451007030000880c600b05007802c04c070110203000c076030007600706002581c0300c182c2002e0200e810040d00d000d4600c04800071864141e01409014880c00080c0601090020120b01c10b07840d40c0c0240b00d46c0c018100000051085443c0c007403e400b4201a09141d500c100c01c010b085040c0c802c1c3d0002c20858416151900e8400045146586040040bc0018101640d400d0300e840d02080c0c49400b800744100900380c803540c100381801c1c003108010803a08040d0480b1900f1005002c1008121f4211080d1001c40e001200d19005040d290001039495034403600b801400d951800903500036141813a8609806085c4c040b044903c214403040ca0710140e0320071801500d015074000c0c00015101e510100c0c255016510601c183c0d86900d44411100a260300144c1e9003801103500410382c04503244040054030b00404001c2d0110461a19102c406520388103400741c180c05040e00d0383e5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 216004838 1250 216003588 216003611
    0x6140a05041109031b010e012a02011107080c130b0d03050a03020706050106030e0d03060f0b030903040503060103082206080129030703020403030905040506060306090a09051906230a 80
    0x10262050481c000e0b0540740017405424030514034002d116000c50100b441d0200e52081c5502c6001c15580d118181041000c0b110180f101d0050310080710007040b0304001c0c6240c1c035074180ca142405581c0050540e00d00a2820800c0c20007040600c094034003078080c3c00c40c03800f040348400d40d469a0b541e0401c10342500f0904e0350340402120460192080c040060095800d000c000286e6940c1940f01d16211107505007900e00f004030a1004800b030f01c100d4410317000d00ea149039170b0900924086500841d003240d4483e0032030b450300355281d0210741010302c00da105549003400407800074065078032980000300619140424881c0076050150241810106010700074400800301850960590705400e400c07005110b09401036142d00d0310590050203503100d4002200011824000001c0da8100350058030b0007090020580360440d40c0750800c0c81510b4000a11005046446804140102d4400e01050050024001ea203c80d22942810114169484102d035a002c4c00c01000200040400c2c080e40103411a40e4441e01142c00301502 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 216006088 1250 216004838 216004871
    0x1060f03090506011d0a0531050706080615030f18030c1b21030f0703090b1602041404031d0f03061303021e1b010c1506060306140a0504 60
    0x401d07008085208000000c2104854034130040a1885010389031206035481c03014034030a0b50820b0385ea0311034016404107081d90b80b1050328910660400404903034105a10310343c03200d80c5840075584c841d41c04524000d080c08243d090a5003401c100e5440d115140f803940c180800a04c0017404000c2281c02c919140d080c800c2c0c410308082c801c5a142e00c3d12801100d489411035860b004060415801a40c41405103400c2c540b205141000d5048080c49810080e608048404c03846444980c4400011410481c003941c01281c07564140b4050080040001514100400584140012510a4519102003100c0b030810000040d0f400b4118000541e0390301c1180c405140e0900114a001e01e480784501c2c0d02d07004043c100407860701400b0a0380f8041d8020b03030844050407d544010003d804844009d400700c0d030000c40ca0408410001f00c4007120342e90b01854040b0030710140b6102d0440c0340002200603410281c4070320042154541c90301a05025180896501407001144000206244810f20130b41c4d0169407204070b8100300802c503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 216007194 1106 216006088 216006101
    0x703030608010513030c120903050d030203190b031b0a0f030b1504060302010203220b030403032414090a020712050309150c040b2a0c01091d01060f03 66
    0x347c0c4900c0b1008507403003001414004009800000103c08028500a51482c1d40d00161039080810402c0640b407844000804101c2c10502c880b00c041d60042103c6010780c0c10349090b41c81082c16900410040ca00560000d101c001016400006101400100920504060201d0b40b01c1c52035600800c0111030503404041d0060b802409080b43c1c0385080d8030741540040e1981c0000c2d00c120340d80e001c2c10990f94000c4800300d0010f034440c0211600300944c007000004250307000c114020001e04018031854a01038251805202d103c0210100340c102400e541180d6616400c00302c40c0014402c0c0d0a40500664001d0381c242c0f04a1207160280075600f0700c26a00240070b6a0a000c0342d030300c1c00340b4041030200c03160440c045541354005480599051303405141080022000c0ca107010700300a00101001510030b0486c0c0d44948902d0b0010740d29100c60080080e40c20341501c805042034510241c0500b0120000d102 = true := by decide +kernel

theorem cover : BRFrame.Cov 215827338 216007194 := by
  have h0 := BRFrame.cov_init 215827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 215827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 215827338 ≤ n) (h2 : n < 216007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
