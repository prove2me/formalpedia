-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4227
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:55:54.907101+00:00
-- url     : https://prove2.me/submissions/341c3686-d068-4e8f-9498-302fe818177e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 760071942 ≤ n < 760251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 760073192 1250 760071942 760071947
    0x60d0b0d020613030b1e0105090717270a11010c080705300c10020d06030506190605011106061e0904060c0908070f0e0705090d050303040204182013020406 68
    0x503054030300803004054070b540c0700140701c6c0945800340714111005207694010001864580c460f554040328900c0c013010445801021041c42c8d400542d10035505044152400c1025902d60356410040c0c503a4a000302811151600c0c0d130045c0440b80750603141005000065042405003541c00c0324043c960040031a0600c40e800d014444402040e2420514000b041c542c869003a00181f0040d00e00b42807071040648080001c5544d80002540402004452a6117424001010134401c0c88901d1003008051141d69070b04d21110380d038030704491880d04503e0500803a803401442c08000002c2080c0e0043e4256509424106038041a20038805c0300700ca8103900000007010802006503e402242c0d802582d61115845d00d40c480c0072940d00e0b10010300546d2210300706407038200070300c0759141d05d216008181800c22071700c3c0000c1100800e61514071f40e40c0c142e1b244d5100005010031400c2520410364000d40d400d119041311400f030341e500549040c0f0303201540a409400f03031030350315195110944104169424402199100d0352140d01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 760074442 1250 760073192 760073227
    0x12040b061302030906060d0201210e10090f080306130204090207050f0f250b0a09060212030709090905010e060907170f0604080f0c1f0c0905060d0b0d0206 68
    0x114014407958403884031085250007500c0c0207907101009005160340d07240a1100c0c80000041c16810018210310b000c980310070700c0384000800d0007100b00c0881c40c0c07860758900b5450400014441c032945031a203900840403032a140011100303035621030603480d605c1d120400091005680d0003100d180980c80042d00080c559803541c0100920340c8100b05139410300c482c002c2d0940d02d41c070024a800b41540c208058078495a004139840e4a03400c0310003d041920580c43d45201c0800e600944401c4010500e0010103015940d0104691009000c0b0300d00028518070f0712400040441c00c29119504880351240c1241c0104a8203400c0180349102240444002c1d1030004021580d85645225450081400c05800140f2042c041403410201c00e5080c0184410346840e03581da2070070b0740407a4060b40341e080d0a100d101503c88090010071196000310018158070030b4404d03042d1046407042900e900078005065001c0140b43c40d00016681c82c9190f100380011100707140000305246132b110700707002580400c00013800344002c440790a4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 760075692 1250 760074442 760074451
    0x9060a0917070f050f1f08010f090c05040b090111012a020102250c181a061306110114010f080705010f05030103110d0803070e13090816030512040b 65
    0x6004004007884841615a01140a00c028101070484240041d00380042c0c0c05185e014003401e108a41254052624401440c0f1007590340003410180041000c1d038240041c0c2d202500720301d102040420110340300a01244694850f49482c10b0002c204c01c145c40c0c2c012046210f80b90201c60080c400c46002134102004603090400e4495440760004011840b01d2052081d595044000c850248070306800e100317414512601d4080803289803d0011000c248400000d10014001c1032520003c1040302c507030031246500407106082e4500030202405240302c84400c0103141002c41e031041c1084004a000c0030515400342031413a011807541c070b40c0f0000005080c0843c801d00d404450450082d00c1c03015880341e00440c2c03c81604e01c4900001030040c001031001c40c0e941000098041d20003440c00540e40060ba46001803500200c4a01000c26840181d141050a02c500c40e800c0e003d00f0720500f005205004d6880503007501440c0603513000008101d00650400d8040ca007150116690307003c3c026107902c1e0a1401c0480703200102d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 760076942 1250 760075692 760075709
    0xc0904022e0f0516171902032a030313050c030313030209010803040302130c020a060c020a200604090f0b19060215060a03020d0f21110d050f0f09060a09 67
    0x1140c2c00c00c040d00c5101078441400d181022003040c03803500d071104c8000364119001c1e03440d150710802a4110005c0d80a07070041c01504150091b45c2c4428800141204022420103552100c04c05105080090400802242c0c0d11100c905c0e6140070b1301203142041d624009440900036098403002403481c1d0320090460065044901c22501c041c220f07038032010f00903224011440000e40240306418501052901d680041810045038411100007043c60b0f1202d20603074041e40c0c030360000768202549500c2448801200000458100c1c20f0801c0601e143d440840d00b2413040e07103e2900c00d981c1c0c920002d054000c19410003081040d0082a8980b00184002101170100442c0310ba400035100326046601c02d01c0801840a10820b0004d0101c3c0009185401380645609010310450b8108182c009200c00119803880c0803c00c509001440314090070f04d14400391201e0061002c800c2e0a42c0200e601c1c03418150300c00115580b90b04190105500d5052181502c8014001c000c04d0360f50116010505100c80d60380401312508407031000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 760078192 1250 760076942 760076957
    0xf06033d080c010c140c150306030114011503090c0302030601090c1116171e030c0f0c090a090c09020d0b0406090903080604050c040f0807050306090f0c0904022e 71
    0x240c01c801d6441c00d030040024003082441240d20081100804c908948130040307400e4a1045401100007000000b00e14006440494003006100d42c5007001d110382d0b0040c00841607000125418155941c03018101400c4e00002c0540300c5940b9801c1200760813840004507800390440345656114a940f0b4060044103a050300007034800302041555000000b01100250311501411007414180b074076040c28100710300348641d414415003044218005c01c9940424418214502a503181c0d51009040e0f420221442e0142404d5030200b42081040d030303106498240c222001c1c1c43e00040030302030703440c2c0800480042e502c09000d01d40302007000b90a103401a000b08030040c400315010000b085d140c4c2c401c1e00445650040280004119900159090515500180d0800c0c042d02c6641d05040d41c91100c02d100182c070313030403e50303950b000080200300504080007a00e07001808071b0064141c1d0055500c40b10b07560b18128071018400d043d414082815501c0300070404145d070304251a4031518001d0b4001030b100c0860341c03001b01c0d000078500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 760079442 1250 760078192 760078199
    0x6010506090d080324010f1202030a0b1f02011a0a0504090201030b1002030705070506070308041202010e031b010c03140a051302100e10050301060f050906040902160303050a09020f06033d 82
    0x987c8051a02881c1d07807a100c07040c00fa810f02c0d1100a400003054a412242d4500700070b445030b603440d5000359401c803002c0000040c0c04010280282507420112000d010714602c400400803e54949244078165401960006036401043c001280503191012059800c003e110a049681e035502000800350f0320300a404940c003041c4e8a1090101078800d120703018000641040100d03001540e10307c620349010407140b0005c56000f000704042d41c1180e0001c0c0d044800c5480c44603807080c0d408020b0140039861142d03070504110340e41d50390f4000350b04075038000c1505005030364500c00284a1800300b06c4400076144c003c0c011014404417010064010a090b551051040d00c0042040403c0b43c425412070703060390142d075550b1100640f554402e0711942c1048480030f41c070040c00d00000c030340304881d4809466465200115640e803c1403d04010f000c40328068400e00c1c0395428000c0c0e100c00b58a407041080c0c58201e05070381041d52a03603a420350411100b40c6000c240d10101400c10282000c0c00074070751241d80d0f8101c14520b104819607 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 760080692 1250 760079442 760079447
    0x60c140703080a050c0c03030313030e06041511030d1506031d07150507140c090106020106080604080d021210090c09080d14070c06030504030e01030e06010506090d08032401 76
    0x600307110090a4035000c00050300300b5481000a80310030443d0804842c1140c0c0b9400000f415500111101d080740c007015030b6241c09041d800300c04100903920549100c1e00c0d060520341c03001041000d01c0d600d08240045d440e1031102e00d02d0300f003080710a41441070004100c680440c4c000000220024030031480003c1c2402031030b1f070305500702041d003848944108005000301e038a02141c08584003e4500da0f4401d1010600c580c4000c166408102082c000030b4030058201c0d0130300d5800700501c451041c2c222004582c504002482000d000103007154025402110150702c620001c8807a001034800d900809908105400501800001540c0c8980030b894020100b440340303118400c4101d4a440702c0c1e105882c3c0365488003080d421150b001c2da24090401c000704d40c03850f1826080340c40e800d078410f11a60140d0700103940c0c1d404000916a01480891200721b003480c09000c0d130f400c0841055581c00d0107004e414414200091441419502d0841e00b41009502805141e01c0e482e00303400f2845880c4407400c880702140600c081c101d41e02e62 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 760081942 1250 760080692 760080703
    0x1030516081b040315050105031903080103081b0a0f060b121203150a0f060906050408030a0e0a0909060504020a1a030a15050a1203030606050306011b080405060301060c14 75
    0x460907521814650b9a41460703000c2005440740000319600100710200c0400e85007075042c950118141030100d501e502d010141458081e50300032900c2c034421900c040383c00281d840031000741180e810807a03e5407100c0f000000328200542d44140d00d4010310900c0402020401c0d0303084138040342c501031a41084011103800034000f2120303802050104940107040700305047e001d03010207590481020610100c004d84484082a4442043c2d0401854284007101c204291944120721402904140c980941494030301046030307949010b030b800c0800a00c020f0402501c82d5031503182c287c9000b000707900001d00414490303007403c0300184802e94050f03005000d09000441c80c007550625103c080c4c5a03201c010752840e5107120058006042c002c42a103618803044400141950751980001e000d0441e094410802d000b8514015084680036849072051102c18001c1004a0303811200c400f0301540d00b5111008446070310314246090340f03c0ca8129580c0410084004981541c3c40782c40b00c0c1002c2d12030980c000c0404c120018142d605e9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 760083192 1250 760081942 760081981
    0xc0a0e1c0b0a1b12020304060b04060e0103050601051c060c1205010f050f0316180905100e06060f0916020a120509031e030d09141f0c09030b01050402221202010305 72
    0x840491394501c800c90640d004540c000d000b9900060b104c0001c5d4005026030725581c0c13003000049010001070060250500100f03004280c11200001c40246410540c6030049198401400c0159240030f0030915074000e032701c51030300485020000c00c029030319803800e54000c050314050140282c0e044880381c82c042c180003685551090003071010803c50741c584000713540345144c00013030b85038a540c4840c0d00d50000f580800c0224115200043e0210702d0240d00c56601d484e10000421b124030840000051a00b640c8640140e147c00c0038548c0121081c0c2d08150031b069151030f0014000a1501c0d50701103826404d41e80c40400341c00703c407800324203848102d803000b0445c0c8220142412040c081303410800c40444441c101d0380c000d03802c00e44501e80780e2241640e078010b450300b02501c00c02e1110406030741c0340a000c0c580043c0e100312a4194440c0c144449524150b480307010381c104050003036a0266600242c81c2c8400024038030301d0030052018169a00034161a0070741c0c00b0205540c0c2408a011a003005d02043d03100c4001e00614122 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 760084442 1250 760083192 760083197
    0xd08222105250510051f08031e070b06061b0f0615010503091917030916082b0903140d020d2c01030f0207060b030708060c0a0e1c0b0a1b 60
    0x140d02413003015400604011300b0030410100f0700d0b0392200c024030000503090002c100d0000515100c2c1e2100300c0c5030600802c142d90500703008204015810019110401c1560820f800307550b982c2e1660024061412840140623900c0600d00c5200c041002c00d5100051561040100540e5849000c40700401501d040c002a108046660004400400341d0740a9106012226014022400d28041e03440e401d408c050740180e40f00e01458010102080c04103c9003228140107048110007480c084424404400e4507c8120f803982946c054010942c40003103218200c80e0303001c1c581049049105070401c01c011540c541642004c2ca01600491040354000303401500b4525402000d062818155141b0fa102032060a81c010512814940d84030201e0459616a1028119003840346000180ea20300303030010180380c503903d50b0140325254480020800100c24480580c1c417812802d042c080c40280d902c1b00000d03030140355613440c0280748101088200c00d20001d920030a0254108803000c02121000e10300180f8084090b903105d001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 760085692 1250 760084442 760084453
    0xf09050712020303090607060506010e0f1003050a0908130608090c0907050a0c0501061e09020a09061b02090a050a0c09030b06271302030d082221052505 67
    0x82158620003001c03045100400f41c80c0360080440c00500190031856003510015035610400500356004442004d11043c21100180107080e410000b800c140ca40c100000c08040c0c8500c00b142c0507100941040014903071010f01c00d51590041111703c0d01e0031803944200c0000441007000301e86031300004900d440111f640036017250026580c000050380d25030b11a00c924010030500841220116500b803165202070300c440a0b01201c0c0800c2814843c1c500f5009810800c8414410440ca080151304520315008031059420003007500e06a0703a0044007080f4010201079002500e2a040040c6d1521a82c0140d100c1c5049090405c020042984100c845d0216800000d203156040c2c400700e812440c00000d2183c1580c40c080c0100b0345100001c0304d01905040907151480030740b1044048404501c0c0c14060110a036045203030030199490700a9003001d400c0c0045140800001c0200314000c1170061440480011b440f81c0740e01031800303810451005020754801800d00421102d60310404201c006103442c1042c909412200801 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 760086942 1250 760085692 760085699
    0x7030f05031b03071806020610060518090612030706020304031b201c0c0f150903023c0301050c1602132414060309100c1803060209040f090507 63
    0xc1c2c550340064609010722030001c010481c0240c0c5c05107114080c0c00c4c6035014102c80d00f0b1404001d049100c443e007042d410b002050110312140c0e008807804800d0801c2c01c4030104015280e00e0b010803d062190964020103000005007002170210640041d40078500c86e680b100d907032100400d1946400744801c0c07001484400f44100c404501c8001030301030b40b0b60300c6006004040c1c0080400c00d000400c450760208450681002c0030420001c00c2001050004207108440300e450f890701c032480102510612702000303101d0159240ba1002c900c0d0f8200c0d01c0e2510b4400401c895501d0f089060781c1d541940d4504045520940c20400052044041c18080c0e070010713800d070300c1c03121080441d42e400c005041c1304c400384034940325a41e10480c0e650f0810a48809450403200b110369252942080c1d60507180c0045289000d014000400c140300a149000910880030b1104a00008402c0000181180c524001c041c1c40490814175400100900c440d990050296502c2120100603550203c841c101c10341d0040e04015100f5040b440081 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 760088192 1250 760086942 760086991
    0x261f0b0d0c030b035a0703060507080a0b030d020c090604180813050d0f03120e0f28020d0b09030405040c031a09091c02010207020d0807030f0503 64
    0x60724104a1410045030818018000c030b4035126480b1411107481c0c0c03040051081c1c10140060404049010b03d00c1d21280c1044030441c03100704280429201c13100f01d05095142c3c40c0000a100000107141c0c04942802a401c1c0340100900242c425a03c207004189031003040400d0385000a0001901c4040750042c018403003001d81000750001c001841c00b41c0081c1c4540b40c0300248a192101c80c00050300c640c0c0801d45070407040c074012400c100590060788c02400901d8906003c6640c0e014000900c603418039001c440c2c210391107648800b80411106090f0305114811174501d00300c00206501c1510482034011140320703464010800d40d40e00844c02c002c1e400519200c100c00200300c0c0c6c01e1845600148140449162681c1c400218040301c5101e503039000042d03030b02c0b0307007500d030308101e11060244980341194169094109060034035111008000300d00c1c409a0310304c0390341448a0003074058404498006000c1c1c141110a418102d40b1540521800c1380014240900c00c031006000f401504d006215001304140e140f085681903 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 760089442 1250 760088192 760088201
    0x3020c040902011211031b03010f03080304050a0b01140102241b12070314071e0f090b03011e0b0304080d0203060d0f050d020712050616261f0b0d 64
    0x20b82c1005009035070950840410f01601302409822070a140d40c0785845000504100040c680000f80f010040004101c0c03500080146015a5001001540ea035141c0c1d1810324502444e144008084003420000020714541e0003150ba030342542c0a8080d034900d04e01024010f04500e00d10150003031350513485404103c0c034140e010381407480b90964000151802c038200511b1600c05e0403c54201001030785409840780c1c2c907020311485a420070001e09100310f441400403034041403607050b00c02d4242000394400c00b02c4246881061b100000b410030055540d0b50323503103458000c0c4401c04d0b103086c20080510095000140c40307142e08101c0e1300c1180c0040e2614144684072040602950002c0c1142d80d0190103902c00c50b012030841c244036221a4401c40c028800b14900c0c80010f414039805510039001c051005d08207070040b440100303510b580a14406080d189400415809a0b0f5000f140100c0301044d081150040c5000440104264095a4050b0380c0441303290604374050a400c1941c029145028000d2042c407500c000302d40c10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 760090692 1250 760089442 760089461
    0x60b1c0b06180a0603050706091d09070b0c0c0a060e061621050d0f0b1e0604080d0c030905090103032a06020d020703090e0c030610020f10060503060901050403020c04 73
    0x461001a91804031040030b103502502c0b0203407499511030040080200c00c00c040c0b0002c01c1d0310700380003140b5032070011882e41d98401c5292052900c1c4e01d0b0000600041002e0000101901c00803c1d01900c804002281f1952002d64040c4140034009081c00401c0260140e681d040d04104010103461600b00401c58003100790400d54400c4800340c280c01e042003007054003040b4082d00741065558540d2107807400da910000340e882400441d2062031400c1030095180e1102c1d241080800c102249045c000380100300400e5491255a101440601489000e040607a40c01207540b48a54000d42d107100403903448108008521740c0c00e01c8000c000c5904009034000303403000e829890030b45070901c2c2007481580645468501c1039900040c0c0f4500b01c01c0d800500e4104041d0000e0890002e0001441c0c00402032030308002000541c0f2024000e0740c4556080f0a82007481c0740308000b0300c0f00219182059442d0740d103500906402501107801458400c0c045c8800081c198001481550f00ca103403d076004084400c141c50901000780354550 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 760091942 1250 760090692 760090699
    0x13021020a050607050d0f0e03030c071b0603020715050106171f06051b01050103051e070b0d0c080606180f0d0c080f0105060303040f060f030b030d0c060b1c0b06 71
    0x3001d41e4041001442110b22a400d1074680030b41e10303011014110304441e14111041d12403454140450f1011300000f0030703039501081c85041c0310307519201d90500345c00810824040e113000503071a81d40030442e181e01d5000340918a1045108480c4107110980f40e00955409000d80400291540c10850f5600d2608103040c3d0810701030405050031020680903050051b009400040c082440045d40b881d01d10620201c401500800400030022541190b84407522000814166407048044040c002e1084400384042d10080507091000c0c0d507038038174005101d00a0f003400107400022942c40c900040c000c1c1041004ca5100c080350354080c1a9103072072071040181c00580800d040e508600c0b542c5507a030000b086880070314041c110200c000c20000004404040c00d40714024052402030b0818070041104201c807196500685110742000b040c500501403003100100b40003409160b0600c602094594019008005803540310700442041c4102d000306800c0c0081601102201441d580602c1c03181d070040707000c3c101803680100c0002d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 760093192 1250 760091942 760091953
    0x1107210606180b0f0312090904210c051b06090409060f0f05091b010504030602091504090b01120b030705040914070f0e0a0c0806040c031401302102 65
    0x910340d510400210b240304020035540c840e400100b41ca4a050501964041240103140c0030080d0070b0340e0503a5009402c8010700840015002c03604001c030a6042d0058000c4082106003d070014640041105a581c001611036001b160203526403604025510b070a070303400c05031001d803808903c002844001c100000c8190f540c16a03402c5000b4100446020346d05010030b800300d010901e070608220003400c0c84011481c6203c401c00c100840e560b030740d0300030781554100c0f074011500507200c80c030102c0414804542e042e1074400c40c450000d408600f07a040c035808100d4088003a45c50a11803d030340540c40084640c071140040e4180d00110b8100314501c2d00f5003004140c14810340340d004000f80c010140903d0090250018a03508440d00b00a1014061400900703500075481c0c0c03014400800a00300207000d05c132002c3c00d040d005648500042d29140d0003504841074640d0381e4074064806696444544c5c0d0014002c2500324005400d0b496006001d00b20f140100844541289010884640307600110307a040011028000942c000c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 760094442 1250 760093192 760093199
    0x709062a03111c0504050307121110030e0d050d0e010b150a1404030b09150708070309031e05090418080405041e02030103030905090906070806010806061c0209011107210606 76
    0x2410303400f28000e200d440c1c503500e0f00d040000701030409810380c1241c1004400c40c510100031070300d16100c40c400d50205451010f007544a411049000d400010007030544c0748140000180c030300382d01c413009005002e4150010030404050380022401d03580302000c19070740b0842d2048225000540040200340d4031181381060074950512007812547c4d50400c1d0303c241c1d4441000820055000018000b11807401001088590a494a0300380135100140181c403031800c069803480314104150141c07420703d668040d880314110302200303070f03160003846a80305201e001d0265080247d82c03505c1c52640c07524444079075484519103040a0030501488010503801c10444241c1c880101a280c03202603030700c0218086c601a640c0c030503501d801e01060000d0440098500c84240e8001400c004140b61700c01a025000202460101035035242e00d400600d1501500e03524448080607500401c2569803603a00030a50101c003a2a840014500c01d0603035603e500240c8105460407041955813507002c00705001c10086148941000030f0030548 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 760095692 1250 760094442 760094473
    0x90711010b090a0c0f080403080c09040605030a050105060f0a0501050706052e061b080d051815160801060f0c05160e06120102040f06051b060709062a0311 68
    0x8260748140d00d03d43d8034001c820b0100d50000c0d00c3c8030390038403030b00302220705050035603004002d9400207140c84421900400c911039076a0316a008017004040c014216000513800d410000d00815041d90740e0b6124400021020080b4148541e50104549c01615600d09000c400d8403400c026160007000084400880c11103490303003550504014001c2081080c4554899003011301c040c1c4000c6206001c00300c1e840600d105040010a00c80450700d44032018480421603483c3c1070342c1c040200c40f51944840f100d000c0d2348069801e120500c0007551050840e843c1800c007a05042809440d42003003802207800052081741c4020415020b484c020001620a500f12150034400c41c08050840d50f154004042031100c005c14040e06240c2259582e00b00b400704002149000c1c40c2c40e00c11030040f400d40c82542e0911001041d00b02068504240d07101c0c0343c1c00d421050b100c05281c100c1001344503030301900070100440d40d010b07414502402c9420154003076184c1404191401191500d0039070f80e04080000b841207a200718404a8000f80 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 760096942 1250 760095692 760095709
    0x91207181d0d120b04020301050616030c0804090c0917030a20010606030f0c0e130b13020c0a141507140c0d030c09091802041806060e06100806090711010b 68
    0xb14255640001402065052000c0d24901300c42c5500c154010300041c0415610300d02280c500e00d10080034040e842643c1d14003581d004a501e03201070a20f2001241c001000c2e00e503600101107a9041c6e550700305103152541c203600d4902c1c0901c100030005900038810101c2d540e002d41160590510b29500b8028601d00d6000791a0946540e80c22030000203031a05007041000c00c140c020290b210603039040c400c0c4001108c00c04620021f50301c541c40101c03140c5801240702203880c4d0030041906804281d20a5541e0310340c900c00c0503695245100100d80d040c03401c1210790070462000c5910043c00c150b0b422100081e48901a003111a5400d10004500074682000400a840e10404c444c104078001c907100815540c11821001c2c10f20b0000d50304c00b0010354100030001c25081c40d0441c501c0e460642c11240060960217990b0001210050100000c0c401e40c42c0440200b45081020621446443c0c2242d54120b41c09028000311031000c4141e0790700b078210480e800480c4881d40158010034071a4044000020b0418080000030300c00d5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 760098192 1250 760096942 760096963
    0x15030f030c01020a08070519120e03130609051f030c0e091303140c190615060201090b011406090108060402211e060105040909020301110f091207181d 66
    0x107030f40c00681c0c801d9851700281070755401165414918142950100d000b03d400315540b50880400081300842c1b00c40040a51262031005012011030340c81e500f01d881c4c402c1280020b800703950b01142c40e035400022145000d03241d201d0305410f82c01c5036100900d0039a1056000d404480b440000b4030046006000c1d85031540c51445220780c0700c0c00190001c01600741009040c4200d03a0104000e014400c000b12058880006111900e00c2d0048501c8040c040c094100f030340090100c000d160038984c80b0031074009070b0079905411041d1441e001d280c6000309a42c0ea0346003051088841d02c51075400c0201409008010740c0603c2d8041c1c6c0c4030f10090009442c002c4103074000f4003145c3c07203010601e10a0030340340d00f8804230504001505820300402c80d28004c0380d0400000103001e901961040da0030554540d0307140381c00c40d102034001c441d0a99080000300d0701c4e015801c541960f55001841403500801b00c2112402c2a41400551304048a0705081307049400402c648421000e08007050b00007071055410507282071619001c201c80300d0403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 760099442 1250 760098192 760098217
    0x903040b120f01210b090304030203010e062202010923040507120e0a050601032603011502011a090601110f0a0803060306010e011d0405010e01090809040c021515030f03 74
    0xc0e20b003600070201402e42c107800c41d00108502450b5252208100c03225160800c0d00021a000c0543c0e40e0b1111620310b210b00e0300025015400c0a4241100e40d0001075040d000f1580ac0b941040140c80300e20f0604140700b0f880c040a400510807040806c10040302c003811705007184e0080d110300413080d50302c8045415035a080e60000b00141b141c01c1910a812010711603650322000b044050030070b206254076030030340d242d0060001030a00c40341b514001d8541130401000b400b42c03090f00f030041a100c0d0b944419101890100e84a180059400c00e00d003000342109030b610002d1320035401403410090783c681c00c0044605590906200d2064030500900c0c40c5c9103981000504d601d10300c42d00c0401e07079a00d0712801f45800d0101c1a4460251a0010310040c092a00c05040c038000388035400d20321806a50782c908160340500906000c00070154078140f008410f001c1803500500340f010040c2c900380004003040c901242e4811020507000c41000c01440850b180000301c0e42840c01c041c800a0441d4054900b20280c0e03429540501d5002c0382 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 760100692 1250 760099442 760099477
    0xe0f0115050f09010e070e060c0109050c1c030f080a1e061d16050a0c0b04030801060206090f06190605060a0c021e0d0209060a0b0703091403060705120903040b 70
    0x20600d04000c0b4a030580009548a04803940360020100b0040d00280c003140c00c1c0013808000700607680355081030f2514012001c0003404080072506203180c841d005a0b05c100d001c1d9040800901412543c50462101c140e4036541d602e500704191482212100005014594a15181d80070314002400c2c0302050f180002000740700142c0a407a1283c5603480b00280d02100c201c800c0d800c4100f10110608480801e00b007601410300f40d41d00c0005020444125071030410040011042d50140070501d51300c00012810303184c81c7c1c0c0840e046904c640e000b4a40c1c84800c071030f101d50f99a0296000407a42510a034040700000d5141038041000c1c0d4481f80011000d0300300e10345807000034042d0394502c01549009145003409048114000c0c10242d800000b284641402090103402000c00b0000718515889014000f00204500c0042c01d0301e0304454a0010b02d06003491003000b50b400704180003110f2500c0c01203512401a021516258a040f101c0c1e440703e0050200141038100e940014440010b0301410030b00244040c0b95101d51003070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 760101942 1250 760100692 760100699
    0x50109060602070501020a060c05120a0203071101020313151b11070e04020d021c0204020d0b010201140f0f0901020c03040f080d0f120b03100f05040b0c16060e0f0115 73
    0x202118115807000382194407900e0704210390790300481c41000c010b802610104891200d00020f584e41d20850641c6064000c0031020013a0300017140e80a14000e0381c00c1d60b03442c4031020424150500340d0000341c0f01c031a080c03101400c640c00000d4250b40d00703082e01048a0808504c1c0b50030380011601012407844540c02282080c401d044280c5000d00007880900784c3c46c540b50b5100e050a4010440300301220300001d000e1380000d042241c590740100f441e80002a8002d005560b54202c02c14900050610f01860758055800e000c0d05000740c0c02c40303a26003449401c130480c0a112030b6a42c1510340c480000b010b0401b40e0b49550030061349000d02e1050008001402100e207907074004a140940080c58030040d104d1010801c0007100480c015240e0140000340055a22000840c2c1e80306000b000a04007009402418882c0c2e01d09180307090076440d2504014456070007040890507035034500c46400d07214459291040c207101480e60b0b450001400c20303031220703404201880441300c00900440c0340e1802c4070440c00cc45844400d2010042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 760103192 1250 760101942 760101959
    0x70b0403120606120f090506010b0409061a090603130515010f090c090510021504060906050c03190213170604050f010e0705100e1e15071e030516060501 67
    0x1c401d0709a015020080706141c003000500c2d8072800c00d8400c0300e440c1c07654034801251002d9080800c0094000090b50031a50351603d000001d64414030401103007604149000403036203c480581c00e1b014007615aa6403900c8540010800103034001401070140c841c03040f00c035101017103003044011030341150558418015414a040701d400303000d290788540d68450410100441e00350348010034004807081651280058a0001d1060341403290344076100c425910075004020a00207160010880240203400030013050302c8401710143c1d00d1008481c00c403000b400041c4850381043c215070003031403514181400030704480d880e0191004d040352600d101c020154044010b103c24030000b44000c0c20150341c0c0100030008900c00034107454a0311454802c8038440c803011550a5551401001da0083c8043e0091016034a00e034890340d603101d1601401c0300c1300d000c1c03240d00d0160a0075103404421104c140d40c118802403900041d40c100c101c645045644c04170104941442201c0c04003150b0000f0b400c100b032107010041111342c1043c0c43d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 760104442 1250 760103192 760103207
    0x30e060c041202010e130c1d0108090706080408070b0a02120906011a03040c08030a0215060121090510050a060501140a21060302060a05071e021023070b0403 69
    0x50303003003240100000c0018048542d20040302e01d6080c03c0004012001000095440312541c01c0d0f2110182400c0d801d00801e540050b110074074411920034640c0100420b07004641e5000b00700e03201b0045078003045040c45028060321105501c0741c4070f0400075103013000650b01c8181c1b0301400c0d03480811103500070400c1d80031020b03505502c0d07501c1300b40c0500a007910742c90700c4031290701c102610742000c209001c0003000c03405101c040d107036440241c000001280d81d28404040001e6032004000c01e101c2d10389181e0004580c403584036150f000181c1e100039481a0b10307043e10150b85001130003841400c03601c03841040c403000c84d8000c035401032038851920f1101c001280c1c2d141400145c004001580100031552081000d400e03074035000310300c1d0014101741003400040e07004103030580c2005104c40e400c080d5001c0c0e008100c210f0069840001000349500c60006013481c1ca014040c4800c181c004043e0080d44802422400054203204100c60b400c5804503849104684210700b01ca80c1c020303482000162850300c41d00041005054001e0f60 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 760105692 1250 760104442 760104451
    0x30f040c0b2b0b0906060711120715051603140c060c03091203010e04062003040602190c020a060809100f0c03050610050304110f130509060105010c0c090902040e0706030e06 76
    0x2c05000c10340405000401d6004002d01507485100c2c04900ca0062007100041400030340d02c080d002800001c900c541c0c40d030f9146114800e044821a15005030941c0c5486102562000001d084280980920980e002c0d1191115140c9005240c0c00a0084105105040008500410a4503000ba07074900344034003000e04141a0941d801030180d000c00c010003018010340381d0990f009401001c00121406c000c00f2100d00140d00c08010885584040148003c0c0840396000781010300c0901c040360b40030303400c0c44d8013030321a401a0f10f03010b50b04c1484808100710050241c015140d00a902030117603200011040420800c881d82d01c110085001d9071018070800c42501407284c1a0000000c0b2440030f4070b58030b0711318010220b210041004092190a580c0ca903440e0b01c40840d881c04074400144000280c0107907001060080a040b01d850402d03100b040c0000940d0f5006002d045180d941210301000c659003030640c4000070b890340c600101c0e00695100d07580040040d092241c08040c0070169070102d0308421855089203009030190 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 760106942 1250 760105692 760105777
    0x130603060f05060904050c070b16021b030c0103270302100f0203060d062309060604050c03070c47060105031009051504020d0c14030705030f040c0b 65
    0x1414842030743d46000307032019564101c1e400b2442e941ca143c51003d941c001c1e51802031040010f0014056002003003e042072440201d40c3c00c8030740c206800c0e002a010810340d450704e81d81640100000a155503c03d4220541c00422611071181d00300c05480310341c0700003840754004e40051700300b4440c200805942e0f0007191216580c0f01c3c4151b0540c10110000b80035402000d0f8000c00d0303a0f036181501c804e0000e8550803621031000c0001d2070a0685804400113455441c00c40b0294880c516042c00500c00a100c0c2080d64012110743d9144101c454841da06c1300c1d880142d55805910f0a040b011a1503101d600f840442401c0d03441041d040c083c0042000030020140101070605410302600307000f000422a80314a007082280c66040e8086903a80f2100104111000d22015072034003e40001076000e40441603070819019503102e5580c0070795551110b580311015003c10b980c864000b42c402c1021546c64520101d0603a0418014280c10ba00c1583d40ea01d402402c1d4000801c4001c2c00714600e542882020704029100143c002d0308 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 760108192 1250 760106942 760106969
    0x909060c0301051c0503071113200a020c030d020a051606140d090c0803041701051e06270105150705100216050f01090506160806060d020f13060306 65
    0x21409412035000c1406100d010b0a50910384d030741030400c11600c003c0e0f40c0780c00a0541e5952015400c0845001a44550003401200900d400c1e40c041c0c28544180707510031156190703001e8103080030404003455a210008620842c41030300e018102c01c2d6000d11007003440080c640c00514440c0750314942181010340c018486080c007400300c041009040d03001441c02044d0894003201c1d40d520b01007010f00030002c201d450b4020b4036406840c540840d401c2d40c004010002c0d50a0061700c20f01c9488900b51040c03e031401190010b02980c0100310140790300d050700002d070742c0001b0020600408048450290030040d07580034104150baa04001c0100100c0c00c26840300780042044d1140d4900c1c04e001c40d00c81ca86c0c0d444122030708007091640000c0340c0485203042c81007041c106a0000075203010740840c0d008540a00040c2400796164014800410351107005241d488500f40041d0b00e0354501503507000c04102464114420500c0425020042ca201010b00c0c04003d000c800c0b0040b2030102101d0800000408868560b004641071080c0c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 760109442 1250 760108192 760108201
    0x1020a05030306130615090f0f2103090b070b01050f0d0b15220203041b030b04151d0604030e01050315130605030a05031e030708180c190302090906 65
    0x4070440e68402c0041d529150384481c1083e6040c0105440d42c0a030100d4011035441001d6140e0203c0c100e0300302e602c0c41c0c1c0c3c0c3c50070107911503400020100942c800c3c020307403d45c011282d00346007101c942d049000f90b0090074441d005603600c2210518690001e0300481c0c0d000320031001400310789080c20300001200401d8a03804040a425915801d207102e01402c9000c000a980d100500c840d503901c0c0c141603d100030800407816142c5400400f00194000307660456a0400200400950b03049038a10501141d40081011003130740c8443d203550240209256149080c1502d46c0350103254520141c02d50850140ad0000400c2c06213081d0400030b00340ea1111501504008042052104a1203059251807004c0b000700c035510042856a100e10300240070a0780401d030103000d540b04940600c2004405070512142c40d00101601808005c41c840c803034801114901c01148400c03020071600c0142c80744826150707141303504498280340d441b400a569032001d01041500b0182c090428400c50400011994010205000402d040d080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 760110692 1250 760109442 760109453
    0x40830090105093d02070b0c07031704030602040e060306070e1e01020c1306080610050a0308030c0702090a061a040e0c13090c0c021c02090604021b010e010209030c01020a 75
    0x101d403100c41c400c0114502041c40010726107074804469120112980051481c101068640713042c601c000700150060410003e00a0302003401c40d030040890700b000e030404a01b10f54030340d0065060140e4031a160f440901010000510510082c005403604941075a81440d00f1820185803c4d4000c6c41c6200b000140704403001e25032554064402d40003504034100031503188010040740b40400c0740341d03c02da115800322a18886170030a81c5c840800e540415042e50b0007690744207600c00782c0d840701d84184c40d000014460100003141140c000740d81c11480000c095440c04003240c00041a803d41625a040f08030b95034103041200a410388036020541d10384422907418245450340303040301040300510104c009400050101d00d851000455030009c1e0a000c102000b031007102c114020311018048108034002c180f42c80720241480404040c154040364014000c01c0031740d4076082070002035042400d902440209280400f00444020700a0f141182042800103131942c03504420146030100b0401d280b41950002c421035404640b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 760111942 1250 760110692 760110697
    0x5040b0414040611121005090106020a0506071b0f0b010e06040921050c03070b04021c1121030403112e0c03020c040e0d020105011e0317040830090105 66
    0x2034203c000044d450190b5022241a403003407142d000c1440c600e42c000c1000150303244580406554003034901c03103100d030b88800007660344a8110002604a40c0940000b4640e00e00c60845841c0c0215081c18036541022b860b6503081c040e12089108480c0324850000500120b111410761690140d811507040c46143c1c002d031a143c003002408a220041482102008501540200d080b9141d14a40004503a907901660030114041d220a070b40c102d200d2003061007000542035001c0410a01c068110840741c50404002e4200803c02403110800c44280ca1100030182c0510302c20303c00313070004602aa030034450ba05001000c0001d0100034510741c5101407088005072201d107484c0107800003000d0007801d243c82d00d240d01e820143d190401103412550301c1170400340b075484008000700d0004030b001215002800b1603603c07149130440102c2400488041404078000403c041081d04503443c00507064103000c03614041d120b0064505101d07240c0c12202000c0c2034003981e00c05401030b03d05625811007082044605100f1400002801403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 760113192 1250 760111942 760111951
    0x10b070515010b12060d14030a020f0a0b07110a02220509030f030c030703060801052401090303020c061b0f0106080f0606030604060b040209040c0f0e0f0a05060a02030f07060605040b0414 82
    0x315a400c0000d0f280d51500d04841b0340c6180c02c030180d203e1142d61044240c1d62684841e60000040c0125001e0170341c4210300003040081154000c00c0308101b580d641c0700480d40781c42d002800920f54032800340c1c80d9002d0784444900f20100380705518180e88900e403404019083d602d01500120045d80100083e40d0701c3c1d0210ba007529040510b8400d210741e00d88804074210090300503a00b0104183d440d01c07091000c4000716042110602c04040c2d400c03070240040740019211241188809800751700f280100c0c01091a151000b00701d0350307214003c1249107444d203d00062038680e04103401d0030030340e65540090081740c10801101c5000000100141054a41107020940300c11006d0300003818151207660001c1c01e580c4039010381e01e00c0c43d4060b108000c44002200c00138259003900d01040086500141d0400c03080c00c214140c1c80d06006c019010840c450700e03040038821641d202070541400c500003072002001030704607440141017160140c4008210241000100003c03502010060307031040d4604100c1c0c81030f0040803c03099901 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 760114442 1250 760113192 760113217
    0x503040803151503060f0105070f11031c05070308060409020a03482705102c060a0807141c0b040b0a0506011e030f1509050903070816030e09010b070515010b 69
    0x5030b50002f02082c5440d50341b408400706000d000c11a81c0445078001c01804203d40250303a00702e0b0799101c48051200301e031545c01001c0d400c0b0288050500100c0c0c45401048080d452101d05001c030341c1106144808001e010a146044400c1140d075a16450900f45940c00060504003001e48801134000b0400e190f03460105508070185603e0b41c0c00501000030700c0390058010101c0c08007800044480c90f091100c680a13100400078a1a541d40208070542410501101901d04002c02130030404e041102100180100c4401c260780320710440764001c404003100600700c01c030a210b1440710031035040500e0302d240c0010f8002d0900141515000030448507a0340101c0c0000b102144541fa50100c81c08044120b010702615070116a079641008030101003d4520840a0b045508012082240740c4a075105075841c1e2294060141200030144003e1204112042000450502c0303410f08656001100003c178400c804264005499100003290a1043c8142403180c1c552081d400300b03074011550b040500311007060041034002d071030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 760115692 1250 760114442 760114463
    0x501170a0b0310020f0d20040308130b0a0206011508060d0b090f03030106090815060a0515040909030816080106120e0f01020c010e07150503040803151503060f0105070f 74
    0x4107031003d001c0c03102100c40440e070542d5901245a4180000c0c0d02000e150145ca0746010346045078464401c0780b555820f000c60041c645018556100c4903003d81050052010000e0603103070004180701e04500074101c805040c1c01814080d0701d090600d080c103a02250b90321090000c02001c120300c40c2d84074094541c10651120b950801c0e44c0701c425840345440c04882e03002e0407070311001001060a80c0c1001c0c03188211109001110300c1c10340000c10301e0b401c090f001e45141d03410a209100c1030001c1d1a100c200780040400c0e07007103500d0030555aa40d019042d03590288003600411484000c0c00b141c19645c001000b115217050419040551501c0e90003045c0500c0d014403080c540355180d00c0032a007e1002d0142e80a600c3c00c2200954440c2802c00289008240c01d0a118466215100c400103003e81d0440141e4415080d984030141140c0d0b07107444111f641d42c00100010240c07540910f0800c980d9540d011003014a424404015480780b4225040c00480c01401c141a07041c804103008c048005040d0104591005074805102c11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 760116942 1250 760115692 760115711
    0x19050114090a0e13020405010303031505150906160602030c04030c090507021e03120408040524070f021201090f0b0a0908032d09010c1b080a0e061c090c0501170a 71
    0x202c840c0c0401300298082c0c03c002c000400e155058208031203626101880300c80c116520410011060150500c500c8911800e02003080720340742c01c602030310300001420040c8030b407038140f65901c004a0344100c5908001d004080360910a101c850010040a00500c00d07040280b400e02d600007961701c4030919024030030400c41c0c0380b8104922001780140d4801c5900918000c0d4581007a03d81800302e608180541805181f4101c0c01404409041607120000644491960718120182d110880a20140d0105136040305403400c011b12540400d1040c4800280031b607030007918455851500307010900004c1c1043c94501e0501d803545000c40c01240843c4d81054004d2048480c1080781d9524941000d01140307040c1ca0303090408100088034506405c84014441039503202004155125144140301c8000240070308505030034450300794820302075410011b00310340080c885400c00040368201c844a11070710100e41d85040d200c070203442c100000e140c1d044003d000242011030455031802503841d11190001c0007802c441d62103181c0719 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 760118192 1250 760116942 760116961
    0xf0b0a020903030c0105090c04050f0711240610030204061403060a050901120b2802132c060405150607080403020349050f0919050114090a0e 62
    0xc40d035982002d01525211005200c8036030003007a04031130700b001c030380500d002e103520b54506882210b20441008226040e240c54400d17044441e02c1e1110a450410300c104031303507010380b0010020f01002a0003030041e12803407494507105011040f59040388072030a15006002c140400b60b0040c1c40b041038009440c03038040d280d9690038000388205c8001d41c044d03508414050008900d0340003a4030008581c9000d1520011940c403440000c400c1703003420207254102c141050031580c0c1d150400d80c0040643d16490503540b0442c079292800700b07003200803030050710f0804049102d81015484034101c5180e0301010486041000d80780000b000b00e00d00383c458400301d00c034103c000340010801c25100245c2c0d014640140480e504004400d00c011800c00d501401403c0c1414582c8801c08500c05988406001c401c206540083e04504c624007070b900b5402100910f03a5902041c81004d4050f11604050030180c521014412105803920001518040d00315a501c800050100306000654880030001011165101d207011f40703a91384c0c0c4940 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 760119442 1250 760118192 760118197
    0x2406031202160803040803071103010e07080d030e060903040b0a1b0f0b010b03040210110a02180103060c1404140a05060c010f1a0a0e1806100602010f06030f0b0a02 72
    0x10051584545003451003030380050002c4400e00024880d4a00d035403160615036a03409184140712482c2d00403c880070002d40c02800071212520301038004100320040c4410241810196000303550f5681c0000e10b501d40099041c098601c1d1450544003808250414869a980f244150b000b255604c07040000c9000390188542e08a000d11300b800f103102a41c0742424070307000f00c20484d20b00d002c0d07682500c4000081200030340d1800f22401194020610529480b4030a41501c0c0720140702c110085e10301400f00800c0c050f0326400c00312800400030012034019036045107042402c03141e50405420070481c18102402ca500c0707103c8210b509032404482211800c24458001400220f810341203181c01000c0840c013002da2501c150442000d0b841d085400f440307001e00d04001241c81080441c4036a61221902a041000c4e8072003500343c0d40c00640b148003c4410a00d04020702e0f00e803880507900f914a10049903401c001c2d150b4288500d920185c540c2005119113451626940303040c900702000501808501e002282c451400e5604 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 760120692 1250 760119442 760119449
    0x403050706022103070e0909010e01090819080105180a0227042004050d060e0a030f020106050307050d03030c020a060f0c0e0d0f120309020a090e0c030a2406 69
    0x8840c0e0098407150001c1d29103507031081030b119041c5140f01c0c0042055001c0c06a0b0b1141c030503603440e050103003001c10400282d85c0000c3e0065403503540c1c40c46001e0900c00d00b03005401140d0b0040c80c40325640c0762420030700443c603107040300070604100c030b14001804039036a080409520b4a502c43d01c10811501c0354a900ba00034456035014400c15100030700d0b03072440c065820020148842c0e0480741045548004900e20212640c2586145032604040000340901e1812510414044c0c0c014540002c454043d1241c0078503051921a0582c0400d08040000c203806070b09000c0d540107480c2c16406050700c145480003107103507455100c01c01000e02d910781c071050302d200703108102111086810175000c3c00040b9003880890001d10000320b007180003c48121405070681001070b6180c80c59580942581d10b61034403a114005040c0042000f50200740e00c4072a0b440160344da1f000b0040140900c081c0009920500d0200f407440c003400716031114000d4008154a0010800d0105044c0c20148401400302882c2c6080003800c0081440e0381 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 760121942 1250 760120692 760120703
    0x150405010e01120f050f010512070b0415091206050105240315010e03121b0105101e0b0c0304060f0f090e060a03050a12270b0a09030209040501050910021e030402060403 74
    0x1c5c104896440050005412180180d51000b039802c48084110780794a054001ca201410702080100400c400c00013006070f41d400c075890000c250743d031a40c90f15564056595801d94240b92541e00600007441c00900400f40b9000c03c1248151100d0419003a8025010041c110b4003450300104005086174010700c294070000c00001c040d6501d0003410076136010280c00c222001c0492903c0d420340111b518005100301409141100042e0820900d003170350407180030b090b14411b004601580c41c800a40d401840d8058041907680e40040c640325030031712200804200c85611107208000414010740401034000559030141c804040c04a0090f5a078040411030103401944000d00e1481045c0c082010f009041c154101c980401d580c80005400881e902214a299094545050584601c1c4100002c1c0340d11401805c0001d11070510780d4000f0381e05c1c2c0000d1041c034001c45041c0d07926510740d010000318400610510046c03052a120450402d0303080304515210109100c1c1905d8000d078004003140075135a6003020b42d4021903205 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 760123192 1250 760121942 760121951
    0x5040f06030b0a0e091c0e090a0504080c2a1509090903041214010c09081b01021c0806010e011110050a0f0603030f09050108011404090c0b18150405010e01120f 70
    0xc440c0e086c0e9a03e0040f880c40714016030041850b0017140708801207038011038001c00e964195102d80c68003600800014000f21083c0008110a500400062081d0b40c0724108486a01d1018014007540c07410784c656850209108000041c81c0f000000c100300c1c1078407881981501e00c42c1c900d6403610586841c52065410201c91400e00c040e0040c1003044840c8a84c1034030064100038041d16407030400c107440c100072901031b40109800840c444040001c4900368080030000520441e01014a07040c0a40030a1841c4546200091244010001c40d960012481a450f02c401e181c90000510340c80c1c01e041d260b0003d4031403898030b00d41700c1001c00c0c2c81e0400d40d0400008812481420000d5036501d240152042c260072010030045010044000745640c0900e40303040c1200c1080d41000a442590b400b000014140303000c013114001044100410044460310140014a0159540510640e11041008a80ca182a2401d0101e090400c414844c599101b82c4800381c019007801c01c000e002103e041900b0140c02000101310307200740790 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 760124442 1250 760123192 760123201
    0x80c0c010917043b090a02101e0c0201050a0c29040c0e37110a020c0a0b0a0302072306040210081e06041508030904060605040f06030b0a0e 61
    0x1244003c1c803c03103030000185103c000054503070741c0f42c419040304404071300042d504100003101402031001e6484500d1005130303426107074540d00003407494040c84142030001d40c00c04003443c1c10808800d581288480b4604001c5c4d10540e00c1d50001b0128460b40b04002c003080080c0003124200404401c01c500c5942400920810103501065900b004d4a02101d090300c5002d41c9030300018140c10403d1280e40210301c025004c21088124541c80307a81e443c00941c092541980d0203510b0160000c10f84180b0780c0c20b40454510542c0c0701100c0000920340401c80301c0306803092000700380411003502d0600440700310200307a0601503258503407410501c043d0001030102070b00c541104064244800408140380b44624030848900d6240c5001070b1084500070402c4a82d082c2510b0818208084d01c04107010380e503071000300140040380300b01c1c0c5102c028080d1541c035402515590b10102c0c069040703203040c4c09800040c0c015458000d0500e480d152080d90700c080346224580605550790300c448099214000e004016003490003004505040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 760125692 1250 760124442 760124483
    0xf2013230114090c131a0919291903060b0c0a0b0a11070201030e192003120a110309041103060f1005041404090c030803090f0706080c0c0109 62
    0x29114081d0f0f10560011000440c05141d42c2d084c1d50308504440802039030f15092401c5080c1c0c40050f1088021211b80a2040e5925a80e902c14200352030f01e00d401c6030340300c805d180402300300908050160260f005040700051410110300d580c10303224032600340e411104488211030020b400070000780c0c12100d644203001a5a8246c0000051541042d80c4070320000384680d41c60700300007000c42e50401440c0320825020010301c6d0240d803090700700c11b007000161425180c0e4060f032054a0260307001255004c403000020f182c0103049004484000005198041c3d0142200c0c81f21043c1da03192601c201608002441b00d00d00c14241070a0781081078078400da1001c2c100b0061110303220800c44081e00121542e902c229100303010035980d03081c0248030741e0403101261980c9007031070304107100340705a80c10500c070041d0419665160480401e43c04000e2200540c0a20000c5540c1d08052120b20b04003502d14800050ba0f604c80b031310800c0030b640d1119808c3d5001da000149a5200d10002091034054501c1b01d501401140420b02049902e03070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 760126942 1250 760125692 760125719
    0x306040b06030412140405130b04140a06031502030606040e1506031e060d120c021302070f0213020901021207080c07080106150c0f110307120f20132301 67
    0x1040c5481702c02e10200e886000340b1151103a80103050308100c41e40d080003000e00064001c0c1010100c0284003103803111429039821811401250300d564019180d07041042400180c14031100000301c4e0200551440c07600d00e0110341d072032041d1b109841c5000c9411001074180030762100954030f003a80003054540d40c0d050403140307816005a82009000503078011400b01d5400d2400003416444590300c4107240c0e810400015068400751300c070300c00c1a40c1022a0014001c42030501e4402480307824403d0708201040829401070143c0c0c540036a89200b24240f0400c4441901d81c1c0015400700701c0003004510f103035646002e00d05003080e07004922210000c0d108010000c15800c0381034102400723035040c5108054800c20070460440300c2441207140a464541c1601401e00400c1b1245050080702c0702c05002c81d08541d0b5981031103481d0000341a01503401144d406036030001c000007041c841c8801000e00107001140302c1038100042004c011010f0081c0d44076075843c080d207420010142c11700d10449003250800000d6075034144038003001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 760128192 1250 760126942 760126973
    0x81812030c010920150c0a050f0601030b0c03010f0e0402010e03030a02010e19080306121f02030a06050409110f041503080d06090e1c020a240b120c04020306040b060304 74
    0x1070040c0044c0030410301044001003a150300040181108650144003c0d40b2540440070b800303142d000f8100b1000103d90f00b0050424118541e40091606600d107052076203074018007411040b50031504200402000c0e0541c00314a081d40d02d01c481c00e041d281c070340d440107a5484104000107038040c0400300f01445c00707075019401040041c1c021003d6856080070f0074464052900f000c20010180c04040c0045030190070807030a001c3c20569800c04a611040c45203e10074055000541189485500002080b20802c0310f406200004e20701074605008000c07665035021035000b50b00721803a01030340361001c540310389544503002021081c403c0755154004549906041c841c650090401d40d40c42ca06100002440540b1840769043d00348007400a400384598400e240d22042201c2c2c010001144200301070300020500308105084407041030703680c4030204800400050241c9260400940c46148a1580c4010448000ca04843c0d03841044500690703d581d5400010010406402205c0e00b007080841040308100303076600c084128 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 760129442 1250 760128192 760128203
    0x4080a02010606031506080411040203010f08010e072111040216020316140d03050c1203040201020c031f151203031e0504080706020309100507020721081812030c0109 73
    0x203850303c501041c1c0039910f035815046650070042d8802c0044510510f9819081403081240d90061100c0341c00080036604283c10045200001c40410041c5010074419401200d4024001e065040d03d00f01511420403d803009070340d1155000101d0070b042180d5281c40618020000b8811903d03071074950340175001400c030b40c14100d0107845802d094400b1101400f40711401c81c0d0b040740e04100c020b240b2405000107540e20076002c03420b00c03c0c1800000021007007800710b0400d42c03030503a0407070751a072400e4000245495038200b01c40c0c0c000e0f0019400d140c9400e164090107041010407001c0807424200f11103041b0801c0342c070390b440700c20002d00c0009030b08101541908400740490300d039211400d0b80d0081c11004401c988003520010300128041015400080c01c54010310f6008101400b550000b100d0034295000b03450003180c1000044e0000003007400351103040c0c80010307a400d00b0301d5540801001320b5a85d20610307220309c801c080715104202002d117132956142c507203500e001031030f0000380c171b0701c0d8103810050601914055600301c03003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 760130692 1250 760129442 760129451
    0x30807210e060a0f110d0b01021002070506191506050f0c12070309050a062328020601060207080604080708070f060207020a050621091e0f010b12102304080a0201 71
    0x800d02103034001c28001c51080f107030045c6400c44c0034010f00d0087c4a4044030701d066000d0001c3c2c0488021071032000e0202c0501400160403503251030040d8100403644220b8100009180c1114004401c6c2c00c03120040940380e541c00d00c645d695002080815079406802840603075803140000c400d12403000380b0044d008051103078507034074403c80d00e4804020840030300f80540b07000142d0341c0c11401c0707086901c00c1514007620040140c50f8540302001100d16a26120b2400804490b40307150610150a5410014140104600e1000c0c001c0f041c200482c00e070b11454003901c040c06018021500c074040c824800c044480c031903804400040d2054840c50306501a41101105920801ca04000000e5504100c401c23600b1810407105812619921551346920010001d41600b0141c0b15a031004c01402c80045036220480d00c82c00020b0140342e070462242401d45500360f0341103010340001070b10080d0302100090f0240808160105c0032800301d0900b0004aa1080c0021561264075540002c1c0001d1240750340003004034048680c002d12 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 760131942 1250 760130692 760130711
    0xc050a030302100e24343203061f1806030c08061c0b01090e0f01110405010f02010b1f0e010329060706050406021b0a030807210e060a 59
    0x44d00c600425804038400504605124044a03c120400303612550240101c3e881071041d402d510f60800f412501400046e40c40d22815004030741203e018030900c1d0420445601401c42e0040f03d00580c6103100d450f82c8080c0c0003001188042e41d44640b8403400b44541e68180e170300a00142001840408184c100b05141c1c0c0c000700c000310303600b0f00c83e00542203043d045854002d110b0b00c1c0c1d0b8007130041c40b0400c0c0815084c0c505c8030f110044000f800d0816018020607030301d403000c1441c10916074000e003080d4034401303101c4450789846101d0a1141c0c031481914100e030801d00b400040ca440c5031310281e0140c40502d20655210f50304034020f145410246c21742c5641c4510941e42e07a00e04030108001502100c14101e035040c02d00300c0f807034000000481c0300c1c0c9404408400103080c00d03041070070070750381c2405950003a102110f0542d00030410391048a010314240c0c65076030000740108510b009503180603200240150081c01040700c0b8250015210a12150270107001c038104104100b4aa91424810780b5400151001e0100703906020070b01c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 760133192 1250 760131942 760131971
    0x70c150320030a0207062903281a042306151003090203121e03010303080406200c010608060709060e330a080a0504050604030c0c050a03030210 63
    0x900311100074003110306005062803a004082c0e000181099441d6408228400c0001e078617025042d44880220181e002c0359041d08070503820400482110350080e400001191644d0301c0f04220283d1011907007030f8240148075581000100d0b40d1a20b001c01d407420610b2000e100407c11010307844174001c07010219004144134200c60050311100c0a41c0d01d41201d01800b9008041407034480641c1c1400c48650400281c9200c10b40d01181c1030084168416000742e5011401100360405080f55084e1007403a070740010315640c115500500501005030014043d0ba079100a1514140a4a00002082001070316a20f4842602d5a0100d020b80007501420480e030080e900803a07001402900b0b0b81c41030314516102c3c107210700001824081404000a03024014840000b200c4402c800c0c01c409010700012040d404982c2d8003140301003d0314018014100c0d50090b458803040201058011502d503401c2036140c980300c0c1160919042200506025811040e400310680c0d000004040e00020001c0d80701d0b4003688240f2402400c003420 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 760134442 1250 760133192 760133201
    0x1090f050603060708090f0d0e0a0b030403020a060f0b040603120e0a050114070809041d060f19091103030307020f010b240c01020c1e060a110406051b03070c1503 71
    0x781c1e070560302001c04101032500440d4040c0c0d0102d044400c070740c03c0a088101c41450118119441404034a031a0303908e4a103410418034001c080d2440598407481e6003015a0001d548001044014050650b501600c041d843c64940005184400080040c4095516401d00a0300704107242d41600c04160800c503504d1403818a03903c040200e49050312201d4031440c00000310340007548150f2084844101c208861005951244035841301546021840615403128894040c548100504000d000c03900e204c0400844000c4021004070705c107d007010104421102d45008410184801c03801d540c140400700800091035400651400b17040300c3c0d000248296106407090020603071004030308244440003051580798404801e8014a00301d002c107030005180c00c41c101d011500789506414280b003481d03d42030300701c40c040004004003034000180d4141000318000c12542c08045210b1845002c05100340410300b003000130110380202e500c00c04414150796030350640c0c0c50100c512400c0d0b80a00c07010086042e0095015510a206 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 760135692 1250 760134442 760134451
    0x10c0203090607050c040903050a02120f0f090118030605060307051c02010e1c030c0b0c13090b01051b06011d150f0f1f020c010f0210090204090212030301090f05 71
    0x6585441c0c40c03101031069030f0384440816203841c880c1380c1d8242e032144c69510801039464048d98500e40c072010118002410021258064990521b0500224072504076044c1101e4a2417182c604584e6209110001170321075024a01840009808004002003070200541050f8404c0d2000c4050b00c801c43d44410400c407603106464100016004600c3c01c600042d402515030480300e00c801440ca8900ba400c24405c00e00001c200c640c21030004410514500420910204890300701c0e00b00a1200c0c1480300c820110340440d0b14a10900c448543c0750300217074095074042c0044414141601000111a01110904aa640302d007842144c3c2c2c0764241c50403002070220301180090082c6015140441040b02d00c0c400c200d0f0b0700909440c3c5d590b0200041c4c1d04500c20340d42c0c14210a00556000c1c03158030804810030800703410003030703d900e81c01c0c1071056104444884075408a91103100500c0010b00140c60309031800400c00810007844c0c000e4122814900704120b4880000140d8121044c104081c002c0380030303aa600605031601500d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 760136942 1250 760135692 760135697
    0x703210f0b040e0304140604030b01060c2006070b0426040e090a03050d111c0b01020706050c150c0d020a2102120106050a03090c0617060604030b131109160809010c 72
    0xb0080c8072484e0b0f550520f40c2180c030024507d0b42402d44a4450301540c210a070700c40e02c080751103044903604000941180c0350032000080c8040382c003050314001090191090400c014803001d00c610000e020000024039283c01503050b1140310706104404903503499079920a00880c0a18004140003a86504001881c8140a40e040d82c138070741003507807400665001e411071041e070b148040824440b41c0454515590882d4000c2c0300c069000c55005031010003e81842e41360381200003004001c100340f20502c8000107101d6450700342c2c0908000c203503440f40700ca40614040e60f5070810f055800081c10540d540d81c880b003601c107151802c64904084055072000d000c124458050a080e02c1e0001c03000422805000754064040b451440c1408940d5400541d10194182510781008001c07802c4001135185880145d9040303035100d1006c2d94401e145c00c2c2162550500703924001e15940e080410141c2c040e041140030002e001d003060024181c1a400e0500900c0c03150f0407a4400d030140005409140000d20001c3c05002c0c8101c01c08164 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 760138192 1250 760136942 760136947
    0xc16060504030f0804120602180f150c0f030301120b0907080a08030402030c12010203191a10050d020a020106180207020d030e010c08070f06240b0703210f0b040e03 72
    0x1a0759500c00f8a148040c03d99101c3d40900c00018010b000340d0a04810522070040143d442c03010040048112035203c9405009541045a40748a038444109101140d50320010a41c0c503213180c038515914064072049607a42070b01010000141e4907000d06c4c4194a210310800410f07850340d5a400c0c050340d4441891149083c1a800380d4002004940fa0000543e00070780042c1c20b4404d8000d05001180d14880c6c601c80601c0c05030360000030080b2120351040803100740c8000c00002c0c020380182c0e01710100340305440741c00d19114000f0039500079039050080c000c807006007000303050070754407100410f101074000c002034450410340c0d040502070140311902910840b00441d500503d401203440841e01d00701c1d40525128101414011044415804152540003402c2c0355485091040c02442962401006840740003c1155941c9a60642c810011800c5400c0c0c1c01075401c007110745902c4c0e4141d404d0807583c00c1c0b0301c0710f01d0004002d012884000e85001981101c02c1401103c07000340161a0405c040c041100c01c01d01c102e12071500203 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 760139442 1250 760138192 760138199
    0x24030405071e06140405030105070207031403090d08280306030203011a09041209090f09122604021503090c241623100f05040201050306060a120e030c16060504 70
    0x42422100d1300048040c030740c0c2826145c4000c6401c40b00140c5104015912401081080059441044034902d030800061400c140c0c1001c0400c54000c444800100b44000106000b4447c04410440408141c445aa0b4025020381b0f020054014001030006a000754203008955085016000c8403005040000c1c0100580d0743d5244c44491034855040e101074108005000d00042c029124010070031602c1141100051900075031805540b60032134441c02105009000e190400000316090b00280000840301801c03903151745500c0001c90003403541d012034502000110910603d2440001d00000250b002c2c1d030780c180241505d41124100c8862040e6142e0035440170030004400020100301c5c080d90038032504e0100303907050a2428003105001c2006000c080c81d4002412841e1045003805403003022200e01d00c040059040c20b800080841c400100342d00d0117118005021121180305e14964403034a403002100300911008111601d44030740c801706103003c482c4500d240c13510301e0400400b4000c003200c25545803645032615 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 760140692 1250 760139442 760139447
    0x809040b03010603020916020705040b1507170409090209060f062a0a2103090201051215030703050f0c0102060f060121020307031e090b0a050624030405071e06 70
    0x12032980c0d103034140d52103120010058490280803030154841c00e0450a000e4a6901e0080c41d088295100e64400c600700b9518200a0f01c414423240c0300003a0070206140c0d035014038200038243c940000c1c905000b0000015001940c002d0301d0b406460f40c1c0d03108882d58807442c3c4541f4100640f44100c054001d6000c401080701414183c6c0590945c0070307100d48440d00c0c2d151003000980301e605100001c1021307a00b42c43c54001c0324403001420240d6145551231401d040000444540008080340035070820007009a4032440410f10066505c050442c0e800c00080072511001e40701d01e4070030345684003448981c04600c1030314401880ca60012030100e02c140c00807110f846440d074489004640c081c0d1040b5102802564085003800e280d40280001d62041080f610041003009210003101902540608054141c0303103030042d20030010b8254000340350003143c40312001c0303015107400c000203000f140c050101411004c0f0016120b4290f08031580694489c60240c816078600380e585041405522100c4228140c444c0300341c3d0301c180300c0b260 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 760141942 1250 760140692 760140701
    0x804060f0314190b091302030c0102030a080c0f091c1502071e1106040303080f01090509060f10050a090902150c03040b071a09031b070b1c0e060403051209030403080904 74
    0xb803680f5008205070761070344045941c12405079001e0b4418250700700920103500f01000380c007040b103d00388011403074007050646c02004400054059008540c001031081030240d620401d030303495418002e241c04151850024455949000030f03008883c668000d0310307403101e8005c0620a0b0340c4441c0d0032140018000700c040c203003004200035100003103491030200900700c61161a10390260004d54880d4440c0c1c02682803042500650b0351050313001000d55800c10080004141d400b1407515007002d014215032100740c07119a84440c02c10800e80201c2d0700b28022910018171041550403c412841c0292082c08100c0082c06803000c90344a40c1c42003000c5648100b01c200011120b100c024540e040c0600b04851890000244580107a5000c1d10419015440459442c031201000281c2072501300d403507002041c80c646050f01d00000c44c0a09042c01d8452041c45c0b98510003024241c2100980c580d00d0300c03d8403994038181c9000783c1260806d060a00c40d00000600242201800108480c15079802103078035401c05a18104100151 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 760143192 1250 760141942 760141981
    0x33e030f0d0b06131701180c03110d0203010e0102120c04080a03080a090204021201060f0905010f11070b0a050a02160b041202122a010c020f0d0516030804060f0314 72
    0x43c810000d10410900710074104c0701520307140740301e48655441d5032560b509445c200411869140c50b5280f0b00c3c0e000460404c110070490340e03c80d49031150704c0d80020005502003c402c1e0040d42550030004041507044040d030080c00c5d5110f00e80d0269425440d121303640f0015020341c1c02000300380d034490006800400e0280140c10742c4a403403480e022030f0040c505d45c00b01b4240d800c000880c0010702068001800500d80211940f449565145081607225103040c000904142caa43c041509101c08682c1030510b000003440344001920540c5000d982e02c120b0074000400342c0d0711a03400400140a40c00320400c02e1041801403604803403508141c2402c0a04004400414000b0140200e83c480d01000e5501c80c1401c05000c2c500b030624140e118007000140300c010114040c041e0b441d61300d04001076070200000690341c501e0040c2c00c415007a20300500c0d00c0d41c6071510340c0ca417104d941c048201c10349640c0b80000820074500d00038001d0701c80039580c00c0001c40040c031041e4155002100b80000700304483c0002001d15000c40303290440d4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 760144442 1250 760143192 760143199
    0x303010905090325060f0212010e1512160815160e13050103020901120b01030b0403020f12090a0e09030a0e010926010506090919033e030f0d0b 63
    0x1e000c003001d1080c00e001d1319010a161400345104000342400281d114000e490308200d2410344c5050605408541140300500448050f609643c01090f602c1c059031050300d0030307408090140003226a0307116207030307039142025a1461004484503d02084e11031002c245040410660841044c1c10303182c15107508841d00d504400d903010000b1425050019594032149030301c4554001000048a50450040c004007071016080103010991410303080002901c95010281125003010012613203071038a00d000c0b800e040e0740b0f04000078903203e29552004a0524140200312070034046682d9080156104c11400034080112604d680b19001401031104450140d103400710241c5052408245803034640305403480003074210700c040c0c03c10500ca154a10703080320240305441c4c00403412281411a441e189028556038104d080c0c2c00d20a00018418043c10540540500c400b4003000100700100b24076681034a030303007400107010080d02c05a82c0213200d4090318008021a801e0703040b409030300c6140100a110381409000e400400940 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 760145692 1250 760144442 760144447
    0x15120c020a060203010b1309020a0207031b05061b1009020904021c0501020d2007080a0c060609091a061221131410020d0c02040c02101d12040803030109050903 70
    0xa08a40300450180c4440e03485c40e62211f401020b41d10884031580c000b101c0007481041054040d40d00015242c04403680305000000c1d6550003180c11030715203480d90116411180c0426013a803620141c20010b40158210300465450420022480307068500842d030283d040f0000700c0100c0c3c054248004600300d0001e05070a6a00512890707074405003203070f0203020302462641d40e50300b086185001e062000e0b603030400802c04403404e01c0d00c540c842d043d940c8280c00c03504052144107030900c070070440039400000040c580d0400c108410042414040d0003100c10010000d0700c8100700001a02d685090302014031101460002409c1c0300c2c2c410708081156500c004207440d11301c5014041d0089980b085010f040191054110106d0310f00001814070441810329034140c1c0541d00030070840d042541c2d00405030800c00ba0100c070080b0b558850581d0503410000305d41e4504446a041c035804001d401c0c00a6207904202c0c40040c211030f11241c10300b4100d511801180a5041c041c7c00410040000c410160021078010340500103891 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 760146942 1250 760145692 760145713
    0x7030318060c0e1504050603270c010e030616050310081f140903030a0906180f02030705010906050f031f0e01080d03180f080d061202040615120c02 65
    0x603862445250201c03451916800048006940510819070012040e00c00320f80010802c810000c1d0340c0228007a45004010200000709070003100a1140b900156a4412413031003410207006685030405000903502041040791081d200d81000101d2601c2901c12403030740ca4070b0b810410421500c0d6070015180010f40c0c082c40780301090400041c8000c01c505003503664030150144045400c0030507501380711792000780310701032408200000b500401280d500c003000c3d80001a100049203003010091184c04600e9902461800f010004c000d44004540c1029000b02d00f210320050752000110b99110700c0c0d009002c009102030281412700142500a0340d0031129950960a030000c030b18200c0609011294044941ca032111401004001c20a228450b010600d40c5824050600340c0c00142d600107080c1340b03004000d03446c601300207010300c0707005010795968280d011020300940795503141c0c61903a0001598144d1180740341c071100080b07400d050341883c4c02030f03142c9845400800c10b00c00c42450082000f0700d450b405602071940c0c4c0a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 760148192 1250 760146942 760146971
    0xa0f03030209040f0f11040503063903151f05070501110a0c0b0105030c100f0201060b13090e010507140309070b07032706050f0f0d1b1d0f06070303 65
    0x4113641d29415000203141100100440035590200c100c840b0540c001c000600070364070080386695005001c40209208146a03041001c414000315001e030543d0b80c00014810003101035000298000c0003101c2e070140304004414100200301c104216040c85040b01c041c00c40307903624082c2002d021914014400002d0180390a4a82e0089a000c0800a07002604402201081089000700d00b0301502c4250001c1100b200d0341c5c0c02103046030440c411244284110154100c40039403003500a18040c0400c209440e449a00c0b00341c1d1030b04213039414014801110b003459401e02c0011414403030f161284d101076460300c403809683c040c9900207905c06414810302d401108004140c03000f900c402814036501c80d0307495444041407513142c68000c10303000403600b0700d005d200c00081180d00d48c80b005031402092508407842d52852211007900c1c092090b0f82001520714242190300c0360012a034900172070480043d496252144441980c103195240c6044101ea40c00f00d002080780d10385081107c081c12102e4424200002d01030300d034210b0b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 760149442 1250 760148192 760148201
    0x10e01020a2604050705010e0423011a13062106031109090102092d0a08011a0a061e090504090b0108120705061812130e01170a0f0303020904 62
    0x20078000c11080c1c1e0421200507120845402810752440b944071050030195a80303038840c0390700c1c85010304100c1c0003449802c41e96681d03840200b081c210781d40601000340340050b446902240911400820020600c1502d26022a00c8100c1c0c400044041120003021304019043d640d0702004080440c40c0d07041803200720701503c43d910070385020314081c1e4906201c0310b10000070004103207001400f10385513900502c548611034132030885030201d5080d4607807021404210f01a4800490801500f1183e200200100010b5900d03810b60101441101146040e9030050324034080c400611294412000060802c0d160311000d06030b15a20300c0e07840222413030b010751082c1c3d41d10000b03000d460a8500688040d01d01100400504008008410280c440040c080e41020401d442d810b0300c4540081450444503014002a91100410700504040111030140d407525190003031034001c80b941c1540200e2180411381e000101c0c44100004610303c4200810004108013882c0c0e075204007075005034440031801c0c19001d21080b0440c2e9500d005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 760150692 1250 760149442 760149457
    0x90a030b071103160c0b1224150309010614010f03020d1524020d050f0309071d090d02070e070e04060f0611070b120c1b011a0f030d0f11010e0102 64
    0x50104c04012802d101c81c160319103510039800c041041250442050141c2401640007408080c50804a985480c0c10714070500ca04510380e40c8482c1080d00303c0580c111600c003560168441e01c000700040340d201c00403d2004c0a40b0744605002c5001a070303040700968800e4008000c8500c0c003074004a4428078a080f9a455010541c202c91240e5040400301030082c00c2840e80c1c000483c07003a10003026030a41d10344011340607111304c0403000c2030400004009000740c0e100304112401000c4101440b5a460031198504140880946802070300c0e004081c0042c00041c8006004001da80202d1080242501c40c040c040e01c000745201680b40d001500c403200014403d2a00300094000d03d8170ba102d0814050144204c2400e080298100003103d42c4d0034000044a81e6480840d01ea00035a1035801c19030b01d83c044c0116180802d000144002a0340c207100d107000341152140c03001d01c0f41c4141a507280c6408181c0b442050740300d203000c80035200001e00800d030544000703100300ea51500e44005180005907003101c5130744141c01e84c5d00c03215 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 760151942 1250 760150692 760150717
    0x4120f0b0f0105150702040605100503040c09050106020c040c0324090b0a0803090922050109020f270c07051b0108061207050d080c0102070b041403090a030b071103 72
    0x20402062040144186074495030318058070700c096041030300003004981c0e20015120004070203d1748908540310faa110801a10001340446040c0c4002e060080c006d2b40116411140b12003103000c002600798103406841d0684231143c0140c0070340c98405d014000181200c148801c2019190300c503240002201a0783c085100d0354001d07014a07458201007488040d100008601030189103029410030001c04003000383c41c044401280c1d024056155504121010001c41c480908842a03070402c14040000c15440505402c0c030940c0c0842000c403030754040080c0500d0400c2c151950300d01c43d1504407600e10008446560013040540005c0c01e00ca816150f03545003c00d51000c4c0c0085c0412a401980d00d036811400f01ca40c408030859613030171300400401c0c003142c6861140c4641401940208000340401c200f25003543c03c0c10580328021904d840041c2880082d214040c0c805482098450120341c40320a0302008881020340e026010074000341ca5950348010049000f0030440030850b0151312070702c02e01400d10081c4155128103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 760153192 1250 760151942 760151963
    0x40513060207060c080717130812130203060a090213090204020c01090528030504031e08181008010803070b060d0b07020d020d08100905040615120308130201140f0412 73
    0x54028240850141c614070600051182c5143d104145c45806980061042302d1090301d4101850844c80c0c0b40107003a84240c5d43d034851003c01210300711503001d003485140220100c5440781c40d410b581c1d904a425214001e5046460700b072808180881d0368000c01e040a1014000510703009411a4070b90840e2164070003100c80b038100c0e40c0e80d407a900d21030352200c100807000c0070000418008242d8018110707104a101c000c08844580b1130501c4664800040d000e401500441d906942d040480e000b08400c031103070007015210701c0903445908480f6104c0e42100381620901401580381c6156500c2d80c1c1c203131a000420240c2d201c0740c103401c21000101b224650a0207007045400604030001d0b1388034082c1c10300c6003043c40c0104100c20103003040301c03101030000348078222018010000b981d40c8590a0110162482079003501c0441c05030040000d061000d0005010054001c1c1d5500321070b0b4540146402000740013100181c00104103400c003803e11440d05004140f6890803400c0140b80c55580c800501703000b24024803c0d02c10f414030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 760154442 1250 760153192 760153211
    0xa0b100e1008030703080403140708120f011a1c1401170307030c0b0403230c0708030403050d1407050109080322050d180b0f030105010905010c050a0204051306020706 73
    0x20031a01d401650342425251914101000e0035543c0c00303441406030811042501050505008844514030035540c44d140e9030f40c485084c104004264001c00209008080350800205049800ba803114107031000b041f003a80c200b041038904202107030082d258104a0101d114a1007220040900c1b40d1502d402e0b403001d10b018998545070907124039002058604120f0f4000300280000030fa800010402403c0d0300c090040065107503030500300d450072519900b206515108603030800388070325100c0180900d148400d00b2602d00c6c6031940001030b224015071100900d140d0046e505d414005000d40023115030029002c0069007000020b0300c4460a46104600643e00e03414000b007404000c440d220034401d0b90310359103100c000c030603c04c0740d807466651282e04402c50104030303a550f0840110182c00c0c941c02c0041482004a07a00c0703071400c8070b80e52030544c000c1c4900d9001c40c4c546e07003001030154010316062140d1074000e0701034003488603e9000d100143c2001412030b11607180c800c00300f80000e801d030304c05400c0c0d690085c18000b403560360 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 760155692 1250 760154442 760154459
    0xa110316030528050c0f160b010807060c20102601081b0619020705030f06041a0604020702060408030a0305100b07111206040506043c03020a0b10 64
    0x902074a00c0c3c007100700c0c10520b103d910001503800c4211210460001500c2ea4804400041034003800100e04200000014164034005c03240c203030701c00400d000e42d10103040d40c1d030703603c4680e95076003c05e200b02c1010400c2000e0040200e40c80300310240c070030082c010f48074511100590004022071036001807e00403454410304011680d07440301e4a403240e00f01c05000d00c1c40d80c0d410300c4a80d070740c2e076030841118208054400d414006107480f400b0a90f11151849450309100c8030701e0020194480603980a0300d4080e1087c2e03251a0b0b01ca0b400000e28502480d0030034110044040c040d40a02c07001c50340106400e801540800600c80180c4030480207000400c0c1c1c8001441e01c070f0880040c001d003940c20281902540070003c40050040c084170b00211011140c8c0920000100c921000100d0040325400310348000794041c02040000313121b0080744840c401d9200d11560200c40301300b103403069003a002c10b0302e07241004056a0318000d6a0b0344030f02c09041115009004407070804182e0f1340c0f060000d010458500b17a030100744110401c4480c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 760156942 1250 760155692 760155701
    0xc03030108060601030204141201150902090310050403080f0c0f040b03012612070f050d0915022e0e0f0d0f02070305121605060f1920030a11031603 65
    0x43e001d203415440d091418524482c0301d19041e02c094401c5100c408a80342c5c2030760951041c40c070740e1002c1140f802c520baa1049410001d40003503400034001c0c0585280c040c5400300c2407080c41c1c411981600c130b084c615200c1850411003d503000f095030400480400c4507a83c00b420400c080c0c0018503010003203990b0f83d0704000c004c0703800805040200c0c80c03c081008240d1003603078001c05c8400c0c154040b134858030740b9158541070048165101c18030240c2140514901000740e26401055002580d0001c02414a10411500c00b00e80e591040003403c014032810f035050402086d10035410411141e1048000308001c60500c41e45800c01459040c1100c15a11429885070155080380c2c060305030072424005404c0031859031f00d9054071803241400621070340e03900007019100d070813079208030101c82074000d411140e5519105030f880c518001e00b66034442c00c2d40340d240d0846002c09500d025105030024000440c0307604540c00900c0d48003076000a4041c00300703507031610a61440c541d24500030350320805d55031090300080d0140001c094200c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 760158192 1250 760156942 760156951
    0x604030f0206040213020f1611031203040c050f010528020d2609031e04440304120b0f0a020f07030521010326032202150c0303010806 59
    0x5401c81c504200140c2c5e5000070115200c03c0c241c1000da1744164156009071390744518815400110501c05202d0b09025001030550001700e01601102c1104d00459035002290000b160020007500140c0c0c03060100f410005006200e032203040c1000307400c105203010349507030360842e2070041103200c894409100c54140d41001030b03c60480560400035001410304002e00084d0300d00d82c2000034415140c6020440a510807c11500c85802040005028055140b440c044581c031901c1194101080480b2200883c020a000b03a03009a40c4c0d806c9503450911020240411140c5030000b420703ca010900000800032070543ca20102688101010041450724003058150003401070881008280306001c1d20201c031065000326455240c00d401e00b00d0300d03110141c3d051710f00385c481008115681807030b130400017041008124660720420f130180801a02030382c1c1c0d00d40c3c0a0042c0800c540781541c000300340c0707a400c0310f41d400086000300d03450001e0084204080b03108480000e0340d2020707103003503000d503c0040100903089080c020507402 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 760159442 1250 760158192 760158197
    0x807110a150203090d0804090507050318030f0a080a0b1c060513030e010c050304090c050a02010b030a11010c0203030c060705030403091a0a1d09070e030d0504051f020a050a050604030f 81
    0x3044080c0000954071302410341114001c2031890303125000c2c4010f1006680007060104e0040c840b900e44a240100107030030694940c9442c10490b10340000d25200801130f0b41c01500498007407400d00c641c814040703984ca8405003100b10055544c0104000d0b5407162508201c03561a00390540701c0400107480c1145c1103030740013803041003c4440d40c180100000c1c2d00051100362040d09181500070b00c012820018194410340c2d0194243c60301e4586501c070025082400303002da00c121600200070490b05a81070684a40148070024011070030042005603a41c0030f0b010050740d6500141c2240c2c10034416104a40c90524142c0d40880420700200400c030805034811003c0c8040c0044040c3d00115240b200d45844a0b4090032480e41c0500521403500800e0344200001d00030034540003020107000e03050008015040780e0424442d070f802801b0b0404c10090150080302107500301c1c3d80180070f400c401b040080980010030902903020085001b0300580c080030940400c180409140a2800350080c2e00305858003800607060075510304107 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 760160692 1250 760159442 760159469
    0x5030103020d080715020307090f050d03021509160305070509130c03031b0204050709090c030c0903080f090306011e120b060d06110c0a0501050108011e02160807110a 73
    0x589500c444000c2c0e49601c0528540c9420840c03408a0f005c00c0800c040c051094400300030003881c41c2c0e02003c3c140403540308204038001c444c0c070751043c0084821400405030140c0d1020711262070061b10002d095900c8003002e0b003036645081d03807082d44000041403a401940c850780300030003d0200d440d050310b00d99001603e211a0800c00211070307551000394205440302400303001605407908040ca4005ca41c4860040e0300410070400c0d845c288902520780021030098140080c649451000054024030403130b18084402d846845138030349940d54282d0658812040c20020000503c203680e05910100081c2d0b02030b041c070311509032040c0a03001200c1549206948030741044001560001c0120b09150002c5802080c2030303c0302202c89440b41031000180502620702c501500c0000395080302000081000002c49200e24020700c9981d03a034401e40342c05d940d4200d0071001d0b007801c00c00300c0d8050600190b0090480e00c1d100c1074a80030543e603d0b1600203a9070000203050310081d05c036114051442c03a0902150340a01045141d410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 760161942 1250 760160692 760160699
    0x403051b07050405160f08060f0604090c030c030507091202060c0105070c14010207083106030207020307080d08012c010f0509100b0417030904020d0606260c160f120f050301 76
    0xc028006d803c0b0300038180001c0b030f00411075035154180000c03100300300134000d10341e035541e40c01d4010004c00c40300280350006803030300040070f501d01d100e401002c0c054201584c0e05440c090502d9800003800038501f0f000c90b8000e0040020190980081c000d89110703400988442c46c0d0300c80b01d41041c00c100c0e103002110a20b00c0c1d104000100c00902c0c8002070b51b61071038845080d044620180301c000c4070103032001c0290031540b5000400000790790b0b81c140c006000ba14030039426100701d180c2c1d0380c0c911a60350108104c100c010a40040062002240070003040b4841d05401300c000f0902e034468510610745c0c110a0700883c540d01c482c0c01d01800079003444580950080032414040408601e00008102d6034001c5010b00c40d080d550190380307000200410825190a203d00038000c55450100300036234001002c0c2d80c419a004200c2841c890801d003d00070003145244c081812039180250750b12859002d09512000184c50407a101c000e00e6030120301d400401e00d47d041d104041c42044a441650702400113480455050b003002801c00040c0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 760163192 1250 760161942 760161947
    0x403180801021309111626031009020c190b04171c1104050a0b18120a150915150f060203090907030920010e0d0203150403051b0705040516 61
    0x88900138400090f001d50240e0003e0803a210b5020010b455038040c150513000c2c040d020301e5682c00315203c100361000200c501304d46480940401c441c0c1182450008030200b2a42a560b001451282d14030740a484050203440381d01301e0803e001c19415284204808204010041e01c400c400000b842c96000c0c45041400145040d030002800044004555848240c0740b604041890103440251000400f62590782c0d4454150010b560800414840f8a110400b42c1c0c0800b07003030140400b01d400000c000030b80400581030701c9024465605031190610540e440201001180701100c0f44040350101060204104040c00101c6079604c0070b0707800c03200071070362541010000d07580c001044480030882595000215036030300e4000e400030b005094000d402c0d014890801d11106000d040b0b00d040085090f206c594a00e114502400000300703000340000d4050f0f0085020b40910a1100d2180da40507101e440e0ac2440e280080c01e010000320142c1880c140d059001250a10140c5403c0c0202548807403040b0458a1041001000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 760164442 1250 760163192 760163227
    0x905070e0a08250807062114070e0609040203041b081903030e0f060c041d0105060d0e120c0a0605060f21010b0a0b09093709050105040318080102 64
    0x4241c2d090f00d40040300041c50201015010040a0f15026180d4041d941c1d00044c003210100092158560120300313001240040d184500300c03100300789400c001d016a4131040295800341180c11020340c8000c1c01c0c0140005036560340019849288200c00d1241d1003166000c11707202c0390303000f904560b00c0c1c0e80041c1c80112a0000307000c103180000d90903140215401d40b00068140c00c2c280d85802001c0580140c0301044041c00307444004108807031404160007164840d1207501c00300c0800a0003041e074020f5040000c50903004040d0402202060108156140c02290000b00c0a155101145a000d11b4014810b02c4c0b060200610070b843c1d01c0081a03403500200c0f1110f070009404550943c020884c03e04810011103030181007540207581303101010f00305081c941d4031441c00000342d401090754030740f00340141400200e00c000d52290100520401c1c0036022020602c000c1b01d0440015065681c0080c0369580d01c0c0300b0041842401820700580c005e0700c400da070300844540030300141c0c0480c0e086586e45038010041e9000c1d04540c0d144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 760165692 1250 760164442 760164463
    0xa061a03060906150a090606090e0c090303030412021501090f06050103021908072109200312090316090203040201091205060112030c0212100e070f050f0604050a0905070e0a08 77
    0x31807040708003941000071600550b1b9000501c0707403031804e2008074505030491070300815111401d0406d00f02c1e945281028a00e0f204140160750950400c1c40070400003100341c2d841940c0c4555030700541300c03520424030030700021207426400482100e4454012000b100e580740f02d210040c01082c6425894040180391505854405803502002c002442c0300140140d44101030030101000c564140c800c16070900b4114101a0080400a680c2103200301802e441c049085040d60903442c101401030150b0140682c811126030b0004a94035400d80140e03000660020701110258003c2c000ca45001616401e05000060480940d42c000404401d800381d14800441c80004a8a04690560031002c005580902c0c1c1110f11200703104009400c002c0c0b413000441e550802080c40402c0c500c000e4010084e48074100b0100740d40c0e0b04580300e10480480000c0c2d00348070600781030410045141010380407074070301a44c49004c522003030615408170408968540c1400156603220840e00141903080f11081c6ca014207080c61651141c01250303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 760166942 1250 760165692 760165711
    0x51801140606030a0605090f0405070609030312051009090f05010c08310f0803040b0c030606250c030c030c0911041503110406031409010606021c020304080a061a03060906 75
    0x299084c4000d410600240402400351004c5040080341104070f0041501c080b40c0e40d00a03500081380e150310605646003181e4060351920412a09030400c00010440642940e941d0b0301c0b0184042402c0e40d44c0c1c061048114800c00451004200c42d0808608440148461004014006c1c003403007140d0300148205148039132541c0501940070b03000c184e4024007200108004100c104102a803800b405281c0c1d000d5031286026502c3d50b61180c1c0c1e40c4181c00f0b12440100c07021a400141480252005007580100f150707613051070341620200c840191943c6c000c45026078011941282143c80520070040e0341240070b4010208024284627216007100c419420303000d40c3c0100c412180030f44038003000b4140b280e0414050590400e201070368407070b12a03030014082c0920a4416055141d44004102480014400c0404039a02030380a805d8551341c41d4003400b0710400741149042103120902c4046610b580501c498080366100b4240012110018040d0540c11300050350158840d07081803040012100001c18603aa1100d1241c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 760168192 1250 760166942 760166947
    0xc0301061d040606030501091503080307031a090f072d0309020f0910051e10030c050d0f0203180109030804080904060812030f0c032a07080a03051801140606 69
    0x100a503208550710118254414280200052a9601a4070183c107a4210603000c0c40380b031510740301c5400403500d0b0340b00041c001c400c00c1000482180c4a50302000c001d00c00c40d01840c0b43d02d0b43c0000081c1d000b0138142c40f0544801200802d1020aa0300f0084001ca45900003960300b00c40300404408840034000340c580c2c4818141c40ba010b40c0110350f02c580030020142c2000305500c5081c00c0429007400e40000758050300e40511a241d0400f00c425804980190083c00000c107081d9032505da01d0b404030042d000701180c000910905000200340c034102c60180d041c11b05100c20b0016220b141800804c2103010a040d0100301692400740d6580229522501451307205400010050340c4a40d048081130007424594007c1005008503c8601c1c01c1201d40f000540c05200110307007415041e160000108410b01c03003034a00f010440ca03a180b01c030000b8541b8154400c400710744140c40c0c41c02c1c030881e0307200d102d1a40c1c40000a40e0009584030200000d200c2e001020b1030501d014003008001c40000c0103400030505502624017485a0f501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 760169442 1250 760168192 760168217
    0x32e050f180742090503060108030f030613090b09240106121505030f010b03011a03070e070e0406091d160909060f0c02030703111617100c0210050f0c030106 69
    0x1607007100c41c80f9284180c80445075400c0150001c1c2000084d020780ea22901a2000005083e200002034500ca0f41091040c50728503180c21081200b11600ba250204041e0388030000d01021a124040f1144500e007480080d040000c0e8194000c0031108010016206100d000740051041d0742d480300b0030819980c403c1000080141c502811004600c100b680b040b64944144240d5040c0d0180640000c0c45080045e0002c1c8500c1c00302d4620040317a00454081c07a6015482a1001c1080d1810311403050342101c1c0c40d0030660242d4009034041004e546058001018940e00c034650a82d0000c0500605204482c046000d048400030340580d8580e11001e81c491042d40e07a8a6580300c07400c0c06043d5001800c141d03451501080703001c030b031050301039125000f00c20264042841c042c18000a0301021032881d640143c070380c502a070114185a0085481c140c0100030b94018420945240d5094045124081c0c83c0707601c0c1e400902002440a052005580c0003c1c184000003030f140c8280483c0764013540c2a01c4c1510800e0400b009044034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 760170692 1250 760169442 760169519
    0x60409050f121b010b030c3109030e0409050715110601140102122b02090d03020601091d12030c070b010b0403060f0b032e050f1807 58
    0x40190180c0d0500074814070255007500c400040040900c003d8640c41c404441c403503c0c50072115500d0809070550005031055040d032403e00040300c003410503500c00c00d24141c02003d42030204c2c0c40c14070134075010070364420580041c180c02400c6200398507070499007440050007594516465040c40d00c42d00750b0400c03a20221500d8940200d5101d5400321000040b64a1980d5402c04a4001540081e109015004101051084506440c2120b030061074001c48203409140e07140d445914040c40c180d050806640c02d0145882942d11303070032a4800c1601982c000e1106504081d6800c08072016803d28152800c441d40180241120110f446900203598072903243e00d95407100c0640b1a00d21a80070014445291100080f44182014002d001903c3c0541000c200342903241c0343c0702701152500a0705641c164030030781c04500070903041c3d155503a000760545071109414100702505000c0c0d0b94140c40c03541c1c0500e82d550800c001e103142d40348121650419000105805860008092040340000050030381a9101c0c0703141610441 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 760171942 1250 760170692 760170703
    0x904060f290f0c0d2a0b2205030915040b1912140601030f090b0a020a05071b0e10060215090705040c023d0b011e0206092a0d060b0613031704030b06040905 68
    0xa807a04070300800d43c0c2c6107103006916a403143e01c070381c0e1040c0d401d0309a0b1412006401c2c01e0303a0375a1980d0300980d2070181040e0340310444c0b8002c3c07016501008000d000c590300c004118090109461110780700c454180c10044005425075104034444000c0c149047c1d005000703e03040580f580d070401f10f480001030b644c441100c0116224868a2405031003c14040c1c0550591117050300c09104554441c00c1c403000907140e03247c103207180c82d455210341001a0302450800d62610041900250400d07660f00c21501c629039500007180070355186200120250704201408952a0410032060840d00c040f58035019803114034590f5100440c0343c103003442c2e0009980c0c070300202e110307406404092008603c0c11089084442c2560b0025900d0100f00c4403d24240140e2040f0031405440320113048400d1000b070041e442a90b205020b1000e01401380c18140c90080e102c04207103211391107070030081c000042e040c00781c4228607046080500c1080403110a40600100400c41000445c103405480c0350410030803200812900400cbc00c2452820 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 760173192 1250 760171942 760171981
    0x9131b0902031006080a0506090103110d02120d12092f0310330605070609120e15190c14060703020904060f290f0c0d2a0b 54
    0x54800003c0c040e0400c12030011908a46140e62181d01c6540d404060409481065421301c0c1c02410340700040c00040c00103544c115031802d01811210900215400041c1203030701c4516880308680101040b00d0046921800d01500d516210344140140e031a43d554a2203940500304000c0341c5d520380a140e21110710040d200e000300224005007100c664064a00c2c0b524020003001e4207038401010341c0001c2c00340d90922505c000b1450b0b2040c6c90304001c114540582504c4541c0958001c0340c0720740c2e40d40e0645002070b00351401c02003000556aa200c041030f0440c0300384110501d4000064411160074407066440200141e2446217001e07081ca050040741103d0318109008a00444400346a4024002007101840d41540036200d00b900442d8244142c554070010388098a41c103005403d1001c0a2045c1b4481c40611b460500040405d07107210f5a250040700c0c0300016080d00110f02c013072040c0d00032843c00315106502800d10a4242d841c540920800310003a40811390905112400610300520040022040c81c00c8e00c0903043c1c1e5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 760174442 1250 760173192 760173209
    0x70305010c031a1c0b06010201240e0f09061f170d1b0507053d0201231b09100c020411040315020904150909060b09131b 53
    0x620380581c00240241c05207021980d980d004070f030001c010314030700000e40320010a000c000741d01650f0729680322100340140041400b4159074a45025117072140c50301c031b481c000720840c2582d0343e4000d608045031107041c100e019040c1c6d0307600840075050103803a480124140303800800c021310602d1007250b0307410500031001c0c06d5841081d0711000310f228000c0168000ca04900c00150075566000b0328590b545403017941000e007110107000d035400031606007c1403d1401010782d03210040c420307150000704c441c1e010792602c0350408402c0307654058080000c017480f07409001c3d8625000700c80340c0c074944540c64040f40701244d503001090385042c201c003000b1103040e07089480100d514451024008680703c611410001d07010740c200e201c003203000340e180404548441c80300009560903254056584c0000100060f0381401941100c060240c0c030075586c0460983e5007802500c88001812404c2d00070800100f0f50503d00210384400d42000c4c0030f0fa005008000801229040e54000740703510440380403600015401404504400e50040c0d01c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 760175692 1250 760174442 760174451
    0x90105090a0515101a0903010510060c0201030513080301060c030206090304031e0c03060609020702190b0a2a0f0203060a140c0f0d02040b121f1a1c05060a0e0c0304031107030501 78
    0x1111405c0050441440a400a0082d0f85503050381c000d100e8540d100341000100e40105590054ac8290802c42d00400365986501c82001075448044082c0d01c02c0c1d003c0c3d404185018240010140c060003401d601c07452001c05582400d1075502c41032600c1c030512020503d115a08a9132908008000035054084c4d500840100301040e160846080203520101c4268407507950514000c041d0707612030350b1081c1543d921001e03450402c50b0006003039401f41c800061982c454510341080c02e46001c0701d280f5011000f030146c401c0c034448444600516013400c80191003070340201c2c00c00d0070403051940d6110000f5004404a20169540c0d1140d0702e0104507070042c01c0a02e08594000070380000d1380f0071044080c008515010200d180b0301d49694143d00c2d0001d000c1d8860700490f0303841750010409042207001c01d02d03044611159a600c0d00d140c046aa41c4003807081c0c01e01c243c003103944506100742410030300300c05406010400d01c03c0741d4504044540c0842800010001000c000040d14020a0340505003c14802107912800070710 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 760176942 1250 760175692 760175729
    0x9180c030e151503070305030f16050d051c0c1d0307030b040503130602031c0b120610090f060602190204090f0507060807080606070303050405010b0a0e090105090a051510 75
    0x10100e110988082c0c400352141c502043c514600890004112980700005518080040e03000340241d802640c40301c4429403150381001e0108205020004c100002035441c242d4844400d0035a5080e5004243c2c0c04040c1c0349026070040e885a0420014202c0e58000712846030801c0700314000038a04404c68000400c0481c0d604144420050008054000c40007103142c40480251074000803039503400f6081d008884200180d40001511025038004442078030050322065160200e40c1d48076180c46000c0e03400e500d00000340d510400c0034401c1881040c091204100007441220701d0580001c1d0b0b6040e240c007103a03c40304000c20b150411551150b000c0c01855510040b201d45080b0340d82410754aa807101d100d544040f44003c00014446403050f40b04038030030f41d80181710390b0601c036030382d24128010708004204440965840c10b12480c1c560321007400d00700900d80111803a035140303418030381030382580c0300540350781a0b580c03044586100050f008901500d0722500e0841d204556078611403090070443c0c0035844220302d83c0c0b80c4031024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 760178192 1250 760176942 760176973
    0x40e060906010f140901030f0617120405010c0204180c0b0d060602060106140c0f0118020a050f06092e1e0e0105040b1305100f0f09180c030e 62
    0x184a1541180c0060341503603210019540c0d046045403110015402441a0340e0050304200039114040044c500080d9031520444600c0448003281c110880c592940c58845121072410040850101e180110b40c034286490440003034000007100600034130454507150389111103000c55161800064002e441800d0315070b0746d1043c594490344000400d0b0308140c140070010600c00e00001f0300c24121001992820881a4030f00350040d83ca4100c0950200c850180f602c90083c400403d000300b040b840b69003c0f201040c00380e87d00c10000d10030a50390244c2c0c02132410300450740990341c41c80305940741820181d541a451640c514225040388100c400d00e41e0b8258840300d200000a90300055200d401200701c28100d030b0b8411458400e90341880c01d2000789000903c10030040c032100107800b02400b1303045404203610040030303150700001c0e10b250031010454000481e40a04015840c0e400305404c0c1d9010100d040206001d0b08121031802202841d41c003517100a603c4107401c1d88128403036446911139103100010703102c08840c01c00c1603 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 760179442 1250 760178192 760178219
    0x1214071e02090f0c040605071104050c0903010606020624030a08030709051e0d02040b04091a09070609060504030215040e04050a05010b010e030604020d23010b03061311012304 77
    0x50303002d8400c0a00081030059000c01c40c40c002d290402e41c59050514246045485070700100c3c0844e42080805042516600d03140207450241400c2030310b00d52140c0d103103824142168034980c00082127500180034403844106e010b10b5801d0008a40405120901c45100880e00d4041c40101c000c0c88800000704008003160f0009481059803002c440500c100151440c01d50841d2144443e1658042070b9130003200018907140d0b011a4110740e001c0c0010440c00f030b40c2c3c0c07101010b01425840c40030120401208201c1c1103001804100040c08681c100f602004d810400b004166000b9800002c0c010b81c0109600ba81202602095030010641d120803510b1520301031030020748480c4611000c50705507007800c002040f5907000b12035482e0708070000783c011303c040c0d0b6072502000309400d0350140540e440a086010400302481c01071081c00c42192900c008225968907100f894070f0417000401450081c500070505400090703007807942c0040440c003460022503d09510883d0a40b5408507403619419140004d400144d20005504 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 760180692 1250 760179442 760179503
    0x30403051e01110901050307080a060f0806180a0309090e0111030109140709140409081e03040c1e15030b060d0605030105010911040303080a0e06150f0409121407 71
    0x3030003420f07810a007140c00350041002c40f0380414014000140b15920911100c1c1c0c0c0008018008265243ea0700d0600383e5400064005414070b4000004001c00500d150080c007050800030f000407d01b0350456100100080e14901480c5106038551011000d2504250000f00c00c00c500c100c0c4003550395070369a911100a00c00060003141e000710510004200602910021040700e2020300031054240d00c1c2801c1000502e80a0801c845480302401034254401510301806140c40960075401d95a05160520000c2e0041a9010000c00c80c1002d400500c1c1c1c14030b80c0305110171a9080d440480d07a41c0c1a0070700c260003800e43c086205800c600086500240c0f40c07020740004048030000e078000c1240384d032a4054041610444074510700804400c20041000a1141c502c0a034080c030b6200000645c0e032100561a4203099069840340080c52f0076001c00006440d010303145111a1400300c0703040011010990303034032040209841000c400d024981580d20314071584441150b268982c8040302d116210b10800c001c9104005440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 760181942 1250 760180692 760180753
    0x150809011a010206061c080f0903061305030a2d03021309020f1801050d09120f030c08070e0d0c03080d1503030c080304020105222c010b0a0203040305 66
    0x1440c80494403031084441d00904040c2d010f40f042e9641d16060040c41002e411215982d41c0b40e8201c20004950440080e06401d4205001507503031792440c0042502c1c0840290501c41c0c502003122108000880000454100c000c142c141580f406201100b8400c0708001801c8a079219410307400b09030f404540c194000c001d06010020024290f9840301884000c0340a03a071852a20a1000c0024940b100c0e50b40012000988052504a140019884070131042d20442002212841c507044410004240c00aa080c1c4000c00302d85401c019000c1c9210001b044541c006e003100090080c411400d43c0280c65008090610030340000c02520255500d00e0014041d900120400c16007503e402c0d58400d0101c19500a01d0413283c1590324030700003032540d07107481025500c0170b03004034140704d0100001d8022200d48041c500c4412803102d2121742c6a86030005000f500505000c011414034070786003c050009611201d81e0f810356104690082c3c4926221030107a01e0b6105580018003d0b1080340341c1060070018980400c45d00d4281d09 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 760183192 1250 760181942 760181951
    0xb0a060e0f0405010f09051218031f0507050a0e040905030d09050303010e01050904150209030316080c0111430f1a010609060c022107031a01050904170415080901 71
    0x1103210360101c860700c1b40011308907044206a280c036802204054840d0b460560380a01c07001740408006403501c100c0c6500c9011400c0380d44d0040140080d540305860b44646542400d40c13800100c9840244481d505210540c412a6140614414440c0c10030031781c0c19000305210b00300300303040b154180960b8a400c244610154004450000300c1d080c1080c2c89401d00450b84503064200061003500020f000e504050580ba41521040c03015105900e84602e00031103842c020104256034010315440300c0c0c03c3d54121070244084c814108044000034228040d25511002100461a15201c840b003204040c00c104c0000f0407028681e20841c8410300498140c400c05262007a800c2c1080c210780210075440d90300c424491280496260030042000d6800303581c584008620081000d42200d4000528128032818448140c425500110050040251561007140752981c5403200342060b6141100044144c1c1c4000d0004255110500011124100d0501075601a0010b103c005c0c11455018100a120400898940c801503082 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 760184442 1250 760183192 760183211
    0x160c0f170705010527030a0f1202010902060d09031709010b09090109081b0a050706050c010c02030f07060c0908010e01050a0b0111060f07020307080d090201020111030c04030b0a060e0f040501 84
    0x12a5411101c0603141c245c180a20100c1010100d049188002d5042204a07030f182019035051002c0384a20b4490541840500124101181070050090021080da89005075500242c0c2c1c4080a4a00182c491400850214040e1600301e410408000c0c4002910b02c40c0014807074404419007025508110070341c0c101c4165070314a0700c041e0030ba500c03070352014208039030800054400c24004e4040781a210848400c032500c5030342d91394403145802d616610890010724081020710040000303014a1505220900c015400e100c0302d01090200f92145800c01401c80303540740782c100074080c0030b624000c0007400448000c000390441481000d001e4101211f034601e00760b242050741c03103903503016007200950740038907170003d00d83c40c1c0c0c65104a40d4641400f03408002984000d2040000140b5074400905500001c0706011510300240d10000e400c0d11548955015521803d0007003022080e040d02c02c0c0c3d812240c120007980038544840b1142c100410603a0004107a851500041114000d4584e582c517001d10310560081012002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 760185692 1250 760184442 760184489
    0x20c070f09092604030605060607021002060a0e030a0801092c0601050a1205030306102c130504032a060203041b080c03030406050c0c120a03020d0e0603010b160c0f 72
    0x201c080b488489000140000c5c004900315038041a40110080c2a280c0b40071156000112102c184030300c9540141d01403c00c0140301b075214003692498001d42c000440c10b1070b29a64025140800c14010459041e40d140c0007040c04500c010020070a00459038003840d40c11403030b00c001e103444907001d019080c0120504040000c1d50000306107100745054100c0061429501c4250400085c405401207800421000502c102d0b040c6528002c100390800b102c7c2106107400100e60240700e5a5400201070450192070a02000007003504405011300c445024501c1c0040720003485004007c00380c0c1c0f10009414144007100f00420020120f66940f001403402d2518202d45a980e03032001d2b903414841d1080d503055041403004004060040015010350750001094a643d0500c1e400030541c3e00d144808500351642c41703036103075000341501885000aa01e40b685820601d40c2000b00215149100c18850099003000c001000e0440c3c40750012111030310756000b51550304040d0344e4982c0c044941b1050148519a80340c60403032189064 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 760186942 1250 760185692 760185743
    0x31807170c0103050a060e012c2e03080408010e0c030307020a12030c0503070803070e0f011e090506070819050327012903010b0a03020a05091801020406120605040e0c04020c070f0909 80
    0x203081a015408d2b00b9521002041113a225130000015500c0c00100800003485420280010305004c0e400012148242700000d0302c0c06078150b0115029030401c100280158a405500c2e03825030708998806068107010745000c0300c1c1c0c8c000b1184064040c0c000461400c0812500c0002180913402913625403a1a41e00740d010401c842900180329404241d922a5080b101c1c90044001680b1803900d00b8940c55040d42c40010844070b501c001d90444042800050a00241300a1a0351680c18003040c64060704514006c600c2800c0070182c01480520341c1c018000038110210250000e600080702c0d02500c00b40c01c0b04524807042c601060b040050720070f50900c2c0b100131080c10030b0303410001180e800604640d861072400003440364aa401030580c100c0c036501d10305001503100b001d00007400209001da80d0311410700400c00d14141280c03815001140f15609002a6100c044ca0014041480000460b00141d44103120f55445141c10300b00e030300854000d18100c00c00214510b0070f42c400710481340203c032003002407071040002c4480300703 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 760188192 1250 760186942 760186951
    0x60c0807020a11010e0a0308030a15031728020a020f0d08120408071403030403170103020d060e070527070203040b03070f03060506031807170c0103050a060e012c 71
    0x180d00c01070903603000c0380300c005440050f160181040d4217a070100c180403c0090304640c20950303c1b140000140500e818161240e9502d60640c4045c0284103411941c4036859a0026240480c80c50700100d1401e40004400d128120003006500d1640078145041e0001b948510140009900c01d4601e0482201e19007800845031280903403141245140180c03c511079264050060402c1d00d0809040c000701c80007599406005d80c05000c580c00464aa2400e490010415214000d5109451341c0160042005032503d118051185600420110b02090b0f088409460521280d103c00e0b80041c071080f60b510005d400c00412032216907801c803680301c16070701d4079401d83e0390303100314425480140001c00c0051060392040e0850070100c00e19250102d90b1542d100002038064000356000b18602030460642c1003500030412407000100021902d19808105400080340c60700c40000f00281419210340018541480d00c1d0b1110000d0300700080100140c1d40c445010f000c141c1040c0080031102e00c8801600391150010040f0301c1e126 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 760189442 1250 760188192 760188197
    0x90308060402131a13030507090b0d0201050306040228051b0703110105030a020705070b041e06080114060c0109030c0b071d040e0f010c18090603110d05100513060c0807 74
    0x2940b0b41a07440390031913104448442840780902107040f00c9440c20704284000c600031002800100e0800000e4400c032445560913a12545400110b000181d07044002e507030348803030111401620b0344040d81c80303181084560742a50508800d1803c0d104002c540040140c50b0303031080040c0504082144030401e69840d100b0340402f8145940d000440601c41d8031600085521001041c400740c14040d0550ba01844d01c15030303421072850108046000c2c0701c0030107040ca0900302c080f0004170030308060b4030f45000904181018007981c1c01074140b0701007494480e282c40341117944550b0b000008200a04103401e004207070b040d402c0d42c2296082017038000300d44403611485030b600c0e5a00180036040d40381210001000001e120603865026180070710861156200000c0c400c94500664035142d034009001c03207005012442066800404555142c080140041401403030384261880703043e01c485014602900380386140c403014407040d031115403e0808000d0aa00d0400b801400c0314480d4000740290000e5800598035800100c43d200d00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 760190692 1250 760189442 760189477
    0xd0b0901050609090c2715131404091a04021c03020c060a030f0c090905011e030206070c1a04050405010609050f0409061803110705030c0a03080a0207050a0306090308060402 76
    0x8561500381302482e00f110550810703914000369014178500710403904440c11901010041d001d4001d0070510108640880280150740c5031022048185811054600444000a41c1001d505803d40c6481c2c0c02400c4240c0c204640701c003011101d560611070343c1001c5800300d014280103840d80b024203580034005082d9075415009807508125034010f000041d00034100840c20941c5900105418040070b10450308003c1c92643c656803081d0410008409403401a4011202d0618680c1c05101c8450b034040004203807036045075065610b00041c10320740304400c9030b0f4001c40c01ca0303600708402245030350072400200b003283c0080e00c003800140c0e6151003d41d0240e20520079075400240b100c0e1003105034546944001c032501c0c4120350014a24406444081e250200070300f044001c80ea81e85e001c4080440c0411504004140490050294010003801304024580c1c521009280d104086004070085009120550250a01802204e013a03582ca08103c4c018042c80300c4c040d00480c2d90100450100d01b000d00888401c651003043d13410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 760191942 1250 760190692 760190707
    0x120408010f0f06050603220b04080c1501230d0611040f0f06050d0504210e010207051e010c030e0616141614030c180f070903051c0516030201020d0b09010506 69
    0x1d200f42480c000c2418019404210707c800900c0b98050540100d006072280d03030f01c1340c9002880f04e207012550820302c001114035400410040070b40040f981c81c04111507268500380c00381310020491018150724010485c07424040d100448000c00000b5008441c85038400d0318a4603035440c0d00c1903541040d806044000b810812011900d8000380c1c000e5600184105011502c02060302c0b1061540d000003140a40014074441d4000020345e0f0400501000e018121441c2c00b80221070b05442c410440c080032014103024412a100040c94007a10103040c2841d030103080c540c0d03101039540050302c04c0220300d0310440d84c08011110f0104a000009000001c80301d24000d541000c50a014100c0340c0395004a09580c3e06214110010749030b0303201c03440d003000600c0305a4000b003424140130310300c01800d56000b0026400c003c403410b000c00200c0c0c0c0008050a1010380e99000a4134100c1e40070381200c030b0303216110324078490381c80c0003110790200342c2c0c1580104001c5000b00070400c40c40c2680703020040d80000030302c19940d01c06000d00155 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 760193192 1250 760191942 760191961
    0x11011a240409021b0a0302060604060801060b03040308042603010302040f021305060919090212010b0f07030e01030e030705070e16020307021201021e0405090a1e090203120408010f0f06050603 84
    0x104164210804070842c070340803595400c5d150244080301140144c21000c2801010f00309030003214043d0503d80700901500741059400c070610b01004101800b00541030000c103080c02207010b05000e4018050b00042d190742d4129003008040ea0007031000724003c84ca05280c80340ca962a034400da03a0311503000d8400499051619041250390307000030b2003095101d039041c68a500350b0b418407400c01d0300929010b200036071220124072204202400591000d07290040c1000100300d101c0d0100300326480250301d410600401c12842c0b004800074020318204444900c4001800d00612100085071000c940e004c0d044071500d680c03442100c0b10b10100c8103001401503441800300000519054031840c011005a00c0010b0500c406550428040c001070020150391070400102802241800c0c0c811a07409500c8503014454030555040340a0303050301448a44e580903550350301c804110768083c41034a624503400001c99407503c0c1c40c3c10000d03008010102d000c4442914050000650882e90702442007120300051020382540d507000401c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 760194442 1250 760193192 760193197
    0x2090a0c1412061212130305070f030506070302030c04150c05010b0111120f0c070f06020705101704020a1a04050a0e070234090b0102162411011a24040902 68
    0x50388079a000e61001d070407100c0207240161585500074125220001d2a41c00c0090600205800c200c1c0100300c02b590500c00b18100041198011500d450010380d44c1c0d44100360b03040d0902540c0c01060381d41d41403c041c541e03100d5111a1000751781d8011030080169510440054602030303190505410144c01901ca10005890078002400301910034101d078034609a1701c1407000c0e08011040c2c200541d2a143c0007400e1000c0741d410420100070b0f100c00c1e1803200206805090162800d89212061000c0d684a900014110b484402c00c000c0182b0701c140c001741910b814803a1804464009000e21401000d03207003000103101e010215128014140b6401a03c80b0820340c1031540b20410100d41c0c3c5500304030500c16000c41c15042d805204d401007a0302c1d5000196400c6c040002400e058842e100d100340304455060911200c081c1c00300000707180360002d4004c81c0b510b50608040d00e03a03559441705003446518049040300c0c00716001c4644015040112200d14000d520b40e82244c04894170f00c809080745420610091204d60102d500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 760195692 1250 760194442 760194469
    0x61415060f040915060f03050c090d111003051806130b04231b01020c010f0513050a0806090f0a110d0c080f0d0f020307150b010c02090a0c141206 64
    0x1e1030b10305034a81400c1c0c02911864060b03800222401c610800070a9070102c5021040161890144028104941080810700804d00000d1103013515810400c10440c03101c8140291510103042c90b9a050403808010300100001c80d428046901100510481c2e00e10200b00a48690784100c41901c10704090b44502c2e61000b8010001c80300040c403101d907094502d50099448121b0025000200303107216410441e482c944911895450555000149a0020342c0e000741c0900c4865115107070540d04c41040400100d003100c4164081a000100480d010500036800724a4504c207030700703031402c403665246003141c0f2a03620600306002030000010b0340844441840c04600c074280142c010041c452040381c40328141814040c0350082c401c1250301c5407048178000c0d900480c032040070540f240059410419152510f6520840203041c801d20103550789103140b01070f03014038540002e541d0007038203440705850400030050003410034216080204e0980c28050000000c0031045880c00301400c80c2c0d0040d9504c0703c800703200c18108900c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 760196942 1250 760195692 760195717
    0x91c0c020d0f0813030b06030c0a03230106050d0302010e070602070614032d06011d01090603020903011803020304030302060a0216061d06070906180303020613080f0d05010306141506 80
    0x3070b44c094100750030710b0304019601543c010100c6090000c01c2600e84102017801c6401a07804840420106244d9410109007019018104071103644060341c0038010030860304100c4d031002c034984151007419070540c02040e07801c912904a680c1a91100c1c000c2e80c2e03030355440c03003080002900c980d07014104821820246400080071080200c3c039400303003070b1001d13114900e4640c1240f842c031007841003000d10742c1c1c01074607000010b4894000100840070750300001c042120500696051540000390b41d90315480035804010141d00c20300000175052110301d80203403254054402a0014440d05011030034036050b51003129004030007842d60f04242e8015659442c05890104030703289140034a030050191013102171083d00e11640a1751b581a0416062002c00350100f240c81c0181944070450403003c1c00026000110181c1141444000c01c5840c511468811441e00c60590b0781c2c51041404160900b05030219004541680c1c4246020b11021035080c001d20b41200c011103250010103801e01d10031a45040c040000d0240103001e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 760198192 1250 760196942 760196947
    0x1e01170c06071401230a0921020f0a05010501060906020313180f0516030e06090303013606090608160302040209012304030314160213020d05091c0c020d0f08 69
    0x1001d9941c01c565a660005c102c055030404c09113407070011000d2141c1d0021130b0360010441700c251138a0b1003c4c40c031040b5000b46004080c424412004c00d0080121030f146e40d100c02e0480c3e03002c441616285001c2c20b0700307205020101d8071414010901d14000b000f961001c404180346030324807510300712034003009426014105441310780d16641310381301051a0150a2052003403100c506140d0503480c3d0010100c580c00c02c2c40c1c00c1e554000340305000c00d00101008890440e1042410340401d80185680001100111482c0e411052001c2185000710380c3d8131b4100a04850350440108086a9185400c60b00c070510b00326894403030030302c5480c184014a07150703014000c5510103145c0b80a2450030054040e12021440007061804240850300300201a48000d00943d4180c0c00c80d80142001c450003444902820100c20092140010708003075514000343d035065902c0b8105d4401d003070140d814400a840e89403603c4001c00f034207807403c2c15001180b99020b9000c074800303581d0140c80c2910003d032584889080140310001155110800c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 760199442 1250 760198192 760198223
    0x80118020f090d0c051c08040b070206040506071a0115021c021e0f0c0604122409031d030d0e040908090402310e04030c050a0501051e01170c0607 64
    0x1c03805407100d81803280007040c180d241817604000b102c0400c5112115420307950240c10000407004010f403000c90300528005900d611061000400b035010700d4100d603400c600081110010320200c00d10a80e80411001c480c00060390700d4000c400c0030081e903202c0c114051390118010105504046509442d0b82d41248150f4441ca400b00103000c811454103c1500c00e590700000300c280c01103800388144031346900d0440d54285440d02e4000d000b000740f924040060310074602001c58145212000240b00d0103484860020000c1e20300b24074000d4034410100d0420450801d010030b40082600f400202c2075122549920748948409080c000c000c090101c02c00200c0d450503061001c40150b884030f0015210140220824962001030903a2000c01001c1c20705030700c01702c290700007010041000261030698000d60549400b444e100f449082082c81c00034203c9005250b0340c6404100b1a03000d4981d69000c2054820641a1b2034603641c131406000003034584c1c008108036801c50300c9000070502e0000d004000301d40c445c00d24200d08040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 760200692 1250 760199442 760199449
    0xc080d0516050f0f1006050307050120011404080408060f0705160f0c0b0a02060907060903060b0105070b010608070e040501030b132904060605010216061427010206010501080118020f09 81
    0x780c208000c400e0350300100c03491003045c50500451016010a4000740740041c80c0000080880751441c2040c203802d262048079444a440a40000d41030248803403084945003406c2c580903803203510522030a1043c0c000c003000304d031156000c0035500b4000c0b10f00b5564a810a05c0c1c40c502d0030480a0f2a003c21500300710020340440c0024003000b0894010801d0501c201d07111a0246006410200c0c0288100d43d82d070440c0405200c06508900c54106403138101c000042c8003421000146c8461007008805400d090b140340000520950207600f0501c510300680d500a03072003e0302400d00040d6042800020001114000003030004100c0e605040d841c180680c000042e202505016581c021044840c10345c060254902000305201035030264000a20080c40200110501c0107000044500d8a002e00004c0103440010a00010803120540e541d11101c40c00d46a1514401840c0451030503d01e9101070142c001c0300000282980505000342c125080da8003e2403244200e20700c1240258000700c100894107170180b102210545 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 760201942 1250 760200692 760200703
    0xf060521060303041a0406080c120a1a131a04020f040311030c06070f0b1b0a0c0c0503030a210b0109140414040f0212010506100e030c04020f03040c080d0516050f 71
    0x105c103903030000e5550b401c1050045c20f1031002015840c0d601000c00249411086d0152100c1d88039a05450000e44420819aa10782006120005c1d95014050074006581d00000b64410f400c541d0320012401c240c0c400250600c070903401645003040342d101d03041c0000c1010603004080551048001000e680d441e07905500020b415030803001d030035a0b011441d403110714204056280496044024104000d9086000b43d0014020b44290002a01001110249001040b65400000010300801025a902c907141700c0c0c0001d0801910002e80c3e04612041c3d426a290900c1038440c00450707410694075089914141307401c07107035051409e40809130015602e5400d40e1004110942150140d4401c1e0b080006140b00c5004010740c0103400165180c01c3c1e403404080c0001c61351032450140c2900030608000340380b146490002420501403c0980741c00900018000d044580340c100114422032252060300d1400d61075210f902e03030b501c9002030980080f0300704000017140e0b404014003c640035485401250041e40d04aa01a400d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 760203192 1250 760201942 760201979
    0x50c121317010b0f19090f0e1b0603131407030b0702010507020f06070f0c081803100c0905040203151f1b0803010504050421090f06052106030304 64
    0x210025080c850203065a84100742a11500c00a004100c04030b0001111100008a15842401d621a0300082d100c428480700000b411072400c1044159004158040680351100d1180800d000d50001d000340500c016114205855000e044181550703500c00f1800702032085c490302a0360100e568007490050301410003681014605c075445007802800c000001030700707480d8050f1680c030a5402200000aa800d000140309a1022803450030340d150780b01c80402556815001407014104001c0010034200c044548155500c00c0c0301c00750115640380044581410450741e800c94108001a60b0700400c00c11450140c01540c1c1103941020029210340300480004d42030300801801d0038001401c10754010121b90885262400d5184251000070510000c0c1c0c0c9221031071005000d498466070355680820103010540c0483e041c0c1148050f102d8408440480e40501038400350310440d5850010030001240140c4108103803040d004450305130242d19203189003807066400004001c241c15220a200c002a10940801c0d4031088 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 760204442 1250 760203192 760203217
    0x1170715030b0109170c0112290109060f02061501360801060506030109020d0204080d090f1a070f020621010e060f090f04020319231c050c12 62
    0x2c9100009000d1424641c0310364080b48440d11344054600c00845c000001036024138015403a581c2a00510004207a0300c8500e039500314080a00035011100400d0b514854242601c0304540103940e008100e40c04a902c07044100181c00060204440d498402d00215022405040010802d03c4084030100801a0310400030401c040c00d1010109440281c0c2040001d40110300c0240b00301c1e4101404170700140700c18031132511620750028018021584e2a41034030080c01d0020152505800c2203180105051005d006140074507010746400030f41040c01000c11210107040a01030303820034410f80c0380e10190f10240f602c1643c20135070420060100780341c84503419040d0070a80d108400594101544900b248800a090b075014081800f507a40c40340c0c4d500e101003948512907460034621030b44c0358030101e4102203003d201c43c041e0b180d114007484200711200040840e101c0d18451100c0b240040e010b54107176141a608020202146443c3d020000c19104c6c074010031000541e00111b42034510000103031365081e40406100b084 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 760205692 1250 760204442 760204451
    0x408070204051f0f05011b02240301170c0a05131509060603110309190f06020a0e010f1e051e0301080102040305060c090a0e04030c050f0f0c09040b0117071503 70
    0x6010f008070802e000390181c140d000c0003103820000040c1000c1c1c28400c4110050041c201c0314411980c41e0410003034a294280c803d0140c542e081502d0200c0343c2c0003801640f1a110f02a0031800c000d100005410440002c000c041903c814a81304c180421060640c0d0b070702c2c00054440c0c604150b1410450b08840c004c0140c0d000009440d450481c00504a5003051180e18003480c042040c4880c80000203030001c014906900c40e0101000c25240c6441c0312032070903800805103800402e05102554001c5a4040748000c00e0f03c441003102030b000c1044440c4080c298200701d100c1034440c200392440c0e00c0303400644103182000d1001401c141543c003da45081d0401d81c80039030346a40000c0c0034400c0200910507140c0201a00c1c44003810a2041c40009a014a02e80074403d0701910201c0041c0605208150040e0003d800905031001115800640c079142d41100e2403034800e61003014580555410403a10307a51140b80c00401221030782c0d003080200c2c02181c8598050303400320702c20194007194080240340380c0c885604241e1000039 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 760206942 1250 760205692 760205731
    0xe060f0f160b18010227060c0601060203040e0f0609071412010e010305160f0605070c03060504031101060f030b04110109031211330406110d0203060f030307030207060305040807020405 81
    0x40400f42c0c002e0035072a0340180f103111390200c100c2003041d603042090140d01400c1c1004a0204640d40140e0170b0040c201c0c85008000030b0840d07000b000170816500c21041441c44c966818400b201403500a551490700509400000381d0303194422055183c0030703242c03550114600b8116600d01010350400fa00402070300d400c441c0041040090811140c16a2041080d445800d14503000401c00c000006100f28030074044001074010812034815901000703942c0c029010000340c202030500600340c841e58000b0f4581907203451404507104040c2000882207a03846004585140e030342e5a00c2c010032030f20150500b41446041d01c00400014a0201030f034030302c1420f48c1e81d400c00800344a80481e10304038403a901c120754200881840940e20600340007a0b0b0301400c2d5800048419140d5203002d0005011661048824420100b204d40c400c110f55002140203c1d41124455030b0b6914940405880f4030904c100103015a0003107404000c021b000740c205035030090040c40c1d00c9060040b01d40110f0103440341101d00d0606040700e051a03c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 760208192 1250 760206942 760206961
    0x151903030e100201181203271406010f03020105131703030703141303052802010903111902090405030702060706050703140106091a0405040e0606100e060f0f160b 71
    0x81c02c1c48500c510007400007480c040d0441d001c00c0d17900c0801808002138000b45c0d110042c0680c00400840124072444074030380c088080c1700c12042c03004030001c580d000c04c5045107100d00310000603094181c800c94076180b000c0515680c01919903620407111410384214100000966041000c64028182042c00c055035480c40e08400080403940030b4150604024210810300c00c0d04080124000315031545814102e98925494030401540c0742082100b80b0101c411300f5091080380d5044d0400d80b10b90f8820f4403120401500b108402c0d44030035007030f00f000e014400b4161109c80580740080c8956045805541900e203000e003150082a521b521a010075925161100140191540d1510590070000100544d0441c1c0f5410705100400c0d09401d84189000044103400010001009408543c002d25004004201da1490090f20a031103100440f0003500c07a401e41882007210307034060001d00e580190010041850985540c00f14041303900516603038032000c0f4003403012030780c040074004c02c8107800f50190800719021f24008200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 760209442 1250 760208192 760208209
    0x16090504152909101b030e1e09151503010f0e0121020103020a0905031603050106050a03030203090d241401091e0b0d150b150909151903030e 62
    0x100003181681c0055101d01c0742c401400c1e2042d543c000c4500c21008510350b1403c9034204d0000140e110712640c006030400400d40c01c81440c5403050303003e07503444c0c0c01c004200200090b00c41c0c800070aa0f03005080000007075940300c018580350040c400000c16820383c02e80f2640c0d405c0d0032600241c225180311201d0103c140410905500214014146120301c200f11030004420310f209008040d400906043e008604801c0351401000030030003410b809811581e05048000085881540c60b00c815185075280400100e11402c02117800c4003a00d40540017189031075040018484403000288003560081541c006030f04c4225409030044050108428000c14410b409e48070354140040180c2c03204030038a1520060280440346005039420883e445800014280b00a80104888107000003004003248401d041e038004030303035040d4000c5c098510283c954400954502d485507481f8854040140d80c004008000903c2c0c900700c190302051045409000e080615048040125400410b600110301144c4582a18105420301060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 760210692 1250 760209442 760209479
    0x50c0c0d140f0a06110f1b0c180a1508060c030a18080a0e040501050a1e030b190c05030705030c09011211250f03080406090209010e090c030a05061609050415 69
    0x40480c50009410940d020520803402e0311031060401f50b014412800d000d0103110308014018028a0001420035000d8904520440e05604024541100e1581c0d203e10150f41000b5200c5000040220b61159400a80c0030741005180c8200a901c8225003402e182140081414240c411480551141100a8058600700c0e0b0141094001c6240c203004102503a500e442034012030700208520343c0050a50044598440350b0307a000603102544800a00500c1c2c5110441d8500032004503104200240040804454074442600c109001071380a0020800c1d01400600400703000c0d2050504060f4002e01c05000070a4607400000c40d4102480032915140c2c01c4a03a41d0400251088215910003500260f520b000300c1c82440d840280801100e800080c040103011360200b158150002d12203000b40d070b034880b41400303110004c48801c2c8141c05008882141800c000810f140c150b9030020141106582d5045d0b09041c0507034036001d000400007c0c4200080300d0322540320700b1010520284402d48403500341101503c0c1d0071207070036 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 760211942 1250 760210692 760210721
    0x9050d0c1a072109050a1a090c101b02090109020c0f01110a0509010207092406050313170d091109060d080703030b0f031b040c050c0c0d140f0a06 64
    0x1d04000502c0d80c003904800d60f103102082081100c4004000030700013082e0b403080c0100940f099124200510120740d54440a10513008602c80c403564a180c40c0d10380b101481c20415030491381c0c0c1c0710008c1b10380e40681c100314404080c5c095144c560744400c1d00010041c00e8203030301c030382a800e50015000d500c80c2ca0500c5194515291140240700b002c81400d0f9243e428490580c61070304010000c11030700d400c0d80c07003440705c9401450b1981c414050f0150108000c11180480300c079a80060508000004a9500840c00e6903c601c454840210721005140c444c40304a03440984034504d584010003d80c0001040f5100300701c555400f07402520426104502448031441c409091248140c076035240b0140080c1d000320854942c940d15250200341006094042640c04115940b4260704d4010140c859484031030901c01d080b5285000c0300c0c107001c4040f03502d070241c5080c46645966580ca4112405910032403c15001c842841807086081c291700781c008000d003c1c1000850500f60216801503660a02070081d1405500c24842400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 760213192 1250 760211942 760211993
    0xe0109120203030d091e03051c0c05160507050303130510020304080d0e0402160b07080705190c110a121104150e060a0506181504030b041509050d0c 65
    0x54000a90f0703409100036403003415071501810350401c002c0095600360064440740385189030490b40f50107001e5401802001013410411a80045440418081d44000c4c820326140c140ca040e2141d00030103803012810f101950548034883d40040c0c243c40400c0244042451901c11007101da06100c20401e200e81038001003021035005000070700000c000403d00754001c4d411803d01c10f0688204001140107401200142052002c0520081092001d00c014a900c2202e0590f02c3c60500d0381d4251065800b4010701c055031f00002c000444040c0500c2c0901a0600418002c0d0740e201103c1c1c1c0303050009034100b134094001c0e03510020f42c40c01c50001c0011410640000040403201409001c1c142900c0da119a0341038800e661851400388041185900c640d803451f4045d04000e0007056603400b941c081840340140100013a80a120a5100c083d00c0f19550402d490030f41c0e511654070349060b1202c5d00d44214031000c104480c035010317036134070b054400044042143c0c1d446200c0c0c64803004513220203400c20324800e0050001141803425003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 760214442 1250 760213192 760213229
    0x40b1c02030c0a08131e05250909020a17030c10020a0804170c1005090d020a0f0803071106070e040b0904030c1e1a270c060711030a030e0109 62
    0x649043d52060075051418000c660384404008145c3d80c0c6800001c1c0001c2c0c2030161070000c003541e0300c034540c2609016404640c0300b00701e00c4980c9003035400c0e40e0600034281160303034038203011802c140e400191030ba034002072124100548600b18805030301f2180d4958040c3c2c2d480000c1c1c400d1581014000159020400c2c1c404500b4a0001c220140946000500c020008203481041030306060314001503031104100c1074129662211401e02e00001008242d44c000c0c918800e52103581c590510000340e002d211035101407603440e544c0141c0d542c16070b6600040d1031642231060901124101040030032119201300b80680e03e1054582c01c0da0140411900d40c82405170140e4203040c00c200202c2e40024080d46c6d8954040118202545880c0604640750303507140006064154841e00824070a5070500c1d828000c1583c091143d080c000c41c41b01100721740202d0403c412103904940c00c00d0402d407920001030a491400340c40b0300b094a201c03a000007401c02d0141001140403a2000e01c60741c8107960f220441034080e041c0400f00120b504034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 760215692 1250 760214442 760214461
    0xb011803080f040e10050f1c0b072705010e0402031e1902040603060e0604020c10020c030f160b18070306090f12050a140906030a090611040b1c0203 65
    0x42804090201d040c001820360a031404441124010300c55131000300058284025418500d0129210b010b1141d411820416550f10b000b6101100d19101040304022510041e500c404004e00d00030400c000b40034030b010310301c1d4002c11601d0f41e00584210100c10700644a04080001d01080c05030800d09028510600c100704150f101200390301005031021070300103120f541d28180f20500a20303005a03210a640042030010b11590180c11007030035034444514520043e6291000d00080303000d0005035940301e0340110040401c20885600034426500e422099034640103109009407021b9100307000b916103020003038404006011140c0741603500300400000011240003020082079862205010145c007040d80e4606110400030500c241c4040c255000310f0012291010320005001a0407640d02c0c04046403082c22500b5200310030004540004900030310690450303c944401c44020300c240b0f041202c10759550200c0354100c1000c0c80c0030700002d0540d0b0f1001555107118403020020285900c1c8015011801881440000c00d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 760216942 1250 760215692 760215737
    0x3160305070f14070f081812030a05031f03020301061502101e020a0507020307080d1206120f0204150b13060801380d020706050f040b18210d0b01 64
    0x107455012458642046091102180d010003900601ca00310015401450042e00d4000701001581100d01e012340a403c54450354030b9100e1241d00b0740001d5030403c002044481820b5100541c02400020010f0258032a40030a0840f00e003900600d58000c2070300424000142c1c100000c040c05509803400384080386a45000740ac01242d100d000600f500e0300820030034007051140e81900c140680003030440e40c1c61a9501100f64440c100c8006910005403250b10000d8072a00700c0c054541214002d10319a02d1380081078594030b1218070641005c0341d01507100c0c600390603403919201048001d8200c3c2d044c500c2d2f0f2a81190b094030600e02d07142c2d0014041c404040010040094004800342c02071040950310849950a41035000c040707411300301b5014200001040c030624072045a4040e15a0901c9010100080d807500c0c1c03100940c00c2412500280107100d80800074403400d41d881054140d840c840c1040351100d2001008104544131070a07548000d11801003030300034140f01c8034011a589000c00382040083c010b08444840401e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 760218192 1250 760216942 760216967
    0x2090610170c1318060509090c040c11010e0f0d17010b03060402040f0b130f0503340e040b0a060810020a050d060603020d0b0906130f0b0603160305070f 67
    0x40700300100080040e40103030115000f030704030550314801d401d4445008031802e0f8502203002c0e4503240741c03070404907070741c100f0424141c010601c4000030304034440b50300e003000054210b011324101040901c101e14000c14100340228072030b240407040500041101100c40070314001c1c189404038200840c6900e249160202012110b05441c80e04be1030542c3c1e596080d010401034426035010240340c000003400000c0c2c540c00c1401800c542c2540c4403240550a50703c0c0c00d0050b40c1100c5005503a455040460005c07200c011148031441140d0341003d050f0030444200405180a135400d034016210702d140002004100418915481d078009040d000400c445800c00c2e6032103594a14540442c00b8640d400611009481d001d40d013600da141c4218032092113100d407100001806134200410499606041c201d034081c0a10300b540c00c26100d4400601000b0b8a0092444a04003421095a14012141c2c1d40c4040d03a20076125400258491044120074171504c0d0725008004044440007020302081045012003801c40c141e0040000080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 760219442 1250 760218192 760218227
    0xe040b071d010c052407080603120327011a0916090611070e070306090b1815060c0604081201062d030219030e010e07050a09022506020702090610 64
    0x200019844c1c114034003480e804402400f854507a0382e405144486040040c072400d0340742d90341d00d5291582801e0594601401c00901200042840002e001926000111031640b60040d860100311151a81c2c0d203084521881f6010b030070254046c204800e900300300d034440b034001040003600e604002d11490000c1005855000d201c0821603549040030101808000700006003500000900e030700e0805500c050000c01081c41545403250038000d0b4034a81b4600441c8146400d2005041600c031071b9590401c0c8400c4000030000c850f03000c3d2040c0004070401d0402c100251240d0302c51f07884140c2d02d013040c014018107c030059201c0d204104102100741e01001d2881d12844100700d002403440c1800c003021205030068020711640803645900d00a030154200d5068022818410b0000000c00900070840d80250700c1d40303502d016150f0010103000042040d4084c0703070b000345048508a2807480003161451400c84011440d5032050359419000b05514065180140300f40f034200c9230440d0b103062510714138100500002d001041c02c030344 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 760220692 1250 760219442 760219457
    0x1b0306070f050d060617010602031801050901090e01090212130807020d1e151a030c100507050304061e03051e1503120d180c030809190e040b071d01 65
    0x441e0390068043d0741969602c0d4070148211501e44030000c01c0d14812100c0c1408007107028000051a40c00441180c1140c40c5910071850841c0d005401501d140e40120140381c1040b0080c0c4000551105a0001d14081c02d000c00c0050b90b0b442c210b014031802c164000c0c0c1130108a94800c0c81c0100021000001c0741e90250b416111810340403041c2c05c24010341c2641e04003c0e0664000d66010b0010000d03c42020104062690340400244080c111002c1540c0143d41c282a055030000ba0355103814900324034403400000300b13450841e01d4000555215030030b50f007040e4010b2012988080ca141d40101002200807a4180c0754941089a4580007046d540041c101c000000c0d910380d80000072030040040ea07020b0f401007100c00760854010843e851041d100c0c0e907008c40c0075525802c3c40c181c0d2010003142c0d2074980c0e6854903004168501c3c3d050458031060810761140075070a074805610f044020b00d44900c641003000420103800d08420b14941400c00ba041580002d2404040024940000f10150f6100400249418003840c0025 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 760221942 1250 760220692 760220717
    0x1e110c19020f0a06031d0106050f0d140118060609020708030a020c0f011a01021908040515090406061d191e1d1e040b04060f09020406171b030607 64
    0x50b420502e5441998000240502c0030946580640240c01c0714003100c41b41500140c8004c00c524200e980340c0c0115035000300460070b030400c94582141c18041060160303030000042d034003c8a040742120100e0002560a40500741c6a2007400550b210b18801401d61010651610040d661101d205200003448124015408034201c824000d080119110005c05440204207011050f9a0685140c90b040c403054014400c0c0d1000f00000d094800c0202ca80703d500500b41814142040104610040034068088200e00f0034080305110366521300490b002405107032034103250070b03549000001a04501030003180c0104404172091030064040701c404170855942d020070340c8040f0340e6890b50300c12102c026403010303d0383c2c03400304e00c09050011041102c6006140070440d02075041e1200030381c0d681c407010440e0040c140c1c02c480700c0000c02180385a0401101d040941000154400300d90340000e044031481d4000d40c005110001240204183c1001028000c1c1c40c3c00b55484070001041c00002c0e642c10700102681304009003010290f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 760223192 1250 760221942 760221949
    0x615010c1505010e010f0b070c030209191e0c02011b03020a050706020d0e060106020f030a03051b031f0b180d06091a09070b18040b131e110c1902 64
    0xd03462141d2002030181e540e4440700031004507001e000c4c45400c010300550000b141c440d000222864264019808214030707140da020050071503c0213000b04c1c15281050f070084160000c074070800d8141d41d180048002051181070a50040301c642c9a00c200c107581c07400300b002400200461078900c0c0b8006600c0c0250361580700da01b0803039240c009c2c680001d10841c0040b68254030b07611607412918454850320b04070fa566030f985610032a80e03450f08640001d080d8000300f10310300500d031203a081141c3c401102d561404441a074110601d10546c8101c4655512414184090300e003007010388104801881034901142c141a4600b420910344101c8591312403280042d242e0100802c036003500300c40c21407030300042c49001c95010b0b890708100c040000c4130050315600079001c0103d000001c001c1501c2611049100380b840d240500303410310001b421400341050f4004d100228284c16030005000d0b14043e424882e4900307a468002e00c07211070944070f082e00840c9046c5030900901c0d0402c0f90000d42101c000fa011120301c5400c1c121400403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 760224442 1250 760223192 760223213
    0x604020c032b06050d060b1c080a0306140f0d05010b121605040203041502030403030905031902120c030a0f2c010807170a0c03020d061e080615010c 65
    0x105000c0d020100e048510168800d28861011014400e80014461840800802c07240d03607025040e40154840704803008210300da03205c91042c0d00003500b28103480804418448070019583c0702103078200b800007001c030702d451f0f4540641401003c480e0302070784451049200245034110443e906600407036034480c0817000d20009401150500c40081c1c03c003000d000700440c040340c03500022000c01c640c003403107e800010719003401c0c400c0320321858008850404000c0105001006548080e0095041507100c01300c14011450038002005000d0b42080c07070304001110640064105810524100f840d0700061000113419000802201e403030481c1450300e10842c42040b902590241240e401910403214003042000e842e0414a0218821400c00d88901200b9a075000d4200d40140c03440480b4140f1441c0940132078942ca910342c110040070100c90a000d030601001140520480700e07503a01001030100350103100340c11030b00e0300e0200700c000e40555806010545851503210310703015890711a00c1d0400482d14074413400c1c860b83c6002c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 760225692 1250 760224442 760224457
    0x30f0c021c0b0f0f01050307091a28050301061406071b030305030423120f0d0e030703031112040b04020a0923010b121f030f0506190b090f060402 64
    0x150400810740d04200006520448030881c40f9140302c030100750b030703240d00c409258101c8500a004100240c10100143d01401b002030410540400304564444203075601e00c10000c0c00040400344444440d80c800344070340744045560140303000f079160031001d10000d500c1d00c038201c00040060300c215a44d188140341210090703581c09500c099090707558501000b09a8020000c5019034002c2c1245650b5400c1f10007044200c0d01041c107881c1c0294440d00700b014046613040040c0c10042d901c00c00083c1001840400032040d20900390074403415810000c0c01c802090703010300c02c0c006521180c580460800e018242e9803000807402510181c403d05180001904550f0f50000890140884c4042817040d90319820f00007002e21448e6000c0500359114000106480c1800270030381d0510203140f401c0c0103598941d1481100d0301d0680120392565841c0c17214003c00842e40020b401000284524010146441c20103584108290780c00c4102003140d0801a031001150ba461040680000da10035203011036840b40000680207106040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 760226942 1250 760225692 760225729
    0x81605070b1602060c1905060411040b0f240d090501060f0e0417070f03050705010b030303060a090213091d0c040203060a060e190f0602060603010c091205010b03011a1c030f0c02 78
    0x4016000c00201123441c50140d846000e070180021300c01d10401c829911000400f03a00401d11051640300c034070b0031102c0340300081d601d0071499414640400c0c9544a5900c8251004002a1540300e1941042000d1081000410b181d48401c8441400c044040c01c1c5640e000d4000381c041d50b81d90700a56000c0401d1012100820303032145405041c00710070710300138109801c80351044d5229440e1a44145c0301d1b00f404021244500300c01000c3c036404034100b8008800942104118250320750104101080303810252003209458240b2a8405c0c1400841800403454001038250640c0180e0040c028040700b031315031000c40001c1d905182014070a0044a90109820800d04001030f1860400e81c94000303001d0b400380c40001e0a881059084e19159903c9070285800c6c2c40c044451400013420b002800c0100c80c8101c0041a491846040040b4180c0b070104002400e4421001e11801c00d0468900da2000b9841d00c0e0640300e10702034008071000595240c0d501c02901c0311040c50241801e000f004d151207003c40d9200d19080c45009601d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 760228192 1250 760226942 760226983
    0xc0307050613090504061a030a080a0c030c020a030614150112020304030e1807090b0f09090402030a050f060a0c0c05060f270c040c0534081605070b1602060c 69
    0x1806c0600103482c901c1c1858094120001c02c10b00c003401c01003201106a40c10184141c03034140d04060486032070004034400e6040000b900011320060340d030590080d0041d40241000314070580110002540d008020303010032018040320510040700e0b40c00c6a003040d601c42c0c00342401602caa842d03040658513051501100c0798061261100341e580142c41a8405014038200d5440ca5101070b1150318000651141604615004c2c006002d040468503003640d40340d80c410310240c1a94006105555124900a40d1581d028600e802120420007050310600c90701c0c1042c0010314110540303c509840303190b150307000940070f403c8255107103000600d0700c0c401001c0421072241030702000b11015210189540c840d2141f156140c41107052100c0c40300140d118400781d07860811301051b50308180d022400056605100a40c5030060040d25100b0707030010034146009000c0715060069080311607207580c074055041c081160408144080305100c0030001c01d031510914410281d040e07031110754400f440c49445d80381c403070384151807000303440407 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 760229442 1250 760228192 760228201
    0x4050310090605060d17130e040b1b03070f200f0304053a230604050d0216170c031207060f0207030518041b090303110c03070506130905 60
    0x45500c108040e502840041100740c86550400c44d062603058170190907030410807413024061340010024540c07412642d048000d69a584c08000c042c15104503026125400c90000304000300b1110700b02c0480314507484e10302c07501d18980034802900c000b0340c100c1c10b6000c10400c030521180d0000305146600b80c41081c04100c0309200a5003103110360f0380c1d115018081c0a07007003008040010615408184900d40480c28030910b00850260258003c2002b58405850020140041e9420900301510030502e250352040034064900d82420b01629004450441d901154800c0e01c0009192003081c0e0302405441e1869010721030907400d10300320f0740b500d034055408580c90700401030030200c040350341001000d1283c8104c00500424052020355000c0703014001010b00800c2d81009200c240086c0c505914050080080002446801c854100604481c00d49a440b003c55281d070424001d140d0014640c404070082c210082ca0003ca0140100e9103400701c6200b43c40c0108004199100c4083d00d4051590250900f6401000136180 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 760230692 1250 760229442 760229473
    0x10f111c110c0304090612021008090114041101030c0e010516050c090c0418060e0105040b0105071a091614060c0a0501020c0c1002010209030a151e09020406051014030c040503 77
    0x1600c1900646886d056000070801103580340180c515030001c01c8444071b540d51150503280602c00900101b420355a030380e00d02c00c10b8440300c50020b0050b8042c5211010340c6640000140481d44a030541c6402d1050140ea1142c0036130b40101200d0140c44110300361001110310b03280c030910b840488501b02c1c0e03000048400700041c003460500944125241c1c1001040742030070b80c0208c00c1c1182d0703c2d03000d100704445681005000c1c908040d00200801441071412624202c4203444550000c008548507801c003c4001c02841500582000304200000c244036099085600c1c00e00d540000741c0044880a0140c41c2c042400010b40302d050101b903107aa84c00070000c2d540d84502342c24440e01c40300649070651041c40c42c2610107255910501c00c1c0c0b42c52000c0900200118509515401c002442c0b40b0061405184c9500c0c0ca41153307624201170703841031281002e0225850103184108800c0c0d460b5500040c0c05100d806140000031903020b00c140161021103450140d403903c40b5460225a4495174001c981c040c498039060541601 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 760231942 1250 760230692 760230697
    0x3040c1a0d02071a1006050a08131505010302130608060f06040221060901090e0309010305040809120304050406080a03021b03010b0a1805103f14010f111c110c03 71
    0x38060134190324155078001e0318101100c440d00900000a206100c40e0110900400090f90403031700d15800c400701d04030aa99130403541d41d040d0096802680d100d900403c11410541c20000007210108002d2010302e081039a110358485000b007125040d01011030200c0d10f65180d5604682d2100c80c1c1100403105c0720800c0d0404448924140ea40308e00442c24007000051039a4a8402e03241d1215911020394a1b0615100c011809030801a10982e40e840082105c82c41035920905121701020000010f076488a1a0604010846000340d100c6c00342c07030f00304100190002e6030105040c0d0540c8241c103201e25600011001090040c98120704040d0003108890000c103003404205194056034540781828080356561913078060b510985841070392000a804510782da601c260280c002107100d40781c410403040c070301c00300144051341c105840e0003a50f0f10307011010600b0781d0007000c2c0148079080200303d001f0f0140e16442c11006c00e241c030505c20a11165850f24114103050072207900001903e640b812191a207030082c401403503444c0d9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 760233192 1250 760231942 760231973
    0x813080706140703120b0a090f0b09091204030213020c030d053405070336080303010501050702120a050d020d090806010e0105040207150c020c120303040c1a0d0207 72
    0x80c01d0034000d80b0000804508480302c282d4965034540d0684550050007020300b04500c0c170150300042c001d4001c107401e2110300c07a16070070081305200810020704201c14840340d9440544008541e41040360494904c000c0f00c002c40d001c40e0340c10b0301c0c407400858010a00b00b001340140313003015006020014404040c00344a0700420300880240384140c1810038007150b410310301e018605102d180e410403036070041d060f075004002520000f802802e080c009a2081d1640c4120400c0170158441c8a14010314064180e0124100752400703860004021451541040000381c00c6005455009100d10810782c283c28000d1014009122219400f03c01c96601f407000243c06900d0741080f81d45040020300c00a0001002407001a929040f0341e0075112861741c60342450300b4000654405101a1402d04203c0841e0b503d8030000d02c94241d0000040d03019082c0e40e8146c0c010410100c0070030103101c400e54010710500022442d203070341c0c0400315902c10781d00350f5503580350808001c001e0040c1143d000c0641e2010403410b0078811420000741c1c04 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 760234442 1250 760233192 760233197
    0x111150106091d01090f0902030f0a051e1b01050c030705150a1107020d051e1c05031603270b0402030f010504080f0a0c02060304050f0c090c0d090813080706 69
    0x1140c0c0c64144100059600740f42000914468000400005032a603004001003c1c0255020a2440460300403904e88841c06041c0d00465100e540e140b014441305220b00000c1182d80c210ba1107100e80907850195540fa44411643c01c050102203081e14241e004e00c0c2100e003992641e00c29281c9441c0305080c038a4071545cac0b01d4200c01e000103089001540d20000341c461400d1103001810140e050180c15000c2c490f82440c001700484040c854a54140443d9221030040c9850110000041c108030310b00d10101908050094408014020b040c000d02004444024580910138039900d0000f44540050100c080c1641032a500501e80d2401e04110f002800510304c00341c1c0c86a4001e50403192410010a8010300703c50342207134040e0840c002030107030f03225003101030008003008101454104184034550f00003826a0f4010b580407105170703101100b600044074040c13203003048140c0d084454070b6541c030303182050390003920489200d00c0b00c06aa42c1602c4040120b11000e48540c18001d61986204a807140d1101c0ea0300e02590054001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 760235692 1250 760234442 760234457
    0x709120b070206090c0612150a0b0a020c01030912230c070329010506030a020408030406030b0906120c040f02040b0c070501172214010f0c091d0103110111150106 71
    0x300e0a0001802c05d240b03000a003038103140280296171000349280c09000d403616040d071301e020f01c840e035035646440202030f141c000f0700c140d82c0b5809484007074500010300c07503c6410b0600f44207031500030400d12040f2407401c0d03840b410004044502040500000d00c11002c200800c0c0303a02207026940701c2400610074042d03e01c0b40d030b941c6444071000a05082c1c03c01c4240d80c01082c4256050051145040000245400140c480400350611f900e5540c11811608a90081d1001030368584201d5241e01d02821425040b12045e40c2207440a0780120001da180ca01300304002e40600e460700400681002c05074100e40042078403041954644a02d9412030380c50703265910900340020030308010080b14000300c0d01546d00503103198101c40c010700304041c02c03008490031014050342c00b00d50944103100000070a0080303003144848070200290b005c441c01d0000d005409a40c020321003880368032665524094000650506403600311200000444043d030048402841400078607440d800380b602ca607014040b000300303580d050b21055200c101 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 760236942 1250 760235692 760235701
    0x4060207060603122706050c16031a1311010503100509010b090103290d0311030706140c09031509011b0201060303020705041803081b040b12130c09050709120b070206 73
    0xb61040008945501182d0030071010880e06020300001c10302548c0341421b50700d005400c008220300b8400f0652085d22242815118480814031804019502c03603911483e40c00c500b8800d032125001c0c00445510340381840000008610b074031801c1041d1200074200200b2171025503031079145410458020114540c003103070612502c40001c11141c400d0160040f251540b460405042508005000b0381920b4160280b1900d038803420301c400814801000d20901860000c01c1c00103c0641203540600010203d4100d644103000f2140c0035900840c9c0420302d9410000e01440342d84407200d02c98010030f40384034902144981120014200c64041d00421300f164002e800340c82c00960b4036400c1c40180c1e41f020716620400c1c4000d4201760000b07070117414419004521001c5420100c86240a44a0385038800d42009981680118100a601e1540ba4259070b101c60b4006a846110010b40d407846160701080c0580071803503490318000303400f6501c2151000d000b0b0041c690750901d42a401c0c01c110b4140501a10060b005028400016 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 760238192 1250 760236942 760236977
    0xb040e0109051603031d06040b1801020c03010b0f0909161e06031b050318010204230a030c1203110114150d0b01060e01091203020c0306180c04050406020706060312 72
    0x102c0b174058403500643d0100c07080d01ea40d2070301001e0741d1503846101071201040e81c0c8410406480c145d80001080d81c0e23461660700c0068500000910580c0c800d0f810030151000c55203959800c0907030780350207454401e581d40316803035520b00b4110385a4103000c4c029000d10000078039800c0b4107072800c500700380014020149611900e00303d0076290504446803804001c00074180e45248242c00441d0300003621020364210312409610715081e03a205a001d031024020f1000f40103050302c07171020100c0701c810080b42c584940b94a55070300c180030400e6034850b03042410b1030b07031048100f0b06000b10041103034814124001c22035084803075490304610f01c054442c440d2205041c485102c542c141558030019580c1c01500c081c4150307203000005c0380c0d2002004011410030000c01c43c00120000300e00001d601c494440d8002e024050340f00700601d441c00b0001000e100c561581d2001c42040c926010400d508503142c25580480d07103a585060140c064401d042c80144500e2400000105001100302c410007031100344d507600040f01c9454040c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 760239442 1250 760238192 760238233
    0x506040c140a1410050f160255030c1e08330a14090a0f080d060e0f04031707140a05040b0d0e0c06090a14030f030a030641040b040e010905 61
    0x9003c40c0900c5c00c1c8004019240804848001d4080274500c40c0c882e0700b2810070394072016543e0044403e04d01031f81d010300c06c941c28021400003001412407175114545c40d0002039a0340e240035034683c10400340c5010451658070b220709050b0f0210a918034480d041c60416004040c010301c0c4000310800090f1241e0003003100d80b10007003143c07c0120b4210019040580d020b440740c502d5940215002c500c580c0d41c1d20400500e030241082ca051086520380e14018261819083c090300104003001c001d04c0d20001002003007103140c0c01c10200302a13854003003081600d40d03002c1e100544280c40350380c11030700054401058000500c00c140c0c00000280c0d0941041e54030148180c3e0911400340100e1f441d0a44c002107040040c0800501e070044040c52400003011150050030071503803207007150f002032046000251100b4080c00b489003007120800010900d014900181c1c2d0400000130b00421540030a89020b90700e4440060581d03507290000c0301840401042080703400d01d040d140c40c0c02402100c2007205c02e409899501d8407250701c014003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 760240692 1250 760239442 760239499
    0xb10091a030d1107090c050d050901050f241c05070503120f0c0c2101050603120414130e0304210b040807030c0506040c140a1410050f1602 61
    0x40c00d40010844080d1814003074041e2000ba14031410400040c054414000d000c0c1c3c0d296540c480d08ea803a6450408281a1003000344201c00344d80c18031003070000a521201039035a01c0548068120420031591110401c0811004003041c0c0c03018a400c01f03804607880081036a61514400e00c11180605d03a074505064540b00c01000d800b010310000c1c002c1c400390040282c000c1800100c41c5003a030b40d0418511002400c0070b82c09800d142c1c0300003400104516084024426950010740440081c580c0340c80e6010395910310b10950280294408058141c09425180c25004000e03032008564140042c0008204140ea039410a00c21031403030007425440301590004c20b00c41011881c1d003102500125645944908039198460b510490800c4041c01c1050042041131020501907880765486900c414074048200c2600b1480310943c3e8845c0110700020409405880101400c002d41035400855903040300e83d0585281c018000d04000d08500041d1031594071100d240019000d9208032503c0c8446502501800c041c220a81d2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 760241942 1250 760240692 760240699
    0x1704180b010503241008060909010209090a0c031e33120c0306090b060a0b09010f230408030301090e0a05030d110c0d0c03081509060d0201020a0b10091a 67
    0x4041500810300218070520785003125081303903003c1000b10120b040c0c1e1030340a06180c00039080308140b02807460106034080c3c11000020003541070001c448002182060050003e0882c0ba41c3c504082c2c20003800f9811006010b004200e032003684c86130001d201c00140c104400c544002c500d213030b1900c443e24030310603a03109804c05440e041500760038140480b40304903122218040e17904805001000000500502a40100521840c0d4078a581d0038600107014842d60700e6048208080e000344042907a90343c0c442d44030401c403002490320504003e44034103000c220b221081071a13903020b5800280810345400000040d412140a45d508000f044038405245486000f003040c02462604100829080d4183e9500100341074a041c86890f440c01070603070000c0e0b103060341f43c40c03841011034070400d041028940c00c90041d03a4000070115a06401000c2800080c0c031100b07008040c05d200d104e580c688102564030800c8440c5c0300950041c084032131030800c021032001800d810b220b4030310514149021496007003190032072070020300c5010b07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 760243192 1250 760241942 760241947
    0xc0f010b040c0c140c030f03130e070e0906010905030d200705010f030f020f070b0f010f08030714010e0703030207030516140108040501330b04060507021306031704180b0105 76
    0x71303034402d645a41d4800401d0901e1144030901403035684c05001107419018070800940e1b842224045501002040c3c0c0d122a078000036650801a00c242c2260204116910072120701c01165120350041e22103040300c2c0c01c12034041c41045c040600542e00034a52184014803228092a42184c041c03080b540c908480c042d480c00640040b641504560107a0002d05100c405002c016040c00e145c2440c0d1840b98110309415510180c02d40e0170b000b10311454003040307405403114602c80400d4904002d80282e81c6d02c02d42031300503c004480c12004100032800c0d440b1341c01000740359007600c0c00315699040080d5188028003040c5c4442c0603110084a500b2400c22440045a50b815510300740040c11100550710501c0042041e00c165481d5a040e554010040035144000e4440c1a005004060b0304101c5c1c0300848460b4000348402c04003000140a143e0b00041916141c9504a030b2010b60394056120102c05440c090384014103000080704c00c010707604000c0c0003902c20341e144a040c0e001c2c3d5125141d011010389114802103400704004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 760244442 1250 760243192 760243217
    0xb090108040309181b0c0c1202042a080f07120509032217010b06030a0222060801180920040212090c0f01210b150c0f010b040c 56
    0x180a5007680035000341090000c0726a03030307416201c40032500307600626410780e00e4140085008110f001c0111118107450800f002c0c111656441804a419010340b807064074404041d40115138031600024440c1c00d00d17100b915200c3c40c0109031145046d26a0200b840030500c000000f400860044603a588101401d945030070044c10280c841c1002032030f0240004400780401c0040b400101d40641207045420804199589a14603003000a080000c1c03900d00940c140e414400300e1400750b078521003a03030741040c00e030000180c0e070711410486203c0381500000144080030810302e00040c120340180c2c0c9541200c0086c0400441a81000b4888088030b250400c001c00c0d03444845691108407202c00e115a40000000d0300052901001e82e59000e5803800803190655a40d214005010180c14485180500c0000c2800c2c1040d40511041d09004445071380464072400d140c0d18582400340d955502c0100300c000f4812058256551050550180c0783c2401f100f091038198240345d400308031800c15100342007040c1c446984d22080301c182c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 760245692 1250 760244442 760244447
    0x1b0e090a020906030f010e090a0515090a0f0302030705070e04050327060c0a020f0d08040e04080d091a090601060e0405060303040306060b0d0c09230d1e050f0105010b0901 75
    0x1405040e003440e0590920202c0d0143c3c030303468002d500402d082c542980c1698076203a032006480100600812141d0091010003000840000300101102d51380c00740d002e003075074031849224544010381d84007138064582d1000041c141074010004109150047c1e055176103050302c600c07001e48000c40070f54000b0443c1c4d00c200401102c8001d418120f2039042404880302818040c0d400005440c0d8020014450094201ca0980d9045181c11000e00c50034141c02d40d50030b044444107807105a020b0141303125504e0700302d41c02c0b400107041004c450f0440700402c007480010060101d460030102d0000e0180d0000f0608038010741c01150301c003000001c17000d04803650303541c82d81d140510800030700000c1c0c035000c0c04868262000340b0001c00040c0f0f142c000c0001420103410500c4c1c446801860002c1030f0b0315000d80700401c1c0445528140108082c45c15010b001c448513901c404180d0011501050b0384121011000e01138205221155024980780c8110340651400382089a035194031410350682251803e02c110045d110040240900550 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 760246942 1250 760245692 760245709
    0xc0605060301150906050f0d0807030f09050a0308030106030b1503070309020a0503010c02010e100c20100507050a020d09081011071220010b0306010306110c030414041b0e 75
    0x310180c00400c1240042401241c0007045070030070410151984824825070410342c00200100c2c0081b40e48551300446920f4200c45403140d50406810403284010008046021b01c100c0e41c014903020f031448010550b2414000708036082030048900182c14480c0d0000c107403901149020700505034040b8a0325584500c030040c2c0040114200498218803420000922940c082c41040302014080d0000300d4a1b0482440460030034210700c5125068600e40b040e4840003a900030651241d40103001140c1d00001303200b1492610380306007040c04d44007890409041186241d8490090410021a40c00b125540d444603941a11040703042e01620b40560300c01c1e003403030714800b006812903500d0140f40c082c3c8915100403502d4040c07000a083c883c80c8013103903404c2880c1c0c00d00c108040d0340c082400c84900003007100d41c2882d00003a40310081840040d05142c1c44e500000d0355840200700701d4584a0883c41100c1c0e99507950f00c101d5604012030340c00d0a106a1514050120300c4503400203204080b80c05940742c000e0f03802503030108a4200c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 760248192 1250 760246942 760246951
    0x30402090903120109150b0c070303081305060403210c02011407050c030f0307090b0a0f08101d060102010e0d0903120206091c0302070605010311040c1115091212090d020604030c0605 80
    0x2070703400001428847e1900410002c080d05c0042c0980e9815420007601d401805000034030702084c80d00424001c102c002c03800e10341284c2d051030b00c550340b0990104501d0310704100700e049442c0980f6040701159851340540c02000c1404101c580c0020036a80c0d090141c9041c080c424140383e141d0010004110461120001564445000c0c100103004c103485a101150780d4000c00d11510204814001d04a51185c00000f042d61042c0340300341d05e00e1410b00348080e202145030307a400310b14110824413011442c540c0c001e400400044900c00115001003d0540005085004501c001e50701046041078928100d440400c1c482d209070b00714001040f040b1645070301180c0f1000b05041040405030b09000900c005079140c05154000c40c01074801d05c56001d2010100801c45501c18603181c280940c01c2d50704a18400b000c00c1c01c190500d18109070490f15a503994816040c04081c80822a0b014000642d05480c1040b00a0541c05880018101c5418000090007641c0e64001541d01030701080d42100c101000415580205500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 760249442 1250 760248192 760248221
    0x13120807021e070e040c0905100302010f030228091a0901020c061c02040627050a05060d02120f090d0f080c1c1a13050f040b1008030c03030402090903120109 69
    0x420307984d80740c04a2800c6013541c0c2241d004105180030440c8003468081c00c0d4022030b2000f00c0148031841c56002038094a006000300082c982c0205115030404106102907203642c4490000c80c00036082d1080042030004580298222005900440c80b208212070b02920000001030300100600c00980041003040c4c0c0200014211007544100401da00c1e202a0018000501107a120444450004225000000000511082e01011400003002140c2e034504200c4116081a10392a81d151410000c0314080d01c12402450076516648060000c50582c54071018841d40380607058030285038242204031044842480708d540000c2c5003201140541000d54000c1140041554031007203c030240804e0300080c0e4150005448442841d21022511400c1056501e0520300984001300414a040e030003032012039501800142660080600048803403010b1030401001d814580c0c1104d8951002c20106581da5004440881c011007801d80426001e40000050300d0042c0c40807800d01c0d00907030901c1040802000c4454441e01c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 760250692 1250 760249442 760249453
    0xf050915090f1014010b0a02060601030f09050f210f040506030a06090c0c020a060f120b0a0e04080d0b041802090402190314010b0d0314030a090b13120807021e 70
    0x1440c002c00903442c54555160b8081036186942c403004c0c200000580c0185680b40080140050403507000c00e5481c3d02401c242400100c0e0300800203403a00804003c50010b0140c800c0b0440242e01e210001900010b400340c00d4205ca0400300c0d0303103003008110b01501d0320300105050240001d010500e840c0d4055503000007100c1002442076035450518083d40c8408000e074020810610350319007541054041a4041c1206042884040031032a5008106034401001e54064954a60040c800365840e6030515000307001131105841a4101418080619413001206032016440c1042561a07410039008080d5114048400d441500000350203200e000080248101d84c0000c40a030014040080c081007840550702840301d4941d185050f035115421903044480c1c507403041c140c03c560750001079440381c0d50019508000c0c2d520b948945510b1000c00213440551001031030b0352a400100000c0c12164258448030364001c0c40848555005510b0903616042d090311032070010b81107101c1d414101c0442620507111100b0b66411510b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 760251798 1106 760250692 760250713
    0xa0203070906122d060e0408090d0c0515071505040b0624040308070203060703060e242e0216061b02031c030f05091509 53
    0x100b0000002030049168181341c0242008200c50219030403454041d00200d101a00c4044180d20802e10704140006c0826040489600070354010120503d4852100140a00540305103001e40700c101c08820009081c2d00c8440e160060000c0003003203a620ba02d910f04c0d09000e03245004d280485c102d801c007000d20010640704451503412100c1115214642d41500c811080381001c0c1e13480d4a820310201281c00010702c08071600409078141300303c0a5402d19950f02a00b0750444103a80111084407101c040000e40601d0f440c1d01c4065001502c040e4903a00d044590300007640c88040a05085290401c40102c25000d000c200c0e951882003110700180c0b802444400c1900002545440740c0002c0044580e184820b003014480b1503002d10360090305981e600a49500386152200c0000e0704900041d10f001d18171a90401c00c0e11400c0d00616029018000100240a0a8140e840043c1960000d4026580340e20f = true := by decide +kernel

theorem cover : BRFrame.Cov 760071942 760251798 := by
  have h0 := BRFrame.cov_init 760071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 760071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 760071942 ≤ n) (h2 : n < 760251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
