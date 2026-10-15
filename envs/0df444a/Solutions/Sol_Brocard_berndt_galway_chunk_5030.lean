-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5030
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:31:07.502988+00:00
-- url     : https://prove2.me/submissions/7be744b3-1b6b-45a7-95c2-2dc1405b68c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 904496402 ≤ n < 904676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 904497652 1250 904496402 904496423
    0x606020d02060415111218061501080603010f05270604020d14070b0f1201171f0e031201080d0e0a050105090a18060305103b0a050f1504 60
    0x407100b2030030034940d5549000101d02c5417000060000c01707070011005002200901000c000f00540d5549181ca28608030b0000742040d8107200031104d0a540c02944240d05116020000c030319240c03000d52044001d200c04480810071820588801e01c3e5001010905000598440003040d00c00c8501040c00c07805035500908010901101d035648180070840e04900302e5580c000e800700041c80f5100034005119508041c0c089659410820f10500c14401d03060300b220016008410182c0f9051100007104c004400201da00c2041450086290401510380d20345c0c030100501001c11130341c080c10402c0f00b032175044c0c0b8490000c0e40c1480f4075284007218100302104a00754480ca500c0c904100650051004101d90311024104a1030151902c007010081c800c64100c3d000c1c1c3e1030f5038510400510005106041c00150614418000f1190060b01242e41c01c1451004852401105071114013240840321124140c1c0140416545420303100d061060311107107020b105188600070200c4d509903501c0213040f414801c6510005400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 904498902 1250 904497652 904497661
    0x1109121618021e1908010b0301030b0c070804150807032a0201091a060f060f040b37030e0a0c1e050a080606130b01020a060f0b0d0c090606020d0206 65
    0x10748844410145816155003000600001050000c900e15a000e090316001d94804c04160b443c11401e0030390101e0420406080010701045040360203c0341100d421101d003800ca6128090031698074800d01e0401040031000150008070000380d40d040f600303807541540740c00119568000054094540000c0c50344a00c0405261682007845081c0703400041d00c103a4400040c510303203640d071200c3d60114451800440003590008002551810f07000c0e0b084000d82c25100d040c10941c1410174400140a5070080e00004803021594190102031030001d011002452008011980c0c8e6181281c0086601c0e29107440029040803d020002c0300c0001d1042c100d20b40c00703049024094030b44022202c1e50074901100815140943d54001200d50b90b88d00c3c44005060103001a00d1182004010809800001d03041038428508104480c001c0341c0e0042403203440103800c000301203126510052030700028500900703030a5002c40d941c03a0060600a45206110980e40810b2003004441d490307450582e13451a00307445440041e07200c0030008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 904500152 1250 904498902 904498919
    0x6140c10090c1d090d210b03032802010f0c1d0a090905060a05070813112404090e010504050d1110060b1213030806010302130911091216 60
    0x508815015070702503910183c9404114032442540c22811000140c00760500200007001d05c02c0d41507004940c1017113444803050140b0400c0241d90700d1404c2c0d50581d41c84e080d01809440600c101c170040d8505564101601051158003400c41c1007801040c001980303031240070140c10100c0d10030070740888481d4440f01070042611407031000c0e9080300c03c1420f401c100c10b48030020724a9540d0007100d108620074409084a45400360503503048450090141c410080c1d20381c01e02c008040c2e50054038070140d0700408000280c01c1c483e404101f0000ca1982d54590514220840c04d00c10891180584241d4030074201c00c0c8a00030b001c4806d0340c02e90700141d80c06010381e00305100e01d4063310702417005210218140e0302511661041588490203e5103154420024980c0024481c001403149481c035076480f030030501000c0300a40c640d40b0001c003130780c1d00200540e040c564000380c2e40100d01c841d40c420900604000030203004d0f2000c55036903103003190890030701c1a02aa042c080c0b1129007002c04500401c01000c02c0700700459052404814 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 904501402 1250 904500152 904500161
    0x6121807052209051c0f080c0306370f05060c2d060c21090c01030209010201200910090605031f080613050c030102070b0606070c0510030606140c10 65
    0x40781456599038184600140d014001260700034500e1158503510000e075000507004c8908240c2c41000c06c00b0743c00c10004c0d00c0745c14602740c0f82c12510a0b90051a40c440240b4846060050003224000152601040380c4a40174488030000a81d448038004c000802c0d9120f05100981c081e80c41d00680d25040340d18160024401081050004520000084d9880f000c1c840070070f08000c016541c03015007020000b05600204500d45002c130f035032062a485101c261601c41942900e410b0710075400750415400284940890b8400d4010030110040c015500213084c1c00016071680990100480d6402281c030070082d20032440c02140d445084800a0320748900d03582e030b0341c02e50480518440c0c040c00243c03181030401042d81401000a5442442d051003540c85020181c10014580b140e03194400d0302c240c3c010011000064940140c05801820503580f00c2e844486a203400c4088d5480c54120030707040f01e403000700d0300d8802d0751540196084038020b486d540c10302005441540114406c203001e200540e40801c1404102e400150300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 904502652 1250 904501402 904501459
    0x21050601050f1504030809010807090602030a0c11270a0203040c0618030803070e1912150b03120a03050f07052706030106020a38040f020612180705 65
    0x1500c00c0e0595000d03e045501d4004c1d800c25103c4004c00b290703282081d43c01c20103080c2c120a4509000d00c0003860300d94002c0d524840d6143e010104070944400204000c0017450305048290300600100c01c15000399000c10403030741c0a0011100422002e80428038100e420b02c02c40340200d800005004980b820000d09807500008604904404a01000d0010124203c000654020906a0b4586070119403032410483c50820402c80445100141c030300400c4042202180030f5036559101b4050511911800c03c648001d04002c4000e07505400380c2c4c04207001c003003034003002003801c41c2480d2070030041a10f601c442201540f0040b21504d01091081040003005984400d01c14141c001d401c0418400c2850300703010516a400a9124002603404000301008010050514020f0b500d841040a10b1a490122900380c4440d812410b013002011410301003018010918541031320320390090100e507a2804d800d00b079108442001c45402030200f0106113282c15000c800305804080320310081c1140030f0001001e8501e03410741078024 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 904503902 1250 904502652 904502659
    0x50304030c080403030807080906090706110c0909030423031906021b0d02010f0218011407051501090b012c011106040b091912050f04051201050121050601050f 70
    0x2141040010b00c0b01d00107201862096580405030f05086001604030341e0042c103450f071650494001c100000038000390590490b89685803402c44d82e009181a0b03400c140e012621141c0103c5070000700448071200000600459003c3c0215480d260755511071b18812400c60501c50758143c200903415401110600003544085015a1006140c048450b042d0b4506d2031030500701e15030b00c1d0418180381a4058080c41481c3c1c4140c80e81c0c400307503e40300b071b1500301e00079110418028134144022681414140080b880548551682c000b00f140c14030075250700d4241800d0030074840c080c0e0b111300700310301c1d001994072070030030841681381043c16540000032101c06200000c0da0610518104080d002158082e80f108200d400d000700c2c020002020b41c0d04100e400c590401400100c50101003c0c0f140c0c080000406103000b14088100c40d141c9551680c2c00240c42c558684078a40c426030780000303e400d012039105e00c190b00550480d0080e9403203a1000700b0b200d0070f00700304031401c0c00098099080440100303e02d040040c6210359086000313 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 904505152 1250 904503902 904503917
    0xa0504140a0b071e1b170d0b100905010518150d021207030626030d09080a03060806010b0403060e0307020d050d0f0e130209030109151e05041205030403 67
    0x344059890a44411001c1d01c03002c0009080c4201d458100c5420031302c0805607401004d20500f150005401da010000814404004030744584051001c0c0300c59207085040089803080d61110b81c440d08501900c0c2302e070001e0b4030401d138040101c24120f0051440204640d410386a0314240354070a00e0900c14502d0344022643c200b001c2400140000c1c60b034100406000c0414640180c8502e00050600840c05c7c00500d46001e0525007842485801103038000109200194950b404c81c020380040f205086001d0380c61800c10071400c0070420410010b54001401c54203146680400541380c0d50308000340e850400780b26002d40090100000c1c0081040303a0040b05035400d003102103a2422150b80e000c10040840d880c03090380e280c0c0141c40805200c42d032060300c5405050302c3d40303001c00c4485000070001d581e000001c600601402e5000032405c1d0551000c1d00020301d5141c003d40c0303014000380d503441400c024142c040b110f159180c0b805145107485a041d40b0070103021719000f0700249465280303181c051314103500140c030680074800302c2c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 904506402 1250 904505152 904505183
    0xd09120204201c06030309030b07020708390604061407050618071a031603090f030f02010c09240c1e0b0703020c10051302370e0a0504 59
    0x4807482c250301038051000d0990310614580c070640444180700c1001001402d00b030302040881c0d070040080341038070b400c0782112040742c568a4007030749046400d9001402c00e001d88501d0b18040d44800c91140b04443d658028071039030cd40207491081d041c04d0911101c83c2d0050b030510013405586d201e0070f01881c040b6449d424071460302000c2c1d1070b540c0c0b03000e4003260200c842c05000c1c0700b0002c070600180140c00003010300d003948804044801450880f01c3c040206089150760b10150326030401d40c4203811100780f01d034001039488400300070f600f070080409086d10610000b560814910070003052044100c481266060207060318940c88004000c40c40e0240f4488800c00c0248100200f0042400303c0e000e400d072483c0750040451007803003071304d001d840c0e40e0030081c499000e01d1300c14003640684440214181c1d040f5101c0000004441c4c2d80c10000301c161508644000c0d4221110603a03d8464954030b15101c40d81348010880d418030310301610302403990140c2c2409803084416030500030400e0002aa04142d801600c21410b1030b900010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 904507652 1250 904506402 904506431
    0x40b0408070303140c06010923070e030115030c05060a0329032e0903200109020312090a210204020a02010b090a05090a1103031201080a050f0d09120204 67
    0x16400400c040d8000c00010010142c0045070140e40e8540080c1a40c2010350148102e6201c5105114242c1142e031580400e0040480c40d04402c2d119111056021000e03003000d00c401002c039022240020f0080d843e140c07004215230003680ca80c104482d840102c04902c40c0c140001c2c041e140d045001e4000606880c1e500310b104855040040403820940440500d14400745801098035104416001c1c0340c6902c0c3e94610743c401d4003200345103042d1980b28071501062001080ca0102c902c000e02d800041c01b1901500c030641e00061045d0042c030b003030900841c110b41d1030202e00a8280d4441c462020783e030354024443c2c0740c1001007450a07201c500c0d40da9400910015040d50750307008581a03900c210030020040c0d6541c100341205180c01d00c00d6540018010300100701c540f41620045955210a54010b011005100320100c2d65070340400803102c1501c1c904204100c1c80d6554000c0c1030352040d0740d080464660145502c682140700f00081e20a0780c840c695034552121a16000300c00001d450710001c186d070041c0d1120540c0c41c40c2003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 904508902 1250 904507652 904507657
    0x4060506120309061312030f020106060e090c180402030c12010f050105032e0e04030807090302030316081c050118051303030b010e0301050c030924010e07110109060f0b03010e120a0203040b 83
    0x40c069298008d000e140260000d003196182e4101009002d1114030560540c1c5031104816800b495100e451560340d90a8803050b0315908940300060340c040e0002040041d1108508007800100078020b400021030390300c035030001a21110078018140000c000384002112001481030112030692807840d0f103c40856541030000150302107410019680282c04140000c156018194642c400c1d428035001501070700350703400613885e4400d0074881e80301c4420600e5040240042d02040b1000010301501d403030a06220b9202e03410140809104807400110b5600426030f03031a4440c018288a4110f524049401105980c1c00b0740050009094081c10400704503041401a00c003482000d0282d810081000d80342c0c42c1c0b1803482031400c884014143c04411130580c0d461401c00902444a0640b6500c110450b00c0e0340c5d420200302d47c0d110f49400c10658543c20300014400784084c950080c00400340305281800400361910a15007a601440c050324a00ea0007039204641c01d068400207411440c407130f1300c103030381c50a5a10b040b03080c40798 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 904510152 1250 904508902 904508939
    0x150e010801021801020606030705060c01020418060603061512050c0409050709050f030f0319020f0d0c060b090405100b191706090114160201140f040605061203090613 73
    0x5a5000580d4a400440783c800e5001e500002d01c0103020314074001c0007181e2200a180b16184c000c80011521640708030080d01076a015203407c00c602d44490850312b680c01d0142c682880f80d84042440c00402282e40d42520031042c51245440d1035000414401c20700301c10051100510031010340030240008036031554a8002d0900503441c0307584190001781000708000c2400c0134100340324030a6100810408607c0008404c0d1000103030607110a0b002d41c0035010b0241c0c01c00351100b4011100380141c2d24440ca101d900001c2c501050b60040ca800c21040c0c400030244004280d0644001e030040c0d000ba4800c03e10030343e06400c0000074810280003203d07510b025554000100360180c00940b400740214031507401c400000c1103000d0703000080b64000d0019181110700491103a50180004006510300c501c0020041c1c000d40000c3d2402c04624402e2070b1903e4400c0500c14204010349003110f50600300303030219409150000c02c0240802c0840c002d0740c901202d0030104079469000204480309140c0e000390005442e6240303090405407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 904511402 1250 904510152 904510169
    0x1612060b060403031e030b180604111b0607050a0509040b040605041803110102070206040e071b14191e150e01060e09070f12021f03020901110604050c04150e01 70
    0x100c1c0002c0000c008900f5401c0101707020103140070b500c80f0340c55440c28070b841103050b40341003c8103560b1074401c0030901078001d83e040b6030b103090340004100400c00c0c100700c007068034040d08c201950040c2e11520401c49041c8030380c51061000980c14000c0b009030b85825846050042d00050002801c0c0c0d917100086020b849030718603020090310b01500071400b072641000c2c81c2c480094003a0b000310324101c0580e002600901590154038060340036400000d21080c0203981c0020040481c0c80700b804483c0721890b001c502c0800210f40f00e03009008040c80a8110920700b1040c00c0b04a40c401101c9044c030740c070744008401049480100360765540c0850916103500c50988140d1184003419000410000d040019141e0b1445004d00701c071510b0386c060081001422a400444816919402400d124290150002a08280c440a007040920030310010300f04210750158000c0040d102c007030b202d0b0500041300312900c81d102ca0f4100c401601d603070003100810300d5a2400394418408960807402c8a0401622840601c251034002d0b04a50107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 904512652 1250 904511402 904511417
    0x60d0b15031b030d0c020901030605190504050d090e060307090f060504020705060a1104030f020f1318120203042301180f060806090606090f01030b040c0203070b091612060b06040303 80
    0x501e03060a1151380c030440c416007411400000c29a000c01c214010520000d0802941e84010400221001000c00480d4006000038886820310741030590320359a40042c00f50220300c203100c0001d034142039261010720820009003d84051483c100100300034206207010340c404250744000124540d80c551000d003000354010b00c0102254644049004d040303600b84128511180c10520040000611140880144590556500d818800c1704000f040e12041d001052010721070030203901c601c6503e4007008003400345010302c920080d132030b40404041c0c0c0c4038070a42c003400b000341100b9030382c040c1e00000c0c41e84080306241c0181f50a01100502c0c03000b1305000354030340d000b016141045820070011154000701c00b0f500401c08803010007141c100800000e000d07105080046000324904140068203030b0007030b44041e060041c050000c1c400c01100d400003e4403903000034400c40d0350324040c0c000303c1c455940000e51442c0001e0003403c0e00c00d01d98240740720010a40200b0318121400c9848043c90314281c0c0310350001d0401144240c40b40017 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 904513902 1250 904512652 904512703
    0x1614161508150312130918080906040302120a02131a0f0d0204020309100608120a030b010c06020d0b1306060e010c0c08010c09140108090607110c040608030c070608060d0b1503 77
    0x1041003505038000741b0600d0401c1541d0152200120340148087e50188109644840e43d2010441c240141d41c0060751260340082a41100c40700400c003140d4051084400304107014030700030f0540c200c400102080100e110341104980d110b080c242104400040000c04200d0351030429400903003aa441200c42c00b5460300404441d4040700182d015040c040c00d0f410020b019101a43e60200350907004d204032500803d600d40045c3d6043c0c0c0d000f41018915030340c103c0419503460052000400107044008041c030301031816402441c01001c040d100322030581e0810341d1051034070012680112820388405005a0b1000000c2500080408e4248590101c00c00e00380c44007802d640c07822240403400c060040e8a58107000010f0108440302c1301c0428480c1d07010b042d134104400e425000300601c034500300c40c002c400b50f045440c0120101d800e590000c0540340e00044403045411190b21164101d916541c01c2d2801c070340001d00c0c40b05000020700c00710210f50b801111500901501c4a05600180c68103031040c1c009041400703e003620340b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 904515152 1250 904513902 904513927
    0x1c08011a0426071208030c4006080f0727060c030905031c050c12030103150605100203070605061c0309171f111614161508150312 57
    0x100100300f07014404c1105501d43d20f0a91000800000c041c49001a0f1091030b507109550950301e6958410788041c03108402078a01111039503044400c400490030070b4002402510440505124a29609440019032200002500d9201c4002041c405085802c40d04101102240d252a001408a6a246105442035050103000d0405a0f00300703e0094009102c510b1001903140d1800140e0341807450440c0d03481c00320140c06824181e0290040b040e040b400400003090084602e20300710b86004c10541044002d64a07000c006104c800c140c2101c0140c0c00500c10040440d9555000a03401107014140b40038120800e0400305010307a600700704501140d01084140800d0440050880851503000700420640e620f40841c228a480490300f04c1e50140e445080702e042446c858026601040800b103005400b607001881c2c003609040500201c031400f0b204440010340c0f02d074804041c100464241c025100d03950881e44104490860000b0031520801504410f00c440740c0d113080140c0d00203402071172141502c42040e50100d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 904516402 1250 904515152 904515163
    0x6031e150705070f020d0c150512060301060501020a0b041e03080a15060221070507151107031e0c081906050f04021f1e030603051c08011a0426 63
    0xd81c1c1080000d100810000e5003011000c030329541c04840c0030241040d58a02000e0307088041d00415131040c92001080002604a4081c0005100c034400402c13550342d464007414201e03046031041600581c071810341c2901091090303903003e80041c0145d0319a1412107902d5107103d00300c02d03188d80860000d0020300c20071540b0311040c030130041c08116070b50813000b22a01e00400250740318148072010b00d402d04140d13001d09040c06601c04452815a0080a480b902540d550b03110610051041d28000841e0f09000c01c1ca0b001080800e009080e240e011200702c0125681c0c40c40c3c00710348030710118200c82c00b0361104004903806200700200920b903001135042001d840c44a00e045001c0e107401902c0491120401000d0000617a43d40042c4002c61544580c0d004100c4000d48045501e0b0b844181840103901c0c00030301d04840c443d4980c015005907400346049a41411000340c01c100050f05030110040020000c000502c14442420814101141540c0f0342071705068940780803001d05040c4070011580794911048108000909008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 904517652 1250 904516402 904516411
    0xd02071a1b1902011e14090303191e0509010b01030e1903080606040909151d0a02040c17181618021b060a09200a0e06031e15 55
    0x4260070040c0895100c00c10600900c0140010384451051890445100350301902c01c01d2004e10085200c848007030800700003080321049000200b00c80e00c002400340d501c0001102c1c010368220105061142080c4000c00c000c1070600610b0b160503281000b694078400040c091b4501480061000040e001080000503003183d040c59880c20040c0c11101650070166050310414040f190035013080700f001d941c0da1001641500c505e800c400d0b002ba180068080034492071080302202c1030500f10041061820300410325080700b14890030100c042d03002c54400001030405803c84c6c4480003260600120065015800c1080c0d04011a601502004917190400d441c080070003640e000660303a1603080d8a580c0c140101d284510b084840e035408802d070000f9a10395503c0c0145c2481c840301d444603096448078200005220041e2810140a42d0200d40ca01c1031141d25450389140008210b40040c0310801e454503241607845070020003041c940d85030180c2c100d88054211202c4606140c605041c000d8980c3c4030600700d40c03007041c00d406003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 904518902 1250 904517652 904517671
    0x70b18011b0503060d1a0403020a110103021801230f1c0e0a0b0c070206030411040509061501032307090807060309080f031519080c10020a0b0c0d02071a 67
    0xc1c55090aa8109049a4028909580c10702200348603080080e5206110016810300010f6202040281540491400070051180c0035042c1c482c848200110180d000301e100c8071101d400d01200f04505580240080404200c0120780c00380d94441880c0790390150740003402084a1400000359081d80c0c03101140c085900201690303c1000b89440c0148515520182e03074400918a00c01c242c042000302c0801000d0b42c0c1201d6004182e503503030707260a07d0200c044a10105550340100e0500f00030503d94900807600c940b080055600c0042c00707010040044000c2e19589101046040d02094450b17210800380c00701910801c0a0303141c44100600d840c0ba05031400d42641d00240805280003003150000da0070a0407501194108035002d601da45130405010031000c11410030961000c1510700310b480d030301952203002c4126243c60064034161901c0c036007805901c040d52039803030740180c0110900c5000540d8601c41075410101e0303512001e0500000040e03a43c101e0344170880560329110f00d072013410340d01402c000d01f02e42c0c441d0114 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 904520152 1250 904518902 904518941
    0xd020d1b081e1c1202130603141b09360108070509060d0204180c051507080a0c1403031906120314090f06040b0a030507020f0d0e0105070b1801 63
    0x103a401d40c07954540ca00c55400d100310044030f1140b01d0b21031407582480540d203c0c03086640c0d8185031400e020080c164820507000c03a0405204403841c03070784500c00512030040140704004a40b5141c40c00212a44860862948400301c407466030040e1842403519040d0b21010b111050800001c520442c0d503d9005074080c03942a171007040184125103945d200190040c4054076056001c800030710025001d800c002c0c600405078009a0052000d105811002008a52090f208010301e0045002c022040384103c16010304034140400112a201e0300c140e418503502401400007100c0b02082840c103034156403003520180702804507071454051104c4144070390002442c14030100c0f0742001c015940502540181041d00d18501000305040303020391240401c002c9580c03802440c8070750719600c503001c0c504181c0014900000003440d1000103800039000148800d400d212181c014454410490cd01b210640c0c26542e4660402405200640014040068950044c80000f440701c800255145083d401c40300310603052942140306 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 904521402 1250 904520152 904520203
    0xa12020408011d031e0a110d0c11042906040518040308010e01081c120f02190906051204050a020d0303020304050c060406171b0a111005060901050d020d1b08 69
    0xb5542c0f94118140042103851b94506001541e0703c80c00014483d0042c042c1b4490329159941c000e178080402d41c404ca60101e1203102d41000c0c032044641d0140392691500b08412045a804070070035072101c0540c0b00902c0c0b2440e20303855002240c82c0011403a0501500b11002d000d00c010581c0008180b4090841c144000d41c0e00e614180b005940d46074032020303802075811f1144030718000e64401c0380c1c1207000b100074000c188074011b00401c40d0707002175005818001e2030602410741c1608407131240000008845581c1e80700303800c0100303451005d404ca88000d04115020702c83c5084180060301c070780041041c141e000780c03030050b20380c036160074440d0a008070350300558801c441c00c00007800910741040c8882d580701c401c0050b01c4c0b80d075540c100e02e0300c50114030207840e0011030b240802d41c10300d200d0b4443c84c2d030340b0030010740300995020100c0c46404d1410340c0d20907a402a40051600010701180c2415031003444a0b9000400e410701800f41600c500046d208102819000740210780c906000e0100100030900c28591071b81d01e1004099031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 904522652 1250 904521402 904521427
    0x5030d08010605070c030506070c0312020f340303061d0c0d0e070e01090204030c0b0f0f0304050c09010801051e0f0a05070909240b16080a12020408011d03 68
    0x41400b0308028408041000002c1c0041e641181c0065580b010440320300b410076400240ca8a40000c40403030014200880f501c80d41c0e035650096500c903000e81c14046040c0745003441c20039040e6103040090b8540c40610f11010705007a680a201c54561400b94900260b03860401944110a01c0c081c02c0404213484a00180840302c40301d42e0407243d0402c51028000b500f070100f160703090308051145d07200e40d41d4404258000305606680307030b0082c81240e02c14201c4071102a52030010101a01485800d0079800b4418040d8803840c18a01c401581e0092042064811125030f00300010242082038006d94183e1303549804200d00e403610200d00c03008504610401d280d203450300308181100ba40006040078242500c41c40415246070196040c94094880b02000741b204982e140030041d00440b42c8050040c00c80351591002940c00f500c4006c132007807846c4052202030514855211241e29902c00119201009020030910186036454809000980700040010504e5000e180706660030081c01003280c0140d40081214911590 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 904523902 1250 904522652 904522667
    0x3306150d1a100f051303060603050f01051003050706030c09230103050a1404020607020f0904060b01020610120b18030d090204060927031e080f011512020f0c011401060905030d 77
    0x903d0b80ca032039583d03514000c250b00311200560b07200520160800c00003004021000c1040c52980030350300000c10065a508400501140503480083c01c0350700305210034807070107119812006403045207040841009907078020303001002001c81d1804000c0e00415400c0e00141d0790500966030040e041c5072041c1306901e2101545825100c024100034803513180000e0010841d100c050b003070307041500c00601c4858685010f0600704043c05400d80c005e4014040c990020340481404400c60050720a0203940e107510380850303030b22412400d001030020400c444680d42c510042d004100005c0c810b00c42c2a130f2010801805500c14402a07406540100480070300b0106120710080d4050302d4282d0590822107180018001750806460a0030700c040c200d2040b800b258900312407690845507143c0103011039020030395140ea030368600300030540d40c0c0303458000010040d084d184130545040d0060310175003a2003030701c4520344845009030350f00711100b0201c4201880c25403001084500e4004004400610098000e040b40c1034034440010b02d202d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 904525152 1250 904523902 904523927
    0xf040f062003031014030f07030818010504030b130609141608280c0b12010806130804060c0311010c080f090f0a15090f03050c3306150d1a10 62
    0x5c005001d0007001540d03003002207102040782c10703082c1d071170850310390828403840d50102402643d040103081e12500554820b2040710116600404074010355194603000407840b034210365082e90b07a90340320110500030403641103440e600250845c00500c14010145414003171089254404800c3c0d0b000b0051550800c0b210410803444080a03003003c4440d10054649510341e10020b030405034413500d000c91001c000e51700150045040c1c90305002101c519642d01100381c08489100b000041c0f240c401400f040083c1402154040300280c07103420481e10382c03500c00058074212012040d0110000301c002c0240203d004070901080d42241800001d00b00400c00105681d543e2060940020090541c0046a440c0c800c00c1d83c0c0036130240c560140d440c049801c41c42c107004109410805800305240036086800c2c035005501040d04100b0007610300380710744a458003125450240300040826422079029032030f440c0308603000402455448210403000804a040807480440c400f01200a50b00031000310503d080780603000b0240c100107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 904526402 1250 904525152 904525169
    0x70201030c050f0d090204060b0325051c020301090b030304030c0e131b0f0501030b1e01020a0b09150609010806160201062c060619050f040f0620030310 67
    0x3954070508044800d0f1042c0d08145009001c04a01c02c0c071074480030b40003807034094000c60307092150503150380200d14980300c00d0303406101c050800c52411641c0114041000403803182820002d00b00003211035000c02410480010302c00203513000006001c2040340348079043c0303035060a40045050038115a90004002082e00413904d48240610004100000c191644402650700c00d100310400d02c61800380030352101041c00b03001012244e0010211362940300e07100325540b130300000342401d0441070f19810f80303072900b012100400d04500901c914800030450944216000d00140401009034160100f550301c12108003400b03980c0300300c00e0240108401503000035040d40140c800d516140c034104800d00245d004107061303444032300344d16512207841115900c1c28a40c076503540311044008040f0b0b61380c4000c011440c45940c01500c0382001e0120074020284c4210b004e400403412a0a155141548070811500001f40d6588040c00150003008281c10318060500e590002c4940c080080d0700314102890041d03e802228000c0088 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 904527652 1250 904526402 904526411
    0xc082107110a0b0c150906060d0201030b21030c280308061201050a0e060a0c02062202040603060902042316170a0608120309030307030e010b04050c0a09050307050607020103 76
    0x1840d69042c81007801800c41e4460315a481003206030b401d49400c031011100d1003403000301000484070300c4041103140c40358900130400141c1c0d12696005500510401009503000144403a0348400c02c9400c502c00840300020f0002152140c003554841881c02a00c000c02d51201c009000070010b801d00103100840f14945c0c03505185003990f440c4000720300240c41d04400407203d90b00300400e1083c002c8681d800040000c0c1000d003907500541da064180d0080d1144600c0700c0340164000c0000920101c01c2c81f169860610502840211001080e00090180d412a070026503855980d186850110b00e014818400124004c1e02c2d02001c1d030941400f80c2c506010020804d85422007001640c03020309118940325484104c401d1102000703400d04903100e50062605001d1240140f2460700d026100d08550401c5c0d900c2487c5ca00000d500c1c6a80e440f8089000e8140191052950b64031007003c2d500c15a10380c0150380c4115503001c0341d603442e20000c00c8014600c0d461765010501a401180f81405207440d4081165806038080c02c0c00b15 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 904528902 1250 904527652 904527683
    0x60f0705030d0c110c1518011b060522020f010f02010923071e0b07030e0607050d080a02040e04080f07021e03060f01260c0a030c082107 60
    0x500350320032007542d00076030707840c0c5100448204e0700301c0b5140b007089484004881100c054241840805200c0c40310a0410b00b9040c03040340c20303600c03000c03120502590040c5801c4c0b0311f450083d10384100c0302c0f4000701d046034410384901c104490310190480c401c6444102c409560480522a00070444000f03810000758100020305c040001000d00075000302030103640c08861004980f0b40100a091010912107000b42c10b40510761001450707024586007070501c6105812040219441c02004441c2c517801410104c091000c11004400c0a0381c8000191031601e000e0380103803942240b000030007009a00c006040e448801e2042c80140300b0840c00c0224145c0c055405059075035510b05c501c0c84c0120501034158002d500441d949030103800b1403280c2c03008009401d4103a04541c1f00b40c441c100703000c60340c4a0034043c44004c12840030040345a00c8500c00ea5a492407094002d944c030345003058000ca03c2c003100c01e400540344014014402c200c1004100040c0d12111a142e038403100c2c0351000281800b00c1d12403c80007500180c81076a140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 904530152 1250 904528902 904528913
    0x10311041a280f080105060114030f0411092401021906200408240103030e100c12022104050a031502040902072103060f0911040b0d06170309060f07 65
    0x103404089882e030710107072036803100c500c4a40d103800d0244a030309508010101c0ca0950103100d4404080042d41041d50039681ca1075000702007014000d0040e2489070206040f44c0c0319480b0040072601540c01d10700020701140e0745001020b0100b10040703000e41154440341c0b1842c10281c403440d5031407040303601c0701001c41c540020b0501060502401c83c1c0b4800f100701c0004000400c20700019001c4c044080180c4007124002c5501c402e60b40aa0003440084e000c0ba4501120482c1e600d00082e040018244600740301c030500005807113103000344404d03a1079600540c0c04607580d400855492224403649400c244030103031400c1d06040100304480c031180b000402c000101c0004525510003a01a540074014000046480700781c10305110407000044002411100c41641c0508007045c8a4010b40c001d41d8140c01c1155800351521180100805216048048203401440f0109002507008003d009000403d100030030000c3c2451460050201e0f8840501d042d03900412440e141038a525003a1014030118480e1079880d40c140d030800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 904531402 1250 904530152 904530199
    0x304061b080c1e12061c11150d09230a0804090902011b240917030a02040302090408031e01060c110f040504150b011d04051302060d05010311041a 64
    0xc078005002c500d10300360905801c541e600c9000e01b190034038440e030710340c03464051442a0514017400c11407008080f880f041c20310350003020f4424100004103190500c08002e101c203c462003102250303405181c4024244014100380341000079080361014002c98542c0e9541e182c030034460f41c4070320100561500c801c0002d5a00401c51a98410040c1183e0790324098503146c40003034014152880484050302c1c3d0301503c440c0b603131440f03241e0404e0740c468032010728010b1303203504400e00307410084c0b02c15401c07074081001200503140c00480741c2c007891182c0220b54682c1000707002608120f9030003914680034250a0010000c003a03004c09064000c64001c0e590300d0021003950045102d0480f298800782e000790070724042c0f00401c0700381c0307040204001400d1010000c4543d5840111050102000b0440524010a00c261900c0c1307000e070304c119000742c6081200b4a0000f400d234003040d03d50b0011300d102d00807595180c00401c14010329000300005040e00300d900300070210980900c540d81e443c800d00698003408116000780c0c00c61110701c90 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 904532652 1250 904531402 904531447
    0x1203121b030702150121020d02040e070e0604050a02031e190c020d0201060509090c0906040906090305180d080a0320040f0609150503040807150c050304061b080c 71
    0x2103a80da24035080302c010f540c4803112005001c000d1610000055940a50702d02c0c401d01e810602149a901c8880303808204036070030741c8613060740c0c059512022035804810412020340201505540c2d401149031500411045880045c503111605004108000380950307852501010303074414050007040768503011200354881c2c41d0420044109882d0680b18042180c0014030b80011007000da0007840b215483d2022b000c800081602d0a140e240d010300c0400402e0300d0710150095020402820000e60002d01d500c401045d2081c1010503004260002100000a51404401514450280c0e183d40c0d0006551b9111125032040400e001c082560301c0c46508040c0c064040b00500e40248441d940752129110424150030560300d1241d0b502141d181000001c03031019403003c0c9a2001c0d12600c8c0ca0f4159512900d9041d0180c1c45500100c81e14507811b800124840c0301803185c035081c8041e5548103a228509403410340308585124500580d6040c000341b8207140607a202c4a000c1e81b24070780b02102521184622014a1142e0020b0f0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 904533902 1250 904532652 904532701
    0x50406030c122d111e060c21091f080c0f07050f071d010b0703030b010212030f1611061501090b0304080a0311070807021e09040c090b120312 62
    0x45000400e804045103200d5480c0c050703115213854050403420080111122819140c2031403610801d80c800e4904500501032240114055038000034071145259403030348090001c1c01030703200049250803403410300c1d001d29400152003009603070b00c3ca4000c0c40c001c0c2810800034590441d41c1c0002481d590021a004241c503800c1d907120301221515502100c5460702e03070380c440c010041d117208903c2c10025141940844207040b03035103014001e454268030352030407000f415501c00524194461a02c001e680c03501404021482607050a02004503428008201031080c9409191442000040f0322041d6840001041d01500141d000d242d541c0904503802c01070700c44240036030003000d0554000c030410007403000394801000c10352003c1d0340400c05c001d0340d16040143e9009420001c0c0a018061040a0050904045c414180349013441040e168502100000300080e2084408440b001d144010402c400d8100c0c1c024081e194000300c410807520200a40140d83d00d0182079495160702805601080c1040d02e004134000042d56008c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 904535152 1250 904533902 904533953
    0x15010c0203061302030c2b0206070b0c030907091e05100f06031b020a1505040507050a09020918130b0c09060a0f08251808100903020601050406030c12 66
    0x10020000c4a800c03c040c140e0090051090710010740c5494030003201015120000351607410800c4040b455182c50120707040b07030449410052400030078070820f42c0c01d1043c034117108841e54916045011500380506580604140c900703000c200301080200056121484000d140c0000c3c0703c2d51803980c03a01c4080a0340e030004e1341c2000c201c54082000c59240e088030b01880d09942c040d001820462008030382c1c6032480c00c805440c070b442000d251458010b00340c00480c0c015004408a80105860b000011807941039640f214100e2a4002005d100c40c1c20070b0000030200d0b00400700480310900c0c001c0034440c01140d003500000c0c013944903400044c0c80301c540882610000140940b0154807003102070005003564546290120100d0210000960f41da44c0e00044800b650851581c060009190480141c542c0c65000d00f10000c0740c002d8400c04070714500100046050000d500c0d2000c160341c6050304002e42800d2040e00b0090089003802d0045c4042035120340710308121111140702a400505608100306080c00b4122038104512a8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 904536402 1250 904535152 904535161
    0x14011b080f1b03030705070b040c05031b041a0913170f07140105060d0803040515070914240903120f0a1d0a05040c050c01060e01091104030b15010c020306 68
    0x2500504040446210106620400c2c04002a904e010031540000003176010402c04000903132000f442508980700b0850004802d0b10f5800081c2050303085140b1540300b128800280149103054020b010340905000c1c88104c4486071100800ca254030020501c02811740c2c5581c0610030000202131010114451207a03064a402c408106810160301c841c030300b03840030070344040a502c0040040c0320f0503006000051101d914000070341d031044903a4000400569190069080501e050301009c07015500ca80c05940c0e404a1031402c000300c54800441e0154200d010703c01081000329120140b42120000340f61071410140c9079540440041d140c03214070a514030f203a80001c22002d0402d2911000b51181c0100c6403036103070202181172011009400240031071a40000e00c410200300380e05150b803200d40312158514020345440c0005050a080d00caa0364030001096031401c1c010403034800b580c812480740d0f62104000f140340a19545a021040002421441d58220f82c00c0401000741c1c01043e0745494240d0180603610b65190 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 904537652 1250 904536402 904536427
    0x51302013501121b080a020d020402213304020c0c0a080d033b24180a08040b0904060f081621030e0319050601060e0a14011b08 56
    0x4140c04136050501241d48481c04541c10000f801510400030003881751500e00d408000041040300f1040e40c01a5080007a0040120b44c1e211540345810124040301c420300f4904a0618141c85c9903510902a200d1040f81501c8403803000c000a2042c0f4041700c015856000e140841e45c10300040743e08044d8021005c140005103504045026601c110141e2420415010300c04084000406c003100d140203904e40075001682b0154604013180480c80f401000c4a180000360100d10010710281d82010b00d000ba504010090842c0c00c3e610b070703903400d42a140050a00d0b83c85642d1046040d01a90050050400c00800c1d000308540340c0d907010300d0041450040d08414181e9903032025440d000410a0080134040310100071840008070740f402420700b40b0321384084440450b1510300f00c2e540f121078118280c1c180640c40c64a01d40e861240711119920340a1405403070194500f50380544a40901000305014a9540f1410000080e02140325110340718207003400c001c16485030001e40c50162101c00300901802001c54021810782 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 904538902 1250 904537652 904537679
    0x131e0b0f030a0f06050c030c0702010c030c02031b19050904020607110d1a0702011a1005220e1501020a030807050c0703060b030705040603020d0201030914030a0e0103051302013501 79
    0x140a04d8040000352246000b0a031207104c2200e079605c4940f4100021801540300755581c4203075034000e107000f00c400100e0fa4000307414103032066641d03003001440213004010b6250458100a2015000f8103080001780790030042448600300a00c080c1c0314100118641c0240b083d07441c004420f0314402800031030001c1380c502e462401d584150b160ba15040124500040e1181d005100da800072172184a1900442c201000c100600401e00e24508403c202041c4240d44e1002001066000202440107154003114148008904c01440040c020442291545404183c40e41c0201c3d103100d14580510308a0201d0b0796245050328944203200c0c01c40311610038124000141b09566024500d01d400441c280c0f1242e580d030781d0800040d00c00354080658007408420070303440190f00035070001400a02c10f8a217a00303440c0500d0304c03c2d415a00003c03070b450041280585140015030f0706210320b550001c01c40009056034144d5400013000e2082c080b009107070031005040e0850f030040706514035014103003249002040302d607116403a1b010200d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 904540152 1250 904538902 904538933
    0xf210a060e161d0a0c18030f02150a08131e03020604030206011215020c010e031c0f1b030902130903020f0f0a0b0703050604020d02030f06131e0b0f030a 67
    0x59440310b1000c112403261840c0110402ca10009240d032684400342400c0080c01185071039800d111700c050040c003608030031488240c0218010003210716404081e005120003440c2c480d211440c40345040241280d0950030104080e0400f4586901ea500203440346440000c400300490f95441c4160340c14120b504141d0300103035141c4203902c00d50a07941d440c1da8607084441c841d648040c006000350a130600703220071882243e010700350552030303400040798a50483c4161410b59000710032440440c100100e19210349070300c90040701c40c51410001d08011448040381d031880444c03031480d840c0e001c05407a200c4190a5595035842902c040d0051a01000f2010007854007a6803010030811480c1d45000d03089080c0002840400c45d560080c0d0011841c07405540c55032002c90082074000c0c05282d11641c2807117054010344051000d180b007030082e48010640341c140746040041c0c0c03e1000403ca0300150910b1240241204507454003152554410400701d040c019820000c0c1104000080140e0107110741041c050078401c5000f0359402e03e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 904541402 1250 904540152 904540183
    0x1f08280c0b0c0111040501020d1d091e07140f03041a09070303200601061103070507060815100e010c150e03090117040b0402060a170f01140f210a060e 66
    0x2410540304c030300c04940580d202d8140960401d0056050150264101001c1030b010001b001e41d0700600c3c08005a00c1000c141c2d801c2011003e8800d4180c0c160580348690b0b6044030582c00c00c0340022010000c607044510521143c3e241031280403010400304243c800f0100440b21030080188a286000800582c0d110504e01c070550015840e50070300d61a08403140083d04e0380c084088040c01c03140e0708084060355542c4050030014113921080010740082a0280040000351a09540d109914108540c00c020300c2c107000c1c030302c49200b505507828115105402c644402c9429001782084400a0703114100040800303104c001000c02c15080c00c04036511858003100800702c402d8241c0360790014410700898070350b002004a500620b2410400c0206000d0300d4050042c03d005185803801244034038941e4460078400c0800e6031403082241c070310b00041c4502c1c11040000c0e80414010349262400602241c002000d040c00355480d0b0410358010b645026040d0400c3c0200815560400d0b0305000b0a015210a90368a20302810324810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 904542652 1250 904541402 904541411
    0x6150703022b02210f0c030c100207060e0616030b0f03070f0e10030b040b25020a020109080a0c090c090812130906030b0415020d060b031f08280c0b0c01 67
    0x180130400742c00c0c0b0880e0319003c0d003d0074450103107043e4000354800c04049410317200520100d10341070030030400d00719000101000035031100808e10300030b016111424800180c5070000c00800000c1d082e45c1490444c03138219840c01040c00314490300070a0311781c95015030079909402001000304008220b0300e1880300300d0301520010840c580d52240c80240c410305501004001488000c0400d011402c207441d01504080ad10303040072208035004107041c02000b1030b420b0060140e04250880c40c01d668001001000131310500000e00440d11603603032210840419402800c8840781d4038000350000b540314248041c05030a50000300c030680a600e8001c100250000380410560020300c8072b002c190311005001d00021a540803540c404180c80e81d40e183c0745070520845502010550901c4081288505401000d0041c03030410031860382ca080c03420031500000d10f8011a280b5000030851704201004002880d041844482080c0700700100e04205103800d44040307008060a01c0381001408201c2408000041c00602608802000b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 904543902 1250 904542652 904542673
    0xa35030d150506161103154215040b0406170106030c1e0c240e1c05030702030403061505030d0207050a1a0d061401090e06150703022b02 60
    0x8a1482070618103138a21a02c0c000c8280010014411490500d0004003a2007500d40000c2d40c5075071680c811600100346031070303101c21140a428803102e0015200101d42000d204680a040e00422500065031124060a00070021010380440c01d410340e0302800c203010f0296a115a11100208200207621500c550031504030b0001600c140644a1907a01d804651503006011200c3c2c0d90106050801c0c0c12106d05200e10034040800003100c250381034076440c01040d064500800d0211001003210340c10f00e04070b482a0f01403000104084080a95954030ac102440c00541c0da0f80c900100300d0540c0a2548003d10b11410105c51840d0480110784210942e54160110b030184d0b4051a0202c0e80e4001e64401d180c0c000882c89418040f103600c1c05030300c45001042c5036001d480c08000e8441a41224015800780d0003080e40c0d013061112030b41c0e00103a43c43c001c0c1a51202d400090616a002803804e04a841c440801d03000c0008101c01094002e2290b54035000035851440100c018121000340300b4044001c4200050180700b5525 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 904545152 1250 904543902 904543909
    0x120b01210302060a0f0207170a0215061e0d0c0603050613020a090e0612100902150a02070504090c08010e07030308161b0c0b0d1a0a35030d1505 63
    0x404000360941c0c003d00c00c1e500d880400c3c40080a03605540b451054003080000003240100b040c03d050101c0c1d40480d00e5a80343c0d6850003e041c4070345003150444400307442041c1300b04c95488212a103900c40c880d4a905c120152000000b80c255000c00c0d50080c0030721020341c4000f07031190b01580080c0c410807003036038040702c03007000110036500320b100d51000c10b00404d03201a801c0c4035018002e940b0b107030300090103414100a00006030581e031402910408441000c2c2e1030340b40b128218188882e00f00e028204840346141010000c05019485424500482d4012642c40040b036082c0a0824183e80c028165130000308584000342c2040380e16020280001d4000c9000280410328030103051038450b0300d90000340e540e02204034107483c7d030700b00f0084018001c0d500c130b58090350042841d16541c0010300c4d0125841c1d01c005144c01c200c40700c045079154191000e0340710703003a010f40402801414400c1501c80d8620b2415000c58411020210250002c801003e41c10911000c21803050300450f65100000740701c00c40300304282c429901c07000c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 904546402 1250 904545152 904545209
    0x105090906040f0203031b0102040f08030703210b060708090f06031006141b070303030c0e0d02061c06080c01020709090c06080a02040b0706140f04170c07120b01 71
    0x8100359900c09800680414411000c00c980c0d14402003d80e403500780740c0074241410580011550703081d65800102000350040e00a1304a005052040185040c84501d4401400e403c2550030040314080600080c6549202150700081c0c0044004240640f100c08c14200070200c3d42014100d54010011030020142d42e140c85001c7d83d22840840c44040f85660424100311040d4119055012084030140301081c0880400580365003800240d030b006007000b80c65424000c0070381d141084004180322801120314a16200c6085070144c01d50142d40d115a03440414140104030510000c42200582c40c04a02203600c000205202c5010103007682211031036500d410f20801152042d250003040c0d042d1000e0704104803801820340c0741d840882580d0050030590349031400c00c016801490100c80d42583c3d901c0e22401813090083e481d07040011038041035001d00d01941d40090018980008402c00c04021a10302c51007035080202401401290075001500070303440c030f00b07880101401e00031381ca003038941c3d44d80d400036040c04d8042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 904547652 1250 904546402 904546411
    0xa14073c02031e03190c0b0109050c030f0c1603090515040509010e0903070c030c0e0106033615050a18030e0108040614130b060a12060b0301060509010902070308010509 74
    0x1d031602480320f6055040c1040c094483c9079960000f407151920103405070b0035903401904680c490b000e8090161421400c21601600320100951408050000140810090300c0d881240b0f2204454152074100080c6c0300703801000982512054030340011410103600c45c20400c200d440989a00c445256030a0040c04680540c2c000c2035044121341c0c0c01041314420f42e040541e000f940e504280d070302e003040a07252042140311a40068950741d0000320100620510503003a180180407501c0d0030014010740129200300000107070503894015030b1030b000c0101c2c40a480c99031200c20a50044010000c00300e00301500001d0b02c82155140e0007945040d00364a03414081c10076810895603d6540d807094101c100c401941c900c00d000e40103641081d40d403a9105165110704c9891400b81e4440c2c1c69a8200318030620f856900942c0040c0000d0046e03201d9001003000c90b069892f040c200580c0729202158484007030010074010140caa0119502c41e010a000050080056000300b0910380650345c0c4019503038132102400447c42e020368 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 904548902 1250 904547652 904547659
    0x910122d17030402040603050610051f020c01080604060803220b070c06180306181506050307181b1806050304020906100903061a0a050a0b0a14073c02 66
    0x611031071805611000540d03110384003c00000305d054403611800c1c070b0440226010707aa4000321000601c000d00e000341c40e2503900c5603010025915040709000007501c0701c07211708146040c0f00107800801c0d0785603030715089000580041d20441e07449081c0c0408000c2840d80003150244054041d03c004136420025100b04c4646a4010b10260401c500c1d140086070285140540d20012400a0702c020000941d280140e500007084281e0310850105941803040d80c1e010095404150700340382110402803514003007580000c030f80b0042c00721850002d401c400803001c2c003003800588182144039440500c1061704103001c82d1540e0003039400c00c84600e071141e134155454070003520065401050b040002c0c03010f280500c0d041c60300044038905001c1d4079a480e600d00e03003500c9858070411116904174403983c07280d0801c1ea403800010242181e080903004d1600b03100750054401c81d0040e800700401b180442d050b100204044a5001d0351040d44d402c03400e030705522034070540010100002c410450001e140c0c0440c0c4401e104206d007c2e41c008 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 904550152 1250 904548902 904548923
    0x1110d0e131a10020c0307060302040617010305070501030b03010207050607020f0601150e0f0f21151303050304051509100b3010050a140705070507050910122d 70
    0x10400c01103c40d6081e0090011846212a07071450ba84060040350020441603e0140e100e43c10004064090110312458070380c51484a03004001190000581c8800c0320301c2828000f6a070f2085c040480d01a10074040007804521030001030040d026070001d10018408040070070340c8c0960b62507004503092001089408000503004450954491809014800380a80e0080080f42e102c8044008101c6408030601c824100340b840c1d0700e0400c0009001d1208480c0074181c0848007500703103408a40d40c40420b800d00b001804024000c00000d040000821138110003d280301109240703441c01c62881035803070000c40c0c400307000700c3c0c1800d070307040e440e42440200c0724031340b40c1c0480c0c03030790300c905035a01c680c01c0c1404030300c4c42c2000c0904ca10352241e040765290b40314150003843c01041c0483c80c450400d507126010321001c1d000c5010004204128008620042096400d13510304841c5030b151501c51903d107407690a003640000c002c545003226100d04100900114090a091700d5880903080b41042e07004a4141030b07041005003000148 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 904551402 1250 904550152 904550201
    0x706140f0609060120250602060a0e01061a031f050102060a2c0319020309060315220b1009080a030e03011107031205150a060e01110d0e13 61
    0x2c2034069602880c10301d40625003c2d5000d05c0a40349551540e424100d9030450002c1d009100103044141c040e007940180e500038101c2c646000256035280007818030001a690340c2c0c0700500c0e40c00030340010300145a84001c080106c0c2668100402c25441580d220311884035070041000b03020414680142160f0058014000c41d944460300031000c1c000a4001c045c00009070408001401c3c80040703660351490b2000000c58441074400b003604908007808000c20195481030184c2149951520103c90340540c0510110f103107201d407407000c68052001c50601c802e1035074030f04904208039411507002c0311100707000721040c5200c1071103c04141e0b084401401800e019030040058180420f005040030542d054011b000059046192810b0764900d80084604a0002c2c802081e01c2e964088075004594100d0200e1075241e48502901c0c0c0003425080d0948a070305d05101080005807242e80c0142d4500c450b0b0302c200410b440410030407000c000c1401c002c2c2e4803060702c611040382c91560200707900d1240d0354501804882c5007174815030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 904552652 1250 904551402 904551409
    0x2015010302100201091209050a0f0b070f062c0105061203030a0c0e1314010828020315010905061c0519080c01060b1e0702010816030f060b0706140f06 66
    0x520310b404040d0b64940c541034000501074a00d075112002c0607075540d08141e003402c0c2001103951003907000b43c9a00c031410400b0301200004c0700489810f5540000401d0b5901c8140c50503a0150090b051280d0030001d000d4080a0407603100c12428150050010080155607152403c0140d0810390b01442040d6a005000180308003100d944064a490f02e90b0600c2984010114006880d4402c202e111403003c9880303c065803013004120780020301608005009d0140001e0b0000f207006d5203001e080c82c000111603900004004d64809200b5075005216001c00802c1f42c5d80c4a080700e42c0038042c03d40311079010f800403244510000b480a0445079440d41d01c50050441d802102d41c3d9500143d030a020160765105080100046051b004d116510080986802c8136464041032024100000f4a503600080788500420074040144c1c0d10612603603001510307400b81d241c02021180d048004040d40c95201111a20345000440c0d980301034005004a14824030301407140c2980340c440340071410800c0d60f82851242501d0045004c616 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 904553902 1250 904552652 904552669
    0x90503010e0601090b13021b06070f050a050a090e0a0b030c0d030c0f021c1104111606050a0e0a0c051504150507031701030f05060603030309030904020f09040207032015010302 77
    0x5c8024902449a580410740718101c1e8401254942c8030b00001e1540310401d0001c0c880264804040e0400792041d685c50071000c2c000d4803030744407030340704018000803200f0070140210801005400360001d01a458607000415030b0082132403801c02846807245a0b52040d40d0703e0f0449079010015415600d101c0011560f9450b400005d0790410200e82c814410001048840c01040800040e9800b030481c038003001a181d018001190f032603113112102d0a504100061100c0112000c0002c40e0350700000008007907980e1229100100a078154450a50140c1240d000334400c0035004c1c601903410488005000048800c04280d0502ca0352241110030720080780040c14103070080c1c01400000c0e0290800340201340c01841c2514441400f600120707081208131500e1014010100305c0181d10036000d400070b501d1070400c0085140e5070b00610000070710681e00024a004010240d03000d4a125000c080c0040d511100a468054071007110038071b8135240e43d012441c8000e5074070000110924000c0c141d084c846520f900356000d208829 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 904555152 1250 904553902 904553921
    0x3020d021b060f0d0f05041b08032502040605151803061501050703090e24031501140a0509102c240a03060b01030f05091903090b030f0601090503010e060109 69
    0x9551080401c10301c080602602d4811442a07541c65041c2eaa801c80e0442490307100d4110340301c0341e4003d200161500460801d0b217a40bd08210440e404600d03200c3c4001406450070741c000700c0c1c004c00d0718140840c0301d1200310050401100080154650511110141544c1e60002c80726003524520490381d001072940030f94020003442e400703032070414211901c540c0002003101040d900d41100c85002580c050040c00041915400342c40124045c02c000800420030b03100003401801402121181400b000340d80303680d0700300006c00804000d0505082d03450421210003580b41248500450010022902a00c6c8004484c000d206c0e00e0158a80e80c03036039100c0382003a10700c500e07400424601203e20221100901c0d41e8281c1d911005620400011442c44102e0700010150781400c02410006424201031027821003002c28130b41803406074031068011507041c60504030b03201081d0780d10406544c0400010f101941c40c0100c40f45100b04020f032102d002e60343d0f030b503403c1c182210780d09134060000e03070001001444000140d80249006 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 904556402 1250 904555152 904555177
    0xc080606090603221110020d09140a12050c0f0a0810020a0903081b010f020429090a140337032307060501050d020d08220303020d021b060f 61
    0x30081d110102840481c0d2803442620008031070145c00c602c61400002d0048642034510140c40c121803480b00280611250b8060441070819009400725a5115001c403400200841e107500c51a1a082d07081c10303911042c004403064007600815001c4485420425030107411642100020004500c604151800a400c49103d80b001c0001d41070703000002c00c041c5000740203c6400440c401c01e0f0184055506070840f910b03a0340c41511707030340103000030005840021414400c20718200750114910a4680740e01f0b1040c480c0307801341a440310100b80080303540f0041e55400c0720840825030403550580c1e000d1200404028142440c9001d07040400c034481d603d00000031b600044240f21342800c40c98000c0c1000c01034451030000006410f070400c0416443c0622405006240c01410b09880380403c80505801080074002c900001803c508000905101084507000848a1b9022210480c01e1701d60303203c0ca0001d444100d080c00040c018480d100c14265001c29507140f07283c1c1031b10300030400d91602c0b0400220b10326035041051140807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 904557652 1250 904556402 904556431
    0xb01091a070c0b07050610050411120a090215120108012a0e03010e010f360813092a0807300204031202060919140d120c080606090603 59
    0x100070030f2680c080c0080e940303d02c024000034074005091028010031548010701c25418100c1c18403c0002c6007003103428540f07000321081d0503559075504200144c80c0c1c41200a41140702c1c0e034803410840c2e00240c054070807200c142c5083c10f00360340d9611308682662403a5191f01c2c4c60714401002e043d000c810710709448550807003d0400b100d00e45442400642198004090700e403499444811080d000400d501c0780796200801034081070341184524540c075003050f00f50b041e10303004600c042040405100c0b07480246c1d80324502450300ea211054070317520102d01401c03001d42901e414050481211038851252041ca42072a01d0654410751540d454030350444100c17a2200c5406024401c0003588241e26040901c1c001420100c90405a0b44600c1d51a01d6081c0305104015001190030034818000c13025004078a1003120860780c440e080f255a2503040541034455040c024540d14804c120952544542200c421071000c21001d000b0400c80c242034500f5104a541105c5c86c0c0d0b07000700c040040c20283e01c0c210018580101001c1c50f55030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 904558902 1250 904557652 904557659
    0x60e0423010606300c0302090a05150d0509030c0d05180105030f04030e04090b100e0709150c03050c030d0609050c09060301030f060b15130b1216052203060b01091a070c 74
    0x1000c6420078a1744200281e00010540214181039401c50024a001d440400c0b481005003101c4034035014610341d041c00107460b0740200319800000c0083d645400405403c0c1c0c0c45642800078040d0640d484840d040c0805500c60300321b19030740d60141d01501d1140794004545000b580d01c942d0b04503143e06410810f10f5015a9400103100810040c41d1141d2040703503074181d0500c0681c20300b84200b004440040c00003040003039094040c17150110840040c82850b121341441815a0703040e1034155858040d100610102c0c4c4004544844144c1c0682c000324200c0e560010104105d844140c038022482c490541a550805820401040050300601d00c900c01c5502906000a80d6802d03500026a80b105101010120b41000328190120100070031040004080d0180d0b154544130a403a0327842024180141800103020304072000806090084084a4089a8908034042e43c84c01d400c00c0b0401c1e40075140003d8540600c0c00802c84020b5005000b50360a4449041d114006070b0041600410541e0100a0842d1890000340000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 904560152 1250 904558902 904558997
    0x3090809040e24090c040b010c06090c0e04060f0b10050f130f030503071a390d020705010605060a02070e0c0f032806061b06060e0423010606 62
    0x442d0f140b011002d0300354600705145040c2c40c1c25042c0b1540c1c0d00c52072500940805036a0025480030400e540904042401600790410050002d815801400c040341c005040004008066201528481114104100180c181401d0102c0324070150100e00104000300030f000403600c080405003000003501d132521084551904c03146d00c0c85c0d500c190b2045890303501c007241440030130117844613203e001100101403041324075040c0100710f510401ca003003030140406030b0b91b8444a281d0032101c40c00b84045180501c1c075a555080013840c4020b5001c131744152055440e000011480345421002c5941004480d40242055414034601c007080b000c01920b10700d07080f4000c201e4280710782004030195110358465605140ca00120460a40301c03c03001151a24240d2300d401401e002c0715030400030707000ea07051061480e00310f4064070745403500c020181500030480002e110400c1204200c5400d01c0540c1c2c40007a42d00c4c1e4000400c500b141e02c2d081c1c07110390160300042554006e128528203200d84d03c0039180034a0241034056178010201300b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 904561402 1250 904560152 904560193
    0xa020a06050c0601090203091506041b0e180915100801140f0c0c1002030601030b090c0333010c020127030b10050d0f03030912051903090809040e 64
    0x2021071404241c0d410240400d101c21401406211025403844c5444400b00313803200e410003040c1c1c901c550104041000c0d0382f1a58807005405c00301014000001443c0d61010b058020215000fa06c5a080c481001050082c0348175240d019003a100c0c010a01c3e9100e0380404032007194002c001400500d05031400040f00c0b00240121202050300001910160038514015044c90000902d000c01241042040003c2e904c0d00095400300c85212039030040c0c0700e840351001207004d09450900190701006140078080c0342880307880110300480314002849600741d0b044142400d0460484805c102d0b4104d032090415042d4010030b03c00261520500d080ca5a1800c03240f044194035005802d00c820b4004142024001c0143c4900600d0b00b1602d40103130074520a02d040d0000f010950301c12801000003d000c03102504050198200480c00c40d48801c0700c0040c42002c100003491500400c8540d0003d40001150000e010f02901c40e451000b03030032450041c81d1980c26010b0201410b031180084a40d4811042c1c4100511040f088 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 904562652 1250 904561402 904561409
    0x160b18070608150103020c031602220209100305010e0711160e0615180415030c03080304060b041505270a09050115242102040914011a0c0a020a 63
    0x4a100b918244620314654030f40085401c141450710410500c1100c9400100307036200b9040c0600310399030501c8a440444da00b086052b41510204983c600000310b00d040a8002c1e0540301d0080e0b404440001c0c0c0d0b1101102519020302c200c8990b030034540c0c08540560300c5520607044082203d812583c0901d040300b07107000c1c81c014580c003050102160784240901c0b4074010300c0384040003c420700200e0602c80c20400d001c0091490102061180d546c1303000a44c81c0d01d500c245110700640e0000b0300b4841c201e030349003803d42066100b00c40450383c051508125000300d10309482980c5c0c01c0c0c1483c1400340401ca0803c42442004098030b07840004c444581c5865282c1003400c42440c031312800c5000300203c0e45103c645005425500701e812840c15007840b40b10300b406030913800e02801c0021001a04005c020744d0701c4210540706814800381601803003c040d0120100100103800030300481d2801c8000f0024070b03070001200c10700e1b42c401b03000715488429203540740c08611510001500c05106150150f4003514819070000320b0b600c009a2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 904563902 1250 904562652 904562657
    0x20a1203141f230a12051509031b0708010609140c040f03141c090602100b09220501020307030504021e0d020f040e030c0615011e05031e0405010e0111160b180706 71
    0x48a02c003000411f21000c40096010701101c101818901e0f1040d8a9000b0b100ea80f000c005580707540d600001c20200300e9000245010002082074039200c40e1080c02a203c0d00c1840010503003030b2030210b5480002da204440031905d007110402e09940c21590303070128034500600640b60611070441c0c5403034008003403640036504840648901d18828a0104082d051041c904a11626a880d0003d20700705500e40c1156254444010000c1c03d0010010400081c40941c1d83c000140c403641c03004c800c2014481c0c0580c0302a004a000f200c1c800131101800740300c041d01071154000c640d000403219900b400142807038481d6030f280140080006c00d2400c030181480b4615082101c41310440d41c80103090000007c1025031045180c4400e04c0e0900c1d0b00d40217080b402c941c1c421580c00c200200803000000428040740300711000e440700c58100700f0130014102400d1440c06416040b0089103154605055105240d81d807004461101c0071040c0d007200703604026168000714040081c40500307007540a624106c821182800035001a21700c64 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 904565152 1250 904563902 904563929
    0xc01020d05040b0c180904050102070b070c1a090d0c020a08030a020a020406171911151e13050d0203010608010908070308010602061b0a020a1203141f230a 68
    0x10304203050f00c00c1d40a015180920001c1004802d241c3c034040c0d200c806000280ca0111080c5c540d40380090080c8242180503181101c800d003407020081e800403601007558080c0385012443c29034040c0300580d56505844003880d076802488020580381c041c0c1018001c0900083c8103200c40e03540c0e29911400c5034041182c840040e00440b20540451403d889403002506201c2e130710b034240da0b0b121200503a0300c050824804c0c0a44402035220003c0001d18050102a0240500b9404620601011101c0c01c1d81003801c5184682000c07485d100c1080040e8420380303c01004040350000e10b207107080213000e103203507540300c09917010354a90300c2c00300d07105030b090054007038041c030805c00075580710070030b05000741040c0042c0c01c10801c5410020620007048600c0007400304103000c1c0d405071591340303030b43daa803e0746011a0a03c008225001140f81c04000311341550040c0d0409280f90b00a25803503490300545d001c40f407900d6010b2452181854411700502c07801c0780e240d10404d0b60321995540c0c80e083c0900015178000340b5038068520103d00e0f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 904566402 1250 904565152 904565161
    0x302130f050f120f01060b0d0c08060a05041503020a031113020702030303070545040504020d240204090b0a050102010e0a1403070821100b09150c01020d05 68
    0x11040000800310500c51040040c14000002c202c03500c8104840d210390005507503480d401c1e80600210040c00b0180008000880d03462107960140e4006150401001e40380040c0f0001040c0150300c0e040c400d13207004122000c41c0b42000c00f040300808d8241d101210701e0800c09808030058036040c401401860142060701c100b54040420040042c6400e6150443c050052050a0068030008107998121003a0700b0620b40b110a0a04681c0d90100413036100b000b080441441d10041306049030480c8a0b52020000340844000c10724180003d4890580d8001e4000c2d0107210046d02140e0202046510b100301c440400c04090402c400c005e05907045030300551400c2da40e0b07032074a0030b951801c184110001d020030f000900520701c403801d0700d81c3c0314000c00b28080d000c030351040035200d401e601c18000ca45c0442d510020701a1903a920018058020420b40c0c0085d10065120010070040c4140084100403509a80030051921194030240144c03d030070402040ca100106010110511000380040e06d8003404181000409240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 904567652 1250 904566402 904566427
    0x3141002030112050c2407060e0d03140702010908090409030528021b01080f0a2009040c05040308040603150306090f0203070609051305061516110108160c05070306020301060302 78
    0x2441ea1914424203200941c4070b101081b03418840702030007084a496449070550b0030804081c1c1a011210f103114010040c2c11140305800d075219840d00000784200306416a0348040c240d080700c82880d0003411480c404d0000400e185050703040f1100a5100e449c1550601000201c5621003c180c2500c0501c0b0700200440d00c56000d40c100034040c4416141e0f00300100120003a40040c01000001e000c1c845504892000200444401e400c1660030040b45d1100e2612603281c2001c1a00d035420418500d0300c40c50130240104035480c07045096409507504a803e0301e01d070518012042d001019956007045031841d2840000003c12554410b41c00e407680121003c4e0f808900038070405042c2a226005082404000f14052100e500e400000918152800301d00040c56100d1070001a0074440b12902d20b0145c000c00501d1552502d000e610030160701c3d02c1100c00c0d095140710240155611202110803150b01030f5051890007407544110805c0642502490590384400c0e02ca03100c4a040e40d20036008100441d8000074092000c81 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 904568902 1250 904567652 904567663
    0xb09030a02010509120301060c03142b06081231060806100f030e01111803190201050909070e040f05011716120305120a0501060f050903070314100203011205 69
    0x28448005085c071202c3e240580c00f03090206005040401c06082100c034100345c000c2c2c0d90309540c0d031041500300c1d1b120180b03000720030000780e8500c1d01c840b000d00400a0a0360040903900030601503540880c0030384510080d042c800030868100303c640303056920652822165035401c000c004120000c510506031201c038107294020b0000c0b0303c050141c6005080c150050701800da404002c90142c50b45c1d43c5804103102000384202d40c0500b03d91481e540c10004001004065a88202c4420140d0401601a100c0b8162003120b00d02068040d558064045042005560740324070f81403000035403006c003d040050013290702e0301c040380480f0242d03551064681e070381d00010304c15141e2401c080c40c100d6100b40300400c0750010b0040014440c3d45c0612460446030303100ea48406c10540100c0613074252140f000084421850080c520380d001d44000c0c802c44020031101416074034004c0c440d43c00ca030001d22014004080313075880c681e103400e803490000b4642d81190040c1f4030701e0b80b045d06086c0011070080c00428102010813199040075421321 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 904570152 1250 904568902 904568911
    0x203041208060d06050702012406030c080f062716081003051b061c05010306060504020711010f0e0d050724020d080702010204030807050d11070f170a0b09030a020105 73
    0x402201c0800c611070f6a1920700c03070100c0758803000c04900d5440307038041a805007051211404c070408007052422090f030381c4580f50a0440e4035540d0107212821100800f41d4403944180c3e840e03c10082c9500015086041005402c088100780308528002249104600041d5032401c1d1401039041400302000c0603229840f51109800c100910414507003070386036076941a540d400712400c0b5405640320b1400c07131999a64003010765461182c41e949820045d50801c1c0c4600c010a400d010803944c40e803920b00c1c0030580c1e05142c400d46144079030020029020410031001568000d078005048400c01c00c8003101740718203888480c0c0000741d4910400080000c10f0500d0b0301075141c0342d01c048c4400c504481710001ca14013a03500240094504820782040e814a13155840128068801c90300060b286180010720001081000900c01801441d560780300c003121480000303d151038868512400b070003010340140a0100901e20424052081020811983c95400c19903c3c81c20302d48044079000c1c442d41000c599020100e0702030180c00d510 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 904571402 1250 904570152 904570157
    0x5011a04300b091c021504140316150908121009150f05120d0f05120412080718090b04060e010602010b0909010606080f1e1006020712050606121e0102030412 69
    0x40d40090703c0083d030b106c071044580c003030f00802c000100d000d02031101c5100c100c843d0014181d95039080ba0314980000c1e000c2800301201e14582907141d0000d0030f13050348500000e05501258261070010705d1400c68800c090050407c403901030185c1000108007881c1d104500c1942e016952240d200e40c50490380b080088100d13401140645080b10864004500c003040940c503621090034496210501d50200f214140122402d08507034014900c24001400f02001060022500704c2e600d64841c0e9079510802c0361030b2500321301c120f0356846441c80c00340106102a040941e13609005400042c4203640c400000212410030703030146000d40d6440001e0801400c051044e6984a082080280702003031074180000d18613a0020640c60180b0080c20116016540080400e00d1072040490740000c41c2c1045181039105414512a800140c4640e00000990703488542c0d95126a6070010060000c40c4c1e501c02c2803125007507180601060502a1404400a0b1801c0380700e914100d01004000588902d001c0c6803422428102c089600207 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 904572652 1250 904571402 904571443
    0x90d05160b03060d1e1b3b0702191208010608090a0807030e030a051c1713020105070209040f020a05040b0d0303090224090405011a04300b09 62
    0x4a42c0c40d18804201156400440302d40000c00d00d0b001070070509a540380040240b074442041c07840c2c0340c21446d00a0140c480c0c0045030311500c0103d01e5244c0190700d50402000c800c40c440e0800400c80441441140d07070020a41c01a14019298503060400d031049061003140c0300040d05c2200f6010584c003560182c094034803810500710b5400d1030b00c48a07a5841c1c2e07002d4000c0194600280354001c1510403d200ca10620000d82129110030a40c90129180d00440028620440e0300c0c402c0c01000500c2000040c04c0405062214040c944403003c07250000418242d090341405010007c1d9001a255069111f1045010701c0c0400440fa0701c0b8410802c60448581c00144103605001d82051555101380403038041c60392600380020600c1c1188040b40490b4400b140905100c12840c440d03c070f07818500300c01000300d00c03c03c40d001c02880c0e80b0746119801140069000810405060009008400240036002a08000703405224402007103120300c43d101400000303003114070008070310a11002d0542001881203094002d02e880d034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 904573902 1250 904572652 904572661
    0x804050f0606180402010315080a020f09130f02060417030a02010e01021314130204060302070b090102043506011710050702030d020f09181f05091b090d05160b03 71
    0xc0383d40d0030403069040d1444140d00400c0c1160301a0340106070040400004c00151a134804c541c41d202d4241d900240d00030154501d181c032072031502d580b005218001443c0100140c0c4025142c5540c2c0c0000410201d07080042004040790214940025855003014500219174032000144000e0a5038565081020242e0040c8200c1100d035002c5d0380c1c000d05540f10306c0304588003110f034540054600c9034800e01e401d010900c000340200d12682e00d40c009202e51070160071452003e8541408039402c030710a03849003500350340010855520011041c800b2031445c00601900c2c091552000c01d505062080c04c0e1702400000109059901c40c808090081c4c1c8800640010101301e58500004080c0d12440303104c0303507080010390015161080502d5581a12440070002e000300d011741a20001c00c84401c0c205691194050a01411035810490703251107420a40b00003810700c0301d403030702d4506403807142a41c0c0c0105840001c00074801d8040f0341d101d0070300c46808140548014500c07800c1072002102c0200c011303007000100d48010000c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 904575152 1250 904573902 904573909
    0xc0b030c07030302220306020d06060e0306180f0d020606090901141504060b0c01141303020d210c0c03141305120c09010605030121030c0b0a1b0804050f0606 69
    0x76550780707806080250392943c04400b206040503502500011242d200308001c414000710350302810b50020454410080540c5843c07003500d4074100c2021f9203a16602410008282610001e02291001550070403120030744410090b5038140607400742603600690101003001010320b00405042d4105c2d4000000304200b00001c000600c14600c001c0070604003c41d1304482c0e02d0140c80e03541c0b28100a0600748a00c6465020312615540a03065a0b0b000307104c00070255011419a08503000b444225640c59001004d200c2c4402e6410b23107030030099183c90740a0703015814044110707131014042c0e01356070300d80d40e40c4082e141b01c0d140c9800b8144c6000102c02c02001c80701480642e1542100610840c203481d412581502c20200b072244061500e0b9030902c0d6560003506d4000000381540d00500654180d03202090302c900282d10300020014013005d24500a00010804500c58000c51010202950407214030781c004240701d0301002511802c5036000205800140e0040c0401c001d03c0340512040701c40c0310b41607020349020706258001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 904576402 1250 904575152 904575157
    0x290906010309080a0e0105041a0409050c040503071215020a050d0f0506030a02120304080d0908010c0e090a020903070801020415030f06151214070f030e0c22060905130c0b030c 77
    0x140d03410300c181d17810990202d038085c0040e1402014841c1c030280404809500c4010a40c003c0d100c0e48002504007404240340c10f00d0344090720183c03407001c0c00401a09280c81c40740600d00003000c405441c43d15141c4a0b100341c6c4071280c00101002c804070b489050355400962503038400c60310000c055015061500007030003000d035000309440ca021901141c8071079802c44c1c1d501469041d48510380c0142554450058140441908480a10225620320000700301000e40810184d440c154102c070540c0c0e0100004002504466080d4042c2c50460b0010302280c00c03c58079130b0605400c83c0d2143d08103120f01610b4520b681030240c1c0c540218034035103800040030b0140c10f01e003103500400507842c0004c007000c3c4808070943c884980d031a513104941d1143c1e4070008030110704004a01410900c0c00c0d0100307400190420305030549084e0b0002d80c0306100d01002c0c1c00740004000c200482040d841500c103e0412041c0c5030310300096030784401d029a9000341400354503068031080314680301407010415840700380c40075824001c00c45e03d415000d05 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 904577652 1250 904576402 904576417
    0x3091605061e1611030f060f0105090a1404061a040e101d01091a0901050601020c01200a081305030708060609060a03050a12020f010204080304090f29090601030908 72
    0x40840c03940107290b40303540381401415929650b0342811a03c0006028501d1004900f001040d801d03600006004025503440d494100c0d810b044804001004122900340303540f0703455100c001c030400040c403100801c1c12200e02e910103035002c2e0b5500e40c603080000c8050401c01c991900c010b00480c0c00f0000301e0034400072a503c4507800003854002c00d80c0c0714041b2607502c98500314614080304800081144a001385007107040d1544041c08594005482000031741a0075051260340d00400c070503001041c29040303500044603040d080b115001d40d0004401e200006c0c01408118a803003691280391324580b500d000200b1034000403040d5103c544243d20255040018041c04240142c10003002c1d0303015070103650f0303d10214444003010b6000800ea481100740820a0051641d15030442c021250300b070358508060319200d41d00341c1c025809440c2e4240c0040008000052079680548181050080c01082031040e1403030a440038805070042c0d000c8854042d40810091900410440d48580f09007000c12030207842d510340c00900e008510 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 904578902 1250 904577652 904577677
    0x4121d010e06130f030b091506221b030603120509090a2007081b0c1003050a270b010501211802091003020306060d0b0c031005060d020309160506 64
    0x180b90f0500c030070b10300180b40a001c89640380c0d61019620310307000100f28070441d0500b0640c0030741115005891041400940a81030080116811481442c0c8050f050000e401740c610303585030748086410403054600c89042c505080d0752000250303d403a40c2025000c0c5901410000200031042005e2501646d549003615040340d050000001c40004030100f07101005032074110b80000110100340d800403c01e50f01c0042200c036011981020481d0301c2124044da40b40c0042c211180c0c0580410043c440c124030a40c01076030320000548010a140903a1802148107802504a00103c400c1c088108818000c000e045640100028a0100300d103840c0c3d00c01d0b070818a40180b404c640c1791031701ca240010710f040107041c081c040581c0043c2400c20b9828500c1c20744d5012a55071004a0003405010b000848031326040040c117146940120444000360744000b42c10031a0b03800103089045114148002043c04e0f100c8101400020726418030042ea24201516504c0c58400c0c6c0000102843d10b20030014800d070b4403658141c41106202e003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 904580152 1250 904578902 904578907
    0xa0308030c0c010e1b040e0d02060c0705190f0c0b0306130c1e0504090b0d111009080a0c23031507050403020d05030409230417070b04121d010e06 64
    0x24041c103002d0301c01141490030503c1032001d164010a10ba021150b120701c17040360108211072002810300d44650510a40c8405a00b10b5800103480000f0700c0300414035140304100b5103c2e00012403200245c2d07561180010b0710081100c0303980404100b54031000c1d4000e45481e0342e54901350b20f85840096081c031001d09c0c4088070592039050190000d8080c50111465030720340c030009442c0030041c0c00c0003401c0f500988250b040103400e0170304002060a0680c83c80c50001d811210000d680c2c600b1205014034000c58804041c108850940700040c0403a050140418040c8154000042c0030702e01100402146280c50140090b40b6180a012507550f400003070b200303615106500c0090341541c8440301a5018000c540c006034200741c17850603000070004048000d20907030381065001c01c010303240c021410011100b0707a240a840030b0344d402c0c085408140b02800c60460060340c10340041c84c240003035403202c003a080141c400f00ca1540200455001240e08001c0b2003101d4440341c3d41140a070b0201400081c0300c03410b212002805510f00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 904581402 1250 904580152 904580167
    0x10825090509011a0a060512131a1603060503031930050f0f040b06270a060803031006050d0609090b1e0402130b1f0c020a050a0308030c 60
    0x229954401016019001c001c140b4010002d80e000e0a101d02c4e0829141103e0340c641c1d4054900503d4540544449984160810f50307100c18005110b42d014104814041c4001051000204c0c510083c0e40203000c540f007a10034506000d0126868240a041681c051604081040c440c0e034030b001040d110000500d036002c0780c01400c005000d8424030003c24001e50217021890f8102d4403041c20b0200442d1449100303e04000581c1c5044034507100e03410940b00c9116803002c400c045404603032900304054020b0802030140e140042113000f040307040c01c40c0400124845189204000e00c0791014403910009009600195203140740c0f8000004025207907004550078000045a8408000a55800b000c0600034007001000410150300f807440c46413008491015441c0c0c03030441d107030701906107600c01c040c010790340900401303c1d41210b40c224202524a400d62190489a4038010041080340c00380b0503510841203851310502030040b03005200441580c1e030026030003020f80c45810000100c21008503544155400034681d05d4042 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 904582652 1250 904581402 904581463
    0xb0619090f1401140f0a0c051501030f050c030604021f02011b090e160c03081e01090e0f01051005013b04050703090f0605151f170108 59
    0x25641021103405481d05010600110039090009602d000f600c42c004004c2504030b074a49680308644000c03a41003018046101205e024031000b110172403042d0207503840d85920030704003411000260b105464490418556505104042c031a40c0c90781c06055001c0c0c03e1519054000c074100101040305403800048110f11380040910079848101d4000084206844425840c2c50081c01c03641c25010b0f800b881040d83c4003180108c5000741e0f000000d801c094490b00314481564034180c401100081040b5408002c40e50441e00e05064241c0b8280640402200000c14401000f200d600d04051030020207442d030b15140600a0792580c1001440c1241c0302440c146450402d10408407071100010501401a054000c00140706860070a844155811042e6010032440d542c40320308906032611508041c012654034064140031409603004039a0100c10180801c80c82c50032030340842d183c00800084a01d41e0b654410501e070b0b129a2101032007030300e82c4083c0c202c04500e5040501840d14ac03140c0c00c1603c650060651032a194608 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 904583902 1250 904582652 904582667
    0x5060313050312071e0210150902131701020a1b080f070506160e061815040602280203071809020607061d120a081012030507060608010b0619 62
    0x59026080d01e03240e03e666000c0640302c0f0001d48400c0c020881c40720708544228100442da104000b600e030b00030494180e540201100800c1e2001c940003410780744070b0010500b030310780d400244105200c260403c0c10755880c0428071601048118400790071a401000320076445a40300200d1707400030040200c440c641c40c0c021f10740105144100c0105e000303078413008284e0200340140490740d00e2140c10180c0198814410b010000c43e010310b0210359035a4090001d1059070030004155503c0320140e10302070501d241000003480c0c440540d0700142d10190041c4d1003030300d2006180600002d49260098480061600b49034070ba80000c0c1c850905000b00c001e6001e2400c81101801c2d510b0700034030301c1c1940203017401d83d4640640c2400c00c05000d11a20380c0410024410710818410381c000b0f04065840d2101c00383c02c1c10990005001ca031500406081100e21069440000c101101d1082488041c103100e5110380e1741e03910b207070301e80842030341c1c05603202070344d2a4541010300d445611680100c551056003c8001c2c0500c001d030410503106003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 904585152 1250 904583902 904583941
    0x30d1806110a060c08090c0103020306061c06051309170a02071512140117150601180509070201060e130305090f2d190503122b0f0e0d0207050603 64
    0x560910141d04403654008001d1070243c40080c6c15568605103040065041e40700a481d89600644100003103200ca11445442e9030395041c0c3c0c888040b0b005581c5600017000f0b14005140c01c0001e0b0340d140250020054034114201c0124003003ca224140a900040652110b0319480780101d2003031241c51810701d407442000951403480d41e41d54200316400089618900c10b8409001d00e554a0290b404c034001d0103400012102181118601e50241c07985d14500111880b007420f00d292181e492505502054aa41307014403244503660075170000841c146403131346030405084068200c07030141082201d9040425071180c201c1c3d440d120309444220011300c00b0000b0030348011005001e411022042c1e10310402052000d2103441040c14111034207a921405101c5a54000c4c0c41c61103616032541c001000c01403e111400c0c00380000084c00c03c12014215010b486608810b602c0c240c030031405a0380c410b140340c00b098003445000740c00000300e80185a028207100002e951604640607040c441d00000c40002c404c44070005001000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 904586402 1250 904585152 904585163
    0xb09031905040e07082517150a12080a032a0905030c120307170c0d02240f0f04110409080430030516140c030d1806110a 53
    0x490354001000704590810700410b08485070620106000901c10b815440c052031b5074a801403c03920101065031000d01e0b0394811181031007894101c0d0384080c1c000309040d9102d0300f11503c280b02005900401c2000c241c4c0b1582141f001a0014103103080031610080580300c7c0e5840c0c03400c0000c0c2c401c2402d14103560200c00f607003442c800451b9020b044204243d004900b007048034816000c8030405080c031010040e0142c43c0180c0c14800d0b0388180200800f24a00c103803501e03207452012804900d4105425100b81c1811501c542400c00340c1e1260901c0d0302400e80c110b150f84000e110329102d89007542480003042003030101c05408412001008000719050103000a00c0200c4410000c100300148442440c200109410500c620f000030492050038440008a400702c04219041d50881c144c510031a964040c0c4035500040c80c00004000d08843d84000951840d0b152114481d146c0002c10588184008252900340448894000c0041d813680c2076100c20440126001130300d0103400c0c00c2400300d0300704003441d2a1000e0218050072 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 904587652 1250 904586402 904586437
    0x120b150d1203050c310906030f1e0b130311010203190608070803090d0317040c090e0c01081909120c1509020f0108130510021b070509040b0903 63
    0x801c84180c1054a852080c1d0b20107001e160781d41a510040c60090b0401c1c074021101c0021030404003001d8110724076070051400442d0350f10a07202c4005604440082c0c008031003007007881c1a004184000d0310200c40e6440b41c01c10070300407001e1641d03640410f0444090002d0050b0030103108010101401680d02841c0b90725808005c40d16403400880020403806a01d200fa0500303071500310701140041c408600c0e2303410744442100952400c4024028081d080c0d654110a43c1044a00410600301d0411a04d1080c001c1c1d000e1558010fa280c24117201d40d040b02c041c5c18626000303a01a180701030859801220301c5500c41d10f01c58041743e040200e01c0710b50300508180c10b002443c124000e6040859241c001072915080740c01002203100d02002c5803204c20440e052143c0280d801f1501081c400501d601c1850004d41c05606c03c030300607000200c0750780d80e203242c40e08180c01c4954640e0049403042c1c04000d92001c1da08112030b030100614010386400041800800083e03c060300100045001407121301007003013250f00d2005031800b0440c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 904588902 1250 904587652 904587679
    0x5010b120106150801030c150203041e2c06040f0f050a24082d03070b04150b1c0f0f0b0f070302091e0102010e0d170c04120b15 56
    0x5008103060b001d0203019a10510080720310718413034180039042c0d030fa115118825440c24040303080c090740c3e41c4242c4181184010000440d034491021001c0c006008481c5000f401c0d941401d00c1d213072038990305a10290b0220303031502d001000c0d58201c021032500010143d400280c041c0b2503c00500c007a0107102c850b8140780f824441030015554031a40824a11000e00c4102d40e6261040705007200d16003114410380a481c2d001d00c0d820180c0e516101d000d904030400e038a5812080002d01c51500303003150895402950308100340300411040c48400182c41c01041a0803100300480c102800004050f00250190812a0120030343c00c48104a80c40782080003581e00502c00560028071890800c841c0c0004072001101d140070400800e4a1034000e000f0b81d13050150041484900340a00c0e0145611010030721070450440d134803001c2d0440132100a0124003007a0302d05903240e401b9000001024000034601400318829801d0800c0700304103942c201b510b00c0060507840010b01e43d0a403600c100c103070103080c1c001d5445a401140350307c00e02c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 904590152 1250 904588902 904588939
    0xc0201021e03040c080c0321120712060f0803070b06060705161d06010f12090b01121a01060903031101060803030c190903051f021b0c0111030310090905010b 69
    0x250300c10fa10900200011a840b008280d48808000d621030f50194400c21002c094119070a0605202c040d01081d403d060040842054003040402d032020350114424014200860003c1c0c052000035041440d0b03030644140c982a0020b560340302da0b0304080d10b1002c480c8040f4265668034800ca0b02070581210481d0400054002c00121121007403003a81a051600c1c4034a0304140c0c3d221a0007481020141c503080d4815003140381c191802c1544220a031002036417503190030700150940f84e440b40a00107040325150641c44c60318154040b0318846084c41c01c503c00348801040a141e00c294502d00340c9506203041c4044549030201640940456040740c851800040300b0000702a410300041c0c1154022100a07017000c02c421507054130640306a020152043d00449030702c040300034808001c0d03124400107050040c42c2c9550b42c150b80001c6c400ba015656025081502484a0356030300012440b0300c0d44200c0051890341c10b1807122a802032080d0712401d6000c80e16818800c091140030752242c1000c4002901c5122002050981c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 904591402 1250 904590152 904590157
    0x50f0c04140616081c18030f030e0f010506030f010e101e02070f020109050607111e04060e0604050f0f0a090c05040203040606240e060903010b12010903080106030c0507060c0201021e 80
    0x40e220117018074020000391440c0f40117807a038807241440d40240e01c0b5a2034a0854001910340340000038191600442c15040a04201c1a081040c0d51000040c0c281801c004040c00d010602c100d049981e0f042c1100040100d001181c11840086000390015080e07081510810610342100303100d41d4002e1006c58184103004060814081c490b10036030f10900895100e03c02c100e408c0c014040054101c509124801481d81411310360b00c1d0102c0810f40601000314501030000e0240d904603040303442c1c03251000050042038103190203150781002c8081e4400c0c00b2460510040e00000500500d0b0104540d01c42200400380150408200b01a21024005554a28040c00c101003d401544184101d0001ca8132440000b4182a0346030504007030300c1d98030071070080800c40410506402450006505542e5904404d2107942c4007110540c900b140e10002040c1880c2d54280500554416400b040915051005480340b0550000840e0301d4107a00020009c4c032201028400c9009005050108030103400685080786052071034000b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 904592652 1250 904591402 904591417
    0x209010f0603062106051b0703021045171c0203070c14191a090a030c08031f060309020931030c0f0305040306050f0c0414061608 57
    0xb018404543c0d2014201c05021400c0d07001c074607034142503c0c1c644c00a413068101d40d4002a071001d0b02e803900e650b2a44955003650289800f2000b44e03206424684201105001d005e43d1300d5140d202c210307028000307065164615140e05c5003043d94040c203251854000c8040b242c03200b07e400e1304403c02c08110214444208400c1e40203072546007040c0b01c4000c036002c02e94014000c6a120700d14941c0c4104260a00d0ba6403002c0b01e80c481001280107002e026824040c1c0003010603181c0c078840c0117450b003103811214404264508000981802101c1c0c000700f0700000802e4016100d414121381c0403902c180c2d82d6480c1200c22990603803075246510401c0c0c5149002801a40c150811507140b402240d84110648032546800c410050b21000d000000b0340d01003124891042108101d914103001e403c0500a54845603104240303d2540d07001100401c4002c03c0034410b001c0c0c240b06865005a0401c1b02400d01d052070410000c071400703144a548000d88021807102001d40f51b02e01a24003100b04540d041c001c0082514107d0001d070007400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 904593902 1250 904592652 904592657
    0xe0720060a090b090f190203070b0d02210103051c030207060608030c0d051204030e120a2f0f1207052706150a03110f0c010e010b0f130b030a0209010f06 67
    0x1ca82c0700c61340802e2189020340900b00400c0c2900c079074910311200a2560b9016a0305000310800060310303101000c020035100d0a40c240c0140d403200b0b110a28203c00403c60720100c20854041d00620001d500000d01d0500900f040100341230105107000c007180a485483c00041c01d490600c90b00041c0045c0004c0a41000f0220034191080c0000000c0c3c1115503004010b01c2100801120001c03401080c003c42c40e100c00c0d020040e1010b01c01443c0c0c03031b0728186400400c0701c089982c0301901082160800e642c690507840d41203007080c00a0700c100484002820000241003152003501c061791b00d2640c4000c1000324000928004d4424150000c0b62980c0c0c05138448650444140c06803040d000404501c5e0140c000c11071001d04100750760a10411510440003000b084400100845007001941c1742c440c1040c02408407158a00008511a44541181800d4808090704c1c90300a00c000c1a002e000c503074a42842d010044d00c00000010b03400d9260001030b2902d541020040d4008088800200f1021800858a01542c4071034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 904595152 1250 904593902 904593923
    0x70c120c0e0705090108010315150f050103060b12071d1203031503010b0a1a12090a050c19090f06050409030c0501050c070308070807112a06040e0720060a09 69
    0x8070802e88481c407400303130014001a5020010700024003448080e01208800c000001040d807039600310000c07254860780091090b8040000104030a42e49405454003810300601801d04024001d490040000c4024003440c050002a00b04018100c4201e0001d404100b001428844801c00b0060481d40ba94029120b1000c80c1c0182e0822a9142c02c2c140104902c0e000043d0032252203e113840c440b80070f903441c0c0d0700302100703030100070008003000d00310b41e0b0007481c007511a10002c0c26088110b4074000d8a000450001e140c09102d6036107041d001040c0c05001542260b900e5000440c0031001282840d00030310080e0400c1d85e009207882e80800038035501114000d0b10f14490802040182c40d81821411580500d02004000800b03150000b8a203a20440119030400e0103070800740042c80600d500a42071075803075295500031b108002400082000d03030b9075489040072001e9038107500d010305020700b13241400700040c90340c028003945240d04403910b016680005040c2142c44256882c9040c01c00d4540084c01d5111801c0d82c1d039280b507 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 904596402 1250 904595152 904595161
    0x130204060506090901121a01140103290f01211b0801080c120a23010c08130809060d060b0703110316020432091908030c070c120c0e 58
    0x2c2011141c851400903ca4000e0342e190440c0300c56140c001060031180c5d809150342d0074405180c50300c141340c080d1400710b03030f014054400d44c0c00040450394004000c800682a21550852940380c0c105201c400c100c2c1961000003040c0d162005035010107203420f159458210b60300f400e85071840158005440a0f64a2880c50443d001000302142c1184083c003a44c3d009820400403210146009548028407001d408281e404001c03840e120109008900450b882000310038030328101008001b80f10b45600e50a5a0501c0461810070078090b0900c5003c680c0024a100800155440709540b030b0001d40d4030341035a0f280c003408001e446215444581e00103500880116005160301e058120021058440c0107903100136140411345113070208009030258010000c40500604800d000a4600300100260b801e07001c5180c1000d814a0324071949001d0400c2d1404504c141107041e508009451001120f801442404075252140c030f290030041e09800341da500c40c0c0500013aa00c2c1d40070400c0f07071040310751303040304e074076102038070007946c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 904597652 1250 904596402 904596409
    0x403031704050607031505040212090706170133090906050105090612101509051807082a071407050f06250b071107080102040b0a0c1401051302040605 66
    0x81901d00501e241c000e403000840451003540800c107421071020303c03010817558903030206040381e211241c1041c0d9070743d400d1304001010030100418001800d2500d04071641254031440c010000106020f002c55400300300c580008407400c3c0f280c0e2204410030509a000302e8240c0c82401800c04020381c4180c000e00da0400d0700009441d8090300c1583e00e003034400b40005103080b07402802c000a10400800610400c401240e000c038002e005a11a90400031441d122652420306020400080c0141c0640080180080f0402c00c007075583d003c00310b42e4019418580740000b03440c01c8105c80605d101e041c801e0003101000070601d0381c20301c5119080103100040701d605807240140c440e01072184610441c28080c2c0c012104001040e20f15a0f11007142c2c1e42c600321041c4000345d180c07040c0d56140d0104000c0d6400c0740000c4081102516000b0148980350041640c10300031440d16190908080700f40c051500848284005000c5020500c1300500320954043c1440001300002d1410341da803020b200707011203000d0340294901540849c0c41c2c00c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 904598902 1250 904597652 904597697
    0xa031b0512271c0e01121d06010902120f06010e090709081501240f1101060b03160207120f0f020d02090c191805060a0516030203030105040c02010b0f010f03060b0d02040303 76
    0x1106a541c003010906c002c6c1e4000107441071201c0d4020301110350f5440c6041400621005000e44115a000340c0e03210342e01c61202a0340c00d8003074a83e505480e0101c0034001c8503a0042000b000d0071606035440200d50342d550900360350b0540c103076100d11254042c449540640181401c0d03124180e03011029031126000181c403151070018030a80c40305011505055514501d24010000444440d03e030030b0003c281e141d00d0f001c907501207030011345400c102a0b498a00c0d8624403501440700d400504142801080ca4032415120b44407051404200a02004885000d15040d512030038140d028598001e400f8140c241060103003400b090b84032015512910b04251f2082140c28405c0414800304803100010350a000d040104012440e0701138040a000d000c002c2021905076a15090010b480500940240d07480e50301d804140025982d410f00304030304592404060310029aa005502a0880340070b10b8010101050740b0800d6008080c183c01030400c0020116000f012880b0720740007003060300d00c2640c948841405101014003243c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 904600152 1250 904598902 904598927
    0xb040308160207030605150301090804141c120302210402090c07020109031106041703090112020f031302031e0f1005040b0a09080d050103030201020a031b0512271c 72
    0x142c2010030104040381741030300001e4210840381078081902d20b29200003030855061013401c66100c0e1011800f040525000ca01000c0601015180d00100307005a000000c15606e40050080419854482c0c1c21074441c480d506031951100c0b04140000040c03d18510360201c0d0700f0445040344100e480c140004d020031203000541e50b000e507040c1c403410101800d650700c4643c1c008800b03000541201d4140000600c0103a541001504441807002031030752001c8400005000b50788a40ba003a070024010880310a170007450f10102c07a840110002d02c0c1701c094400d440000e0820b01400e0300d46030f29020318139114440d41800316a0764840403411080381e80c100c900308141e0042d16400c980280005080c00c0000c2c040c02c04c00c1d007104428902c1600141d250030881030440c402c40c2d40030b81007600107079404582e07031030301540503c41c1a805644c0078100d90701e944c2c07501070000c1c0248288040410a00c00402c0401c04440e10020082a050100d48105120304014030342995501000d809082d80303603000c501c600c2e409a0290018402c01d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 904601402 1250 904600152 904600157
    0x906180f1a24040e100e060d110f063403022a09040c090b010c020306010b090a0b0c03070326070e03241009110a08090a0804030b04030816 61
    0x20200100208484104038003050320100350707405001d810041050b0001e00c003500c0040d42c0e4021074141006074074115421034119101c0140c42034240200b59440707904440e01c4582c00341c0d03a4108020310303101164041c0c00701108541c00c1103002c608200c0344101a031000e0024030110346a1001c150502c00a0082c40c000303c0005405030300a400803041d1400801042126a5100e0090706d55414160011510441e0105e6082e210324410f420144400c8029000d00c00300328000f40390225040045030002601c3d1780040c07007042d000c0c1d82d0010712281151643c001060052001406044d01c4110342c03010b0303503169072100340228000303a0702d821031016010714031206490074080508940c0300c03030f56941c205440040c980129a5810302c110b0003240c07050030a4500c0c103d0030b5401d1b0714503540301c0c0c1003207014107000c29010303040380c082c4a0520118500d12000401034451141c101d19010815440707103961282050f11006d00075184c0200001d01105200341043c1071402944251f44100084d610a84a6280d0742c1c1c001094900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 904602652 1250 904601402 904601441
    0x628110c180a1b0f030c020a020a0506090d05060f0429240d1a010b03042006090306100609080f060c280e09060906030a0f020f030d0c0212010c02030a030f060906180f 73
    0x80c82c140f41000e01000700000d028045250380a44409142c03c0044547440402d54182c010482004001d03401d207001300c20380200b601c45020140f0b91584009900602050b9248045a1b01040810709051050700d10b02002c0c0c41055250118100302c0041c0d501281d00300c5600d6440d00001420800880072244910340040704006d4105032966110401030400c03c0c03107944518180001e00c060b580520540740180180a842c000c09403500c14042e00c81c0410f94404429504100000c004a810108056a00510302d1402c0745d500d1140303403040d0585001000781c01d9220054a030075192410740080240c040b0103812038806032160740314010010980c00031541c0c0e58040e04012004000512198490341c1d056200a0540c50001020000b080c81d240720342c0700380000600850080410f60800e05851040c150104e0000c0c404d621504002031f560723200d40000b000805035076082c0340c0c0d03501590343c1c818005000c4039441400301d071340d41c1d00108100703140109c40b0030980c92400704102440b01d003d03c1001e105000000700d980 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 904603902 1250 904602652 904602659
    0x101401021203060a0b0d0209150a020312040836031b1011010c02010903030f0203131e080d1d0604030e0d020628110c180a1b0f030c020a020a 62
    0x81c1c03500050051030b00051050004108070440c40d0150000a41d06100140c035550404100000c5450b101a001c191307100c1004601c022175030100845003042400c500078103c41c0ca80e86041309051103035402c0170f00d50303005400e0070494880c0e01c13415a500c400804100e00441740f040d4000c0540310341c001c540303180c17003050542c80820a604207250042c04080440c10103408140d418000d003425034240f2201c400050355101112001c164040c42540f0f0038144188046045141120345c0b82130540224001412091100c1e044080c0290500c204d000303100d50200d08640c0340d41c92104000d0103400100344032842038041d048510360200000903445d1040350542d859105241c01c101c207000000000000c03e03600082e00304044511501a0b9012048801800003000d096030301441000300036401e1040c60640c5500204003001c91503841c1d659038900d030b01040c40401c00546072008490300809180481d03400018441c0b07000e0101d2030f04500032410700103607620b0030b12002311203070310890b11000ea82c0d4000354400410304051 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 904605152 1250 904603902 904603933
    0x1120507050c010c090503010f05090a02011b08040306050f010b0c07091808040b04090b030d0504090f061512060f12110114070f050c1005181f030510140102 69
    0x898021115003082490720252040b56800d4800c07418101c03000c10542e5004000c03d041c00d214081c004000500b0810107070405c02c80f032a071a00ca0501d00641004151400721031440c040c1ca608910b0242e000c000c031035a450b900e00c0c22402406007298810260190361000003482d0004ca0101c0d0f07500c0361443c001d01754541c2030500d9180180022091070036010501c1c8100b10020b07a01c0d000a0018107143e2001d075031540c2c82c00d80400151605000701900030b420808032492600e03002020340d42540d55664010441a084a100f40020702d5141e06c1407210340124107051100031340000c200050760195490910000303460f1240da00c5007811600c00c1100e101c8880001c2070210340401268031240d40c1c149070055403101030704600100f90304500c1d015645402d6481158081203004c20039070300d6000302501c00241016a079040542103004448a81110f011881d28048013641c03002200c450204181e13038030032540700003504c000340280812520070050f98184200130804d0002c5c11b00004141030305900400340300c504001e46 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 904606402 1250 904605152 904605161
    0x806070f0f022e020a0327020d0312110412110907020a0f060e07080303010801060f050901030b041103010203013f02011d150702040c080106051603140705010e0d050301050112 77
    0x1042e20b2000d0f5000744450003680c0000d0030214069a80840c0301443c028100c4890110586200220030204042c0c07001a120410101c101c240c041c1003400b20700080aa03840c0107092114034200008200081c0880c200074004114504039020703000d01c800c0b00070204180603500b0001c1e104000940d1101d00c8083c00940e126060071102480b40a002c1031798080d8510461803c20b550b00440940d070004001402952000d1049100624101d091000748601c2d20003c0303148103406000c09060842c1000000d0107201c491861800c981c80c0140085540e50b079259038121180d202c3c110055840584039890341d540f400c41c90007000514222102c2002c00403860786c015202400000c60030b50485c8050860120a661000520303c00000000341203039071442c50744104011112503507140c200b40980d100047c400355500c501603c1540e15180d01c0c10320300f5855403d040e10220964000603501c2c80b80060031030104030341901b0102c032094204040351100d40a080040c0c071640001d02403d030002e2049103688001c041c480c3c01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 904607652 1250 904606402 904606453
    0x4051518280c0f11031b19030f021c090909030e0a03080307320304021201091b0e0f0c0915031e061e0d020135091b04090317010806070f0f02 62
    0x115040d0b0107010f11303902c847d51202c075000c0c1c006c503100e044801c0280d50103004500c102c0061603003180e0f034a26644c1c0301414900c014003480c2c41140c1d580704400c007054003480e00584501c10040c0080211660b910703103e0160740c02110000005181c8218aa01070501c28101d00d080310098020345071580c4d5030303501c600c041c1e4000800c1642c1c44101c0e04d01e04040750f002846002e980501508209104103600c1c51810195491948103403441210700c820014104000e20030281c128096014403540c441c000710000711340d4120806c0d190480b1a001041c40f4541c52045100c0e00040203142c40c0240a50340c450400501900c9280d5101c1c8900848041050518147c203840c4034447c814100200c89168810700d1161603c22100c1d400407440c6040c03280c10502044a405a512091410080c650048403401c428001e00e450000700d4010703034641c3d8084041500036843c2805a00c00800c1e68011903940d00c158607656003065904070003141d81c202404105a01c83d1455601c8041942c00a001d92056880741c602203081004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 904608902 1250 904607652 904607707
    0xe10060f1a09060703031b05180909071a032502190c12050109061506020309040e0304080115030b0708041a09071a0904051518280c0f1103 61
    0x21140c1c00f561044081c0090601035680054210300e1041441c00c00461014201c051000074131000c80003050840031609104c006561921968a1b00c1d500107203004c0e5a41c1118100c3c07096806944c0c500c0700c0101c080c5116012750b00e5400c403000c9030030b503000046420803031010700140c110102e07000c1d03003402c01c00b09440031621074180d031a40a9030741d25101c80d2081907003c00300d40700d9440c0c0c00b04906000140c0951400080c2e42101c0c44c01c1c503071806102969030301c0748100301c41c040e80e1202580e403c3d09800f0f2090740c0c0140714010090180e401d00070001c0c002c1020900080b2000c5041c074012601442c4181c00c6203110301ea10003e1150901003800108034a8100280b1904035480b80490205582c0c40c01074181c0004661402e00c03e40702c404a10810090350341c014204045030715001c0d0700c2c6c466595610005070320950721307075403100c11911503100d9400b218010088000f9032506044502c4560200340e4444907400c001c907501e01140b40f032141e1003180d41c8280e1810669850b0b00602c4407984a5000401049510300500e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 904610152 1250 904608902 904608907
    0xb0a2c0a020d1a06040b0105030105010311070f080915040e15030307050714180c090409260d1b0c14010b0a030507050301060b0f0a0f1b060e10060f1a 66
    0x36800107640d28140e480480d0880f24000300c0503840c840c400d02858101004403814170861407442c0000b401030005208082c101500d8080e8450062203980c200c0b111180c00c40c00709070101265081840b180e074880240359008503207005146030030344488000c0d901500d40c0d00ba001406900c940344003500a0300c1d18088a60b141c0020000d140014000b044001c0081c038000d9101252031200ba800c0002c04400c1c051003d41c80320035441003001d01c401030002c9890294040310009164607882c03c000c16030041000310915580b0096018089550701080a400000e01c1000f090005100101c56103900c8150600f0160201d409448003070002131a81c44000c1410340f50b800001060100100018401081c60f80103441c1a04808400c1c01203041c28010704001e8044100d042d40b4054403040701003514440c9480c8c2e0b504000082c400706a1192080d6030465104055070303420f69030105c8900340000100030303010038000305200d58a01c0d81140c5419000b10402c070380c00000b000b82110700c2c0400c1244450203040c124152001c1c00c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 904611402 1250 904610152 904610173
    0xe061317070f06050a20070501090603020c07030b130c03060e07090c020a12030b03031b0d020c01050d020309030d051509091906110f0c0a0c0b030c072307060c0b0a2c 73
    0x800c210107201305201c0010b0a43e08e103890009070107640160040d6080500400407080d92200c00100c0030100da90000f20351800c3d5a070503c041140d0600c0010041c12407031229400000c0c050541c00c01e40c50300d8040800e613418156560b030914222114804500c0260300079280090100b42c2c00d03065903881e145203080100d101c0350b4010001c0c0c1181c1c44502480e1040c00c1e0030603455500c02041048001d59120340c002043c40181d03040001c0d16500a55010030300c00744d00000095603d00041c4207548122890303400912807400c4c040e0390030b190700c08580c402a00031030396000010b1401c0c0b00002e4440c80c2d607401228010085e40581c494034054031182036102600c1404122030020403403600001c0c40c8030a4940060700c80d2038103170300d0b10f80c950040030b07400600222014814010f00b42124421100c050f648408500360324040c440070465540b0b909140205a03010310700000441680100d081010070b48510100645a030304d0011190898101c1914010754101c10071019003c40400c500d60019031b03690500300c60081c0503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 904612652 1250 904611402 904611437
    0x80318060721020901092601050a05041505060f01031812020a0309080606031203130c0e0601030b0102150a0b0d120f0e040b01080a0c0e061317070f06050a 68
    0x100755040070008000042004030400d14100014007001051402d602c1d144a15000031704070b2141f401380e1128000c0825036001840282c1c40d00300c074031030b01d818001e01440c50300885030310003003000300d074140c07007046540303040c90b40700c0e0396500c95584960f20003000044100c00c5440118018080c19050503044071500c3c001902140102c00f4904804485600401c4c40101620700140007010340d6102d010030381d1184050111559000c900031100c1e03481d09580c1038613560b1f8102005001e9601a0010f132088404004c081000d044c1514064807510082c0c90510201c0700710001265100c601d802070690404080011400c483c000360041c000f0b242c8002e1513100c2c0302502d9142d00800300c0090030888086800f8a0400c41e415400408010039404211420045c2c4196440041c021610040854050320366034454505d085004181041c150074028009a03203d2005a00a07448200c540c0039190a0349491040d40040500004419041e116804030150304603142a409413075a400104600c1c060020340d07480c0703200309031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 904613902 1250 904612652 904612663
    0x140408030403050622050c3a1b0b16080405130501091808070b090708011104050906240c10050708190c09050114070204140711030405010c080318 64
    0x14003e4014140381e00700000304400742e41941c034030ba03114507008500304408540c01056161800600742c4100607507101c0d040081500000042041522655005140746001e14903504004103030b106034075107060900c0040756031903158283d204605002c1030400400d00380d00500b030030455003140720301d00e4141080d0b118000500d410030001040b030703440355449004000c1a0120700800444116052500f40003046985400602d4030450f41e0142c03074141c000000c101c941100300a030f41d0040c4181c038000c0180d040c10b4124044907600a20519110f881c004010403410f02e0220403400311158128050504104078044c04801794000b503c00300414040d0a0122950b0f050034003c0368490191680c403407119140c40b01c0751140c00c0619044c5200c01510740011403a0440d044101c20b8107445003401c0100c0c0301406e0381c00007812071241c500001d41081c10150078007000325009520500448054452103105005a0b0b0b405540303000d030f03105850000b00449008404121640f00030360b0800d031601d104400c00c4008041407440c20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 904615152 1250 904613902 904613909
    0x30718090605042a05150a0e1306090f060807060c1113050402030d02011a011103040503070e0f0903090109050402220f060e060304050c0f18070207060314161404080304 74
    0x2c00c07205064080180c0c0440d090000341d04d03100c440c019110700300300100d000c4211103454260722400c00560800d000380030340000c1a502000030501c480110580005801514140c07003080c0b2030a08191918968160074002c0100f92940740009103141ca20300881101c00461084003070b2010440b030428151640c40d04102211031040320136001c10130b42082e00c18107140404080340c9500310392400030507005511003902c642d111000e0034600302d1090400521014118800c43e441280e2501c144000010064080d03a442c5224040c0d4030107812640e80d441d08426106d100302ea180e180012aa0a0103104500e456400303810303210780e56404082f2140e503030545100e0002c120380102c0300030801e01c01e04003c0340c0d600540c0301c0b030000425503080707082d0b0030035950740741e42d0384545110b0f2441519403170000040d42d1a00c12141014000d4100601100e0510440181d02c81301c45004400c0081e090503510021008200c05480c02400300012120300000200000c840390181011b103040c80040030040003841000400140019 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 904616402 1250 904615152 904615163
    0xb180a0c1b0812010b1204080901020708060414010c2313030203030c0c0a090e210c06010f0e070f20120706020301051f02060103120504050a06170a050603071809060504 74
    0x40b4a010b410840000303c1c16448400703881d004202e80d4000e0380c0030f803000755080307540211066140c4151800503420603d140d0003a5041303108130420041480656030b5032150450715000204403094062408840d88500d026015000310890300d80c43e00b20307495041c01800b4204a20007100440380d1240e00190071a030100d600209240c0c00a6a60522498005c42c1c0d00c0040402c10001c210390011440c0140e210300f040300710900130307070f1341800d941c408048500b04640c59402110f05840c201d40c2c41d2280743c0b2100030346010385010a80c0d660001407201d40540d5a8400b019503503150b10405100c89481c4003480182a08040e80c1402515041c4100100c4d040207800b000748940000741c1c4a40c10502407180c5059541004502c041c0035888000850f0b03004036210381580e800c00440b40c4a0031494100780c4080c80340e90303c140d03081080034500080c1e16501c4030022081c841410003c20307003500c0789880541503a0043d540d80341c0c590002d120401ca982001094249500d00758000855030103100d131240000c42c1c200f21400e03643d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 904617652 1250 904616402 904616407
    0x1709030703020f2a0328030207090203040b18071509081011041e050901121211060114010c060213031b060e0d0809040f0b040b180a0c1b08 61
    0x7016014040d80e07070400c0880c0010070f500e98480c01182c0040d9040c003204108001e214061310140d450502175801d424854444005000d1a010350b00c203e82c101e0520300343e005025860002c110000c2c1070080781c1c0141c0c1c10410720003440d03d9000f000d4070100700c41042c9030550f108840c070005450745e00c0b42e400140c040c495114080c0d035a10b81480e00d41800c0c0710306440094075103000c101ca008038860409481c00d858054002580c21a10300110042d045070642040381d0066000c0000500440d156600346042072103481142e2006c00c806d00296514a050520302c07220b5003000c8018040306030680c0c500750b94100705140070f402c44e6000d520381108a911501c00324510b600308044c280280305031000070030030316242d2070b0510150030b1905000400b00d1030303841c218900c521545103144041c02541c000b40d51205800800800c44900119141300041c90540e6001d8040d0341000c058109500d8210601c0c40c140b80c030094512460b031ba41083d100018480d88000d581030000c07601c0c00d000e0551103012003150440c07040150b180e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 904618902 1250 904617652 904617667
    0x90105150d02100e0d060908070606140a060305060f060d06080f0d020d14070803090a11040212130302030c07060503100e070219050c060d0506120a02090705030403170903 75
    0x480e10140122454010081d100111005884030030198030411102d02e04141080a000300250503a200c091000e00514100b00800d814800c042e401803001238841e80041000079a075002c10308076058032803007640c0d100c24081c0e17041100394025000187d00000050038605250348000c00107003560000491404405e85d07805040c054088104045060102420f0080c01040c4000e18004e590f00356010900c0104004c44440d200d490b80c606d0f095408055000c0c1c902070b1249440d0001c1552000e030440161220003281401c01054103092085034001102048000700d543d403988403e00c2c04810500c000c400710700c400c00690302d0401051116101614280c1d880d9030b40c904010150850036040f40c0c2041e981c07115000d09000312580c0000e02030042214080401d50880240d091490821941900080d000301d00043d40044448413644844d108070b1003210301c2d40e0040305980da403556801d81e0b410001d400410700030104041e10301a002a582c03192092804002000700340546001d0f2600503141c50b00c0613030002c079188 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 904620152 1250 904618902 904618921
    0xb04020a06050f160507150f0f0504080d18050d0f030f08070c0f0c080d02030913050c1c0b031e0c01030b01020d0c03030e070b040e0106050307120f02070b090105 71
    0x100200745600e8641e040c83c90070382009840388101450402000301e41d64102040100a000030780c0140b00c00e5030007981030f405262001c0c0414408241000000e000480318100c0540200c0980381a00c0208008084140928005440c0501e41c81400308220f190800001016a00e145080407014862090724165072070301c0ca4050038201c45c04010b0414022500104100507511103940d403600c9401542c220141051402e04e01d01810381908000d03c2e9018078544004d11503000402004201c7c1d00380d0f46d0003400417410402c641110001c0d221040000c800b044840701845401c1340320f41520f094100002800107110001034941006041e62002840240c8640d043c006018858503816030070a08061100900c4000005c0d00c030000d1804030018040440c401400b4148641e10101555845808642c0c04584a0460314078941051203900c100e80810b00011030143c1c49041075a020f9003982d103517030744c1840e00208541c004d8451001201c0840b40d080c06440045140c26002c640294800e0f4000140e070709042000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 904621402 1250 904620152 904620169
    0x201020d1d0706090e0c09190e090c2718010f14090604210e090f0906090706080c18060d05090c030d0e19120602120105011b1106160b0402 61
    0x54018804c106000300101c68440c2d0300c199101c0102a241c41ea200002d000046001009010104100280081c00304100840c080030900961280c01102ca0711034420003003000c4800c7c1040f914480c00c1e4180020a2503800000e200c2d50442d01c14080c03071001e00b0240c0e45c070724211540c030030040044ca42c42e0030b0850b6070440314a000b280c10103070341c0001e000d51780b905841d002c1003144c1890030040e05041d9030100620310b5101c1c0c04044101030004002ca10142840080d007131020100340c1d00f04c1c5c03007070203004041000c0b00000a6a00c040b1403080e00d920006503103075102082e158020f1140e0f240c2075400c00e0019202569004010400408111000521070611070266460000c3c83c1c4980c500990214003890180e40e00980e0241c854401110100302d51188850900c8110907076a02109038501d21250703100412803503401804c611465600b21440580c3d0f24001124900c2c5044040a80301d13a06403208400300f0800c6022a19840c000b412007403a148000d00007a071641000642034410814100030301045151a200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 904622652 1250 904621402 904621409
    0x2040513031b081b0105340e12010c21060609061803060c0c050c09010f09090f2103140c030c031023270606030403020f15071803080d0b010201020d1d07 67
    0x104214000c04030f110308040d010307d59100005105400240381166503800c110340e480324010380c0c001c1c0b05440328041701038120501c4000c1c201120f1104421505103240c0f07442040b04032442c0d030307640b007807000e141000544810780c0c4030140940d0707801c5084001c40410300c0c5001d6445884810b5846142031000d9040035401c02c907103880c1441c410b546881c0104102d180380502c2c28141e0328460740006000d90300e46004003905111580c0140880c6481c0001310701955603116420b10304000781c81c01d009a43d80e410101c0d106110866240c42010380c11b10202c0c000c101440041c0d9841024544210010741c1c0b2a1f000c01904510904007901c02044012401040d040900c3c0c0701d94083e560b1b52000d43c0e6401c0880d80318400e0349005100b24001c0001000003004d06208001c1800140c5c0751800791020284502e8826a80140450781d4402080a0340c08038503100700c0b044400003c49400000e048d003052154008c02d80a801880801c07411590240081c0444072144d2083c118510703200829110f000c80008a40e03410500282d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 904623902 1250 904622652 904622701
    0x711030d0206040c0b0a030209180417030f13080903060c0306040f0e032b06140a050d03170a090206040b040f08120a030929010302040513031b081b0105 67
    0xb024400020b04c610032081c292a00a036580391a0040100110028062041801da0224103403001002240c1c014890318011401f0700307542d9840110100c1400120320098900b80c4681800c240040c01d040b100d4a030b0480554841d04886203440110390019191640c00d40314034458500001c01e1080501e0309118100800c0c3c6880c42c284400702042c3c15040d100d0142c0660303c0c0ca0002444171440124a000c41000052250080c0400c4242d03200c1d2010540c410681094034040c001000e0301084501c0c00e0b070821020301b5415502c207200c5000e0004004000e01c0081e0440262589401d030080040e0365200181c40070300703003000d40306403201e15014406400b84a41e90044003103070060503004410b85d03000821100042e400d8100031806080c5441d00e08204a40d030aa40a030071a110105d026941148100007412640212001e2016448000303c3c1c0000d500d0b9000f0040209500321540980b0318250151300100c14010201141015000c415081110014520b52030042c0d558500300001c07540003038240c0d1402c0d403000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 904625152 1250 904623902 904623913
    0x403030b10030e1e0304081506040b1e01120b15070c0f060504091e0e010e0c030304060c14240403020607091805090109140c010905190513110711030d02 67
    0x41510352184140c108080e440c500000004d061010200103c07401131903001c1c100c5004603820565075400e0502510601d200780e0401e5203100301072500c4044010309a0f401559642c00c403035004c005461003404000e0340709801d6141c40310056180c1d02c00d280d281c0111003280719190395001600e0f0003543d05000360004005e0401b5000300384956036014003642c060322158240020030000903644107060740040740340c5409160804110800844064011032040d0380c0c08401c80302c41d0b050400030181c1b2400b40b4002c20001412008070380c00400c84455110f15820074210641c1c0d80c05c030a0108071400315402940c00c200c0300c03c4d040300b844101740c0c0c10001e8650107002440c000c2c800f981404050841d00095141051005807941c0100c1d8100001b9800784054036030000e64581c184044101a5403500d91407245240401c2c2c408100150381d09007003038080300040c081ea0308a4200e0b420300301044445545854003000d583c1c1d0700c5460100c4800304500400d00306001d49641103c0440030001c0500d0320505030803410454108 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 904626402 1250 904625152 904625171
    0x40e09030c150a06091109041d030313080c0709021909080d1d1002010e01200a080408070b090a02040c0e10031a3a200f0301050403030b1003 62
    0x4681c800307002e00c0b04811010951180c40803040a4407280c4c000d25002ca04d0802c1403c099142000104002e0005560038000103280e450111410301d070142c45040544c00400004a0411400441c1d403881c4c1e204031011800c1040302c41d0624076084141d0008a2000e43c0000c040c816004030019003090401e0030f1614400c41030400c202661981400c20306202401301e402d620170602610908400708a94000c0d1088101f62a4160002d020304100161811036500e044402d29410000005541d000418840580d00e0480007800031146141c0040080d01c8a10081c8000b2000982880100e4024016107000341074980c000c1c01000101d131078070040c1d2800d01500c10311804040d240e01c0c0010315019001d040010b50b09140303008031598034142400c1a68425030a500b2458031104060075138a85a012200160440c02903000402c450490307a038010308034207440181146107610240c589085d5600c05011680d50380001c001180c2554000c1c0ca040303010036184c1001c040c0c9818003d40b980d100300741034a402c0c00305000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 904627652 1250 904626402 904626427
    0x90b120a03051b0d08061903021f030b12011509050411040507110f010501150e1e0310020705060712110f0706090b04050a031e08060103020a0c0611040e0903 69
    0xc001002002d0100100d0b41c1c0380e001100000600c2c21503104411350701041444040103003000c0b401c680c001d10800620b00c800b451030001024100581c2d5016000c0300b140c0c0ca20b8a6111206440328454608154a0703160580050f1134502e0003009510311800042001c900f104200d048480040d04150495850b0400308404260000c030840401242601d0000381d40e104c2c4602150381c0c141200b00300c415446180410916054154405070403a2000040c4024000420304d04441500401582a81c000c416001c515403c0740c0c10310b0041d81a00c40102200c1040421810040680c4c2001c58151a150000380812000581282c0c0380341c03542d18500c00401804440d484041030078060042c28000b07040d0049259404c12800307500c000d44940d0045000c0e0500e01c0d061800680d12039413200c049000800d031640c100b1481440c3c502c0c0001d142010b4541508a9692030300441c001d4101010803c01c104503c4000741c0407030454800c4594242d41981499642c6081c0850601c00c2e0f000508545034640c42007100700001203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 904628902 1250 904627652 904627663
    0x60f060f081f0f03060c1e030f09051e010b03030304030e091f1518060f0e03010b09311509031206060905120f06010306050403050c01060f1505090904020f1513090b12 73
    0x40c10300181c0342c41c02c15050f20042c40140c01c0102140705440544d400809000700a55054480c039000307014807a001c4003814380b28003080c1c40c0100440e42c8601205050300d0300340c0380310350300c5407030003078043c0c81d280e0048184501c48425038440500d0001d04030b0b0591280b58001d1035236107044a10300b65150f015243ca84010040b05142c103002c001c0058074070480059540c02e4010615450002382480ba003400d04056904500c20206800381e40c40f01d8015018008885255082030ba650700625040c07003002040000c00e001d002d5800049040004640d400d800881a6109000150005030350310341140d401c0000703110b046100705070b1013030301e650290440b408003000000782507065a5012402007843d407900d203010f44950091014100075542090808a0945442e04500007140c01600d1621041c8030240d200380c4440c810811441d4016200c00f0018025042c00e8034090258140513203018a11002c1061824041d0404004203a0101140d1410000400d05005400c01e44008070780810400e540f00941686d2071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 904630152 1250 904628902 904628957
    0x90308010e0a0e0703120f090b0715060506121b0f180402040b0c010207060f09080307030b0114070b0103230303130309210204060f060f081f0f03060c 66
    0x207001100054003002e050300565103410544003122185616881c00c2c00f42803550741c2c03070040090820407803003600724891b4002c003085407040c410407441c1048549070b0f031a0044a49600402c065102c1d003002800d5224074006107104524201c2000c2c0314185141c43c21494803501c501018064814005551403482700400c03601041d1010b94400c0c0c454140001040190050780d00401051001051600c2c0d14041074000b008400d21501080104032a01401070084801d40c06020b44100d2050000030040f0307000768015004c0e00d505040000e0600341c460058059a440414201d502800110040040201003a4503058083e440b5420b0b90003100c02c05402030356800003e1640c00c40070000b002120506002d80440f10140c03510881751400100e006c0d280c198180c250402c100d02aa1604500103001c0205115030070030396400c2d558040520b000c2407012100c603a000703002c0364003e9403451030b914041495018104000c10310507583c1c1d00b031503145051000c11030702e2002c40d000c103011441c034140349442400340f16140310 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 904631402 1250 904630152 904630169
    0xb04110d022107080702070501180612090b090c010908010b030c010c03050f03010f1e03080a0509010905090108060f1f15020109051518030702030309040506060d09081305030109030801 81
    0x12102e5080c00980c041e1980400b95203400d81600500c01407079400746129100f1042d5400f12010181d0710401140c50500310070001c000750040f08024040540b00c0d0407081d410030740c10303800454200025200c00300b404500303581105080d800458035102c1c0356004440200104106002001030561a6020a4440305402c0742c1a040000c0d80c46544205801101601c0740c0f04c2200f10100e450b5030b1900a070340000c412a0007404140500c0a00c01d2548420325905c02c01540da00c144500c2c200314805c0d00c1a2940c0d0072445160b41400700c241c0d0301107039070f403601c6004500038010b580040c0807504040c0c0c0601d54103580030748603404038000c05210066416510544130b0445500300c80004500101760b80c101e0040400300b40081c03280c01005003501c0400245403e40b4003c152007019084002c0c08448102d5503407046901c0250560014880b603040c0345000c0c2c0c07040798800c0b0041d003100c0c03400c1165580c1d80c0440302c801c0c108485038600030985001406040040c0c2014210a0703001704200c15003a200038001607014481e0aa9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 904632652 1250 904631402 904631407
    0xc010b0f060d050402030325140d02070315061a030601090b0c07051003020f130e0c040f140f060c060a0b0d0f020d111005030a1416031505090411040b04110d02 70
    0x71506c0410440701512408505462008c0c5038520218024412040517220800f2004021a0406000c50f2004c4242d1441e00201a03040c60f50303031074500300c0e140b100100d030110b581e403840020200704240300711491495503a2410382c1c03898200000751600e511600110f03034160041c03000c20a081c500245201c00ea650449444080c0744140c0411000b91080c40414908280003141d0280f0810f503e6104100ba951241c0b9420029a1082801c00081c00380f4424141016264041081044400c003110b18007480c0240c00c9064003030450340402d00c503601c400b01c0c0080986c420030800c20388035041d100c1e40c2c916400880d04640144019221803800c80082d20010b446034081000d24003c110b403003034150200b514040d040600ba04024400078107150000c40b039403a16542802100304d00341c002d000103180700e5100e0b1301014a010820800440003091a00c1610700c01010302480881c2d50b42da006007a0b80b00e07500c140240c8141c6a144000e00042d0380320b03166518010b0b8107001c40103048a140340c050342c403100011500180c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 904633902 1250 904632652 904632661
    0x60302071703100b07060f0b0303090f0d05030403050f0f0705040b012a0c0906140607050613061103010e012925060c03090516120201140c10020c010b0f060d05 70
    0x20b003d40c519886081043e800203000c000f04049600800c0c042240d0460400010700d94105050301c2e03104041c0314075401030546a601c802c41c60417080c00600d240c09607040724102a16551454600111982d424080e80c0c0040035002c0e0b117006c00c1049170007078081510103101d0b5000c1440060909030003084c8000f840c541c0450300a03804400111450346958101d080000386a070b40300440301c000c00d0790780141341c4803084000c64aa02c50416404842c4e0b50742e80040213281c1d035914100240e103e070b1a4a941116116100d420701074015079590302840c040c00f0b01a8080d2000c1d40340c616030b07070742500384a282807208000c1300f00101d070410b1010050310b02506d0002c0c0c8000c001c11044807074001100814100601a604d0701d0030034840158554003d0003d039101d9000c076075030208aa0190b0f10701900314410101091040402d4100552148040081d40c40c40c000c00d03c3d042c400416151810102d00b880d007076550079400700c0c1480c40e4071424096925000000c1d00c0507003041200201040c01841a410441d0302c140e10752003c80e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 904635152 1250 904633902 904633921
    0xc05100b0d0c090e2503060e0a080d06051c031d04090510020909010e10060509040b030a0b0906101230030e0105180303070e12070303080a0501060302071703 69
    0x10035681e54401c19919550ba201c3c011040102a0030314443c03118801d0000540c2c10261300a0380d000d9000055005003420780c55651100013900305c1c0e9a00c018907002c2c9040210000f0320760406450f1074039887d02c0110304603041500313100424a8864881544000101001d40420740003d101003085e413452023a81e42100044011901420080f2170051462160040080d44140da560213030804079422100d4044036640c407180004000c005444d07106440205000400019004100801010300c014202240c01401c0100007401c090304c0031404c0d03480050000801802000511103168012411607801c0d01080c01c000118013001400400201205042040460030031400701505103282400c4013000c050036107a950040141540c01c0d0400515824040820380c46103104210040c4900c0c0c3c0301c001c505680e1900d0303040714624041103501c3d8200c4440c2d036010701c0503082840003601450298880a003a82131a104280460b10141d102800b0148140200c1d400513102d5041c007546080510281c41d142d4440072900d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 904636402 1250 904635152 904635169
    0xd1b02010e0109050d051b060f1206012a030206063001022a0f07030f06020319020315090f09070608070e030304060e0f0d030e1905060a020a0506070c05100b 69
    0x11355440201e0380c000c0e5003040b40000303090190302c00091000000032400c0b02400343d41c0c007440b088032014610502000d20b01300141003200354401c00501d0300034905a0442c0031081800c0f8030b404040706030610030503010285a01084207607001001980d40c0001550b03031501e0310010980704038000710328003032501201460310801d4043c1c0701c0342c1511901c900c040030380d400101081483c2c00d1509080b580941025506c40d0350000c41d14038100c2e9000702d83d000c1c03511001d41da2140294001820388901900c1050000003414440c8080d501c90860410f0710314500c0c0721003040040b03062008000203041784584e402c22031501d401056074002c8410500340a12543c54841c0292249070780d9107c580d41500c40820006507070b51788000b2a0364104400d403541035030340c6c01201c2403212859000201501003007401565040328100814140e40031920703414001d121326140e0002803c0750744031003003040059001c0d159607800d200b030a004051b00481c25007084482c03030138595580380d152204040008100b995a49151000382c884624 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 904637652 1250 904636402 904636409
    0x4051834090c0818150a140108011d011a1002150c0403140c01270306051317030108060402060a200d0905032d15040507080d1b02010e0109 61
    0x9400a595481d814580000c01581850780009024640400c00079103c000440715a588481c3c0074026400b24800000011071015103108001030b80d541c0e507040d000c492900500d0190a00200101d0316020340c51601d401083c4449004c52264584002442c0ca000c406040921148007507904400003980742030280d0500b0001d500907201c41200904119117921450010800c2e01d104042e4501d05000d0303100410703511002e00040501080c00121440000142c03040c2400b040051043c4020540c0c0e101d40d11401900c909413051180b540c4d000c00303188100002158910305071444a107681e400c6600d0b000c03c00790f82d440043d2019010700e000041002110744201c6182003d902644810380b5006081ca042641d21401d10100100142e01000c000c54140b401145c071450381c4442244902c4256501480400401184103400d052441031150ac86650882c03034404a11550152020300b00c05460b0010b018182a0001607410800071801e4443d4520140450383d1008150286000b000011281005031030003004c80e007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 904638902 1250 904637652 904637743
    0x6240e0411040603020d080a140a02210d1d0d030209180603010f05090c010809070b04030314130b1c0c050403121101020d02040306150b0f0c03070f11040518 69
    0x40c86c41090000900c001e051801c8a03994010181ca50b00001d0b1445001d60543c00e00140c000d41c090f101032207400c80c5460b5081500c414002d1034040207103410403c41d021103800b4019020602e614024103001800740130030203861400c055203090f1011000038101d0079103e45e84501040c503c03021403205e880951203402c00c090380701410061420700d210a55902e40a114001c0d00084e0040c0c0002c1c0c40320b801180c054200e41c583c10210342007a007182c0d81920110040800d880b900710301440840d049504940d518030040c480f4542259807001540300d8108520010308808460300e04002c0080036282d4000c0c2184d0407203400c40d0034000e41c103012072011900414290b6030545590700100f0000001010341d401482124402e03d41000740c034515420204d040b4a5901c94034091000c1444200c1220000c00010641500d05005491800d034050b681c2c0341410006550a4424110120311f07030700242402e10805404c542020980f07400c040000820035603d207402c49030031590702ca18010b09a40c8000242d03940304d0008540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 904640152 1250 904638902 904638919
    0x711010204230f030c0906041a040c0e0a1403060a0c020f0a0b10470703090603060803090d0201050f0d051302010e060c0a020d15050406240e041104060302 68
    0xd01d5045426100062542d01c03400f04001912018900042d9003004084007070721100003a40c51f081040010400c40040e426101d0034404603080c5c41d039861040c0098880340d501d5101d030302e0308024144440441c3c2508850040104103580b42410303a0f0014160fa03210100c607001041c1d08040301d80072400e0070801e80701c640e2540700c1d05a0030010400051200f600c00c150000c10001110b40c1c0300c0b6007a4288034070b10440080d40c0c07042a1000491b482e950390b84001ca01c2800d407540d01007003c0a64910380e03a4081a41030f000542610024803500d9418001c46000340750103001103043c507a8220001c1c000048200d4000e05100340041c010b8030381c030400d00644460300d100c0c18040000f03241140c461200f002c05a04220b00180d01c41c400d03840103282020680ba502040c450040c0b490610300d80c02e0000c03080d10113a090f00c00e040d140250004010300c9006803031041d803080d80c1c0401d070307000016201c0c0d60b41c410b1a030340b50300038030a002010310140214400b0a6442504030011074408442400850028200760b0006500503d40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 904641402 1250 904640152 904640189
    0x4061805011a13030b04050c060307030906061517100f14040f02070b011701181401050601090803120a02040306110310060302091c112d04020c060711010204 69
    0x9562100e4100c0c0c5407007400166800e0a54030303401541c80760884443c2c94890143e01031000c01c0409443d540e005118404442e80400d03a43d00081c0d032a00201c80700740c00aa19080aa41001114020a0b00a249018604003001c000c1c82020302030f88009520060506100c200203055409000d44170002058403481d203182c15a200e48810304e1240900d592140140c0c1810500c00c400041c034403c403059142c022007021038a900b01803500315002500d90507000c10399200d0b0b1440010300206668080354a11072100040e42c80e0a840b251402d441c001441e0034180320016070200a18a0080110f8650500300e10404070356580f0050090000e010b2600301504161030000291603c41080700250302900482140100c12942d6030411000ea115003c4d00581000121010b0345203842c1c0d80301d44411943c85a44d1840200c040b01d404180f141d800c1d0956000b03031030048001206558219402c0140030303003060342d003035140965207581c41e640c415000d000c44040105d10902d14490400a60544000d02204910704500c0400e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 904642652 1250 904641402 904641449
    0x1e0c0b090f070e0705030c07050f0313031101020f030d0b0d0f03390b13020d0b010510140306370609240e0d020301060807140108010806150406 63
    0x4038820204440c400d035080442c14a076107400e01440f0300c00d10307618903146d580c03804440042078009400c2203d03a0300c41d00e50440c0c00158240040d0034a5900308221140c41485c6081c440b444185400585043d500b004a20480700c5c03c001c0100e0340b0480b0300040204060211902203000c540c035011001d071161501d2403e640806611071405810401c0a0a01a0510007000d4103145400e1468202004060390b0010b1100003552410f010ba5001c8a1181c03a500c0c0620586c0114032001c00140b011144c0c580960018411490181c03041103003c421440c040c20704554001206c42203200242c10184203150800052603004c0c078902c151501e000c0550206d00380969201e602d01c80c040124050f40000c20342c1ca41020403000900300032400346a503d0364002d58284c20ba4401034400182403103010b42c02c1a2505490700158609000d801f00803c41040103102d03030fa2400003411041d54581001e9410802d80f0b0004215695001403100e030014000d251000c269404e10001400410455000124445c050103500c2031000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 904643902 1250 904642652 904642663
    0x8360610170709050406061203090305010507030b0a210510060906141315080d1d04051003062301030308090d1e05030c12090604031805011e0c0b09 65
    0x403100054600c19684540c5840611a41e04100110035445407200308480e203c01d8014540140c0603841c0000c0054480f17000403150940e045003640424031f00301040040060900c00d0f01c0d8000e80300c2c5000c000e640285e5000a2a43d0060711032501449010400241000d0703800004d041074940c01000c44601050144120020b8481407141410051400e00c00084254618070b000001d26001800081003502802c0042d00504000595003040c55181c200070403160030400840c0c5180c9455124802c10306030011845800ba8289503000303009906041c10300016035104424032040d294460004074440000100c0345407070751140f000803101403100300000002e0641101910340105212801e40c0c0790103400382030a40d080701900d1130300c800c0d0a08664200c40110710400217540c0002e50429450b00e424252840359030340c03807001d40b459440740c2c000c00c0a0008050704404890f080310080003200c0401c0f858100042c100103400c0b029050300c42a6220b40880051140c8980d02009030301c1500d1420314200700a81030f03500c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 904645152 1250 904643902 904643911
    0x708090a0b0a2c0d15090b0702071a070201050909070c0213092a05040b06190509010906091503020d0e0a030206010503010f0614101709030a0e10083606 67
    0x82e20310b0212514210150702040d02403c4002c0c18180c00d14807036555807003840482e42070402c0c5480e0f9480e40c1130300050902c00c4a03409842564011b02070300d4141300d1660000d02c1d2600c4201c1e001c0c101000100c005036080001c1d2240c201c4120340b460a544d4038404190b40c03408841714004e502074002c0c21158104109030340035090850040795419000300303035a1740491082860f05e0107105501f014003010840382c40c20f0f41204442c2107006c1c1505c2c3c10704407050f00c0300c80800002585000810804600f4140300d5a0100501000380414604060218500100202c0748600324144408050700080c0c80640d242c11500b00c444222808002c9501007009400d009403542030070b021300d82c030035400c0010003500185140200d200341c4801d075180d50703400c1007502c042010100b199036a11090112944144034103005014202e4031490006010316541c040c0820014100c0c0c624100c850b115900120162031010340c0400c0490b840314041e00c1c00c4082d0040030500d480f48080c1c004503001c01c540c0d03c1e09071001d10640442c080380034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 904646402 1250 904645152 904645187
    0x919050903180d03120225080a030b030d0504151e080114041505120c0d06091a0903090d050c1e09010503070e07050f04120b0402010207060906050708090a0b0a 70
    0x2c480408100055018521000340001d040c41c00000c03100d04055004104816134052a0751071000b00c0e0111307011250001c401a5490400413030b40d94502d80c4c05000c0c0c1950100c080b0050440001c090601401d81c1c090350044040503020b80400c54009402002910004640407c40303001ea041c1601c1d00520804090190125a8000e843d0040d11404e10303000301d107207507030b12402100a01d0b81403800f40007103840b5a0030020760503c6030030b941c00100e8a03014104c2a4060003141c012449144030b0604c01401c00c81c50315854040d00c54007040004228021044c0d035140a070446241070803500d5030411528003d2100001a80a6007034000640c0340d0030251000c03041030f40d050300d50079a503030703070307860800d6111300180c407828000349100700010340050b1244000342804210724040900345a2070318070803541c02038400c07000c46403003290f0b40910044d03603010003110000302820f10309580071a06010000303020b40102e80000b0502c1101207100d1196541e040c5072140940903031040180c5070710f022400106500300d6035001034003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 904647652 1250 904646402 904646437
    0xd02071202010e100b0d020a2306090d020f01111e0f030c12070602070510022710050c12161e02030304050105180901061206080712020919050903 64
    0x10841c0c0180a4007401440c1c2d840a080019070240d0060003a0132840802d5500010361351900c001661070400c124040c20b01c0341c8841107454101c0e20038409204074104514807a2605200003050303603440c2d26503580015410f950008504c0c00e00030040e01c0351109144400d61a0084815043d03409581005600f200300e8910100c602410340200034036200d1241c0c21901320a504400d5500c01c5154a40f40184403c2e440b4150061070040240c5949041104400f88409a0340c1c002820b400340301407004850014165400424000031003c100050044d00000060402d205021450707500f180400c3c0401c11020004c005c50640d1008050550a110384101000b1520f00c940f118480c40c043d404494840d0100c0d81c0070b0005d51510f8200001500e26400c202d184035400015004072400175100d280c040c600a00c3c6039140c0b529100b6880b5103103000e484e11504010304550003080100502d00411140080031a01610f5198240d16850140c880a01c4074005041007281848140801214004001c08001c90303140308462 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 904648902 1250 904647652 904647683
    0x507020d090b030f1312020105010911090924040203090607090f0f0e0a0914011521171312021f020c2b081e04030b0f060301110d0207 59
    0x46107110607000741e2034080000c0c40098210074500f150144c01034200c03d081c4c84500744c00c1c1d4880741d02e000f00780d03e2040140d44640040001100c81e000e400c9081c11001c3d00c007800c25001801043d4813090003844a0182031691005440c2c0013150000f410f986031014005640d0f91500d07645043e903541c000c0c0e43e00000107111038400601d031111a1902c1056402c5c0d01140d8465524046101050b200090041d07001c540d03071005c1d088002200b00645804007034010b000030031840003c104828a0184c03c1c0c1c030070440e41955204c4404105801051400c095038043d6080d1210110303400340030118041c080084c1e151441002c00810b0000030404405040c0348201c2d024962200c040c500c1301c4800c0d0009000001503440382005510510342141c0409030001c030349999000d04480c0e070f001014691010002a560b00300c0000f14414000e840e00e1844402000ca07915940c0350602c0c0d41c0d03440c200080d00030965200f80d9840008a0f195641c2034015001e082110b80005440d15100710101d00258462081104e896850b20f02c4070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 904650152 1250 904648902 904648907
    0xe07050702010c030804171308060609070c030e010509180708180c0630041403040e01050105070204111303020109051206180712030509010f172d18060a020f090f01021005040302010507020d 83
    0x34dd208210740d40d80c0703045461182e0b6043d1203181034543e01d2410712106100080c2962280c41400801101011050740d0ba4105070714080d2105c41c1c040c00c0d00808000c82c1600c01c00b03070400001c0c0015981c1e01610142d984a5001000740204088a040d030414110a404031890300f246000985001e14004c2403050300c41d4480c0d004a40d036030b1146116201e0a040b071071004100e1513005102a0040230f00141c00800c001c0d00f070b000341040030340c001e04c91042402c01a0b04144159603000742c6110140205468140c0c42c840c8200219598140007004140084074128024100c403606100820041050021141c9010440c1c03034040c143c0d070492980b082c001500212004c000307512411403892101039042d8000d00760313290700070744400d0b4041c0f84060000c82d502401e211030764000e00700212481004140712003090700c00070010316400c1800180141000350300600129070800c0c401800c807003000408940140c01d1a6265005030304044500009498851801c4104018560190012071143d6040c0d03081e10070000c26801c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 904651402 1250 904650152 904650169
    0x1404050d080307022404060e03090306040516060c08041217450f060702150901020d0207080c040b131a092802030a110706060e07050702010c0308041713080606 70
    0x601008507094401b14003c03c000e540480c901881c0402520301e04241b65010901d0200159000c44d06548070300c103411900240101c0203009042a881c01c40c002103000e844110f1180954051a40c8400d5480307158410000c00d0040026080800c0b1035441e1100391143c040d07100c0031403a524030b40d440c80072401d0700305100504005040c810003541081d0003a4004450610130f90445200d2803d404c80341c01c108103409680c0c0c452852541d0400a00142d990b90f8032031000908150a4a4200048d0741c1f050005104949020840781c8002e0420349000800d14111130004001c0904c800c403c144e205c0c0b80c031a00c24941140c2c2c1d4055003422074240c0e01c2008070b4848844504002a521780303080e202440e51800203c204d44280c00450300810740d0792010884034a4110910802c0d4020703401210850340d1804200100d802034240d8550217000c40c10a03030b05200c0c1c0307500060a44010303420028100108140050104550700d00003d81c0d000e13490750455201d406000729802d00c03510500440b42a8031034000000c50310320b00f02a6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 904652652 1250 904651402 904651453
    0x1f0504060905121b1912050f06130b09150708090c0114040902090d06051602070e060a0521030406020c03100603020a0513291e03030a1404050d08030702 67
    0x80407044c0d50b800c0c1020102c00907214444e840540001482d00c0d42c01040340c3e02001c0c101103c3ca000701d2584500d001d902d4108041d8904100303401c01000c0190700000340c03000022040c0c01a5140180303665074030106050044054061200314455000d204943d03900c0032000c0c1c820f41500045691002c4410b0054503217507545104a8007043c002c20040c800070070240c000c0d020160b07000d09070f408020116a91601624002c44c0d4400107654182e80c0c00007510f03410410700c0b0040c04188000b49950901001054130300c1018044c15000701c003407000e007901442650402484080030b40003aa510349440b00ea0007519000302c40601c07840383c400c01c0e16034151035609225000031664014107800c2083d1621040c0440c0ec50380c5a00c04c5582d507039950b00310b042501ca01c40c5130800144440e4034404691180c6041200320441300c0c030f501000c8480d8030075503e40e64800000301c03400e901960400108500404030031460b0b5114a410584d00441009820010404080b02075400f5011580940b00b5014412101084807201180d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 904653902 1250 904652652 904652689
    0x61701090b0c0a02120703081e13030c1505010b0c0106080606030d0c0f0c0905100e161d120a1109090d05090d02041e0b010201020a020a02040b1f0504060905 69
    0xca19002c080d04010402d060450064400c428040c00400310103070014a8250080380f800c00c1007100c20074600641c1c83e070001d950003405000b410b10380e4100590031606000102842010100b00e0288000070000d803101a80e001414805980c450082545035002070704296059802c00301d01003071506c00400c2d40b520030f4001034014148c0300009503003102c2c846410b100c00d580a8405540000225081d0b400000242400000102d0b00b0300b00040014494071403548409010b060990900c0400b02088801d0306150206160003030000a2541c600903800c00e55070b400130f9028403400c40c04480482c000c20141170711402030b00d002c5840140c89040c00400041284c80e442107401801920514900510152140d168060034220030f903070312039010900312844201c040010390400c000c0481d14061601502c5101d1600b88000d504100d0040703006036540080140091107641c495140d100d039900c03440ba1600d0320480c2041c250f09605402c000141403030b4814000c1c0c800260b400384004c00d035030521580c00ca800340e401c078 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 904655152 1250 904653902 904653923
    0x20c10030204150921021507030c1e0507120302031b0102040b0403051608010b150a051c090605090111041404230702070602030301121113020408010209090a0e0a12050f04030606170109 81
    0x5144842c81d62310520048081c80440c04082000c580c2050100c2143d000d4041d14856112990800602d0000e4940c89000700b61300c070900c400c0c0085d0380403080d00e213203c511140e08a901d28103108164060302442e0400b80150402080005c10710100103051070740c411403013450034070064507130355030b50f09844040340f21903000070f1560826080c8030049002080ca8850502d4041c1c24012800c1420283d140204080d010b89512400c400d018000030b0301c104c0ea001001840204003200380d421904455000d00c0c410102c82c01d18103c054009a241d54025540c4030040001500302c0741882c410305030808000791040030061144901c0440c5c41c0740000100c03416603d11105000b8201c1095441107074183c00e4a0003142c10980f1a44082102e0a841c0007138000746c07151030005030301c0c1c1c9181d105118040303038000c1c81010320600341465001d1007900801d0180141e5002000c0c403800000401094801d442420340c40d094508000800009115955000400350b5540b040200b68400c2400e12440c01e0b84d04d000700c003a04d82c9410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 904656402 1250 904655152 904655179
    0xe07050f01080a061208040501260106050d0204030507120b1302010203090603040f0f0507091103240102030f03010f091107200a0803030a0e01110a020c1003020415092102 75
    0x15503202c030790140010f0000310780316868102c81203283c010114225150704000c6414091584c001020a4000107002000c055521255401104441041c0320300418000009403450b0b0031000c0d50115005980c209040b0f481c202d548040300c01c22040c80c618160f03001c3d280700c0c0126000d981441c1d000408076405070700450808003400100070140e800504100c0346141020700e80800a040140c2410046e40905e0181140038504034001c801e4401140d030300d4041200c02c0003002203820748562065001384450200071100880356005070315520484800c2c41d40c000c004800003031f4140c55071802405550802105002866504107103030054003402400420000540d43e000714011007a40b800641214010020b80249a40b1a1000e046a0040c0c1d4180d05603512820304007421882400b0f1010035600c441c0d5182d190480c22080217403550502c495482c441c50804c11005600b500c641c041e68060b150029410302d0030552018068071a40ea035200f694450214881c0748151607145032600041a50041c1441a19082 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 904657652 1250 904656402 904656407
    0x40303030c022e0603121206080c0102100c0203040506040308091005160f05100e03040302210a0605070203090604150e0402130b0d0905070303080f0c0406050f090f0907030f0e07050f01 81
    0x1500c810f52012555542000008216003003649104031065489803c0c81010800350303402501c0c0070750031a103490790050061200d030b81d0b07000608500001148400050442c9006412421032003141e201540c0711038049404001e1000c6840244140502103c0c04021364048030001e50b1203002e91100030312052164614000070034079030f1700e203195030b18801c3d4155014040c80905170030880e200c0540500403648007180038021403c10700c0b034100d2017215044c43c4000e8442c42c42550359480c0607551000301901e45071404240e18034000c10940724080001490191a283c84820440381c04100040c1100000c02903c10a44541028400c40e000120b00b11070004045052169a441540c040221512300698992281c030210304280041c6c40614030a0366002c0003410808841000b50310050b000d20703c0e40c54200020041c0c00e41000c122280c1c00c03e80b00308152125455000540c00c1024a6540741d00301d0600c0041020541d415400503800c0d001d201d008000c01182c01e000d140c0e49450f20701403140c011901d429107144079070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 904658902 1250 904657652 904657723
    0x15160b011d1b0403111207090f11041a0a03090515040303200d021c0f050f0109050f060d05031c06080d03020f1806160b0103141603080c03130b040303030c02 69
    0x36102c4074941c42e100e00d40e41d147c80c4c0c050388009000d40d6071b440101d1212103076001d240805880040b505080c1420300000c403541c130807550090f150b82500000c4210085007c1e800203800749801c1030945501a1a1040403c1ca0742022101240042d1900304050030203075150081d15488071440705410301b82004106c800009600c0095902552035a0444101c1c0b0352a10b030141e003000c0740031040013117210705103048841c01071201030b001804a14240b2040102446a40201c20b50101040b94241503640c41d504020341548140020040b040c50b000c1c103440c20a44540c1c010b44100d4481030211440c036192074200700e00b01c0c065081200ea51030400c10217801107a500c107c0381c40d1148402054585403000701600603200f680700c40001c8402c1000140100107200b614001244014000c401a1124680c3c50009440c00e441c0360100401005010640d0425603104000707680d801180c044440c12015240e020302c1076140c0040c1320840009003001e4080300c80c1c0c4d10108020703c01d6407000304405614038015141c600d00c02e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 904660152 1250 904658902 904658933
    0x302060105190807030c06350c070f0605060a1d0a0b01090b04031101080f040221190b0603060109110a0f050d0609140a020915160b011d1b0403 63
    0x30b032542d4002007039040062080100a51185000e40c40b12450910050906400c24000c5929032001c0286d200341c0d0000c5001130700b5250000b01000019580d24103000280c3d0140e400d02401c095240d060702000c00190f03504c2603000d540106e400c500c4856032144041030000020801145403400700000c941c40c1070440d00b00402c0041c05062048000e030310342ca002c000c02c1e002640255050f1030301c0d0510b44d40d9541c104113071a420075142c0c1070445441c54a50003103001c080c1d8881009454003c1e11201c20072414040c1702001511034000c05885030380c021410201003440003a0740d1540300303000e66400090310170764501c203c100322070a283c0c0441c1412030030318041c0c0d08050545200003d100d01003000a150f00c0c001c0c41664050020501c1c0041d81506404844d43d1100d8010304003038560340b04005035041a9504160060500c1c00785412964621013001550078101411800425650307900c000400d500d51800e889010109024106080c2590307100201c40210165070400c100c1d8550401042c4041440d61f14546140c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 904661402 1250 904660152 904660189
    0x50402030a120f0f0503100b0903010b0a2903090a030809120301030c08010f09170a0e19061e080f06032d0714130203040c0b07080904050703090302060105 68
    0x64034510303150150301d02e42c401410740000c0d600101180714203402c981e10f08480b03001d600c1c0c40c60440c43d012142d007a1359075041c00751a00c0081d001c2200c184595094220b0800d089014000c12500b95407141e81409541e0554805440c941c00410321064041107031007aa0f2280c4582d42c001c0c240c40701e141c3c5003541e4000c005007020889001c0c1c0c0c421a109000c0c00c80c0114001d5100322964040603140919860841e803940300c0044d0710038103102c075440c0401c40d001a540d0700c0c0003100105680c2e0b92184c0c01c1c10340344031010071415500328425081940843e1101000c0b80120782c0b5070340711003070780707403140107928010020304c603550000304004030045049000f030b03001354030340c000800f504641e030a845075185081282d07040001c1e81051442600d0040340303580c040c000f00f001405d516418009a25a034800039100c82c40044100c454581d02000007414814012016402448651500c035982c1c1800d080c1500079130700107071000b4069410000480c54651003446003096503a01503010b45981e90906042181030981081002103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 904662652 1250 904661402 904661413
    0x1110405060c100504080a1e0c080a11010908070516030506010b03040f02030a050c01090504090305030a0e0109020a080303040317010605030610021e0a0506090303090a0f0c0317070203010b04050112030305040203 93
    0x441903d50303c10640110b00a80034980c0351030303101800034508030300f50307844103405440814004403440e000010516129484100d03da2a041280000c580100d035850300c3ca4807540c2031064203428400c503540101080e0b4011001d480c845a00603542d6004c03800c003480010101d622080040082c2d4a03440d025507000b07442501240001c500d2500000d26068280006540a8100900098481d030708280d401c1d000740004d450511207040300e524041d010b03010003001c11744840c0d12502a1121300b4429408000d13117a9008100c0c2c8405510349201d103030340340c208940803004100c01c4c00034854102143e043d9641201d2581e07448620310b50703a1006009400c210f03414498103601c51015007074007482940c680a28165005801022240c1075400c000b4a8030b100609042c116030401c000b4405640000329003094195041311200618107114500040d22801e0b540c000380a20910010b4002c403041940014180c40b402100244404003401c0c2c104400c4400070b100d107401c0c3d14010b0400c903000038083d8000c02c0c3d1282c0000c05846 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 904663902 1250 904662652 904662673
    0x1031a0a0204030212030c010506011d0111030c010c05120a0636020c0d0e1806120708060112020f0102010c020601120206041a03160e01020c06072f040e01110405060c 73
    0x83c105d220222162680b50008100c5a91440b02441902c1d80020309280000c000340c01840b1012212801051450402c4103061100961040400840d007040524900800c01e000404100030001c0d0841045a011104200c000c511444114004c003416102d003180503181070f0040e0a000700ba42c00c481d011100c8080e11118003406107004d0ba1010b807105035200400b82440c013084120003000a0b0160744401e03c22040d00084500d411095842140d00000584807203641c00480c0c4030191421400358001c0c0503500c01d00313001003584100c40d0000d042c03482c401e4038a40504900f0030016401d90f0000d460b100c00680c4450010080f00d00c041d8040382c9032074005880b107403506840d50146c4019100c90840928520030000901440d258030040071850301e0f01502d0103c801808120000b03480b81409001c1764407424005c1010424410103444e0003406003161220042c412500b402e00300340101120280a22030307841c00701c00c42d20008041c01507942c075040c00c25078986410708003010442250081041c01d442482a80c8103403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 904665152 1250 904663902 904663909
    0x80a0e010c0306140d1109130c0303020a02090601023c03031003030801080a050307060b130510150e012f0607030504020f0a08060403082d1005060301031a0a02040302 73
    0x210600c5070700c2c0d4000c11080e08100c025105128420201401014240346800101d0101090034044400c101c03600402600d07040120761407260400740240400080d8a0000308150f000140c41600074070a4030390800942e11800103a8840c3c600084c0b034482d840c1e12080c8422505a280d0903072107845008003c1441024003825070307a02e940c008039144801c19040031300c02d10070315401802e114011300e81c0300001d0581c40150341e5401e40b01d001d858401089943c43c0c200349502075582e10075100304074803045010041444d0900880041a00b10b208000b80388040c92140f45141e4403070207901c41c22900c180c45a034808903402c2e220001038290104401c580d100e158010611548007407143c1405080ca0b07540100d09410702d80100108104204032644c0304403c43c20080000320b034045513281d0302940600344251a9034900c000044090700042c040c2552a01460440c401000140d000900603a07100113071000b0191030f80103015440c8000c0c08081c284a11520540c0c3d48201c810901e603070310106401003d420990f40b503010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 904666402 1250 904665152 904665161
    0x2030c01061d0c071707062a1713020f1f0c150b181312020307050c0a050303090603040303020909270a15090501140c0408060c0a050406080a0e01 64
    0x1649290660401002d182e40c02d10840c10f4101855101140c40c211030360b55107480d10341d2541241000e014002c120841030281d1a0700ca41108042103685015420014a443d40b00030a022030350300c0800d640ca40c248100b81e103100c4116110342000407400c1c00e42031143d02045417806454020a074003040e0001c151a901203c500c91216840490311001402e090503e0101d1507240d0a808170741d0814075043c144400c6a940d550b0404990030700850103006600c404600c0d21859000010107030003038550307010102e46268000000c2c58118012001d45050045a000b0810145994801e881d4503a1044c89031282501d0000c1c0155005071090a00603d0103184c50041082c0040071900124201110300c800292403800a0500c07079440303d080040c102e014010b5880002440003018181c144503550038860782000404d50240020011110144143d4540700910105c143d00502603403080d0b00520010030f142c1c40c085c0040d20384494107a1910380c01c050401c502280e056074014550080f6036101c620408980c40203105 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 904667652 1250 904666402 904666409
    0xe010c03050405190b010905070c06090516120c0b0a050d05010b04060f050a1d04020d020d20070f0b0604060b0d05040b13020a15020705090a020316080f041202030c0106 74
    0x40c00709003072801e810401d003072020b50301c0380001c0708045078200300005009641c040d054810144001030140c54012003250031521580c0c0050200c0d203450181401d000e40020708000c048101e6400d5080135444000745005030a2250000704441320081080c40b51b00010005003000d00060328020b420140036223240c900769242a40200e04101d40060184806540201611808a0b040c01c003d803801031100390062003845880c105c00201141241228020707a103030740465150000b000800e5444115220002c0000d01042c910440c0305898010741d1050f0510361410703500039540100c1d1211034283c0d913450700741d00380340b0042809910071b076501c00109490045401810700b01c0e21941e00020300c0d1030b040c9882083c0c82d001400807444c1d00200d000100c0180d9070f051034001903995520003150390300b1700791600740e2034488560011644070b000700f0100961101c0660195120784a80100700003040c00168003038608140541e03052000c0e40e16900002d02050050ba05940090a14411285807203503403072003503003154480e40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 904668902 1250 904667652 904667657
    0x17070c060908010b1c02090901020c1f180f030c050a0b0403120c020c330304051f091505040c0b1b010510050303120901020405060d0524150d0e010c 65
    0x10010b00601c5024030815504481c259220420703008580c100981200c581030000344544031003000100c0c000c0080d0140c076040103c85045130300e68000c40003400c0c0c00102703000041200034603206001d00c101f10014580790580d6001010b044003a88282c80803610290a0700702901c5a10034a104400025018209503200b075000b81c0d50034040d401a017049070256130f0744407482d0045500c40d0202420a0b680d011309001c0c134218480554504400d58000d500c041005060004a0710714040200030911001003400c100d041028075a8903881800b207241e0f00e0444031035820241640301c84216211036080503a101c55002800703032580220840d07840601e520264011074002400c017940c41881c41e140402401041d41001074002c0f9290b080b420f04000c00e03a0790103850070804960100f040810540042941220060240034110540e5400c0008803040549811784051220440744040d9060000b80c0484600011800901c40404c842c0d001d141c004e16070b0002c0e4085130340d617603660320244d146035003d120f12900021140c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 904670152 1250 904668902 904668917
    0x3130f06091a0106020d1209020904030512010609080303040f060e070308091005070206030406090201140a021c110c010302030a061d0106090b03220c0504021c0606030b0102030717070c06 82
    0x91514000042c81040681202c07400300005200d020b0b000708030700103004500d05d131510b004004215404003405100c1006500403050740140f009250707010005058800d24a208411541d07610b41048070046940e1140c40560f800c140045000200c0c11001146501e010390b4012440c500d50012080c1414220f0f031086400e030788002030041c1103041041403d00400d159060003401d10603144c001c204944002040241050b544000034400c6a01a0360b0000349804411240c0f41c03074003840d03440695503003080b411182c0c800030001c807081082e0748210240040410070750050311240e1103c10054000c0e40000d40451041d9440700c02c0441d42e000b1603400040d841c89914a4030f109945840c130050b10b14800c030741014200b8141001080b91001046690b840e415000700170352a4500002c1c24132000030081500f01540c045d00024246c00880b043c510381d00caa10800c420100090340d030743d40c0305508940440b030015026800501000011503c1c0d4503880c65100180300c0107524050140da2120b5507507081d5088200840c0c0c16 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 904671402 1250 904670152 904670171
    0x50304150f090c050a0e010b0f0c030406030207051b130c0908012a021908070809210c030d20010204050d151802090408090111061518010609050603130f06 68
    0x20050f00300400060341d800f02114140142103680280c140925a00c11000003a507511145558013124001d0b2a40005c0c1c0752140c0d00c80800801a500801c2c05491521660001e12000b1f500d4488080100c10010820080c0c0c41e07088400070040c040001c1c800d0140022040b001524800030700803d031085141d14841d510880a004001d400075800402c2c541c11903101403600c4090700005111130a4480d004400c0584030000780c0f4051400b446030550b01504405808800081814400d0041540484110a075080e0a504e9818180d8458840003403c0000c2c2120003101014444004110440c210783c030009454280c641001c1500d4141682048808416403068110035051030301c6107018010880303543e001169503d030000b500c5d440021f0400381401000007030b800200e03070040e01846014004407080e00e5181ca8020006441418180d445074020240300c071541c2d8400404003900c605a4180d600d9407135156007071005001007504000c000b0240c180103008060042480403040d401c40d41d01c10040071a08454 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 904672652 1250 904671402 904671413
    0x30601120b0108030412020111101532120f060f0906010605030603030a050a05070606080d0e04020937090b04061212050a091a04080f1c050304150f09 66
    0x103050340160f00e950401c0c44240865504030541d00c81c02034092070441c140c01d000c10115410310f0b04115070107000c149004c0c610903400501c103851000721070340e056801c0d802d80103507282002e0388680301102c182c1d4004418030100003032a0030f800c1103010b00641c3d002c86c0c1840880b8030b174652400005030760725411207c400b41049080c1d4810085127014040c03a1518904500780000030a030f590150030303440f03400e024001c01c0c020758180c46101600c3d11550001c2d0140f140c01e60380e00705240c03540e0310f1000400001c0d0300e200314107885050900072545d00031000717003034a00c00200758048000c094100740d80e8206102c00900001740120941c10151010740701c202c5000484030114010441140d0160388440250001c1d44854404614080807800401c7e007141415540c40c2c00300003040700d12020603086115080c588659141c48039aa1074040c0080e5501c4c001210a00031000c0141d980d0307032242004600340c132101c40385414250b5101d140950b030047d00c12002c1e8804001c80e40d64400030b650103446050b80c040daa40048509000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 904673902 1250 904672652 904672673
    0x120f04020a170604060c110613150b0a09050c04080d121409150a1b120506090903030415021306020105090d08010b0a050c030d1401090b030d12090201020106030203060112 75
    0x5850300c0c2a51105030401841c80d11018000c10140c0801d42e40d21074012042c0c055801510400c880c80c0523180c0d0351400c6111404004618881600c2c4001060040c400d040c1e6148241c2144403801407c80920501d0009560080e100c0109864010700f400c5c400010f80f0082080000d44820258450300c1d40455000c0c4038108541d24042000285105c0c0401d2068420000c07074601d485d182c80c9441c0c1c2c0d00300d90764603441001030b1110031105041f80c5d0340305048684641d80095400b2008880381c10030701a0b600c90404200e950340c1d0070795881300b246d001003001c01c00041482c07401300006e030003141c0d025050250310a00104e0b040304944c80040903075120410041200d006014910100d200c03407c0c206003a506149520f003170b0780070301d61000d001d01c040000c00f214074481c10400c1c3c07101100c4022092250485280011090034828443c4515403800c103808035940c2d00d004240721120f1291903950001c11211441854064803100100ba81035558a12010000da1803c2c40300602810481c910f08500608920304903040c030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 904675152 1250 904673902 904673909
    0x60c02060c09060d140108030705070f050f010c0f08030a050103020405060312160f0c031b081f0b18091b030604020a06050f0d061410030207050709050c120f04020a 72
    0x641154003040044900c4805603038502505a594607128201d40c481c13100207110b001d00c146181c1c02d882c0000510700350000700410b0351a20503030030745540726607400d40c401c401c0b4135500509501c110781c180110522b51050401c200100c0c000c030070a0950306000d84603000c89a00564455041c00d40f075800520941c1458010240c007c00154018400b401e24258030840c1402241d18614600010b030800e40180040166000404c64204650445e256a24a400c40c0b207a030320790001d0b1100c18018400051005404180c4640b00420400015030030703150110b80000501d918082183d00c290780100e001c80c40081081510300c40c0d21000010709038005020001d445100e40d201c1d28038443d81c0800c08000050302c0d05407191046072305504000f074540b041c1501c2d41d2000d000e0a143c640400f0720700070000a03417504180710140348031004d450403078219483c00003c03010380c411180007034400d5000c072208101100482d0310640c2c3c440c2050802e14240500441c400384803400030b49406207034807400d105100640c6040b24420008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 904676258 1106 904675152 904675157
    0xc020f18090115050111030a050a0c1a04051e070302040e01020903030c060601090905041a0606040801020703030f060f05101d120f060906070c170d0c0507060c 70
    0x2406040c105011000141e40f0000d880c0d40544403007506001d00300091403602e00050826a00c030341c48005104104036603a001600843d081a0321800c030359038031603041d00b03075410907080203850b01c96003000d09905032104000d08142560001a001e081300d5060b035020a40d280407099140c0280209903080360103010010703503007d20640105507544a62000d0f290364020030344540168003102e000b154024440500805050300d841150720741e15034000b500410301407402d80c0b28801d240c01c0e80c000711011070100e600d030011010582010700400d03016041603031222466501c3c1400203101294526520340610000c4207541403240e100d11134801a680014000000d00c0413890402940e4094440e480c0070a40a0140800e0100c0c00118a050094030255107518044105840c0c1d40c925400800c40e03002010010042c90a00c3d103481d0160f100c18031401d4903819220030683c01c00c8020b80f904100e19804 = true := by decide +kernel

theorem cover : BRFrame.Cov 904496402 904676258 := by
  have h0 := BRFrame.cov_init 904496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 904496402 ≤ n) (h2 : n < 904676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
