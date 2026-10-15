-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5216
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:07:37.622275+00:00
-- url     : https://prove2.me/submissions/33fd4030-c4f8-4563-b85c-a92150f4de21

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 937949640 ≤ n < 938129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 937950890 1250 937949640 937949657
    0x9050907020a0209060d06090503130506030c030a0c0e031c12060305070506180a060e192d0e07030605011b0b0a0e150a0507110a11090c1e07060b01 65
    0x18039800003085a0040d50448004159035a00c00200b00400100040a0043c40c1005d51405c103020002c001404d216460399401001d40344c84005001e600d2000750307a00c81600d082000061f0702d01d03680d0b80c40000d40305170030f1070013072403950200d80001d10f000300c1540e030411820351403100070651a070004d8140314138020404003888490b01d90380342c064a801c013038401c01f1f010303100000e011a03a0344021500245030300c00080501c0e000540382c480007000c0d10102084540541000840c009100407551503410071a81701501041840035452404400340c1c203107a445240b0384650300000316104140d03407802480f07440946e1300042c0715894040010725566042840c840310820034000300000ca0395031440d49501880900e030118188c2d51058032203140c4811409084100400003003031102e94403242e00114002c1c940c03503640c3d0004c07004581c42985c03603e1024800030205010980381c2d85580c10710010481d802030502c07403520708001e00c1004420311003402412020780c0100c00518902080340d94031484554003002e1030091007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 937952140 1250 937950890 937950901
    0x1509060e040203073b040b1305070510020c09040b1e16030c05070501020d06061214040f0203032803060b1c0b04021908040605010b0f180a1212090509 66
    0x48548284c0101c2c10000c0080315204483c09034501014034400b0155480030003011041c1c50554818801d9800304d40540c40240420164800c120b5078234502a080b1006d414035070700e450100284824295507030010348c020304000b82d03203581da4014410321a500404000034240380624594146400301a40010070003845810f0200c40c42d66903078501156606802c00044d12440c844c02501c15008038480103259600000d44060300510039044807088504523101d100c140712031000f000094901c08a0400c002d528800006170200f030345603480c4000b1f6070010782500c0c6040704582000101c00343e40aa00208910030700441e4400322b501d40708450007409601c800394240901108240c4809010740545840701c0d403200c20080c52555542e04a03400c0034040c006070b07441c0c400c00e01c1000e80070000c02c070360944230136150000000b0794500c0c48003100c00848414140304d00e0b1a040344841801401090610b03904100b00c0c05002c24444c4503041c064117010b000e141200219041c01a00501a25050b001076004090311028400d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 937953390 1250 937952140 937952143
    0x71404120b162010020a171008100f021201081e060f010b1b100b150304080403080f04080a0b0603010f0b01020601122f2706120a061509060e040203 65
    0x1c043c002c9048800050300d48199407600f0b44000342d410f240f0707100048120740242c100900020601000500d01c01c9541c980e2480c00c42e00f80c1c00c2c031403000980c02000303803985907600390340c4118150086100014102a21807408100e0341c48d090b0440402d41e4045602d145540c1040d500501440c41e1241c020030f0103152030342081095030340603c20907190f82c001250a80c22220241100090700481070704803108160844646130242c21140e007140e00400c203040485e217940c1540b0046138411754118451030f282a00e1995801100d80c010508221000c00c2800302055035001848200341490081c0c04200d000c0c1401e50416003101c8454140c038044a280140f0b9a86592700864850f0468484111001c1ca04510b410f040a00301601d00580025001082c110714540c000600507051032082500c0c1c010502d03084d0341a20000305108224600d49100c0f41c400221780780f80506c40103081e5507440c42a140f22201e1640c60600b40e80b11040d1200e00d02040c80c0c01808001003901c14000100312800316150541465000300c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 937954640 1250 937953390 937953407
    0x30e09130f030c02030f0d0905100c0b0601110f070b13090b0a05010809071e06080708010b0315011e0309170f0708130b0f0301080613080a08071404120b16 68
    0x30240400c0c10103102c107655086c08410200b00f8200240c5604ca050070b00010a0f40c45280252442606141410340900388903410f07402d1030640c09030040740c850312644015200850b900c0c2c841245489510907600903a81305100725001480ea2900c0c0a0712402c0d404030382c1c3d400e0700e01c54020461b1149481c000e4a6540c1d1000b0091085500a0078140655155070034424242200f540080d201c0004441d032095045034411808000c645095031050150380721400115070032a0207104010152406001264045240c0f400300444082c0c14107101c443d081c84c3c0915658a1451000c40e5804a0b598020404c18060302070b01d010319600114042c01d145c070402041c58401030140d5017010b02020008680700d050104210300c4030025041d0a0050380c2c1390b080307001d0440d600c0e6000b406007040e1030250001150302d600b90b1046140c110f6030321510150804032802070882e50480010056002c11032624040080407540000400203002100440c0d44400307010b042c4040302c0b90010303007222440403e5500081546901c090513 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 937955890 1250 937954640 937954643
    0x6011d070e0a05040e07031104050709140a0f080f0d1115090f01020f0a0e010914011101062705010806130b0c0408060a0501060219030203030c0903010204030807030e09130f 76
    0x40012080d10010400010b0540c209907042858a484192501d2000541204481c80381c4401c1c0d40002584080c031040d00d405035a1000850040c110511a8441840c243c00c0046809080310810b1980c41c142c0f003040c1c80266104601d86d420003940e59250490612045107a00130700d0418104c1032a59000c1c0640da840d110701c40348400d05c02c0ca00842c00840003170100400551161000355120394024042c020703254007c21318580420441c3d100c90240d03500600c0700c10200c880300542114540c05403001565a107200b01c1141140c1d551781e41011075160011503901d1003048420711921006602e6505081c01c4842c180c01c0302c081c030750090080080c1502c0300840d0a06a96100716200c450344c40d42c107950405402240c20440e41d0303000324810012104502d900c01ca040f0746982e07088405445c041080b10030041e134200c0b0050010381003007000545503180c94004004030749014000529280e07407030319903000680100804030000350100031007010600d415801d254000070f60700301480e0800595541e13480c42e05180c050 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 937957140 1250 937955890 937955897
    0x6030a05030315192d06020606042c0c131b0f0c080f090405070c020d0b060a03080708030f06090106020a0209100b070c060f0507053007050d0206011d07 67
    0x460b20104c0d00e41c03001c10450040c040c2a00200f00d5203d55040c0c8480e41c0480d00d84821140403404070000c5000c03c400f8008440d0b164001c0c041540398038007800064188480c000e0200712440943e403940209040d169464000c0f0352003e402020420401c02a0f00d60f6501e0003000440d0074201d00e00310300c422000d07440c000300b079450138401c040e040d07450004d0300e1075905803030050f0079007102041c4070f4901400d0700003e01140e6011074040086981d43d013025962042030000194005549120450000340d8002c203003500843c0082942c0300031540c84c1e403404000e070b00c20072040714121404006d01c564460380001664002c24103c5240400d5810500025928591000003902c0b6442041c00f0901080c424649034000e8100460b100d42e8074421400e00511600291240700300055415090074061840399050701d02065015014060403101c030300c011b5a04401b0080d500d00c940310180d00c2e1640c06c07048a00100a1184588040d04913410070b80d1010342851b00c164000c06015020007503070601d80d0f4000464070342c0080d0505 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 937958390 1250 937957140 937957171
    0x60f0f02070509101503050610050c0a030311091002150105010f171905090c0102070506130e1b07050f01060b030118150305370b0103030c06020d0c090e06030a050303 73
    0x1304210b0907484561240041c5ca14200003d141c3e1981600003c1c411030f07080d9050340761200d030420203c40c148120b400c101701580000c8680400a88650032503407864080081ca541070509000c0007a1401a55051006c09030b409410010f20218080700343c140141001d003400304081c49400320103000b4040e1980091000401080040d01070594805902805c510342001007000340f4121840b96034030b81d200c01500340584141d920004480ca400d404841074240d540f04644041c0d440c10740d8004019070040d104000c0030740f6080d01588103052660261900f24044e000600402c000d101805084814980203020000c00400050051300340c40b60503c0e041d17001518000805d40f4003003144400310708098000038054011403c00c1d914048003545421292034007001d10040c40c0740c1071500c9a00003110b4410080c51405040010001720307006590644026010313000152610804d0b9510074200ca000005080100e0f14162080c0210b03c14120943e038840c0e0141c00a01d02c000d05038950659038000140b03a80320000900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 937959640 1250 937958390 937958401
    0x4170a0507050d052a0c0609010c080d091b05030d201e010c030b0d03030506010c140318030c091b070b0a0209010305061801150c081201060f0f02070509 67
    0x48045944440c0c0107020b980014481c21001030095010007217400001c415144265030079035214416504205142d00181032103200321082c03102c0d541008681d503040c001740055440208604100611400d922210002813050b060b24100301100301804420542914075078080c002510300207074609840f5101c0c10405203000c40ca003010ba050303c0d502400c0d80c03102d005a00109482d042c05044640d4040d546c5d0300244180c640c0c40390220200c0f000d52058030340c4141070000c0707a00868001d900107600319006251107407103001c0315242c6084114002c80807a01d242d03c00289844d103030102c007854404100048003d407080c02c40310341c000342c0201d4018100d070004d002c44000107205c801522007102c040d0b550100c9040c101d8544030419000035088600c2060100b8202350000720185440040500019961400205564245502e0303c4540b0051012901440801c24006000c1020040602040c8980d06489007a40d814160000c0444105803c0e90092141e800301500443d80c0100319001592001d40325032031540e440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 937960890 1250 937959640 937959647
    0x90b01110f0312150d120e01110309131b0c030905010305060918030c1b04060e01060c1101050d1a010914030a140a0606030f0b09060118021b0d050a030b0904170a 71
    0x13542c800d940c002d000d0458501003201100c0c1c41c1d1b2600071319840d0081140b14010041d1750b20b0b07005400001c0c3e91303041005640554980130f49280c07108140090001a89840000c2031010070310b5008448000c90030700003c1d24100340d40511214040c0c10286000e02560804502043c4011005000c400208040c0d80713030852803400400545440e001d0304011102c00158180b10751013200010102d16000354280b20b80400d8a5001c104068102c0d50a135450050400b9182c4440b503115500e00e04481c1008000c10203200310b9016400b82d102c48100e500f03440340307516030214001b612882c042d40c048070025650300c04441550f0703404074001c0c5209800256814081c00e00700c0d17080b030a280380b09200414451900b5008800e200fa51001c4180c510721400030b08290707445d0084000d607241d00c00d03c907000380d0202c14a4440c9800102e070300501002207441d0112841c40daa041c0d0100d003480000b9074543c0010300d011500e03a02d565454020007200312402d40f00310100b401c250b22482c06032641b00d007500b41440030005110551511 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 937962140 1250 937960890 937960921
    0x6030106030e2505030c15090d1a04060c020d030c0906050a03020d05090a0209070c050d110c04092406030803070513080d0201090605061008060f19090b01110f0312 72
    0x16040c0d10101c3d401c0e8162110042410907004843c060712900060041300d007046800c1020840c001302c2481d0410520b8001c00c01c0e4070072400e004842c5225040075441e103200d58a1992405540f0890000c00c0041e03002e20001d2800c0d5000b0f42c0078040500708071881440540000e80441940c4042c07500582c0c494280405502074840d0503104000390f4076200401c451200f0200781100598404c60b41c12040d61900031040340c9001c108100500769400504003060542d010300e0700c0c03190794200b03d400d4619880c0700b18000b408903032a410080d19510744d0240c081d43d1815a005802e0000202244100070740c90458880703204a010051040c070034890f000859020b01f00c01030180000819107841154403c505440d4000d010b130070508401c03074a1508040104210785007800d40140c40c5c1d4026600d45409035076000c1003110851681058030380240958018031200c4488880c000090804814007251010749140018104003407aa0042d00075040071030740000a082c08821501d8807050911f02226580b541043d8918006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 937963390 1250 937962140 937962163
    0x10806060a05042301020c0102070617150301140405062d06030a0c150909110306040f110a0c11060309031603020c09040302150901060f060815031906050109060506030106030e 77
    0x4400325101c4800040100112004e48800c0c3d0079903d06008000059075544c0309070080780041800c80b81c04030035000c0d51040300b55200f299061210200101a400b203400c4480c4401010390108443c0200004d000c001c0021b590040950300c0460300c0d5421b05040549203400301140a1081c225000105480d580d0801c64907055540000380c0c0340540350b0300c4e80c50348121103c55070410049040810005080c0e906889864801d1258466062641c0d44000402c0010518446d98081059a032011803407144a0380d8090f01080c0025100c04031b01e1005403c002503251280420f40303104200800422a42a102100766901d41484182d000401d6080d4602030382450302080740b243d0861100b9040109265002500d8003282011102464040e151404410301307840f4103004004c07512404120800c585442016590740c0000400f600301c40c201201c1c00000e052039110742c51800a884055481c0007440100c0c07084500515601c1001c004c2d2929080118105010510903a03003450307503402c1c10050303d803014403048007400d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 937964640 1250 937963390 937963409
    0xf0702190c1d0a05060301090809041e02180a1e260604030306060e040e19111507170c0c0d060f0e0607090806102d0306020306011d010806060a0504 65
    0x305003a51004190600c11200f8118280c20440403400c14141031046451060300305103403900d00350f084000e2001500c010b0381c2e9009039403403540d4600e21980d880d101801c55000c040d0030020180120300100003811505070061054101004207848401200a01c0c40c0700b180e80300ca115903009012820b000c07000c081c3d0000f6081d00d90260a040000301035241e4009429500ca42d01e034200300c4864941400102e48403510310900580c8541c0501640b201c82d1403c10514034032882218a040c11680b0200c0c8004503c42d081c8180c441d40030418030f0401074429814600d07000d500c21990300b0541c10a295aa9804c11020054020f0034025444001c0c000300f504084420380c4601001e0212203c40c98400b40d690b00125080000286103080119802c8800310340c040c00341c103840d0710f03d0340f00e503003812406010607034180d0400c02c00c080846e0050040e03c0040300070074003e40c0078440c016140d2915070300251580c6110300b40e0010000420b800c848190781c020070701a420150980340980c81d41c0c039028007664248520782020120 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 937965890 1250 937964640 937964669
    0x6091a0304062c07030b070203032a04030213050a050c160308070302251502040605041802090a0f0f050a030b040303050411030a0b01081005070f030209010c020d080c01050f0702190c 80
    0x800c3d6001880c6421284244222030740342d51080012600e030301080d03c1d440c1e0020360340c090001c40a440901c0386254001240c003601d00e4650b4a40c00203045800d1084c1000c81c1c261500100140039005118a13507020690103000c42c5001841680c003203020202080c01005d00100d08003260006100c0e078190742a00281012030602c050322203840400b0070f00380d00300494070342c44040611080201c69000392002c0300d885864940c102401e06000c00310350713202200300781800ca90a01000c00c0540c0c0ced034070f05413006100503c0c7d07100b00d0a04114441001c4036944c1c00090103201861000c00014074840507042e4803035014940040d00b512146070000d1080c511040305513051281d0404c00060110340703504103040b03458000440d0000c1d6851290041954422500240030074840124100414001d070001d100d6010149011110304100e64005851402801c005030351102001c03410407402c907400d00c502c0d50020064861507940f4684168025900c17480c0c90148a0000f04030340001040011940d03800b000f42401c3c3c5400d00070f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 937967140 1250 937965890 937965971
    0x6040b3f0702031c18080a110c03030a080105130e030a09180504031b05100510090e06150d14150f011202060306121c050406091a030406 60
    0x400088031100024440281020070381c0240008100d480d0760441404480350f0032000070b5540000e0074240d41c0e42001c080324064940c005501c0c0002001d200c84c00c0d80b211162500b07000003440c685001c1188031406580700700b08c070021880e00510602e0465204644c00880b4a008464807400340c5143d60300b034001480042000401103411018800544607401d5500b099940c686008078140c0d4411344002e408600000149141d404140c003000d59a240980c003100d0584002011520440d0f000b02c1e6005ca03492901c10b018807000c102400340301400c41100c001088181030001c0b00051f804510b94071144640940c1409404002140802e40080d891a000740c0d400b0080e41c04401001513400c541d85480c214000d000401c84e0201032003051b0255030003400d01421542c03060148403500c402e45400d118a8812a00c40c081d40d4020440e5841c10002a55a0710361558607200b0081c100c011541c04c4240884509048080e10745156000d5907070064000c400400c8264100394010079903002d404402d0074031000e003e80042c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 937968390 1250 937967140 937967227
    0x182514011e0f1b12031d19020909010507080703050910050f0a050108030c070b130905070c03023a0e0d0309081606020c09040303111b01050c070206040b 67
    0x8500d42d42074482c014904042c0c1c5404a140580b414014100140356450400c40c03031195000c0c41000c4080317030315948005140002d00b031401c3c1543c19000c0c42220b48054034011810010700c0140c0140c8400000e11040c00c14010240c48210010540020155214000341d0008810001103281030101d441c2005581006a02281c41c1c0e2400c80380052114100000020401d03400012100f0620301040545821713410200400c05a034020411480d81c145021008945034a4038410740c6d01512903519030401c0b2000902e006410159042d45e54400da000f6060714201d511014641402c4400030701840002c803960700ca9090b0f410f02ca1100c1b503117070480080c1c1e120404040d0024035a8096030b110314100c50703110010791302c0084040c60f14000c0d4030068100306210039550811503e40341d0000c1c800d040210703245212100101d180d8000c2514a5070190102c10302030840c003820303c5a5500814000c2c9081e02d03003655500811040d100b644500e4100d440c0c00a0741346200607817050321200c050286183c10001c3c15018000030b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 937969640 1250 937968390 937968407
    0x4020a020f160302100e01050f0a031409010b10050304050f060f0915040218090a080d0b130c020c090405010615030b031605130e011103182514011e 65
    0xc2031140300e000900180c2e40041441d110490b940103010070012a500c04084800c258068031050500106100300f02146034190090700c1301e0415543c0c0055a0344480208a02240e009001c0b640180d14251402034a0b44805142140008040c1400c0c1e90300d494a280043c40d2103021030146209014820070302500c0c044464642d8080c400d0b4908680e041d680f80300041d107812405a60007580400d1100590540f01d000030b5456512410280a40e14218243d0321480a143c0c4909005810150780310540c062515003102d03042d688e6540090100050405840043e54488000b9010352152000e030700003c041100c00d40013400944501c0c0b0820b005008141000381c060001144042c0c800d0240701458684031040010742001c80d40c0050151900082c00c88090008045000c0101d031555241c0401005030481745004501846080d40c4038007098042c0c07244d1505200070b400c2206000f07104424000500e040d004001c6068401c6910054981c00e075210050700d07901100c15a4172609025850070456041d00202803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 937970890 1250 937969640 937969663
    0x10050f13061808010212070c06150303050a120501051c021201090b060a0803030f180106081b090907031709010c14282f1801060e0616170904020a02 65
    0xb00c40c802500c0381005400d078010419844004242c190020f19480d1050140300b03182405948001000740c00320408800a1080790015000720300c00080c802c800c41e5100400317030501e811606041245504013400640b645014104815480301020524004e5548454174000802d0440000b0800201c8074608020701140480d2200d1140900d04000100c2003408000c80e4450700c00210207951960755003803080c9889116200c0314046642c0c0304c03800301d8100010880300080c0180401002000c0310030508100003840000c0c0180c100d23400c48102040056400d440031038150403080d11498030341010100481d145080c50f80041c0c8115418003426200f00b03c0410b41005101c0c41c03a07450074070032484680907907840c0710141000f0402450074600e038880d1003001ca51100141c1c54080301c0c440300400761000507142041c1d02c2d920b414562404004010060300728881544800098541700d050000c3c0000c461000d008172007000c1c103451040314a0101400c60982250030312800108119100c0f440381e50029a511010000d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 937972140 1250 937970890 937970927
    0x130c0e0d03030f0f02070f030f0908070b04170307031b020316030803060405060306070e01120230090c01080115020a1e030809210d09060c0c02190510050f1306 70
    0x41e0004084c00f00d000301c0e403c958110300603007109140703a94115010320780b40c860390040101250012a030800140044002055200e00c82e60301e9500744480c3c10340c4640300c8081880ca0b036201b04100e000094100d034141100d45140382d503c40c02001180046428484090b81c400080d802c2c524004c410041040080d43c050103007524100207582d209405e26954200076140760020914044506901d503104185a0700d03110f8030100c000d8101414000c000c0c00304010252140354060f40c4004503c10000c0943d841a4010303018401403c0da03083d40320010b02403070018010001c400c542065908201d50007040f003100102d51141910101070190324211501c414410422070008640e0004111204c000040d0315551201e402c062600c040e00c01c0400d584541c1c02103104600c419103030503054000c5011403040760105803554440c04211003140c810840da072021031190040b946c3c1854001c0c030168031414050034000d406c9060807552200d0b9042840c14a0203070880c001d20420780c0c0302c0c010484a600c4145556460300359130 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 937973390 1250 937972140 937972151
    0x10f1d040507050f040605030a0803040b07090b0a0c02010309052b0e030d0309030219050106060f0c120f050f0714070b07031215150206060f01020a02130c0e0d03030f 73
    0x19448058400280c0d005000d60b030003100d0501403480e080949811000c4000c00004019944001090501d408041c00f1340b0380d21400320400c421b00a05002c00fa52140140c80c1111286050401080c0c060041c0e40032041080781c21100d050440e4003d502160146030480f0881d003901c0201c0c190301000c2c45000256904020a80348012507203030040d0414414000c0050181951841c8850210010b00034201c081d011440f82e40ca100031001e4001149600090040c0e0000c2101d50421102074450460a4180740400800e804a103012030990001d948840c0103525207070f040221300150458140c011840414912600014050704000402c4050080b185900301503a220903904c0c01c00504074080e110300540812581c405d420510f10b00350748029807260344581820303420b588842114800c440d019443d00050390002c400c1c00401d140c20184044103400c00d20080c080c0704000e50225110050500324070b215070340c50360380e0060742c68050080170740b0201d0060402d6081003094100140603003941412015160b2500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 937974640 1250 937973390 937973429
    0xf060c1541010e09010b0607080d14010e071d060a030902040c260703020d0e0307031d010f030218040e0304030308061c0305030a0e0f070e0c07121407050105010f 71
    0x41c14500380241e031140540342568600404100d040c00020a2299155605c0282403040c0ea80c05000d080f056003d004403d48840090201d1003c542c045658100e240c4103050040184000d5484c183c1e6012250786171008100e0300d9640141000d0605080b20380e4031003c0891404002c550503400903481c14001c48041c40480b00000b403d03500d00b9415590741c20a00003108c00e1080d1400500a0b440d0400310328580185030000d00284a801c072a6601d509807800e4100003920f00034540c3c00f40e80704902c1005800ca1050075074034031740080c040050150108040c1600030880a5045603600001c441140b030184c0103200c007507800380d503864a942c080c0c08101c0c00302d41c0c0c075004a00e040c20810001c50030500314090020354070702162410766890700000c100c0d4074400d4484001c8142901c0130b0050706002d82c00d590080c0710041c20a00c3d0380041080007040140303003203400c1c0429004100e0021400010300f90506180b08409044801c00321a407044103c0500f1039800c0200000c1d251030010f07403c80c02c68040b21103480e140343c0d4030f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 937975890 1250 937974640 937974731
    0x70e09100503072702030408090f040b010509041814030703080c0a09030f110a090b03010b0d080301051512010605281e1b0c030b09070f060c15 63
    0x2507019441d05a0300c0300b1010b01c150106010801d0051010311020358440700404858000d99004071011150040c01203060078290800c2140a04404021602800fa1920319000280a4052031a403144602e885002c02406001d18038218841c0c6070700a0210340801808903200e80d541c2d442400120002102d5000040003408080f09449001c4800c0c0c0c0c42c001c146103942c42d2122051070614040d10303451603810040c44165684d00494000300022640403424030200420103085a982d400001c1c02089815203460009540c541100e054440c00c0301e43e10b400d8103080b100b411160144032111a005594980086001c07900100174002c01017000600d920381d03040e604407910314041c2046d5600c0110b003603010413800c0c000c000030030a6040c2150f807130001713601c041d40c0350700f80c4411051200540b5103d403520814018000d0a07401705903c02d00010050842d246030034032414100000e03105072000c1101d8200300c101000385c01030300c4c98210310360044240410211008841c0b0a43c101d0f07040d011038044c2c140c5000c80c1d0180c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 937977140 1250 937975890 937975921
    0xb1b06090a060c03020f13140609060301210210030608160e0a0f0e2b0809030d02030a09020a0608060901061e210501032d020d030f020c09070e09 64
    0x9402800040520ba61010050301612024100745902404805444100c44c070141890b0009403101040261920304005d0303280c00d0010066024031010442614640c8800048a044404003051560f00407a41c00401e0340541050800a40c440307241151081c010358560000425164030a054038401c880610001201c50102d20400c04680541800242605a281c0c01406c21000d00b0070f0104100000301003603401c0c40101ca55000440c1d01e202041034014101d217190018542d19810410342d11304146d81410b80d64010342031150f5600780c00000150320300304250000c610056020340030403803294a50102801501c41150a035018440c808000614284203103500c3c2d1004008090b0210200c044560032200f0207070200c00a5040c000000d0400c0d4600c5503445020300850003810841602c4140c00c41c50b20101101100350022002c078402c0d01c00241c0da500d641c0c080820742c1420003111400c00c00c9000d0707082c08210b40750aa8400c1100c42044041030708294542001c031001c80340c2c0d011568502c0c0c244007101e613 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 937978390 1250 937977140 937977151
    0x605010e01050307031b1d040b0d02091b0f09120c091807030b040b1807030c180b03010c030614010203040312110f0f0a0204180b190e06010b1b06 64
    0xc610951520495000300002d44e0440d1036481c0100e003e0103030854407411000d48003020000500f50307015072000000b180b469a4030301082110240882c2100304002402c08441d80806807241e0301d40c0010908409800d01c1e0030940200a0001d1a19029403c00c0325815410600100c5c1c01010b940d01c0b081801c0e44007082e5200001e4004203411965160316a07400340401d4030001c2c2c4800303486240004004a141545118407480c400d02500c84586080c000e082d00c0540c200042e440207034400c05007800040c24051580c801c0d541060740d003503500303020002151301030302c44004100e4165280c401d024401e0790f0f06030080f000b50b400c2c00c42d481031b10070813504c01242d403031041384030150606a002000010a5115005005010b5120000c68074802e0a00019506101c0c0b50301018410380c0c401c01b045400c50825000350752944041ca50070710945100380d1208085040300a110b90b500c001c40f115804038071710303469009144c0740452030110b071003030368456003d44074071f90001a0526250510409040d81e0001c001041403041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 937979640 1250 937978390 937978397
    0x106210203061e060906030906160206010303021002091c050601030b01051815030c03070801050415090308060f0a0f0303031e020a121a0913150b0a1a0c0706170703060501 75
    0x3c0031003000800c00550090069580600c0402182e032080d42e5500195000740700040140030f481c185844060748000c0050880c1c0b095400c110b004002182e0080794001c000235840034096656404000040d0b07688119081c2a0503035021214a0014417a00040e1981032700e00c04c8464140c5070762554100050244400350400040401e00006100c8020001e00f41e98501005802c55031242c00a400003030810410b50403401403a950b07901040280405d000303100500c5140e002e1304000e40102900c0c010804000203140354050b5034000f40c0c85484d601c52034145401411103400409485440340b40003009411101400200c0065800b0500c040322284e00c01c0f641010801e03112b500c05817a00445680103004000184c1d2420529a400464980c232443d8129202e00d200264441d4200b0399803a1042801d0359a10706203902e20315143e190a516203d5682c001c00382d604945219a10601e076203601c0307200d0300c540d600d500591700401200090307203900700e041c83c01c0c000312103200d400a903035400d901141107800e203100d0785001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 937980890 1250 937979640 937979659
    0x100b01050c0c0f03011d06190506010c020d020d0b070f08010b09010c1b03021525050607181a0c070b03061003022101182d020f040e010621020306 64
    0x1580b804010f80b1240000240010803142e45950606240e443d900c007101e43c0b40e800c035074100000b00492580781f00441c065068100940d081c00e00008060924205000380030303a0410f030050040d0b64440607814400c42d4060300d1411b0511705241c0040030b10100f159110003103407401001080032201c101c00d030340b80d101041c4e40d003c0c00c11a85442e100d00c3d001242d44d8111b0f40d45120913001c40581c6a040c1c06406088038200116580e01c80041c940400350302c20440717084182c2d844a414400500c01040c110381001c0c40e458086000c4406c1c804202c4d104505901540e0000d0844c24001d072104480e0340585800301118081c1d5130322680d41e40040d040ba22044495071380c00102c1d40c0803014902d0003603001d00b40e0340340d4014044000c0040280714000e400b900b82c02c0b06240040807107410f1403425042c0074501c080f207541124060041505070801581001c00c56440503a2034021800d525038072410130941c1c00070941c0e0007001641d541d40319000380081d50000c41d6200544150780210141036002e000710b9000b20b6018140f88803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 937982140 1250 937980890 937980913
    0xc11030405090c16080f0301060e01032f090d0614130c0b07060209060d0605130c0504030b130f0311011104140f060409020a1e170708091608100b01050c 67
    0x1051303803200b14829008600b9100400204000e08041c103086481124220b6995040ca8009060650400c9400f07040506000c50701d15502d42462030016840c0001118000c0e001d09105045002d0207518485030b006070041c051801403099a4102400c400480050051551212892801d0820f00b4800c00381001201c003074100304918868005000040c0509001410400780c500024210fa02c182901581c507500c2c0e00f01400203152031180c400310649840c008209038503e000010740340340100e210183c4130004c0400010740e04c0c00312810301d10201d6071200f0600f0b8031041e0303072074054044400c507800c0e4800c6619180b10344130026007800031102501e04100c0d585030164940000c100561702560318950300503409000c00903480d178807400070b481d03820042d44036820208150041400405058031118080250b006604005a280d40e07000355080004d40c1f030101e9456480842940ca00740341105ca20042c00706100000a540d00085010307414202c011505010450480004560600501034040344980202c0c00820 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 937983390 1250 937982140 937982161
    0x503040e04020102100f050601111c0c080c01060602030c012f030601120507030218030a02090414030415051801020714042a0903030f03140c07081204060c1103040509 73
    0x294003a10500c1103401c82d0340d1817224481524402d0a2000b0700d0354941b4140051981c203c800111070101400040c4281844116150404003821301d4440601859001c02d005101c9410100c4400b03c0c4100300038024241d0b0780d08001d540c3c0c0d100280e2015554078002140310945e8048012420014401c020b9800c0f0740c0e9188801c050b15071025103018140402140880c0b40d0891078007a15208140755100183c5503c400c00700d11400c800c00401c070038400d0304416903070b000590310000915080745c0c100741c0c10428100690b00040c614072a0360044081d0412104044094a03407010040c40403a1701d00f10765841c3e0b400b802d0016030380c40180340905e01491030324040c5040e4030306142e40710340d8880c0301d0401e800b5000070f01c3c03542040ae010625074115000039845142070045c560041c0726880890102e14081080d91700354500d0000c401000741c0700c81d00c030000c00034401d020301800c182942c88424809000c01700340c0c03c040c60300d0401454000c04c0c84000c02c120005240d52074a020003514101e41c0c001c2d00d00d41d61540c40c42e40033b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 937984640 1250 937983390 937983419
    0x30c19020306010611010f0501080601050315040510050408041805060f030c0a0b1309050f0f011d04060902060d021206120a080d0905070e0a09050c040b0d0b0727051c050304 76
    0x145c2e590359503100f0b01e0212400d406998001c01c0c10002030041541004281400d0102d00c00c02c038210180074406010000e200060f010780010103d050000b03164075903244c54041803045070300000203103e0340018207001240c0c031b07030107940104005c844500320180818181500d03120041d032000da105d44000410003441c0503020040c079a10304400300c910b10140d100e903100d004850043d10980940380034a02003007a0200f2152805024088500503049032080d004038403040d007c0c00800040c1304a40f5820f10301c0c110345450b81515041589200c0654642c0031464259840078000c541c0144524000281400c4c66140480c100c0750144d008003403146845e040c4032a9001901e28101d08590a100f8407100182c0c08a20104c4180100241a00410584a5410442d1a007007040304414070961600d101d400459032100940f00b03102d47e0011a2113400d90312440300381e580040d2450301c030313800c0c200f10365a05065204040d00241a54402c03a20b1798964410f04840440022480c0c4005019901c204400d00540500752001c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 937985890 1250 937984640 937984667
    0x72a061109061303021039140610090605060d05060f06030415050a05010b0306120f010e010c020f03070201091809052a31060302060705030c190203060106 68
    0x200380703094407110100d8103a9008081103400d81c0e800c3d0701c042c011481c10084410a1140d2031800b2100c05001444034410712500107155100036101110486c07292031000310f01221590000100c483c6500d038003420545900341224000c0b600c0c202c0b20400700720403110340b02c0c06d02502c00280801d42032400300240c2c00000e007806845030340d00c0381407070021400319a0360000461040744501000d0355039414034140c103425a8400380180d04800e040000510041007881d041e20b1380004100d80c1c50307000c801b000e0180e034200000225404031035400c08103200a4000150803507003402c1b00c0d42c2d00700c41a185419901e1a00e9000f50300c002800184c45140802c00b142c401800015030002c00200095040c941c4c6d03660724545906c055180d8035104902e82005604512410b480070746a000751181503c541c0b6080d00140c1002c054401150070300481c0441c515200c285074010400340d980501441da507614a410010741da6013016008a007140f04004200d0f00c2c40900c26100104260301600030300d070b180d090103419101c00148008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 937987140 1250 937985890 937985921
    0x120e06011509171509010209010507080703030219050901020f19060207050f160306050108060610030e1e012a0e0d331107050c1905031203072a06 64
    0x3055088590580c09500144007006105261030610036104c1800028000503003644180100d92036660001c0880302d18907444400f075640c4e15158941038000f8064000111150700e00050135110581d0488018201e640098007250748410303d000055903a064114101040c140c1c400c0c24482c0010740381d40240898500c10000e0343c040100784805640741141640002640b0500c0c0c2d84208180055407040b20f002d8100300d000b4102c0c03494030001183c40c8180313403613800d400c056441c0e00030011507005000c640042e14902081c0385070a44082081d5020341035000c10b800b590b8080d004603000d00200b41c089000e0500c1781d42c46285210000904000140d14004015250032004801500c408043c00d00341c104085a181c41120f01c00b1843d003003000403607c1009480035060001c00200010a50000c2c420518038411205450401d5408001c4540000c4662115405100700d40b620309621010102070751180e1a02ea0302d903049549038420103800130130f180c14140700a4000c1d09400e00404d200d504080001e0340c4110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 937988390 1250 937987140 937987157
    0x5101b0c021507080a09091a1c0c2d06020c01140c0709050a15090b010c150f020a080a0e0303070804121e0c05150f1306090605041101120e060115 64
    0x48418540358009101000002c810300c2c014840d555130b40c441d107651132445a014406040e08c00700416000c1035005207009104543d910300c60708021050740342e43c0103000010540e4030210079604d120140c41040302158048201815000b00b14113200244114940d401651041110b148028001c00c10f50b00440c0c1036a01c1d401980408955178220b0700405000d411181303000510011701e00720700d55000c0c07019005140351a040c006803070300b1680e000c503902c259207410403490b2094490182c60103000301040342d501c0c8a13050020031190801034000b10100d02c11040ca000510000002c500c0607500ca1000315510130200e50610007050215030403858290315041d0700e007001c0c84c8200c00c08105039603405411010300b00040b0312011500c20090203004007035001c200c2504020701da042a41071586801c1c0028400b043d031542c0c41a0810034006c1c260030500165030072042c10065402c25082080c143c804003040301d80821510780268105a26a20603510700d01e02480280900d070342002e08445941599410a004110118 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 937989640 1250 937988390 937988393
    0xb010b21041a0a0c0207090e0c30010b03150a18050d0207120c030b0606040b030108033609060102120c03090114040806040308040f05030705101b0c021507 68
    0x60303140900403402228500584000c0200d0100440c0c0300a250b805224100b04154101c0317500090070205a41c00890045140d414002c6103521700348018144a40c000122440e5000d561030b502912100342c0a81031082e10b06000e0001c84500781c5206070314858040d8450a9000107003821400c6094000c02040000714008010b0480482e0460361960161115040041c0d103045040d01046203100038406e0001c2d001111080740c5a1403040c1c1701c5840003a202d401d810000804c16592a030841340903003808846140c0320350b106c040b44d50b56600304085140050550b00d4001550300d0645616030f901c3c240d40f4000c5d00d0301107034490921204007409003a407810b40c40f895451080c001d800d01c02801c8141300d103900035601c0c0d0103180c0004203e881c60040240d40d0000801c8144400c001c0498030940c4582c25042c540c11907102c03803030016095400100c0c003420601021400008009001c920b50121000e410000d00c00088101c1035001e41c3c00500005002042001f0105401820001e1382c000d8840d105110040c242801e5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 937990890 1250 937989640 937989697
    0x30a0216060b0901060f0804080315190f06050f091509030d03020919150305090c0604030302060a0b0603130201030905150f010e16051215040e010c0e0603040b010b 72
    0x1905011900300d602c0328100580d50400c0c0c41554010b000c24074181c40700f200e00500103410854003800c0030300710000000001740901032401486040c81c0018100400d5100c49004000030480180200c2ca200d030482000050038038030800c183c07020000290440c91401180b08100310001710f22001d4138042c0c0d00288088107550750240700080802d0351985000d230740c5003901030800101700010f041a031841105c415092014140c0d0381e03190380e101c9409050000b03043e2540154249003840000041c0d90280300000c000c803c15134003040e80c030f00451802c1720a100b052101000c00c180d40c042210a20148100c4910110156100e03400c02e40c0120301850603103c01405041204103040804c0b41d1207410040064010072a9680710608564000f080c800045695035404400628510603610340c3d0740882114404200d0070754410007984403184004000304500200145d03100c1c041c00360a4a01d1003c26098242c2030810304191044a01c100c1d80030342c041030540c0c20114544003d070172418086980020790f11541c0011000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 937992140 1250 937990890 937990927
    0xf130b06040b1c091703130209010609240f0c08130e0f070314040605180709060512070302091b0408100203012102210f060a0b01020f030717030a02 65
    0x15107070603510310030350280039050083d0240300c1090070724100c80303c0040b800d034120900d03401030801c0485940b6202d0410f0042c6220440d01d01943c040d102c00700001d8000d401072003080444800010303164413518542c81a000f094a10040c803004604124410140d0b43d202c0d48040500030b100340101418054094804050b03800f10ba04888900c007042d0041c00805030320840c4640d0710074100d1405100140300b80310741d00208600501300a011640300d10205070804940c04004000c0d41d552001c03503030381c0d075030340e0860b4405000d0740d10941d07000c3c075030310303040d00f0300c100400f00e030040c2036079005403502000c1c4d2150310044085982144101d12070b030708107100119203072405029200155aa41c0400b50f10bc0d4101001540c460f8003080d2048001080c07906080c00513103d0844926030540384001e08910316044951550515a12401c601943e0040c0000c01601e41d00380c1e40614103c200030390890391101c001c155080d6507880740c514050f100c0074040352440b403442c115500640c0d00c803026a00140c140b221911104a0016 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 937993390 1250 937992140 937992149
    0x7020708010e010b12160e0705090d030309110319171c05060301060f1202131d060f07030e031b0109060203090c180c16080c0d090801060b090f130b0604 67
    0x2d441d0413110400c0e2803c05004004107400c1005484c0000302d400496012190030300c00c02d000241d03404000361002c2c0c080e000b0344400c1c07140a0b041d5611206140b9009004040d6800200c0701044e04031420003040c100007a9191144441c0b24a6011108072034036060f80b1030200344541c1040b14400c00c000044420107042005c5274030070f02c0d035011070981001740400d42952241c1d004000b208481000404c0310001c05050100d03040d405440c00c890340703801c1211600c00790110030306201d001c500101c2c10520004000030403901c1940b036090340c0c440c1610340c41c9085041d6031300800d038040c2e103900910000c4090702c40308a100007125486000000c01071342d5995100180c1e0803c484002480d00401364982d082e00b0000a085803540108d4408152490f00303585494580c010b00c50301c20308140c4e4000d059403c0040c0c190440b989100708004481428000031130040016040c1c0c00358804079400c00c1000902114000305503203000000520081100900d00c1c2408016031031000303aa01010f880f010030f0210340e26510014405030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 937994640 1250 937993390 937993393
    0x1c0501060b130e010b090d0210020114091501140303030106110a120905100e060d02070606051c03110106030f0b042102071406072015031509150d06020307020708010e 73
    0x280c50040100341032001617202c614801010004964a030f5950030a50156a0741220150020503076044120300400082c50710358044000d41f000e1010794100018007020a0520b00c0401803140c0e02e481060744061004002c0701e030140d1081c00140180c50140704000d19085669084461038511030716216010620414000041580c003001402942007030403945074402050306045642c3c42449010031007070f128031032103a00390315030108100c0708000031500101c00800d0300400c6450301103441203452164402c0454110003254410f03986200c14903040c00740b038040f640c015030071807d00f4000788c4030319103814030050045821003009100c90703508403100002d801c0c07180c85035401014102d04003131610f05c440242038035191003040140318200000d03051103110300a80d0300800140800400a801044d16444003005170303850f90202004000b0030124103040754840260880e201c451a480e9408007140068005001a80020b004d034041004100c00760000c5400030181d104480055031f41e0b25603a402c5511100750041103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 937995890 1250 937994640 937994677
    0x70b160c061e050c070203060123031e01060509040b0105060a1209050f0708070e0a0f0204053f030a0309030219080306040c02010501051e400203061c0501060b 70
    0x2282000e1043c1603112005400c01c0c4c1c505095500040c1d039407481441a078060384061044200c0d1400310304486c031036041c409012078049460403030410105603507200217850b840d0319000000030b8525119a900d80204d8005420080d142d00304002d211881d408001079205210b208495140c512103548141c07645280644040d18610598140d10707410801c080d400300050340c1c0000e03c140040e250349007400b50050008040060740c5c2199801d40006402070740d0080398800c1d10702d440c00d903410000c0700c43c52030303d03407171a030f1401ea1a00200800380404000d40418819154018490060443d00982c00001064042e00484000c400321003a83c041d442c0040202715900e04011043c00010b01300381c0035000d0300c04d600c0d0001f4880c035070400300071440c401c280480900f000d51141c40790040c1501c40d01001107100700356041400c411242001c8480c50001d00d0701c0100c1042c0192068809801c47d1031098a00031403000701000690100c074000e900300a05841c800b62400d560f10f8500084158582006154204000010000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 937997140 1250 937995890 937995941
    0x8030a0c021b011b0c030804030822060e0f130507030603050c0a080a0224040b0702010f09050109091517010e15040308040b181b0312070b160c06 64
    0x800a00300d140814005003030320b82d2407481c1e804c03081c000c11000040440c1402400e20b400c04c0f80f42c10703800d80d0020b086884005808018409038000900c442e04280e01c1140544110380501c0014004600ca65400a801d009866550703141c0480b88107050400280001ca010040b184510f080382d10a840c404040303a0781e42d030100200101480514030207042100d61607085413411001341d07150494508028410351080d02084c080c2381e0072070203080140002110141d1140e0b02d03108106025032044d2070582c08035400d0035005030118402c01b408000d03581b040e910340c43c60918041c0403a001c0d00401c1800b000d600801c0102245421510b4603080240e00c07040c0010400c0c042090700302c1e0405034040207000703440307005204020129411482c01500700c1ea002651000175507038041c0035220170492903200c0380140104080e0410280c032b214032103084a0f03003c405a520b851502c501c0301c500ca200d000c80081c518801000090006080c480604012281c1c43c10841c4d600d036400e80e1b8903401c5400307040400c1483c0b000c0514210 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 937998390 1250 937997140 937997143
    0x307060807030b0402090603220f0606050f0301020c0c040b01021e250b0304030503152106011d01180b0a09020315011b11040b060c01140601080105010f030506040908030a0c02 77
    0xc440850545017113140118a602145140c0b200603c4511088215144890940b0b1444482900385401c9004c040103420546040b5020340020712809103d8500400b1045491506100311501c4403917820080039220039440074071000d80782c40040d050550061202c041e0402281501d1019110b000304003500c0c51042c550203014003880f1541098100c2d180c00c180070b0180d9000b80b41120340094050038815120366843c03030419403410454403115041960700d0710500003000b0000d80503088040b40b1080d40c2c01aa01c1d540188490100e403140e150300104817200410644410080ca540000c00101d00130800c414030318040740ca01d85c0154002c25990358008100540c4641c0c0b40026800494240307017441000c42c1602100b829145d51400c09031a11b0422014034200340e85a600c22810300c000a44499200c46145004500800c40d41c0c084086070818400082c070b10f0341c41007a04c10705840c0141c580c04840d00c001042180280b200521240c0c0007a962400503011522260155204000302000443c4000038150000d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 937999640 1250 937998390 937998401
    0x6040b13120803010b030a020f0d0e0607051e1303051515010c080913090606060e040e0105010501051603030b090112020f030607052d0c030405010f050304030203190c02030706080703 80
    0xd00140301c1c0030584400141d14204590464101210030fa0b01c0b600d40009103c020300c80e141c03658070000303c0003070040c1240c5060b8014060302c55000098480a0392640070544451294422246040d00c02440485449803c00701030900a0300540c5c001c001c1e01e84958a0a142c40003030898945460519000c20000007481954990040c03000e103070012200e05190794006542c01007003000d030b22480c0c4ca8075000702019010b80c005802c49810550510410b940c3d04000340c0035610301e0101d207010314101200fa040061050040328125541070396603503c2c0c0801c00002e44d02601c0340341811810152a480c01764030039035481c0e5070030380a082092441380b81c0d550a072040100100c0c00070340381030081c0c0154003040360b615001001c4d030740b03094583c6001e1030306081d000000c54001090350781d070b10049481c081072039000120004068000d545d130a07292412068608c21003910300e4041100c008005034010000d22080821088080c515600141000900010540c3c0064200b00c4140c00280c0002c0d43d04040007405580360151 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 938000890 1250 937999640 937999649
    0x30c050d05040602060c07030210150515130b0c03130b0306090109050910110702210d080f220b070f03060501030603030c0b06190b130905090d030e0c06040b13 70
    0x1d902e02031500c03c01940f42c0c10010300f0758000c0b840114000d01454002e002c4014051890704040100208500c1c0c44496025030340156805154000f000145421250741164a09809500c2c014030051a00545414542c44040103601d10301040c4840f007a84907403540908044c2c40305000d055140d160400078041340f100140d10a03140c00c2e01b0001800610803001c1440080354224040c040f9031500c400c402803140c2e03c10f2400094002000c1d9108088055800c100c811081c00e5074004d460599803e0b00341101c00c07003000c0d070707413041d091541c03002040101c803920440401850000c10800070002e40f907100e60010f154121080e80214038411488660f140e854807450015110900b010000503046071401000b5041e10362005020006100110307816a48807100f07078002c10500c00c070b15400341da02c90035151a20b402100c8100226250560041340485913800f4051294003004014007850041100072400340c854a0b10f84941800b401f0800e101c01c2d1116401000a00303100381c2504d80d07580703138144143c5200005501 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 938002140 1250 938000890 938000897
    0x1050f01090e16050f040e010f0609030519060b040c0f090f27060522110307050d02030703090206131d06030d0f0e0a061e0c0c230d030c050d 62
    0xa02905150729010b0b038101180074000581400560300c1900e442c86806002040070101140001d47e403c0301091880c16182030580c083c52541e504c000507115080c1d5404000c0403508003840840b800318561414403540d030300512010601c40c001001240c1214054400500000c02040141c1c06203500800218010001012941069864a110900d0706041e0000d44c58120800c01d282d44483c10183c0c02200c0944001401c00086c0b400e81408800c94415140341d1825a40c100803a484403a031042c0141c0340303d85581d0f103510b403138000c0c1609404002d510042149003490340c5d8540d81400f50315030f03402810b8104940d0b04000c07078150510610428030039044465014407844601040308645011400225100041c10320041079a40c0c140140c1d5402d40084169030007564506000517840e50107400c43d8550301060320040314882e0446001c403088060000d0240103003919400070044400171007440e1907403850840c003002034070a2200c000340c10054070700b005800041007400300303205020040c003460311305000506 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 938003390 1250 938002140 938002157
    0x9140f010503071404060801110c060a1104060309031106010e06030f2a0a0e0403020114240f04020412080c0708033406150f1715040309050306090601050f01 69
    0x2000280d40390603502a8000800b84c1021040c1d107038649400040c06084620b001703104c0d1806600d00401c0c0d5403c40450b9002c02c2c8160342c08545074005034400d0f01002c205000e05c5510703041c20b100056020300702c00401142004000540a41160402e0104a001c1c0c14000385070110b03810004105071070481158203c0b003080d0802c865010461f080010130203201c2128640708240741030400c000841141103603108140c03018404080008050381940081101d800c0002207108c40c0d1038800301c0c0303086400e41c1f04950007402c07550361048900d40f50062409000f480c0080002d49410b40b1662000503181500c072080300e41c21000f00d5019241c1d01c043c80182d010b42200c8000b117003810b03c21070040ca070b03045031400c038a050741c9100a08800c80122000000758510381202090040d0a14080ca22501c5062840b40e11107040041d84081124901071102c4240b90a43c02c0041410580d11629805580c5d40038004400f13200c4c00310000640c54405002c054401d0b240000a05444d615000611001100280c0c50300d04220241 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 938004640 1250 938003390 938003399
    0x90a09180606270e0102040f080c030d0e030a14010e0109030e1804030c0b0403020304030f0b0a0b060c1203100518040611130b0c012414100e0112140109140f01 70
    0x1c00010303e90000b90345010075120898485140244a142c200041d0940c800001081074000015185075a410607421030f001e42050220441d40803600158183e4190850420310300851503d08840f10020316450000408802e8400e031a03084800d03200007180401e8440120400c40d01d421483ea02c648040b070849103040c0c1c600f958006010080841004250186083c04242454420025a4003441d0701c8090440c1c0d400d860b0505401c050b00c11500d08a201e42482c1001006081c42000d403940c3d503010100070411155013001000c070f00e81000f000c1c44190246010005156a0b40d007c9040340d00301c158030040f03a142024141032041c0c5d10340c00c0c0200c240c40300401074031643c0b10441201e0740c1128080d004868036109004298cd0141495840b081c90402c161800c1c11851070310718910804513101c000c24020144c3c500b4081c402c99240444818002c616004c0ea401c1007940900c0034481c1c0168282c90000d03810100c000b581407800c101b038108c1104559511500e040b000014850180c1240e03040c02c0b040140d41c0360 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 938005890 1250 938004640 938004689
    0xf0f08150403051e03040b01150c08160f0803010609030c060e0105042102090406050106020d020105060a030201081003060f021911070b090a0509192a05090a09180606 73
    0x6000281000f1001691992807004504031410030000d14880c0c0340c0d00d040c182801400070b03000b800340d500d440c40c84441c1d100c951400742e5880c40c43c2c640d018191a0904060600c440319182200300c05036414030309210060700041044004601816060300c407440440d040d0308144060f03000701c0d00448103004070f500c0f264440d603130414107403000c540d48201c01c4d402e0f030424500001215554140000e4000030701100740401c00140f80c00c0342c0d058904550803210007820820f0100c0c00e0380c0050b20059000b034140c06080c000b5500c5002d1480d44004154a0051000e90b2039a82204413600d030340340701c0706017540030034010304100c6080790410464060b03141440a414065003a075440340d1741c52189100c0b6600004604456032299410343c0002e0000405080d40d911380440c190308040c9091500107901441d01d01526a040c1000d800c4110b200e14107602e862098204d084103072170079804244410303032001c82c803840042d00303c8080c010080703121043c5507440c8800039a0705d00441a500135030004080c011140e121340855144 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 938007140 1250 938005890 938005933
    0x212211f170c060d020d0e0a1103070b040b03130516031e020306240a0602010e01050c03010803030f1b03070f0807300e0d0c0311010912031e060f0f08 66
    0x20032501e05a0711221940608000c0c82100441b1500f141001c403001c0d040e480101e031444105004070f0304c02c00c5e0309200c4402c040d103a00d0303580501c01009400b0b010521481c1740c030402131544900810b8600b61140010740701e0fa85071102070055060000880c000a00c208844a8a42900c0d0325805041201d6180c00d03500080d10b940e0002c0007103d000120700d0a200100504c1c0b0b58130091450041c00c1092010b4a0301d0000f4040c12803d0100131140d8285004146040007074000c07079040b950500003030341c00d54441d981d200e00511800740000786600e408034100042c4c000720000031b6014603565212566185403540d00900300d894000c0c035040078403403c0a0300581c0400b2845001c0c29014404241c0190030103054583d500800701560590100d2241c0d844a071619608125030100741b9000740c40d003001250000c1e180074280c40d4a804001c0640418529490065010380c0004483c0c03040c84003290b050700c0d51142c00c1c0041752010741c00090440860282040503882d01a0010003804c082000741c8000007030401c6082c010f01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 938008390 1250 938007140 938007163
    0x5070c0e0f2217030a200c01060e070e1e0414150108091b12010606050901020f0712110120010614010302030907050d1505010f170303070212211f17 65
    0xe00000001d20081c050740c446c0c00241302c1309540c0d0740503103000100512150412080e440c2650704e48a0041891440090450301c2540c4594a5060740d4105509111600301503080c81d1042107898239040f9000d507564080c070078180080314550f8416180c0f00400001c2c400e81c20b0340503818001a00180075440c0d001040424103e0341d0044400c092141c8003000c40d2000c3d0b2049a04d407102d500c3e000c1d01040456000340140f261480981c03c44000710302d00120b51b40c88107103074801c4480b11030030711004100003003007505c403c1c00160050500e01c1055150024400c0e01c20441d9038811000d956400003404180c0b1904154a07480340c080c038045045181841d80c1d1941d440b403e001d410312071094280d07204104241c804900006500a82083c041540c5d540b21680c1c0244041c052100105000d81440200000003c103a0384942c0141e4000d0030401d8501004031826440044103d198805003411505d040b0240c201d00341c012450544042121003020f40307440306800385600038595124440700642040c400001d03140b03c0c10b2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 938009640 1250 938008390 938008433
    0x5031509090705041503020a0e0c120c0409140718050604030809030313090c090e0702060a0f0b100507020f0f030a0318120813060311070305070c0e0f22 67
    0x2a00d41c241110310304201503110341da001d8180303441c254002152110000032244240e4a200e40c054440c1071025101e40d044403007a800b414140000107810302070764019604402c0c42010300c2d2030161265820f00c283c0e80d0b04589000a005548140442103500c80c200c2010310740440f91400a03541000001401c0b07105d107100c0a85800404030b0308401d0390b9018011607000b03200118840040a540740c44000241804141341000304104c007000003440540098458452a5148d020b401c00c0e903600c810050044c014040c61041d890b5662417070030002e40300c50543c61404000c41e158031380c4441c401d104000550700c0e00084d26001e41c1c0d080d03030004410307100090402119a41402e00342c0d6421308000ea1011104526403000c0e10381082e80c0014803d100a4000a010002c50301005600c020344440055094514800529000d59001c01942c40880d2107540948040342c803440f03426480da1f0b40d42400501d0404161411041890070ba000d1103a41100d0038400220040c8010350b90111344c810762962401203908100d01004e1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 938010890 1250 938009640 938009659
    0x1e03081503160306090204060e0f070f0c02010f2f011e0c0206190e0a0305280f11030c030301080705010f03060308070308060d0605240411030c0f0d0f150501050315 72
    0x45607075581000002d001c49e0011012030385801c8c40313940e030300d07140540305400030074070b13240f490780b426440b8141c900e00607078041c0c441d88454400b0f0f1008445012000c10201265a1300c400d241d124951805d039400402c00400c000803440710080b001c1c520418031644081c0c1c03200d07440e01c2d400340c1c4074580105080d5031040c3c2504070b100d000411140c0d60800780c00300030f4001d881c0b8051080c4a104064000000d00440e4401d0726038601e140320250141e8403143c90703150704000883e84158003030465034810802c6c0c16a0081450070f07203007000d402d45035076442d503003080e0420704094116107424083c950b407060b41441411400d01c0c051080724610307107480000d4801e5850240c200079100e40040c8403521007041c0e500320340c0d902100801452a2422442843c0254400c0e100026408401c13221958942800390b02e03282d4002e140c02c9451030f20341080403250350340401c07907145681200303204c0200391a84070b11403500d00445081c07010035034141415003092000c125030001c80c1401800e00c10722070641d000228000c00380c401582c1007501c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 938012140 1250 938010890 938010893
    0x2030c07050109290f12010612151a0c060a141006050d2a030b01080108030a0219020d1403070312111911010603060f05010801060810091e0308150316030609 69
    0x1082c4644003001541d0000021410746d40a10000100d040b2000e0360784240307210724048040419141402d204141980002d48284064526030055582915000740c1c6646001d145652072402d001007110230001a40e5070b01c0d101940e11401500540d8001d034225111412903082c144041c0140c000d09100c7c41a86070b44240000e43e00200c01a0521000b41042483c03801004500b4014040c0c480068071b240020304074400000c018600009a8040c6e15540e000b82418044624042ea030170ba04e0740c0420303644060b0f5501040c010600426000c841545608040e50343e801c0c050074040e16090a100041050310300d801111982090380c4429100070440388191019000e400820880e41c0c0313100129141015403914600104101d42030f1300403c841000c24601340a0b50fa80d50409501300e900500c0340100d1b170f0300b141c8079004807107007913910480344907102e050610447d6540001d2601d091840c1c0200301c1c0424444028422550030550b04181800c204500411440840800861400e40184402050951502808030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 938013390 1250 938012140 938012219
    0x60b25050a0b1b1206040b060a0509010c08040306021b0d0801030f030c0c17070311041406012d0305070e0a0305070603090c0e070905120105040c050f060904090302030c07050109 78
    0x201c1c0c100d001803d65200d814210805504610907918544111300d13040c1151024140b40703040d01c1c81640c058071030600f000d004800550344501c1e200c00885148004102c0800020302c0392000c0c00d4080e41144400c061850010251403401003021040c40920030040b0041000400303041c94100141d61610340554003002e00c1c60280c805003040c1d00211644001c080c18406500800a81c0c02c0849000b40e030940382418204090004a90041407c606104050b0000810329405800e00c181c00c1c01c00305040968901c148010f80d4107015001d0307048000a9150310901140790703070041002c280d100007204c0003445c0d070745180e80300343e501c030740c1441008103140e252403c40d828014170075045170003490300c40f00c0201185000710000741807802c20b01800e40719201509600b101c00b034052203680d11030f940c00301d50070103410304000c1040001d2042c070b0710300c56200d84108080d603a6a1103d00031109028400c0e002581c641c0382c2d45231402d050a0240d01300c2c60412008045c10441103903010000c020080b10602116941a074082440 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 938014640 1250 938013390 938013421
    0x41221180c080d1716080405030d0c020c09010503011505091e2502150402040216060c0c05011a0609040b0d020d0c0e0703050c0910030f060b25050a0b 66
    0x1c1c1818080810008111502154054520a05a40c1c03180b01221380b41925041c180103075004000c000b510a092212203004402c59034019025400b142d050070050140701040d1040200d00700c005801040016451b41804607000b40500b40480080c80000c0480482c90003003e094842d80d48030f1501c40e0045089804072804949040780712340e00340740c1c8528090034440b841e4029030041024944071400300e00c0b6410f20201d141440e80440c00311030121515643c00b000013035000a29040d0182c58400080c800280b150b100d00d660034a40e5441da4002e400103410310074210340381d621801e14103050760a000403c55a9280071121903080c05c41d400990150814041260b8001d0f041000390071140381345980041c802c0d104900811101c488a051400d0381d2602002c41c2a92400d690b00003241000b844620224900b02c199043c2c03601d42440c0001e000d1000201c0c400c1030314016405140010400103206080800400300d02c140e100c4d000044603c240d030310317a407810b85e543e40f496400303040c244007031020a5a40c40070324880d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 938015890 1250 938014640 938014643
    0x30c05072001110d050c12030105090c0721030e0d080601090909060b060a0c0b0702070b0403060f0e16030314040302090c0319110a021605060f0d0b030d0804122118 72
    0x120ba08600d00c4c0c1c100907102c1d0b8040840d83c0c0c0306201c0d80f10101a00003899044a05035000940001a1a180d10120b183c0503005900100c80080c064142800040000000d094003140380d80e801250440300b08a0031400c04145400001c00c009007401004042d91700410000d04541c04603c000542107018189040140b00d804403244c0e00c440d0008803443c445a011041d45031040c021411070741c2548852200b031380c0c0c0c1c0025100d081121203090208001043c0258400003040c00d420001140c1040f070741e841e0030300380001c04415600400c0d90110520038990b1007648610005a94000b0354a85404c3d034000980a450040020034001c40c0007000441318515050b00042041b4502414000f0860003440c0f80c0c419000100008010310408001c00680807060300004c0c100c9002504403446c00c10120003505495100b02210f40c003890701c45400c45825141003180c0c00d10041c8a40d2200081c0c28240b400040544641c4150743c20085480000c000c440032840380c110018000000c005552090580c1c01000c01c00400030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 938017140 1250 938015890 938015893
    0x50c0f0c0c03061323060f06061b100c1701051023040905060d0b070e1801260604050714131e0b0418020d020d21030c0507200111 57
    0x50111342c0d035012041c140307600d10074a81c03051101500401708880d80d0000d001038103150310900201c2c5142c141400000c2d000403010302240d10f001ca583c1881041010f016800283e0f40c0e0151054480e041168824030325089610301d8040110050640300003503584040c044c540c82500c44190740401c0e180902e8000004a600d8009141440050012011650411701c1107040c0c02c0e04142c0040c90070b10b01000742203039095004c248000d045d180c0c018101c60364011044015000b00b050b004c038502003050400740d11300038a01105658000500c0d0718035656030007071a4090b00159408101800300181e000300c1d1840942c0e20243c0c1e00011200c04100103101520000d4400345000e10b0007030755004002c424000503985881c5036000b4400070350030343d080c0000c17100040036080e060810541c0c813000500d014901c0c048140c0c0000c080011148454541122494134a03454400d4181070341942c200194050180050150850404074104047c9072602d42da017105c0c4101001c4441e4486040a169a015510030507103000c2440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 938018390 1250 938017140 938017153
    0x509090a0c06080a0b04060312030518070909021804080409020f0f0f1305100c060b040912090303020601061b081303060e010204050306060d120822111003050c0f0c0c03 74
    0x82d0003809146054490048650829a000c000c0b030a29006800c111380d48102031b5800714601c190100c0003018098004403402c4510510b0719520b010810180c8080d0181c50720003d0a01c13150b02c10000b001811000c0041c2800c0c40c103040101080a0006039401c0f200c0309000960790710f014404070251885400400e504105011075001003a0b0b61242c09000e224103104954000184c4900410800661003100ea00000743e100300366000168050704003000e03d08002e840403951440700d980c0d80380d03065002c41a0a001550380700040051550401c003660052a01d4180903e4241d9400034000c0c4000604c20080d040c0c000c001141e008442ca0341490f08000c68101104009682e515240d660107036205115042c032038807070400881e0051410140c0d02e40c3e0150302058207440c04210316800e0718454001028042e800a00c410742850082c9084a4124041d11440c00985064907840405c042d10040343c40304020075207890700b00b02d00341291004071000440c00c440e940d0744a2000024103841c16103a035038020b030103008a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 938019640 1250 938018390 938018399
    0x60e15030403142a0114101811030c0c07210303181505090f160603090c120b1006020604020109270e0c101805010c0f0b070e280509090a0c 61
    0x21041c00131401c003400080c8141852440301c0c0407198404c0d50006004a5601410480c000280c2d01c808081c074240b600100701e0f070b0440354000b402604205c1b001c170030344400003c080415070014070118000c1c0100c4119111200300e02c144041151400020040606540c3c11400c03840e110f441544594840c0d0000c0186003e001000c2900064074003645c3e4108180b040065588504a000c96103021004450401c000c4c09850703d02d040307014020280c0281c03180c4c1a00c0c0c101040307a11307281036400302d0103002762100b0701142044210300d08a09000d902c03d82c1103400103000e100050380e0140040d002c44e14241c240d00002044042c4a01c9690350079001c01c076240345024901c014591300071070f500e0a040700440c0c000c0110100c08000b50b0385d011003c0c0760345010015100c0140000c0d80103000e4805081d00070140054800380542d1542c000381e10965458002c10103040c40400b07186843c103a0380c80c40d1400540000e0f051b0540c1000c00e20440a00c2c0140e900c00c040c828001107900d40b04010855845400140000e000c9545 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 938020890 1250 938019640 938019697
    0x2a180a150e0a0812070b071709030c06010608060d0b06040e031b010e0d0801170102190e03160810050c12010f030c09090b15030c09070504060e1503040314 68
    0x16030141a0103850340b1200001c442101180036028448000c0c822890304c102640c9080c04008014102824000f1000e51202d1420403c2c14076885180b666004543c1c130912841140c3c50303e1816409842000f5003502045000c0d03c40020345130030641d2150b1060768940311100000c003d002c0c0e80e07402c01510311010408504000804001e000e001f0002002081205000c0e910591034281d54030140c00460b0825004014440b00c810b4241440840000014100749291301d007910440301c0c564103d000500d2290380148203107011311600e4609403080103190095440c24821940742c0d8224498001d80da5075500c0080c140d00034400460b151a400c020208045e50307141c1200c000c1003a00d5000070f0b030b65440e280744040b4120b0700b188030712070005401c140503095039030fa03460010104034080601c141c1c0500600c01000c036640c480074003580c01100642c031580e40307641c10900c00400803440401c106220b1200b1240a600b40589841140d070080c0d0545806852226111482d0030a8411941c0c851490700d440c00c2c103041728284 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 938022140 1250 938020890 938020907
    0x24050a0c150213141807020106030203070605030108010b0a06020d030b0a030609060501080d0305130b090307020904050309101b1b0e04061b030e0c210708062a180a15 73
    0x3500702c01507641511210f410090001d00341d0b0b910742000c1c5c8000c1038441999410482684207129100210b105a1039034086401e2455591107540802c00210052054820030700a404d480d400a540280c4410b16201c1d000b9a52020500c260b401c0c03540d074849008250310382a0621002d950030a1052154107014075142001301801d2281c80c07624000c1c0d5581d040e0f410303c03e000c1d6030300501c02091200c94a0078030b9260b000c1ca1100240c51602e20348410445c140050b200c800c5054421800740014507101d528a206201d08007a40e401ea500800901c00500d0803840308022000e07060b180c01c08000303400c4000103101e06d0143d241980051080343d045104200402c1519041103040028240151102c040410700c20f6040d80c44507040e80c502034201844e00d4185050002580e03da031081d65901189000700354044070300301203a070780290840d6004482084603542c0c2c409555070b080003141c50030080300002c0000c03003e50784c010182e6400c003000b80c43c01c0010042d651076440d40050040c0c1c080c61155180380d440080c0ca42907 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 938023390 1250 938022140 938022157
    0x90a02010c06021b06090f0f070320010525060c051e030a0603140a020f010503240121091101050c060a0216060501120c050307081e010213030312050124050a0c1502 72
    0x808d480c0a00c480304000302e0094106ca900c420306a40100031000098050394403140030a040080500c11b403080b00c4032040017060000e8510490814a005505110003610420032000d42480001c02c107401c1c4401042841c000812108100c0a80380d4481c441d031003000c0d003099030024160b4200c2c215825502e4902203405c030506442110b202c00603251030001903460b40801c44200025010160a4004c40314141c4001004a101450303c0340c2090b90407072005e81c00f1582d00750516911965180c1c550200440d400f602800c143d4242800c5040403221176103603640324001004030316025004503a9984051000e504002d05a81c8040140601d684903010309800d801541000d85c0e1458410307100040d01d043c0450300c1d90607a080103000d844e034500081038140c29500c1612501c000c941d420048108104034840000c0d016510039680d0708181c201e40c044130005da0f181a080321072210801d0300b00d40c0070b0b202e4820b0454014076030340c14101e44440c0181c00c140d90615100001400c024030707400080074003400c103500408001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 938024640 1250 938023390 938023393
    0xa060509040b0a051b09040f140903120a14062103071202160e06150c070f0501120506011e0c050601080304290a03020f040f08060402010305090a02010c06021b06090f 73
    0x26034503030090700040c400c04205c5848140341003100d40110304054124010f40c9002e446d002c9150000e020313208020300000c881c6040e040d0408140c07411a110303034808103030308480c010005200217a4003040c150309145020b05003502c1600c51703038195000e401060f01c220b007141681009030b80d04d0300c0710340c10005152945a03454400500842300100034071022081413000307070741111101200039692101800ba2504040000c052103481c240038071029007200b0045103000d041d038902c032400414035280016020b144003030798540100d0700b01804c0006a9070720400500c44441481918071488030420b03c25200310b81c031010042c001d40516000881c40007000030061007201d0b10340c441d40080e080c11010000e02c0f45a00c4080c48100f07030003082a0751210344290003411041c007184440503d010780c0c48100803034071945036021b405582c01900820040d9a050b00c00d040d805081c2030040c0c40400200c1d40002c10318480c014006040a40c045107258140b0483c0307507140890034201013242d08a042000119580b5030a100406150b07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 938025890 1250 938024640 938024651
    0x140a210c05030613030e0d17070620071101030e0a050708070602030c030904020a0504080f0c011206060f08040602040909050715020712030f0215180d09080a06050a060509040b0a 78
    0x102d0600040480c802c0ea51125014a0440240d500304d50f12485002e0444e442100c08240d01d0100d202c01d4001c0413101050f110306681c03542c0c00e00c2c021043d90300c100340e401d012450180d00501e03d4a07420085170030080e84a009d201c80d02d40704c000182c0040c0340c412020012845450010f6042000c0040c08000b62840c40c0201c84c50165241000c9980f4861022181c0f107580052200700c00c90b0406802a240301c0e1394508100b82040c0d19040709a14085400c100e101c0c4a51000205600d10f50b04400c0020954189007001d1010508100d0050a003400800c40103003005106800501405001e505031400b0305620f840c02d121100c05030400950365140d85c040d002020310303450810215030340001a0320302280d9800e11101d150070106d407815a0300783e00c2000c043c8290301445c55801c0703001650030b02140c0300c1c02032144000c0c41d480224298038601803117219500140420150140600b000c00500e56050a07400b00d804030321540d600c1c1d2144043c224550003a500001400244420020020b4140d8401c0007854130801c80d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 938027140 1250 938025890 938025899
    0xf0d05060916020706110703052a04060e070f032a141207080405070803040f0801140c030a20040e040201080f041205072631140a210c 59
    0x8090701004507030b070260340180c00820106011b520440d843d201c1c00c0c42501c0d050351f81c9403541ca003403131a040e240e041032103011401c1c8102c4085400c464280008161420090076048c080c048520b8000500110140601c20041c000c1141c07003a00700200c1d801c03041c110003010100d503030128100328200b9a42c480225002c1c1d418080d900360040e05903010344284401c40800ba80f980001680c507580d015000750303010f01030014003003000042000103000400d00c24242019151030581c49500f182c07180401c2c070411004e03440c00c1c040c4081c401c205607030700010301c0100064a0b0804010944844042c1d540300d0522050200d40040e81d410b043e003a1b42d20481c000e0f224202e01d41d6460700400e002c414102d1340140020314490700010107074800c10143c00006e108200442019200541c030f0a290170140d810114050000113482641272400c080c5824205040005025484d4030a05010030400050048a19101503907190000c0340c0da82d080d00f2002040c60b0071038189a0322064041d110740000c010002d40d405c0c0000d510020307 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 938028390 1250 938027140 938027161
    0x172506090e0c030f19060602070e1f0506090a0f0914090a03020307231504140106051f090f06090312050f0a080a0b180103051b0d080c01020f0d050609 66
    0x740b007440c080c40308500c1d55440f1590726050050181101c9901820b03d195a00356030000d01c0b43c1c034050301007a0020800c02d498400502e182a000914222000803c0300d000300000f40d540c03221a096450403a482a1181e1340000072600d1100180e000000200b8520030002c0c50345e61a50048590509241c500181c40e41c68091003942c0d0103c00324020010380c0300704007007000f060020f0a69050780c1c10140011640c44980141c8500d480d40b240d002d4005410224107200402540300e554960050f00800240310703c03407419001a200800100700444880340183c0404a850311a80a201c050300c50501403c074031170380310300d001040d60072103000486034184030708050701000380a03006031007008201d05034640c5000b141010032105907102415100301e99443d8802c01c1101e41e1441c0b0082104d0740000c40e001c03103941c0b46040103031401003150388000c540f000c0c3c601c0010344c40e103e0207008441c880d041800142d4482c0c0a80401d030080c414101c07518151000425a07100c1750116402240c001c1008442c0040d49407a8420890f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 938029640 1250 938028390 938028419
    0xc130204051203070317040201050f031e0f0709050f040e06160e0604031101110f01061221050301150504080105040c03050f0610141305090307020114120117250609 72
    0x9804580346c15050741c03940d060103e15952281c4107150080c10485106510301c0990000e4030290007480607803019840101e403059290780e0000710145000c0460800c10b074040d03e004c5003401074a000d6120040034403242d484941101c00113144000440f420340c60b1903002c5140d4000151100000918603400d007100394035180d02a0350650780c1140319040e10124120056440070fa802841c0760302401140200c0205d00030078403646000300303040d10114074482081d01e00603071100e41c0c000308400c0c501d0760100410701c8507910070140c070f0545000f09010b000043c10f400c07007554030b070046921401a030740c20314041004000010b41410220b0388101c046881000c24907404c251210000c49101c0300318001e00b08104070300781c0680c0a40402d0100505004425403401c021501980c1c0115901c0c0120b0740005042c004650b4015049012410b00700e0140b410034466103075400c0031150610441d8915103151412104000c8203001c20100c40350b907900078212a900d600c1d02c4031082e2803248119008140c1c18034000400f0095084103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 938030890 1250 938029640 938029643
    0x62601170a20010f17060108040629120105040b04020105070f21110f0a030e060c0114100503030c030703200604062c12071a0a0b03060115020d030507020c13020405120307 75
    0x4015155a06c1004403420b200080056402c940c6aa009400224180c0b8280044030912039844102201423000d0184101d500400c00d0074a07854041088003140c04207142c01d0f00640d0928000d0358500c120308194400c184100c00c091708010000f04030000074925000d204030160807585441c1e180001070319502c0c2d2202c2465030100b442c0e801800010000a01c6640d41000c1e0190042c411810121407090041c2102c0c4150703094075104040d0401d2050300c0340500c1e000402410120021403030014055069900c0740a1b030140142402803e8450f03100c0780b8203086907001d07030f03070b00348001c407070903464a41012030162905a802c000c21610a0060f161601c0c500f501024070400c545008000300030b40b17007440b0002540b224a05031400000c500c0c10581410300a40c1c45406060721800106440c12150101410320006038484507595251014542c015500401c059a11000c0b0741000142c91f564614141e040004201d601a80446481e00205590043e54084c0059690030344200369984004000ca40d07481c03192040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 938032140 1250 938030890 938030927
    0x2250509060114190504140907021504020a0e041524063213080102160f02240d140402150a0522062601170a20010f 51
    0x1d0400e5000e403000008101122007441d203440d500d0701125480401c48000c14000610001c0c00700b107a440c0b0800b0400b808107040340c6090641c202458080d50303c0c98003061404600d650403000800390350b00d2614060041070760b4000380c07800b40780501d4022208030141c8020841a803820280050704070907040c640d80c4d5120325404010300141004802c0d5842800d4448e441c0e81003030910404554042844215840b07880d0061031135443d001401281c0c3c5030650305400440c80c0781e00c184020785600280481405020307030080700d61540d100580c0081901c20141440c1c10318504040264201003030346c0080108144000c1040400040040180c5c0079076144042c0d4000e90b005518500c04130070008507200400450805080091178031002c101d07d0f002800030b6a0f00381921310000c0b00c003000410f0304810544000e441c60b0b0b0700e03140c04e000030f9016000c40e803006024a070f40103640c02840040440040202c5a451a0000c030141d1140b1349003480d00c102c00b604490603d000034604100580f50b603004480695074000c2152 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 938033390 1250 938032140 938032159
    0x3030a050d0605041a0102061602030406030b120106031407050604142e02060a0b0906010f050319090510060b032a1215040507020d0507020d06020712022505 69
    0x10459458005403148020290b54020014455507988900201800d9140c5010310402200d0300180c10174034010000e01c800303099541d5060210340d01000b25401e45d0894240042c10307041c0c4a001c01d12041c804c6030406170030340c40c082002c401c2c450542d96110300c003802501200c0c01c65454400380302803402039100d15070750500c510320016444e00d041031603640d1011b01080a540d8080d030841600c0c80c909102141c0001582000c01481400149402042d120703c1d82650740fa0424148800024052038200480908000000c4082100c0404201c2d80d0820108006418000d801050400310b8580705680c402c5120103203410720000b500c54400041d28410780c600ca04180880000f01000b4000400c00d0b110203004040401402c0f0b180c0c48a602203500901d4a041405902501c4138140f000300c170805003640096501160115a0071a0311004540220342d060b94040c401c102d103885c0c070344060300800200520340e2034044062500664006101c00b0108006c5c00e000310361919584280f0702a032031602070b05801c10f2078074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 938034640 1250 938033390 938033407
    0x70308061c080a0c03030507260702010e0a060f0b03010606050343080105010207230409021507030305061c030806360c041d04050703050a0f150504020303 68
    0x1030080454003500120284506505603126042c503403040010f400410386000d880018907078188910782e4814a1403e10400c5003000072408400440b88481c48400008001c00203664240b0070740006d0341440e490701c01c85103a00010714044002c0c0c00740340345a000251920410080030f107014010380d401c8580da900d0385469074460401a0043c1c901940800542511000840c20100e0424444440c10041a008001c0c91641600d00130b01d01d0206030f008a0456011204c1030120034110f40300c006501356800000b040c0400c1c504c000c140070b81504640a50b000c002108031b0450741860100801a0a209030340420490380c0392070410000c0c1400440014550f182c05c640c403000240104402c3d0b4001e4001401c0c0701c9100c11130044408117044070b800c1003030101155040d0b06010f100c3d62001c1a048015141894203044c01d08882c50300c92800a2040103e100200c0042030600100b4450880519081029203445c08441e0501c40e40845a8003001c0320069054081c4101c0c001881c41800d00441c0e00401a61405001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 938035890 1250 938034640 938034649
    0x90102040e1f03080409021c06140112060b03070314090d0e09041b032108040519020a0e0108160b130506092d0906010f140706021c15090207030806 65
    0x198070302d031140c10240d000003001040422020340300400d000078015940c0d0303c107000c0346c2000705000714540340c13800d0400c0e00038040001d4855581040110a01e0010300805140100c90003421003a8408151044004144a0800c2d03158200d004885410030500d15941c98100c2200e54400901e400c410028489600d16070350351a041800d990014002c402d10102c8460107418588440d034a43d000700d85c03068250603014050904012010782c442c417141440c08591401d910341c03d807640d1412800403c11140e054403442155180703240d84c005401756840c450700a6031551007140d130707030540c41c9842d803070610945500144040c800c90841d40c03001c0a4501084034249854140400e0b500300b8004070342e000c0c50b841a00c44400d030103040580128580c0c0d0f0018000a19018144644c039080078040030304000070035051640c00ca40003c1080c000b0082c071844140e607030110703003001c2c002400380c5401e6804070380c603144002030361500710341200a00c038252401c1891026682d480f403008034403a0038001008078075a4000180c05140c0b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 938037140 1250 938035890 938035921
    0x20f06010b031506160506071404150309150c0914010c060e1002181c050d050706090b2a031b070c0909080a0305011203090506160507060c020306090102040e 69
    0x4040190a150f91000000140d0710781124070319038900420700c00d010041c040c0402103180c125103641070091015604589404681c400d6000d004455019039400748907561185d0310004000c1d401c1100185130f03010528840003d04075880c00c100004d9210354021078065101911400c094105840b200c04d100401d594034000350500003812103c5000e003000000901b6000d000030507a0482e0b08010340c480c2c2d41c0074010020802c031100c0000040e44c01120301f59000500c0007400a1111001c3c4c1091600e54130140b500c0c00c00f800711030700001c0c200120318040c001c000b5510410901c4210000b42d4000305071080200c840e880d8002100c00d0608c6514000c0480c000f101210700a02505005805070181144c6030384d005425199100c40894407000300081615907641c0c14800c43e4058460340f01004820000c9440c0204105a11b000300e274421040081c0c5034403c00b0201c6081030b80741f503110b07080e5109a5951440584040c2118000740c1c000d014120018003107070010300c02c07502610201c040348105902d07485035040c418070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 938038390 1250 938037140 938037151
    0x1140609060f030319090e01141306051c0605070809030d0902060c012409110f0f220602100504050a0b040201090e0a1a010c110910181b020f06010b03 66
    0x28000300000d000f51814002004d4070512030399035002075464550010044245a800600302d04040170052007405200540380c0c0e98404100d91090183c00c000c05590000e20013940003e0b03001352191030042c101203400b41d030600d030203004800c108896070725040142c500300c20445446103035400400106140d041d05030300c24010f6500103070004e410100314188207030842e110013500d40b88500c165820600454003d410032400f8206c40d010a000054400352004a00e029100301d410304000c01140345650750207940142d9541c0b0181000018080c81d007420200000701c0f0601400c0010300401401505542c1240211030241e0f901c030008111900054039244200c85000d0720890401030600400075600c0329001140b80035183c0c0100000d05407026542d00414052608040c60500904c0700c80d40000c80c803069940001110180c0f4582c03129942e804000202401c00c0e040800460f034201102d980e074000c158000f070200b103480100101c0f072a4140100303030b90318030686403603c0c0381d0351104e80103020750912200a940c101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 938039640 1250 938038390 938038399
    0x10213091a0312090306131203020322060f05070c0c0b0c0f0f0615150d0903030b0406060315050612070c110405010b281d0310020406110607020114060906 68
    0x215001c400241071502821500410500200f01d1102070700d001d0100703a40003450141340c80303d00141075590748429060742c603100003810350100008a503081c100340300c0c51000401d004504920803c52516134000c00c9040c2045020310303d05000036150718002e00e282e5501036000480740c01d010740340600c13805036644080c0c080e0342940640044005240010442045581c40030700280080303180c01c030005603c0da0b101640c418070445812540e086207504e20070481d02e080d16000000304680741982815000381070202c8949800c185480c00c00103203281d1560008a003640c1c60b00d6041102940da00401c141070040d54510841d141c01034001c15201c0d40118008541503120340f4100c0c545022410004e4101c4d58240d2040300450000107010402040d0941140000c0191242000c0003500c5088010714290003802e101c030900790400d080710481c1e0b8040100d5490070401e00030039999180c40b03a8000304549001040d4440510451001c20351280c018001d40c0040c00b00c1c440a00300682d5100c0070803481110191215400c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 938040890 1250 938039640 938039681
    0x6080c2409040204030804090c0e091807030209090709050a02090102032b0204030c03050f0601060905060d020f0d06080706080708040b15130e0f060610140c01092301021309 76
    0x350380b920300142000314080e251a546980c940303000501501c9408501608000c11441000199a6501040b80d000340005207810380c3c1c040311030031a81c9041c44980000e9031002607502081005480083c020055501ca034100b4085512120307400401e038010b500c807071400350b0800e004120091020300c01040135483c41c5001507103a410301900b00012640180c0050700c13410700517481402071010070171015010349a69002041550314046c0c0050140650f402180c0c0314210004454114900940580b400c542c00803605550714860303424910300804040c450b02c4103030302402e0350000d100e0340500501351203400552104201681d642d070303034000c1d9124000c0844a003840ca20120042c035490b203241001d01201004000159410b25002e164600f5905040b60403203940328000308a201c2e10b480c0c08820792070f09a4188040c07007543c002c0d2444001d000e1030005406642c60f10100d1804d012800c0ba4000301c0c3e15500102c54031a0b03101081c400e00740d11804807485890441090b08111203c002d9000a88141005445204 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 938042140 1250 938040890 938040907
    0x80304030813031a0703110c0c060a0309060e07051c15020a09030803090c12070b180105040812033418050a06170a061d060102070509070305090106080c24 68
    0x11130854440f01e01c0002a0203010402403c0d0984607641102d0160a0490b0501d0352000c0903c0d95081c104042c01d004240c0031401003191402070708070b000050391102c41480704540000b00c2d103589451900c03605d84200c0407159400790242c2c8a58407030340300a0308580700840035804400c441c4069880321800404110300602c000010960701c1003e90300a440700e0b00030701071680164040194002200f140601070341c116003003c209501020341260441c10010045810440280e40140e074070380034030781c8200c909000b0040b0320406140d1480040d4443c1081c1c182c0e50000d4807106400f01c04401c1c0196a41c0540400b80f40c1c0007148a010704103c1c030310025101c1021604c55120710110b038424070380342d00c0800401c101902d51465a0301c030102ba20751140142008000389450802c070f802d8200c41101180c01405010408280780364420700890010b00400740402c0c400d400c008074010014042112000100d5290134070200e048080484c00c00403020009081964010031000c01e0300000701000c002c105500340c100702c1880c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 938043390 1250 938042140 938042153
    0x120727030303050f090f070e1509090706020f01060302181f08010b040b100e060309010906021b0d020a0201090902130503060a09021801030c0e04111f090f08030403081303 75
    0x380d4801d60700410325007007070501210740b0f05001c1c04902c0720780c01c0a00800712a540001e20402100c00241140040c2d071900940451030301d0200008036040f44004003001043c60000030004100e07036140e403c60740004c1030f185080b800c807002c90000030360003840e20301101d00c0c001c009a0900d40082c400d86829601440307600001090480c964031800c0c599440b420815507510b8280b151041c07594017541c0074a40c0c160160f400502108850300014806e140110104040035025404034a805600540c1159220050b114041c60108000c914140b9440342c0c12050020610200d41d034003600d075041c2c480303140300e50401d2401c10203504180181c0410440d000c1002803556000c10909001d01e144600005d443e841b280140480c01c024042440e100501c00001000006c104111440441e9000c0010084a86a518005800d8544401070980c0540349160420805550400c0f00c880b8202c203843c1e07500520f5440d8140100480c840c421030100350000d01c01040407801c2a0000d21001c0c480d1007603101d207240c90745e0322403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 938044640 1250 938043390 938043467
    0x80319050f09130e010f0c090e040c0b070302100e2a1e0102010b03070f09111204020d030302042d050d0314030612030403050105010f170c150d020c0a171207 69
    0x11b140c2c551145c413078142440d00280c0e004d020f420801c40440301d918103900c800341a100305100b0782500ca04001804070926209003d2114003000c2a4018041c840c00230a9203030759240740311004540d2841070000c041c000b82101d198810251809011a480c04480610b003540b00c1c060001258155500d450011429680c288840d40241c241c060360890402d0406843c40c0440e2150030440c0d46004d400c1280d0807042c4180010351f5406039040329008900f41c19480c00b10040d025a40c0440b000d4000d800c00007060000d0b02c05c1010180300c3d000e40d1080441e81c0c40003000292044c0c4000039020901028a004541c00c2c05001036600403009480e03000001c83c2131034010315542c4158000e641a0b551100148840d2000c6001d074001080f80c846442000d110100d8996102c80e00c40903e940301e10b14500030300d550810b418080d5040ea915280c011516415480c0646480303c0d010304080301c0c1004c0d880041c0001100e20429100b4410811191544560f10090140d8442c00c254007402d40031801c0f003000801190718080c91 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 938045890 1250 938044640 938044661
    0x30920040608030408011b0807080c07051005011418070507080f13060c060605240c0106050a060e0108130f0213110f070b070f12020a0302070c080319050f09130e01 72
    0x1d48507c0d0b40101000500309200403010484c60006001010740d01c4014260031115905003c3c0e81c0d01d40d24540b06103400102100e00d02c200307007803a0000a603d0f44040b60400034003c00c1c0d800350156910322091008104007101c25501080d004c0c40408003180c0c03890080c014155140c004540b0b464101104282104c0b02640a200081e254410140c204800d60281e0002018141c9a4070701c0100444d000001d000d0080150381081d52010aa50b083e203c825000302005080140c06141c0c01d40c1c450380b0013000102c0110086c2d01140414012504090010f40c002e180d03940c0143c420380c556605039081240020324030f0504000c00f52210600841d81c071002d030080101e4084140d01030742e6174500c0d1800c80a0002d0051404d810300034524240e151240c1c01944103100710301318000069440c0401c0000350020f02421101400303c95104402180440c0300000800d600003450382c0c65820b100d0403510848182c0b040702881c0201410a1124060305e080031180c0488100ca609004104241d03a0030a00e401c50b20007402c0c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 938047140 1250 938045890 938045893
    0x13030606050a0b09210307020d05030306041103101e030b0f0132010e220f15030f030e011710140f0603160504050901090203090d030920040608030408 66
    0x80801c214604003115100410a100f105400c02d81050006a03e0380d060100300c04601e028031003045c0409a0038802c0302c04d1b00d0350040c12401040d009040165072070304100c0d18640074902d05804105034944c400c09403031203490741c3d890031300c0014200500c0c1202048030360392181142e04c8260000c40002e227508421442419501e44121351585403c14140c2c10b280e1080ca220051007110480c500c0e54044281682d035800f00070700708521450054004540003112a070b041050400b040f02030115140880d401c070861101108a05200c01e4440401d003002800350751000501c400c43c40f41071880024090343c603a0325040b00c141000030380346520141902c1c41d0041100c4541c15021024001c0c840280d803201020041e001c00d981290b000320300d13000403900c0c070322000e401c2510004c825040d200c1c13094800c03030031140640700140c010029540d40c0c031030080103500260340d0413402d40101c4400c84030480c803074811054060340151a5030000740d5080e580d902c143d000d88a6040c4c026071207060104034014104004d000401e681030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 938048390 1250 938047140 938047151
    0x1b0a0f061d010302040303021504021203120a0609051905040812190507020304061409030712051b18180c0604061d0418020915040606091509030308130503130306 71
    0x5801c100c40100542525041c540b040c0828004668001840c4d0b000d1030382185031032100e8a8900014012000c00024880984070004041112490780a0464040c0c8030300102405295186d440b100e043e14000c9601042d0f40d20321491588214020b40c002c103412500900d501890488013030100b00914404541074481e451301203003018001421841174a511034054400b9505203420304400500f401c8100c1518211440d02194014180c1d80c01e0009000400003588003241c003080034a4040d4441d43d201c21811340704c040718100c9090742e007031007074094454918211600d203141c4c0d2410704442d099040b600c1001139611820003524003031f45603000100040c0a194a031002c450100060729540c5c90781c0060094040c90800c41280c180102d4034488a58059044171a2041d0340d03600c1c0440c08107681e0070010143d02605118000405541100000c000d880015405180390308183e40f0a580851651000900090081e40015191100d400c01c0616540c4290290f81c605009680d400074500b07126003040c1c0b1110707034a4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 938049640 1250 938048390 938048417
    0xf0d0605090c071214030117070b0a08090607020109030c0201050d18150f060b1603121107110f01020c01030c0c060e0f010b120309131e0906051005031b0a0f06 70
    0x15001300c0301c2d4a5982c50504542201c0032800c0403180411f2042e290502c940981000c00220280050030180010a000c2502c42d030030801c0041241c0002e9450400354000c92020501a0b0f1040c000d03880ca042c4c26890f0b0804d14039050303004651070f6100305410160b240d03450741c0c640741c14041550480b2080d80250020340c4100510b90840e0102c410a0342010019440c3c001c0821052190700d09903030002c140494030380d884615605065821901c41400c1d0740501c2d1906001111040e00342002d40003103806169034652600e07841050008204241000d02c2c0582e102146190f400d620130740108442c11418500040080142e5407840d090310031402a070100c1d600185540c1c2e80c001000d219110000c00d0442e004d400a403400c541c00c1d5160700c01d503040c1d43d0091014010380a26140c4942020a07401c0e1044240b8002c50361024021004014605084a069040001049102008032481c10564000402400d42c08810b030740001d00f502014110719402034000000007600890a40250300201225260380c46644842c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 938050890 1250 938049640 938049653
    0x30c0203070807120b070e060a05040e010f0b090d02040f0c0215090604030836010f14010f0e0423070e10030b0106030b0a09060801060609120302030f0d0605090c07 72
    0x2990009411540040f4041203c1a03034200500e1620b504840304c0c1ca11a168a001201c00f00c484071407190308100c2c0010660199a0300c640100100c2d0b912800900243e62500410380d43c0342042e109880e00300000b0b101d03034003251400381c10401c0a0389c4003c000042d241c00703449400e02503902803090080942c00c96000d200706150155a01580004424003512507031a15660103003d503940130f0000e040c2c0200c3c55042c00507900441e039170140d5407901703040e03400c850940d03007566203000e0b10741e17112411581400c00328001d0602010482449c10f1321040c0c40206030031403c0201d4241507003401001621a00780180c1401c410360b002810000c40f25046001615480d1f060000c0c0441d041000f60084000700840340702040401c02c11900035065a906140108010351300c200003442e40fa03001d420003240346140160009060b481507212804030707240c60702c608007920b54a4034041c451102a10014000d071b04104040700c5c1c5418007074000d03c0c403070641001c0003507010b480300041150604100d41e03041280000142050034440d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 938052140 1250 938050890 938050903
    0x11109120601030201020d0c030c21170606160c051e03070b27181906240503180a03020c090c0304120e040905100204050a1e1818030c0203 61
    0x1140c0041816516550000350740d0504401e6881c1003100042411040500c00c1889175101508011409104030000314001c064418000c442000b1600c1da445510108510b0248581b050000405a83c1008510404003101035680802201c1070082d0a0700402d840d42c41104040721041c00d00e8030720030111703805014946030100c0e9401030840244280300700f501d640e42401000005d5004003080340c616080ea00c02141070041d920307181c0070902001d0340030003d21a6110622800b03030f007075003074080c81a00e46e00e4120042c07150780c96400300b0480041c1c00b0706480e5140154015034200c60907500100c05007000f084aa82030200c0320b981240160445c00355a54540b600c06400350b001220b4031940d601d5030030160b85032412469070b40401e1046c064020f2046a2701c1e501c60f400909115044010b444080070764507124402544140101c41c40340030009004a1a000d90b00140c1d001c900c00040106601403c101d40070b600354802105000e10070b5210080024400d01698002d52424845d072100180c00d801441014103200c1c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 938053390 1250 938052140 938052169
    0x11802090a020f160b24062109010b100c0201021024031a0f060f01120e0a110307151710211104020c030409020f0706050108030309070905010b07110a0305011109 71
    0x5201da41b1440010a13512902c10610121111a41d0381015200c0c0c2c0102d000802c0c0100d6a0004c035801c00054202c1034005240300302d81118030005507942c1d610255408070361284046d0061b031048a0305040354030f00340d0250406690141210ba01180d2070000220048a0741c2c0003106e546103114421400e09400c0e0491075002000034958410500d004030203e4000c0c00c00501c001d042207414260781d00042141d1f4022200100e0040c2900c040541b203041c01d00e60444441c0b038460192049070400a140915407801070320340d42c0103030384440300680500100544001c01618144203441c146200040301442c44d00082c06658070b404801a20600a0600c0d0703102508101105004a0040208401c41d00c804001c0360305030b641c152001a1141c010700e41c14401400f500100500c0345182000200744048000080d501c2680c0f88803c5400540d10340d05540c0c1561000e22515801101c1400000c0000307085059040b0001c3c009000f901c50559280c640c542940c480c40001041084000750041d010b040c9021202c0418 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 938054640 1250 938053390 938053411
    0x120c05041107030302131802070201090b07051914240618270f1f060812031f0b03070e0102010e0607030207170f090a0503011802090a020f160b 63
    0x400c546160001c09100349040141050340c006100c0705403604070511080038052070029414a2035107451001e00a40c000b4100fa8007143c03009000082c819489000c4a10107030788238001d0720190140c10107680700281c641400b101c0c0a509001001c80d01601001010b142090000341413400744e0011600003201d07000038000038000c49050f0001d2525101401246030028160150b8608151140c00814580000c0c06440341c0b07a13004a404480341e00c9000100203006078000050320b070320b540025401804a484510030407020b500140500c4420240c1c1d0005150b01003103092000240c0e4400702d00f4072080e503140303820070340c2c440da030110034000c076240d000d40400306142c428002040b81c060103490141cac1e640001440d00301099000a00d180400807546603d451803d11058401e0700c60030203404000064000c004a43e000e422481000151031405000d07056940642400000c4030240540a00005400c02440c5407401a000c100340c0c08880101001001c10700040300340e1540d240168640003118810161001000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 938055890 1250 938054640 938054651
    0x109050d02180919080406091205070b0702120d030510060f050909150d050a0b1005090f0405071e1e232209020901081209010513030804120c0504 64
    0x584681c0d15040103200112242c501d6aa200007125251404003220820000d801101501c00c00882c20080d205442654030340b2040b0356103401100f9081d040000020701290300403c02081040042001010b2403800503105441c1401c14484841c40e01482e0710441e00040e071303248200101c10318070310000e1001d011645048a111a13010000a00d280942409076104050f884085411490016171304441740d00041c1244074102c0c49810920b403174240170142600d00c40c14001c009090307906c0450340c3c0030541d8001082041140c072071000c5010300f118024000c0f100e5100300200810071541518140440c180841c0072040c5080c24a80d06072045049001400c256905c810010320511190300300d503240780468030794880c1000c0000300000d00780111240505601402c07801c8184159102500901440b500076105006203981c0c8900c1540e59102c7c000c1000c000700c50900805541d03611580080403916000400842256100d440300c0d0702689c070650004d2031010704004181c040003030a00c3e83c00c00030082290304228 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 938057140 1250 938055890 938055893
    0x507050f040e06060c0a2a0b03010303050a0e0910180b0a060807210b041a030c0f0a0806091c020a0503072d05030a03060509191121060109050d 63
    0x54010350144002048030b070000681d07140c541c041960012519901224901001424040c9144288000b0904210036070030880c001c07408031038011011101840c030700b40c3c9103070f18507107084600340c0008103840100001480012070a60311141400c0c0901e03450322180c200c20b4501100c05142c03892090b82e00044906020803e00382d41c0d40c88806004032601410001c40d60365030030000b2a0840da1408040ca542048160044070740011a807100140305010ba07002c012814019821030b0501c4448104a5410f0303101401e101c51038100b1114200c110480a04444e0895031140360550410700f0413500001164402203c1a60403020000349081c0b0319914009440c4290303154850503100e20500f0000742050410f1000040d0a1115400c1000f4090b046812040c5e4450306240403902c2c0e500541440340044e0401101083d10b2070030702d1140c1d001d5110000840c00741e030f41d8208608003500580503200e01000051201081c0f030010b42900114200c09800002d84c9490040d00140c085104c58001d03c0c0941407101c40c510 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 938058390 1250 938057140 938057167
    0x30504080d05060105070b1e070c0c06030e1513020f0901030c03080a0c02091003020301150608061212040308040503010f020315120f070608040b060108091203150d0f0204050705 78
    0xc00c16803480c031002c5281d69440300141c0d81071140c0c00000705190180300c20040000500070820012106000e0903035110b844030601210540303803500f406032044480d460208400d07030283e40402421070300103058900020f00803844d1095003e00b116224003c41d56000c203d421440c0805c050001484200c82541c0507505580700c90420b06250b000003081c0031000582c4094460051120011599008260f070016140c00801c0c0e5242582c1e03072008078080d60900e42d5000005903403e4504007680c00940da40c1e43c00e0b50b03030f01b800c000c4801d400d644102100d00855003034800072003900f0002c2000c2c601901080b55142d16000600d4210313604030491420680c41481402101104440e002400340001c0744c1800300c41020f85849030421140f03402224492264400000b00e1580100400784220b01500514107030743e5581006441c040030448210760720b40c10079200540360740242e03006540c0010451440c4aa0019410041110341000032401d80e40e601c000c0744c0b04021842c02d40261a40802540780041c2448150581407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 938059640 1250 938058390 938058397
    0xd05060a27051e1513060f09050c0102060f2404020c01020c0d1b02010e131e0903020105011205190606080a08190320090103110a1112090a03030516120207060e0103050408 75
    0x5c022250455580d005120039030b04480310050944000b0012440f203460301c07a0341e500c10000308a01602450ac00a0041d159030142988a14075800002c95580740030021014901e40c10310095510a40c240040729051b01c3c00d2014180c02d100150081c0300c007982c814806052151908141401040d403144c2040060342c0c00790b22400203210503070700c0070715401000c95460301a2015100c0304403240841c2840100320340d0b00b600b10010441c025002000942d07200d50080c0b08200c010080502180c0c480000c42c096480c0100410b0082d50007224001101a1541c80090804040e4001034846001c0401c41101c3d5850f04041a04160503d090802c070340780b140c00046019204440e400c0c54170a0f00131440f051541d000303400c04e0804100b41000c5035516146510007401200100031961080d10402500422607035803442181c001e00130041c50342400900e1a6000c0711580d010302241320b403046072001c083c000282c03100070103c5100f0564000d8441d40c0d040040042c01d0100c0d0111031030416092209000100d02118200d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 938060890 1250 938059640 938059651
    0xb090a031e0210020c0a0f0516080c182517010e0708010506160f140d050f0d050604180c15020d0c0813032f0d05060a27051e15 56
    0x1685810540c0c1d0080d0610130f80001c0500f901d0354000070034041280c0030034141c07a110b03401c00326864854ac0f030340e00c001d03030761140700e0300d0250002184a000c00f80b502d00d1a040c90360024040f500003208400072040900c08003840c034100b501155460001c44c510114010318140503010310344c401e49103441d0208005080d12410310566004003000a42c04204d030040210030150b441d004403090032109414130b00707030000020444901d0054081e4000c0700c00c000c1d10820441d01c0220b50084110b081c4180c1c0c2070000c00605c4003030902540f09a0b50384001c02119442c5c00892401405010003c44052508981c006c15540f0081b030b000071900580450804aa08000c080300d0907500680359036260368083c02a50300c00c81050f08040d0503580300b180341401ca1034038070b02a00c1ca41f0301504000801ca42d000000e000300310300a048001c140c0d81210000a81c035000030b511040a507072880070030000d03103803c1c00482c00910314a0743d004c1c0c500b6000300700214144805030f425800c039407841e4030003045403982c5500e4052103038201520 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 938062140 1250 938060890 938060923
    0xc06040b07022a03010b0d02030d03020f090907110c010816031509020301030f062405090a1d0106030c05060405060403080a02010219030e01150317090d0b090a031e02 73
    0x422800791080280300c94240c296801c4030f404442d90802203031003d03044030b074183c0301c3d60078003050b851242064a4590300040d80a401010302150004082c0d0203504440503040c0002000d01890039655103082c506070094805441e0380d1181610210a00e05207a000c2020074180400d0405001701e903d61035104d000401c83e6031400007000001242c000c0220003c940c0300701891030000c0000b0091050003940c0e030003800e00c0b811003040301d000b490f0780310b01100c004a02c90201c052070101d410085400c01001940c1d0003007824800048120800c00717552401165044401d58581d5035000920402c100d10801d0000b130310044031300c1e0f4142840e02c0b00182c4d44e031051380401000d442010584903140d80c000d4050b680300c081f032a952812039a090001c010003c000c1c034080c01d5600c0d030030110380880301c285901026055a400680c12030349071250a20071f0311503074001080613401280348001c00010601d040030007400303440d00c14050f007a05101814020400580762018004030310f200c2103418046600040e002001d00c0e800d4a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 938063390 1250 938062140 938062163
    0x405030f07020d120923060d0e1006032a03050c45010504020310030314091306060807050c0d1407150f05150a03060b0607080a0201020d110c0604 64
    0x4082810301600c01e0000f0301e00d0304d15840300340d9040c0d000703002c41040c4d44804e2040c0603d082645800c400c400c0e0092852508620700304074141601e5039070b402030341c00784401500300e44201c419448100e08a807019441565100d00c0f10940c2600b031a40314105106a0b40c404004a02060540c6c48035a00d5134071040040d84100701901c0017844040b1030411100358144202240e200004d0800150f01c0514020000354001c1044900081520701d094070a40380034180c00e2400c0c2ca140f03400c603a006c0d0b46850302c2c5001760f00d1260007808101c0c030903982d40307184040aa60340c00022803d02d00c0d0100c090801a4007034a007c0500c1f00600c00400c0348500022030041100552600a402509107490180b05224100000d05840b1100d850880c0040b800c3d04100c0720100f11039002c100c41e907a550b800c00d13261405520700b0f59101070410002c1001c038001c0e03040040c00c02070007000d062074016035030f0746c04402c1d2b4001705070382000d81d4020409582083c1188140782000d25400c580c0340c0390060f42c1402a403200070060000b0907105204 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 938064640 1250 938063390 938063393
    0x40e03040509092107110d03300606020703110406050603040b06010903061418160608060f031510060309150c02100507020f07090603030e21011b03140405030f07 71
    0x80014402c940d130208072401d48032030007040c61802d0303510004007558082100c142a288504100b01000d1016425035112401004612048a440300c0380c4005500d40001b40614030785404010b02c55903008150300d400500107249940b519040e103404581000d0b1080c0d1504000300130544a0a0461340d0159101080310030941d6502e00603980d80c0c48075040580401e1900004a51341c02c0340c2d000361b1b13001d079690144202929503d00030a83d61175030741c0882213040789120101002898054014180c00220050031812003c40c02008a031174030703c5072060801c886801c40c081c0500c400b2003901000c00760543e49014030074840e1a0b21004038044081c00700340e640d5a82c1d14000004180b00703118240030f140c80b64809000702c1c01c0c08140259a20001080340013240505000029001c6861040e4021a50302d07031203140140ea41c21003007104500941500042c090002c80305c200040a00303205099020390301b80c608405e0307088059402803c4907401407080b07070364203484d90600000ca0b4000040c1e8a5002c020901e640e500c100d01d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 938065890 1250 938064640 938064643
    0x307140a030807141b0936190c031515060c060906141b16022202030a1a01020307050c1012020c030706051608060d030504031202060103060605040e0304050909 70
    0x810803e00d0380d001702420040500d8442520f03c0d08640f044500d1896525040340c00da202c003001403001d0301c03144c82441303581e8080c8607100101503c4103095810f484218017000d0791204900704400c000c030390200d052141441080b085031585905a03422520070051141d02500303060302450280540c40a10001e13042c40c41c2004001d420242c03070254420000d0065440520079921020800e44840b5010000300c000d8141c5c4000d0801030300c1c086221074051038070700c01081d001c2c410840b1590001c85440c0844103544030440506000440c01219070000018030750310300c2581451803445080e0081e0440d0820808800458400901c41a03005811541310b910300a0b40007040d034100c4c03250000f0286080c0049640200303d0404030180c05842d01950082c4450340c0c4403c4281004085003050b84003141184002c035406040480903840164841d00703001d0702e8031f84c0f6900e80035040c6650407400c07001680800c0c010f0081002da40507003001450103a034148490700e5003900d410744a00a07409498045c0040303600051100c40d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 938067140 1250 938065890 938065913
    0x106050708072409050c15030105060d0b091603060b0406080f0c04050d0305270d0b0c1201090c0e0604083019110c01050403021e1203090307140a030807 67
    0x7440c08404001070044124030041e100800041d5007a0152600c1c56a0700d04140b22407147d4401c42a2000385103078244001c03c2056080b00148400003650707862030850988902c1600b0303000d518501c50083c001601094020280c901d0b41c0c10918041d503041c001004075580151241c0e40040c0700200d0480c05035640c1000f02102e0085501656005120701415400d160b000341c01071030300c07140303001c00a074800c0c110119015410024400c02d54009412102e44800716201021b6160440403084145141c00b281404424503d40b0a80104041c01e0343c60007102110398005810320000c41e01030315440c6c01d19191041058070317104030702c0c0400031403105103402c1c8610036040b05507040c01802c1c44500c01d0301d41c8501041e200d90a07804000417804510303810204000e4903000100f005000d08140d542e246014110380c00c3c040c01c20406503081d906aa0a0340103510f199640d0b401c2c110309601409c005544030200c090415147c0005584000c2e071491141c4503800c03564072990b40041c00d40c0c0d00422110ba964105107054a03031400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 938068390 1250 938067140 938067173
    0x1401080a0902043308010207080f0a0203090a03120201051806130503070b040c08070f0302090114010c0c14011b02030606060c1e0106050a090203060a1a13031208010e010605070807 79
    0x1c646540d003c0b001c1c40100c2c0840b80381ea0410484c1c0c0c8103030b5180d035151400c03407007051005000c0140501850b00304202540013002030325020710591303046c0365812001c20003584032908101d50785401150405070b001e509100e0f5035405000301c0c202502c40b00300024641e07100e0b040a4405580c0c0c1d10b20800b40d50501030200101d90440340d210700c1c60b100c24034041c24003c800780005d0041d01800d000300031000074500450450541a203400801401459207400b02d0084040c0303c181e491414060b0345000394010176848610030300140916150700a000c40c5201c0018030512030f81001c0da00c0804401111405610006000c60707010000303070707611540c580f00003443c10701e4105950400a04a0b030260f0300d010245106407c00380450303105031052600591600d40c0c21080e8081129441c0c1c020591800030071800b158031101401d000c2d10522210f16051500b0240740341001c00750420b85030708600a041b491400da00c10711041c01403a4014a0f40c64035410160002d01c14401c00314040e1052402069640038000e50703070403040704117 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 938069640 1250 938068390 938068421
    0x10204050d14010e07030b0115030906020c010e16081c0e0307080c031005240114040603062102150a031b121a013005040317011401080a090204 63
    0x21840d2034619050682061060615404d1030801e4084140005400c02aa94440384d2007060743e082c034800c0f1203a40c0a01c10407608041c1c9a034903610100e1402d1000301176284a00b03002003240c00d6905080d500e880d0b1003582103203051061400400000300c0104040c442c845038840d04070010b0509201c1100c000c4030600b066581805a20b400155030007000410008410b4141c081c0d420340c100c120202e0084035002ca8540003c0c40040d0f80580854100c0840c031000c0c44c07414140847c2408a440103511150415004400400e99400c0280540d0313070b00300301c1e1030080b084108031140b003011035501049400750580300785814071001044050196019801c10003a420385408814014042e1140c01020150703140309801d1000c1c50010429449035002c50000f55400068440c503140b9079035500420240c0040410499031501503052202c0101028003c07075001d58020740c0c072140d5043c511140140300c0081170340704a100c11510040c031808c84c0d800031282e541c090501d4034000340c4c445840c001324000e13120101c8412400c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 938070890 1250 938069640 938069659
    0x13060501080f0d020111041707030c170601080c180415020307030218100f0f0201020d050106180902121305030c10050a0c080f040f050f030412062304060e01020405 72
    0x1007800580d2a41e401c049508440d5640c8240b40160708a42e032880d42d83e0381c50102000b00f8045400c00d00700824990110b8000c0310146982d030f46030f90518000940090107911940b0300540120001000410301500650010b401009000000140021010501c1c0d0803544074440015050041712140d03020f480e00a400c066540f482c141c60000d000b58014400f08005400524070000769042200044400c401151941d0300041001c010685410b10000c480f101150340800c4958070001c40d900503039000304020380b5101d040048904402e40c003222940c100c0d0020f20f10500c03001c4900107050b41407681190341505a2a100052400c2032170544c426003114440c10302c103409a003000200540c1c056481201041c0040290040428084518200948000e5070070307406100410049a442c0004030203007403040d400c9030009500c1c142101d046802c19404a1007214000200c00c003484014092a40401600705440104c0140343e40c01080c01503001c0d001a24869907201c908000303070400d5040301c0c060b200042c4503064 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 938072140 1250 938070890 938070899
    0xc050c01021207121803030506031204030b150105070c0605031008060907090b041a0f19030c03031e08190e0a0609020a170a06020a03060b0c100617030a03020313060501 74
    0x40060b001e45000c8002204000441c402046034810f43d144036a800004012002c56074404401500010705525451301920036034420714600d010007000254400c032209203440c42c0411400c404845507404250500004001c0e810019000a4032031098502c1810301a0f10b0391160414040179140e540c01c0303d001842100144000c00c1800614101201c00d0300301d040c041d103401c103018082070f91300d1010081d0103034002010300409031421940b000c060f19400781c10301c1e00d00048000001071503461940241c482003006501801403591051202d841030302c0150100045803032840e4000c0c07400800400502d682040141d00542c0314410f900a8844d00074140c086542001040c20f10070000c00c19400e0072446a4008040016241c401c000d03a012004080000b4007441c44a50b11054045d5110b60568410590344d120040f84d030b10602800341c081506102c00038141030f5034922010040790019080009a1000390031140890a000803c4034a400303120310700581c603a10b445c0c0300ca410b100c0d800740c0010805802c3c0380010a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 938073390 1250 938072140 938072167
    0xa0f051c0f030f0c0606061e0e13051b0316080604060f060e040608010509010c18050102030412171204030f02011505040207032a02091b0d27030504060e01051c0c050c0102 75
    0x1301c0303c040234a6100e0008070403940c00c1d43c10f20312480700f1640000e11161005d03000000ac0c0e114961005070341e2004040c0711810010307000b07141d204880c8518040e02c1100f111f403100d5480f08025a04c5141a1010000103041008800000056114500030050500340848146d101e603009180181401d000a0000d41010403100f80600164140340c4001658007000c600b00d00d0580440c10116441a0043c6107802c1c01c244010140020400066400a40b843ca017455000c40140c018408070701440c3c82080b560070700345001401104000004011a810701007480200010780c904074003114800c8400580d01c85903440d043d512130203030910b401301d414500c15100f03440340c1c440304802d480e540c4202d4510702c40c4c0e80e5000380001000342d4041c055020b030b502400881c0d0750320381c1540b000d6910203900103510903200b1381c2849600c0c01405244114009100030400704030f0300d07400c04e030341191a0b0805d0800906104041d51002b0004210b074402402468071012071401c8076005404441c1c40282c070fa0025580c5502c241e2200303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 938074640 1250 938073390 938073407
    0x1407090b19030c0b070c030b0103080904050901090b070f0e0301051e011a0d0218060d2708030a0f060e07110c0a1202010e030c0a0f051c0f030f0c060606 67
    0x650007414845001920102842070990540768007524071240c99091584500300c9030042c400c12031b106c10301c070031010001c203554550030b500841c0302d0390440d0395403107500042c401518400340445013942e04024010b0b001420320f40010b60300052074a06409040e080400c2140c07200b0700c0501d1281c06518000c1030018642c01110280303e556907000c039004075a681c0712241c408070180c50a00c80c81494007400b40744034510b481c0c0c0003480c0c9462000c1c100b425807d900c2c1c0015000e5480000c40700007181d55441082c205c445401340c0880543c241c0c13203180f4060113040d101c0701014800244407404480e6240074103070164101e58440c0000d0701c421650a44145400c00700603000182e445ca4800e030750f20680004000324a04030320798030261000220342d0210061a0760054a041000440ba160315005000c080b100d40e445581c01000149450020a900300b071501d02406a080c030b280100400030605030311208040790502e07255003001a41841c00401e0304413665001c40381c4009181c401001182805400280d00c2e0348140e50 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 938075890 1250 938074640 938074661
    0xe1804110607140111070b07081b04080610080d05090105130812131e0603090c0503120721140708040315050603011b0801090c110703030f080106210504140709 70
    0xc00405c9848540d840ea00c0c06546c400801c58640600040c8007144240400c581041005468480342a465030456845801681085000364050800c000110f110f0401d40d900030000300d030241c010800f140000030002d01c2511407003030510000041064000191581300c4000305400030545001c1f60340c03000c40720002e9114140b0318059500c8402e01048181034410703200d141924099860310310724034240c4194060000320740309a4080790a283c3c00a00b58505000c0e40c07000b080860400b90b40c6101314981080e0075034071140844c2141203170820508c40c85801803003030309034828407100164a40398607107050091071049800080c40b03440302070316a29a202c11500103d0107117000b14000e006001502c00c5407803e0f104181108400a64808010030400e14550f000e44103484840c540004807001d540c0b0042d00c1c068150b8411000240d1100074003020036441500382e409031100d8607200e0351421500841d9145030303007010840000140d84402040400c28000c0e0800f8105403240b0a0380d01c4070b59242810710041100c00c4c00d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 938077140 1250 938075890 938075893
    0x3120c05131202090f070c030309030203070507060801090c110705010e030304120c030213022b0603051213060503010803040e06061b0604030801080a150e12130602010c0e180411060714 81
    0x400c0804000381714940c40740000303580717002c05951991070803400343c02c88283c15020b500003000340c10007244050003000c004d03144c161507441555141504d640115461290728004110019501400c60300b0041014800c40f002440c004d041960000000390852145901900442040b1482d5204119147c81c40204503030088403458000d4840c101e500c8140c0c41800c0c4904030b2404220392200000410b035000881d0440401400141d098481e03072010702d010018401b0030f11895001c00e0122800181550b614060556440c4c02d60540d45400946983c1e4052800380717111034155803000070354a803241e60a036500321001c401090b074442c603400ba0a070303100e040a55050f40082d28100021419410028078003000691012010070021020035001c8010401c01102c02464020045da150300904114003822400541c00d142c800010315205010342100c0104d001c07101400760000d0700c0c1000340d440c1d0044001052524407084010396691810701c420981c0384015a0b0321030b40120341c000030b1000352100070345948044070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 938078390 1250 938077140 938077159
    0xc010e0406060c0213020903030408030306100306050612040303020f0d020912120f090a0302030d050309010b37030c0603090515160507030c050106120b0a050403120c05131202 77
    0x414041514260b0140d40301240701100d9410042c00c010b801c030b540b43d8040180c01030800345000c00090540c1e1181e80400c00607031006c020700405280441121010711003600b02001528070381404141c260140d00d0b228104460082c0006044c540039804503503051940113a55642ea83e010385008000750083c1e070025004040d14194071441c85000152464000840303051103062401e0108111080d46c09200403517084480002c001006880810007403280070220f8070b8060700c1c0c0c500b11110600311610800b09a00c501140240792007801454407004040d1a001840d881c100780001d04c807007015a0301503100030f1402449290000d08282d1503400010854030500582c3c0c4030301c01540b0003021f80a816620385c0214400c5800c205680f034002c81c020222240329041c00009a070058480c0c1c3e00b1140607a00281150740340c0700341c0070104500240815804580740380100303d1400c20782c600415102c107540085ea6400d50300c200c0b80c600d01d80900142e422040c805d0485d282c440b42c8440c01a02210030b0f44400b00c0c01040840c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 938079640 1250 938078390 938078417
    0xd060b07030201051f1a0f03040c1a070b0a0902010e0a06021e0c060d05070219110a0b0c061b0702090a020d050717040b0a140a0603020f01050c060105120715020c01 72
    0x54060341e20300301c1d018042100035041c82c8031101b6210b00300c403421300031000c20040d560703240840d0302c0518400e42c068560410141d10703101111800360105998612a4081008000d000507062610707642c01000800d00081d05810600c010b80b021907000036100d0388900d1031403002500b00c0e80041d0301d03194009071132030051043c0820030017603654000456120350302120500044403201c03070302d03817000c0d91006043c81158400c1c41e540b801c030840e484008030240c5201c40c030810350801034280b14500c80020301c8425404e07460058260300003621640090464500c8030281c5036181a00010707035050319000c9030005c3c24440c2c1e03403c1c03802e0410001e40c450529420640d003050000741703804d0302801c048140841c020030111041d6656a07034018401000070101c4002c1a80c840c9500e03406c0c180004e0303182c0300700407402c3d00040d40750850041249404400042604008042054000040020a110b411284144d603244114140c2a01207400c00465411042d10b100c50010f0300380c5129070010303e02041003000c3e200c5510000c1d00d07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 938080890 1250 938079640 938079661
    0x1f030606020f0a0b1f0b130f05011d13110301080c0d02060403140a080f0d0b04052403030c0124080d1b14030414010e09061f050d060b0703020105 64
    0x2e0038a2449401451403100441c408410869001d004603026003800001c0707800c84425100241c100c0f88540001145144005012148181c007411107180e5480000b032614000a01700d41041c900c50100050070501c4403119107030051107600004e04039805200c40950b42c0b004029a8000b44104140c502c50404038200078100340300d0b124034203a005400c062034503045843c0d03000e52449001c00025035104450030302010032102c00140242030000850b139030740c0780410780c140c000ba00c19100d40a4400c3c0d2030801031049500041c00561000c040c0c3d00e424400b07200d2a240000e045025400c400c8000e5401d205020b5614417203424000c2a00203980041c1d400d050b11090001d81c0c411340384540d140810100026000c0c0e6845480524041038401d0480f03030300426000c40080d06540243e40200c0d4a00c460748454070703166821140711104c1603400d0740c18204c1c80c680230002440d00c400820340c10728003142443c2141d01141c402c100700c801c007010307102d014844ca030740c3e600c49009240d01644081c1c005519140c04135007203084 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 938082140 1250 938080890 938080903
    0xd021609181509020a21030f02120a0302030718050307060f0c080c01021c0c020a0f021c030503010623043b0f0601080405120a05210702160608070c060b1f03060602 72
    0xa08034601600c148161f81e0a43e480c11141c13000e501944074100b8070911540040004200c4611259000b584904100d2809000928900303411804807102c1d201c11700441c3c600081000456103149828440c038030355010f00b601c0000c406d00020700360700d1001940000f90181500280101401c2c11071819500020352481c108072000e1905000058016900900c0030a101a603403001d100c1c002400d45844448018800f488028166001c4001c204017100400410748c02101c188802ea4056a85480b818038203401540b84d0300c2280542d14074001c1111084441d2005010550b01581d00b00a00745e00100041c02c0650700c1c00004c4443e4607940f1342400000f1030039441201c8041c000c1e548040101904090400c2c20045904000c0e0f602c810000180b050781c44000804030010341c05002d1040d420400d08100e030f002428081710200c043d103480b20701c00741008a55800450940c0c003400b1480d02150b02c40c03161400101901c040e1000550000700100c2c0010b100410b03520b00c2d82001490f41b0300304030142d901e00c4241e84840 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 938083390 1250 938082140 938082179
    0x80a0b01060512040b070509040203040b0a1109131a1203070b0c04050915031f1406060403150b01090f082d0307030804020307050904080c0d021609181509020a 70
    0x5070fa5101240c00030b80304406450300304101d81406404e01c20010f010408a8104560584148a000b003c2c4400780303029106007003038800001401b6142c40609008070380120400d002401d4859626840c4400306e88030f00031912184400141421007000b1660625990794001000503580c06d0030980218104083c5c6901300e80403150060202080c41e0b4607100c010f5a14840c5144d01601401441007003880c0d440c02c0b111585070501a280c00040c81c12410200100380c0b00c0040c420341c00b5500c00c00061001c9a2010282c0d000e016990a000c1800b85104004075001c0460354004000441c0640000c60005800300b81c8005801807000c0304096078070300c8103945410110811034009170750002c010060120703102d4203400e03074802d0024044504240e80e900112704030420841e410385400001040500018030181711000d0801f2084c4014a4150510351001000034007500c100d00c080c944d181006000b45c1014a003000010707411107440307044901c17501124405410744600480c0300c0d25000fa80400c000141480886918 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 938084640 1250 938083390 938083417
    0x106060e210703060e070e060913020d08130b180f060f090406150503011d01050a06080406090614070f080f0708060303040f060201090605090c031f02090a080a0b010605 74
    0x60040040c240609844025480500402d140403000c100c96005010200c620359004040d840e2170400d0f03200c2c030020b019141c644905800030510401c1c9580840c02910560104d03001e04407407000345012012445150b141050102d6002d200089025131034002d44002c0407031510151000ca04403040203030b1417200d07402d80380d4003400030710508e030030014030030050405c18501410000c0e030b6070789400030b2141c4442c1c02c0310550000f4100000510820450414403c17800c0c0d641202c0b0023465044c10300141c058401170081e101080240030020781480f0b0b07a50017100c142c680026040000c1a0310912601082c9011182000414011903400e06450720541000e4070624214a1070f170740d04d4681d04801c40702144003520342c5905201c10700000c11410140342c4840c0040115400000e8811414908030f0240c030001003072071203181c20030180b1603910348006c0340800180700703491076012006010030551402801000d10b4250099003111000c2241c900c00a0196007090040507082c281b070380c1c0c0d031004848a101302c00706d44410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 938085890 1250 938084640 938084659
    0x60402100806060d02040f03020102280803070314250906020c0f04060e130611210601020102130e010504110412110a0b0d0f0b01080702120d0e030a02030c0106060e 72
    0x1003034403449072150090b0700280000d1400e440c1e006810160381190f00109100010064100115a01001809007161000502e113404862074000c54654012080c1c0281c01680c00000280c041d03482503010452140c00d600314640e050a0903403002d0146165949441d02d114010120450164001e940881c110b8a05900030401054040d040c005620310103105a0381090300c5440104840c80411411407041340078110029422001d41850781c1640d50005440b040f10004000418050095840950071413407440c0d06540c030341c0c6450300101e00a11801d890b4030704d0b0913540c0b030001c6201c4c1c002e191868100c410848051081c0f0844078248040ca2003180302c0e055100341d08100990004041c18103042c09418010215410290344101041c495889500c82c403514581c1c810314110024003074441c1c140110b00a19000c482031521440103591550303248640140200c02007a660354940b0a07411490020340300400780da841d18041900030350789401c524141da900354200b10000c10841d1268074100b0f8510382c001c0801c2c51 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 938087140 1250 938085890 938085919
    0x1030b1e102f03131e06030207150507120f02070605160c030c14010203010608041b0807091a06040b1c0513020108071e0e01030b0a180e2b0e03060402 66
    0x60240e004070041c003d0109101400904d02600403a400400c003140c2041501c003443c8910803000c440b2a00804141031050050a012480354202c850f002d807420600000d0035210700c8420f44203103500900c400409824450317411a0052190054064248611810702050f10358a00a10050030a00c1c104400540c1030848400420310807141d000c00580140700c21400c48044580e51800d980c0260007003008180c0034400e00042042c0842050903403003020490402a50902410a4450b4142e200e550704461b12101487c1102c41e26032550794514800a10381503949a403106116416000803141d400b48100c030100c01c41c80d44206001c2d5910610729880459250200d40e80151103004e00034203200d00700840f100352101d036040e06180d1110342d090303075850b69404a0f0452000500ba00c0710200351034040c00c0c1c40c840411001e0055140d810031103c07629008205019040d1105c4d02c0c0030186040000502e00740c803a40c20381e414a0841c800c00165040d03854004030341000e42416510f02d0140c40094000044051008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 938088390 1250 938087140 938087207
    0x1b120f060b0d0c08070510021b1203130806010905010f0e06060f090d0b010e010f08030412050a020907081e0f0403030e0106150306080c0301050c07030e01030b1e10 72
    0x50a08801000849200c0c8261683e00c400c2406811035409944040001d1001d854000c0a0014036a2103100401100e0080307003001400d05616841640990080c01c1003121a28050055a45164040281c4032000d0b94402d02c455581c00c082c419000c4c0c003481d120012402161612490703042e1a28031b0302100b0552280d100384504c582c0a000c0b6006501e80c140031102d0b0580d5000c1030750810b1030003204d403d6069414002d001030400da060740310b10310702e6100706010014030304003000b52812500c0010360050107101a0a01504100402c00020341c444074843c1000411a00041708501644080b0300140f85c1d0341490240c1c64079000c00f641d04210507044080085c0000303109800624010f4400400441d09998542c0c03440031280300085018007107a140e9009000b1800c0170031042184010440082c419800c0c90340d4111094415460050100002c000a540383c0303902035048002d2901020b0906161081c02d580c032010900701c10701e0000c0c42507206030f45144407030f441146048403c4a9003416031001d69044803004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 938089640 1250 938088390 938088401
    0xe0c18151b03090406510201020910020102040f0605030a0609020c06041509030c110409060f0c020c03010506061905130303030e0105101404090c0905040809030706080f010e061c1b120f06 82
    0x2c1014907100b00180400407440d06264031b000943d40001d80c403486400c08100245902d0203440045a1040c00304101e000c40000350300c402c603015400c00b13035070340c1c1c41d14407040b4090609900100212400003401088940e800180c043c07180b4040c2030348403800e1100801080075228010700240005903481d0404012502a0102e00d0040c0402480045d5000d41f035601c500546080d1142d48941581d03c00d291840d6179014080d6601c03c0314120000c0085280c6030002440e00d0144c4003c1d05440c80988188440007406801210580d0120b42504000b02c1d80d24035000380580704490f2095800e509003004140304038000c020030800e070347c44a004960f0a6410405100c000d1000c00800d954000050320700241a220510443d4000d5024400040e691100d400625140c65010741c40041001036250800c4804800e868802d41901d908240741041601e501e400150310b0380180096000c1e00c903046d40c0e240304000f071b80041d0604061040c84040116980d440c1c1000801040900c05409040440c03440e8001034001d6200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 938090890 1250 938089640 938089739
    0x70f05090303191215090f1d030d0e010b0a03030f050408060f010513290402160c03020f0312161406070804110a120f06110d060e0c18151b03090406 65
    0x10040d04400c10461643c03502440748d206600001090340c00d0031a02e004a184c40d5412170004e0102e1400840450000c2c03c00740b00180410a82c0c44d00445403910a07003c0318001c00010007241c1c60303030030401303140e0020150a10900f8410002d45c4e4981e0441c0615004021401340e590200207407050f403044841d0000c10780300c0b10183c1d01c5a030820860340031603000e44000d0005405900c0b00964a4294410300a040729203102c0c0354801d6100503144580200040c0446401641202c803e407400d502c60b150008041d20784400c00b01690003480100548a40c7c0301d400b0740d11483c041e005210414000710188450113000303004031003640c1200c40d4888c02003080c0240c040c010a1140c4400100d10161780c0c0358111a4002c03010500d0a282c880c0c90130028500780e80441750700020941c200901e4484601d0303d10103130388480207100c2c1c0600c07825403009503c01130f110107550410a15840e85024502c002c0b00c280c0c5c8036804541c80070711543c54600017084440f102d4000c000d07100d1002d10300c18170f640c2d0113080010078400764450 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 938092140 1250 938090890 938090921
    0xf0f08060d2103050603010c02010203060a1a09060703050d150b040e040809091906050919090c0812120114150f071208040501050a050906070f0509030319121509 71
    0x25210b80d03905030207040442400d095980003400d82803000825003074500d20185107085a0040c8144002a95045440c0023121044500901e660400400c41c02341ba024801c0300e551f210358049a25018150032800401040e08440000c103d6403006100e0000c00300c425004646c0e800c0b0044c0400d0100c40c0000b0109034105000310389050400304010005001100101c074005d0700c4808040c400d030050354890240b0303c050007040319003903405c0c0307400c9100b400c08a6404850080c080d445402020a000c48075038031901800d01c0405681c548200b6003c14485ca0740150041d05000722008000a03240c041c0707418024011a005104019481854031030000039044100110310303505040018500045000c0056500b000712611412554940740c180079084a400a01c02600d01c0d06150410402d17100c0400c4080e0b00c000941002038200d12609000c40300d500501000035054403001a00702d59038a1400e10f1507000c90b42e169a048550170102c59910305a0340310319a031791100c0045c40800e0001011541101e200e1002200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 938093390 1250 938092140 938092163
    0x702010306090c1e0906120b0f0406320607020103020322050d09050d050a0204020d06032a1505180d02060703031a1c06050a020417030405010f0f08060d 67
    0x240b5030011075100e8038156001c601481d04000f400c140d01803503400b1000b2a41007003443c1a03d4501d02409030039030191101011a920062425960b076a6090a0041400580200200c1d5113070162944c103a1100185c06503c0c04100e20954450581110115894840034011b03030f08050381940150080e40020f010310481c0040b2403480003c08582403c113210071401103005140c0e40c0c1c001e42c00a0400e0017603030015801a104030034408046000002e0035042e50380e05860040e40d41087e082e02c030004068175000288000d807120500303c01c200b940090046440201c1c030380040800d6854106c8480b048540c0c0c018000310700b06010314000c011070307200c8980400c2d40c09070400300c054146a000840070342c010f8004501195603403003c00e0400c0411024042c2c2c002e02914550444c0581840c14070446200801c000c204944034800200e5640140e01983c0084c03410084040800354103607141a1680c12900900740002c04803c00340030044c0c4600d2440c200032b00315407a00d0040d82c03601d40c18842a210f1100d002d580411420 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 938094640 1250 938093390 938093399
    0xe03090f040905190b06011b0b0f090f070b04030501050a0b090114010e06071208060f0105071719090303030f02130b0703030b030304090903090e150105030702010f0f0930050702010306 81
    0x164004c01c0780b240b20310705c201000c2c50200c00142a8118800072441490a00d601910014000741320054024010312110302c015500c501d402850b000361054007640d1406203800c001444040f040c00350054034030481c02841241d580c400000211000450455441840d0100422440c1c2c0003500e0781140369410700d011100101d60b40045100d0f50b2141c00708803801004039108004182e40804410b411030000c5452000e89890303000001e040703029000f00a80010481800000341d003048404681c24407903140d218911360346000a01408140451205030f01007418001030485160540c402c5605528074007000501803828040c0e101c0705070700000c408500f40355803914480c0503580c080000c1c100411a441d0701040e0f40d80289030040001d0044c2e440350303a030001603070305216900d00800741200c02e88200b0b01e040c0f0340780c2da20444d04030702402c04083c0c00e400c00b6240800710041c41e20340d80c1044000c00d005110280c02c085108000042d1801d4410004a101503410f2070380c0089480341000b413807940e00525000c00d05580343c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 938095890 1250 938094640 938094673
    0x504110a2001090f0c0e0f2e051005031f08122a0d02010605040b0303041a040e090313080f06070305060f03070f0303110f06060609010c0506090609010e03090f040905 73
    0x1103040131740b0345845150b020030020050411041d40f110481919089a040828203c0310304200c14240b201d02c070041c40301c00c1181096120488c002000000c00c0c80d942c054a040c006071080e031056070300400200344102c912106071143d141000840ba100f00003050320303010b104009552604a07020000f402180d51140d5030b072038800078045002c0c5000070006400528481640682114096401240110300700f001001d11542c0100c1a03504071900c94550280311901040010a1845940c00981c1000005c02c140240c507034001000e402c036684403070400784500707884019066a82294807a1401c182d401000015075041c4681c11183d0404805000074402c0c1040c0340c0020b00740006500f10030480c4034009020000e00d6070100c41c000800c800000940404035039043c1940e21031500500351030081d5400128048171f43d00c540c01812540b50071605403105801c0501e0050380b01c0e501915018215800c2106c40795094401100b00d4a0640009044a50024519051201510082500f900e503401110200350000b00fa = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 938097140 1250 938095890 938095913
    0xf12050c0a06290d0204020d02070813140a0803031602190819030b060409020c0c0607050f2a040f0207170703080109140f090a0c0f0504110a200109 65
    0x3141001160280d21400580b03001115001290040540c0200c3d01856840f500032040c40141c0698025941d8002918400c0103445103c00c0108610380c000b0f078030741c41030402d0601403007500d0031804804c10140340301040015105503405404540e03001000800c4032070414910208000031030b07005460b04d984503020164081000741e601960722040c00922510a41008000f03400d0369030842c04d08100850401020882600842c01000e040e65030015403110116000c105c040a4000d00803c280e07510b507060314100340c564004000c0880341d2311030b12242c034803964524100320030000d00b254604c1a0b00040d00c0e003000050080f52440040c1142d00f0003046000c1038230006807001d460065401d40755034101d90329004114880503032201550605d0300c03040c5619586143c25080d00a40110240a203a441d5440303407504004e00c8180081118624640018111901645800851300100c80401000d5401262902c1503c14015103100091440d5a802070f00110544902d1401440c4d800018030340c101560381506c0203a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 938098390 1250 938097140 938097143
    0x30c130509130615030503070b0a3213080915070b0103030201020901080a020c0303071d09010f06021b092a0a031d1b06030a1503110910030f12050c0a 66
    0x4030507506820501105000d070200e9032155025540d0000d207146c540700d440c1e001d0440010700c118071100204045140c2d0782c00150700ea40c590841c400700002c8100080e001da00e84001085840340090b40098024449110b002d80c2c942c0c0c010b000580780c00911400c101c2c240d03c844602440414041c01010f0114820408442c00785103c0e0700016524010080050b155000081c0b8142c101401001350228054010095031307000001414848018042401c81c3c4a401c0740303450354540c209540c0800010b03c031005041c45004c841c0c280d002e80d0b1040361a00d080c100e03000181054075822423506004140155409040d19028080040728041200080c0301c190265601514402c4006910ba00780741917000c0f082c072400300044010800526846141424541e0b0300380669031a05d00c9030300003000007040450240c200940c41e10418440c8801d294491414404012503804100d01440c107690019504c0000e001c0640e05403070700080e030360320303012426a5016080480f0742c030043c0403c03070107116840c20b540c0c08001140c0c019 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 938099640 1250 938098390 938098411
    0x180609010b1606230609040c0312030e01240b07050613110603040303090308010e1528230301020403020306010e07050904060303080f0c04060f1107080307080301150f05030c130509 79
    0x70501c6280c08130f01c200000c0c3c0011300c140c00300e00c24400080c08442084c8100da0b882180c0e800300b520654410340c010130084455000035401c024074242c40121040d426180c0d103005401c0a01c10544800b00340c231240c0250b030030040c815030200c000b0842d007003024511422030f18460b41e02c41401e11003060200f400c5420581d004c0300483e888131071080030142c000821602410700744000080c2468891121000d6001601d0b555008032184004074400d00604680380070120280665203c0080c2d407002540b4150314107a01c40036204005542c40c1240d403906000722421a174000f0020704080e42000400c0035071130307070240c003402c00e100c000c002040b45030321203000d51f01c019402a100d07600c15281a000c10005a10b0041003684480b204010a000440e080000c5100410a51030304407540080c42040310324152031a00200f11601c03000c03980c003041042c842c00945c1a20b401510705121003003000015100302c030405d061603000c5002800040c80001c0700101078030038024000380c80e4002d02e5a0354040307082500d0654210081 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 938100890 1250 938099640 938099681
    0x40905010609020c03041a03060d06091109070e0a081507120e10020a02010c11070b070c0914160c0312111b0f0d09081c09180209180609010b1606 64
    0x1000d00d0303010314205120301f04001d195241030000076800001410009080994802c80f01c03044c002030140540400d00080c00d007140d83d041140010b090704c0ca0840c921845002c04a50100d44d656000c24410b0711103554a81640302c9440e0b100040e200c144442c031a520b101a912540c1c50354100e4108100500d0303d00120006950754010a002420341d000818521f0511045980c44581d0480000d4454100c40314448030503154501c51508442100f01907000d030001d103041a02c450107800f5240e000f1030040c1c51448010b001c0900b40f050a03190074031891005404644940d56605010350079400c0007a07241e140341841031401b01448528540002101c0903402c0c0f99100c034558921410040114502e400384a04008600514218039a036071030302c03a401c3d0840c0c5c003101e4406110b03c0c03d0080307442e200600241c0404ca86150680c0c11458000d4201c004018031543c2c1c41c2211081c115069161540502d001034040b40c404d03801d11207460615030210400c8078800c88604000c4020400d144600c01850071a0031902e0003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 938102140 1250 938100890 938100899
    0x5121911280302210c0103027c170705010905180c0c010b0901030f0201030f05160e0609030a030809010e01020c100b190e07030c050a0e040905010609020c0304 70
    0x414504c0e9112401810803107140c8441d0344040000c045507180d10900c1c0145e81c9890030844885d0170440326034183c0c100c9841605c18001c42d030200f0a003890381d4501810500074501c03034420f24144d82d03011009038462030103010300b00f420f00c44c003001c041001e03017601002007802d256890300740c03041050114401c1142c40c3c200c3c0e0010b005a44c0e029491f280140801c64000000b10080071b0b40d800b40500241010611000c0000e611207e2102034101c1c5074044c00c000d014407015a540d06006200003851030040b8006854614483c07403c400c0c500c1018050803c1c451320000e0202424410b860a40a0203001c80e40040244085c0701946d604001c1d660046220343d41d00b11083c28412202800e40300130303001112417030b4011b1000c50300340100007644000803604010085403402010f80810313011b8800d6070140f13030200c14110021503002c1c17044d208070303000700d805039020460705e803024000f101c1078019002c112000a091011401051426401240d0028050000081ca00341e60340340d4041264418a03e4018942000ca000c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 938103390 1250 938102140 938102149
    0x90e0c03091b100305040c03121707050414061b0102030114040e0111030c0d180b0403080a0b0f06130905090703020111010903050409051e070905121911280302 70
    0x3840311070448010702e03800b1042400100d802111902903410180d940001070148a00207030900020758200015250400003100b006000050a0360f280d04d02e0440d100108038910303c0f401c1120119a90801076803c030ba000c003400c0080d00e501641c01c4550408106480c010102000c0c07008600034005100400e40128000041c402581c4421490100f0345c0d24200148d865004400f08032a8884442d50042d80d413072020103024001084110504040c5c030700c480b00206e041143c0e805442e4080c0d8003c0d00d411080d5650760301810190346840300d8182e00040515032066807800c00f6000b51030740c00d000000780d4800f0380e2143d0340342044481c22981a00d040d84200300800c15940c06c011501c510485000007403004000e00e4074060034900c160312075401c0707081d5150b00003158031000c80e0f08140c103070203a40e10781c0e0114144000000c282280c903016184c858a0b1000918042e660000382d600000180d1084416845e07006071588440f079011050110f0b000860035400501502009404518201d145581d80d12601e00794018070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 938104640 1250 938103390 938103403
    0x90206270a0b03010b0f1c0e06070912050a020907300e071a0901050708070c0f0503151f030b040b011404060302061b03130b0c06060301020a05030115090e0c0309 71
    0x95503400b90400c01840300400070001ca800c20107020001e42d940303481180c10f40c4480c04400c1e90541e44140390410030030f82c7c2480450128000c140d60382c0d40d45240c40d01d0b209610380c220305618000b099a403020200c0c100504211600071307070121440c1801e00f18801480c01800202c031481d10040302203018265080d1b00140b880c8200c2a80c200504000d004650418841700d0342994082c11803964a4004030380241941c1c400c00860b2645070b03016207a035445214500d0b150281040a00500c500c03034404110104207400d00103000300c04100b40c1c40040fc255100c8995906200561103000307a104942d81c0707004400b080361610f880c3d00491207000e50148a40c50000110a85074501210903c903030b080640410250340c8003010366100c00c0c6d2401d6440010403e01440a15501c92071140071801450311720001b90042400003c3c003069820f000948000c0d688480402d4201e22488100501180044c4018003400c0c10a50f81c80e4011192414440c0003203031200d0f01d240010f10101e5000001100000c1000070811342800071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 938105890 1250 938104640 938104649
    0x1150504030b1504022b0b040e030a031e0c0c0302100c09051e040c05180a050a0e18100b100801151d100306030308010b030f0a090206270a 61
    0x1a60416096540c0c1c8000d103100a401d0030704007945106000302659903581219098155884a0030221010f060643c128510700c140c40420b0515000c081d00340d40c2000c3c02071900407680301000e5031030900006010f600a004400d2110002d109042c09140c510616101e404500356407515070380c100c082d192500a11b045000d2007500846403d0159181c100b03504840444103a5108a076071b0740302da10f5540003220400c5204131107290b0007420400030152694000c3c0080c0031402c00d80d140d0722540f1250b642030206107010b52180ba5080b10a818040144004030503c0d545c001022040124500c5c1401d09080c1c940108040c28281c030680c0c034200d645070303442e05013000d004a80040c01c03d0b0b0050362503c00d000c2401c10420705201d0510681050b032962030f00416200d0560048018000a900003508070001c008180c940000c40c00f0070901c40011801c1136100c0c00b0389200305650449c20b04203030b036545400c402401992000b01c0c0c00120074001380080708030045088820b002c0b120744040da403001c15010005030384c2c0c40343e00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 938107140 1250 938105890 938105897
    0xd14040f021f020c0103021b1c200606040e03040801060e160c2021210403080a0e150315040f0b010801030f030c08040b040510033b0304030b0115 64
    0x92001c407a0040313218400c140f400d090040c0c0341d0000c13100c91880a540921010751b00e000740d1a13845142c0c044851100b1082030127640da600c400458804600307020606141e400603a81c80500083c0c0e403403402e030308240320000c42403007603070b003402d60700c180b401d09491440c1c2080c1c1d141c80d80c44c0d04000c200e50350b00c071810900175424075110702c0041e4076440340380c68049041e04450318a483c1d800c918045454203c14a00280c0080c420034200200948404c1e44030060000c03040d150308070342c8001c1c01402c4944001da07010740b0f400c648900d00e056180031007a100c2da81d1000900340c1201081800d1303a80385084c4c401651052083d0303400c402581c0046420007080f02c080700c601c0d060040c58842c1101590341d20480642c19654800c2c2a40c000800c18182654030324940d19009000c440001004600e540a00c00a801120402d0702c40905a004280c0150280c40444418203d124080d403c086500d11a082e034003a07000e80d41e00841840001f40071152419507009400556142480100401601126106c6018803030b0310761a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 938108390 1250 938107140 938107189
    0xf010309020603040f140703080904060509040c0905040303150b090405060102061302130e0109120306080c09070302030709030c080708060109060b030106050c0c030a0f1a0f0c0d14040f02 82
    0xc0c001040b500020700080c000600502d0070504002a582640d40700c0c850071412036604030369915103555540c0c814091a40500d0138480000341601740720004a0146a0190112403024140b009020090038018403e50416458060100310000c00a0964000d4050b4450907942c6100c0f000900064a1b0040c3c511340c1194010710811982080c1507030182c184a50440e401c0c0c0180c00d644a10300301501d4180d101c100e85501c0d028a1804014007030203100341d18280d40d00e080c440d40e0b176510129500c032400c070900d4a400040000020300c0d098800ea00659004045041c5104110f4032070b00c8100c0310340c0c000d4005001c160b00c400c0c424400da0004004050046c6000d28085c0320a41c2400c2c0011280d000620651042c4180850250b00e80481408420389500020b011148140c5c0a418000e0198840f09420b65000c0705942d00029444642e9002c42d10895040e043d001c95a120311050450030b07070200b2204ea00507035543e540c0111110404040c0c5000301d0040800f8248907002e070041190a4210f124088644080d02 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 938109640 1250 938108390 938108393
    0x70501150b1b0c09010e160305040b040b07020a050a0c1706060310020a120212010306050915010e060d0203100c0228030c170a120f180b040201031b0e0f010309 70
    0x1807007140e50501244040008000c00d481e005881c2071118458554050340715000441c0700c2c800c25410314414400c3c40100406603446680c00d800f11201600d010385008546070015000c1000048401c0c1c1084461045031008850307a1511410030700b12910031180071010700c000b00400e40b03810010003034400801005e40840d08000b80065a0f0301280341d075201c11190042014141c5500460a901041202c1c403815950342640c42000000c2e00002d0200b01c851510b4080420616100025449950b040182e03041c0144c0c0d00380096418441c200402199008010341e02070307070042c3c0f41807003070044149001001041c0900011006414211800300b03052280c400601862111080410380d0342d1110381506001a002c4514103003c0140d0808000e0640004400180c207446241c0c810b90004059404000800c01507410807070b4082540c0801d00498243d80d0352450140118400d00c2c5180d8000f441414000b80780000c0c07103848180c0a4509840c403000c40d034a400c02c1036041c28055a40000b501d800d290800a407840c9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 938110890 1250 938109640 938109659
    0x1050402010e04152c0106020313060f081801060b1317150703020c01020d020703020c24091201090f0c1503020f030106230c1e070b190306090c0507050115 68
    0xc0707124901d0034002e0000412110710f0540200c00c0c034120105d0075240305603144c1c040659a5802918446106030500b2800120540b0520b000d003811001036403802c80e10b4a40505550811901e015080225540e41500280701109180140004060181e1502d03217a0306e0301c4507030454164410314100359074014148aa231410801003071243d2240550400584580c0c8421000b40240140c40d07030300414510000346030b8141074000405613106281102d54465404940e0802d40e03040440412842044205110000707a074648050501ca5114804000107050308042d03c2d203448901070500c0079110201407680130300c120700541285030b010f1a20780c14107600c3c1071100032120882d44030501c114010419403030038040034400382c0c10390ba0015480000e14981c80300002041144c4440c01d0901040d40d04080d02c3c2e0005150300c010a500d8111030002145c6810a8210224604200e02e080ea4400030940c0c2c9103000305400e400340c07144061003011030740d55a440300500d00d4400d08640f0000e802824215001c4420800d0040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 938112140 1250 938110890 938110931
    0x1605010b0901050d081b0706090806090f1002071b030f050f010203040807120e0907110f07030c03170f18090609060a0302190906080f07120503040306052701050402010e04 75
    0x5106074031076a508038020604a00b021b00315141403090081403030000d9880d510102020640da2400250340303241d00c40382601236407440214072000841d0040d14586104054541c0035247e1a4081d901c01a030582820154a0804046400840f00caa1070180c0c10340c184481080342040d00075599000314a0750810b9114203100340030324100105840442c0c000c040000748030306181c0c0344103075001d0081d4002e41014680601300b42c60004c8101c030644a405401d040c4000009624421a60011050003010f411502c4859025044002d1203144450410460303a0110202000308103c071540c41d0000754460480c020440084805000709100d0705a40c4148102c1da034814000b0760499604490000f00074030b9684500c0551000c544c0000182441c1a10000340c03210081441004c10f25020117030380380a501d6042c5454840248640503010354014081030002590b10f40c4102d401a000b9286941010340030100c840425000023045862651604244802c550304802c3d17002d0504021103040c4819001003031a01100314 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 938113390 1250 938112140 938112143
    0xf050609030f1206010903021c140a0320030903070f08060a0b03190501110705011b050f030c070302030d020c011d01050603030a120b09090d090608010510120e031605010b0901050d 79
    0xf0028400b26600382e0180000c50000d40c1d029210511411019152442d0b11098000070f0b11030103a00e040081d00441f012a80e9081c041d407644807200c02008140c241a0441007007480b00c0314920003040011020303542042804000d05001440a40760b900740003c03142003010160034900014140100a102990017050040340f444180c0f03040041d0780211b051513405402180301d44d07140070200040c644184031041d045112004502ea0745089040000b600468191088442c001a010010b20208400031018070007840e80b18000c0c0b040340e0030280c181c3c43c01d40499008808191140e903503005400d01c1040554a0840d8221012000708100c1c58600c020070785a00c1401c0002040101035004403189110300d84c40502610805084480365150000015617200c1c200d203002c501003407803031000045080c4107010250607548090252180c07020a08810348070324901c01c00307100c0384a0b250701c3d0070710300001d0400182034450500342c80040480c10b6030800d40e00310703100b4145031405501d0410040c406c0b91500141e0340f4415 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 938114640 1250 938113390 938113417
    0x21130206070c051306140607050d111002030a0c0f09052b060c020a230715051b06100b0412020906030307050105010b0a0801120210081504090f050609030f 68
    0x55030706141c002450700180e040b065100c8a03400c05503500d0200c1c0d520400564440c50700100c800c54000b01040f0306c500820000400320362004503681d5480d4805d9110940090041c4101d50311106014400d0080c0d030001c035078018180342da8001048aa99110307031030901c0000d42d800d0204460381424046040f65200c16060300c0d001040200c59110150589501c030b84079600441c04215441d04410004d4682c121940150780c2c64004040640810041c017140d0a610070b00344004014951400c110310361300d00103250140c000d0100c14132000902e0b249585d01d091410340c024010309030514110000c04c40188007034000407030b4410280403d2084000f224242900f2640440f07130301441c1d9a9075000649103218040f001000c5500b8100002412450307403004e000c015007180c807941c045030f0303c940e1180084452200e001c0d6000b0002c030f150b05075542c00362030300d00c1d00142c1c04001d1001c4050701802080654065200c21181c20740310f2005181808000e01c51a60008201030103103140c00707000f1a403284a40120801024007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 938115890 1250 938114640 938114647
    0xb010e1c120e0d1b0f080a0605040311030c010b0a151d0604050a030c06080109020c0c090408190503010e0c03070903060216020409060e060603011b03021b0f0321130206 74
    0x141409100420b56040000302800b5a4001c030f0310300b250303020254440210058200c00c0303010030f030003000a92507400d0f5403201c001803420510580f60384020341006001035081c08045918221000707070a00081c0b654060303200010460341801414400301c00c1050307009010440300000c0b0100d45e20340c03051211208041c1104540c040c0c100d0940020014031596001c0f540c00003080d800002002a034443c640200c5030107458011050381e80d04114000c0e8400e1075034940385a0000c201c440054507125440c290010701450500342000f02c0071200141045800c6900d0002c2500800100041104003031075660000d9294502c50640c140000c0c050310080302404020030307071500401c600340080442c115206140707070000c100f80942056070074000020300700d111000a01c1c0c01032800054141c1014040c1c1c4000b480c0390725000909503000ea500324000d40200f00000c01940c00c0e035000303d641200c20018140760261882c003866036100d895042048051090030380c031401c12802d90070003080c403e20b40e085048094041e01c40c943e6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 938117140 1250 938115890 938115923
    0x150606170403171e072c121c020c240d09080f0c0c030703021c0302031e030612010c02030d09061d060f011706130303150b040807230d03140705010b010e1c 68
    0x401f001d50110041d46114682e04100295603c0c0c40070303044c84541e84c0a0382c2e40c0304003080074040003840c642c2c00c0c4010840280b10200d601804140203003030800680e440001e00143d50340c0c841045501040040c2892003010400d0700c040030707041c403020701818001c900030060030f440c550108174068404c00a00c07820000209030300c030905000f88107c810b98040400032880c1c070000f0166990f140c0c2c2041d5981805010110b00b0b200d00040d0520070100d0004054000b1810013048950307003405000307240c0c2e0481e030300c43e10743c640c403000ca1030303550040c055910140c00a020107140c100c0c0c101c40c140e18141c4c042c10601c000065440b01c500ca001c100380e90040034081040f001c00110317007800c0c0e025040d03940c2ea000750581400000141000c02001520aa420020603103035004c1d40da580d0f01c030740e2500e03040384880384040c482d01c8085103183c202a100d482d10b06c00e0401984400588004541c1c54203e100c0030b0b61075075101c241820496a0100c40e4618116048905084000022103540f58604104400500c020480e800805 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 938118390 1250 938117140 938117149
    0xf09090307060f150509072a060f06140a0e0105131b080406150b03150102210c0c04060e150301110f07150606170403171e072c 56
    0x801c0a40c2081060104404400380200109540f1a00c0001002210408609450b207550040d000354125a981e01e500030400743c400510203206200d9040d907901c940000e4001850070b02a001403502c00c180d000510070300c6d000e82601c0c11202c031842c05206006000c801d0012100384440e49055070700950707580034192822000703030b4010483c0c80e010750045200d50303420303642040d0311143c8140b0980c46802c050100492070101c194003089a0300a180c4500020310000b400030881d00f41c99000020305104442c40907110514000c0805000d5042d03002c56800080e01d82c0c4215410054030741c204c40d041d18100410791401c3d0300c61400d640058001041c000c4504249121560b00350040713894840c685d000f0325661003074000d0898599000c4001210280300c911003c814040a81c030a420448103d40c803041d90007600c0828110b9550b00050080707061041c40d002c034030fa0000000721468441c0908140407100000844580041c9103001881c030340c200080310502c80c0c500780e00c0590380124401100e0002c00a000c0440015 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 938119640 1250 938118390 938118397
    0x1090308030c070512190e0a090237141b1906060e0603030301051311070809031902010e040905070512010902090708071e0e03070303180e060f090903 66
    0x1400ca1030303000c400d000b40320340d81400611030584120200c882400030000c803024103014011107902c0055a907040c984485002e082e0500940d1001401303580b070b49850b1501c01040707800c024403054100310703801002040c200d0030f610f0b20049407172001d003004441e4a00300001042403a0510907120920303400700c0c44e140a0b110300e403071000444040308241d030540354080da480c9072150b601041c107031080d5090150008509500c0c030041405144040e0186140d68200824800744841c20b00049105c44e40d00c0402c00709225952010b8032599200710203559564640c202094981110b042d584042d0829012a10380140e8100c0342c9141d036141d0903100415110514149141840c54940c00f8507009010914142000034041d030095018501c2110030000c00e4446200407910000202c4100b004a102c01c21303030314400400380c11500314006813460051108124000030a0a0a02d00d0703200714003149600d0f071201e07500485200300301c01402e1400d101001c94a040030000e0880c4660040150240000c0008910598028400ca = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 938120890 1250 938119640 938119643
    0x50c1e0c090406050a1d03040509060d1a0403030c02030a2a020918010c050f0a120e2b020c031015230a090e0c040c110111030a0b04020c06070c02010903 67
    0x2580d54602d05030404101a02c01180c5103421070f4900008540d0320350820881c1d210b10003035500114286418034040c0485440c010f041030b0b92000d03520050300c00141f40c6031032004684405107000e211030704162401800b66104001c2810541d0010300201c0c0fa00d5070300003440c5140d64400700b00b2148800410300d1100c0600942074020b9000302d8900e0030000d40081000110020700c050000070018441c40c0c0d042140c45000d410890f03034a0701c07000c01c2044410b520451011403044110400020903020002e000c6141400d4295500c0302c3c0c1040100d81ca2030440c005101a540c20b540d030020b0860401c9140000c0c2d1101103070162581d0f01541c54200380b001c084c00800002c003810010b010b4071a10410030050180340500401814400d414903140400ca00b56070303000d00d07010100305400502c0398807500c808010103050040e049a0410500c1c40904034001024060018851700c80101c459980c10a410560300355421144003500460041060105500c000100b440c0c0c04840ca26192603000c2281c40125021411a0700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 938122140 1250 938120890 938120899
    0x19060602031804020f0d0504050102040b040e040516140d05032b0b010e090c070203210408010615090315063b1501030c02120a0206010e07050c1e0c 65
    0x20850903000001882031440390103000389580820400c02c000d0b407007820568201908140040d00109082d0341101d90007610800c00541080e4903021144041d8015910090062080800744018030400703106107000100e107412500005400c084c1d0b198034041c04100094020008da003000e50038064244140c61404901c6d0365028500c040300c4905414040c2040e45043d40c00e458061010307120b60040a01100c0c5c010041c042803d160f071010040300c42c1e50031850b42682c250141c0d0081005000748201d0a841552000f0304c3d440c0c031142070066580c21100e85421000480c801c81602c0f11400380c100c803d03482101d82c026000d07000b5405c40901304002e441d45500850a034000d4119007417601c4410f10ba0a589248001010380e040144207140600080042c0c0780b03203180d2030340c4c40b010040da9482a0000725040b00c03540110b0320548040b002000f40d5a03c1810190300507007000d001845041100c001d025000000f0b0700d00b80e420326410490743c4d6141c6040b12466184501e10600040c2c441c007051000c14403e1720f0050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 938123390 1250 938122140 938122151
    0x10201020d0e03040f0801140a0b04021c02130807120f0318081506010e0109150203120f072304050108060f1017090a0c0e0a02120109060603050708040b0f19 69
    0x901c42c0d070380d90700305004c2c41c1c60900c24020b020030780c20014403600311211008070054141d03494400362131000f01311030781178a50040e4080046a500640708a02040410449070005035540c18020740308245140540100c021500500c8082050303034031041030003507160340140d6020b1200c0c40520f4182d98225020009045c0303c205108005140c4d40c002c200036549943d034091080c0030356076081c01124000c3c018020140030420380c0c035003840381c0124040c0c61409140203004403407600345135602c000d1400504071401c040f03404100080003d0594040702858441410454400c00e0b206038600c40c18042c026400307941d041225010000d00540eaa903040c1200c0101c01900d082c904030748440005081d400d804840ba1007241c0b01d00e01145a02c800010300d1811590080f0355040f9050510440381045140540482070f8290203200c400e900b40d0030b00303007458003c0000380c0000801600d8040050700382d980007800d40d02803003160303400c10012403401c0000991000100d049415142c2e0b03182e01342143c0000a012200440e851700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 938124640 1250 938123390 938123411
    0x2306280201020306030c0901180e07050303071b0e01030c0e0712020a0507020108010f0803040b0f1e031005040213050607031218140105010308160f02060f041805070206070e010201020d 81
    0x10350085014280c15410784152140e104140102d8010a205501c000da09c94032078034021250940c13240d8003800c1d002065035a07a5580d81c0000b450342c0c2040000740d6921403954550a12842d42551410040804140c10b030850361441c1c6420849400b24440c001c681300c00e54000801281c4148010b0040100585d03045489101c1c9040c01015900000c000320701141c2c00c03400100d846030540c400700341200c4100d8015442e15007004100b907210307040104000e0390b045080c4089440030803102507000c04094402825900c034074010a05819400301d544c4014000c500c100102c0176125502c940740c1050b65409d80720241d541c02185411aa414644c80701441c0007442c1900c00c0c5e000800c91034200078024040e0711200c181c2c2c000c800c442c600703c450070701c001080c241081001040c04260400b030049418060b0000076001049070300800d84503440102d0300025920000703000e000007a90000b144140b494030100c00c020601d851070740a9501c98004c2c02c001c0c01d10804e244540340726032007501142c4250501c840c003801a10b400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 938125890 1250 938124640 938124643
    0x50d0f05220314120a1503020f060a0c080c011e05010501050a0318150c030606020105090a0b18060712050c0903070303032c1e1902011b08190923062802 67
    0x5e54100f41d0280c1090321080f501410104040c0549400070b26118081d00c50350100300c05940104e94070310a00184a0404000c90000030203004825080c03c004262150080001d11181100111400c1158506030040c17000f40d81c0001902c2c110481e5040000d448258003043c140341c00031001008283c1c191186038094100c43c180c000031003500c20b61b02d0030f0100c1c546800c4141e0a0792000c40e050f04196100039003640224109401450f008a03841590000e0034081d400c00508200703049032045c3c0450040307440c010541c00c0d0f9206241c1c0c020941803549062220b0080040c8e00e8130064400035040540b194442180340d00c0ca0200e0528840503036104445a00c8019280c5485004d40404054040442c0040003021080441c204903091050786442001d9449540156290320102c032a145074442030300904400101c2090003000e14982e5190f815a5038542c00f00b00402050b019002080b140510440d400750b034680040c40041c0910741113071079540340c100340032031940ca034107040540c404440528400e42100540 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 938127140 1250 938125890 938125927
    0x703060b1303061506050d0b0d0515090c150315030705030a0b0609070503010308040e0c0d06060309231e1c0c0b0a090b0112050f0d050d0f05220314 65
    0x3190f5010b000c40b01003141c2d10460032116101311030109508002501c2083c86680c000c0700c29560040c0441c2d0000c0858070780900c3c000307420300e41c0749400070604107114148404101c0003500850840300c00104000d1800000c1e980d000240c80111000440702420241760740a12000e000b6040c06022900c60004038141421003600584110380991101c401140070a0700c07480c11241a40e800405c80e40c50545001d00c805ca450f0b100421401c0991814007500d600090140600390041c240d07907901003091005e5046c200000c0444011002c00010a81c1700c8074080701001c1150302c0c01d1104c01c41111003508217021300380c0c2402e02c00990f005d0301d48549813016034000d4000f100c9040c65402004140869a1851726100440d009840041c1c450828840100b040a075049031840c0500c0c0310b10300395021009000340a91902010442202c0032403c040344520300394217540304290a0007088503041c00142820300b01840d441e070003800d80622041040e41c420042c5400380050b501c0070004075140b19610b00300301811200c10300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 938128390 1250 938127140 938127143
    0x30615021b041a010c0503040911030105040b040b0307090b030309060403050d02100209010804020d030e030106030b0a0b0d1e022409120c01082a030f040201090503150c030703060b1303 81
    0x111101c520624203262140414003000405450110800d04006481d21045170a00b01d81601c02048080780c80c0700c0c5405001d00b05002c81050030313103a504080c200029541054803941c02a413408880e900c00342d80010350181118000000020b0b80b6507181d002c07900350b1151110103500550f0002d03000040201c001400d0130b8030200307a402d4495008a844007403090388212400140001c0c40c44007c074025241c03ca480c2c0c4400c9104e420401300601d24100800e0070b5400652040c0c5010b0603060400150030702501840621100071980e0a122047e280d4410160803544440c8250400d2010010b204540f10218201c01d0b041d01c070344401e040075600303a0345601c05600160019002d0b40140000c0301d00f2800000e0f424902040584491209950710006d00191054502c011006200e0400b00c0c2c5a403800ea1000450090030074200b11110342c5024000500b4000c41540103500941c42524100080040100c8880c1c01907200f000f400d40e292140e403821806021a50440d0400c0c110024071050181d42e803030000c2080300e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 938129496 1106 938128390 938128423
    0x1606050a0e060d0c0e0f0604030b01030f1103030c0f1002210613060303022103091209030c09070f1805010207052704033b0f0103061502 60
    0x29038614a091010503056802001241040c06c0064440d1034140e8202e486e05213150340f640c0c4a45e80500c0040c1c80d440e00d00c050031302004480040c22450f04030041c1200d480703400d40400303140c40f083c1c00d4140f0b110074450640203001540081c002d9a002e0003069450000f941d01003018121701c0791006204a601030310316110080b0b5007805200351409103009a00520400d84034048980141110f484035081ca00020700811540f80c0303002422030146040c45a5103600e078140000400c1c5020b020790130050344a1440001c000320710f507000c4a038a2400c00503541b60300b080c00020b02c409401510074058680160005102800305041503010110003484030a8540e85081000010a400d030031b050307800300c3c009490081c0203110171075038884910f11949034450020400c460510222282c42c0041a02805542801c504213440d07806544114004d0403175402e481140e400380ca0009440300e02c84030060111 = true := by decide +kernel

theorem cover : BRFrame.Cov 937949640 938129496 := by
  have h0 := BRFrame.cov_init 937949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 937949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 937949640 ≤ n) (h2 : n < 938129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
