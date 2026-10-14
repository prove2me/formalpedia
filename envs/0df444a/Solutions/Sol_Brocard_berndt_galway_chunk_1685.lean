-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1685
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:13:01.597262+00:00
-- url     : https://prove2.me/submissions/53ee3d61-8f4f-4160-97fc-f80de84df5ec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 302877697 ≤ n < 303057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 302878947 1250 302877697 302877703
    0xe0304060c030219260a050a1b050a0b0115020a0b0c0903100e0d0219080304170702030a0305220312050703030e071235090d0605090304170c03 63
    0x100c0340585081e42604800d410144d08080c0e000c081d6a86014450049100f408a4030740c45580041840030402c940301261003030312186004100210000501c1000b085405501ca0b41c0482c07480400e1118818480c0072540e103040c6011100c1d04100c5012280d40c0040003029500e10b0f01d0004208580098021210996185034000e00003c0485001990108103503d09171000c11920030f0030700009030100810081c901540341c0d9001005c101d20014401c01881074100d800035001100419417202c56913082d5199070f543c4100d804841d42c1d50fa6401c140500c003541c0541e8040000700b41c0d00e1b000e52169a45c40c4585409030807803039030804060f00d401401c2107040001440303055161242c0e801d940351031a146e01c901e14049003d41a0401581841c2c400d40b00c1c089041c1041c040d006050034030911031184449880c1c5c081c1440d00241d20001d944900c10724103414041c0004800401c0c046400410504009407150742364011180300740c600c50465400030809110041c8401d503510000c02c00d1600524060781d0180c0040c0d5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 302880197 1250 302878947 302878949
    0x80a0501080a0605070216170d0c110105090310090c0e0f04030f051602030a08030a2904020a091203080103110301020915131508040b1308120606040f08061602010e0304 74
    0x46211394400005507105c0c803d00001c140c0040140000740000d83c0c424800c00360148020401156004582c10403403258080c002e80c10613030b6071100f20079050b03803540401036a141d0404480b0f0703601030050112854401032203114000d010343c4a10024a0384500341071341c86045a0000300407010013001c0009000c0480c0d04074200f110a00308901d4810f59544440031b1220113000401c40c000d4051003440c64800400010074080c6210755005003040100c5003c0318510b00e03d101e546d850a4007241d04125500c40d01c3d044c15001480403503814240504041d80d01e04100c0411900352a082c1c1c00108000014410131102114060b23000c10124029810650440300080004000008100c254100010340c0040d035208060810700800c94002046500104100080d241002c1200d08403813082d0803000058003003040c1c803c9a49415045140341d170419001c0301c0382d40e0f102e00c80603000300da2103078050100259001c505511540a006968083d003010b04000981c1c0d0381084072400e0840940e41000e15900b42c01100005540c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 302881447 1250 302880197 302880203
    0x30507020f040b12010501030b09060709150201110408061501020313060806030709021204050c090f0601031d060112110307120b0a090b18190c1509150807080a0501080a 74
    0x240307029840c0005030050004508194102421200c00e101c0c032441035208074122401288120b20300d648800c0c049131181d20071102580400c4105809200802d20558a101074812074000060102e4115040500c1500140d011a0140c0d10433401c1001041c4004440c158040081c0000c50500c0034032692002c003008075004100400007194001034650782c04100a000800150004555400001c03090300300d43d10003100e099a00d441103240301c07109401c0a0348800e1103124080136081c10342d2a0030300110058040c2041184c80e000b804204440002001e0107800d0080c9140d0044c00c2e002e03800c1c0c4c50085840050528400d201707400c031520070481d15046240450050f98481c644803c076903540b552080080201e00800360035020140304000003031002444140441d41d21804450340d20060706000140f000300c3d60700040100899480c10880d03001044140d50303540c240b604110200c0d54940d800001014481c0c01c0344000640c00c881880a05500144101e402002c440c005000c0d81d1b040c0242281d6550043e80c001b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 302882697 1250 302881447 302881459
    0x9041a24090625030216080f030405040509010b04150801150e0105010309030c0b07080f0f04051c0905060c160501020a17030703020702061306020d0c05100510030c080304090f0903050702 82
    0x40d1001145070142c00d0f00c000c80082c1005101142c604009617121080a511417510860200108400301c000640c9114030078468000d5250508010038000030340f030041d045801a43d00c592072481d4640e664050281c03184000703484020b20300c1c42c00c042c107400d40e40d001c600512400c01049041c40811150384100341500c00a080c085824841898212503400da000e00107401210802c090066069100510034002c5803580401440b03500e564071000617952080e60010003681c80720300010031090310440c45545400c41d505110480c1c564400101e0295800401c0c8d2400e81d0300011b02a00090055644882c0603010030300c018032450b0040d60307603506100c0d0044500d43c600c90000c80010000c034801c0d0100c40c0c0640c0e001c0c1c0b086440c0c0940d0076101104103442c0c0107100141c050802c2c400c40c1e061082e80d550b00301c280c01000038840c2c1007521880030f00a107405060103c20300b604040101c003154205080100800000340216502da1410f507da8089454400320301c020320741041244000309500c00240d0301c0c0c0d00d03012a80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 302883947 1250 302882697 302882707
    0xb010f020c06090312040902041e3c0b1201080a02010206040f17040314010f0b060706050a0906090f03020708031207050307020a02120a0303051f0b0d0209041a240906 73
    0xb80c50301175031030300d002d030141000a0003043c41e4040d90064021142140100d035025001002d4040f5040c00c140551074000440900030510402c420f404a003c41c12100f066030344010154800b03c49241040d08580701c801400140301c0e00c2200c00750303492401409240c02130185188241e00003511a070024002902c189a912001c405128a4005002c50000780410080d92285c0e240b80c1828000c000c3d0941043c1c6520300034000d10084928018005807180c01049140f4182c140c0c0d40340b20060501a107503451041d594501c01c000031342944a619050707030050b183c0b0804181c180c41c00a14011b51604458000c0d081400b440340b84004007041660040d8941c1882ca45a45c0c23640000c1b403a09155280c065400743c035402d070f01d1202c40c078003040421480b03000c1d5405002e1952102c03144000e41c2403608290b101c0407403448082242070340d028054250f20b41700501c094601108003000900744c50446174490b0801504403d144064a07203603920043d540380000c0d035164030200405c0090b5176801645040340c010200054 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 302885197 1250 302883947 302883949
    0x702060f0a0e0405070f03051602060703020708040e0a061a07050d110a150c180f060f02150f1e090d11121902010b1801030f0311030712030b010f020c0609 68
    0x3468481c0c40c2c002900800c02881c04000041441386c400400d50301107480c08010901c500c0848259451901c0b041d0000e01144d00c5000c02180254001e4074190340a4906001c040360081007440c0d203601552940e4004691030341232000025034000e48903a858000001001320f000010400f0a50a0720030700c040c2040c9128069000300c0314203000210000070704071a103000701c40ca503075007050740055880c0000341d846410315000c00c00b202000c0e0000307014007005403103d18400c00513030313210340c003c80f0b15200d003032050b40d81810086007100300d24a0306483c00401074034030034200241c2c001c4540d40b14070b56242001c8152410304000c3c15141e2580780c202008000c02c160600e0130310140d201048000d00b8544004000380c0d0701e101040501c5007040222a0000c01075082080718845850004455030380030103101c00780e800d01e920b142c0e504e030400244080d04405004038842c7c2e94024003414000340100340e02a0340000224514030360010200c80814107224140f2512400c034000365980021082d08000b02030300c50a5840313030804 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 302886447 1250 302885197 302885207
    0x302060f09060703031a0316180e06070e10090e040b0703020919030605010e010f0b090114040902090103051803090d02031e0d02070906060806190b0307030209150702060f0a 76
    0x1000d842d4024100003042001c0650503448012081d030803400042144110504050710350160703403003618400344003100030311241c020000707042700100b001c807000111404061849800d040c0c046980c03a000c181c0d951415101030030098089048030307205241c40070040e0700b4680040141000030b040500f4141140700013810f003034065070456804070070042c0a241c1070a413442062400b4556030100700c5085050078000902407985041150684000400a041e07485c14120f0042450300300c0d061250401c81ea03114482d0b8811203040041002c1c222004000d0b9583c0b00000c0054160b4a000e442d50400b04145800c40500103404015a42c040d0b5003207400c140c1000700e03400000c0ca00098440f8442c0c0700300c2d2216504500100008003003032046000d409884403241e4a100c403030704a5405108140c0801c906200103501403811004105a003402e014298006075107440e0a4007203a0011100303000071940c009024400b900e465042c46621001314407485207000d07142da021034024020802c4c0d5a0500d10045403c1c13500d98021 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 302887697 1250 302886447 302886457
    0x150c0f0a090e010f0f09140402011d090403030504050f0a05030a0315090f0203061e0d12050c0a050c01090f05060a050304020105071505150603131e0c0801050924010302060f 76
    0x38800b2803007656180c01d01070096058901c120032103c0510503000500a00a0003079400b02074100307548018940d071360780056424541c2000c14000c8100f0301d203044182a5940c0000034001e41c000d6a0000c1d042c0380c00d151181c5840454032542080e54040481c140c0050000000c5a60007405031401058600c0fa80c50546a1030f09142c10541800c1c0c00c0c0300303125215108a0b0f000d184030700c808440c0302d00c52a40c000d510702f018a55449003590068030050840011a8001e100c101c0be45100b441c0c05840d025500c1001030409030f1403041164280c002d140c440c4120340c2e00c0864000902103070300c191740341c40c0c2c504400903e43d886415400c900b88540440060306582c000c0342503454454000e03488112a914401144000f4003085620700000c3c401106060400d040000649200d40c00c0d8800341441c0304183d0b00c400c442c0b07051800415500d1a04c1307030301d540b00151603180301c40e008016000011030103080500c525070515684000340001d00950706421541440c2403090641102d4050f0382c0700e690307200701d00c01942e034910030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 302888947 1250 302887697 302887709
    0x1715100e04060b0703030b010906050409110919060f051c0c0327020406120203031e0c0d0206180604031704060627050c0414012001150602150c0f0a09 66
    0x2400b000042d44840d240c0092600341d100e035030100031b0a1a00b400544032800280200000200103001c1404041d00340c1c0d010b0704160300324103000341c104040342c2c0014402c0065550030102c0000d0040041140e2a0445000b00580001381001810060410035800c04500030f10011183e040d00e425044420354000d911640b80072400041c4034029610100350549040c81c2002c0c100d00807460001d000840f100000104c0b006540e0040c05986032540b1924030700c01c7c0758450380202c02c0e100e0042125540c001d10800c802c082511103500602007902d001002c0305000c000460303000c103c64100c1c00170400001e5000450807c01d0a010100c400140c076203082601c01041036070841d098980361104128a00c0004680402d100d0900840500030350741c414040507a140640e114620b20189034405440e1250300500f0710401c40d40b641a00310000752280c40c400307800e4a06a880307541840f0304250060040b03d43c1482000d05c00c409404c0c1c400707010708018518a02030701c0b501c01e00707030016000030402c140b40c1c0c1d02c250800002800303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 302890197 1250 302888947 302888951
    0x70e0409020f18010e0705040f0302120c0616050105091603170d06060801140d0209061c0c060519030c0c1101030e0607081905010506070201230c0c011715100e04 71
    0x1001081c1060312001703000e07120038881c0c0640004c0f04d140c4694119411744001c400d5200c001403555082c00ba0381b044906540042d8000c95005050b5911924054401d400f50aa514940e00701181095404c650010b8008401074020500100d0345445800801c004c0760707808503240c1c10486604100c0c84041c003545c0c070060041d904140f070008030030342c1c4014124160365401045131000c14a4a0811440b44801c00c0020340203209203001134101d00d081c0c0b8040700c2c10074040e2410590020342d6034a2013080d2440d9000400440d40119158207240c841d62040401c3d0102410100080104120040c0c10781c407500b0402071502c806142284040d910a81010300c0c2160703010115901800c0018000e4103500e0121841d82286c415901400c80140c40f41c080c44c1d041b55800340545141505580045945060340d440840e20140c4000910741c42592544c01400414441000f8180380d11480f00010000880c1402c1c00300b208043c030303042c0b05c854030302c0f80141030154a080320f482c0a21440658191000411100c0703c651080c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 302891447 1250 302890197 302890219
    0x302150c0d020a0308090d1d0a0807150f1103040e04060b0d0f0318140607020414010303030b0405060603060f1e030109050304050324130c0b0703030f0b010503070e0409020f 76
    0x5500000c4008002d0304c6501c80080359039030b030100c40c2e41d201600801540014030029440700c1171003000254656048003d00f074071082640b07401c0700c680fa0405590128100e40000505040d0a039880300814480b05018079281440000c5100002d03524051801b40d02a032210b940040f800f00801980301d002c030400042d09140401a40d070421440002410b90254007040708189102603c0e100f4081c0754054418000c241204400103d003070003825000140202d8001d65140440e5281d1096038000f0303402140309541c0454200040001d04c41030f00d2000d01828051002030042c040701d80d0312000443e4070550207640c4500207c0360301081019a0200405403600340d440c01c8000424450080000c0003610b1081c1c01303d64120007090402d20606080118210317101002c440800d041c44114415150b40b1340c00303501034060702d0781c40b01c4400c02154010a0101d011079034450070002900c005000d880846070090030a42e04528207400f000d0a505010158144115a075020303041c21951815202c00004030040d0045800c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 302892697 1250 302891447 302891473
    0xb0309010605151308340b071b0902120c0a140a0507170405010c02091003150506010e040603030815180a02030405060a09050a12110615040b0306060a0302150c 70
    0xb0b44c0c407000e1190124005039802003030328000040c5000e5440c9078501c0c03007041c1050003117400754058800300440040701040d10000800104513000303030406a0044842c1d0305440442c00c4130b458481c0c51503000440c0540140310000840c1c81440748564030411031840c540d540c0d440001c048401c40c80c41001a403070140081161070441e41e004028240c01d9200b080d6000100741c480c04940c01302d00039489500d0000c0c003070042a0005007007203182c1d5a0482c0c143c0090303402c49034882e0760b00c0405d6008443d800c20180c0d0b89074100a00c03584d00503a119017121056074100300c428159140140a190300410500e030010914008102e02c1d1101c911003098545007015010700c81c2429011800698030541d411760702446803a000c141c198405208116001d5842001007502c0030265480030707810f00042d8403000a000303151203111040201806864031408450380a8a801c1c0021420001103540424071030340070341e0012040045035203601e03008609503030301201c00700c5909149405c1a00c0d42e00c569440c0d080207000b41381c0601c0c40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 302893947 1250 302892697 302892739
    0x1503130f060b0307050a0305030406050702031e011a0d110613030209010b0702010e1203031909060507170a060b0f0d0b03030a0903020f04090b040303090309050a081c020f070b0309010605 82
    0xc82c2101518505540c03581007101403c03081c0030140840e00108002c02100c1d00440c02804024800703400e40e00744e841e403501e18045050000e141d6404903510f442118020340c94031007104201d405d00701e68254100000d501c9840d000200b100c4418084e140000b1821074414145507984c004642c020b1203a8005d42c0c50709445102d0740c21074402240450740001c00c0d51040e00d002401703440c1c50035455000b142955030310000390310100c0c8013500700c0654681c0c600d04400410498020540314020325141c603002c240c45400711200c021030052038126040c0c0360890030300c014040c0300200c65109100807111130712030801403409001084100501a0705200c001050342d2102d03001404181200d0003144c010128032104802d02065860703030b0700300820b0f005000c000075001134045d61003640042c0c000d10b0036400d102e07104c0e0003080c032005540e0800541a807088040629940800404044c0c240161000e801c3c244040710840d580d404860060441c0228007000140020609500c40c100504000f4200780b04c2c5a0702c0c01c1a440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 302895197 1250 302893947 302893961
    0x8010e010b03060109020403150c05040b0d1b1107060509030127061b09062106061716020c060c01270219061b0203010f05070302030f090a021503130f06 67
    0x40203008203c00051402c4141c402d6404507500013400ca14034400b00b4804000030030340c00740c1c0300080c40400c0c0302c00304100c42c180000c0d00c403401c11141c0c00200f5030100d4960340080c900b80e9120008001086a09038040d85004c1074030000c84005040c03070340c2c072004070000003800750140c590004100d88920105440101600c030b10f000307100b4010302013009078100300d030824400125004440c0000c1000f41000b040310741d108046500714218010729001030700c011200075500b900e041ea40040001039076405145030300380940403850b8000e6401121072201e001d02060107500c80e5071082d046131041d0400300e591100c101080d080206195061000501d19a601e082c0f150080310a980080c0c1c01344000d0015400302010441000d0291040390321400f0341f10403600d4a083c0010100340040360107548880708083c0400c80380c002c0a02031503640d1405a00c0b845e00b404040d40182009080703110b031f82e1200c441507025803560316445030250b481091095482d40e5140301e0880c0d9490414004010b8900100d142c02130103401e80c8440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 302896447 1250 302895197 302895199
    0xf0607090f1d090a0506070e040f0203090a1211150a06080d0927020f03060f01090b0a260916171c200f0d050a05090f0a08010e010b 58
    0x3044554071800c076091201580d02030101004403400c1c8440030b0007000c2c140140e22915003c00ca4441c46090382e03500703040400543d881c4001c50b0b000d0402a42c103242c117000798440034031005800c6045190100000d0f07590f10075004090500c030740d800f0482c01020b214059042501c1d501c18112a40f00310b451900c2601c411048070591082450041e0100355101e01045103c1048000e654414226081a032441c201a10b044142843c0e0440c0c012102070404590014154021881003420345900c0c0c1003003402007140c40c80b030242c1d041151902e418071091008809a50740380d07000e03180403620380310058441c0a0400c40030392060080d001c401e0801c5101e600c001400d0400c80417542100c490655140041c80900b540d40c1d0308004d058104c0c09945404490f808000100c4640700d24210705c10700d00007152203800038a010300d00e440c03d400c01104041e8603001084804802540c82c90042c0c0b03071520540005160b4000c04a08901c1041c1400c5601015517900c001c0602800c2d64600801c00c58a189400b2070003804512296 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 302897697 1250 302896447 302896457
    0x30307050705010b090f0f0a0219030f110c150c0904090524060102070306021e030405071a07020a140a03080a03020c060603060906010608070c051b1806060a0f0c02030f0607 76
    0x2812424042c05c003d004601e81800300e1801c2e12240c10007007041c8801040c1d07252481e4240203224001c40314a40c00084041540c40009141401c64001001e44011840f0803122500400209000703900c0011035130f42802e5540c40014194541ca5046102c41c410200701c15402414002e4400502c01b002c1080d46082c3c0c02282c40450006480010704080002103c98601582080b2810804140740c0d4004042c0d82c0601401220190882c0c40300c041d0540040c0c90036110390b48481010b001d10000d150f0704841001441039514200401c940c001010b0101034010211065200184d18500d6180c1034107040103544d0100400380c40f18003403000140250031216a02c0e0543c03040d903020a050381408650b0070b000d1020100a402103a081403c140d82c10b4501504000c04c0062144983c004200700b40281e0903c411041e00100c0d100908000b0080340d18014144c0e0b143d41c0354200c0a0100076903d1000f191003c0c00f09080c2400402e110010070b6409039000748000c2c1d0503004140c01b40c009032502003060382c0b04205640314 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 302898947 1250 302897697 302897711
    0x60906150e06030f0d0c05030904050403180b031006120b130b030d090e040605040f12030911190302100c06050f0f0702190308180a12081e0112080c03030705070501 72
    0x40584d40c05458107203a0071500410101c0c0d00241c4582002c5d80303064084d00442c2d180400210120b800c444007100e00740e000400003a1401010085464840018030582e05642e04500749500d150500b81801d200d1441400092520501500002d401045184100074280c07610010200c0001e0050b044401480b03110303004003410b03150007d0140007044203440001400783c407155150760f101e00c02400f0107001592100014642903000541001e0034056440450750041070a606501d0316042c1003048021441c810303050441d200280800215803c1c080302c0d0121060201a500c03090159450340c103083d00070303000e04c1c106020820400304990039540640c100390602d004c40da0329003000305d845107108040c40e4000e10301040410003080c410038419801030060850890040743c0340f50618030700524640121090041c1244400c1415009010035a104600414240e24034120000040011805016900300c600c42c070441c4500b44090882507402c0442c00c0d2007180c0c0d90b4140840c0c041c246801964045072030b9824050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 302900197 1250 302898947 302898949
    0x6010807200a02210c0609061b01020904060f05031f06050a17060a050c031f090513031d0109091a1504080105060103110f030a0b030102030a0b0a08030304031b060906150e06 76
    0x54280781a4000c4d0016016480020301007020907403146a42c550700035420320801071140f03540788030308001003242c2c000140d072240320206200941e6a10760013a42004807842c0100500d80b0040b86450654448101c0e1100e40820701c2c0c4600014101074100325040f05a101001c03401101162500c041c03101c000e0215041940d60108038802c0c2d0f14200d81c000c070551002c0c000310b00c0c0c1101c004407400200c2980c0300b0041d2500d4852180c80d040341c3c030484440040c10380c485041414150070000c1094080b00724445441004881c8001800302000e600c100b606665540341288064040078024150200000700401d025034117902001200350081d0003859825403a010100e88150300078403c20801c0074401e03040a040151582d44229290002401d00401607202e0302c6c2c02109990a01c0203521801da503200024800e0342c00021300820396442d8012000c298810000d100120343c1044012001440c2404a640109210318212014050f00640100654100102d84d070724441b4058089007550880b01c0b0604003030391088 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 302901447 1250 302900197 302900239
    0x1a090d020715140a03021c050a141b09040b06041212020f120702031e100c05090303040504050415151a160b0a0e060c072906010807200a02 61
    0x551007102203541d4460f100080300580b0041d1028000070b08005081042081c852070700d0407148204009038540d44e030100804c0c400c0912480d900c03090f85c40e1041d031603071810114444006403010080d031440c090201c0c0668a40d0359581256004240180100b6200c2e96107030b05500d1503a070098001c844407002000814802031001601036060a00030005015184070850701c0441584254016a050300400622030014000c401035540e0174107800740100040f8a041c880340080740e4040b001c1e001002000c11103006280c0e03000041d0307801d841045a000840751038918000c40c0d01942d41ca41d98007001e04100441c098040003d20f180111040724001c904010140b050032401c511420146180b103c61840b03014000c00c400807084c0794888274445000528203501c00025150590894580c80d0040c000507000042103081c6240d4235840d101004200d6942070010035100b070299005007a5410000c1000010310ba0f58852440070310245006c00e84d02c050030400001da2620751044042c01c2e0b000e03003070609642e00784d60150 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 302902697 1250 302901447 302901479
    0x10050d080409020d06150207030c2114010204052d120d080a020d0e010f0b060306031c031b030b010806120c060d02070228301a090d0207 60
    0x48425280781ca4240503604009402490080f010070fa643e400216070220050740c05921058242c0081807202c5c55451700d0302002c4400e07003010070040c2150f807031b100c1841d50914001e20006d0b80403500090070f0380b0302001c0038024007499110941c0309042180d80c0d4038082c3c510841c80410300c184030090311810321a0090100c9403031781d50740040e241e0340175a000c0e4880034490fa44031500082c031401c1c0540f03005045070030300c41a1502c030101204c07103035075800d1180041740c19489540941032095a91b00e0031894480b00294580d001d02d15244010f010700612008182d110750701c042240c00b140c90440c141c003042c0c20300040c01451408041400f00c1d804201049d41803410721409408403405e4401484410000021f0224540148001016054080c860000142c1d21000c1c14945c10060320060441c031008101440400c940c207070301c625007000c03400c4140519051050150f100800c6a400042030540345860006641003000000060540c441414008030300004924824203603050303070844442c2d5460703100e510030704161 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 302903947 1250 302902697 302902703
    0x8070501030605150a0903050d030204090b1903140a0206030411130504020a1214120c0d0c02090406020306010e0307030b06010f09050f010818030c0a061a130b060903011410050d 78
    0x1400c4013100c0d1030048a00200718820282c90701000740780d60f996880d0324100b10314910703801298000c41c091061a42521608449110071244102000d40010700c081c2401c5460001404071000b042e60342000110030045030900b554040d1205d9580d103045d0400c075a082a0b54042c49d8400c00301e011804d288000030b4002c0d940680d400401d031150042c03401c80c01c5d158041c80c2d000111008280c8265503070f1003250034004481c040b20440c0901e030740e4280b2885428140b0900c0c8100c801031061261f10307103025031240121550b105a100c500107a90b41c0b1800c0c0140c990300c0c106404960700d40b0071803601101308040901d40502954081c2c0f158000c400e2400e0782074800c0c0809010301c030b402006a8501d20f44d11340c494030690b50407100e0854440628130140a140c0e00f96400745954000b10b40c0700429003001c000c07030b521131500340090f0190194680c001e1440064140340581024560060315840c62030342942d620021101c3c0500000c2c02004034090700704a000400030121044100d4055420001403a414034410f040401c41d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 302905197 1250 302903947 302903959
    0x306030c082a03070b0712021203040f0b060f1c05060c070b040f06180c051003290a051804060b0409030855060b0f0903030c150108070501030605 64
    0x6510202c0382080e08840d0b80c880e41031140c0540003a180603250f00038000c4038010505034000d0800b11a0280ca000382903881000001010020080824020488040e4207035005050742d06a484100c00908640c0003540c40c917902c11f00a40c80030701c4800d840c00002e507480f44280d09a40d0a647c074503140300e0b058000c000e001351203441403030000750020301640004511544110400035800c810440840380c000314a40040354501c05030b00090100d03150503400d102034210103103010b0104401c0c583c140d241c03c180c601080d5000620001d41613800d5a15540c0180107000007914964984010b00c407485c1509500751b070180c40440c0f074030890400070704103030241c410402c1d0544c40d4400a911903074140c03906040180380061014280005000442c0707100c2201d50038901240284140e6664856139101140b41e010010035542c40c54141d041040340c1000041d107409014810010b511902d5040200742140f081042084c9030f03000e141a0031107000d03200512035050300c1c1050308440760152250010341c00c0300e04c1d50140035072000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 302906447 1250 302905197 302905243
    0x40506060a060f080a0f05090304090b030606010c12021e01021201051f08041e0b01030303230601050a0507060e0a05070e060d060b0301140103060e0f19120504080a030306030c08 78
    0xd0240010a030450846a00000c0140d65695003100307d8000390f81000c0b00f6000010704119496150203030420b015030440180c151410b01d440040d10303910702444010903803c1941100b120481c02030005080f003c0000051514131004550b68038001d50005401c0014140c05400204045c01c002400200d000d62840e8003042d54210700c88113450a240007031041b0303440e4241e600c4240d41a0030440800010b40e100e20740c11401d5504603d00071b4240e44030303042c404406a010764010200d941400d800b80e80c20000a00b04150b81d10000c6504580500c95550060155820700700c1810070460f0010701f0f102094080c00940e5801ca403201c0b140c0c060b040080e10460b83c8250045100004164107505c84410303054002c00000d510a403680d10200070810036030064a00941d666004c0c50340e5103003449410706242c00d0f44c0103022081600752240c80c96001e4080040d00481404410002107030140c011100a04107a40407038078150314900c0d00a004c2c020742d00048070241c00034000000c0d4040c001902c1c101c06202140089500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 302907697 1250 302906447 302906477
    0x90302090703200406080f0a0b090403030e030d090b010515070804050402090616060c2a0b0403020c031f110a080a0c0e21010c0503010308030f130c060206040506060a06 74
    0xd0b0490010144030b402e00f540540a40c064020014002042e860312044500d20707181040c24801c1400401c410700f010706001c0c140e0750315a200072105030300a5042c2030005a20340a81d04c207a15500071102a8010340e0b140524210078098035000203030403150100c03840004148285e0084d0244e006a4500801c0d2110900042c802c174036183e00600380f4000041c1800b420100c50070380c4030440c1c90001e17a050342d8150391010030f4114a81e0000c11072451240d04400d650a800c020010454442040c8401070103c595030300c040b80800d8070a101c58a5460310050886141c000f91280ea5064810404000550b10386000160300480000304103440a0342e607151980c14840d50740c200120050b1407019a1001040300c840303640d0380d841c2d9806080854550400c1c027984040d2040c58071180c02c4554104d203000521005000400000c0d18440449034820340c0030440300c40341c2d00c0300701d40c1154400d200440240140300e5840c003c2900d55001518a104d280148212201030312003505101e4040031900460000541d008890400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 302908947 1250 302907697 302907701
    0x60c0a020709270303020a0905060f0406050f0405030304060206160f1b0201030e010c020c010210060e0103020105071e030f020d0f02060a020a1b05010b031203220204140a0b10090302090703 83
    0x41c481c01640f003000208400d1920741e41c0c0f0001c0c0000303c000c283c1c082062000c0300d621621a4001d0710054414900d0302407041134043c0f07a80194440e84007040000902a83c0078005441500d00504000d0b04882e1110b488040103502c2e0342c812281200584002502444124031a800030140140a0340300e5810042d8800c507186200c00d12240c050b0705042d10741c50f1407032401c40c0c2446021020055a03003e040c15840d4a0002420002540441a03459013001014080d484401c240c1c181160350908100d503549005107040c0811154040c5205c207a00c840550f08020705403c11415204445240c0c02d58019099000c0146c070480b4289003010010303805000040c00003812070b0b0080c0018000c5040112952201c2c02e49140144c04801048440365121651801c2906040008104030400140020309602d4490b018642494824200490071300103024404191b407550707408990810541080350300e46143c185084c01c0076110440c0064000d0034024810810a4459141c21041d02e50051201e0620303181c000003200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 302910197 1250 302908947 302908961
    0x302070b01170c0d03180806010315090c030b0c071716080d090c33021902010504030206072409170307110a0f0b010501050a020a0b09010204050a17060c0a020709 71
    0x500b43c812040012003c0d43c4100d0b035440e10910980e9410100b50815612880201142c0d10080351540210014000540c800c146450b42c03114440f80044c544405040003004a030241d0720250000c08584288009000c000d0b00800c0c4040c0990b10165400030780c001c194149210312141001000e600f840d0100014101030000c110b0641c04420106408406894000080e02c0c1540700c03821580d42c501418110700c1d2411003d40d004188030031100a01840c030280652641c0c001a40e00c107040074403414a034116030080041d100074503006807009440f8a15860030f00c01c2c400014600c00c091022100350740c80050414010070710364039030044298149000c0c907070503104550400391908003403049400003500c034144100702c0140020b00485504940ea8218200700180c200182c0000c0e040020420202080a4000605200b110350101007500b00351303208214580240100c0c1c118503403007600b030203000a183d403000c0342c0719600b40b040c003080d12000d45400c0c1081c2107038442d103001840540c020302d40401a60354a036100f04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 302911447 1250 302910197 302910239
    0xc240304060f0b130603050c04090b01060e040906020a030b0310052a0d140a05010f0e010509040c08120c07090203041109090705090c0c0607020708060109020f0c100e0d0302070b01 79
    0xf1409680403030000d0800015100e0040e074441c1d03544400c00030310608001540c10b0000c186c0702000f850849846100c41d15805009410a10001078a240c80c00e1f107036580401c403140d41000d42103407200082d1500070082c01218105510a00c01c02c601d05d02111842e1140c54016000c1e12041d00c075514815071011007a02c0a2a0814a032070401d025121100314680115900b24054030100340c82440c20780390300011030383c060b08145d800c4100007000340b1140325041c00c0c403410f40b04101c624400c940c5d520b28204060081ca60000c841c1c5024042c01c8241d0f43e504400a402004e00103001e40d84c005440b0303182d081c100c1c0011140a050900421940e107120f0070302c8902c80790008003200070b445907642c6580c00304d541001c0540782030000c6172000940518cc6001840800d4000b0154800741480c02d240184550740c0340c406001d004e842e81e0340000e172100d8459610781264132010074030055a00000225041c1d5008124006218103035005084a40710b449120341708848a05074441e00c006203036400d010711101800468090340c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 302912697 1250 302911447 302911451
    0x9120503040e011413051603092a0503011a060a0e010512010f0914091b0d0510020c0c0303031003060b010302072a05030a031b020612010303020c240304060f 69
    0x2084000c542c80d0b0b01c501a00750b0000c010420240002401680d0307108207014084a4a000e0034005803180c4013400c0314880e950351901188a2035181880c03948142000c50200c3c5284804001001003040c841190089483c224000c001489100308100c11720b803580070b641c7c0d81c010410080b1461490040c0b003010044a8103241140c01c2104100c3c24502c8140301f80c01403044148012410403030405240920f0190040f0b95a005481d0b040a049187d612841445c541d03032034410454003c400d603114074101030880c0350044103d41a04018503031075402548464141140c44c014040ca150203414000210380c00b40c13034000065500d1a1561b181c41300101010f80f9643c1c100340c3c08002d01008116060013141d100003d007011107000403840124921902c00541c416400307500100d0340d00000c030f500701383c466401842103411112601400d20000b030003440b448140c0030183c8a40c070b001009243c2e0000e034604849501783d030410300950355081c103072907040c2540d2803040d00303d2810000180040d00d0303034010843e0b010102e400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 302913947 1250 302912697 302912699
    0xb0f010c1113060b0406050403060f060503060601030e0f0d080f01062d0905060d0c110d0e06070c050301050906040c0515071211011a0f0901030b06060c0f03030727060912050304 78
    0x7a10a003170b03000758001c3c000500042401d0050101c0b900c2100080d1111840400c2250b1810000ca600d0f040010281d40c18181d407050740c03d0208405202105541c1d4404042d40c292144502e809003907000166090611213980000109080f8003c0c908a030849034207441403566141c21044210128030040c84a0302001f00da420300040035129200903005000c41e00c01c0100d0854195180100036900c0000001e04643c40440b001a1168200741c03940c1440d9000c0d00c1c03441d9640003d04080045a0080e80a15050343ca060100b0542c21307004501e460080c1e101d03105807003401d0b6850b01040380a90410b0304105964200300540000281590003c401218070b81c141800c00e0042da00d01107013140c0203051502e030f00307002c1da0f1900885890702c0b00520b04402011691803441c0d5066031201021054020415401031400040700d040900c0c040091260311040503003200e54a26000030020320f4803580e0b10b5015044003500d89544130848034070600d101034172166602c04d00301918080d0400c503081c0442c50196598081000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 302915197 1250 302913947 302913959
    0x5040c1a04091404120e1e0301060b0d09150b0303030a0c020114070f0207051c030503091509070e0c070b04060515121c05070c03110f040e010b0f010c111306 69
    0xa0580c401d070403c034206456152508000c0402c0c1503804a60007080b811954513a06030f560755110300c0180b4449420040c4441c004c9020900510305074200000c2c21034041425800389081d07030407982d0710512600347c0108001c018440101070b140c102001c0b651507081072000422101007036000c0c6203100000d2001040c0c1100a818540f0744003c250744a0300065200405901c41d590100020b40c01404140c0c0c00711200c600c520120305210802c04401810400e002000c541c5580c0c1c00c110304150758411144205503404e05038121a07039440340e84503849122007107400150400403070606403203280c1c0c2c01c40840034455449503201001040002e004051005031000b65070300b1a1140d51001d03145404810051800c4091002c40066441ccd0701c40702203017001010001a80060000014a0101d0307500c00c0780d2b10345511095001500c29010106a00e811516290400856480542110404900907241d140c480080240112140c046e145030290518804207844581810700c0c8071101c5c900b00c0d071b81200191341611a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 302916447 1250 302915197 302915201
    0x9040f0507030905071a03010902280e031b0105070605180a0303050a0b03030a020a03080c19081b04082e14010303091d010512071e0e0a05040c1a0409 66
    0x603403020000b82c0e40303000603020403400300005c1014040d19070ba185010b2104407a02503407448140a07617038429402282c81ea08074040000300800c0032960007000f404100d107895000f048001c585100510a202d18403400703080712124a4490450901a561f140c5444100c0d180c80740900350180400c008200c80654542b00040d0602c05c4044042c0329950205aa00308001c0c04802d50782d03c3e420407072003174100300644031056170009240c0b20b4955141c01e20450581e1212001240c5020308584012416600001e0a14650340110014400c9035040303d04000c000c0c4010241486c2c0c0540e01034204250700203422485a0401c08460f0280140307204070203c080c2c0d034034240d043c060700c80004598941155000040c010941c00c110b0200c007030f02c0300c62402103009411141010f074104d018480c19000f9011106052441c01d070a1120a010303003980001d083d40240740c401c3c050801c9015204a00c4075605040100f803ca4506000721406150000500144242844100881c1c1303800720403441c41801040100159881c1c440c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 302917697 1250 302916447 302916451
    0x2a030510052a09030f12090306060a050303032a030a02041d3d08070302090f040503091e120d030c0215010603020a171627060f0201061703030601032301060509040f05 73
    0x2c0495447d4040340c024580342c00c401400403481445a218144280e0b1000030540b0341c009144103940c4410204c092044504404d0724602c03a00d03c0741c0010400007449e12503002001100d8a03180403a081e4212070240050707504090304c01a00b80406100302284080020103c8500d84100317440501e20f9000d1600801a03a000ca070f4880d8001da00001e80070030542c0360880141d45e000c000c808550f5804e01d01941c440340c44e41f003203150003032003001012940503040300f40c000c1704100359001400030455100d41c21020360740c0e0b2500901800c0002c0c10174001030707192480414004a44443c50000c05200d0f428140c0c00d6000e90002c3c0340c08805c01001046004500403840041c0c0c4c01100188540300026000c101d000b00604005008100301d44411820104c0500042803031340d0886107580b40c02c407403400c04244101d02401d4168002071030540b103001080c0c4c044101000850290100762400c0203503246044811040c1700c41450510382c00340d02800100400d40c0a40300814469100800c0040c0c0510610603500480e042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 302918947 1250 302917697 302917723
    0x9010e150406170705031212041110020c0f0105120406050606090616020a060302041202130f0c031a040c05030a050c130603090c0902030c072a030510052a09030f 71
    0x200001c2d142c00e43d00500003800a000140c0140c1641c00c00b0302003194841c4240603808a400c91143c00140c1400340c0c80300311310400340b00200baa100812844034000e5540c1100300748140718480f2a03940b00f41035806401101c00c62508000c82c40e020303607201c0c3c44805c01468000d000760342040c0c0c20000b090407a560790380142528210550300501044d1176006200301c1c0c0e55590040700c24144100800d110050f04403001f03407403250b07041b1826019a1000d610690141030510b004055031410070390400c028507090703048041d81f0a1520035200c0f80c85a21420001036500814113400498000c00c0800c0c80805960800f0f644a80003c0505140a04102c44090600d40980c000c100090f52626001e040100c0200c0f26002086079101c04c3d811130a1810040c5068801c01000070309545881c0070350021141342401001d0b051081e40201440982d403800c1c0a41c4400107501c41816503450100000c8106481c40190021810318071401e41180550103490b0089901c040c0280d5070500c1896440c004803502040f0301422150 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 302920197 1250 302918947 302918969
    0xd0b04050d020601060914040c02011e1a10080103030c050313030c05030c010e1003020a2105072019060f060609060908031213150603050618060609010e150406 70
    0x10484000c3c24408103800080030400070000030010031131210303c500d0b002e0008031400503503c46550300c10303801080318520031038042c12000900c036542c8000754044480d4036501038090802e48103c1d0108480403c09a007002c0125410200600100b4412010000c0c46407141044914156900c002c1c10b1100909500403a86086240d41c14030580c141840302505510b0300b820490b0340034000d0000184d040310044e038140109a80460000c0c45207201d01c0141c420540c2018142441e0f5018007150005400c0403505c0d0400304a82100302c801c3c880c80030200701010041c1e82c0248c0300c1c248025880c1c0c81c1020000c0701c15100e80740c9802d041040080a8400c00e00140425120814014a032a40103801005241c2c440905070304203121500100d4142650154044400d116400031380380c1c1460f1031808030b0310314401042c40b9403030040080f0803c4070000d221303801110741341464010781c2c0c0092055581c5080c12502d80350010800340040003041c040c180030f59080000700cad854010005a6201040460301141d000103040d803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 302921447 1250 302920197 302920213
    0xf052e1e1508040b0408090307090608010b03060708010b040509070c05010e0105011406070302100c02011506170f0106020a020405040c080a0503040f0b09011e030b090a020c01050f160e0d0b0405 85
    0x81255200381c4204049051942041c80c10f600c03400050ba01c0204041d1a07074000043c1100682c0d000d02014002c5c21180604000054840b4510340c000d09285184601904c02c40002c61400c41c003541d1101e040343d9001c2d6580d0303d00b506220034403c100101074040028802403136040000a0002c1c01413440040c980340c0009030561400345c21705501c51000201c58021b09041224201080d40820b000d940c40c0625480441c060b14900c00803030040a003001421007045040a0100d0510745c0403107107003885594089591096110401c0816002100388552800350f8820780905d07005042c680c0013154000d004484078100c40e075413040d0007070a200c1c04d091304954036000090280913401400045130080c2c8011603500b03042114180010305890041700314582c20500313052414000380d05c660801c882c0324601418414060514504000107500700e89010040780d400c1c200081c1b82941d44040341403040344980380b606c0c1941c0105a0948482c0c1a25030342c80d8025100d181e85070702041211040c107004900c82d4004088403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 302922697 1250 302921447 302921459
    0x10020904091a060a0519120c0b040b0424050702010c110406060302120a020711090a0f0f0c110c0102061803250b0906090a06050a020d0e010f0f052e1e 66
    0x1348240d003040c1d10904188141080441c00c0083e40d400780da00d058490458a1828203141c4401c07600c6600600b102c4c80d00040129608a1603001b030070403125078000030f1100d4181c030710103001034084032881503000032004d001450166110314150b8803514020005004402c1ca06008182030ba65150000404260001601084001151f11407079104400c2502141044645c0d0703200400024000d81c6071340b040d801e0801051254002d5030008843c030030845010081ca03002420a01c0141c440d090300200400c504804014181e400070800f9804080140e001c1e05150399101038801c10f252040441507070a10040c00b800f030007166000c1c40c011024040804021158115142228003c0401449000700750017000511403200c40005520201e20307401600822560b5443d14034074000d004a41081c40110700304841c02441d0340303066001c8444244848010702060050700420020399401750f88060b000310120080b85511a010464155005030380807064200d03690300c1312032401e080e040941107103d0040c800810080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 302923947 1250 302922697 302922709
    0xb1206010602100e06011202060c01141617011509080a05100e160306020a171810020903030412020105070b0a05160305010506091003111308010c090810020904091a06 73
    0x711803ca10b01c188040383c20291240c0d00c661042c03280000b2800c000c503407101150b54002c1903805541c1120001c2154130f08481714001100000d880c00303603034841d4410286580c980706800b0f407a01078046085428042e460a0084085401c0b1200c0000800003460720100c0c405205004007006940104000c001c0000348c1d0203d24200c031060b21650342c4e1540007014002811031415013450489070482401a2107444009064613001070301500b03900c040740810100142000801c1e5001e811808003005c4648000071200031038124892610300c180c0c542c2c000e010070040c8040c076143e00d82c01e01d031042c54040e00701b050581daa040fa8580030340700d000c021a29801000b0702150070001c10041050140f80a000552601d00070540c503200340c1c1d00039030164096000c004c902a00a41100c00700c2d1508241299031210407010004010300d250207000d04550801e503a80b00c2a43c41481d03400e040d5105680601070b444241c88a400c02507020043d000d4209440b05219000301e0440c560320b00c003a004951010385685409010480 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 302925197 1250 302923947 302923963
    0x3070b0c0d0516061a04090311060c04081b0409060e0a110312120402040b0901170f010605010215070e030d0c02040c140906070303020705060c071208040807060f0b1206010602 77
    0x70420505016000740079904011202e1100e410440025a070303407440120aaa1860380032030103400c90f00700103019042503485401c0c00201ea402c441541c000352114100c1c3c4601703104078803443c04268003c8441000f91107a15445100320704000f030000500b58000c0c1d031114152050905e054080d5040b1821000922801034240301c04080110080c004405013003a4524a40c003444000441240011000504540307a1354414807031410300a110302c0e510343e510001490801140ca252003d14005c01480340071b01e407414050f190603210147c000d045200201c0d101e816400c10010413480030403902d01d403103100d580c40074065070207080d4090fa16403480c0325a80c018003080d503c0340c8296104020702c000241c400c0c0f014001c251205c0d503004072010340d0b0307a8100d8101100a030040020150680c001d48082c1701c10008a01d001b0042c0c02d10828542e0700303d4035503040560307040004480140010f1420442030002903041e5014002420700724000040316000e24001c18131022521525244581c8560f0040c0031264040002d19 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 302926447 1250 302925197 302925223
    0xd090e0106050c28050f031c110306010305092a0907051305010f0c05060f0108150c071104091a0a050109062402210403020109050d050d080c040503070b0c 68
    0x1d10f441c040e201900e6860810441d60151a403207000400c0001030501103055050b60044210350420400b004110303100e90090142880d0902d00c54458580f400041c09111070300d03103c0d4082d0b6425a51100c1c015400f510000704120709070b00909400f0300b414000503408140405001e281e001c6842e5207103083c0103607114017403e134101f03102d0b0500100011403140c80b65601550020b2038442c494401c80c0400b43c0f04500000002001801800200f003186928510000d049581389800c540307140c0c2410305610a480800d0b250820a2038041213000c010403401076901e0f0200c440a840042c040301152039290080b006001f5410140c00f0340024014050000d0203098094030030300604020703a03454110038a240b509084d100c0400114a020201c00c81402402050300e420741400d03914460044445c0c13410281e6100d400200d011801c8400d010405080c070540f800c840c15072040003425044000e010540d03078020002c001e11044c210400c004078213902c0910012000f0640f550846454100c08a6540d0900d8400c039282 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 302927697 1250 302926447 302926457
    0xb0301060f0e102316060f1103070309082503030e0f0c0103050c2802010608010b060301170a080c0703020312120f090a050706121410260d090e0106 65
    0x54101e0390321812807992000f070504004d090445a40042c4a8502c24040c202c242e5000c003240f201641c6180c8042c50004c00d1107080101320366544042c201d800c43d08103400213518503005000003a003141c003d510007803c1c0c0d4090b070007a0341230004035100514507040c0c400c0101c2143d820407104400f0990180102d180341820140500144400721003070a41d1003118800c03090425460f0004030320000222012110000500850000641c1200c140301e4850303480a81c0c90801907207400e20010703d0383c41c10702c02e030280c82e0f10040c003043c40c1d640703042c0f0000e480e0f821800d800541c600a02c045000001d40c100000d00780c2d40c038040060041076265004060403c0541262175010b4901000005580030301d1900440d030050300306822030002d84803004064600f40070701800030250b20909102050f01600a04240171080e202c1c1d2f0b040c89000c40101c2190180841900c8a40c14080711903c1030010741d5000d46848000c00e090307501c1076000e43c12000490316010a805040c008038000580c06d000d1b40b841d840800d0b001d007140f0b00305 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 302928947 1250 302927697 302927717
    0xe0405071209020d0c06080405070f0602060106140c15060a0603020c1c020f03160606090e0a0602030a0908030114010f14030609101707060e0102070302010e15130b0301060f 76
    0x30341091030364001c108009903500b49100840d41c91842c95021260014490102c041d241d407005000b03001c3c1030f02c098505104441000503903206494050042e1021903005e0000f5901c0c0c000f003a19001d00201c400c800d400014000140c412000b00088005a414000c8082c2c15013485020301409072041e0704a041014010840034100030000588600c6114108045421854640310224105084601e6001203070000040e40d05081d0404107a18001e94000d40040014650782d80d865070446030f034900d00e01c01641001d1146c0010842960181d0386c885410400400c04030507665610426620981082c940ca03036041d45d404002d0759125900c1c00d40491203050070500038013a5284071401d80001400740f441284010002811074880104600c020200c0c5020290409011002c0c2908c40840e801004d000583c0c12303007841015071001422008494043c0c56208980139540284151001440141030104e43c0411603000d105814071a000f00178402c8561040e260b50410500500404a8800c80010050101c103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 302930197 1250 302928947 302928961
    0x80d0c1e0c14220b042a030c03150803340b07020309040f050a1512080c0a1a0411040204030c06050702041401080703021306080c150705010c0306060e0405 68
    0x107901c041d40d60080c40200d0244144001801425061004640850f1006410b1030000e600da00001c0041d58121801e0000041c4910f094444145a9001d15603065078841d41101060103644000112025403601260b806602c0d40700c0050031200d136101101c0c42d0300004a50307501c84080489640c03600340c0710024140d0074012082101e00b400c0144009080b1054140c041070543d4001c01c111000850050720a11081846030812001843e08642080030582444007142d03e03c015400a9000e4494005e198013220760183c0b01d002c0030303400010b000600342c400e03e1488070200360382104c00080360b0501124030361b0900c0e29250240444a511181a019600501080c4002050b500c03452042d00c880f8901103448103282e00005024041e441050209042444000303e081c000c0850700e00240c0c0c5c020364046600c01901e0702007c00701c401300d01c240d48042e0030995003850a0b1500396450300e0724241070741000382801040e840e584e00319205510400c010a545d01c0042180641025503030032001e604403820080e41c0791031b071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 302931447 1250 302930197 302930213
    0x20103060e090c01050f040503070b03040212012a170c1902030c0a02040e2401050307080a0b060f0105070605070e04110a140912160e06030604120513080d0c1e 70
    0x101c0c203c0d041c0240414940d5222000c0d20580740100070042c2142d43c0f09070744203902c16841d402035a0036400b500303840c05100301e031007014000c90030001b11080205031040d01e0200800c4416090000d59001c12800031256940002e020354924001c0010500217940e483c1690702804604c0c00c8004000103640040c0310040070590040f43c1c0303404090701903c0220700c0d03070030444402c0d041c8800e804801020001c00c6810390004c1403510500c5040c0c1e80144d04840c59540c0700e491650740c03014403000003030800d11804001021800c0071158110000b07010304040b800e00b0b15a980d04002e88008a81107030020324101000301c1c00b45010302400d240c1c07058108940c0c1c5048940d101c02040502d072035a40e500f0360f44d40001c9160260f1100341c0b0f940c913604086400d48281c0388100501c1d10540c2c80c10701c1140e0510014030003103519807a001c11814003495210301109500c02201d1016030f61500811803485135103050003400110000c003404405d00c000b40f01c0d900c1501c1500240351880204040c5d0004a08060410501c200007845c54 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 302932697 1250 302931447 302931463
    0x15020c15030705030c0f03090f16050607060e0703080a0806190b0a230a0203031905010e0f04110409030e090a0c121505061c0f020708030a050907090612020103060e09 73
    0x70746032003550785d544d181c4902c41034442c405290a144100004000281c24042006ca00000b0000203856001300d65407290f00392a103090241d0342e4808020021500003443d1035220003250100c400503640740d40d0381d07500d501901d40c00140c802008104d1032420020f0510b40384203c032040350410382c0101a22070802c04d00846902501c00490140070944002c01c0704400c403107142c12451440c0c40030080e078032014440003d499403c299400c011000f050010f80c04101481e0041c0e6050320200d00407a071803940d400c800d01d041c0d0003010340f0583d00e400941d062903501d0f440790b026410501d030107501c03030800c0c885d0b00b0020f0010400d00241603811a40c039000c103a40310fa5503c10700590400303084250110b03080300c8800008281010f507a0000b0790141c00005c42142d1041180768664a10031480410800c0e243e2000001041e80700c0c0d000c000300030601c1000000e9010074964081034114401c0f00c100e44ca280d444190131421208560844040d808901d01c0c0780c0d04569250003400043c003580103030303941203007400c100203513684104c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 302933947 1250 302932697 302932711
    0x6050610120e010618020711030c030c060703031e02040608072a021f020d020f07030803130602070606030507080c0d050c01140c0d0801060f050a020601090203090102120115020c1503 80
    0x1640100b001000d401d40002019003000c14000b689038280500c100001d61220800f101c0d4641c82c181030034001c4c61301040618103154003a0103000b41307900760020064164082d883c11010706640b004010781114028244c4600141d0381d00d40140e0b41c6e810042d0107001104020030380d100f00409004101c003130080314180c807044c1100711150035003640214400140448000095501907854130503140c091107900140b8091130a150350241c0e4104601458600e032a148070380002b07062003000304080b5901102003003d041c40c69000b610010304001041da41c0d507040d0b0350300e54000e441c1a40400011b1118400a0214004400003100d03409a0200c09540d02500d6034256901c160510482c440d403041c01806a50031038002441d100180c0b011040c80b0940505038400038040d0400199004000c1519540150101d90a03040c098000f8001c0c0d82c600f011a5000c0c4d80010141503295409124800da1101c036001c0c114060014843c1c500c07040c020b0300d40001c0c03500c01000042e40c41110100c0040841d00c0380001101c1d00809 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 302935197 1250 302933947 302933951
    0x20a05090c0f0c0307140d1d0406051c030f0905130b0303090901060201090c0e0c120c0903191505040b01030b0a0204030c0305031201090c021f0e06040f0605061012 72
    0x3895030004446030203070000d01d020b00b4000140c4401e894101000901189105449560010350319000c00c907030312604408444003181340c03020100f15100200b2901c403040302004001180494a0744045505880407502541030340708640e040600301500056003030401001850102841407820380000d1110303c80b00c070740070241da94400740f0140715101071003140d82c41203003c0c0c100f0800e0350b5901002402840414000d8480e15090a00802c128903080350080c01084040003481c100800c9003100b82203000c0250110405503400c10544c6000c1c1c1381805800f220190230104c0500103031203810030300c80b01000c42c81c200703940600d8031307003000300042101039914192604940d200b21950f64044640703009104981000e42150140d4030000100200000184007101e2004200070980c1da8030803104041d5160106507034056000705141215461001054807082003c1810104100100695142c1040402c0e1400e441c1100c01507611403e1050b540240f680005042c0ca028041d0310200c0801001c2e5210a804940342c26 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 302936447 1250 302935197 302935201
    0x90611010603140a11010c02010c0b060a0906061107050a03020303070b07110102040e01081504020319020d08180a0608010308070b090c030f011a0a0b07080a1b06150b0304020a0509 79
    0x100950060780510380c020030301d8500c3d011004003e5981d0340c00c298100d6040d1142c07000c50301c080d4030843d000342c001030b81a100c0149244c01540c60107140c00c401002180c20030b260314000100160a0301800c0d0040401d501d4100c4406081c000e01c1c1c2c1410419040039024104c0c0000c10001070703c00008403000b040e08001d408031036484c4e402084601d0380c02d01d4540c400f2503002040206029034140100c0741219802c000722140c0e040220303005c030700846007140c002c2c0d45034212424030b03100c41043d5010000154801440f801e40070805988084081d00030b030700041d400580c0102c01500b6400c003001640040c000078184800150303d181d0710090b59100d50140100003071030000c00320340301c00d20420140305c15880c0202075800d440201c00e0394074000c00d000e00c0f44080c0c40140c441c440b003c60410031540401d6407040c03111740d071800d40700ba1a0812558001852034040180117030b6102d004a00d003540079090b032442071a0105001c5c0d020641c0740d80000003504036030f0004000304240401070741c824400328102e0b101990301000513 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 302937697 1250 302936447 302936477
    0x403060203100b0d360308070c06020d0b030c0102061510030b100c0b01050d021503091513062304030c02040b0a0f1d07020303040b2205031b06070906 66
    0x2051654483c0100035008502c00c034800400f500714010308201038008582c10400301d600d090b040c40400180c032001d501c80340b4078440440d10410010354001c01c0360130300c80c0c91002d491f511034003203901255103201190340c2c4d0103464940d0b143c240611a407841091004103a103041c070540600f407410540b00da003071103240368042414400d80641c002c500072010013002e410001820420240104007800001c5a910303910710000300e082d140c05090040143d0300508208004a41000324a602c0d90000d4140c901c64400c200751074021042c0c1c56250b80c420f04002100344588001450802d05860501c1030019841d0101402004008200010544e2154240c03809407440d09141c00810001c0101070b2105820140501d40414028100d00700c1d1400c807480d80321a02440030020300031681003001610780200507002040400d0120750030303811440d0082841110103000300c0b54404c0d001c070002520355049640d5000450200440c181c07a03441005403000e9080600b40502d08000020502405401420288142020f4440320 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 302938947 1250 302937697 302937721
    0x2060603061302011412070e01180902030406060806040f030305090c01080c1c0f0c0e040908090111010621050f0a0302030a0f02030c0109080405280512010e061008010e03040b0403060203 82
    0x242c404802d1950342e50a001b0328103c014800c403101c0000c110303041c40081165224400c40c0324210102804044101d00b0040014017039800a407095404980b10354010509100074480c0d680654800c1503c0c16612141d03190160641c0d0b40101920443e40180400e044140d03042058103903c001e58121065a03800340800d03200c40054185010007910b40307080652050301c46550710103c1d001d012a2111210240303584204030544003c098000c0085205024886465004240b202000c0340c00a0011039036a441c2c090880d6518054028000d00502e001aa503040c0b050512801600c2c101c1c61000d4411000d250314082d45c1c0780f10300f1080200304810b020302c83c0c1c0f6891091003a5509151900300a10a041d81e505080d00030350850300550f0f2090703905181a0185441c40941032620321105250400401e1510081000c0349212007a0340c0e950b5500c40700700a101c4034040c46124030030180121203c1c1482d041c004a10f08607003400c0074140084e8402c000c10b03c21440044203071000c07298841c5026a40b5503034413001140e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 302940197 1250 302938947 302938967
    0x13050f12060106091a0f040504020702031905010b0108090a0c050f0301150b070b010f08070902090f0303030403320913060806040c0612050411010c03141c0c0206060306130201 77
    0xe902807030001203240340e4440840c1d411142c0420840d09008581800403029105100c0a8103648204000030842810150007508416000030700783c80e04080364410141d03034125010b40407541070359a000619079540c1c1210b2800d4100201d00010031002805503140807030002c060007428452035407500c01c2c8100340d4094000d403c01010070300f46503843d242d07241001c0459811580c011903071868844000702d00c1c0020807030074400b1110b80d1b070010408240b9140d5036000951290140c1d036008080d41c0c0c0c900d00942c408000440c01a4440e5803181c0f5040f241b41641c4829041c9005c2a000541203190901d86204980095a00101e41210701e00075a5200102042c0204902c0d80001c005000d040d081006003c0d8110206003250007584480d40d5801c0c42c00e40d100b084072000c8038000c1040404402402c0b032540f1810603106164441d040242030030f0015200c54140d40c01c5030f1102d0b20301c0007041c441c0703602103e407038000c044c0156201d00017420242040300c0000e8950400901000d83c0e803801e4000d010a581c40b40c40311003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 302941447 1250 302940197 302940229
    0x501120f0b0619060302040e06061e070602040f0608150105091806040603020d140105060f0a12150f0638070807080d0204030303150e150a080d09180213050f 69
    0x111403d6552000130740690841c0c400c3c400c405c504100013401f076040003000c440d0910360380054076040c81c0f100c110f44a402d4100c040192805542800003080e140342d49420240a001540c4440089181c04640c100c108100040c01c07e04000060081c3e140300d480381d4200c28805c0303807200c08003540ea41c0c42e18041002019143d10107540940070301c61034410321149d03071602c0031b5000062009200a0f545c0c0805c0c0400914880241504588440c1e8100101d0605041d01002103101d11680c0440c1261440e000c0c003528245804500b505903075420400828114041000b05c3c10501c2c40480d0f1800781c2e1100d1001c0904c0e4544210618071000551082088989000c030740c01140c0c448c0140e030301c0b14011a01100250440d00080300460310f00622804040c400038103500880300086c401c1003203a0b84549181800c06c0441c520342c1d8119103824000305400720240000c11406a03641d49418501e8580740c00f011044003140c50440c2c51620400180f102c00008104520580700d09988041c507010607040440c1018803101800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 302942697 1250 302941447 302941489
    0x20a05060c07031209170306060c070608100602010b131d07140405010b1c1d030720060703020a030c1703090d030b04020f04090c0509090a06090501120f0b06 69
    0xc1c9048000003a1075070358001c0c2e07036895041c111130340d44008803401c10401614030504140980d00340700503440219800407028141c1c0781083c00c12480c40380b501e0704075005100420680000c02610240c10f1190ba03008029510090204000040210340c00d05100b2174201d10450325440541100c01c542c1440c00c40c064550750403035406a07900c8070710360f005444164100e4030590401000183d0600001c013900c08200d20070160548910340101c022000f0507a070344503c19110703c1c0826801200b2802d102603c02c050082c405184807600807000300f901c0c0c110041030359106500c107000310404a41d0004080b4005545810000c1c0c000303a042c02c180b60001561400303810951400000c1011600c000f240041640c07465840a01c0b014000a003044241d001c3c107030480c119140c06100812880b07440b40c02c441c035500445d05140b4644050036021170041034048491350607513034a9240c1045164528491180101103030800802c104200b035880362281a110b4901030594158000400c10f00e980c1d11401801c0d11600d0044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 302943947 1250 302942697 302942701
    0x301090c080609010c051c0b0a090c0e0907020601031203020f04050a030302010b04050603070b0d020912030a020d0e0d0804030813090c0201060302091b0f0304030201020904050117060702161401020a0506 89
    0x1200b03940b20740841e40360032a9400c1044000c5d00501410558071812100603045c40c496201c43c0b0a50014880104565130001142800150640303a0b4412843c0d14001951606080690b42c0144002c0c2000640800c08542c46140108086401703042001c011f02940d25000d65034038950f004500d00741c0200c1c0c0080781d110341d5040c400402c1640540c440c0d961418240c40500060383d60004150326102988500c0c1103221042042c45105c0300320781d00a007411403000f8403074010403007101710306031444d0007005000002d41e08c034400b61044660480d4030300d0340da107004440c002141c003180d40d80e52140780a240f20042009502050340d40034001c010700d0581c00380012000400100ba00c0c9080207002e4600d03444107034000d00b020004601e004503258101c847c1c400b032510005141103071710340700403caa43c00107005600315507003071024507000d03034417030140303074001d0001c00c0b001800e40c4220201141803101c06458074047d588041c1d040a20402d07440b50305802c9514410100454022060060303017400d079001002045030140c40c00f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 302945197 1250 302943947 302943959
    0x1509031b15090302030d09050a060f090b0403300c0305070f14011a030606030309150409050a0605010306060302030601120506010212190e0d1505060d12021b0a060c0b04020301090c 79
    0x882c1e901224002c8040f900301c0034109030241e0310350800703000703003500b000302201c0034401c4a0140b0070b0040c048416160004403960703034468141c0b103170300326400c129500a0454481d414144080c1c034843c8058080781d843e4000d0010054001c0e0151621032001001e103e0042400d50a1000840080016070b40101c1100c44840400307a140e070007007407017822842c04101810788182582c100021414441c80014000f18038295480c81040002c030420352103448407603820800407034010350314060300f4011408a040030414074280340000d02550300070b0b040201018030600400100d80c1e80821040a030f40c0324140c002465886071030040382030078541e4010300810400052402141040010b05022404144e0f03034a0341142c00c1c0e1420032501d10703012500541105480413590030010101e510041c1c00260007003210005129503030b1620541e100182d00075025820845980401d02ea90070500070300c46008940d54004541804009080710b000020050f182c01d00c500000340c1191425071083c008540c0010b0010b4409a40711 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 302946447 1250 302945197 302945207
    0x619180f1b0315060e03150411031c032007020d110301090b01050a06020f070e091c021501060e180a0f052502151302130e070608011509031b15 63
    0xf03072102d080724140c034200044051045e4880242c20500070301802500d10700303c01031400382c1d5015005440032000b400e91410942e0b810841d07210fa0f82801c00600c4841640100b000c0e003180c03031b00a5050b0007000244070120f07448042408032070b0090f80c1100d603074503000d110b42001c043c070989030000c03540c1562030490301c40d06210000e61041c1c1281c10468a12201d0358440c0070481c4c580e812030317882c1c0540740d02082c018403406440c150019409400300045480b00c4050003807014030310030041406000346c0c0010300300d100d5481c60084c142d4050104e50801256100f55480410070a030700301c00340c400c07500ba4107101251b00b0540682051203422103041d414406818042c114400134080540051056007070805c403443c03860700104009c42402e54451101c402031f078603860030341400c003614001282e0241135054615450b40e058882c00703c9a160105c002c00c6000d0800e0000303400d200d010703005404170900b07440c0d010740d056131b011700050143c0c1e920011101c1501c15001820303c043c00e5981040c0a5030700300180790a886c40d440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 302947697 1250 302946447 302946461
    0x81603115b0507030c05100e0708030405010507120c150507030b090115050711040504060b1e010c0303050c120108010203160309050a03030c050f040e061c0c150203040e0c030619180f1b03 82
    0xc40190744027166141e03246580c81c4558401e40e80032480500505010822a90841e2003c00003030420300f07010101e0703540700c05d40f2545044059141c40e03541c0c0d00380a00c2c2c170703031610960880c8101540da0500b6941000311b42d03070a81010f00c0d140010858000b030410308212940f078100303820301d00291051120342020316045001c1c10950041038010780c00018100f61048240408503419081a110303080340c4a542d0318102c01a045c01042d180c01307040d0401182980f900d43d860014000e0502400058a03810f1121000c0629400d80381080c00b00741c01e20701c5020100c0c07008100c40c40d00303079810300780003170f03200c030402c45c19246070140c903607880c001440c08200061020b045484091003244203c0c0d0824603201c00c2401e01d941c1d14205c4c540509405100b1742c007030140305040c0d0305a411004150048a0138540d5882d400f0988003011980344d50081404818401c1604003040c04444540c41040e8841d006130802001001c160b0342c2010402d0251340381c0119400f0f550700341d4031402009604541c0015001030b1184040c01602b40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 302948947 1250 302947697 302947721
    0xa0c081b210601081b03150103060903051612081b0301150309020a03060903030f021603121b0c0209011d150604030b04120801081603115b0507030c0510 67
    0xc14440030380c503860041020003064002c0b00b203204c0d190f401e545440ac02058515422030502c50f08114034030a02c041800d14100451240650800f420316101c0003c100303d01c064015401d41c41c44000d114142c51407042540d040d10f240c1940040801203900d4102c01504c400030029420188070350004c03040c001c282c0c0101c00c00f41e019031402d110103a0203101c48801c03882000e20b0003102000031814140041d125038146640200c074000f020034020b213000306042a54445c5502c8002080d6840d40c40c90460902d019424014190444101e40c20500401507010607100107041126800071513000c092180c5c0e680301a03a003e59000740720700340395141524116101c414990206400b080c1d5100000407806d40018841080340030422494029034030b95600e9050b103400c001c40c0e056000d0300745403850038200e0403d09001a030a40400c1c601e0414050005854400503802540350714100a51132480141c51400107004549c15203450f10710758941180c2401c955001604c000180f142c0603418810521141c5c54100d1441008 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 302950197 1250 302948947 302948983
    0xb030403170c03010303050405010c17030a06050411210414030304080a020c15091306051002010902011701051f0309120509030d0c052e0204080a0c081b21060108 71
    0xd0342c1c048600140824400140001c00810060005511920800c40c0d642e20620b01c031960940200c0d82c01909800448a0100050351203408210314507160250390424024844d0705882d003460a44402114104118407010413902c1c40042420000442c1d5032022047c8900180ea8880c1020706d4480a42c0c0e0014a00000510500c1c801000070f180500c0c4070340300341c50807a008507d4000e4203010f011000c2c02039900115090f5079048002040c0d254500c0800c20450f0b550300003d4860980c1c80094544101d0b940c100000c0340c00340b0014840727a15005030401c400d207c440807086522401d0b031400c8001c1d10362010020102c540b21502820083d42000140291440131001d42d00d2070580540200c1e0041008080030341a03a21032040605a448402c0a0340810100c00c020915035104d402004001c3c2e80c0940c1c005180c541c060802c500a00c8055581138001d004d8180141400c6890140300c0420300503101e001030310804140200965070340b4500d40603200b501400c015102c407981d4400ca16074a400030b0108002a1403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 302951447 1250 302950197 302950201
    0x1b080a09080f0601140111030c0601052b0305030a0e010c090503061b0d0207050c0a030510051501050a11010b0a1d01080d0f0302160b0f0411090601270b03040317 71
    0xc000c524800300d81c860b44014502a803810310f244402c00212a240b9041c404401e02043d00070700144024504440c040d00100034a52600060061003140a246c2d4082d8860f1800f010514000080304112480d4051a00030b0310b940310107800b48014620340c155494250301c0c042c7d0303400d2405d400c403120700d0803140220706031641e6a03a008030f1261150032705145851888810080c08503c11901d03400f51420501801c00c8503003040d0b403280880c81082c402d800903207031039101c540c0020390503089020315a8096203c0d050541c0440710800045c1c100d02440e1911401d003c1c1d681c1c440c1d43c0305003095010302c2032444000c14001c42682d441c03900d5202426401241105581c0140c00407502d41c03400501c040001803a6906c8081b0700c85401001c07002908418039119044071420004000b0400c0903002c680142c42a2a8004080c200303490300700010a90400700d0ba00900011007082181d80c0c0250310b00000e20100401c900000c0380d644402d000403403050b0004540500d0200c00e01042c50b601241c00001d000c0e0542d9102a5a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 302952697 1250 302951447 302951459
    0x30e03030313060905070b0a0801080c06040608010e1302090a0b0108101a0c01060e15011808061902040b04091407020c032a130c020c040902150a1b080a09 68
    0x1e1008035900026401a070125100046050740030050440c083c1c0b040e200c2042c0c642c2800704041d404514507200151000006000e42d603030a11900b100c07000d0072207001d45081d18009002d44500c0301441b681285224000c009940d8421800560051550040c41104645400e12040006020703d4400c58000780b00c40300002c00c1c90180c0c4041c241564603605898800c0321035182c2e0350486511185004030595210000002c0d01c0d0300c0b5526141c0100c0c0c88060448051062070300041858051018100e42407820640c20440c0e2000070603140e400031101400400e000115080f01c0740648502e034403c4103040d500180014000342c0a82c09040300380c91ba40301500b255181c09030100c0c1e40b521101450755140d002203000c020100c0c0802c480080c51174141030900a000107400000350f038420300b5811800f0f0b0b1345e240c142030387c0d00c554103001c517800240d412281040400c10580103e1105082c054402d414210002044031b101d0b801051542103079a58440412800a00c030f18040f80c442c7c01a547c04404201001d0005c124 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 302953947 1250 302952697 302952703
    0xd121803022a030c060c150109061a120115030920041805060c03040317070e03070801020a020a20090103030e030c010905060a0f140403140c0a051305060a050418030e03 74
    0x20818004005042100154080001707561140300014254440d10030b19420156400c000540200010140099994600b01154a03a281d00d5040e1031241c0808026076959952108101070541d245282d140d44042a016420740040c6041030b00541000e54150a204101d540444410f004e6501541d040c0514044032103010318181542200070003a4110000080980d84604c0c05950f001c0c2c002d1420316200242c03004029459038060300c00900003186141929080c0c241006200000c1030700d0383c000c6190003007031500203454101100c8010140980d031402c030a2568900314807201d418200802c0c8040b00e5940780b0303001d020440e41d20a164007a020350616a00e041d07000d422440201d07000907101c2d5240c0340a2420841d9080d00c014590300038460b4030ba68030403c0b4201c010207070000d5481481104250491900700b18a06402100b4061080614600a10081c1c03240d134101c0040c249101c3c80484c503900c0ba4130004001c0001d0313410480e00300b441c5c4004082440400c0d1246641180251a1000c1180d0518103044d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 302955197 1250 302953947 302954023
    0x60e01090c140d050709170609060c0a020a11060f0f0c010608010204060503010513150b07021c0f0b04080c12090108060301140c070203030f030718080703050d12180302 74
    0xd541c0c0c040c0120b803c24541c070340202d039004565262401c2d9050721114480b548102c1b056850b00d09500c04010040721800401002d90800380c2010300f5030800700341e082c1c000d584a0382d482004000c1404c800c400322480e100c40c415100c1400c0d0008180d0b031604100004035074507410600210304039608113031001034a10b20600c00c07a81500c80565425195030301b00810720075460005244c804040e9230787c5100d0301800a06130ac84c000a040c4101000c2d907241901e0042118005190010108032043c400c003400002c0c0004a080400c942c3c814840c0701d041c1c1c1c82d4180f01d100d0380100903018409018031441800c5c031304590f5008001c0304c01d0980b40d4600945030768092500300c4460a0315288075046500c089818034113070602800d40107200070200c1745403104406031008550001d0f00c081d0301203100c0c90480c000e4684a1114100609810030041c5145032442d200c01e51307685035602500302880704440f01c25002003519040fa40c041d1101b040380c1200668217240080d601c6000e142502c54881801182da04041d81d5001d003c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 302956447 1250 302955197 302955227
    0x7110a1d06090402030f0a0c050109050415060e0a030b0c0703141c0b06041e08010522030c1e1b0501031112060d140601090b090601052704060e01090c 66
    0x900756900028408050006003040e80c0c54498885812542e07042004000f0a00c1d105450b0361181e0382c94140054032000c81c0340c0181d441542080100103408a0741c902010403900240741c01e1200141c000c2c040307456180c450700b01909403500b0742c04020150b840d0600800b503182c03203956501107420a00541c200c240c01081d209542d030394400400421550403d4000c480c1d0f815000700b10758901a030f903801008401241c41107001041400e10343c1001281c03000c0c8203007540f044058862001035881c244403a5040c4080c0e410050a1115201d03210060160410000c460501080b5a040c140c4900b0308149202d07620555019000c00350340034001c52507500c01c0c010300fa1000c00210781c4a00f466a1100341821000f8024092904005080868004540e038201e01d0740c1e068444402400195040103005020b1b1401c186170309020b00d035508244409664484112031405e40c03802068203690400d065102000f40d10980d6090b84542880f03408a003040340310302030a04030b4800003020840704802110560b1440d191030111 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 302957697 1250 302956447 302956499
    0x90f04021809180312010305070806060d06020708040302040e0a020301052202010c050c04050c0c060a05010501091707090c0f0201050603060408040b0a0c1b030303150302090a0207060b040207110a 86
    0x9000e040c1010900c06400c41c0f109008082100c18010050f0b1441d009010318180c01740d2950010810302205000c850064504500038144510342400800c102c0c80701100001e02c100c1d400101a01405641000d80c0c01440e0300403c00d00000311400071032941c624090105038480e5103070102040011800c0c8a042600d503070600019007000710a50010349200c60241070070b076901e00544070740102c55031320f500c5480d1003240e41a0f4060340310900100410701d00170000b045281020b00e44401400b035030381c00c5824003044505240904400000402c1d655003000020360005003011305100c0c3da1802150460140212500668020042c60b500c03402059940d19045d00c011742100340410090042d81005401000c40c8101230070010072030641075440515002d404460061082c44000e014800c040d4540200c264500414a440f1041402c540000320b504d0340c085c10410300780f03078000384882c2000b00e241c010322408c10740108215100c210b00d0800034182c0c240ca1071030300e1044a0f00800841c0c03504070340d05920900d070340c00940 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 302958947 1250 302957697 302957737
    0x509060405100b0a050d080307020f160902070312060b030a0b01021908030405120d050118051e150402070c030b010e071d010e030f0c0f040c0e09100e0c090f0402 71
    0x100340c003c0c0b6821074000d8005202c00700100c0c880d11a200038186861091101582d80d1809010003410410b01280320200d0760018090500729103060202001601d081303181c01a65020280f905560403036544890041141c10500c0c002a40030001002d1403007010341c2e031400e000741c601c100700483e1503001d488800c5040910007400c800110380c44101035640b01b4429030480740451402e00c10094560000c0b440d05490381d440d20f0041c8052100314114480940c84103c1c280140d052059030301110400020510408148403000521801c00d0b00d1500c01c0011000ba20855403a0498107000d0540d10007400140d810800c80000015000c8840c00303900d01c00c1006130f66083c8030384020070b2030141d007281041415041006482810031035660900c0700e0443c610814000f81012418a014440c03c011070750081440741e460040000c620036045941c54120038411100524996211070b42c406c00034503070740c12088025084c0030401c00016060401040d80381008c642513030126614200300070a81c8039942014400e100c080f01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 302960197 1250 302958947 302958973
    0x60e03030d0509010e1506030d090605121506070c0e01060903030c080a03061a030f091207031b14030703090e010302130b0102010b2701091103190209061c0509060405 73
    0x10000381c103c240b05002050700e8441c40003081c03401441400c20145050200c0500c41d00b460200600c59404071541050103e080c9090b901901a005411a655402e03280c08002182c800a0f08009020841300a2525444008605041c101441b0500562403e0000e603400030800500842c8400d08482d4103030340d244a0325803d40d481401503004200400207141d21400c010030040001001050000e254009080d101e16006005206a2030050210401703904031b103208400d038030102c20441d01e4403601740c24484d0040061030302c0d02038040c1400c9006849a07005000440b00041d0100050103018080c1e130350041c1a5455400c4804645401c4c80000e40c02081c000410021000d10381040c40c00100500001170210303058808640c009444507600c08117502003803200c0e0102552040d8282c0500803050301005100300e440702100d0b0a00c000703424101c20010162406107a01025012100302140c05001103131214050305000c03408031544040203205070308080c0000c3d480000058818030864010005040c08208a1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 302961447 1250 302960197 302960201
    0x7051507170a05070510111b0708060901060807080d0509040c030b0d2f060a180909061409031303020f010c0206160302120307090b03270610060e03030d 67
    0x2400700d0380e50000ea501c08014040c9040074106102941c0c0f0380e10756505a914180d81806100507285200e0b616001d030310a8080792000588040b007403808040322000d12a00c80c5030340b42c00c540b580104128450101045004c4406401003022a181d150441e103010352100e040c03c1d12981d044034410001001444901d05915003170b0841c000b030340c0030f60600040780c0a82c400840c0c0f4038003007990282c9921180036040c0c1c240d9a07031001e10070341040d001c0b0008580c1d03000400c001400382c031907480c100e000c028140030a400c9251000d011440100104031042146504a140010150401014400c0a203c1c4480014246e002c04030071035407461000160080c038203045900300007208005d010000e040111a0030703164016100d0400400b40360741c048501d401d28080350715000349800f0045407001c0c1120010300070300c000c10340c102c81c050090b644480c590940300c0d514a80341c00019000b4084441441c0700b0100d2070005c244000c07031040e000c0c0c0e00007600220f03c69141c01041d50a406c8100300d00d5010750040104421401040d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 302962697 1250 302961447 302961457
    0x60f05071112010c0801050616060504030e060a172203110309060403080702040614100309170d1a1005090d08041502030a12090c050d141e0f070515 65
    0x60302007100410a03810100c0c01d5840d07a080710010702d80d96140c20340c0300c1c0e5070882249401801c7c1181c50700d191078034866002c000d865107584001c1115459101040030103015200f50340000c000500841c0c0c6459400000030300e02c0107842c499448020024003c5280d005a482078002c00032a220003200306a081c0e41da040710007000e560900c2003640418030070300704540d480c240108000d5008205150302c41c0e04c1401003100300d5542d94030591a01c000d0609134411a101c840d0801c15000071402c00240c40c00c21820b000950b9150401d90811031400081c1c500e5000b02035610034801a031482600e0410f1089040512680100040300c000105405110005252912103c40702045214a07211418688d030758140068000c8407800042c096040800c158580540c132540c540707281942d0741c000f80070308102a160701c08240d2450007200d0040d4000740d10801031080489400100942e55005c940a054000750302d141c1e61429801e40c101d45000390f132041c034000304000825800760f44004019001c4191038000440e4150700c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 302963947 1250 302962697 302962703
    0xb212a030a090c06020d0e09040c050d030909180b0609190e070b030103080a1107150309060b100f021005060a061808032206031503030311130914060a060f0507 70
    0x26041c4010000e00c01c2c00b1198014135803030b002400d0407101c61001404c0c40700007049036800f0b01c1c0082c0400000c40e40c03052040003111401d1b1001c00702c0c031140c2d080c100e0350480a0341000c0c07031240c1402d40c040b0b02c0c00703143c01240c1c2c5128000c0300e0500e1541c0b940000c10155190681c0c0e580da0300c0c4da000c20803400f084250360040280166000803520f41d241d4a400003811a0001d9005a858010105480e68010340010071031074640702d000e01406400e410682940382d0042c840f00244201a0b0341d00130750701041602d80c403130250983c0090512140c0c1d40581030003000d950780d0405c0207005005007260b28401c00c05a00a82d8041d41005002220440c06d14808a4003030640d00002c442c4402000ca00050001061000380f0b031206d103070750440907002518807000400581d6035011000b01403800c80000e1900d001d615070001038030351514010442030081803540410340280ea114842003070581c00d00146051240c0d00516010b848190040d4550341ca1004004d2140d181c0d1080001180d550a045528140b2400c01880c85601c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 302965197 1250 302963947 302963951
    0x315041b08010905010e0f03031006081b130305011808031603150306060f2c040503040513020304021305010b180301090b2d06010507020d020a0b212a030a 68
    0x394404030700d802d6454514054515035910a48011641c0702885000e5410150300300071861801c001c1100a004085031099004001c18040070408664064041942d17181181c2465621600c441a400030b41c000c0a1108444543ca040e41d0a109690f20340e541a011507005402a811075481c540301c009545509883d2004059440003008000c03020810640080c41c00740c00700050480c10f00302030303a40844d001d411191407861f00000c003658068040381031116107526040c6604213a02d8500d4180e20b14051600819400030381000c001000c1c200310b90145200364021606130f4080c6500242d9007085601c05c0c001c86401401c20132042c040c04220f001e4240a003400603000041d040e1a5071100c882a0000b41c50014a0342050b04000440d080c0000407084480441c0012014a080280002e0003520074032030700034090124410040c0c1950741d9a0001c0008091070b4401c0d640d5015401c10746948001c0001c3c51710320301038011010508841a00c2c0302c03100300038a00c086030912144408003880c000d410003040100065 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 302966447 1250 302965197 302965199
    0x110303070206030c04081b09040303090f080d0c02011107080406081f14040f0516180e010608240919020c01140a060503120a05070507230901050315041b 67
    0x20302e8160003544590a0b1800d800e446070b040440e41d03030510304500704110b04907152540d100140e03550340c1e000795000380e4903080010720303d9900c0c0340c04d00054000c817070050111380700410708805840031600b190b495055580c2c0200003000041c0426071039070252400207030001e001804280806ca001e6503030070350032a100e9581c55080c003142c0c00b240030260324542c11030070001c0240c003240710a40c00c05000303800380d04204440900072413400d8075400503d000b03410810410014181120326400381d4501c00380c00030b072002c490891055a11000c002c3c1144105070390085139901d16900e402240700d4030044405d2000e2001341003020540b90580c030704001008034110060982e900f0060480354002c24030030040012100a0003c1c01854805e1140b001c4400a502c924029080310780c064450130101c030222581d20356242000764803550103040043c41c0240b66003016103049544000c148404010300300c20305400b40b0446800c074841c0e8842061580390703400e07540794200b01c801035004200041e4001c1011210490300c040380110903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 302967697 1250 302966447 302966449
    0x1b03100308070303020703030c08090a081b030414120601210c05120607030605030a03050f070825210c020d0312110301090e070b030f0a090b0a050708011a071103030702 74
    0x1e68800c803811070109a002540318105501406004812040b03801c0c401c81c035141464449489001d0034038010000341c03001400d5059641e00e844a2907041050404907520b03980c55004c404140c01030010490f00c25003c10741d0783d6281480001c1d580b8181c0744000210074400030071406400040d040b00700f00300c800321090307400802e15480321104507202c40c7c0208010302035418a060080d0844403075400840c0240c004840000210b80c0103400c6425107454050300c2c55898190703051058950140c3e05102c0050411050489a00410760000d400703802c4c0924001c1c800d40101a0703014010940d600310a5001c140c43c0180c5c0409450b000c2070785080f1070701a05041a41d103141c038070058101c42e0602043c001c1d00c000400140029038a1f440350f1103502c913a4400405440c0e06103130542849010081a00c8085e1034a034000032003142130b5400034207141d130740700c14940711034100901041d0241000326140030014a2900000400c001e405502140d07400d80784091515125207501c890000204000c842034151004020708401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 302968947 1250 302967697 302967713
    0x60607020a15090332120f07020a05181b03010608010e13060612051b0105071520071a040206030601030914070305070e010b030c040b1c0c030506010f02061b031003 72
    0x11a1200c45d8101200c0904c00c50031030544005e682e01c00c0b9a0020188106c110004000c64896800c2070342c407151540d19900c0018400170564201e46c7c1c10116800900742203840b8045058060580111100c081901303803690f0304500d000034440c0780c00042c1807100412050704600a66600000040c01c41000c003030301c2d600d9481c180c4840c1d500020310001c1050360001402014800d030900d000310381d26000110071072000000d009001c2d0107000381500f43d00011146604001e60311290500d12440319880d0004040401c949003170b0002001940d03628a40f150b0b00e132207007101070300d0603204540c028800b41c11a190140118000c000c520011510700c80401c4e240310443c40204103440c0254400c03401000c84a040c55402c6000c00c6040e40965801c110504c02d000400c86182d041c1c83c16640f41d10741c03075501d030b403210644810340d0b0b4681b446800f0640d24150104040c558560007162240c0d00030303281c0e003002d83d006500c200c0c0c1d00d000441340545a030300c135103400e440d50040c070300700540d04a600c140804140903240c0e02c400710 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 302970197 1250 302968947 302968973
    0x1002031e0f0a0b1c1b050d3801060c0b0903190311070b090604020102010606050c0d050702040f020d05061903030e06090301060f080d03060b030103030e090714070c03050105060607020a150903 84
    0x15030480340800085e40c000742c010520713024290030358240c1810b0301a603032000d2040204c09000020980d440071080040306c812001e4586800041e41b801c1e4003541d40c2c400181c401130201340140c40c07080b22003000855000c000001c40b90166200d000040000c08654811001480d03a81c4142d03c071080d0070011140450030040c8a00c0c005e12042c80030307240700e00b020f20000e030031504290302941c2400400d1000c010f0700348022a00490044d060b09000c1e64650642c0b0004006007441480b1462091021034182903420095201c82d2141c14191905040494a01d94849202c1290f11004001480328a01000d241c00e00d00701806501c4001b40000c41c0d01034644501c4414400ca40e003012100d54003c2c6a400c00344c80c2e141c05010002c003440c01500e803641d41035440090280d0704814a150150042074040342c05a4410803808103050440c9856503100c1c0907510341864456581e12096605600301004180d007440c0c508112440c03903500400d00461607150583c1035000718422206030003401002c041c00000b0441e1001041 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 302971447 1250 302970197 302970203
    0x6010903021e130e061801060501270e0705030403020c0303030c0f0711061909091505091f12030212040e160c02041b08090705010917030c1002031e0f0a0b1c 69
    0x100706486c022112002c040c10700304541c00d03241c0c10a0b204100304c3e41c01c03c2040c00c0f003200480d1074000c8542580c0c1d614a04406d560300c9014a4400d090400000b00d81c80409180078901c81d6017a904201244030030103030799020a454060285508000e0b4400001c88075000b821403902c40c01040103d00703c072a000a500d038104441c10400e0010324800d503070040741d200440b038000e0486200d0401110018201c406040701c41ca000d803900a000c10720104095410b00b00b0040c0e45c600c84044041c018945605074482c40c03501044085015110700580085181406801e0340c056070740b80d06080602d0b5407050740b440d00d00c2901007105020305c2030010807440541c580e40034a003070030400f928a00307201c100d2560008114980c010314508981e00001000d2055a92000004007216688110020481c800380300c0d05081d0300c034010f1040a42c2c418842c000030140c0058005e1840b48000e8694085002e045001c4148640021a0807a0360501c0310f0000030780c1741003035902044d0381400c05006000e900b82e0800c10282a201004030035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 302972697 1250 302971447 302971453
    0x1a04030206011a0703050403141c02030c011104140409020a030f0f1104020c0a06020d1103040b1006050c15360607110703060c0e03120c010506010903021e130e 70
    0x61002c021260b242d0f0314003484040700180fa00e105510010070b180168040109140d010f045241020fa1082148109034050408642444484543d02940d0303030740001e1401960307500f031250704554041c414042d03d080751a012004129050054104002042c01003000c9038481100400440400c0d02c602c820745002d48500090181035049052071040301c0321515000780300e03600422440c132485901150201c12564002409078640c050741580341301a2184841c1c8d65a1841d01000300300c14001021000c502403255000700069050301d48404035104d02c80e8992201d5a5446107240320089002d00f02401c1e80548412100c00b0f41000d002d49042d07080c81103204800606110503021002820240440b5030400348a00b80840c592818031105900c4003c68400606501d13074071500101881c3c0a545001c0780399400038161020441000205840340e00011101001c641c0f8150002e086540104c5410043c4c9400803c21203040720503042007090000342006041d000000350381102c0c00c102c1240141e8402440302006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 302973947 1250 302972697 302972699
    0x160b030403140f090409050f10140708040b010303080403050f0408010f050f130f02180f0703050603121c2004030203010b0a0b040605180306040b06102a1a0403020601 73
    0x61401070b40d6a540d0050300c008110081004500000325a910f40d4107130f130b001c079185a06041031820808113011801142c01400842002c180c030300d41c07001035060507803503900c251038036038440c22588a0310854000341448490301c018000700e805590340c0c90744148240303011440d10700c0c0c8000c1c001207504164854501a91038410307400e052240c0e0b004050b48401da8613100e1005140440e09040c2c040c1d44100c01a103c0600c046d820301c20b64440e548108101c28142040302400d0510346c41003004614211070302c00c0000d2401011495901d804107500402d6014425450700304180b2044141c4589410340924640c141c1e1003100b09002841c26104292800c400d608554480c2c3c0385005050035074407840d404034402d15042c141405105d540c80b003501d055500038600300c0e4460543d140d071186544070b0584903030b03030601c15030082208200c200003040e40700d0304c0203641c8420350004100068811800008101501001d0280a8404403440d01351850fa1180160208031001c62040d210f1624a4000e54049c3c0060b080140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 302975197 1250 302973947 302973953
    0x405030a0f12080721020708030708010819053705030a030612020a090b0117041101170610110c04020f0a080121020f060c030d060905070903030804021002160b0304 72
    0x1401c2c1c4801100d0800d4096480d01340c0c3c0042901c010304a643d2000166582e200b820b0116950648090b10751102e50643e0301d0034203c00c040d02d024400d10800c0d4480c0301c1c0300150040c1851054401c0389aa92050060070310b058580d40c400212000d0b00380d582c81c0904034030a00e60f0400d43c031403506600a401000655918920000d00070141c83c400c0d00304000120f03600c0380102c0183c8030300c1e003960125071012000240410780b6500494902c140c00300c0c6c0e14205003000040c072090080c02441030301d403403009803207043c04482c8150012407042e800726403841d48048080d00d5a50b02c039004440c1e0a480040040594034007803091400503003242c0000303402006003140462031601c1e03e03400040c200d000d081002d003201c980386140301d840ca2810012240080c06030300000b49280054071a501568810180c44040c0c9890350098481c41004004034420001800e09280108486d94021600720040d80c0d0140d507424240e0b501c6130288403032044040c00740070451090741c1d4400042c10a600d8440042c0c41280e241e5603a90800342 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 302976447 1250 302975197 302975213
    0x5040c080f100f0b060a0509011d060304140102040b070c05040501080303041709030a0606030305123108070605040b1527060d080307090f1a07080f0405030a0f 70
    0x40c10200c055400700000c10714440002824420000004001207400d412120700d100141c0550351328a90019800300f25200e605d500f20003e80341040b82079a4144c00311810030070010480912481090b0011402c101150100d10000806081c0101c00000985480d66603403144600703501c1042c050705c7c06403c0aa05021500d424045c65005216441c0254194207090719a0481c50800b0194602011030000b0917000035102440603120b0180c0200082110960320b003000344c11580007200354101c650003100040c015404c07a81a00301d10001640c07421024103a40e0302c0600c00c203078940c0d50650b02c800003801600000f8009015003071140744504bc050340203007084844440c0e00b0b0003031903120744580c205000803003852110b003000000780d4800c0d1218a8058072000c001c0352803030031a5100504101c40000400040c19048801c0b00215010000e00d051615503540030380203154180384007040c44000c200050302c040361451016204d400e040c480402d140c41c1c1d03180d0001f86440041740b82240c01d421184010300502501c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 302977697 1250 302976447 302976449
    0x60b030a0f060e04120f022103091e100c02030d0203040c03050f030309060637150216330206040213050f0c0c0a0c091a060f0a080415090605040c 64
    0x6810783c0040d50601d0b5131561522040c0708800c004010090005010051082107400341c0f01b000d41c01c03045c00064000c03020b102658030464a60000d0701c02c400c0202e903842800c1c004c0c1c3d00310403840ca000c0c00300c004e002c811000207424a04200c804501c014000304001e0211440210b0096105c0c01480b0586e500c0d6240180c246a503051041580360014801c00c04010400300744503501180840b82d104c0b00d130340400101c569003413809144440711841b151000301c1c4184d44000342400e4815141108000c0908400308980e0f6241e45042d8101c0c4007100c440c10440d8a07480100c40551200c103c0e80e17110111020200c0ea2214050682d140e4010390041081c48150304001258107000d45001005000614140c2080d00500c50040c00020b44141d00149001c0300d0030050100008130390b0312640501040755100c1301e40019013403050380c03000c1c02c0208110b1860f0300d10300032048510318605501d001c0e04040a100c030545040c1c0c001001030740c00030000f04803100000c803180b0864000910804000403203092a00307220341840b100b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 302978947 1250 302977697 302977709
    0x70909060b210f1504020705010e070f0f05060417030403120e0108010f150804020f03010f090212010c02070909060603020909010c030b0301050c1b01020702040507020d0f030b090c0d060b030a0f06 86
    0x82500f40320005581141d150703480b18a04507100c045a407a4800700b4000d10403107030060100c0d40b0b0540b601d086c115011034964105d56404500c4003616841e0203460303107000e00d244202c2d82c3c084000c11040100740341005015884503020000c2d20f05050ba40d0f141c0c5150700018001400c00180f495440e0403841da00605003a02504010961400746820070191080405640c600042440345410024003155148032815945041c050024807081c0d044c050008040c0015a104038440d05d1400f0180751080e10520401141c0282a8000c00103503282c100c0c654001c1c00c03940010f88019440380004805611070254084c0909500000003440c2900c140300103040341c070013030485032003a41413509001840b8802c1041e2070b1b42c20182007410007a0890880700c1c600a1003080d0000b03400034284001c1020180d000f00703130100c0000c0f040e1a41400d4050141c011011641d49614240d440385000c40824009615040a445130000641c40010810380301d1200d100e540d00b08440038035541d62140411102c8851030b001e11401084 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 302980197 1250 302978947 302979007
    0x8061018020f04090f06091514090432120a021b0108010504020a05070c0b1207030207031b420204051003020c100606170105030a02090103020108070909060b 69
    0x480c0c415051003038403d9202c0e98003c035454846810a078404c0e80e0211000308040a82001414030003032081c070036600315104000312003108041c1401182002e51400344241d510000c00040b030040052101c1d6005d00c01110308081c03400050014456990810040d0390480c0407810311601e89502e183e0007403502d1070111001002c0112010303208401e9030003151080c1960402c59002d61502c050b200301300c4490141400181c00341841c2a40010445403d0b00200104880d6031240080b96503041003d905910402d40010001078154101150440c0b014120686c050708c605070078407c03510700400604030303100c0710706000500000a00b0045e20343d4009000380c0105411400d004c0d801d00c0d1400000681680704880c400c01459000200d5803103044c030601c040300542108100030001d250f12030400400d0b00c22000403820482c621b210001c03d030307031400207100744040c1da000300709164980c210780c01150010300241103602807025060002c0342c00300c60b034090035000d441034001898803400d58021594105d42c40240d4a42501 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 302981447 1250 302980197 302980207
    0x10050418030f0e01030b0a151403010b03150d0b0f15010903050c040e0a120221070b0a0c031808072a03060902030a0f210305070509040e01060806101802 67
    0x241c015011090084543c142105540c480300010303009000054080c0742e00c441c01c0400401d482812003007002e1031505e60b0755004003410b42054524800d110a01500243c06001d200240c814204c01c40108020b43d405002010004490341d01c0d84100c9000f910707407004111072130041004001220346000503e20091812010041c5140c85058a602c1d01c0000e890085894960003030502030200804110aa070041052404403074681000f922049000c4024440820b0b401001c00c42c1d04100050300d0080741c00404d080c1c100c4c0c40c0c0c2c00c80200207040d01d00c241800d03d6211040c50500c8100c0c08043c1c0b09403070058051a5070f605841c43d10003080d0556003501403041101a0003198000a4080e00d503080e00c0e03220000240382141800060f00d00400d1200003066002c00b03404103010026100100c04548001c013221000b0220100320950a440e1300b02d44c4600041c0c8240121081c03840e250b0405418072040d800009140e54507024280d05020301100c8000804400e05070400108540100c001e2400f03800320000c40c148 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 302982697 1250 302981447 302981453
    0x906090d021b190f0305060f0a140106051303020a27060f03080c010f020a03060503010e07080627010203010605090915130c03020c0d02070609060305100b0304050a05010510050418 79
    0x40144090b08a0148a440c1c240c10a050080b454200280c01115803c003201d42da41d25045075141001c540c0a211011aa0041140001c0c2c5000361501781813500485141e507800c0c001c08650310303040240108490303861040c0010141c0c1300c01c40144060321010040501c42410008121940181c1402c040e04a40c9004410095501410016416a940304050a0340c88070381171140d40c050840600350741e2006100241d4803100a8150307000c0760407114164003d04c080c21200907802c2e214003032880f54904540290340001c258140704540c1e82d0703000088070013540442588502c0c450032600700f41c004201064000a4404041c940301210b6940304d440c111580240350b0400c80498140d44124a0207a1856181c00c1c0c50110640640c040d580300702403d030304451480c000d81070029a159421301c546008210795810116a480c07103030091510603600c06450072007051810102c0d51581d03000078019a05402900a5134000035403c1c01a03a024500e42900d20f5116030510080108a03003240400502d00a9007119440c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 302983947 1250 302982697 302982733
    0x315211c0806031c05070c141c03021506011103040306090201030b060c190311060708010e0c0901140c120403030c020310020c06060d1e050102030a050702010b0d0f08120906090d02 79
    0x124100300c02c44d00d10114950909542c98060940e008010b0b42d42d21901060340704200c40081c503400c104036200080040b030000c2002c004e04040ca0f000c0d0040c1c01100d82c0300c000140386880d42d0b81004e010300d841050320084800285c2183c0250f0002c84a50351a10b50361015903030f05001c2c20000d034108039462480c2c07480748620507a03200c1c4104843c0002c0e811140254003418058550020030360454420b4a0341da2400c0b000c010301c511424000c0b240d80540c2a4081181041c0c0d20055902208041c4c45000300660600c0300070000c1c0d044011810014407074130b5004860400e9840c00b400044d4030a85640d48000e40f50320406003041c9002da041d2869902c10701801003500300014042c0c0c1c2001d4156003038141000c0500741182d9481030300b111010b04040784001c1000b000b005500a40c1b01d8210040100000d450f05d8000700d09803400c607450320703501442541030070740440e4400481d8100d852203030300128980180c6891350b00285800300c582074910340052007000100b02c4103001d401a111120b1014085569203000d49100c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 302985197 1250 302983947 302983963
    0x7091104060f030207021e04050f090a1e140604030e041806020d0e030a0210060f03020904030f02010b0310020d0c080f0a090201120e0106150906050315211c080603 72
    0x400075400c0500300d415019134101d50b03960742c0103000308032005400d81400302d541c403203040711034007a41c940800a0200c08500d131450b4010322040019001c1c00115441e010f811050507130030451007103101040070000540d058241e0440d020458040c05042c9068103028043e0102d103402140070701c0c1032010303100303858001803117582c40a54050b80c010b858940404418009044518489140d4400020500d02c05500040c01d042c80b000030101c240003154032445105110411803100a40180884020800081c0030f1150324250b07d04520001840e540c0400000b85801904031030310781c81a1b400901032602402ea4001e0700c4044010b400c0c0031803a42000e0110000c42e03a001030410804641e00c50001d41160b04c00c401850500540070001c0c04201500b5001e180200b80c0c1e0311920103041010300c3c80c0b031001030050080c44110f904984485042d030740d50810358120002109041c0c0d0f441049485c4000310010100c841c15240321190b4000d1052100c0070080c0176a000707001e20703444140100e810410089550004000ca = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 302986447 1250 302985197 302985209
    0xb120115050909010b040f020913020c07050105031f1202131404060b15040308090406060f0c060f0e03030717130507030f0507050a0b070204050609070813020f060c030c07091104 78
    0x149440c3c0c1d42142460040c01018030080e030090902d11091444101c9030084c0c5508101142c0c115082a0030407800d0b0301700c2c402c41446e0b0229800041080040c0c1d0f01800296500500b240000e00c8941490004042240f038203400c00b030040b8030b100c6404070039420700c5002e9106140d1100000c001c01c245030403d00d090510b0003400181031603101d0754076001645074450003001001c00301c541180c40ba502c924010410360004203405000d94a01000002c140707101c1c10280c8003210080d00e444400001c15142e05000d01009004102c43da82c988014000d034050400095110340c0d90340c4e95007000241c005106010712034001d000a0754440160721600c0c0411004644041125444404014500b1580c03900c2810542294080c0ba070080314124001074001000d801440c4051007140e0800c960341d10744040050142082d20304000196a078070001d0342d80d0122048a0311024002094950708014081c0003890550000f50100865000440e114007030071800c01c0380344064200d01106124000da10800e540c1c0e14041d500c101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 302987697 1250 302986447 302986459
    0x608040b07050c070e04050d0513060c05120324041b11070f0f0e0708040f0602030414030a030c03050112030f120b0406120b070306030b06120c130b12011505 69
    0xc981d5050041040b5800c48a0600940360b1240d0780b0b0600c0d0f90f45000c101ea040d00c0d42c4c010080400c1d5524860760403074888482d18107a0703200302030070603000312080b0309141803c031040d1107000480c0300080400c070061442045001e65200441c014288154040d4a031061814012030801d128100340c10800380c8240c0c201c08103444c0160607802c080902c0341c0b800301144d000304035a501c0300c040403480c69206101c0e1419206220b00090454950440440c4e45040c1102d02400c01c0348002403400014000c0e400a60b003050040c0660071404500c8182c00d421503120010380d82c082540c442070084050b8143c0034090040105420005544000b40c83c00b800440c0b10443c801c00f009070954080d000d12181d0343c800c4402c00400f6008010813515000a0118949220b100360b86c1c43c0341400005840c244240905025244d208009848603103951042c011071013101860390b201c03809407417030114881d20f900384010941c0c20410070101e0740e0090702091029494003012604078a9042454107141001d150050031704962094940d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 302988947 1250 302987697 302987701
    0x1103010c0e1c0b10060f141b010e060106050309071d0601050702010903081603140901090306020c0a02120304030b01120519030c081309050106020a1104090c120c0e100608040b 77
    0x40e00402e4110390000620b62248103051101141c801c0358401d041c1da00a0f2100441c0300002ca81c19074814100342040c1d600501c0c20450721400c01c0d54400030600e106a841c0000c55010884c0c852075040520036003001002403004000c010101d10300700f0110340100441032100c0704200d10701c407401c0c01500005000c3c80c1441000141c8900310392107040c0420045411120068840d03000f08101402c1b4403401000313a0002d414030000c6500701812104540041105844143d8400d00d15615134019400c0b2001b48090b502911945401603218091074001c60459034002d50b039910300f0752400074410101030300942242c0f00300e0500500012000a043d611181802c0e6030402c0205807440c00302c40604c0c58000083c0070341c801180c0c2c500307800b1000555109480104c141071102e0307078a0f800c04a80e034451241002d0100406201102200d050075404082c2e107500481c207407034216446450783c016120241e481214274514035001002000084448c2e142c004111201885549142c4080207044110140014080080c2d10340 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 302990197 1250 302988947 302988979
    0x9060e060f06070b090c090f011d0a0b04110706061202091819120207050319031215061106011a0702060c0c130b1203030c0f0a030e10091103010c0e 65
    0x4140c0b860f0702d6022042c0d00c81c40c54a44074494454602c01640c5004600c6400850038a40a00b00e00d02c3c1a100e06501c000030255094442102c004d00c00b801000d01d20350380707140c41c00070340c0c44900488001d4400140b900c0d55404003460101c0848040c0d0748410304480020480c080142e9521401542200c0410100119984144202400c1a64003070140c43c09610050401e4100808100115803400b0550291100285e0700e006042e103400d0102c03840b401580c804107030200024025981d0011801c2d092000254121458194512121441d005a004590359000b05140b5500c2003005034007400069440d500707080c0318054400103502480c0b0b4003c0c4145404a04003008107010045543c0a480003030446a01c15230082c0004010200e03454828020060000d07080940341001003124062400d0001051501032030002c1c1240d03640115074003800b010b4680410241413007003089401c14192216900090903038286c40c2c44140c80300344515081c0030303034100011480443e801c03442c92200060282c84601400341855 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 302991447 1250 302990197 302990209
    0x310060c0515010306140603340512061821090d1b05012714060d0e03030a0501080d1e050c01050c031f1a0a09170109020a09060e060f 59
    0x240b0b000c103040312481c1c0004180002500000300c5042e00103c6492143c503040140340d01c498020302510b043d400c0c2241003080b0424821544041e10200b0804034151320303101c070009080c0400d2070180e4500c0380e00030f10a000c03028034141191942c542d403240042c500e101d8801c12200880149500c0003261541c0800e6000e11500da0282515140e40d02541c4001070b1000340c14100742090050003031030f001600d04e41280c13004500e2221440480c94142c3c0d442140140b07815081400c0d4031a9004072a0841020301030312070741130024018003103001c5c030003405191246411400c1d0001c41d24144e000e00069404030403800741654002811030030baa200f58801c0703008031002c00025074203442210501c900a41c81d010400140c007034220061409128940f140010400d40c00b4840c140d00c1243d4080d0288410524410300c0f0490300d0760004103d9054181000c1d86641c0d903814102d840080d80140703410059440b07007489811807410000040c00f800c940f07030701001341901f00320504294540c0200018040e2076050400c0d4482d5980e4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 302992697 1250 302991447 302991463
    0x20601060806190e13050609070b030c130803030c0316080613050907050312030105030d0302040503193e01111f0603060c0203251109100305011a12030310060c05 71
    0x1038444d0501900f08050392181400942c141900c1c0341c02040d0206a50910104600d0103c640d048030310340c11520b941c813070104c05501084888101c80d007039000000745113070180042c5200d04405405c694491400c800c2070b041c0d1102d04080ca008010100042086a030b8800300c0c07980078001c07044400503450f0707240f107049460402160040e90b4144202c80796207031582500d200440c103a0748181c045d1801034031601015030607030142c0c0c000c550341600082c8011100c1300805200702c0840d401599103440c2c10380b00c1212201c2e8882d0058003819a61405400503801c0d40659070090b00480c070a01e40b8040c4d2802e85044030303469848100360604000b429118642440e8000e801c40b07006540c00500030410141d8001d00656207500c2460340350322020a80c1e2409075581145001060764680026140150030490f0040100e00e610003006a54100701550010010031001d02c9211210240d601840c001034036102c0c10070007040080305801d40203620402c00c215500700c500590300f003116558101948410301c01c0c50f10030300381001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 302993947 1250 302992697 302992709
    0x71202120f04030c09020c150c090d0b0601030c1110090206120703140a0e06040305090117010303020c032808090604031202010f0b04090c1701020405060d050702060702060106080619 80
    0x3010a011840741104002030044a100e04c007015942d41c2c1c0c1c0d50254083e4042c3c8040c10b6500d4103d0900b6940c203964544000354090045402986469080740000ea18114005020398550000100b00300700c55030140320b19000701c0c145080034489214585440781d501d1015452104106417100c0028046450300c0c802d0f102f20203100c600744034851901e0b0000800818050400700180341d81d103004030303920b5403551140b4001683c9200180c00c041d92261810345075944509916410401000010752120304084999406140301e503001d01000c180840405150000c0004503000c200065006090001e001d0490620029840612680c95100c140c0010b10180929840a0301086140b81112802c90741984280554685204200b00d800c8000c42408111001494000d0040e035035240c01b070000d410101d83c01d0719140381080016241944030000b08a6503044841440c0b2031545030303020300007030303c2d014821594800c1e07113440105200c0d850801c0c01800340f040642442d000e048a8180e82d191112000703d40b9014040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 302995197 1250 302993947 302993983
    0x1050607020916170406022a100c050415110d0e030307061d07030501090506130b0f0a02190503041106271309030e01020d02030315120c04180b010b030c071202 70
    0x782501b8403a0113940600010408003850300c280901c20008104061007a160000c001e10102c403044800d48020030081d01c4030800d00c14148000600c0c6480450503601d05903190343c8440310300c0203101000386410050300c4c07a0024070180007440c841da03480003c16603640300e810804c080785052640503071004031a8400f0801900b806204000700510005402c04442a48504201c4240340c1c2c071803054180452522800504031122039010034000d00c0d03510401c5030000012100103240c0024070301d0003004e20446040c2c00c1d020030300c040204010300060210742c04208034241c3d400c2d40b030b00302000041c81080740c1d00c0b404154580000c1d004000180c8424030400825400801d0800012201d03080c050054008654941c1c01071142080b818000c0d0b201000707071fa00a14140c81d05d0304e07120740010b08015a4030711004840445201300020085650f81c0ea00a45c10340c288114415200c2c1c50143c10507801e03003841600020200711041050041001c1941c0032a0b02154002c207070101d509142c3c03901241010b20080c22540011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 302996447 1250 302995197 302995201
    0x60a031e0207051e03031023040c210b09040b1009060f03020f030c010801120302010906110310090b0d03030209040e0a0b0703060e010f1a040911040e0105060702091617 74
    0x110000e120712142c4841304d454015515481c0d2403d80d24442159203c15442e04058200003500c800d45c0d0118080000969400c0f0000343d02010404444c4907403d448002143c0d6602420f0303e64500b10648542e103000b0000f80141c01030b00c400f0a071011000b0307100070202100c15000a4003000040328410240c03020358400d000380c50b999145c114211006001c02d83c401c00000c1d0061880e46000035401550303100685480d47c503a171903c1c00c0b1000003144041c1c2902595205d505440006202d8442c40030340c1034011507a20380301e082c0040310000840c01d5401c0380c0007a61070300f0b8050299594074562500d44580c1403a0140e034440c2030101280c040d040714030408000303100b503c01d0f071420401c40e210321610901d6180d40c1000070b590303142c1d41c83c03030104428030400768402c140d03200520041c040d0780348140034800e182d1411440c0030f90301c0345418111001800311000e40039000c00d042c0008c115001c0e00341d0040c00104c130345604280850300050f004010203021042b4a2540d003031810040c034026180e2144a801e5500b400c03100d4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 302997697 1250 302996447 302996453
    0x30c010203060f090f040201141b0a03020f070303050d090305120f18070f031106070b180616021c11010213050f1503070f0c080319060b09060a031e0207 67
    0x41d40066501920aa5180b034040c551070410b070b0562449004445800c10350784d1a503030015114101c01030074102e8592000c100c030281c510509020641d004041344010218958039081c004d042ca2000c8042e000190000300302080826800820340310b42041a110015400d01c0340c0c0b50a0b0b4803480380f01100c1c0c01001413030741000300f18079002d0002482600c0c580b00d02031104c0d0407100083d07100c230038a0141e06400c00d00000305101041c24514001401080604402c0c540074031600c840c162044101d0320030b20702000c28a54400120303420b11a06400c03500180304045805000e550181d240c01e0440380010748440751a00d0b044090740f26090302401030705031000855480b13420b9021010360881d50302915000d10001500a0500c3c100582205070342080c5100c903504507100d40204962003c8014030700400c02c104104003a000c141031000560041040e1860038240b078021140c0e01c0d0039100d0503480f244002c0310600c02c0c210b00e42c81d000c084032042c00003403800160900c490036078104803d05000045450610200e880810 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 302998947 1250 302997697 302997701
    0x8030403030b1807210b0a06030f060503011125020f0126090a1403040605031b0910110d02010b090105220204060315120c030b04031b030810050102070f03080c030c030c01 75
    0x1c0f40282220b00b80a109030117500005584580c0b280c2a00082038540801415101c2c0d80300382d4441d400718102280b06555503001900f5201019460107400500181820341c6e034201003044540440b041c410800c00c40d210790005025020f000140d030381440f908140205900e07481c06001d114191065005049034148200303540c0c0e4590301403808407861285150750350810f24001094500301c800b02c1c3e9525195603140441c03c0300c5030300f0520004561000c01e21200c10701c1e503128001664107040d103913503001044240c850324a2409810114038829a45002401540d90310342d0701505042d540250b4540c0440440d008200f00c01c014842003410359584081004100b442e0b06400098072460904401c04245866044408603442074150040075051200d40c01c00019003548051540305000f03003010181c404a041007029280b41014048001031808010004081034050440340585001e200800c091030070862040081e40684c00051b05040c808140022491400c01c211580c1c401f2000c152500c400a500503540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 303000197 1250 302998947 302998967
    0xe030105071817071203110111030604060b12010312020f010e0c0108010b042103120c030509011503030212032a0d0501050409020d0215130f0504050f0408030403030b1807 75
    0x44603a1030074030004200e2200c070000074512043c02c01a24005107048408810505109000c900b030040420704450355400a02ca030340100b118140006640e450000104801c032000c5420480d4100403d1100460074841220181c0c10359501c600200b0f00d4070342d140c42c141c0c645040c4946810b141d600f0082d803809880070100c1c0c40824100e00380c80e400910307602c034400308500c1c1c0294007407060207031702d034440713030608410081000c15849019042c0307070707a01014580030300f0203449050400401103601c403c00d01c80101402d00c28002c201c00356a0b0045e005c642103a038000d440f07030400a017500307444401002040c1000214480400c050304250400c1000800410742840907030001c0c04140746540ca864000521070a040c0a06079600c0e42c0140480c00d4011075600f001503440c24424621400d4109000080700980d19540c02405820891100505286004100300603204014810009a4868002e02000448540560746c00962504021807294624800b26598481c0410080c004080c44003d00501e1504460455 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 303001447 1250 303000197 303000227
    0x1a1b0d090203150f1308120a090507050604060c030507080f0714060702060103030c12090e10080105100b040e091906020703200706050904020d060b03060a06030506030c060a0e03010507 81
    0x401d02e43d0304460624400404070740e000c0322182440006024110101d48101609224140d03a0741003a10052158400d20030448a0380300941c0d1b6010b00c00e050003410840400240000c940d6070b0706d41410700c20300818218041f02e005083c090045030760020410303d40c0548488505911a0903162625030404000031650030002c280d880c003030400030070784d0b5901c00308034541a40d400d91622407031844035568140c600c201c0000345004120808070040f0303915180007155270048a15a41c200c1c401030810340d02c1400c586000d8200b42155079000d00c10003003640c046054504948840000b100030b0340d15094144d040000a203004034080003a00168000c010207035002d072650380e0180c3c1e5081c040100b221003120311080134aa03201c200b544405420030070b0a209800421007030318007610240c14194442d9604003542d14035000060180008402c00c41c4038148600e901000317214500c2c040c0701900f49040826103c0701004070242c0200c1c000182d242d580b5015600032140c801e0050f0003003000340740800c0300500e402840c6100d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 303002697 1250 303001447 303001453
    0x40b030c090109330c0c080609010c030501140f030a170403140a02090a0f110412060b0105040609030b04022704020103061509050904050c150903010501121a1b0d090203 74
    0x1055603820444140b20045130000032810981d090700b849001c1044000ca644104026607044800003524180c0400c001c11758034000745450f040c0010640d00355481486010308040c40d0400420031119900a082e0b800d01d803e03144068540d00c2140802c4c1010300da49e101500d28002d01441074206412100200110390281d500aa190501142900d4482041c0c2001950041c100c10225103100d8842d07000b040482e003903003000101850321040140e0385410070b40c0141c0026012483c810140b01e00f6026078800c288091a140785420f0a044018001c100746001c0600803400510004045455000e020142030b41910134401001030034000641078283c040300d080b4000303428002c00047d48001062844180300c11a12035201841c1004180f000045004205561510500c403052402d9150403900303201c400e14450303000b42d481c030605060500350b500c1a8020405540002031b0100030801c01da980d400b03001484920b421254a07185c035940b0443ca04480a0703c8203400c001031101901c269a446148064425030507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 303003947 1250 303002697 303002699
    0xc14031312081b010e12090a050d1211030d020f090102100c050f0309100e0307030201060b030c07111504081b0603160c030c080301060f020f01051504020a0203040b030c090109 77
    0x21071441041850801050b200003405803000240c2e0041d41e048102d95020000070f450401c0314119898214001b04010318003400181362102c0c0d0826205000142205660b9103c0885045d5212100031701e654940c2c41c10018017100700d0581d403900344121940d801d1903500564031501051801e1140d81e11140d4868054400c081e044184a50280a001c0707503c0c00039110b240c240700c14122003e07890b500007405c4895a008001c02807000400a00c140c440d03600701d8030011600c0750400c0c074010b821145190402c280b480403d0080200c80f028441c100c82c49030f40d20103d1030100c200401c010840f401d664410448100b8400300d000700382072100140312181070142031465031000700e2480500681e448103803803005c01680200003007000c09001b041c0e40c240c102e104c0d29058420001589800c00ca581082c1c00410020303a43d4040c1c03010300c0790304010440f00111404000c00440c100100c01180c5602050720450281e900803d00b522500d0007030042c0c400414510418039a28940910403d10741c1c3e104011003400302e211498 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 303005197 1250 303003947 303003959
    0x1213050a060807080a06060e120102160609050f0714040209040b0d060509010f020415080c0d06120b090d020a030e2409030f0d0207030f06060902070f05060718030809010c140313 78
    0x415040703c00c1d5458009922300035905004130701c1500070880c1c09540d000c01040d0055418443d1480d0200d020b07000000e45503030344e0b00d801401e001d881100801240c1c00210240b00d4504040202c40942801f1140183d031001c07054089809805030020242d44000080032a00500c003d54000a105510b000d0080210010001c491803ca003c1e500482c1f00b400188040302e64000e008103000b6400c035424012072400d003201600400c06803042500302802503004d0f844038208100c1c6a10315141c0019299002c4d21940c0042c550095031210342040240030842c00241a0300f01da10b85550683c40d034400c03d5100c100c0c0c114603000c10341311603001c589418000e21503d540302c0c0c012400840c0061a40a02c0d42c003034002d15107541c841c58400309a940099800b0b0f1b03a11000010120814030003401c0ca07a128010b4460244800c0c1495420040000c205c4020703c0b10840c0c1249441a0703161095040d654050407054499081e040120342003450388000a040005e0f921100c52b90803000406816020030101075890125100c42d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 303006447 1250 303005197 303005201
    0x25090c080402010912150203090c030a0609030806010e06090f0a0512010207050c010c02013905061603060b040302060c0109081b0c0a0f15140310090e0a02031213050a060807080a 78
    0x401070440d106c3d192036000920a55002141c0110b41c0d60200c404120f04980042d04107400140c003140c160f903866103d80c00b015003000d4003584c404001d08241c040036908038049680f078443c0f2000c49204010f00c02c0c1142040e5509903170000604000340801d11544000b403004c90007540240d505035461f1084042c001d109600c00d10790b40080990694032221964031300013a2003845200d805c0140b03040c42c079090308061540000d074268841107014074004e040b82c0c280300d00c2d91003040c01c5d10008141014144041401314020840032039003120f80c1a07a00717a995044041c1c0841c01800c180400410031130707001800c9180901e6510765a40c00101401c03e5801400703070341d030400501e50401c0c03145681e000c0303001c00100300384c90610100380711020090800940484514550607802da00841e130076036050060b0b03a01031200409501c50341d016101400d005018403080c0e0f030002591516020040c09040318001003003944522042521002440d02070200e4510503203806003d000780c401114564002001100069842c00e498 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 303007697 1250 303006447 303006479
    0xb0406181a0f010c14070e0703050115020705031b0105070602030907180b0a150509120708010e1603020f010c0c08061905040b0103080f1b0d110304060225090c0804020109 75
    0x58680c2c130a1080d003640c03003515006200c038001d4181e0042c007400003500c0d801c010107207104849a68000400c0d604195541a0a8404d0545442198046001401151000074400e00c2d9140c590b880315032800c42060048030540b05100c0000c00d114000b0042c0211150300203005e0080d540849034050903403842c0c0002c42d00301c428980840d0f9000170000000c01c9a41500100c4580ea1020340c0b84c2145040516004030300e82500c00905c0c1c9485500c407001c00c12188900b032150300b4a038900342e80500740086150b8a988441e41d0b441c040a88078800c04102c01c141e81c3e004a264102c4150301855641d00035a032a03201c81c2e1030742e600700d9001b080001084210384100140d48a00f03445540c0c00718202503d6403c5460790002a0840303c601030041c001000f60403a41250030740d0020f00c035510b17100100041b828040004241040720005001c06a2050105014058021a2102c5a003400c850000a84d021141a002c454021640480d08842c54a1301114030030f68400303100c0344224003c0e00c60755070171aa034801000d104141 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 303008947 1250 303007697 303007699
    0x70611010b0d0c09060608040c0504110d05041401180c03060203060303190804060c0801030f110411070c03150203010b030c0a0905041109010305010b0c0c09090a05010608030a11150a0b0406181a0f 86
    0xc0b2103044c0003a00d420f511503010800480c0300f00d41094dc80d114140d044950640b800e030750301501303030403000078041e82400b5428001200f5601d0180b00541aa104061405103000041145030007000107031658400b00207440650000010f02001c2410b011000790042406803015a80107060030440240c16002d115039038101e039403041403403c000603281c0711094444242c0022390350181d20741e1403503441522240c016044690149410045540c6541b911501f0396030030a45c3c20b1501d0780103100400900c200c5409484e4405001c1c1d001656490325140c0072119956541c010300d40c440e10b00640d103400d0301d0908001e04640301c0c013030f201000a640c8030f000516284c0290036140445500400c00501c25007004017540350040a46021a0380e1111075a0780c20f402d44232241c1000c01c0651000c24071002c07141e03009401c11005c80840c00a004141042036455004d03020050025542c00e032124601c03d199110783c2d12600040c4241c03d03200d420348800c0b40841028100700b00d110318290080c00019803080c60035131805182e01030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 303010197 1250 303008947 303008963
    0xa02010912050a02091905090607022a042d200d020702032b0503010e16020f06090102030105040b030708031210090e01021b0d02070611010b0d0c0906060804 69
    0x4640a4054102010707480e0031a150b02821002e040161510a14240607403191003a02c6181d000c103404003070890300700030440f040c0c541c400002e00c2101074001c01c040a000c51032020b51111b400d10711071480f0207240c113900a41d800503e45003441d0b0641c051a030400c94081680b40481c0e021480c410600400c0e107402001c04400c500030324a209042c40306a000802000316050000b6040110030f0b0002420160100b40a507400500480c001c1e01c84040c81d40c0800800c0183d040148c115414110b15021483c0e00a18104003400d130043c4d2040c40c03074003c100f0403860849805c00c4030302903c0d00f010010301035042071142038007444c1800000030346898049102811350f440000110708248103404030741b0f0507450107841140700c0c080c52000456485140d016a810706803140d400540d0b203c1d050005246040000e0401c0190b5402c071091805060b540858400304030b8680380340880340d40d03ca5030310442c0101b0b055111280e1101381074222200708100c150181e000c6071802c0b5400c00880381d680c0d0301a605000d04642c000d08000d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 303011447 1250 303010197 303010199
    0x506070c123f060305060702060c07120f2d1115060f01110a0b06090c030c070201030b06040503011d060106030b090c0c0109020a090e1b15070f052d0a020109 69
    0x11102c82c1ca65084038007180e800d14010401c0d4480034080701d209800c1540e09400c401d0411250a804221480c1c2080d400312a86203072902944074643c1d03144004400c0401c0050078810b02018600c140c000340302603045400520b90004130f552034a102e00322818540d1000c40c02c4514020003200c000310340c160250100c1c29902000d0340c0c850007003106444041c0e14043c14030110080d1070140140c10000343c0010340c41864413500b1410118100800c040c001425030510802c2042002035500900c0180d40513280d0a00b0017003a0f021102c00001c9140c010781e0003481d0150300c0d21120010a00000740811070100f06e24043c0c4802c1e9881c3c94080f0256140e00038034540024500c404500c02e02014002012407001c94000000c007030f034181e8005031402c074055010303220403620350011b100a503406200c0500240c00d85910028102111030100301c1c2c507140809100614030f00072031040d041c81080340c0c8815038540d00c1804e443c40103201e42150f0340796407a40100104003801000580c02c0c00711000415920b40c64058480c40c00309 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 303012697 1250 303011447 303011507
    0xc011d010f0b030d0516020d1211010e0a030f030506040b0907091409060120210403020f0a0609141c03020a05150415091b15020d09030b0a0b010c0506070c12 69
    0x260030f0841c017241c01064005802010501c1410080040e5045607038113040c8101102c4ac10b82520110898604c06402c203d030100300088c6c002807812441201420041015034032040018001c0c00407600043e0800010410014800d910820f607100f560390444034101c4c81c3c000c200c01d00a0001044031450b0102c1c3d00720408102035250444120f540441d118104c9a0710b02c0181d01c0740b01818144d140d4190610004030b028800c610f000344a580444c5011303141c406400e8504070008092941d01d00c601d42504c9000e02d11401d4076120194103000102c000816640d00c505a0320f070080d6160066201030311b540c051600031107a60409140070781c1c00340d6008199004200c103a007030408002e181007442154210940000d10800b905080040340092111400482c1603d035035842c0a400d001c5409074401c10403d5004040c000503020309145600507041100000b108c0340d0900069901d444107a001804030700c02d40c070800c030015034031502c4c8000c00d501c21481003101a0f10b100e0250f96000f00b83c4003640c081c400350703c00c450705 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 303013947 1250 303012697 303012727
    0x52104030803040f0813060e01090602030315150403020307031131050c0d0e0c040f06050d08090103060b0d09060c0f1b0201140a020319080c0703050c011d010f0b030d05 74
    0x1301405007101520b80249040320500342d0400c2ea1100011803403041c0b100c1c07400e41e00984080002c0010703001071032551030140458600e02c421032042c188500d074207201c2451030640c8502600d01070743c3c0c09022100c4040c1c90b41440c04180302029403442c0300e000c0000c0084042007800050410300501e42c8131500004c80070104001c050b00000340042810350b024090310f0039041c82d500412002140c11409040700451400c2440f054880300d0365000c0003107041c22030070480c6444d80070b1078000745904240030310f860700303405c00c01280030346000d0f8010800410086401d15080d0903d60103a40c8003845440b08000c01c8203004810b40b00ca414501058000c10303d1418180d8141940800ca01c640d2481490840f401c000b20548070709154000414404c0182c2c008034844840c0f0540d0440552516440d0034601c004e89000310941e00d00d07108010000701004404110400e607403109411614640c41000f0156510142c03456100703000700300086000b0f0019042c00c284030820308011843c85980506651914a072000444910203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 303015197 1250 303013947 303013973
    0xc07032004092108070905011407080f0409062405030a090c121b05090601050c0709091505060f0a09020c0304090e010b1008070801062001060305210403080304 70
    0x40c480020300000100d0750321440b4142615105401c00b62141c4009031100341d401560a86000510107000d0500c0100e0380c03c030300c3d00000c8038003d103803200f4084030500998000d8002c83d200100400c00104246401400303020141c001c1d1115848200403a03681d41c050b001c2c107483da000000301000300076411101308074440d200031030f03000c0401e8202007500d02d9280d842c00201103040d40100d010340c1501d21030300c040000703c1700d03c6401c561800b4261600c1030301f444001460201c3c064840340c10f025000030700a84600050014500501c0c90680c2000341d40d0b200d0501c4403103109400c140e4842d003482c02c40005e0681c5018221441842d4019120300c42550900000b04002d5001078510112807200340000079140f131060007002c0300c1d24103040c000314200c4884401e00500380d605035610424052140b0401403000c1c0d00110031030444499280c41c604604190060010503d141c2c4104252542044004018803200080e00e034084200120071120181490300d6401c014003540c08000e008200810110f00840d80070f2503000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 303016447 1250 303015197 303015233
    0x105040b0d120f030608030c03250f050703020a06080f04030f05040b1305030601080706050706020304061b021b0a08070509070315140103051b0316091503060e06060c0703 75
    0x150200303041d440311182c0d00c5140c00560b00207500d9440242c3c4896243c0100070040c0980c070f00550501d408407541c41d40b64042d6442560004109001c808000e960398155003490326048555080c1204c507a003840c0c4c1d140e040b240420780c003c000101c40020b030306102c0e00700c903441100b505090b003120341c94641c1d00311031100810700741004215080c040868102c0130000202052440000105ca02a2516080c1030500710168040d000c030390441c0c0b00401c00543c00504882c6515404140141d4a0b030356450100000d0801a60001c01040510304004034141c001404e2103030241c1c240d40d41141c040d0b08a040120001c89402201190b0704188007c00c50b0b42400000580c00c09424100864018400d42c0305020804543d0f10090081d0f41d0220b00d003640d03581510915400424402d5642c0c0040801341016400d440301400d0081e0010401050001440c4200900c4020342881071003106018a0004000c002d40841d0040c4000100c03d90042030070b9103448000c640d052450100035000042c60354443c0302000c0c0401d5106 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 303017697 1250 303016447 303016459
    0x7050c0d27090203090c0a0b03040b0408120108010c0e040606020d0c050c0409080a0801060504140f1206090a1704120312061503060915230f1305010602060702060f0105040b 76
    0x42141c40841c8401c40003806903101e0042c0c591600c1d50380613180403c0f01003540d002e41e140403010b0140c1a100011254495081203480015032614546084035110780b10564003404154000466030242c1904406a500400d0b40d9a9100010b25000c000441d081c40c030500004d03a00941840004a026600d2005100d005806030341c5000113405c042001d8a1229604881005000407040740490f0041c0003107025044502c0c0107410141000402e02044100070a071610400d1800724207101940c403803004200070510801540c0e268140105525507035801a4000c480c00d800030402c8070003d00c05136060b50202c0d0055160103080110a4134241c8591908171600c00c04d060703d480f00401c0100441c41d02810303c0009a81c00200c8a18200e1003208661412440300c1e025042c1c0352041201032070110300d400385003040000200e440e5450200149807001c4420a094000070044529690106642e211034103c170015000e81e0101d030303504001280c60b41002c44440c420301c0d99000041c0030f90704041c1d000d01070020002d445 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 303018947 1250 303017697 303017747
    0x30f15010e01031503170910020316080c0f0703060506031902030303150d0b0103030c1104181203020d0e070f051903060b060d05042a0807050904081e04090507050c0d 73
    0x5001103030f8040300b55800006c0c82c00200d0342d015052016240b80c84401c40e201443c00c1074100b11908074550395001015102d504042405400f84000b0b001150b0112421401c40d00380d00e65038545040a40012284180b0900440144520304a040c0c072049161640c0103000e149155141c941e00c140034480c0345610b03034016039055030401c0003507010070641380032350300940300c1c00d090b08051300d48801590f100c180803600440c102550001400c185800718030380a940720010701c01d05694200214020702843c000c80c8002410004131300d035400c0340400c0b5502903c3c44060b20b000708540700c0003400740125161106246100155a0800101e58290300000d01104020140791504800700c0198050320300641d0107a40303901c14502880000c9500b20010480c03200781103900000310380f800603900d446034814880c0a01415403103000608000c00d04041f1056105803004409170b02c000c0749002c1c00780f60494050030b2901864800410100d03406181038070451401c440003003885280103c812180400f161140d03061202c0a0b001c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 303020197 1250 303018947 303018953
    0xe0a0b090a020904051b09010c05010213060e03010b04150e060126091510091d190308150a0303051e0a1115040c05120f0a030302030f15010e01031503 66
    0xc00c94020600d500c400340c0c440f80305004001c00c40301c02400c241c0180808105640c00700c107035038040e03d0b2000b1090908680700981414103a01901c248175042552000950000c110580c22284c02000b28005500030000e03061800e05010032a40c0039080c112940c0c0d155401009000c200391800c43d4440018549090411943c203e00c1402c1d00079171090980c1185604100040d494007007152511145500c032012005003404c0000c0d40140c2c0d035a000f070840c4a070301c44041c1c440d00815503541d01c94804406048604040400104418201c03046204400041c21480031a03191442c20203082031f419002007580202914540d0f0a60b420b91040b012aa080c0b480c01c140058205000000303405038a0141c0c813015603600b6036074061428008200e00d441d44488600d42804041880b011680e015558140e0351f07a10751041c400d0306030780341882c1e4039014045489103441c51401c00d07070705401450003030001c6001c034141511381c8030444040b40140c141403400551083c000030b08642c0702e5004410442a803003005103005840351 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 303021447 1250 303020197 303020209
    0xc1806030a020301180b011d0103060e090d090801060303210f05040809030c15040510090b03010807061b0201080c0f1b030430020114040801020a020a05070f0e010e0a0b 74
    0x4540d9414a40c2c0072004100d103841044100800306411601008444110800600b1152200b024010904900d20050f1b22907400380c3d00c50f1000e001ca00e01444c00340d14105618541d5a2985110750f00083e107010400505500305001c0c50090341c1d45612542100c4440140403000c040380711380c6890004c1d8440c51910f00c400414860b1a01942c09410220b94515001d01458580b100e000b0445009503102a07080ca1030b01040f2040e60282c4034111441e1208046603002100d1040094010b0301e00340d4000400040d040100050b0365044030f1640d01c8010201c0720766000c0b0140798048e82d001074041021100000c0300b0780070507401070140381c000e401e60608000a0f042840001c0c0303c040403801c515800000e050207071280c0c1000740080d85400d404e0001d41051020500764640ba0380e0300000303060108201d00d030181d48c080002541e0242c00c0d490003c54a8a5170b6410007540c03000c180e00152424040d051021421a40315080102501d0804650303080036441c199161265010003081c11358800d59401c0201050f560305 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 303022697 1250 303021447 303021451
    0x50d021605071a0a0e0d0203011e15050a0b070303111b0114060a08030d05041104020a0f110f1b030a06090804030b010510080402090901270c0b120c180603 68
    0xc0005080841c24031040f0040c4503025038034800b0b01641070105814407540000550035617032081c1c46100c0030918a2003c280500800f141008000344040b500307542c0300840d0f03440720a1482506a10050080ea40e2043c00585c0b01f01e030203101041c0b10100001c00120340203030045030150000035103c0d4035001542d010b42c06a45c0c04501c500e40c42c1c1e51550034204962a03c00c1401e0b40004003142d155000300d1030f02c1c4051b546ca1246880c040d6819444900184c24040b403621503200080e8080e109550b80c0003904001400454902e0200340400c074807221084503031600081c800001b400300f4000b8130428410b0702c1480b4200100030070b100d40c948500109400018075602a0001d41c030311075020340d5103460444ca0603000c0707035105070409030203100082d00866103e58061f01e4541c1098058070164401d03290001c0c0c0c2405000040b1030800c64503d181c5001c0203101c0c02c480c500ca01107004041c0c1c3c10415450300c400e40b005200b0015220b02025102e0081008092601300825040b5244600d4032142100180410304941003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 303023947 1250 303022697 303022703
    0x3070e180705040812040b09130605130506030d0c3518010906030b030303040b040f0506010f080f011a1009210c06080402030714180c0a0f090e07050d0216 68
    0xc0390070880b64904000e20b0071417000c3c102d101c500380360420034448036078001c00240a12401e0311102016000e24282c0c0090054035004d403840c076100c0590b03107218000d0714041ea0b1050092080001400300207210792100307541c036513000380082c840c81c035883c00c0301124000c0c070a0365071640303000b52a01c010207205e4070b0000c0052154a444603c1c03888490030002d0221086580400e09060a1028041d000c0e40c0c048122a4043e0b07000c000c4403540c2e211810103004119030000000c10a204442c0081098642c1040706000c6440403400c4074111052034209900744c4000341290340b0101803180845c541071800d04030514a1300400e1410191b0781da610111000c0749440342c0c803d84210a075030f6030310209001c0e152001902030005410491101e0601d940030039940c00701881075161000280b680c0d00170f150740b140760200c007601c5981d156080a003004040485154803201010000c0350741150b119a03414015041541150440d04802c4419510748800341c0b0607500042e185c100e030940c20018854921203541018481c240 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 303025197 1250 303023947 303023957
    0xe0114131d040c050d030f051305030a06060f0f050a14040905030d050411010c08190908030c01150e091903231b060123030106030206070803040b130803070e1807 71
    0x8107420180100e00f09070f00110f0082d1050180a00840d412505100d208082d518055a0322200d000d130b5006080c840d50012541801000d0024080c810b10382c10075000d40b400741c1c4c0c4031014555181c040d01c0b00c0f640a407240b10781281d0344490801462010080d490b0390000040c0c00812100c02d00c1c1c0d103490a41d07104e91141d640b4160784030148414441c50f0049441c90360300c2800c061036000c00c01c0c0c80782021400b818078801c400301c0114800c003416a200b2400200100501c0084a0703c44c180d1100d01406058825001008072100e08130010340051500340d024055072080016082c0301e042e42b0045d05841e241030000350300307100142c80e0605880110300d425008850040001c0c40e00d91f4a005540c03016004500c2d003841c1c069020500500000c00c201d00c1895000e59403040740d10986000c40301107405001a070b40065400440401c00c40240150900210720030b80c4a0300445003a940c620440844025038100090042136041c0002045140a061070f006484c4004001001c4100c01c503e00b0310114004441040000d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 303026447 1250 303025197 303025201
    0x20319050103050a060e0303060f0f0f03030406030b33070f170a0806090f061c06050a05070f020a050304051c15020901020d030b06030705030711011109100e0114131d 73
    0x88018403442d1b8501400c80045d41c034600340540003890607880c0c480b0303403403048840040481d0144c0c2c9011440038040d0015098076101c0c2c1c0e94820143c01400e640d07250034080c0001c00001005544500703040901c20743d0700a807034080380b022141c104045410040d000c94015406016003c080707075104404500f001c00b0f8103d8190b40307130b1094000405440014000c0b50040a5140510011107141e445242c1d005c0c0303040d610307900c0324603948910030003401c4240400b50926291105108802c5401e802c0309100f0a0b01d600c51502156410500300c0c0e40700312403a80900150418030091106240013003507035014440903080039008021907180c402800558031050b001081d0300041c80e0b645960180b048146c03242c011f0808001200501c001305480b4400201003800b00480040040e40325401780d0164051a140d00c0f0003000038283d2070303505034800c0d8031079040c480c0700e09082d10180c1500b030710500040d500680103a48480701c2c000744039510400760f00034a00041e5000c04082011880ca02030041c00c005194003030404407a18 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 303027697 1250 303026447 303026453
    0x110d1407090f09050601090b04020f03011e0803130905060a0305030c0d03050a02040b030a0c05120c07050106090203060303160c080a15050a050601020a380f01091a0103020319050103050a 82
    0x98051541c07400c1c1c2203041c43c0180c1e01041c1e0128009044848144001c200307030f4200000034000740310b4550307405000c02c000300010404a080e40700d4131282c040096151081c65855031181da5032800303a00340041000303401440502216040c4d0300003d4100c2c1000d00008c11641e1659151401c5400504000740d031584514078400703103030750f040c014560802d61f42c0d00110314181c204a64451176102c002e100e10942503d403e0844c031200e00c10b00c21100315000700b8a11140c02d062540c0b00c06855840103500341c90f103609003034010a90801d14402c507401100010021850041c40e070381e14410901c0b0240d0280c5031204d1107100003c20700c40078811548110721940d000941002e0000709042100d000de0f003030703044180c82c00c42040884e0b40c000400f0401507030050300021600d0341a02c0207020403280100c0501c900911003031100103040039150014000c1440703071180c104a07038030b48403400c044a2465902071142d103046c05a1500b65400399000b1130700074481c1d220081c0582500c111401c2030f00c100303a00407580da9211120502c14 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 303028947 1250 303027697 303027701
    0xf06060a080706030519061d060619081f06090f0e04020d03050c01090f030804060b041505040c140f0a090b070305030a0e030c0d021b010504050d110d140709 69
    0x110140445800c0304190406007095920180c9000d620103266698010a031200b6410310350701d0580030004802d103d19525030101c3c80c00c2c2c0c0c160300403201003800b9a00209890389441c80680351044c0c0c166009500050740b545044900f803502a00c1c5d480903000c60103d124944c50b035007040303c0140500d510f410350080e14080b0200d8110070558071000c2150240b0081c000160340e0440c04002c580c1d010b10704030740ca94520001e40da004001d05d0000401d4603003104540b0041641046516104500a02040040417003a0040c8401c2d02d1190300c1080400c2c50b0000140404e107404d5001d520b0651041c40c0413070048489030850003899111074070702c0004c0c00001c20400401035002d1401c40290101000b90303402e094265401509501014044003c01a1105800121503000f04242e8807107589546c101c5002c0440d040c07020b9140c140031007604403108030f8000e90901c1740d4001d030300300c030121035003c0e000d440200c00c1d40c0c403a01825184809250b0f0b01203c60280e41000c42d81c400051200f207000c040140070745616080044c01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 303030197 1250 303028947 303028951
    0xf06040207020103231902030c040905040c0905070207030c0510080708070507050615042d0207030c050d03051008010e1b010905131a011412060310140405010606110d0f0207170f06 79
    0x4505004100b080300c02c22164043cae03000c0f1548803502045d0f584640c034000a00d003000d17800000c04180b801d01003080242c0d000517144100e0780075804a500e29921402403210460900003050b02003010200810b00c402d119a5206510013200c1c0391103424a039083d581c07a070408009807030301101038551483c403048500d001d118000c182c800e6400044510006251200d00d0300c0100120a100c0d5035021441d80e0038140500080c00d4a568410280d030810241c200018005290a88540d00340d0803a140d8041403100c0c0511480d180c000b41c1a000302220710381d44490b000c00350f0402c501d20f810814220320028035500c0d5082c04c1080f060480388007041100c107641131a8101c040404000d41001294112001d840807020300b01c4500b0b100030510503401c1c1c1d9072032011a161400c45604070054514080c0c0c0207503d03444000341c20b800366200c1c41c000c2c01025030740c410031582403030400007100060300302c400b901c401c203401441c070041c003000c0e1401620b482c640c1d1820f48a403c840808148460381d00f040e481c0d44611802030040e0307a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 303031447 1250 303030197 303030241
    0xc080d020a120c1a010801290102070b090f06040b0307030b1504061206080610030510090b0c031e040c0312140307030e1f0902090f0f0604020702010323 67
    0x3003071200d42078a07078481e9800003584480910a03c80d20303000a01901000c443c1e1400740301c500c2c529103941d40e840103a00805500944440c0c2c032064140c9103103003000c1c60842080c0c1c414141c0c01016214200712040140d94400c0141590028123044003201341d44819000e4801800c01c02d542c1c6403240f5102c0703006010340300d280000c98400c4924024040400c0d000e4425902601d8140c90803244031040f41d440500103141940140d00a84195820003907140d64151107901500d1003101a40d2441301c200689030140c1c0c0e05648000c14032946580010307141c01410740519485003035005c0b408064080020800c0c14140b050b01c041e503104005100500501c0b44000c00a50040c200380b5112080d010603140405c170b6800090060020161524015601d610301044030480d00056408521609100840d9000051400035412405681403d0000e0510041184190b1040d904034541d038809030b031050f0400c4000d611580040f81030603903400d21903a92200c159414483c0030318003500d030b202078103001915a590380c0312541ca034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 303032697 1250 303031447 303031453
    0xe090901150911071b0f1d060d080d06090902040c0e030a03050901020c13062402074208150303091504080f0705100302040501021f0204120c080d02 65
    0x55201820219540802c8560000000407180d207400c089003030030301c00c4d00c0d400f410320341062002c0400b000000162600f01c0c0d90105003c074045a4a45038043d00080440b4022002c80142000402c1030030040c20010206101d00c845600c4c04500d1035900080303940a4200004242c3c0c0c1350000d40840c186407040b50904607403400c00b45405080c0c1c000113540d42024000040410401050b4020246d00800804500100090001c040d0b0201000303e040140807500c0b8100c4550301c2c0c5050b840310135420f51b10401c00c13a14164041c005441c14135405040c00140b90324090000c020500d42c000c9034507400842c10501d259841c218226040c8521b000514402c400b5000300001181c2e2050034a00781e4000040380e40f40d000550342d5900310068117000080601859001c0300c818083c2d03c603469004400419618159003044558410015040da0100d0490203035005039405030303010703001441d418406104203040c41441a41d016160507150304254401c0701d825101120001c6e00d0100070300210405100c2015080014802 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 303033947 1250 303032697 303032711
    0x712120e06071103011503030c0209100803040312140c0a1a130b040204091b0806100302011d040603060c0f140c0304440616140d020702040603030e090901 68
    0xc1482c840c0c500020b056048074020040075850a400c055944080141101403880c1d4071704014100745500102203100301c00120000300924204030304078081c3c43c2102d00550510b803c5070740b0a84079a105a01140c240300070010303042038003020500104500580c0c0400307420300c40c5881c40c2c021400700200d0400420000d41e00208442824400905101140c101c03140d20f100741c440380041001031a01010243c02c0b02c010110350034940e5007103241201295644811600e540d6030b000307900304441c00c0340e000090000e46035240054000c0801d911070b5a90110040001030b140d90b40c1e6031540c6c01c070b078908000640800c82400c89222056008442c1c1081410714040c0e151408191516040d200d20a50207041c82031019844000344d810359500c0524000d440c100012081d000620207400385a4041c045044801d11502002841c810200c0100d0403003c1c842d03880b001c18858141396410001e4019100c0800d06690078410301c0050303915800707440c00460294a94106a4003103500b4008640c800500800c1240e040c496 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 303035197 1250 303033947 303033949
    0x12081204121706061615180b0903070308070e011b06050a0606090810020a021e0610271107020d1103011112010b070303140a1a1903140109050712120e 66
    0x4641143e200301041c1005c5041c9450b002e001d03160a8800051040d14019902000030302c42e0b56104001d901a0710003000c5a81c803000c1039556032048082c0200012608401314100c0c0d4014462100c100c0414141000140d1203441072070541e101c10303e070139103501d6218414042011182e2050102030704162071324498090801461503036500751017049a4906500048030000b081c0709002c03640c0030100000440d0641c65010000750759400c0164ac949902c6103590000050798107111000c003011390110181181e1245800051000800800b071aa840d00c041c108031a0006aa800a507070a187e4400c0740300080c942400d2041c90b007154182840c41200782400c208075001051111081030454809603d02a036075186450201e003e0280c4210b02d51100180c0c001f400300c1c07000c0da5044002d60460402034030700604601e02c204850340307a55540c4204a80e45001c000e05c086014050035007042c0c02050004204034540742d5455280c412160b014101ca020007180c540c040182ca090080b00c11300761450402c0c0f4001a000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 303036447 1250 303035197 303035209
    0x207030209040f111207090606050a0c020f151210060903020132070f11011b0605091204080706020607031406090a060801050109150905070912081204121706 69
    0x20b040075102841c68802c1d08108601801c040040b0003000c3c110a0041030000c1140d0741d10212405036400d02ea0802c000481c0a510a0013694503601081c4c0d503039182951940c080c423010000304c1c9032580d0410a00a0404e18282e0400024502d030511a6078805251403d2400d240b1546880e8002e101005800c1e030040000d42e0b48085034142c6030250001044020034100036910707000c000e030805402d139070700d000c42c002d020b014007c3d82c0741d2101c5000d540741a82900b40c034001180c02e0264a940305694131101410300e804103e00b944807961045c0303800c003100e007070011000c0301501a801690150700d0700e5112f4441440640c1e414801d842d0445250305040c410030920012031000000700071b01c0e480c0101c5410000900c16007640d0054401003410038020000c6507101c41514001d0304005d41c03506184c02c40b07034400041005180c80f81c10b11443d100c3d039444503814140480c0402417040607800751355900b0180002000c031808a031a460140f0700c00d29481c43da43c200c60b4800b40021806100328074004c20700f4010480035440700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 303037697 1250 303036447 303036451
    0x8070e0705031f06110d0206100909020123071406060d0303091e03050d06051c0b0414060708061309020a0e06030709021204061d0c04021b010509010c030b010207030209 74
    0x16041454407a552079029016810010407254001c40e5000000507000c3d801845d0301c45c0707115400d400c1d00c11103a4000c505a0382e440c02035820300305d0615800020850007207a07034044920365205140c6a01c461160459003222081e00507100c0d03002040001d481d07001c01107070442c01d2100300d1540e0301400d074502e4a02e0001c0c8801d0781c0d0300c001405240d00e40d03042d0740c100441484100000c6c50406000e1900401b541001030a0f40c1008114540152030300c200402d0b1441c0031340c160000d018410b4582443c115031556442480c0802030800c81d20810380d40da009000000071301004e4410303015580e400c809440d025080149556041040041c885d2401c480e010141c0ca8040460050b00d8034012032005a03151381b004646044900d5000b142d66510210342114103015254400b4000d9006481c14040340c98080769030401c1001140f171b6646140d01c18101142c0504050b0068607114491900e814030304400f0460903800e50784122180d214a0350f5403c54540041d80600c03031501e01c4a000c0c40148440d5040d40e001c294450301c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 303038947 1250 303037697 303037711
    0x3150105190b0a0e10050c1c02190809030d14030601030b0f0a09050f1608070f0507020a0b120f01080a1407081e0d0302090a05040e0a0b01060c0c08070e 67
    0x40607110301c8690034a000014980c0c1807080e540c949030303040024041d4480e1104c0e103210f003240901d80c0c0d4a5501c2441a9070b042da00400240070102190710380035804120106c141c0c0150302032045005a40c00103140b0340a16140a58a101d6941d22007004240c2058a0540442c0500c101c504082d5000d001d4002502e6010500307080000303d855038031000402c008000c02c02940c0c0666081c0d00422117413203603000b0500031300320200302c04081d440b124030710030119664075002d1000440f6200018070707862241040301c041803240e0400e60b1400801e03401296082516800c00c00b05410000350407040c1034000400b850340728a9210703030060700e541071880f060344543c0c0113240600004901115143d90300010710a1100a06001c4100e0f0382e00003800c500d001994600341c100d0349142c00b5004468808a0090080399020306004003d40c844c2d0b8205010800241803070003113510305104420852001a0075101602d010744101d07102d561008000340b40800c42030000b40c11104098010303503000c00088030950a0181c000320 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 303040197 1250 303038947 303038959
    0x905040207030c171e0702091b130620010c09180213062607021e032106040612170c0f01140604140405070b0d1103012303150105 57
    0x4142c0c28211460000400080c000d62840b03040303025800300b051300400300440441500c1400c140c0380b41013801c40f800350345030194200c01c060000803034062824a14185041d4522003050820039810040940002c59801580100b010002c2c5100402640d112040b94004150020b020040c03681c00d0041c101055485981c10381400e410201c00c004ca41901503030381810388410b2172000240d9480f80207080c864144500f041d94024020306460403007814540c1489012550010030b011645044000200340e941c042e0001d280c0170030300064050504010003020354042c0408110803d003020000c200440d00c05070320842c1c0c01d00301412103600040300807801918124645a101d03868440c40c0030500d09100078071495407940d510304950b01c50724410fa02a42e03805000c083d5000c2100d8054885c40340026102038402a165910407003042050b07040e050300420f440302505101141f25900000618070710340003a08500c1c46801c0d0b51240581d4081001c4690101140c200c006080c02d40b800c0f02040d051010600405005d82 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 303041447 1250 303040197 303040207
    0x31c0e0f030d020415080f0c0d1103040605040209010815060904020303040308040b030a050c0a05120a0b030a0326070903030c0317071d03030a140306040905030a0c110105030709050402 81
    0x52050041820101000e0192030350b444090600d10000e40c858050745d04c1d80442081c00d180318030f01c90395003603101c2d04280380101040c1d1030f054030340800c0e60041000c00c40e200f615080d05c10704546000e00a14003d0b031098502056508181c410802c214405820040450b400040000d2580072144030198004c05c00396003154250304c80d070000c40e00f07501ca00e4201801411000a00041c250101c0700210721441458008002c180c8546400291500c1410303100000500f050120003a00c10003401000c1e04884ca0850000d000c0ca21034001c2810205400010740100b500049500d18048001204501c444084107081e1514548080d024011061030302000d0b04014000c0e84460816004650211a201d4800300982940c941800010400030b0700c3c008180600707029080d103800d1420000141c0d6800070464450200c9085c1c80b0783d410400e6003004201c55071040d11101d00b080070920030f00060451040c0c0380d80307103401c1c140d0500f010200d9034040c042c60b6042040420420443d02e51000c422826203d0449000d6562 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 303042697 1250 303041447 303041471
    0xa1802010c0f060203011e05102703060509101506080c0c030c01110715050906060105090411030408072904020d080d0f1d0105060f100c05030d06030311031c 69
    0x42c08040c40001d0100d8800000429444680d90b42d0140d504c03c410089071307140e900d48050004800f900198400480c600081594419078420147c90440c89280210744006907682c03a41020383c0d80948131400c40d50444c0c1503118810310940106008540b001c5a005801440e1000c0140014001486690038050109086031248400d108540c0c400010900074000180740c2c41d00d20364103030700c001d60860b6001c0200c030307403245001c403d0b000f010721549000c0040e140c2a40c8170f0b00150340301da200c0094507a0107540c070ba82c01c082d0092204061405103024005040d110f032031030718000900000d0306028201c0101820f9120500150303503c4855481a0f0641e034250b41d0500301d2500104e20f004010300e01a1071401c0240a042d0500c46900103400d40309019081000b41c02010301a9088580603643c0c250841c00c070041105840c10a0154007038031664901e0000399404468489500355000321507000181500c0d144d0410a00d1b61002108200410000c040c5250046004a22080f4001000f605102907201c0203680c082d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 303043947 1250 303042697 303042713
    0x20702030a05010c0206010e012310020c0a0e0f090304120305070807020414101d04060b031f0504020f0f0108041b050a0602070801061202060a030b040603060f020c060a1802010c 78
    0x1c0260b001c0020304c03200386502006074468109001d800390903850100005101e58403016a00e501c448a030121110100036031082c00884254148858198803519200e0300141d1241e584a100030080304640002c0d50074005018050800041c001007a40d500605c801d2141490b0710350b410807916850300b403260b5070302d400e45490521030103510000380d0b000e40360944801840c200b4400051080700003104858803943c54084030400301800500003040c450b0704100080000d0080d50111400110050489069510085110f40d8440c00309040003100d0341ca1302c0500046092a1080300046003040b50880102c4030204002041c00d10300820150980301468141184e031841801c0c0e5201500c409810340e40c20301c0e00c03020080d5481075148990795007503103403060002c0da0248411251a00c103500a004500c0c0414101c011009811980180c0768421f9a9900c00000202c2a10031621841d001e0790001d61150542102d00b420500000c1c442001241807030100c2d0700c1e140000440e03a00c0c80350f0909144503410024100000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 303045197 1250 303043947 303043963
    0x27061502030d1806020a030b010305070503091b03070b0a0504090c05161e0c2c0c040510020c0604090c02010c090609051e03010e030304050d110714130f05152202070203 74
    0x100f813600c00519804042c1d415000340c06080d0382a20144800c0c1c0300d402044400b84412182011103801189255440903480328110002240040449030500c2d00c0b03441040003581b00594010100b800042c04000d00300781ca004092800c103041c1041c0303041c90f5918118900710744074110001c0c10044005241d116007203c0e200390301242c540007030103004000d440d4218001a08130b540803030304800c6480481045c0100c0c8094126210b41c021802c0305041626101c1030180c94503402003400258014203600e40907544400d40a08020a190360002c00c0ba074031a00030190840340c10f150004100700c010030341804142e802881d201c0496200342d64401c418011850584d20408183c1c105c658994207000b02c000c20341100101550049000d07006603030080403119020354821203820900c0c0310940000d54104108100b04400c440a218041c016800c0c0d81c140c10200300490b84021802e0740e1181c2ea80051103105000c1c4500a03401c10425501e01d4012000324101c20340b1b1420700c0140a8115400249201c02c6440512a81d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 303046447 1250 303045197 303045203
    0x304021915090b07020a062a03051b012d0923010b06040303020d0305150d050d030e0a02060706020a02010b06040e010e0606030c090409080427061502030d18 69
    0x44189511224000072040c804081180000c24544012414a0b9003604489020340d0082038880c82c40c4c50007030709544550034400240d01ca4a2800b0406c1c0c41442c1c00241121074030700c2a513800d60348110b00d60740e07044e81310051104030070b01d0781c0750100340c88551078080c8030066009a904031178116201c0f0340322100060111814020007d1141c4a0466124140752024020003280c01e80240000c9030400140300440c001ca10028006034400206030106034001e5200d83c0d0408030600c03e1001c0d4608140100300e461104410895040d40b08004140c0ba0f203600d4490089140313500805012807403a03a4002a149000c0d43c407001e45941d0340020224a07580c001d5101c415102005001d0b141c0b9165a40710075070312610244101d2044d0004000040c2c2c40380f80480c00c40348140a10340e42582800002d1052000516200400702d072107032010840400d4a02c20400408400c440c0f1210a540c900c005119100c180c413642e5124001c100320025601c3d010740d402209994040800e100001101c41c0240a0f5901c3c40d01414030203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 303047697 1250 303046447 303046489
    0x7021501030b060d021513080f010c0f03020313020d0f0201020d1b03140d11070302060a0c0914042d0e0a02010c1218060c0203060f06100f170a0b151905030402 70
    0x780981b66103c68414110341100027654240c0c14a8502c40b801c2c0e0b803040c110240007406000e00041120300944c080c58019611800d190f4410256a002c10000d6941041c01c0d207101820100d42c2d0304541e810418420205140c9c907051800001400c5010449200c00400034203002800d40200d8480440505071240f20078054011f0040c1d4041c44540c048603030107200b040d00140a00b100203290b882c13981c0200060103c03141c0c0c030034400ca80b0f0202d103807a840c0c00710400203a105840d900c0d607241e0030202c201003401c211100c2040c801d0302d007107400e10703002143c8149003240707da034100040382030150b138001e28025102504100c461b0111400c02004640c0d5000c403d402c0d0300788080d190390118001e41d00010300c1e139034580700742d085958a8842981148040c04101e401036070108000f041100f15a200d0f007030620400b1031904000c000790039040d211510342c1404440c1402041d0303841300840303241e00e459840e0ac40c400b8580290146071106159504552460b80c0c030104080c00400004035085407250302c0c040c80cac0305960703141d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 303048947 1250 303047697 303047707
    0x711040c0c050f01050c092209030e030c01170606030711030f3103140a02120d0f18030605100b0307090602120a050d0b060c03070b07021501030b060d0215 68
    0x280041c020075100340e41521a08600840415051140c41d000b0141800142c3c28140100100021035030310404a0a0b5420603c0810f40042014001d5260052107602e41075a24200c0000341441c00b0121060181000a40100000c60020f091203142c0c2211003a00d0880c1c0d2540d880d07a0641b5552501c0e1901e40161100180e007107407200103131000d0000003010603403d014110100c1160403035410b000b00041c2440041c003000304005140c4c09100d4444003600340582d05211080d030005500b000004008200b1608903d07090244294043c00c0200d0f01c24440c1484e00071a0072040c489180d010160000520b2140d07604041115001100c442500500b0220301c032695a103070000f00140014514403030040941f151010401d4584105030035034980403641da88840c10200c46500b5000505006444550064810031030003103c030200388001d0680078020403c0310303c64240114000d1611f907440d0b6444840514840050000034032060940d50891800c8400781030f800841d00008140c96114024180350f4000012 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 303050197 1250 303048947 303048971
    0x25030f0b090f10090b060a05300f030408070902030c040e070c0602280e0607080f0c0304170c09040803010b070311030408071404050c030601081504050a06090b0d0302030f071104 78
    0x54070000d4440c0842c45890340b0ba186c14030a03010304602440d6844030200300080403081c5030100101a0703201840b54100c6c881e009100840c00d1180e42d483c22100350f000000c06010302c450410510000304000350045145203454030ba804402d004600441c141e08403c0400718103260310030041c02d50f10b01e030001c5046603201e01b41c8407141c0512040403524213028584e0014030891600038a480008040081c107442c2c90a00c03150f17108040c0d07078001501103110380000d0002d0102040300300302810180000c155400200d240c9124070501c2d00d040d08003020320a081010400c07001990b61400e40381100c08082ca819250b055928055440048050340c881e070070310011070001401d240010381c5400320b48030084421341100100c1c051100341c0c1d40441e0b01d800d64400800100d04154811008180d0120020304c0b0340b9160b8603182c1c006400d135403054404074921501da034003c0c40b01000343e10544514a500301e841140440255034040e40703d0141e01d941c141d00c404081280c030f092140c03080c2030080c0d80000600c10410049400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 303051447 1250 303050197 303050201
    0xc0302030105030d080108060a0905150f010806010b03040201050405010c0602091f090914010e0408040e070906030f0902090106080a0b040f0504030e0d21050408060925030f0b090f10 80
    0x40704031803280c45130b054920b442c14003d0084a0503100d00401400c1c090307072003400e03e00c00344c04042c2040b9564824611800002001100c005014021207464044603524240b0341600d00207040e0441c18282c60704100780300040c0e8224040318225003085c00c00382424071150420f0402401075460040c0c0008204644040c0c3e03031a102d10a001c0c00e200d40d15180d4819450b03010110403980e41400c0d50071003070f00d0100180030345205030064507406846800054075040d21440c40041403202a1103060200d0168007041c44400d0705406900ca01e0780c0c02110800060035290001554040b044c414001800400c402090b10501960814041400064410701a1019443e0a6001030404880644c001408000310604038940b10390700d1400075400404405004800604850034055400c3c000400d000c0e00300400104100d040c04024803035202140074143c00c20020034040d091143ca0341d41083d03c00084541403000401d071032480b6a0181e00a00c8403e01c2e552203030b24241c6812881ca8501c000c910aa291001c6000129 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 303052697 1250 303051447 303051449
    0x507110105090a120c08090f04020c0f0706031b020607031d0f03040f06030e03030f0604140702010903090b030c04060315030b0103050d030b030a0c1203030b042c0d0c1202030d0c03020301 82
    0x881d9540c0c11451050304c1101d000e610110001c04c4214100600515490f04031503203c0030090050006203000d21400340349241c1402e07460001ca6130f4010380d104110098045c450000030007860814440d44220f4030320001d448000040954040c036035205aa400fa116101c900000d4100c50041151307046100004800e41e03941051140000ca24640d1001180c25442402220010300300e01c1c00a6085840b02c4403282e00c641402841150040c0d0f840052400c40f88003207000f203000e50f035980c0000440600c5410700410b41748260b0403120345880c0030001d010420003964101d0301101c0e01403034000355400203035260103601c503555400179001d0034a9000110a0003800702e9221800d5086440800901500109041c1c4600000f00041c24043c5903002c10800004081000b400d000d2207031400141800010b80010120343c3c100340000c11460f10041034200100301408400048002d000c0140200031803220b000344401c030007000040c5051356142e203c0f1425402001039400c40b070394940b010700245e40201d400400a40003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 303053947 1250 303052697 303052703
    0x7030509010615050403230a02090a090f08030103021309030e040c05090d060209030607020a050d0804020f10020105150405010e062e05031b0a02060609190e1501061e030507110105090a 81
    0x2696a601210443c043d407203183c01410080d01030b6182da500ac01506500041902c04210780b202052400548205204500c403071040341099181c0d4154010b0100314580b81c500120094a05000c41e0082a00907100044030310381120046010203455600300c0e002d00a0724080c641041100344000104002900a0258500181c08a8040340c2c0d603090300b2aa500000e580240c010340025080380b00c10b03403040c00403651142c0080c0c03914a00402c5500400e00c3c2c04cc200d4001070050755520280809a080025200035101c3d0480c1e041c040d80d4100b0300020540003020780b02c0e43c4105001c580348010740c0d840c400c510906801640303034103541216000d0090495401250001c114112a000f848503a0b080070044d030352854019130042200d41d0381c41d028410360b040080c202220714481c04041c0c20851501b801482c521500c954050810581c00380d036803078036108040e00014207100340443c108042c10ba102144040100c0c051902040644914009691442c40448100760b154205020010702c410001001d5509501c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 303055197 1250 303053947 303053963
    0x2090d14070b0d091103071505131701060e0c1201300c060206010b040e0f07020f0a110415031e021c0302061b090a0528030c03050f1507030509010615050403 69
    0x41c01e2020147c403904280107104856452110990001d8803803009030064511116029041e29114030705900100d0394100c9c5207099030344440b000e2000d0400d9400c03260300314003401e04040c00c0c0b070400309076200b080705d05000d002c441034030350800381e0010004841d41c4d40c0142041492400000a503050001c5940c070907000302e00141c1b14640001502410003821a07088550000820711507450f0100a0100c0400203440c101c00c511500544480024040c0b00c41e00700c1901c40c0800d411008a014144030988040381d0075044201003650042001c0b0300c80410039080701100a105251803000ad20014030030208520400c41104003142d260701c01c0680000c0c080c0c0c050850b1210484400341d0814072035810341b09000000d60070040d00c182c100a141402400c0c1c43d9540c0a404150b5058a0720840000348100c0c2a802514410301d1950204103200c0144000d03c9040c4604000e000740380051201c5503880d04010300004201507884c40010307100002913002001074808882c1070803509440d282e0080c40b68201c0d00055403d84 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 303056447 1250 303055197 303055223
    0x1d090405150c0c0d0503060603040b090a0c090b040b040608060103080717030c121005010f1101090611090118120f110a0b09030c01020705212803110102090d14070b0d09 74
    0x185c084e03010360303110701402481d171469580e030360761885c1d5441000740043d8044c0c42014045400170b48003600e07502c05465071420001d060600c01080105503500345142074003603403078010148072102c000704003181507a401101c3c0d590b035a03501c0e2030018589403403c18030b0329010602005010182c882c00c0010003114a2101c3c1000c2281c48441c0f0703402241000d481201d0108919461185505014000c0c00d00c6c58040c2400024901440e038481c0c40603500c420050141c054400030b207514503582c01000c4802c040c100a9040a001400c02c2c2006504a00010028111659140ca200c0030404160f210810440c0050400d0991643d90031106455805c0040c80c24401e004010406010b9440001c3e003000f1104000c3c0400315002d0340340008031002c140c03110000c000d405600c00100318000c2c03405010019400039801d1072581c69040c207005016030040d00c2c220318180d0041241e04210356841d1803190310136070003000230850051000d109504d0403409a1245655000c00326203600e1500c66030303114040c2c07030340258581000780c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 303057553 1106 303056447 303056473
    0x5180403030c022d151005010507020f0303130e1b030615160c0501140c031b0c1003090b071412130b13060c1d090405150c0c 55
    0x5034182402d03051101004100f01c5c08400c12200d0500d1060411540c242089000e91003800e04000010980100755602d16443e04414a0b0040489035950303241c901619840d40c0520648001c1c0450b200019554018168101d42c41c0e107500d44010b182d50b444108114445500d109402c1c038190b000c1c4961660b1030300d8691211a00341c00f804080c001e00e464200014000750202000c0c06500ca414030501a00420001c1560740d00c051b40d216545070320020310100740c030344280d00329110f03440303040100c192000139015484003405a01800c10140341da41c90b403a0a44031b03540740b03030340d164035446042108050320f0521034026a000800d0001c3c2c282e1440d025150000540d13010ba17a002a03c1e52001d042c0d004000c0c084c480c5040304001400d010340c50350240700d50414581200c1301c0b054010300d5106c000070200700d405c3c080c04011071007900404031036081240e0b859100340c00c03051180300244101c49aa00c41 = true := by decide +kernel

theorem cover : BRFrame.Cov 302877697 303057553 := by
  have h0 := BRFrame.cov_init 302877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 302877697 ≤ n) (h2 : n < 303057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
