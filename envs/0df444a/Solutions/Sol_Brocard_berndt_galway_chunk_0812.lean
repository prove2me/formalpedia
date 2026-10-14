-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0812
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:56:37.478549+00:00
-- url     : https://prove2.me/submissions/5be31120-ac03-466d-8b9f-7ed0224600d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 145863309 ≤ n < 146043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 145864559 1250 145863309 145863317
    0x60c0307170d110a1202030c04090603050610050105040f0905040609140601080f07182018010801150806010305092814010522061e050f01230120030a 66
    0x206001951400b0b032140710284103460f00b020092600d08a6004034010b80d080ca41c104010303120b031a0b690080b081803045034440901c841c148400402400004200030b4050755070a42c0703071038510790349a0040d0303001e00680c4521110b1030001c0c201006011b40750340080d50b02c580b0036840000c5000325503075a54141400000e0400740340d0701c180300501108104001080168520b64002c0c4096450644009030152903104000b42e0035485169401e07540031500083c02c54025907944d0701d070300c1c0c620019144d0106040002c4041c00501103078000030b0002d0000c209030b00000159540e80d809035079803400540140401420440162060240395040d200807a09560200c0080c00c034602d2500e4000d003041e80d0301d01402d09640f00c1c541d240c101404040b42c104540c401200e400c158209a00d100b0711b04204000b06180616030601410f80d000422480034070364041481072060144090030750362103803400010204415100d400b400f2015000398003940c05090420021000882821803508a80482d903086400180460b4081 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 145865809 1250 145864559 145864567
    0x31404081209011a120a06020408100b0a03020112020703090506041706090c01090317070b0705030601180e07030b0a051002010c0917030d2a09050307140a05060c030717 74
    0x208000105550058003800080c05001101d813580c46618501500c1d0070720401c0880c0b4028801c0310280440c402c0c6503000007003117444959400c0348680b20340e40c0c1704c0e9000c40b09142c0002072480d440c050b65a4404d03a03070103a40d8008180c1c10190b420000358040d000550a1100c90700b4001080d982d400300600183c21844a1685000e2000c007260b850b00d000504040300d5900b190702190201d9070300580c25000c40780c0040004040441030041d52400c0e10800002810003202c49d000c00c02c006400038015400f8500a9131240ca03000020400e1450040035030040145140d88000420860391003500301d41100708008003000036541e0341e40c0014103007403052a06480940d440c2c2000143c400e40010700e84000340080000149643e1001c00c00d55124412038410700d001c83e5031090860a421480c01005480304481542882c2d0b04060700da01405588440c40303168840d2003103110100342c925890400003e4a100500020b88450900081020f10f0308100c0d142d00041c4010b2001202003041c590340c180d0390381c001c002c0c0c4560b2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 145867059 1250 145865809 145865827
    0x6190311030705010504080c060a0c0c0602010b0f031606080712020408010b040b0d050309040c110a0510050114030a11030a150e01060f1d07030b13060807050d02030709090303140408 80
    0x20400e650f44800d050000902040003425004150038400010840302244c2c1d94040c20406d03549171480a102a2054200090110f00a40c05501403001c5420440310490794050507010180d450404030000071503040e0240003000540c0c0030321a540d41110040c2062600d8140741e41401c0106c1c5c209070b102c00080c3e074503203680081c10b00707152040c03a000d04002c1c0d520302d03100130700c07921905d80e60301c0b544603030070701460303891000b100128440c8100c000d9440c9084103403001d2462509080760f417440c40c002e00101d2145080d00000342c5e500c102c1c9010340c0745038026001d02002e80d80ca03200e144d40c541c1c403c40c5c00f64160260700b10355000504500c01603c2c45545e503080000d5071090180d01d0760700b100d03080d4110303080101c80c4000a20000d040b1083e030b000042e08036010315441d42e03501c5d04128040c0a0107003025802958403031030800c0c10007142c0c00c0042500c0c0120211218a661101040f0b400e24a112000c0d401d0342104109004c03120190304000166806030402240e182003690041418030800c54050381c01400100e05901 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 145868309 1250 145867059 145867063
    0x21c0314070c0b0f13081216091409190e0d0f08010302090a0b030a0204020c0c091e010312030b030307030302040602060604060315090f05121b06010e0408030619031103 74
    0x3400c88228600001101d00580e030f42c646001c2e0181c041c2400d05610000039070b64000f0540d0071140e507607103c40d0071501e50348545003000200f88180c1d01c0a01000301d100d1040c006030700ca80850700458210f250711006030341050052108801000d05002c00c4024401d101e180d07120858003a400c00110044003d1220070403284005200c180ca018000e42041105801000540c0c1c0d58190175400c40185080003c1d10720014002a24110203010000d40250012030050513400010942a56880d402c3c0da52030b20680e00c0c00c204441000f600018810108510f00041c070104680a42d02c01280c1040c0c2000032700c01204400007031075038000136002c0b00026000501400104d9060040ca600b10f4000d8609009540c01d666880c00c4c2440f1010303580f4000c80d0b40e44c40b100c1c05d001e0380400082c505a00442a202104107204043d145c0c2ea201c081c1c07a91410303442c0031a035507040d040040ca00d07040340c2c110302a0707451a0300c841c0c2d5501d2003517002031f1400341e110302c8030b80d4003000909158440e900218440e405a03121040314900f414 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 145869559 1250 145868309 145868311
    0xc0504021e0a020c031e0601090c05070c030c091104050603040b090a05060103050a0611130303030f0f112508160f0515010f0605040b07060207030311071103010b2e021c0314 76
    0x24032214030305900840c0c0142c0010700076040d946102c1c00130541c05404ae170120303002e000740030000c1c000320300001000040c8001c00241800380d614a0800744100008001c60100c143312714403d80e60000340420008003c43eaa041f001c54000d840b010a650118031903490301860014207810564454010f00c034200b0802440b0720500d41c00c0c030030032180182002841ca121000e440d4040c0b2001e418144c58400c000083c4d0010750050a1303201040308100580700310843c1c2e8030710581240e503d125130f120101d148603a070304080b00e20740e030394181d40070704003601e482039640390700100c8002d501c2d0465111500d0001d0b280014000d1040801420031145d02d80855031402c910700446a207640c6c230180900c031003040180f202840b8407003182c6040303810101c0036a96201c1850102e0041c4400001c3c0c4401c81c0011a0f000c0c20000c2c610300301d00f6401c000324020303c001d82110040107000484d122002200c00041d02960312618403000054003400c1480c01940c1201c18045801c3c003048003112611000030341e44064001038044001441c07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 145870809 1250 145869559 145869583
    0x309100501050f0f0310150810060e010b1318050f0105010807140c03040801110705100203071d040605030d020102040503070e010506040b030a06030501020a170708040c0504021e0a020c03 82
    0x50209500d49000f0a42c08441da03045a0b0064a0218103840e1586003007080c075200658502d000c10444484440194504259018840c41409040071110007903006c0d002d0711055449944a018440c1d00e0482c03001c1c1d950f0300c10041212550311401000841400a9101206c40500340c078020a83e850240302108805078140c02041c180b180800c02e0140a583c0f00c1c90000c4240c2c40d501c4c12903a40c4580c0c001b400d00e035006a9101685c3d035070800702014806400700b070282080d188a80c0803514440350020f0070200340c4c0800c075030f1807000484c1105110320608080c08056820080a080010b610f134881010034241030401e104000540e4002408001d2410b003042510010048606101a10f5041c200010300d00c3c851441030344281203011020407500b10ba140e01050040d50b118000319030342d055030000600f414810070794005102d2a514005440300b030040c50b0780c1e1300c40c5030f20002c0400e03028104001c00c4025001442c00305580482c1ca21014030304c65991009090058458000f020703810520300130145000d00c001d1807 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 145872059 1250 145870809 145870811
    0x60a1116030b061f0507060603120e0102060a050609070c111009180504150507090b030f011d1b0f070c0b09240a1d040c0314011e030f030504030c0303020102030910 72
    0x40ca0104d1900202034604010300c1c03405564407043ca08054024154079000074003102c081d68180399000340c00c040c80c101202800c1e02a00c40550b00c5000c132008941e01111099001a40302c40050400c510810300000d25510990301d210701042c1110124049154140c0440086500c62109000b00480c490199441c1c0348040c0040c8041c0c034060360f64095844141c07203c400101e072540041812075000d081e01070090850320000c03544a180920004504410a12400380d401e9100443c00300c0840c0640000c601ca90660a92800c5900020441e1740da107a03c4050342180d085010310040c4002612038031000001c160082e019616854110104a000c48100c0000310003038101803030075880055070a0595003906441d08007541143c0c1c5502c0d04044104825150340d911500c1c028a41d0700b400d07050703031110641c40048907808016a0b01d132800320440d20f04085680c6082500c100d0200002110490002d00307551091030400c1c105950f90b40d841c0360811903a0070031805070f5000700c01c020001e00e08000e80d054240303036040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 145873309 1250 145872059 145872079
    0x80907050a0302033a020303040c0e06061c060f03030504090b040902220f090b04060606020d090308090604030c0f06030b06040b03070305040203011b021e011109060a1116030b06 78
    0x20029944010300940c4811641400d0119100501c170101d450340c444204481d0f6800003a44880b00a40325401120100c50040b0841000314000f40c000401900c104405010103240c0892171450386603c0c2c02d0010f44c10a140d440d04e20125400a03403110303d01c025442a11403907117a40c10301041d24269031000036480d004a141c02206030150f0b03501d09c0f041700219405804222240118000480a0540d250108400ca03080141b030030108016071840c03a110768007a407001c0104a17203c1c2d00480c0c840000c84866000540e541c40e0034004610388100900b02c114000302014505507072a5201c080c03510709544140051140c2c2030f07003088003e4050162440443c42147c1a13803401e130404009000d04c0c0400380220003015500c00010701191000d604c910500c440b81f44000d0065010307280e0080d6541801c81c5200784d8034091000441c0c0c6000e050041e261080c0401103203608000d904010f01105800101d01ea0701000201861500700c11020b20400351103166032190149420f0a50603c3c0300034940281070240103800643d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 145874559 1250 145873309 145873313
    0x3070203030106110705030a150b0306070203030613091202030415110d0f120906060f0e10030201080403120204032607030801090b010302070213200c0d08060a03080a080907050a03 79
    0x48112815583c0b181000302c041490628014038281e03c6412890300740c85000400414401104203100141000d60001d01102031034806140d03c13140182c07400d00159200303101150702850b0101e0200038001d0320600c005146c845940350040486142e100000168000280500c0710780030102d4454001c80c03041c100a5000142c2c0009143d640402182040400554043c0e007001c00c0c0c480c64104091020307031401400032489900700000200800c0c8503000042d25481d100242c000583d4844500c5104181c8100441c00c1c0b03103400542e003240300104120100504411401d01d581e58620141000c0c5002d00428029a5696160f024000c2c86000020745c0d524000c2c8a000300099001c1178050640c3da040002142c00803001005801030300858200940c4a071a0181460b00031f100b50348130454107075140ca200e0130003400441c1030500703511400c00c105000307401c00c100c00c50100380900b0740580c100401501a4451507500d031645a0075801140e0f051000408000c2440b01c250400c1000300e01a040031030384030044520395 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 145875809 1250 145874559 145874563
    0xf0102071202010c0303020d02130e060301150315020903030313020109050d050607030e0309030706050909062b30020c19060e06070204090c0e090706050702120c040e0a020411030702 80
    0x14410003810404034480e204d0405200c1c2e010b44030410f505060954486003680c02c00310800c070050081d003a000b40d1000025841d45014010004241203501b9212415800c5882e007054000c90360b5010318545408000031501030b1020402548900d070b244940c84403041c00303440018400302d1b440e40b08030701c10244482204041a030108086401c40501e080000e80000304280032400c0d0f015003512198980140c5d14000303085c0c5c0d00320340200f00c03001c07007204d08203a145e890800704221540760345180c2c5a1800c1da10314142d006184ea80c410103416000b01007202c0030110840c0019000388000301106004189a01a80e800940400c0000c0380640d00702d82c0034001400c22000288a1a02882240200001039a5802c050b44401e02254a515005807050221800904204c203407060740e8800c0e544100c0402c000a04c0600011800e101610060f9a48500c1d200c01c80d020441501c00030050440c2902a004d1070f402113540d28481c85400f0250701c00a06140d00503401004200c4a041c820700416100c1001000300103540 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 145877059 1250 145875809 145875839
    0x501050913020a05060a18090507050f031902370f0c14010509030a080109110a0e01110703060b01030e010605090c130b040801200703020c01030b040e0303040609020f010207 76
    0x903040c1c0042508410780002451038200d42d02030b03604450300181d4401516400b6980c40404d20341d0388040101965260342c00012280109d5070800001e078203000c45802c00200b1001540c2240c51801030101450580d1690001c030703801400072840c42403c040c601c007c03071402c0307000d1642405240c14100d0010444031a000d400b4811404880341003104a40500301040603001200c54542d244030020031261070a04019030740c980c002181d450205a00c6400015409841c0c0910381c04c0c1d0070040c0006041010101040c0c132003940c0541040d0510204a43d0501416400c110010040d80541c801041d0030658000160031500385101c0c0c0300e0750340d04201e0240050380b03580f8009a045124040c00d9590782c04081c0704c0d003041c0c8825400c14102083d000800103018041500511420420b510b00d40d000c21080c2074443c0f85900c55501c0c024050b80054010394241d41c002e034881312380d49202030008503152040089203805c5a1089904491017581d6519060550170035400741299040203000400f0000d090021031800110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 145878309 1250 145877059 145877071
    0x10b090a0305030c0607170c0403081b15010303200606090603031303050d122306030111040603140a0507081b0d05070c0510020306012705030d090f0905010509 70
    0x11001800141545a804540008680080c2900d44507254401e2054440500b590042c002a062120050304041000c0b4598000d1a0b18940507181c1407466031201132940005905642c51b0010054442e2001d40a0181400c000d201d03014011035981035140241900401da200c240340324204040c03c00b120040050351035000f420884007504c407582c4140020703140d841410030b01d880346116840d0000c1004000291098030b150143c031002101107081c00300030b081301c00f06003140c1d5100c0f13101c0c040704d6000250103043d5074001c0e001170000715100c030700302002409551143e031080000030780e103225144074148031561154020350030603000d11140c102148001c20307030500501101040e62100014041040034a0219042c0f400d41d500d043c803a0b4544480c0103030014080c01010344590007110740102890240c0c0c0300b01ca1060302c05840e103c4c00c1a40d51084c03020442907019210303500112101c00802c851360b00b003090317180c06566071750340e0840e072130a06a031813641340644d41c0900302550620005006a5680c115a9607102e8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 145879559 1250 145878309 145878329
    0x61206060306080d110a0227060303070c090c02071e0e01210b13120305040312050702120703020115090b0a090504020102030d0209031f0b040b1f031e110a17040b01 72
    0x186010805d0707030609610400080d0f100008008a1143e0107504449400314140401964002c2e80d440c024903407a072203419402041c0101601e07082c0001502a4400c1186002d5803049442c4103440c0c00d081c182440b803078440ad08203d03182540801150702175211880c00b5011110704042610540c0c40c64010b2200e400741c0040010000c1000034045003990540034920ba0340110780a288440350f034202400601c0103490035000544128811181c800d03007405514000c031055402071265044081d010046034110b4241141155241d80c18210703041c801c0c0c1c4214010f4001a40001001880f0008202408100e548141e00f034900f01020080540c2c0c02009403441041c00307000c00b43e0f650504d6030020b401c2c402d03900c2d210300104000d00d19003000c20b410b9501c000301076181a40e0400c920306860341000080050850b1800c4c14a1000189040c0ac0e4845d801401c841c5542440c50140d800c0c2d22041b003000d8981c1c807800310059290128001c0c0d00d032a404144401c40180c0d440d600784084c00c1c913448601c0c49803014002c8001403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 145880809 1250 145879559 145879577
    0xb04080a050c01020d0605040c0e0d020603070e0d051506030f03160c05120109060e03041a07061b05030403080c090d0f0206250606080c01020307060c0309020604061206060306080d 79
    0x80e40c060740c115070301d0600260086543d80c41300003030035004000c10701034540128540140d00410601408030001103001c010591581d4403610703420416030f83c0c03005160301c08100301c0c4140076280d621010701c03505446100300b0161000442d8190011000315005180303030f100340e0240c0d03100d480e0b40c2008022205160481a0501160301190415250041c9103611941d084041d8070300c1410003070010743c0403c0c3c040e44554001d0001083d446810f40e56400340b03002d070000c240707941c0c001da81c4a484600000c2072090311401000c10b050a107455040813400c6540c4014000c00c500108000405502c036070200c0e404400d4803580360400070038001148503808085002007808030060056400e5549800c241c072065280c484a44c0e568440d015072a040701c06054204903031160500001148150020520f0480040c1c1a0300071030030504540c558002509036028440e085c550b413003081d0409a00c131000180068102929240c001d40d01c40340046003124080d034000c000301890100b0910400d000400c40c0510003002d40f600c3c200ca = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 145882059 1250 145880809 145880827
    0xa060902180325030f1a0c0d2418090501021209010c0203031509040f14010c030b03060106140f1c02030420090c2b0603021306060c06020f0918060301180b0408 70
    0x1628030348410049000e03506000c0201f030b826079000a00004241d00c00c144802d4043c80c51007407076040d4262080c00c0020305110188582025500543c02910280d1400f1a41d40c4081c0ca070703c0d0890340840c2c0c0c41000d1ba0841000c016800400340950b0322001480d00c029841e600d0f2116418450307060024020344140041c4012034180811407c01c400000d422121044114502c8202d240c001c00d150a003c41c0400d0600400c0c4a192502240a81c120b84580c0c94100b40c000e41c030768044400354030840083c220b05505011070704100b003240019001000c100d00d40140d41e41000c1c200241c990f14407001092041d07820900e009840d4450a020581204103040c0e09900e84002a6800d50100307000c03440310b040ca02005c01c0d1440c0141ca5a084201140d0003681e910300c03030f805100040802e035041402410b0219074440e41c840c00142d400d90050045108010480381000310082c0080d20a1480706001803d09101d00306106062400b0721035038151148040302c80001051070ba441c4c400c600d0340100003412401003c200390715 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 145883309 1250 145882059 145882073
    0x7030c030e03010501090c0e04050408031b04090c09030209130c0b03133f020a11010306080a0609020306060f010e0f1c0602030411010c02010e04050a060902180325030f 74
    0x1001d64018001d00003582c4907a4210000c2082d6903001d000200852407414980c1024030444e4001c1d0f41002e0f4032403540e622942c0090a0f91054203507542410820000000c03102002c0c810000c24040341d80d0749400c0e8514500402034183d002604200342003800810501c001036254403070f00c02f00d444000010b91240c0c1d030a8400850035145040140050250f811403210a00a4034820740c3d0100d103a00c5001e50310450300c0390080d074a00402083d80c01603405801400b000c5190014030300d00340b990524022580980b202c100f14100144488101c81498a5482c100114501844180e50055050b500c10413a204900700003401246048040c600400002e80190310f140c813103c006c2c009101d100300300105100c03003a18080e0000d500c100c8050302c000d58581207441c07196200320003a0070003640584d1541401401002000b004040c0071b401e0742e00181c0d55802c001140c00c1d440c00501410400c3c0000c00424400c1c400074141481c031003c0d2540c006002c17a05154100100000c040c03400e0740c6e00002601a011103074a4150 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 145884559 1250 145883309 145883327
    0x503031c020c0a0807060c050c150402240c0d0f090b0702030c030109050609060a060f0b03190c0e010e0411160524041a04030f0302130b190813050307030c03 69
    0x2c40140510000750b41481108801408802d118a50402c4482c1401104440074065158002125001404030b40c0e90a140a1911900540002c0c070b103401480d0100342d041650720910700504903800e8007080d4450203690600020200d0070382800d0540da000da140c0f500a001a0f400e0282c14400d010210307541c0199181003201c034252900180c000c02c8402014100b450795000201e8122070303144191000120300c0300d5540078030030455411a9880c80ca6034180b081d0a005600010031b94480c0d400c0b03810951900711654080c0e401e030b10400d9141c804112004a00040800303130000c00c068002c41c1006286c01988199108840300707450714146c00e82081d100352070039906021722051004030404002c403c5040c0c1100d05001c03903009521440d80c45079602c11742c1c104041d28060440b8050045100143d40000f524081c3e0014003007040c1c0c2c509210312039a210004034503a0b4002c0d41d11060140359480c02000c1c0c1e523030410007440d009014207420080320461641c1300c6907203204003080142080107080d40c140805018003022 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 145885809 1250 145884559 145884577
    0x201060b0a081008030702030705060901020a060c0f02150f06040c02030d14180d1202092809140412030b0604050402030405060402010806040b09010e0c12010603020901080a060503031c02 82
    0xa0381e5200000c000007000900207a4a1403621020031800150069000080b12002a4003602618056243c40c080081c02d41001c075106040d070145214034400035000e4443d8184240140c3c9a1601070b0000500080c64141402c0800402c000e2201c14411100444c0d01c2c42e5502c151b040340d01080e8900c4441d0201d066004450a80b07650900740003048aa0300b40c1b80c1e1030148a440012a00140e1070703000a007031541c0d21120342c0c1ca02c0c081000c25029040d8028a900204900031000d840700042d5140082c105070022383c4806440115501e05006000c2908280646100d500903501c03281254241605e558001010070030000091550302c0300d410099440380c00a5800401e4001d0045490349070a0038403c2d1a144103c1e0102d0019801034005840b0307141500c0f6004840307902a28040d4580e09100d03050940c03400c080c1c000c0302c1080d001d20420080b00d03180d800890103001d00f6640540c4400c0f1000015000d5200901080c0c145410071030244000d0320000251140444c1e40b8100564051807095005c0081c0f05091034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 145887059 1250 145885809 145885829
    0x5090c091801020f1206042a120e030c030705070e09030a0315120302010e0d0302040f031b03080304030c0b090c090c1602030f0106050114090303370804110a0b040501030903020106 79
    0x7174003a810540c0302182c45000306840500500812504c40e000c0c0c028000402d075421006500e090781914803500d40c41007003d248100c0060a820b042e4401072542d040110310015543c00090000c042040c14007030f8000400004031540360f2070810056140d01c902865880c44105503070b540e0880011081242c24000400382c40883d4900005141402406070900c0c1032100702600c600c215040300d081c403900c22034084500d1450070b51010390440c3c0d0303007051640b940301c08a4881d0700c5010020000c144010011801313584039450380c103a1449603150110051800510303610041d080661031000c56204d03130801c2d95215034090441a59501542251086000c8507031019405110700307080d00304840c40541c8030005542c001d0725001c21410603130f80100340d10b11400e07a10640540007884421b450203000b40c105261a01070200130640300e18035001c3d00b0200c0320103400703607800030b01820300340b00600c00c41501d1a5010301041c1c508400490401556a11074400ca1150904040c6d44601035400d01d0310039801100036201801d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 145888309 1250 145887059 145887067
    0x81009060303170f06010905040902010e0306010b040e01060f0c020405181f0e06010803180d140c010806040c09030b1807030b100803390f0706020105090c091801020f 73
    0x60080c0f03c8610043d040c14080b448002048404902208075031144605940320b50a440c00e03d0705001c050204108100e050244559882480342d40034402c81e406050303c0c501e095292840c00303800c2031238090181d00107400d0011450b044444280e208002801d0b150b0103440129032a1144105010030110944404003140a81c0140c01c411912001c44c030000d15403021018800c024030b001a490300c4d103c00b8401c0d5802a0710801120100c1c0481e590240303903016000b040c0070940401a160040d0400744483c6503c1150080c00c0010600c0d070304920380680280041e01d040207110b006a2014044854030301014100d0a000e030001001c983c01100c0000544040d40151190300e562450141030901d400d80c0c8503050458500320205940b00c000043c1c6120034608461201c104c40c000f4005981440c000c0f070100029100040031800d684400c00c4407007128050f10006141c106e240c00701c000d08461014040c2c0c0c005800c907038500849940d41326001500004c003614103642c12452403420600900c40d88544666410002c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 145889559 1250 145888309 145888313
    0x60a0b07031e030b1f0509031204080613200f031014151e040b04091101021e0c2b0f050d0302120a02031003140d11070501050405010810090603 63
    0x10950003820300c415802c6118050389407000d40c1a5140070030300580140543c2c80b880c0d0f01d0350a0b59040c0344034a200e400c00c03510704144140030904186503010301508061002030204107180040003d03036480b07112110350a2440344196100390b20b0401150101d02c21418044900c2d004c1c0e42e07005152140c40d00010120340040c2600a0000c01800240300c840750709645c0140050b01c502007a142100207104001c00109249000181e010b1403049444103003908269251040310f540e85031071007031b900d1090107041202c58a9180d00300091904188083c40701000440389207000188000207045941c0f03482c22256508035010300d000c20210f020450407205884011565004144000c1005140e000ba001d041513400b80002c01c80e00360260706c142c40201d5030f6918604001804025642d0107035401c01c000014a4181d5a82c0b602c4406691f11781e14003c12454204400316400150064000303500701207602c0181c0308586c0b500700003030301900030340c0714050610a4260001d080c5030407001400300648040c038000c1040039124 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 145890809 1250 145889559 145889567
    0x1215100302040506060405030a03050c0a02090a1a030109030e010c0203030904150312020309010504030f0f0b0c0307120b100e01090b0703050409051f031b0806090d021c02060a05060a0b0703 83
    0x10321040e40101d01d804049409810502c003110300303890001d8020201c8850b03560f0100c0b625803141e1000b05183c000e0520030001652105045030046160782c202140d03501000350312103522110580703414480e0703141005500000b41c003c003407029000400d0070000340070300a6001180c114030400c1d0390182e2151400f0b04901e00c0007034181c00781007070784e002c2c1104058000d04060242eaa9100e070f561a41e012440520080000030b00300c0c0b02480b0280e118083c144403014417030352942c0581000740c48040c2074000200c2040085640482c110444c03414144013403082d1603240780420200c04007003014500300300c903a214462103039014400e07080c01088001000c907504c454a050091040d045406444a094140320101750408d13504d660603001c101c1c1c3c8000b482031031031842c1c0c0d5081c9403203c108007110454181d00c2c0c0000f1018000e1120610412200d0058041c80140c150000c0c2000c1707a509503162110802c583d0941b0704d0340c0c0001c030642e0000e1943c01c00540c0e601c0d503500050781702846074031191221074001074100402d640 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 145892059 1250 145890809 145890841
    0xb0d02040e0108011b020a110603060a03050a050109020915010801330801031106210403031d060f010801060f0b07030e130915050108100908090405040804080d0311091215 75
    0x880c601c25940c200c17502d001240c42e082074100c0503260f0b490003000b4a04618089006582240c1c0041c884400203031f80369651030610740c0d0714100b580c0c680d545070040d105608001150f240e0102c0701003030030051502c00c3c000185c00c01c007040c01013907038182c4038181045a6010901c0710203014007010090a486a40c2142c005000302000d010490302c07001c440c403040040c0d0404130192800d0501940e6401d8250071004400e00c910500240290200350700d03061000c020b00c00003103001041140c0c48000d03010b280342400415000304410b038001c28203a03161010410507032310741c00b102c1415100d003c4803940e52240301d81022940f02c5059449164000c801c25a8050306079240d6110721900d500c200c100048120310002c03014101c50092180715219041315050b1101c4421990204034140d10841e0f1117030400802001180442c0c00440d012030b48500c00150500081c0d40812840c070b40f01c145441c0a2100340040031080b0268069081440d02444e80b0680d072800a07a41031000c481c0380100384c4951405450f05104440704150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 145893309 1250 145892059 145892081
    0x703120905060f0d09020a05061306030b030a110d080910050a030b030d020c060a03110309010603031d100c02030a15020319020705120f0c01050c0306040b01180b0d02040e010801 78
    0x100d40340014103040c400190780640044801c42420444130500c3c4501410a400d01240c0c1700b01d0852021074242c0c1e41c040500b600411442e40340d12658207100c8054122428040024825070005403240000341454100c2400710500341c64031048001c403894500020302698400c248e00c00104903414a04a500c0000341103000e4040e03609228041814003810346482d41a01d0383c60058002043c8401e9a040840080214010320321f40000ca440558403021003035002901e00004d0780c3d450792000c1080c10380c81030100c0c0c1244100180710f6951a119000608010425401c2070144000004c1500c00d5643c14861541900d0304806e860400701584181d17180290300c1103900301c072181240c2c07501c0c0c880c1c00400d00c00d03110301b2940a8000d000342c480b80040d1035101c4d00003c4580300180c0d41002169580b1100380a014015120201c8a031740b02d0800404010640340400001410001c0b06c0025030100311141c3c11210450360880011507941c0c21039807121002e40305942002140310104400007a10f0302c0c056005502a00e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 145894559 1250 145893309 145893317
    0xb01020c0d1211011a21060c0318030f0309070e132603040606050a0b0a02061311030f0a060b090402010c03030c031b0203040305010c0e06030103110103061208120f0610120b03070312 80
    0x40d10303d0814406d601d80c10305041c195807050001a580c1c0742c0410045401003010306500e04680c0b07014031028a10342c44201031003c80b03800401441562002001070348080c0401ca107850720789141001e803640a441c03500d24040c0c030129075200c1d103907400b6aa142c0400c44528245002650304e203850704007000941907074031a66000d2483d21800040c0c0d5200d1009032404540c103580039202c50340303c000d44101e004940700025507401811020745071640d64100082d08070030100ca030140595140c9030805008807100b24100a004882c13517010000184e9010f4100003005925040c00900828064411002030400958200b101101864071105054001014000302c0e840b50780240100048044c0c02c44010705250480343c0c00c501c0600060001621203440311240c454185400642e1300c0c2d440c0440440460107040c19600701c0000280d201e03000f0f10f0b40740401d0b4801d04010210043e800d0002c0420740a03a01c0003a054100004001300c4800041150805c00e0000001003c4a0205449090141c008082c9a10b0f181c003203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 145895809 1250 145894559 145894579
    0x1303021203071d1306301106030a060e0705090306060a0302030a03080a0e0d050306130504020112180c0e07110105070f080405010e0f0c040b01020c0d1211011a 70
    0x80344591007120701c140541c3d607410741600c0d0700c0216120b040c0302050b00305070322811400043c40340080c18440c00c0d00400501d405c444812070b450440c824800e5103a8038209056045601400102d2101c03488071050020a0310070590303a03600c40303070580000c0019401c80011911064207114145500c071010342000d038011010b0b5140364869000300490082a8803009416400804200020900816180340d001120201c04210940f824101c1c0d4109000211580c01264011081c08014101094600c0c9424400081001141065000a44034114420f900c1d600d441c0c0f168005082c0e81d0b4084c00c40c2d103102d0340c00030034000314603220350071007a003070b0801c42c0ca03000007440000e400d100e400014003a00d8001c00460b2100c00001200100c11184414020429240b542d256203c2a520110400022404e0108107000e081000b840100700002c0d644a540131604541c40540411882e58485001016032548010000c52a90070044280c4040710740003001d030029440c2c03548047d60400941450035200004940d14010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 145897059 1250 145895809 145895833
    0x703030908100b0a17030f0403050d09080303150f04060503100504031b03050f0708160506040606080d1202090102011401090f05010e15010e030c030703030513060c0305070b041a130302 81
    0x8603900020340540c0803000342c400300941c05400c5d14401c0324400c03030810382e4544002000c1c101410b50043d4400c4496034000c0000103a03d40e031002800028040d09c1c3d000c2c6255080039080301104007004e01c1c0140c400c40304203003051400e589681c011030003411b001d0291340c200d540c01940071008040448094011900c0d0020000d4101146030340e06c90100e5041e22128141000b00213a0b06668200020490340e00c82c0420846240444900401d0110b070b1141c801403041e40741c10301d008030540c0d82503400561280e0050380800141c9401c01d07007a44080c01c00d100c005855090f0000102d01420b110030704211464042c10000c502d51255401010246280392030502140e643c51400c5580d0f40000c0b02c184ca04100800b40301d80156105001d00c40b440e000082c11180031000d0840040d04141d09075004802090001039200341000494003008020309260a09440e040302544001c0c20307038850345100900c6041a58006410002c001c0030b06007060725a92008a21890a2040c00c150041d140d04250050301c507491076a50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 145898309 1250 145897059 145897061
    0xf0f062203090306020d140901021903061d10170304030501140c1812071214010b0303070f03030f1b030b2d0112020d0902100203090d0320070303090810 67
    0x2040d6459a54142c8652540c0c83e681c000f5041403071521202074441c1c516002244003030850394003d160300c800040c0d0381c030304c4000c2c0c1a0604102490060905003480b00402c0311b885904c01c5122450380400c00200076036103640b0060402e60207030704201402225030800b01c07460354001000d001600c2c8904000c02c1400100451008025021900c4890800040240ea01032000b0040032440840010300800e002800c84000d05040412a4003c40c6c286507a4078001c07824444103144609140004000030030140003204003081e100c0c828004003034032150200d03249800301031083d070180100d80b01c003902c100103076551803246107401c2102d050010b00190a007403c20b4100c0c0344c0318111070082c03a1004c48810b00340705207149a00101180145040c180000c806c90b110207140d403400240f6507840803600c002108070b22403040003112075501c5508011540b0a00041480d91100c109001e00140c0604220790070300d1341048418a0b41054440c001507500511100004058010140c5020303240c900c02919180310029010f0f030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 145899559 1250 145898309 145898371
    0x1527040c06110d0c080903060901020919030803070e0307030c0b03010510171503010915091a01080a02010c060b060d0e070b09010e10020304030b0108060f07170403110f0f06 76
    0x30400c0d0030500340c1071a03d5000341c0d1060740841c401c1e6030782814112003000290a010701154074142594001804464a2500400c29800015125000003070305083d91103c118a00006000c20144a901500540f4954003080030100850340140c008911755252802d110150304203120f80c0c0e018040c8048012081c0b4060031480180e060381c41e207a0707500c1303968401c0003641c140c4070036030080e07055540c4080800124600290102c10b140707925101054021092828031001c15450b500c00369052908030041c4810000450513003050f80e024a0310314035496407401c2803402882070440096011200003000c00c00701540f50840d0305512028410b80300e005961b83e0a22046201d40703120030f4001035004001c80603602d080c902d10011034500d441142e00b03280c2c603a580c013242503c2c01c1c0c10910442d44014100510001082c0049510032114a41f120400111840078690200058030040c2400880c1c00c0c02c46030700004110180c03074040b240381265808090221919120301007540c1d480310000300d01806a01044200e20a5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 145900809 1250 145899559 145899587
    0x213140c070b1311090601050f0a032004080d0c0507050a030609030e030c010203091e0409210c03050409050403030e010507050406020606030312071103070203010204090b011701030b1527040c06 85
    0x10722101440c1301040b02840f402072070300e4140007080c81313480b43d1482c094010700841d60300c50702c0000d8100881e560016586a108600720800c0000304070030700012401040080c0c03c201541001050300e1914901342d030070200184c000e6034000016240000600985e81c00002440f4000c0d2038801c2e5a1030040141501c0d00400c41d021405a8810000c2c0300850402c01000280c003131a00c1d074041001c11401c000101030300c1401d442982c4a0b640b44c03200884d19902081c00c41e0150b006c0d8100b001a510706594040c201c0d000314410700780f289994000003800d060094001d40700300014030b0020441071030941000f900a4009008a100602c69103002640909000048070f400500d40e007880c610f65507810340c0c100c50b2089202c0c0f4a41040c00140308110058809001400152402120100d0420241400100240b514010700000004482c0041010405036418140c1259084d0b0030311801c0219000030070b1800c0e40c0e8111505400c028261281405600030160381e0040d4802c52142052655072142250117543c40c0e00f030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 145902059 1250 145900809 145900823
    0x705010207082a0d0c060603050613050d050c1c05071703100602010b13090c0308070c0e060306160e22020301030b0903070c150c15060f09090f0213140c070b13 70
    0x903641924014038903041c0007841100041810740c1c232650b50301d08160341a2043d4015018003115001000024000508403070524500213050000e070b041880c1c7d0752400700d010700420503840c03046031480c42c1c4100211809181c00001d09006288012107010456000300da541c06010081400800d0092042c02005505c10b4010310008040d000042480010030514030100c2d04180c44800c00800076883c50041e000b0381c5d01442100d40340a00d4090a005100b1004141c03501c290050000c221b02c140e026410074031546460700e0100c20130030190000c00c018404850440c1c00c03100e4141c81a02104501c0d80003941a07904c1041c0c8060035451b0181519500d00a03494000e200c3c02d85100c2c244402d4424507010b6a0100c4146041e140c001174507143d65101051015113100482e4603a18107020040260b00c82200501e9111030800c0520a292030340031980c21401c4000f4418001d01c00c00108000c80c54014840b51b100c9010390b4141d6061214014400e0380c1b007490708492803c0e60800286940b00e03070b0301c4c07101082504644 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 145903309 1250 145902059 145902073
    0x80415110a2003090604090f0902030d02010507121404030c0507050d0c090b01020312040b0405100e010509010608070b181201060806070f031802010c060f0c030e06061002120703050705010207082a 86
    0x480341d01612307440140808980d07844080d0405a5400c100c0d00399242c03045c0e000003480d400e010400038088965440c258030418248134040d1201c0900c1d28021381d00070f41601d441200800e0620b41241041007a034041d50784254000000828071019405100455815100400c800c40ca03107001661071b4001c01d0b8881c1003040c0405c00060216698281603640248900c0030f0307454030940755164404035a02c0d0b20b00b03442e20313a54034420005095402d1164501824850004044040c034050000085110340c850001804820b2040e4040c2d98903004407800c0703215010402403200544611050743c0d40e00086400e81e002824800329004c2030350080c429805850920380544489040c550010740e8006c00c181000c59600b6a1080c0c1a070b031286251240000c51303100e50340c020409a03282d0003840e203050b1010b40b17203921607810a00381c1d003a515000505a00020803d80400781c507400c850400307030b40034010180040c0c81c0303500009240042083e00c0c4010071000011a1100300b617400e030310250310008079054400d0b12007a44170303072 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 145904559 1250 145903309 145903319
    0x3240e0709053d091802040b04201602030703030c12090b04060302090d0c030507050f030606090703051b07030e010f0302090d11190b030105010806030d080415110a2003090604 77
    0xe03800031a0703011000c1049041c0d45803136607400c80700d14140c042c0000c40d1140c0c0180462419005802d003001c0101c40074042c0002c41d50078140880b5035a80d440b00c3c071b201d0005031801c0403101c05107080d1045030014191084185d40c2d0a01174140d50050300700b2101180700403200b1050b0350103096042c0070344483c450310b2407c4c5400d03c0d10940095000d407007e580d001c8280d0b49100c0000d03000c0011800034520030000782950500d00010b01415803078140425102e0b0700b1040030071049031a62500113511950a203404203980e01c804031040708007000d04590309650301e00014a001030540184c052040c4600a9039500a01401c81c3c0d0100c04074001c00c091180d10601d242044808602c50a10720b0502d00703001000f04e0031500310346018007180300440e8042c101c07507800800108030300d40c0c000b030100d84d2240c4140c014010724501c0c2c410040c0f500300001e0000340310b0480104892220a19684100c101468901c10643d0341d100d03030308000d041948d8281c80c10411200401c0404c52059011040d81c042c0040070b42040c0c1403900300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 145905809 1250 145904559 145904641
    0x90103020a050412030e030609120f090409020d0302150105180a0b1f081b070503030a0c1b14120a020c0409060f0519051f03240e070905 60
    0x2007a400040000511000c00e440d001c0403140030070030303100780c41e03182c0d4024942042c182040c50087c41d10317070316400046140344800200c00440755032070384e0856a03039656101c050008008001d040f130069003001c0b06030700c3d040426800085c000404440c0f150004d4003aa07a65040083c4585962001821600940e01242d40c5018507040000070700310040002031100c84040f881c2080d80c404501560010b10b2140c28004244684c41e8040401440411054503000c03054413a140c1e280301c080d248603415580c4024000525209503040142c00c24000c1c0c110080c503610f420200c0481e14168910b5180c0c0c0100c500c0c00504800c0349045500a402e2074020b0031004070001c04000040c10b10381415520399460381610a01c40074148140c0740702e0001d11500d030281c541c1d0707a1200401c560380104454900e21b51b1201c0e80506002c404600c0d8100ca1b4800c00141c59960001303d9108a00144d454002d851414842e40c120400303000300302c400c11350302201802c10182d41d46811000c0c140c9182e0100300c0200c0c001925011002002d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 145907059 1250 145905809 145905817
    0x303020d0b090a0c090f0f050d11061c0b1e01270e180705031504060209090103061b021504111207080303251718010f0b210309010302 59
    0x41000003070201c070098041540810100ea030100c042e40d442051009a17500240d800d8080d0100c40901000c4908000c1081e03408440c90080c20320651080301644100010701030704030741101000d0404d58951401a42d044000c514441e6002c0000e4102070036200d00d8181814455121031144c2d441102d40c14000005440b1382c105168001c041030071b050420b0040c175007801120001001941004540ca1900c5204803018030030301c0340030b2981c0d90020003080200b84c2d00020300142011842c81100400c0d01e6524041e002445010056a0003041d194000010300007282d0200802c610010b800b60031501c0ba00c101240c481e0410454070003072030040030101e40400c60703420003448041e4000e800703000c00f2411981074a00e03120442d4004520340d44000300300400300d81a8040500c208201c034100f0000c0c00312502015280420b00c41941c21000d100310006400030b811302c0f458982c0201c0c414000c000d0a200341d40207002400800881030301454401c0c0840002442c0784070541c0958120714095820503442c3d000440103540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 145908309 1250 145907059 145907077
    0x5040b0105070605180105160c17071a070206060d051b040e06130c0609081506150d050a05090607020703140313060c03090806270709050c04090e0a020d030302 70
    0x18000c2d035000a81c144152030064400a103460b004000f4001546c2c01d5400007080510f00100581001c559103401c50200c00d80303e584071412a9a00540c81380f4004503004101c00a00102034040d42d009100c0424010300b03004004c2e65003500c0c0c2035070300c0f03406201e5440488070004203d94455070880b0844040a051320310186030040c008600c4118800380c0c1450040141ea0f084642c40303002c204102040481d070100d00080c900d03410308007110340c03800b010107403a904848000d035110341000340040c2c0c0a6a4562004c0007001b64a01c2c55a215800d801030300700148404c880d00080c05160001140e03401d41e001030312a100b0089030380100081ca04640d125003101003102011002440140710003072100c1440d0003e800541855502c10b0700d4040780d07040003000d464403a0300004c00760300f149d418000d11307104801c4140d1220202c0c03005240b114107100042441c002082c0e02803c81c1c14900824020710a600c4c10007030088a04004050164060103102142c42c0d0b4030f280d400070351040c0401e000000290081d0003900c8070705 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 145909559 1250 145908309 145908317
    0xc090606023c06090c0108070905040b0f030303010612060f03080703180b0409020a0e0420090a15020703051b030312360d030e060a02070c090207081b03070b0105040b01 74
    0x180500c001074402040320440c40c0d4075030f0001d204022156504001d940700c0c0c081c0034a011022400c01c800064011080c1c2c0c020107004c5c90719484034403200d07118401d0000c00c03014050122a542c2d82d6400b001455100d0740c3c0542c50142d0f04000c00002c50710a91a0080283c03500000300c54a0004141e4003980c21854449001c00218070000c00010301c4088000508010810402e000d0f903501e100a100030304200c0c3e40b02c0200d1103a441d006031b0312040102264147c00d40d402904016669800640003d80c456200e613002e004040c8440017504c00907503012808600300c1c2d1181044a040465069904085034000004a50541e005000f54400000d001d90066001002840030b18001c04d0418481e241c1c842d000c6040040030002c0048060740340c0b07030400c0100840b203001c2c0350801c0041c11009803507480712805031802900c582c0108000046c40104124440207100880013107540e00994503110586070402d44050014085400e8031592070359011084a032102d5004040140580c2800b08103c01040c0c1c03220128100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 145910809 1250 145909559 145909633
    0x30601090906080a06062304050901090507080a051504030f050a030f180b06030304080330010303020c011d061b0c100305042618010c0b0408070c09060602 68
    0x24482807007404090070f0007030054004820300b41020780a4030a04c0e8401e81c01084020b00d20321240700d42540c1038903001401c42e0049516201c6c01d0409014002c21100540039000c0d0030400510b4440026003402014814410b5980c0101212805800b8100032280038011414016542805600c0342009140d0782c0e0316070500107110222807000c3c9086800340100762854a14201d02542440103000005ea44440704034004c5103020304252105480780952412441e156803404500e030822015009540301d00601984802481d41e52820300964038205c40d8502c0e404a401c00e1041d902c03016841b2441e0703c1c42e20000d803d01e440e0a600c081801c5002e142c0d000d410540b40100a024801a600d0098200d84105190340120b03a40c06e00e030401c04403002d010b514003241802148080c3c0b2003081d110b01944c0c0e01c040c41da80c151450700c401c3e000681d800203810400a10140b00b00f01003104000c119005840201d00980741d00c40e00a442e0004401101d000d4050310380940c0c0244081c504174200101c4640103041c2c2003000c81e0403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 145912059 1250 145910809 145910819
    0x270b0312030406140a110405011409030d0c060b0117010501080612060c0a030e0601030209010e040515010306020c060603060f0c07050f060a1d0109031706030a02130b010906180b03060109 82
    0x2494005440403200c403070f203580403030403d44c0e80a04c07a00c1c2c00901c00030003040001008400c1e401644190b03c605814081814050341b108800101500c0c0200009003d440003062140c0000f850540058012034140b49070110203e01e65114424880a120150b81007208503420400196814400280750f550b108405409201001c401800041e000e071080829154880750401005021780740d100d10007042ca64821401000941d03110071800341182c1d008800c013507141c0c80394100a030401e8025200c0411601003403000004110265004000404805058a020b42c41da20201512014199004001da441c0b0001144c00b031280140108540340c41b8004a072004031504520904120044130320441c12550742500e10240a01c0b4881080f0740451000200600c1c4040d541c09000740143c60780844524400d04e000420586007040075020064004060403601011400094050040d030b019040c0081e005100020300180644401d1209c81200d003a45819142032088a00c51074000401c82e50400c49010300c0011 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 145913309 1250 145912059 145912093
    0x6060c010f0c12092003070902180a05040209091603020d090b01050102060c0c03030c090406030f0609140d021b01031103040f060c091d0a0b0a0b03060a270b03 70
    0xc1c0c6500c420720109041d00c0968019001c40c00e1100703100100750802030a90f000803405141003030316908490f24151310900d044003180ca030481e1900450059440091071496500d00d18001d4004600101c8401448075224414001640038012600340c001c40c2d0b00d2b02007440b903000c1c12090300c0442038528006040207000361106080c1c030000c0030156144c1040c2e200501207960f040c00250b034440c41c1c04500750f00c0c10004821980c3da0b40310041c030410080c240499440750303a039103d8000d02c1c021508280d400b11480d0150501600800075000b0441300b012003070180940701c0d034011894890340f1400390041c10700403809500e6500800c80d0744414504155580b50744c8040120b071180a90300813030040e0854003081e00185803120032100c41c1d508120910480e10000c00000d194079500860b09920071180c1d0049460390000c440180a03188103131940000c0c54080407031400c408a0181d031186400f251200c6020340d07101c1c03040c0300c1c21000364054418890601588102025150410300705101c001c1c0c2101e1480b144180b60b08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 145914559 1250 145913309 145913321
    0x90105150a14160309030b060a06021e01060e0f070201060e01080703030503090312070203070303061a0306130e03210c07080313050a05150105090610051c110406031b030204030f020906060c01 84
    0x13004120244028802e0242c4041801d81c080000d58011006c00c0c144000a5602c034071200685000c0c40c040100071704140e8081d00710398002d001260b28182a400e02c0d910051841c10115442e200540c6001130018a15002d90125812240c2100c060303c0c985007151000c9a59610007040c158a601c020000210146041d03100d17244504c040794045c544801c000c1c038004042d55444d030300081618402d09281c11100041d48112508160220b81003034200300181d003090f0150a000261803103500000c5047e015206120a01021020f00360014007010356401520341c0107809031100142c100780080c400242817103001522401145d0155046a283c1001035039454600f940e01c0b0384141d80c100c3d1190040002c0e00f865100a9080602100d07404140010084000c1c00d60141540800e22031103045000d1045002a91188a040724a10b648070368071500c41c10040c0c06428003005e00d4844d0740e4003c1c1c042c01640d00c288291416070380c1c003c0030807600241a4003041000c0c1d102500240d0b00c03203410411f407103001c00700340b00e42 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 145915809 1250 145914559 145914563
    0xf011a040f060e18010b0307030506040e0105090616110c010c05030c0d0513080109050d12060314010c0e010c11090408040512010b030d0f17180f060105090105150a1416 74
    0x754483e10600d8061080595440c2c004e040b6580c10b082c018000d400510050340d82c0841c1510b800070380d680c6c802000502a100c041074000c180c3d481c013021705c070036010046901c0e4410440030711041045c510000007140c1c0240d8503034403030407507410424940100350f2180d451113103290300079012203050403041a40319007400781140042d03000c560001a08588407160884030002003a60100810580c0c180c2d0f00c074141c41d160b203060054204081d0081c20039255074254441000703903030000e2103c40d0b85405090010700800c500d0040074082104482d240900f58480c41021440940c00050000641510310520540031030107041181d007100300344000300c0c250b120071200c4289205220008104c00f541c000a15003483c9036100004100000250115100c903005010746010340001080403246640b00403a440c21907400e00407608d0b090080310400382408200089882c10f84801b201c15000c542d90722401c105902903c001c011307c05000c01c1c085031807902e0003480d8801c035860b460203440f898900c0045103582800c0c202c81d01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 145917059 1250 145915809 145915817
    0xb1303050c06070201020309130213090509100e030703080a060e0903270a0302061c020309030c0d050910080703090c170111031b0f0f0d0603020112050f011a040f06 72
    0x1001404001c01aa801c10341c01070320b07524501116600001d40b00e10031441e5050144080204401c402c00d4507504860200c182c221004c00b07980d89822000015100655501502e403107005000711101401d4442c1001551101008600d4600b060f035003a07c07981c0300282501c09081d684c610014440105c000c01c2c5c2d101c0c170460006569640c00d1441450060052074070707101c254214202e012100d03a1281a010019240c0448605031109040000c480040740b224803003e601900220901c505042c00001800c44041c410301270b660401c081960440e00e5005072020154030844481d5034401d8940581c0752503401804914001c2060081038072000000d0f0407581c848052245044404500c04c1820720500302c02c0c0502b06111459800d01c0141014007481c84450703503110301030001d809044c8808010444030944414649030392510000700400c0000d084a10081e400b01c1c00501c1c42c0c811010962050380d01c1a82102140e52103642880c0c01e14504000380450341360000d1080201044241c01c000c0c84000034000c2e955 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 145918309 1250 145917059 145917097
    0x18060305241b0904020702040209030a08071a13020607060b092e050d020609181009060e0f0a050613020408030315031603020103150905070f031505091308040b 70
    0x6155000640040070310390140d80b64a856180d000941003102c1d403003e0121005604c422450001500078420301810640c176114594403c01000a840e01400500b4080c1054804042e0b400c5211000700d81d040320001d140c0c0319515420703401458604041c0c90032900400002895003200c1d00030501408080c1d803070803185501488480125210f09034441e50b0160480141440140f0700800700c1c1200109020080c071565011a801541c1e44480c00d10b4035000c0880e00d00c01181c0e041015007a5402d0780745010300605241001004070314550b001040074060584107000403d240d0f14010036200074080606199030244103540003c100b40e080c2c3c0060006400160099980da084c40320324580040c50725412140a070b00103003a0343c520405589a050700700d0707030213090103e80808601c07510514804c40740c0041e9440f61038101072141156001c04103084100c0c2a880030080018160b00c2d0118040482c480d041c0d12030744180c002079203840203c01c451031152003429103d00f07060b1505840b401d190000758041044d03c0d581c86c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 145919559 1250 145918309 145918363
    0x20d0f0203030d0515100e040515060f0706050a1a0d020604180f0c020a030f030c0e04140a0501060306080307032307030c0b0f0c120907030503040602070e09061018060305 75
    0x4071992111382802c44001c1c00424294001400841d1039400c1f6500c260341d14800203d809131207441b82500e82400801903030340c2e1b11407844004180d030001d00c02903c908d0b20b414000f52680300ca40c03144c03003840a003204004054001c40e600b0042180c0204408a1f04090305110009003807100320b10241c140d4100d00e0011070380bc45500c1c403880440d848ce44842e003c542c8020f4240002c00d030040c034a401d1000072481d011400a80880d800d449168490802e07542140c50101071000d1200482074460043e813458809100c142da842000301c5c207a400c907009254858104004000020380964900390818142842c4400382581208a0032a1504120802d030041001c90003544104801c2c0c0c40711541c801c0c00c005030400b01e1b06004580c2c03441400781903180e40302c0c0a900c40c045841c0c1203040003040010b66000c0d0031650307200c0d256080203480740c0300d41c0300b540f0708040b080740403c141381808a403062140d04132154941c0c10902e07121181c0c1240e80b07d0001607600302e0307071a10040b012a405114890581030314441c0d0112801c00e103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 145920809 1250 145919559 145919581
    0x1060512090a03050a050d0902100309060f0b0f10020a0f08040323030d0e0c0301050103030210060603060e270a0302010c11150f1008100f110c030403020d0f0203030d05 74
    0x3040c03481c880d0814034042001903000420750b602e00e1040c2c40c01584901606146100a048504010f5401038201c1c0e190a4000d5050300f22104c03407441031400340140410b1480142c155500c181d06641d2244a1180308681c50070010700c0d203600c41c410f91044a042107071540f500700c02403806010654840200140030f10074030072107140e84580714844c0303171351583c0400c4400c509030b80340c1c000c011110280300d8580c40d40a80e0311108000120f804c1360024000c1007603507520320f0f000c1d54805190f112002018107040d00002c245000c0d00c6004212202d8030380040c0c050b51415131140c1803919071215a40940c00c4202c80c0840780d43c1c1001414122031183d0000680351524010152000c80c04201d2440c1680c0301d0303128040c0260f0080d0704690400281c41c0d81c060300c0d480f1070b0703003020202d02c103600604000d00c40c01d00c29203800e5445401c001d03188000500108a045442ea0248420340b00340074402c4006d0344100410001400c040100200c1d0300d00410b04640a1126035000900b1a40007002c050019602d91007030114a07405 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 145922059 1250 145920809 145920811
    0xc0604230901060507080706061503090b0105060c030409050a0e0706050c060f04081e0f070302070e06030f0d12090807030c061103070c030507020d1703010303080a050f150a0e01060512 81
    0x1201c50880d41d6141607001041c078401d80c1001070502c60041100320412405801c0007000c1c0c10407c940d280c0e040c5d680e02d0b008000b00070070701c1d040d10411422800010241884011521009a02000b645c40c05040100b56406400301070403216140380e42d124500400c030010b01c107490180416540d030700d55400d04101001d1034048081e080d071540c03443c1041400700194146084a000c0944400281c41251b4420341d500f034940034002103103160300e800103a40d004040c0c0c085401c80c185c400070300c030480f0181c175244145695150012440d480c0d81d03010f40d0076001c41602841e05844d110701c00e28808290300007141e49503000f03904500822004102d80a0800c002c01605026641308420780f03401050440c40d0520b03000b42100c0845402900303000b80000c1a1055480340098003254603004411040c0b12010810b038020031354001d10043c0c0002c0c1c49107020440122080c020640a05078410040c2a240c942030f141d03882c3d9807030a403006a40442800400580c500d407040405000b041640c80311500c844c0350710024144920 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 145923309 1250 145922059 145922129
    0x7030e040b0d02091e1611010c080612070906060e030609011b0f09090203010b04051203030112110607141b04020403050d0c0c1a0a030b090f01170c0604 67
    0x4100400c140c140c0e1242d1461204098044514107800c0c0c071501e051958031510340c0c80361011441c1c2c12040000b440b4128141034a00c2c8010f40c1d600014005111120707003203840750303131049002600800100d203007440d10040420b8140303913104c20b4070703861a550580b002c02c44645503c03500201c5e80110304500703285418440c50381e114510400900140c0000c032440003858440ca4288024400c001d01e010030300a100305000c40c082c0110003421556542c603118910010b800511502c3c1c1b1030184814001030407100841506c0c1280c0c000e00c0c0c0e502410320565180b6000d64200e600054002005018020101e00390b5004013010324100d0000d00300c00c038a040443c8100c280341c28000360150b80100820800900001543c1c20814420b00e009a0013044518210203014240d40c40410010358685856246400010081884141d151800c00880c030421040c0b001c40003044410240300601030004000d210b4502e10841c00c080c04403010b0f600d85501c8072000810f183c00c950408140107050352031080c243c404506500140c0c107 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 145924559 1250 145923309 145923311
    0xc12060608091e0304030606090b030c01110601140402090907110c01030212010b030a140a0501060e0a0506030f040c120c090609050906070e01050f0f090a0b03011a0c070503030c0307030e04 83
    0x11800014032a9034500021884190240c28680782d483d5203000d00541d0040e560180040c00000d585c1c89050b000380040080c0c551003070181e100220b1080d03020710202c0d00404a8540a40416031034131030144283d90b25a56020b42142e02000b13518600d076904c0012030310840040c0c540b1901101c41c00394051900d07800c40701040c103142c4100030300068400e816055074110b030004243c0960703c3da030320816000070740381e54241c280d2200300300d00601030070305020b411250580da0180d907851101070b0b80d1010000a600c07a840350070342101003080410720f80f00700380d11003030350150040c21000e080743c0d903807480e0b09640f2603082001c0d80d00f016102001e1047d8038050145030010508000203220030309044d100161079500207040841031100c1d440041c02141d000707009641ca18a0717410103407a03d80701603000460300382e404403d0062161000130400700301100c41c4400c1c0c9061b5401c075408400701c1c401d20f22001c0300d84e60201e20f45541510442074000380350b035010401407158020380d801031510344d180d525015040d00c0d00f21101c18416 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 145925809 1250 145924559 145924561
    0x3030605041a04050402060705030403120e031501121403040801140c07030207061809051005120a0510020f090a0605070b01120f02013204060908120921010c12060608 73
    0x340c40c41d000780020b8080300d0028054030742c0e1000800e1441041402002404086000414814601703004000c40340ea60f1114100c0f403030f2070b50030140c990700c00004144182c10080c0040c0300061b1000d51101400380309140301613242c0c40001c40a86141c115900c0030682e80c0d100c1a41e03140794000d04600710b0b0072840f0000310310700700803c56401035100e04050250704100314050400c81007001c040080e04c4000e203104a01000103040003101410245420f002c4c4030702542c5600c4136101100d6001441040c0b1030303000390181c6503903541415640040c0d03210303208608118100740400d4400f542d416100704010420b030b032125a5208442c0c54131301803140050f4418a00c5200b04403400021401c0e8403400b20f5403503030910342124002c102c41c00900450540e922900380042c7c4690440034101c441c68020826100661603048015035070b0204144d4820b01406a1003182ca0140410341c0c0c68181400110902c0d214a8550b042200c0c0c203903035250031560002000700c00907610042455030900c0a01c940d03000b420b11440c000c001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 145927059 1250 145925809 145925831
    0x9060e032a060721050906040201080c07031d040f0509250311090a060806090c13060b0708090109031502040911030705090f030106150504080c030303070c122303040303060504 77
    0x94035001000442440007201d10403002a0079024103070507081030002c04001d5810080501c903900c0208650407030100d02f03580082840d80c8141825202a41d903d0b41c0c5c2e41484982c1890800c0c00202d00003219508940c442c400c0c030010411a0184c0c0d0b104402070402003100d0001c98002d00c0f419681523020007105104c010060005c0350384012036500040c403e580e00c0d40c4640394160300900a100342e610003801c0f0701404050005221020403001f078610021110f0b4021944880001030458142d0300c5a10810a810040c0c9000641403c015080109050424034615540e03034403140d03c2c449881641107a181c1d4000740c02e002c0d48039140b04074a0744c0c031500f8144504500d0102009842440340200070792054100c4040440d85540035084800609002c4804c1c55000e009004080d0564015006d9921180036802c2c5081c6141400010b403840790020307580300d509000301c030740b5802010f0405104203000c110000c0e03481c0308000114a04c0ca07003400301c0b421581d540c80c40d003820700804032901900418852410315450042c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 145928309 1250 145927059 145927063
    0x130f121b14061005010f0c020105160f020405060405270a0501060b03071805010804110409120c061803051e0f040308040608070905130f021207031410050d1509060e032a 74
    0xd806001814040440362003400180d0b2b10b40900d0703228040d02c0b5424003202d070810980ca5002e2090134803d40d014040d80d180c680400007035030340884000303580c203103a00719204082050302d4455820076005419a41013500da0303101c55096403031319007124518660000038080d4940e4002000800003042d152030f0b0103c41c0c10300000811540e0040c101074029280002005d8090380c940d40b211076400c1c1d00c84081c5d20380a00004c0c2c0a050602610b2040d80c1c49482d21050200410403480b40c42c1c0120380c036969a0b880d003160721000350070102001055180410050042e903001c456014010b00145000d01d01064455250800061010100405441c1041499030341008252201c40b8060000b0990130404907a130000390f01c1c0480240658030125000700c4040702404402c0c0d416600501104901c019031402a0f82c070904000011107443c403c0300d0304a5603004c2040003068610016540c01205010301144503035060701c52038155501c0040100b8140c00004480c003094869a503d224090035034040c4030421084503a01d01c3d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 145929559 1250 145928309 145928327
    0x6190204030804050d150c0201050105011404030c05010c1a102309070f0c020d140c03031e0729010905010512030405040207020f09090105040605130f121b1406100501 73
    0xd8000c0e02134000174010460400110301d820718849004102c8034a10083c003d020304400e01c555804070b2340c0290042040c109020071501030300e800400586070f0354508401100c629841e01c030180d814500301d802409182918802c65802016143d5142e41090b040041020700108071099110680c842007102400c940c40d104d040c7c90b400191800d209090f109140401d544101079030b20000e41c0903844450010070401c1c08805400e40c1d8404400300c8980309400c2c820700da0361344140204104066860b4019040032413580d00185200c601c18a100a9002690202c204a40300766030741c0c51020509400061100e82003034172aa60060401300c0d56003880c1d80301c803014240c0705d128901605018580000711340e0155100c0105840f00324070054910240361074803000c014002c00341035908560150810b0003040c01d5250340c4503200001600850344810000385561400183da4001c40c042082c480600072100c0404481900d04094501502c003075002e2140701000340c0c0c01c04000501180400c00c6818091000d039174071918403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 145930809 1250 145929559 145929569
    0x1110403050c0d020111100e120301030317060f1f111603060504110a030311010b0307030804051e10180503031222020418060f0e0d03020708070b0906190204030804 72
    0x10b0001103c240c00120f4210380c41140e041000e100e02c410030184940d15500c81ca4035002c0d0704040d201c0c5854544507120f000d10003884041c00007013482c003100c11083c10b800c0c04150440c86c000c1201c02d407a0340d440081244ac4203e00348000055280c01d0310b400e4010782113500c0e084561082d402800b910b40c0c0014020301c0c1c00d101804080e00e440d903940001405c100d061004000840c80060911000c26030f41c0c940100442c01c6044840250750910610303064034200040ca410980f580403000c282440d0802082c004c20780d4142c1c0002440c1300d502e2844110030749814924030004c03030b4590358043c18945c0400011080c4411540018000c0e03204004000c914614070305141c5e084190b10b22030070030701c142c1c521481300381c40c50128010394003525049441e002d2001310000c038a5200c3c4510340912800f0701104030310048840011514282e50481e41403006080c0c401d44c010b21006120b00e180c2c41c2407007603503121101295021101003956501c0034040c8140c0020016901c0c9030443d01c401c09510749400c607511408035008611507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 145932059 1250 145930809 145930819
    0xa0302130b0102010902030a0c0807140a210606030c05030f06010e0610021e07090c020105062101060b0301030f020301062102010315090c030c0f020c0d08090a030209040b040501110403050c 83
    0x10700800c40e8802e410040a068009040791042402800d0020312100148200e81440c801d9003000141450743d1b105143c03000d44002c188480c010b00d0301c9014060b440e4401402c6c01d4440720b1100d4000000c00c05d110340400b543c001e51040c01014105018946405a07102813199150700c2303200100803804030840b0545d0700040548020103c5590040d090b4030340aa502020b0702e5020701c03100f1510000c0c10000d40d45080740c032505801d00050103820400c1c0e08845064a40d0b035000030086030400d00d05200b5a80300d10014036408000290141d407001c10346140d030002e070401c0315004200c030000d00551809005100203005a400300d1a400841e100801171b402c0001c100023418141c5a41030051148450807000c001001150018881000356078401401800140d003050301017900f50616000241c40042c0001c0c0150340a02500c1007170f009500c0d049031580280e150603900c001c2040c004401601c030300e00c880340180e12440404045007010301e07105083d5840d64402c48400c220a0004102143e03000401801d10344054038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 145933309 1250 145932059 145932071
    0x6080705030a1520130e0402060d0c050f0703030e0105010b1314010201020d0c020a140c0102070317040503031903060e04020d06020304030201150f0f05040903050a050a0e0a03110f0a030213 83
    0x104100c05450501004c54900041003034100001c21001c0081c803400b48191083e90482d9103542d000040c0700c3c0f040c0c401030340004007400300c0640520550b114040349601c1f410082c1c200251954400342561150744128000b0b52a004000ca0002c001d002d02c50140c8040240103080c11484d00f1748086d03148191145049a0604203140055039001f03504441424040020610001401d40780181d44c504094200301c1d41d89804d40340304070900e4404600c0601c50f03001640680f02c0b0341e165450382c6030000c821032241c9003c0c500810000550f80d404000419030346112049680042c5c0764810090101c1e41280d110b20004d00701d00b42008010390b1010b990b06507250f48042c0040c6c50f610303542812401040e0f20f036900005c81111031070202d81712440000c148202c2da008281110400c3e25031091005545c00c80c480140418000d01c25100220b01070f60141c8019811743c50000107048011000a00e4800703940c3c82174030b5039400000d8079191401e041504104510041c0d9415a000745550b012481301c0b4244281200300d03554400c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 145934559 1250 145933309 145933343
    0xf0c01050f1b010203040309080c01080c0d020c1501061806020a030c12230309010e03090901050d0201110d081603020c0c060d020c010501030b0f100e04020f06040b12060406080705030a 81
    0xc80002c65040312038001c41d20384c0f60174a00036110020078010050741344107a0016a5666201c1c0032850301c030341c1314540c851f824a80d0502100c80a034210305050016030050105004800c982c001080340281250380c1c4000130007101c40d2580c258821560460821500005840804a500816180003555101b0180d403009001040c040f03403003405424429203603d021018000b80d076030b0a180a98050391030040200203211f0f002000c16540e10502c90410740114807400108000d241c200c00407030201d8018101810445440240075040c21501d2074210f010034408400d11404800008844c1c1020506003030442c5001090103040b81c0d241c1005611610940c40002e400100b4141a010f454005041c10024002540c40f4a05540108030440b20001140d42020020304004103d84013001101c0d1880d004401689490302030000001003400744a07081002080b0006100d200c920040c2a2210b0b000c0c81c0d4a07032400e141c0c007044180e410542c0130545d541e000d50000c0c03203196808a03820203095842200c450880b8645 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 145935809 1250 145934559 145934587
    0x9070906051c090302010c030501050604180903140304030903030905060702211e0a38090a0c080d08060909030a1d04020a020d0e030307030e010818010507020307050f0c01050f 77
    0x142040b11200c0e420410a20101034054101a0f030481050b1410322003a0388900510407580a2071103040c501003c0080c88010540781940b1140c0785600a1401a41c1103050000348425a402a50b0840024004040404c281030340070803880003400c02154250310f000c01c95000a40100740702602c101050143d074803002100c04003000104140781d07034200d00100b41410b895690341c44081c1d46500b5149441340207200d9162001e5840c200c01251000c035061340b628a48402d00d40c1d0301d40c0d4010500441842070f840204045080c984420000b01981c00007007a2131009804001c18404019041c1400352100a003440426003001c41a14407403919486e088240c0240e0401c814080b51210f100c0030b801a20019615903030907408240440310b01c105486a8010145110906030749100d000c50140004511400785d90340e0b0f6204d0f085054021901081d0a200141c3c030000b2682181c40c15250702e0056400018000700308942801503440c51018440030b801000e50b0301c000a05184100307496041e982c0b00004101740d0790411 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 145937059 1250 145935809 145935847
    0x70503090c0a121a1b0a021011030a14040302030d0b060403060c0e1203040305060f0612010e010f1d0712020102070f080105060a091505040b180a0213050907090605 72
    0x2004041c41050b5581d409519089401004143c0d21900c0038142e02c140794280310740c0c150084c0c540c29a540100c00085480b0f101c10f4002141903030450041d0004408079100c04d000700358060040d01c1185589040c2007142c04e04890f0004a0402009030744820800031980100940d00e052401c0e03200032550908502c0090350301c1c4a150802041d051411095429aa5004844003c0d089056440f20002640c2010040c0c0e03e0240b4030000b4072a50102d40010b2280300c0c0d8030101a04018080c2040b422045041d202a083d10f02c10242142541e545048550200515009034981d5007422266401e00d01c800a40c401d0312880940540c203010304445141d482164820002c8100030300180078140c02c42611a2003c601910382940d1181c42504d4400011038034031403510a07031008050b5440000712003860720041c00702510481c00b540d84d00100300003139001c4641210000910580b0440d000503a10309031000d961b0500c0115401c040d0082c00428200074802d81c100c49803d09032807450416584030403131100500b2180394 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 145938309 1250 145937059 145937083
    0x150a03060b0103110f0301080706021f0f0b030d0309060b04060b03010306180b0a0507021c050a12061706101a030f0a020904140601020f01020a0e04020d0b03030a1106071707050309 79
    0x280001e0b05d050307108011000780d41038910000584240715034a201c1281e841001c41031140350784204850403101c1c900b099004030a040d21550022070341180410000e41000e0b07041d403482001c262103071008dc041000c03600c40c00c0d0404800b00c50400c15a810224075100500050200811300d40d0f4415200440507802c43c2d400b80303550741c00050101c992038141004000ba00301943c094015104e8800e00042d0b105c5c0300a5802c03041912039584c1d9042c011541c104030340c080282e4175035841d81c60f80c42d4000304800c0c07004885108891021002851075060807040c0300184091740d0b001c4080c201c44414110120360a1034116030304104103034001585602e6544804000f886040b0785541c4c4145442112042c42241085141c490742c0240c09548180182c04200b82c280d01c0b4055200c00000d41c0789005060500c0d156000e031184691810001402e202c11f40046880c55010040140110742141071445050000300202980000e10340f420080901244600b1364141e40e0140800c814010080002224944100403003102c1d61 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 145939559 1250 145938309 145938341
    0x30c050409050606071b060807050a050a180b04090204081614091503030a03050601120902100f020709020c0c030d020f070506030408090a0b190903050a020103020f12040515150a03060b0103 83
    0x648034402c648242d06d211f5440852000701c00100114010421384a0f41130480e12001d1a0805200d41111544403045d00e4407030304001d0769804296848800041c02c040e01d0303103000060b5900d04017a441d0b0b141403111b421002008041400900191419082011000d0429900840641c0311180d000004007945074449802d0300c00842c00e04170041c2c0c1a04414040c0c2c2d03007a00c5007900704c030716910700e8070564800c1c081c080e400454164a030030700d4610501c0510004036681c81560072043d00c031081e03d4184d03070003100c9108541c0c1c0b111822541515051040802d0801c1c84d0008103113144001e038420340c0740c205520a040c4030320340110000b82032120007402c480180c40c004000c0c80960b038807101d40d08041d8020f40121440e02c00d2642e80510300350b000351046410307646c10800900d46600c0d140d0045010350301c2841c071a20044414031100f03842c2285111b440d405507100301d01420703105540107150400c08200400e04070443d00020002c034bc0d00c2d00c2e018014001c0d40e0f00a4004100701040ca00141c010b801c28242040d04c071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 145940809 1250 145939559 145939583
    0xc110a1a01052409060d090c050a060207030b1614030a050703060b04050f0f03150408091503150112061806080d020f12030618011508010501030c05040905060607 71
    0x11400c0180010840c0010000300503601c40081c082100c83c0c001d01c0091910004a03240d04000d18400a080c0c0c04000420481c90402c107050a682514a010320483d19540340300814003007480c0a0131403a000e00410320003029114a1a21506014500500000b105141000010b00281d205581c40030b000d40c031a1002954a040851f1480c0091904440c103000091502c0b80100c0c503400200200c030220752000700540c54844009041101c180d45011801d545841140f06404040010140c2a48210b004662443d101c11040c4203108064000340304505124070100308028076800981c0700c5800c1c115003840d0458084103404100c800511190b0000c02088407280105401c3c010030f038100d04140c54071003013a00c0e42d070302c0f00c0b80c4243e948218002010307080750400703445c43c01c0004241c40610f034001c0004020714140c500b42811049084800e811088040075185c1c00081c655820024081c010807081c0780800011181364002407140c0034501603220010345a0001c54a9a902c0c0c8081d0f03501203401c1400382800c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 145942059 1250 145940809 145940813
    0x4030602030906091606090b032a0301060f030603200d14030403021e030312040602090406060e010323070c17180102240f041509140f0703080d0c110a 66
    0xd82d8000302c07044138551285549411070104549003041c02c441c041e40ba0241a103041100f00e00c035640000700148500b0000300e041004000300d900d07403020f40040c490081541ca5052075402020301c076030101d0341c0d4145400c100c41080050018800c50350161441880107000c58125400214140702026001e800608003030241c0030b014a0100c001c20071648221a00d4441d405101080c6203180d0b0315500050703064101740403270040c0d214101c00b0290304c40d200e03043c014030303007085072000400300d450640101740003806060782031300c81e942c240c406ca5001100c251040c10304900991005403041070300030030b68401c0007001500d000400080c4d1801c100c41048101355580c940c80620112903840c0c6200782064014032850041e40413500e003c0c1107003d4007807000000e201141c2e44070403803035110b2100644110744515511010749601c1389240310f43d5000c28852020905404c100e50308051a0104038103032041d01c0d0700011003c100207100d200844824920300c3d080821035070f0851106848114001d060b10203903000350200d44c0c00f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 145943309 1250 145942059 145942063
    0x120201050106110a080306040903120614120a120e2403090105241c02030d030504050c0a050d1e1202010c081012020904021c0818090624040306020309 66
    0xc10b84409a41c0c0c0c0c240c00ca400b000d0159a03903242c1d4406003201c0d070100003007140343c101034200100890080c2413901448810040c80c1e0115091a800320030705904100280381c2c0c500e040080c5c0394411240d0300082101206603110100d038001d0000032072080c080c400c4545a003d40b01c40200620b02c4406480346017000d003151710b0718480c0780c0c01282d03400c0b07482d46448004bc41d45072901014801c1b1403050803625007a03c81010901c1811000c107080703540380c0a680c0f465440140d40820611001e040c607590301140c40d0605243c880d140401000103241328500d03c0c0e1051160345c40e01c1c10342c50300a540081540808151000c1c90000740b40400c0000fa00c0c2d0a40c050342c1038080c5405412501901c86256507000d06a5507415540c000b4221600540181d155400e0914025190030701005030040e00041ca980c0c00101c04000030168038031000c41c01c95078000d011440d80f4100e40c10a240c4000820243e074243c0580c54814000b80d004040f00300001da080f00c04411046ca141405001c1e14055903014000310b650341803604140b6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 145944559 1250 145943309 145943311
    0x4061b05031609030c06120207080f0c0f0c01020d03050a09021804030908070501080412090504050901090c15200c060d0209040e0703080a0e010e04020d06050a1a03071b12020105 78
    0x100a0a646459010b98648101001c50850f5000140c4456039424460300300c500c170f140e8510394407405400740040004960200000c000803602d0401c4144da481310382c6007841c2010b001010050140d0803441d8424081d9130085400141511989070000e02030303540002075001801035000181d00b107011000d903004003040b1000000d008600179151000400c1d521040140d5401c00740c042e07640042c5c0c110022400181e40702003240c116082c0743c1052240503869401180c110381040390080d01582d1540314038424410600c803664080c020380582d00071107120b010806010349050b1011426040b07003901e402c1e464a5414882494003500040c00340c0c2d568080400310030080d402c102501485646002e100c060902c030001641000c4951049006003082d018034015544250010039550500c400100038001c255214401402030350490280000c3d40b034201003c0c00340c0038409400c40103144d200c80d00701000c0c0f2014601601e5114081d49015480441a48440c1100140502001781080c0503141103940140d0190042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 145945809 1250 145944559 145944571
    0xf0d0504051e0109060309050307140d111605060f0705010207061a0d050d050a0201270605071803080901202a09041b150e090a022104061b0503 63
    0x4100800d00b4040101e08201e41c001a280402d124040070021940260800110a40182d003a40e041c1005a1140e0840410a8103441841d40103580b8040d011600f10381441d0510400c0c2c0000e00350400f060850105204242c001d951166030081500d410103600300e01100ea0807548034009644510117403904001428060b070280080c0c032511144010350342455456004001d410400030308503600c4101c0b040e01c40e50b0003011aa0115501e13039002030040811000005540305c18003904035074045981c2000c1e000c03114060310090804c880782d5030030354200c0410030010099030b41101e06181d40d03d4a91005a40000824031940f5003400c28200840c04104080313884008030100448140103a018034140790f07544003c012500394444500804940030403640941c07030f420110003144402000e9200c004040041036005200030004020010000d49170030518503450304940610342c103508001e400e408851a8120f00d4121280d4a008400000e0902c0051f41165808465420043c01581a030500080c01a4811580 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 145947059 1250 145945809 145945819
    0x90606030a11040f03030f030c05160c170604020901121a09010212040f0203010501050103020a17060a0815010602010e16090506030a120207091103010509070804050f01060e180615120f0d050405 85
    0x90803412800380c05421172483c014ad482c0e614044000055888003104000140e41403a1021408200844c400d901c50241e00d0303020008101a2629204000b200030050b0442c008013507401c2000c06c00500c150a00c43c0c181c500da04050a09a5a440406030082c0120802c0324281040c00c401c1c4401d00c101d0443d00740351580250020320231603895100540c2607110340c0e0200d0000800820814800300300d030107191900402c0c01045070704050b9039001400e20344004a03004d2080d0030324040c0100140c0340c09114181130500c0b401c000e030038100350b00c00c0100d80c030312190301c00d00f00031a495100140e025a018030480031031941c0120381484001c1080402035650b51b00c0e0040300c29103450007658641da100ca0209a0313040f06d000508004556450800c11504200c01074400c03911403041c168021507020080c09851701900c1024418031062400e0614000410900074442130907070481c009000203c03804000007040280c0c1030700c005050202c0004254a001c00f00d007043c16444c01251100c13142d4641c0320300180119102115 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 145948309 1250 145947059 145947077
    0x4050f0a111002070b030127060e060a0f15050d090c03120e0906060a03090203070306020c0a03030606051207030c020f010501090f0c110601060804030c15050406050c09090606030a11040f0303 84
    0x242c2a613a60716607004020f00c100d8203000411104861340c2d43e0700105c81481038020014440e9000034026203d2903000a4503100d15402084024100b85149000030074022000107800c900c0d1503ca400c51071003a200b800304000c0c00240c03042c2c0410254210713101c01580002c81440803a0341e0b00b0100c440c01e40300c5650070009074480c50b6804052600201a50242d10f0040501e80303000310a100660003404140390403030b00340c010240d00001083c2c203840038014a0f40000e0140400c5082450000c0c22908150484400d01a040c450b05100811018856038090410305001541f40b03c0140181e18105204542441300d41c00c1400104400b60355030441c8043c10b50b84c890900c003070101018141c0340c04514072601040317a4000c100420503076100c4d0400311b0300a402404c10605440e02c80c2c03a05030030302d240d414083e0a80c54484041c40100f0043d841203030351080c140c503415030030a0001e60018142002c050401449414040301090921040b82d100c80d000d40140702513640d4a0f0f0713840f1031600704020944801e50216039401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 145949559 1250 145948309 145948339
    0x1107050c01030617031902070510170a140a0504020f0d0c050a08030c03070602030705070f03051c05010b071113051305121306051b010f1410060903020904050f0a11 72
    0x1580004c900402d44040d50400510708100110000c0130002c290440c41031420001e4161220130603048051034070383d180704940c1054441c160100d03a0241900e8078a501e04000010144203104600342c2000140901003420b0f22980002601fa580081d51141e01000548170320341000b009981601c110750040d60212241940d070130317951703440e405108c1c10340c0324a030400c200d240001a0700381c3c001d55200c0b01c40e0030000c0c240740584e141d4078412004a030080b13000c1880001ca01385800b1900200041c030149805c001d2010f9810805030b111180103001d4002c2030b06a03062610701e02c035500c031402003e240441d80b42c02c1001e45003004602354844a540c6059032580610f813401140c44040b001190354981e204501d5848991919208039801e0b44000000610080b031050041a41c01003030040e1003401060080120b4241c1099010440c000405800c0c180a020450010401641c005c411442200d4040720105800e544070300b001c0f810004c00c251a13118500809180c070080259911171841080b100f900d080c545400b501c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 145950809 1250 145949559 145949579
    0x6020732040c09031e1a0a09050d05041410050d020d060308030f040b070302030f0610020307020a090f0c09050a062303070903030e0108070e0603310203150c031302041107050c010306 80
    0x340c440503250032108005000c8118000c1941c6d078001c60040030001d44142151960f500b451850f40740c8000081c8001400c0028100070361040120305030171150711402c07540440713016241c0e100b812405500d064000c030300c0e0107014090b94000c0d0021338006c99403036524a081092000b4641080781d00703d03000d44034000070aa0081c400e2003074070700c00d0804d00a13580c41d03034072004100200060707440459004c51108000c644010b848016500000b00204400401c000b40b40c40c110009652100f040306081008600c020421075840c2c0342c8250840d10305052144100e40608401c0c02a0707824584a42819030f0004140402070340d000c8107890489000b0f595003603803140d07040300456200c64169000000140d10614404403442c00130002c40d040030080100e40d00c05d030320800b5040084020392040380d480410302480304065040501070301441409850380d440541c50540385144050001400e20742900e500008102c0440d2155881500440f00d2034602c551104d00354940283d8071620301e46158002800c1079000100e00b00c0e4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 145952059 1250 145950809 145950863
    0xe0a08010f050f01140d17070b0906060d02030a0b1f0f06030605091612020910081005011707030203040602070212060402042a03181a090706020732040c0903 69
    0x4c091780030141c80c5102c00400c41c0301c940c407075000d03580c15040011050f42e25072171b80000c1c20164800c00c8501c00301d140c02c808503820450000c00490044030300902480050b80c000c29840540c039402082400e0544900c081c0d94005540960a5840390a4070000800c2c00c2d00c4400c0c8032411074040365818090030382c6540038016440019140312103401c00c40d220382c0c0301d21402415600300403404407200500309801440010181c1492241400210300301c01c0511208011892071070703000c2c14081c01c000c0c1c200040e40d80c140342d1040c0010100380070158040041410025141c0454101d140c004080010a0040400d140e40b140340c180d40882c4264a400c010007000007840501070360f103621081006d03c1038124a80142c000d0b0030300c040c0100040d0300c0340f504a400142d1342203011030031120545008402c0c0c500134070428070300310b550782081085d07501583d0200109081082512440e00d44400c0b105140c00e600100d003420b191000351460390003402c2180130a03004e0750251111003124045c645102070020a11078410000031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 145953309 1250 145952059 145952069
    0x8010b0402040f030f060f021305040b0d0503250f060209120706050306061317010c0813020d02150c0d080910110304060905120423041a01030c0e0a08010f050f01 71
    0x82c0c0fa050400100d65100c0c082c502240c09610003045070861030500c0012030740400341410540e0321441c5c0a20160400d41300341840000d041c0c074840d80e000b040b0340b11503a80b4000c4805540310212801c0c0307210003c81c042d070700706070040c0c2d4000a82c01600c110303841e20f00007179085000100d00620b0b06a00c1603c40b244001041e0b42110003d0312405d10310b8513000300b4440c43d03612000300c000403034012000010341210005811030011451400001c0c1001d2500300041c0316060140022000d4507007414464056a070303800004c10080e0303049070000c004590559058040e402941400129405000e000f0702c1007a8100c43c1151142e40810261203000100c4030500088841c0e07009010a158018400103000030021740c000c2c110207005604590b01c1a100c9a410340b0746034807940156071110303140140250002441010140711b550101c5040c00f00c4c220b1182e40015940d02105480c3c10162a000140156809a540c0e0341c6595005131100d01000c0d220902d2601a18500760901d03032041c60a00010000500c02c00f606050324 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 145954559 1250 145953309 145953329
    0x4031a040c030b0604020405030a0501050108190803010501031802210606100504090c0203040509011413050708070806121203040c06030c0c030309081201060809010605060405032a100908010b040204 87
    0x1821501d0f0918801e500502803508150700700000b08043d6010001d90907043d100e90000320301581020041d45c03c00d06030900d0f900c2031641d0210050f00040161003580e055031000c2c82d0020b91407403224860f4240041c6008040d401003440c5200313078907010f2140000c400b01c41040741203038400e803111420712041e00084104900054401e0109024003842500070b00d890000a1040740e042035195000554114021703400021401000000d0800b9810710b844000c00b001d50055003001180f4080038090203801d402042e11040003504000a50302c2c1c0d65680d20807100c0403004007110450503108004100650054409440401d042200001c600740701e80220f4800c00c0c116a280c0340c69084c65035041c0d01a00054100300c40203d014000f6940c00c002c800c815600a000980d034901d041d050100f40c2da400c4600b00c4e005140a20401c0006200a07240090281c400403044921104940d820206d90030301030590004580d8481900d51503030140d984d11011000c00e451800d0003c0020035241d81c2001300300d1040d4480d038031042d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 145955809 1250 145954559 145954583
    0x901020a0209040503040801050c1c0b1c03031509020915090d02100c0b07080a0e0c09010b0d0204030501050c07150603031e17012423070203100e0304031a04 69
    0x1801c080910b140c1183c41201200c0c03c03d134680c851542074031000c403031a6019202c003103201c083d50100e51503900d82054048108104e25907095001c1095542c20030000441c0c0c5400b88611000c140c0b1a6010b0b503000300110104148240c0c0f10100540a54402e1010b18460b52515a82008655141c011a025010010000600c3c0c00d0a40e0078441c909400c1100541400304108482010403000d2041c10310995055840700720714506210524201e41d01401c04881541c0903403039200441d00c0c4d54039003505480d40144141c1e26148000d0284000c0c1c821600014100e500b0704060003414280341c405000020301c102d8910010b2038800d0300d02c004886191101500151210158401d10030b04510b48404103d00341c64081420101d02410203491182039001d40c51a03004041229800100001c2d03580c000b80080c81d00a4010303084180b4581c180001c0b146507403504078001411011564100000d10409400320f00601256003040d10041d12504a0300c0b007600d200700b0741300070f0846a40a400400b885654040c6500100e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 145957059 1250 145955809 145955813
    0x51008070507080301032607150f0e01020c03070b010b030403021002160b090f0609030f1e1201030f0507120b0a0e0712210c080a050307020a020402070812010b0901020a 74
    0x940100a8404414000104401e00c00706400070000d6020f03601400b80c14030802c1e07203104a021140803001091803d80d030207002c140c001451030202d419641418180116603000b041d0b140d88001c0c042e42120200540c400501c8440f0840044003510241b802103803410503507a40e82440c4080b9100458000b00180c000c080484181c0d68540d02034a4003100c00482c01c020f80b101c0f603454004410b002d4800d6009079220003284418408100720144e413260598003c1d609140c49070741c60000c43e000d1080300009200903da1240d402c0d03504002034076091120002d42d0070555a4a0414607180c1130b64000c295418001c0e48000304000070030b152017031000c50b4041c048000c80c2d42c640c2a45002050b0345412a074050007039810001394004000d0b05c401066010714050031580c6100425000c125001003680004d000c8542c260f40d000c1a04030301962203111450400d0303540c81e43c40002c124100151040000e5009202058042c148402400940760b1b9030314143e0803c8044c1d0721113508003220300403003d40e5801a0311000400700 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 145958309 1250 145957059 145957067
    0x606020a1502070b13051608070302010e0d060c0804050c01030605150c010b0303180108010504060501050406120e0307120201050906190902040f0f020918091c05090406090606020114010510 83
    0x40c081141d8200181020696a01c1c8292207205a40040400302c08040c0075003403240900c4600c0040c0e50000302180c000d8503100095032202a0f901c000f90500c401c100c0000060f8580c4d2000081041d40030808008454013080c000c1c0090505507000d40300c82c410020345100a5001c1d101d800142c541c0103105400c0c1d031103003070040c0b03103583e21481e0b200384c00355240e0300d0120701c80d14100302414031203032010004c210300510725000425880c1d0592255105600b0000200100d0341c1210495080d10914a00185801480d0307890901420130580d0154541c40005111411300000c04000b0304a4a240d6000348201d0b1078044907155558401d4031000d1890a03a807404200c224559403040d00340ca48080c2c40420b050760706030342000c00c44151160000b01d054000030007034014500450345a0402048228416607424100c100c9a40c42200c02c0a00d044248141c0034000714900600666a60440c01881404441e8592010b007005e403259114050141d130800c0b1079051480d1035140c40744d050f00c401900038900b251020508031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 145959559 1250 145958309 145958333
    0x5030f060d122102090d020607081608041a0310170705090112060605030f120d1b110c0d111009030f14101109041e020d060510030606020a 61
    0x16034800a907070034000010300d4070119101c0320a6580c64040e002c03a00078861181d1885008110207107240b04100140c81c0b0703a507442412800329010f0304e00646800072407070041c0d43d034406c40810641c1c484255440c0c0d0100b0000c04007c00aa440b06030100e9005003190784014080c0c0029203654071f4080d4580c0080c0f000341844003000e01d40c01c0c050012642d5540e84c64001c01c3c0b0b04a0f0a070800c0c5603010040407a00e040c807803a4010ba03c010070040e0018414801c50410786922540d130018422510b16000988a0020b80d042e001190501d50f00c0300d00c6184120420400381160350302410318519805880340d41062880c183d6040c0f04003940010050b56581345070030803c0b5680c21000d2005090114528010000c036601400e06000c180c4030710600840d0070305010380701d07142c101c000d5040c2441c94140001c4980391802c0e4401d645080c64217a0340804c018801041094269043c07074180d0030750758404036000d04002200e41001040f00c1068580101d101754100c0118103582c81d9000d45400360340691030b44030029484031204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 145960809 1250 145959559 145959571
    0x103020f0d080f0409020c0c03031204080904090c0605030a1b09030b101a120109060303090e1024080903070803010314101422111332010f030305030f 66
    0xc0c41c030f0070310b081003500c0a98010f5048205159404141c1c880e4510041050314203a1034200c00460800a503913264460118000300002d003850070100d240c032002c1e02d81c3d4110a04440e0700416080d00f071900c2c1c620080190f042268068441e606003c0350b03803401404015000385d2401c2942c2c41070790ba242582c0360240d44100180002c11154005c140019901000000d805c01810f500d225260340d84500a5011070300c403c040c0c112804007440d00804100080e001942038003120000d41d0219a035580c5d000d504d11107410f1562103001c42c030081a5000300300d00c0360a4280c456110311501e605109845900380e09569008a4900605c0110b04200600c0402c0d004144543c80300c8444080303884100784290450282c0c2c04001d1403180d1050203000f441342e00c0412000d11902c101e926445000400c00c0c648a0900031a10005070038000c51102d540105803184c1a08a1130f4642d1080f400c110009000e959100141c43d26864081c118244c20360000c601c407445100403000f165015681c0038255103400ca115140041c0c0030303040e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 145962059 1250 145960809 145960823
    0x604020c030d05040803010f060201110334091d0402030606191e0905090102090a030809040b0a0b0a0e01020d09060e0f030a0303060f1a03010308090f15030105010e090103020f0d 78
    0x181c040d1521080c007030741c4d21480c410402c81c0d4803945040c1e280142400710380c000c0000d590420416002c02000c01c82945d62040403510b01c105401c148110700540b050000078032556100c40030f048003e900d6001810720782114064680711860700c840c0062201c4218080d40c0095040c1c105001040d03003450300b011402025060b030140c410300ea070f9480d14400750958243d90220700c144a1a10700b00716410702441401c3d8400da00c20001c1d440c01000d030001540301c2c1b056000c0284502004103100d8030300c0c0c541d94020781442c48060406500a6250300d000109074000420380000904204240a01540b006c03403005009000d82d200c4808480c1403400035a001005010b807180c1058400701200f42c182d4040201c0c040c3c0901a0f03d00040d01402c0c80f60a40f150354954010007540b5140c0d80012200403080d00c1102d0449170862242921b81b800031001a000354100000d0345d0b0310141d00115500381030141c0000318100e40098a0300526003e0350010b020400009100c041c1d40702c0f034850003142c0740d820051400f2100600c1480 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 145963309 1250 145962059 145962067
    0x803070e0f1002060415021b0f0d0e030a06050910290d02010c0f020303090d06020d060e0106050414040b060715140c0f0d0f020a0c0221061f0e011d06180604020c03 72
    0x103000210000d0394030500308c2990007031f0041c410344481480105d001c050f03180341440f00b154150011036a00e0554a800521440ea5140040c039551001d022030042a400b0b84014044032980c1c0c0d680e01ca0140a06550700019040b01003603010074540f0107400004194103846074561042203460315000b07410080d5059030103020800c1a40d07120b5a034444401491031107100c0040e220040d181401d406c4400b00d40110401d100c0c05001030291542010a0f20200c0388168907084d0104c08000116000e0f12541001a4010002140040801601242d0080008181c0703804000d41c2d080668a58200c2e503055031107031034001c400c2040c0000102044000c105510031400b01103009040c0f40e13009803c0f030b4822401c403800503201159110440c13802411900040c5482001016106600310005450780009048032400340e94440358480c5d25201c1d4201c000090402c0001010305680d180c003d82c401c0341c004081580d0200e1290000b920030300c0c0bc207000c21a40c8100c4466088230307503109018000254058000c014007440140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 145964559 1250 145963309 145963327
    0xa0510051c06090303020d0f0606020c04090203070803131707030c06030203070c0b0115120506060a0e0307150302040608091903140c0708070306050708010305060712090803070e0f100206041502 85
    0x40101d4070f00e14800c1da0700694414800c03120108940c682c0500040c0f03541042010407285a0014000800d89401c41d00040d1059051000907c2c0004640c05014140004201c3d0050303a0440d999180c1128041e8081e4001208110f094a48138103450100800b9015260001d000e5507100364007440d404040c80c00e201152600300c0d1507a0700f00940903800361020441c1003040120546c1d000c0c6c0100266a00c1c48014051801c010002440300c1c020b180515040241c0b16240030b101d642d00b0010080200074a00c01342d09041103400000300654824080c2001040041012440b11000060341c3d034030010300d041c0314681006c5150b6084814008000801c0f0021030240a0149075103014800900100080c400805200e0b286151038000d40f200200007001b4000c06200400110f0070204201c0d60040d8540342c41c00d580900010b0080082c2000d08000d407d4071004420480d030300b6086030380b6031601c07181140c86107040d020b84001c01502e04128041c0e23000681110010500140206000e6185465a403101600701100b01d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 145965809 1250 145964559 145964561
    0x11a0307091205100b010c110603040501090b04050c010905010509030a060c02010e0102040b031902070506071427030601051909050c040b16110907050a050a11070f05090a0510051c06 80
    0x1c020183d8a40d0815282003da40d0090300c228000d0348401e00340a01e0a5200340c030b82100080741010f200e80a050000700080401200390f20117211960f011000c54858100341c18260740e00d00e400d4074402d01082041101040319800760090b592a000010000d111011483c0d9991b4090004610341c00250364032661160000039081c00900054510300c00c00b185c49152140852541481420005181c07910400000000c203401158066000c030250030120074216201c290f4004a102c0d08001040118125520f252495101000c94400290840c11140142d0f211002c1040c10301808008030400350a10404000e4203603a41c00041d802020320301d0031400c0c9541c5000d602030703517880000000920764024000b641004401707601600c9401c019580500c052070030351400780840c032074040c40f00c06210002c580700c00100d11501e0110800e455403001c0c3c8140c0c0f41d42d401040c1c00d004050003007603c200706807000100190b0207440b4440c4200002c841100905162a0038040d4206004030403541d00662a40302d00086111 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 145967059 1250 145965809 145965839
    0x10507051e0d0e040902030a2a0b040e06040e03030615040e0403020309031002090a180209030a03020106060210090f0f030c06020a1e0e010c020f0d06090501050a0c0206011a030709 79
    0x1c03500103800031007640700e0020410201e40c00702500c01e5217441c0c001c1c80507880c0001c2d111081c582c40040240c9030003400d090620341000da80c41c0c0101e5403c602c0c1f40818032103442c2020700210340003010455070741c3d19802c08000595003180c001c141d0550040c0b00040722031500f2118031a10034210400d04c0d1030a5102c0e02c01000001003298142d01580c400545d500315410108480c50207644510421401c002a03603000a40c511014890006150701ca404108148000c503412150702104c010120384043d8558540a806403006200d2507015020703101100b507280700c19000da84242c6a01107401744890701c00f43d0310105c182412001c150100701c100c42c00400004c209200400040710942c940308144000c03024010503007c0031420140c100220308120040c280d81096114520070350403500b41c5081a40140480d59600f61a01c0261000d41024032150030b01c034040d032000780200030342d1005014811000c081030f66901c100780308140420780191605c1c00280201409160018035a2a243d80340940e154428401254 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 145968309 1250 145967059 145967113
    0x30905030c010e070501020a0818011101180b07090b1603031404030305040b06060408060a050c09060406090302040b0409080406110a02180703060e220807020a1205060705030c0901050705 82
    0x90b440c85403000f0701804111200041c0300902c002c189038a403550300c2e95900d00071403a28841c030006140c412540d50b80981c880b542c4158102c0e008100102e24440e6a1107105c0f00290296281c44d100004104a1403041c00d9113420355403d000c03610716203451030000c1c0c451080340c007038182c0402d90385106c20b804d032004a192a50056010759000301d99130509040c0102c0408006d0304c541d106400411042240e440c02213080b96001c0181c08001515503100704500d800d500c9146c50701c81d80000001804180e0036005071461041e00d0099408020304008001030000300c0d20052006040c00c4c1d0140b00801c0b0041c0720700910003e09806109540313081c0455801320720b00358480751501701c0207030601c0100140d856052141100614000038243d00d03900b0141c000303010703040a03100ea4602010105131468207210b00c110450350394907030250800c0950750390b58280101501ca100800c1740c06000705d1000c500120710800036a030086c031240c051940b41801d558019945540b1240044804e0302501a000f010f004800742943c030388003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 145969559 1250 145968309 145968311
    0x906051c060e041b06020d09170f0718060f032402040b0304111e090c070314120712020301050a27141e0405031207120606020c0108010603021c0c030905030c01 70
    0x211400ba144c41428490b40c00003c11540088402c0c68810342c040c9110084a05c0403290407001940c2d540c0c2c0a051907404500000c06114002c00024800000c013031003c00409050020000141c8030f10358442c20306000d200262003a00c41c50410368401e4100700c02d0700250102e000f401890541e5034a68820b40b500110b400ba00d1303100340b40703485007068181204003c048a8005200e121186413850010754103d00180801a4065010030362008250085c0b02d41c1002c0c031104a1810384030620b04425030100d080440b084000200015940c0f103400c1d066009880c140c030802440304664506114441d02d48813a003141c4046014503065000c0615040c40c8039500740c468903490b40303151915000c04644030041e102408252041d00580c10000410300c0030081d6014209101c40d03004164854003403c5859684c01f1185d144010b240c454001602030300020045885c01080c2c0707400703000340c0c0c1e80c110580407030007a0890040010000004070b222035a559020710100030450400007403e02c490f031951495a080b8030079191150f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 145970809 1250 145969559 145969583
    0x3220605010312231c0203040b0114190605030a060b0a030504020f0f030703020d03020f06011206050709050d06090501020c072603040521010b1201020a0905010906051c060e04 77
    0x11100c00d84200040728128200380741043c4008061040040f002000a108020042117412440301034451640a0428100c0d056449007011b05014000d20f90a2050684101c103d0303c05440900f4401003415020011b03071340a08803c1e00c1c05a0982e455070004003e01d49260351014042840307400c0c140945101e5140366400030321845c2500c180710f500d2212440d5103101c1c02050b404d580c12030340c0004803070050741c1d810395807106114940e18050785803040c401c4408181e8090075002099490b40181e1154bc40e5000c1c070014811a221114191006000c9010b911f400121812816020800f5074000c10800380c0701d180010300c0d010070a031000f411710900d500141c4000c51044000d00c0d4062000710103410000c903401c041d601d0503140030006004002026140804202021461540410203612464003c4805041c25546051a245a81c000e6005030a060045004950040303029403103084468180d4549032a07603854151007200340c29210803105100c088054a03202c01144c005802142d01380a82c0c494a460346103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 145972059 1250 145970809 145970813
    0x10020c040b0a0b07031b081603020d05130302061c06090b03070b04050307061119060c0305070207060221160f0b130b0a0903050d0e0d022808032206050103 68
    0x150348180301818882c0d0701a440501c4400d15250840355050f90500303146000b40051042c0d03211900000c0000f915031800411802d0800152001d40c0c407030203100fa0f082e1848491400e90596443c001c899000c0b000c0d480040007803006080ca04010650f00b22071801010351050402a90b00079641d854200e20045070b160003055007181020440e410180c244140d010781450300380001310b43e64045611590003004149242122a2041800702c0d1a5075286203140d00c100c52502d08107640a41102942c000000c0d02d4403000800451000c20044143c4c0d00360b45c003900b00c00542c40461a02d2100913032800109007410031040358520303030000c0d40c0000b15104142891072003099003400840c1040c020300043c3d01341d000403180780008520600c40355000c0110500081ea0380071a040488480c043d4404400c4c2451905a0700b00c0754402c005401440142c4540c00c070b40784c100314409210007154003222204200c0d20310100a00001c0d946a01440d070001c0540303054110b031b81c1507020380d00c2da19984000640c0c4856940c070041c41 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 145973309 1250 145972059 145972061
    0x10e0d020f0d0306140603100b04060801030c0e07171807080717030c0a020d080c10150909030c0602091f08040501151d0601350a0b03060a180210020c04 67
    0x80500341c2c90608000c090f180014140024100903140c5101c1c84c0700000140d200c500b05188880600071449945444079195180508408004e020554164904031000140c10f54029420751080d18165a051060f0900c045590f4480300c0150002001c000d043d000c03681d101d0000c1040700c2c01004804024901a032901c1c80340740c005802d074012034105070030401c1032000c1c076640051009091507054070381100020f000c1c24180140d0080020264841c0a1280404131000c56138100154120254040030401541c6004010840d08242030003000700d000103130f0210208030590701400c0c4200002e0014840d80a004034882000701c41d50725010003040d180c009000511400b4071845005100d64110061041c0c142216800341c1e0036181a2805040161070000700e459206604a1309183c03c4d05220010750a1652410b0340e4404030242e480720041050740018015403c18011450303205405000740c406501c4026a200c06000c20303070781d2a120000c0c1c21494100603241c4c1003039816011003a501500240310b111003000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 145974559 1250 145973309 145973323
    0x203010509060a15080c040f061e05031b030a0209040501031209150801170106080f0d0e0414160201181103010b0108060307140102100c08160c080702060c010e0d020f 73
    0x10b01440d01e0f03c0c0203000c58904041d00c00d0207078225080140381556500c00c05a410300c41c0307800038502c0c18001c1034001403aa8100740303890b29001003a00c080988618901045850303000440f0240c201c1c4030703034550000f0f0075428100119004180504090300e00030502000c2406e0301d070281e00c110b400c02010405c1c4005164032041050107000303071070981c001074a2403000082440390180115034070207403407100f8074904030f000350b00c030800408083e420b0796060741b03070009140d84802480342740201046104a9000c86440c1c984901c031003140d100300c01c1c50800c0d200c010300c50700f180190b801c0d1201075650b144082e104450303071000900a030394801d881c80301020f405441410b0a407107038614014140840c0c43c09001c8169004290401928101d001c901c80c0850280e0040f86008088819910080d14105001d410207511154084c030030801103808841d041c00ea404100c6001c04003610142031080280841401071604d00d0082c207000c11014000f01d02d52015440e8282807402803180000076a01140795011105800d01042c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 145975809 1250 145974559 145974571
    0x90105041101080a02090a0602030a020d050c03160201050f04030c05040f0b010e1c0c0e04030212041a0a0e04050907230108040b0622020306010909020a0f0c031b05010203010509 78
    0x2805542410307903503501c6001c1e018244505002443d8001010f250f000d6055504000004140f03049041d50381d40065100e80c8010f0035038005002c0c0244003c0068001c500f12040c14101c40010340c640b560f04103051280600c43c210403030400c00d00300191540414208040c1c805140a07002e140d82503407800c82007004851070051303421040c504214170125a6a080a0b40c0c0038896030070344809000c04260114168003450f4400002c00f94075101c04040394a00001c90090f108500c0794003258000b008185411541340030314420800440c3c1e8190359488841d0b149005482c1d03221580c1000c0c42800110000101034440c1251103140540c002c0c6000c105c5000003a91310512486100500f401c8240d610300001c0040b0002000902180c2c0358402003005500c0e0a00300013005034142c0140c11081e00c182c8401800785d4002d4440d2400102032550100e0700c40701ca8402c4a003440e02a4480b2025104600816580340071184415400d00c103900240484088107106000402c1d44035000069503507040000b04000c1500c00b4000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 145977059 1250 145975809 145975811
    0x2b0201060603090206070f050708030a180807050d170412060213060e06040902180303030415050709051008090f0f0a0201121b2d1e03050708060d11030d080105090901 73
    0x20f408007588410003200e0b805e039048100c2c58a00080350400b545008500d60180300030b840001001d00196510010740400314400e603448035625580e9004242d503500e501d0040a520208e405901d50004048100200141614590486c242039075200c0d41080100102401e030740d1550006071090305a00c22410200c007510b141d0405422142c03500012490a0160f400f41800d000c0c2c0c00550b106240580801d40c1c1c020800080480350340f8036240c504001c5500311032a603070300b1083c108004564224010402c0d40300355800602400025114410304440c019006440c0008501407000c21a60f00281400b00301c4100440100900c400001d0b41300040c401840c40d071104005170b02d880005012860050654072040f010b5207440090030042188009110800c104803a100e100000501e606040d00100c071502c004520843ca0180500f02950550a4a4044a0044c0040c8000000591904d0040702c140001400f82d4917000031105840042450f2a0f02580c8400c003044405004104034542080c155030300000d2000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 145978309 1250 145977059 145977071
    0x3091c0e0102150c030121060c03021b03040311060304110a08010e120415080912070b060405060f0f040e0a0503070b0f0108070f0504090311010218090a09020a12052b0201060603 78
    0x70b12002d0a02060040703801180e682c03807c0c404880d8100c00b40d00700c4244c110204019001113020068000d5002044443c844580840e103110700c180007006a40c204c94205000045070941401000183d81c0000c02c21581407090f1100081c50352140b1803100080c2000354000280b04d45601d80071031400e10701580e184002403041009021043d40c180d07130141da850b96030404042580b05c20f500345003040038143d1040e00411010411006126141070100c0c00f614042d50700300b00c582c072000d00f80b02094000c5901070b41c01111580d009171a9003400c0c2c1c0a0640c0d034200d81d0645807000d034036544042c15a0b00c05841601d08038100c0040c0903040700070102050051803e40020400e80b45803904030b003c000030394880d580c132440d40d070030217001414010a0300f180c0c214400c0c03000f10340c1c8510070800309040d00c6181e401c1d00d004108400026004800521130410b035550011300714041145080c10202e5001c04081044805008401c1c1040392518803a0a003495812540810b840c0c10b1442c2000900b1201664429010141403003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 145979559 1250 145978309 145978321
    0x307030201021903050c0f0703060f2a02010e030c0a050105060102160902090103020f1b0706032f090415030308060402190509010314070c110603010501020d0503091c0e010215 77
    0x3d000c0d009000c03480000c10149100b82002d45481c001d0095031021805400c45171030542601080a0082d0b0348140b0f030800403009d101c80818122000801241103008042ca000302020b00c40c913040004100440c80042103c40107003421030300719048800c0941e03079688078150020030001c0c00c0c05569441602840149038881c0030703944440c0140c690b80308030400d070755000524150991298044560151540111660310a40703c10b104440d03800380310100006025125012402da8840d019180e030f0281060300c1e6181c1c1c0300050100944250f101c021030300e01150f04018210b8140c43e03034019942c0702032110356030030100c62030740c14040d1100b14001d004a108520401c4044031400b0348140041d060300c800d142c030a840c1e0098400507001400100030320300c1200003035810000d1495101000040c01d0744580c440003202118601405800d00080c0506805600003a000d01034280c81400a0340d408000f80d001c9603d50a00070403591500c000344800b0200003081940b8440b042d507010840030083c81c41041d5000c015103001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 145980809 1250 145979559 145979563
    0x7020307030c050f0a030f031b020d0f030f0f0506100302070812040f0204061707080c03060604230f0a0c05030f0606030903070804080606190305030301050d0f060203070f02060105030703020102 85
    0x280c5004090020090454092001c00c11104d4441c1c01c4807002c88025500c1c80c10302429aa0100c003d110020b8246684a00100c103840382c202d2601225400800380c00c44d01d00000e840d2800e0b0302c0382075001c05a8404c0704445004503030040c01090071541c180060281445800c0c80807420030207082409260040060340002151b80d000c40351640e1580c0100301254071640307403256128100d807102a5000381031000100c0c8040c401070000320ac8069003021121110760741e403101901c60841050b041d5060f0048400111a420190002c1ca180c240750501203031029400e410300300b102d0300f0036200c4544a41ca00420040c00c2d004600c12010010f6640c100642186000426044584002413044d40a000080081384006004100395034201b64080c00c0c40b034440c0d0b122040590b8440d8102c0303103584504188549400e40d90f0310480002d00b917035004006140386a0038002805040e66210508545100244200d600850303410320196000304d00300e41e80c010140200e038000a10745001a00320300c0c0b09420600c41000180e0300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 145982059 1250 145980809 145980817
    0xf021b04050a0b040f060602010e0705060d0b030f0a03050403020405060904120311250506060901030b0a091e030531091d010c05130e01230a08010c0c02090f070203 72
    0x4100c501061903900e40311100050100803082caa04a41400e02007003480089030425003d45400d40d000700311040300345055036590741d030078072030345801440800a0242095036600404281c1101400302c42810340c55881071450100720300d00a6000030400f0509004600e42030042c1b0341c2000c000c0f02c5094903030800c5c0e202d00074816111036607101416030302c8207981400d80c415401d07260002e01004210340d01c1d80415111040d05a0400c204441e17a002e10400104c484c0341001d00281600c2d0020010640e5689a0404034000c0180c00010b50384000f132607031007801101c07201000e405018426510346403a000340310204820204850140f0541650900c46e810500b00d410307410804881141001043e00c4000440d526600c54031b580c0b00171700550038a9a4050b415030400b00405010019004a03692603980c0d40c903070283c0e05800e004588080400100308840a90003180c0040035039002020381c0031969031890b00c5404c42d004100d128022910080742c6005503c1c0c503e01040c0e001d075842214260a14120390000e480e481 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 145983309 1250 145982059 145982113
    0xc02100309061d0f0105011a120c0f0d020c0607030b03061506070c12050d021c0c0203010e0f0c0f15090111070806010311040f0c020a08030c120c04060f02 68
    0x20340c40d221041031250a4122042001d00f40015801d0000d03c10041a155190341c11182c4456092000009402645020940c620512460b804d81404200d102041c81c010002e400d801e29484144a0a010121078038000e280c0818410001a62006074030801410060000c1501062516014161103e42c41c0460b55039400b11000f81e55a070000d21040004410740074141c00989800501000442d000b1040c1c8a0441c15a01903800c540c0c01003045803081b650381e040703500d030707094001c00c2c0c1e88201c180c4a01844140c0e503194070050010031049a00803d10386001e4510011002d0750780800c2c00d4040c00c0c104401856010442510141c102041c40b0084850134812030b00e0307043c10051500c2407012440e01c140075844c09000c1302e2080d128a960f403401c0c031b035242020000340140b28600d0040c000c000c9203201d1103102480f400c180c010304009500b64403552100c1d04000d0038060007031820170281103e440900c02c1c2510a4000a040b2610b9500342034004008603065032005080d944020301c070000381070703070402c03582c58180c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 145984559 1250 145983309 145983311
    0x2070303051b01020c0601050a0e04050304031502120a05010f080a03080117010e070306090201030f02090d020d0c170303091002090603010b0d020409050403111218040f0b09040807120c021003 84
    0x480b05550b01001c2d2a0868a19030b855440442e2078440d500000c225541251000c480d07401156803104a504180b4009607070050055108202c2080091061a01e640c1c42c640d80b500d00500340714504612a2201c0700c21a0100000c56460005104180c00a803030140a007600c44000c01203450300d44d4003e05645010301652909008138962103102042c25080031204030304070000d03155100e6607441c4c200090800b0803000c07400309003040703c1020161824401e41d44189070050401070103600c66000d010f0072100d024410383d1100250140400c810000400c50320703c1c0c202100046039a0b1404100550070404005194500d040c01000350441c04e0360703044266030540344c021036096503600f00b01001e040280b14075401410b220b03040c1410032080c10b0300424151005001c00058540e008038407103104400344070704400c2c9140503110013200300b000c2c10254418111444060b00010381c0391904c400103440c0c7e101c1111b048668210000d541c00400403086e8003007043c903c8a040c203444911071a80013511000ca600d413050101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 145985809 1250 145984559 145984567
    0x5010804021203070c0f060c02090c0d1409030c16060c2a0b220f0b07050f0a230c03060a0207150c03020901021603020904080a05040e151f0207030305 66
    0x241d40c0d224070300c031a102034800071255035100d51704e070105948500748203410050404010000c1c54030b01841c080c0c88211f5004001d03031741c907580d10740c2455110f0b00401d0b5001e80d1640e60311241070f544402501080d000d0340c5020f0055858501410140d841c200513440401c2d040c0388560010080c1641058a055405512907984c40240400050071010040c5504c25101c4048a103080002d0020301c03200180500c54040a00d9100003100d00c0d0385070003140307641c0f146c41400015100b00f04540070100014190b130302c2c81802660003081c200400c185c40c08009482c29210445551446c44950180c40341d0402c501321903501820440c0402c40000ba11000024180c0e0040e0383c000810303e080003040800c641e0441c40342e8904000394441407000a00035040402c003e409403190b001091107000c100712450b01241d40c0144181c441d80d4850795103003016004007030280140401804045080a46940041c2c07084061202c85020100340070308000c150170440402d40d40038094040b01c000100c0e40032406c5000c0c4c94140c1405940c0e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 145987059 1250 145985809 145985813
    0x30b0904030f0507150603020109080604030206060f030a0b0115030b03190b0709050d03021509030423060c0304120501110301050d03030b011e02060114030303091b0a0902040909020406090e0705010804 88
    0x11320407440000c140b01c40b02c0c68443d04140c5650f1000b0144c90007070740c03150111078481803507540c0d0b84c0b400d44000c2c0c090307400040003601501e0108042081138001a064038880b0410759111006080d0a0b00081c0d984640960041d01481d8507106071441003038100c0042c103072500b00480c90200d0304031008010b00700944810001d10440d02503000340e00141001f400514404a0317505000b9141da200c401480c80e41422034001c901e100c070000080d1341c140e95010101260310685042d4a50030103212010941c1c1001090050307003c2c2500c02c0c409003000705118010b000000c0f4451610600b160a8803186075580c507000e20040c4000d481d404940803030b16a0505000406046003401615113a0100c0c20840381d48100d1207110344000c2c0e001c0b44907412170781041c201c005180700010030191030b4081101d0722012a4070410485900d2000c01002c1c08140750b0181170403c8807a00d404d06c00007a40c2c050382100d010380d030300c40c0c1124046090501c00c040090080d603104100c686600c290f810f031034900e240b0499042202d0352000c581 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 145988309 1250 145987059 145987067
    0x60408070513150918170a083105010603060c0503040c06030203040c0b160203010509031b0c090c07060f0c030207020916210e0307030207150c050303070818070b1801030b0904030f 79
    0x15241d9004101b454840c0004029076001d50300c41c10000700010750500204000b00c0e10340f41800c845c100d000c50185e01c006480b609038905085222420740d6a59243c00c0c000000c07400c20b100f202c0d024049551810341d41e151504000c0190842940050700b018810410880402c24164810065511401585544d039080d45110101555a00c001a50551801045c00324541000005080d46c4030400c00d26542c0c0c0b24130308140750f256408541c3c0190000507180001d152051410001c0c4a4a40b0074017001450401484180044070700350800d0301e0210340d00040d11001e5140c0400c903194428040105074103002d0000780c0040030307141e01205400c2d015007200c2081410010582007180140e04d00c0040745d8580503a410b009590304038034850300704034402c88200300300b072036118800003200540c105004503d142c0715000300300c484460040403007004108500754104400000d103c0103006185d0104916280c400d9562400c0700e21001a600e981818a0440c8800e8540c603414a581da06c540c01d81003407418404004011303030b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 145989559 1250 145988309 145988351
    0x201151d0604020a0302131401030f09081b100c05120c0316110f030d0501050405060603011d180307050a050106051002070909050705090405010507120b061e04050604080705131509 79
    0x1031f0007900000302261708652110301c10b1012a003640d052103c8c0102032141c10488603000000381203003100304000c090544c40030310200d007102094030071120190000b40c0c050003124244c15060b000100002014008071010b8001e4035003102c00c070407180d0301d1401e01c0103801840001031f00c208400d000d208601e84480d600c0500815200c18511005d990790740352401a0080280424040c0310303c29850200803c0d428140361081d281070300e15044c071844040448200113015201d0040c84034a07103c07041c80b00801114428006003001c2c91040c4010070782c5004a15050f402e641e1550017803402a40d0b181100e560043e400075000c0b08846044200040f07010282c02c20505001d51900b04075008145102884104001540720034812100d5540307201d000c1107004086402e895201c20b206911501c18000201c22030102007a900c07400503d000d130607181c03e540d807011901c20b40013a40201c0c2150071001d410030140c10101204c8030000c11080341085515907140007200c0c007a0250251502e5590b40380080441041c0c3c409182b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 145990809 1250 145989559 145989577
    0x7080c0406080c1003022101030c12120804020a03080408010506040b010f0906030e0f010e0d02010b0102010209090114030a12030903030608060603120a0203040b070f03031419020c010b100201151d0604020a0302 92
    0x310035a84990440c7d16041000e10003114040150f88002650010100b041400c1960000313406520707000d60324084400700c074060001c1c1d03030100301120004005090000280b00500c3d45600100d124a080c03020041110610750449041c01007140310304900307507403010340032050f1441400d000a09078115040d407440c10b00c4500c0000b465603c0c00701500c0003884006000301d0503c02079802400010300e008012400d030302030186569080206c640041c050648405888600c0c104013800700e03100340d6140d4a40301551903011010f280402d40e41c20050b001d050703045c02010042d040200040c0000d0034083c01095540e0910760008030032840102d081803400c3d2003441101c4c010b00f0341144c180d848181505201c06440103100741100800e10381040d0070840550303c90b955102e808221084040320440d402c0c00e01c0a5884a10781003800e560743d0000740401d940340c0320710815280140d400092101c80d0b801c1e540c10881c2054119689110600da01c60035080a844102548030106580c0540c51300c50302c80f01a8060f006046003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 145992059 1250 145990809 145990837
    0xc0d0f09080304050d030b01050306121f0b0f0108040203030901030e0a05030309010f1404030906030509010b06121b031303230a0f03230615091207080c0406080c100302 74
    0x32090502880001460180d4021001e441e01100c01c0441038013100c40605000f4045002032000481d20300c0c10742410303034146a0fa001a94107249014401418007120780c2000c1d280590341e00640c02e502d0420b8480f134ac400003028280b41205090030780000b81c0d04d008604184d0704242d154001540c40203802d0020001c09030388001241c1d01d0b82080f01100b07000e0100700c1d500d40102482d010b118100d001d501c1c207090f0300131900343c3c440b0a40c95080400c11000303420f0040c1926195922105401900d40b100307002030100142c41104403a00e42042d005ca010111403040a030b0700c00802c1442484002ea4041403041441c0c0e5060428402c100d408601c80c88041c4107034400039a51a10202e19006991380100c5525440910350703070200070400f40c907030714800380c600100c840a007900231365000101c080c1421618251810b0405220504000c0c8007400521030308a0110003d506801092080000d444200103404c54a2400c640c14880941000d4182d6520050301c21032a02c42da4114a4224000307020740e040790340041100301 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 145993309 1250 145992059 145992071
    0xa06051002011a0409110103050a020c0d091401080c120405150408070204060503061027110a09121505070c02030709091406010b0a081503010f050106110708060c0d0f 73
    0x8001e4000d2030583d80b207215000ca0058180741c14034203481103039519076102041c143d401c1d07036140044004100003483c98450079804c001516200f4030401041c41c542c070480d52003201c6281030500f030205114050310700506000d500010301040d44070800c01d5840030700c80c4850258596480d82080c52812182400e496031030b14902060005005014008200d0703d03000755014084199070f5000d0550780d0b54101c0308010a40003903813003804407101e12540c0b4070356000000c940c107069941c049421411103050085140740081d00042d400d81894108a4080c000c048c90700910440003880e440b1881c4002859500c49549071742c0710700251000c5e014683c0004150703005421500b0843c0c4401d00c280013000c500c0002c1d00c0c0041c0e01d501c2050420070004a090584803c1141e260815403000e43c01c0c3d07280c2101401c0060032301d12250800195840c00d02c6580b4501d01010400308072549029405015019220604500e40d0041c1c08240314044001807100e4110070041d80281d80c82d03485681203801051101c0040800900f452 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 145994559 1250 145993309 145993339
    0x60f040b0d02090f0d0302030a03020c15090d0807020606060a0302070203031e030a1109030d0c020109090c18080d022a120303010503150f04030c03120507020a110105210a0605 77
    0x5805064010b209440711113080750141d041280201a03c3e0000b00180d204000c00b0148030712940281241246503412140b00d035404255003c41c040003120b6400c000d500c00801d005100da80100300c90f0300440b55001401450030048045040d51080510100500d03400103030890841d24100225000722950f4851811111016458203009500075600020010b05040081121009090880c2d501b07030b070000c004042603801440d0644040b88000c038140e040c1b1900c1705000410b5480c5004094031140c00b0340e581304a002496030b101030300c2e008607000341645521895826428a40001d150845150729080103840240804451810421a40050342e00000d05082010400ca0b0004c00f440c142d400c03c0301a10003c02c5519204142900225141c112940e1200041804603004260b2500558080e140250030b500819001c01d098440c26109140140e00c43c90401e0306004e051001185944024078003586040e86042c0500003484401c0c503c04100031007600400e41d00c01e49030740705000804018001c46a0000a4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 145995809 1250 145994559 145994561
    0x4080409290303040f0e040606030f060c090f060c06050603030c010212010f060e0a030308090a0f0b041104020301180506040f0507120609050c03070c03020a170d110f09060f040b0d 79
    0x10040403241c0550018180c4841c0307404015102558444042c0c48800351a04044c0ba41400002d80103950313040c0e0b034081c04404112055a40300406000340b4020500c5004540018508a89a070028040144004c0c050160a6109000b502c80c030f9004400410f00c2d032a10b0b000a401c52040c51305001280d0310020b807840c60b4079944440c04d412100342e00703807504d616691401c080c0d801090142e1003541c406440742c42400001d01803100e06822000d9a001c41c0c0c009003a03652900c1c0001004202a0b03042400401088204609400c001841d9001a01d0550540d4909401400351260144014281d19265000034145488552110f41c1c002141d0f00188002c1c1032211002e0030038414001d0201401d0b003070100c0840c654060b401000c2c041c1d88420040c40c5503a85114044440424810045046010703100f503d0380483d422194000300411100c143c41d650b003c075002d85c801100d40070400c2112014040c04520b43c0c03076410300d098a00c4500c0965038266651050040300541e4441c54022034200ba1001c10440d2402d221 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 145997059 1250 145995809 145995851
    0x309010624090906050612071704060902040f0b1f0e040203010b03010807090905071a09030d0807110a02090403050a1101061e09090b010501120b0a1e1a0301060804080409 75
    0x725444040400d900d488140b8141c4002c0c0c0506600004100504010b05102c528441d501400c145000001e136011501c010103218025075060750800e031100701001c19880c0600ca04034004d40000d00c20481841b100000c9020b4110a051001500d40f100181d10740450162008110415005004661b20341c0c50702c0b0322803140d400a0244280381d2181c9000800c000d03609106c1c3d10841600100100083c1e45007030341100c1040d04041268260000c248130880f80d0340c404001202c50101280c4036202c041c50008030041240124090f10703a515030000d101407015840c1c0040964000e60949030160742e9880c4540c0580d104841c04d0241442ca40c41c1c643d00091b0b8403440c100d001001c031200c80c03440030200d940f8820801500c40c4288060501c1e50700100411940d8011000400103d0620030045101c080355800600c2c503940c99800302071841039441020f1110040c0510400c080d2050303001c0c3c06181880c4030b440099074001409142e00780064a00491f052080140a90b001009104020b004012a50700c0500c03081c01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 145998309 1250 145997059 145997129
    0x9020c060708090607210608030a0f031a0f130905030a09031a01080c010e010210151e0608130627030201060803040b072d030504080c040b0d02040203090106 69
    0xb0340c00010941c8590301203084c134004c5289680301d4178000e080c404007403101380c1e01c1040040019901c00c1c4c0000c902d902031000d08550629620b811b2201544401e0160036507a507119495070140400030b90310030030340e01c00a1001814000b0b481c54040402440d075007400401d500c0002808a101c0414540b4405038060780d80015244100c1c1a00d0500c1014040e00c1000e50081c0071300c58030341c1c01c800e20320340441d4491400c65200410510495000011000c20003044940d06000f541c0440d680c0c42044c00b15100400701000809822203e850915180580013404d00c1c01c00703400122241001c0c0090024001385400803507025084100d08090003801c0c034920440a0000c09084000d035007800c0e40000c84a20200555048610803e9614508016941d81480e40f0003c80701c0c61684002d006103100404140c0c00e4420394a03840307900d50710354590400342c1c12441c1468407503e4921641c03c0046a4026466030681240a540d06840160700c1e07884843c82240503207466001900724080b00300811654607218500081c0031310f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 145999559 1250 145998309 145998317
    0x12080c0a0c1b051513050d08160f0c0603060905180309061806030106050a11010905061602030706060e010302180c120c1c05060a120b01151b06020912010203060a030b060a09020c0607 80
    0x2965903007e214454001020240007000107000c40110014400019008948905d500281c044083c2d9107551292455402010000c0e0360781505101c080703c1413081c4c07500700200b1080c03c07503d10041000345030f0300e11075024210300424001c5039107041c7e00ba0401e200d40c24407400414035902c030b40e16020001c00f6074201031414000106103031401c498040c0184141d80c00e96801c071024000742c0c0d603014050070074000074810540c11031000b040842c000c100140300700c43c007400d002c40d1a96481d500d10300400035500c001c0420f024104a00303005000c00c0302c24210031220100f200c0c04801400303940310791140500d40a001c8200111040e894a41040c4480c030394415481040e0403100c800d03502c1e843d200d45d114140e01907200180840301410041c01080c0400c07190f84072000662030401003d111846503001803210080c02190b00c9900400c2401c10743c682581a5100c46071480000c6040d0319150001400c144440d1001030080300d841000304101e40c44514400d4054400b100c01991b65480888040381da90b202210301c10001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 146000809 1250 145999559 145999597
    0x2070510050606070c060f0509060705070501020c0306090613020103020c060a0501050406080d05030114040207020a0b12070f0e10050915090405090604020d110103140412080c0a0c1b0515 82
    0x14070300542940c4c0d4031900f19a01810300350030316000303488049801001205000c000d00c21a038545c2e5404000348005441040981140f80c03401c400a480c01140444584c4030707030000c1c41040103151300010150342c00b28003114078a40300030b0031b0b0005900a2188190101c1c02d40200010031150103003540003207040398010b440401c5220f58519031603803603929072086a4002901000102310361884101ca41000803c018401480e10b081170740000d0480e0b5041d4040002c00d000494103013402c03501580c0c010340c41446400c150050018000000345046024000d0794841c100d50400354100c188074500355001c3c60030180c070003018081001d8001110303400210074907204a05003000541d18120108090b03000d00d5004d010036807440590740d61074102d500707107544050400d5514a0a03407400080b0141e00c5020324002c1d2034110382504d00090090174404001c091310540d080422032041110f600040c2d420b0b240b074002c1114072066849030b184e00214841270703001d25445407600850041d5143c18600900040e02d0328200410300f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 146002059 1250 146000809 146000821
    0x19020307110d1409010c0c0f0303020a051501050a210506090a1106040302010e12030c030304030809010b03010506011b05030c03040902041e06080402060c01091b060f1103030718090207051005 84
    0x101410b88000f0983d80e0000d0000710300650054040796041803103030400d003c4030b6450320000301081803164811313001640304509080a0120611100303051200900c1c0d01c1d669036042201050880c40c480c814882c048101507410b03c8100480b4405205042d8040242c0300340303042041505981c0c005045040d5a5406040380c4e0310550300d04141210b0880340c1c181c4030280d02090704410040000e40448100246010800480c00d2801c800d20040d8412407081d15140d1140c149424840e0031201c1030b07250507000341e241c90705205403a030704400d01d1203540404010100c010805481e040e400c0d400f0b5035446521a2002203800703c0c4054098001d0800d842c1c07401000da1500150b050844c0305c1d4a0680324400c00704841c10007080c05030901074020035000c19650004034032028295a2107501070501181304102110383c14090120b141d02800034100d0100c2c46c03a004d1315554a090700c8545a1001406a00901402d0041850314a00e001140700040c14800021502d40d590790030605d80b902c03107111310f00c0403803883e190000d04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 146003309 1250 146002059 146002067
    0x110105040b01061107030f06050a050117060114011812020102060907060507060b04060302090f01050301110c1f0e0d051305010f0e010806040b04020d06081908030f19020307110d 78
    0x210803500030381c460740e080c2d10300402900c2c5402004250080750080040100202d00d001c0900e4680508c90400000e1910340300352514200e40b01038100d0f0300030030445201842055030009415041d203406c1107004100700680d40040c1c0b00ca046d0b20b04100102c21030004005114048400c514078514000c0e000c2c0d03400c90707030b4488507192150b10501814020036001d0040d4004690a82d004589200f00600002440e079140e40000313854a4080742c20340e074030801d800010701c4242428021145c840713142e010968281030807610010749840c4400c0d60700301c50500e24607041c5034000954025001d103d00392070070f80c0c80016124500600c264001003c007170482114040000e80c4d5403084c40c0640c3c80c00021b58400b03660212038401194880700c0a0b200390703840381d20f0b102d0f00003195580380700402c00161030070740002c0c2c040d152001c41030500301e0010200045200603400c24010070031010403a940001c02c0c0c1741644682d03071207040200000070003c010070001807020007000900c0c1c1d0459002d1040c41e4070305044480281c91101c00b16 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 146004559 1250 146003309 146003311
    0x60e0105040f0f060221160206010803090111070308190806010e0a06030c02070e0a0e0705030a0c0e0403090806100302030c0307060f0e0a0503010c05090108130c18090501060602010b01110105 84
    0x4015004502110002c9034120650307806862190001500c0c203214414500006c00041030064002c4112200b84108005440309141b02d6110500144c812585003905c0a6224064104a107061099003498000420230170710a15002e1580507800315190449892030341c81c0e90468500c1c11000c03642e400041a01907024560418481500506a048540c10003800300d000d402481e41020540c1f00707400d80030502c4a281000244103102d03030400040c03040c02c403041c280d107400000c1d4031443c004d03007080000c0c0d0702180c1d82e22075040c20f42d81c088410180e1a00c440c0f40c1201c0208941e40040e00700d000748003c1c00324124070f0203840000c82e8021401c640540003210100764552000d441130714080340124040c0b03890b07240144c0d0700458010000700700443d0150340d03102103401d684a0705010f0000810000780f2a580d0740c0c0100341d0743d0b0080748800490307007190304a0703941d01009141805100c0001c040444241004280c5800404059500200904c40e490381d41c00064080c14200380d0b21030124094240201d010a0144a40f07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 146005809 1250 146004559 146004563
    0x70c0902120c0702040b0306070503060a0603020c0c010c0f0f08071106030712180f08040602011104300f0c080706020f0312060a080a050c01090902040b07170c010e010603060e010504 80
    0x607845032240300302980c0907800b02004a800644508a500c050741d01070111900c51106615000d070759140850420200d402d90b600001c0c103051043c40840c44e030190004086190b10340c2824402c10217441800d00914100508170014408114565211304010284000d4000144a0401041d007090140208481c0d03000442e84039000860b0300c16015a100070f550001d00b0b0b800000d03c010402c10750300b600c50140c40715115030291054080001c042140581c24800c00038500304a84c042130426007003080c0129100b486590a00305580c11858141d000c804500ba4004a181c1c002440300d40c3c807000b403610889407052841100100e0148680000302d20307002142d1403040310141070203540303000c8040c219803404c3c000c090b0116030080341070040443e104008014401c1d845005000500e620b4410800051590859400480c07400f40184002c0000030105019a079005500c410305200c200c800044d1003213a0700460484401c0c941c20040010b042c540113611010580e8090700040c81861100d00c406400d0720019140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 146007059 1250 146005809 146005837
    0x10060801270b04060b0406080f06090706050d0917210601080705071b05031203011442130806371407090602061e06060c03040b030705070c0902 63
    0x42002070360340c0a80da5402880b130100001c50348505408a0100e41582e001132041e948824a10009840200700195020000e8402452403505200005200d03014847c030b10041251030b04a131a0801c0000d0004299091220301c8150301c0e0210382c20000d0007420f51881c0250803088400124050f54030132407030544180c0c01a1a0b25240c02c0182d0ba980481d01002040e0910300d03410352002190a40e028000b40c50f0701400759003020b4803541081c4000004001c1c50086505c2000c0b045601444030491100c405514607800c06503094016601040e0070b5030145101542002440020302d428501e44140480701c00c1c0c032204401c803090343e0f0b6425015070380540300c85921003000746c20058000c0042c0001c0710048800703d0020b40402c4c507882c50080f1141203c01070b0703205408160209010711050b981089540d0740300341014011003c420381d0700080c0c40f6035000039000500035503000500c4c041120003001200e0040034089a926a64581080005e000c1d030044c1100b118091316640d00021034200e1402610652080c4843c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 146008309 1250 146007059 146007131
    0x110d0806011211160c06020304030b060111011806020a1103160b09071809020111011e18020d050c121513150504030327030207030f1410060801 63
    0x30041d2600751041e07071410b10007070301c84540015903202c0034050b007000c2420050911640000707203040140f00000340c00c08011540144810004161024801d5401103c00e08000d20429803121086000d800c51140058500092886400801c22244d00920f4501c0c415580c1046c1900e2040d0700580360b00c80c58403148078840014500c5000b250a0f0b00b03a9a4000c800c4004584100d81d9a11403c0d02200040c8a80e0308015a1080c0a0040d5604003482d14140d00303468008000e220051329042400898501d02a404030350b81d03404100805480720074070004940c0080030340440104d00d00d011540d0300001c091060144105000c0401412000249044d070440707170a040039100e65400c40344003071013401c5600555000b2000f006050355280b80e0b105890040780282d502103428582800c0c02c6107022500c40c400a08508401904000f2a90100e0280c05032640b0035050301c2410102c0c10084041045d01e0000c0c9058082e10020074454540d0f9408032048401020090000746100300000c000e80041c00c02c20341100318080d07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 146009559 1250 146008309 146008321
    0xe180109020a051201060e0901120201170703020c010e06060a0b03040317130614040203070e06150919060f0e040207080406030f06080607020c1206070f1b05150601110d08 75
    0x90040c0450605624016044c1644040b5406200b00203901c80d03401310341090201c1407030b0b043c1091030034090541d00d030100c1c51038030f49076000802c04115203030b504140f0382c50303400803a100074801c1d0122404045044001d203d44d905600c0300e1a221760040e900d01d446010b4981000070604200c0055903ca01e800d500c7c1c0d080790354601c030201609000010003100305e0400d40a030f03102c00102e951090048056038120613604501c1c0c144140351426041e40c1040030704942d40c10030080300d642c4883c00d1f84801c006050640d5110b1814a0100398204000480700208452019000c20394680c0a180341080c0103081c0e48a00d00c0b0f60203401484120302c18800e01400c030000400062000c940a504640c040b00e03031a80000415035521220503040020070303907496005070400d03c038103c02464041401a40d03418480042d04060a0844000d41092030310013480e424044aa40c07a143e01c284a40309445c2c40e10b4005007642d180038090400880300103001c81320240410640c0002c60201140022107100d180f24035121140142c03114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 146010809 1250 146009559 146009561
    0x607050a0f0201152d03050c0607060b09010314060a050709090506010509030a21020f060103020d021201090c1a130e06060d020c01020403050f03132108030f04030e180109 75
    0x1401c071903056640300d00407440b5814491003602d00074580c00540040740050000d10840080301e032000e0500e1800002d0b010700200b0b0000c94141000002110f5044e641d101500d403c4010f0b20b0300c4d072501359224034200000010f1060502c0c66094a08403482590099170b10710f044082102c04c10b84565002618000c001d108071001c951106800840c141806810a031900d00001e20f401c0080300d00319214080f41c80e20000c0002c01640a00c0921281d00281c000e4100100c7d40c10b42e10841444064843e01e4810000d000b55100d0340f0103056a5070402000b444604100e05103409800090300c2062040d000d800000381c03d00ca02d00b020b60313042d80c00500050784514a015450301180c240508540d90201c020000c00350111000e1005085520407a0005a284d501d18180b4508084030100c1c0280d803600308001944a04d074044c0700800540d032800b14600466101c0e04004c0f85407454039a002485004000148049000c84054482c481c520076130b50f41030b10350814014042c1001803010554201501d10005100081d01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 146012059 1250 146010809 146010827
    0x1b0e040b01090905090a0b010605091e060f0a0503070e060909180102090301020c16060306081c050d0204080c0405010f0b0d0f0209031504050106060e1e1201060b0c0f0607050a 77
    0x81450100d0002d0303160264001294001e480310295684001704200401c2410b0740c9440c0140304904045040c905014041000310b640842c0000c0c9886641128148a54a90055a8030858010403140e164242100f01030070640c0305a0303040010400da043d00006518001c0b046030801c00b4050710908003900e0b500380310310500c03500b80314451055400344055003c540302403010b0800030035048020030070845150f4090040303058a41001d420181040814404d0000001d130503102e04034900400460680749441c1221240a00c641d803207549030000800003040d000005400e0741401045904000a03640d61091100200003489158207800c410b0000b030900d441194008808618507100140c90000b203100003e0811120048005451441106100c10b02509100c0c0c00c0240040f4286041800d18420000e010705074501903c14400d0510f4560580c80d850741e460504030800400c4c002d01c45542c42d01c2c4251441d40120761011700a1185500300300c4070801c0010254013414664850351300c1c21660702412120408 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 146013309 1250 146012059 146012081
    0xa060902070f0b10170313140901030b04030203120106080a0f060302032d030304231603021314091c030207020625050318040e0604020906040c03110711041b0e04 71
    0x24004001017005103680001c074807052020143da1b071000d900048860080d0300d074000e0182d01c012a28508640d40381d420b84603041d00d4110080400660341e80c0b404a155100300548005019261000010115004030301940101c2c3c0610050090120442030901107940a10005c1e6056000090403040c01803014940658951100c20070503038400e1b20a90180381d68400d8500701d0f0071240c00310308007012104954031592410030103405405154218840442031001602003e03100e84902c40c0c4100c4042d0540c7d00240450000c1c141c00121490000c090a031540801c940380d4079101080780480002c64824400c54042c103a000b41320741c1c200204507403101110150003140d000701c5d03c0e2114290f404100100b014040c8002c00001b402050070700e035002d200c01d84c0c0c010200300820790301c46000c0c40010f91360b101c00c0d5548650b0913540040c018954900403006401e001c421006114400900c0d0f00900c1202140c0d8000e204090702c05220001007280404041426248072000080d090140ea40305440c03c2c0d081016918 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 146014559 1250 146013309 146013331
    0x6070503070e1809151003031d04140f10030512030406020f0403060203070e060322020a1d0402040e031c02090102070302090f06030c090606070803041a07080a060902070f0b 76
    0x82c20031002c0303143c07180c1c400d01c041d4030030000500704020140d080000040d17801d50482c82d80c1c42c0b03050858440c0081c84843c000101030040d0040c5410324070b4031080c040308074504024414400c010403040c001400800c10f44958a0350150800000c941000584400d000c0342c4d0710070004c220707250740d1981d2151503400c09041250920707000c028800034402c072403000d80302440c007603940140e490922020240440c03806980181c003440d000c1c800c014003c4181c042c0d0034401c168020350343e2007030140380c40007500300c0c000e6811a218500b403442d0542c5d481c480f040d01040c810f500c05c0d2400c000320070071900003650303d000b00294164a00c0001070380c8a044416900030b0140d00e4410300403280320640320342c0040c0d1003400032102406c00111580070009a480d0400c1146083c2c0030580d4128800e0404c0800f14505114a00c0c001d4003840002010170304010141402c4400c0c42c07030820055034107042aa02c000c0001da015500250424244400071908000c2d0344200c4480710b47c040c0d00850780c0110344e03030341d944000001080c900c108 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 146015809 1250 146014559 146014577
    0xe0103090c170325080a030b0d0519061a09060d0602130b030411101211040302030a08030402010206010906050604060c03170108070807060801121103030403080a0201091101050a020607050307 84
    0x41070355001d000b5222140e401541c0c80f180c00303d00e07030b0303414801c01c80c60740c2d400900b80b40c03001c1c0205585008035440303072000e8a000300ba400144008514012440040240540b00b01e6100680045480356807000980c030070441844068a850740034a89810108156540800c50300c022401900d4810f50028900e4402c000244c182803401c0c0c50460012460f0340708058001d000800c00081010013450700381e02d01012107a40c0c0d0000e1201138000d1103240041801501c05a036203800508014030711007550700846d030043c11110610014508000f0940059038224098071403040080340c040342c0d6024400940e41c000c1d0210303003000d160003402c03900e1052229041c0c0a1000d112140048482220341d030f28080c060a80003050a94a8000c2e0f2030f2030200c0907400f640411170480c00500100220130b608901d03064002e003e0842e4080020002815441594801030483c000050044140d0b601074000e590102d01806d24001d5600720382c030040d0b40b04d01c1842e0360103005800000004042c2400385003e540c10541500d803000c14 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 146017059 1250 146015809 146015819
    0x20a121a0919050f01060e0d0b0c091c05010c1b0b060103110d09050604150e0604060207020f0a09140a09030203030601080a061a030f010f05031005060f0a1806150e0103090c 76
    0x2c80d80b01382ca9118980c00c04900500c8070a801440180c03407194180c40704010300809880d0034009000144c4408010400028654031540d11100fa03101102c04072880020307441135a1400034000e1901000140c04145016001d600000b418252114983d402180d04080c41d900c910045000344101451424000c0d42402a0f01810303c0030b00c06c3c1d0244500c01d0000b894507003410b003440070012800d104081d120605000300e41003401030225685810a13400341c805a1540d4091000961011a0407080c07500100101030000f2000d01c075821182c4550301c0b48081c80400d460340c1404c04141c031000e10b405005a403040001ca6002d52080c1d03400360380b1200c051030004445032249400600070303d90074800b010420f0040203010190070301a40765130051800c42070701c405692034200465164503e100850500c02d989200203815910750041e0742d0800c81004000c004c1c90ba403520541c15880b401c540740808042d02d4400e020684c0c44040860060b004140d07143c42032641045c1d4011000b0f03200f0880300700c0d0885925600002c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 146018309 1250 146017059 146017061
    0xc130303020a0201021b01090b0d0204080105071206060518090a0605040612020a0e06010806010507150f0e06061509040e1009030906020d0c030c060b01021609020a121a0919 76
    0x1851003580a440032103140d00009180c0002c00e0311610300310400c40403d1540b071380c010300e11004070b952214080b900d030140510303603000a010b1503102070b01e20750900080240181d0700505040a030142c81000b04200d64461504580c00e002e514032882c030f9051902d209680078a0f02041c19540000c1c421001f003005034950300030070207464480e408107900d00e03011000c0504519110340d0280213400c04803210315261170704000091901030080c003441e0500000280c07110901c91a04c1e490a003500c14058180411315146100c040109000d00542000d0b0140c00040b44440c604825100107000042c590341c5d04000c01c541c100002841721035400c2c4d459204171514041d101069008280c22039001762140c0d0139141c549000070303040c20740980c100c3c0c0030024840c02810000340c000b000c010100e41c10020028038038014000507171811040f04400060248086800981f10f4015001042c2d4481c181d9201c941c1002c12880503019613030131b41b8001c40b00110712220800d903410306000d8181e000c6042002d01281600644042c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 146019559 1250 146018309 146018347
    0xc03090b070908061b090411040918050304090e0a050115060f020d0c08130e13020405070908030a0f11031209010606031a0d03030b191a0f0a080903041715070203040501090e0c 77
    0x4102003400300301045402601c1c1305219000000c00c04407454081c1664cd404e8492140780203801543d6555110b00011030420051605526445002003004040c000c4086e0051440c1b4810303000040d07000c00c90020130501c04200c0c502441203030f0b00d629202d08081e80c4e4851035034216207040d102c1a40050b0002501310240190540105010403420000e81380324014042504e40007000e00040c080280b4040000105c00401c454010760107140070300c071a4900314000c442428004281103114407021079001806905a5910b40c05103072108001c1001030b54445081d0150b0318107484082001081609207885410050441000d25201c1d14001a150301040c0010ba1010800c14591000f08007160f8244038003c0004445a10f0480c1c0c6002d0500300f0034210084101c1d840b600c40c080040003200382c0400c5003810b042042d50003a20342d200da4030b02018401c0a08a940b410200800a00c0710038000100b40c1c0c4500100450301078450683d200104c081c10304007190500c481c0904a49145c020030400e48020300c0e4060891 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 146020809 1250 146019559 146019581
    0x130e1b12010c0e0415050105040b07080d0203070f0f140a080a0f020f0705060108120d1a090a090c1a030c0a021c12051b090d020f040c03090b070908061b0904 69
    0x41c51a550f41101840b00b211540c94000c9002e000300c0c0c034241b000d6a00300041d0f0b011a004884007980d64855481c0040079030150900d09001240040180514107030040c800007220000c668a65200590313580081320340800e001503011801000b00442c01cbd18a1082d459182c2c4000a01c40c0807490b40900b017a120205c0c1e026052407080c00d280070405504102042c81b010b801060640010a20380a0401007030815109110155141075995614402d00311103a00302c41d031015000800100113864100e00344e42c0034001c01c00080b500078405801c0410729600508a4070458606801103e0442c0d40b05215500d0690100482105500c16003105001041d14825030340ca2030406a0303030341c51590070843c1c28142911400f40a40768625000da00403900404203a00b52141c40c02c0899203503015051a001007805079100904441c1c2107030a103070b821681c29415400c0b00b03500301d100b40d044000981e500002201c20101c83c1c020f44c5180c1c0c0216011841c200740400215944901c1007100900e441c000c0c6001508580100d015 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 146022059 1250 146020809 146020817
    0x10201021e07050f06070503010b0c010b090711070603020c1216050d17060108480702120604030e09060105090301020a0206100f1d131a0105130e1b12010c 68
    0x50508016041c0f0414500e181c120f0018041410506d8020b4600d003c14042c8007912600410a0040d00c42d0075044000c90b071002400000c070034200744a00400b03810b85600a50424071a118002800030b1081c0f00f00c4580701d1303075003001d0440d80c90180c200c2030080d030110803141c512840714030314880410018044001840f03050784407000c0c18200c0c99100780080500405140c10700c1030150411401a001080b101042615140200d68a01c0039090701042400d00c0c0514500c40041390503250002c081000003406640c2c000c45007502c5c402080c0515983c0e0701800c5400074001205030400080764189051080e400040506180d4181050640130908a8101c10542c0c0010f9000800380200c0001c0320b03540070040c048010102482074200000d10320300100d1064544110140c0000054074403130035807441001c19511440203000c80c00c02e050200f015074000e000d80c41c42085101c11404c02c0e14540d100760442040903a0242c00c01c0500d0f004414108030480c06001d0304580f0000c0c5201d100002131040701400c0c00c0343d4035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 146023309 1250 146022059 146022067
    0x1305010b100203091801050319081e0c0705060f04090e0a060e030d0c080106021e0c1807080604050f0c0d0e010606031a060f1b100c0c020405060a0f05040902010201021e 74
    0x3001780204034408501d260303880210040c00302d601c0100b048007050145d9580101c1d80701e4640b4040ca0b00d8404c085881c0030550300640c2e5589000c4a02009010b941041070448118030744801c00c1080c1480307001c44400c03044c80200420003400d6459000a0029207d0806a074107402c2c035619110180d461a0940c100c0c1500002040880300ca00d6125041d1812030320702e004d0308550305002d000b0350748074000881c40c91f0545225800a0521204206205159501828ac070280e0441d0320740c41440076a050b620100800c3c030990001d0902d0400d0b01c01e0502ca644182030b101c103a42c4440703800001580c0034500d01c0c20a00d4031118007402641e000d0040400502150342d0004440c901c0404040c81070003055000741c400d14040190150a509403004d0b514500e0030340c1083c4003208000c4190629000085848002440c1403081000ca07141d08507101e0540b4600030b850902582d590171040140481090160035195039520800b0710160406a1180b14000d00c180001803030001543c42c6848100c00349040c21242210000f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 146024559 1250 146023309 146023327
    0x30a03050a0c17130c150206180d0c0204020904020d06150e030102120f100f06020616031503060b040204050402030a0204080c01080f0c1303080310150c0b1305010b100203 75
    0x301c19001e080155143c944500c20081c040100f818002400044440704941c900c43c0502402d11040401442c00d08411103003944c84290180d12a44d003218566080d451080c480a20040301013080c096520032580d94081545e400e40c01c01009401405540760000d50901c12048400210311981c1c024001d207603003840502d550250014104806c904905000f03900510100701041c0d940603002c0d411104807083d5400c2c03039907074440c03017102e510582e130220408800c0802c00041d0160040b814900841d054880c008509002c44001c1e410b8038400c1d01c170300060101100042012580590020b100004028409890155124001020b82e0420759148800c81d60000b820800c1c10300400007031844003c02e00b0000306610b041d8003401460100248035012054000401c000349a80181b152006958030880c1720351281400200d01981c074180d4010b00d141207012803006280c050160f425201800da200c920003020f6a59014078070f6452082c204211015901c8100c1c4030741c0d90b40c45401c2c0151a840d04e034011500c8031060 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 146025809 1250 146024559 146024561
    0x708010b01051201050609010c051209010201060501050a02150a11070c090506040b061c2a0e03011a0f03010e03030f041b0f380904151511030c030a03050a 68
    0x180041410321408100c4000243c03901d03038510f4110b07001128416141e120920050310580d800c000001d1213400754660113090703110090040c20107480700307038000c100060311400152018403448105c00056400603100000b048082654281c1c010f42083d0b020405040001104110b0f0b086840101c503205a102c030184050425840390f640d00c800121000d100c05907d850104550384222170085d4440648000d403007000386195000300d98a18400b600012018505c1d0420804581c411801d8030005580c108000d041c41ca814024880d2800c6580d003c010704032600c0701009000c0107107424254155407500b58003200c0794800e10285216910090101955250500d4148085c9080010250a041c13101909110103050311000d6410754040f0350001910b00d01c0e20500044c1240050038410402b030300c920151060321841406009194425502030116440043c01030301c100000e40240035125030034445c2080001e1080c8103590304001c02d10150307480c0c00d10913901e42c1d0075640844070203804039484005006110402d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 146027059 1250 146025809 146025821
    0xc020a02270903090a0b0a230304120f120c0903060207060b27060d03031b050d0b030604050c09130b09010605011b030e01050906090406151e0c060515060c070801 71
    0x102d4809145004142000201d00c981c05000300c0c0c0803003901142e60060580545118425110701c07004e415225188210841d4240c1d200311000ca4000ea041d9643c0c2d00401e0150440c8101d820300ca480344070070b12462323010803002021034141e01010003000300342c0003011a0701351005103a200e0080101158054458007800104000d0101c950100c02c016059095200212000301e0340121048400610417041d604044019064103841c0142030201c01e64010920f42e000b400404c48580c0311a01030003418050307010961103035800c83e4054602d4211040c50000d9140488915620802030752114080421544450405840c11500460a0780d5a40700512541d80c00004441280e2074001441150100c180d80060007041401d844505101010984100c190f80d103005032042810060410806555034400c485d00d8110050720b14008240407050282c4401042407400d59506884c2d1254414039000f40c4d181002081c00034051020f030600d1000403905c50342c5080c000c0c0860500c0c4001054903a003418911821100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 146028309 1250 146027059 146027071
    0x13050a0203100f06080f06010908010212060901051e060307050c1e0c09190f02360301020405030312100f12020102071e060c06230109060b0f0d0c020a0227 68
    0x7031059000c000c2e040d130180c01c4aa000303107041c0340000c031b0707031644001a1480b14041d00311400950000c9182c40c0d100407414201d500c5030303e04036100c00841e6690028000b614482403004c0840103180d040860a5040c25802590480e6540c50054070300032450700c2490074001c100e01076988010304010700d0354a0020810000110034400c072907101030340c01c0800b10300304000550002c1f0705a4645030340458040d03100b5030741686c04007804d800442c5400c0103405034052030319421071002e0b01c40032000081031803a03050510940e170035244050300031480d0902c042403100312403000800c0c04c10007109240740070074080380f140440402880d0729210204200c0361880060b04000c1aa080114807061180c065450794003520701020131504141411034055000d810080c001d06000385c1c4050a40d41c40b06ca140481041280a1074101c2c0c0d00c0403400c01459807903807101d07411441001a034642c1c001092003000385001c05603018280854141c01107865880141d808608188014040c0c1c10b0030282600303062075140c0c40110501d611407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 146029559 1250 146028309 146028329
    0xa03020111120604050403140310091a1804080c0a03050c0d0e1c02010201090503030f040309060e030d0305090309041a0307171903022b0908030a091413050a020310 72
    0x1910407a0b58840c6034400030a854455070329100410185406070485017800c1100c2034800faa680340c00d800030768115041d0310650509514005800c00d43e0740283c50400032038100144200a8402000c8440030303000700181080d14200030400c80003030007500c1084803c4031240700e502c4060300c0302c400e050120b090a2001e140d68040c001c0c0348400c070103180d407100350198948240003091b09510f40e40d400102e004004d02400101284800000d1102c2611118082da1007240310395070b8104410744480e0102c406810101c07587c2c1d05507006045410883c1e009800c080c2d484410801100d00740000c810000e001e0350750f02024003900c0c2c01c025101150506040c0000f4000d003c04105021107042c130342d0303102603a8002d00c1c162500350085d010840c1c4201071090010360b5200124001840c490052500140b15485c40c0071118404a44411f200280d504000700548484202d84c3e15880003030786c602a16221a609204580c03584840000d8010304140540d00c1402d004000206006072640361502d40004204100d41203040c1e45 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 146030809 1250 146029559 146029567
    0xc0405010909050a06050903090d0506010509010605040602060c0702041e2007150b010c0f03021f05010501080a0906180803010e1005060703030209030c0a0e070e0906100e0d0b090a03020111 83
    0x49100007900a4101754080c20004890b916081c4050550140000c4264841000030ba42428404001101416903104442000a1b6669220213644910485c0304a03805604407000240003400c01102074120346001a00110715080801c803003181d0300340d05403220200c4a5642001502c40191400e0814444014034075007072404074140c54076241c0c011809400225252100750350340f1640d102c0c10000000507402640c0d0314140d00300380b89c040e40310203200410802042410240003051000c41c0100f90484006845194040c0c44800c036140c05481444400c0c1c0d8920f4944840184a500c15901101d203203000c0c00d000e685950400805065141020300640c2d1868800318090205560b00000c171115150715050050341c0b0901d140100c0d04050840c421036501016004000400c11401036800f031241080e56a04613885000004020040c00140da1207a002440002909003141c0900c114112402004014941005040c1c3d02c002d0010012221450960005801c8030200b540900403100e0044c5030b82c45007820 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 146032059 1250 146030809 146030813
    0xf08060703110c0c0609060c0d05030a0b030114040f0201090b040b04060908010905062706160e041505010309061107240b13050c120c030916050904320c0405010909 72
    0x14030380300324a10503c00d020000b408040c87d61003408030364418008074182c0e450490000c1000e001504201ca940c40c00500b00b0b00302c014185810700c60b6403100c80d408840d405040d107071a2600d02c04501f101ca000c81c12b01203034801c0030441c4500307040900020849480b5250361141003500041c11818140e005900f541c0c1414000000190701141c0c240d4070400a00141c034400124104440c148920042c24000a0007000248070b4410080e040d030764410342d060b4940116044080c02880202c80d8041c507640c6030207407008020b004a40c4640c011035220b5024010125002c200d0401c0705005502003802205c5c03080744101c0b58820072540003811000000301c14020442c28042c42c000c1018022108040c41c252940c4e14001b0b58919046401d85400c000262140101445c0c1181c1c0102103900544d4541454810709000c218031808014010081d140007425440f429200e0743d503401c680a5219010280e480c0000200d0001f0308240400f6030002d845090080039481400c009220071210107800501505041c2542100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 146033309 1250 146032059 146032063
    0xa05041e110127090e10111803060603070303030b010203040e0f040c06050c12160b04060e06010b0405011d2701090f05090c01120605040f0e070e0709031403040f08060703110c 77
    0x104845080a011900c4161014034509160844050006c0d80f0715060106c0208107501000c3c1011820350310540300240c40300c1040565405040b5105607040d40a8001800081d100e0f820107400300e10f060040300d0405440e91005411400202d68114420107032004100c00d1281c40d4205e880280050705007203140c50003440003e0340322602d4000106480e800040c40d0380b450a0411121581250000e88112160400d0318106018001018603c181fa22695001091080300c140c00c46045600585910380c02d071003d25440d41c0c19030040c210859001c405090342c85038140c061300c0700001c907408007601620f0560414100008485090016142c941d2400041003a00940000c01c03400608007420172600c11020354001c08050111508400c0d0800d0904641c0300035900c0c21b4101da604851034509580405480341000da034004000c80f01980011000501007002c6032880d02d265010000075810b4070300c0c01d51594051901c1001903804240154094010000343d25454070800ba0045444e4864a00e030a0014210076 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 146034559 1250 146033309 146033387
    0x717040b04031410140c03070c06020408010902040b090112030305100b0c24040803060d0507080f0d030605030d0516080c060412031d07061101091a010510080408030a05041e1101 78
    0x1d11b40000010540e050300030090b018400d503000d0415555140c0b01d40100e4044c00e07081e181240201d040201d006182e01d05001d41c141a107000c07032801c100b1403440c0c0d2000c401400e0080c2c00291307590034051020550300350100051004108410041408111007003200850102c034500c81c514441207001444001211041125003000d0708440326504014503081440c101112a40f11a980d4425031175505500240800d801810348803d0301c0401241e5603070020301d5161ba4003002d85000052003040640050b0003040151100b450080c04007609214004072843c2c80c1503004d46082d03c407407003501c001e10052581400381c040f03124121a10390601c0696043c5065a581c8903002d920284122040900709061095001c00300241d0082038032a1890344462041d40c600340203004207800365200c1e00110042034000c04403d03000d550300803206851542c0b4a628800102006081111400b1540c0c4503150064018000b0402c2c4070b010300340109100d0304040000d051040d0402450b0f0641e080e000c00d034210f04800b41c192b0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 146035809 1250 146034559 146034571
    0x1020405150306060c0105040c230d020d080c060705091c1208090c0307091b05070c0b030c091806091819020609090f010905011a0717040b0403141014 66
    0x110b07440751240000035030315008000c2e41c440c0315860326007084140a81410f9000485d004c84000700602d4507500f10007030200c0700c1034101e540c12000320b80462005042000c81111510f00a0404606000c92008400d0810100380c603031500280c0d020500915629058004010786443c40b94844206d0580380d445d00c80003112482604c0500000700c00162224906008071517081d88010309403024103494410341001091440f440d44084200244041201401102200d00454000e2040e441d60b603e000c890490340e500051510b0a182414000710100e80c070bc170000b104000c1c0110007010040d1400c8001e011020f03000a00c1c51030342c080d82a603407209021000c07030340000000302c2c44210890b079034180c00402d00c6031240c800c0e01e1381c00c0a60341d000c03c407440e80102d00751410f0341c4030a80103100d2a40c0e1520110410040c1d408030316510b034005c20034807000030300b1005003655040301040786d903080c41c0da41c800e1035949400607442661505c0c542070708103d200e0340c00d0061252055074075408009031020001c000841c46e03401446 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 146037059 1250 146035809 146035849
    0x109170613020307080a061b03050601090308070c0b040603200405131a18010906080303100b2a0109020112020c0607080a02090319050c010c030e0411090315041401020405 75
    0xc1c40040d52400e1140002820f0180102c1e078104842d0310b030842c01013446884030031210182e071540038a640d03c68090180541016541c501e1194210f44074036a8507406601300300c403450001400001c011094001500040040d9140020214050041c0444143c20400d501c010500300b0401400f10780e8030400841c0c0210040c16000440c441e9122100651a0030a002690720503240e5081d120703421542500345050315000341003400f81c9a0380e10701141e540e01080e254a68150000c610030301c13110744080044d00e011035009650000f4040e02c41d16203021544183c00d031154076512640404d06558001d01c3d80d00728090081811031070080400216500c408003d80f10104002800b800b0600302960764054600d589401415145e503000840510102103c503640212920702403034103031800c50f60040c2c0c60540c20700d4041d116a1408400d0504000040c80201e41c48101c24000f800100c0f804c3d10100b2a81c91510140741400381a4100340c28a61750b0300c1e03903001c030440003a0300400c814005a200c00e400d80c1200c000c0c00c9a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 146038309 1250 146037059 146037091
    0x605041511011d1009080d0507021903031a0603010f09111c050105040c050c07030b090a171e0a0909020304030323070f02030a0905091b04060e01091706 67
    0x240807501150024090000d0390700b0504051100440c8501c811038010201d0200c61003154150400010360f41c1000340034100c408280800221030342960000c5500611510680750f46404288545c44000c00c40181a80040d5668440c00346130130044440c0396260004440e010704540c949010b1020b1204180601400d0903203801c0820382c086400c90554400410f0411908807200c0d6900c034490040c942445110700c9903081900d03018074039000301c00b00d0352600b0905000d844414219121111080009098605184100c20141001c01d03081c044000c200350001802c44c0c2e84100c0a58803040024001000f0910712400b000a09041c94002510000720307440c407500580c0b66943da00701500140f034010b111140c1b0648070300009051a80c40070011b4840d41d00390f183d044035642c2c0850202d03500e000d051004408611034020500041c40e10302c000c5948a051079828100204041c05511000e0b04240c2c4401c0c0480d50301ca2012083e980c000c02c511014144101142104170403104030035903a210f010340090050b100080d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 146039559 1250 146038309 146038349
    0xf020f1210020f040b030a0e0111070f230a06140105010f0915031107050303060a210201030b0d0623070f1b0317090a0201030b09090601030201110304090c0801050301050709060504 79
    0x1803d13070b401400c100319030b03d80340d03d802c0e80034001610450030640055441d00d500c0c01500319054066600007034100c50740c0070141c2e85030358410f0b410000c400d1905005600079444c450b0444c2c1c040203544c413400d204040c04110070451182c400420302c0182c22a5051044c04624101c0b00e40d03100c104001201c5084030b189403045820742c0b00358000d00079140c0000c00a280010303400c040c803000100440c020b02c015244a0506561364805101d1401115100c01005040170b0408025600ca600581242e10000b8480c01c3c908200c0da4072282221841d201c40d00c51881c1050810500070301c10820300f9880009414044184054050000d1180d0901c1886481200f401c1e181074085c103114041c07804030741c0b0640701042524103210724096680c54080100300d0009040107a0344c001414558203150107088440300400780ca900316030065442050030140c0d101984818170000403540094003070780b08046626118000e540d410641450300f582c07001404d004c14000c0c0e542e401c100711b5510008a5040320401448105081c1c03440e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 146040809 1250 146039559 146039587
    0x150a0c02030304030c061b150b0102010b0a03052a2b02030105070210061211010c0f08030f07080612070506090415140102010b01020d080403050702040204120f020f121002 75
    0xa000065007501c00410b0100410070050100d0080d1003084e200c03c9042d0108180e00300c221195248001e102c0701c0b2401842e4182c06140e00100003032001400049441654040031aa4200880e8015146940030080d0714001c1c07149210947d241240d0100c0b0341450121280114000c0c0c04e144040350702c00e1072141003801094031281d0001c4803141d4000d00a000034181004001e503150686001c80d00c0701446c2c000009400103120061200c140d40c481001480355015400545a402a01f5001c0d030b02076031170201010000300050700440c40b91940d01c0c070b86e032680c3c01c0940b0014007003580100340502600001e69920402140018010100c0354103c40b8140e440200c800400c0140c4040050720141441c0d848021900c10a60f940341100e4000c2030740200290200b4000480c0c0c0c81e88800ca030341021801074804180800d00c90801010403134005800903107029070305e4004034400c003d003000a40391580e01484a0045161844d205490714004030b400034480a800401d0b540c440f00d84c007009ca6805540011101c82c18102d07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 146042059 1250 146040809 146040827
    0xb0904090f03030501030b010602030a0c060e0a1b06020c090105030a1103010e0d021c080c0d050901060b040b12010e0c120a0b040615030f14060d030908010f021b010605150a 76
    0x1c040e2030740810300c40030700d0040e002d000c0a000c202c94040002001058040c800400d54803c0c0c9900c0e80c2d20700f821f40154654000070b094516080750365004411030080031807490441080011440c0340c00c10895460080028100003100411034483c08034900100300b40d075000502100c00c650441801e10000000724006801000d10324403601780342c0a0102010b400580201d00c0070a02c2e01c6030003001030800c0f07880300111410030b01243c180410300d0040c4002c030401e1420f075005590040c05000009a04e98030f5010b142200d03009980134a2401c06c000801d001064041c0070524010300c000c00d119800c0d810034211018030703801124184a074242001000401c0e02c4032a030400902180080c0041000315150a007507903400180e90b4800d400b1030300302000c4003e1117600d403040c2d940e58100d1030000d900e50b44803502006490641c452050b01004540c0f4000b11b070102e020310818000500c00640165141c1603031406a13101c04071007030403200b01e901d0428108105e4440740b001410220101c440f95560b420408001d8a100d02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 146043165 1106 146042059 146042063
    0xf060819030807090e04080307030f1104090902061209070302011704030f1b14012f030402012003070b15030a11040515092d100b090409 60
    0x31003011003e40110b081e203001d010140c5e4407141105c0283c401d98040d03681d0480042440045909032158020450310560280030800c0042c0400f8998001e5108150566403240f425108558034203040b600c002448000e031962609140d110b0702e5070b501103804200d021500b040c44a4500f5080021064852545031f51809801c40b1b401000300e455040b201903400100307018600710000915619800707480541c00c0d1740001442003d810445c0b447c016003a41c8030702454a20414a40d118a084040f60362150702824040d0301200b291b101c030041498400d4074112140004a401010031580d1000c441c05495104224050b11414800f09a10fa040748103005081c5445003000a50904207900101d44c810080368240c1c4410340f0034008039180c181c0466000913040d034031405041212022060b84c0740006c030b81c0391000e101d03031400c41c0071028490468001e4040c1c1d16404201300c0c8450b511500881c11040d = true := by decide +kernel

theorem cover : BRFrame.Cov 145863309 146043165 := by
  have h0 := BRFrame.cov_init 145863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 145863309 ≤ n) (h2 : n < 146043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
