-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1025
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:53:28.804081+00:00
-- url     : https://prove2.me/submissions/0f072ac6-2783-42a2-9622-74bac923908b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 184172661 ≤ n < 184352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 184173911 1250 184172661 184172663
    0xa0c17031302041113031101030f02091f050d0c170c03091203070e03060f1b070302102d05101a190516080306010e0d0203030702010e120304032907080103 68
    0x543c542500740c4d48001e00c24155400d02402c0c034007001c0ca84d6030b40e1910000c00310100c10100c0c086824441c002c41000d10903c255440c41001801d02d8299400306010302040c14003140401007805410b200c20107a80d091803040c82140c0580380c075000c1c02444050403411340c1c594010207010115000308200b042c3e00e5000b0503081049000c2e041c405440381c483d680309460342401d0200b001e80601c20207003000003032070000c52050300641d03680c00701201c400403100e40740145104500015015900104041d2540d400325400407058001365112a03103848038501504d6011200c42540d803009503215414040d01901010305a4000d044840aa01412030302c403500c3c1000d4041d08081c142114010145240128001c1044560a215096462800b0041c0c1d160445460b04255291800036000390f482501e1070516806100c00c01380c0041c01142010055030045801007624607205402205404403407090510420140c000f0f10b100d0341030009070410100500400b500c0309503080c01241400d005000010350403c0c08a4196 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 184175161 1250 184173911 184173919
    0x9060513110d020f030a0e07030c0e0405070909050c09070824030a12020703030f170c03180706020f010b090f061c08040e06010f030515040915020a0c17031302 70
    0x38484100518042c014028228501d80c000180303c20102103050085100c3d0325505010002444041e40301661510b46020080c9618200ba50030f0004e100240b5443c0d5001c0e100d14115408151501d182c0e10503070b8080d06088a00d40d001c001d8241d018070300840b8851303016105140091a516014540003541c6843c5080c20320303403015048a56000e500c0c00d000d50014035810612450680c444000c000f5a181c00030300c8140c000500401c00c05c00b03941c0c0314208070544210b08107003509060300c0e000441c080302c1d031010381401a00c0c5050744071060121801c3c0030350b00040480350080e014620004c0307035031400e4a05c06002d0a2007102003a0402c404240c144800e01d030428801e4030180159112179450b003480004c0310401800200e00840d000401041641250f0701c2840c00f030380c5000900740b48220903030960380b06035100011080501c10003819420316900820103140560352000c40d084045101c8022a406401c0328000100041c55000070b024031012001000c06542c1204e2b4914980411014200410000001d100f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 184176411 1250 184175161 184175171
    0x709090c083c030405030114090d0806060f090102011b1107080303090a0308060a0306020313110915150d020408010203010609230103050a09050f0703060f0e0a080a02030c0f0d0909060513 82
    0x2c0010700b0000e5402522015008100700c424001c00841808400c03114610184100b040d034902d81403060041900845019016609003030f0041c040d000c40b500b0900c4118110743d40c514809260284d100c0811004103061340742c18820101c0c154900e41002600d4000e801e13990310807c14094100c00004480c4083d54161034442c540f078852400007000b04800b0740c0094462400070051144402885032980082441a610301c5804041d1406004800c0c0c412243d0340401d200c1da00d43c061182c203101103403070608075151144900d06405020b0280403a00300c0e4000c1c0700380781c0d0f0200042c4111504007007100042d01d4200b004880703440b003000000c40032135002a5503604142e1501c2c0412f016038540d82040306103035440310580d0b52840003070079540d42c1d8108078030094034000d04220040c00901001d00c200d851400880d4098508a48162600d010940c04880c100c07003144010080e00201c3c64007400303844402000c100240001c0d10742d91200038203040c00342e0050000c032031524400f00700300d903198075040711801400382004c60 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 184177661 1250 184176411 184176523
    0x30f0703021c120b010801030b15060915070209060303070807060e07090c03020c01050a052710060f08060603060c0d05060409020909030912120702120709090c08 71
    0xc1440688614180e48102d00c60740c0d412241d402c108800140c08500108100070400c50004503600c1c0c0007848054445200e4a0229802d42c00c0c0d00c1e0304040d0803801808407880c00040e031004c40c041303140c0542150484000807071032804500d80f203600340c0d4002900714021030511a090315410094880d411000344070982e6000b10301540b810900ca420010070f43c1000412070410400340c013030013030340c060311140d8810351070b0800044007442035108450140d60f0890300701e25458030701ca2078084448040c0640042030300c10300c41103c10070120345c0644c80c06000580000d039005440d1034030180c6440c2c0081c1030540b00342c000108105902e0b4401b0700341d40e500e11520748040707059100d001c0424010810004065048041501044002c01000006043c0c6070b600750740c10420f01203010640340d00c80036010302d40700420354200514030151030a48034030400003092100340d510b480c0c2e4484401084403005241201d400707820040030084145d090040c821509407404407503040c0403240c09030b50403043d43c1034000500d4403540300c0f442c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 184178911 1250 184177661 184177663
    0x121a01060f110f03070b01090c0206090309010513030803010f03030807020d05070b060f100206090c010c1e0201050c030a0c150b010c080c1e0604110607121412130b1008030f070302 79
    0x65801070b0f8000035039030740e00b80d54240411402d40900030b0080c0c03241450800400d0510000e80c4034490381000014600300380c4100011212640030384402071300300b100680040042502800154021b10307220010018040c903502c1c0180113020f00410220664216148050310580c0010446107071b203621800040d0943e0b41c0c400000c8942800d04002034101e4020309200401d03940003d02c07103004e40000d10443e9261120a0011250000446001400021241e280380071900c419011411801e105050460618401e00f100c985160402c420000c0050807100300801841b10f102745101201410590a00c6070904010001e0400c005100005141201c00100700d642c0600070300c40c0c48401c0c40d03102d00002809a0041c040d0b503441030150b030180e41050560021098525001c000c2359256940691800c60b0303100ea9542c1555558031f009174500701c0190030000c1070040c258205055120300040c00307440d00320a0150070003007a440d4000f000c2c02522651050280419080003080e904034041c0d41d0011644c03a4118a422 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 184180161 1250 184178911 184178923
    0x20c0a1d07031b0305071e0203040311030109151b0518090901021b160b03010e1f0b040e0406110405061204020a0906060206010305010c020106150f0201090804121a01060f11 76
    0x180c4030043c540f42d01c1191055040e040640030b548139a0302c602c400d215101d503801d40c444031071a0420260740100010000a102070ba14410f0106000740000f805070015149c01e00381351039001c62200d803140c0d5900c24110300c601211080703288089500e0035a04080358404504064040760001c140b0903141e000008540910035012990701c500041e01841c0103c102d05201c2e0f0ba01d200c0d508070741910b040031090128034008407000341c0c0e0481782200d5407401c083d280c0002090981d020170210b1640800c00682c041600707a9108000c0c0002c0081c104500c3c514540303410180121003000b110040c0350881004100051b030f882d90107031b4081005448095802d0f0b01c0c1d91001030412000f50b44039080b19401d105000036030715000b24070281204e0084000707006408075040c00f28200d031000c1c040d1949040f030102152040368811051079040c0307a054000002c1c42e041035240c9100d10f422682c88a02d00c0500c028428080007045903000c0083d259403489240031303504180c005131051204010250810460200b04038140c403040082c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 184181411 1250 184180161 184180181
    0x302040f020901091e1e050d030503010e090a02090a020a05160302031b0c0a0311041e0f0e010504050727090605061f0e062a0d020c0a1d0703 62
    0x10401820450485140c0a5009060814041400c4480025820800c1c0b1214501e00e000c0043c41000c003030504003103021014019450b869050350845012482d9182d182c100181380e40251074040e129031406100340d28041e001045612941c100000d0b000068071903a043c55041003044001584072a05030404582d98044c0342c04000c0501d08255075041859004002807014108401c5070203c111100700200e582c5006035100541c0105180000704041011010300b40c003484d000a00100b00a0000404071f25460b0109541200d881da441c00c0c40c10507260345115080c1d0300c0100d00000e00c078030f181c16100d15495820714401c00c10710110b07180024100c890101c4900e41d03460800c4030200051070042c10803100074034003152501c2c00390f41c103400c019006030341001405105000035a40e0340c0281d195942409270a4100f1840c641035070414030b110782ca4000c0004003079500007484600500000460005c02860071000380c013064020810268180001c0589410003050504404038609240d124000d0842c024089019 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 184182661 1250 184181411 184181419
    0x14090301090f2906060901120207050d18030309170106150201051b04080a0f06061a1306080c0301090c120513020a05010201020408031602030c06301003030c05070302 73
    0x1c014030030011403032035000c403032401414650514860b400c42102c1c0c8582110f190141c100c000f0f07001690501d480c000a159600042c5010024400b40750b24001c20707600030800071105c50300680c01401364154400c4800da1801d00814141c58514611780700a00b10541034054404c41e90845013011500c207600350086001000c0310001e0900072191400003c0c0213080646140c6082410701a00a91001c010b9007a103054540d14400780415459a55841c91002c0d0820707000c5a0054850000142016061601030188500f452403103503a03808400080400142e1900820f05105104041c45982c0d42440c06403419186400c2c8000341444011000780c0781e0001018584c1010390411041118000310f044121410920950340341d502e65448100590a034026801032140e180e2043c00924004050038150540341e0740082c0c03d50b1a139001d01c10115081c0d17809040c415a1480d1740007008190030300c0a80c849042070144608240f540c0c14030b0b40c03207100100054400601002002c4419005012042c00410010743c0e00070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 184183911 1250 184182661 184182671
    0x6030c030c010e0d050c0a1509060c11240408030a170f06090901060b0d02210103050607030908070c06200c0916020c1e012309150f070b010f0803071214090301 70
    0x1500c8000d440c0d595234940001b074529400051410b0050f99610000c0794080c0700074070900e54030000d201c107013020b2450500e100070041c8184440e0714008c0c40104060250a00619640c412200c40a02031900907040c82c4039211401040140d00c1d41c40e094001d41151044500304069100c01103e07074098000d941007200010000203445100d034009074018451890071500c40d0803118507d004007002d0490034070016149400080002d082c5038031992014404a120722699802c041d02612030f44610035103500030b00041000c9100c03500d500a80c1140e15591840010001c04050113204040340d40810082d02500003142d05588400c8060300034800c40341c620034007401c43c0c0309690030404404120f012503111240803951204d2074041c4201c9032000c44041d2001411079515021400050001c600d003140038001c100c000502044902125081c000c20015004000c81540c42d41810310046c80b4100e00d5200e6002a0f10070040940056064031403114107d0003414800464042501641c0081c401d4a03640c070f174507500e08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 184185161 1250 184183911 184183919
    0x40605071103031302090a020315060c01020c03030f0a0b0306041101050703050c0616080903271206010f090b0a1412070510020105090c010507080409020c0c040504060506030c030c010e0d050c0a 85
    0x8200300d81c03c45c02161180590344400361803804070302c02a41d400c12218450b0102808509000c0020034080c0c820200041c80c182a440a4505580041d030701908403040d003809200c0385102c1401800c8410b030302100a0311041c2000e5480e001d152514040c02c906000c4085160014140a40151100c000100c0300341c400c03e03e00420805d02d1910a0025040462441800b04801c1d00303001007600c482d625456148500c9480d20440782034481c0038108041c1d804642401c600c0c89401042c440a40202520414000014140f0543c0300554182030105401444120000c200740c0d004180f4035940408143d8014010508001160f401c0c0252030308071642000035085a184083d505610080c480c05006041e80c4004e01d200b0011180741c8940034000e0804030040c0020b00c8070340980d5004003400341c030610440380300c10005000304044e00d400322829031350030756500c0400c502e030f003030501c824180e21178214003a01c440898440080c2c405e040380017182c0e02800300088501c1c2040b00c00c12203201d00400041580f4001561 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 184186411 1250 184185161 184185181
    0xf04020408010504031103040f0b160c06090f08010c0c020609040603020405090a020108060a0501051c0225050607090308030109183504051e060d0c0e040b0a0e04060507110303 77
    0x144c0b4120001040c1901d5000e00c0c440c003000360703400d031164a0034034902580b51130004a280c1e04280072441c51a007d4120b01800502c0804000740101140c1d02e5040465107800080400505540c0c06412035904002c0480750700740c0c0c09540701040301d41c112402620b5192000203d0000c01c1e554000941051414040c000740c1d900004039200014400d90780e03400b46070f9999090050740507540c460f02e80814018090100d0341141540076103460528828018207111015040d140000841081c0203500c0054050074403e1000500c000b5a018141e401c1001c031841c91a82e40761102d2005106111006a444801e001c068498902a0303144a07080032071042910040300d1007000446801d0084100d4550110600c0c800c52682d9060b1012104010321008003040119544000103c801c0107460f0312440401204c0c40c10501e521a01d6078408544da1403c1e20180c590702170000b00d408540009224040c40b02040090a4450f82080d910650165000c43c0b140c484801c181d0305082c2e004d00d140c4460001004100380141 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 184187661 1250 184186411 184186421
    0x150f0c0c03060f110c06220b0403050405090106030b0d080a12020f03061f0203030f0a141f0f080c06090a1a0c1c0e120c0d1103010e010c1d0f0402040801 67
    0xf5206000700011030404264024900c02c0303120441031600300100007458282c010604114a0201c00c441003202c450999500320160f10440e8200c0125402140031b1195084c422101e501504081c201003101d0107140340002c45540803e40700808503600002d0001f0aa48500700d614503941e80d81105645683c0001100311442c0c01c21140c090040049908a01244480000b40c400c01c44041c0c01452450300c1700745104e0f08040b0002c006e541600d4032000c11109950300c9807901403003002c0358140000000d118491400161142c1d91018800c05020360040c0801c54000ca22120b4408045500640e51030315000400c0142100e030740000c000004205400c03001030341840042c01181b100605460500322901d882400c90100203640b0800603107030f03c82c69045820300e800c000c0001411783e0100d40c0644003031400158001308164082f0f92540740c081c03001d81a8142401070300a800c4859000340b14400c900c1000900c8801d4058405540481c6002d0a2805481d030030150100c0040c0940190340e41d944a49070240684 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 184188911 1250 184187661 184187681
    0x801020418020f03070804020604170610090b01050d05090124080d0306030c170f0f0c15040302330a030e061e19110a1106010e01150f0c0c0306 63
    0x880745401180c600400c5100b1158126440b10415046807035034802100c606030f0084c412078002804100109000000302c45d84690255020004d014030300c0c0c407111030700908400758810302c030341d6041c4400c81d00582c0e0403078262500380c4030829000489076035400e4650b02410003818112040b40c8404140324090081c2a041d805030f440540440d20030203000c0320124202d440521000d8401d04803414140152501d01c2842c0c03100c00c44003c12036800620040e84241414105520192254451751104415041481032801c0f4840c040c46641d04041c035580116452120341451100c40c210f03854500044407104044918000402001694449481540240091100c20034082c41031055000007841d140444030809600c191544c181d85042e02c1c1d003083c42000074820264201011380700c0d80d80000981c84103018280354411540d41202c072000303862540303043c0003040c0c21244140c000000140101b52200048150443c174034030741112403000c1175400300c644800601e002000d200c4c0c0348400001780882078105a50036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 184190161 1250 184188911 184188929
    0x201020d020303060d020d03030f1103060f0a0503030f130b031e01080316080a05070213020d1803020c010c020a0305030d050702010606050408100903050906070b010303080c0423150408010204 84
    0x81034858000303982e2800101d8149a0103a00b4445030001810150460440740e4400c0c06c01013981041040c0030010b641d0400036802540802104216031458a90540300c40360f9000d03036040d0919418407002c40d450f40305000303141d04011f000103a4803060000b9141c103000141102c412064490030a5007400c00e0b251265042021034098244c004101080701100f180d0545a170b04900d008404000e40e11031916401c000b00f280c0501905103c202c0258846516114940068020051369030720205008400c0783c000084900343c3e00400200c0c00d00290700051048058403017420003c1c0250344920024280c04010b4000400074040031071280c074000c040b42c00030f500800701c68001b4000162a0002110700c2c0c0101e01c6190007640c04103c9860810410f9403060030300ca8080e1810528202e03000d40440e40542c0f00c1e803000c44141802d90300400c1816440345031150014110925503292902d0f0840500c900d100000604018402020a9402c940e82e001e02441c1d0050a000f96a500c2c1c0b650f840c00a4002c1d003051050001d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 184191411 1250 184190161 184190173
    0x60106030e0c0d050708100905011a15030405010f0c0503061f090b030a3809010f050103050612071403060c130b0c030702151b060f01140301060906060804020102 71
    0x2140030340144404646810014080c80e0703501420005072415003002640e55005414010555410a20070400c0c0c0c1450054003290f45965441d00c1800c442041801c810602c4520080714003a83e550140021601c0010070480e0710b9460f0360602030300404440c58505041442e1002090555401402035485100c0803500e0f10751020ba00c14084805403050bd40d1726000901560017817002c080350401450b0040740780300d40040d000c1c1010000e40244c10030700c403003140c00d0144403540c1d8011445040f000c01c0300e2003069604a125500d421004003080c24540541c074140b644540c0015002c0e20380c2451003042d84155400c1761030640d030703910000016500710002c032030185c000c80b00003801124524084a905140c40c0c443c11000d5443d024501080c0d0b00820401c0c010b500042103460301682e64840328040c610340201c60241d403890b80c0070810000b0f00301900c4140c1590403034410051070080241041e4110382c400500351449040c11000a401060180c001e2502c1034601503012841d02c0d840707161300388114801e80072146 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 184192661 1250 184191411 184191419
    0x504060e0a05120705070b070602070b01060e030d03051e0a0e01060902030606071b03060204030b0f16091a16140c0108160c2d031202070b0c0c0f03070f03020601 71
    0x2441d40c1007464040c14590201c102081030107a200000c1c140c050040041c2c0c1d20480d2149018401c6034014030f401d070781054000c41e03c801031001c03403140e140c010900d509003580d0b9000700c640442d850341405548501816075903800105c2c500c061290131040c10602900003203892a0807000017008150302d03100c4590543c03800c840410070000300e100b02d0340103000052555017403031899a19034544142d242041c1c04c0c0b00810160000c0015414000b400146214070070a240c03907d040c0c401690400401403e0006d055090503003000d0460700b2550050699014020080100007440c0e22141584a2011a0307030320a030342e00340404180060031a912a007814a035043d100601210350044956030800e4856601c54545c000788141c185002d02c510040030f62180f070495261007207004403c07607a00032640c1030b8048450f01c14480710406910500030002500081b408504100311a1074102001d04001c0ca00503800c540001c460700320341410491802a040c2c0d000860b66540024504003a0b51550090114003503c0f684001003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 184193911 1250 184192661 184192663
    0x40510060801141e01022b020607080f15061303030207090f050402090115030b0a0e18011e091b030c09050a020301060e01050901030f0c021615020a15110a030504060e 73
    0x150950f030081c1400940b00d11a08450300500c03504511606600c2174680f04034414030703241c0d40310103619400c40c207143c0d090b88aa8000390906c1002094182081048001c211881201841c0d481e01326201c4109c0502c600c61103408a01c45200c0e640303401c010800c08210020400d030380020301d80c00303840ca60503090100341c0025904009651007950020b41c001031410050280501c003201005950304c203854046010400c11010500380132180d0420a90303138070828204256031140d008800340c00d01e5090001c010b8141405180b140103032100000c01075107a00c0d40b0111044c041000b03036500c40092107600a000140e5a403130042d003080424480d0015142c1440006008184217100383d80c100c80c140e803035100700c40b03507201c00454075a88208101c1741416a14000c2d80f40e280f0503846100a1440c95800401c00c10b52220141070120381c1e254024984602d0f0040c0a51005501090034400b8582c1f0003a41c002c03640018000401074580f140300c1003035034400400d2103540140c0c540c11003070086015180402c0070300d20b506069 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 184195161 1250 184193911 184193939
    0x90402010e09040302010f060f05010f080408031807090e07150207060c020402031909060c0315121407030515010f0e07020601060503061302031f0e01120204050411040510060801 78
    0x1038003151a000c540c118504001c0c2a6550081c803900c000600c0004041c080400c6800302e0700300300c1460b4481901880956041400d011100c12181481c0a10f032a099551040600c070050110003807196500e55181d034014104003010141504817421312080750304100c8559100800d1044401d04146814901c3c01d0710f002140020540c0c00b140da960220701003079006c1c08003a500242c010300c3c262107003080b03a01c0d94250b58402c0f4410b29100e5007020403a400307580740041c2901c4170b42c80080e410100400741000f44070702c0c12191143e0705038420b021050700940040381506000c029480504035001701201642000a014002416a030b0138000c9011410785400b0460208070040320848003603809013006006890290b000f03560311400c01008855031824842ca0041a41c00a46684108103110015a440f0f40364035031000019140c0403035003502c15854880e05003541c1c0c0c030010740030b4069036441c00800e05000340780b40b01701402803010b03005118038240181c3d0112070808622603480050044000032507405080300b05 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 184196411 1250 184195161 184195163
    0x140f0705120a230913090b0c2104050a020d0507180c050313050c0d061a0405251209030804030f0201060b09150c0d05030907050906090f060d0c0b0a09050904 69
    0x483d404400e0307014010f4824480c0c0c501c1204035500c01c0c003203946035540388a80c501400d52045400314800043d0720708880c528074040d054140c1c00006100841d0484051240710581200207642e07046681c855040480c280907030070002a400c07410b004400030612a001950304221002c0403001a01045020110380031600341e1002400010b000b00041008542c2c0140e00340718060191059812038200040041e5004d076052034121a03007502c900405120201c801501103d012040e20207001510307100205425500300310500c803c1c44008031400c12001d611a4442c03034527086406070200728101e401c1c100603080e1481103d040b0002000c601c07400700058810f0184070300f180c1d0070b41000c5007040200010042d41e01c8140d075000705220710601600503800400c100c1c864040209481d129600d051240c68071b410b00e000b07500410300490396141804041e48400c845503034820322460b0300e1055038488000185104030703641000b4000741c50b5250301050580c0c0ba0b0004020707540040d00d800c0c1100c0c2c5d541c0248014004100c0e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 184197661 1250 184196411 184196417
    0x4020901120c110706020c01081f050904060905060403031407020c0a36020304021c050d050c0c0907050d180807022403011401090621020901140f0705120a 68
    0xd988154100160015024448182443c5804020324070a852400d0b940d03910100040c1e101059521095810404958000101301e290b68a8661000f101500c030010500c50580038081c2d00c0300181c144a05a0701811005078040160340007810a4100203001e42003042240c494140e846c3c020901280c00000d14116590b80a04080c150910302500e201c0c3c1c031136102e038890303580310f00300c210320480e100004d0744a00c14a03d14000050300e07410503005001300302c0b07494000842083e8045040002242002a542c0171015607490040d94982c240711049003066195548503820103142000d010211360030101600c0c6c0c1c3c0700f0717070b010800c21208903226440d0356051401e00585983d80800c00f078405402c044c8480031600800001050f99078807107544000075507000b42d200349032019800200a4140d0f0344048100c009100c01c0c5003800695066244600c038004c0103840c0f070100540e000401070403e03401541e0140b0050a108038a64803015544601e09a6034410482242c0600400c07651900001540e0155030340c4100c256 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 184198911 1250 184197661 184197677
    0x90611121c050a090b09030721030f0c0215060a12061d0607022b02031c0b1c06060f0b0703080702011407021605040b0d170f0301030b1504020901 64
    0x2511016250303018038001000386001030510303108410306008560040046800002c0c40113100c1c1400030301250054144085034004101040209907a00307800303860180c008145440084801005500922400c40041803241c24900340321949078011980c001c455a400f5070030a090b80c0d4a8041100f074150030f0041c034040c142803c42d10004180b4917881012407847c0440c45001500c400c40d5041d1401c8011a0340302c0040c1e1202861894124149070440080d52640c000000200d52603040030392203000d5170024030302401c607207500c90300b0b50b00c42504401d00710040a4942d111903542084042180e990703001c016103206003800e07000195011000a0142280c802c40360490030080c00d99011030710208050114000c66482d500301c0301c10424008041d0380111400e400500103900540c00715101da2080c0d170301c40c0307104604c1c0101065082c1c0b80d2603801043c440e8041200c9100d0107103145030341e0480c010001c69041042020001000700034141203e036020752500d055610310031050304100800c2e032140210f0180016815 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 184200161 1250 184198911 184198933
    0x1505010503031c0b0406090e0601140a060e010813081306020f0712030809030d110d0b01080603032d0a0309030909051b0901020a0219090c022b02071206020901090611 73
    0x40e5100132250300c0e0041020500039940c9042c075050307a0462124441c02e8000400400540c21a52403203604100c0603202c0e41d13000c0c0d00d004806810861003150032410b00c4204000031b612062035800c0008141e40c44138600317486040415459900b1421401034a0141c45054075800c1031040001e0400115848002d00c1010036009070b404450007040681002c20520082c840c0710010a614020b03d8001c00d240c08c1c119844410034208541034078540781301e90381403201000034000d032034501104075152804034412a8039089004201c81107400c18040d10315900410101c0c81c510b07030740c1d410740185102c14000c0d80c0b02c205e01921074404004940c07007030b5800c00c08142d2004c1d690400c0a00c007806000b16850500584440748650740104500d21a4001d0103000801c03015018844480203101c2c12413040c03020b1004204059848001e0100c02c14840340c00304070b0040d118207407207145108201c840c0c06041900c10114401405140140194104070034050110b11045804204544999036004004040f9070040943c1d21030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 184201411 1250 184200161 184200217
    0x30705010206092107080706150506031023090c030601080108030c030711040f14040507140f06031008030c030703030c030203090c040504030e0d110301050c091011030d09150501050303 81
    0xc04407184c041e0711020310540011488100141860031f000d0b00c0c3c08103540d1400700318001c812085800045c40391703200780180b2100504032048102034034029041503543c1001c011495107004503111100e03034001c140e0002c1001c40382000c0c0285005031402c0c4c9805455076250000180c03680140c40c40745142d58400c0c00241d000c2508010b004864080141c80020740b00d11040c1494155070000542d010681000d00500040080410142009150480440007450f1802000480d801046144140b0611011000c15030300c6001d14089401000c030701c1e00700e903503030501498900d4581d00410002d8021902c0c01102c000300324040c1c02100d1094041c0009007407415040300402008050161080e4200040800e0010490b01c85801d5041407030b004001c50070030b2030a540109801d40303600070032030300007010140105013280e280c80c6220550030445080240d454082800132074694060b183d0869091804c010326841807044c0382c6403c0080203411501400701d60380325002d00da1b5910030443c2c2d500c8215424145c1000e4512 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 184202661 1250 184201411 184201453
    0x61c0e0c030123190509060403021b10050c010e030418060e01060c030503090709150f1a0403020d1104090b010608061005040b09190608071d13021615060503070501020609 75
    0x13100407080518141c41c0103480080350011a0700c503807107500c10010b010034181c0401c4046180381c84c1090102240e8150300224802d0005510450180304001c1400c624015007900600c003071903c004205e0751103ea440c02c0d100000100b030100310083c14a402004034442d9902030445059071307140d0711401d1174840e096404890781d80c001001b08880380100e4a011a2602550040c01c980c0c81042c03150003512810480d41d0400d01142c0d40c448a4800542115a8075589098007510101c1c0c1d0102e442040c002c001707042c140030f1401d0000296610610701121002003090051840d416905035540e59002a80d41c0814440742c4c212600f50b0401040e070500041050b01c44070b07002441382520107005d4070828051281a801e5103200c60300144082403015003040140d03030303000c0d455020003000d460a0345840410303140814050941c1a00034a1110340003c0e4441303107000d1400d0490b19455000c0012081c81010401c036400400071030240074480d003d451400940d96200080325400b820300c2a01405e0003081d80707580800e5400b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 184203911 1250 184202661 184202671
    0x3050c1203090a1517130204110706020301120c0602030309150a090b09060702010506031b10030204170f0705180f3d17060f06061c0e0c030123 63
    0x3100800428203182c0342e12400f00f00800208100843e4000e203050003400d00003d0b0202e404501d00d02030204030220000c25000d200b95a01134a0008041d203000034200028030039000040c081e14000030001078020f4505000c0901c490140440051464803a64100d0b12031005540c9002c4984c410604001c0e15400b0101a5400885036400001c07120400c0d41e650220801c1154046040d030081400c0210b040e0702805240c1d40030078200e01a004040d0480049038a85140f454400c0c05102c0c0c00700402d20080c040d034101e130040c1402807144000340020700c034141c1c0c1d100b8040d10f5030942c0b80034050000901c3d04251070440a03128070741014007001d9a607040c07001400d00c00100081000819070034030940700c0a0b030400d1120004001d0006e9030141100b58403480e020011540401880c010b00540e1104044021400c5c90300000006044041d0342c8416000482c103000701070f0070f150311040c80140040140440c1e40061805034190003074810581d146401c0600300c5070302c513001109491000160044000039040800d5100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 184205161 1250 184203911 184203913
    0x201050d05061c110f030601080304030f080906030a0b03010605060a05040515040504150e0708010b1b0a230106050a030203120715060303030b0f0307060f050c01060504090f14010603050c12 83
    0x220500520401032290b880f0780135101c03a03034203407401c0750981000c20180c222004203800911203549131501c421398920441c40040c100365903985040080240b120200c0c1d615550080545031a400c00c412810300500d0400030080c884d6103000000581810203005991450101c0d80343d0703130300b040d25000038008010303806c0e481c0e50201c850070000407403a0b64492040301c0980d44400d481036010742c00d00c524403481110241c020710030300100e032004101012201048440649000b201c0000c5001c141041c2e610340758036000000c00c02c0c40300c10480702c19803a60002d00c40000000c07600034490103980b0014886540003d00020750550801e4900e01e00c00398165009000d024030610f418864007506450070030890b011a0400c50000303031504400d001c0c0d450400722240581500f10040c000c1107251a00c05041802c0c03030490f15051240100f8480c04401080d13002d44010400600306003c0030036280740006001c0c040354070480386007a00d0211030240c1641485142c080d2030303000c0300500e018050101002a283c40c024110302139 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 184206411 1250 184205161 184205179
    0x50702040b040606170c07051e0115091506050c0c01030e0a08030408091315140111150f100305060105040b21100e01020a02280c0f080c04090201050d0506 68
    0x4a848a2250a000344083c5d501d2100c40e13100000043d0642d000a800c16003480801c0c4042d4020540105d881c01000203406180c282030b183d20500710340075200603400c045034001c0c916030021350506207821400c0040b140c0c890009000b0f4607504143d96074000d03005841d0a5500c110b480c802d00b940203500060348080c43c18121802002640d80340c0031503074012601250307d040082622500d41c1016070503506201c0e1204814000080c214914603044180c900c9400c207181800312540f082ca0340244202a04201d0b054203840b07160303d034060120385480701a40c8160854031520000f03241d001e15420f030242030b82e43c8000500002e910346000c000260401e0000c00c1c2c4e01143d0390301c100d0f01500d41981d8010080d480c58010f041480c3c3e02140f40b0040741e81400e40401d01d80d004104c03034024581d001c11b03d01e10103640c9110348903110940c40c41d0342c0a4040c2c484c400410311900081c010544a42e0050318400722049082250108041c56084c00151407040700c0090110b201800580946806504855072100d40540700c194 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 184207661 1250 184206411 184206431
    0xc0201110d0e0115180b0904150f06080a06091709101206050a08010905012a1d0409050a120201140601050306150f040905090601050a0e100e0f0a05090f07050105070204 74
    0x4c0d0b100b8a9001c1410207411010065884c0414082c0c80f00c20081102c58a40c145800c0d02c914400d12680c0030315010995070707031004009144c0d0700c0e80710070060000842110250b01c04c0d03107410390080903426015100042d004100e84041d0910800315101440007514031180301410460984e1402e5804e18540301c6a91035078008501a02d40900d0383c1e006151080020a40000508000d821075a111820908482c4d240110344202da1030106469a001400c0c03400a82d016498042d21107002c0282e80c5143e841802d00c0e034994240100001c071440100d0092400b04801943c48805038221042c3e503070114200015200000d66540c00340028591141000d410980740b484203c48051095000301210b4819680c041024400381420344216a030101a81d4000e02c600c0d4185000200348010f64070031003981c010034000040380b0200c5011483e0007021030411480c2181060032080c0c0e80c02178121880c0050b40d24140000768000400109148141e011101625985042100460b55940b2501050380c1054541c04441 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 184208911 1250 184207661 184207691
    0x110405010b221505030103142b2006010503060a05101202120a080d0609061406030c040e0108210304030804020f01020f07080604031b0b06040213080f0109060c0201110d0e01 76
    0x4803510183e40c1d2890790300d40c1149004c0308070107a10541c0162541c404c0151880082e0080e442002c040f1008000c29406210341e80112000442c0d024070026241c03400407000c4030f0503000124181a0f030740480a0340c00580c2d42c520250103c0704220303040d1a40da40e1120040000b1003410001954242c009000c01d8400350803600014901b15201c401210fa82d100020000780c01c1155106a0000d007146031011720629162068295440d001140daa512079100040450054a01c81e400c85008281001b041c810540e945c1d10419201c1c42040c01d4514109085a00d0348050b81c002c20440340304a078140c03105a1240c60701e809005401c00074120340303070651140d1203101028040c00c11020f00104403030401002c6038a482e2900074907031203045c1d511200c0a041d00030010006104503850650040055a0041e12a0500005c0480d041b01ba030340089181e015440c0700500c0d900040d0000c010b000c0c010b540a101d00c42e5800e00c00c03422622452403c130610102840585407815440c5c00c0031601903000400070030640d41011703100c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 184210161 1250 184208911 184208939
    0x40e0604020c0d0c02010e01020c0d0803060d0f03030504030201061205031b0313170706050a080f15060a02011a06031003061104030215030108010c02070f12020d050d0903110405010b22 81
    0x640d01082105130030000710760340807100214405082c030181c440c00d041d020126031039000c1d80b4401040e900c0044000380540d103900e6442c8101d503070400c0c5509010506828003400811050380c00703070f00650824074042b640750000d9002c90700540c1e1000042d80340c1101002c91a440001c540078100d1680002c00c0341400844600441c2c4c0003800f4a00c0c00882c8030344109149902e440402e030b1002c0d0502c0b0060002000b2280c02100c1035901c0b80c0250031040060b82d8680204811210f412181980201c0200e40080500d80c1548044900f40c0c81210713a40000e100a020000c250200310b400c80000c2500300c00034000126242c10a241d20090b81e0009420603840781d001604640311400d00111403c40030004000c0403609000b011000c010500240031081c1c01c03c5184003140d0b069006034000403000040e94070841d25001c01c003010080c0c1000c19501c42c0f50174440b001788a13881c580b000f40c0701d103020207106507400c0c1340600ca146d040310195541c1d903103840300d401c40d025110711030500c10042c600202000010121107900d44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 184211411 1250 184210161 184210183
    0x10030605070c020a3008040e1302041a01030c140f0711060403050c010807170117030706060b030a0f0612141002070609020111060615030a0b04020403050f060714040e0604020c 77
    0x641c034440e0802c90b407441d1700b0045003200e901451210301000c0012901d0002158155031500c038a04207195502c0d24002000181010000c0d04149000440c41c402d0600b03000310982c54400f40e80038850080044c000b202c009a0184103058843c5003000007401551040c8004c118051040c1c1204058070649000283c017a0480d40c0b0603100b64009201440e0341e50781c082c0d0020f034820541d040030b26140c90309200d40c1664030814000e91142c42040050307110503840410503580440e41c0300360140072054a44103110000c1e082a42c20200b20b608000d102088200980504002e48200c814566410b020765155840b1030401030700c03100d16600559100d001ba0a980d07000425421703009a801254900700f6100051503a10345194519a503042842400000d68401112169003103c00d00c2c1c150300d94503024514401850f0458055500c03600c0000c000003005000b10701c440b03030103400d0000d60b41d456941501c140ea04c0310072400301c402500c0b8104024050292100783d2241c01110142c801818005042100f078035085810700c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 184212661 1250 184211411 184211429
    0xf07031d120a0f1b0308150405090106050a0602030423120607030507090906050108042d0c0509010b030606040603020711040c110f010204051c140706120509010510030605070c020a 79
    0x100b18982d160007140c040715428451074240031890500d8005000314404c000010100a91040495001c2c002c4802d140c20602005104014038140042c0c0d8030300030000da101703a50007402c190f84001030490011054400f22a5100d9404485040541c0221810481c9503421139101801c0c03c161000c0d15010858240700d06213030f45000400c1d081005000d42001b60035400400942e0500d441400566406607a8940055100f00c040e040c044000600c4102da014079001303802e8507508450018284030303a840c8a10215281602c0c1c0c11001d90300c81e44203101c24881120002d800c60020041007001c513209500401c1940c1c024400c2c0d106000401c00020700752400a454000061852810340108240c1070010a0841911a0086291918003004903081c2d00c031448040110030f0f0960308100c140418a188100d14102c24400d60341d11544625010b8004050902052003161804001800342c08052154134000c0564040c003103912851031791060b018001c001c266a0400c424900c1e4540141c035080108405084404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 184213911 1250 184212661 184212667
    0x8090f030a02030d110f07030c021809070504180f15020403150b01020c010804030f120609020d0207030206130c0b030925140409021c081605060109140f07031d12 71
    0x1140040580b640c851280d40e507500c041200d8980b1b00520012603a00030b0381400e010b640074580d8000100c10501c01907044907020682e108210459501003260303400d0b2581100e00b00301403d0304940c880f040b95010000203000e0006009200c0c04100140302844a032a8000c00c09072601d9220f0392a207a50496401c0ca1207215034490086960968061200790300010342803800c1503c81c901510010801ea4038000d20005124200c6a2851154455000000600740300c1e0010f56440c2d108083c0742000303501014003a0300501800001c503c40c8074180c3c3c0c4040e21709803c144445500c0c2c1c20600200e540358030107000708010f0310038007650318004051010048010341c40d00440444252030b002d08104c1c0200c042040174811854002020300594550202803450b100c000490010200346103000d040303610840d0403451407038845c54401e4040141c0007a00d24181e46020205001401c507942e5443d48100701910448082408900010842c038843d500483c500d840b480b08030b107a054400c1d450700b03040103940f07541d1440e401400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 184215161 1250 184213911 184213927
    0x6091d22050304060f0908240604060b030420090c09012604030903050706051c1508060a0f0f0603031d01140a05030108010606110703030e040b180403140309030a08090f030a0203 78
    0xc013503c07030010a5851f015025088103406458011141700d910514070000403408160303203890300d41c050006856141e03241c40c2d880c209800c290000c0b103d0107107020030031020701c03003040582c3c10210a010700801c10000d0b85810200c032700d001580c0d14600558040c60700903484203426a520b040034240340c0214007a4440c010081c0c21400c0803418080780d80c001c2003c5c4282000710320b01c078404045c4801d00717039140b0003800a154488661011852001c65106003210702c6641c00303101001401f035102462400e11b040c401c000b8000100c80d100142c41d80c43c800500801d025806100040002507041035120005140c40d9400d0300152500380c9480c3c01c14107001d00069400300041c45180c909210340009082e0031b040000003110300c00203107651a6a2400b00408005451509400070744840c2c00503941c1070001004400d00010b1815400c6003407100700d4050300002c03120220b800340700c842c00007100d015800354405140340281204058610a4000c0c0c61001d01d442640040311070321400b03202070100c40e443c550141d41c0d03603114 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 184216411 1250 184215161 184215167
    0x80a030207170c0d0306060e060702060c0d050d0c0c0209040209060f060307110705040608070b0c070b07110f090123030307050f01050103120801060c1e1202010606091d22050304060f 80
    0x1000c0280b0038503107411014441e10342c00480c000c8441d0b0302200c5052b03640d240d5102182e80c50040804d217000c0392280044200300c0710b03002400340c8069a52500f081040c1c09005400300ca801441240103174000300650b02240160601440056201070041c0440310501c6400d004505c041d4011510180003411907003c3d0041c0d44001d00c0004006d2104440a10865080900042d2075904034401c030035582c2d00006040709864400d00c1070800034600512042c0d100c458a0408050180c0740f0320900e80f0417240600070681901c1d0148840e4142d4603000320fa42004407240d1140e09400e1880e40358141c0c9480300740845030003d4810801c40c100d000c004c17400032a69514529040c03400000304510f40003401902c00c014010194098103140c1c41f0b070b070000322103a8600c030420003822805110900241c019810091072021300c2d601504074404031406995540d400030f958000e410480c00071046d004400702000004503511800020100c170700340928156020011b1041e5072034511316401a805900403230401168801801c0d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 184217661 1250 184216411 184216423
    0x1204080306040b0315011202010915020d110105071d040e100605030712080d090c0b0706050906010906080304150302040b03040f0605131e1103010606030f060807060903080a030207170c 81
    0x384c00400c4212801000210420014001d1100040c04201d50000f5a88130700c80d076000405808541003c0704002d204000c1d12540140c2c0060301180568400044100c01480382500c41c1d01e86944040300f2018641d80842d4400d0314841c0b461f40710781c41d45850008144280805c1811203a49200016a503150400345400e200706a4002e08000b1480e0304000089041d00c4100c40e0242c82000000500400c10b141078892050960000f0049010204080e020405180d00c901c2c02180d450b02124036580c2e0741c0784014182c51040c050051541c0040c0003c100070b611018040c02e4922280c1405030900344c4030302c8c0281003504229400e5800d040203103110414402c281c8601c41c3c0111088090b8002c500c2c0c02c1d00d0f0340d100001c00e8203407082c0c00c0f1728226844041c0090011400e465880081c001c0c040160313504001000342502951203860245040400140803e0000d1a58102c90340c41d1280b0320703028659110000c442d04030100c2079003455000c02000e030000310f641c1c2c0800240300d007800c40d0700e844610344000640303003032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 184218911 1250 184217661 184217681
    0x2010f06090e1213090905100e2103190e0703150c05091306030203030c07080712020918010924140f0c070f050d0f080a0903080f0c120408030604 64
    0x180ca0902e40e44650080032910b98220080c0320449030351a1518498051414026807000c020249040140020424042481900d415010106121000c06107107215107036104c5510b01d09203c050000300d0001d80002c0c1001d16403104960300100b000c844034041d1141529110328010400390800e500c10700800c03503005568106408407900800004504c2e000c080c056200e04058507204801f10411a450489160401e0b005198054192901d944100404d1039861505004a50460080550101700b6130b0b961fa20360383c04031b50000d003c440d55460b60b6128081150486240250039500c40c0341d4200850b0b001e800d2400080c01303d40d094070011125a120304100c40e480311501000395412428800c1c0c8400c090820360300300020718a20740d0f441c003141ca4040e160f508600760080083c001e401c0c20000310741d0810500041c0d01055225180a0356a11240d50b040b02c060280c0123000c84d104d140404d42c140c89141220742d200c0900d4402610b0f1842520240490240858045443c1c00300041041110708090081000c64 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 184220161 1250 184218911 184218929
    0x30c12030601080103030e030a050a0311070603020c060a0902030a050a0c17030304020a031e0f05030304141204261e070f08030403060506040b090907030203010b090601020c0112150602010f06 84
    0x94204440003d010440610001d41081054100c0092540d000e110b03c0380202c0d40300003124180d900518015200705404006002980514140000c0a50080c000c0b01e01950407040586025660380c84040001c00c040c040590b058452031822800048040000b2a052401007105202c0589403019080d403071100024100c000742c1051083c400180c48a108403025030754001a00c40c1c2d4104104441c00c10640140000b61100da4000400000d0002c003000450255014001c902e418070190507c85585160080310320850090400c020005007100c6100714004000540345060411914540d19282050250b00781c5c41d050f15000d40400603040820a100051222900b4030040ea440c1000c0d42c2d0722405248000380410741c031500040c8840e0390301c0d0700501320080010406c62503420021000380e611807081c00101e000c0e41c82c1211200c03141c5056116036108000590061221484070001140d6048000c034080801d01c1c1c9034140d01c140004d800c1380c410b014181d1030707000107500c2e00c43c80c680005484540d8046851 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 184221411 1250 184220161 184220167
    0x7050d1107150e10050f0708250c0b1e03160305060306012315120f010b0708030705090f1f08010905010830040e0420011b030201090c08030c12 63
    0x24454000c50040c08143c8122200510001034403015034061145003408400260005100c00400c40554050065811402c0343e100c0c640c81c010580b44841c0202c0c41c40603100203c400c008001c8100d00c4401045007a00100701316801d50254894000643c03c1a9489e10290300f004c03420703124a82d03241c030403294000000c0b001031150b0b524041413a001d002c1051113030050070300100d07103404d400d4036001c03040c204010a03a00c15a83d91020b400040c107901c501580c00b04100340b84270340000342480c0d000c0283d40313906800034411859501c03200000c1e07400381e2061803002d80040f498650000282c3c0d61102d000f50a00440101558803868000001c0c40d100050300300980040c603000061004582c0051210074280d0b07440e000b103440428500840d20401000380010f0310b07400c000540403800222034260745002c2c521541c48100300103070a1008401100740c040907140021200070781c15603222424036201d00014081c0c00005010309081c1c480480c138038001d0700304207020741c00003d0303014048070201300d0001060741210000341 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 184222661 1250 184221411 184221449
    0x31101061d2401120603020306180d030c140a0e040608031809040816080705060106121b1e09080105040f030e011b0f03050d0e0705040e030a0504090905010207050d1107 74
    0x401540414a954100070104d84420359400d104e80c0400061600142250354600d008103c042e038020280c0740036846801108080900c442c0213000369100a420341e02c4031009190501c06042e201e82014000780700b0004001f24491598940b840350300c0203800e00348003542c0c1c2c0d000b09d2400782d0380a40d0a01449400340c403d080410000c52811000d0b0340521100c1b040b200d00310000c0d41018440e0b40070303180c4041d0440c0501e200008a0036044a078413001120500c0c001e001000b20020010036042c1c0c0900c28a0206a07030050303480c122603242492500205941c04c4c41c03c149034446c1300107401c6400480d0b084a0000038003801105060b00006481d00d41d40b02480d11828079250000f0000300501c4804008015840e0014013004041c000d80a03258000031464040016103582511f241c0c0e03512403882440c2c040c51804064100c03001c00441107070a0b5900e543c4690b4074241c030b03250100c0014081301500380c0b440c1d50300f40210000200c00f40304054801c04036030340f81c0f943c1c01003a5014034185801c0c0c0e4090f10443c1403150b1222 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 184223911 1250 184222661 184222711
    0xb0a08070f09020904020910030b030601120f03080703020d060906050a050901180504030e0d030305161d090c04030602030f15100c02130f06060f111504020607031101061d 75
    0x74060726109280540c86030b849901041c0a8042c3e489016448a4803452004c030302e903407561201c1103d08040781120300d940d0740c7d030018000c1d41052410142c251440003241201080c02100ea05806c0011480c00610346440825480120f40c2d490b00103421841d140d960810207803030220100300140c442201e40343d1792035241644482085030480b0040c17402d183c603900040d06050152950582c01c08002d02010034012543c680103000f80343c200c40d00c0d040e001c2400b4100100d544641e070303403203c1c00c0181450415540b692004200c1e0b603100060540e4a0304030301f0000400052700500246001c0c141e204990b0079241000b520248055080c0700c2c101d405203d40d08002c0340740755400803492003032580544802943e410341c0c68440010741400020b00d0496070601100003091540404128a61007040e9a50b8031000f004110140c1c642515007050680f940c0288049800351401c500180641c52203800c000c0c4d00341c1d076000c80c030394252000f80d07020590325121400240326030031800300100da00540c41a030030441400303460020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 184225161 1250 184223911 184223939
    0x2070b01092a050904020d0903031407020304230d050c01020706050702030604030305060d0c03030509040c030204080604030809030c060a05010614210a09021507060c080412180e0403030b0a0807 85
    0x31400ca0b0b000050142c4110340280102c85411002a10555a400c0002128000b1781101d070004c4000130319201100102405600e4543d028041c00c1c1d02070351030b0918001080c02c0e03c01d02c90404030b984801d840324440f480c0d03032940c504081803889000a8800c603a40380c0700180c2404400d5202206100d81080014010b0f540400e5140e40b2591600700060300751034030000318400c581e448000070210000c8503404402e00d90800d024007030103042254140040074450100318140e00072031184d04090390186020034002401041e071240d020b0b400e20b00f100e0030302500d802800d1a000b000d980092100c0da5070401845840d5100350034086041e4110b4000e880d0501c881c00444bc220b50f640319004045210001044050301d0b00c4c0c0002040359002400386a14414540d45082030340d2041c001280e0061809108401190190f440613102d41e0f0412a05a150084500c3c1603414007084150099900341c0c5000c04180c9425004050f80142e000e982c0c005200c2c03030b00e0000c1c00f070b4456058205140c0c0b6071119400300610780c0c0607211 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 184226411 1250 184225161 184225211
    0x10f0809030d0518191704050d06020904090f0b01050a1a12060112110306090f1012030504030f080a0f08010b0405120109020303041706010f050108070302130503060a02070b0109 78
    0x400940f941e208091844081c1c2502c40c40030301d41c01031112919051050000c090560341c002c4074858a0703503c0000c180000780c410b0380300b040d40110005c18000301198203913002c1c100b242006070012a02042030303501ca00030803d8202c0c08641015549006010700e04180c0804405814081109000010317038102c01c000500031649548075059088001030042e0b4407600780340701344007002001800143c812043d2490300741c004481c2d19004281d0080005d644000c865001802683d00d200102035a600700381c580b040c482c107000f2040c0c081c1300e0300700000400512258140000035008094403502d42031b1072107008042e2541c040252080000c1c1074010310001c1d00c440100c03021204100e5034a0040592041c0b107a0140499080207503260002140000702c5502c940546160030075018103881c12030b038030303480e06c4100d10000d0b000b0b440c00500601c0002c3c2c074040c040d40c01030025200b0300465640c115500d05c0042c0c50680201c2e0b40290444d0045130b41801c2155a6004c18050012220103010a10719807107504044090600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 184227661 1250 184226411 184226437
    0x9060d0209090f0d0302041e050109120609020d03030203060f03070312050904060b0a0305091905030307030e1903050c0d0c050c0607210c0b0603011a1002010204080102070c0302010f080903 83
    0x400b2070120344080001001040105003921140c07110004003600035002403003242c3e0040021581011541e100c80280000d9800507180c0300400d03030900c8481c903800840e01c0c40407140d095555103442e02582d603001000306041e00c01e6a0140c2d4030b01e4401e0030301200e1303040b0861140c0a40e0001c079040c400100000110707241c000f590300e407032511010a000050042d1a26a001a40d12580000c00c0e251155154000a01c900d070311608681c9409200504081d0500320f088014140703070818804079042c94801c0e0441203440899408542da0f641c0342a003900c07240081c110040700895000981c07217104850a001c404510480e5041464201c0016224143c0715501242210300ca04000039a0310108207101040780c0c5045004801000d000703030070704c002500c8007800b841c060f1502060f03800000c0080c98140503c08a003104401d40201e110740d00c900b07200d9642241c00712081555000d2001141e0072000344003400c08035010b8145141c0309484c500000d0702d52515010500304014003d02003100311138001084031000c40c0214 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 184228911 1250 184227661 184227679
    0x5040e0607050a020c13050403090803030417090111032a07050105040302090915090307020102070f0503030d0902030705041806050703060b1c060b0403060e1b010c0602070507030206040308120609060d02 89
    0x140f0101c0c14482069070072948602102d81e10381d071010040d80001d208510944492494a4071000003581c0c80c0011200181203802100c00969115200750181c6041034040c1813821046211011a0f400d540020000c100d070b2036019009242c070304040d035814505141c80c1d4006410203904020008117036100f1400081d008200c1100410001082006a10340720b00e264292040107041007000192642d101d0300c1305900510521101080412205515408440303000340118600b503580c19071f0f0409040d40240581e494092841d0014168544e4050307200b0700e40c1d400c0340304440c01429142250850744054512000c05240c00010b120101d040f10403110108020b2008007940c1c0d80b00200100505000c2e01f12011829010400000b00107540c2c01090114080b002503450a2030f10004410b109140148904e001446850090001c5100d66004210441c044c2003038074420703900d0381c020514940c02a4411550988001680d10a08180b00520343e0441c0088071000c113203040600010b50058011070001c1d101e48040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 184230161 1250 184228911 184228927
    0x50108060d0606170d0314070f1e021f15030312020c150a2306131803020309100504030c090218040c03051503030301030b010605031b0f070c05040e060705 68
    0x41e0039121096920100a0110580315008580500700b140d1400c40750b440703000b20000441e0300078002c4e80c001c0c81002014a03100e41d84c1d148200e0307240314180d0300035040c001044180c4074110341002c1d06448082490b002402d1131000c0b5030710f0700301201d032480000c0741725407801101050701c040a1a41504494242c50700395960b41007041200b0091007002d0740905c091086071204100c203071102c15064403035200020304000303200d040c0c1c5c50003e101c41d4000c012190601440000f92451404004841c0050400180041d007100701e16000c150200f5122010742c096800401c4040d00d914104281e2400d0201520340141481e1440c0d5a0404000c11030007801d80c26a00440e01160840340c0d030001c41c90002004005004032040040007800a20080d141312007200c00f920b00a4070306040c000100c034101c9500204101f1107a190205c2140c00d500050032040c801e03c01c0c4855040074840b514098541400300382d176655610341d110b1801542c1e40e49540e0025000b1740c18130300040e6110700c000c0780060740030545003807442d526180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 184231411 1250 184230161 184230169
    0x180203090c040908130905070801080606030a0209150301060b0706050702072304090605040308150a0617040f1502040e0f04050d1103040f080f060903090d060b03030906030403030c090506040b0405010806 89
    0x5d100f040001e1a00d0391000280d095400e030019401124261240a041d0740c9805c00c0f5034480c01e04030391940d09540551035050044c180503040503807214207410345c440c0e90f030360080000b420355500f6844021008400710381740e402e000722841925040005800141144c61a0102c0d45035074040703800030311410300e0304804400d41a13201d5401030304240350706ca0740401041c5080d107000b40501c0e8066600400c0c5600d46810700049043c8544101c080e0760755074484480005c48481089080e0000400c21104040c07107101000c0080c45000007140d901e100d42401507210780c104a00c07018038803001405000080024414007002c44c80102e42c02d055610786140c4a01130060100744a49144100e0b40320a03281d22030039000084107070000c5590007a00b000c510640c0c08903254107031a42d607603000e009034555000c420305e0010400140d056108101c0b4032000380583c0d080012000004c0c1e881d40041307d040e030101e034807181e050321030380d9010044030b003c0d00c011503006003000c0c01c1056030381c5203005902899040c01658400b041103a55 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 184232661 1250 184231411 184231417
    0x150903092c090f0114010501140d020903060108100e0d0509121c030c021002030c16050f0d05070b06030601080714120106080f1b1c0204180c180203090c040908 70
    0x8004480c046240c1044042d25660301c00907900e0602c5940b90006607110300002c40a082d04031441650b680c5900c0259110328a0294800e00b02200900e81c20065150765450900041c6d0081c00020050100d0b62100d5212a091340c581aa88440c0b90b0010b034014a0f0007608030301a621020400e0383c54120034505282018500b020a000103031034940d0440310b800b40980d068014504156840e804d46517000c5552104038183d000540b0108a04103042c0700781c07080d14101400b403c030704c0e80c0100f044406211409004030300342020082101c0014034001014000c2c858009441c41c0c00c07160a800419681d85001d210a88441c1680522550743c116084180260360700c940103103228405a90081014030f9a921701c1540d41d851075018030903540101242c01040548020011001200152040345003086d001d0360204200c0610108a07401a52031550710501004000580c00092260002891407403c150003555013000c541204000355004004010703140300086842c580400080c2c0b0082000b24441c509010140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 184233911 1250 184232661 184232729
    0x902040912030f0e0c040c02030f070b0f07021b0402090a030c090f050f0417030a061211010801140303040e07110d030c120b010c170c0109030c15090309 67
    0x98100340010341400081c100703454560300151410040000f020004070f059503503025001105410507204a000c6042603008041010301c1841501c0c43c05c8070380c0b182c103112500000000c2d14405c506504120712005499401500496540010020038504500020308e005a820605010f1a000b040002c1c0507218581c403003014581c01001d60700707402e03200c415010081c180700d0100035440d418080410204000225818003550b08050f01e890b83c20f0000780c0389200c941c0080c06034540940c1d80c01c00010502994400011740c144a40801c0101c12000e0340010410481a04805592485c1014a12003130b900002105c0c211012000d9000d90381d690440c0903100d91441824844003801003a24640e081c0b64198000b4205d00c82c65101c16601a00e440301b120115100000590b022074030710340100d030115402c840121624403035509000d00d090705a02c511030039140e031618100c000c0380f4044c0901040040c10b1010350312400089508001c081c0d142e0710000c2c4107040f40d204110604186141d09a40c609417612892224 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 184235161 1250 184233911 184233919
    0x5030105060a3902030c0405090307060911150a020709061d0a0209041d28150b04020c0f010f0b180c070812090c010207060e10110607020606150412060f0902 69
    0x483c41031001145a664079100c128480c0c0528100c9204500c1c0c07c0c4560b60084850000440c100601c40c0e4801c001440d000005542c400c040320105c044955608480710030441150701e64544a242550011303240c04000c0d0070070541c450030164244001c0380305400950405106144080c0307141c4902c481007000307105000c5000c0e0820b040032010041004805c00c1c9540b5003561a080311007001c01d40111606d00c1e05a22840c3c0550038203c140440802c800e11f246000501d0303410300c00107612901100040403640310008070070312604400c6840310482028841c402c0c04004000c401c6c01840c0c110030002c4c0750241c0314014550340340102400324500300010030540345129070112070140d5a4040c003014406205080b0307280115480f60b00c10042aa501c0400e60404444664590a032800500c0c01005110111002540304003c0d100000e00f240d20401c0000900a0302950050311850600005000550005c120b1a2a08103410030041010310a000104840c0c030b90060000a903200326180c652020740b0790000b0103544 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 184236411 1250 184235161 184235237
    0x9021207030f0507080109050327030d080a061a0f22090204050a14030604061a04020423011d040c03090206030a050106030e01090f0b07030204080304140f0105030105060a 75
    0x8124040e03601c1c4040e03038000c00869102c05e41d1081035038242d520f2420000d00780d8000f4090032030401030a402c201c501030091224801412082d402081c94040700403288000a40c0400c280038841c6801c0c4900c2e005080e0218914544000c84440c2000038810b282c0103154004c0005403100300c048001618030100b011400e1158411b503660124200030790414040d05200720080400014117400d003002d912110000074000e003d16a5980e1200801450b0f88001d041c0820729000b500f982030f540350310040024100080001003c00d508401d14100702e8164a580c90611124056014000562818200302c6010480d0301040802c1500c2e0708401074098440002c1d0862008414003965030b400340c0000e410307946195010820440304540b580e0903030300d8503100030344900c2400c44040e004c201c020100342d03806078903420094038150392540013615680c4a5400711481032a0013406040034502002e010500c83c03400d1070070720b0855050400248031031040e0300b51402803252055562102403019401d1210240d500000080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 184237661 1250 184236411 184236413
    0x3080115180803040302010201050a051e04111305160903031e03020d06030807032d2a030215010b0a08010b0a0215011e17070302090a0b09070c060c0905130902120703 73
    0x19aa4004e404100c0c050350900000855441041c4291441283c806000100c0c04056014011840a01400560344200303403d9240b0f11a0301d804c03d0000d01e98802080c0043c2600d070802d81d09840d600300301910401c001c04240c0800110b41e00a072648182c9042c1e4803c600d01800ca035030141d000b4401d900e480b103101c5091841c000700f0f02c4402009411010300a07181d40c1c81180c4050b000d00b102c86046d80080b07103221454504101c8261103214140301194601c401940c081039408440d07001d06212000480040e8000030315031980080710540740340102050b03040701d800c00b41c0155014000b010305000b251010880414140080c0c0e108210201e148030348c1e80c1c0400400d503100d0000b002d540320081c000240318010100005890040341c4c1c842001d03140e00c2c07000b609440b42594204002000042e00d880707a201e0b00c4681003221a074495070085d0145905444e0440010b0152505001340d41403100d220003071002400007003040340c8910f03190b1201048512070008013060786100040d00440c0b0300c0c0c0818028815540040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 184238911 1250 184237661 184237663
    0xc13050a150f081627030b160e0112050903210a0c0c020303040302040507090806010801022113170d0e070311030712060b0a09020a030c0e0d030801151808 68
    0x1c1c0c08002140d89044281c01c800a056400c03550980d01606080f150321480380c00310748549020704603079a00d49451041c5482004d80342c00300b01a19042036500410704001e001d481c290f02061b000c0d0500c000e0034602030b140c1e140e00001e08207452003603c880b2a13603140c80c00a04516414030483d6a0078080f40d840081c0c40301c0000d801a004882241c030040003620300500c00080034001c078856100305034014021481c2508542c20312014140c05003044040c0b01400b5004a007060062090358080c0c1101d0000581781d4030316036014180481c0301d00d1002ca045180409001d950789a107940e649a09821029106400d012811411018451040c0c0c00b44151704d00940c110101d840802c00f04102ca0103203a0107840419401c0416403600c0583c030904050090214080002440d2900504045039005000720034040d920482d880aa90200110b0b50001e0ba07107910032450650001c5004515060035206035100000e0b070f5801401c500010f0145004c202098030030f100400307206d04180600340f00002c1c08040d05581d294605 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 184240161 1250 184238911 184238939
    0x14070c080d030e0c01022a0d050708030315012f0c040c0c020306060a0608070804060b090a021b0118080d090519050105150f0d0302010e01020a09030209011205060c13050a 75
    0x2d6111800b461018640d13540c40000c1030380b6840d040c1388a02410308070302c15002200030b10312400d0356003042101024502080d070a2120f4401041103070080d541e03078036207042e060700300250540b100d43c1800101da28410034031072103080546039440b4825141c0015800441b1040c900b00d05243d9156000b03050065101e003ca80c441d140d100424802ea04954094803040308200301005180a103200040d03000b000605003522a00101ea0090701902c8001400762801002c2140d01104858880f45960006001c40840d564992103100b5a10014020130042c1c0c01b1041c1c1200040306004054401d80f00414060310000d110350005561940c404104d8a12b00c2d14080b5007208030000c910242c0b00c80d460300000030748201d1145120844142c00a14240403400c1c400104200c01d043c403003042c0e04540d83c2c0c0c841070f45403c1302440242900603440e100d0f03400c081c0ca503204100314454140c110100506580c002030000400018240c1d8204240c180b10701d0700e41c40b010340d100604c8513803030b48480d42c080c00b041c2000850301808140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 184241411 1250 184240161 184240181
    0x30909061401090e0f0403081905101401030b030607050f120702150a1a012f0f0c031504021c050a032a11010f050f0d020c01051614070c080d03 63
    0x1031034100c540d16404a90124011034505c070300081401e00060021b48948440e0343c0c0011403000340c40401d000245a001101d2048644c0c5200340c04040c418840c1c160b10008020b90342000b442d0038800c0c1c1e042100403d807220b4000d0540c1c1c06001010550301074050b105c800361030301026032981703c05461074400c03402503030b80c0d154101e1400c0c01a0f640c00860040400c502642034454101c00c1590201c000c80e0004440044244105911200703160000c2156508961a0103412040020003455184eaa0400c41d604007210000e80c02d20951103c044c4903c002540e881c0b03540e101d90110380300e940036030f9074440100c20894460301c020308a002e814000000c26070403d0a4010b1051070384030900704049207100303021310965024000b41108800200c0712407030b03600c0350310403902ca80750914099040442c03a8521040f1604128014400a41c0101d01c400402c0340922401d64041440300a20109000c400e801030038072011107030312003480f48d0005842d4003404084c000000c001e0081d4000c44100c0f16401d44018014034a8070b003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 184242661 1250 184241411 184241417
    0x150501030605100308040b0a050d0e0a03020c03010c090b070303140403123e040510080910110703032003040602130e22172209150b07030909061401 65
    0x205000d0340307aa098030000c0c3c0c1d41c0310815600d81b0703091101440c1540c1011451004010040102c22800c1125000d0480006a450700404040b205894040c1c148888480e8079400781c2e142c0744550307078059405601c0c80304840b030510229540390282d0a04901502e40000c403040084086800e03c41010342c0980d002400300b10a00c8104483c1c2000054400100041d0801c3c544031a031070074070703244000d500907a000c503c541f91201040ca025918004101440c04032150040070800700801c110800c3c1c810700c00340358190400301080088040f0048102000d008030003001d410141c0d5036000c1c00c85008080c2c0210341c01140f01e51119240e01e031614095019610610a61207100f21440c00000d601101c001880d020300804004100d0143c120344400445a66410060751101d01c2808502114010000108011400c80031210b1418041800c0300002e0303481c940c03042e030109280ca4001d0441c510484050416a50319000c82e41c0d5682d8603082c115020f88041d00044039041c03500c40c000070000711095002d2107540c000e807 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 184243911 1250 184242661 184242671
    0xd080c0f06100b09130609181403040302011b080f041215060e06040f0b0604031101090602071d0702011508010213050102060114120703140102030a0b0306131203091505010306 77
    0x1282800045086104441202d841444840918904005545e00b50001a00001981613403000300800307076101d03484c060030344228102151050121150021a10701c0101c0021403409146600003018403020105504400402e40802c1d0b081000040844203440d949002e2652240d803035100d011450b103d8050700300c5005410319102d00140746980511000c44040340403e848a648010a010191600d24103400c03200d9501c803940111959103101801c06180a1000c0d00c200d10343d541c0014040c00a250002825980480300420094950b006007013048000440c612000b03031154101680580f020441c95000014812804104200d0550183c421000c00003800d4078400c2d61400160384ac1c09080c040d241c03036840c160221128605250414441400c580000c40e00c5140d076075158419550b04090150110b41d4000050042e00320003401148158002100501841c0c141100036003212003081d18020f0440d10783c01294946c0c07902a600440502e030700412182c0d000d2401c5113901009040902040b2001c910382 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 184245161 1250 184243911 184243921
    0x50901090516030c0e060d15050d0507051e03060405060402090c0c0c1509060a0305100605120a0b1909140703060501120e011d030706240e060d080c0f06 67
    0x80d00a1038003a510342c001c1c0e480c085110300401c402070003a42c442a400e10000110110150326984010324501c14818000900490720041090110003c1e904c510f204841d2141200c0206001103002c1c000c0302c03021904d03400c10b104500d0503d01c402c40304040299050040b1810003080c4840840c1d540c0c4a01e20889032000c0f981e4030126000e034280078080701c00781c082d07008000e03440035403c003120090544840528030504000b190b00001d003490380034065107400203884106202c00010030f2a540da0181c0180c1c148a4280f8080d40c400b05c1d080301c0300a03c094a40c0e034403020003c08036103c40c0900402106040500c00446840d0340404016042000740902d19410100005038003912900c26281a100d05075128000c0c0031140c101c0c40050100183d171403a15560b1401140340b01480500c01107001080c074005581c40781a0340c1080000ca40c1c3c80d500201604081510650011880034009002d454803032900901d151103550103d080a16600b10050101c500003c4401010302c0c001054420501d80070211900c07907840e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 184246411 1250 184245161 184245179
    0x9150412030e1c021302071b03030e0102060c03040609140d03020901020c0405060a061805030313061b020a1806080a0305120709031511090409080a02011104030c050d0201021002030a06050901 84
    0x10264580950000f40300141c0041c40c1000d014002c80b8550301016060244075101c0011000c0851020612107072489402c01c00c16800490480148000340094080307843c0c050821021480001e0000f400144e880100c0d03c1000310342000f06010300c03003107403c803641a0074002c80a4003d40c00101c0040c003510400301b00d00c00520f02401124400c00c00a098082460b02c0c084003540c1007140c421070110f258941c8200071410b500c040005c0c0c00040c202c2084200d1851400f103024203c07240b420002d0501c40404c8136554056282c16040f1802c58002c0041c0401c00c40c00710b0702603002008150801c5100f800b80b02181300906a0080192800058411140240303031590308068846941c0303440003d14004c0c4030b21401c42c40801d07541c8800c10201c040c0010341d00d040700040015045541d03083c400c40710345070042140c3d00380e10740c244103088400d0100303500b0a2425056840d5408454040c0c070455110340390900c158803c591080c019050071840d504800e5450342041c104600181845000d003038041c0925400025003021 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 184247661 1250 184246411 184246429
    0xe0f0402090307091812090f09050601020601030305130506030114030c030a1e060e0f0105090118150c09031a070e04091110091a040f09060f06030209150412030e 71
    0x2401400b8441c500420040034143c882c441d00703144148580d989021404443c100071b500d00d9955100340c1c440b030800f0351600507030080760441e13031266107008204036a0b40d80003e2031030b040d80e402d400c0603515214000c1003031b010769102d03030070071500003401100018468051b00d551103076148003201540d0100200c03009140c1d07511188900035142c0340c1403001c95098080004c55145400780245008a07807014a040c00605d80f514a5005070b055070340d518100030f8007040a2150240202c800a14044a41d0503a151180604d40b03040500c0e0721550b5075079030302d400c0d1401103400c08000e5500c000d07052000065041c81e03955140046402002141e12420080c0322031400b8800c0d9040f641d404503070030700b80655000500c07840c2d16040480703c0600c039040e080415448002040007031100083c054440e03640741456030046132159070751300a14601c1d00b0140e003489078001d908500c0e02624514075005031224070740340001e8103800d005040d59440940c0090081080f240e15901103134124003c1e141c5400380c1d5003034001e100c420b40d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 184248911 1250 184247661 184247677
    0x50c0315010311060d051603050f0601090603110c010c050a020105130b040809030f0f0a05252d092403020901140102011d0115060206040302030d0905030c010c0e0f0402 74
    0xa00000040c00080c5400d0400f030841032010340399500740080c50007250300303c95040d14003083c0142c0b0310b0a03412140c1c0e814050f0591081c4440d480f41b84608011001901628140c040c4c0000c4c152a45c03c0021681464000d85001d1680803000340807031407080c5d1000d0200c4d441807040000650074800007d80c800001d04010000c40d50102c54070000b0303910740d04d810782c00d034101d800401e60501640d5480700c60700100304840d4080300074001c0a00149112807030000e19116624211210000c0f500c10700da141302c0c1c04890000c040b2400307003040c100c06421400c62142c8901100c0d80003035001c00b802001103a109880c0d800001c0c0b007060b111803403d81074024002420f9510702444025030100e2407000520940040d0b286072140b5610600010414a0703040c01034410000d0040080030883e0740d9030905010703121001030060020010340c00500f01c1c1e42000e0324004e40ba84201c40c00b40e0306841d210038000040103410011221250806d000800c400302440703e004040d003c020071041d20908404002003020714207031080728246 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 184250161 1250 184248911 184248943
    0x703090b09011e02010b0307061805010305130201111207061b11070b0f0409050c09040b010f0203120606041205010509070503010209030705040504030e030303070801031a01031a0405030c011503050c03 88
    0x10f0145078540507005a826500a003c40d5229402c205035900d0070031010026010720788800c0508a4803d0f00160b0302c0c0c1a580c400c9041608200a01900000850840e4022038086c60622036038007000c4c00040c13071f003100090b8483c5800800143c00c0c00f401003d92004580d080d400c0c6184000142e002d0003204c008140402887c00741e08200c1003080546060402070003d00801d103c0c90703082c81e6444203801b00300c58044400b5030001c07a001400c41d000e0301d4240f0038142100b60900b000c03140201240c400030b50f24014200c1d00541b10b15100e01043c0240d4940042d58010304a60020324030031200c518020303000e000283d894960a105141003c2010719040c001d540c3d0403200540181441454a02084003505029000394103101c4442024125a102800214820a81c5d078481e68100d500d18585054185590314440750421038030303001440025000710301f0030765000c3d180c0084c1d2000d45403030801506500c181c3d4001000c940c6001d090080741c040702c1c4e074070303000f02d13030144040d42c104c4800a011f150310303a03400b550a0700d00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 184251411 1250 184250161 184250177
    0x160e03031215060406090513110304120c060222060e030d0503100b07200d0803010302060901031116110603160503090102040302030a0c090513020306180c04110703090b0901 76
    0x424a090511503400b052036941070002e50070807808204503034025045500002e05025081c030090401444130f1405007291781003002405042d05042e8a28000580024651001c14414070b9890b48038501389250f540d0804001c5560710a012070401c003c0003640020304074070040400001d6414065640c03081d0340c2902078007070300140745121004c44883c1d0000702414000e0151311030215854910348040c054491003202c170598030318504164201514005203913240f0600e00c1c0d070420000110f40405490440b9415141030b81c5034842d810050780507001c800c0f81d000c410000469805c1003007480c5942b8288840c01194640ca1111502c424099188400c40310400c5d0f03078891664242c20a8804c400441c2d205100c1400141060741303d078006400c0030359502090b2803014030510140b0600159100303172034000c80c20b0240003079803882540c04039031074203001000c0036144101d50843c070518401c14000e60300d062400130000c005000807e0465042a0040c05c819000214000b0000c9624078000080769503201c01612010a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 184252661 1250 184251411 184251427
    0x30e0a061715060a0e1f0f0912030905100c1a01090f02090f090405031b010f0b042a0504050a03290103050601030f0f1203060302010f051305040e0a0f0605160e0303 72
    0x17034545000300d18190020352004c040b0104d2400006200441c0c81303103541e040c681c01e59888006200e1440ca412506d8140000024140040d030000c3c01c0000700c0d0300c1a15004a042200c0307105507502c215240000c1d01c1024107100140300700b800580c407507060b164071a404000b42a00507007044128082c07945c0c0150009603e2005811501d81241c100d6803051080c002c89151000385400820175081241c050070941e9150108400c40041a00940000042c25903040043c8103422080c00c015520103113098a030420b00210160703d50303120780d044a0180801400f90307481036540307242010750300303403e4211441d008003d08420840042040c00142c100d903001002440683d00b180c0310704180c5203008008507010f1102c01110000925001130360202e101c003684000800500d140001350481c016214581e0400004100c120b45072100286100141c61007035600181c24051a60080d01c1c0c1007810001418080d0428030300010810071390442d03403154a4181c079000f1a403112420507204401d5280d1002e40c15081402808 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 184253911 1250 184252661 184252667
    0xc050706050a06051e0109050609030307060e010608010204080a11010309020d11130e0c030706021c120e070b0a120212010e060a030c080d2003030c07030e0a061715060a 74
    0x1e070410302c08480001e09543d182c2c001401c0003a000b81d07817400804680c444102540e0094010070081200740c0e440d07860440004000703038991048d0000108210b40d82c10044010400940c003807000b412000c2c00855841d03865034502e40d6940103800c0e0840d4094a1040101000d501c203024400f45250b015182030120402c658903680d40003c4000b641d82c021907690010300041c422401014038441168015200c0000c1308401d043c1090b40d00d401090555024440c00711080c110449034640300016460807820101724200c0c2040030b052107804000182c071403403038042408201040101540030064480c1200f415035034644005034001d648540440031a60801004a40c4000050a070b20004c0100000c1c4041d8580e90f42d1004000e0b1504050300c590b10501502d008150090746020340e60b00401107540040020000d000d960344401841c00d03440e101d0110350b081c2003500178402e00c4044c0c2401051119160385801004140c5594040c0040303002445401180f10051032100b9103443c0329014104619100910f001a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 184255161 1250 184253911 184253921
    0x9160b0705071505070b01090e0f060c030a0c090e0702030909010603110a0806010c050a0501021c0b0a03020609180106030f0c050a020604020618090c07050f070803030708041130010c050706 83
    0x41c14048200001760001d094910f4282c040c26400303600281905851098500d050880a421400b650040c000e1040b1003141070156544000720001c04a030501c5951000c9801d10899030005e161405194280b000140d00131000d8000303100b084d180704144c1d0380d0b9100308805481c81030a0b080c4103160100b00700134405101e40c1c3c0c456030081d03040c1411003150030256562803900300d50502c103540d5a503010501c070b800714019041c10b041081071b804091111002d850300160752020f00d8030000303201b404000341a4250340c03248445810f1090851403944840d40c1d6a0001901400c00c1044e07a01d2900c3c540a08203900c540110700340c640340710081d402441e00e5500c6900b40060f13030340a4030706c03ca59008103600341242903076074005580c81115040400c0d030b220602c41c076240b0300d0031804030341c4800b0036000000e0902079800700006036544641c95141560854566050095040316007410254016895143d40c00548201011015903141c89111030710078501c802800c0e03801c0312407200b00f600c0090001c0100c0000705405800c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 184256411 1250 184255161 184255199
    0x10e06041716021e03060705040b090d03210c0206070903030e040506041527020301050913060f1802190b0a110c04060e010e0604020f090108040c030b09160b070507 72
    0x4101103010300d40010b802e444135240001210710820301e8a41007801c05218880d0041c1c2541080c87c1000c2c18490a40e480707015003082d50b405886a01d2810302410f110381040101020302d50304461450340d10b102c018001d0f202a07001d40c000b500c03d03000803a050910031109242242c2d05540c40c003080005480800c4090f010162500350b00035115807d41c0300d4103d040f18184010140007030101240311a52a004030fa040d400115142a05c1c81440100503e48807298500d03805218620718411542da41e25100c3e0003041144a1041e5046c40e14204286981f00f100304242c6180c002c40c0c51000e01d0341138003000da440504038000d413041d9a006201c40c0342040d0080c003200120003a07510030364614200110100d41121529404580902600c00040269400c0018201d40001065805620306103032803041c007107240304051016041100080000301803101d108180406183c1c088800c2c0d030181026003001c0d40c2e43c1441c0b00d01202d101c05041c40025240ea511003200c400907400b0300078001d5a441c05a03910501c00f15004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 184257661 1250 184256411 184256437
    0x403230d090c0305010c0e040b0609010503060603040f0c0905010603050604051b070201030906110403030f090e0103111f080601021905060106030e0709020c07030605060306101a210702010e060417 86
    0x700800020001e00031513101c2c41c00e6541f12032441441208000a03121090b58180c021842005500d071640d078400100c2c0c0c2d000d40c0c1590310340c0c0d407a140e178901207805180c00c0601a120070b450210105440c20b181d00411f0480e9565a018070160311240708010444905546924000c40e080134410403045160000d001d03480d005040010708d0b01902e4841c5d5041e581c14410014001400040c14801c050b002442e0303040028040c60300315001401c0502e0b00d42c1ca0041030201070304141502c1d02c00745035503461403469800103901d4165016801c00c000005850340c0800d07200240076008034250840f80550f600000c0e044a600329000f40381c580d00e002c0055009003070980c0907003168054014080b0300f50b2031a000400b102c20016000300300c9181340d81004400c540c0c01422091098001c50700b0301c543e40e0b14009120342560700c00700300d40c05c40d04248403020000d4880c803141150110490b083c201c030b10055440c141c42c424000b0780c00034052418540103094440d241110020040d0401101c0c050300402041c02400e91070f0601c1d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 184258911 1250 184257661 184257683
    0xc0c120702040507110a0b061309050106080618060105010e060c011a0f0d0c030204050709170c041401080a030e01020709090b0109050c09030a0803070c0807200913110d08030f0403230d09 82
    0x278070076585a0031007603c131607440e0b040c10001300c2030030004140c3c441c6640d4559030b0b400300000c2c003080c4c6031700c81072003a141002110203040c03100740d842408850f00d812803440200100b0600140c000c0b01310805000e25849440e80394041111810601e8098513150362249858130514159420080203200140030309081103981ca10110321100f21020b070240a6940100410b250920749040100380c902070744480740e01c041e105004005c404400100c1c10b00b050f605050080080d54401c0040b8502141350b4043c01d141818416540144880d1518142c103854a55005002d103548408001000740300c3c2511070354040e80b0114840e1301040740c0c0805590090114500261b0b452000e8480e480b068000440503151040c02d0803900d40740448419500c003600d00240d0300c204e0a4501322207000300701448107401614004003600f20200e26030320110b051014940c4040096202e04240c040c0d45030044c4101c60460100c0c4000d5410340c0003004403140060b40c1090301c00501e20b0810540b480c00040c2c00da0300301c11104c2c81031030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 184260161 1250 184258911 184258939
    0x109150924180f09030c02270a0b01090504020304170711030a030e0f0a060813110409050a0201080c0708030103140a0f150b0a0e0705030c0c120702040507110a0b06 72
    0x4500c40c1001880002c810045000720031902d003044030b20b80382080540c10719000200300066004000c0a82d103c0c0c04860006100300b8000511001461241004002904007800c22604091035408140580401c5c1d03946051103031144140412071005841c0500400025107079078040c5e030354020040c613115206110103200e40300003001182c980009900118041840350100e1a2035051041c54030f005003034221036503a032152500c0c10140c140c0318094081c8110349a101d8007481030051849144020f610040c0c0304101120b06420000d80f21144a80100c1c0080c1c21a40401d5000080d10705403800960028003c51569103503640c8d29811540320095100d1500424101c200401d031915038118015001d0003400c20540400b007040340842c2e0001c41402d2051600003014000c10807a01c03041075101d4454144075a8070f49444107100b01e280160417032040d951144081070051048003c0180c072541d4405c0e00d040c4a943c569140c280c45404038131160303091230b90098a0140209108441c1590840805040842c1064035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 184261411 1250 184260161 184260221
    0x18050703030201050a18020a0510020708060f0604050714031611031c1b05182e02010c0e031011090d060902030f0102070804120c0506041d01091509 65
    0x49540300303a0150351340d0000c20025040d68020b10314100340000000c1450f610030703800201451200d01680340240d110401182060f4000c014050203040d000303080b0703083c23454600d0b40c0314034400c000c546480c0614100f00c0440d03203003801742000d140491010384159040d41d580070f0214924460850f1030400700140045200c1444000f40014200308003031b111807110050f480070060094403c4071001011800c00940c20103030150b449400d4504070401200100b1303082074074000007118462401c80e0244042c5541e83e07082c0e4101170114654031007d4158000b0b01052210050690700e0b14261000d25030150030002c117420860701c06511071001300ca0046981070900380c2c0f060101d811043c541c1000c407601765a540c0040198035041145aa000036941d009601d801c2060b0b031052140d000e903229811101c00048140010041d01841c900090800a46500c3e10741e981c07000310354801203c0d4444d103880d0214203030000c1401d080700c1c020ac0c04c0e00c2d801c00340e100362440d103405540130090002221031001c0c810951860080c6041d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 184262661 1250 184261411 184261423
    0x1150303050f25060c020d0e04020919080d0807020114043504080708210307030b0301090f02041b020616031b18060806030a020108060d0606060221070b0a1805 70
    0xa80000e1071080711a1520700702e005c940350f4406600940d0b025080395a40c150340106c50860303542c1c050f500562038038624000b184402120315a040c1c00e450980700f01082d545d8000502058404441d5a45041500e81d01000e83c201c852149000820200b01d5000401283d0885144400030f02c072600071101c0383e1800040000c402c01210700c2d900c5004000282082001c0d0304001140240c5445000b07041540f12000c40030842d0003080112211140022000038031550280c0e00007845580060000c3c00103c50a01e4440080d06122004034802c4e89420507a83d04602da222141114148a4004140685170a800d070303c101d400207002c2074109526407461020342143d40f00b000400f9191a2984044125405003602401882d500800100420300c0104251540d0004809001640a09081c422a00e03101e0100b185035201090140c44a810400c000038520b41c0000c40c4011162207120030519242c4030780040e850383c411904080c2c00040c030305020400c0c1d40c1c060350011000b85000c0c100c1028031a030710340e03e00341000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 184263911 1250 184262661 184262707
    0x3041103060106020c0117090a060b0a080703110907050306030d12230f09030a0e010c030917070504050705070c0905090a0b090304050109090b130b04020d060e04050d0201150303050f 80
    0x103005045c29099a5030070000702c0460321000d4045145a00e40030032103550700c1c3c5400d80094415034607480c4640306034450320903c0c00540070230001e5a01c0c1c20345905217442201c0603240d0490251f490b032800980700354480c405580c01104000d02400e50001c070210700301c4801403d0968001c0e06076070303110140605030a003503a88455a4203a84080b50f28601110402450071004100300ea03d50010000f40610350b81c0700040d0704134042d00f400c0410544155041c1210b407400d25800c4a22482c18001c45601500c00024401040320130844081c0700036942d920045505004080c0700520501032010280079541d0b06800140e84140032004940902c00c0c1c980781c2d045510301c180e8100100740c10009081c4881c2d41e01029400181c028517005010840c0c00401062030022000340a0703505958804600060741d40f2a011180c4d0b4074005c07801800201d48804070307000102c0080e076088849100782025501054018000c4e000c030880f541c210200f03600d20b10f880a4a00d94002022000140340802c1215a510501c07004a6030007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 184265161 1250 184263911 184263913
    0x201080403351005010905090f040305040909050a11030705060405040e190c0602062212110106140a090509030301031205090603010e01080f121803030408010e012304170304110306010602 82
    0x10305102c03c40144805050300854108202d9210500142c0c9034010010303080b280480500d0402c0d61a41000c484030700651f008000b4050410314240180100041c0e04100e0a00420662040040030401c051380c1d260720f4072820340c1205060104102c00d00c4d20b90300c4600070704140415996210003004402c006ca804d144400c585c0010100800c2c400d86504210320b5510021803001907907a92a8031b8100403205010304002440780c1406540099200c0c0310303c0d10400a40e03014002880b605840d90720000042c030b410107009006080d9000c00042d1054a13000382800f030041c00000c1d600e5079003503031501900c4210422010050180402510880d51103000096000302041c4140e10602d50408080c41d080008802100368140c1c007503070a045524007000304541c0341c105041001044a840d4134007003070442c000c5600010455203880a11032aa84040d00500400e65116980404031421100101030301039090310060007103950b020130308800107810b00065408c180210b98005192081400091a0031800d800400c01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 184266411 1250 184265161 184265267
    0xf060a030e0d0c050f12030f06280602010b01020601030f02040b0d080d09020a0b0c060f060319061410150503070c1b03050c0f0306041203090533040201080403 70
    0x18094180b01c60800f40d02600084c1500c04035541d100b41b5030740006841c800c5040c44d60300200341180e81d0b0240441822181c64101c03014844403006503200c600251080300b0165007840c2d0080f1b4150320220712581620b900c40c40c2d140381815141c0910000340310325286181c0113014012170401081c10314000d4902d03608140e60200e4144010b20600450700c12540c02502040c1051144408804010584941c0701c0d000d03400180d4155901e00010f45448048482151b03100341800d030b50301c10301c08181c00c9224603a032000d0a50505403980d19030b00080c1012807047c4440c00780680030201c20203224100079a00800c4034035107401444250703254042c03150080045075036458185242002000300500c104d0010490803584018101400400b107600c2d680001c0c8028064400c08082d203092038000e522406019810100700c99445902c0e007484507601104040203240c1143d241000d0b802042072005992245506039103010241e1110742e025540064450540750003c070801c4410020f0061074906180040f494400001c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 184267661 1250 184266411 184266413
    0xa12060e0f1207020f2e021e010f0b090105090403050a020106031505060a061b11040e03120106020c0301090312020a14030703021206030706020723220f0b0f060a030e0d0c 75
    0x36082024217516402941c1d00f01d2942c079100c0c210400d941d00340302450654071a0800360b0b001282040180c20000403240244812500f45040540c440d0102e0100040c041103200c00000400480410074480e1a902c2004480000c4c0064417540207880c61850600000c04c0341d64807030703480b0a07600781c00140e0754040c03d0b6a4010000240340c100b80c01d4000b000103091a46010750500c9400080114030f0304080e06041400c42c802e501030711541d00c012000f0281c00d040ea0303100c1ca40000e44109207070081c41903800512904094042a00d010f00c54a08801c0c0e26171a61030790814002c1040300a074221300071190a1100c5185025104a4584015031082c5025540140d03240003101c483c42010360040c0c60329001ea400004203001c02c540000c1c5040039281d110b840040c4606100c6040c0112203411807446402200f000ca030307402d1210301382404000d40150348400b882001202000041100c0f03200320030a6001c043c1180205003818500f0060040c2d00e100c0c0360104859402c0c0c2411071070542488030031000905010300d214 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 184268911 1250 184267661 184267669
    0x160302150c1c060b041512020f0c0d0807020a0b04020f0306040b011505070b071407050114060111011406090901020c1207020a0b04060824100c0507050a12060e0f120702 74
    0x10b014020340200030401d0600b030000b020218003546c05060710403014200ba150400d0300401c05d081072210030070b8056503140d0600c6175214640d000030214060510400902d012500e0203502110300c90060759008007545641ca488030049008003800507600600c0e05214010340307490602c036961242d802204066010752400001c5010307000804014420017000b4011500024000040c8941000652605043d8501c12903d084c03814418941c00070300562800840c2e0558051001c4680e100c0e0100346c0303030303030b6440b060b010601801d945890301d8051180c80e041002601a01d45031165581200c22440010f007064003040ca01c0b443d006007000ca03803011300c0011507000d08601e00401123101500800200b24102442c0030006016000c01034041e203a02d1100d102500440c41e840121a4940d010082c940900d035010b070b180180030001865400e0b696806003a80100710b5040c60b01d220001c0303e00b1242201c5484107951560802007a07403940c403401502410051080b56901000402010b201440c0300359541c02c3c0910400c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 184270161 1250 184268911 184268947
    0x61611040e0f0127150c1803050705010f090806180c120a0219030b0a0207051203150f1c060e10092301060509041e050d0c0b0c03040503160302150c 65
    0x954186040d820001403c1e4908003000c250145d02c0401c80c031400c0f500c180d5080d0403801a034142c150b0000b0002042c0070000a140080303c00c280c84030846a00e0b008012140c49405010710751103540000f0105051f000407070b02d20b000051080d000d50b00761000f00000500007003a1042407081542c44010b003441589400d41860310444038414561003c01d25565682180d000014496000c0b1a40070070140d0510005200741041c5a04860400f44d8038688100c8802c0c401e0700500a06000c0c41082134400c0d69810100400742c509120b5803075500c103c802e541c0e03d81020b801c4e040d180d400c20f4011300c20007110000702c07405004040d6100d640d64241c00070030000018401d2407403100140241c0c0c10b1020401540d03e0b8a1451038116410500e49422a007085004070b440165000c0001e000c2e22452004403429988100040e0002d40300302e1442400c0d4030750002c0020f0f540001d135801362250700304000480c200844034481a10151180c01a241858a5141c100300b44950440303400ca00a100040d2200381010a8012 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 184271411 1250 184270161 184270211
    0x40b04030b0604050402010c14030403050307080d0506191404020708030a020a17070804110d0b01060801050111150c03190203251d060c01021303060f0506061611040e0f01 75
    0x20401017403410381c000034a000c12402010702003074002c0202d0384010308103000b2200515000740c02c99940350018a03080c04a5030004144800c81d42c0390001195003468005c8020340c0c01c0000320039105143e030401c81c4507007001e0384024005131b10035420400c0311f000031154005140724040c404030060700c401c08228090002c0101003e400e0450080e1010008103a40000e0034071b402c190030040031010b100002020560703c141900d80034206440c0712000064035039001202c18180c4000ba0f840300d10004200400682d1803004a590030840c46c0d451000658202510f0082c40e4401030314000c0380c0011120f4541081268402d440b007100c542c292603404481801c04010000b8401e40a1405080c41c1080010303001a000044c2150b920070a800103c05000000c02d4040d107210401d43c0d1090445030350f5a14102c0020940605c1a1000d2800d02001070007500e071072826240070f404410305901e03000c05140da4201d4540d4040d2842a807042c0e4480d40006002c13020401030702220086000010b03108032000da011008403040c2d007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 184272661 1250 184271411 184271419
    0x1180e010503010606050708120402060702030102130501020709090503120a090b0c0a08011202010206060918012f0319020a1b0b04050c030d050a081b07050313091a24040b04030b06 79
    0xd82c1002500c0b230b038201d4080f80110b5118040c16107461000035124450101701950542c00881e031411070004000003142200e909808440710341c0d47d07a052880944014200192140e002406a00702c010f41e0401506d5000c104044001203074039035a130f105040a01d0030740303d40410071400b043c21040e41d504061704501400b007001d070f58110f840c200c0d80000d41d50074004124501a1060708041350a903a82390701c0750030751200c440e402071011241a5881001032504c00d204004140009129180301e0180c2000307d9004a440300207d5800609074800c100103540110318540800a08440e0240140c0f108130400504601caa5544040350a00e814007901e85003003000094403e400960701100c6494120044402070602c5041c07080b440e54407004e120b02c074040c507142d21401101000074542c0030400301000404032003a04003c4400c0d0726444890020031500322580c554082c080141684049141084038000704a0003900f0240481200c005010019042507000000300c2401090520030400015080c0d135111405035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 184273911 1250 184272661 184272667
    0x201030506131e0c0518040b0d060c02030702010201150f0302062805030105030f0f100915140910050106080a020715060609090b030109020d080a110a0c030c05030a02010f030b01180e01050301060605 87
    0x440b0f11700b081b0a030b407140b00d00c02c9545112000064175026618460250050002c100d1741640b884041c1d141e42c0540d400300d006506c2c040d2585180d410000b20030055440c03041114905138110790074003440b40c0c0010a00b4500301181c2180303420198801d00c001c00b4280140d07840d1034503549401d00b0b00d45041e0351444408916040768040c111100c1700010030100480c90307802c010413600c1c410b06081e5503004440158401650403c40010791031040680c11038000d0004404031000d001c1c0008190040b59800c0c094103000440450210b0307103400c616005020b07807a00403041031a00a640003003c070300302c602e250301440210721a404204128059441100f141c01001d40c024080c4c405c8540c001400e002003801c0c002c144a0000c540d8110003803094904000e40ea080c4d40c01c03030b0200000c03401c020000c0c041a20086844038000384001c11281400f150310b5a179141e041e103403e0044442e0307080c140d01502088000504101da140030500b684904030303400100800d0b1082030b81002d035040209042c03d66603603400007c01c0c06010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 184275161 1250 184273911 184273927
    0x20714030301140a120b0a020d02120901020406090e0103030507030e01050d090b06090106030e250510050706060609060210050718030b0f160c06050c040b04151e0207030201030506131e0c05 83
    0x1c0b181056003e40300050050317440d4000d0278501c0081c06541d084030080c0500804011400c001540204103503900307034885a1040c0d0303443d821100101c40901006000500a124a4001034080c2c4051480d4a505050680c2086c0000b1003080445402c607000307490b070101080900a050401e0b0360510301602107858240900200000c04558400070044210b8580403c04011160420703440d40c0540a0b00000784060b0188000312402000e98200100545605240240c001081030059060310112052034002d02888012603602e8802018000c20190030300100d1203a28402901d010300030b00156105141d00301450030301007900440210014024101140c200c400700b010a6040440d0742e1b02d55a00030008207041c1d80d049810709050040e5404525203071804500440d0b00b44072011858000710342599501e45050090010b00d640b0700050f4010b801581015009001551098020f50740c4508003800800c40030111180c84002c8820058200700e14400c002d4024031400c110b03001d015505907491800320304100e40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 184276411 1250 184275161 184275173
    0x26090619051302190806010e0a0c0c200a030c09020a0809010b0a051210020708070b13080f1602060d0e07060c0507091d12030a0606030915020714030301140a12 70
    0x410b6002c1e205502e0030f00c000441d4124900c0c41000b0b86807100c181d9040d544e4824820450110079120f880740a400c0030030072006e080c404c2060b4142640c11420030800200507842c95044070100700302ca9600043ca944011020503d031a6001000b44611140103070384002000d001416040060304068059052070f80045d402c0d40c824041c5410389004944151181d00040011480c2455400140394114008039914082c0220500030b000044c1c010422091983d56406989144440c00203004240071020701c000409c0c000b2440107071410006010740362841c810300d60009030f06a0001c540c01900261a40c94a68044205100940003840181400c03500c44d2415594162108542d0140d00d8400355580e00008d010600302c10008a1800844161242580e10b200a12882e502c00c45410400301c3c1041c1300081e0042c0300e031203150038480d00020001002512020302c50080d40c4513880a0f102c180044261108044040c001180200188141c03022800130040c00e00c4000620741c0d00592079820710110320b0003c110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 184277661 1250 184276411 184276441
    0x70507050907180303020303010f0e060d11010203160b0a23040209060411070c09050601090812180901090c120504030e040b0a090e010506030f030c0d2609061905 71
    0x801214510110b50b0ba0b01002c9404004400701210a1402e04200005040c0c0104c0214140e4042c0b00c0202e45080c0c81d60b030140d01a8a003550356907041600341c10107402190509541c4010348030148103507880d1000704c071240e0840030418035094400d204544240709a200c0c070745c4243c509201c90400101644002008580310041000f040640200914000034150b9910303a0b00c40721b40343c2c3c90f800c012030700e5030000d0502d0f001805290103581c48080c81c2c00040b07030b041d40c05900018110703078040e4006d08040e0074141485410381c1200c0504542000d5540020240d0350f5503140444c00b03486030b02030000700812800001440c03101502d88030442c02d8682400d00c80801d50200d800100000c080d5000f00e16a80002c0109410905503440402c02c2441c10800341d01003041074002034051003040b401c4400310703c8003501e4292a80302e8007040310005c3d440364213075400c175500584402000e00b2100450340da460122901c3d038400c9800441d000500c3e80c101c00308003e08407840c07096519152016840810880c03614800b03241d6012 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 184278911 1250 184277661 184277669
    0x3090f030c0f020a08010203041103010e2508250b07021f09030b191104050607030813050a03050c011410060c02061605070302011e0503070e18040b060f0402070507 72
    0x4000380150700203001c55000403010b069405426410300907070f03c0d400719000350020740781281c0c0e421003000004140d1505000d503111a1013014040c0c40300380704030490140b84500d55814081400b0182d8400281039800740145100345a80152100b10207180c192010301c81c02440d000105111410b012000240c3c0310b443c8220042161201e030a50b032860078000a0322041ca43e03500c01481e82d030f200010083d8854a0400780b0f108242c2d418000e04c403000c281550300799280114010b042d0480024032654010911030381c0074903001107007403020500741030840c3c940d141000300c1c0c003105030007103800025040e600c40001d2283c2c0c00704002d203003200301441c240819410210b000074890482080f186040e82c3c1c0c291b554210840c0d88046014a40704552240742c03800f00e8440b103162000f07038045103905076087e204011160320030010500c1c55445074515503601c0f405603081d048d07000c40203800810015040010903200d0000d6401140900440d000ca0314042d0104451480d21034540340c041d0f801806207500085002440d17400350303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 184280161 1250 184278911 184278917
    0x2112050c0606060901050c01050411030c030105010506030403030216141501060507050a02061c0905010c0906080c04051c020301020a02100606020f120318030d020702030115081f021b0304080d03090f03 88
    0x19200c0c81300480c5d1500501030080300c20f518200910007044040106100c0508065080d500d410001104040c22a8424481e41c1d8200b0010000600028401d034010203459101d0304021040360100c1e05d03201c81e000d01060428420340d100701c60351300c1d1544d0340c0b44021303004001910b0400d282c00030660b00c00c2c0c0c030703070765140c4000380107040200300840c501c1c2e01248040011106100c08202c1e2060310300b4442c0c040c0045004900204e15a80030128403544101021031082002c0b6010a1500b07107081c2c1030200c503580f0510301003a654800820100169003c0c0010000251a64010030b00c200008070a00221400380d4401001e55000d05900d512507a000710380300c800e5144d1035254a84030383d07c407076408185107c60403001426020006010ba4044011fa010b064118001e85c020032242c41908041d40f184101802a4001d96121054801204d810503425001c1450701d03400242c1040c008418003081c0c07084820f900b6500390008101441108010002c1c0c0d030610416203410301c04c00300307a03441e030084c40803896402400b0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 184281411 1250 184280161 184280167
    0x507021e0102043809011e12050f04030206090706020d03020306120a08040f05241b0304260d080619050907080103021201050c0904152112050c060606 66
    0xa00102941500c0040409260920b034060741801c1c91410b50784c480c02ca00008400b921542c8070f140c0d50110658004403030603150382038403039000e000e030302c503d02030120b4544100140a10300341502e0441e401040e004004031510210f00d030506142c081d0400200400e4084254440542002199030011341c0a882100701d01780165a030303c03040d002c103200005001e481001885221241c00402055000410894109020340314400741c035242080044171a07170f940c8103000782c0b070954000c4d18103030a0310040403004840800e9130340041ca464002810b681050748100c241c08296000700465540c0f010303410074851500c6000e003d520016200c040e0042c0350207003240c0e00868031107108601c4002c6400000c8090f15004101745542d00d00503400170200c1409020882c02415100940c0c010751505000b01801030080039071542c03c024040044c000148030001001c030442e4079040d0000748128107400007a22000304034520484418450401a03c402806203003102003020400a5008101c004203030503400110480d01103503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 184282661 1250 184281411 184281463
    0x1a01240e01120b0607140f0601030203150a1d060105120a020303030115090e010902030a06060f0905010e041d030c0c12120a14031303140a0207030f020613080606010909050702 77
    0x40800303d020350f80125000404130140000b4140b00c0300006220002c0355046030001d1403658640c02c5c01c0c0b100a40552000c80c043c1c141d088450300740340d8490790050001540c0729a604c8441d0b03070b03c0340c02140c0c2d0040b82c200750014082d5051100b4660f142c00d00030001400710900c90343c0072036070700c0c4414460178002080c9202400543da00c51107034a4001d00c03840c88107010550f1900501c10081d40280e80d4500014508000040e296001d440d0030a0807900c0f036100d64000034a05001540c480f50f2030f0b0206580266200c02c48203814045000720001c884c02c000085880305030902c480d9280050070501c0c1881500005040240c0c030400244462020b1026681a51105812030003922240510003081c4074082d07002c010400141d88460111000502039a0b89000c030781c5010b9002c990a04c5406110b40060300140024004100c104c00c00640aa00c050040d618055500ea0110030041c469000540b0355004070b01842010343c3e00c400403901810480404214a0501d50406556106050640071212038050000c0c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 184283911 1250 184282661 184282697
    0x90601141b03090603090106050a17100e030408071202130905030301090903050d0501081b0a0f0501030e0f070612050c031005010f110601061814030309130204031a01240e01 76
    0x80f9450b5002d028603869052003401c590103442a409240c0c0030b001c008100144080403007014844180500c005400e11808140d1417101800c0803103c1450107200400c0000707000c0304100a200001c1c044c1050f800703041c24140c810070014680d070121031a050342c1000004008175201008990446401140c0020101f02501c0d05403518003506000f0300740301d8641030002514500100e404014007126541c1c0078144404130040000d40700709030148100700c1c01c000c44184619400384d4801c0d40226200c0c0c0440d1341d0301c111a038030189007800c42c0d00309000203007000280351110300a0f4007402d908120664440c50840c031384540d00502c40a00740c41042e04000c005050160458010401340b05504107400580e112036031a40e00242c02c00848000d0140d0400600300c0000f050812070340c902849003002000b07075241c8410304081140b07401d0369528001441b9800c0200000040d0410280a0801c9500d601c04890b036242c43c0000c0140c409078500c40d800300440711010075415600c480c5102c000f550908141c81200c400c00191 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 184285161 1250 184283911 184283917
    0x501290d090f0c051003050c0406210507031409010902030d050a05130e09190b07081b030f0106090801020909010e0903040b07080d2a08070e1e090601141b03 69
    0x14007001d110301c4008090003034590304001a04c50a8488491600f1280713812030444404581c0320b401c0602c203110604c01702d440f5401c041180c40d86070020704a62030101d040318007181c0d000da8081011981e80c0354804201404002c01070f621200e110001c02000040e50040380e182c0781e80840c1c0f181004030024010302c14500440c151025030704220001f1441070b0f15222040180801640c2c0810244541402c0c5058511f448094011242d441402c01d6285d8079841000c1c0e400101c0540841108665078000c040c11180520141d446100340c0303079040003254504040030740840700c00d81000c00240d0042140310620317220001118119611441c484105680304000c4600314000c90308000da00c1c040c000303540341c1400086006019030054a82c01042041c50b01852101d030a0a0081190303051820390704001038041c000d0000719400101414191840e8101e18001160f0178800001100f6400b20030322080c6840c1031040169034031500031700700603c3c0062030b40d10001050183ca5640c02480a5040820112481c24025 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 184286411 1250 184285161 184285163
    0x705040e060621040201120e0309060d11070f0b0f0906130507051c110402030108070329090f01061e120203010204120f110621040501111c0501290d09 66
    0x380342c0e072161100700340c00b00f07400544080c0e000403003200001c44212810303c40c19401600e081e000b149801504801c2c486107410640d503244017182e0320a1011070000b2000000c259807440f840071010504154944030354030b000c010707018200d1060400200080307004000382090b00f003216200700d29100103080c0341541c6000c1864001d2a00090000b0b80a2409080c4074161900203126000c110240340502081c03200b240402d2103181d140d58032030101040400c4a0081840c40100c8003c180000c0c40c20844440b50104002d540400341da901c920a0b42034900741c2031060101034072183c40240e0034400b04004214810000b4001c1000101d5840344600466400358111070040c114a040340b020204103040c4108031911914003500c460002100da555540b6100c8121101c140c07259403280110f030741c0d904662148060040007201ca642d80c0d5040000110140d0001c0c1500b9107002c0b002c140b009840c64900000d8840c103900120184820785040b04403020008134280c002c00026447d140c480c4103a031103a41c013a12004078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 184287661 1250 184286411 184286437
    0x1f03020a06020d140c072306070c0509070935060c030106020706020a170912071e05010c020d0303020a1b06020d1b080610020703050f030c0f03030705040e0606 70
    0x10300091040d0003003180000c030043c0f511000780403240c213600d2040342e12070340d030400703c45c1c1d007000e00c0621200da420307071803032001540c4007113981c02800c00c14001c143d0b180d000800c10b460310f8141c0242005645013103414194006000d140c1200241d02c1d01955085581e000f400c0179240c64a20700c5914480c240c0111401410b0364010111070482c24407c81038181e540c401e000b87c0c2d00601443c007010400350700010300034880c954801c5a000c901c44204680c0103281d040003900c0e50740040450101400b080e02001034070050501041d4121040000074010454086581d00071418408100281720140c0c3d0303241c82c004800394160802584c0c42c1d60681c42183c540010441100c2100b40352012401801195405454046600741d4200030080340c202c04000021192040d08000640541c00103e80341800e201d0380f03041c0d612500407244000d440b80d82d00b1703041c44a0003001d10340035800480c410440c04402c102e20300d107049009014502d1400d01c400001c3c2030388110700070003420f465103802103901612030204540380010565 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 184288911 1250 184287661 184287679
    0x21809030c0610030506010512120711090405060117010902150a03060806010605131703070f05010b060706090c0b070302060a022203081308030316080405010b060f0304140d05031f0302 81
    0x200700d00704200b40384c04141d030139128079000400c60381030101c510040d0240400060202010b0852040003591003107100b195680e00004507000103444d08880203018901c5240680704640c101941900380700b0108100c006503038107040d00300026071a4032807002d54000c0480307001642c5100e2904c1c250060145d99000092034410300c000040c285600a0240582c441e95445a1240560310318101d0f00034000450340e240c29400401c4001c0000712000100030500d80721700c4c00410003c1c10713100069140d0700304034015110191103501e10310030480c00b0365511010745035410b00641012003a40b0300071750300c3e800200720300400d82d13000880802480e041581c55403c03080c14440000840c1c4c0380c1c0340030b1003203070090549080e54001600d0089120302010066a00c00d00c4d005940014011048204a030341000181c4103440e19582c540d0702c08400d49a800040ca950030482040310394909291801c442c9090303809104501ca42c210f10640007102d680002101e412a602e04600c24414400400003000f002c241d07403000b94003117940 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 184290161 1250 184288911 184288921
    0x206030a0615021b010806012a08031501020106050915010c0c03060903050c0d0305010308030c0d18081902030403031407032f010e03030f0a050907080a080d050105010c021809030c06 80
    0x5801d50a51a03128407a800d16201c020040d10112425287c96002c01e503400149085888161b400d5101040040f4101103d1000d9071100c6829030300640d101c540602841805407101d580901500f030041000356490203503850500c002c01c41010114403000d04212120341540709100b01c100300480a1500040d003002000b400345400b038003541c07241c252510540240703400c080405001e40301d02812a5000640c0a240d41c0e284120175030a94480d580d454100da55846941c011034040300c4020b40d0143c480d0320119680d99000c6d0488819000700780038802107610820003400001d51150101e00602548a8030300d0310f030900f51906840c0d101000000010031420030700c1d51402c0d01e40c0720a00c1d08114403400002c0040303410130450140c5a1000301d07001240000b0010101d04008200e81c00f086e80450b4040a440c0007a44840580342883c0c40f180c02a26140c41c0407440c0c41c1c00c403000c0c0c811140101030900701180c038100c2540c003045441c001c0401d08030405402500140300c07401c05004a40c1d582d9a400103454141c900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 184291411 1250 184290161 184290163
    0x501060b0904050105060a0909020f0c0f03221404021305090709030605070903030203091314100303080631021b0114070c0f11010c020d111e0d0206030a061502 70
    0x4420341c040e109038100400001caa0401c041194080c180784e42d502c0b011030703081c40c9030301c80650b01079100c500c88103004200342540608c0611035400200341c01c0002e141c0d0740654168010070b81c0307003545800c84068022a800c210f08008100080c201c405e056402684950040c03501d5a40c2115960203203070024244e0080205040e4812101d03000c2da80b2400c01000300352109402106c1c10071003400300402580c01080a407290b0320b058264079501c02241f07040400c00201040e0840e0b460581034512800c5440200000e000b0160080342241d884034095443e0344070403c202130f0081c12820b03201c0240e9644145840400d0311020725130102d50a000d843c003003903030506c0c1d08082e8140c02461510845c0201c002c9040100d524103103c1ca00c0203d107a50484030703182c070003405625592403070842c80c3c80950510511a444200603190904c15003c00d0340a404044803a02c2e001c1c05124000c8034203aa0314015001100c0803095035070f140c514000d20150140c1d1507a4903a074420000710000d01c40307a00f0582c040081c0498110186074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 184292661 1250 184291411 184291417
    0x90601122f011403060d020613051203130e0f04060f060503190605011a1e0c0a151b050f0901030f021305010f0c0c03110409060c110705061207030b0d0501060b 70
    0x6402e0303850b41d140c03d042c100e0b22099400b0640e4000d0f0b0040b40d604203000945810790181070500014260b42d0301655403240050b0220701d481c1100141a040070481c0b18410001100c0d030002409181144880ca1400d44001c1c028801e0080004000940d1940d0602440e10554000e0001d010054100c400d03202c481600c08103202c150703031011902c00f400d0034008181c410009419080c80f00714210031b5070501d51004682028015850503010110809002c00d01003000704111030500035014640d2903a98030902840c80c07007642d02d8070078204108040000107200346a0b020040b07500002480042a071903044c0d03100102c003d441d15120345032041e0700100b40d40507625944407103603049038002d0b22103000c4454440410381d10103144100c060885a400602000400c4108000c2c0580920080c400502c07081c0559034041142c0144101c0d1000403401e0900b60500d4000f00818405010f0031201c00342400107400c407030410240001c2c801804c240c0c60b1000c0d50300c1d07a00c40910316a2400d61200091201c252aa075244005030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 184293911 1250 184292661 184292753
    0x905030310091407050a020f1b0918060402060a14030115090501080421050706090b0a05070203120414070b0414010305130b041b05060d050114030609060112 69
    0x5406a0000d8800c00500c07a061005074043c025600580d42d8400c1900e80c3c0e04030503401c0c0d0547c01002011440000180084021300c03090001c16414019004103102007440b0040c520000c5801f03089400e010740c10300081240c4d005030704540c042d50310210368000701c0d1681000484603188240110002c508050409001e01e60303105c05503915450140d403107004444103081610003800b03110f00c10015030321158140b4100c0c1d0943c04113040861500d892a0750310f00c00c0b203214820036900806000103000b42c81101c0d004030f5401c4015440158186000c0b10ba03000410f01000e84001d00304510b11040c100c80701c40500c0356200a04000c255079444940d506080c0301c0a011800009000a01e8030700003c0f101c94000003550080381d001240400c0590700c5903110046034009520210f0442c044482c0061a6901c031b00043c40c00d04006640401c3e213516000400c041c000513600700503ca5005142001103109000a000b4110754007003035009044072217410088041c0c0340c0c01041b905045080c00f405034004a03c03101c1b040c580 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 184295161 1250 184293911 184293931
    0xa1a0d23071215140a02070318120501050901110d020c100c090303080f072007050a06030e0c0f0f15070510051905091b030102090306131a060a0e0c0d09050303 70
    0x3d8507800e00c4074080710300315140460010004c1c00852a07044280d400750011510a040c603a09003504c0b0704504490608035480b01500042c1c0c24050b20401038280503030707a0481300080082c4040c10070001041d90500a0f12515030400d5408103074410512402c0003002c8001d0f44981c0200000458030b0700007013030301855000503008524080041035038004004c5000348225041d58803060480d00c49000350700c1000300d290600c45640310700307900844e030b50303a98020311390040100c3d1311300080042d107071001c02d820081c0b0042081c1c4559100c051072041344d2240c40030755503054001c407024617003a0740e56032a810070360141c504068614441c100c1e0f03040004010f54031890190001810040d1403801e890744000c292007007124500c5064103c00035403c070040101c4404078140760700a00240c20010120302091501c0d20032101ea4845118003400d01e024415881c82d00c0d21034001c4418000c1c464070380360000c40c030380b90716510402c0b06624042c0c00041c044982d5809541c3c0391800c49805001d02c0d00e0303074200265203400655108041c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 184296411 1250 184295161 184295183
    0x1030c06050301030305090f030a02030f010f0e0a080915070c08030d0e0105060d06050c04050904260703020604170c060a0b010e03012c1c080a1a0d230712 68
    0xa00c1d004038140c038122541940c406107443c0904051029004a480c9095050300c503142280005a03030038001145a101104000290070340d10703402b0001528031020315080160006c0b00d541c030101e800d9a045403010082662049581018400302017032911a284010f80b0070901071202003101c620200c010300c90070901241c10b00c21103407801095400c84070180c0300c0c02d40c0114a9050f260000303135207820036507210b5100000142041e41d28008501e460078100c408a882000110704980311201c0c0180012a0342d9841e8480d41c00c3c680d06a902941e5103c000c0c1c0702403d1195100e815400382d15100e0100c0d0000303045101a1013042c00c100071250f01906019100a01144203032200c9450740c10148206d41e014000c840380304070448000c40e20000181d5440328002028013518801c0d04014a0004032200715000c2c51f901c0e03201c50728201030301d8811240c0340d620142c0c00e03c400d030a42e41803954401e42e10080264100740c110b414501035500391400c41d950007140c0d4040b0300410400041400154144049580c041d40c14041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 184297661 1250 184296411 184296419
    0x102041802040b180105040801020a05040509150904140109230d11190f0c030b010807050301020406050d150801060602070303080c030c071209120c05040e060702030d020a031b0801030c 81
    0x4140d01841c0110022444240800c001601c413482c8042098001814a1850140c549030354600ba80d00050141d40410f500041c20009030400309009a0b001400104607066880b82d0700c00503054030400741000e400145690000d0114800a510110310541e0000c0e0f0340000407907400310000f9403100d008040c4001d0048402d40c996150041410548114420010300700c0c0200c0f40d414103a5040c2201c5050315003030410090980004c10f102d481d600510302510401c14107626240b43e60345801c01c1d541040f4020790040c0030030080150018240d90700d01c00d0354580801c0440060102814078101365000006a40c01c1c26000106c5940200c0c0f5002a01e0003542c0303c0341c2a95560f0a007021501c019541c41c54105010017000001c03035620401c0384c0f2820070702c0c034005045590324011b8a6090007034640a444242c12198100002d10b0719109000041c04107002074012403500e400b001e03480380581d541002031070b5000512066541e119500080005130f00314411110020b0600c1c004100078000d000440c1c1258600310041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 184298911 1250 184297661 184297709
    0x2d0610060315141e0406030507050307090c050403020904050c1302030108250e071e0206060906010e090711030f0408030c0f1209040f0609090f020a0f051c05190302010204 75
    0x703040c0e40d4a4140c4007100f8480d00c1c1804038504139045055842019440128050703a074070f0045000460144004040782410f0004041c201100c1b40d0040180c03900e0601d2541074240c2040c2614201c80e0103c0e10408c06945900b80603042115184529501c805c4910301040525640c0c1d001d1410394014a003243c004444146480c00449042c41c0380b1a00034150160401009049105842c0d0141040c03905011210f80010b400092f039562070445d80140c1c010b034007080340c00d08090603842e92114003442c01807a00c0541380041040d950700a04540f040003940103da19010604000b11004140d100d0713149a9120f41d1041016144e404c4441802410b018508000910100005081c481200034000701440d240d071407003c00c002000300d100c1c0021000d450351030010b5029918400c41089030b00030003500c031a0b001c251041020304003098100410801d58003009200c03d484c1c501684c00c1c090010000e000d000005030421600d45a02c90703545040184c084c85608003010340c190060006c44040a02c6007035000030010b815 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 184300161 1250 184298911 184298951
    0xc060906070914031b0402280e0607080a0e04020c030705010b0a0504330909050a171606090501090f030c120e0607020402160b070302120603010501082d06100603 71
    0x15031680c0509240354042c01002d4940c1c45210009100503d061238400580304c07641d03040300141c422401d00c0b0064107103c9421441c501c08500042b01c200d450700c0000d503206001401220750030700030440e0b820b0007801c5684651341110441d50504040703d03150116440c00034042c0c64450161030003512620703000109030805026500088856030380d08070b680702d016000070210300310b20607c400f443c4a850900048401c08c1c0c1c070070004014000d2002c0c00041107030741000b110005800c82c8000030344c4820441002c03200e01c841c44040100c0d030303c4240424154058104907004d07144050020f000303001c600703002504060308017081000f410b04c6030b0805445100040c42c1503601c0b1801000b503c0d000101002141d0051402d94024884080680002083c605468841894803a0211100c4004c2a800940c501408104041d06a8802c05c1100240040d604220205417240d03041e01c0b580c00c601c000c0401d800c1703031101131909580301d2a01c80e10882e1060300e01801c501000c141c49100f07034800300c0d02d40000d411042c0c40600d09 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 184301411 1250 184300161 184300199
    0xb090f070e04050a120207030611030114010903020f040207060905060a020306090a05010501021203041a0a0b030c030f0a080702150a03050a0c02061006080a020f180901060206040f02060f0c0609060709 88
    0xb5007901421a103032018207010009921741140140c030300c044002405441850b404002c09402c8984940c10074074000518940030055a040c04480401000140d440340000c0c400080c0965000d602c60020349410300140c503643c100100140180020044e83c06402c3d4051482004200d40d500c0c0365403540c11586048035401c1c015540184c01c0000c092040451074402160001d200d169007d54044810182003100503081e13402e400b0182c0c484504041e03a00c0e040280f0201444102c1c0503240c208103980d00f40e50364821802c801000e001000c645a415592070300c0d020310f040207148038507075a100721403000140204000c4800e41c042c0f502e012010003040b44009011407040ca1140643c600300c50410340e041d14840c1e4000e2003285c0c000e4003045220f60224280c009444814460161a00030450b0441002a504016003060007150700100c10030002c140415840c2401c0c3c2d4064600664401c4107800300c545501c154142002584200400c3c004008030014643c1d12661041c0da844007155110001c1e040c1000800f90 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 184302661 1250 184301411 184301413
    0x80703020105070314070c14060a092105060a0f15050d0b0a1d0601030b07080f011e0e0103030c060f0b01020c0f0d120c1502130612090b090f070e0405 66
    0x1051005500500c001c20f000c0e40079007814003600410118a00c1907500642007100d80c0c10940f001080a21030080c001040b400e42268107a062066186008048035240c4c070507005030b40840042e031044030f4030109490311026000301c15203444d45440781101c030140500910180060349805203441e00e1101e075104010a643c0001c2a980c50450103403241030780c0740700c040c00881d50a03590b00740b41d10006422440c10001581404040c06056145007045826502c00500704403d200d010f80403c16840081107400d070540c1c5800030b50440c2d024080e008100c42500320313000300e00801840400481456009107098600c1840703104188400b94005c4038807021348070800d800c503001d6445941c04468901d0801918801010081d050b12a40c100c1525645028628443c0190100b03602103407400c184450303084028a071f0540c100c0150310348280399210480d0002103100e500d042060100d0506101007158008040080d007001c401c0165040519443e6120300c00c0b5002107105100745440000c186118000d07252265801070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 184303911 1250 184302661 184302673
    0x2060702040b0411030109061a2508070803010605071e020102100f0209030303070e0909010e0a021e030706020d180506030c09120f0a110d0b07050d11040b030702010b060408 76
    0x15080c88007810300345404035030084d2200c0b0703000780c1d80516102560007003070b40788404103045242500070400d1001d0321600ea031480703404200d06168506c03100c0d680310110041440710785011155051481c09400340800060921030004000111254814054500c6d54058504000316010301d111003249288a0180203000d600b142c003034010009880c5d444000481c001d8100075190050320000607046510440d42c540c0490104242c2008604010103103a0340607826030020170680020054144d500c80f41158001d12604010440c0d5403c80b1040411544601001d070840d0521621203001035110700004d0204400034031048042101d408000791400700320ba00107040d003480c1d03851700031407007809038880c40ca0705030000740c0c0c05251901400204034519484100e1310141c034660f20503240005505007514103152081c0d00070000000825000700203143c0040c102d040103552184101500c2010384440304201c4800d101c081400980c6003003c1d80118403416a40e4001c2081c5c220540402c19540194055071120354486 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 184305161 1250 184303911 184303913
    0x1002040906152c03070306090b041b08150601050903010e0a0209160509042417010609020307020d08100f031a010603060b0708030601030609020f0d0605060a35270307020607 76
    0x1400108030a42e1024003640c000c10b8587e100c0c0010743c1e450440031182c000030801080f0611072170103107014008086e05200760f5181e00c0d0103242d59595403400c0302011003044002c003040581c1c2c090b038211206850098024040301e090343c548103840344940c10060307003d03a800e0000a4801c80003040d02d03120003103442c1c8616041413541c00c00e0000400300c40800f10015018852802200025840c1c528001c01501c002e03103411078201407003642510780c15800140082c1c014818032000a4000c2040e01d1a22080c2c41c000e940350b5900704d200c000e0150f941e8170488202080c0b02c00403007032055900f480f02c07288041c0015598240d9842008a044071760a1041541020b030500078003000403a400c0c020740c0c10440524001c00c880e41c5808403070040f6800741a801c40c0643c5c2c0095408070340307485030041800800381194014140346085201604000725000c40c0541038a1104a1600703030b0b4548500302c07061001f03103000c00c031342e603d0104000c040420700588900d40041401c0d42c42c80080c000001191490303607000d0100ca00740501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 184306411 1250 184305161 184305227
    0x20309011d03010608070f0303030b0a0f0902030613050a09141506151224220207051c0c0b0f04080a030209030a050f0601151403010506030603100204090615 69
    0x2107440c0d407a5055407942c1001602034010804100900341e801070204c000b902c0c500d0003500b03c0f004410813034064504c0da4400c01804c01160071480448499680159480e9903000000c0c1010445402e0f00c41034a14107010b000d803012280c0c1c0000000b40c03003100c04018070030402184c65030311003c2401c01c5a004203d480003420904100c05000300002401f0103960401141803030b1078501c84001c0768600c3c00e0451640d03e003040c2d001c90415803200000700381e40d00215075002d019601c40346032082840751202900003400108001080041640d0401c040e28541c05c503d00405000f04000140341c2c064aa80601c140810443d2400010b80c0e80601e034881d5030f0301d140643c1c01c001070340650800d42d50590716024080c0c1d6000802e10500a4442104000c000384c0195818034202c0394aa1035031802110400c410946500018000705089078151202224000d80b2031369175400192418008000061860740081000241a16590031107002d40310f80c010034132044403d00ca01143c00d10390703100c2c0940b86641e03445400060b11031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 184307661 1250 184306411 184306457
    0x6050709080a171308060103030c030f030b09070e0316090207110603070e0d061d0a0b07021218040603170301030201020d2606010e04020f040f060306060207061d0904050c0f0102030901 81
    0x4e0760200341000c02d13035150202c50401409a01c00c2c0d0120f0309003003403c005c1603400400455032460741e040411a0b001c41c2404107517801001804101400380940305203000d6176080001031034800703518003138050407a101c54140000e5045030808440c041d8081c00240420b01d04a41502e208bd40c42d55a60b00c80340001800700108000300030001c6c2c030944d035140d202d00d210703840e8030364540000000e9800414803040245841d06031418002e000c0b41c210740103034805182183d00a021949606104050300140030103480c009002000182d00060000c8042c03100b006104041c10302030b604a80c000d0302628200321054109642070700da1100d0004a840c0f5001c41d4440e1200d100b8420303a007002041c9020352010300c6d200f02180899104182e00d15984402207070410100c5e0b10070f0045806800b0030704e4184134941c64414069079620f51401010140619072500700d01118420034403406036140181010914202810210f454075a2401d0b11801904040e400300c0c1c503075000200311501100c06954485034103400701481080a4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 184308911 1250 184307661 184307677
    0xe060415050c2803140d0e0115050a051521070207060908150103020607030e090a061a07020a03080a0c08040902091e061902010b030607020607020708150127060306050709080a17 78
    0x102e17052002009008042c8111414902c080000058404520740c901c1c84001c440d9010920401e025030040c0300da919180382082d8410441c807500b984442d0450501d000c4440c03546903e00c101600d4004000c1441c0c0e0003e400d00460340552541c10429490b00e14480d04c820114858000048003500104018101a0000e190080c02440c08420f00c4c18043d0024640c540159205064251a414107002e01c00300305082064078046007140514203100741e800b00743c1030f00316848080c10909000c646504898090300c00d0140031507104a480d90b6898803024603074002c1d08407481c010301451410300e2110345005c150740c40c2c040300c0b000207042d14200345140868140b1003016102a0341155250944150310ba101080303864000d04541e0058100344c5403041000346850b001c2e038020a6568840c0c80030241920f6181900b5040d03900c14503840950401c20881078038003203040001c100000386002d00c00000e001850b8070160081e582541c8040c00190f80314803203682c2e079500c15406003100054001c81d03981e456081000f0708100c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 184310161 1250 184308911 184308947
    0x307051602030f0a060510051e09070903080d150603020a020a06020306030c091911070f03030b060f03090f0708030906030f0703090f05060115030204030b04030e060415050c2803 78
    0x381c1540c0316505002035403004030b8016442d0000d1001800400107000e01400055420380d927040b541c242144032000c03a40816a01841c510000310f409203104501200185400c840300c1d43d9070306040700e0701d00c0060155886049183c00480c03804030340140f181c001c81d10703160342c250b00420384410b080d1580360003540302804881e810b101e101000c4145131107080406114042c0c01c0c2c1c0199a800c0c0d0041038001307582c4162055030035003c1c20485000000c1700c5489403c11560146800148a000c4402180c080c2c4901d4030b8140441c2c4002c01002614039000528a0796200c00030242c0318596521f0340010741d68040d03401032a41c03160040c40014442c01202d050203a11943c1d502c0d000c50f5035981610b9451081c41c6c0c05000b41e03000c1c0c2161005000d11240645a0024141c40c0d25003140381c14510348810241c43c0000d4001020060030f01d620018503603c64042c1d41c05004014140c10b101e40d2150405002c1c0e0340300604101c41d500400e40c8a0003a1040c82e0030750620340c003500070f80d58090810ba0b0360803120042508171348210 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 184311411 1250 184310161 184310173
    0xa09050906180a0e0106030f0c080a02090a020304030215130302010624030b06070c0f0311010c02100f360f060e090a200414040e03190210090f03080c030705160203 72
    0x488109011b0745008500403084000c1413005030034515a855400c3d00000b980398000391a01005031503601e0465444102e00030016140e403030f541380c120700b00040090244018010481405500341c0e80c4080f0b5640141319400800040b03503520480110f00703440050130070640c11001c5050410740c0c025005040c41c064018010780c5440c0007581e0b00000303020143c0024074980590f01c2c0030b2041019070100d4a80001d02420025008001540054103450000207407804200c080043c1011660080c20f005003000e420320202810070300e41101004201000619104604034000f100103850b105159440c01550140c1c0c0e140059030308a1018411403a101903c55603200d60380e0ba10004100e4910400e52a00e000540309c2c4030364442ca801c404509014100710854400d47c81c000340c41c60706c9038000085440703008194008d40e60842541e6400d83c2041c1183c4e500c0d408107801c0561803010001c80084240300144030b500d610f405611480d80c4088940400c03a03016010802c200001d0000040055500c6c00041c801012071394 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 184312661 1250 184311411 184311431
    0x70e0a0c090f09061a270613090c020d03020906090f031501030605060f040e1c110604050102070b071b110a150f0909090b130215030c0a09050906180a 66
    0xb03815903009486255480105101c061440c41c000c588000c1c040c000da40c18545010381c200160100304888042c000e00c1c80010201c603856500a032903c0707c03000c0d0a4004090f984850b290003038002c1010510040c000e00c0803030040c05001c2c7c401d071041041d015181c02e0030480900140007640d0450f04000d641845540c80d5000c00b44000001540a5445594081501d003005401d0002120a0005403403081d820604001a90903000604040000034014400102150254156800752a40036000d8050003080b0400c820300c01d0540061845c1403080400c1c83c450360b41d40781c0440342d02844400d40e506031140d9214000101d00100310018900d00c0061084410340d680d00450700e00349401048240100f0442c114000c403503a0011104401402c07000710501c4036041d19502c005124600a100e04000c610b10a074950035502c50003d1010300d40321400441d41e403070401070b0781c1081e1500070b01c43e407a0014000c090041504e0070030a400c58011840074040001000c030ad080050410600107001c140304580e80c1806003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 184313911 1250 184312661 184312679
    0x20d0206040e0c09031e0d0f0e030312090c0909070e04080f1b0607020303070512091204061701050a06080c030402041415191203050a0903120504090509070e0a0c09 72
    0x6008038550f100b00b50380c80d4610340605080c48500100c4080c800340411140a08a00c0442c4485524080745403100b556031f90000c0645400c1c28410701943c041c8804604540813031681000d070f901810981d003c4032103950044040200c102c1040700d05030011303000082c0810400301d8010b0400d07000b41c89080c40350b0810403000518403098001141845524900742810329031f8100038050f140d00700c08948060f52562078031090250641c8591481540100368080c00a024020180300074040c1d05402e0400700e43e01c503542d12008004041ca483d880358100110b000010307031440e0020030441144c941d922040d606039201e2144590b55000148240d0704030351030711110307204421040c0506110755010302d45018a8118403041c00449210384000a1841d10200d000788010440210605c90007545440c2495807030070694400c4560b6412680010011a800f1040240751034001b4041c006803050294200481d95840702616598080c034421540065550306c0842d00442c669080a810396545042844d5940c1e0f40700c0300c107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 184315161 1250 184313911 184313939
    0x206030a140a05040218061e0109090c030605010f030b01170a0b0904150b04021e0a0203070501050108100c08060a140f180f070c08040e040614070201060e060a030807020d020604 78
    0x510800d030f580c0d004100443c50011303440302c0001d114a600340950b04d4114003044066a4071051020340d01ca055290005d01d80c81081c034500a4500d0000c10702410806050142c0a0300d054000c603070203d0700368912011021711a10a90504000503903070182c034402d00220441c0703110006403442400030f45940204034a9220304007402d015921804840c110001c2a507a44003c689010000d81d11681c01080b4100c030300150119099250f4035440001903840d180c0140503803031071151000050841d4206000040e1000c00450401200c402c122402e0041c1c821410040310840000c94440e540952008424400c58481007030b480b80d086400380181098001e02c100207040c180345400460300501390041001840e041082e01a41c0014840c108081503030364507034500e02e0034010f900450703084030200c200007424030010703402c80d49061151030742070700f018205035800902030021805000c680a8016020030840d08200d4000e504480d0002d0304107083c14411f50030130124407010441070341d12a10520001c901c0020511007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 184316411 1250 184315161 184315171
    0x303050a0216141218040c18091a06071211011503050109020a080a0b04060e031b0f0f06070e04020c0102070503040605120a020403020907030c031508030a1e09030206030a14 76
    0xc0b41005250018082d40383c41c101303449070403040d4070604c190909000344082c3c02c034100da0110f9004c5941d145130300c0d045070844801c41e20007041c00e404440002d88142e06601840b40503c000a0f608849065141444680c0c4a200f034001e0041c440d007106c00300003c4c07183c0180e80c002d42c603800c00400c807268404250051a44213800a40360740c0d5580b1080001c514140d4418001059060041c20b641102034840940840000300040c04042e2500140084224240200c503500d0010759402e01041440d480c03c0780e034a54902c02000d00c0ca10841c10201400540020b04c144111050756031025820810f8080c040a5001b4054004181d074003403011388009442880038001070001c6984854071110f40c0c89440080c402c0c041c00300c4845510411052025840d44005030f80d000840341004181a2500c1c001103000740b00b03041c03400141c40d02008000c01d2070072022000784900d941a548107058082ca10741c0785250081111030400116a14850410040c2040700203907500148800b40010362010451510b5162201220 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 184317661 1250 184316411 184316423
    0x1603021b010503241909050a1a060a03180f02030d082202010c05030406020105101719080702030d110c030c060a080405070801020f0d0621200d06060504050606030c0301030303050a0216 81
    0x1d2240018500c1020344c08451201d051020742500d44400c0002649030307130340d203028100000303116a01030b00070340dc0380c5075583c0c85106040c003003101c505046049841081c0102d101f8003421503012082e620984000b80070f860100110120810500d41000780186410b030105d043c80ba100c0f02000101e44140b0140005196580002c101443c010b00d6603110740c507a0303811a10301d250000400e240039000003d040a61034490480340c05095a00b801c0540c2240202c8030025454854642a48000caa1004e41e40b91190a0b1404a58110406508240d1200c0980c5038458001e1400c1c8848161184508841c1d03402c40e004405a50220792074410140c2668003070b5108030a00c40000844101c40511840307064024100e45600c0c12100845102c0134130390300100600036000c2064a0b1151b9050f9150941070015024020403003101801d0300d29144010b400075200e0288900e1405000410900380b11040b0707442080100d82e543d00e10780c21a50250010040030f0040400c0650a2001c105240425000301c440c0d03a000e80307 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 184318911 1250 184317661 184317709
    0xf0f0501060f020a0b0c03071e020d0e041a0d020a050316150306180e010f06030c05120105070f1211040909121b140a081603021b01050324 61
    0x31406080000062482d104542c071500c0c50f84080345844203a5500070352200c036820356a444011085807105810340f100c2d105484204402c08000b50001082e000e0025152a458007808503c1c040004a03124101000e00055841941003158a07000000b1170080b4030080c243c0710101d07103582c0420f2410000004202040105030010b11081d824942034401d81c043c2480c051114909100010b6040001859803099540d02d41c1c202c2620780b0700a420120114403082003c2004503600d08040c42d200b0020311550b4000c41d00e42941060b09501800703214451401503c0d44081401c06400444403064641d89186485039555201e41ca42c04004000300024644200c0100d080d0b02141807580480c0c003000720010901c14900326a0024501b070074a240015034021500c0e02c81c2c89641c07408681044a11400180344100025000034009820b03000b03c0c8032640a5821035420180c0105940da06071411668140031502c24000181a04401820454840c032600e00c03d022610b40a404150b41d242a8150130421040c20 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 184320161 1250 184318911 184318919
    0x203041b120605161409030703061a01030605040213051509030703111e0a1a040f0303090f0603140a0b220204140108060918030f0a0302040504290609040f0f0501 71
    0xf4000c0c1038000354481e1400701c004e0f0100310007030241ca91800207040001d802280b1403100340e80174000c020065420010074401c40010000c0b9540a8400c1d82916001c0791601c0382c08501c1c0e04040c03082c0c13400c2c03440d85443c0c0001039040a04100c0f0781035884104a07080c6401300040c101c0f907201849503000031072056003414111540b000030803000b03d010f841c0f1a070115031007070010300c0d182d0380d1038105a08451240e22441a0700c1003924010b4018816a04060b42c90803c1e81d034000205a070020251040301e8820004840c4030782c45210071019580001420805101c1d08004601484580c0c0c2c40340e1110440104280b020309984c50600007100442c4041503034055001c1000c2003202d520200c264802c00c1d0910700002d140c0b0707007200094034490024101070030048000780e01c24003154080003191000c0802c2902c203900c075805108010040d610600841c1c0c0a6420212220100176075031288070102c01d4010340b0000020800014045290018149541c0c01901c9091802942c6020b04c542c00300c004014401003040d42c14 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 184321411 1250 184320161 184320173
    0x90e060403091d04020418020301150806252604061b0201060b0708030417132103051801030b0a0306090b060102060903070b060a0f060503070207080f0706030203041b12 74
    0x5a1000c015400410f20300100420449400e65021740c5c129400103144400700b82000d01c64161510080d019031800c0c8080040c100b41020352000c6410410850f166070796280c0f0785154002d001c100c802c50490203400d50400440c003903410480f442002d141500218117041740030024943c8181c1e81554050341d100b81c80300c1d4842040001000700d0307501c1e00007401050300c0d2040c400c80307501c95568050301c41032001c80030404000c49402941c1100324210002c030384079080050f4184410005107e42102c20600344107400c0354424503800088500c1e0591200e500301003140014800070700712001b01d90b042559410305041c007955942034000246004032000a1031a030f082c6451502c1c00005820701d03040d0b5100000300700300344000004035606940d014082c903000d5203414000c2a1400e2060b0003081c1e80710800100400d00c10780c8503010b144103500a600716140c440d079a84690783c99604a501d41c1c00650460329051000c1ca010350015a0441e1040d42d008032003001c1d000200315441100c2e081000a100d00f86020814002 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 184322661 1250 184321411 184321427
    0x608040606050613120206070203010903110f0d0905061c020417061e0115050c0a20010f0906140903031303050706030203060904120e1201060609090603120c0507090e060403 76
    0xa400d5480500c0c3c88142d5444c5182c103c80ba00c9058250148281103a04540317801056400459002e0003d04c50100940b40141031451080c00c681ca1901c903042c1040e215180004000c1052095501c651098500b0f1400f40031641d409682540464015021540300a50861004100030020129111030340b4403154101e900b0104003400780c080308840c2c04c4403e0402100c110b1054112100c0b88030700407885158140560b400d00030401201010301882072101d09122404826010403c8909170902400c10144010b5a590007641c0c1c1c58400038444c54001e0111502610783c04401030000c00269003401207400020307207942d1118494195800010740b0400030080108110005441981001d605600d00800810381040d40140050300030901d8480c0541518058081c8030800d51015000c0c050008008401e240a4201c07481a000092500c0200081d0010144140e00550f40d1055407000501c0c3c0c0d02c0801c5a00d20064074040e40d8a000b82040040c450000d48103103062100c02e0b60183c442e174941410003610038a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 184323911 1250 184322661 184322669
    0x60c03070311192003131a0313020105090a03021c052a040b010e1215131e051609060509060607111311040b090306130b040b1e010608040606 62
    0x14010f200c42c04283d40c0c81c4240c9214a00309241201005007042031407802e001e14035000d10701310300000038411844420626588192002c205000c51403c81900d410803c2c2c1c4402c035101c00c0040494141140190301c298010104001c1c01001c2d040316a4803a00040d01407914803420030304001040c0e04101c00c124081c001080400c135603000005d03005142c12114201000301d0007505110301c2d60b07402d1507111607001c2c580070861680c4c041d000300f01030010b10740b001c0c3d40c80d6460383c18180d0010324880098600e10405110f4200c01c0e42c080807006050303440c10b050183c0100e02000494141c0a0f41200d04100d1210036185001440c0501c0080344240c5000240100c11201a2029014100400c1054007160003e903c40b01d064405a440305a50320480d04107100420400c1c580190011001a0016003d042c00d0050b1899071022010759000340c46505442e0b000d40c0c21a10001d111340741960024001c81c0f00e010034240d21204104c1200d8182c1038054501070152030980001380819144c0051209100c3c0911a60002d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 184325161 1250 184323911 184323941
    0x3060f01030c1b150f09050705225c04180e010e030405030c0609090712021204060903080714040b070507050303041508130320010b03060c030703 64
    0x1035a45694001d00010f021481d0780300340180f000310001005142c1402500604800500b0045009984014805483c1e0360340203603a07a1140e1100072445e0b00c1c15580400c900480c40207101450300880150030301400c0d036920880d03021025030880c8058407040300c031041881c101c1104400101440005440c441d0003219128681403203400118040c400089000c580030780ba815000d107220901001381c0c90000d007030043c100303000d1542803216031034a40c00e0010243c015030f501107007a200b0071036400c0c09005460003841c0d10a940515200082480d482c081d04180c1a145800c1d1005864600c03a06d00800c0c9849081c3c2d021501d00b6900d5661009143d03029080c03541240c3d05281409401e0301640b6501118092170041c0e0501110014418042000401104000b01009400d59850301d68404103409400010501c01c1d000c42e1440c40004c01155107000d4504020360b040e15080d008802c1d680328440c440c022a441042c1940d0b8503d60700c50941e6081010a10a803000c07000a552441c008800070165001d080d403801d80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 184326411 1250 184325161 184325171
    0x30507140607020105030916090e0d0804110103020903120c0d031a010215061908010b03010c11030403060510051c0204150501080f07020106030b0c0702030c1818010b120303060f0103 80
    0x11581d1a84202c48400f0f80920303040c2d480e61101030f0468180502d890000910001085000400300e07101c4d00321148441140d410f0303032454084018191090241203070001c20700385584a18046a43c080ea002c1c140c120b0002c4d003243c141c056021802200395104032540350142c3e204c224400c080076454050200c10442041c100d880340240c1c0000030b552041e4821848600304503030000a1203a8466002c0102e42114a01200a05558a0050389d000740361601016003c1c0d42445100c2c0b600c0e50248400300240400034005605e0075255403103c03401802c3c05009440841600400000c80d43d0302c064030300030340710418800303201c480390184100030403035040a10051a0382d441d00410171060780c0180706994003140d501404c2080e41c0d18040202d006000c0f9400003130007541c5010a110305036031280081d00c88207200740c0403111143d00850801c880300d1907503600c080036107415000041002c107906448082c5000694004200c5a10050004212001d55034040c5045d074004001c110562801c3d50810400410a003000c001e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 184327661 1250 184326411 184326449
    0x51003020405060d050901020d090c0e06060403020a0e060121141b070303020304060e0d0f170c04170708060c2107020a0b100f060c031206081c0302040e0a06030507 72
    0x242d501a07103a440204a5541c80000d541b60801e4040b03d001d10600201040420741e549030a220076561809103141c90040d80f0002421410603408440c20703660001c0168604500d4420511441d0300300801050400040c000b2014119982c14121400208130400104203403070100138100000c207008254a17242c0151000b204206090042110021501803030090380d02c0e80c841c10148094611140454603512a0007012400158000c110b0703030000300b007580c0708400c0004011800345c0601007643c1c1c00304200b03c20881044540c0b40058100c2c1d28003840f80c2a60016550f8902d40c1f401c0100840700144a15800a041520050241c8a245407400e10b020000c070a0f0600c441e00a6850300c0c00c503002090080c003400429112541c0781c6002d001040115134042145841d010b000f0101503029800306d01044d110b042d03110b401181805003a003610801d01c0280881040c5020390301307178030111212400505500b0440824403e00040709140301c1c2c004001c0100b40c2915526040c3d00d40001c0d5031010b048445420700943c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 184328911 1250 184327661 184327669
    0x3040e09010f05040312150506070803011d060604090c0e03010c050310050105070c060309030c060905150f04020f0f12030c160b1c1112150a0602010c080609041e0309051003020405 79
    0x903403818002c0c06e0000c0d18918040d4010346080b40c0ba00304d141c2c480b60100b0451704200700c040080d410b03100800c1e48198003640c0e1800b424026142a07803401c3e886041404103001c1310301560b0028244c0829860000b82040035800440e086552075810000014400010886441060342070000107001c01c0c40c00c24a007100c9a2282410030f0068000d0000301920342c0351880074188200203c0840b9500008100b25814152402c42e41c4c5089400c0012141a48140043d4480320f150b000c8900c40c5801500521599841004020b15101d03001480c0340d000c038000743d03140b5890200300046c142d03210101c0000c050903544859003104203403840d484040508010884400b02c14042e601003000035140c00070201d40c840e0940707600080741c01403c00114082400c01c0400c011480e81d0000c401000c035042c1e0301810000d80354a0124280e4940d0410f600c04102d0103004101d190401c8021554428020b00700f2542811030350001045d41d4405900c140c0c0083c1c1c2882090005241000d814205550a410110300c0c0900c2c10b400301e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 184330161 1250 184328911 184328927
    0x1230103170c030a05040806010e06091303050d06090603050c12070603051e0702011e0204060507110406031208190b0f0d0620040f0503072103090803040e09010f050403 74
    0x41844500041c07801e5188201c8090b128103880c0d00003502e03118115514028031540042c070488105104501c000183d200c06500d91314060710000c0c001000704c0d59012504a14858401800c804100081006111070701003132081c2809072003180400b040407450750070014941200e0800107441103022115083c0302900014000084030a541804100c03541c42c84081015501c1119085418000800400c1440d55043d80040841c1c95104103540b440030600318180e04a02a80c000c810210310308111801c081555285a0402d00308000e002050207502ca544940980700c04d4440b041c0819007134800c2c00900c140d05803160100d0100d101040110300c115034002540348001405082c010b100c9600e00205105254001040b004000c5482003c0c1c000c1100448074284e000b4440e1000d9118281b6010489150100b8450112030040325028a40c1c03142d010403017911404520201c0c01e100004500140041c82031020340700034860720000304104d1800c01200d50a41c0c6040c10b22011062a000400001030f40090360 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 184331411 1250 184330161 184330163
    0xc030105010f020309030303042d03020d0513050a060512180c0f21060a0605030604080306120316050d0909090506010b0309070503060117010b011d060d09080a0e0301230103 76
    0x2500d02e00790320a034194803450702456010300000003003100340321980d154198640c1c002c0929061100381064030048802c1c1325040100160000381d480b0750101e1003a809005010003121800d5040780d9554005801000d9030307404600071500109031880f80481040400c0c2c0d203c10f05a2406400c4c0380401040ca4a4803c2001c855104896480008550782c41301c100b258640e8910a0100c445608c400d082a81c0e104801c65a5140740e034100340d0080740c03500f0b001c103209001e5580301010380c0c29030300c0c1c100400c00e640034204a00d103403078401400300c007440c5c003219008044042d002d4005840c2c1400394031002411590281c010a440070f0520f0804400104009030031070445000c500c5103a101e0300e0b46840c1a04000065212540c18451100040303500031281041d1907102d12140001c211110b621001551075081c03044202309403ca814a02d0101824200000e240a075401580054000180d94580e80b007900300e600b0140001c0c0004c50340c0c5005040912039028000540d8680d4015050001c503180149101400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 184332661 1250 184331411 184331417
    0xa03090509043507050c0307080109170f070503040306020702041a03031b100e060a05090c010801060f350702030301050f01030b19060c050601050405070c14120316020f060c03010501 80
    0x203461400070303116020700c561039010b0881c078641d44c0f0440d041242ea10b07441a01101d10038002c0700380c000389004c4148550852554044001910840c030f828001a268024031118070700c007007041141d000002e00074401000034502c640401030f19011a401440222502c51364404040ba008440748403a990300041620584090b010031111200b580d01341003418215440c402c1072031135040841c41020101c0105046100d1041d0f03210400c99075951100056403260f140d00164081500300d00144443c9100300741030b252204850030001848480e615a5140b03000b4041503600d9561182c0148803910b46201d806180c01000e90b00c001c0d41154104000910040b00c0701c400d50307041c950380706198034250701c03078540e03c1c201540305155001360a5940e40b0060714604d0041e0048a0301c2c002c6400125051429104107130051030b0a40d1412420442c99a034118000e40d2a4070300c4038a44150100e50504980c658010342c41801441100c003100ca00311803000e03107880c28100000f006900500c04002811010000384e0b81105d10034a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 184333911 1250 184332661 184332713
    0x60f0304060b09100305010e0d090b0d142e0303120902120105041a010e0405030403060e031c02091801031a07090e0c1b0a031202030c090a080a0309050904 68
    0x1207060001011994811904008007100b0401c0f143c00b4400107000f2280144020b008048112840070784400c0020504004900c15070401e100c901094401703440700c9030000700005880c2d0b24242d2015040041101c4840a5100000307620605a068400310130300300009544200781241160f50180800410003041e4600719500c00a83c0e041d5030b40d5801400042c0d0fa800020841b0b8140b9092102014047c0300c2e41000700143c0e20000149040c40113212446260820007440c1094116035988000d0010306246030310724402845030415500c04180c2c20703107501000d501c1c01640c4000038410311200c1c0340c0c0daa0410700544500d60042001c20020f038142170304c01d038819281c00050b0750707524800c3c3c81d440c0c2070740c010501c440600d03c10080c9426248000b08031140d0f00404206000c000820616983d111510008002640d4030010700d1180300d103600556040607140d07208900704500c1e50085090b030441c662100c0c2c7c80d5445051042706068100345007074003034641070f540c4490798030702621016071408a0301041c2800e14008 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 184335161 1250 184333911 184333913
    0x614060a17070306030813050103050108061e04141902011107050102100b031903030207022b030c030e0334060507080307030204051c02120d1b14010c200c060f0304 72
    0x10342e1100005d180d111140d030b40c83e001005603100000f4550701032a40401d107004004070300c0c0503000508500c550555001c0c0b200584a000e80d0401d1120081c2040300c075101160541c0d5204417080c000038200c50400c002c801c01c07010aa00004048010b52058104c1341c0e00107445c00d00c600c0e42e0108941040c00d11014000c01d145000e50302203072070440010240b41c00c01c0c08101c00e4030109a407540080003428000c86180341c06020307000c01c1405501d4080024138905e0265083c1c400042d0040100c290713118020305024030324550010109040005618030306a80600e0b0411400d80094660b8081c1140744086040d095028103203803000e051845403040c040c0241d400440000c0c00184a80c046802810300580035000074200c400c07010300c507845110812845030340e0b04403c00c105441c002441c03003c2405140da0700246000070f045d03014401d0140c000283e80c010320000c17181000f48000d0058105030b90483d61101d13403080070700d508403c820710072800c5842c00ea0448410307030001d50344031804e4075070906039003603226542d45503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 184336411 1250 184335161 184335167
    0x209010e15040b03070503011503060f12050a02120a030315030b06060c071212170c18040207060c0818120a0e1f0906020c09090a030806010c0501020403060614060a1707 74
    0x2d02e500ca8105404008100011141e100020354100e0b07510030061100a100c40a0503400e03151309000c2e2482e003820cc1751041110991000070841818041c000760b0b040d100c2d054020407220b881e54541000560302c8941c03920201076051146035200c40015040b20052030075a6a00100040045c1c6018070461011036014240d080c140002c0c001012070006c112807400c070920341401c244441e0348007007002c180a0000e60000b8a03175550840d128241c030400c0c0c41c2c9481d2100c00c0040c0051b01e100d0030b1a4225a0911070480051014400c40409103e6500d88442921300307101e030712512a105070744061081e0005408109080400f2055598101c41c80c100040c942d000d400203d4499950000d0582500201d00006041c181d044400da5086d240292300395000041c1c0e103020710180a200755406082036003c1013a0201091040e410031f40c00c510140341c117211803540c5484a9082e41c00075001940c0c0d10350384034810000701c40200340200203480c5c1130300c16908107002840050840e0419030b9501d40740020304800903c20300c2c8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 184337661 1250 184336411 184336417
    0x3110709152705042109240206010b0d09081b011d1c1e031b0c050a02060a02010b06040b0301051c0201020d200106030c050a1d1f090c1101050a0209010e15 68
    0x1201c201c029505142c201004100007182d202c1c101f010001894a404030b00080c4031004000062600180100d9192090344a00c0e030f07000c08801034071182d41d01d01100000d0343c80001003500e001c1a110900515500100f21421111043c4606a54041c0990042d07021503004c40c5031086801c45c4489003c0d141e4684005032059820b582500d90135294002620b44060307019484154070146100e20f11402203800103066030340207441c21003c3c1c06544100d5840005150860040102100c90300c008074818a403c008105941c100340c0041a104001200610030750034006650040049801c284000940c9541c0010391150f14516003281082103e409010b00b50481074041c80c400d03404400200503003a500d027856544c01d550f5005441c860a025800040c00645d090000c90136001d0142140c603480d2600c50024440101042c41e5070600074003000c0008041c00346114080341c0301c46d25142c02c0a05207600c0240390841d03400403c6480c041d48144106061664010b00c4074a042c0c0050f5041144207240f80f20351803080c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 184338911 1250 184337661 184337693
    0x90d0c02090406020d090b070f0f0e03120304050c090123060f0f160b0a0b090609010b0a080a0b04090308070305070908100b040b0d1406090304030b0609040311070915270504 76
    0xc074071802c8c8032640f42e020408425900c4140d9507401100700408085881c00c80e41001203925502400b201441c8480080081d0703000351080d800c0705c1c410b00c249004103c840134240e108602004119814039990091181c854803d5101103403540d03d419040c0d895154507010314041c40b100b00d0380101b86400752001c07910155400e15005011481c0514205800a005d400e4000c12180241e00c240c000c541603080420300c9070b0590351400707034450038007441c00c1e01210008001020241600d0702c070700d2403050946031442140e010501a40e500da0852624040c00707401e440c0064a0b1500704403071650300b00445100880e40800c009540304001c106580c0c031071300040150409810441d400080706408004203c8008207038512902c0710000d07200686d80ea082c04a07100c1c040c601c030180c0786810002c000395891400381c0e6000d500c80e2003820329803509011520b90303a190001a8004c41d003125640c01e5012464043c0b000c841c801000c030183e481d881001d040c0c40f80100104200c02d8004e20644440220b8100415000520300078 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 184340161 1250 184338911 184338923
    0x80a03050c10051f050102030c060c090d15150e060a06030c0e040608030304030e100f08040f080712120207031d010c02030d020106061701050f090c190503090d0c02090406020d09 78
    0x24103044600354030044c28410900d600c01000480021503500200a031500c66040101414451340d071500a418164000c680300d0740e0001040f848000012000304044c070341020319420000b40c240351080d400b03a94801c66041001042000c10420205a90b01e80c20704040d62030625010400401074201510b011620b9001c255005080190101310781c04000040e40c401c1c1c0c00395440c840490030680501881880007150103000a550f145c0c4040c40500a5144940007480b074420322002079260340390940f240c0c02004044940c0c8003511006c54440c0e901506400030f00544c031320704500d40506507030007511080e1524140360002440112214481c5e000380c0c11407482da9009001d0f2283c4940010b0002d000780814052100441e070f0702c0841140807500c0c90103440c1600e00107000207113485642403c2054003a0002d11603009042c00300f0400100b11042c0700101000131507916015100d080078024a802e003404021076800300810761202101682d0b5141c0b0298004c0c2e04010010790346c86002160314090300215a0107080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 184341411 1250 184340161 184340171
    0x50c0a050f1513060b0a03020d11030610080a0303050a0f060f080d05090d0320010e0c0307080a05060c1c0c050720060406140403020901060905100801080a03050c10 72
    0x1840300100d40c0c8400c1211440a03144000c0e801003002e40181c0c07003640c92125401c4a0722580d0000b0b19150b000341c1d10140b000b0101d81101c0e944e41d0000b842402803100c1120001492482a4880c0c14204940f13030b00103615a641000b03003070906248a541e180c000c84040c003055110000b00b480b580d410362050941ca080d6410500001d9155a00111003003d5481021460b00c555101440c040b4890010b554045100030504c49102d901d0740c400325140395980e1510004c00101703081011400000f441903070312130300e41d90300540300d608090801c160408001d40c0c070803c025004600034100240340445d00d0fa0b07110240c80d4002d6101d9014a04035100fa8945600001e002e91900340c0241d010354011002c0c01d20140319101040c800c401007400d0818005010840c00e030442800d000c1804034901662240101304400120203042c40d5030b9400182c0000000c0c1c2c401c0020810020050140342050b1403080414046410f00035415490049000d59507100000c000e030400c000410200d44801c018841e51040030140b100c1800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 184342661 1250 184341411 184341413
    0x15230304080c0706050f0f0a180f090f05090a060c2606100c0c0302060a030e2b0503010f0302011808010e0105010501021605090604090501091502030a2910050c0a 71
    0x10142e44030300310071101d9110b090f07070000321144a9411503c1c20405121954104074400c00c204440d50403440041051060600d4100004460a8080e0b002807141c250080340803490003003a00f00f1550800407600300d86040c1810030103075480004034816242c0c3c1c03040000907610200d8400316801c618078000c01000d545424208e03a903555803a01814000d41048070401c11540030144140d80e00c811049004001d1411244100090310b0100042c00d0484001d05011824500b01014103051503100300904102c0041e889444021080c20505030f8013188071410281c0c42d5505082004030090102e01c0000c2c1003050606501c02c0702e803102c1800100401110000313000a01308442c01d80e000e0503003402101e0051048060042c06015004010401c850700035044800d10780b542e405110262038000b4040d81c0541d2210611800a820002c0d100946c40c80d0600068072400c200f100d40d8181c990034002043c10841d50b0040340d4036284108400400c0d039204950741d080501007078400350b50798000c41141406900402e400d0388 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 184343911 1250 184342661 184342673
    0x90f0d060c1d010804110a150201020c10110403110d080307110f06010b09010c0602070b04051b030106060e090703090b2a0c06010501120609180b07080115230304 71
    0x10140c20159100c000c00b1481c039480c54407001c2403100d116800502001d01103400706014405900b0303512405400f0320240340e161901000c64904008074040140e60000c2c100321200d10074090220810a9098103100000010544901ca40958080988188a000c161440654498040544042d4007003011a160316002e400640b4221443e8800b000702e0081d1006640d10b48004104241a038003400c1c2ca59003490028070045a4a090464046850300c3d820494040401d0032250300a20640c071a4008180100100704820030080c86891002d01a81c10144244440f80c3c0200420b094080300b55000f5556554502c811400f50981d02c402625680e00002404502c5207401340030700c6914503583c03100700621002c003084905c174400c248500d03401750020b000600456100300300b41d0181549181010900541f200400012540c071800c0560798141900218420062600c44c0e940d401103141c00d21400542c074006210444424000f00e1760100000800019000d03c42001c00209244200300f401da00e03850302d86006 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 184345161 1250 184343911 184343921
    0x210803070203071b05040e151605041d0603120a0207031e0b040c090b0a05030c0114040e090601060306050d0209010e0a15081e0f10050a0b0603090c150f040b090f0d06 73
    0x85e8001c1e17044c20381c91072070070b800020a030b100c44031110048107250303440708205c1c100c2d01103903a130765010000104070004040c24aa0001c00e9960010401c5140904140f0300701450500c0c034100c1c034441c021040c04858102500440c410003100d030440602400c1e00074490522040e201d41c0c09004000249840038007042c000c1101d03090b801e5540a03c001c004a0050070200510300c12244511740d895404015104c80325442032410910b02c0032582d01090800c2d484a0072103c14850881d82884c0030792004004100040c0d25014880c010902540c804524100907000714011a1050207900e65081140020130030290096005205101030500c3c4890342e01d80b02d000701515280c1c07480702c41c1043c06856804526064011a201000c0c0c00010010018000c054816070050003000701182e0000d55190503240603500c503d0001d622490400b8007520340c0d8111041044a0704505038910a0013800c14000c0607030100d107000407502a6610b032640c460302c940d1800005032040320454085504003500b4801c82080009035004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 184346411 1250 184345161 184345169
    0x12130b0a1211070f1707080d140705031e090c06040b04030b0c0406080a0908160f031106070f0e04090503070f110609011e0314180106210803070203071b 67
    0x5100b8660198010300603401014406072585440146201c00a81da140344004216a0140e446041119a0720741b0900b070b800c441c0840c243e00fa1a500003041c0c440e8201407141e4024945d017030044c110f040004240c3c2245101c40f50416055001a000c43c0000c0020041e40c9a103450040215903260344400c0700c02d000e50041d2004540d011041c0c400b0440b1840d40c50255030548010343d0313030000aa41c600d0b041e800600501c120540d4444400c024450050a2408c42c500b8007600948660503151740d03500d0000c04007069030b51070540940216050044031030b404001000c480001d031500c05018886400054001c1002150060a610002583d442000b101d880700e996440c0c05250321a201c035212a042c4032003031180c0c0b8921030014900c8800400500c0a0810410602c81c0c0e6250010300c0a00740d400008002e14140e40d00804004400d04001c0042424003809014000340ba0b01e00d0306596807502407815204096100130014030000c0001100c140c42001910310854000c03003c506090b0548201103021070740303805 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 184347661 1250 184346411 184346447
    0x504051606030213120b040314040510030b0108071e0e040e070e071b0b01090203040602090a06030f1a3d172410020a0f0602030105010806030a0512130b0a 68
    0x84002116044a4080e01107546c02292004040d961543d007119030b4070703500e40e5000351100c061001091940b640f20480340c007c0b00070340700042c1d01c10b040c0c0009407034564020b02810400218a945040108540300c0d208401102400c00300074155071400040c010b00751030020186a0b2007080d400040740030790b074511640070354544e0b00c1c2e0800f0a0400900340b00c050b4415600900707051039400041207480e0245d4000c66220f030240c42c00605048110000501c0042d06900c5240081d48812512980700324520820601544015648481c2c1c8250804584404001c45003500c0d0b005401ea580700d203020858803c0c032980d2841d50305490004a03c00400350004d20300f000901c840d2002000000c5240713644200440000120020600080c150b110400c850200d1491068085028558030280000c03590011402c007030b4490040542c6075810440010720040f4003d206610075030111142c1c0000c00e2000c206802c0c078220003651a551503501c03400c004c4440000e94001181145c00082108d040c23a0302045241c94015689 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 184348911 1250 184347661 184347697
    0x12040b07020303071d010e04020c060105120a0b0a0c110d0807020715080a0b01050d060303051c11070308040521030a0507050c030a050d0f06120507060807050d05040516060302 77
    0x1804a070380f400700301c425102180520300c40d00303010000c0c1075052514000500d00f86000343c0c401f50224040c2d800c03880d001107440c4e000d070300140941d1901803200307003103900c41c07100601b00039050352129200d82c5800b800d100b146a40d0340000bc0801841148119008180c840843c0c20003504500010139014007200c101c401400b940001192080105082603074a61840c0d440310324548030368140000034042e00502c01d0600030b082024407519207040c01550001c41c06611126220500001c0030807840c62036609528102e440d0001c09102c1c4101c1105441501d0340501d0b18000c81e5903646130492404c0c101078282d18030b42e001c400d10340c500300e9000001140b1460640c441880344c0c1d02c4244080d40c550046080c47e000c590000c3c020001001d128034040d0005c1900c40001090404851a0700c000311111904244005031000600d403086c402e00300a200000c1c012031604405c00d141c0214001e1480c011074508010301520303500030605200b806c0200485462800140445607039441e180600213600010ba9008290412 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 184350161 1250 184348911 184348921
    0x3010510060807050a0e0105160611040320030303011802070f0b0423061612020307020f150c070b0606120f10060206040804090b0319030905010314060a0b091512040b 73
    0x908180c1e105c0280310740340d204881140c0780040d0782a0b048074129125401819800c5804107415000b0081c100c0344020040d9911402d40c1030500e0711000c0100400420b60482d01d060a5903103002045904407107a24541c0098050f458a6040281c0301c2d030040645140c04403180b4406002d140c0340400d000b10720650800070b041900f9010a1018400301c61642c0f0b0079004140011072810580100c80bc24046034030300707074143c1c085400b50702d4101d800640707c060069008040c80402824208040740310300000c1c0140d0308151a110b0100e80c1a841080300060480165502140c200d413504000d41d85c0c40c0b070001c600c0a0052030034480408101d1000c40d0740411031403510600140e03950003c1515070003142c02030304d504c0c6003604013001c2d1005040e60b00c00840d0103210320051281c902c03207204644107419109607126a0140d103000001010384031407601211007801c2010074420907607203801c111804c803590040340c0340e281c1c01c04100190001511500d0340c075454030005594506514200c04140c400c510801d0110b244c0e0701c403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 184351411 1250 184350161 184350167
    0x320010902030c0f0f0301050408030103290415060b031504050c040e06120c060a0305040521070f150905010609060909231009230c0d0602030a0204030203010510060807 74
    0xd14401079010340150f00300c0c1a041c01e00c00254440340c0c1025241d140d510741c4060129003190412078060b10702c240701000500400241d0300328000a81003004400c0d4080980c0e20311a00043d0010300300415012604a02c841c01040d43c5d0400c00040201200c00b58980c90f08200c0b0415038480d00c003040d0321407450100082c580d0000c0e203054070103591050080507540d41d40c0005000303900303a01e402d21307294600c02d10607408480c1c0e035032000074040c50000b0342c5e000c030301820617252082c50010f1350840c41141e0380707041c2e186c6071101c9038102c25a0350080d04404d20b0389030f0a2450910f10090902d801c010040d443c280311101d000d0050540000d82100c06815003044240da40b07440510848080610043c680918441c035440004d2030411a941c07020480d00540303800e9250781240e02d0444501c1881141e000d2245001c6440c4d2100d44d030001ea05400300d86000d0208154400d0018030b808000001c01000786502101090100c0c545034150307009540d000c2e008101d1800c15980c102013602d0248141c2c000224114001070340544 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 184352517 1106 184351411 184351421
    0x10803070b0906070e0607140102030702031b0a0309050d050c0d150b1234080102031b04050f06070204090c260102041a03130609032001 60
    0x4607840d0408401000509100050300b120080002d0319810440c01c45d454030003102c0c3c90303941355000d00d051058443c4460081c5031a603c044100044150000300500785200503840c018144074000d401c441ea02d050f504070040c0001c11403401088141801e5000c1ca07003482c4130b0f40a4681e40f082d18008900b030440c11400c152840d03640307240f0300c140c0d00c881803141003402007007039600d054445203450050765100201500d2614054561803241c07484040891400c043d84590b122084d5019940c0c40360a010b5042a0f440110021324440da00296803012811902110000b5040a0b040d02c01c040c104106500484400da070842c0d110b0040c0400074441c02e03007010141103000004000f0318540050015030407000c01c49a840751f0303c1044144410a41200300056040b0400c01c0141e0360341c3c95102203a40d10207040300080c85241081c02000c00c240d0080610000d64506200412072001c064a907142640c1c = true := by decide +kernel

theorem cover : BRFrame.Cov 184172661 184352517 := by
  have h0 := BRFrame.cov_init 184172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 184172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 184172661 ≤ n) (h2 : n < 184352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
