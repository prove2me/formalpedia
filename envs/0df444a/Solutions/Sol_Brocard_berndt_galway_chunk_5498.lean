-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5498
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:04:14.167158+00:00
-- url     : https://prove2.me/submissions/bec239c1-a0b1-41d9-96f2-7c19177f6b96

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 988669064 ≤ n < 988848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 988670314 1250 988669064 988669067
    0x1508060103122a1209030204111213030507110f040c0201050a0b011d040902040e0d0e0f3304080a0309090f0603031403060a12110301050a060f0b0d110f0c010b01 71
    0x404404564850f02000c40c40f400d4640040c1c210300c08000b60204206140c0210040c1d90b81e100f410b0310780f1003048500d0f40b02c4c07211404081c19100c025100d0011382c020140541c000aa002007216136061707000a212210300c503548045291044d001c999103520600700344545151a9055009a01c104905413052103000350003001904e5001c40e2100c00708440c11400c0044141d42069040040708900c090030014112444458260130440c1001000001600403080541a858001801c0c01781c00021107082d200d03c00480300d580089800f1101e44000094119100200215150705a41c001c1440b00c06584103810700d85402001d0040a000360500c19140841c1d403c41c00e0340c1c03403140d1000d03603602d0f40b6401481d00e04610949043d4000600701035024002803008201009034042d0614868485d91030200091b458404140c00e4a800030980d0090301c1c0b41107010064042080d2030351080f03990510322103a541124a10200280222840308221814000f49c0d101800c15450f00514000c0800e02c000c0040f810349900 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 988671564 1250 988670314 988670357
    0x3060501050c150921030a06060201050c0a0c030c0b16080903090f06130f090905100920010201021905040602070e0c040e0c0705010e1b040b060706150806010312 71
    0xb020540d84611000d81428107090403a6422900e20421611a0891988440f0301500070452000662601106100b20040b8500030034000e41b80e42c0c0004c0c8580d04e00703203580211a00468044d20f041129020580c3d0505000f002c0201d402d94014031422076034070380410f05166824a1141d0310000809a0000410b9840084155840381c01c005115407403440c031001c10401190008004141028200a4005404080d042c914001801c0d40b0101150f110500d04004e82401e00691720b25112a041c011b0070303000034031800d20754515204c5074008405c29010090040340240100070f25800304a8180d50000e03509074000000c0c200b12143c69081741c8500d0789911134425049016260302e8024981400709100c01404604582e50011b5042c030000d013800041d844040c295912070968022a400000c94502e82071000910000d00c13000a803010301280405401042151043c0e0801030b010303d03500d1100d50300341659000701c01d0041907244212042c0756103074105880e0982c4021142004110000d50407845084070b000b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 988672814 1250 988671564 988671577
    0x21503010602282a0f090b0d050a020103050a0e060a0b10090815040f02030610051f0801090b01050c06162615031207110306100b030a150509010303030c0306050105 72
    0x45442240021540e10a443c15840c00b00600310701d604503445000c4280103036211070040507001d01c003280c3c4030700e026050740444002e05007c0707008441c0000c100f0049900080d000140301d0742031031b0000300390350303080300e02c90003410380502000c11070007010306004a030f898a8100d510b544404880400350007000f80c1c010b48001400348154200c0d50445981d440700d0306003801406a100e40121b04c52201a05598002402c1581c110780d039403509422400c06101c1424016030110501e112805004100070010380098070b41d200521070070b8406911550741c20303242d9110340c0a4600b8121901d0840d851410a41050b03440c0d04184403400000031071611000385044c400b50400350f20701150084041c002d85510b0003405200a04208082d050301c81c5508400500082d100284459400761b04401f460f02c0100b0101410000e01a001d030040540d0440180b0184004504582c0c00400700000041c098002c5001840050044c4c1d12842d032210040000005054154110350420300850b40d041142e1500c03140191803600581 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 988674064 1250 988672814 988672873
    0x5160b0d0c0e1014070b091e010b010207090216050a0305120a05060f06130e09030c0c09060a050d060e01090311012904020f0904061512061d0c07021503010602 70
    0x10f420b04001e64044c130788000500c0c8907101c01030303d0a58035496441c0000e6050703403041081c2c2c0c015065841c0a0008641c1c94600d40c02d000000d10a10114000007551111580511001c050340018004039140b240c94100c21490b0f84441a1540c449076410050620b401c05070707940545950781e9000400032201e92081c54030032403000f0411452140c4400600400e9004403400441c0c03224540b202090888409001a1052008400031956412002012400c00c4007000b02680600441c4040c4a000ea480d60004010380e407055a80c4401d403055424000003620703020040c061994640404a410b05a014004100c4a07010600901840b4a90780d9580310080009070030180c900d000303000491942c03030700340c00408051214100f41c2d4100a1030400007012103104d9446540105400040c01c40300d0b13901300c4081c5640b01e20b21402080120314002d4a01500322641c0740b4030b0030002c2060001001000301d201aa100190045d00010071100828140d203a00e900a0107040c1c09803140b0520981001d88651600c00f444100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 988675314 1250 988674064 988674079
    0x60806090c160b040b191b050c0a080f032d061314090606120303090712031e0818030a050d0b0103060e130b070503130b0405160b0d0c0e 60
    0x2646400c0d1031070b4001c0c4003480941c801d1400d805010842c2070401c1e070f004600915100116050a020384a0f8001343c1083d400c40c0c650800307030030703028106c0c5c4132118224580e203608040740d440000302c82c49800d10042d12002890054045107403649180319001030740c4039030165418a613003203581e02c0100c0c418420710305846521400250000c0c11a08001c00062000c10403880041040c01c64585001c0360010100c40b0440c03107900031410000075140244104c3c0c40c0e40100400f0b1031660405200d010384401c414040e1080c1103c0010700e807410140b20b020710404a030702007901c1002170418610020090710040c0c0e0003c9803407442c0c3c0507402c0d504102100b200c898900688585181508020008020306a079040c001e05140d0354000c0050049818112241b080c2071045064071000010714040031500009800c440810806200b0040500075194451440640082000c08540e4852900303500c2d04881f80201210b2049440b4001354021030040640340581c40c2810601c40602000c600701c03007030605400415400101d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 988676564 1250 988675314 988675321
    0x703020712030b06090d0803040b071806140d0e060403110c13050915010303110f0c0a06110f030f04050a0e0c0f03040807051b01020114010302031b0103090212010903080106080609 79
    0x41c3d40f10381e0700e406020f001c540c10004214001070711102c0005042d680c0381030000c10030041015248441e94000c005091400c8481e0420142d826a455680607440a1006082e9050400510a81a0b500c401e404203c280100e0281480560b182c030403d940c00c0700403a4803101c5101a04002013035003540b82201422044490f00090440340107007001500403042401880210990015803880c0c00c1e000e54041e4446c0c008004030b0302d00b52883c14009061400c2039030480d1084c2c00c42c03a81c8448240c8104c074070a10b4000f07400c3c15601c041900340300307426490b00c0d00e0384000100f80081d91044400f030001c54004858030703140c080d950b11030311580c44800c44100703401d000100a00001e840032a006981c200f4051901c03603041250542d2200d00e07112189940c803131388000800c0d80799815a030900171880030308101da40c03102e107039455540400d1b9181c10058040480d459502040c600070b9109030300c0000081e400a0844098640140420b8000c3c080c2c55000c2d00044d040000100b511800b400310f8a006440103000a0310a0742c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 988677814 1250 988676564 988676567
    0x270111061902070c0e09030a18180e030c0f061014090a180c1806060507170a0201150b03010801050f0915070c060f0c0801150909090219030c060201050703020712 71
    0x52040400322107140c0c0340840407825101c8500142e00c504880b80087d0707950070822402800c240d01300c01e1b0082c134071280f9000034403e0700303030302d881c400103a960440e4082150b43c40454014290300034451420141e216a221440c2d01505c0041c8083c001e8045c1e0b0f03402c94000e0307180d148184002000c0070501e1303007010b1140040f41d411030260303101020b01b03e518000094844441d640f00004000070307070301c03504403604c83c1030301d048030711100c1d204510040c60182001341c80c04c41b407607864244101c481244100d01e181e001c1402c030f072103500031b400003641000d81c1c0a00700031041e11400b21030030740e0304207010320340c0d00e50b180c08006490544412250380c01070307116600800e201c5141c09142144910010104000c001c2c4061040c6d00245441c005c208018030b6180000c40c481c0c80741c5000412161050340300003801c80b5510003800581d9046080346096a05998010a100000b070001c60030b000c61044980a8072041d28a000080c03000c0f501403c0f09640d10741c1c1c02480940c5030844202d040e4040c3d0000079244030083c0c0428103615 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 988679064 1250 988677814 988677817
    0x2040e0114030f070b07021c0b2a0d02031e04080415052505060609010b0919081504120c03050406030e01060807060207080c0a0f12030302270111061902 67
    0x52100a0407102504401c45019013466180d900c008000407000c03a0f00340c02c501d05031150350004e040100e94001031104640b80c2d00792041000d0052881c0c9003001c4000d038000b40b0403c04800c035081005143d583e84160300c121300d40c025031040304c02041040c0c940113007485c500419188540030301d80148256051604000107a00503e803006404000e12604004040307401d15003014200482070442410b4082e0195814100c0c1007000080a140c8030780c0c01c400044c040c7c07028040c1540c01e01d07481034400c042c0d035a812171141a464809074110007090320401e088043d69507641e004151007607107c0c8440b10310244080301e0980724911640d40040101d00d06200a03c034140c800d41c41400c001e10884004103c0556030121581403107450703001600181c001060a016a07501002490b108001c00d50316508800e140480d99070200b18a800303810f1a5502c040c1e030f030406051190b0140d400c00140d244550829240303403c01610130404030007803c1d0100c0e0760050140d503450f6010603d54410021080d128000b09090b0091800a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 988680314 1250 988679064 988679099
    0x5091902150903160501020d0f09061d1e120a080a080a091208010f081209300715020c030c010807050c010603060b0f120703080a030902060706050f070302040e01 71
    0x128802408078042030360f01000192201c0800c00c0380c3c40b480c9418000020b04100f0202012020f1082c040f0b40c004489500105120071246589440701e00c00400c480361154400300320140036402040320100d14a40540d4402c0e400c2c2ca0a41101c0700c0d840da03040030403034030f23183c011311807006e0031004083c084200600d001e0208164480c60721f5070005140701c065035408203013010060602001910050060101c50092005c503805402c000005140500c0b1002d212925442030301041c038011620a414503c0c001c0c6503203d130351190b142030701c0c081105100d4440320b80c2d03448610b8821740716406209910300d0261380c0042010380b000e030000786c040d00102c000440152100e030030240000041100030080f48061718000e204440156120751808140c08200c2010030201c110a04540b0344121407800c00410010000201d4008603984004d00540382c0325a02c10a0300144800320700a500328000103001404c01101d42c1c00702e8031520b98980704100c0d5494440703086040b80584d0044c2440c2d1304001d001400507000c07607a505142d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 988681564 1250 988680314 988680349
    0x7080604020d0504030e010806031b10021e370f170a080a0b0f0612060102100f0507080c040b0d0e12040608010602061e0c03330405091902 61
    0x50000072000d02c0b02122000c603030981c00248038403101805581d03c40381d126000041100207101c0c500c000c1a0500104158039a420303c2050140702c2404028000d209450f10b8034402c840b4802588400200c868458150b021010500f000510004c443e20401042c21031030042002c009100318010b90751112034100040400f07995007a0300c005096a4101c2c1903004001010441c0e4460003182041501c8000340c500c0c1d2403000b403041502000d00420380d1551416244800c0f03a1100c0082c00f40c03107040042c3d0a00b0201c9070150091400c020809000ca409608154003445440d991061030703644614240186000f10b008a002d900c00c2002074030500c07256a00526540c060302070580f01c041402c15140050355005900c0034001c940d010004010a90701840f81d194450010304940c1c80e8090113032544e540000c0002c112014480010020032402d0811006440f07800d48400d50b844003542000e0807010100c05010880c5102da41820006000440c004c981420240c900500d11221085643e0070050060a4aa88180c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 988682814 1250 988681564 988681567
    0x50a06260a1217090303070813060e0a20040b130209130e300a030e0c090708101202091314030d020a0f0509100e01020a0506090706030b090106080708060402 69
    0x42155801c0203500b60406848000500c040311885102010004200c254070350801e1041000c11604032000c194051001810000e02001c039207041c4000300300c210a03140c1544980b0b01d2030020440e901035480480b400a1800d6040039000034108410303a41807940003074001d01c950350b0840d2919491b0b009445900c4004010140d000301500600d012601c0018900751150f02c00c21500014402c44080b40160f251800e00240d602c0100d03604510182c480c00348244c042580d500d070b10f11403903074060040c88a0000c000300032004900b440c0d14000c1400b036003030f580d03213069580c1d903600010507404040c071b0240c000e540030344414030b41d55940e820b1459101c2036020540300c1c4541807200900301e0724248000c00c41c1c0c843c48540141c540c42d081500410a1201041000511008001583d40c55544100c1e141c1101c106182954086001d400100d040400c0202c00034254481c400030300a00e030b00081508c20942e40195800c029400c1504c04200c2d0a130028854080400c4900c00800c804900c42c10440c0d62240c0003a0015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 988684064 1250 988682814 988682833
    0x111b15091512130b01030b0408090d0b01030b0c1c0e031b0106090b04090206180333060105070c09050c130303020309090a1a040e071703030406050a0626 67
    0x249840d0044118060301d200d0000340418076005480b03000d5003100c0710403540340302108982d90f090307861003040c00050500f0140c0030003c2c1c204035100e011a00f4002c8044c0070b000c9002c145103891030900c0d07001e00044070a824030b000010842039018098520b0190080b01c2102d1040a0307041010007003200380080320b41e90004104246480000074845081c42c0c05500000448902d0202441c040b1682d140c0030504c128101551030b07001d655404160342c400c40341000714010401521000030f20388107000c42440e102031307a4120f03201150f4001c6080e10032032010200c0702c851903130b58010046038248148070000b890354004440900182c0c480340d1007030ba8044582d5410500d440201ca405078081c92040d0700440041e0b000003a850b02c81e04107030a4080c0c000c490240248030500904040341c604c0c1c00301031340300c1d4084c503598440c2c02c5401904008010017000400c030100884600103000e02c0d02c9a00489040c1c0c0e810742480c0106440103140e12548046416521111000301440b0b5440240302c0b44a5504911501ca0502c54 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 988685314 1250 988684064 988684069
    0x6050303040e10120c090e01060e150102070b070f1704050409240b100e061c05010501110c09040b0712050f01170c180612030409090201111b1509 64
    0x1000a050285180c280903e4a40000018030810784c00410251411080b61800580c0c100d074000306a6428601c045a500e140001c1c130350060049511501c5140c0141003404440351111420b025901c0307003a401e80c0d45098803020035100901c903000b8000e0010103070201c407101003030070f01d04a040351148820925180c03558800001d829515152025658880329103800703101040342e2074028002646d2036070148403001c134142c0050541d5440c80740c030341d003030003824802034144e544c0c6d03101202e4105a5102ca4119021000b01110340201001d004150110380000780c0034400103000180c4880c01c00e002840102e05688035695101c001401421450038811070000030a14100c0900503e807181081521500c00c961400903040000403040b90700301c00b142c02500d204052a16441c0b214000450780703045440c0c060300c0d805c0110340c1c03a181345510541e050001180c08a52060139410801c9468001d980b1030b80742c011402c10064588984040042c1008070032140341d0012300f080c04400720b194540301c2d000f50404062401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 988686564 1250 988685314 988685317
    0x3309020703020102120f09150903070812010e0c0301030807080d0e0123060a060203120c07050609010605240904091e080d060603061a0c160308031e0601020307060b0406050303 77
    0x40780582d4000c41d4800c840135140f421785903c0314220300341c0502414408126603d41019031900d01c02040c55400003440043c0c1042183d060a900444066640005da24a90815102800713612402c0d03020601144100110303005480c16207401c5000c8a14008166440c5203082e4488a010350174141c923200c8980e02c4507400e00c2602200001c1c118106c41d0498040040c880c02d4500034942485598504401c1c0b00e169400000e0365000e503040340b0303400f00c04c0d2501140d00070075000f1400d0050141c4605010003007400d00642181040303c40642d8a0b2682d234040c00a0400340703a003441d4a14030101c40901554415183c960489445203006101e402c3c00f0040c0c034440c000000c080396000740c0305c1034030015050501c43c0ca98401c1c0c60091045180400c203050402c5004280502505d8804815410224081d03c0c604410320111104001850741e40140d240d41e40340000041d082160703800c070440300301d83d10200c0070b10b08203600e00d2049230141c0c00355140401d0f40ea40c1c0c40c010680d13205502c1c2c11560395100400c1301e460410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 988687814 1250 988686564 988686577
    0xf0a090f0e0402010e010f0e010e0f0405041b050a150c1103030c0109020906120c21100c0f090b1b07092309010b0102060424050c04150201330902 64
    0x84601c6098580360002601e160036810203503041180d002c071100e002d40d42c41004051a00d2092800d45441d07000400045c9041e412b94120301c0c0d02c1880c0505010800100054000554400e0009900c0d0311307540700100401000c00d4401c0c0c8000d5540f118560291502c0742c0e25054074a8419080d40800c1a15100802d01c4c5030040e804410729690360310300344025071900c03c500303960019046500351a82c2e51819a013544800144910300d01840c4940c4400703c4c43c1d4100444441ca40340280202c500007400c882c04c02000c1c0541c80c0c2c030600401e45120181c4281485840d06d003041d01e005800c031034940301038006519465203c05c2c011052a01800102040a0f4114041c0c907880404d00c88a06200310342c1d405403503100110140c00007549a240c070f9034501c0681d03000702c3c260754081e8100d46061120041d03410056482004181f401109600d01020400d503086418060002c1c0d07101a10700964010400e00700741e0890710800d80c818a05003035a00d070800c0e044103a0070b041144480390014041103641d241c5440381030360482c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 988689064 1250 988687814 988687829
    0x7032414040f020403020d03050702010c061526060115030e010e070317070f020103020f0702040509100e07080709091703040c080613020906040c021c051804110f0a090f 74
    0x4030060509103030034050220000e03044581149441d10b10303400181100328603a4002c040c04404130f0b000040d0f82c000d0f0329892083d40c1040051104a003035070740b488481e900310301441d4058403201c15080d0f8040030206440326589014401006140d013070015401189400380c0e8044105134580b603803102005800c1c02400c1030b0341d8074100149103860451030050b580b85d00c0800c040601600500c001400303e6040d46c0d00144c02c98082c05c3c01680c8494803200a09188181c02001c3c0d00301d800d040c21303c05c108900043d40d00340c01d44041d0b000c121030b40c0c0740c1131581d842d0a014801d40e10782d5070000000b441072602c244c2c89490964490b0110f001e115403260302c0c00c8030b10381040740c0c1510a508032802c1000301800030310543d980b20320060b854210b150243d85c005181c0c41c401400d1b00e13000310350702c201c402c0303009000b001581c2001d0340c501c0301310104140d1588020920350046424442028040f000b02d109403e0900484910071181c1200c61b00b480c0740315180c0c0310242c110ba03a9031001c00101c200f00107100c8003454060701c090440c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 988690314 1250 988689064 988689089
    0x20703021e0f0f06063c01050403020402030112060c111e01150b0a020706050901050301060507050703061a01030609060b071214190215010e01090908040305030a0e030f0312070324 79
    0x85001c0002e4010080000300151b0940b40640b001c9010b0007142e2080130340c0402075002041c000b500101c5540c0510340000790030610000c004649041e950448040e0644294400c1c8400c0d00605421123140040310180c2e2035642c000f480080003a9050b480ca1b00003000c82c000001806403095125500f003280075404029041400120403802d240c0c10f0103503038042c0406040091034540d0030704c0001c1c0741303100502c00c030400c0000104580080200c00c0c04480c0c010358005400f03002c414070920b104009100d0300130348540801c2c03a0800001b2818002e001e42d4003100d0785884c049042041946a45d181c401d0010758842c1001501701c02015901a42400381684142c4915032240c1d421143d00040d1525080790034a0010390303240340040025000030704009054920955012034039045602d050a00360180c1c0d04028000c0c0404160042200ea1114102d0070303150301141280e0000380e1407a0f00e5510380c0708400c441c8080d4800f02000030300b81030003a006070030b2120140901c84c020722448400c0b08440c41c4203802c0a44103011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 988691564 1250 988690314 988690321
    0x307031e0f14010618350102030106171b0304031e050301061d0901051c080f030f060d1110091701051602071d0408070c0b0c0709020703021e0f0f06 65
    0x7141082c98054070450400b051000444032640c0d50712080c038401e0580b002c104a6561803820210b8030381030000368440c1d0003c0700f44403400601c207010750801d0082d600014070302140000c4120010009500480c010104200f841c0d000400780c490345d0f03100403c150180b0016201100b48609442021640494240e444980b207506120300108414500107005c03560701007200304415140c0e1000b9a40741150f00844103004855200709130b04054400c45600500305120100d0940880144200203500c00c841402c1840303070340d83d114010400f00e0718207004054280079201f0005955801c0c42c15440c42405c80034240359688031342e10010005103141c5070100c40c490765140c1c0d05210344000c0d50b02807102c0650407800645800e83c00c111000055a00d440031000900c01c43c080841d06120b004070480781210b40040b00d0ba1052521411811034503806003000450503c2000f0000504490900c203407031106605501806070740101c100380003560b4110030b5078141389014007084001086003c01c00c1000820300013000d4a120314 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 988692814 1250 988691564 988691591
    0x308040302090c042115020c0a21050d181205120f06030d0804110603090a0b0a06030c05210f0d0816090e2203210b060307031e0f 57
    0xb000780a003e50720038203000c203108241d00d8804908400c072400310b6401842296060240b0503080e00150703ca8050310024803490340380e81c042001e03094107028540200314880d19000300340b140c0304040c00100020b80b0030300032415190666000300c466003404150204600d407103030302e0701d0074100520345080002c540000b031030061090304100c21644c41441e1701c400001a240840120740c40710a1104140304005001c80082c04124003080c28080004c3c000c0c1109403245485500e0383d0303456108800c240d8141885400094040d0b01c0c9000d5001a01d90145030704040c00e03e05000d200240d110043c1101010b40290902d80907030708100881c4200d420288014008008081409881000d01411094040d83c0d0007400518494201c2c030f680d0125410000b0403059650340300d0318132881035071020011580c2c250101d00ca10616a006420500408080505903200c440810b60704044078501c02c0900d41110042c00010811070003035019000841c075a0b15044001c056004680e0100d4181240c0800c944d50388825143c4180c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 988694064 1250 988692814 988692829
    0x5071a030a0e0a0302060601051b1b0316080d050d1e0605100e1011070b030c031801090201090b030907030f061a061611010e100807020f01022d0f040308040302 70
    0x1e5003040081c003001d40e204d8400070f4407104004e01c0a41032200008401c0f50b0035111b00d9406180c084034000b9925032000b244160b010719015891039070b2183c0714081e40204040c03210b450203411203102070b0003414140100d280aa40c1034004d404641c0507241e44e5000e0032103e0038223401c0f2540c91808c1580010b0f000c0c3c00c000403c01c01030070010002c401c00a00c2031400c4102c0c4c44506401c0b0501d0300c2400c3c100c041c0302200d0301e120318146c4c86400c80f210424000c010321541d00d000070084d43c002d0720300c400c90484600014206a00700e50220001a0014007d0b00040108908031002180c22150030700c107850300c071741d2262101e40c1c40250040049036603e548010180380e0b030a03950302206090008032250b901d00305500117000070480501d00c0240c0945400b04408a0076030181c5424045c094010f0300c0c1400564400320058450503048030048003500560101c000c1044040c400c803139013480810010705a08030100361003490319505020410302e94004209500d00c2c840300c04080e0006601c9400202d40e941d00310f2040c450316 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 988695314 1250 988694064 988694081
    0x20d0f0c171b070923040609060204050a0e04020a05010e0f01030903030b030f0a0b0708010e0429070e191208090609040204030b04110405040c211b050108091c0c05071a030a 76
    0x3000004140d050710000551b412035007129001c50081d059040201c0240f250381e001e0b587c400444040040c0200b000302c40544a0382c000c98000620955032801980c5039101d040104c1e80c000d0b440c0c842c00c6480e40c025417142c24984c2c0646000075170f00c01c0e0140820300d80034040115049590004039080c04200310080b840b070340407882d854100029458001c6038540e050000d080181040b0f00704100b00c040c030550b0090381c14802191032038042603007130856019145401c02503400303002e5505c044910b1505143c0b40414821100c5006c00c50703c003c01d2940b01c907030340c3d83c11580c00f46500c600308000c9000c4540d19800a803000d580100100c20340c60030640340006004403240800c0c1d0040d410941040080754282c000002140c0c4010400c0b000c26204050b0030240e14a40c2800606811200040c0070030b2841c0a0b000348c09480d42a01c81c0703220754a4480845640359200b0403d1845801c1c01d05540510f0342c03140641050891041c0d044807500380e110350076010504030407501184c40e0342d40031040104008013401901c24 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 988696564 1250 988695314 988695341
    0xe0c0a1101060b2d04060f18030f021002070605030601030f06030b09061909030518010201140c1c0207020a06030b0120030921061f17030901020d0f0c171b0709 70
    0x4462030492400514045c0f4032a074030500036140c07882c0f500c950003040c6141d1030681c1c3d5040300c1001900da01d003000100c03170003c2d010381c007a00070448a25440e9000140281c01c0c0c0d0745907202e141c1190340d607500460250618038400480c1d107446800000009140d98004c50050311303a10050402071505820020713590038003881400c0d60b07034103118221000ca500242255504000c54020310311502c01c0c2c8005030301402c08401020f414070700440070012a03113070041c09020f18070006079211401080c5884440164091032a003e07602042c1c01e00100102d0340207600401141c1c0060501d080c1c10503040224001800ca034101441035500005154640da182180740e04c0c1018212810107100d400307114035200c1e0356480090100340620122514100500040d03040d0000a02810080c882e03480c203407000807a2039802c400b84107400742c4140100001d1142c0642e801403440c60380c590f2103000340245626800d09451035051066903d039001c0150380c9007050502184450b0b020715000400781185400000402c80301490032900 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 988697814 1250 988696564 988696627
    0xe090325031e0e013b09060f0609100908031803060601081e0a0e0a03020f07050a030f15140106030e0f010e07061d30070e0c0a1101060b 60
    0xc52032500910b2443d03e040c0d0a1901c4501e0b15009404940d000244010504140d06504c41035000d80c20003101c1850040c40070b0302c19500540f101c10502c2006031104109030b07031024041c06002c2d2142082ca0000300003c1c1b1a00d00183d040380d556032800d0450b488a5141000c07500f00c1c801d564035a050800c82076401540030f00e0160480d1070300102a800380181e0103002103034406c4d40f4012030300d020115004246207180450550780c2e01016860040c0d42d81100a01d01541401407003000079251608440c5401280e4100e86101e1303244000c3d0f078404140f1240740d9002520150780b04a0306030390024110300c0314081d00054500080ca46a01d2800514021003c5509a620b1381001d01c4001c001c42e011a612046941d141002c007410001d0846030036015403203508894200c20417000c00002d0139000d1780411030700d0500c1200300da1000c0e20415540c1d00c0b240d03203010700450300b1500d0000ca5980c0a0810041c10000381c40d113404210050241145400c0d600181d03c001a114004294505003801141804002210b0b4800d0074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 988699064 1250 988697814 988697867
    0xc0d0807230f063606100305061605091c060204090b010329100215090c120307050a0209060d0c0e180703021c031806030501061103070506010e09032503 67
    0x159041c001c910409803221000110507461060801300c0b01240540c18142c2c0c41c1c1e071806034041032600e4028130055455200e500081105000807501d250484c1e0055030340c2914007401c58061020300d1003011105240c0c144400c04400c0411071a1001d48068001040045141c40b05500010140d0340000c54002401068020402000000441c50441c4042c15181000b040c0c1421100340e061400a0040c00030300760705d800c10400d40580102c1c1d81d40402e0303001c80e03034034110a50390081c4035a6405100703401401548100310400151410076105070f407048006025480c02d1006030f4a61510a41d43da0000201c92580b9041c00f42e00d04440d100343c00485d0041c03008000061841d000a01d400c0b01c2d4404558080c24458082402e0600c9084860010002000d6280d90705585041c000d0041c40244185400500890000240d01c6004000c0310f8555801600030b01035642071108c13610308544040e041c1c9a80740b008010801000e14003602d60240e0000c0c4502031410300a0f1810b015046960071045083e800b100300700350 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 988700314 1250 988699064 988699081
    0x70308130e0f01090b0a030b0a020304021011150c0c0a03080403020d1b08030406150f030c06030504050309011409030f10050a020f1209100e0606041505030c0d0807230f06 75
    0xb8241103d400450104055289a0200302c0080f12904050000e0075001c04002c40b8100640003580101e20903240818840a152802c48907454050666040340e0411380d40428500418991a500410f403900850b241902409081c2d1408540040032400714021801b00400d01d901444213800511641c10320721454082c1c9810b4100492105400a1484d20088081028490198400040f8404400d0a20314250f2525841c100804c0f4500c001c480c00c42204001241c80b52081c051300340501c0c0e102c0001e509001181340150b900035805800189100c0342400402146c0e5010031039010f42c2d840303280c013a00800d80350314032007000c0e600014000d031300c3c8034010891003224001460484401085c51020151192a8500020301342101e60001b222020b003000c0009800c4400400e07058012035080350704010740100011800c1080207075124540d415001740c03500752044c0c01d0543e058a02588541c0c0341c07519118566a40c00d141c000c224070780900c0f403903101c00c101000e150308003d001c2e9034400010081039075141c82842e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 988701564 1250 988700314 988700341
    0x150a0b0901050f0409090f060c021b0906150a0f14180108130804091406031c05070f05010509060915040c030f061808031e130b0711070308130e 63
    0x1500341001400503c04106800ba41c0c16503005e0b08045505000322005800c110500801084c42611910728141407110b07440d000290351030b03a44a401c0d2140a00c030342c0d25402c11111002c010507aa800000002d004080c103081000100f81400060b1540c0c0880e903844080181508011011280003070010000c61a0004000c034000001960900c1c00f160307980e4444000c51201c2e500c0100c001d00e001800306000c903640c521070301702d001200c400001410440c1d54880405590303e480782800e400188d0b111049840d882d1161000b090f4450090f0322100354461255206821998115100c50180e000311080c440240c4007070142e0041c440300e11511541e14100b40e00c3d855205ca08a1100800b03940b41030310418204003142d01f00e00119030301c1e03500000044009040c040300d030381e0040300c000703023000102c9000f05605c01060005900500003c5170641d100c94a82d91a241000806032450f424031a11030356038140880100010000340d40305080090320761801c1d05e4282030300b5440d90020148080c07883d041200300c100c00754 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 988702814 1250 988701564 988701577
    0x150e03060c030907090603080405090c1207110f0304090b15131e030206031e1b0f0d0209090106111c0c06110c0304060c021905061605190b150a0b 64
    0x1c1a65a50740c503502e0708145002070a52002e84580e00307040000050140c0903000d0011142c066500c4025030b13070b403800d802d041d520404070030a2031070800501003480c2504c21089124020643c00403103a045600d5150741d80b5640260384a00481912454059680d0400c065a10810042c04a001d8140035104145180d200307618000d44500e23040c2126040a201d80301000b1000a54014102e21350724200424014983c0300c1c24051220941d500d500821f101d07502d400003604011908000e5070b810714030f6180d011040d0380d0152a0b01d4a4082d02803080243c583d40e00120a8002c14554685220414007022820309100410f888100030344918160360a50302e820104000407154881e80001d41844100c240c07040300c0c0241c09044009100c04103001c10400e41281c10000228021520300020903566184800d0381c80c402e000381c5030014400c0c81010320661103030180a1441d8450010365001051f40001101c003100c0e00c036020b0f117401c0d1551080c0302c1111311040403020600010f482c2e0346540c0d801d00a11004038400c11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 988704064 1250 988702814 988702831
    0x300203031215090108010c082406070804030c0e0403110312060d060e030a0c060608031908040618200d11010c081209010914012a020109060f06150e0306 67
    0x5400040200c240080300702c80040004110081035615010070a009202840f0241c01040e00003001c00c03030601c04040b1440001101100c404090a002000d01c0760540026008541080701400040005107001d00da03071019081851000c0c0c40e40c64a0704000b014000d20404001680c0c2081000c03a588001c20101c040d0b0108041e11802c0d0104a140344c840c0c01854034234424040740c000880c00c0040140d10a0001c03200d81d0040400b80012030b12006140c0e120701c1003050320101c3c4441d83c4118030711280100001355015020300c3d000100c201080b241550503000a003802c4640314144d45580c0c0089031030500010084d2019034186a03904003035a42c1040400003c0781007030501041022610030002544225107400740c00c24865280d500b040640f0f40d000c2d101400302100d0310204140a01102003051089034180901c0462014000c0c50b0307070300e13140d4020451090070011035407103800140c0401d00c1c038003540c0c5600c00e203118001091480c1c2103003400840010702d0b01e24100200101e4070040c40da000034986403c8441c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 988705314 1250 988704064 988704097
    0x932010e19051302180f030a0c0306050703140403020a1b17030304030809030f0a050f250203060a0c1e0e18190501051e0102031330020303 61
    0x100006998640c0c410010941c42481d820380c150154600104000803600c09079400000103500e940a5000e80c00342c040e81e21900d81300584041500d10344140c11111b049009010350f5059a0251a80c284a01107034100fa503100d51203805000c1c0007541072194450304088001c0d000781508181c0c0d002512080b00f0032018240c40004810000d1a007203010380c04005040040701c16003c2641080d8032510398000321001d03004551280c0c001800200c0110450700620040c4803a10b142c40c810200550b07041d0884c44503248022414840282210109007440b5100d58160099030602400ca20403d03240040040507e9042410440d00c203401c50f42284c886548201c038800b41006125401100300c1d0946c606085940d803004000c040c1d004064502c9808901880192128841e00b140382014481512428411290030000c0c000083c00c0203048900c1030202110144152071422074248141c0b11010541e0300403072600321160440d1400798800c401104444007501c039424414904940000362030f401042e0714280444032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 988706564 1250 988705314 988705409
    0x7090618081f0b030d02010b1005090a0b0f071e050d0f0906140c03030f0f06031501050108100e010f08010e07050d080d14041a061801270612020109 65
    0x1040d0012950340303101504544c0082045d0740020702801c10050858011200808410310040c0f01c4c1c030858280c0c02010386205070076440d1940b601c40c25400300020541880d401c0c441e02c00098088030b00501e0b240000f86055110081c282000c50500074200400c03800d12540841c80c1c02a01d80148100b01212143d06045450403450712200503d031080078140c0340c1d87d000000400c0800d8421030901401030640010400071952808107169407100300b240d40545804554004000300c0d1320a6020315440790b5500107510429686400d84180300000381c02c0342d1002d1100d000b05025002092007120813001350080180b0030185800c02280840194540140a5503000241f20001ca8419000560400130011582c1803900e0a401c180c46481e50351008900001c0d100b201241c01da103440380441550f400766482e012a50391800407031000d051480c2e46407140f644690004c4107100c0c200c5116100c000c000b034034007051554016200040c80c01200c1c1c0c12004064401240004611030301007290603071045c61956200fa640c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 988707814 1250 988706564 988706623
    0x30606011e050c100c090e010e010b070b040f0b0405241003020d031e1e0c02134101060903120e06040e16111f0b180709061808 56
    0x364a8140c4c0e451420b000c00c400310180d000c032016003240c04840880189980f13807106018566020712494a0b10101800000e021900e100c2c2c515402c1032080101854902e020750300d010360b84c070301100c1c10f0b26160000243d0b03194091140b0030000424001e140010b145181c50f01040c0218010390002900500c1c000c4407100405004e00821400034138418001c982816001100402c0c0e80070103104c0c4549000c40c1303120f8a0070139010750000c80810b40e0080001340403441d48a205001007100b5441e08052480303600f903c40c5080408203c042529404101c2c100b0f40400b1041d00341d00007501079001104003c0c3e005002c001050b860101c1407040c107186c1c40d0114101c5100400241e00d4003071900b04010707400540c4240103070722410f82d0850f100342440742c480131216181c1e01011501c6065618140340491101c5654000d85030302588410b44140d0001e084180b00c264240560101c210304440308000f1030311198050002031b400040e8500d1110741c0e0703681307181154201202c4940f00d100b864103510300701258035420b4a010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 988709064 1250 988707814 988707823
    0x10e010914120601090b030111030103150b0a0b1606050609010b0a03090813090b030c010509061206061218012d0b0a0b0d0213050a08030a0f020c0d0b06030606011e050c 74
    0x201e12908035042545c507050014024030203018084d101c0e42c0b03005112109512905d096a0489402140303030400f0640c00b400c00700c044c01500b0051741c0d1100032924003041c0c0b4920440130308042200100641c20f0903a451404600b150005026103214401c04001040b8444184049555008a42c60045070411081c9800402c1d8010310303402000c0d00e07002101c080b4003d0116409000045000c400b00c03214481200010749031845100c00c41c9401c031800f003203520b08074200c41d44484d82140015014070f01e007030002c005403601200142c400038041005502c840d0326400c424080c0c1310b544540d0042c50f044c4080c0b1300c42d903010000c0e154180d00c03107281d403143d00060b001d0b500c40d03031f51a00800c4a490b442c0c0e03903143c500d030841000b03510400c0041030b4410096404110ba062081e2070300d00740c42003130009500d0404800c006984032a031052200b0210710078042c200f07200e40c9414207000411071240c082800c00f404c040741014100000240b00d01d04002492580100c00b654203404101e40d0701150500c1e0b65511401c04400e07081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 988710314 1250 988709064 988709089
    0x30228030203062e0e1503190c0e090f0c090405011404030906030e0105160c050a0807202e110a0b01060e12100507030219020615010e010914 62
    0x54040c1404002c04504841d000300c540c661400040028131216281d40b042c124880d01907401000c074200c00107140041d035600b40598a000046c125540ca54142c00262110303141d03e8000c40d14100e1b01d003800c02590301480c810640100048010380140807408100c3c1d0313525412003104ca881070f80018042818042c0c20741c00480b000c01142e21048980c41e141c10041e161a0507889008000b0b4500450190718810611a150055800012010100303209000c02c42e180c5140c00c000f07982d1401040300704000911290010407070f8601c510301003020208400e00c12801480c0300b00c2503d02801a801d4201d40311516091714001502d201c13980f2100d03d01103035a041b0f580686042c4115520b02c2030f00309030300a102540380301c00e048034016a00e054100711040b044c0065004103058071396a952240249c0701c56210190020b81d44030742c2520300142010183c8040504030007842e0384003c00345c1c11010a102209409281d00394080c603080c00c12400044220000034250704151140402d038448004d0f01c00d005940d9402d50030386 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 988711564 1250 988710314 988710319
    0x151b0703020115090905060a1a0a06090f0605031e1503030703030b090105030703020a03060b01301a242802060601020a080901050c0703060513020f04060302280302 72
    0x44a044500e0064000d1103860303000000c1070688a000604c42040c0d000303000e03a150344a0047c0c5a10f4460307000700c0000e004940210300c089161060003151644600a0046c0201043e07660540c02c80e18000b444504985280c10030710070030004000704030406c0d00c10f0880c0da110801c180300410150b503907040b5104041000c03105140d454000040e184d000c2c9a8903400c1055422011030b0150b001d07981e2507003010354a1145210080d00f042c40950f082010038500c3e4007010002506040200e11140182c040d050b600c1d0b221810844080342400700d01d914021144079462240d070054140000c02402c42000074214000015107042d0610403007006d42d4a0070094054400800b48000c419409a120700030f060308415801503000014030400d00082d0b525840004c0010900f41c205001070b242440c1c900046425902034a2501c200e807180704400000500c035481824460441c1200c0e951800c206841082164078042c03c1040c0301e01c0c20b201040c0050380c2c2d000c180b60708842d003002948046050a03464881030407c9980040e6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 988712814 1250 988711564 988711567
    0x12030606050301051e01270e06030a05121b030706020a1205070e04021309180210020102120112030e032a0103020c0c0108100e090607030b01050712050f1b010c090e0702151b 76
    0x4a05087c000c151106032030300c40d81004519620f980070700d9503600300e00760040c0c0781d80c0c0704070480ea0b00104540e004100f6010301e900d07800e0300142d1140101b4a59404183e0465245600281803c641c90b4000802034110451107000c1c0324500340400000c2010070742c846014421035001481c0081200110f0012000301210707039080c0140c1d4500d0380c8501001c46042001da00401490340030000951041c801c5071100c0005040c40703943d603400c10812200400c4030010031402d21139178012000b120303682000805280110031344000b000840c514281841c0c0d030b03510700459050500501c40302003403c00128016181d40c2c0203180042c00343e82e4640380300d8410303d041da00c0f0a18400e29001804802d03180820700d2407281c0c0c61600d06000301c06000004650340e100310391000e000d031071050110220062140c4014a00c044014107018100703c28010524110301c0c0e00015003250b69503801c1440c4a460b0130800d03503c01002e41240c102c010345400c4001075110924000083d13451031003000000c4840c1c0090f404100b04407040003001b0b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 988714064 1250 988712814 988712867
    0xa02090601210608070f05030304270608031b1b090415180b010801140c03060d0305131202030705060c1203060d0c092c0a020105090d060912030606050301051e01 71
    0x156129176035401a225481c025541c089944e04001080310121070002d04443c2c0c003a07103500300c000b80000302d442c3c0c0301a410b83c9400b030002d2220700400181c01c08030038281c1e002802d10401d015480c0b810414002901d80303080f4907481104941d80d1480f00c298465001020315141280c500511401000c107080760103114020560345205001c0a1076906040e6403a04000700003c45441c030f15240e410304100d1b0500382c20070040002604504102d00d19a2040b4420b040090901607103c0110b03c115042e908090040d0031071541b4031080d85001c00c8460010a403da41c00c61030000700306683d5031138044601000c40c9011000002c900302c0d44078414403202c019001107480c10b030035480754982d2000d09988440c400400c130f824104003002c51151200c1200d0070096030300805440c072403a4019640d540100300c0840d1b000202c50740c02030201d06075018164495110301c0035010a418191070203021620681c0140d81048014001444103461305050600743d040c800c2c091081d05a140340040780c6820030f6a880c41d483c04040c5806 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 988715314 1250 988714064 988714079
    0x3510708040b01050306040804290d09020a21030807020708030a112b0f0c06180201020d0206010e0606220f08011406030705190f06020c0f030a020906012106 69
    0x2140580e00c030b40c400c941203980c0d4404055442c0e405582c003030800a0200005c11802c410080070550b040e460300e903e1520351003c583c445078690461092411403a484508200c02c42c6410105000600340d503215202801020302c031030f03c10741200c2030f20003420f0010050205a129008001001c000c0c03814408499a9020200000f42066400300181c0c01c0c5203d24540aa00c0300c040200c0905809030007a0a0440580c500c40c1c11a005070140000400b071210781c420103070105405015250490082240d100c10380206480024073b40204900a0811508100010700c03508001c601181c0e0019070855060742c0350090744a4050800082d410302030f0141140c02c000040c0341808044140403118004003c01005081c4e4085400303c620480d25290306403c4000280315503c0c00840700b10a20160392913041c0b50f035886074844801c0468070b0b0007140259001e60a610a140f81c4824610440401a000342c044c155055010a2090b40003403d81814018081c907058590800a40c2d00305104108003020b1200c40c2c5e88000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 988716564 1250 988715314 988715327
    0x60c010504080901030c0c05100203180a080306010f0c0c2903090f0f0703080909091903050d062102041d07060e031002090109060c020a090614035107 66
    0xf441408207080c44448141d45000c2d00720750746c3e003076000009002a10b441c042c1050082d4001808140070001d2032022a4242c0320402c51085100c0c440d50400307035682801e20001d0001c44e0303220040002c00203108800380000d40c0307064184d021942900b00001180400709104031820f40d003c400f006900300007008110042000086454405040c2c0c81507402002842039a2500ca040700d0001034222102041800094144a041164000d9001c000c1c0e036125100b65040205a0a02c0501500020b2020800110780d81e03c600c00c1c90f0060500f4044c5607400f4240c01820040c110700b00700d004e80b09903640c444901035000c0041d51050f01040503000d40d070b51552602c1c8050440054040c5850082c4a1030f1a10401c04466100b2141340000584078001d802d460104200c65001502c041283c000c90800400a1080024040d00020b000e18080c55591001190145071801415810141d2003241407100c43c0d500c040040807503206001484081100443d40404040d031422650940340004080c071020000342c00d07031145 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 988717814 1250 988716564 988716577
    0x2060d020d090812180d1d0a0b19030f0b0d02060912070b0403171303120918020414010c0b180a0c030f0c1403030316110d02011a03031611060c01050408 67
    0x7244111804042c00300306e56412000c1200340c007051a42d60b0200c1c50200300d01101801e500c0050207151030585500d0362680c141c0155502c61282c415a40601c8042e80e014010250309840a04081000d541808009105d511083d80b0103809100001041c80d0280c030703000c40741d00401c0c01000895049a9603500001d0695205220a840b01e90341c88034460705100842c0100c0304503001c49072000a00350f0030342d02c80c1c0007036842c00141e080c1400080100010401d0648030003d2600020f150b0068555280407041522290118500360402104111000014514019550b086804581c00c0340f0b90608a04a16250407c14139002d040c940c1e046e60000704010401d040d03881030520607000503a540381e448003800650902038045075407580080c000904801100c441c00b03095a840362034940007441000c07a096003044205880000141d4503050041c0e4510340c0741905a4549009600441c13030440c1081082412804000c4018408e006900310041b065603407100f81c070803401d85000200102e00303041c5041c1040f50304c000d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 988719064 1250 988717814 988717831
    0xa050a1803050406021002040e070e0619081017100203070c0f200901030305030103020d020d06151a0a090b16020303030106030504120507050a0b07090b07030306081902060d020d090812 81
    0x340202030b000c1118008e44048401005208850740ca5004095902c00f290516482e0010000d0017a00302d10104030600070301c500c4494031078001d1818040707141201044c0d9504081601c1071141900c611388100040c07112803c2018000c01a22501c606004680d507040e901400703402c00c204140075105203d840001c0c6200d03011186142d901504c80003042c080e0000e024070028000ca40207100400c05400c24080b0207058510080c003c1404040e195038142c00c41d5620204401401e210342c1041c00503800b080f000c601d038121a11016030401c1d00c00b0f080200210054041c500c0182400710f0f681d1404050140003a0f03802c6da00400366074480d0703181c5000130000c00741200d040c1c03191005c100c0c3d5212060300810480e0845500301011e001c0c04161a02e030351a481501901c15807c0216004d80011a2568440030300003052182d42e0100740c1d06e1400b07108600d0a240480b01582041c0e0220328140141c0c1c440c02102c104826900b00035072100e1056407480024800da0700042c0180342e0000da20341c040d0f00d946103141c0c4105160f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 988720314 1250 988719064 988719073
    0xc0503150a2d0209043806040807050d020a150807020d0504060f0e220e06011e05010c081306090501170709050d0f05010e010b1e090a050a180305040602 67
    0x2003241c4032500c020510b008450301c840c003480303846010203030002d04840310060400b1480703401500a0071058003001604e41c40042144100000003d0503421054020700c2c112511410503041c0400c06403908014400c00d44501d201d102e0200454454084d2000140714407030b042c00529030f4556015010354030460701c2d04014000d035400c2c50100e60085044d582910116611a0101d007160542520021709844000b640584040d0040460344107000c003045003c60005800300e803076440181c080e490318006810510341c080407002001c541c00144031020701200c6007407070801280c000c2c6040c6441103120b088000b200c000c0384a10042000ca4204500208a55082c1d03500644c50510141e8141418001c4c0d403148001001c3e20420400ca280118032200e456004442d940021400c03903035042e08480303201c03c1200c0d182c1d4403800c0d42001d62614a4188410390203154000d9600c0100070005044103030024403200c05a680c49010a020408550090000400d040c110030400a024200a0710716000351080c400103118 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 988721564 1250 988720314 988720331
    0x60d02090f0a08100903110a030c0201022a09040305070611180d05210717091008060108060111161e0b031e040c050616110409170901030b0d060204061d011b0c0503150a 74
    0x5e040cec0b003400032107100301c408400031907000d010488003907409041981040000e10400010030180d2050a1800050410f2255a80206251000d011000307881940c42400d030000c4a00c08036201144a02c003160070762006299415a10290000c280101c2c04050980802e02001704220b5010b14024040030300101d0301080004480ca02c1140c0044040300e56a00007410080410690f50007030041c0b0000300042819660300c0c42c084582c8500900c001e603c0304161400d808580c070799803410364032810701420281e0203031840d51600c54200c3c000c0c101400c6501a0401040001a081c00640c1002102815001302180e40e0b070780c03a402c07074203404104182c02070f00e10207081204807007946054414441e5180d0700000061414011304504c108940013440c82e070741416101c6451450740d98034240001f01441c0710301801a111350030210b000705208100b0014441c01042e060000b442a81c011606030f00400c0c55000750b00c0d40203a00e2800c0c1004070b14a0340310640601c03501208851600900300124070488040c0401c1009a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 988722814 1250 988721564 988721593
    0x6030f05091504170a02061602070803040303110304180213060f091a22030b060409021804111f1b030c20060d02090f0a08100903110a030c020102 64
    0x490545500701258007000c1421600003600108507405030280e0308440200c041c5403040320b510740c8401ca074100182c11020402c0b2002c007103203c54070900b0f042e0384020040c1a090110307031350381ea1049000c098180300400001c1c205400c000c00807200a805854030340c1980d030f9640e1403550040d401206041c1001c20100d000424050700c00d00ca414001c3c1a940d44080720720745003050004011620f00160340f41400c0c07c200d2501150004100000130740c4141c070352440b61602d1401c00f621051005400680300e18104588080540c3e604001d4074a44d0141c80014445510366140800440300b1800c02107030003920480c0f4480d141c8000c6c0d0b65103540c40c070f001c0e05e50300c150358495050966884000380b0000d0115421400484c00300f100d043c0f04c2040c8800c146c0d1004401210000012296080030b013000003503d8001819110310f041a000300162540c2c192042c4012a04040c552520340e00c8100110070030560381c82e0410217140c41506182e0500014a007940c10203078843c1401403500b55166030982c05031103107a00708004107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 988724064 1250 988722814 988722821
    0x70c090f0b0a0b252103020f0304140114070e031e030d150f080102130602030711010e03120f0d0b0d0308062e110705041a0405060604030b010602010606030f 69
    0x44100034a18a2050700f8400080600d40180d03240800d040307140703860700003051036100c0704000d403a00500c100440103c0b0000403440a40b8044a44800c050062000f404c1403401c85064982099101c0382345c6544803e4544681c1c010818240c100c506201442e0a0050003a08a0600d00d10307040280c00340d40710642d590300f8840303104000f118002c0b100d500030404406098007651181900c801581c8640320015922030030201c081070365420000750359500141c01803190755440c0d0340c1c40041c540b1303002039404c003020340c1c40d80d029101c000b84506040c000041c1a40c50660360074045000070388030001c41d10380ca0703c0b007032103920005400c641640080c2500d03160010066180c9944000116039042e0b4a000b010f039100e805100c5403170315586085440004a502e50a074850006400051f588555591407038000312641c52145450045c2d8001d901851500e40c60705001207500c84111324070701054070702007426107941000c00c800344035a61000e02584003890001c41d0060303043d0090310844801e0f179810312030f40b0010100700d42103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 988725314 1250 988724064 988724081
    0x13022704060810090f0f152a03110d0207030e031204052409180708011502030a03020f091206040501061a07260c0106031703010b0f070c0506070c090f 66
    0x242c0c0000101c8001c3c4070306030060390f011841401105a010001e55918419001c410801c4540e00e4003429640d42d55a01481100c441804880189140c420700800000302c0f640000e2000d070815031192030840d81c00b0403282c1100d4542c2070012003155101d040d07007001021035000151040c801d00903c0c111411201400065505403140141210f100313201d004034401c1c20000200400c00d151741300340b003807100c81da0ba0b41c44c14240e0340705010b13100285803401400092400e14141c1010900c0b801c0f050b18890030b107500205442c0c0744501ca040060751855182ca1004c034a01841d20000d50051400011407654030010600d03d010301d2241c4004d020701910703611003a550039403280002d00a20000e00c4a44080381c0301c03100c0085036100740020021048840e24256026a00211150645a45401c0200200116080d0740c540c60000040246e043d1b50624081c01c8613441008400d00e501031012556005200004002100a00008012a5940d503440c0b41418a08810303105040b101813900601d111248070340d0181042 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 988726564 1250 988725314 988725329
    0xc080924130e091c021c080609160f05090d020d050d0210111c09140714010212040302240703021b041a060318010f14071b0f021302270406 61
    0xa032601074510780304441313440001e81188034203585c1c00c641e04100c000d242d0700144c5640e103070022450b19806204002d54040c040303584581580550144d4194054000040003d45150403651035084400040c1000340100003e544440f5441c81c41041107000501c0030304030002c913006d546000140c5495041280c20754039820782c003288100010310f80b0120312004010b400400b1440051020059202c41d8500568460008490760001e50240300c5001c03c0c1c610030055910034130050940390300501c5540c0c1c21f40110f00c0028000d000c0241c094502102803881d41900d4850300212540380c001c0c0342030080d0b40e4519001c019071025900700010f02c02c4c2c1028021203010b403d80c1d140ba04104c031030704012300c800d60340000c009020305424144a01d0800c0c1080c0604050b10b651030b480860301f045003144096140398043c00d200c040c4000c0543c1011028220b0740d90500d115003119240660950340d0010600c111040000482000d20014903980c1072192105009068004c8500706900059200d0501040745c2c076a0090701c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 988727814 1250 988726564 988726573
    0x11100e1b0108150118230f0609061b0c03030309010606080105150703231204110d15090302011503030c03020c01021f090212060906010e15010c080924130e09 69
    0x80300d540200c582170f0242c240c88840390030141c0e60b1039242c0e1051000c0101d41016282101c010071079032420041e909411202200d02c0351501d0304210003e50703140315900d000300d44c8089041900951a07418072041c0010071018094036038924000b403116000b0706490180304041580d440001c102d50504155081d560449111030b149401d01c04d0f102642d030302c0022060658803030300f4664403241440d02030001d402c0925850350501034606051800d001558003440c6514003643c4040e00300070100d101e9412001c04507918542c00a81000d941c14102e02400c0052420100300c1240e020000402d5841a4510041e6009074255010603541c44012a11081c1083c0541141d440e0051000c1c08000740c3d030301805e900d5100405000030f1507030042e030a17410038008480d49503c0741c12500040010301c1c01c03091015400810b01800002c00d1141900180211241c02c9002e07005c0c4801051050060300d5040c40085e04200f00040c81a1000c554404044168800b1a0307035020340396880340004402d40038112490150040c88081d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 988729064 1250 988727814 988727851
    0x105060d0201230a0c06110a050f1606050f01060201180b07031d0f150915071407020a0b0a1d100c05032203030306150f11100e1b0108 59
    0x11950b4220310041c01003002c00c4005010485070780c480003001300454644a6078503034500c40c28041d003140c1e0300043d0070f601c114040081d640c801c2e622004541100c011690059140d808241d88803004003042e0340d0040210b440d0605200810700c0038501181228416402802117410641c90344942036000c4200070b182d00c201d10301140e500f9000c0d0700f2254081000ea658850b010380541d140c80c3c83c12002c240c11240b00d4100d622031076444480b81e200a51b02c010440002c003040079010700e02e19a480c01c010903603010000c00310025003081d0610f2040f00d4a07142c004011501d22038a90340c1c08007260b0701042c01e285c042a01008162090211301c844204411002420300240e00000f0400341c4940d07440c3c0d41300f224103020421000a41036600c04241803880c0c0c003000c1d2a00014114a005411108203402061054075141c40f03001451740c0c044103e1074841040c0c504a01d61025021070180f5040c01ca00414071014188404023034103041c00280205881c460319041380041c0311180040d90200b4099812284201454085 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 988730314 1250 988729064 988729067
    0x7210306170a020a05310606110703150c090915230604050402030a090c062f06150112020d0207020f0a030c0905041509030e09070f2003070f0308010806090105060d0201 74
    0x4950706504080c2c580311088091461001c05110f58040368a460f80c2c1d07c0c00306011840d03005a41d00c60101c141c0006044183c11501da035071400d5640014481d00c4e46c0c0302d1510503610340c440c800e000d0003040d0308001880b100c20340b440308500101e030a0183c1c4401d0a10000e540c03c900920f03000b10046960081c1c8160f262504150500010390b0005003840b490b1303515003a005c1e00180c5010041d100030030070380d42c60103200c141c254040446c0803044083c1ba80840010814030000d078102203861500300e101c0b13a09254900400c040140e40b016200303e0b1112090b8800300d6906503241590b0001e10140340300302c807104070301c400d12001c1001c5074805010181892600700014060342c1c83c25031001c1e40180c040e100e90100e070f281c0a5941001e50300181000c50002e40e2a04928560781000044150044050f0a155200000c203800090140f4003c40c21080b502001d9214002001014001c82d0941d68002182e04524555414040c0c2891000e00c5515a1131042000240b003081041c8646400b03860001d241603c2032149400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 988731564 1250 988730314 988730329
    0xb01060f270e2a18010804022110150509060a1523040303121406091504140c0301060f0207031113021209010c090509040f0807210306170a020a05 64
    0xc095030b00c021a42c25a00c3c6903503503140c91024071a1a88920303542e45070307030b02d2203107554400348805414043c444040c440142d8400c00c00c4401342034250030380e1080d10001c54043d8546580107001c07102c1c00e4900fa500140d407804800c1c0580c01ea43c07041e03c0c0030400b904c2d04401c0c0403400c4c1d242e20800d0002110040c807494028414140402896041030342d0015000307841201c10400d921a80c0114041980b114055604090703034040d05400590740c04c1c1407515441c1034004960701c501c00604d64044544854881285959543e0002401921400443e081d5280040003090036600c00e002d140c010580004064140520000f10b5138103507903209001040c0f040d240018030406031260340303c0444c019020b200c5c44052850325a141da10400c0c025002282010880c01c01034150101c40c1c001d64002da803207804000103e4400d0101c0f58200ea8003003800c55490402d81808800056401107499414031541c4103484031580c5074002e01d0581d00d0302c4000d80713000f6103290010341d80c807624403000a411103c002c00030421440c1500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 988732814 1250 988731564 988731571
    0x1208030606040812040504060e0f15011202071211030c0c040c030b031c030e0307020108061002012012010b0901080a0902010504080109290c0319090b01060f270e 71
    0x280054103054807400f100342401c00014507450b40842c003003010459485c150280400a0803501c00ea07070010b0405101e064801d000080440301e00d0340f80320541e0b82441c0d1054404009120154408640310540c602e01194030750440304000c1d0000d4400c1205030030302803000c011540325024030030042c04500480024407015121060100e4185581c035416903400f600c0511089800240c0d1400c01d07038402000348406000c481d4002a8440280e1040c020381005036040b4a045da00100304595003080147d00c10341c100e0240c2443c9034581413103000114511040d40c44240079029507681c100f1002103684c1c90768512001070140d05c41040c0001e4480c40454081411030740480101801031410030310b466110300e89603003982d000c0e11044481c0b20180101c80c840004170380a0940b00c401c6605041418204003101c500c4500000d402031072015000b1018000c4d080c00c030350050034580d80c40055040f040d070303580c14064115000ca40950f070102e086116507000685101d1524491504601130a203070280c20040c0402d048003006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 988734064 1250 988732814 988732819
    0x3080910051c050a450602030108010c0306080304060c06050a02071406070e19030b07090e09030c1e07060513210b0a0603020102030d021e070507081903210f0f06051912080306 77
    0x40780170001c10214001107000e0049180046469848090001d0442d4202d612410040d002417009001c110703030200114008a8101c400840c95031a100c1c0c0c20f81c0244240c40700203009080030b20302141c0c110804684907106500070f4459428030300f500401d2020500c2203002490702c050300200c06000003244162540d4204045240c0105c0c0e05403240042c211007002900c5180d01a4004600e4180e1a4400c010f003844044820712601102403a090303400c1c0e07650f2064000d00c001d0100101d6458000704100d00000300030007004a4000f415008064521a005080042518540c018030009071440f40e05000f114112641a8008c61030b1444648a400080d003281744500c0259503c161b4000314902000054105140030f00041c00e038480c81c0060a61511803122260204503004c0407144010a40121440c0c0a40165980c08007455928440f01801080b1b1b62000300441d0303140c41040c0541403015444002510015601d1100780810b03004c000c0c0400c5201e1150040d0722140d0190140010a040d01a58005101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 988735314 1250 988734064 988734191
    0xc07120f030f083606090610050a0e18150a020315040e0a080f04240801060207060c08090402090612040b06151602030a0f0f1101080103080910051c050a 67
    0x50b2500c40c1824006d41c5d19540359485482030018144035201c26000a0608540c0413607002d20b0800419910000141200d0070003030391000d220301020302072041d04494800e00109074090b00d0300d01c0401000303400650b65094400c0c503025050fa06803e10380b0032024054404c0b0003c1940c0502640c4d141c00d40d92240110806c1ca41c0140800900000d000706485a00034441c1c8041d08401c5414100403c0b4101c168400c004652104104000341038001d40c0c20040d05821910084e0348260420104000c1c1c40341e210044d800010000c1e460912405041c1440d0041d031040c80388080ba521110100400010b11000712721900a0401c2080e002e01003082408610f148080c040d902844100c0d2180501c444500d0019501c41c890307190030310200800b500d41c0c8000528242403400e415410350301c4501a50050172100741c002c4030780c8121514858000c0701900c1300801c400307107400241500510120003a10b002d0700e0800c0382ca03080a100c0e900c032582c80d001d40c0c11000d070224614021102e00380d078130142041c0108018402c2c1d840 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 988736564 1250 988735314 988735411
    0xa02100e040f0603060b100819021209030c0f0f0c090a09021c030e030d080115090807120309080c060f031504021224060a050c07120f030f08 62
    0x355800341694148000b10000f40d540c0c518213140301a0703205034508900c6101c5003c1843c0c80250030042c4680c100982070a02400c541c29402484001d00c101c022040c08900c02404000054100000a03c00c2c98802003e4890512004002c26a100415409020b840d000b598841055003090384e822640034a0800005c0394410194020a1009040b01d5103031043c5140d0100003418141c04c141a140600d106030001c0c81003100048004105070418040c0078202c00e40d11440040c524840c8c050341d00601040000c0e039074034550342e64549090000400f4100c0106a0315100041c02e0340011410100c002400f0f080c1d1881c8c84503030081804160710080201c00e0110300c90f55003207a035843e03e2000e416140040b0607001410300b0407140305040d02c200c40c10400700b080b040a408c00e00684030141920300041043c00e1075600c0c1c0080c0c0241034101652504400290000001c00c0301c10701040500252001d8020384851203c3c0c0e2010f8000c0351907039800c94500d103102c05900c10082e10604c003081c1210060b000705259811196 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 988737814 1250 988736564 988736569
    0x3050f0f0f0c0a140607020607030507030b090c3402040e0a0f0f061103041109101e0e0f01060f0e06040306150e0705130e0702070b030a06061b03020a02100e 69
    0x4002c41d4145526500c1100c09404000f100d0103104014003e140081c0300c0c40c0b420040003961860010f00c03000400d5104d4000c04e411078000e801840121400802281c1c46141c600d4903008150044a0714011803441115840345403217440d07600410318800300749010700080a175020700c00500030320250b0794224480c0382d0035100415012070121344220300c10314000c1d45403000340c00c05a0541e400100042d42d44681001440005081e41d02030380e81303180055030030192994404990302c41460350340d44842c0c0042401900d40460715a996807a0064610300c0c120ba4545803520800750807030701000d0084101240d243c40c106d0600703d000307410b240740c1507100a00f0300d0300d429125900c240988070000035828003002c40000610482c00171100072a40709400346001c500b044040e4800702240c00851042200a40303691010130b0b2035500c00e00050000d01124140c481e600c0c00c0070742d009401481c0f61303c2450006101d0b04000d90640030000c0c6001d1009030154020110070156408000740c0c134481034200021300c0310503001842a40c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 988739064 1250 988737814 988737817
    0x2300c0607020c010e0a0305060f13210f0318020d022101020712020c06070b090c0409030e01030e01180206030606070609080c0106050a06050f1612171302030601030f080903012c060403050f0f0f 85
    0xc4c1833500d003805a030501001070050102d00b0140c0040c941000b980c000501d111507416619580c04540c00c0c415220705001043c18001080c14104804403000a1051804415001070003118420507e81ca044154150103e8136540000003065101108205084c0071848040c0a6904001c240c03040c1c0b0b03078920424000078102e54172035404802059021000c0d00301583c15200b90360036012003200038840030310f07020008800d0a240401c02889500c0100c0490401c0e21880c099441d555840001040130b04001d0601c000710341c200c02c111803560340c2030640100702c3d403c0c860942c004455050712242e0a00c1c4150018215a4100d900c025814a06110358800801c0131041a1030002d003203600c5054070381c003400c00090520302e4000c10400400d85e4041010700141c400140342030459400004076000f440340384c41c3c000d03035610400c4da04940c10760070080b81e14075010501c180b01500c0c0700300c0002a00361800070b0403c1501e46a04840160120340f05100000d0a980e52000130f02c0807103828400c0c0d42ca0140850000e8445 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 988740314 1250 988739064 988739093
    0x3140f0601060f110d08040506090c0306070302130905010e01030b010617061c021f03060b0405060a050c070902030c03070908011e1a04060803091002300c0607020c010e0a0305060f13 80
    0xe80c6c2c0300620003405401c1c40001d0b00301c19401c003c1e00056160b880803036a50316002d8001820517a001520100b0781c10944210000b400b0060001d0001d07581d900459200302500780030a40382c0c1880b110001405501030034504000c91b617891000042c6907240e004100020304000420402c040712807803101f0043c2e0700d00311409112000215404e01d07201d002e6400504a8105030000d61000100b0841800030341d9502d0700f6038030542080d26040741e448000200c840c3c2401c906074007100079240040180003c0665140103540b05018a54035180b4180d039442d403681c281d03601404000321182c4684d002c285000034541086951085a002c4440e20505500108049400035440244542c1010428560f14030f44203e40c100c10f0b481da0310080c6100d03031401040c8490001412401d6141da20043c4c24070b11054071880a03a02c001895009594440c9001007000c2d44960080c825a4009410b41414000c0c13803070241304074025660414014007250391001c0c14004104406040450740c00c0320f0340706600000310300941903190b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 988741564 1250 988740314 988740317
    0x403030c030b0f030304120501060b03010b0d05060105030717060303092709030a0906030c0c240b0a150c0503070212071404060605030627010602030403140f0601060f110d 75
    0x400c1122614010101e90301004038034840c0c0d814001480190350008144d4094891140c40e012080c001d40c60708500514071544080b6400101000008600502071f0140c0481b0314280c5040c891950740400440d81c40c8412900f0300041040690b41c0007500030945940c40d4003107c09800c8a03d440b180b20700041241084a4020302c500450800314080b0030300840c0320300c1d0808a5840118102200c61802800b581c0460103440100b580c0e03031440842e2030344502c4000b00d9498110000400641e0000001c00d042c3d040b5480131084c00d070078615190304a0500d04106801c4640c40c4401d611004000c4600311124244903105403110f01c030900c81320000d43c0e0340c90000507222500c4001824003e1034400c2e40c4035211540711509215500d010003c03c4030b1a002811030360b10040480d8404040115422140880d030641081694150064400810000d0b0000003c0c002d4030b0040d5988000301d8848800180d0f2a1989010071030345800c5140100a554041c3d0186000d0f99002d06200d040000d030456120300c0c00914098040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 988742814 1250 988741564 988741571
    0x80c090123191404092307050a120b0709141e13060312020c0a090c020f1005090f1609051801020a05070308061002061b1c050603120a080c031b03040303 67
    0x3d4a80c4068042d00310f080180d40070320000415031a10900c0321200c150308000d034565900c040002c0c81051090f03001a02000f403400d0b01c00c94a0302448405c0340440d8904942c0c1240810201e40400d020345071502c2100d10807078240710350030101000d208500e80c07850303441c50003041849900c141d42e0340c4c0c007030046180e5850460002061855400c114145400b01b2a0910039500541003941580e219441054242c1d01103410200e0b00068500c8200c2c0b805092044030100c900940e10200d22034815a0400c030702500c24035040340c48841d0f001e030400f40c81b150540651446401c0d9484108032140140d0003440e480a101c04460030720016202c0141e003607921007850000080c0d400203080c1d041541002c0081d40011054a041403040828a4040d54808018003c0201154000d00d5010329050038011555072504c55035070201556201081c200141030252915482400350a0321019400348800a5901000060f660300381076441d201100c25455201030304282405003910101c1c43e130f4000200040d03005512a41c0d000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 988744064 1250 988742814 988742819
    0x50c03090a03060905121c02090109081510150503040b09010207050703110a06030923010f061715070801120f06060305100605040b03120d0b030f0f0106080c09012319 73
    0x460900d10b42d48581b2080300010f106c540c2202210221604591a858100503aa0410000142e0749105507500c5140c4500c03400150070800d44c442d41e5020f000f4528860b40548803520b500140c400c24005010340800100305000090100e4018414150002c00031000145040125202c1c5800c124480d041035965100008010b1b0312420f000340454020182d42c542040940d0055550040c074514030000d29195104c240301780e145030442135103d004000360f15401017203000c0d0b665145400040400c412200180100b842418000c20507814441c4602066038641c88160700b0030850340605aa06c0f50306403441e4541c1802000010303078034820b25020318010401030810b0f240420b45007080c0c0d00e264102c0b5000b1070500750400035945000806006200040407510b458458080502c00182a07152190358180320310521800401700100304080041c1c1e500380280701241d210902075035210690107010340c1084031040100b242e945001c0c0022126043e01c0341c2140110325950020b0094400303106071380d01004501004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 988745314 1250 988744064 988744073
    0x2160f1202070806070c02090601020c0a17070e100303180b0d020306091005010206072d050a020f190f081c020310051512041a0a0f050f090d050c03090a030609 70
    0x2c10000d0038003030003c0c0031a02d4507220040100103401e000900411080000ca5190b03802442a990700540160014059030341e5020740d10a9041c442c100c908950080e29004200c1c07a074002002c921462050b0b4105142900d10341e0300300d42d010629082d617807030926150b81c041101e085076030080c0101c40e805070300035840e400d008c004c01c89031007009403000e215400400750420960360003182e5641d2050107400e104070762128458400b4020350801249160181150405200e0386400c070028208843c0c56900300c82440040400c1150307901d584105c0c00d1180c0e80390305a4800000c000111480503e0302c00c01c0c40c0e5081940c4010381d0303213802100d003a0170141d01d034001c00bc10440444240310740004004c101c480030002d181d280b41c40c0c3c0440c41504c01001c1c0669400c4c0024040c84080301800056038084424042c1611f40390b25840018007051242a42690520010400d04000085028016104000504030070107000f41d040c0c83c154407c0314404000d00040c407021100d41d4510980b1402140900400b280c24034140c5071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 988746564 1250 988745314 988745323
    0x803091b030a170a0309050106030b01290d1a04091101080c071e06110a0207030b0c03090309040b03010b0414010f0b040b03040813031707020f0906010507030302160f1202 75
    0x840394020b90000340004040760400280518a00500d840d07603548002241e4218003801141c04007904a601344000001040080b4118604031004920f0922070045ca000f8040e80f00d28180310781d100441e00a00c80c0f603c40c00c541d58403e100f1b00e20092244c059214841c2c0100c0e05481085d00c00b076564200d140081081d65800c8034000e1f80c4130342c25518942c0f400c1d4803079481485028039400c441500d464540c80d0002004100c0c0d20844a8901d40128030340c840840c40002940e42c03015010403180c600e60080442c042450031401e882c0a40804c03c0a5420184000d06000c010482c550b42c241d0301d59220815520305446902c5a040b5240c84480801381700d42c1041a525440000b0f9400070160801c208003c06c4241d4030f1206498110342d2150440381e8070548060305031031580140e0006015118020700000c5c07100704181c000c094413442a6a0f4403142440c0d40c04005000e501115020b01160040003902c0000e07110340d000302100c0711100150764255003161103101c100301400b041184c0c111510860603011980411 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 988747814 1250 988746564 988746613
    0x901211a1f030915020f0301060f0905090c13030c23310f0f0b21030913020f03090c0112110418140c09010e04051b070f080309 56
    0x15101981400095280c0881c1c940c001a0320042641d103003024030401c010300900780c2800c00341039015500d4001806548070242c1c028810203001c0f03086c051480511501940c0080102c520080c041c0b1039943d5208004c80941d031000f4408204449001000720000301d0313038840c0402070850075243d0318060019540036019092140801c0b4410050031420024641100c2e08a5040d03080d461640303032500c64244042405000365815130079000e8246138010b44034200036801103040000446030004d81c0b0170140705070348001d6030508120101e60010090303c42117003802c0c80702c2035683d0031340c01005150943c0200d8600d810740040d150401781c0d17004032129907a03940e803045108108990082c0204119403140650687c6446640710790800400e8071903120f86800482e40c40980b120420000d4480b1038a009501103460f60b11044505011030b04a07200c0c1045401c01c1e114a604c10880910b44c408005200900001c482d0015542124038494204079240055400005140107050a0005009950011000e40d01041000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 988749064 1250 988747814 988747819
    0x7051905090412110604060902210714060d050a0603030e091614311d06060d020c1905070e15040e070503250503010606050409020901211a 61
    0x40500380010394903240e07900c0d000341d0700604445102141c04004d032800203000d0104071301400780d4810402440060303007080560f0b900c05c6a204d5504c82607290702c0c560130701000c2c00101c1c0580c49448107021104030000d0070a00c008004108908007202a1520310644100712503a03152a61903480070010150008141202c02104030341d040c50324904a000c504c692255241140300b004406a03c00e034444c0d841100b2900c000ea48400701d025400b070141144903030008041d01d03d0345800c0545a0004d1001c035a01001181040065103140d043e460740e00070002d01d80c0008942001459080240712002d500411803840842440c1515001f4507845003042c9041081551181d0b0444c1c9001007000842090b105400c010f0200896000800b00c0803281e030246040504c5e080150903100e411007407200300c00c004484400e4055112041d190709600c45062600780c2e04184900d1001c01c209000c18040d49503940c001e042c15a00600d45007410a060300c82010710345288900c1081420380d5440340d501c03100c2d813171501c03801c011506 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 988750314 1250 988749064 988749109
    0x30109060b12060d0c05060a18140d080a05162003010204060207050105030406062103020c03060103080f160206310b0405010c050c09100602010c0c0201120f0603080a090509010f0302031c200705 85
    0x102011503428540c0540040c33206c503000500452607401242030b40c81101081e00312040c0c9030104e207001c2403119004100c03d50318808081811070382d440c05000f198196115640030b4205185070400549054101030821140c2d01e894078804500d030190200d15641e5003898128009881305141000380c1010b0300041c503d80a07401150060020031911011260512000a074041d500c00b0125400d0040f03200c41c40e0020750140c030001e110368888824502074801000021104100c400194074080340131000ca00c0364a01101051100b04020342c051002580081e0141c0203440648640c0c2000402c81107040784c80340107071601c581c01072091980c244110007010010703007801071405c021500068000c0004010000030315464458001050451350840d400a550200751644c444004140c017820522160082d180124444000001c1940e0450340390070440b500680900800b00d000500404d00c0d06000c01d1a0040c00112020074800080540d8001402e038540c1018026035801c00042281c001c080c00d140b01b110200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 988751564 1250 988750314 988750349
    0x30d200a050c010c0f0b270a0c050f180702070608071d120718062112050a031409070e370b0a080102030109060b12060d0c05060a18 58
    0x100003101a501082404d0810460302d07a817030f050038800005100201044450700600070404000e1104101044002e10fa000032146080d20342503035198203c00207001e24504010800890034030045104030840e000d44015203c4640442e01c80840e42d00b44c2e072000c016440030a00b041500d0344205490340020340d0f031502c1c0e4941c101249950125211068200344120310000640003140303010000b9030010300d138140c65084a650300d003074080024800c3c1e10034040c41e8060161500c611461030750142503410b82c80305446c80f62180d4217204440540001500d50241030b60741118001902c0c1c110000c610440000d402070401ca030600c05604000c61000c1c0c0307030700031146840d00d005011080c0008050030404410001c4d1007a80c003800b281c06c020b402540e0038070b90400c941a20215080c1c106400441c1a20504a000d005007551100820014072406c800e2042c42c102c03150104000340717040301040500900580403003c507140c8400c00a8025030004a030174011841d100d98020f0001c1e80d009000bc010b1010a010166200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 988752814 1250 988751564 988751573
    0x10302090604020702030615062a010f05010b0a0c05010617010912081003171911060705030103030c02060304060b04051306060b0703020d0f0c15020c150c1c0209030d200a 75
    0x9006003000b4100c0090700810407032901da0340e0030b41da200c0c004148011440d40196040c40d07101c030b8443e1015280bd5007032030700d410241902405118102d503031b0000782902d040300701c007012611450300b2030b001c50b10380d521404005200d1920a808031280c800e031400018405043d03141051661400320064001e028402c4100a00029000280c000710303034120410510b11a07401514008610800c1600c9080020340300b0313680880c50f84504e20b5544044001c0450311292501401503d00d070000340f00080000f980303090501c0c010305003c8042c581061052402056482407070001809807241110008000320054018800b80700c603d00a0301d004243c41080a45008259180203480300105401441030001c8129220301151080200300c101c540c012880d50806440610310b9006076200c0c5444945c0791044803641105505d5400d0b005010304a007900d9280340410750244c0c002910046070f090002c9960a114698090b14203010000c180181c55440c0400c010030144e6050303052051240500c09070707004812120005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 988754064 1250 988752814 988752823
    0x708090106051005070f02090c030f180a06020a0c0203070306020d0605040b18041406090d0f0509011d130204031a161b0f02041407090824061c03050301030209060402070203 76
    0xf18018541103035100d140d810a404c02c5081c250000390000d5425042084a022030000345006401020000354251140c4002d0640350b6586404040990481c41102c4000380d00c9a0003416042d40500f0490382030901500000d007016850b9000303542c010340000780001c03081341c14891000580400c9800b00701000c080d0020851103a15102c44c5032120b02944082001c0c000002884103500131140200e4166203000304181d6203a5451310085400f0400e40164042c4030f9008000381d035240ea1041c0c0d40c6150081d56031000002031244450702681004041c04103038810100341c0000c201a601404007880078400051605450480003001c06407011201d0f000001416800800d04a28a103015043d01000d401420000c6011500500080d800751400500051440b0076621991140619840d050601680e8040e115241e618510804074000d64102101110024215001d0740000c0c1c09031000350070010f48200e0300d81c40340303c129090300461804001041149040e1f03008652219080e01c0c06e5041102c3ca07404a41d56 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 988755314 1250 988754064 988754089
    0x1806050313080702030f0d0e0a240e031009120509130b041b030c02070501020d0203070b0910020a0c1101032003190f0e0c0d03090b1605030d05070809010605 69
    0x79011407070455802d110302d220a81d480c058008040c1d402003c0d08000d043e40e600a8040c400c000b0a94206034070700580380c22803c11003140c3c090602c04899104101407940110985441d180a1001500e0514210344003000024104100004005926032603410003190840d62080350004100c820004c441140c1c0f1102070310309074082080030116941c150200020044c1c0120400c806d610501e003000103103160342c141c0100205111036006d50703125070740301d41c012610740342030152000143e8010000c1400080840c040340c0d07481100d2101f5a006100c0802d0703180c090764400c24581c4c00041508512200344049001240e03803043d024201004000581c00202812540006000c1c1001e1000300008200a544400e0f155801c1c00455041150601d40c64000c0010014024036901e01d1013a6940c081981c10603141d42c9074103030340548400721103034504500c0c004c02ea880501c040b260101c10b031854500080080024142c90b0944202c01700d624502400000c10001c0c00511008482e818110100f005880f480070003440c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 988756564 1250 988755314 988755331
    0x181515020106120303050402490f060213080607020a0303090813180f0207050c040b060c1b0108070516030f0e09010b1b0f06010506070609060507030b0118060503 71
    0x222800241040e4010034180e40840300c403004820f00c0f40c003059415401580f00724801c940f0100d00c4181943c0c104c481d42ea04074415040300149112040110500e109074050540c80000c5001e05801d15944030341180f00002000c445261f00400c018040a012042050207001c1070340007407000d40740c40b8030000d5607500450400360a240d520607014052200800445125529075402c0c0516184d42d0020360805070150041940318501c0d00c0c080000c0980e040c000c07503c500e50440024081c2c4e04a120421006007071488805a0000c0100301030000b8010910004500310f0500b2260204500d04400140141c44020900010440104000c2c4010800390030b8500613540c140c0780c010b0346050350000545844c0050010958002d6286c000020154048030003040a00091010540c4604004030140c0c0d6840d0720070711100c0b10790403100c0140040d042c01c80c01b41006d180611f4000c504061103840322405c449040e1075404c002600d4000504807035030082c126040582c0c0e01880700b1310862030300c5002492808060010304 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 988757814 1250 988756564 988756589
    0x10302060a11030c0715050f09100318030206240d060b19080a1203050105090a0e030d020414090c18130b1f1803150b011808071815 58
    0x901c6a02c00c507610801d4100100459546407000d40c1034030340d501010311411450018000c40d0008241c4650113554080a0007004581441c00140407c0b0f01c21a04544480c200365031080b5801c1c00019944645100310f0003034000c3d00d150305000524410310707003204580c00700c0d010490f600c00707030140c40304010b11800540003000080c50300207100c0040c0320f00542110207401003100b5040443c3d01c00300480c0d40010284600310f400a105407010040e02038400074884c6c5580043e0703440c0014907080303050f040b10480f140701b64207403461f10014180c401c040b44c0090b0080c040400e0012441c2c0071034244203005d1900b00110103c0541091035203a030307031000c003c2580041c80c000c030300c503400700f9400b080641c00c0801d00c0740000700f120340303040b008260040c00d0780034000c00d26000613034005280d50756004540442e0300340d9401001d180355007680d101d02c5002401041d03846904000e030301200c00c4041414200d800c40030b040810007411515140c2075541c0d000d180351078001c12880740303004000780c803080c42c01034610101d600103403010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 988759064 1250 988757814 988757827
    0x10f050f06030a14100603050109050408160512040e010302091e18070306090308060102060c0a080103110609040c03060503011121060d0501180327060302030604020f040b070b1e01030206 82
    0xc0182180e0413411220441481c103000c040c0c1d4000750a002515116501007040782ea80340c501d4415200140c1c4c0250640e642000300b125440c00241d54041014000c01c1151041340400010840320390155108d150300005c82c0005000b1440c2c04ca40f096041800d80c220502d40088940580e60b9000010702000382c0a186604030880014041c06030700011a0092810040c070386060030007070240c2e04101d80240c0103014210001d00c00308009010782e200c0840341c0e51071903400e1303007141ea883c040840051507da6101100f48400c00259803140189a05980969004590386107840c0c140740c00d5031003403580340075510f10900071f02004d50303000d041d1039014105406500c2c04075203800021955808088101400711b500303104030010f1a1042d01e81804400344650303110001a103a0b406002241280380c039541d00c001e01d4910b02084200e120760044e5400450003000117281a0084140c1c1ca09036010740e200c642e20340380200d420800e00074a89802c40c0c0c4002c52078003c030541e141c102c00c0f0140854050000a00c00d00006c42c02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 988760314 1250 988759064 988759081
    0xf130f0603020310020c0706020d080f0a09050a050c090618060f01110a2006210703110d06030b06040b03030f070c0f0321050f0403030e040b060f03010e010f050f0603 73
    0x3110080d5000381c1600c64481d20040d074074010358072509100700d080c81103c00002d0300394800550b544000075144c1d10307103402da151143c0c1842c1c608000307006190200c2d103882c00d0303030041202485050000c40c4660010003032482e0310002e10a1800e0000c14143c418036490203130460100340304d00f01d50350000080300d01d4400d0b0404000141e903000b0000c1060103181c42000002c1040010301c03646420450481001e003000e4210403001c1103494401d1212103000c1400008200d106100c4007410380b90802d4850402182c0c540d501c120307010302c0b9040555929003841d2a45410002d008190f06080d81128041c0c5040c00041050340c0445d40c1d034400c00e0181014803900261040c180100d6401d40f00c0a42606408190140c0c1d980c10305140410350441081d080d100c01c50102c0e01007501a07030855031010f2003c07036620704051440d181582c00c0304041c25001d42068a40303034113961642d0390740001c2c5104440c0c400015265410400642040c280581027403c4500f002c0200340440d036100c20b4034044003c0105d41d110740d00e6892414 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 988761564 1250 988760314 988760321
    0x203100801060b04120c0b030c3a0c020715020d080a020901020601050d1e030806130b2808030313051606140c1c08182107170f0403020f0f130f 63
    0x100c03051f0101e01000788000c603101e0900034007000110180e0010000441c2c10791000048001d506000d0054810000c01e07008001500040c01034640760040d24129603803202a14842140c1030704100c01030700041251404950041c002c5031704680b8180c421403c1244007030020b0356828060041502c50300d6019203010801c01000071a2209007802a10b0400784c000381d1402a010400580740203120380e0008885800004140c460b402c0c410f00000c03d000d082041c5040301c104042078800b40440c20b41d40907807002c1000b101c100300460056207080010024a860340c24400d0410f07200b075065003480562140208042540032070f007011a030030603808103a922505464611714221648042240b0280503031105481a50801da01c240f04400041124908010820106032640e070040e084003400b220700e1401d90502c81140c0041d144a078414440001e906000250035451078000d04011104001c00142c18400c506106c14443c3c90003000b41e51040e0820107540000d09030798046c0d0381071580c250341e508042042c441241c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 988762814 1250 988761564 988761569
    0xd03051e0702032d010c02062d0a0e010b0d0506010f0e0c0301050118150804330b0f190302012c010e03030d0603060207060501080d02030f0a020106180203100801060b04120c 76
    0xf0025050010006501d4850481d405900b41401c07030480e0190805a42c0001c142403d8503100278155506d80c1c070b0007001429443c62a0700030359030f10401094070352a6161800d068500840c003c011a40c9402c18412502a06400c504601440f00e410301401100a10589040d9402420504408688043c1080d0040c03ca98894810b00c080380009607003668000400c20701490107410042c440140000003180380d41011110318041415820000c2e4907411558441c0c0501c0c04000c052501c174003508d800081d4130210484a50b02e405400b02403c0003190781051000402100c4a28000d00c0002c0020304003c41c0c103a004403503818003590f04d01401c501d0340c003401141c9144111400c01c01695459003045402034104d00c008803540c40ca8100042005140041c22840e10301d00c07503000f14038101a0340340c641510f401c0310144c42e00307541d00c035034010400300c01101c034081c4030707038140b120050b02d9240c03403070641e100414181c0c04114244d1400c0d07801d0003442220001c0b00c0503201d0f02a4003510038025440c00f02ca6120711507 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 988764064 1250 988762814 988762903
    0xc2d07060f020d060504110405010522060521010e1609031203060602100509030913060504052503051006111f140108030f0d0903030b0d03051e070203 66
    0x110340281c610158050194452030400800081d9101c1c424401107540e0154180345c05d0800b4401086650701c9900104008041e58400c042c945040d081900580d905c20b800584c0822000326400f00e000000c03d007420302e2041800c03116012545408000081030340040d02d50580b41404000542d4414000d900c58002164012423071074a00c50115001002440b05003d40c0c801406145028a1481c00a008441c05941030701c0c013035850906502e0804c41d112540860425010b505da80740002c2d960360303501c04c0a119a000c12035450b021221394800b17805000d10f011040342414a4001840f224141c0448010107540040c1000d0b2112048030161910b010582401902001291a59038003044850f0b00031401d4003001b5000303403c060743c03180700f4a52240607101c02d07501c4444042c0700021052200e0f070000c01043d4068200000c4034400c10011500c40124104150041000024000303031007882d60703002c00340300942410094106141c69001a032180c84505894401d2a9100703e0a002101500382e002c0200101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 988765314 1250 988764064 988764071
    0x10b0c010b5406042310050d050319020a0f0506012d09020310030501061403060106020303070206150d06022205030d02060402270f100905070e150d0207050a0501050c2d0706 76
    0x40c070041722032041256104400c3c259000b000030300f4200040c0310380811342d00c00040c500384485001c0c2107005001054007030341184a111526004905d003245804030060103a409440d040d8180150507030180c0f0441c00403100c810207030384801e4040c011a8208803d0b268081c20140c1e40e9101c140c024004a0345c0c542000e4815442d082e80000c00d50240303126500004015016214143c1c0d0780e82d0709076101c0c00111600c20158200c480007035049814851161028400104401040c00403500c0b818100d8005ca20404812034804250b20307884900b03442d00768020071046000780310080c0d49200c000d4803044003134002400342034003083d892040b4038042218401e80c404120115a0b5113020004071142e0401950445124103010001052079150b5000d403e201315a40d8032086004020181030156104580003032903104d0170140304e071001070722141c0000d211540c003030001005004e0460070300e80d08650014210401e446030400c030411081c400d68490b0300c10882110200148800c200400700c00740d00c0742400041031140f5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 988766564 1250 988765314 988765361
    0x20d060902071106160b070203040e13021504050109090f020d0507020d110105010e0606071518060501050307060e0d0c080604030f170906010b0c010b540604 69
    0x4079805002d10500420a0300c640202e4001403203007510039541c01d4840408010451800308103850129a0044981d10449241560741c01525446070410340380903804045000317500007076151008004180d004842405854945402c0019104070118481c4400460b20b900c401c02d121011b5078151080581c03152030a22007403421040c02521400040203d0011841044110200c1c10301441903034141d426000c0c42130030507190320307042103001d030000c0303404880c01196120075000d04c1d5100d000c2c1e41450308400e4264040180c0c02e20b000016a201600850301950140508100311903201e950489001c00c1951007240d0860030342003040c5c3d142c12540191015208500500041542c402c036010702c40300c007507036488450503000c554050314070780c0954000e03020340e001d0801844021155001046441c06103000019a8584413010070010020030141e0150b10f803104064100c90f5100e0442a50005502c0000c0204410002c803884040c942c81840000e55405d1a00028a2902c450b8406039829a128204c2c1c80c0c1000f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 988767814 1250 988766564 988766579
    0x50309030d05130e01050907081305011a130510210624060503130b0703181209081609020a05070816060c03150e0603070e090d0306050d1a0a020d06 65
    0xb402800043c00070f4009a0340091400030700280b00341600c00c010034001c25500c4061f0122001500607008503081c040c02100b40d0b0020f0310074840e05c02c1807888408440d8040c04058204540b0070403d0600700c200300d08080401412002c2803102405075061803030342928000d104e4034948040f1685240061400d858038210100000d2440c0c1640b22141840720300700d4600381c0780c4c44200c8807404269204100c1d001c0c8041c03100700041701015040d912080314680050804241c3c0d118030a04821400b050f81c0c20407041036085800366001305000301134503450004103134142c542c3e1012480254644180b00314140d0100780a51074510aa0031a014180c001010649070002903480c00e00701c004490b021541946400548005c0c10b00030300442002c101075060381d072480d80c9062800c2c08000c000400301130303050240100216030741c465a51a5801500c0a070002c115980c01d40c0400b900b01d640300d402540c442c0c42c68400f000c00045541c00c01c000001c150300300c10302494071003044040c040e0240e0000c1c446080c0c1070074004548034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 988769064 1250 988767814 988767817
    0xf2c070f0b0315060403050d200d0806100216030822061205150a03080d06080604030230180103060b0c030a081b030103021c020a03060e37050309030d05 67
    0xa03c035903a0903d0011100104010f5288181c1c4030080c0550802405103004502a140102a100240c0c104420b0000d09090450900c40d441607004040b50740f0809110722404e0500d03180150001c1c500041005030004207010307070484064400104040790002d410640303000944034240d90b2448080100c50705603254a00603001e030602900440129103840d0019003580410407540c691a1030203040c00881c1c03400c0da2103031802039101100c03100c2c0c134a0310b80c800010902000c0103181d100b2130182d4050184d04060006510081c6003803003801c5241840c0f001412814299002151ba03200e0803c03080f10500c10300103005a0141801d50b10010305082c0104d0f242d0b454502c00301c000c01466019a0782c0d110305903a5408405080d030318a140a8101000074001800142400540034121072001c900c111031100315030b40010441c191540046417400e450784000400c0c3c0c40100844419a00c0942420512007d6080c3c880c0d90388524a5040380000c4110b0b0520081c0401441202c040b860068241c450702100c0a0b40a89103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 988770314 1250 988769064 988769071
    0xb0a060e0306160e1201110409230705310902030a0c0228030c0602040305100f05240f0303180306060a0e04030804082b0f2c070f0b03 59
    0x1d009080010308030410f1190744010142e810f440d081e00c01a080380a0082c07404812031080c1641d0740c1c82160078458141a00503000500d0a010045082d4003002001d00d88042c950b1010010703120680c0c2402440c0743c001054038111011200d421008031107007042151107509070000c43c2640b1b203036030f800030400503100d4000798810900803070305014000782d90344120b1303440c00514100c0742342c20611041c10f00000300103009800102d0003494583d00e40401600c442080703034031591003214113170f00c92001c140d91941103010f55810b841d8860300812091030700c050308803181d14111144000456190301c1020281d80d4052000c00c8586002d000c80f500d40c9800f0303507514404001c03406158441e00c1203400040d0382d4a000940b04064841e01020300f211602ca60fa800d540f40034015108441c9070805100c45c0d000e4129440130504906400b9070b05000242000940381c0840d04000c000e40750207810320308540c0000c070903400491104c0f00d40801100c01c0448000010b428041d09400000400d00a408005050450100510302 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 988771564 1250 988770314 988770319
    0x150605030f040606181b111518030a022a0105030f04020102030c1002040306111903110712020307060b0621040807020603090a03020d2a060902040615030e03040f180b0a060e 76
    0x42642040801c2d40c608038001601f003000e51160071440e80c01c181a02801d90061307000242c00721100c400d280410704642050309504010781c0b00c030801c04031800321240481042158003420407011400138000038130500c80205400700307091100c00410f04591080040b201d4482482c01030328400c0c1115580c4074040c0d403003880242e48060600003030704400381011084072402c003c0d20401d080e8041c3d07014020f401903c4022103500d20a04203101d0700000c11010500d82070068000d0307024550740c62291600c001121603050625006a405001c40705407803041d03c01d020102c0343c005c41502c41e15500c0d40b80c14149032150500081d0081c40100c20711180e00300001c0d02e61240b610a0b002da50003010341d12403c803801881c00d00358507003805030076003802c80c022003c8842c60402c03030003950042a0aa2143c0214041c0c2d201a8404403101d1a010781804280350b15100c1c000c011242c05000d0352911340342140500c3c0050690183d84081500c2c084039084042d0305a210034620303400039040000040d9103d00141010703d030b007401d250 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 988772814 1250 988771564 988771601
    0x9060302120c18150a06051b1204090e10061412010c0e0d11090f0108070f031205031009061404050c0a271703090301150605030f04060618 61
    0xe0701c012000c01e5642d02180040c00c3d030440040c142107403120000300a00160403040b035006290116441e0450014064003140d250f02d030707a0b00742c02d00c6041003045071a4800a84c1341c100f042d42120308030003102100c044440104011900c107685d00da03014203100911100038074091528400040a52710101c0310910341c030703080310f840d030400f503016101e0f41c00d0b121700c41064400108010f9590740103150407440e1000a501072000081000900004140405001d542c0c940400440302c0040082200070084100600640d4848006061560307580455164081102d00140100400010050004041804001c119928003030020b5aa24cd070305400b0002c401850701c0c0194208000916101e08180481b511036400c0d0346c40c0c0c00c03000c003410741401070445080080b80b400c1030316950008504042071481800c000c400c0003d1651008440100f5017140c0100190641d014460881001103d8004060f0303603002d104d5812700005d6a5036480d0800003098290001200740d601200f801052480030380c00361800000c0c080c03400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 988774064 1250 988772814 988772839
    0xb03011a030d05040e010e0a1409061008031608030c130f050109051c0b04150212100609030312020915070305130e060d0f06020c0a050609010f020a08041e06050109060302 75
    0x1150244114040d0015880030000100250002d03001f8440d4440190900040c5191105e00e019504120503105100c0c590300402c18040400c800b8050b800082c04000021498a20007940101d28908230702009024001c01100050304a00d441e01121403802040b9600858643c403808010301e0f90501e4021140044c804c501702103600d0038005229003109106001c01e030803000156558582c92013000300b003200e140c2107844400c0c28055482c00600701111410b210b2102c20310340380000b40740c09692940001c0030000c20640c100003180c1c1241c855170984000e6000966031314203120208a084107890042d1000710000100710082c580c0c041c0c040c00303841d5a4204814070090f0346520495000380180c0d10b66921070312000211000840c0702d20482e528038031801c405130501c002c40398040e05000c01e42800740c0341074009600304941c1c06070038031800940c48000c240c00c41c100000040014024080104020184190300c04014003c55203070b00003220455012074140400e6840746400405010548400ca0003182680d096 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 988775314 1250 988774064 988774067
    0x1090207020a05131d100b030c060306120703050706051b07080c0103180516030b10080c061c150906050105040e040f020d0b0703050f0109050907090e010b03011a030d 73
    0x2140c4485800810780c802450400781000b560003120111a10543d0307541d1400c80c06a10007203a030074411129803003d0b1200b03512117100c00081d01d0721100c80e02c1c0b098001d0310b02c021150f0b0301c18090301d402c40400d0715001c110030f0381c546201d403070180c1c60307040039049206194000801c154800000c009442c03250115601052521512550303803103c5005154442c0c00040e03940c400c1e0b5110303078880a2901c940c0070143c1c00740059034803003904086119000a10b030036010041401030140354030740320b038100e4140082079480500c0e0540389601c0d840d0382000a4814140042c01c1c041d000100510700030b544d0440c0e40104000484260b28140350744041c8580d0006500b0107100003010b6000300240e130111103002c0345040d896030b161b6031440d480104c4020200d9011301e40800103000300300d07140e410341e10990f1140c40006031400d107003500d003142d210141e000c40003031800e000402c803c2040c0402c0e180202c0f0307085440130071554808078025001d84560031120b5015841d18280308011414803241910410049c3d00303841c1443d031817180 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 988776564 1250 988775314 988775317
    0x41e03080705100e1f0209011206080c040b0d0b0408030c121e0a1104090509010603080409022a031206060c0a08120a0b09011205030d09060203090d08061503060d0803011706010902 79
    0x4030040d9021009125050740c243c0087c40c40040c1490000361900d80d00035004221886c0e9000f503600c0e40d0080941080c541002d22824244410488080c40142c00729511482d5031a00280003d1038200d000c4007180130414883d0654080c0101d0708400c07107240c50510000d4044401c0d0500c45070000300c4810103d01040003074400c038090641d907042150302d46424440da220250002520700308066580b4080003000c102e6000141c0083e120341c1030b000d65200c0203200101040540440e220510101c12180840c01860000c103c0f40c950207031004040309980d804000442c2401440031020032030050b044110104801030004081c41d229023055030ba955264200364904851300c0031401034004440000500207044038282800d105407180c0112440c0180d410070303d0f401d13942a0f80080390055004000c0c8101a002402140a891003d10f48151280703400f20000f012206c034006110a0802c1c0040070400c01c0d00c4408150040d15000181540d40396901c444090700c101d0880030180180c0924000032030002c0b500d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 988777814 1250 988776564 988776583
    0x10503090705011d0a03150e070b0d0b010c080c1f090f03140f0a0c03030e0624030c0307060e0111060106020d030f0e16140312041e03080705100e 64
    0xe0041c6400e00e00191046081d642d21114400140180c030b10b500e68407450420003640c030480c400c0315512544540712098940c001e8190513079070440c407000d021b03200c0360f407040d285000380e61f510120304400c03d1030040e100e2960888024010b5000010320101d44000001c1052001049281b030f00200005d10302e0131070444600303120040600707001801e107001003071007052a04121248080c002e0320340002c4100001580d07001007400b00c085018280640c0a140e0148206484483e400340a00540d04d0080444100d158120100c01005110000b240c0c03180e8a04001c61511503201404803607a00c2d4441d071000e00300815180c4a00d0000d84520128160b0f41000703c3c59074101d8080e0340050600140c420401d40243c80d0350302c0e840c140070760340e5024060349203000c01c00118407020401403070030701c68104070361840300d2001c61b0015402139011800f070f0b104070021442224129150300140d012001d90007840340f02e01b102d1942c0040c00070503020608009200001c0744a642e070400f00e0b00f08220503403030715160701d840f8810390 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 988779064 1250 988777814 988777831
    0x1409060a08091204080a1a1b0a03110c01020d0b03070b030606180405040318091814032221030f1d10030504050105060405100315020f0c0d0905010503 66
    0x50110125080c09030038215088119107083c2c464600304200c804900d80c00a510120761940140291404d03c88850303203240200c00c0b808248031041ca403e5002604510b507658144448160000f651203105209600030542d0303182801101d95960340c5009468080d402000007050400c0c603200d4450304514000801004940c0004180d03400d69480400b00720f61034204003d80811003881064180c03c6c2ea41d1441000d118038400c3c1c4401c032010003540102e0b002c4000a4001c4070030a860800c02c14810b450071401c2103030bca42d000d18005500c00d1308c1080c8a003075000d0360f550b4440180d0010b0440d00011400340003001642c40c050002d40311080d007400e542c2c910400304040503020921441d01c00041a1154a460082e06005007040c5c030f18040100c04034041c0d503c1c025150f00040d5a0358148010408207014213600282c00301c606104e1800d14084400759840c0601c40200362603400c58407000c59100c02c0d01520000d030500f1227076a0b00c0d2201c6108554482c801c6441744000602c175031602107550360041050303900501c0780 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 988780314 1250 988779064 988779067
    0xf07090e0309100c110a030501020a0f0f0e06160b0112050d0306050105030109050a0b0901080307051c0f050a11070f0e060405070801050409050a0b0a0b031207030518060706060303080601140906 85
    0x2246001d03a5000808a07042e180354041c021715030126141c8517440b000071403082c2c00042e42e4254031032b801082000d00e441d0200810018010b142e40c6141d00607007043e0a12400c44000303030746619000c1c01001d40006000b0040124421200004a100b948056040c1c028002e10a035aa100b080745811401c0302c85a0003020701050060005105002c030399031046a108450720f90019054150748005090700409900c6100254000140481040010700140c5075038021080c80c0442d28010703100150a4450440c03c80d01040800304403041540d01c40e17104000000c5e061010348008640301c85c000741100c003090041c1c080440025011907114206403062034031135032940d611020340364205010000a0200c814007507840f0b01c1441816030105251a01c10b84c000d082801e4009800e070784c1c0c40141400c20311b1140303402071005424030203400401e80150803201c100b1600d400d5060625034440001e031060060300006000203103011408800c1507000b4009502503082601d50000003c0a40b1640c500b80c490b002c0040c0e08a2030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 988781564 1250 988780314 988780339
    0x507091e06030b1804052508072c010810050106020606130209060708131401050703020a08161212060f0303020a080a090e090a02091311010c03020f0f07090e0309 71
    0x401c2e4021a04902e0050842168042e044c00b0309410590944094825401118a004a0116042e040c042141150000e095400e01c1d0008160300e4848a20401040b40300301880c1030078602001e0144a03288051032100c5550b96110b91507180c1d90101c094440458900c0c117000400c00300c0c00095440c0c070440c0e00070541c8500c082d950314924082c0d01302000c5181c00a02c1480001d000610900107050030380a04203907807d00300e02c4c08001c56a4021210030307050601c14100407420229034042803d0044c0c6401000c805d42e00d85032406040300d0f442c52007a0207001071401546008074250311001184100324004024066140c941c802c80201132014807004001d644407803d080000b55800010f003900014a0515158007561180200903400c01280c2d03255554212000794411441e2500882c0c1d0031901001c40070010342030942c1c8800d400c4250b400c206040c88941d2032020704041c0300b000074940151092054641d02039048019035501c0c00540038465481341000b80259030404000b003640c0000341d000f00f00303945e203c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 988782814 1250 988781564 988781567
    0xc04180f0f030216091b03050103020114090f0a03050d02061602072309010303050c0709050402150d0906020c0d02060606031320060f25050615061c0507091e06 70
    0x1c80765002101940201900000d0000c4285450401448a05000305a4580c29814000c1400903403c03601c090510300001880540d9100c8004e864620840207440c0c0c0e00c0283d0000503140b00210741016a011000e9200802000000f280a112500d0143c0849296458101c0c0d4040074440c66028140182c5c462182007040300d055503000c0f042041c40c100c20305540106680402c11f00402600f0560101e1170002e02c803299042c0c108900401050406410403545c2410b0340021120304801c4410201c1100200300c0461a00c26035002500160b4816411503031038031000d40081c0c540310588040000341c000c1100041c0141003440c205c0b4819800e84580b080d0004090b030b500941d10301e17400401c980d00b00b030200c0c0c1040ca0b0f440c1e4100030035800030058105610b60b142e4014910b0813200410f5600b8510b55400700c04000500d001030f4054003d2203811419088a80b081e022134142d01070310794012003450441c0c400c800d8541190340054001c603070035a02c0c0c115094507410700c200c1e101c014010074107405110a40c10803069 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 988784064 1250 988782814 988782833
    0x9060601230c010e06251b02040e0a0b150d0f06153f050c1314010308091011070e0c0d09030801060f0c020306010e0403110f0c04180f 59
    0x191404009410301590050190868138070804006141c0c2c858800e000030055038107030211a8a10030454504800c004410040c00b00f0302c4400c00040d8201c11107908021541c0f250003000401d400b02044410003c0071b4106118084410340e502d02032603298204001503402d109006051840c0c000b0300001040c6d0f1203179511801031840041d8070000c9007441d50080340d1030782c0d44160f0390802c0303e40b13803010800a00a0341d49030180401c403c08405510440c0031081e00091070100310030780100c0088070b01e0310494592200c030002038000d20541c00c1c5502e100e03500102c02c20800d07902070405200300355011007007407240560039101011030445000455010300b0f4208600c0a121011580c89054071142c94207090409441d241950002c4000300d010480c03202c01402240d5204072340040f16451031505002421068000c2a01c492040c0903400b445582040050b0034035024448041480300d1800071201001111101d041e01c0d81c0d01510380900c0360342004203401500758443c2085e500031760000090b40d1046c2c4166101100d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 988785314 1250 988784064 988784117
    0x6120804051212190801092705010b0d06020d050901021318020702150702090633040f0e0a0624050903010e030301170601080109030509150c01020403030e010809060601 74
    0x14460f8014009698949001512200c3c0041c035030b1410491400d500a400d0400c142c00208013a0700c3c00010f480d04502140440d10310481d0010f2801c2c2010a605015014100c200551034020844580311010000c180d13009204822101e1300801c941d40725810241c0c02d03845a50f00c00c59420112440038041030f594141500d104011150b001444c2044d02d40c041050601000040b40c90810302146060550618540e00d5910010813540b901840704a03041000f003400d5038481e11020050129080684000d04030200c4001e0103405101041c1559100c0801400c1e0074100e1364004503034103240300043e814071201410b801d000c40000b00c8116407a50b05504403850f800c0b10113040e90645d29059107440d04041800194081c003581c11002c007022036101c0741c440ca07041044c2d00121090b85051600008240d122040e200c16010484a211141d40402c000710041d01552074140b100e54400200002095002004030301500401c0c1c0707985500703a403558101c40e1501e40444000e07000c42c042c0c1418403105440c00c08190701 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 988786564 1250 988785314 988785349
    0x9070e15032b050a02240402040c0903030f1209020603012c13110429030f12251203050a1d0d0f17101403190b07120e100612080405 58
    0x1215000c414110b00d0741140801d0080021b40072030180015428039008400d041c41c06400c102a2407842c1da5002001c02d140d1a0301c103420803050071214505190350340c1001c060160000c00340b94481d40c40382010540300792031401c41c60000700c80303c2c8a503040305d00019010b842228243e044509907070068485d40051805060348a501684e80c901c04d000002460842000c4d4090745c80100030b5550007002458a40b000084061384583e02241516525040840c21925031010a803259480144210b506201c22074480400624801d4050260b011140c1e042c0e02103489008054000d010b41d010b88172000100944208142c000b43e0806220540c4850082c010008149002d1404100301e050347c1c440c142012000f500d0314882e168146100704111150003000441142080b070150040a40f60440c031200100c20300320082c03048540900042c00c07940102c140e03032646000c0d03010034445206001855600e909401080700040d0b880d051001c80c45030441c00c10b0141065024240510741400d00d8104010b140c5503541420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 988787814 1250 988786564 988786573
    0x605120c0c010504030c03090f0e0c0703050702091302151c150915030b010e10030308041b031a2406030a090210020a1716060509070e15032b050a02 65
    0x301e800c09205a5110764060341d21a807041b422890002c5c2504119401810f0081030818240b01400c0c85014a54022030b1401c0c00b281e48010515003500c5901a01002075808651a800c00c011711420f5030400d50742d1b1b842210f1402c005803003003202c07a5480c0206541c0b040106e0300011880c0f48182c1680c8590b0710403e00d98129103815540308012015200c1d42802111201c4080008108000498002c9809048402a00d22040c6031924000400300081d100241c01c100c08200810309114000381c2d10010603007104c0d12141c50315120b00b0200415481502d85011043c0044005060490050b00709200c50300710b5070130b142c0b484600c902000038075000500800d0101d80d841070f034600180d071100006031542800e03030094a906446d0303003031007050150303480e1140940d1706040100082010162999441d595840100000c081d1646c040c91864591290000b4165940000500c03140c1d901c80015104d60310000c404071a18041515054101610340c501003405045c50740044d440014001d0024082d07451581c8101c9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 988789064 1250 988787814 988787827
    0x30e09090c150a030509030702011b0f1b080c04050709260102071410060b0406120b030f010608010c0e03120313150603120509010c0206030907080615010e0a0605120c 73
    0x10700c4a42c07000e440240034882c0003c2d0034001c1c64250080f240e011840d00083d41c140380d20313600064a0301c10403400f080800d242a045207020408560f04403106250808060499336040320910241031119010320841c03072086026280391407402d40030b40c03445806c10380d54007502e6502d0252080010801d801d03020b1040381d5400c54030004c441d424400b07496020b00600000323502c21254030b02d4600340391a0034503070341800342040d01c18003274904200126011075107030713240c41c0340c50071b240c134042d20700504c541c40445a040c09122000200724074150040000c1e1864003000704811101480244ca1210040d5402a0035801000300803040f030043e20082c640c00b1f0046c03840920901c813540d4444102940309404040d086a441780c0070300511400100400c010030290404c1e510780300021780041d00c00700c1480c01c001d2041e4000400079110700c00c1841040000d0480c4411a07040b400e00311204128800030228031400031311201c1151079070b0315001c494101103860711340b103062803c0c0b65198844880d12006000c04000346041020 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 988790314 1250 988789064 988789069
    0x5030d2a0605100f0f032111100902090604270201021207030305070f0804210306051005091906080f060a030b13170a14071502030123030307030e09090c 67
    0xc0c50f100c0c0d0f030801ca0840d080da090010840d80380407150008416100c42c25030520000302031031000482ca04000303040318044841940c1c100c1c0d1080c20140c00c03241c0d034050b11908030160301e5147c00074220a0720031503005009a40c2c08091108a5400401c0e2481003440c40c0c26480740901640319001c10a0700610564404d9414031840000e541c0c881d09007140002d0b0b95070100700400341d01c00510705501100b46000d4645041c142c64805031a00c0e03c204d5032a104565500104a00b03009500c802d0003828081c2072612400101000a449a00100318032400b034100d1b000600c014514040c41c1006844603a1074030001511014682040014000e03c2c05802062600003c00412086052980724003841c085840c0b001003140780030103040c000b000b400c0c1170504041c840002820b0300301080000711101c0c28400c0392140ca1034140751039421000c000f81d5100f188000004603110f03001000c08103a580c02da11b050108540c4a009242d524800c240000d000110a040c140e401d034170709a030005d50804401c0c42143e0181254031300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 988791564 1250 988790314 988790321
    0xa11090909010f090b0106090e04080406030e071e060e0607021c03030b150301030227070f02011b030b01091a03040f020f090117010c2102031b0a02010207060605030d2a06 75
    0x801740c0b0703d4160200100605580544420b0284c030a088840c2824242680c03a0100c501450280710141a290760098060000800603a4024070140e092040740411311031a06100d5180c0e4081c103000a00741007042c00d203d041c00411900d01580c00383c0040c0524410702109540b04840c06002c80806855010f0351845903541c4000c2d8802c49101c0345001d81d04c1d4034510405c00941c40b080841e1000860b2500c55014001d080c0ca14070358807460b6401d00c0e258412800308120300402c80040e000f541c4942c10300d0071402c4681d06600080c0006401c0c0c80e0345032031503140d9529250240036441c10b10301c541310070400900000c1c0340e507619854152019014040d08031117480040d121500980040b4111560301035601e00b000d609003c1ea200d0364013507091000c070452410300851300c5c00c0388211035100281e0300040854020100c00b10200e070004039070192140c443c2031b030060080c040d521aa0040c0c1c2c4c468184172002c51540740204012a0403080742e1903050500a541029140c0700c10984240e5010388840c2e802c50021503d02d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 988792814 1250 988791564 988791581
    0x3115090302180c130e10170a320706081b1c141f090e0303010504050403090e040305090a0b0301210c12080912070506030a27030210050a11090909010f 66
    0x4510a03c24644110748140701900d9501c070650607129a441b407e190240407841409081d00014240b0030030030343d83c000c1ea224a480170642400e00410f0820002c1e201d501007410429548217a031110000d41314100b5500c8602d15042401c0c6a03014200843c40450362952215030386148601004104034450080400c81c110f030440d2061005221800d0500c2c1c0c104c00c0d48c0d5a54080d10048004200354001450255a240014042c081c081d0780e079200441c0616005250040041102c12014007443c5018a4028002c0d044603034014000c08903003002050b8182e0035019203041c1c4202030b03003440e90800d14080701d40c54406a020183c500c1e0740030801c04141c0c6100400c41120b10382c0944a216914000b034000e007c0d2502e08650351010640102d4014001c0b40e41e6442141d8004482403c00b02e41d6500c52601741c0c80125845940e92281140351501800709a004244515900da01440800843c1c1e2514404e40586540070000c10744c106003044441d100c1c0c035056606942209a5000004030800403030700344021101080c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 988794064 1250 988792814 988792829
    0x61c030806010e011404050f0a030609052406100c02130203010b0c150105030601030201080a0605090a0c0206100f0b1b01020a1e050708040b3115090302180c13 70
    0x31020030240e96000700c0f04802d000820b18080320551040720310840580118003985225548442041d2030380e0f510818844c002d160000c0342086a02c20038909503036a07980380c4142d40741003400c4070306694120403c080464454032019146142840c0101402c83d100a002c510891740100120680d418400c414809035001e012103119031a0b0750041c0300d0340c49242ca61820900b002d80141d60005010b1034a0119410341126420700307010140d51100500d810103040c544e04100e4109168908021000c08284c22070200031030960207403070132516000c2c0c0d1040070b142c85004062650100079410081c1c448900c0060244d0302111603c8240030000c030311510309a9121200ca100051a0088201000c80184070083c000c0c660b10f04280d4640780d2582d80d598503500841c0b003515031226011513500c0110128404035805028203155440100c080007030a40b600e007500e8068100d113001841c3c5107014280c0140c030907105030307500104041d07161058610f03480d032007020003001e0401019050000070f003100d8840401d00d0103804e07038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 988795314 1250 988794064 988794077
    0xf05010b030c040207050712140a0b04030905030c01020c1215090a0c0e0108120901050909070809060a0c0c080a030902060a050406030506010f0509010f05130305071401020303061305061c03 83
    0x600c820940b4040c022040944a64410445440003650008480c8103c40d01800d80b07600400450525400300a50641420b0803409054009001c2041c4011810f00c107034401c0c0c17110404a502d850905990b01a00c10305070f07000d03903c07200f640c000c0c3c0d15017000d03540e03409017100701111700300844241c1120031000e055552400c3ca900c1a4054001c01500c150900003600800103036449940c50040ca50740d07140055500c10400102c0040c1001c10b0740d101e001287c54050020f40004003505080f00c0040000504132025940d48c025500480c20048003405060f81c0082c15540b841c007402c1454603006219481815002e0134155250100e00041c2c4030740f0040d200314a141e841d03070b40d1030310b1070600c001c1c0039900000c04103810081d000c0128000b0b59001000e4410651003881c08011284040c3d60594031031080010a80b41042405c02c00010440001200000c0d110203040102c1043e0300000166900d00061350540d9001000c40c0030400c00ca0401e41c46540e021000800200c600d800c0100420020301004c182039000529 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 988796564 1250 988795314 988795331
    0x6051f08010204180c30021206010e0105160204020913050c130e0714130b0d020715022107022d010c0206060a0b0904090c0f05090a05010e0c160f0501 66
    0x910303c0421303074203100d007076410b21025102c01001000d0f01c0000c0c54000b08612034054061010034510031581c48852905021503845e01e0b140d44540040c04200c400c5800a50644030b400d20381d51090054030381c0e40e0320780d1301140c01c40051a070800c0082d40094032119009075201042c04d01a14482c020070b4080c2e04000324069523100d500e2126100307060503030407031041c2602c140107001c1e00a03400f900482d0107001d00c06080e80c4a40e01e00c607403610b48501c0342d401941d0f4480041004544580c0395801020302c10b21890500c603e00544007200b02c00d031f010350007040a00c1500000761a02c000501d0044075405080ca2041c5e80d005102c10420b00010020b084440c404110790100300140040240308074059804140010003241c03400e500010031200c4a070080003050070011402d1641034070b868005080322544441e400e201c00c0c0d11007604481c0e41056214403031080c0128004074480f05818840c440c1078980d9070300465040c5d03403004900c0406a01489000c0b081090402540703001c41c01e103081c640a094800c0002158206 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 988797814 1250 988796564 988796579
    0xc03130306200f04060c021818100b03030a0e0d12030621020f060904140129030108031e041d011703160f020a0506310501080406051f08010204 63
    0x5071880c0010311907200704101800d074143c1e03400356800c50302d5034500784015145a00c0480e160440a584c41005440c11209002003844070920b94800380501c9011940403110f0000001c0958104452303468141d0070402100302014413403001d050b0981c001601c20076954015590b58103080a0500007400020f588007006d00140e0805902020740c2d1a24040b0800c50b9078842d00000c0030b903028660200d2281c00001041c1ca007a407510307001038140c081c405048161075a950000f05007036041c1d44060481e00e88002c200e00d4850450401940d050714001002903040400a07801c0c0c603685122901950060701052000146a640d0400b10300042021500320320515407621250320030b0013140c4200914540c0042c000618081c003a001c40c07c3c1d061340c1100314166040c19a00200d15090303816046180c102c0c0000402d1600c205030100b6000300c440c0c11600c401d65142c00c86a070104015454000d031070001e501c0c4404100403840a0b0002030300506094110300030700f20003254100c01d503001a80200c50a035008070b400c01061b0f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 988799064 1250 988797814 988797851
    0x340b07090f0605030105090a05100f081e0a05030d0c1206090b0a0e060d02040f0f020a0c030e0102070e162703060b0a030f0221100b120708030406050c03130306 70
    0x100143c0c00c2950555044c54005280300c20010074512129030307a1f60002d103000a20400c1c1c8002020b9030040c3c10314940e02c41c0001c43d1070310160030146010188021044034168000200c003661180c00001540c104961190b800020b04000c000742c500b041440c004010b20014548116402055010b1000411036404030a20041d00f00d00c4c0e220140e000c03111020022151104000e000040f80c0c104c8001a2540d5141c00c14001000324070300000500384042042c06250f070b0810b10310340070240280c0b51110340c0c0c4101401282e0794902e0f806001c1c248502d060208546150292100d05c62007400d040628a03050401824000c50103100000e81c41d003502c020081046c070174144a00140d0300713030687c2d01036411801d54881c1c0b203040101100c0240134101c801140d0701c0780030320f101070b40800c500e140d01980e081035500404400076109407400584504280c0e01112200c6500159078011201c0201c06103007002d15094040e1a41d801485810400b80401c0003001c000b1004980c0302000795100315000a0900c8118424a291 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 988800314 1250 988799064 988799069
    0x140405010c020c0f04090c09021b0712020102032a0f0d14072a0e0901020702040e011e111c1b090b0315060403081605010e0102340b07090f 61
    0x55401960f40c0708080d445840d04100743c0201a68046001901c1c0e103030803202084154040701c4854070204040d400e101c54030b68040081825101100c072000d440d59080c116250104000a015a2041140c0700040180c04c4c00400b02500d401c100d152404007075814942003940071846030655400000750900029041610020743c000c0b4021101d007004040e9442c4800c62100c0c403000b05801100011020b6055002d002c184d029201046144545080880002e400b0b034005910880c4154207007044c9111188052040383c038415000c0e820b040c10003010500150003060a05800740d84090100001007006c00070301c0c5c4000703c0ca801150006100320510000c0759440c42085100410030074440300030004070503d0310540e5000025940c0e101d400e0522800003030000d00c200c2d800204000c402046c0c020382e42c901030303285000d0540508000d005601084913041e080b80b090755001c8041c403003040c0c68500400c00829030100034000d00c5e1030f40741e00c21300e482d03c482c182c041c400c40e820000500701c500244101420201c40000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 988801564 1250 988800314 988800317
    0x9060e070e0402040e0c030d050c240a0509030415081503031c0c020a0f08031005090118110c0601300c0e040c03060f06060818060403120f140405010c 66
    0x611605020300300c020201d000d40042d20450304d40403a6104410207003c0000003000040c102c0f01e5081400c54040c10300e81000c10802c08501a11294401003510001000800b00c440d800508041e40c0d8002c42000412019010030014401880082441000205d4130b08103a54640c4410040d85003003038064195100075216036009403c140130101e11110700d1050403854030b03010480850900c5211500f00c0c81c1c02010b140241903c1c0d1621441c4090104800007140214803240c2d800c1004c46c0ca400074040004028800c00c2c1c064076603484c0c0c0f076401906030350119011007800e10510b0720744600c001d129071800c5001e800c1100c0400d102490300d58025501e04000308080c200c0454203442d605961161801a00c0d42e1146402d40c12080e40090100080c1e9010900610380c862402c010441c840c4212000500b0317240103c0e4041078019002c0341900142c1d503004c00004904900501c0980d40d140c1d0100d4004203050025110a42c540c861282c000310a4002c03044012038a40e0054502c2c40c10782451030950715a400c1f03020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 988802814 1250 988801564 988801573
    0x20d050901110304080307020a050607030c120b130b03030918060901150c0b04081603030518030f07061d070602010506090c091813240b091909060e030d09060e 70
    0xd0780902c0d21003d0360762141d0004680c1e526955450300c164140410154024454000c070f50810000a805501003000c02085a4070180398000810b060411582c014400c01c0c0d00000d100c00c4088691305640002d15445406420360f17042c10f804c0408180400c035400d055038502d108020070407526040131083c1d24010710120f07278484540c10002c2c00242820247c000007078040345038100010248800e0b0400c4409118000180131642151030a0040007090140c454161080c01078894080000000050300d80010b0055140c62501c6215074920000302901150302d2070440ca0061842c0c4401d005100340702c000c2c201500003080310702d401400c00c00a00001010a9188501440512425110300a5100c8107a50ba1903854429132100200f400828240c400d00074000f0800c014010703241421803049011031007003c0400d00c0b840744200100f00f50941d04039000380c0486002c0d0840e41225040d50421030103d07003e48400a1400b0300111018110780c0310310107a0310499140c20300801080024410700140c00740b17940182 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 988804064 1250 988802814 988802831
    0x3090328080408090a050607050d0f0c0b1f080a050303090705010c15090312060609051320130902160308060a140111160e0a11090a1203110d03020d050901 68
    0x1a19021002d08003a01070345000c2524103107900d42400781006000300905180c3c45500c6c0e40751039955150000340341d5000070f40a0140440c07141c01600b102502076030141c00e6030110b590b00c6003200c500040403018031000b040008000901d040b81480800a00740c01900507503582d1030580e030001d240c001c05612050400c50524000008600070010b141e40650359554049108406820100c039141c582fa0f10591b20320f07261000c001011500032190782c0031210191079924580b0500349400003283c046065414041800c604809030081404c0010700303e58800340a4000102d441d04d503200700700c1c3c0004105500102001c914001030580200c0301950001c1e0844860301040d08102e485402901c5105581d8180041c01aa00050b00414005480380085122103c2d112550f100f641c0312402d002610301c40c0c4001d00e072124159203420564100c41804002501101e092803030040207403104462a070040d4200042c501070b01c204140240503450302064aa03501586403500c0001c1034003114000761a0000301c0e071600544 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 988805314 1250 988804064 988804067
    0x1303030207050603150f01120e03040501020c0d0b0609090f01091a091b010c1109070c0b10051e03030c0615030709061202190e0901020d0506041503170c0303090328 72
    0x102015017006448200c26000024016038201003140360b0030413628100600507204542c004090000c40300700360300329040d04c000d14040c000e04500c0204040d0410080704000307001400d15906242d009108a421540d40c44610b4090301e0848040c1d81c001c59458120841e050511800c0000440c0c04c5160b00740a05158201c0f000780303040100c0e0318014030381840080c010880502460508015030204098405100c51800d01001440781890031012648010003002003400e841e800e02880301941c9002d0941c5a151a0104203440d0510301e81d0307101da5141c881040382585403807050100c0f500801420343c00c142c80039417010402d405e1002d590440021141740103410010035a6600d41018641d070142c40d080701c130202810381460b0304601c0b6007000901018401c1403105122056004004003001034404000316180d24003000260340041c451582c0081d642c513030500c0070030006500001c0b51440720b00c100d850000a01d862030704542048032450082d8001203807945400104041d0035042c280314902d134100e01e807030b440b40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 988806564 1250 988805314 988805341
    0x102060a050601050403080d09050706080405060403050313061a0907180e0907031a0106120926130b0304140c011d0118090e010c0504050f091b1303030207050603 71
    0x102040103900c8001082c01a4068001c0354080c1d904244260b036181141e505202c09402c56140c121105d100f601c000140c07040c030407503540d40200e510501400294842d41c904441c26000948281c401d03148030515003000568074440e00e03110b44115244046424607500c100840c2110061882c024004070151011002c440290140c3c10b440281c10341e82450740360090801d00d4112545c10003001780c400f03650700392446490701c1082412070308117548980040d41d10111003015a1046480104034010700582c140c0101200d4008045070740d890190340341402d8440c009411071001650104500b0b02c000020301003844200c080c10440c0e052030303900a02004002d180002c1101c200e465582280c20f1000705003a0160784202155140003c885203032281460310380765010b0040000c840c0f401d14640c40c106440d0b54035405802582c08039a4000c1942c6050007a08052022641c0000e12140c41d0070100c462121001020501520040a00c500503406503400d40c80c02a00d8014540c00035841408140100200e400c2e01c40c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 988807814 1250 988806564 988806571
    0x603150e090a0b061009050d0809091f120f0f020f0310090510020408070e0a021207050429030601030e011401060810080a05120a1b08090103230a1806020307030218010e010206 77
    0xc0d0002c0c038a5002782041c203414000d200c2015448480359050152a030408060070300030340c00c0c0e8982100350507995003640138a840210f90080841c0200c0030113030080390700ca82106009a001800445840308154006410090f4800404076400e030b132422030000303000007003007a1071003208001011840c1c2401e24481680d211494400c510b024441100002c051034400c0d012b40f003517103844c44250703801d608085801910340c1e0054080c880392408400c00c010112010150082d4145441c04801031a60325400f00440c05031540d00d500038595901c90402c550b00d04004030046d4020440c9035606c2e0700605200c104202e60344010ba0003070620398021a1a00040382d80881c9842a40f0041ca150703945d0fa0540c11400d5861390022030b149080f4407043c002003000d02c19440001e0904480036a03041005e00085802e11080c2d0820a280324500b0910710001141306c1d00b5a484010044d0f00c12068546003500c66031084140d0b031007103500b00002034010424403500504502155421078090900c400007100c1c05000075038449005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 988809064 1250 988807814 988807819
    0xd14130b070c0609110f040212010603150302031b01140406050412030e0319170c120c070b040315060911070308100b1b06090a0c0603150e090a0b06100905 68
    0x408259a98040c00500c07000036071040742130201101e581080f00c0d81c0151592058080c0c0081040c3c001240340510885d460252445a141c41c1c69007800d40450040611000075040010000d5000c03025982c100160660101d490005541215408000421140030510208030003141031005002840e001300c00d072000da500ca2055211061402e040032121180c180d542c45800d4010308881000f02038541070b10110550080c031084c5c20203c481e100282c882d1141c040340c01415001200000ca85400b940000c1c8840302d41d01e0b04035001d00e44c450256540580c016442290401801c028581c2d40983c50700518000b0030f48050700f0030030300440200d103040038402e0080081c208241307030b00000e0400318403030400380103003030802c5805403035821010503d0034000f50380a01d03403a244500c40000300d00d0380340040d2004145522128004803a4900b04d0254042c20010041d07501032282c01002140b2100b100b69014820300d0b00740c0c000e096503d8641401d41d500403020b48954004c910b80c0f40c5c030003140c2e40c010f01103404a4405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 988810314 1250 988809064 988809083
    0xb150f0711060708120f1012032f07140d0c2c13030e030706051e090303030a0902040b10140702030c040f0507140306130c11010c02030d1413 62
    0x1440080e05501c180600140104c0003c0340204526410100e03280c030031800b4410000e441d0b10390161034224050944103c1d00d1480c00c21040c080001d10034407244110f10015a81e030711000308601c40c003040148a00300c0e4036140b540540e2040140241140c541054000142c800c2c000003201c0303440d011403001c03160040e80308a0300c1c1003803803682400d20181e0842104d21552808112428031491415840d1200700040e40000c0c108001e00f2aa40b401013400c0c012544642c132014a0142d20344d900c000c044106801e011501841808076000d00d031400e0000314400c3c0c448110006010602c0d104200440e41c403500664058008014102e4030741d90042030310010881d5807507101d0b480381200c1c400a4500300310480c0c0d56400904081d460f02200c919500000d01894040e19001d04940d8030030110442d80c001160040d5119061040300c0705644016071005034800b41034907004030b0111b001140c05007500c07103102c1c1940040e480003e4202208007184164400c50082044000136070401300c4100024454510f406042109e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 988811564 1250 988810314 988810343
    0x70603200c211c14070c1e05101a0307061d0a0e060a051c062c071a041d072a021305040206030403030b01120f0b150f07 53
    0x204000481c6514a80c0034a0001c10b00d5161500b00c040e040498030010f10f0011510040400c403641c0200e101113204003444032a81d40da0240101e440c13620119040e01d4900c4244144900c50064854220455000700020040544000c00680880c2c0d50017840e83c030b9080e00d8240d41c42c40d42c1e802040010880300c8074604204100041d945003c6169001440a036009040110018624500c000401d2151104a402ca41c9070740d0354809010780b407540c46507051800c1041d1a86040040c1840d8052100c0741e801020300c16070440c2d000300c500c1d840b2056180e229281e500c03001c070030403203110481026032416103100d403040d003854503141002440c1400c50801d00c400862100004003043d201d03414680050713030000044c051490b40035803581c000d0030520200340d005400602c4082c200700018020140030b01d038082d1401d03141d40c1d03550f00c2c100e00030314841300d00c50304012414548103940d50a41c01144000740841000040e100384000400c020700c036041c070a0410840c010320120406010860544e0001500700340310403496030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 988812814 1250 988811564 988811587
    0x804020a090f051005060406080f15040c0513050f0d0201030e030c0d0507120338090a1409061003170f13030203060a0608030f090117040f020307060320 67
    0x9411081c07615280c00c000c40c1190540740c001501500c1d128160041d03183d02c940500c420381c45a40030700e02c00304081c00046160a07100e4201e0b01d500c041100c050030055180c0300002030035202c59043e01c0d0002500410340b56204007174803181c00c001704405c03034104030241c280001160400040b07143c0030f4145030b502c80c000d0844c01d6060044801003102c50b0b0a440c0c0310219428007400d190040e90040c1c904d18074048502007900e0091003041012984560008904a94940820820041b4038001e0a16541c8002400b002d40c0708d0f00b80803801642080c2d0041514050340d40c25507038108000b040103140c0c0d84a2020300c900c0c2d01203c04d01805494100c5944001c0040c00c0b032804096204a018207001742e1800501140302042400e100c0f029203208070291041502c40c011140140c0e2124028040c042c0c1003002541c1c07400c00c1503c020000b0b00300605004d002142107020310854150200c0d0161500c00261f40070504501e170500185020740703080e081c01c01c48e48404034007600c0e000d040d0480d0f190745e510001031a2800903 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 988814064 1250 988812814 988812829
    0xf38030319080417070b180c37030c060f02070b031501051909090c020a021e0a1a0d060e060a050f01020703170702010305011a16020d0803071106010b091c020a030515090d0e030d080402 81
    0x1a40f088602270900d65a86420f0610340401c1c840e6100181d030303584090960724030101c3c287c81100c2422a6081c1942c41d411020306052174040c8419050100c10480c00d03000040d4050750501903640d030313280c1d9000140382c8204441550101d80030841150080e00e038440040c0d55024a01c1e102e40c280007100038507500c1403408201d41c035040f82c0001c0070303c4164411380c3c400c0740d92502c0141901c081c810002e1150654950700e4101c060820381c0e100f6480540c100f000c1c052410b0100031000441814412240150b940340c0b07131501755002180715038003480130000d030030703420365825001d030754010155400761031038030300740007044203004d0151610b100c600d44c050840c1c110965661002c004445c0342c0044070309a42c0e0800e503401800320084d81d5080c846e03901843c00001110038043d01130b03400c00580984206210000c204204854010032202280e11041e40140030000c103404007c045030341158075280340c0300da061104a040ca00100b288003601040741710812048162000300c2c3c000058a000d05020b0700035107451000890300c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 988815314 1250 988814064 988814149
    0x11031906110c0a0f021305040201021509121c050c0f0417011b0e180105062208070e04060515060d0f38030319080417070b180c 56
    0x3901c0340103501c2081c849404d04e039013140c6100f1145034141d400750119280c180c2c0e4007150041d002d80c02075a19042007005e0800c1c0ba540c407040d44801e458501c50f40301d02941081e00114604692101900d8a0040d180694480d9941085841a104c0d00781040d010b11038040740300c0c0b80150303840118a44444100d919094100502c020080c0e000329a0140c00d20f500101008500c004440c45840d2003400c0340c40d860381100f24181a1500a03007807e142068440d0091255403850300003030301d01504581c0003e1000d40c03e101c00070241019103003442041c102414a48291440908000100303031541c150030034503070faa00003261002c0040c1e10010502e00605240398004000000883c0301002042d10308500180706030300317030080040a0000c640300c002280070505a490098010000603c01c1440305540700c28020301c1116401886000c9010021500a050340943c0c1c00450048481c50401c0e418844e07a1a0b1511005210289810051900522030000500b2000d4078800c868404403c0f92480c0400d541d401c00104d82 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 988816564 1250 988815314 988815337
    0x30603031b070f170114010612020a0e0612091b0102190618050105010f1e031e150b011b0507060315030c180e0601030b0402300a1103190611 62
    0x15250780c81c0342c014103084d41c0c03101035400e5518012a6203c0450b0701842c05050310100e64400382c0c40524205c9040081d804038502d842440724a24400350142e898074020600c0780c04168820300e03a0704201110616006001c0204903091007040f907101d401d070f640041c001c8141020070fa00c0145401050519000a00f90a1499040d80107448000020b105054100a04842064071441c00d85a0355040e101802c460345500186000c0401348100040b40781e10018800c0302e0145d241c3e1a00340a401e980780f130707009030000c2c941000c0e06d0b450f40001d01d90356030041d8180c3d01120070b80c02800e164401e0765440710b4035014036016901c127150740c8041184000c141e003030703451002d5588031800a407115164400b00c0a50309103059803030070103414440002e4142c1350201d4024101c950002800310143c44690820121480b0141c1c1c100803259521201c0c454409d400f044600741a09500150180c2e54150622204102c0e61040040c0030303038041415681c403040c0e42c048201c41c0756003010000800905a0340e8001d4507200740310300e644 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 988817814 1250 988816564 988816589
    0x90503010207051e07050105030402060309010b1206060109050a15030f0e010c11010c050708070b09192103050903040e090f2a0907080106050d15060e01080c030603031b07 75
    0x20003c0015010b80c4520503c0700003034450079074825003543c6440b40d0203030034001030040c40460014100100a560031403003420004c1885c00311940401c0c23a02c004103d0300b04117a030016060021a5800140c660060300080d252030840c1d40c1041d00c103000002c5014a00002c05507114403002516050358825038407200ca0900a220031100f00000402003150098203507100d500c0c11480441584c0908101c1c2d180f198020300340b500700855500c45561500e0018034040c3d06000720081a0700002800f8130140b0001c3c4074040c0b400d8100c02284a4405010074510b8007028180343c0018070131401c5c40002600c04603507400300c5440075a80c501e00070364180001484054550b108030340300f16003194043d00602542070401820091304001ca07508001080c042a2010300c0032500020050000302e01c140010450168455400725010841904030302c403114040c2d00c41d10010b4009481d800096901c19011500846540c445905605105001036220301c12051414042401c10600442c040401d0100c2ba00411500d282c40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 988819064 1250 988817814 988817827
    0x402010c0215030c13090c020a290109060314011e0c14030703020c0d030c050313111f260105091905090102070210021b0f0a09061403240601030c0905030102 69
    0xc41590045000d0954400e440a004a500c1009120300c0a20103015802050058083c5d2030301a52450030110300b039080104002d00070384ae80d2921000768002c007006000050082d207141002041d5200300e030880011070b418100902c4101e00c128400d00001000403000080c0a00c503d00c05565901800302c0362000c02d48084100b01d00707203816602425903050354609035000101c501c802102200c0588203107401266040c00403480d6080d5401c41c0780940c1d44204481400c64840900150072405014480b507400c100404250303218036400119002165044034660900d00c2e400400f4070004281406050300546007035001507150030007140400e0a0383d0120070b08120324249a15068081e50005d0307400d900581e02a003e2550191000a080c01c2000007240e004140c251a441004081e044281d076099120035600d401041229461051800802620312108015807078842810300f04100a104035613541c10070217198008807550500b040c0d200800b480e002581c0c0c01090001d5801c0d140e2500802c0d0103620102c1c3c607 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 988820314 1250 988819064 988819081
    0x50904050f190c0e07050c0109060b041503050a060e0316050703030837021c0506040f05010506041404092130110409181e0b0402010c021503 62
    0x4600703080403850907152800382d158880c41c0359a440c454001c103403101181040069140c00501a03401c80d0451034140d24200f1900303035440c2034921000c0142d4446035580342c40d210501e80740c4585a00d40101c0c5d110500234074956258152542c4c100d1101400a586032040c0c00c030380c2d20040c000c0f01c4078482c0001d60000d0341e1105041840c1d68003028042200802d60701c40c08980070360041070241304181030101c1c40f207000551626440f90b2883c0440242644107400f44141d1803c2040b5680800c003032040d4200c001030310300c0c000701008160b902c070340c0741213032a185010011b000c1c03030701c9a500b158283c514003040d0284040300d21000c00d0060030f4080300a061032001c1044c103c108100120b8000d06443c01b50ba44114900c924022080b900540c2061801341082c0303000d42da10300c00c410b07400960b60700c1c040c0da201c40d040660320400001611783b0549021101000d1000d0b034020801154801d0503520000c03880342081c00019614084050310103030001c0d050003503c081400855840d00350030030700382d03000b070010310386a0408848 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 988821564 1250 988820314 988820323
    0xb04020d1b17010203060901051011011109040f0605090610120504080306010f0207140d0309030507090501080d030207020109061b1502030603010b0418080c160303090603060e07140a030605090405 86
    0x606069240c811035442e00d80605009690050300b000b0700c005c0d41a442c000401c029526241030040900001d03a1400004032020700c1009800e4070004800b0743e5580340382c400c12045494151355046c40b40c2c9002d034280015164040c40d5070784864150349011940c1c048210940300858000840301c40710b03081c0020441001000307000f5500401083c0c99035288040403030803d076140c14542c050360041031101000205d061a103c2c0110103924081c0c03e2101280351030391a900d050184581211030f0060b1500010403280c901001506401010307807500f1410101280e000030240000c0c0d1152100b041034800031905003070011403003840b400798046103012a01c15400a41006500111080740c4294680361615105041c14043c0000a030071055000040d4401036448032804e802a9807100c01c0e9200b041c441900f02c03001d440b11780d030144d40207882e40d030f00c2107160050040a581e5140c101080c0341251406005042e80c010040500601550020342c0e01d60130004001c80003010150b12295118045005001c20b002c0c0105 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 988822814 1250 988821564 988821569
    0x31807080a151b030b041d07060e01020d120b130c020d18030b3c06150f0702040b010203090301020d0f0f0504020333042108060303070b04020d1b 64
    0x1100301c203034a1a02000b0700864412190490040e5690b4800d030b500d440c0f01c0e50082c4440312000340b000404041440f6031440403031000e03803043c0b0280d010b504180100740d0045941c030780824003440104412a40b410005122707402c2c01116499103070310f64250542c20b07500c3c401c7e4981d80c8011a2070801c504001513000951714002040b401010403842c041e0100054114500c0c08190f90700244090300700d071514050501034500d0b200280724411a903407151071000902004503100c411700b031401c01600341030150422900d07045020050b080460f0400041c1810080c0c1070030b8035001c58044800144840b039180060381188a405011580340d4400600d103140743c800d41c0c0c00041001c108410412131603541c080510221541507401942c958400600c40030090002c4160a075400716015840100240103030940704c039440203660880f1200501c2c43c181907840a8030003100540012031400b4500381c2840b0001c0f98036071203880c00282400305090005000e540b600c1411001040e072040a00c40d6a0352000c450301c807612a0b50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 988824064 1250 988822814 988822823
    0xc0d0516120e0a08030a02041e030501050606250c18021b0c220e0d0f020d0216090e010209030d02150907030b4c0509040b070302031807080a 62
    0x200c80781c50140014401c0d500c21078080700060941ea84a911510f01c43e0b04018651800d964080202181c5054462640e413002e07040444c0c001111811032900c5425220000c2c10240594024092070384c100c515401481c851204000c4003071710f80c1c0c1d120704102c802c058107600484501e8040040c200320183c0c0030741c01444203400c0340070310000031810410300640b21102d4910107039000b80b01d4000300ca10322071400d00030316080d140d041e00018550080740c255030030b01e01c2241c2150085046007584105e80c42c3c0501101c255044903102615031190342145907100d81400d401840030041e50b407a030f00728804038254100c1742c00890007070454026001024009503200703080d440590217101d890003c90281c850000342c20059039800150341031a5510400902c11121303d004030310085110801d940700c101c480034212580100070800c103801840100440e50412191315030300090040241d007041001090031400c40310b4010006140c0940e894a0b1001a26071080c480e04180703500d07000300f100000c0c2d0442c0010f02c04400b140714 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 988825314 1250 988824064 988824077
    0xc0307110a0b0f07120e060a0c050c0607020c0a05040b090a02030c1303050304091b020c0103020f07020d06090b07020a020607060e0a05030a02010f060f150e2701030507081609050c0d0516 82
    0x402e01085c1c03d48800d00c81104156014002241c580b002d41c0d00071440000c0c50b841e16509208ca0b241010340340a1080e00c052000da08a0074240a15082409410026000c1a107040c000504031201190741c240c0020500c100700355011020400c42480318089034841c442031212601c0302e42c0c0f1b07070501503186d911606c00c0007201803070101c8540c00310304516041200c0364070743c0c2c01a11030785801d07a0040d8040d52000b0f508101c0d0074410800b000050362030444040600380618400070ba00e11035458181100c002c003912810a5610010075500140d503610120b550042d030252004c142d080011400d2840d00d84d01480080c071500005c0307480101c603a4158004542c2d9041444140300c00c5542d00c10020783c017603490050f03144030403411040b407002c2c50244c10100701c0e80801400203000504540c846440001d84080d010006606141c01041030000420180740600a04005042081f00300705403026400030520070b148009440314000b5403c01c4850040c0d0b000220003030010300c05480c092104540e03154001c2d000c030b400f00b10b1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 988826564 1250 988825314 988825337
    0x17060612040b0403230c0c180403050a020a120e011713021507060e0307060515010507020103020c0708060a09030e0a0608010e180d080108010c09060503010611070503070e1e0c0307110a0b0f07 84
    0xf404260001c5040148c428103403592101c0e21304650b22382c001c803c1c02080d07100c0c0211880015906035100c2c2040e420300c1c0d0f40c420303642400340c00042003440f00807a580b80c0c0c40107070400d200d10920242e405d083c0156040b07820b40145089468040fa00d40075554000e419185003032011022010302000414840c0e10130481041680e40d12141d02c0105820325021310300140c0e091001d040194040d0380140612130140c0100c07242c56564545640c41d080302283e8072001691141c904408042c3c12801d030381100102100c0074a00207040c00f100400c8108144a20f5001080000110780d4005844414422070384c0041c007540e121023140080079044020a201d015005c2d032803c07440740e1549202d0b071040820368607565121461a481c05808807103040007042000c100b0f005803900002d15503030411105c40200148043d0a000345084a408151282c0034200310440700640c1e002c025a5842080841e544401c031400c0c8040c648440780503152600c0302e9186c00504400c450344c00c1c40605c1c10a02c00b454480c00c1c0d240c0d100c3d001e491 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 988827814 1250 988826564 988826569
    0x3170405210c1207052109130b0904080f120708040b0a0203040201080a0f0e030d09030305090a0302070332011407020c0a1217030717060612040b0403230c0c 69
    0x700303070003402c0302e25000007007080003803002c580003400f10381c5c0250100d401055240c040389900b0700c081c00c10700510f0000002c4118580c1814a0380303260074034410108202d00f80302c66010962654000340010008440000c0520f81802c516003580c0907001d00d96038203000c0380742904015000e500d05440c00e0b11032403030100c005503401c00140202e81c03217074ad81030707444400d140c4075504154080d007081000380d1f5542d42c40d8400780e502020104050320000b442c6002c08a080c00d19400d010301140c42c00740c0744480e550442d02c1218007198001686200b225440400807690615104144c0b0030350101003a00c013140608100401d038540d10541244003412110301840215850744503040c1d81d102114020350f03400c0081c6074001c20089035160036920300c0c0c0e80903210b400c0c0c1010350203400762015441110b5810108003054051510301c05103911059205034250381885ca03141c1e6003c016010100010070013811281ea140004040522a022018a0f084482d030406a91040d44192034116044102030443c184100c0c3c6150100d071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 988829064 1250 988827814 988827817
    0x3040b0d20121503030a0512010909050a170412060c0311031b031302040e070e0105030d050d1d0343120c12080403110106060e0d0317040521 62
    0x9a61400301c0610302802207140030556003006045036060700e90f02500c2c1c80e00703440620003024000d5165a50340c4d41c0d101880c00107451408182c100380b5480e4030b40506080040c100151041e00c664006811010310b0028803400b014510407900000d00750402456410100019034121196038040350300c0c24040b0180c08002c551030b60004883d040d09500c403064290454039500c000840e04580c0d40786400c412a2541c0c2c0100e0300f41d0b02000e082140a40c0031000410403c44c20f4070b102c17800340030105e010b894060145840200540074200e41401116501c10042a904480d08035200912401720256a111543c07030042200081100c10120042e40c5d0a80384010b600c0c0c05d00200c4003064800c141181c0703801c1e0180d201d91498030100c110060a22281b50f5102010484907000c01c41d509510365281c90440c5404d01d00180058035000c8005030300da0400100b070001681180000c0b00f080c20660709600118040d027011608a1031400c80001020500401c0c00203001c8089210840c40f061042c407011134400004004015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 988830314 1250 988829064 988829111
    0x70f0305040e331c0b100b16030305180706031a01051603030207020a03061e11090307090b01090b13050a21030302071a071e0309240204030503040b0d 66
    0x160030306003142d096500807004036803103000141c80d000c21030001841c83c44001c0200181940d9180b90842009804220500340c1c6c009480c01d4042d0900300703140340d012620030500103000241415100d000007000304180302d0498135031f03010b4401100d0425a8070f10340507004185040d1a0000c8a141591400055014008841c0300382c0e284807490080e5081d0740c904800035040b014040f64042484040040425624051807480c01c03c4240054010115031501c4000c40355900350b10341e41d9031424081d0b1007499070041411070441d1110ba202040e20000c100040b2180e56440d0400c401c41640442c0309582c41e800c5016010a0b200240c03544204642c4400040e00c510522110540742012600d0240000030302c02c2d000741a2081c0300d0109108034003007289043c11014002c44080d000a8a22a188507608440d2500d894651020342800c01c880303075043e00d5001c10041c010148400900140c04407118202003603048400441d0000152912141c82c2c64800e14683d1042400c0c0d412f05040800624407030b600c00024149 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 988831564 1250 988830314 988830361
    0x28030905100c05031b090904030906120605090a09050309060f091503060607260a0f03051503071a0705030a0804050601050108011d040606050405010602030405120604051f02070f0305040e 82
    0x40d175070340c2e44403030111420045086030080020300528442c0d4460504c510f0080e4429128420b4071401d08800034089084511444051400c0c2a010021078940000e81d9400c000c1d01035000c00d90000341c0c142549184902d40e0401c1e0030800c000f0b404028645580050b14003200200c901d0712280104400c580d2107400103680607640100c3c1004118001844192440c005900103503148001113817060070500b01d50030000c0720303902007100071900070b009552511401c0c0d880503002680c038903d00e10240120341d54140c54080c04c80d00012083c14203810101c0c00e01501d2100b42d0060460740c1c7c5401403400100815416202294640319501c00825150f0007202460305892010b600e07003441d00908200c641d02c0701e402500c142d602c907503100c0010803151514091127000c1c01c91500296502c0e860b02d0140214840c80644105042c0c00c0300d4140000201c01003241c0052030301034076240c40d12035020042240207220300d100081420030010140400c064000001d0801c13280c02d100603074460b031b4404c95000c00c000ca02901104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 988832814 1250 988831564 988831567
    0x406050f090c0703090b03010b0d0e060108030a0e030a02041a030613150c0e03060103060b030d0c0206030606130e0108060f070804030e090a0e0106122102100228030905100c05 77
    0x80c41482e5000240042900030301d4907441203a5550a46140c542c42a005000038400000351015003071440c1c064850a8221200100300030b42c50404070503101d01a10300c1440401804803084034055804200003003810b60014010030242e500200300c8000f4040c1d0400442c06030080d040054815142c04610700f03507d6401c1f240d4140da42a0000044005010030411728052003860704503a00c3d0741d2820001940070b1407080790005084422801018581900c1070803000c204041084110010780741d030001d4982013481a1006071311546286601a4102d40300d03006210014001800000c0505000841d980a54044e04444501e500c844a044801c0c14080f900a4045192404036040500b0000841e5a11502e00170000468042c840026403d44e0f03100d500489041080c0300000c1c0030300100c2d2500ea6030050103620440012007503903502070f449103102c0e85070030320869010469610201400c805c5d92800400754000103220480518090010001e09a0980d604d10510460005075108cd01c41c0003803480071611080e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 988834064 1250 988832814 988832821
    0x1b031b1b090a0207051902031605150306030a120305160903050c09042901080c0103020301061205090a06090f030935030c340b070219030c0b04050406050f09 69
    0x107980c402030980b042d11a42007020030007261090001140f4810094544032444809004042c0303444203220039007003010890030701004507658512044e07030841c1008000c5030301ca80c5e540c80000d0811085e4980503108141a586415000b81e26901251082104481c501c00860300c03001e0440303044503940001050303640032486040c2549081084581d0040c481c4c01651103070301d03030030710344251440458690000ca9160790b001804510000d1040043c500000c0c6070850940d07150900060244954030b80c80003110f6610402728070f07290b030140400d928042e0824014081c5407603600d0201d480b811848810b400040c516000072444044208000071100d5000d40c0c040ca001c011895602d6010645a682c0022440b0800a50514030418400310f01c1051080031401c0403508900c0322a803103144684080c1a450120b601c041c401c0c0d010740426035035443e40641d11300034010428084540c684802e42c0018100704420000018074100b028000c000359803051b18140104c071707569000c0c072111800441c0070300e901180c1e14002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 988835314 1250 988834064 988834069
    0xf1202031c02090a090e01020406090b030402060316020c060304080a0e120c130902120c10020309030d05030a090c08010f320907120602090109061b0b0703021b031b1b 73
    0x1a140d000030003004d084040d40c2d203010391421240ba22169101594000c9000c20030750303801c542e40034000d004144000340b46280030340c001007803031000401e1550344400c40040100258801c11410b807001c08060115592800d0905048000d034224040c400300040301038500380801e0034524a50803220b00c4440041c00710321101c0c42000400c00f0840c928100f115030f10300c158400350f40c1d554620501540c050b400741c0345c0302d904601071004000740547c1c40c60541d0b108120329030982d1030000b003031030000e41c441c0f4215440351554082140580080700014100783e0441d840411a60810340c0310034410403041108210b05d42101c0c0b690308000181c0e00d070f100001e1035240411507002c8084001f180e03005c0001d03400e450b1072641b00d03004061203030401032003651147d9000c25004103a58000c0354607400340c1001c1c00c2a041443c02903038a48041d00c4000c00c02424280502c1c00b00c0c00c014081c1d0180c680143c00e5110050808504541d4a40c0d680c20200c1441244031a05540e050b0410b00440c07154125403c0600640c0314401c1c4106 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 988836564 1250 988835314 988835317
    0xd0e18181002131e0303081f090911220b0114030a06060f030c1b1406130c1a070609032003030603070605310e152b0b09010e06040f1202031c02 63
    0x20700e004012121207486041d05036000c1006002c151274001070140d018100102c2e91070035517192501800c154107201c075488030344540030000e200d2804c1e80842e181e0360b0302c00102c481003400c0090280c48000403092001c1c001d601d130080f001b0740380103585055060308500c1c0b08505030349050b070301c0e04040744044000020000c05a500d581c4550700603601c028540316050500c43c03401b4000c540d510f0200e20801040b80070840c542a50300002e12040b4101800b0304151000c0c0c0d0310f1481041401484650780c0c03100001054040e003010101000c5084214004d442e5402845459510843c0e600d4442e0048543c04542c040c00748050b107a6005444005e070280c03d4a8415007100404241071078000110340b03034800100034414283c034034410601c010100c0b0180740c40105201c80e84068070b0359050301181c02c4440030901440045044a950713001000441c4d80d86030032400c2c1d801044100550305150080004000500c00d845000c480c000d032062000813500b00745150102d071030380501d8841150031303d8501401c0d68002c60a40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 988837814 1250 988836564 988836571
    0x60a0e0417031006020f0a03140a0c051c0e0402030f0103140a0611040302041812030b0616030807111203010504020c190c06020d0e18181002131e030308 67
    0x1c92a2144030169030500185030000c440c184005200d90074180800c070b6051004c6010b06040c54010052040c803076034003615202c0030b0701d1650301c0c2040228100328201e1040d07041048080c3c0003004c1d00c181e84a03503404000c8c400c956100001c081046041055000c1c00c3c01c3c400c40b4400e420041115000c0d0f404c550340c10260603c0c009400000e0b1080e41a000003251452260204200a82015555540c0f440c0705010907604889010804802d10f0491480410600500342102507150701c0c0010f011124103001031110300400c018101001174110541d01015001280507000301c00d140c275100c020300c00f140c028a1303807125094051702c1a95800c1c0010020790406030040d102c0c074071a990644000d8401201038545249085209444c6c91059120403c40341303406000400600c40c1ca860300c0c019500800c0c0220340e80304080c040320705030b9155410004035a19104d03080401580640d900317681380030303481c0b9030008042c1d004011001035500403100002007404224882110405496540411441c076586060301e07a140001c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 988839064 1250 988837814 988837823
    0xb040f03050d140402181b0f0c03030906101e0302212431030314010306020c0c041b0e03070b13090507230d02070b0a0506040e0105060a0e04 62
    0x40c0070b0140300100e80c0c0541034890409061014541c42c2900400500201d412101407143d00d00c4005d01043e11207402d800e40d2003501e440042a030321b50030340b29255000c0c0301d88107880c5010700020003800400700000c58428029082e4400f614030321303511240100c400c041c445840903014002c1110400050030640203409a41140c48040ca10400040345003509101c003456031a80103556402603000d540544170003da40242d44003800c0b50100300c40081d042485030442c90f1500c0c48445051006081500c01d41211030480340211318000c055030b42c1e240c86c00194100c0444c1c400240152001c07882c07142000d100302c05041448407801c40c4076001419042c2e82c5a41c41285958050190490200d20300885c980101844410f0b031032a05460f80c039102041c1300302d44c4003500b4070040041031034a11524680c40003042d4a001e490302c074450b81e20012122520001d1191080080140031030310100011501c055202511a040c269418000080307500c059500302c8070215072081c0d1010105d0414090040d8082d007059000d0701c207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 988840314 1250 988839064 988839067
    0x90d21020f0f070203100b1008100305070807091404020609010503090a0803010b0a0315320a06030207020102010b0901031e06020d050405010b1906090e091c0e0301180b040f0305 78
    0x1844111984424103142e418100019000110304040204807042d02c44000e0070410221002c0014101004003020042040140008030323110310418001d0381c0041d03500c001100c001e5591689102c1c0c4441c498810a8401ca1406500c5114a401020402d104560041c222480c18111600541c0d41e5000640b11003400c2c0306400e5003200007001180198060610341880c1a194520301c68000e050300d620340c0080040919180c801c00900301003203024080c500c10703203404003082103800c08040503034007650340b1041d440010342400061040c1c040d401082118000c0e80248103140c03050041c00f4003208c0a1000404204458401404001400d1084101c0621441c8050300d810804066442911003e0310241c1e1345964508180c2250b140c6025028440e29040d6a0201c65030b250840281a003034891060780000c410090014004400900c0103004508507402e00981104900300300410160b03122265034013039842c0480105003a0084c4051441c1c95a10600c40811980c2d01d50b036581110090000031801d1040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 988841564 1250 988840314 988840327
    0x80f060405060a110d2f0c120304051c080a05011502060c310503061b16020f030a03020706030509010207150216150203040312090206031b041a04050306090d2102 71
    0x1968010141d4204c406c00c00400d10300305c14118104d07610b800781494001e10000708600d11003480301107002900c0789101014203440340e031036080c84d5042100e00c00d444031016041c000c52294041d0460207690144c903100d48104007581c0c9485030706028080361501d22000d80d100b1000505c1c80d0034030200a190100e0b8841c540044500600040e20020059690070030085c04207010078803c90500300482a88452070440c3c4000000500700580c40510aa0340c0c04114000719900d11000d54403010041e040000700a402c40c1c0925029081c001d4136455280035100c0001e040c000824001c01050003900c07142600030401624580c2e5080c5203000030b40c0b012040c4504504c031400d10f440442c2041010551420002d200580d4034942454024800e0168178003c468051404002c040581c84100640e940020000a4206a0007440306c2a40d194050350b0310103089001000b0720440341007500d1003d0022910140c1c212404e80d00c841440075120044810001d00080c5640b42d00c0514680c54003880c0040c52100000500c0c002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 988842814 1250 988841564 988841587
    0x302030f181e030d11030423030403140c1e01050a1d04020c0319020109031706040605060d0207050c06040b0a05030a1b0c0210170c0904110a020106080f060405060a11 73
    0x166102c0e1008442d810100b0001c282d83c0840c02985140d2894240f020b145240ca640d40c108840841480a001015809014103c0b01d008000301c402a58000500343d01c07000c100c0d00110b42e141c1c0c0d00740c5241c1c003030718a072042040e10424035a2003a071010016156141003031000c5a08032442c0011055011015621118034007103500ca41c0f0042240541400241d40e440c3c07804020442009680400c44086a150805c800c010992143c40907100803911540740c5400d442e0540041c020b071440750000c5501100014140501c0001c80d80185480c600ca0410307503002c10343c00000c0001d523004510a80015a50401c40b5000b882d10400045621a1a142c80011214007080d40601030541307501c84940442d040e0b02701001949080340004d01a203456150400c110019420700c40011040a05564104400421545101d540d01d4100720400d40c59200102c4d2034820100009028000621507580b460040c1c071030240707089901069891055420030010035150b00d880d101784c001007401891141010304144202459113 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 988844064 1250 988842814 988842853
    0x3020d1503050a0b010602030c0309060f0705060a020c0d11030a0c0c0e0f100506031006050f040b071208130507050108060a030b072309091518040f120302030f18 71
    0x1c500900c01802c402c08940303050f0341d0600060304a10150340c1700340300000741c00c0d00000032620100000d450041e15540d01c00d11072034180c003d4170ba004095020301010000344101c694090500c42c0905070442d07044220070744090f034001c103110510050a070000c00810b180c413806100c401030b1440c1309180420982c0e588180c543da001c441070304c0150721900c1c444144081110302c1311000010b072404440a901c1c50410112402141c2c00a210b0001481404982e1400c400c142c001503c5c000c1404070000fa80d039048514210000b15003606c0000b01044020307001c2800f081c1e158a80f002480d0f440401805680e003031000666a0900c001c118641c00114000c000c400070300b01310182c0d40210700f1502c0354038449500940c0a4562001c2d2000050b0646062007544000c3d612004419040b84425420071148000040821900c40d110a65144070b0341940003030104011003080701c004bc0134050005e4000f02969035004600341c0c4000e84017201f142102e034010030140c1c0c11851a640383c04440c907049074401c10f200d48003030846 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 988845314 1250 988844064 988844069
    0xb0d02090f0a05150108040b09070b0403081308010b0a090213091409120c0a06020c010b0a032009161b2a080d05030c0c15010b180d0309050103020d15 66
    0x70149010500041900a00500d500034880d450101204d48109000070400c0500620280c10110344201154602c2e00510000300a441d040050f29a40c3d0303201d0078000c050f5408440c00306502c031005c01c0001254038040c8a5054180d40082060900615010720718010390400b00f40c003d070444606200180300c0304c6c00d10540c03000c11003552012000d0b00c2c1c00a19a803c04900ea50074800b18001004102d46842c0c0208808408951080c40180c9590b0850540c90040040401450704502c0c0800048240724050744500742078404064223000c0002d0035001c2c45600f40081d5103503500408910980d0100340d00504000c0070320622417211584410b06900e0b542c0e4000d40d8010841c803040c03211911029140342d4804000041c00c0081c00400d00e04152000003021403100902090090202240218601c44180712880c42200201e00300b04241d6191500144030394050b802103805034000003892031041c20b0404030790b02440c0c2c060302e4190500d8a000010b401a600685080e90b6441d07440c51005402c2c0d03980c070880d101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 988846564 1250 988845314 988845331
    0x30f0317071e020f0303130f020d080c16080316030c2004060b0f04031b03060507021c1d04050703020c011b0f0801030b04030e18090c0f010e0a090b0d0209 68
    0x8002490b0004804401c0c21105100115000300480391a00e070000400c89170889217402d1240301d0000c00b070030100e41c9003401c514003d5000364a100b0510034040c43c00007825036a121315060f02ca50503006001c680301c00007030f8412445030350014003074400b0801d041140b1109545c041d04050080c40c6c00c0ea6600d502083c0c1c4000c141da82e1500c0f401c207440795403c0910506000d0800c00c50014580044105040b003d8003d40c40014000518a002803030251040b120020065500c618184503600308164040e4581d24039100100c20201c0507040c446045208284800e00030700f00842c03500714900403005110181100070a0002810f408101205641400b40b01c0c1302034001d6254a18072100e20000c50041014240070381140820118130014030100e07902d201113940083d0302d81030000c0180e00e00404144120440c02841c00910f25402c100107480d44d000c244180d02000480c0c0400700303880d03880010759000c0c5a2440c2d083d0421014901030240250980c06000b48020060040011405ca54002861104121182c60 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 988847814 1250 988846564 988846577
    0x30604060f0509032508071202010e1624020319030e0d030917030a0b0a0909050709022d1326010203071704260705070f0b04030f031707 60
    0x701902070034481c5075000f01c5428080e510340503555030f1325450b8144205000005843c0c5103251000c000b0a04101c174492540a8101483c044410002074024126031500d000d41c3c1c0218600804c400768a103040c402564001703041c2d0040240300203001419100b07014000001d42c40104010707003029101e002e080c000120b0550b401b0606071310006a080c02c01b070502d54402d050504040c55040000d00c0b402000b43c01000c588071315a04d076502c40158602030306103051465003141c1c88007804114401c0b1a00704280060290301121052075a0f01c2d2488200d2080204c840d00d260055a401c8001403107a038006040f0000545155080072000c14191020140b00d50055444078602c000c0e6910f035030483e000200f00c00000384000c40c110324060b0005411400c1180300015416040000202005220310140c145180c0c100c2c81e00749110003c80c2112a00c0d0f004140039651480707110400510607410003c010141e0b00d010500500b0245190759007418407404100441c2800f810b00c440c854400030715000140314a400342d4524 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 988848920 1106 988847814 988847831
    0x62114240c0f070c080114220f0b010b04060f050f0d0914120417030403020a0521010c030504060f02132d0e040210021516090503060406 60
    0x80c4200c04512070302071108001c03051081d9041d1a00030001c070120301f1801f10350354008545000501ca114949040080000901507900394420b2240703480301a4203903104442704c20240c120401c048400300c3d04000c8140e006a0b4000098003504042c0d203041c2500780c0d807440724483e50300341807901600ea120300c5007005524134110064084040581d00c0700b44a06076192110360161003240089580055464400540801101d00300d03580204068401882e000a001000074059500004d4440d0074402820b00c031030a0180c12180082907400062a181ca490a14110741c0b805107035404807881400080c2001c5038055608095032031607400d0301c4045000c8220006041d0b000d4418140f00090800d00095011074145041d01403442107646001c007030100c02007260341d000724080401c507070b05185010501a8044040c0030000d0000361805104135600c9030042483c00600b039404540b11690348030f08 = true := by decide +kernel

theorem cover : BRFrame.Cov 988669064 988848920 := by
  have h0 := BRFrame.cov_init 988669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 988669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 988669064 ≤ n) (h2 : n < 988848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
