-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3830
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:48:20.010461+00:00
-- url     : https://prove2.me/submissions/5c15a7d0-f434-4fed-94b4-46f347176326

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 688669064 ≤ n < 688848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 688670314 1250 688669064 688669073
    0xa0504091505040c0207060f090b0d09080918040c120519060b041401031b08030d020a031d030d05010f0602030418020f12040c09110d02030714040602010c020c030c0d030c 75
    0x40701509000e40280580d0002c2180030350f8500d0b5510504002030031801128030100e105943d0401a100d4000f202403800b1a000c3e000000392907402000e8402c50000c1007421070a60b106285100c10110000300703102d080c074003410b00584000c003903440401103190070400400081c8001c84c0d000a22904510000c1071035000781040d0004012080283ea0028034082c1c1701d1075800030001405049a20860341c1e0042e44103015150500d4816078440c000d00c030307070060168402c0602950080c0094031002e00c0c0c00a942848000d042101121180d9403411940001511040040d405c1c01103e000d0301d00320450349450b92600703d00030766a01c030383e20884c80c851105040214840c041c1d40c040b965004921401203071151a2003c000407250740c1954100d4803042c0c070b81d2001a190005000f03413206004403070b0205082401151301d41029500080c6406d082100310980d0000c40000302020b00061b28583d400010001d080c040c01910309408601c00620a90003071900b480590b58005c0711411096161070480841c4c0b420382352 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 688671564 1250 688670314 688670351
    0x1504051315061a0a08010303120902040c030b0f010e090711030c0319090801050f01030209090a0b090f01180f080a17070e0103240e150904050309090c0a050409 70
    0x8010080c031200024a18100c02a030400c8056468018559100704040e800f8000c051003201003003c0421100b000400100c0c0c010444d5001646c4040c4012071400c049600082c121034584020801017591079807525918140a00841c6c40c03c031007030914900e0007008000280c10420010f00441c20031418000d062402c0c0d400b84141c070701c1103a071481144d40b04c0c0c100c02c2840300b03421001682c240002d40c507080700180e014014050103024415440085110342d0840d000d100e00780c1e90040580055118041c0d100700040d62851120b841113070f0b00005844075041d810120350035141e0762008011035488000e40900414451600019000c1d4840008d613910300c03c0040903a0000a4010f082071100062801c000c0501d8004543e03002c0e01070241d0b0104200e0b620300c44a001240000d2000c414800303c0480700f40682c00c0355520f04c1d500480340112a0042134900c13800122202e10460b01151a50001b090a4400c1e09101c142c03d5002803a80b08414200030300224010528010752050341051600d0b0f07950031115594109 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 688672814 1250 688671564 688671601
    0x5061206011401170106080106030b0402090603070c030e06090a050402030a0b0315010806010614071205041a0c0f030c060c0d0b0a03060510090c0906030207020a120b0f010e150405 79
    0x2000d03a5095a550400311281405000c4080d020550300032007881030680150030141a1802d68407002096402e000080b80103020180364950004e030f080189800507943c601c050351190b4039903551403005080b2494010304000e06803101c43d020f0142844003501c83d58500704400140c60040c0c1d0f005850f6591200040d0240c05486185900b6001c1e032640d08204d904030303121150580e1507460880701d03284d0340e0705d0080310400030000c1c01c0038960700e0510615000404121300408444980d01c3c2c080e0400d030b101c00d0406040f001c140c1e2003680034000000c21800c808814001c100181c4141030145041c0700241c0260740c2c807140020710310311403e04005030301580001e0746d80c072400303e000001c0c15824500d912032a1640c01803009407441d4981d41c0d0070000c000703011410760140721050130403596007824180c40c00c0c20581c040d400100d0100da1080c0380c3c080104520726a85480003145000328800c02890820181c6c8a50280040e084201480e2003c420040751012040080e03860007002c0d82c001507107a403a204900700145244 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 688674064 1250 688672814 688672849
    0x1801020a171e0c0705010b0a1d130803010801060302030717030901051312030507020306060907120905010e011104050108070c1e150f0e01181505090307080a03061409040b04060506 79
    0x2c4090140114100d8041e00c0c3e4584544000c102480400b410040078240034400c43d000e806520304401c00d02481c24610741d421058138031a1f1070005115903507440b1642c00036000001300b60f41d590010015450104a00001404201c4c0700400c421400701960b030f180d116080246050100005034098000143e02d40d000013400c1e0080e8010704861546001003841d44120303806d920920030000030070717820b00e8100b01e920b004402c10340740d641c691007400e4040e5000e08400301d01601c45559800c1c40880300c1d030080c001c845400c420b203140180d40d1410040090a170000c040c00e56810000c040300c013100041c204520b17107540905400e020f082410302d50303d48104104010540d501c1c00c1070810404d003c0426294024100c183d2540b0002e108035103070000d5060482d100315601a091241b100f0144e40061b004d5440f06400008900640780b1301980b039202c0d034000d07034091500f0200281c0c3c1c908041220102803c0c000504400441d1300c1c003002d041540b00d01003440406003014080740c2d5130b0390228242d603840c0400c1d40c4082160 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 688675314 1250 688674064 688674121
    0x60103052502071404420314010c020313031e200405090f030d0e01061a0406080f150f03071e0302130b280e0406051801020a17 56
    0x407408002d495003418800c2c1e899180f003694403580a89400c0c0a40b5a4011070b940104e5000341030610a118440310186119142818040612000c0c0800d0950301010798052480c40c9504420841c0941c01c56107403007080703c1150000d11072302e2607a894840e060742c1142c0d00024189214003422459444000a80000030300d03005202c801d03014a030b040340500c00156201124108680d07a9200d11071600c03505225010281a001003200000314441584507450080c0d880d40006030721502d8520001240f518100107041d04030f4042810030900c0d41c09031550703900080004000200d41031801301040300d01d2051164910400508030b010105403002c005500050004022089001e084030107102c44040242c0026400f924070f1040c901d04803440e80c01254102540900310040c4424640d14840010031615400460040c51600005880140084550050b40907610010329400c00080480c040801030300e20005a900520007550101e800c0325900b484101070f410211815035410941c103001c6003101c254001200300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 688676564 1250 688675314 688675381
    0x40f030c03120219032a0311121807140108070f0e030712060e011109060a052115010c02151803070303020303040c0618060507020f4506010305 63
    0x50314100d181c100c400688042040340c070541240001064100c00c04001d90488a41000d10355100388e000303015030340c0141001c80c01e0402e1002c100d10308070401e4070300541422610b41c0048e021a0103101280040811040020004c00b11000107004e00c88014156003d004002d0300b559020b5003c0c003404c80440074002c0969092035140e80ca040700d152a00b15050303d200349411001c8444450500c0385111903889003a0030784c1050440d104100d0940d002540460802800780708061103942c0c0d030780e00e41c510407010010441043c40d0040c000e2130f1a024003c0c001d0704228522804402584421202101c0c0940141c002503550100c0c295400c1c0340e414040d400c0e5098858828000103043c0e0100145014a03c00c09482c052140d80e420200c0c2c0000540f050381c0744c10710740c110080001074013400c014000306102070700d0001284248030000d485c0d2040b416080c441c1a07103d00c58a540100036442d440e001502c1c0e0b105006140b181c03070300c0c47c2c07280300c10060607a0f0503d543ea0002c201c000e012a080324108072202850f0729990381 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 688677814 1250 688676564 688676587
    0xe1510031a09070206070f02190f0f060515100f0e09180303010803070614150402161b0f06020f0a020d030203091518040605010503070e190e091005040f030c031202 72
    0x850464640c400071f10007a60108400b407000c642080a0000e403169045425420b07101d410341c480c40160201d800d000560305d03410000300c10380610746c4101914854421044050b009002281c1c200d4080c1c481003040c1038510042d080d4201a80803802c04090b1001c0081da075951784464400d0081c0c00c002c0c4078a120100000440342070000044c1241031140c2002e10002d214003240584a01e41914600d800d407010392144011030406a0260400c104100f54002d080ca0441e201e0700031038284001c400c1c1e00c1584503902403100040c1505400010400d40c40240303c015020360803d0385402803c0e2000f841903d4941c3c1007000d03d8420820350346800d0300100441c01d0140e040c0803d0700e140d070191b10340703c840001010304d058180c58107102c1e0500310b42040e1115440c40d034844034100c4030b640903059084c0d80060001c0960301054121008270028018891f1940020f0500c42461443c02052085c0b40d01c6071800d00081000003110701c035009210303d6143c10070060b424001c0c83d00f640c11918840402c0090761001c80c8168444 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 688679064 1250 688677814 688677823
    0x10030e0c06270d021030020702010e03060c0912100c081605120c0c010f15091d1e2803110a030905060705070f080303010e1510031a090702 61
    0x2c6548401400600442400c1c4400e4402c1e4082c00f035032080358400c4001c0818001c20644001008181c1d000003241448043c210004046481513140c059001c9240d0045507080641c100a1640441c01003481d403401d075141440c503201c2e2030800d6006100d149288010000208801841e40c0c18040c1e0510048105004c000c2403448210b4070700b058914004000c0ca6194024401c654650b4003a96440d03c582c1d48200c0300c030507903520076041c2080c0d942d607408202c101c6c8030140c4030382003224030110401c0c4041803800d2805810b4802c0071801c0f0210002008440390001d00010b0649a0410701102d40f1800c81c04ca820070904000f500c07950940c1010244010030f4514440c0002e240401d88a80c40b065030102d0611340d0141d490581c000010045100b600c0c0500862800401400780307140319200b1210665181c0581c0646400b040d8045212a40080014056650b10354031441c3d001800c0840c02c00682581000a03050071011030030701c4249940c0310381d403140034201c0641082d00c1c410094102852803c002c0030003940d8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 688680314 1250 688679064 688679107
    0x4090207060e2b05090618030c0910060207091b11030d0e03070605075405010801080a0c2c0403091a070302150c130806010f050108010510030e0c06 65
    0x4800f4820240d101036001e0025200600000b4112074100100309464840c0c0d602e80c0d4030190781c94443c40c09441c00d25500c403005144a0794074144600c2101d0b280c80e501074607103602500a8000c032818980c502680328606c0031204003459080c5032105060100386040c504500c920b00f080318602d81049517030900400000000c0046038810300d2300b0003080d40d58080407148403186150100e5110094070b24840e004000819103d01501c0c2d045d805951580030041d0320840303400c0340031260301102800f50100215a00050681d0061125102510354000203a0303400e8120030b058040d4692900c100182d11696040d200303040c0b0b003010990301d41c80c51141003a05004d0488440c1e4411448000c0d942c09401c2c0140d1804020340d000d09901d50000c100d20100303038a41001550740108020034090052100c039903140d2280b02071030010812030300500141d50504806d8401b44a17650019410b00251138010000d42e12426461170305080c43d0714000440341002c110b400e00f000603520311240e100002140d0000c11b040c000030380d0040d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 688681564 1250 688680314 688680373
    0xf060e0408070b010b09012727180203030f0c0705100e1302180f0d21020727020a09030203010c0504060e12120706020409050c030105180c04090207060e 67
    0x8081c0c1e45c40b407401e613851240403c40ba0009111840d1009880900500c1900da680128a45528651554a1180d960300c031190342c002d40070408050200000c03000e1060b48503e103a2409412001c0c0800d1300800c0d62885114644031001c20005800d100960342480300e41c000d40f800a0481d8910f92010700300030240d00100c440b2500c075489507004503c003c9404c0c42265204070b0340145c03200c54082984204200600c2c09a451601b02d440d60125000140601400111142820011204a5144501c000d16022942e000b00e07800c0c040300c3d20000070804005102062040d4a44009680c5000e107820496030300d071240e84025015800c02d01f400c085a60024080d10070b9800550329a113010b5886e104000c01d4500c55a5031859503080386248107801d0722034034000c22005000b100c0c09485e0036940c081c02801c45508a407200c480758401301c01800103261112100c9500c1150310300701e0b002810150f040720040d01c902d1060017041c030b600003000c204000e210f0b04103840c0241c0380d406560346550551003280a0b0700c0035262000303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 688682814 1250 688681564 688681583
    0x60a0207030215071b03020a140114010815010e0403120c030209130216082107031b0518060c0a060204170115030c05060d020c030316020c040e030306040f060e040807 73
    0x1c40c0c0e1070f10030342d03440c0b065500d540d07040c8040000b0804500c5a41e4001030030b4086018880041022a2041c03030b4000c581307102600001110301c60940c00f01e607900e1040e008902581c0011100e2580c505040003514150b0b210000d43c030080f912540340540d01640d0000c00742c1030581c00c1c9a020581a50584d01610302c02500780e0384002a020308800d040c08a20505041d80038048010304580003080c48003010b080c04a4074a003a064501d03404441c40361590000b216280002600d44080c0441c241034209098205034050070564140b0b80020070b510320100d1001076442c016040481c2140b1000010401e0411080d001402156541e0b00c0b01c0f010842900d07049040a07a541c00c144e101c0d124400030040e01e40c1201c0c1c200c00030244160605040100c81d500c12034210341503030f809004040301007200340020750140c3c46003400014603d0340e900020341000000b406c4107201c1c0349000340070408418088116a071211003120300240318000768202d4801030802d60403032003032483c040d4104401c0040c0b050041080502890041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 688684064 1250 688682814 688682833
    0x905010902090612030316020f0f0d030b09150d03030b040207050f0625030b040209130c091403030a08040515013c180e1218030615010503100503060a02070302 70
    0x182c00114072402400c1350780200300041318403070840c81d54000e819562050760900350b85506028a48034a00e4246401034004541100585415104112004100395403a900381d00c0c0071201c2d0b0413803020212807180107a0401040c1f0041520030350001c2c00c0c00f030004000315168180ca0410350382d40c0302e100e0b8040e02c007849108049448405081140ea18200036000c40d001c00440e0008224044e24080c1d0040d6046902484400c2c0c556461074602208244000d000080c14114120010005046a4400081c2100072070080ca46510007004803090301c035075401c26a03d10344881c07a0151600a010b001c031a00c50005c2d000100b01d19040411516090041e001ea084080040e407218038145101c2e404803100000140f08100724148206900641012041e140003507603001f540d10704c90600451402125a021000075416841000c0000c00c00700382005030010211843c00702e140c81c104107410a4520306000c40400041ca280c0039195103103015140103015911181014040540a5001000c04030003500445560 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 688685314 1250 688684064 688684069
    0x60a1205011d0a14271014070c03120b060d0903051207020313031101210c02100501050607230f0307060e0d0e090c04080115090c080f0a0507110109050109020906 71
    0x1d140074402d4101040c1026101d14645d22140214121035000030844105030614035401031142082140884002150380d9910424107206031000502660611940c003a10b200400c0d80051006054920140e00041484940d8006100d41c000c0e03080c140c040c82d00b4a021481050380c004054081411040d0055000361030b0401c0aa85a0180f8032010032550350781c20b01000801c0e20780720941e03070024060404c610109002e07901c0c803401c4020642c41401240d00d5444010129a040141800144150400304400d5052000240242c4140140500201605141d06920209010514125100200031103078400048505541c40b82c000c0a0240c4103985000003241180c00082024840d01c1b4450f0340300410b910305102001002c0300054826440d244003030001055900c000d02c44c28a161740c0503902d8802c0503190468420a5a207514650800c10503010140718150040784d108540021160b000495195902e26045415600c0d00403046e40f29800e014441060100c107622408125000707841032800d13951200107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 688686564 1250 688685314 688685321
    0xa0c1d060d08120a0e060702011a0d05100b03160602010b01081509070804030216030b0a1b0503040f08070f110f060a020d0810171c0905010509060a1205011d0a 70
    0x2c0c154250070005034960484420307140b80d0041d0b80040004900140d07503032803803602c0740403192000541c0d5550480b040d0400c10303101202114034203d4a240e9010020b03500c2ca48c8802444580c0000c60f42c442e203540182c1c4c0d609101c243e5903c464640306802c80ca0355008004d018012540501e40802c80010105004958032070790000341c44006044c0c0d410640f1580c0d0110b9050000500c00c1c0d04501481c3d044204000584131160025409007a042055040402e00c0004840c41086100c02e0344c940344114002d1603800c581580e5020303400043c2810391603070608101640380314409000340204c0e0720f4089c040c20407040c1044890721120542380c86901c22074510901c8110f11075418220096400300d442052114402c120507a400300c3d9105140d41c0550740ca80c4820703c3c001c501204205182c110071102034144141882104400c43e030f07850800b515038984070018000344580c0c44580d0040c0360014100d240b4034001c54a019243c040400200700669490880c180718800248100c0c00e00003844010030720f024150301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 688687814 1250 688686564 688686589
    0x3010c17090c010509190315020a14090913050f16080f01050103111c0204090b061002011503080d20090a09020f04090b1809060402010338030a0c1d06 66
    0x4c503201e00d401101e0040001c113048a02403403d6007030307810300080001031311000c214002d00400031000d61565104803001c3c1040040c0d84201c03180b4101404001250341d20442c00382d402443d000e80c41903041c0f44a041c02c41c14009282d1080110b07124902e420b1000342c440307031010000c4070100000e030340300d085136415520f00365042840054040c80c8502481d020138608440c0b030b000c20b0629010403a1050840d030703000c01c085e02c200036020b035040440c078006c00000307090030301318480e10f1202c41c802007010b20003551038482681198040607110150102e01c20350b0383e803100c2e4050310820f20084c2410212408001020200794811200f90780560303a26400010710035407600984400c010304401103401d160600038000d0091800301200c5600107000f0091b1016114100e20140c0141010400303131040c1e2500d400094240e914200301c40950480c02030b260f07244c00b925a8040e1a40340041101260b071a12034100181c0740421618000d0050040d88100040c001c0e40c2641c044610684c2caa540762441d41c0e134008109a0305c031000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 688689064 1250 688687814 688687817
    0x22060905060f070c0c0b0a03090b0c0301030308010f030308042d05160b04060c1403120a0e19020315041b0e0907150215130807320c091503010c17090c01 67
    0x60511201c03c0c02001f90500c50114a800240b50801c1d860300700007008191080503071500e0010040c0141076200400034007402c1e04012144400c1d1840d03034020190940200060003190020340c0c9449441c0380420713402c031040841d021501a00c3c134581443e80c1c032840b040e6401000445003220014422a051003a03d08841040d118031004031029140d121402c1848520b4031100c1c0000c01c80d85982000c5807040d5800303400c60300000130385e1942c201c2c0010b00d41902d50000e54440d6918154190041c0e170000b6402100664080d0a42d40c130361503d150010002003030041040c0e6000c03008002284240251908a1148000d0030072034201598519500219041d001d0b0200c005030040048400f1038941a2110764005032a464002413208290315051000e41007020304503083e9040305501c0d5000c402d4201c0012a14100c5e00ba080b080a10b044841c1391b40300e0380d10b00c1441c016410580080e840ca610a0070b4601110b802800a014070120807100030041e0b00c4100c0340104584008012488a9500041c941d42e0888103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 688690314 1250 688689064 688689083
    0x311091807050105030a110406120e03091005130f0603142409090c03120429090d05010603081305090708070f05090d0c2405090922060905060f070c 65
    0x240340044130303160b00040580200c5078413222014150380c1c00200400080130190750740c0c40f01120881e028001c0e10495260b140807540140700c803918540e60b43b95402200061402c14954500e80401440c10010f61640001500000140001051078041e000b00704203d070008000403da41c0d030f612500924503020802d98150070030003550400542000f950032900075036504203e441c103441c9200000c2c80c10040309000c0401090205080050b40c0303084220904110381d0000056151030300188002203801800031840c801c010740100700e414800700798017290141d034110401c41d40d1b400054020704003581180c85230a010307c1d184000142c1c000d02c224017580c0034104a82d50f0502048049404503480d42205000c0c90313210981440d400001090b50102900800440b1a50b11060410058000f052001c0d00c07402e009000e410003614180380d41f401c1903140d00c40055003220054660b080c070003006010740d06000401d1689000d40034030900400060340c1d48a442c1c070311180d00f850b559495007128007000b1741c1e1009115007030703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 688691564 1250 688690314 688690319
    0x50a0f03171b07060c0308010b0a0c02100e040204120219060e014b020115030f0305040e090309031902060307030911040614030f032104060b06040311091807 69
    0x91400c020020320400b510312014080907401554204501d9601034000308115152010401d0380052403140181b003e000d181d0f00b02016600302908d0a03058690003480303204141100303002c0034014800d147c0d40e108040c00840d190380d104d10000c0c0354502680403d0f40704d00300c0c80901c04800d2103050802c00c160f4980b651003001c1307518000c005544d180000d550361050141d060010040d01d80c00001d90850424812200c45c0811100c80c0d4281c2d140c0e81c1d002e0b039030401c40e41030040c0e00481c2c5920758241000c4036401381d07603031111008034281100c81d80690f410030500040e0483c01d000c602a800800b5142c81d600482c26521203040c218503502d076910007144029003147c0140f0010b02064000e910a05c01c46001c1c3c2040d01407103548400060844880e5000803211207141c0e0307100d0156040c10400c0000d00078101e40110306e80341e9004c1c0c0e542401d000c2c819200700d4440c1d180000800704042c0c1d40185401140250075143c072141c591915800440b08400c025000d5a070050004405a070301d0300b0501e024161103c0540440c60 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 688692814 1250 688691564 688691603
    0xb040e0d080c0d02070807020406170309060f040e0705040e011215050a09170d140403200309060d020901031a1e0103091e0201020616300e0601050a0f03 67
    0xc8001c0c400c40402c44140305501416159000400c0c00c1c0d440784e03c090f540e48140f84100400c588190300b11031036061a8081c40c4104050010403501d003514200d03905500c40800680c5140e40d403117680c100d04003001f034040070b1040003034016010340b0a403040320000d5541a80c85501c0c042c0e5584011001a0522120b00045541006198015504800f1207100030440e8040d58440c0954043d5060304840302e40c200040c08102c0d0300441c842c8509445619480d04054207003a00c0003030850076002282c080e8891000800d10f5403000c10021a052180c02074895a1140001030005001303400080c21603020a0410a058081008005040303c807454020a00382c220301040e680340014140303042d045814550358100a0022802c120074041403000b40403981c0c500c0d8292880024100314001d0002c0d006d0071200d403000350f036143c3c004200b20720185002050070075201746100c441c0784000c4000c05030b00c541407402100d8484102c020503064141c801c02c1d56003624103590340541008038032061002800c9040042606a82c40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 688694064 1250 688692814 688692827
    0x10061212030b090a0c0c0b0103141209030a2d06050a0606020c030d0807030f050405010203150616020d0f0b040308010501091e0b030c0f0a050910050c0d0e1216090b040e0d 75
    0x1295291846c0d00e550b0319035806030642c80c02c0c1c10940300c203208139240d071102c513000300804050842000b68141c2804400400309a5800e041e400c0144403100c0c4c06130350404441034030402c810700c103840c0c01840100501c5e13003003400042c241640c94803e840c0c200040440c0c00c60000402e0041100c01500034001c01c1d0351440c0480e03c01c070000e403216080507220080d070381044e04140215030066009a0005a0f282480800703805d2420540701400d000d503500340210302c0814000400a00c07030035010741319002d0b5000c2c64a0800a001d00c1c081c070041004030741c2401d0006140d409015581030f40d4082c1c1310040215242c00c419012a042e09480c1001d040c204001801580c1d45400a19041848280201d080a0500d104d19503070780c00078048a8009240490004000c1c9014805164098641d007425880d00304a00304e42a2541242003800302070142c11020980c858407240d48611100d10240701340c8012900750414403081c4c40075440388078891424010650343d580f40c1031113403001e4000118001d00022000c1101601c52 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 688695314 1250 688694064 688694081
    0x51305030316180303120608010606050301090207260307030b030723031204080313050108060603151302161103030f03061012020a080105041a06090f0310061212030b090a 75
    0x40203d804002c0041256840512010354030a4940c82803182418440c5421150558081541607042c05d03010014150440105c0b810b40d650100b0140c0d89004c182001c10356041400c0a80d0681d00a50342041042141d02001d10700801041d5020300c00c0000c40e00416a072040c4a001c1c2c120700e140f030540841e401c1144160351042c02d84018080e2046200310b0380d40c00e06582c00c1503009215981000588040800302100309601400003420091201d00301040070038503070b00008020b0700c0b41c2c02c3d881c2000712a0341d4440c0442c107005140034000355500c0740d50541c840c41c100070000e401c80e40c10b8890349858600d85008030641d8004ca56100c0380703509603520340040200a217444c802e140103101b401c80e000e420303400d1580001d05008856880e403030f40302d51400b4203000c00c881490380c407290002006403144070240e0320517007211507000781102c9082c1c0c035204a8000906200c40f43d0300c0e0320511490902d0014145420f0750142c55520700500740460300450158003a010b45001c0950326a208181c0c02c0011081402035111b81070b07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 688696564 1250 688695314 688695317
    0x21020309041a131b0201020a090504020702040902040603050d022a0906010909051609080a150506120a11030d0c0c0b03100305060f100b04051c0231051305030316 71
    0x40c290304850220300c0c030152043e0305868943c1c640d001d01104292114192210300b480f44002c501c2e2040c2090003c0c80020b130381c000c16200d103400240817002d660f03035504400c0c1055002001001183c0c0e4034500a55282c0d2070000310300143c01150040746401c0c2012841f02c0d044404d00700a001100d41d01c0c0100540040d008104a041c462004d03004942081d0310b2003807621407403412600840c00c803140d110203000745849504c071444540c0704841c0180003902401c09212071171060080461a51a0b4400180110030b500003445028800c030100d61041c003c8417216108200c034254181d40c822180a1011210b14029001c0502031565407030b000c01004504000440d8062510346503644615107075034940781082c000380c43d6180010458000d029081c4018501000100b0008925610b06403600c0c0200c1c003001428090a651a5400e8012006548406034800089410044d22418500401d02c0f60007503070383c1030408298000c0c0307004c0004080c48480440c40c205141c00c200210b003564ac4180d035050203218844001030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 688697814 1250 688696564 688696601
    0xe030c220204150e0f0603090a0b1005060703170c030906070e030102130303080612060106021e0106090e0d27121407062102040f06140408192102030904 67
    0x12900e02c200c03e1095024102d540300704550309410108005a2421804c90303101d10403c01c240310840382c000840b1392449030700c80c109044941e110200c0340b42103151588102e0300400c0000d0381d8010185e120324054407000f6002c1c42c5800705d48030809160000d0104480800740340d8055004900501d000b6000521155030060006d80f40a801d07a21405920a241d8803c8010078494400d1100a2800300140e051000e95503000742125850517034020350300d40004404810580780703048101d1441c0420742000c400350107034940a0144c00401000f40b035070f440c03510116070001805800c80c0d2030304006803031070031001c1141403030072a842d41c2c200380c25403a03070b400c0c1140201c3e05a503540c44a200d03030400a0013810b00a040c2902c4402c801c0e081050388402c1c0680460542c0340040c8108810311100a070521488283d5655280c410814407020410917042e110760b4001050600c07905008401c4a80c0469100e40e20038170035640000b4403031000d46255032907607420400d00090303002441023031030b03c2c05d05600c003144003c10700c0070f0030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 688699064 1250 688697814 688697819
    0x70e010e0709441b06180f0402040608190603031e1704031e050301081b030f060a05010f0501030c09090e0703081207020d0f09091e02190e030c220204 66
    0x20ba201841e0b908000c01d00500c0100340f1400c402c1c02100c00102d20000704d164641424000100300d8804e003020840075202c459801c040700e0b2207408014030300c0180648119610742d2111006171403480200d0744050b401c40700001d20410300106000744070403207138992252505110400410340c40c0702c41e502d03010700412041941c0305080504860710140254020b0700d50040801002c6540c114007070368040e4802c103000c010401000140c1002411400c9443c580c11680d445210207800a0700f0001c201041d031a40744a001e0501c0701c85000c135804103040f03d203d41129070080c0c0c2e82c1d00064007130387c1c0700384040e0021441140040100c01c0c059008110030b00d1000301652502504d07562030f681c0680008819890f01c03805181009001c503010811a1413005450070a02c40145a642c8014a00041e034000d0040c0781ea100c1758803503100490840046650060800159201d6642001801c005d07954102d01b40c0001e00d000c01c41c2c401c1400c000c00c804407074032005854040d000541040d21a5030040c621019054180e080100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 688700314 1250 688699064 688699139
    0x6150301060e150a0c0302010c1b0609081201090605010e0a1d090319030f050c0403210507140c0108071805040e121605010f050609131a0108070e010e0709 68
    0x40070400740c1c9441d0130410705c2250a009003100c511400060500c04410341200c0003407130003d0519070403548290045080c91140c6480c2e41e2501441d8462940502c44200100c0c503200303150040350541c0d00030780e00d15801100d95400c00800028501c503010b0308942e0007100c2c40c4a9030010000d1540501014200c0b4079006071004c01d50f01520100c2030104c0003039980d000c0c81403140107600616401400514100d402c0c10b0554480c0c08400a0041d1000306100100901c02c0e1250b00420a50700d25135040f08000446044508030542c643c44503c4000740000d8000c07000494440c0203000342c400510031100844081414030007840020648200300381080d102e007400039500344103600000c000b0351804400042006c01540b03041030a44006c084c0554000703081100700070954136108401e550201500d940116421917a01301501c40808403003524210604031000132941180000d40d41c003c8601c00003041c030781681c0c0c40b5886081c0b0700e400c0c3d40c17010001e810040d003006a0043d0352260032800c01903111600e00d80621110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 688701564 1250 688700314 688700317
    0xf11030303190510030503040608130c061d03010e120a0504230a08010c08040f110a17070806040f1b0b0304050703020a080c090c0c013206150301060e15 67
    0x1940400070711002c0c20304207125040d01907113800c0107500030304c10642419076680507224002e5008100800c020300002920780c041052405030b10706e4020380c5e031031000394036181d0040c00c0d04190710300c211601d060035450000d241414800c0b80c0d0400c0c01407001d44214400340f000c0340720300d600009a00003000402d2001044000c002c01950100f031311000007158006400e9000d100517500743d40c0c402581d40e45084030f201c00c0707280c0014a21b50710543c001ca451420007024038000c0b00a0401003081d40e00604092030110354450f04907071103840f000d09003003141c224640c0e854a65a96a90071640103013580d101003000383c002541d5052200b1466003040001484c541c583c00c1c012031680040b80c05440036031240341c0400550404071400e802510035013014004540c20302002c47d0782c2410240c407640c0c3d20b890000d045003c1400a50142c81041c22014141c41c0c801c0c40c80d08007001e00d01081c1114145c0741c1c15280400c025180c0031305880045190701d8446c07800c42c1c0ca0b20906842b0031300c02240c50307500443c40f5510b40090301c240e4030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 688702814 1250 688701564 688701571
    0x603020901170f070f020a0b070c030909050f0f16050708070204181539020708031b0c0a06081305070b0d021e0301120f11090f0403030b03010c0c0f11030303 69
    0x42200f4024500f6040044c9102402e13202601590400307610b1501140302c17100c04645c0400e0342e05055190040c00c0c581210070017455403102051a1505051001888907203080c00d01a2401030f800143d95128141c00c001e440b02962001000700e00c1c10881000014207a01c09000401e000070000110080e051222034218508400111000e40d0035001c115401022485440700308074240c50140740c54600710300b014006600350000020300001420000a81520800688000c1c11509090343d0725850038600c4202c40070300b1040c100c04207010380c907a0785025080c01803800c1c0031524036590340d407420b80b240c9030a28600c1009840584041c0942d440100d45611302c00f00900000340c81100050390303440c02c00c007600510300200c110300d124004108010401c0102040d124405260009407014090980749400911404103120503034102c0320002c2044090310004405034815400f98405011b10400300b01018200d8143c420f100000c591443d80505c00300d81d07085c2f000c2c1b86061198141180142e04d003800689560401c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 688704064 1250 688702814 688702831
    0x21203120405060a06060806061c060b090310050c03180c09180c01080708190612030905030f030406083606011e050901031407031202030702100507020a060302090117 73
    0x350140000c10608102940d48900031101c00c0090600f41362005060400243c6003602c80c40d004603070000421681142c0d41040004410304110f01c5070b40f1200b100a03030f001448072070711900844403a406002e00c05c0c01494800c41d26160702a195a03202c0b05110034549140401200a03c2588103420440d00c0d02206180241d50642d200d8102c03110b1640d102e4a4001c820100d0743c10040f0101c2840040c6812804054000c511403060101c8200f070711410200500090b4004104500070640080a040e00601850259030f016800d5690f0841e0000f40d0075981d01c036074805c1c21700103210a000100940c407094190342400901c903a0b8001088074000300703c851141a40380f18240d079005100100140c4e5288529050a4a50035014003d03052030310000961243c2c05201c00707010300025405890014009101308806103078000c051200380c9001e01d000a41d60341000b00c040380a030800c500030322440c0307000c1d100b5075851690090003045400c0c14102c00301c019421151815040c400b080c0b0f41b0080d040d00b182e030700c1b500c6103440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 688705314 1250 688704064 688704097
    0x80304030b06100804020907050c1204080609070f05040902060c0a030e0310140c03070c0f0308011a072609130f050a09050712020a0b0408010b0916020a030c021203 72
    0x450406044086001c0d120501c41d1540c84890b00c003d07a04400900e030f00030f0b011610318943d5900e06030203540740d109005074034045000e1410f0880f885403100004d04260346070ba0703042392816a00d044603d550388841380104501d8511440c410082c51601c1e800046010784042d10310340c2484e6120480038580710103018110046150903174552000d0a0030060f111300c0000340041844413140c2d039503c1070700d2070b400a4980360a04000000142c0c203c1c0c015400440020750251305041e40c500075044c0144529000c3c05403050b107131030030786000c18a10040c0081d0b406182e0000441c80120640099592000b101804144080ca00503c004d03003155840c07504119000d003d000c408904220a6a0400308941c2c0092a00d4400c51030b0041b080040b42d40080d101003910300f0748031210703c503a6840c000142901c1d96030388120a500c0c0000381c041900c0406420079840c454069500c4092920b5009008040032603400b4100700503400009841d0200744124000401d0030b0020b00304500181500807600c0c1141c1c010a62110842d41 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 688706564 1250 688705314 688705319
    0x7020109022803030c06060b04030b091b0f10030f050a09050624090406090b04031119050303160c050d050901300207050f0109060b101103030a0207031404080304 71
    0x20315142d0281c480b2101d5981c894541c24101c48480402000d02003e01002481d0141c3d808010f130541c0610b01a00340b00e00c0068499a4900d094514040120323079950302c41c0034107a00103420981c07044031070f03041c500014101401c40b02c1005c14000c9503e20003040a04058440c1c12141428059110303039070146282c420041801e40c0709003001e030310380070007e8004601545030340c400e1a5600c103c0b91103903851040440380300d14a0307122400c148001d440070714000b404000e403140c140410543c0010000285604500c00d40703080c017202000883d4104202d642c0a001ea420800000b0b0301b401150b107040d881480315041150740c0625507181e4901d00510440c425000c200c001400d02035940c2c003c8592440304454520400d142000c06d00941941710300392900b02201d075004142582005000e02c00e038940b5020001c0204208031107410014050000212240c0c060301c804101c140b0502c1c82074110054000c0c00390021442c0d03454a2003140c00a6000c0d00050b810800c035200b00701401c540b0140200010a4101c0066480d02d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 688707814 1250 688706564 688706569
    0x61d0406021216030c1b06020c030f0414090f06130f1805011505031f0b0f04050f06011209020307030b1b070503040501020c0628030e2a090403021c090e0702010902 72
    0x5000180320380a01c00341140000d0700201356040090380c1e47e4840c0b4003607226140a603409145004851b11540001004103000c1914000e40b9092040c980d4110f5050105486000240418200658007103410102001c0e20346c510444540002521020307200340007401c584458400ca035282501c0d0001c0307880d40d445288910705c1d0100b804034000030300000ca000c1c01c14103143d60840c205058410048801094580c07400d8071913907480d104101e058800c003800c244110320780403500001c1c8607001c85d001804140e000c0d001111804c2a8404c05150b10b40c003134001d11030a4216110003c5603000103019440d404900410480c40040d44006003000c1c0d031250300219255424500064103200c1e00448840c025407003800303015440c1301405506404a220011800508182104210060700c200303001403040e44076000480c502510841c2c100040550141c0c824039408454401300040f0460640c1d0150041c0e1200e07d5018100510045034a0007030070f60306042c0c0c109540c0d20212220a0421507423800940d654188203000d50 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 688709064 1250 688707814 688707821
    0x15060c150f06011b0303090804210c06051c0905030c1207061107120e011416060b09060303032202090a0615021f0e0f012409061d040602121603 63
    0x4039013420310040064801d585002500401203026041588900c000010302410790308032005041c4181c4215040d6000510b019002c56051000721401c5041250016047d031180c02542d52803400d86181c98040005036a205010f00025001a00c00d0b010030420180814810001030124074210281c4540318071a5003401c5080302c0c3c102d9900800d0741000c010640c0010f9001c4445049804e60b8113241e00000443d400480302d2001c49482d5a026480001d4803000341041c03040c0403421303244500c606014040241c0c0501c4014030301522100c3d0140d1091003c25115000c58080e01c094a84010985451112940028054010a03100d815006a6030b070b8042c001c010001500c038030609080e000500d08507501040d0f81c545901161101c0510650355010703280b202e0300c244800900d03c042c040c02804260300e840f0030b030030b030040c054400815039036103560b0001118138940c01031100321100d002d0034040c0c0d038140c143c00901420f4000c0040752100d0342003010030445c00005800314020900c00c105099002070300d813005400c5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 688710314 1250 688709064 688709071
    0x3e061302060a1d130509010b0a14040b0105160c06030513030c0b100b0c0610050a0602030f090a0302030105091c2d1e050304050709020903030315060c150f 68
    0x841091180850250716a40111805140c1d940b4214a4560180868001d00700c0c600d20000c0c0d01c03040380380b42c4c429400382d1500a030740211019402000300c1e072420b0040003100b200d02d210f29160784000da0203641492a00303501800c45040e040c1005894440c00c60680c840c0342d10741c60f401300c4041000b071034107108096140c0302d51980440960000c4190102a4802608450440100400e11549000000c4081c0840d0758454000e14184014503203030b03500392502d00e4850004071a40c540c6541b44260004651400c0803d400455000d0340256281003020301c0d000d46107611002166802440b0b0000010058500b440703814800c00c0094080d0143c13078240060b051007090083c00d503100304200700c080d0307034000042d002400000f0403000070b041c81a100b0b00c40050326400c1d20400c184001028620000c00d03107a0300310000394400c61203142692501c548440c403030000c0380120030b41c09425501c10710004442da40001c4000784281d000078103490900c40b6071202285490b140510502c1c2030344950381030100702c0c0250142c0640 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 688711564 1250 688710314 688710331
    0x7050402030601050706110f07062013091a060a081e061c1707051605010215010605031503060a1a1813060b0d030503090d02010e0c013e06 61
    0x1442c107014000030514080c00b1009810a9134403002c0e0007078210706108941c0080c40c444a030030f032100a02d040540052584400d2410744419100c1c005130a407411100b2551008541e45441e40c600c1d00340f5074003000400f404480d264480d80501000070b455a41c120183c4030308021940e41042902e407480d4880441a6020030300c41000d407014051003400e60b140320b80e083c4484c0c03079014104100201400d0400d45124030745290f42d201200014180140000420251550185a500c00000c180e03a10012a03541e8001e120240c03c80441e240180308207840b0300c00035600b00394440c580b00c405c041800c00090410005803900c5010b16620403c43d080c10440200218106004840c250408041c5407504a42c1d100010184c001116410320720700308001e119031008111401c060085c070445400da14006e0520350041c0e416410324420030703190141452050064840456001018001545c141001950001d004c0d0515035650100d8401807081481c8100c0e112120041d40f2070548a8024100303281403d114010300781c0f00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 688712814 1250 688711564 688711567
    0x3151f0302011d0102240402011103071e1b060201060f06030b28030f030509040e0a0f140307060203090a1214040e100806090c01080108010b01091a040b04030f0507050402 75
    0x800760381c000800880950641910078030411028004070b041c2101c01d1244464100b50f071408003c042011019184294800c0e260003100300301140380c556030382c0914a801015041a010425002d1619442c0401818450903070b042c0f001c205131100d0713440103100d13402c17110041c0e568007000c0225904042c14000200300905042140c180c0c944041009101e0440e01c4050713070070008840081c130305000c480d048001c40d00684035406607091031400800c1c41d444204407a11650030f0042d014206180496203804695104280751980c90150f0385035446030f801051200a40e020500603000462070500055101e0501540503040c807400a00d014005c0e64058440d40d41041210300c1d10811500350f8900f10350035600c00102065240d6605461602d84000b02e800500b5607020345820f01c8081000080c4d96006400c0907203c10500340e8a882226080341c6c0082c00c07090000720704941c02c00443d208540420855003011441c20700d82074480f008010198030580c0304440e240e1542d0b05a000748217041c0490400b50004a5080d07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 688714064 1250 688712814 688712819
    0x1110408030403122a0c1a07020d0303180606030c0e1e04060f09060c030f0209060a051b01051e010902130b2803200c0d080a06030203151f 61
    0x1540d680520f010003401a810300d4003280c04140661081c130151203000c07032081c1d10141481d109400412100d0000c9a40311030213040400d14846090040c4441038200f1400b03030030503d082c0c0800840c900071990903410705130f03515450202620311445881e02c86002c1c3c000401c20500d14a0803032400320b810ba00c02c01c1c441c0e41c56818030003480314501e110100e1080c0541500501d0322a400c060005083e2030082d0702e8080e182c55070341010400590000c1c038080140d610100704044071030043c20141e02c285401d40b0752202c0c042154907040c074004d00146c15007880c01751090340c6540540d03a8603402c4820540d102071180d2605000040350900800e50f050140001c0c01d015030600c0b00c44850030031a0b50541c001c15409007004079181c00d588015810b51480010000714041542c000c0c40d10140c014041100d0314003121840c00d03041e100d0f580c9440c0c210780d082200798000300000340d0f4101d8201c5800301d029060a115a888690010141e9010040c950303108403030b0040f194140c00d00b410303d295603202c400c99546090783c50400c02c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 688715314 1250 688714064 688714079
    0x1d01090201020d080403110337050a03151806080d0203040f06082d071106010b070f08040312030209041b0207060807120e07090b0604230a090e010e011104 68
    0x20141c3c207803000c1c20500a25103032440e054031070a4101105200310b10000c5034984480c4400f2080f4003645040040c203460143c02c0c40a15803403101449050382c0421001c00540c82c0c03052003944a800300e80781c03122300d0140640d10340e2030f0b119100c08400004200c1d41c0d19620140041307241403108000f03140c1c0c58002145018174003c10007030001c0280c030030700381440384007800100d0445424100c0f08080c103001c0306018002c4042c0300c00100504068400c0c80014a056041007600107001501c18103a4092100443c01c2c1071050740c400341d0031481c661046490050a0100200045000d2036865181400da1005612084d00d04240000c0b03030601c03504001c0320540d8400404a060300803c1900c2681c0580c5000c00d41076484039001ea03184010300c9544e81009281ca0707680110701d24049142c0054420380703041400508403410400c4580e0066024400703240030307c0041c10483c416480316590502a0250081c035459a640b01c3c801c040baa41503800c0e01190b5101c0000000b0800207218080b01c044e6110412810a0f003400d28 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 688716564 1250 688715314 688715323
    0x306060f0e01031707140604030206090d110c0d0303060b040b09132903031308031201140a21240c030216060203061801060c03020c06031306091a0a1d0109020102 71
    0x4500c1e10004c40050104248100302458075080c04a038011181c090a0034039000b9075404084600c20824041d40b00d6921286200300b41d044600c0d400217008101c02c001d660100123156036000ca04409259681d080083c1a1640402510090182d5842551200c003c002800b8214200c004441c1c1840d180c0415068011000004076448026800d0b425120207240404030b461031013034914003400d60a4021000540d00c200100810300342105034a40d4101d030b43e840088865126050190607444540c01505120030f611090802c5154415002e1084114005896041088041041c481c0c0145030702e41e180810110107000d0840c0c0c005140c0b50031031801e00b80145464844070145802811680c00001142003a620380302c08003c000070034070100a40d946c2d900c901800680440758101c01500840c001c1140034600b00040e684680d450481421f502a070311781e107030702c01492401c0c2c080755400c180c60755a4210308184103115201d06100ca0001429610110341d81841000d010304030006a810070394240300503640400d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 688717814 1250 688716564 688716593
    0xc090103030318020a0b0705100b0d02060a0c0b07050406180b03010501120603062307110a0b09190302010b0117040c030f0c03290627130501060306060f0e0103 70
    0x58001a0300b461865848103c1010420203035222100c0c00c0042036100b2880000d0070f03002d10a00803101c0711f00c0c5417440304007902c0c44c40309102c0d40503c0c031403003030340c0541451402810781e072615107031400413007146955400c01400c0588400e40040e07004101031010030f801030001d03000601d0520b09020241d141020151282c030050050604200c0740130b04480740220150032007000395a00c104180315a1000d80081c00b015912094041200089800031504c528002d40b1800904840300c0041e141d455942d4071581b410800c003428055a03845200b000080b81e04140c090b00d00030300c0c40ba500200360501c0c1000010001e203003140e0342c071078071503440401d001c0052241c484186c101ca5004400e54a40562820210092043c0f170388098010b14242c1880ca07140001000c24043d28500b180d0241816115842032000b50400c0c8100c02e980c2c14103c0e990104122036000f00b4943c00700401148082e088410340e03c45003500e0741584200c4d000c83d00c4500c10320484c0c039a98142d8002c3c0000000480f803542c034585540104407082c0c3d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 688719064 1250 688717814 688717817
    0xc12050f190603020306090a021c0b0601050901050d1802120106270219030204030219212108090601090903050a0f050403080403120e0102030c030a030509100509030301080f0c09010303 81
    0x2400762030400e1aa400400082d900242075500a19005007441c0d100c8909240480c4101d103011401e41d0321203800360326000d800350002b62101c580c3ea1106c00644481c1d0010345000d0500009001c0748c3c003c450740d4024044541b04c00703841121050352a1050000c002c2c488511071540743d06207001404121002c81e0705900e4418103000b000c01030fa40c7c910ba490b00030710400c4050f4190102170350069000d6501900148200c1e80700f42c0300c0200030707010f202c19010900f001740120014002518030786011101c0c8141124911405020710622511004040c541050910b84e0f404020658540c104541094107008c80b5005201a41052114002d9543c1c0140309114081ca1282400340750b8801d01115442042601c3c050340d400500c4d10350381c1e07031641801070000e03642c40703a508001000b1a8008180d544007109461150409034000d60814000340f00640c0075003001407640e851f44c802d0356a8042031541c5809642e000f2011040a103035654100605141807415541c07442000368810500f251941d08c842410b141100d405 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 688720314 1250 688719064 688719091
    0x3070c02060904060b040803040f0b0301150507110303041508010530010f11180109030803011401020f0d0324030321020904150501090f0302100c0f05030403060c12050f 74
    0x2e400002c0c0200b840ba00880c48012020502040b03d007000170040061307401c0d2001064101da03540f501c0034541c1c4401d01031120603440a43d030b500c620902030f1000c2c2440b544109046181c0042380d50100e0f195820951002c3c900b2154080a00d0007282c002e0100ca01400c0e007516228690902e22401c0d0442d440d00c4408080000150000f03514082d10a51110b001c45038003000030b1160716030748403814541d500320140c03400c80c0c9044440e0a00d590340c0036107070503812a03034880e0307005096030301e4800c1c02c0007851301c44180a41540580c0c16610351070141401901100d01007901c000a150500700342190a24544446100c1c85140352181800440d8004140301c130480091042c60341070b541c840038658080d0161518140c0c0040c10441c404030890b0726013a0340400d692081e602c4e02103031603a500710900d0300ca2281c4400f80d0010a003002400d029071040c40a1410640100308401a9080c0b1380d460901e076070b1081d40701351810355952121400080d03020701c0c949454401a40c0500540c00d166032881e000c50310143c8680942c0300d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 688721564 1250 688720314 688720327
    0x60306030a0b1e1f06110a08030c041703070807020f010c0f0501060806090718020706111b100908031f05040903020c034c110a03050c03070c0206 64
    0x1020414181281c0e030105024500e428a407400b0819a08403820551603c000500040d00c2c1000030116101e41500d41030401403400d14041065410000c101130780002070041c4258000070a0105000754028403156072816a118500101c0702c0c500c00c8034440b0103c554008003c2c110101e9040401e444100380c045884480c003c912400503100b611000e800207006003410040f00d0103100065008004450b080f01c140c1301141e5901c0074080e01c2d8000c50180b0f80c0c2c0b0005588400c60404030716409402d01a10a01b40003a14100072886245142c00103003600490081a00200200040600c030080d1404080c040078020700d900c503034032041c503030000422400f07000403000507004400114200c41c00c0280740c00f510400c807012690074005e480700304280d0f11600030321840d00d900102d4000e00d0380c0e010300302c46c1642c01848041c02250094501420640030f0300c40300d40b1030955001e45120244610103c60b0f00103211079503600a101c002405882c0000c0580346007002c00e0040141041c2c106540c0984590b04440c2e2565850 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 688722814 1250 688721564 688721569
    0x207051506030102040509090109060b0109060f03020c03040f0f0602010c03050709180b060d0207060e191214040f080615030d0c05011d0f0f0d09061b060f050604110f030402060306 79
    0x28a1b8800360380301c240300082c404188010350000c48054010907050007183d00c0400107442c0004140320f4500000c1321201d580103524401d40c064011210340400792881e1650b07400843c0605007460300704001041d24860704000254092064041d14440b40c1414022860300510140070701007a8030030490701d0301c030700ca2002809050300e610641000d10028405902c0b00141c4207400000c3d0440170007202e105141414030000ca180005684030300740e01072100e00300035001503034480c440c10201d500c540d07007408003002d03031079113418000d00107000904499480044030515081e0440e1a019000d410103180550042500c0180c0d1408104604440320f2818442000d81c00d5103040ca00401c49552103d1504142c5c0d5038000c540c06c0e0125101184109042c1260b400361020b940c4a42c45d100540810030128807484000c225007401520b1103048a4141000510a6481903c4440603184600740e2036140f15907403000c0192074581840b800304454603041c059401d0a0382482000304030310002d40040d03c07a502c0400000c0596 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 688724064 1250 688722814 688722817
    0xc01021c020616020c030a1b050409023604060912030b13020c03210124050a03050c07020d210c0f150209031c0314090a0b07201c030207051506030102 66
    0xd5010742241e40c4031f191800e1500e900d5214030180d43c115880c100c000291480c0501402507840d030001c05c0d052100c0a13240803007280481c00c0d2640411100060003110012001a4083d40b2490045801003409411494401842141d4050034000e061400c4142c2c41c007600e40c1e5424215a0856450050fa5040118035803491401010704442c07401c1030302040e035130345640343c1040b040c121805038040c007241e40c001c50000702550f1000001c1e00000f50703040c007040340300511070f80006800004041d14245004c52036004120100310007030701901c190308042e9502036080014100d440d210b007020300e0107404400c020b035158068100701d0702000d0710342e5210240a42c45c05c402d6504907400c01d41c0c010116400c1704880c0300e85030515a100c020314004070b8600401c3d50344890095030500d1140d140603020300060b00d4030f503440401c050405441c1908100180712440044002c0c03080007a0400e02e8000104003911840480441261018001e03000301401402a0b0300025400111625200c3c4c088900b910030342c1d03545010900a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 688725314 1250 688724064 688724083
    0x309060e0304060518031911130c021e03131e0504060f030309060516140a08040909022d0d060f06090506130902090a0b010915020c01021c02061602 65
    0x41c007001500041d074903001030007000041124401010b00b00c59990070580c9481c60380100405407203038001c003040091041101707251165001000d08808a50000114003203e441e4200070000d60b0007403500e20945004082074100740114900190300d061004000d00141c003603288244103650307000083c0700710280c140d65040c0005d804060300400401d9078403080d040e400c05d000c0c4420780104200040100e60365100310100e0340d540318070440052001c0307030503510703d409880900c101c80c2180c055840f5a20014090000500050200110202e40c00c1c18500400c012525101c0101e000401c4143c1c1c08400c032901a81628454041200c282e444002c1a041c0b04028168a8400e201d08a240c940042034a115644c40507004690580d0544010080a00744004445405802a503c80d40c407500081c005031440e000900d03148818901b004c01d66540310021050340564000754030140e0010103c041103540c6c100000301504800a5102145803002c92001c1c0d29844064450765072682994045c40b68103008101c44c00c0c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 688726564 1250 688725314 688725341
    0x40b010c0b09012004210812150f040203160e03070810050a2702060d0e01090807030e0904110603060619030911270a09050f0a02030c04140403030906 66
    0x128541407280b18000e008000c0c141c091202e211a040c400c920100d415582500d1321040991030864040d500c02016591914040340d85090401098008100072801d550081a2802440780e14090700070801007400220440c45000d50302c18400c00030110380c0743c2c269807035900d640d0a042e41420107a101181c09c0c03075840c2c1c002119502c04ca151034804011980c0c00b043c400c440e1500100500001402402c150704860018030750344000f90f0844002510304030000f04225440da10000410f62411100e86096451a200c1640c1032140441d02e1403d0540042c130a9895840807030b058502480c01c0d56030304200c01240070025006070404400282103895040490301c0741481c2c2c000401c588090510024064414036000712500c1070141080b10340d41c1080c00c0004110031400b100000d64140e010b14444000c80010240c3d020319403101044404a90140009034100d102240680103800550050518010140f40300c10300561400c103455408035008038805400590610700032400074201c2c2401c0e406800b80c043c1c01e8a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 688727814 1250 688726564 688726583
    0x120403021c0507020904110f1503040b0f040506040b0402181305070504020301060e04090614010e010603050f010b0906070c080609030409060816051002071508010e090c030c040b010c 80
    0x1052640000340c8081841414044052108501c4070403100c42c00380500c000c0d0840011008100003641e08181603003e140040c0420803109003890015080c500d40d41c0c030741d050080d4004140014800414280d507848580c5440c00a031a041a58801d0780e61100207201510303c6100318042001c65075440d44016600c941d100d40d080c00c0741840c402c00720086111a104032503600ca0490000340324185802500c1c103c91060300ea1101c501072660900c0040c2c44010f008032010351f0b841d03c0302076a2240410055018124000200e0340e158149400542115005461140014040001084100144d10403a044400b080c0c41080d1140064907001c42103c0807904045584d000304000c001c10b030540000604101c0e50550b20901c4503075550310845444207010b80c0c682c601c40c80090024011410044218035003500244115901c4681d2031045101040341d0301080d5000549683c01000500440c0d046260040f408402a14100741c0e080002a602d044114006028548070751031000580c0c015500051040d03040712052 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 688729064 1250 688727814 688727821
    0xf070302131509020a081e130203070906031212020f0409110903100203150d0f020d080417100f022b0e0a0b09070e2a0903032227020a0512 61
    0x3c02035048159130200040d81400002c20b8002d030b82411844c4080c07842d248440b5500c50460b10a10603400540680c0c051140880020305200e6074411030b0011402000380c5d44014620b00c2c0010000c2c0031141d46c9445080c014400c040e000100780d022a000c580428200150409084100725103a000f101001503150180580790300400b901c0d900194440c0c40524101148002644208010704c91611406810f4601c8a59400014203001b03400d48503c0e800340041e0707030409503036260180d60303189400c4005442c1c1c0c01044111007490300c940207032290707122551019410052406180030050b003440d00720b010101441269100280000e0384a41403484404081d103010180c1c3d810980006142503801540c14400c03ca8002820039001c0000c82c000c0c00013500448128280b94601141d40c458281e81c0301038030030204400041c5070703020401070890040d001c4001201e0a1302d45959841c9408641c8903c4041c03210682d400d03a0702103c1c29101802c0021000d0068441411005c215410b0080c030203881600007550090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 688730314 1250 688729064 688729079
    0x4050106050a0504060f030e01020c0a05010f06230409120e010212041409100f0b040e0c03060102061603060f122f06071119080606100c1101030e030f0d0b030f0703021315 75
    0x30480d06020310300a00243d58840e0340fc600312002880b80c154a0300d00322030b07450912002080022407407040140046903241d4203480c1c1000c003c240140440c040ba882c3ca0012405503010320a910202d4804084039040c1440d01501d981c00510320443c9a1003021b0f140e00140300310f14002018001b0b04507103105c0c410b640381ca6501142140d8170074021100d8145401d00040e083c2c00203030007240d04c140c6060b07000d0116a1501100e100611007240a550145030f1184408034800855040381c50003000c8402c9150710300700c0030703051044000981c008020601d00c14078120608207003400c080310854120541c1d50969607111820300f000c940c849600f50360351121003080c280e40a500204010004d403891201a01d10340c1c0c90382d00c208045030301d83e08904404100c0d4100074030301280003a4010b04410b24103040110740d280d0301c40b80140c1103511006114004000105e00c3c10b010054500c04c240784c06000b1b40c01400c40e4840c83c41c0840e80d45410b848000e11070991703149170094680a54000d28984d032a095850b00d5000d850340304 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 688731564 1250 688730314 688730323
    0x30109180c0b040f17070e040f0203030703090501030c021b361008031804020f070b040605180f120a1404121505040b1f030b100504050106050a0504060f030e01020c 72
    0x4c0c0e401404103031440030400c283c403101100604031061006040e2207240c02140409114000e10554059281108800260714140001c00c01c00e0300c2661500000341c1004c00140407a51240c00341400c5602c558480c031111850402c0d14041000c080b9841c41040b807900318081e1032044020105007222039040c110350307024031364001490300030228444241e21540d1140d2a05949010380100c03400035044480034040581003d82c014000c4030701c4003010610700310031a100d5020450045d9800c81d034041e03036081042070182c0341c815800c2c03055050501402400c81340079071640d40c40b000c5000c40c841502002800d42106401584040c800c07030340c40317081c0a4450f5a070f40705408480c40da198094a04101280c8409040c5030b05110305845582c3c00702d4101c00580b0390301c0044c54a680046155006030034039503c0031010850441da914426a02001009003d07414442804195841a4031900c2800340a01c100720f49240c001c000da40540b400b078901102210600d060440250550702c10b03120f00c6510009450002d20000304 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 688732814 1250 688731564 688731569
    0xa0302060f0d0f0c0f08071706011202070b01050f031209151908161e1808070905010503010c0c0209220c0306151517090a0b0c03090c1005030109180c0b04 68
    0x700c030317594400000d00701510301c0d0708122400c1c00002c04000011100c3c00e1040c070b013141c000906240c42e02c00303c03807138044180c101d80c0560000d44031108442c004002030700d050141009000c006a015040c0c1c58820b8800a6040c01915980b03480b595601200c0b4960900c201c040d60300169800c065600001340d0004041c10514007682e4000d41d60510540c540706082c0101c0c3c088080d500344204030403055103102d2085a0014040e0b20306001c1c2e12098400042d103d008011200180a0380b100000391545800205821945004000c20500c64252840c60160b038804079210b6002c0c0401d5000c04403800300342c544001042c51207100401801c0b2030362010041c450254001d502d0114030040b021206038035070103030925600091010702c000034420710a400c0c1000e07640305840d401a40150032182c401f03031107603108040b00c54121402a09018044208120000d003041101d0729603105641d0b40c450360300b1942d00203145110501072034080e0303500d50701c040174034600c208100c00c0300c00c0c5c00440000e803c98468070106413a90292 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 688734064 1250 688732814 688732817
    0x90a063f02210a14061002010e0106080106080712030503070c050c030a060203091b0307060c170d09021302090a03060504051e0c032107120908070303030506090c090a0302060f0d0f0c 80
    0x1d00180c40704103d07204004854100d0b03e980c070410f540301c1041141d44030844520408654072032002c00070a503024080c6801a004080000c2007280c10b01074043d140c03481d07544c00380c100d41808102c05000300390418101d9401000d141f80c10320842404fc10000d1601110071207450f01032044c4100c2e00305104042d40554080d60b500010b6074000a1580d550011008115200e164035030003859042001d140211603072500d10740f10b21200030600031007528100c1243c01110343c0c85403550316030581108601e421800c0d00e02e4107102690450801d1001c401207420b5005500000702400c1d62040400c0620008000e550701d9a41c2480014482603803204005803150307007007001d1900034811005100003c0c8801c407541030f41002d00c0301e1014140803058403000005078003e8611001c0c411f18143c0840c6075041842804041d501030384001c11241400c006014083c480100755907042d04040c0030302055a0744040c1e180044035012070380309444030301c20303400c00450b4821000d00d000104d140c5500010049400d401404266030b05 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 688735314 1250 688734064 688734127
    0x40c0f0801090c090e16031104060e0906040807080c0a0c0e0a2a03090b0106021c0f020c041e140604060b07120c050312010803090a063f02 61
    0x1268419070903507025540007802c400c07503d042400f0b0700c100c6a1140e50310388012002c4410115612030725901025540c0c100744e1782600284068810b43c1000e00900004006802c0008164901414116200d04024100800f60340b00061104284034480040c3c170403d1100c04103a42614400d480d04481c0034106118045016084a0000f04141100e10426409101c01e00c0c1e4440d048510080745054902036600880c2031590728100d0802103500741c03802c00d001e00b9254005000c00c0301d940c4070341039940c004081c030340f42000090402128404e5010a00ca402c4040a40e008a01240304450051240d481280e20400c52444c01c1e08540c044203e1030880c0e03020b45005e5800700300083e101d180c1c1c091144034400001d80703018454201e140e15584100080303099280118283c078140500040c51045401c1d0a0b0300c551041e03030010510001d1031400b4a481002084242084d8a103000c6daa048010005c1500b5030500c0d90784055074040401a6501c8100303600c0e1a01c1000441d542e021140c00210a0b4400c01c0381c0c175401c0c0c0103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 688736564 1250 688735314 688735319
    0x1401031a03030d020f0c030a17090a12051b12070209010e040b060d0c120605090d0903030815030a21080709120206070501022802160323030f03040c0f 66
    0x4251001449580d00680514030f4102c103c81580701951082c843c00c03920110400040e1544042400604800c1c03002c1ea0700e41601840040381076641a10107410321403541c001d100e8010004446030b400c41400601d50514507241c00b03800c924848041c640b1440000d00340940304075107800c104410f00a10802d0300c200d650301c1d403990302d400001a0200c004c48004102ea89642c0101e0010701e0100201c40c0024440e05419a03990b8031886c06250310480604101d80c000e41790001d010301d0240910442140040c6807030f003102e0721792568800801064018001841990840c4202c00c06501c081c04003000c400d800100070802c5034284d0401410400020000000043c45003010800d507600c180c000038100d66243c1d100540c0001d1540030021b4a40c405a402c8510359420003110f69013151448003036030003c0310208141c0e16448800006410005c0400705451000700f101d0302400012401007814000d010142d030050034045054281e80c1c40d6114042c0d44950000303010003080100201c010740d0100396440066281603003039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 688737814 1250 688736564 688736591
    0xd06060503060d02010c0c1a0912010507021b010311030c0a02010b090c07120507240c1b1e050a12030b0f09040f020105040b270d050a030c0507030c140103 68
    0x2040c0c0703071143d00c00030140741c00c8003661044209038209809401394062580e9030303401d001c8290a1f2800510000a07000c90180c141c0e00d001211050b49000343c000034003440c54210002516100091a007404c0100303903410561169100780d009401c10940610a1b0703130340f401d060f0300d403881c10340000250760300545c245034540b1043d08112400713602440c1c514410508120440c0c0d14422156040008101000400d009075408212000d1800340a0f40c00d44100c004090b40d0a21001e041c1d90300004101c0c14850b40d4002d040c002c800c07000341070320002c0c1c001c41a0011540d0361402a0032002c0d010070040d00034841e070a850800d00003a003c6150302c40700349071800c1103c44140c0c0d091020a018002c040c940c80000c15001402043d02c0e05003042d40b03284140741203840c240e15104843d00c55007040d0341c040303a81c00c00307102e51800c624120090000d10350821229010030456543d222176849101e8200202040b1014485404028007040590b0156078002144900561a1803a8580030181c100e44903000904051544c507624 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 688739064 1250 688737814 688737817
    0x2a120703051210060512250302090307050a0f03020609040f14010e010e16080a0b060408030408060a0525030908030a0b090f04080415171003022d090a021e0d060605 72
    0x120318a45030941044100302d0381300700c42d04004050b482c51041f0b61000d0802e01650112600001da015200161110342c4802854503000f019002280245020903041c8610f002c0103824808403541210007503920301480d8085000f400414200100e01828145044402655501380c507050790b212416401c1d043c0ea9443c61003201c0c000584004600c0c14441e45900c280b0391042c030780c40b0382c0b01a606002060000c440004502039501ca5480b0034100d400110b002e00880d0703403d000c0030b42c1045901c003081c0b0650070b1403801c1c00003003c401d800c0341800c1d146002c00324180e24020340000001e503401c80d509580321b250a42d040c402401024182c5841039255400107161661080b0f040c5000b00e402c03a00e441d080a081c080b0426060181d40da0041c24000c4550403800034403514000c0a201d2215241d1103200c1500e188184200c25591300307000b174201540604e00300786548100032802200344003181c0140319621003404882c0284a03e80c850f02c00051540001c2c803014084134003c010b81c4500784401c0241039a10002100c07107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 688740314 1250 688739064 688739069
    0xf150309021516050d0f0909020309030a0f090b03010b0a2c0418020406030503090114070305070308190207031106070306030b360d02122a120703051210 67
    0x210030710400390310421285030090001031220b00c40f10010040980c0341c0c203140100409410000420071a00c4068160344240e00707000915000500303604508200040503200d00034104000c04006000100ea0150351180085030010650402e0700c659a5071500303030189141c0e2051800b10003203941103a80201001100618210210904090720304802c954000c100c003800c1c200301d856403200c40c6c0b140c801000d640d480c440d0b040118807500045590304164030001d41a2021080b1003000d010061042d0070102c0d406c4811070314100da1600c2c1144941e9113088040082c00c2c00d02c0d00c0b803800548085270301c80c1015080320301d00442030100310440d8000e540e500412810b650003030200500c01c1350404040350400040d21140c0d865010010307141150b4400c02d8006082c0c0d200c68407078290a030b5000308000005982c05000301c01032a9894a40245000718104611301c4a4040c03045c4049016205142503070006403d0040c0020350f0303e203008080d500d1b5060309000300300c2d4100d2803041b0940090180450002030705d02000104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 688741564 1250 688740314 688740319
    0x2a0613051503061f031d070f050d021e06040308070b1f0b04050607050f010c081510171005040507030902090606031003030f0504030f0f05011a031b01020c03070f15030902 75
    0x40118081541340d0b820241d990b5440030316440d112002d100075400c0c140c0c00300360052040103148051810310608011b030700984c001801140c02605100150700c1e61455075141c00801191403100c9043da44c0821a04d205560010b000500c0102e201020411140380250140c03d5001c40906180c2403801c0b046c20203d1140308032160001c04000810090a10001030801c01c4d0080d410748035035880d43c61041c0e00f500d480140180000c4c1c000010060080c0817604038101015007580c9182c0c820440007400352101a107410340100c4103c401001818510640e0b101e04090500540180043d0500c2c0e800600900700454003203200312070501c0020482c9c10020b080c0e03407080d400c05c8404650580b641d10140d54800e060400241081000c110201c0856001840c1c040102d101d03a00400c540400740c00c041d8216030682e910346090b00a9074007441c80c0d070fa80c0000c00784509805d40308110003086014005034908046070304916010f01802c2c0000034035202c0a4001403c4a102480c5903840071038800c0d08604550403c1002503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 688742814 1250 688741564 688741579
    0x9020d0e0c10031109060301090501050a060c080d050c07120503150301090f0f170c0601030209060d170a0c05060f0702300d18050604030315082a061305150306 70
    0x3001c040c4a600400e0503100710b44c41140c9405480c0300400c9095209070803505809444da8010481800d1945015004040c07600e000452085240d0f00c05000344189010012550380341c1c0d02041c600f0082000311007425600020146001c8000d110203015038000300c0324a1400c41038078000005038141070144140c0c69034031024030b8018556aa491a0440800c85c0703099545441a4070740c802c0401c041c0000f4040c403004c0384014945507145204010070031000038203290107041c6081d41d1000083e2414088010b03c10380440c0d290301c510b00780c40b0440d08008402d201030811b1190100b800301e00000310001c075002c1e420590030303a2180d900e100d2240c880c02c1101107a0808400748041100c03501482c280c040d0841c02d040340008600d5907820300c0e100824540350081903806030401814402016058812985800d00041c000001e40c1d2400b4512a2200125040e00401d0055401022001c0c024443d07511401c610041c4030780e07161082000039038800c001d2405002c3c02940841c109401c950003007400e0b640714100040c21070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 688744064 1250 688742814 688742839
    0x906150503070e0718030b010e010605091806010329150403210203130b0918060a05091306050405160b090915152b020708030705160b0109020d0e0c 65
    0x203a18070307000104004c08125240c0b07010003042c502c2c107600200031809404100d840e035041c4554440d0360038060384403405004040080d001c5035250700038118101071803e9921480790f0390b1107005030042d14408102040d1542400099800c401041c498410364003425100c054810703040c4071000c0c07221701c910b0001810114000900140041100420012891061059a05013030401c05c041001d071420340c001c100c01aa0109072403000c0c0c1007c0b079104c2e4024509001441c000e0801c0b0340803407440c0318103000b00c80c010b190f4940041ca400381840d050b10031165010b00c01308003d14082c2011a11900c1c4941180d01b028030170303140001e0f4682c807041940c0001e1001044c0c0d0455072217485015400c0000c0240389900300341c4c12142403400c90004800360045640350a02c089141240c100c0c421085c01c0c025000b0ac407207901c117110030b07404543c0b05030560744d001000e800d101d0364540320300c103130021003003c50f040c0248540315550021504501c0c40e0051f150345140c8a006100c0a1030020000e600d54261409550f04440400040b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 688745314 1250 688744064 688744079
    0x60f1d100b180c0c0105040c090c0309020a12060e0f0f06090f060f07031e0605040b060403200a0f0b1b061302040f0e060903130605030c0706050601050c0d03090615050307 75
    0x1907030f000440c0c000c00300e18200380205403a080d40d00484058032011401401000788c0c0842d4040c450811010b4a02080041c040e9400200c8070501400dc0079640b003d00242101006042e50240340fa03440310800300c60031046070088941d03581036045e9007142c9034041c00c0b0104d00d80040004203403c0004004028001641d50010510303c01e440080411040544442a41c809074111801c0e0900ca49801c20000c00c14074144001c1c402030b145881407540c01403508000030001304891500d1081180c068030100701106c442c00001510b03003031103504030400e40151000000303a00c001c400010405a0b91a1100300340c2c600b5005696074940c003046603054a01d80f80032081d500145440c5d031082c03c02000c00e22002845403111a0041c0c5440342c211160f80c03e0b548002586440e08003010403260040c6000c0c40c2862a6151201d00b41001d8050084024043d41d181c00103d00d02d40c1c0507000f581c01c108225011100d900c040c548000b0044c2c052000d080c3c510380e18000c0456454202100349400380e442c060010180caa203030540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 688746564 1250 688745314 688745359
    0x103140118270f0b1b120603011407181401020a0b0613061d0a0509030711060d0c0507170a02031602040605030303070807021015030b04060f1d100b 65
    0x80710020950116040004442e0001551100b2809280b024020203441e2420302d90220700036008103602c40c5e03090848540d40307918100310f54240b00d510410324030545071000030901408001d1300c0280000400401c0010055001440c40c1142c50884032144000340d44a100c216903040004480d80142c00c1132542c5030101d03050141d800c0d0404006841c28050a1680c4d10003021a80f19400681480740c44403800100d00350002c1a13960000203091040080781401410b003607a0b031044076070052500801c048594000d0351100281d035200424031105104030526a80b0003400c6901c1108100c0380307610344000301204680c048090b5500c5204a4006504d011a05004c04002c03085d244401c9a01135100e80010589031404d102540c01200f09483da65000e04000e032010307041a01d2145504062031406a103090040c039071111034001c030794000c51035268a8450b424041d000d0701905000314111410f0020b20311038501c10001c0c00b200c03503d8500a460855200c011454255403900b5501c0e40c1c08014603c1c28030300030b500d030309 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 688747814 1250 688746564 688746581
    0x1507141c1e03021606110705010b0604051c03050f0a200a020310020906043302010b0a05120f0703030905010f090e010b0c19120e0603240303070215090103140118 71
    0x1002e000300e4013400e503206403e85040180c2c08600c0c1c280450f0784004c011b0b0900454a400704121081130a190030040418200401074034004408081da01748202814004c0c0111001914446812030355820043c00c007034140c000d02503403218503800495071200041e0002c140f0000f159401006440c40346840c6003081c01a4000c1d84103664420780800c4000740c0680b041e40c03184280c090944195111580041e8206ca0020a2a20080559042100c04140e036510303110032509613101103801c120301c4400d090b01c5c00e150103c010250895849a182e0100c2811f81251130041150402daa034035640724412442114800c81c1c3d403184542000300907006016051203207020b01a04440442100d103002c61881c083c90002448500544009500d111080820b03580b002c9002c0da0342e1800c1c1c421601c0e6082030311580003100340150070a10ba4120220101e551035409104413980b154000380062100031280c0b801c41d00c2680104c58007070109103400480c008000c501191f1034102c4030301d005100020104036034540b01030034441 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 688749064 1250 688747814 688747837
    0xf030e0619060f090b0f0d0b0406020a2a020415050105030a1107020603011202040b0406060509040902030f07031a0702121806071505040c0611030403021507141c1e0302 74
    0xc01e000f02d0b100301c143e10140000c01029a02040402c44201441010300c3e20040e032601581055082401207000042070325005a40440d0048e42c1d6900202d0840b08480f59482d40141200801107400c10641492500c0e01e00da40225400c000741c0f40030004141e4103801c58411140800d506000042a2050980c000c50380e15a0550102c0d00d0810300703030b00146507944260050b140d200c0c91000c505007075081511501c031203e10142c40802c116400c00401506900909981512480d242c2c020101152414040310340a003021004840d5102d03101c0c07604c19034900600005001c02d4010b4000109424070014944480300300c5202c01900d0240c41d4007440c00d610719400009608140100045400607064080000400901c41c50005031401c29141202045410360700c000b0800880002e0020502e60110032101126811070741c2c4809800d002c051001c0d0ba01071030764003800700126191a0300440c2e5010401c000c00205131850b040301724940590544036a4090100300e45070359001000ca500007406640202041d41a4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 688750314 1250 688749064 688749071
    0xf0503190c0806010e0618150c07170f0a0309050915120109022b030518090a06030506090705131508031902160e221211120c030706091401060f060f030e0619 69
    0x5103003401d840c0ac034081d401003100c8580c0ca0340751381400006001e01d010b00e0442c0005008544900c2c2ca000700200d1003170041d1442090301d280416001c40030b6407c03c41100d40050005c2007103030070401c071182c02449450800c2e401030740182074018006c0d034246d500310000e500c0036040b000c00c2489134601300d134030360071626409411049140c21402c4035500c1250345032144107094004100c0c05e045107051420301d07402401802c600d80c0006c0041c8450f40d0782c3e4001882e28002180e00203146100c11181521030b444580c00108180000202d001184010f8088042151100c1e007c0b20b41b80124900b102000400358442c812244000c0304c045450309941c071164009228099820702c1c00145140ca0b021103960100716040c020811228032103107190014072514009c107101c020381509040003404000d46178030030600300038801c1d9520008001000500c020042c10a05400006c0080710b856007541101d00c905409910003081e180110441c0e400d21038044c403440d00d40044d02404090f224201924a0051a446294051600c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 688751564 1250 688750314 688750327
    0x6041202030f01111b0609060105060c010f1a0f01210c1103120f010b07050a020402030406060b070c0303021e0c0108072c0f010f0f0503190c0806010e061815 69
    0x1090180c1c4542c0400c09040e01d55840740c05c3ca000c00c0d90302d440f500c0000e440d0011820040380c6040800e88904450b82902c61641e16000e440890b801080c6410540c1c400d01c0ca004036880b0035031007025000b05444030544009445030f50040054071651790846c0310642c0d8004820100c5181c8881e60401c1881c5c14190408a01042d08041014150307000514550f45601d032560412540081d2040040d0050064a8002d4640381041d00e0342034503000f00c101c01078012600003000c80e007007080301c0e407200c1c0080440b10100342e00c420081c1342400301d44003180700030350040c498000b8400c2d9440301e400501001c2d10142c002000d030381d091113005580049000b42808140070741da84001022103003e606102c0c04002994140759110a000200719045103040300395410004c2942c4601c01741c2d50803840f0b000d04519241451500c0f03688a82d0802c82c035403088074000345403908182055407030b180c0018002d80940004d0300c07200c101d0040d5009001c036074015150324903036003a40b500b0000001d090820844101c3c0c04100780c11440c041c1c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 688752814 1250 688751564 688751593
    0x60e0621150406020a0215060a030b04051501081005010e1012020a090203070c0c15091a040803040f0501080f1918050105040507030312020a08060f221a0f0604120203 73
    0x7039007228241c607010b0b00015000710f02c55041c4442a40031002002000680c1401400314801c0245804000c2c0200308140c0801c0134802c2c1002407440c42003590481004c1c079038443c00000d0302c540844950045150400001007010030f05510f000d0700c10640c840300000340c5403410800c040c41d100c0101090307800001260001c11407200c2d90000318416111500d034090701e0a520700c2d0078110081194041e5940140003a020320364141c1c8889114221803a003041100c1d807800644510100d4802c40d4002801803100280000e00b20f1840a00c1c007048038401d803900b000541c0d0740c00c010031b0024022640c015540d8100090450000700b20382c0a2081030b004a68001d2204510f96142800c690b01a0b409039410740c0003110030810107921290052004280003015820300d0119000506410030141500e0f00c01c0600340d0100f032507921855103282d070b490841941180308030586070201c40100951844182c00c00c030707801b14448482c00c0201c442c0205c1c41018106500d454540307420380e1003081e131300f5a04070f0381030003540540d503003e6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 688754064 1250 688752814 688752853
    0x608012306120106081e01051e011e020709180c0603020a1808031917071d10030b15070f1112030703110c0405072f01020d02030109060e0621 62
    0x3032000303172529462804c1c0024410704c007030712150001c15010407a1005101d1750b100e03a04a585040d00b240019140003003040016521100c01c40081618003034081c0d41024010303800508141181c81c181010400c0d121a900704c0b072a140783c1d8060203003070b4444440b01000800e10030b500414100702207140c810294682e0640c01904810300e90701c90002170340042061849200b0b5074224500b41c0d1000c0c1811200c04840c500801c2c1d03e1000140002c041c80f29183d460302d25404084191110741c84010585502c0341c0a82c20b0240042941c120100c4c01390500e01203041303032003265500321420715800030703840c000110141e65800c0102c80d1080343c003034220142212045d0561003c01c003a0001d40d00c00c0d00d51058403030b0342c108090725260b1403026140c031803400e00d07090080464000d445101000035000c400341c24580a8484030400c004c0c5a40103100079880001c601c142c0e034540f41e0166041e980c00110a02c10303d565002005400351065030604d912440d10200c00c0c20500c0d40c042d08525502040082c0c8400c11200c03410031200707 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 688755314 1250 688754064 688754069
    0xd05030f0417010c0329130207030203130f0b1213080a09090b0108010f090c170a2f0901082a031510021903110d1806080123061201 58
    0x61805000c82902e40b01801e01802d8040401c0786802c00c0315000c0080c0200c082d0940c529205040c400300000424a42c485120410490611200c1555980303c6460029a00e921455880c1c180e80310300f0001145683c0903185801c1216181e448944c144100c03036540000400016004195010199142d40c0c005074144000e450102155101c80b8503207441c10241d4030503580c5103684141088011030050080180640a070802e58915800006441541030426101c800340c040401888207074a10411003140300d00e07041031001e8842c403658122180390000401e4075800c19148120700d031074414001140c1c1544640d6000d81e020000300f00b400a00890300400c3c41c24901140703203e1000100020801c0480ca46181c034a01c0c404409882080c00c0d0304007007d000303484440c1d0040225944488180300d02c18188590400c0d9606030220302a90004102000041c02c442c0100ca03030007542e0109c0043c0001c0175030040b001d16040750800365003035403040a4842c1e0240e40a1440c500300d9442801440946200d40084210720f01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 688756564 1250 688755314 688755329
    0xd02030301030c1401090b0a0e190503101112130c091b1b02060f0c0303090c01180602120f1216180b0706020306150d380d05030f04 58
    0x65075419800d0032a5a10410b0300418a4140b04424104040c0d0f4014006811114002e0b030464440f401c452040307030800050440b190380110340480e018050410845180100c40b411402c0b5401d00c12403c00301410f1b9000919113441001041c800c0c891341900e4403c2065101110b0400106641c01940d220440b1074260f0300b00115aaa803111101344d170481c05003122001c0c00c070303a04024400c40070040d01e0328031403040d020703000303000e10300105618040100d041d0580b6280160801520345a2606e140c855655070000203e550000381a07034591010802d070850ba2005581e01d5501808078203009008801c0103510a9a0301800203104100c40000180c1e455200c0e4014005600300180a500704a001000c0640005070346401c40340b40311003048007214103c01c407a0300d10340c0601e016889542c2c0b0760028101c0070748014540c80150b0002880c0e100466903612550901c045402d081c0028030040c05201000307440350201c203210640702064a05c09142c0100c114084030300c5841100e103001411810801d00350081d520569 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 688757814 1250 688756564 688756567
    0x90102040806072c060c0a06150b0301050a03060507120e0a020a0b04181e0e061b07080405040902040f0e07080f030a020a02060d0603060204030b040b1008100b0f030d0203 75
    0x180708018056203400c090719103402980c0149801519200c0c010903130010122005050f0301d410b0940b00c14055803015007244007603560b1500c03142040009000c002030f4030550700c3c03a81b54021034038013054001e49040e10b60140100c122181940e4a4500804016001d0002d2003884801c0d80c59401d094000ca4a420100c10080d240400d803500c103101140090380c101d80010700042c04280320410140c010001c8194000340b010443d080440d4030255a50b1950902c6120203044c840c03502c200b0100041c1d400d00846103098003c03080400183c4003401e5006203e00145811401c00003003100e4034241d040707e0040c078002030000850746002450740c001c072034500320060bc464002c41ca0402c2042014440301301c2a04141025500e4090070ba01d0007500d07844e0300d20700280314400c003040c1000400d001d070b0300210181d40d21134001c566560712030405885003102150126103045207203000480e0b11650b002c001d400c9415400061224214002c041d0f005000b240c40c9007a081b4641ca9a204001e84d4200807103442ca0105401a5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 688759064 1250 688757814 688757819
    0x2060f091f111c1b051e0405030d0201050709060e030703030e0f030d020706030f0e1203100b030c04031203020a08010e1803180a05010804081207030216200301090213050601090503030309010204 85
    0xe015211600e076602d0b410002c0020440c1070b560464122008030b541540310820703074005410300e03984034040c0760088c940622440007403c11150301548258054401615a141080d540e100d040760041c01c1c8107d001d0f05900503860420010b40100324020b51000002d200c42c152606c0c2c42d0209261550103290440182c0c0b100c03400300500340c0c151241103544055a11300f0310000070311418441c1d071100c19421501c0c80300700c0040050401d446040720038024144084600b942c03800c00c407a001007650400d00069441c04a410103c2d40207038028408c80f85500e10740d44030041e090303181c0401307460f00c503030010307c4145944a0030322068000402400181202d00c01180122a8013144400340400d440302c3c0e0300400e050040580900c8042865481514a0641404030308509607803040700c03c80c0640101030300344041620854403034080200c0310300b030501410019081210a91544400c260070385580c2e0f00d0180d00710800c5401100050641d41041c0c0d402070741814032180155449000c6403030b6a000701da602525950204c3d06 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 688760314 1250 688759064 688759117
    0x11150114010c1a07590108040510020d0609152402070e0429060607020d0c03020a030c0f05060301050f060c0a0219030302060f091f11 59
    0x22495080000e1908044214041c1d903155846454a610814440d111400244021340304010320101003180042000d0790300e4404440e0183c4031418182039140c0170740c08807840d80b80c0c0081420b20094240059644040c1c0a1080041d9202032024000707031640c6c09052003010030495280020560401040030000d050340c50710f015281101c6980c1c3d140480c04001c040c08002d40c0c1c041d81c107a030089450f07000b4854100c00602c0002c4e85007084035070080c60000c60310001c200610902c000940398420484450301125440d1084010700c0103800c85102d940143c1c1480200098142542070000d4180320f02c0089107039a4a940000f003c001d0640e004440110b40a0000d00c44c401458800340000d10b0709a40c018195414000010341c801c1300010b89502800010440c911820020005c6903405c0d900a80801007006110641c4003248505000540161041b4001b145407860035101c1d0a214001504c06441c0c020940e01540d801c40050400700342c101078640204400a180080080085603074103090000180300b0340a0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 688761564 1250 688760314 688760339
    0xf06030712240e15190303020d1e050a0c2001090f03150e032a15010812031905190c0e09010314032101060201061a0703030c111501 58
    0x10a044590010101004010180448009441880c10f008100742c3c1d59150f100310700910500c0069000c15848110f40c0c511004408590540c0c0c00703682682c1c00c459040d20103440e1840b14104900c3c0490764401d54450407446100601840403591408400000c401c9e1100c2c1c03d440c0417020b59105044041d40b0501c0d0b1343d0f030410b80c18402042001e40005000346036403242d4012503440007035086c10130748444c074010030301e6020700c105c50116010306c0d0001c00c201040d10049450221001001a0300e21400003006440d50000c80600d040311072090090400268014084915420260106030400d00081c51040d4001d000d0080318882d900d407100310907035200280503110071b07174501e0b02600f0b09106810950340030549502c1c50681c15280c01142030411355032024080e519503c6040700d00400e615a060b02c03401c090000c144003504032040c40e4001c3c450030303072510740d00c0043e64440d440c208142c10003084070300c0000b8080e4000c00402c0c0c480c0e003800040c00c141c0c00d1500741003008040e00340111000b00b00051020b07104200c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 688762814 1250 688761564 688761581
    0x507020d0c0509062e030b0621100503060406020a020a12020f01050a020f0a0f0e030109060603020909010605031f09080c10050c031b03040602040302281406040e060f06030712 77
    0x88503005034070724140255038014105802d158103040304180c04405c0c9030007a0002002454007400480d50f0391850010001195000f00b4020303800009240441c0302c1080b03000146003074030b80040240191f5111a0348480095101202c6042035004005911000c5030b044601456021080d8026040030a903110300542107500040480000c14418820a807240d890481980d04c041c64606080e1500740c16241d00791003c503100350f8460750541c2000d0540040003001c1c1c02040480b4401e0307801180c1a151010500d00382c8215014040d096803148682e0381c4100280360b14046200850100041c42108545034007169600401d0610426440100c103400418481c0c0b003000d61002004403100e0850600900070701d40d41c40f070310700c850103120400300100b07003481190350440c0c0007154001d05030f040d030b007262400103900e100703540c0f0403011440d8035a2000980e04206a84088090a004060a281604160104480b0a4043c1c0495000394180c81c88903696200c400085024000a886a101b100ca88601420989080c00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 688764064 1250 688762814 688762819
    0x901140904180b010e09070e060f1318020f040b100c0c0306050f0405060703050105060409020f1c060f06021b09151519090b03012105030708040609060c0b0a0c0507020d0c050906 78
    0x1030010003040032304d03404c41a042032044540507140e0307540c1c6001510360202050b2841e4010301c0c14090701c0800282c00803403008188281c40b85960b104a030300400080b100c808691903040b01d4901043d01c5240c1c072900449041c10311806d210701c0301c03c5d100d8a80c01c04952040780d041c041c00710302005000500c042005142e40c42001c2e864288070960410021804900892143d07900103600440c030346480c00080000da501300e1440d16580381d00180a0100d405c040c150921440c2548081daa41c0850858408144006202601c50050f540c45296600340600e460005190366810700344080b5441a40e5540e0b08201401c080d00c58a69441d9424680d403810b503c0d031144901428048008420001c01d000b0030140da0464004a500b4402c1881641c0e00c802e200d1080d0600500074040094070f4400c00c40c0740300240080e15840d90b54204044e496a005840900040b00c02510031110039001a40d040c40c02e404c922034007030007840c0a41c1490110b5002c903c01801442e01292040300110040c880c1d420034894603039100c82d04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 688765314 1250 688764064 688764073
    0x17190c230307050105030702070905040f0b161b02040612030e03010c093f030f1803031d061b0f06060409030801031b050d060e10020901140904180b010e09 68
    0x291002030798034400c2d4400d26040c0300300800000d140a00a01c03602c4000d1500d020207110078501440c001086006208044031280c0d140c00100d14006c41711010018924075a07161011164042c107541140801c04017002c90f40103480d41c401142040c5400b030060384162003501c1c0c00701000c8180040500791900316248208000c010181007080d208040d40003d84491851010700240700083d1113081983e408042341d0b90003d954440356010964800014000d0319a00d0f03132240306074032440510004a00b681d01c005000289448071410804a10351548542c1c1200201030078501140e40945034003000711a0003113801900310008020604c24180700655000f038045804101d050300c2541c001d01130000600000c2c000c9034001011610420003c0b00002c098600200140c40046407441c0c05009444d001c00202800d0080c00741440e0680d0f03d0b4001d44205003c1611100c215014030302c644016600515949548036444003c401d107090307060702402100a000c0c01d2100740325030421010035005c1401908405051b0701 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 688766564 1250 688765314 688765379
    0x2100b040e030919051008040606060309080714100e0c120706090b0a03020c161d040302100b0622150e0f1002011409160812030117190c 60
    0x601008450341c3d501e0445400254003080c201c10819500c1c0e41d0002900b213039419200070b540d56041001a80b180344a0003060100c2d030340340c00088042e0382c1301480c020551541806140c0000301c20845020a0f988070074100c0b0032101c0e0440742c43c01039524013205005582c000100c1384030107080144030172050400c0f4500a11259140c240c4c01040806507205490742d4800100b1030501c820300c40e0b0100c40603a0511021100600c4401c07100001482c483c0c0310711482c09140c808000d0f00042280381c117520654054001d81480000d8203081c101410441401c0c550000c0c080100c10150750601202c010190840e0b11445542d41c200500c0544000b10003501009124107500020810b03a1070400b090907440301681c07489440880d000083e0b02414400c072039280183e150030204001c2200004803c3c0c003c1036928401140d580e82c0e40308240d22a559070096035100b4400f0001400749010000d010384e54035441c0d40444030303a03284c040e02460018800120850311400c0d420820001c941c0301c0401001c92041d040c222090040c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 688767814 1250 688766564 688766591
    0x20f030405060f0403170d0b030a0b0c0a0207080a05010603050c150a0c021302070f1205091c050312090607091502060f07090b040603090b07030207020a1a1902100b04 73
    0x359125482c400c0704002110700d4a80307581e100342c0d802542d0040001c4524030b04155684031039000f140c940811286010b95040c494500082c0c26881c03a90031002025040d00d8001007a1110341c820325100c0198415643c0001d0400d80412100a202c1e0181d00001800c50030b5150079810008040d500c2845940c4180300a41c107294018215000c0d410315080c418248217840c0301184802c13038008000c10440b40301040c3c00091246841040e9000ea00c280c1c8164000604c0c0c40007034071240101c01c20190803407011070091195a1140d050300e05441d000d801101c0c10041002c01085c0500001c170340e503500c5034101c101404140c0340c009410070054900c0c103021909102001d0320003540d505c1c005126440800340240801e44103402211904080e1500311503c0381c0d0f9680340e0001038080c02d00040101d8005581c0c50001c1c81c4540700b03200b038070b40581d4010180e45141e8503151001c0e000211a503c7c1d411f92a508000c03511241910324096041e0500c00d80141c43c1d0407400412034011100315031140390045041440071080300d03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 688769064 1250 688767814 688767817
    0xf0b090f03070b03131704260316060509010209190807050102030702010f0f1107060207060801050a0f050d03020c0a260d120f020c010207050a21052b050c0a0f020f03 73
    0x245c410001000300410308200200c403482285055810100140210380c001c405848100400070401000030810000d40c8110741e03070321030080c3c00510201080041d0000460340e401c04e6800a40110001d403d0114480006601e8001e202ca100045894098200b00e590410b0000704010282400514141039140c1c00181040301248228070410124000d10404540030381004c00c0c50315082000c480c0c80d680c0780c41010f569050b03c0d00401c00428078000c00040da0f803418400fa40709842d83ca80c40211010b24003018032040801c4076004600750f00665a1003911515205443c0c0001c04829a03150004615454001c0300300300e440043c1111038101d114800e8005810260601050388003400004100700c81e10381c000001d0160314a6420305500000b548000d00c040000c6072458640180990818850910444a12101e80d06070340c41c0070a40c1400307014608003000804580205070250486001040408000110354040702c4503000c1100200b0030b01410396015203c003103042001d0006002004255408540c0c9 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 688770314 1250 688769064 688769071
    0x51c0b0109090b040b1e040302010609061a09013603032a1101020c0402070c0603051003051002090f100306090b030d270b130602192301060f0b090f03070b03 69
    0x340b0403140d010981b002401c0c510140071811030b03031080c2c441342072a1070001d0283c00c40d842180f9280b400c0420101c0c010203280d9100180303004141030680390961303c10042d24800a0443c0d1801c1008403210000c58404100328948807281c0b030814004101811850003403c4140707000c0b03010300004071400c02e80500d00410b0700c400d110700c2d07000b0400150600b040300040385044a107400045d046400454000c04014540000340f0682d8041e881c1400666544021813022420300d11010f1700ba03500c81007030300c0e000f500280d00400c20841d000d046070007403c45000109010042140c1c103040040d5507660300b004010614403e547e2040011001b0f0314600c455250018120b83c1846a5030074404181400142c00482404290004042104400381c42d90031481e41e900050110340301d028003600507600c48a900071100d41e003841d040743c2d01c181c41d01d883c01505054400e06045030411035010350f60f180d10204048880c100f5003c000d0005071901d541e51034800c07090044008244030f143d8081e9000030f1061145030321400079282d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 688771564 1250 688770314 688770323
    0xf0f05090904051e0304050f10080106080a060f031a2202040f09140703030e10080a02070c03020901141c120f030207060c0503090d020c0603160306051c0b0109090b04 73
    0x700d6200d43c14001c2c2007000342060303030203602d0344000e900e0602100840980f00b1144200d4406258026510500021720520441140003404031300060000c9401001155080280c50400085440e21412020501e2215410a5034518441c02d180141d403804648110f5000e04c40b40802d0103001020b10000d002807004107c020311454a075050781c810240340383c3c0965441500300b034012090818101c1e0342d9444819901050700028040c6011150f1400c080c840c625840140e6614603005a841401ba14001e400030714044036900644000000941c1e80c169020f07010305498540700c0000802c1e02e0400c0307101c0304002c4400601d01c031140d040360f02141b607128080c460400903040034244001018400c60007441010401010b90340f504070302024a6070310501031845103001c0c0302211552007000c2c5060760388070301140d078150340404108000380c152911101f001c50500002d0034040b50194681c40041d2500c0e98000048410414000f404414001554031680c0140800705080242e1411511a8602c0d080001c10203030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 688772814 1250 688771564 688771579
    0xe0d020f0d0f0c02060f120a11030a050705161101020f0a0519021804060606080606031003020f040e01020c0102030403031b0210020708070b090a050115061709070f060f0f0f0509 78
    0x1e0b041401200500f01e0b09900074029035841002410031a07054001c851008a05002d0b2030021704942d203d445821314015104120034159560b000c044800740c04020074280400c00309000c4041c01c3c1c01d454094945c1c040c401c8621078815031051000914007210410707054910303840700b072840d0b010901c081031081c204a0015980c80107001c03680040380c00c118a524401005d0b2107442c1c1008107000042d8000b0060756465594841d00740c8030306d010000980020b980104c10286100c40c2040149051850240f103030704040c00101d204d101c0f100c0d0050032a0442c40b10b00a5a9400108010401d607041c880c507490003c0d44001481c0908070007000a64030706500d039110085c0341d4005819002e100445064556045c0d00200d030140c1e5103099050075480714200d0000700c1c0c0540c2815002906031400c000090241c0e220b41ea1001e00c0c1408011429025200c00b5290408d1409500404604000c586500b140602065241d07440c1c2e8440b0703c14001c006c4103485180d8020041c1041803c180300d6400f401b2144c440d44c0884110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 688774064 1250 688772814 688772837
    0x140d1205090304241107060f02011a130c030b030a03031517060703020a0207170d030b03010203062b021207060807081306241806080d020a020d050a02060a030e0d020f0d 74
    0x151703011394003601010340910860500044071a8400c03404074001c038583d802404090100c0080348621074070b03554083e40c402400c40d90310464003400d9004074a51103140c0b0300841e0086c040c1c03010030b0074250360300e0044d000651038040c40d0305142e07000310070320004181d020032070f2038012403240104d500c491002d00800101074002909409140c802c100c0107019202c40c140356042d21030310399486555000341d40904008282080301c4400d40e40380c10f02c2900d00c500c05c090000d400d540040800040d035100c550042d400c1040c6102d040c0d1000d030f240c81b96080720384444e5000034072415080c40c00c09414000c1c010200c3c010071040a0404c46081004e28500c01140e50000c3f0100d20009180e080b18207074103d1041c01c07002040540740014480269520484078150040f43c02c001140d19014136a03200c65520b00590090307444203004000604107802540e43d154014001c1d500180980c1d4005100d95104251400000c0d0703e44080d030380580c909000f500c46c2d11200c0e00040600790313880c1d44510340300c1042130007810503c580c00010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 688775314 1250 688774064 688774067
    0x30402060a11121308010e281e0302011424010c0812070806040f0209090f1b0d0b0a06210509030d050108071509030b040b04140d120509030424 63
    0x240081c00407440d50712925a85206407401c4d000d404c0b44118980d940c2401e0074030f01c01c10f8012401614030004140d2121521000c0840810a046822011207840f68400075160341003614060b01588070384298004181005159a6190b40b8000500703200d07507141561070000d0110b90655162504585c080c04c280314807010074107100a95010700c0c120148552940820400c099921040545c80760404590412140c655058080220b007c0c59520b00e40240800c0003241400c03000354020703544401d070107000c0c907030b2001c0c001400016074202450351100240c4440030340f1041e15100e4002c50280c41c89103003040f9503051413003904030342940000c1031f048140e0b60760f0b000c10280c410a0044031180003c10000b4451560345107285560f50300c2e44c0c0318890b00c030030102d44103100140c41070314804100e0b608289040c00c00d456988038016490009007003140d601071286851000c07210180074900651000352030703100340240c000b0320342402d50b00000d02014103a04100820300a010707400c0c400624103504405900382c4456034850 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 688776564 1250 688775314 688775323
    0x70503090d1b0b130b010902040e0c0f0f0a03090b1b1806090a0806060a0b0313080f040f142e2712030f0c0c03020402030405010b04110c0f03030402060a11 68
    0x203000d80f41600031820000000040740541c141139108034503500c2141c1c2d8400b0340100300d002c0c83c040c041c801840d06c000725041c103102001810312040220035a901e08201d04071410120b43c4044031100100e034440e803003101405251901140d014016a5a240f0300c400c0e41988100148980a8101d0b418050f0180450075034480d8070660360441005806011304a44440405030340f0801143d095115041040700070545d501c20341c098034000c845802040148504c0ca0f030b1490b003190040400c0c1d034181002030000241300750304100c00303400500c4600c241d00c07524181c020030310410102e521544030613400002040f500c00980c0c0b440b0414444454075020b40051100300140f05e002101c030f5840742e8007031002c01010a21601d00d0310808440e034420344400c010249040e4080d152028522405800175050390300030009030425800455115108800000d03894417580005030403501c0c0c2c3e810700d40464101180c0301d580e00d0010090644141481c400850551506030b00080f0a44a00d5410000304654400fa0740f616000400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 688777814 1250 688776564 688776617
    0x151d07030905070b1b070807030209090109120509040e2e09050f010507020d031512061b120e0102040e040813170c1008040b04110d02041e05070503090d 67
    0xb040d1010303e0b5458880040da9045050380c442e0503038034903050782e01c0714100203134860490b040f042c0907080036031850f02000f0352084014400c00140d501e6045841c002002c418081040b00216243d0680396a000c1c01808100c030864540603030142e004031500c2a840b14014510821039400d0746420382e02c0c40058050f03070054004050700070402c3c0704062043e26241c10642003d48070f20016406c8031070300700b110542182514140c052061551015490606c000c4c1c2c0f4047c5255040c0740240000701d402000600e1a0a181c00311603c504009001614181c1881040e070084540e111800002035050504110460016440180000340705480002c0c002ca41065054130b08070041200c2200d6814001f003160480e5180c0081008003131007044259240506640500d10040c01075803c901900d8940d569641e07a810071400502e5080d9104d224000100e00680d40c1e401070241886243c0035440420381135881c039000340e8070054445410701000340200020b031580021900d00c132004c1031801d42040010070001501c41c0d0301d4407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 688779064 1250 688777814 688777823
    0x1020309060706200f0901050f040510080619181802150702210c042a020f0105010801061d2d090c03060702030a03050606040902070b0901151d070309 66
    0x200c0c400341400201d40c132503481070340d5000402c248101e0150303001545100c3c0082e0300c018804240244001944118042e0550a6400010b145040d40b580005007040a210b03c2c1c0798009490032007003298904082c43c50f0708104107102070244e18981041c0f41c07807109510203100e0640d256550b11050259541c0c0c17859000c8400d0b0050700703140f0301c103403408008549540b21800907401146d46855024641032040703540107014105d0000b03007240c1c490715010030001d040280c00400341a03800da8500c0c00c02d507004880c80140b4401c00d800801d41c440c04001c400c0d0950307205134808035450345005001c1040d44084007100c2c400c0d1a0400b20005c840daa28003103420500b0f4030705628500e80c49044401041d555096281c24001e5440f0800c5030f56420407001015a200012200040103810900034651864025000035800920040c0107030704064545d041301d0300301d811918094a003981c4110610550b20002e10603c0350421141c010b81c243d050074074031610760410008540d0002080f4400000389103621a0340900c800c42d602 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 688780314 1250 688779064 688779067
    0x10912020a240905030319030906060b0c0c0103050a05010302031c032703111614060702030604121b080a0f03090606032a080a03260103030903030e06270102030906 72
    0x114a6407082d4030b0000c00e96140412407074000815285000000d071580c41c40c00180b040c0100c07040a80403005010b620400301e99980d01d07540041445050344024041446d85030000306015100c030000101071743c40250090329004d14040c010700c096140400c00c103110a04035034100e02c00d0140d902c1c00314001c004002140d00c031824001030a80020b6050311003070543c10f0017560b640c00401c644100c190713260a40b10719003074910307a0800c504200c0d902820200003090035008003c242840225008241004d000315801c8901c200b4401d04c80f0700707094015800c200b091243c0071905090140b40c4c3d0380d80e0010705c24401030505001c0558803c42845100c0d41100700b605a00140602400323a90b4504410f0041106120080036000c0c040000c80401d03401c540c04049928550040c000f02490b601c050303d2111500030404911b51000074901e0b1000a014501c0380254400c3da9140b40b09841d41c00c000f0842212640e5240c480c59082000529001841c190301c0241c04aa0921205210000d070041c0d140d4402c0401403600a0300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 688781564 1250 688780314 688780349
    0x40e0304080d0801031a0601020a1203110d02041517040b1803161103030c100b010507021f030617060612250503070602030906070f0c0f080105070e04020405010912020a 74
    0x3884900181242e02c06c549001002c81e03680c1c0d0704002170104550203030047c2d00025081d00891014070356020310041c2428005507000b5400c802140310b40c480b0181c1603100c1d400050420003140d5140c1c00c000c2c2c45900e4600750441030548050182009070190000d00b00740c18400c0440c9550181a031414015501d2030112a507520b1100341491760581c05400c20385180d164680203004030704001c804c540203400003c0160010801c00300380c1200070020500c4d182c0c10040103000710001622044515501595070541d03525841c041d02400030140c60040e0001c4d0548040d00d0300d0110035040010754580c000408490101c103102d032501030240303002107031041d02c2d400f40081c041010252040007044410f0354400d41c19128200e0b00c0b008140d90701e1003001c0f0007940041e003c01040010401d50410000c50900c04d240d07030200307680e5502c1105051000340d0048200c0d07035520014003001d1030b00801d000445540035202942081e2400e40040c0807a0b003c0c0c8207411609502c034051604560718206d000c2d001c1c0104105d115112030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 688782814 1250 688781564 688781567
    0x30213150804030f020714041e020a051332010e060a0e0117071e0207030c06080105030d18061407020d0b0105130212010b0f0d06080d1701050906040e0304080d 70
    0x2c0d00c0a901040700b020b20307019650f01c041143e00590f22130101071124900c4003c03d20000700010034118400129100c032154000f410b900041003111215500e80d03850350710000c0c0b040c0c500d516990018404071140c040e4103203100c01e0303881d8400b9003005117a00002038211080058a6514031411181d62010300011b00b2044503800030400c0141d29020f80e41d80302d0160814000c0309580000341c2d000404590320f10200000440b66140f0000701034024415518010303a0380e60b410645a02c180c00070ba0200c0c2d80003005006a0400b0840070b03030030214074075001c01102e490343c01e010040106401088200504e03241c9130391000c202401200c03102e0750701802007504400300c0c0c104410a1035082c002c0b907101314443d091207200c0f00540c0c02034501c10345007000c40310510b9280c603079519100e134022062219503800a100388624a6180c1c460000140042d4018041e00c0e60743c988020071400300c0c00f03800d00001c200d4000510a9450b40d4074100e6008500b5980040d60440a018603441c500956004204a01c161034215083e079 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 688784064 1250 688782814 688782827
    0xf010f030f0504061b03050402060d0c20010501090507051c0b2202070b01120b150a0503010507090501020c030d021b0402090d03020d0305060405090d0f03020f0a0903150207021003021315 82
    0x42c03445d0503041c1c0c1c039071507410046040d00c0080c0d501030b44c403800a11144101d10b0320369014a105940030304024a012003040c0d000c40c6003030311f8105510305c80d9540b40010490804207010701517008400e45411841d00d01070080359110903413496610030002e0b0356042040c0c3c3e5901c404c06148481030000a00b0802610601030f0800039502804c001c80300014200000695064054540300c900c4d42c4c404050b0f2140c1da1212500060050781030080f0703500c0318a540002805440c280b01d0305018180079600c40c01442d0502001a02d41514800058000c1d40081e110800e003c0d40805c5d03484018282000c4c2c0c40340300c8030410006c0c019001d00b0921503441010019401c04041d000118202052040e4406016645d14002000121041161071051640114100328101c1d8031175411940010740c0b506005080c41011014183e1765007005681101003002440306000744494000d404076019810a070952400f80d041d070128031020412076042040c90380100d020f00c02981d0503d0508044c0111145141d80543d031a080103001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 688785314 1250 688784064 688784081
    0x519180507060f090b07030912050a02040501061404090f0f0212011815050f011202041401021905071a0c0105040602030a0f0509060711070503060c120903090f010f030f050406 77
    0x903445081000280b46014000f0401440400d80340d603002103180c454092140c0c0d01001084017002291000800d40b040840010000c241c019002044501018030601044520680151007401403d20b03000b00c071103058500f11000d40300002000b182c0d8620820005000d04a40c1c03500309134450021540b410307140103918030340341201c1d40309145580340d0111030004400c94018040c4618070702c0003900d09025a06184900c0c2903e0035040c58841e80066000c031141d81241c03c560048100b4103c1116240b100750703810080011030300758402105013140c68681c0e034966100054800c40c0004400741d1000c0c1c076180380a005a5a105403150000e003d28a89450040d00960040745c04081d603510380003030800c501800c0d11505100300e940b1307001851542c48010341a9905071010300c00e101148555440880c05840504c0703420b000e0034a0008107a02c4854811038400c0c0100d000304144904c1e030081c041c0c0d104580d02c6800350a80502c0a00303041a102c0c01c180400c60140c168140805030450508040c002003201d244e100544 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 688786564 1250 688785314 688785323
    0x4061e0509030f09011112070c0603050106300905100e060f070c0f050601300312020d02071a010603140f27010c0903200f0609030a0210030e010b22051918 68
    0x49c41e11500140c040b12000e00a41c030000e02e5035010320f620800311400c0c0070091210608900005410301b220082502e2a041b0304881c142c0040803120034403101d40c000d02d84001450809050070b447c10b0004004074040086c06542048210079001c03040c41a07114100213065009000d0720400e60b150400c2010ba000c401d0301500300d50761920b02c1c441103c1e01c08000040e9240d85940c940101a00090454000c4d400c4540002c605c207500300803031400903c2c00b0101d00c0c00501103200030340003980f41a10141c1210442c04010004480c0e05d020051480c4260780305036445001d100d1400114000598803003020804000301e4a069881e05480b240c10a40115804c01124840c0080315416511030207407007443e00c41040141d8009800d0510b8015030300c0e040340600310441018080b100256001d8001403042c0100c0c00516001ca581d0740f40b440d2804000303010b1001d000c1c0c41910300844071000110090b800e4104122100203255175100030072032003076070340d42104c0c50b000e1001c1050180b0b104025184014180802d02100d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 688787814 1250 688786564 688786583
    0x1d090f0411060c06340e0a081f060e040b01120303091406180f0c040e0a060504290112060b01020115060e0111010501060f050a0e030604061e0509030f0901111207 71
    0x520510803481502c3c0d6030040395154200180c3c5c0ca45080c0c50182032205060b0348140c01c11800f2036004c1041050503150400d10310702403007452011f04828100d400da03410500e11807442c13200700000709162440c0641140c81e80c0903c941580c010381411001480f40e40001004003440d00408400d00d0400144c0d9406800c001c107a02140b03d000c0004199501038042c5096290b4000d1041d0402c1854294802140703150708a0030384080741b1040e0b071410110b4904480c00c89000c06500501c50306d00310200c00c020b100b2229409130000d5541440008050a092070f10001e20303070358407644c00000c140d10139007100080785070707410071601038540f9100c0c05031214504c031220f180001c08016101401c1e00c01400b44a040750722640716041201d4a20340220b443d588940c48560500c5042030000c01c0644040096900c5103005190014060b0700503008070241c1c1c208140021040d03410324090100603603021080314819015024416500d91031500140c880150302c0340781512900890304d0f0446460300d400b008086152107401140e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 688789064 1250 688787814 688787851
    0xb0105011b030801150207081015060906080c091201291f140408030a0203030612060906010512070f080c2719060b0315011d090f0411060c06 62
    0xd20041d10404020300042c0c00f0000400c4401da808012110b28403992041d144000d8480220b02e1070300e580074110307181c1c1959170070303000c240c2154001c44003028156502d01000c04a10b0800f00900084014180c1e25480d0800582c00100d0303510320803068021041a8000e00842c056100303c45080d250750504800400642d404459040ca403403e01401010070bc0980c41c550034400c4c1c1c4040380c1610718001d080c0714000e410030010408500400141c14121000d0340255580d1410304244a240d1044003a60100e5620940a000c3d06020101d56241582d4094561000d9003914020103441c1c14010b5024403240c1c7c40301d0201290201c00810500c584400070395120021020245064400b009081d540c84520b02c115004549080842045880000360b115808601c2a8441d26440e5a980c4140c2e600c2daa24115005208920350b0464014500342d450341083d000b5501c105030200b8001100109036041c8525804000703000c06c240541000c1003c000600181d4072080b0040c07036140c2e5000f0598800c1c450034a8075488 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 688790314 1250 688789064 688789097
    0x15031407030216120c0c0321140a0807050918060913020d110409020a060c03021606051b03070503071b150e060c1e070e0a0b1507061104030b010501 65
    0x8844204850207548035802640751215400d01c0882d000020411054112500c081b80340d034644913020350301a00e07440460002c041c2c646c5d043e442091200d4070a1140f250900540002d402003514081281803c004141c2c1e622440c040742c0314400c9041da1036016981c10041040800200d284510070707003003920300342003a4603800743c9045004503020000750700c82e040200745800a01d920036072851140d4003400101c0c04080585c009510400c00d44c024070009044a5440720506a0400030205c414002094003240305090060082c50b40c0b140c580c0640116032803400c00460074000300125400250440285c944415240c580040045c404240076954031015801c0810750070740d83d4401c0700c00003410b80c0794200e0038441c0f042404040c2c0c110078920142070140208480b1200610b000e0b003400080030070064000f00c0c1c10a540000c16035009400c045420380b5100c4986d041c6e4540e091000c3d0b0b000102d0500a8075405146003d501070243c240340040035510100b400000c000400714068180c41d0241c0b2001900780f0380c2d00c40b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 688791564 1250 688790314 688790317
    0x30a0e1906050708040504020315030c0a080d051b060c0a1115010303030b06070501050703020a031406030a30030204030309050301020909151201180203070501080c0d0506040204150314070302 84
    0x680109051100340d04001c0c0601410040900c240b00d0007019080995500c002004c036001101d44414101044024008614081c040d032040c510040751980113460400d80b455a40d0f444c581c114805100b40001c070f00c10941084500c02024442c00d008076142c40c40c5c01d42c0017044d20303000700c00ca800100d003402515403010340c0701003030070604010803040b1010581e00c0c2d601c00b1000380c0300780314130650049020028400494800e0040c82c1c0308803030503100541e0711741403084014203c44030211074416000304c440500000303940c045810041a6000b207203e544544000c00e90a620030003d1186c0c0f40c0b420058030f5002d403800d070076801030300490b4000e845000c4481e6490051600340c2c420809003941c44210f0300002004004188104922604d000d00f00307032a50b651007036003242140e00e000c0301a0943d550b01d80ca000111703d0100041005081e007881c1c6060f107418030021001d070318000c0000c1100c903543c950000940c192038690640e030040c1b00000040a98010b0480050300034101940189092101d0000090000d8003e00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 688792814 1250 688791564 688791589
    0xc01090614160807030506060702040510030b01120506040b061c05060103050709050c031315061403010f18060515180912030603030702060c07030f050d1b020913030e0a08030a0e 78
    0x710b030f010060356001412002407500800c5142d203c0000d001c9400541c0704c61054510407541703c030340310543c0e42c218100349a20020507800a500101c101c40781d040003810200b400c50304a940041c040b03032a6203440d4002401a0b2041c400d0950f5002d43c85500400e10000140d1141241d001d81c00b0b03035500d035480c0c8090b80306440045414081e4888204086032010040081a140142c016a1a000001e03d54480a0705580203070f0300001d00098035804040c007501d400e20485802c4007072508100100e00c041154130000d2010014041c0403a951070380010302c01080c0e0070701543d444100528842c7c10003003100b030740c080c90f1000ba02c9049813403144200f061034005804003101e0103400c00800071400c08520b5803c00c44c141e40803d0a46020b40648200080020f04415207408410b12500c054208001040c1004281c0140c00c50400c000798402a030600c00358980c0c401042e04800392202000d511455070030207482c11043c014555070010103911000403061404400f0b081d80100079941c1c3d40344403424200300300007840f002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 688794064 1250 688792814 688792817
    0x100f0b2a01112206201f0c020f0c0901051203070f0605042021070e070903121d101b0605150a0b0a081807080309010f03050f0c0f0c0109061416 63
    0x500785141c101e44041c0d01414017000000c2151200c100c0251501c20042d4214280390840e501d030030b000411140c050269007100d4403104001c00b84465200e000461081040c82031a01400c8001c01c45405d0303850600455080710f401c000c0c070f44166101807038082c00424045506989104451000001550284440540c01c9000a00c14001140385c440da60b1180e04035140b40280c5031169410016070080300511082c0b00e07018507260002050b1440c10302c000101684041c0104000e030010264201030742e0586440e9822000741e401544015103010156007190009541000d481050050103007080f200c3c2d007201e07226144000719440400b1100d402c0c04211985405400d407212002e020010000703100e240380030391008544527021411110b508400e0b040c14020340000b4842d410005c2d0303100803942c02c00704881110745c071031504114900d045d541140300c1100150030201c1d03051001031130000245900c0c05503245c5454450081101d2411072420500034015030141c65400f0610740c00246201010060014011806 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 688795314 1250 688794064 688794077
    0x40e060915130506042009011403010605040603091e0c0f050a0810020a17100603060b030103051c031508010614011704141212100f0b2a01112206 64
    0x14100c10020380030040042d90410386d102071407115800c094035018001d004003800d15075a0215500014a9005041400558068100010440300c0d42c0700045400300c42980c540001d0114103450141a0b005031800244d4200118800290500030240c0c00f2104850700c2091285070329984200b0300400038454410b030711145e000746920400030700c031030340041c181c40c249864004030410250303c021060200944500c00d00860b000c006103c0680c143c070588014041c0c120381c0908640c990307a18940c0d124000507011512039007040d2200901402034010120500c2c0c5074200303103034803902d60824034000d121510406000d144542a10358003540240d070202e00e4038454500c010843d643d1521000c90300e11201c1c2c0070444500c034250400580b20b1000020b40300461a00d1000c00550a1840c188181d5181c80d030014962148044400c0101d1403822007215000d80d65401801c0080041c11142c461020b10b103402c4500e50750130000100d503103485050050100000e1080b000003640c18036203000440318814000d80b80852075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 688796564 1250 688795314 688795339
    0xd08090714060409090f0b060a0b270604080102090a120c032603100e070806010f030b0406080a080903071d0604020c011503060506121c050702030a050102040e060915 73
    0x2080450552100c00141c03445143c950f5611a18045942102c81510003507500c1c105501003100d40c0100a030040002c5a10652080c200315a0360064032030101d52520b4078003460340b2100b03501e803007403030920303142034000d1055860715a1540b95502030b5000440c52840b42096020100d80c00d6a099420f4544640211f4034104444c02c550314030112150710003103100c2602851a40b2510411038100452103040300c0c052810001f4549581d02c01a268050800b106000e0150100312207640d00641100fa0350740c0c1d5150103e5082400c0c00030070300600c03181d0842c4001303010302d20000040c013160030014440440d00360110f441582e502e011410000d0b1044591000c21080c40b00811190701d881e8010f07200309114803000082a454001c08008607011030741c03080b1a410385850070009680b41c41082011070340000c0015040780030b176004440e44c1885073b4155500c28804085541d00c159101007000741859039108008669660b15882c469154040455075540b107000000b000034840040c407001c0010340e403000340807400c0da00d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 688797814 1250 688796564 688796579
    0x30908280807051203010308120903211305031207020c0603100e04031b0f020f06070c0e07140403031205060f030a110f21240121230d080907 62
    0x500c00030b002da071a48100030300701c0e40040c4c0701d0f0300660003580b0a0026903521149807a026100303100c010050b00d1203810500c071050200030007c2c81c4810f480000d0313114414ad81e40e80e41500c9800e144c174250143c00ba1001142003107016140b400e009000c0c4402c0e408032007214206000300010391004840354055491325010070007500001404190300310303104e03091144078158078000d44101c84800314401e842d1081d0003003c1105504003a1500a01214141d582d80c1c582040b0303803031b401e1001d0707800c0c8030303480c580c8024030009800d45200c0c1e0402d0100c000d00c440183c0d940c96903414018501841101d5030307101c070381c600700c0419068500740c41d200f000b5070f0014001d8008902c141d01c4010421031b0b8203c205822603882e0754050060340d9400c03400074841c1503094115101300505210503180140310b01c643e481050f2401581c0d2079004080045e41c1c116003459180300800480d612464050f407003809402007103550f08440d81900400030b02c05800d11100e6440880b11650300440d01158141005c4d201c01c030f4203410241d01408641c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 688799064 1250 688797814 688797817
    0x80606032a10050712020105060d0219051002100e060610031e060f0806010f030b0c0705010b0d0605010e060904080405010e010905060a05070c0b0306061804090209040309082808 78
    0x6003251560044807040741c00858040e0200805030400120001010010441c94003007801c0c0040081c4000c00483c90940085038007642000f1000c1d120341550121841c0605060710b0300809020050301e107141c00701820070085e540e506901140d45005081c00d0161031940400150541300d5400200044000e5100100a4005080c5903c4200d5548200d80b00c1034402c0c2464080c04008100000c0344244039454020054108a07041c2c00c603207050740e5000d0301040482c014000c01034110101170310f42540d806540c03800030b0051502c442407a41144107070750617609100d2150300c500d04890240403440354030b9890380d007008030380380b01201c000300480d82c188000d000ea5446454084644481070401312002c40c0c03981c00041103a0000540a00003800014003001002184140b031002009104066804d608052000440c580550f41001810005040303040c5803a41da690071003501c07250060200b04c2e01d8200303030a005108040324094030440d0b10441140300200c105442100b51010302c0540d0380f82c00000280c2c0c645115 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 688800314 1250 688799064 688799113
    0x807060b0301180c08190c0b1309390210180212061008120f0d1409010e0607022404210503040203100207082d0d0e010608060603 57
    0x140d0340e11041605a0f08000340d909003018080c441d46071002d468020803504d0071038152469502540030b00000000038000078250b00c1511940404a61210030700c5184084014165000130900d5090152405800a0b000d600f4541c0b940945030421401400e440301504250402280c100180c0c8114010310065105900c84138000d1a80030910302346c0120f903000036150341a02c10210406411090511110b400c524240600426110010b841b02c8021310b40140380d40d00071100b05480310140090103051009180d404443e070b052010410405509280303900c0e5008141c10407603011b00b8894040880e14040c0002003410301c1103c00b00714114a06e0310900f02e20155500508102c50000c100d940404007409020000e44001584d0388e10302c0c2d00c1e40340c24010145032110781c10040540c1c80c810003480d0b010a07450011a91140992000524400101e02d02c5100a14030303610780c5c0e540f1020118000c1c0d52000c2039004002e800d00b0001c000d10000f51191080d40e205ca0b01900c02940c981c2c0444c200b40318104414124801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 688801564 1250 688800314 688800319
    0x2209020403261c020d110c07060809121608160b0609011a070204151211010f09051c120e040506040605030d1101020d090311010e06010e0a0e210c0f06040807060b 71
    0x1060356444a410646e070b1000c20030003107002c001c036808803500c1040140740020003003894581024140052410340310320000340c444001c6100011601108690b145c41000b410398882c50301c0f0341d24590349182074807862243c0700443d80e10101c0c0d00404d01e14600041114180c4861401440b0700c41042002001554401141240c02c1078a5501d401d0740c5e841c0e9100b01c0c400500d40c0c2001c0344d550915502d03010611000040090f410311039247c8041d04001e5008242034296601070380d01c40820600d0803601c0140510004005106444100001c412240d100b4000d4010c001e00750303403e003c152030781030802003591101d008164256100c4000040c5c840d2045e1100400003900400051030070b04280203000581b07201c1241075021030364000400440d01000d2088a20a0060341c01506075941040a18096858013410280305191103044500d25286c041c008a442c0030400c0007448014550010500081d0304007000c05109801244144041d10b240403a43c0c62040e5407008142d440c180c032565503034005068a0b404a074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 688802814 1250 688801564 688801567
    0xb0d0903021203040b0603100e0a1e06050108031902120909101a0712030509120d060f0e1608010b0708030a06030b04150c0c02030303010b2209020403261c02 69
    0x4030369000350b00114011030203008001060300c1e00c50207152622803d443c2d01040c10b407900143c142d641c800401c101c101c141c2e0080c4510120010701e0060151a010554041c01d0f007443e00000242d80301c1c000005042c044100c03405550840703aa210103030b84400038641000d96588040041320f420b440c000080c01e601c02c0c030001e1070030152526282030034444408603140402c4101d000400506020200c14980400320303262600740f003945803e4203840d45032214404000c00041001c92940d401258580041000c3c0c520220010082d5a0303561100307010a50598520710701000b000f42c014141c9100d070842906845903e603166140030516641d1254640c801031448011a035034140c00f100144015180a0255014880199003246003085007c22a10701c2c01ea140140803041c100b0708010388000c800d0340e0440e1808200c1d070383c581010200d4001c8006640c5a0360401c0c4101e05000320304907040d68003a10540c3c0c040d0031980c8006821255044525920305088c03185c48009000da215900c44000900401011505025 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 688804064 1250 688802814 688802833
    0xb031603080f0c0d0809011104051804020f040e150c070c0b1c051e090d09030f08120c0318010b0d2a0b04030b0a06030f030f14130e060a0b0d090302 65
    0xc03404d00c1000803501d400900e80c80c052105518090040200a4481d613061516061800340010003901c00340009100d1071100c1400201550355280410a003103030301a0060103074003031034919a5210218030200504c04d0705003038081307114000310034142e82d0829888082c18000c01d0801040036843c0e0081840200d000c900c42d401002180c0d81e40c082c25028500b10f600e4203003c1c0f10400d200f4414104024000324072a407040c0c0c0750350b0b242540450500300f104e03044000c0c0307004541d06003040e0305680310300c100c001000c421481c00d112501c003004000f14400c00d10b0350300080154000071811802c0ea254103007240d80c001d440d00e52480116054000280c4180d52060300030a002c6e03001600b014100303055600c170109450000c60204140003402070b000e6030080c040207040020900b1a07540d6403103480d8072040030f0308102c007480200b50443d00a00c90607080a20946076140c075001e1164403c21030001c5800781e00b06410010002c510035007070100c140d5007a02e6110b605241810507051040008201c12035050381144070340c1ea5003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 688805314 1250 688804064 688804087
    0xa091109010c0c0302060d0218191503020d05090c13051302120313061808031312022d120c012003040504021801021513080a0908030c010f0b031603080f 67
    0x20420195070a01c0940ca400403690420449c44594403100d0007012410f041c045a20541e030000c03c1504d6103004414980035001c5000c40090044168400c40f191604d401d00c04548000246800c0c140000c8680d40024507411113108144d0310b00742c03a2802c6000800440c00010b00d801d2440300c000c2042c1c18110b900700100740a00c00315444c0d050b031115020034041103d2040c6c4003a0712180101921150005520f0700000d042c2e83c58482c0c01604c04c0f140d041580080c05801c55403401c0d40303100140b09800807000d6040c1a541c80314100441006001d20450440305094985d0030701041074081c50038140c44154400000d02c000340e26050030300fa803a07400c9010402c404683c42d90781d480a080e10312404003d6003000c90205001a00d060210310080e080070122104102540d2300b007110a0b509030350721140a0351207408808069a00c040b83d0b40244102c2e00000c1071a40c04a00154805078440d00c400e0f41c05d0145c5a4030341d040c13507107131607000c9041c1e60028001141071001c9000324000307240c40070b481040e035031421070000e24 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 688806564 1250 688805314 688805317
    0x60f04081911071a0f0a05120103050102030f24010806130606020a06051503120a0e0406031401110a0e0105031302060c0609010606091508070909020d0207020a091109010c0c030206 79
    0x55004140b075034070102e10740c010412508020f80394031203103c80c42d00354003113881e49540507070800703e809000000350f03c2c84080d21840c16140ba10341404190300c12961285000c5003c0c0d00304903410b0041552a1000810301407480d80c140c100d2462030035040556040c50401101d11510007482c86800100c1c12144a65000c0070388a507400506140d805451441c00b1f51400806992001c0c20b10744441d0300081a03501c4a0750302107584000e02c500c0700f141d40ea80e401f0302241540d10903941120158014a80700f00081030011035030a600c4c007054080c0c002c000b03142806c884c0c00c02d00d02030303005030f840010000e081082c8907500401c0190380001e8202c0c2a6a96203c050f800100d49a20005102c4030a401403c18040101024002c080240c001410003460308c0e41440c44400218100e00c00c080100660040801d41541c000d4001002030300700110305641d94070762599000e01a5110701000c03409213a00160000701b040a62190030220704022262034540031000e401111000c0d46600207490440d03c580b0700100581c0d0303000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 688807814 1250 688806564 688806607
    0x30409020d0b030309090c0706150b03190504392403060e07030218151905030103020f042a0207030b06010e090a05071b0f02090711060f0408 62
    0x148003581d26030070400c07044281d600c4080b080c0c0c000c3c0c1c010300004000d66074200010781e011081425083d200c5045080000141859500b08200b020100b10041070381e0070508001c0d40706034488028a40320a95000c0d003142220022140507011189034001d02c500c41078601e00c0b0307480c0039024003184450090ba00c0029408048603a0210034160220300c3d26926480008901000c80758560500700021880d1410f5600c0b1000000c2c024020194006000300e510440516905c2c1d42000242220b1200804040c041c92242d0150071040071031213009084070809441101100d050701d9000d410344003540c1ca41c0040c40003a2000d480c039412500c1d03440642c0c0c0030100354101c0303007540301107154014180c1c6450340c2482c00d40c600340602580e0410026103c2d03140140c41300400c0c66013194880350006110b54610404032002d40e00c041091540c616581c6400301848551146104440e000729141080da44403d101511451480800184203070806c1c0300081e04003e03036403070075640180644040361610800c2240310722400d20381c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 688809064 1250 688807814 688807829
    0x1f0509121207030e06270103092a08030a02100c030227040b0405010b0a180503070f0306060915150e1c0303050601080702032b0c0f021218061b0304 65
    0x110b00c00051552119800281c908145c40340da1408482d000b00d5006d00100b80d440c0c0020007001c5e5841301042c4d100340d21240d0070a8100c1050620b584d080148000c7c403406e80215a0790072180c240c00800c41c0c40000c41120344020311a0000c006401765100508098007140c000b007070501d42d09111b2408a03e280d03040c00d481c59902c1c1c4900303082041072002000102c0c6c0c04800743d03078011480c000050114012910482d16000200d05111110102c0d074400c9039410702d2160407440e0140110a00054020500e0045c1020740f4401c04e018452a610b07910004211846002c40041034080044200250040da070b0143c134000410b481d0822480c0300100c01301d003103503c0c650b80701300052005410762000d05603d44107564214009181c040124100450000d507640170302510b512031140c00e000c0c1d040b000000460305207101000c029040c40800d11b1071001130003400e12021850003500401418041d442c0e4401d045079503002465142c0f660480c1380b0400c0c09031940100f800042342901c2c4002c400507404081010780010001c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 688810314 1250 688809064 688809067
    0x6063001060915290403031805060c0c0405180c060d020d02070c170c06031f180207200d12030207060603150b0406051f020a0f050604111f05091212 65
    0xd1400388032001d055129600c41114030780c070490004c44043c03021501143d40529003401030611107841c00500720141c0e484107038081000200d9550401002c0b0b0641c00c0340004590402090b5120819821350398501110704100c1d4004003035408862a000020340b003024030f030300701c014240464516444100e900880c0c003030b918200308000811803084d07150141d416003145e000c094118558200301080c240d000240c02c520380709034203003480034803020004030200040a2801000103c8031000d000b200c000d42c001441600c44020204101c2c00d60324080141c0d86403044098007941071034001c0d0311001c00c4030003440d11a2080503000c000743e6010031314034041c3e44051401440300025508200c16a09d04480d0a01c44481c022400c0000410443d42c4403881031141c20307c00c801c030b8603151600303040c100d00304011010020002c40c10207a00000f070201c0040d820388250301c11030700c10040701f51004c1082489829800ca41c58100142290f40c00c40501c9200034003c41790000d0500300600002101c02c504207a200c485400d8036150 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 688811564 1250 688810314 688810319
    0xd0c090c0509040f021c020a0e06030c0403120809100902220c18030201050d0c2303041509050c010f0519030e01050a020f1204150515010206063001060915 68
    0x3e1034440c65202e0041810218a03141c0158204440c0503001c0e2042c40d1303800da01140b1a44003a01401c030000c03a03650000c0555540e444d10480703a64027500140002d9881100c4144851f07032583c014144d941c040c12400e0000d01d07050003140c1e11800645840a002c07600b060140b400041c0c2081c010300280009a2400320108141184040080103003082d080700090014a156007003000d41d0b0000100e52015440c48004a4144410401900e031040d0003502021101e2100e810884018440ca0240d80298072030305425590100d480341400541d001e001c00500741f50040c000c9440d4542c0140302c580c200d04020b080950800c12000c14404e18800c00c16481c4001c41d45a5400211b160028481d0036800180214114140512450a0015402611034040500740038102090520072405419210000762420070f01080c64581541080c100445000e10301602c02c0c0800702d022031a2001f00c50440d80707482031045ea02c4041209698071000140b000b80d800325540c0780340101c0d5010f400d001d61180d140b00d03400c0c0e46000c42e1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 688812814 1250 688811564 688811569
    0x30317040503040b04150f0801050f010305090c0316170c130b0f061902164e0b0f0405060705160203100606020d08070f050309010b0d060c2c0d0c090c0509 68
    0x307400601d8108008c00c8500511550342c03041080c480482081c40d0010f855034407804650710323100200500c0c81d418840c02c43e0780d02c5042c209100b9030003520322100012801c0c050701d0701034942d511450b5080c02c1d4412400f642c0305c0750545090744031002034031008003040c41181c10800441c4e041ea001d5100b02141c3c56000c100c0c00a0250100401c1181560030000c00d100d803031402c00710019100715084030031600170803000c106e15101e91700750194030a2008801951200c00c4e41d40040302d09400408422503c9680300c2c00000e039480514428584500d4001d40070382070a548800084034140d001169191350070007003502c03800160f11304100c5401c0202022100050450030440b010386041000c403081d000300040740c000c02081c0e0303a201e0b440c040c445003142403d503181c1d201c0b82074040c050700320303661029040f004030380301c500a1201c960481c21448a80307880d032801410b0104001d048c0086519200308000c071207001100700c50700300b646803107034075600851070b507803840747c9a88005056400744092000028000f00d1036244ea071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 688814064 1250 688812814 688812827
    0x90403080a0b03031c0b1504080715031a010f05160501020301080c1f1b06020307090618121203090f030302031b0702011d06190810050307030317040503040b0415 71
    0x180b038202c00450a1070b01c1c4c0c00e00b07480d050303500b610011010b64580c00b076500580c0754002100e54900703178640703030756100d54813040420b5403001d051048400030490a03060101d403502a02c10107084180015600700c00715004001540d0107105c1d07000403810082e041041c0d49040c40a814918000c83c0b0030340015950b540b41007000351030524031001c3c071031040c07004110700c80306404404d046601c15185814000b0382d031042081a030079140c04030700014250a00010030088450313480110041510b07255106d0700c3c40c1c141d103d504000d000680780a032000c80009862110003082010f40c8aa240700c40c0e5150109560200395610b011240306014210301194001c41400040d050f050b080c841c011f20a00c010b1414516a03800081490398000502540050440070300c00e142d840314022204080b0b081000885507003413041c03004000e14400c82c0c09116074460020041243d00d40803c06070201c9406903284600082801d00402601c03502500849080c401040000384207200403000c0c0c00103100c010301811f5162003040c0d016048 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 688815314 1250 688814064 688814081
    0x30b01090203060a09051009020304081b0316060e010f2f03130f17130303110615010503070309060c050a0e12030a030c09210201180e06060d0b090403080a 68
    0x30280180200070a64890214030700032140f210001003901d449841014648002d190040072082e4000030800041c82102d038000d100725044808610121007007902d80c1905c038020b074103042d50500d00300c0a542002c02c400e60082d407590840301d03000145101030445840201d03090700c4030610002d401301c0640000c01c462080134040380090142d24503d035140110942200030500c4000034074440340210907200780500c8980100b51039402030801982c42400d14001e400b64995440b04a0025201c0382202889090100b905401540034407824006002c121006466641001744450101030f61741c11440302041d4240a05200c2d2a130300d07103a481d5204240040104200b81e2031007001c0c0142da42000c00322050350000100c4000b81007510b400034045e13049a0f0101c600e541d0320780c016a44d001d10048801c2030784040510250204e4402d0300c805120003240000564068960f1140300072841c04000014050304101d002030050240c0704030005882e400a000080c500f070400c2e2400e40005a4001c100810b0008502c40c40d082e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 688816564 1250 688815314 688815329
    0x31e0d0201091703040816050c0a0902091e060c0601090b040501090902092a040b121008060601140714060a0b04020708040909060225020f040605130c020f0d0207030b01 74
    0x181407200d864030f01600f81d42080000d44036034000009401e000c80d4000756115604900c88901c0f070290321307007443d980d02c1101200c0503120b482d82800000d070505c8075100321022044060074420200036606121600c1e4130b80c0d80304072074005000300124000d0840a0106a000e0421201c002401c4900101404202d81c0160000780c02c2c00d00e0082c80a025907a072010346a4040003002c1110b00b02c181440c1101c0e800641000c6800d0004030100d008500c0d22485405003030702d0081c0c202031710100d917a00c0e1824140340d10385105426198001601180c15035118541c0c00045075400b2019519101940c0d03555819254040e00300341c119040300c01440070711940c50280408a2404072415400c140f99511262610304c203911800320b41d90b58071242141007040940650302580e030403200004c01c180c40031070004150340c9101d1040b4070580e0100c02071620341c136203441948150b9030064100e10348003040c504a00002c1a01d441e2035020f601c22158484418042081480000381c0e4030707030103802402d01c6d502e003240e155072041e0000d42 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 688817814 1250 688816564 688816571
    0x303141612020604030813050604060b040f090620040b0f0a0302121501021006150507021201051f150806060c21090103110301060206040206220303030e0c030105070824031e0d0201 79
    0x6c502c0c00100c89d07810540040300011202c0d5a00000b03402440d002e0000d00f0820705100016052101e00d034012441c2040004180705150b52000207007409104600489000d00d60a1100c4031044c1e02d03450280c481140141801413a1075402c0c284e41c00359200844400c404102229006401940c0c1408544a03840811006018181c2001c80b0a298410b20900000401c0404038116065548045120303c0312038a8400801a509002c0d20103c8600070f9000020b01c500c601035000202ea42d134480c2020485551503403200c2c16a01d51004102081d44484843d80f0b5602c2141c03014114100c40352050100744004031040341e500c600100014041e1181030a00d24480c00c0d0a0004200c0ba0341c0203c0c14a40c07040d8125015035070707600401030b070442c105002c000311422070442020120406070158480c10030500e50780704490840c001081010b003a600200c4440000902e01d5011890021400c7c0042c1c004147c910005400380800f400403903d4041600d11142548409160103c1001418001000c0501c2e42d8802030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 688819064 1250 688817814 688817851
    0x9020f031c030c02150a05061203070b070f0c020a14011107030f111206010b040f080c030d050903100f090201090e1506070309050409060906110403031416120206040308 74
    0x490040c22254112090580703503031000b0b1820b40700b4002c054024040300030071040d508108000c00300418049510398003c1c00e0f1049d030654405000010381d01c1d82d80d84030318400b205540b0340000725a41d040c08200301c8180240003050780c00580e610300c00480038145000249100310a080001084480c01d450442025040900c040c0042404011004441c07034000701000080207840c03000c500717000900150b025040c010000003050782c403035520091048400c002d0000042580b5045e4003070311541642012545a4400501e01e24214010b04c06400341c0b041c02001d0f1550046252251402e817030303010130b80302c80055640350088219038016001002038800402d00303200d9072400d00078500807813104175031042c895140400c00303104140c030840a580262a01410074420740f00c052805002620800c581102c21504051551484040043c10303602180d405558400e802c000c80c100b00180d9a10503401118051703040742901c80440e00c181d54041c01e8180c030340c2c000c0080745440c0c01e00a08051025000311030303010f00e0310580c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 688820314 1250 688819064 688819093
    0xa02070c0909020f131b050a120908160b010f09020702031b0609042a0519050c030702030d050304050d0e010c120306170d08010503030316080c0904020d09020f03 71
    0x90400e640d016640054403030100c3c000541000c03400c0c141c8540c4540d500e40d441300301800c65080381000c1c107100c80f415441c0080d004005d480030300a24207140e0001e000120121800661a00400d0380d441c0251809450b01102c80030580003101c07010401e5800a00c400010041d101a5078096001040c9144007142007044650000e0340b20340c003204001b009038419804e000d85603070310315003100c1034110024400c01104072648241d401d640030464504540040f45001219440d000700c0071100c1d51208800d05490301603800780195925006110400310a200030300141006131020040503607106829211240c503854503290252418850780f000d0001c0041c00e945c0d03080140d8020b201d030300130a50300411031035116412402c1200200850b6018bc108208400443d031b0700400d02280841c4203525991300d000603603803240d007415520712058608540300c0800340709108405100311a41604284000ea06030b01c2c1940c1c07140080e0590b00241003205005560741692000c5241c210444503060b0420b401a12064100c00324 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 688821564 1250 688820314 688820333
    0xa17011203020613140703120e01020c0102190c031502030603160302060f03060301090605160e03011104090e030c070815160e0f0109080307060f05070c2f0310140a0207 74
    0x1c490004100d480c40700100610651109405c00e2030200712031860307640e807c0941d44003a034182c02d134000c10a401421401544041003e504049041e0001d0041050b04c2204000091343c00000780c400d80b0300c548001c000038051068606c1c0c580200f0402684906101c8205404d00000304526007000340d40000c02c10060f110f90f0182d401107024054290b0700d9070782c0c01003c41d0142843c52802481e1514010400c508620303070790801140c6034990303510799901d1400c040515080f21400c44070114000024407040100c0c0e03200b6040121911a69003c1d0707030400492406003440d145894200e14915081350041425840b10600401c0d4448100303040741414403c1040003410f905001640f45000315045851500940d0003185050b00030030071301d411290303540c060381405802860403450500441c0e0038a00421035040c490032910003001d40014036102a0040d00031f8403410b107944450080200d0024190448085e44c007480096204482c0c424040307081d04041004000c5c200d0300a0100f01e00910601c90140490142003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 688822814 1250 688821564 688821571
    0x6150301030c0918050a06140a06271d060105010320030a0b01020118061401050d03051206010e090a09120801081002210907091404020609100e0301020a170112030206 73
    0x4000240c3c43c03110181c2c0341c1e00a5031460026042c0e21814815000308802a80856401161055120065150350003190b040e42c019204ea40420200c88bd0310700b0f194070f00ca80c03800c244080c0740c5d80000340c0c00c800c42c1e0041c0094a000145100d09030400310040220b96010700404000312007103091041c0c0c1402281d0034298902020b00103240c00c075a26000322861b03900075400341c1e07901c21103103840520082e81352410f003000e400780b4807020040b081c00d0b100010b103d0a00c481e604030300551603240ea60605601080522441d00020442410040456401b88403602c54219241c0a941010740209080c51541410044020074031a01c0e410003218074010484c07042d0200e041004107100d0100944e03510030f5a95680314041c3d0a90300c650612000c20180f001c031a1000800c041110b07029081442584801104000380b28070407980a904904208000c9809140a480b44142d02c8014108521469490b0000c0ba007203030403102a840200c0c60412440e00503911400e1203d00600466841c40111091980c00030344510025 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 688824064 1250 688822814 688822829
    0x30a1403041e0c03170a020114071b081201091a030d0503061201020d1a011205040308040b04020d05060405160806010302030d200d0203040f05040524010314090606150301030c 77
    0x210311080411100c58000d01c004c5810202c070b110b841d1004c01c60b0303d03202d03481356458a0240d884d07c41c14580100001c00f180d840b400032500c2d04c1003990007400011018961000c0c0443c2e5940f010840401804281c1111502030080101c001481c00e440c0c5408101c2e6190302140d6500c03d91002c90400525076214084a900c03500682c0c100e44002c02049844d40640503112102c0140b0b03080440703416001c1c0780f042d42c907942102c00b41e80307040141315142c010704110390042d00c2c0900092503043c005004035140701403030b0b9006880584001e07444441d6498582c06c1000580b400c13038a903084460f980382d20f032071240b0300280030300003540c00340c60f682d451640081d90b030306018860a4188a402c1c51451444460720b02c140000340011029503414000f130a00003900c0340e01ca0700401c110301c4644000402c0a040500c10148581741030a4446410544c2d500c0381840c031021070b0141410540c482e02e2400c1030300400f81c06c050040300c424000b0305980c2412410411103950240e0002d410a20610040010950004a0380c0490b10b01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 688825314 1250 688824064 688824113
    0x30f010311030f150a14220c320a08102d050f07030b0d0308100b12010503241b0f0406050c1204050a06031a0d05030a140304 55
    0x500010078249003c5025600c0c043c003440074541660114501010302c83c403000380d001c000030482580304500784c210030b80b91900400f68040d515000c52000303550030003125005440c1001c000f9030b070b14440408100c203011410003100800020308c607003e03c03206503090703000800c503802d0032a541402291a0303102107445002c1c00c05503c5269410030003003141c9100d0078264071002031284400d00c03d001c26001e0501518100406108140002c1950340300380715240b40800000c00d4070036036100310745040350700990203458468411128a030000329503407280000c049110b40785031002c12541c0740500705800e2840010355088498500f030f50044020002820346540150360741d82800d010000b2180150250041c4800c0c0803440703400042c007041e1103800c90047c041c0307455100f044400051304c0400701c060324001c43c0f154640001400b0001e0250034002d400100c0d6080c6030000c0c9103100c0d0987c00c001070309a01041000e90700d5410000d08001b88690240c8008001031406030614514100750361401c00b03054205000506410b031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 688826564 1250 688825314 688825343
    0x1e01080402120d0503071106130303050a060b03070314010b03071e020109051e010c020d09090f0b0604120213020403050703061a030f1624050702011b0c0f0b030f0103 73
    0x403aa150845a282d41c24103c6041c0722075030201a0050b0f10503202d110100f901140c4115002d10001002485600f01c0c034820f00c2020182c1c1e40a030007800d4003038040c1900584038180440c0a90b02c2c1c0001c0c41c85000c241d80d0225600d100c0d210522440201070b04101e22200d01081000b10b00c581203030082e12410f0340c078201c0e400c5d692880c1707004a004084110004240d400340c1480c40140075071442da801c880c1d20f4944000c01070b51031480d809070390f80c000c03841102020801d100c1c03040041c4032443d84100c161050116011601c81d080c14000f50b0780d544140c01c441000328200712803d044d400e0203002d44240c0081a84214641805c5890b065941c00e81844000c1c0071540b18044050356048503038120480110282c1214580c4040030000d0391101c5004141260030f1048400026800325122214032842c4030060300c018000c0c0524100701c60550080b00c0c207a06101342c410f2158000b031110581c42204601a40240014505014025014040c0d43e03101c10b400037011b10a20003e84015510030741100d0340110049120b24 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 688827814 1250 688826564 688826569
    0x20f0102100f050f0901090b070509030c0a151704031b0c0b12040201020c01031413141b0102070f150c140709050f0c0a140a1815020c1e01080402 64
    0x101d01807840c03400c0390900c100e5240072a80ea0308aa4015210454810070b80c2d62440c051034222200098050301c0d400750b100200d44035038081c1000300043c0401809440740c0442c414007003100e40c101903010056072201441005640e80c0e121341003042025a9150499036802c25407402891446c401040c3d5400f1030282019204000100c0c0c03550b80103181ea015250748901f86401c50240d41c1d44111016400360003801403070580c130740c072901c43d0a4007103014595040311521401000351691519034412102d03041d0f007002c64107004004000d03816030848584902c4980c000b07039000090400d00c040d071005850080d03061081c045c0c034158140c89034801003540f40c805c201d080300b030411645010400c40741c0e189900840c0004a04091180c025030320551a83c2c01c541c0d019250405986000e00c00d103019840001c6a503070200304a100c40c4001040105903a28101c0211030348220302805124555110309205e4120304c41400c0303115010301502000e41412a10000524082281e00c0c07660f000c00783c00e040c10000710500241c01c66 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 688829064 1250 688827814 688827823
    0xc0c120804053a05120a050c0d0905070302060c030301090e0a0317190c030e1e06010e0c091009061b05121c050112140f030a2d080604060b09030307020f0102 69
    0x1003100e50a030385440420201403c1d80e80304c42c85d20b40c8040310480005d0406542c0d401041d00505420402a03d8130b0f0352100d030030005245001b01240c45004100c0c000005d42c3e1980050140000800c01443e5254501198134080303d12031540b0b041550014000030005c25048902405141c1c00c010311a0328655651084060745229805100091490400d4020f0b0340c42e8036038040c0c0b00f0201104102d908442000301396540700d80e0381d440781c1700390344e80303c0300041c48140034004031290010302900626003003081c40390005001d401500d10741d00c006100e0740300410000754055498061303d46500800b1480c07000301e0701c0d0551104110018503c2412000401c1d4035145003d20f8015044000900c00b040b042d40c407800c00c80910003402800750303103265862101d0503040b14041054420200944011858044074100c1a518000c14019a0031505004104211207041e82e442012811039a40d03201001072400404110444803203421003800341e60207000601927034500008503244160115108103003034420300300403885c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 688830314 1250 688829064 688829143
    0x80f06060c1f0606020c0102160524030c03060f120a02010f090503010e01141b07170c0607020d030c050c06010b031f0603020703090e0628090c0c12080405 68
    0x80c2514111142d5200482d48400107889090b42955842e811b500012a1380c0e0400101201c0890740341c8404112a10348403030300805160b9600640101094904541070050300112007805070f5800010402c03400b0320f8043d0310007925038000c445541c0442c207481d40856460140d104001d05102d0340c102d00481e840c3c043c604d540c0085c44000c0082c849030640c3c1a0060280801804060311902c2010228040e002c8083ca8030b810684000c40c060b081403020340341c64808015101741e140035008200603003c1c401606106107440360195400805240301034800c010300b200c500d040c1007001c104023800008214000031460b1811910070302c0880e512601c41d01c046980007040580000308420892034001070454251b000313030030118002c0e00d41c81c08003035a840314507030894406c459183d03020f200c5002c00c3e41d2541d003041c4100b03844441a00c000701c1c40c1f43c48101c030708100c506003a201000300307042c0b1844004001d0303000402d07209040c540ca45500141490b1756a117640d26003c034110564104401240f030b50300512000d1070580d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 688831564 1250 688830314 688830343
    0x40e010f0e01020706060b03040f03050f04030f050c09010b0c033004051b06070b01092a0914040606050f1b1506010201050702012007080d14060907080f06060c 70
    0x510720101803118003c0d400f400040700d040d42080c02c00140d003100c403000d03603100d16004001000d0b40c01056400711019403080d214154174100501c80031010450180200030068851401010b03101009803c12824a40591104002c04000c11880d070400d4404016a000d420b2400c6081c04422903941034031440d81210080341c100365000004002c2805400510310b403540a0740c280800403100c0c0c141c01d01c41a403280e4100580000403480040144001641c0f00c0070f165801c00c2d5000391261512491410f40c1c0c884003500d01c0010300c942c181485110b800000700b0010445c101e074100030746071030f1507409086130254030115507444d4404039a024100030a400f2500141e004502550340900c4603010411140f5016100d02d030040d0303c2c000010300307154014451619500c003559601c54003100407004043d203e51204408961300b010610012401440c40c2c060000070103d0903014031940c1c40c2400510480c0507006181c0001c108040d410f002104042100d03594000100f5180d0b1982d481300513582d2403030f08403094070610 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 688832814 1250 688831564 688831571
    0x3010b0409111e01020a11120d0e010e03011401060e0a09060303022404030e0f24191b0303090c051315060f2f0304030f020a0f030b06040e010f 63
    0x30800480010416658111001c0843e0701c0404500d1941c914062482805030f4005010f440c049107601548410848004100102209020300584d04000c41d0450000200c0c4040003180c0340c6603009004035408800a500801110f030018038109030056042c42000240405020154140d8403080002000340407551800d02c0541d40c0c1c2d00e0020340d60035002140c035244400d411080e803480040e42000a000b99050360790042110540001c0081c070a07a0a00d00c5079103c40340c03d01d405041102584012640b24000342036680f1803854500031102e49441c49180400c11100ba0700340c98000309019015840c09406240015004042d49010341c44004c0e690005a0300030354001107020fa440054102d0107000108182501c2c00c6650b45506a840c00c40f02c0ca00c0708003140c000e10584070740c00d1050044e21011842e003c0b0060103203008641080c116401904151032010b03451141d0001e6003488007a9100030044084070031151843c40d01c0d40c13205030601030300c030707502c160349801c050781d1950025042400858142039042 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 688834064 1250 688832814 688832831
    0x102070807150605040902060703031d0709051605040f06080a060506070b1b030907051504030b01180e03040b0f0d0e10151401172509030618020f0f03010b04 69
    0x200314100b10500c1280001e03060207404507440c1810b0082000075580a082035007848803603a01540035010680b40300008a20804059070514420040c2038000c00310b104001403242000800a0000202c1c40e440c2c60500c801040100302c10b2204d06640408c84e0100d00e03181d034850b202c081c0d00d1405410968000390340b048011072401d0a1001084009003c0c019003030f1010860101269520f100703020840c4e640c155900300c0c8100b00031a080002d03124445030030320b02400389059125030355503d5010b000c0c3c0020440c1001000315100c888102d110300b5040c49142002942460700d80340f052121841810310307411240901180341041e11071560400340c076140d020420b4030003003007168551000806038034150003003c40c1a80000074044281401d01a0300a1069641c00d132240200882d200c4001400703000c01200e10302c51490842746980c0072070700f1400d81d085a80c41240151079820b001e01541c81207134400c111300c028005003100503076880c2104001c400f8203603803428503886c481e40024010a035542c2207a4102d4106601c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 688835314 1250 688834064 688834073
    0x1404081c0e01030605010e0d14010906061a0403050a140a0b0a0b01031107020d0f0c08101d0f070513020409020c0715301107030e01080c070515090102070807 69
    0x194882a50340d5041501c209000440660b4643d11990b03020a100c04903070449802d101c200324044038015200c000100c4424540301d401c45400220581d800d50380c0b094140030402d101601030b104c1030f8035240103a0805040d511802d8648442c104000e00c00070003060b400d07244090074081c06003019080107140e13000d458100c180ca00070713100402042c0e00083c6462021098015240192a05650003810049522030176a03999200c0800c11001a10340308842c200004840340100180030311103484100208030b0305040c08502080b01076041001c030013a04456100c9103500000600682207801c221004c0c00d2581d5402407400007072003a5003001070700c24000281500c00d0040040c01e42d04445044989412640f54944210392002814031a26481c072080c1080c2e26a000f05403660818004002000140c40c614010b039490306a4801c0c20205c01182444081c1061344d0f03006500503511130481010945009116581c0d5a2660a2a01025410410400410508030b000d506032060a0341c0038200c1030365170305039041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 688836564 1250 688835314 688835353
    0x23010b0306132901051e03060609030f0a0b0f01060c02010c03110d050408071d0403050913020d0b0328060e160803030f070504030c120f1e110f060406140408 69
    0x5202c810b0043c1c00603001c4540d4403940488590841581e240030019100104100c0b066001504565000c0701c2807000c280650703014402c0521001c0c846008200282e4546000b0b102590000e1220041c1480d041c01000070540110784926210390901e0039804581c02403506641c4529130300c160b14480e1081d02401411a90840c0041060f101c281c0100d0745078580d10801200c403184110b503c000004282400304000030b000720050100f003540200038503000e24002e252081241c22100d2140c110546802c034a1100d4102840400d842c000c2c0700b51441d1802100003111041d214603204001d080c01e6960840c0f030082c5409210030f62101c02280c19480c1d00a81d2502641c0c7d898205560207503051951074086420a40500210303402c482d8015404158075241802800030f0b070144460a40e4042c2c1d0810031280001d1102110303211807020506070382c000e46079a0600100030a0082250307401440810325000141d65900207460440f141c52800145010446081111038090755201c500a44203118901200b6000d054 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 688837814 1250 688836564 688836611
    0x3150b0a09030b06060a02150a0e100903110a08030727120309080106060c020d030219080408010f02040e0115020f010504230d0804080a031d0706020123010b030613 72
    0x80f51030b80d640f01d0900f0401648111180400964000d0b004240b1099401900550040d10310300001b45800301d044000f41403521604c81e0100c1150740b900e82004040d0016000c509000040c1c00604907020740340d40d510010b03c4044c004400703100c82c01b41a92080b5401600c15454102c4840e07400010503510900041e0890150307804801003081c44c0804140c0c1501440b8180881e1001d031707030b01482c0c84490b40911524904d0700e08164210300585e12145041f6841011210540d0701c20005a40d0f00c0d0b00d8040903030701312000700c80c100c1c401d0b6004000400a4031240c0708450306492602d20340521600c00718400f0381ca0800c00072035082940d42030500b001309010400160030b1020b43c2c40401e810b007160400300141d4842c0b100e000381002003000c200103e0040740b0803001a100c40001c1d030900040c20303543c02a4007141c48144030807100055018001c24880d5642c2806442d00c40c6200350a030000000b40c9100c0b0340d41442050154403004440840094415aa01410080c1410920f8030800c070300e22000c4200c2c0d1491082e00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 688839064 1250 688837814 688837823
    0x406030f060b060f0d0b01031d0a03120e1e0a050d0302090a0b041203030b0406081213090605010f08100f080a02120f07031106040b041701111903150b0a0903 69
    0x8403110b901403c2200c03c40d124040510740c0c0f01d280c80300107880900144032101c0c10307504042d0796600400e0504161185000c0c07000d040c80082403096118230340201012019420f400c6d02134200400da800c1c032a000200f03402c17944181c0d0145100c0c8c603111680c95142c00f04100e0702500e03500ca003552004003c0d0b00755004192142003035410a62582e140e18814009128500c107405c00005207251503008644a6070111080801c01800801c4282d03503921740701e00d000340000301801207081c000781c24000c0d01e580c00e040800402245d032060114a15050010b03103625240c3d8490303414480020000f5401c0000c3c811120060591022401c02c1c144d1543c6005949041d0f2803402c80c010f01050300303a103210241c00540c000540c2d44050003030661504654811800b81855900c89800075410300010890054940191020704000503410642c0040780200a09491040782019800780c41040340710f401d007001c02e0040d040865581404240c44100c6032160005c0081603004084556000c1034050b03115500254800c2100d026 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 688840314 1250 688839064 688839071
    0x1203010e0420060409021b061501080f04170a0e0d120305090a0224071401050403090b0918070c0501091b0b03010b040e0721050f07020f0706110c0406030f06 69
    0x2c220000c00e5400c2c404501c951040c0188410410100203400801029400c004004011468005540d01d0001c1c1038070304040170f00b5415013492144d40d101c444150b01080300d41c44c4050608240e101c001101021204258040c0b50000365051450300036035160b81003030700191401d84225014106030030f0707802c00f40280314002414000070600c0200001010b111a0350028550b085440c2151400e00700c84449551031f145500c4203000790320100d188618803042c40b0300704000200b110703c1e1503e0010140400340c0c0107056094801d122074502600d0784000210320f06060030a060a903110180161200e1000100081c4250b003001159400c00034000d810302070b92406200040703900c4d41c03161300589030360100340a10651064244010020b40c15600c0c8440d40084143c10030302000c618043d00c0d03680d111040c01444a4503911030090241d41603110725510b62000c070358030181c4282a8070742051510b9020901c551010801a42c1d01406a50001d000c40849000002d1041000540d20700d080c4100130500003007900d540d490f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 688841564 1250 688840314 688840343
    0x30903030f050a09090e10050f0412050418051305030d06031b050d0f0204020403141c0c0206090f0a170c1002030702090103030c080f0406030e01050a2c1203010e04 72
    0x10403e8810070003060f2603440c1043e040c503003920b000713116082a0400318484c2d5050001458030301d00c1294024401001846018034041c03c11003000c511702d8100008016041000700714001e441004040c001c520a500800c490301d544d00203143c40b0001d550040c00078040040d0480007a0741e19485070040380e01c100342807a408066850000704451440c07003602d070040030142c040f00002c0d2102e040030442d1840148014102a1680c9604209400700c034241215a8007026400c401d0030040b1500c1c101d1a129072030982c0c1c508641d41d001c941c95025492003507000d001992912845540c424405002601a24114544960014800e99035550051003190700440392102c0320320845202004484600340c02401c015080e0346035980440e800c074404481602c400e00300348007800c442e102050003000148015030340801e400c4a0041c0d02c0742190400762031000210b19005a624007008141001130040c861840c246c004205c0c0100f034582018035604851014460010001c901820004603031401107024050414a920 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 688842814 1250 688841564 688841567
    0x118050a0507050703080a320606070c03020402090d1b0f080609150a1104030f0203011401030b1b070c08160b07051e0a021806120601120b04031b030903030f 69
    0x740162003000c0007035420040c00300483c4c0181006030300b0440f0500d001504896054083d080c0b901040104200c42211b20b40c0b120820542d803408640202d0126482d1385404980d07541c2d6020800c492100034025030300850b4480081d40c841980b0282c058022401c00e400081003160340728141028003034820182444100410f4111000411512a040010040c00c084103030040001d80b10a005082c1c2d0740c0e85803910320001b0303180c0d0dc2c2805000158400d0502d40510f101500c101429910f02c41c0d130f102d0718184020010000703d1440c001c2075412031440c203400d20402e02000640201880340c600060030703180d22000c0008120b400090003003124070f010504a02840d03128640c000440c400d01c28050b1444e4480c80f800c00d60301d805040c12002d00c0900c1c030100c5407620036036808541c4c421200074440102d0018181000003a041208180c200505808064080e40d81002c032110810141c2040c0130b00100c4c01c0c3c60020b42010b000344a00846000f6581107400e180d2000d00d402050b07101036001c100d0004100184420095 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 688844064 1250 688842814 688842821
    0x192a0c08070e09060c070f0807051f0b0310020307020c0409080a030c022b110d02010e0f0a0213050a142406180f03210408120301060503011215050118050a 68
    0x3e0103c01e0180032036403034050360843e181e008000207441c4980e2103085800007442a070014040144a840680310116100703980139001400c460748402c07168209091600d00740d0b40401c078641030a036420001070b10b80d101e9440032440d0032125402d15800c10324080c1b6071402e0140c5e49000e044034054036035050000b00bc0d031140490f00c40c6050341601c15080355800401d25025038201c00c640d41c1860740d01d07092a107645000c00551a011846d481c040140c0d65585403180d150b0014403c000d07003010100010300000e03000f40d0204003034881c9660125408c1da1b40e81c000c1001d943c11500b10030052841c2e0000b02160381803510718045108687c1403d00d1101c5d000c80c0d62908103041031001ea403e24003d03904107481c010509070a00c0f15082020008a07854080c6000d0300f4140992100c04424a0815441c03c0c0d45070b0b800c02d0f140c9464000da40800058020040c00100200e9501c1000c4034155120795019960401103403a1000341104001404204e0506110000c80c0c40c00b50001c1d814514024080140819142d04003401c0c00c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 688845314 1250 688844064 688844071
    0x1201060b040e040f0b0a0504170f040e0925080c010905061204051204140f0301060e181002040b0a0e090126030904091103060c192a0c08070e 62
    0xd0609110411490700d4245200740d1050060498006407000390b51a010044411602c036900b05070790b40117002c180300e04012003803903407001d05d29200c1c0b4041100440c103810b8000e0744a5501115228400a07852450500c4004d001d45404900407c82042c0c180300140512401d003d244071921856400c2c40c0d00d9845414103900301e80c03000e42a203180080c0d0075403000b04a03070300602c1540c10f442003030a1100b281c0080e1000740002c10f542c001100b6001140000c001c5095410100d041c0f09030304094091246040a4600940005454140e00d41441c003020566082540c0840d000c400303d0710200e4006054444200144151200342c0e032203000c1d04200740d04000305944207004000c0010019401200c80030400382050b0704140440045034104506039000409481049070300303c490385038041c0c0c100418103040100d42d4001e1400040070f401d00c0c542032104d40640c01613882400c20068580444160305c24041c075426a414050100000d5011482c100394405d000b10f8807801166104a0600003103101156290602 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 688846564 1250 688845314 688845329
    0x703031512033e0a1a011811032814060405091c050d0906290d050c0f01090b161b030c12080903060103030810140303090909010609110702120106 64
    0x4440d48441d1001e0f5080244500d08001445443e010001040060300d00c00031401d4010f415078210740c1004001b44c0c03103400d10799844010034280703064991200c070190282c962020030f4460220503406484254100c4081010610805900e02070003c2003c100c808d41c40d51090340c040d1000d1001d40c84100c40b1a035900c00e540200c0d541c3c0100020f98452952040340184a658502c44001c182a11141c072108121800415224403c241c80d050b041c00e04030115004141c440405c0b03c1c02621a01e10ba01d586481e203d514101c40e20032018040b8030841070380502000c0c4064a5491915600c420030a0751034050001d910806460f5207000300000c0300f08049131034080080e641c0c007070240b03c0b40c103142c06000942c130050f1000c2283c03880405e00841d031103a00c08000290003076009036030f540141d007810154500001e60030340044640c2c00b001c03510100c00c1e45000084401080043c0d44403d81d42c2d072864422401482aa040707c2070703403418203881c1c41481c200c4401404031103008130f45866615185020716401c0b24064442e418 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 688847814 1250 688846564 688846637
    0x2101404210e061606050c4305480402090303130e060a030c12060b0a08071d0f061002030904020f04090e01050714070303151203 57
    0x1d15562446880442011820105045038010001030f001d038200c0da440ba0f621010f07a108460034800c4c10301401fa00070039103603041d41c40d00c814443c00340020f00107040b546403c60400342c0d0140c0300c041c1c252001d010740d003180c0420901040c01460041e440e503814503040e621a01403400912003840212010407000c070ba00055918480c00c000a1580380e90080c4d800b0b8550003642449405200d031421710040004402d1a04001106814070703002050352000504400d015450740d20f020320002d1408041e00c81a00c0d10346d20a03003068812803507c0d038003400410f04e61940200c07400b1800141d07042c00040000581d10064a50564400380601c1ca03501c900c1c04444420156070001c0c086103450505150400c85910b003441035038504081803000ca4107a91040324900000000081c0400a0355002d1181105003650800284044d04191200a0011201c6444480d000c0790020300c07101018042e81c004551598001ca051220541d1f645a031030496064840c19400b0500160031b8048500103505408000c1ca0030300a0789 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 688848920 1106 688847814 688847843
    0xc1501090905030d022a0105090c01020f151308042c06092404050c0d0501080609030703051e0c0f010c050f0301033002101404 56
    0x140005190031a5507002070004411075910003c01c3c01e025890345403981c00c0505a001216000141c52024020785c002c010301904407038810f561103001d60320000303140001642c484084100d02d6642e6040428882209da0090b54500d4110f0144140031300c0a20070341c1d4036000d903a40250040c000340f040c2484101420410090010441406540d86507841c0c00e0000201d45007044c0a01013100c840312641d0078400314111400010540c1e04010000c2c4002c1c10800c1c01c140482d8000d184604510b07003040d0010030103660004910340030356040d000940ca0542182c804680c2030304020510a0120000f407a00705030007100368084c0c1b8801d51a00042c20f010760752031402c507084a0745140d070701c1c0c1400000d025412510080d6810780741140d404c142d94100c05c10032840b6202c460a420400c1010740310351051740704101c40d80001d181301007070b142a10030801103448102d0b001d4800e00444000b4030201c0e820128 = true := by decide +kernel

theorem cover : BRFrame.Cov 688669064 688848920 := by
  have h0 := BRFrame.cov_init 688669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 688669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 688669064 ≤ n) (h2 : n < 688848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
