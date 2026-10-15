-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5539
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:11:33.441426+00:00
-- url     : https://prove2.me/submissions/15103842-bad0-4d83-b9f0-feebcbddd437

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 996043165 ≤ n < 996223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 996044415 1250 996043165 996043183
    0x1407030521040506070311060f011a03180f010f14012402070902070b04020405130506040611160606090606080f06041109030a11031c1b0201170f010306050a020a02 72
    0x11141c4904030030003001c0d811192050303900c0290404e4020500341e040c543c109641e200c544400a0540b92039680707024040d00000c000f401001002d1a0a00c1000794000004014550140404a001d81000d0328060f0031894411094180c0d03455139103401c883c1c1d0840e130383e900a0600e03111b80d151010a441d41010241d006220310510317071400b0b044c40304c03040e0706009100b0840000204440d43c41156200c074541810080b0032001c441c00ea000d1802d10b03001c1100001081e0701604820742100c01f80c6450340316543c86030050032000812840c0240140f06c0b982c008070200320022041446004c0c001456850080e0003000d881c8a030748000305121180b82000316142140e11559808001290300041c602c1c0040303004c1c07429000c1d95850507014401c100c0b01601304900e0036202911600100d080f0350001151401925403400d445143d04006040e51644141d0485241c1c540010a07105061400b03d4070141e80340100411811a4108144600b0500400504c04144216904243e4544095142048071007000c1d42c1d40c8124 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 996045665 1250 996044415 996044443
    0x320030d1107090b010314010b0705070608060d03030903020f0709020c0606060403022b17120a050c0d1d1c110d0c02130b0928060e07230a030914070305 67
    0x30708942e003a10780c447c2e88000303128a1142042c41c1d003540c59000010254204100484041c42845000700c2c10368007070700b5441d00c520002455211040c0c2d295a048000d0400000110705621801ea200c5034600000d102c080d0140c0296580180c07102c0402c0905882c0c4100641501d000c0c1604100620268544944801d5a00001c85001e20141d65010784410412164240604407101d845426048211050004d002e03a0102c4c0325000d68588a00400c0012030f00107640c00c40a4000070000040c00c5c1071680c020707040030f5254402c40b600c1d14030101d44403130070b060869010302d00c600c0c1050400000340d508200c191450501580c01404006115003010f070094403c00d801138851075032181d4840c81d240558004004e0b0143c00341a03060341303051000450403001b458501d03089060420b03c0d0803040c4462907201d06401c0b140c1040c620349076038503007420940b00000c0c04c2c2c089854108000c210308484003e500010030800c481e999001502081c03070700340505d2104072248140025001a4400c00100d50001442a014020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 996046915 1250 996045665 996045671
    0x306012c04080f0f0405130b09011202030f030a030203010e0c120a0e030d0c0201020301081218040b03160f050906060a1d010918052502060c0703090320030d110709 72
    0xa0707814120300500904000450203400011002030608401d4041d2080381c00540c0c0b000c008554000224041c1c0c1d540c0d4000300c0d00a6240b00042000308401c0380f0200107280050191041081c0320b130012801d41e4400c4c0080000b20350000010071054914000c1c5e607603c000303040c48190034004450207121442c000a04852011500d81001c141007200c01e000301c4944812400e401c0000c00700090019020b034009200d07203000382c00360302c0c14500081e029104448600c00e0340221080084036040400004185a103960341d010b21038807407214800910034a4603c0070700902d01c002d1004518000c10420521001040a4001e48052000c0b0b2480c58000c402e403290301c400c0250b450015001c4200403110740400c0c0e8072051031640389c401000555005a030110b401007083c0b201018406984c000840800d40c04012400c00582c0701c1d1000030801588100074101c4603101e480c10140b03443c0c4c1c0703450b035401509000c03401c01d4200600034010000341c90200090040d95072203041c0484280c251002c16070711a01984078900156031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 996048165 1250 996046915 996046921
    0x213031a0903433903290411030c01110a06050411060a0801230102070312090306060602010509010b0907210608120301032604350a020306012c 63
    0x103500007182e22203d60a981c0301c800004505207016a50072008480e400c2003099030309241404070409000c41c580724040c14080d4628a0351b41ca001420f00e010045101c0d1120b112000ca80042800c4540340c055805080c3d0152580179000c10141011202d2000d01d06000e0203c804021004001c9014044250031410018041e610343c103108054180105429a0020bc001100354003940c101c0c0a5138140c3e01c140350002017001c1c0514207207002c03007610440540540d102c503508100007100c64003408140c1200e0b1400d140302d29030743d5580b0415208180c1040740942d4407034041041d091000d04c20804000021203190300c40b420501b101a103418004d0104103400050300c0018100000c45411a100510207082200c900c10640007908040341c00a020460305004000800720344205940b01c0000210002001545021b2a02c108010101c1c01800d084182038481c0c40860741c07404400c0044c0100c0880180a0494ac0345a03204041c10204140c10400c41010034100b0421102c4128501100001070b859400100b0340b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 996049415 1250 996048165 996048247
    0xc0108071b050f060c28050f0f0d061d0708010f12080f0301120c0801060f0504050a2901030e0a0f080306031c0915020d120b040213031a0903 62
    0x1034000d035850a51240b2014044000c041c00024540031042c400c150291141b00190715490001540001c40054070510080684500c0d450040074000380401c1c0d098602070072041000c06556642c0c5c005044402ca8090f10088610f241c50440da04c40300302d10b0400c44542c1409140801e00005001d944000303400c6182010400903000c0465041000314500d0503229a503a00a03010300121154085030588000c05d0002401903050107590140c81c1c0b02c00d00480003c3c2030106000040030020304c035940d140d4031114130901c44031110400c11080308040c032101e0b9800a10b2000581680d1142c40c42c0b4403582c1c484000400416200100202c01d40e13801401c0a40c0d07074072043c0000c0d01e030072160751040e036106501c1c038002d5146a400142d207c0c01c4030981103c134084030044600c181d880d4641d07440340300041551400c404140940c55801004807100043c0014241120386a142c804086a40c100300c3c3e070005da403c0c0b10000c199446045541c0103d2200040d840c0514100140515810706148000d0641281741c96a01e01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 996050665 1250 996049415 996049423
    0x9090509010f0911120a050307030c031407050105011a040506040506210109050106083108041710061403070611150901090201030b01110d08090c091303020c0108071b05 74
    0x80340ba0303004284062491070408200c1c0d04a0303694030030310030f014000d18080d207010089410007205401a000d14200380c2580c80a0b240c4104d8500e0450400a003040b20b1301c150440100034020a501400c0001450341c10300c032100d010f081035610340d03852411080c0700c10081030b1368010454003541c00903181d944d190045034950041001041c61180c010b00d40d05000841e0b052025030200d4122540780d40c40342180c2e1a40031210500d2a002c00c02800d11045002544559004030302e1039282c0c0c6403003505400d240c141d41c0c24218143c00d2114035402c1c03054101040c84112818240542406444030182180000c4110800640d8a0401c1d02c02c140030b01c12a01000103000c1c0703041c010301c1c41980c6400d2500b2180c0c501800014020a1000c030b089020a1900d4669002544503005040c420300407540140340d001d502c00750581e055140100411180e1107900c181700d480f03840b4856024050101103a464403141402c4c43d0103403c0c040400811410405120101300005620012100c4030328090400c00c150000c03d42085414 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 996051915 1250 996050665 996050681
    0x31b030706020a020a06050c13050603090a05030c0706021c17040501020d0f0203240f041a030a0b2509150c06061710090b060f0127060f020d0909050901 67
    0x4942e1000c00d5143c0100c2d00442e914040034407660040199aa914000f400c260140c00a80036541000720301c103206e5401c1040c011500141000104c895940e0340e40e4600e40b0b15407204141484940111f481004260f40400182c00b1b140e048151140b1400d420040080c603410400022064001052010a05201c003c0d4121180d41d04002c001b444412101135400019500903903a0516441071486140600c0c03150541111280300000c1440491a001d10b0810014000780100c0703202d01c4e0000d41282601da039007085400c2e1054802d01800710a480c0a8403070203c0d01e030100100c3d0b41240081d00c41110340c4c0d03038019036141c00d951447c0c168058503c1042d0742102d0486004000400e96480d01d01c1c0814960400b042c2900c1e04001c0c4000c841024040407865401d95014950040044056501041e11031802c44124075024a045c900151030034080d0b140e038201104050444041154007890034802c407070740850030021684150000303294420032000f0003814a4054800d00d48910396440100d2000d031003c8d000100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 996053165 1250 996051915 996051923
    0x1508030403050c01120911011d18010e070206040c05090406060b0a030603050f0304050d0f080915070b0f011d0a0f1a09011d160512070e030c03030c031b0307 69
    0x24031140ca80c80d11035902c0c0703001820180403d42212440b005040280100c5a105501c0046054880400001034800d2551103006042482c0035039a8040c054031203400c0000320102c40310341c0c1c00722949420b1070311010100151850003190821030800020410b6407420404480c415144103400f540c1d217003030030402021660440d414140e0001942941964507422000075203014000746c2d080b01c4220414242e881c0b1440c4512a0403401010701e02c0041612040e031010754500485d070481c41c00c51023100188002c4202d230002408680041600c005201080700415440f28554484030718650420604024410400100e600900c603010000364020403907820102288030694014080c07c07242d9046130985040d807000b414010707580300000003000d01e160200c85400c80f401c0f110580f8540c6403500c1c039400306d1240150b00c40a100c0108400c0c0056000507001c03510a02580e515080203511560415081c08010b0030014825401400100700343d81c80031085860002d0710180300c01452400c0c106450540c003030341e0b40240c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 996054415 1250 996053165 996053167
    0xf1a13120507050603091f0b0604060f08061c0b180115090f020306010504051005070b010b0408010f1a130605091f0905040f02040e010b04050c180402091003150803 72
    0x40d041100d84001a0190322075019900c02648a4043c05401d010440c0c224411b0743c09081c0d080280d54502c00c082490018100c130100310001a2000b2440540c4542d104800068250b00340c0c1d190241d018400a0f00541c045a400c50820014510f0005184c60010054096404040410706002d407804145580c0070200d00248481e0502c003143c0240200c09100d00007010b42000714941010f401c61080301e1081c90143c440274201030a001c20b0110300c035819640103061001c1008000081000f07070b54071070300a20180a189942d241032071704130307420348500c81503500859042200d26150400301e41c1400c0304107101a54030b12000d1200c003031484042c0400782d10040e002195101446031f805100c20607004441e00d90303203889c0742c4181d40c0c48000b0115442144d0140440d138814890304014902508105d80b001c20710000070a0300100c040002d412510103860300400b0f680d0004400b007180907003441c0701c041e14600721002c506100b1420085a4400d002c0d90750302040564540025200e02903201803407001c1d200f404126 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 996055665 1250 996054415 996054419
    0x14161707050f0d15080d020703020a0e0c040b04081605040b030c0405060d0f05010b311d03180306060109050108010506031803310303320d02030610090f1a13 69
    0x141350041d031401078249501500703108004503400062094103e130750180040344101d2800e00001c01404002d0722800c0e0ac12070410002504000c0d0360090009414544054080c0f0710200c00603501c3d0262a6100500503410840208559600466602c405510a83c1c010806940e19000503c640075041030060885a0400d00182804015401020009070959901e00c00d0030010390084601c031a100400c1030141002c9201d5003602c603050300030142c0d50f07e00000400d0940a000c1ca114115004400442d004203c2c804c0403000a01e0100300942d04400c0a080c4801030030300b403900003404000140101c41c040c5c500040800e401c402d83d18120312007800c402003982d0310703002c545902c014850b008941090700014001c40c01010403911581c04800c481c2e0681318003100070f100c401840c40c44115420b00c0801c2c500040541c0b074150715407500400007a0049100107986e0320780030341080340c80580800307590704010000303006001100091508400b0344081002d0b40b11704140043c0010018800c580804e01c00c1d10000c140 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 996056915 1250 996055665 996055691
    0x4151d0d0e151c0f021201080609011409070506070507090203010f090605011407030c1b060201020c011506020c0d051f02180d12030b03070914161707050f0d 69
    0x6a0040048221841c0d00300c50b00d0300c0c90402490054401d40880c070240441e0841c80703500d15510118186110400c09400e240041c80c3d14000710034264450511a080601080300c13206080c4220b0400c0da00c1c0c60b105003524104100d0700b5940d518140582c44c000e08002458009004007002804020001075505565942c0c41c0c11181c04010720512410070b81e9414100c02181c0b540c000c907103141602e055000c2c2c1d0381c20040181c90880d1001c0483c042540c00070568040c000c4004e095502c207101070711040d0005a42d41080c1c80c4d040382120401c0c42800201a1114418048203901146442582d4011030740c008801000d0304010b41000d108131780c41141c0d83c43d100740d014132554040e0068590090b01300e46495208515000740000c002d004a40200840e4914820b41c003014000d600c680e450b00d80140807030705600d48852403a81152084528514000100403c0106c284640040d4102e00d40c214039000e41e17195020f80b481d80712900c01400031010302c8008100075002d56286070a40d581c100c855007082c441c0c250107640d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 996058165 1250 996056915 996056927
    0xb01060c021909090519110904020402070c0b031e0c0a0f0512090703020909012013090905100b060a0906030b0609130509190209040b090f1c0f0804151d0d 68
    0x10111007602428804e041003d030303c0c6c529000c4a50b044000b17403045201d090704001381440020412a8815070030f10106000c03a440066500250248468065682c201044100d1303005003d06402403184500f8000c00181c1450b000540d200410300e400c0680540c09405400c5e202401002d01c0041c2c0f114000d020006024400211841200d0090758030550686804444600b80c80c8103803003590a58003805000b40c84625a81c00420441c0c8810b5489500f045d100c440d1f40c029150508800d9499034000742d210340e030131091071003008206101216110300d001c1081c47c0103014021184101018940d803540c20041684400741281c05038280241101a090600020780300100b106441d07581d1588102c0304001c285080d074a02c070503010768000b04610802c2c0d131241d0350b089061400410200c128010101e406840f0340040220701071990410000ca00048455007004002c1002075101c04c2c100301c0a8810301011074620318501c540e4504560010456041c010000e68140c043d0712207a8040d413142c1003585003420341c444 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 996059415 1250 996058165 996058181
    0x50d090c0312211a0d0c120b06090705070f03121503050303090708031c0e01060f03211b140a0c090e06060a03030f18050301051e130b01060c021909 65
    0x72250002c1d040c800c1d0707044000c5501420741030305060300100b0948800d00d842a103441103181b284040b1b80690b515660300400c2e14031080e030100c503a030007140b0601c0400e00e442034940e5030043e205c0c039016040920548030400504039050000c3d041c4007915003061b000349840d0f00910088a44299465042076032458500c1da03d61007120f20010f1130062032030201c0c28510110840310f400c4060f5070080c1c202c404c0030b6404c400901c60b040e104800c5643e200b83c002038000000002200440c010820700c05800c0c074040ba9240701d80b5107100c9000030001c1600c00c4950b8100703050581401f0541141e1030300790f40d9014184072490270400850280001000490014030b01049402003101000d00c217059981c42e40f16030045c0000303c07000d401300a0202e0250b041088910b4490030340102c00091100c1c440ca0481e5540340801e08483c001d803880c1a006401c11002003c0e240c0064240360490580414050f8010304d9480d009100710060095408206aa9415005640d80c808900ea1818080381d02035071800c3d070310005035008000c40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 996060665 1250 996059415 996059447
    0x7032906010c110103020c01020909010b0a08090d0c0f05150f0105040c020609060f070903120503040b060d05070513020d050f01060e0303120c0306040f09060c031a01050d090c0312 79
    0x480018080c0d51240300700c0642180d1004042c880c15100c2801500650407030103041003a50750a00001c100c56503503034942c60082041c680550764540c100c010082c0b4000c4000e18118140d840340840960a5500071050901940c0008031000400e0031482c0184c00c043c041d9000110b0f0f04a10350900c900f90712101c030480d04030313182102d04020328059040d06a8862800f1148010300340c00800c00500801c0700c40824540c413114074a0b040c8a0280c03a40d4070b0f009480b00c030340c806a00040c030100401003085420303031905412001c200e809802c101da0942c1d0b49a600d10315402024003e400300312001d00150b0068060b20f502c0d0907400e070188100d00d00454880301211091283e1000150b03a040f40003083d08012089541c03003c5505c0c5600041d075240c0f201c02400c0c1d80042d1401c0d8006564521517a0503d68510540030b00c40d00c556008215000b6908006094a0000d15148002c400c1e075200140260381200c100d0740202c07469100488e8041160030b0142900300c1d1584090141e28000350000ea041d0360007441c41d0703400c407d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 996061915 1250 996060665 996060743
    0x801050a0801090201020a02121906090303150b0d0c2a0c09020a230d141f0b090f0d05060103050304061b02090135010f1b0c020904050703 61
    0xa11007105090b100c00c0b21001c3d0250300854841005400c1c005480d8401819100403113105a01c407003421001d0140301d000a44606507900d07056000c0540c140336030101d501001500b0180b96040290040c41c2e031040816221403150b8070f40310306000900038030038456158441016144645150300c581810004c406034100c0d07072100c0030440032031000c4062080d624180126903400b0310581c2c603400000e0340f10a1004401d0010740c024032589200c441e46008403030028111400010150802003440d6051449440210350400c84c0207005020a64806094030401d150840311619100004004182004640320020f00b05028010001c018401c0004c001d00480c1d541c0d90b80c0e8a82907009610401141c40b0941001394480c0803000100010315aaa0361410408400c01094052569910090500155640016400741d4447d000126241d44922904039450302d82441c0040704065600b00502e10403007078400070b1059000002013414840100030880c05185d02010b0319462840c090b0054a4a0704501040c1c90710400d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 996063165 1250 996061915 996061919
    0x50a03050a11040506130801090c05011b0b1b0712030b03190c050d020612070908210d0c090815060906041802040e0f0a111f0806040b0604090c0801050a 67
    0x1c491040040d10041d0510003810f141c1040c04200d100c1c1e0240c0030016060340440ca020510900c02e104500c8150b109040306000301d440c0c10009481e071180700d02c0d008a00ba0301e2100041c086198001400c0e403007c0000702855014040075002600c0340140d400c042c2c08a0403084040344440e030154440102500c01300c007104d690104d1103901c403000c1003c0380c5000700b40d110050010001030821212421045100401e002d083c0010300002501911040f80c1400009040000070000d1240030300ca01503030f50300000e58603101000b0480300c5500921a007080c07001e180b55141840e4011a02c5074000300083d051110036501c114400c3c2e00304007941c2d9030580340c00d41f184241801160b1189002c0c400c4000045000c000e15802c529990208401040300508469941c0582003c4804040f418400c5a4a00d0b02c500b4100318454100c1c0180100c40215030312941c21424010000b20001c0d40110200e41c0c0035404a40c0400e16490040101e0100d0055030700c00c907825420246100d03140c03600300a06031305aa2040d521054003035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 996064415 1250 996063165 996063181
    0x2090312030109020723030a030b01030f090501060e0a23060307050306190f06061e05090d03031b0503091b040603060f09051209240c1f0b032811030d050a0305 70
    0x1b081c8659100551041200303407500d90084d0410300b00c01e40d050500280301c0e0650000c1800f40c40c0501c4044882ea5540c44d4148022750010310310a40107900007204010450024541141e06100c030850b03c9101c0c040240040d80300d58040100714013070140501554403504100d0000ca2501b16009500010709017010704940d0511801c0c4604c1c0e0403100c183d034840340452800149014281d084a20103810444200421256a1160f98510609510070354001416007102d520303400c1d1201c1c01c0c040e0345042000030402d01c95410000551008016a0032007800025448240001d00502c0140c1c8001c00d00342c02e209d24003426100703d510618510380248182c40000c0034652a86d000351043c0409968000c0c1f41740904a40041a0300c0124a04241110b070b03e4075259168110f00d14114140c0f201032402c410841c079884103200c881c02030b40354010701a00203102c0401070389003e011305091040f40c0c0400c4000c1074101030134440c0070b00911440e04c0c2c0c05030075034542042108004000345c0c0940d94a00101e821b11022850039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 996065665 1250 996064415 996064463
    0x6210a1a06190207090c1110140115030e061302010e09070516080c07080c13020a0906121407020c0406060503160f0903050709090c0504050f0a020903120301090207 72
    0x80d0340080034a868400d0400c00d0250b0014407100b001c0c2180b1070303510301062552440c401c03502c44101300c0c0c842038889481841c4d81c52418211068a03800d507810008060100e00c85030702950f040d82e040d8003400b890707030358071100c01ca00620400da5446500e201d1003003800f03061500903071125041d60007a603404e42c00c6003404040c007080c60000d0f10b00c1c20000b003041001c0440c820408044007803803482429000d103060200548540b901e1039a400400c410b80080e65039040515021040c1c5600c80f2040d101541800c440b80c00240441d0080c0c03085005010030004030000c100b1301d6510038000c50745142c01d00801c905000340000d42d1199070f4064140032f94074146020078410f002c5c1c01079074400e09010072075184280d001c01c400c503844180d00f2589000e00c03002000100c0001d200f4080340019085010703002a071223406080480480302d0991105001e01e00d420140310b548043c84602a5001005110150356018000003113484d04581002c10301c6101f034084008102054590014001c550081200c814a01d50300e40c0c41e0411 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 996066915 1250 996065665 996065711
    0xc09180b06120c0a09050105010224060d03030b030307060501030302060a090b011401090305060109020304150902090714040f030305090901050114041e09240e06150906210a 76
    0x1184640e140000c0c103900d018403160b61584024001d40b401c000d2420003040969600e900401078540c2c50740f005102c1964104001121445041d04504502640d00d02401c000e05000d8295802501000d007418103041c000e400402c4000e002608130380d5a200356041050080c682800220010300804012400340700c03040c081c01c01d4454000000d000680d180187d01c0300a803603640c1c5414103000c90070400002081d020310420b4020510a00c01690328905843c00e900312000401046105074036024010015032180d01603ea84a156810640c48107031088000701e5803400381354008000c00ca6a86404003c044d44000501303038000c000d0f11000000c0e6281c0005452440c0c194a4624446400380010009860108003941c0c0e031000115100351000d40380c500100c02d0351401c5403d900340c001c2c405248035800551040410043c1401c411200042c00c040d03000903401810712100781200300300406c62030013036038441040f11801400300314682c22915056030042c00c6150126041c282c1e9078070f04444040072208122250716 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 996068165 1250 996066915 996066923
    0x110307140d08060a150c050c040c082a090108060a031b1d0402030309090a090b0115170c041e181b030209060d09050a0221010c090503030a080903160c0918 68
    0x9625910200c00c94861b40c0c0c460042e41c00f4401c01d1070042c03507170300e0350320078200d6181c5250303a1340d20b2a00d401801c0100c0004001d41021000c2c5556110301202c0c500311307040d00c0310240f00f407906988a486010001d00c504869400c00303456841b00c20001410750030b405810004403000c94044840d48050384050044011003254040d40640017017005c0b080314607104025a522423041540003680000300d4070f5040210360260841040007941109980c40e40d40c0005042614031049181c0e11081d140c0280c1c506c900d8010f40c46a490640e8001d041d4002d1040d0007550358001c0d24000640e4002c0109410843c1c1c040e1003107101103410000b191140c00720492090007152144400a400f40c0e00c1c1084000791b2000034000c0703407401d17031740307800380c100c0600040ea100301040c480c0106481d823044040b4600080d107400c42da8007215050500234001000c000f907071000303c2580d6010b6094105400f4a81e01d180d00e16080d44500c12035803514032074155006040001d000c41d10001e940c000321040218540030502c4850f100880d400181c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 996069415 1250 996068165 996068189
    0x105070905041526030d061404020c0a08160501021801141303150f020d050f07180e0a02040b0f1306050427200912070312110307140d08060a 62
    0x1312000031040740d20038a9040e2800ba02d2003181a008009085812038180803050a480341801c12100d240d0701006546040111070452403e0a0340c18204e41d034400081000304501400304101c1000210b2592100207030760840c0003556614030b581c105c1c50907511002e800310f020075002103e00210711f03030190a0340d14410480d00e404070440e04580324000c0e600c90203403038a42095111171004103505518000b6190131021501e0200700c50511314200a20f5000c014403a2007000000c2d0298489052100d4002c4100c4103c80703000e403003a4a84603508000784c4078940090845540000340c90307500741c040038000e00c4180e80081540300542d0700e03408101c40910807840341c3c040112031080700c04c0076804c401720840b803c5a114000019000da00d82000c01c55216074214660038414046600389280c240151004241c0e00e010020300501c1e030860f500c2d1704e460044462144104840207071440b40c0300404000701c0e800e0680201e14400e49140d20b07803241d542c0d00c44100d00e100004041201041d203505010700c5104c1500e1076248a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 996070665 1250 996069415 996069419
    0x12150f07051c24090504060501052d21030408150f0a020901111603020f100831080705100c0509040f020d0e0d0f0c03020d081e0901050709050415 64
    0x10b2000703803401c0c1030500b407001440c1c000e240b0a40c032042c1d410b2004080100740030130030b071400d03081c210100d5605078041030058174401c0c8a08541300c00240c1d01042003180c94285178500d0340b03d5010410341800170b000031410801e620040541510004003802c100d406000441d0030513581708488506140c0265903c00c1054103c80200e5010301254019014586d4103250a60b070503040d0303005143c50003580441c000b00f03e0203280000d00540c00c007005004d2086105442c403600805c0c41080c01840f16000828924010109030021400c00c401d6400742400581c0002c10103c0020182c1011181540440320443e900d21600c0741c8040e4400346401000348000854417428185076650341400090f000e6000d0344000c26500708001c034a0b90f40d0510580107450200e200070700c3c0c1c0000c0584041d046c012030607641010300008a41280000c0d40c000740101d144806460011b40c3d5440c0ea012008604442d4005800700c8041c4a0421010104c1540528455416942c1c2c0c4840e07980e482052108807080468150344254a8880c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 996071915 1250 996070665 996070717
    0x10c09031502040623070507090f0e0f0a0201030914240f04050717030405060316170f13020a090914010606090b03040803220f060b150904090212150f0705 68
    0x50810b01c2c1c0360000340f0b20314180407665041d048c5031242c0c1250140e2a51842c0b100f019004074403a000448854800408081d00d400c16601d42d50b440c0c000340281056214549503003008800c00010703c1128200c002c54440c02014000400c0340c802d0401c0d10800580c01d0f6002848101030001441e00907500079001d030003101d003012404e800700300000300b0342e0900c1c0c40304010001d201d44600d0011480382c00c240120a5034020383c1003000300000c2821002540d00c80000b824403081c031801c2c0411742d41000034036030100d00d16007540c40440c20030302d041c1e805140440c0c54845000c0a000d5058a03443e0807403080c0c40208112500c42d50260780d08100c40c000d86121840500000c0d00140c1550000c54000c41a440b44030b121558801002041500801080355100564264682000040d000b4860441d40880c0c140000910030f5103106c15034022040f1103441540c0343c1c21030100f5034640c7c1c441541c13012104810340d841880084d0036072549200030380380d02e1001b00c0c0e5a000900c19622850617110f082c51001940841e400c60560 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 996073165 1250 996071915 996071957
    0x15050f060f01081816061e020114010909050c04060909150c021002070f0803010f06030c05180613050901120510050f060919050708150a0b2a010c090315020406 70
    0xc0f14134a079200b010751030b9010644c40e2419100401e01503642c569203944013100e1846030910010f88206680c14800100750300c0d0000c580c1e45040d516000800501019581421880d00007100c02c8c103a0064507002e0080350348074140e008000c245000d43d6030044420030240c0100e0841702c00b98409130041e0006022600540c00c0c5800503c41030b401401c401044907015100d60580e03900070b0f4084140c0441040f0200070b0150503000700e00d40301d08641412410004190b2760121106070250449200e42c400280118041282d0085d5130040d010107841a4010b40e19611022024124000191268403d0368502c1811850500407580300700070708507075040c0da916038500b0701c081e8030005001e200c1450700f41c0c800c1c0000c1c801030344180381c402c0707499656203292400d0204520109540f0045000e024402500c02030040c00f41035000c03501c030850100a07429445146001d143d0107800c20301465003140d400d04180c1c0460f59031040090b400d80340200b2900c0008542d00740c12404038803e510070000412a602009280e800c0810 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 996074415 1250 996073165 996073201
    0x30b0306060120070302040c050306130c020c1203120702010c030e06100506250b010924031b030618050105060a0f0504180209070f080a0c141615050f060f0108 70
    0x111551340d07442c0e60025041e51140204080011804401c01c003481c0341c40350070040c0e1309200440c200864a51403400039201c103d200d1401d4050031000008001d142d00401c00c591006010018903e00780c2030294009010300840056240000d05100c03000b040b4050203d0681d010780d22120902041034640b030144003040e00180c02485041c800c1090200c4061109031280103001d21403d422900d40d0b05203805607080750798481102009103d42c2c1c818a4560781041030b48030560340c1010401042c488404940e844100c4180c20040c00740e8109003c3c012302c10301550f805844544110000c0c4115503034170051011621403413003411250202039000700078a0a2652107070610208103642c1c3d0302c02c1c008076004610144d40541d00c080c0043d007107050320f07227495510410240c0c000351005d0f01440107410001004101d00c60b003004168107004001040f00001a1981006100980c403210609042e09001c1c3d000700284421030300300a0700003003080091b04900e4040d121440b8100b0584400d90705d034503444100000e480d501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 996075665 1250 996074415 996074477
    0x20312060d060e0a030909140c1606060506040803040f080303090d0f02100e0a1106031302091306050f070206010f0b03011514311d072d030b03060601 66
    0x19400c1224011011300003019228029110f1a201c80d2030511254111040340391074800050301c25061104071216501280e0304d45800070412070b085009810448010700d8154059a40700178009400601d2000c04406402241c496100d41d4400b02d41e180300c0d040c2c03644000c9840c104940c0100044e08480da010340303030100b28030600d0710443d0f8405180507200c1046803c0300e2002440d0360300512100d800c00c0000c28264005031001d0f142d460840c1824020660710101ea484001d20428002d000151041c09540c54201c0f001d8200000303000a0402c040700081e08281034400c1d50060160a0002c60b40305904420700c0100d03400a1a1185140e180403040052440c00b01031400400c007042c002507114040341809801d115035141000f18a101c0001603d051026500c1c0340812100d0b00fa4908011896109020001080c400111a0740c0fa50701ca1504880d1021030f10306a511440030024218140e40c0f40030719000742c62149803010481035256504050781c882c4112801400240407200848450160807554171b40800c0e8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 996076915 1250 996075665 996075671
    0xf03041703191d100e37060912020603280c020609010b01090b0f03060310051e0702030309070611010e190b060901031703060a171c020312060d06 64
    0x2107100c685020742d80342031020000d404101202c03601603620306074804144048030101c4501054510103000714105160036886085403406414600c1e0300d4210f6079501d29111200c01c0d05d14440d010a41900504a0240c00002a818040410790400c1855a0100990020b103020308568440304404030001c49159000c0c00112180d80c800b034401d0550145a00f110b0068015150615100781078500312801d94a00a0402554103820000004490111803001416200f205d030b8a607074410101c0d180861040325001c44514050402400700b07042d5000101d442c0e403007014510507444840040b6640c0c00141c0f400b6140f42c010b41401c1110502440c0d241c1c00d5814028004030b00c0c40000e0031a0750810f60640506003130f80300c0800b010b4040100080c4011303071044049801e0303803440d4119124040308881d1550318030703480791000000c100c2030f90701c98200c0b00003003444815581c48540d80c0d940564844e424882ca080b58a000130140014050000c02030390303030502920000d481c45540d01c82c100036807846080d0040e035465075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 996078165 1250 996076915 996076927
    0x2b11030c0711011403090703030f030b0d1203140c03160f0f0305061207080c04180b0106030f02090d0f14010203130f06060801020c25140607020f1f08090f03041703 72
    0xf134920040c5203e0b00809025218261560401908036003603120584101841d1010720042540c803401250380b4a42c1203111041c44620746013080c3c005204118460b0302c603101041c204003518101c40300440c8610b0808010156151041c4c00c182e0741d101c00c1000c2c03c408a0302c00480d98006030701c41e600c416440007006000881075641102c0ca242041d0450304942d246411403c404d03811800c01d80240c88183c00900810b140410990b00c0d680c030302440601030082010b480b003520240000d10343d01038422005004080c07507844003161030104c04441c1c000d01c0031504058140c100462180041c0700307881c49a00710008980d4020744541e034854071280011390440780f55690b4040465911024405424046009802041c1d50403100e405040e0404030402580c20303015584c070091104202459564050410994440792620203a2002580c2e8010410b00d503a00610013407030f20a503800301300c0359500d030440a40d286d100b0b032510b45510302c1c0c2d1242c10191b134040707130380e40100030400507a00081e10f442c1c95084404145c80c10702c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 996079415 1250 996078165 996078197
    0x2040c1707020a05010b030d02070605160524130b0a09020301020c0102130303080a1a1e0312030a061202100c050f0109030e010801090b242b11030c071101 68
    0x1500c250340c40401a40410000002c02400340324100c1c404d86c0460051200202c5031030002c0d5112454003034041045070106810440d100800480801554410240e0f80d200130603400c3c1100c1c00c20394001200c4400310f003d000c250f8808a044d81d0020140d001051008035541c0e40c3e241001400c0c004001301d03015035080054409500d8288042c01da00081c40101c030303002901e9410000d100400141102e07a030503251020448001c2c01d140b28200c20f2210540e40070080801e8031100e41408001e41400319050b001d035110241d04003603047e00940c444d03042280c080140980711040700030010404180203400001c2c41c108585c0d22801400d21544840c400d5085130040800c0310003c1c0d0954090050880100b1804003280a540d07802c01c410502418400d1400c105c01d40f510346c0044e80700d000e14007628400000c4215030440c4138450310112030a600c9000d061849503c8000702a1085c0100840403082182c54016001c20741d21041c01207030300900b252512103042c81500d071960b0300c03c4900c2040c01414403a82029000b00c0c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 996080665 1250 996079415 996079457
    0xb0720030702040507050310060305270c10031406040b0406030c03030309030806040903172d0a060b0702060f030c1b0607020607090f030b041109190b0603100302040c 73
    0x891211000d95150801481404296107001e00320205102c03003402041002c020710503d00c41124102e03c3c01240c00d450705d841e442e0b1601030346036421204400340c11904c43c008200040749105814152a40e0030a000311000c200c04035031303001350654008000000407544515198100c200c0d0080f00a00010344c01d82d42c2d540703132000c14046030300482c0860746440260062503001641a5480300007510248071649090760028903a4501100c6107201c0c2e150180800c0708215010700004004118040c40308080c0707120114107a070742c00110b400040280c2030550100e1203e080d0b0b030a590216070b0203403056080441c1ca21801c503154000610000b010320007400300b140780941e10380c14107001c03a102d04054085400e002c0c1c402820315200910440520042042c10050243c41d002600102c2c1d8100d503220360303d901c892070004960800c1d0100306600c0690038003486503028910804242000102d102040019a04003c1c403040b80011901c444c0801b4000d4801c101508094000d440360804a140c0f100541c0c01c55880d17a135076 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 996081915 1250 996080665 996080717
    0x1809050606040807120606140603010315091b1703071a1f0b0d0f050105012114070e03070608150607050319230301050d110319050105070801060c0f0b07 67
    0x1134240d05e00141d003400700c18421080584107110442c00303030100c80e401141c0c40b84410b110080c00d9209440540c0350880c441d43c4100c6181d580000c1c000c0007000324903803c0b28000b0240c011040400d2403c2800080b0140c00801ca9060a50058603581c031804849848104010000c04040000c0510092528584000700070310018080c440d100640740c1802240000844006130032061440b4500390060109070382180000d4030b0700881040e40c40b008400405840e0150090b1f20311864001c000405018003140c1282c15070550600a42c100d810036592002e0484481c0400e0314013240609103124010300070f0400e680107001d0036001ea4201c071301d0500d4803007000602e000c04809510010742c3d0301c1c4401644440d40084422401100384210342517506080014482100140c001492000030b550340d00b00d81c0d02c1c24015a100441d5180c5445095131031420124043c100403203031100000e10398070012a105020309110880b80360424840745000c034469541003c000d001810542c00d0000c1030306180c1d00b81c41040c98081c0c0d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 996083165 1250 996081915 996081929
    0x13020307050a0e04021c27111528140c0706020115032a050603010902090415081911060c0f07052b0201050d0207030507121809050606040807 62
    0x40d4800003110b004100301c4400040c103106600400400282c1d03005004005802c0040403000214919000003850058030003100704030380302299040e00010b100804800d20403400c400d50f0b0018900b500f9440d0361015110303002c0390a03201e0b13058408202d9424944840547c0c05549420301150440303480707020f90070b02d40003841d0307603d840d91040342c09100301942070294034000d102c0c2071100c42c0107a085503a19003411803218507102c0d0040c038480601070b802c07821600f59401440041c026664950311501c500029621403103206010300d0915060140f0b03003880841d0b200c200c0d0b12040281c00e1403940e00c40c6210800c0090071044e2003409500564011076517865009010500c4410300030300c000d08841045c0d50a000c5a6445107114003280c150b1442d008842000b00c1040c2c952400c440300d4610000e10050301d5600500c11300280451002c00e80e61304040d040001030038000d010740040742e0558020001100d2412400c0f040000b10b180c00401000200541e4202540000c001403285013056201e00c182c51802a16511080b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 996084415 1250 996083165 996083167
    0x4030507032f2109120c04060305070311030607140d0b0907020313091a01050a03060e0a060e09070602100b030c0603042f0607030e030c0406090b0a080f15061302030705 74
    0x80101804000940c005840b146940710f60988041c5103044901880361401d0091841c14150501c8407018800044400401401007290715201d0030725596a0385180002c4401c540d230740741c010782c80340740c0051428425901680c1c0c11001543d000580300c480d40220002080064603416030807410394078514071034403c900c164001c584400039254600740303410307c0ba0311100086280180c041500008198402500c0e002804c0c42a540c0060700b0088008100d1a44150380d42c66400c804e101c80000729400400c121541c2d00c40a951b1030311583c101170f0701c415040c821302016902504e007114422600d07030060108004020286d0f940c00c503204010644561041b07904a5409080041a284452120103590041007500361001c82a10000b004106148100d00c0b020b4240108226003030215501045000402c00300900709024039503980b049080501014000c0b588559103403c0c0c003280264000a0743c035900c109a20081c5648181d0380200a80c20b0070180119402200d05024415104020f000860003050750703550315 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 996085665 1250 996084415 996084497
    0x1e08030a1d031c020d11120912060c070606060314040b090307020303030a0c0917061306021c0b0312070201051611030604080702100f02061b091201270b0403050703 72
    0xb1704040041d00604140880800030042004001030380000190f19488215904c400d8000000e014034005a02c0710710b0f910410302004010b00c400c1016201036441004240641505e41400741d0945803d032030810340040d440f100107404200700d050025000011941900d180c03046a4000c241541e0040310304501c01034807440c2c182c0318568809421030051012002002d02c00400c1c11a8a45401c006080395403100c806040240500c65250704503100107800d00107090480c1c1d04a0f01ca400a00040b51030f25120340070b038100c111600602c8604032004941d059503010320f0280100540c0e4050042200700380e96144045484d03400c41d44003000b01c10b010720f00034500b158503082d042c41000303603071081c5009800401c1555541840d6007a00010101e40101c0300e0000081200702e0003003600300300d005101059500821121030804070700010742c400000c20381a040e05003031008601251640c1d110740641e0041100511030b0000700801d2003100039080395482854441c1c12220702d0b84032080c501c0820503030f0102c4800e071a120 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 996086915 1250 996085665 996085667
    0x5010809060712241a0903030f07060b120c040c020118150207050105011710021c200415030b040209030d0f02160902180904030815120f01061e08030a1d031c 69
    0x174010b00ca400c0d06000b503140c01440710100ea10781c01807102400000501191040c10040542c000750318840029142da038030a48800e020b613039154040e44042d400b0764a001b203480c4116106014480c0c0c500c014420704190b801413036641e21505440c0d0300c1c554100d41d600b4010100090003c1c050035009000c010010340844943e4803010f400c10440c510074100d454410013400c1c86c002011041038500e0300402d407000440340c01c1505a9100001ea4081c100f41668000601241d10417011540601560321582c08110310b00c010014401240b156648c1240d150b0301c0f01e03440e100518803508a402000002e841540c0c10b100d0311900c2015140c0c1c5e181c000318101900801c0324210200600180420b552040750883c07141c1c241502c0c060404d01010340604440030080241c81480e4035115a00c4214600b120110b6101072403031082c80d8005c194500811220009048201408003030125000c401d440c291406580f406049000540c3c070b10350404100b50b0302000b10006131702180d03020701c49151082440800007094912620f0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 996088165 1250 996086915 996086939
    0x120c0203100903170c070c03200307121b08010f0b0f1c14011e0c0806010207080304060e0406090e011b03060e0f22050a020a0501080906071224 63
    0x39960700492406011202280c2d01880c20600300004003100c0132592904443c24009200e842c10180500010078000000c0001e5508030307800500841e02c002100682203010075407160b541d4441c105403540030b0032096004c18040d4817240c822003400300301164030503925903007142503074a14480c1030130455890441360202e0400004030581c101046801c402c0c03c51107008505e400c5207800201502d00150780c2c040d960000825442002084214503855181c9600425020b000e420402100c400044111001c0342c0b039540001030f104240c1d2140e10181d1b0230281041011960340601e40032082c0c1c0300740c0f07641000407141c0351842458140024500080b880103040c98924002100684009080501d001000c01004107070420141c2c00880802120b146500c81c502070814502c3c1800318030380c281c0c0d080300e00c1c102008000222100014800e42e108540240c0d85c40055590769030440380508240c01c01030028081c40d100341c1c42d920340681a00070000d8000c0b60b4178050364803c11f060032540003111502741c041c400585544 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 996089415 1250 996088165 996088183
    0x903060c030f0705160609110301090f1122050a0b0d0302030a030b19120f0819030b030606010909050717010603060806060d2a0801020f0d0b09060913030c120c0203 72
    0x81070203481c1c105c110495000340b08804001800360381d070300d0400c0010403c0c07101e001884018002c000748040704503820a021101080e43c8112030b0100b68503420340050500e590b5119000c0f051204903034018411304045006040d004000343c0a6941d60320741000190340d00204264002c1c00f0364020f60301e4005080300a02102c1c1440c840b64400c84649603a5400341c02403000c240300365800c84250650040503490315004d45968000010840e42002c14200c0d9181c9222510300a2842c0c02e90f400c0c88020312110a0540f00e00c1d05a840d1070010384455014031007080213400c0380c1c0d0040c502d454031a25011100400012104d1b00703802000c0084d48907102040940020011150425411034190805600550312000003c4400e194400b00c8044501e1441c107902000c20a030006180c0c1d0b000a41d640c1c04001c0c0d07070404035071280614a100302d10342040352085050101903140302d48009441d2141d10f440781c0c0204181d9020030f1100720f003003041070310442001074100c24002204400079181d003400b1fa0054810181044005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 996090665 1250 996089415 996089417
    0xd050906180c01051c0c0f02120a0c20090c0d060506040e1b0d090501062102030c130f0219020712030e091518040b090d0e040c050903060c030f07 64
    0x3a092810072000800c0040030904242000c0b41e480098020244c041d101d010400c40240b4901aa4103d0395904400354000392405a8203480c050030b000c80050f8094021201680001900e840440000400c000d40c0c0312078034404044032010b441070109c002520828103c034600d440c400081150354004190340100805000100c0c1d24078101070401c41402c0008000505840c80c0744480c4504405410b64401100e075109401c40302400b18110340e0804c00c4c040d14052081e0390264107641d407a84640440402c3da04004e0358010094510b0741c0c030540c1040605200c2002041400d544c44812102001151004105050010003002810010a000607081165039480040038401d8801c90702e000a91002c0b80405091084030a402d16441d1510748800c955402d80100c0d80101d180200070034034448a44a5038421840f541502c5075599035600c0451302c0f01251403003072012600e000368100301e03890305800c0500800614070340b0f54248a80d61000078a004000c1c1d0710840034040000500c01003904810389203520480c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 996091915 1250 996090665 996090691
    0x1090c0e070504241413060806090103030507062c0105010e06090903040e090304050a080309040e0106080d1b0602160b0a060609060509030708030301150e0904080403140703080d050906 81
    0x41c00c4110708200714490300d811038000c00004d84566080c05004806042c82071007a250361100385080140000c1c0485000e00800700d40c2080000301117180c51454141a42c0d0706036601400c00030565200e03c09420118a01500c0d0544c903054040250f2044128100705810302c400031801c3d52505034100e100b0200070b0060b601500e407050070860b200200004907001c58441001f6031240e80c0c0c03003805160441c000c0b42c000030707480084880300045910000028120760241210104502c00c15000e80b1802c8030241d105600f2150080c03c2d80001080c0914550f00f03108180ca805c0601e5a06203980e540202da001c1d02104006100e000c81e11814041d45501160303000224210070071002d41001d5014040314a684a118104200050310411a480500060300100080b2040b20386958540c0b039412102c104100119000894440001c005850300d02c001d54080c54210810620702419500d0f040030faa06403001440c194428510b0010003d1510b400a10b005030801ca40001d0f42d0429211a90a26030080d01c2c15080c440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 996093165 1250 996091915 996091919
    0x90111161506210f0b0a060905060a03151a0d210c080f0d0b1f0f031e020307021203150909010902011409030a0219060809030c250801090c0e070504 65
    0x84221100140c0e400c0201010018052807a1106003091013040040c500c0b001c2c0b005000400c10f054110070141c4640100c14030050341c40720284941a0203e01c4081c210080c0082c0414002500ea40140000d02da00000344e4107104295010501d4440007020031a044038a01805413461005800c02c1300d6a41c80c9450004ea03100100e4558103058014404817120a0314001410860b0350220f51102001d110302400ca5803802d0810140001c4810502d0281c60100381c1e0b030103018045620a2255940ea40b04034003012266442d4030308100002c0d04010040c00a5103d04110141300640800145115aa07100018043c00390b4001c10b0000041020341a4800c4c0da040c800c2c401c0050b03811604116101070328884080e20b81310300c0c40c00030f4070749000414040c0d04240b06442501c8103c2400441c00140c0d40d0316100d012550311184d500e503a4a11812000108a0f0018a050120820340e04541d8991460159000e20700d5501c5100c180e0861340d6160b8121100300141f1010402c80101600303031075100384a410540d017814 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 996094415 1250 996093165 996093179
    0x190f060e01090f300f051c02030412140a0b010f0b0f0a12060504020a0206040203011104060206040f230c0a0501030c0e1203040806040b0a0e071805090111161506 71
    0xd0303424041c41e0404203105130140385020b0341010041d10a00c00400b4051410001c0c142080400001c400c15503090185a1511009901c200c8016040150b594000c518007490940050305408290f642242d89660101c1d49a084020070400602003500440501c01c81f54502010b0f03052807080f540c00040c0c81041400045c00508000b0107480c1780d0080b5082110318138080040c5803004211a270482540248081900d032082640055007503c00d078421340c020030082c0c08c0c6100f00c40e218040c5204440042e030000d030005000581c0b40e08110682841f82c0752159084041074041202d40703000d4203600c00c0b5079000049040c0c45240800601d8000c01080c2010442c1800203d001401c080c88103182038044c070a5081204c10780300d810800c9600900c40c2038151840341c00c2030310b4103048203081540c3d01c1022074203094580701550008984007080312032521110348078000100315040500001042c8040c15561003501802c030381c1000004041013001091450780404940c07604840d400c4125020150305850302000388880303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 996095665 1250 996094415 996094439
    0x804030c0b2701060918020d260304060902033016020d060c090905070e1c0f03110f030301050904080c0a060c051308030c060a0506190f060e0109 64
    0x40390708018101400e42d16410002c80740045448900e00b04003010300702c12a0346a0651140d0251290580f0a00015039800c4030100720143d20b0310041d5100c030f00c020308240040c141c0050010050540f02006501c0d4030340c548094200e070011902542c000c0e8980119804520301804202c545440c0e4808581c1e108540e541d101c00c0e41207003030750101d00002c0001080410740c8a28281e03a100107a004006900e03a075034520703004020341030341268480480c40e40200403491440e5800350f6403103200c2554540071002200010400c1142e8505600f10f69211010003210128407152a0102c4490294941c1c0b1b04455902030068500701905c125444a5001030005000d05e1b070f141051030380c0054004c80e105440d25090480b19040000e0058000d0515181403c00c038409600721001c1c0610034000002524440e941e00141d507220b00c200441518035030405000100c0e01029540900e801c082e0290402902c83c0d404d54212030900f8154000102c000000c00007044095032010a02c04142c1d0300b0300c2d0946510345482407411003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 996096915 1250 996095665 996095687
    0x405070c03031d06040602040608010630020702060a0819091e03021507030e1006050f040f0b042d200705010b1e03060912120604020c0102190f080403 66
    0x1050f803200310700c5030400001600b410200b07207001e064800a08181c54880000d521900c108404250450000203c640c0140e06100351400ca64120b180940008401000203060a151404189500380000d0001d03860741c0c00640171901c0b580d00c0310341e081c0c185107010359103104042c4403021801d0708208178000080c10122038400c211b01d2031001280b00360103519045e82404c0254600d207082003480c2c020002c4203681030300070050341c82c076850503242032200300c1e0008010b031842806201d42107592082d0610150074250300024000d40b080301c0c00159064084000703019100040020074911084400e80c800d1200302171358410500c0c0c651030040200108566001c2011602d41e070160a80240c0800d450044c01400e410540816200400303901d81c40380100c2c042450926004042802841030000250140d00c000450840382c80d00e0301d8510781002101c840000c40c4c1e4000410158209809001907004c04409002a002c15005c250035800da403440b80344000c001c1600c8480e9202080714910034080400c1e04540300a034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 996098165 1250 996096915 996096917
    0x20a08012108090315070903110103111210082e05010501020a021302130b030708070e012c0a030b0412030501050f06090d0f03090f05040603052503060204030f03030b0405070c03 78
    0x40c58101000c002070509001641c0410030900c01c0b0200a440c6e58400d07891410380384501c10515000032100011002c0740c5c2c840780602051134041062041c5001904403603603000b08000c006000150b03c3e41400c505000c414200c5016914981482112082d180ba1035445401000e0604000719890800000d43d50200c8101c040c0c000c1400000c120142ca00d01d404880d100340c0340d000030400b81ca0361407158a019034012214040020217840c0440c50852103080300082120301651058046ca8401c600c000380c0508510106000401241419041c0d880754100d140045004900340704a61400f4200b02884410341400d050405107004014007807a0380e0707541c1c95a9560030a031032a6885001e12404a040014a000043c0c0f0455981030000304069000d5241c1080c0c1306038a140c070500300e40d100c05000076589180801446500581100c0044e140c401001e094070304400c3e00c159140d130b603a90702c500b0b0499000790001e40c1c81a002c000c02c03005154060080b000b01280603541084286405000100b0300049808001c0c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 996099415 1250 996098165 996098167
    0x10606020a080d05041506030c03151536090317040c030303092306060a05030a0b061504052205070f1b081c0f0e03040513240603020a08012108 63
    0x1e03051000c6d22910700c034802100e090400200d922410141e4828040c0e200c1200d85a501c00c10030005503c650099070581c1300d0203030a8404003400c095441000145600701422170100e4542c0c0c000f01d031007405003095400000084001505c00d85070400805001500c20f1b022400e2880701c042c8000100f5003080f40d0700b149d400d80f800054009143c171344141c0300784000c0320a103c4503084000e294038600011403402d00174901101c22900b002d03541c205160b207610a80e4800307000c120003000051558109030404d5117009060030b81e901e04e4961203800041600e841040003160700120044a007940c80c2c03062003010b410041070705006c1c003004c04416000f0031400c18840002d0409501e4040001003104000581c0c0d18840460b207221b08410700c0d001280000c004828010704017a040600105a00602004403000d884019140202c0c800c020102c103000741100044402205150124104d291000010000007410595a0250b56489150740050421506030011182200c3c04003140b004d14010240151030304da8000d504e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 996100665 1250 996099415 996099421
    0x1a0c0d0305071701180e072702070209010b04030605010f0506070807020a0306051306052520060a0e011d07090e010207020a08010605030d0e01050a082203020708010606020a080d05 79
    0x22075101c070240241d046032507100000450710b14424035405003454000c400400014540c01e1b0156655080c40c03091911150400da00408500022801d41065491800025203130002c13550200b0041c0c05c00b40e10404603260302040030f2007080094050f15005007102d0079003051312401d250025105104200000706410301c00510300d800c540b900d444010003150800c03000c21061811845140c06000b00304011296540b0301000190300c020241e40042d0101068110b4620021210400341c0e0001005002c100100d444c034500319229603001c1280c0c41c07203040c150f0000318880c054441c00d80d09503510007030f512100b032100468070074901500003425404c590815402103511409040e26600901c01e83c4c1c006500408000c0e00480c014505411074012504203404440b204502804e045900400940d802d5000880802c81141100d00c611160b68210303402a039090b4107504400286205984a01002c0b80507030068141088080020301c204402880c0d640080c14030b0100b20f5032a0301e2503104800ba5030256030b940d40c000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 996101915 1250 996100665 996100667
    0x601050904061b050c0d17010501030b03070b040b091c05210909041b0b040303140901050c03181207030c1806080304081005011205030d1a0a030308011a0c0d030507 72
    0x702e80800d8181c0c0d814401e540103e00001041544959104000d41c4981ca240c801c0e1207104603400480504000508031059084c000118082c0401e8200a94503105d40d034404980c420a00b4002c000071b24120700c209644500003806d02015a841c0414140710303100105525020480200c0d80420480a0580158204902000d00b090358061582005c2d0003030040b108000410482d9140400a040c0011301c124107180d5403204406144664000100001c555020b204a0002c05034050442d034041410146c0c240002c100a440c5141c102018444a40b0440e51320205981040400744034850800d801510009003036840e0020b034115607100d0540654800c1403000c42132030540d400313040900f070b140d0240ca640e56906c044d6540da0b030151601c1c001ea00c0d0300c4c1000000d4800341a0201100155100c2c01450600c2c81c07000c0c41c00000c1030078601d09036079032003500c0000460399a5014018003071032081c1c441c0c091300e5060074280c2c2c0b580d0320100b404100c501820044e030082c5140014000c4840e1500e86804103507a80c03a008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 996103165 1250 996101915 996101921
    0x12004060807030b030f0a0b010e2a070204020d0c050304150c020c120138060405150703020a150926070b280e0f1c05180306040609031e02060105090406 67
    0x290401c0c0d02692800e1f00c108000d203100755040302c903841c010030041e8960102ca003921041d00b500000c0031220302c0d4000b41d0342c8040440500381141c001080181400a01e12002e810b480c1d80348c400d000010300c00004c0204001901e8a000b440442c0042c0803c40c0000e4041c020390703161041841244a10700d54030100304050000d40140f0380350345103841e1804030b01200c1d03c010007400c078440d680c010f644006120040203a05203102901c0032908018940d80081ca072a1490f111990300074041902140103000390b01c00410052000c062084018090000b02d56400e82080c0d41d0b10340d40e9121406000b003221080300c1ca45200b00c0c00390380700c0c603400102c200f00340d4940100c00c80046041e50f01103c11003611100001d400c00c819032001c1e01120303001098902e29441031000c0342c1c4682d0181c0c02808466016010b0740620b91040016143e27466002c090350b40ca121482c1c000a10340441110105c4025868120480400d41c0c4200e220b091020515116240e4014036240130351102014000e51780200c440070000382c00d0100c650 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 996104415 1250 996103165 996103183
    0x7110a02240d020a03051608071b031707050a03060b2701020708011401050f0d02010909020a0e06120a150b0901080a09021c0c05150f091809012004060807030b03 71
    0x40e421591404c003108090082e200484101200509404c111142c0318091003a0310700c2100955290759250001c48110400100b06907004e0b000c10040f01100e0620400340d040b440d002d4a000e4580d280c803994a500020240c0d0190b42080c0b100340f0090281850350302d04000a103018004000a80c000004e104004030f01d0001542d00410596080880340c01d0880303100c0034450b060343e800741c40c0c0964507020f41e42407080c501001032000b40028045942001600e0aa501400071110310345012038040c501c1038002081504182e10000d03804040200740f0180207490310560107041e04c650260701c4580d2415003052036600030202e40d181444134000015950500c44d07804000c00542c003c00040803203a50101c2e9442d24041c40504172001205103001003400e2030201080c01150b5009094039250004001208020390024440c1c02e801001205540b2034896018010903c01e9809900000350a40c40044006411403401d010040d624810041071008590110312541d0004036400c0224850009401003440d042e200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 996105665 1250 996104415 996104437
    0x10020903190c14010306030201120506210124030201050f0a090b040e06030d0206060328020303030c0c06010504060e041211070902095b0807110a0224 66
    0x8903010744100012500c107036068810080ca045103001200c00194120350503404042e01052141c80919802400340e0841c6a0009010342a2240b1144880c450200e002501c0d40c5030300c550751910382d2030f5030b0781d903040b282c103050070100b0501440f6103461741d0000b83c030b14400d040d010003000c0740001340e82c0044c0f0f0003084040300500c0b44607401690b550351a4440701c1448029180288a1b01807201070794170803031001541e180a104010080d0101d6883d41c4010070035001201090700d46205141c00d07a00150740c060004e144243ca1055003503560303c0c1501d06650910005030013051203145070500500076039803103640440d442940440305800002c8020003c0d105a44001c49101242c4030b20711000c00c1c070b046550050139030050705a9181c4948101800460720b9134103000d210440d140c140307014180042c03810598400d80c05a000300d4013041c040300340e924007a01034409806040231809a00034410540d40c07144d1005503401b5070002610f0544116030000b040601c241200f580d0303440c00f410410408a039544110350b0f9031019 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 996106915 1250 996105665 996105703
    0xb120a180326070503010918050d0e01080112030801031e022e030209130c110a0c05310b061b0724050712090815010504061710020903 59
    0x140d40390040004a0740500c9015004001040c4030b44280091101400341d20640c4075181180c2c20010040d000348282c45000e404c02580e07840c00b5001c038400f400310140c1d000703480e60f4000113400c59900140c41e076001030380f00c061011034512007030000c02d51000f1406c1c10740751f0080014880a812120709140e110b0000b0000e5800301c40305107d0b4680400c54000081d06905580c0320007003c200303141d01a4120300a0051240e08085038001d07140700100340780d2080101c121942815050302c000150b20a01e41042240211007801c0c84000070700140c07900c005204c0c1c6030141200341e8900004130000003680e030501e0202c00340082d40c4920070610703155582415610f21900c103090805141a0800c0300c190f0f90f402900ca19500ca4a0301d4950400c00003d400700c02ea10408540c8401c0d2a010180d9039180410200e11896000c000c8503c4011485200500a07860520b880030142e101c5541000700f004101c030f4240d4400c000b8606103a2007003c1c032030f9010620354a03d0341040c4006072109007501c0404e013440c0c15040403083c441c40b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 996108165 1250 996106915 996106961
    0x90d03090e070f0201061a040e0a090f0c050a050d12230c0705040507050705060f07200303180601050a121704080601060f03020310030f02040b06030a091109010b120a 73
    0x15026281c900240b0f80c40c0d00034085c89680b401c07a02020044e0328a9010302d948104000d102c410f200010050300300f0680c65000604215030f449041c80e000542d003084a00000b001010421454042c1400b0b01801c1d00b194080c0380c00700c3e1681c0b40070182c148004000140b280f0700d1894a04582c0d0600200c0043e00c43c0b002caaa0740300c140b815141e885a2080c06414452460a80030441040c071030002c2d40e018580c4440200b548e92034142c217003211182d00800c030f1404c200ca6000114036070300318035981200d6454003000550700c1e4101500440c2480d001047da04400380c0c44407004104541e641e00c00207080350762000501c001031044c0d080c0706640d90b1090b0070040c01950700203000528a60b00041403030488401d603036104220704c0c0500d0200c091344025500c14060180845050001c5a4001c3c0200103040c80140002001101003000c140c20390401c84131041c2480d0f0344c40000b0207100b0703110020160040200c401d0400b41d0304041ca60617080c001c011030100d01481b000001001c0413a5980003e84100e04516520030003c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 996109415 1250 996108165 996108167
    0x12072c063d08010b21090709060308070b0601080603070b09130507020f060c0a0807030f0f0e0303060112060308030414190503190503060a0510050d05011d1803090d03090e07 76
    0x10481d1002400000c000000018001c65100103940a01690407040c0300e80c46048004a5104d200162021000e0701903214005034030b04441c421080210b1040c0d0005803141c00a0401c05820200100101c0c10321541038200310b00d03558040341e04c0003506c203050101a00c0d0b40c0c620002c11410b6072103401180303510b80390005015015030000744007001070344407000304d41e040d980d4001520458001c0a0458001c04e95210102d002603010b904803c4001e140300000040c0f45040c0365500040e10104050801580c00010600401c1c4d640b00016400e880d0b5155014001145182c0e100103052100400c060b0a140e01c0c00c048441041042c040800d07000004550022400c155042840c0c89174001354545401101c916844000c1c680540c013507171f2142100800c00d2000500d4002844403000315514110100322041140d0281821184030380c0e030191000d1549c10b400c5801d982d80c55404d10101600d4013030748040c800040c4200d15000402c69000c07103400e5802c400002d10900d01500e845441d504804070122034042041086 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 996110665 1250 996109415 996109519
    0x2100f0207240c1b0f14011d060106090605120709030b0a0f1d0a14070918050c0f2805040608010c020d0906020c01110c12072c06 57
    0x1040e680710810103820709110031390f00301682032140c02000302c444038083c000c12000104102c481e4010680c0b041110500d620250840750075540506007003640101e103491070301c400c101c0c0a02406460814003d11070429102070050300071001d000e461400800001500c4610a021002c001c41d03004c40844400e042c000c0600001d010f250b4041250145010403160380300d100c0c120300503900c40c5150098030000109071100682071000005e02c40b03041c82500700004071941148180000e282c542c0141148502c16032401a0802ca030421900d48101c5420107404907a40e160b00903a0392081c08402c00034a83d0034500340d2000c0d602015030065034401e2070008005404041074000d124512516800e41d1900c0e4001e1100f501c0d00350303843c0280750059118081d991319650044070001429100b003821250905a5400020101045000e10686035005a28200580550f21464070b0f80003aa10140d0000010880f440300b240d50001411a48101c00542442e125040180b01d0f0f007440c180302c0009208a020014115458 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 996111915 1250 996110665 996110723
    0x2706030717060f0a1a091e16120e0601120309051804061503081e1603050901090b0315040f090b10290304020d170a02061902070302100f0207 62
    0x10f19500020304100c0880c0718501141d800500003210340e118440034010a00380c010103040103058803108020b44d505801890611039503440c10701c5040700081e5500202003180340001640c00b141001c021182405006c41c20505581c4400d4520443e40418141101c0440190340140d800074106110310001280d0440303d10f104a00615041c05032803081030358650390810900c0084c00080c0d0600049031002d00324400c8041030003007540094201200d4600c903c6003c1c1501000320045840020070350b5155030408004002010110034141c114036290032552007842d104101548a160b907242d80000d50040c9911400403243c22510070000c506d01080ca804c1c000445000c0c804254403600080412001104e2600710601c0800c589242580c45660907c858055940d0f81141da0100500d1980c4d80404030501030b01d03100f512036004003040d0500d80454060020400c9010b00480d004000e1100403a4001940740c400140e5481c1c00a01c1c0803546c03090000130b0240000092444004107150041e54002c011041c0c0c0b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 996113165 1250 996111915 996111931
    0x60212060909030a090302010818010e100b0315150607120815060903101107080a0324050f151309060807090513120c0212030d0b270603071706 63
    0x490b9210340700220380d01c0c081d400c0080d00046070302c2e07400d0005510520b12240c0100c49030400c40d466940700f010300c42c01d4038845c11100d401c3d5842040c45ca400b8810303a015202490740142c01505018801c20389030f050500c80204100d0002d10f400d200c29803e41c0b5280c1c2151303101500440315524080001000078404007094420658807880d400c1841c0d100d150110807540c51440c000c2c01040202c2c000080708000c0c00c20000658071011007401013401040301803008084140f050354000460f900000c940c4500300c0e0300e20326400c0c500e44420000784007079114451008400241120448034481c03002155548601c5078004a0088004002d40001c260506030001e02c207844038001aa4030007a200c41c20031085450854010010580700d003442e8000c030b154a1040c41e2002514908007074070b032400f41c0200c0c0c40d07601c40a0011240384d00014046400d103800b403240082c294400c80d0030368410480c0302c5da01c5490170301542414080710700000101e40389640c10850300c8018002c40c55204100980f0485403902c4290417541c4c01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 996114415 1250 996113165 996113179
    0x809060904020d1a04111b070305060c03190501030f020409150e0f150c0313030e0a0e0a0c0e030c060a0e130204060f0201020405010f0f03230709120b061c06021206 72
    0x40113a01d49801500000c0001d414000e0922100c414840c2c5080507030307201400c450081c1d240c08004118103003c414420750a00701071720360300e081c01c1e590b44624410b4203003142c03030300f51801005000191480c1c0f1141a0035404403008140d8039070074109100152040c00c100b541c650310308142c02c01040008200656202c1044080d41c2a01c04290900c0c20007030300484213240c0d004401c05c0000c50699035100243c1c240707801f914061161030110030100d1130403e20303030704801103511800c0200211419030340650281d0300c1c811b14104816401031008665120301e9040c034184210404152091014232844a0f50314014008200c1007101c0d05100400d40290300a014020002d12144881c880c164014000c9804443d010303940c0b03084110003240220b03200b0b403000340030508154030303444101e8540c0c102030284030b41c9442014080c209400d084001a000c0743d00365024071004e00c0d0902941000c58900680643d210406446031640411041180008440d9080c80181060301c013240c001541101b400020344182e00c1a42c2c0703a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 996115665 1250 996114415 996114461
    0xb1206090c180402030d1103070b100f0617060111010e03040b0310051005040315110c0106051c0309050d061b020a02030601060e03100b03010612061a090609040809060904020d 77
    0x10788100b140895010350998011070f10b10041e00d100c0e4200c01c4000c1d43c41000d4a05110880d40d94410602082e11000341000b031186041c02503d0701e01640e032009007000c1c20044a00310f040000c100341664010051814821680c009a500b040290007c000404c1101c0640e40e595407110414105604107441542d105240c9200102c0e040c05c010050203150f0180b40c9030b00d401d0919660711f800c3d100c805000351011440d02e50184580641d50726010304100c511180c00458000e00f0034050040da15010030540b01640c0c03101104c0c4000c03070340003103500099070402c6e01c80d09040440ca0400d80c0180c600c1840703403041c4c20382c0b440c0d960400c581c3c003140ca820000d10072000c5c0c900c036903a01c81b0220b0f141d000c01941542e1642040d19101c1e07100711541d001c1e03803000030050b0020511a82e5501000204c0c0d0403810b0640340385444200800c0508250707016035800030f50484038840d142c00c007640810144c4038001c0c0000c1075601c001500584942d207170780036103101c510010300940d40c5554030944070020308031424001072180c0d002466 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 996116915 1250 996115665 996115699
    0x40908071106040302090f06031c0e12010c050403020103110702030307030504140607080f0307021f0603030305061c0b09070f0f03060e011a2806020610080f0706030b1206090c 77
    0x8980440e900140f001b481c0da1a040e034a17401d0701c100a000c2960511507503c4c3d0f106000d0002416501c0c0712425142e000c0300d4442d407420321000290030413a501e51645080010041160003005407810381380c0a00e400100d41c22480703e92221440744002c044d50603c000b16801c070805a00400810950301c138a03669841d5511007106200460003440001882d40c001031100106152060f4041c3da882015441203a000541c9101d074a0030114403041450400b030384456090050580501a03250003103402c1d544a1442c2c07108a41c040340008031518000c107072030128030204820070403c0203500080c01601c441c58018950701c1e05020480c3c1e2813488201c0c3d03164180009070b44550010b01c19000d6260010340404000c0740c80a040000c2c0c00d031800840d041d94001c54070600c20342103c00c146900606200c1d0000c00c03035810714030290b2031140182c0e405000250f00082c540da1038880d02050341011100e2038180898034003583c00004000549400d10345206100340350030083d030400009a5018814010ba420548002a0f240 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 996118165 1250 996116915 996116917
    0x204210302030a0c02061905030702071406120403090911040303030c05030f010905181606110706021506010c120f031811061e030a0c02060703022106040209040908071106 75
    0x1405030141e00240700e20308240e8003a03488442858402003030385280400c00c02c02c40c1e92241c0951300503800204040100003105404001140190a00303405c03406a003240000090f100c0d11800b44404500c1d62408003003030402d401040c4040141051000c14499107190031152070720394010b8030003640000d06101e24907803e035000f40100c900810070b01024145036070810a9070b00c060700002d0f00c141702141070003103a503242d84024044103d0081085590507281e80c5412001040381e0b6000c03030aa81d46030050201045801e40003d6101541c00d08541c00817070300c0ea50000103817042a0034001c007420142d0031448244a05500c01c1500c1d5211000b030f1010021030100c0c0201c080609950100245103c10a4580009a280c40405400502840c8200010b1412201c01a80598206640c070303884003130300c881c08402c0305501031000740d5201d6801d2900714140360ad00409014080e08200540556000135800700d845070f12650125040700c0c8000c0c0043c0000d10103883c2102c101c2e41328450030340c1c0b80d001e144902041454100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 996119415 1250 996118165 996118229
    0x110c15091b030d180503070303110111040b0712260f07110c01050705101e0506030102180d0f120e0102010b04020403030206010b220303050712110d050a0c0804090204 73
    0x40d00a118181c103980781a40c44c00f41c80c02c1821100c40300c0200020301941d041164001840c03199031120441640d0003841402c0d0303250240300d080009401d1000b0310807405000d0503280c6054001000d80b020015134002031b078160030320300307583e100054640c8019060b03900c4d0b40206074010700b002c50400100c0d80e2034a00440c3c010211040f03048607904150741e101c410350f110b100a4900540502d003074074980c40300049460121400e08890b00240f451070640051122514411940c0c040700a130020362a100c10010000707080303884041c40500c69070206183c40203000e000c1c510080103e038040010b41e05176080d00000341c034000c1e0031002c043c0190b090840c641d007642442c1c000c0d40d00b22075050b00201056401d103c6490f4064100503084201c242503018804410f5070000000c100071070107612000d0390740905003001a0301c081e040b1160401c4c405450f10075071042c50006030f52600d40d489494000d444a420080848410141c203001030034100380401c0105144003964010301c00c48030480310146003155024048041c5104403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 996120665 1250 996119415 996119419
    0xd030c150204270615120e1606090b03040f0b07110607020124120b07020a060204140f040216200315090f0d05040b09040b040f0603110301020c070504110c15091b 71
    0x417070030307505a406800074245500903030401045410040078400d03d4443d400e143e5041a070605942045516002070540d0054141c840c40700d807962920f03031115140c804141c2c900510480d049000650307907a10424a8500d00710703214041c1c80d102d0070030040082c042c00f60403080c008420100b0074541c1225a0060b80c07041142d05010308800c1c001d85030744a40317038461001440082176024a1040f440011010f2000744042d00442c1c048103590f82006051007054646c244070107001d584104083c4c5140c51000c00d14400e40d95100d0303480406406091340c02d0906109001501d5014480d038103840c900c4c980c09045242c840c114203000c8860000199400302d03955012a0000e00104001300014420485800e00034151342102800c041031000c01c1102050440d481c1642e001c2c2d41540c3d0700030a0042044100b02c40c031050074110000c0d400c03c0c0c1210955170b2540d026129140c40b50342d480c40200e1007604c122042d1036038502d4410a9900d150322140c80e000f091a0111085203560003194406030130240a280884055000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 996121915 1250 996120665 996120689
    0xe1c0209040f0303061e0e07030204080c0d02031f06090c0309020108011505040e040302060609060301021c090f020d0807030e031513140303160311090d030c1502042706 74
    0x41e64540311011809814143c040684405000c1480e004094940309a803410007090007400303180c00400c261a04015150008241c010442041440e6000400707041030801201e03d0b805040e02807001030300d01440004801444100d81c64940d24142207940080203d4403070082c01d012500c01110b085003115181d010007404502524014446000c00d114a581101441c0c20054601900c0300000202c1d01d9088401b200141c1c405010400d150510680c841e400c201c0079002541080b00c04603c0d0300b000c500c210702040c0502e035180c000400307000b01c0382d454469090f000b900922981c80c00e030418040035446404254003203000c80a410880742400541c001c61018295003c84554917a00c0b600d0600d0490b0200a950015080c05824450b0005100440c0208008454009080b69844010381603450b00c1e110203c03032075428400d4107100d0312911010101e103a40744c9401c09501b041403a00003112a505000807032214404203003c502143c0c84684075485600250340b0440c0c0250400940c020340c3c506004404007001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 996123165 1250 996121915 996121921
    0x22a1e130c021b0607080c1f050402191802130f0b031e0906220c06081b130506130b0a0e0108060402130b160f0b04021f050f280e1c0209 60
    0x12002c064030740a4111408c4c2c070798218298903000c0c9600342500108613504d60310401d0004501c3e0000710b0222030348100c000c041901c0e1900000401c68803c10707008009d0300d600000c4902c0840014181d22010344048500020f00b036484810a003483e400403640c401110003000603026032103a4030303102e05108181c200c009008540e07944056800c0c036194240c00d030100002d00c22402c000a8406221a0007400c81c540d500520380c0341101c840c81c0880390307070007102611520401986a1b015100364403882a2002600c00950341d14144007007860070690b80d4049070801c48045070b07405903250f10000101c0c42d118240d81d160125100d001c100070407442400728481100f6076a041c2002213280320341c041c0c41000c2c505104034443c01305c01c2d00c40140d00721103000201c03450080d0f101044214035122214030701d0446160f0b0385002d0a0424500500b081c4214440076101e030074041111540007421030200300c032307504190f40313803608420884901600c107070450540948515400b4040105180d02d4910350b400f401d4000b401001191 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 996124415 1250 996123165 996123173
    0xd0809010e0a090216030201060512100b0105120c040807061e0804020105090402180411031311060714060405250e0411150a022a1e130c021b0607 64
    0x240c000388a420020051000900486901c05005c146101036440c04460b8510715000707013111a00d070020fa00c614806210000c0010000a076032030300044020b000603680b8031400c0161082e009524185114180440401400c950104090412200084100c45a07603481d0f80d0141c50b941c5031003e0405841000c0d9441d00000f5105501040d0000c0c01030410368500040100464240e03400240444e03500300c08100301e90424105842040b0160006610490460a091109510001c100000500586540380070402c00e83d49150450f00e01640c042450741c030803442441c0041d140c040448003036500f4000d0384a040c0391507180706a400d40c8170280703400c1001c001e8200910003501e1507018000740d6906a200403120741e03d440c0c2d0654000d50002d44903505031a03002c0030718001e140c015000f400c0a094a02d002c05c0d2480307a01c05e103031915a107441c102d0750181c2c04201110340300080f01c145204e20785d012240d81c96280e5400e1150384240203080e190f50030b0b03c035441d83c2503102e8042c42c0c203100c1215810060811001002c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 996125665 1250 996124415 996124427
    0x90c0509091603110f0c0c0406050f06370806030d20010e0312010f0f030302070e04021305180f0c0a03030c0f0807110a0608361c030b0d080901 63
    0x2c24000c0c03c002820000600e40c911803038011071501030740103600041d0a410003504003c0900c070002d0445017800300034100710114558031410f00179070380101000324078040d50381100340b488005580714843c2030344214001c0c040355002c1000310350450041070045021032134500300891b0300351591200d41c0769a406415226641e18a03600b01e0b25010740389541e41c5070f0b031002048040c001440d1400da002100d01965041990807901491151302c080d11618a82c0010000682c010440100300e4281440c41000d541d20350003c80d00715005262118400ca00d0f04c0304018a148032080d908891741001000c980310349160000d4256520500e0301503a41c40b07004800b0800c00a4410904610703181e01c82c2c554040b00384503a5980110310f4119080c1110322807841407051b5801c4c00c105140380e00401442c036000081c2d0800341c8400210902540c4040380c28440704c40601c800e4401554100e0310004040e0803200100b100102480400700580136800010f414030b0413180c858909041c3c602d0312260840c00c0700e46032406c01d10040d529 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 996126915 1250 996125665 996125701
    0x60f0d0f1113140703060b040305070504020a03020d090303062606040b060402041d19271e050325032c0901120b071805090a0e0313090c050909 63
    0x3002240074190b001c41000c0f4040d541d4000800c0800c18000d080c000006801e0b1081500320321080c3c8000d0004002185000404c01f08a4000b901d0040e0b99140a4008801030300c00c8000102c80681483c684604040d45540110225200012025100c0302c01224144041602c440c11200030b0313011801103800705881c2400c990308048020710040c5810743c4d580b06041c0200181905d4010359140301c040000005c801400c41c60000c0c01c180c020407242c01c00d0b08070100e403400c040d91410480f2032118030b88802c011880314a0782581c20800098113100f43c82d0324000d80d4070390010001c441a070801c0d199076449810302d00340845040341d141c1c444400900a400da80340044400d01d80161a40055825421864544080441c0a0004000707142600401428900031244000d029003003007104554600c3e10b80b8840c10701c07040544400301c0e040b5082d07885d68440880503100d514009060ba00000034404400748038041c800d0202d50b0206001e0120407190031041e1407601901c001c80307030081303100c00001e200c0d44e11641c0750500c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 996128165 1250 996126915 996126919
    0x703050c03130303080142020a0c09020d0b060408030f0f25050615100507170a0309050714060d09050109141e01060825170303060f0d0f11 61
    0x10801d428100040241c0402d5441500851a200018048448200c00c8020401c1c0007081500e070300004021700681061103070100c490380c00c2c1c0c54003007010070340d1081c0060283c080d0010a6198419117500392031000350311404801804510344295000301d130234100e081d20102d4494034003450038a1354810160000398082d202c01450110100403000303650101001aa0000d440b88100805142040c03415a25110011302201c03061214288090041e60701d6814400d18441a85011501e07080a450010341c0c041d041c03003a0032401100413462044090345580705000d064000d0089039085942d5880c2105650f82800304190400c0d400c00002503e0003494100c20101d91040700005038640c0d10740c5502072800100c83c0c1d10503d9401100e031f100403c0300303403990300054078880b08000c101e00d9150440071341d81d94034030150f414500103019000e01c005166142d0064010b0910205c1c171400c080503101a652203034030880380c3d20b02c030b0710f8000c51894103070404450200c5013581c040f0107100d00355481d172a00c0b082c25802140711a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 996129415 1250 996128165 996128167
    0x7140f10051b0a1a1005011809060e0403140412061107140c0a060e010c060903020f030d020a0f0302030403080402040e120a0306030b010501020c030a080c0705040c0e01230703050c03 80
    0x1150300b0750105001da5009902c1d01608150f010b92406049142c80c401420141d05030880c1840f1030b00401100c2174040700c01c02d003000c266045000c11510741d4401d00713501c81450640341c640300140101000304040d219a20a503181c000d015418116141b032402180070b40c2003807441d00001c03c00041d4055001c1035241000703a458504000c203139542c010401600c5800700000740c00c9101e8019080c01c02045640c050142410205446004a00000c02040400d2406001c0d681c030307451800e0616000b03012038800091158162550341108440f00c0c030181d40803c911100142c00c1030700e500441440fa2003035a00566040d5a06082501c0f503808100c0944101400c0c214280030b58000c0300d08295500d4001c0c001104691400b1030064510300305108524016480103066400502070001c0940d00403400e500d4582c0c1c00f1a416850308000c00d081407602130581c12044d045441c104408a00c1508550031418003e801da80c0c4034018501100071a0040d4214803020316103a400f80032183c00240204040c05002c200c00b4116 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 996130665 1250 996129415 996129427
    0x1e0f030309090e07032922080304080915130b0a09030311070902030a060509090705010c080a02070803070305032e05010f052116020105040c030327030b060307140f1005 74
    0x340c251805504640c5d698100d00b105e00c2c040c1c8215401060b501c03410440301f61001d00300a5088035500d0755981e400030424807002000408100198091314844140a4002207600720340d44488050740c0d20040c0010300c811600c2000044688044088920b0304d81d541d51003241c0c080c5190740685501c032150141c0706940c0101d003070125a40109102442c402e801ca600d02003405880c1005004501101400c80002c51308940414040b690b00207120050701035110480300d603200d00782e140c22030801c1240d40041c030180c000054041c00381039001c4003450260000c0c0d9030008100c0b407800d58071411610b02803940511500b060604008a40c000c0d840c0e001c0c0900d807414000e1801c8060404501d000c4a4500b580504603520740a00c001000700c000004842041030008200030b003810b464410010201c0d22005003040724000c0904150101c54400c140410400c1c0e13820f121044d00ea01e060030342c8440480d42079010f80b0503600001420040300010b50980100a00400b00d1082c1c05000e000c5440001d05148040c000e00b0486 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 996131915 1250 996130665 996130673
    0x60c0f06091c08060d0b0c1605061816030303020307091e090506030712060207020105040801020a0201050402330a030e190308150f01080702010e03041e0f030309090e0703 75
    0x6654861014903002d07050951040188010115450b400c600c20401c10b401080115103d445000301056005802100e00d0b55a02103042658400c540f400303050080349120300b50030050000b0b4a2401920480a0610b200d0381e49280c075030b5515040506101043d029070030820101c1d000f0f60040d60062264600f101e121174a8100d0303401e17414031140088903c108e2180c0204984080e62103807642001d8200c01a012140c50403c2400d0300000401006c0d0038181e00007a86421a03020b58211030042c2a090025504d40c00b4000c00a40203200489059000d68540b811100d240c4802d5881c1910b51902c04c40d045140020f9401da00c001500841044024960354004e00c0144c0d50701000f05200011007000d0318800103000746001000b03c200034080c100c2800212079200410f541b0511440038148080c6001c0c1300c281e940810407405441c4143d0ba48a590000140100e104054101082003810a10450840141c2d40d0074131074200c8100c911003c0d00040031500180848421900311400b080064030403140001d49a4407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 996133165 1250 996131915 996131923
    0x403180605270105030415090c0306091205040b0d050a0e030705030a12061a03040317130204050c0306061605070f09020a08060a0e070c0606170d020f0615060c0f 71
    0x10801246000c100c0d42c0310784070240400324901540031400600700c460503001030010300002d04000d003640c50903103000c2e0703901155511504110b904010161140c5503a410030304006c0090f0348059410403014042035114500400458088071180140289454082c8140e440202805000c22410325143d0610550303040040000c0c0200e10301a10140d60703a50034004000d0912180e0800c0c4400c0281000010040c031044002c2d002455640c100c602c0b070382c0769501c0c50111130905800c81284448284a42400324101d040081c1c000f0240c400e8404000755210340280d41c1c124001224920b034005030404c19019241c000b4107656890030310904c12191080d40312485d100922000b9003000c0389007a408280251038070b910800e503580000003501d054504500f045411840c031a0300500e40801e0121040700c40d403c1080c5503004100601c424051b5964150402c1092070b00d8000c01b406c407400600c909804038a58410105105015009401c0e00c0c1024240c040c0178010390740c000103042c405030b02034048a4800d03014140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 996134415 1250 996133165 996133169
    0x120b040603060b1201050c070803091905030a0e0f0607020f180f0402010e01050c060c1e0c030426070603110c061e010b120114030f0a06290f09040318 66
    0x12201050341070003101400300da04d40688920303000d0b81c141024811010010002c494186400400316580c9a40d0f8500f043d143c0403114505105e00321002617800d05001e0044054903c107640380d41c0d1103486000c1c0c202000b03294070320020140d034407200c100b184030014030b046105c1000c90306000d8004417440c02070070345144a10108030b8105a2151382041040119a8407207101010501c3c01d0030502d042514850082c1e0352000c00400c103040748140041d1030110030700d0300503e8407100036010f1211503540301800340094480c0c001c1e2207040c950780103411b0881d80407102c82980d80c20b03c1121000038080189040c4046003e0302c180e51040e00c0518040010a0b03c284003401030520410806103041c040c180c144000e100e045105902c074100300760007400307407420400c0990070440c1128064a5180441746543d00084c2c103100c2d003a00040300a101e1244d12004201e115009201207215594508010054209150080000201c10341c2d40c041904101040b43e498440c03d00380c0c000c0c0c000e1501070314090803090b441d54031482ca5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 996135665 1250 996134415 996134423
    0x10311030708150604211115041706220201030908120403020c010203090109031b0503030a0f09140d0204021e03191b210e01110a12061401120b040603 66
    0x4038080101c01a5084001283e000d000c0e00d05a140c07900e0305000040e042010b8481202c044101c2c501c2400307002c5111034451031100002c4c1551402442c40905400036481032040301400c01441d102400241c002154941c45200c080e04001c5000b00741d007241d000c1c41c00444000302d050581d91b4240101082c540b9000c0c3c0303040d0034000310501190401d4140a440c0042d860500c504551042001c4202079a00210700c00031240d01896000b0390300342d00c4200481010f0b0070b4004a405100120b282040d560380100074807820103081e1114600180c54928900c00064000c194a4011859440c20341c01403c203a03004244004100c000d01340c480601811214860348181c1c6da0b1202c0c0000004080d081421074840c2c00c00c00f454100300041000a6040d010301542401866070203034200c44540041d4101e2160010400d21a5900c002c002c01311078506449160f82000103102c000172031010094060160714883c0c001514880c1040f01c4038000701e14011190803513980492580a510b4032520702c4c03a5225402910040c500c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 996136915 1250 996135665 996135677
    0xc0503130b0a110a21020c042c0f0601030b0a150e09070e160f05071202060f07030504200604090905030409140f150a03050f0a06050106020102040b180103110307 71
    0x1e100b60080c0101e0b01880d180c6415000904131a00103216012200e000001d18004401d03031680314001a401e2041012400d0740090608030380d041d51084d250840808890744204120764100741846440d42d41400d80c407021002e50002005002140e00c40d01e956521041c179650102d0300131604c9070b8107000e2121030f900a40058450f52b042c4920380f20305100030006064a030070b28203800d290210906507c829803a10705014017181025200402e4030030400c0341c0090340c000c0c02c2e006c000d0141c0e8100039030300c1d0b07011101111300b489088089010b01d4864044c0301e02487d00710981c1c14020303d4500582400568030000f03a58400010400021000443d024080c0d210380241c000d17641340c510f01000384042d01c00c0074000d0080800c6981c1000b03030708801c1c103420341d401155a4081417810004000400c406458540000c4e200344540c03441250050750001e0b401986621605041c0a582d80c0e50a09900317038041c602070200b85079414440c40424000385029019580070514000ca6503040001020302260310569540c0002030b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 996138165 1250 996136915 996136927
    0xb0411030a1b092f09120c0301110c0d200d0203030105041a01080106080a061a0304110111070e130b0106180503150708091501060201141b03070c0503130b 68
    0x841461401011140c00902081030404850015140700702c00080501d491082c0c4214408011303025111a07003c01303803540900c241901841036498450315542c500c25800c0030011040445024107682c40d008040c0020a900e00c56003a0030b80e40826410b403000700e03001d0311040e0040c501008004e0024220800d801560340c07941850240700c142c50203401404110216000501c842d03036070001d0340700e044440c035141c190f20549a10074824050a42c40d0b0100030006046180039090514040c002d5004e075108129082c8012151001901c00070300c00190301c030898000380003c00c25a0455071440d9031055007440304140100040d03407901e07503805c0d0a07013202c000251058008103001c00d0164018001d084120010101c02014181d14288540003c0c0a5010008a000402c0e4801c40800c05034001c0c00400c0310b0b0151079a10303450000e00900070819448060760f00003011841941025a120350746c010500700d403a00e16950f944040ea81802c035010102c1e05480100041040d00301c48008010180074510f1b40f540d40c0f04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 996139415 1250 996138165 996138203
    0x4020a050a020609070321050403020d0b06131506030c0309060203100303020d230919030b1e040b0f0c07050703030504050a170c01120b031203011509060c0b0411030a 73
    0x109005110304e040b940595414408145010440c486500141103011400410580103c0b200d000300d500c000e4000d402c40445034100f200c2c4444407441108160b49450703a1211180c80041650300480503075261842e601c500784000b80c403035006403003107003140d080200700015039a41e0300040741c2c01101c4000700368403112010302c00c00d9418803245071151038502e026a42c0050060000e00210310884808803040d000003000801d0380ca82d01170061000c1c44a001030003840c1d41d24100b010646e40122040719442c0400711603003c0e010001d902e50340c041c81c2c0100007044180d840f1102d910b00072501030301c15120700d103003807011000043c005c00c20035020b1842030744e503d0380300d03880c00c41440103400d40d58001e20200d1000c140a0405040d000848e0500e2070802d10b010f4841c0800b1144550091004032640e94240c080d60340d05415030720311040114100d84510f106424504108241214800898051100002c51030035110000c0313040c006074644c12070f000c0c03000c1010100040c000203141c00700668085824510002c0c8042c007007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 996140665 1250 996139415 996139423
    0x30108010b042406030c2006060910031a04140f0a020910061d190803040f06020a03080f1504020307020f07060915032004180506010512042004020a050a02 68
    0x20905100000703203103c01a6115034100010f900800c0c080540d544121b0401345c1c41808048014081d00e800350300c00c00c002d000003640740d0004076540c0f80141c07404e0003c40e100500044000003181e410149640078111149800c1111100250059441080700207148520040a01859130407040000007050420050710501c00c007480001c00781d05085825076020400c00303400075880321032845004c010282d5130003000002200b000d09003807050314000074580b0200340040c0000061059801503d43e101c0c801b990341508a1b0380e81d10042c0018002100800420040d40c0b030310002175003041030801e01c541007032100b0021504981048554200681c0441980e550004007404084050f001c0380c9014140542401c0381c15101090300d014003400c0507030f280341c1c9076a400801d1040b6121120391f40300495595564010001145443e0105607170310f1031810780400d2556002e00101d4500407102c00b51000710380d486494400c42611549a2400e06030184882455103a4444c4001c0200703402c5030f164282c40b1800f03050001d1030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 996141915 1250 996140665 996140681
    0x60a0518040f0c08010e131e0f120c051207111e04023108030426150402030607031407031a0d140c041103062b0309180b0a090f11030108010b04 63
    0x501b044c809103003c08a40300c2108403480606800310b02204080504c2d0589d5149000740d00640000b080d8002d80c0f00030783c0d00815a40e10356001d001103482da8400f144032062184540100140a82208050401c041c1044009841c015004103078802c4091070807170120382607038003074541c0c03000b101c02640d90008120140c802c401c2c8074000c00d0351041a01c40c1440001c50b80c4e4401c80c01041078400101c41c3c0c4004040840c40142c0c110b004070001d0301e24550800c01c6403281002d0075142244039000e00070000341c201e48a842002542c0d07141103141c400135100c0c02011b50003441e80140304281c0310680140b40d4000c0d110b010042196a10510200701cac0460982441820040c1240e142031099080100f0701485011038002d590b00800d08403070a41800003588048809141170b00809084c81940c001c0ca0414190090103c41c1118101c2c070725411040c00c5c4071f1201d000c4501b140b504640c89046910140203c490560200c41002d0030322000081944100c1041080b0b90001d074003007016a23444441c0b03103c0c103041a0003064030b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 996143165 1250 996141915 996141931
    0x60501110102130b090d15020a03050708040c05010804030c0b13060e0c03030304110604030507081039050435060c0d0213090903050711060a0518040f0c08010e 70
    0x2c102010396010000d0031001e8410302242d15000300c0d00c01d550383d031340c40103100107030741e0214040c418152181c00d20b5008c2d4125104c6600132074070f40750000c0c1c44d07540604c00280c8190b03808180014082c0c203000064a00110140043d0100003d110800c800220081d040d540205504081c0703141c012030a24050040e00d03140c1d501d80921360484440040e551720000b09981c1c0086d844156401418175001c0400c034140142d0f440a17140707208401c00040c1907080404d803075030a1a6001c00620016004584107401808503000d18654503852059590108600381010002142a440c0280c5404c0c0d841030a642040200c00080c80b1040c4600d4100d5200e2900f040c001014040002c054009440c041ea6144200c1c041c400e600381070702d6000903140f001c40d0844039a00016040c500d504102411460400501791703006640203e406102002c40e407661440c0603415905204c501c0e0795003910701030b1800c0070003486180d07403031641c9c0e0020b403201601c4116916a00a08500640e1070342c1c0c80600e50f00d4441100007089011789115 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 996144415 1250 996143165 996143167
    0xc0c06030b1026091002040f23060d050402010e0a08070e0a0e120a0306030c17150103210e0306040b091204030c051c0c08031305030f1c0504031401060501110102 71
    0xe403841c0700e5101c00300301e4001d0f0300f460107540380e40c1d4085103400c105810148a0015100143c045103940c0b1040403070081d1740d2810703544402d0200d03841d10403805505103440c0701d038444030a01c062007868001e9085035a10034410300d00904024804000320791030050903044182c0a4001c3c140c1071203401100500e4690000407514203000f80003035050342a481d056941c3c406121514001340b0171410034025080107005551085040903c16511041c05030b04401c041c0519440f03009805a0900d01204034603000d0583e50420b011581300180441d085010000e40c2c0c80850600c10382031003000440d9001d202041c8518090305074452a80340c03596086052504685000c908180144000d03c04a10b801400406541c000d0b00c05820b100018840580100403a0000403c6004010800301d5011004000b8180301038280f00100b0f07a0940700d03030402d5118982001c0c1d0f0140c80e40075030141f80b0144241032802d045a0542d04289281a4480d207481150741010f800343d0300c1503912001c0821141d40d100b400c03000c0c0b20507004021 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 996145665 1250 996144415 996144437
    0x90403080a0e030711102127050c01030209041808120f01030b1b0903010c030c02061b22031e0201020c1518030102090d030801050a1d0a05070c0c06030b10 68
    0x5c0e00c51521528064001c491450300b00008038051540c600c035850341075409036800200f41c41a200503101d8200855910304543da07c2c101002940d8a412002039805005001441003160045000f07420001c0c41a60040e00c0303051001e03c038052058000440c500482c6c05035528621040c40d031003e180003800da500100a00d800410208120101164014603401d042d9003400d0015254014a401095140350b850352810101a0011385c050b07200c2007a92085400b510070035607640b000e0f002006641a0a12403880381080000510400181140b10036881041c201c401e260301c1c2d80318501c0302204180451241c0075820301301c4042d0b40c1c041151a2080d1011540ca55880468030f039551101d0060003040180c0c1700550104404558080d019100c103001c1c0a00000344022184c00c00910006080c4280d030700036001d0100200e0b480008115002450745c0410301903d045d100c0310349190050400a00450820489008042c0003403800a075000c010501a03401003441c1c83c00000308000c0500070491402070124551003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 996146915 1250 996145665 996145673
    0xc0510080609130305032214150901050c180604030c0b040801050c0301050f0d060608190309090e0a0807051f061410020d1d030d0801080f0f0303010b07060209090403080a0e0307 78
    0x6c030b0b070303001c0061546204540b10700010b000407404400f4009020036580f54200104803000100b60760051046402c5907000e441d180015800c0324401e40c0d80c00c020750001c00c0810035846c50b5203a605403481c405040c9602d09680c984503411b9071a0541c10600c44164000b03801c0280150134005c20b03411500c540c00e840d246501d00300016035032824407030106004002c0600200c081c44002d5005400400c0740209494250005000b1805250140038080b00230402224001c039404c0b0040c45213210703109070903006140d0404a51503001440c0c00192048032030b8031600d11a810300700710700817060402000507c40403030543e00f89100c40540c5603443d05068026001040c40045060f80094280503950050806101005802403a041141c140060303031794052081100001a182e0301c06141070495442030195100741d42400031442c2c69010621000e0720b41d509c14001803024848040003403181a00ca02e10040c1713044030718004a0351840c401c840940201c0c80380710030130400e0300060103501030921540014616052083da2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 996148165 1250 996146915 996146917
    0x20705010206060f0d141c031a1504090603030c02090705161b0905042108010f03032a0605100501050705070308030601170a0b010e0402190c0c0510080609130305 71
    0x1e4948540407510504c0100e85410b41c0f0003600a8100c014601d402211064003542e40f00348103c0005001c0c2c214954034003013032082c4a101c260107000145400700d003000508100240350140003001d1231440410000030014644c2c814400210b1294a0784495a0181d00401c101180b00411420a01c8810442002c1c22501c040b004048154890902c07440c100c114000c035142c81885070040c8610700d1a000c280002e11844000105010480b0a01280452440c0c401210f800100303202c0e5200300ca0b080f120a0002a000b00481d600145011505261040100020b019180b0051405894480d1b4800c1032000280203015400082e000c00c2c00d0041c54403481d03a452543c3c4a005100c003920b403e0010002c100b003a88110390311903500c0480a5821110b007820300c840781c010041150000d011075110123400415040a0081d0703551420301c107901418800c60401c00b543c035482121000c503104000c0300800b06840d80c0c0d00c0c407600d404000c242d440301c400f0b1400c0c1c001e00034149000b40480102e84407812501c00003030741c450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 996149415 1250 996148165 996148171
    0x20f090409080d180203010501060e010f0507060b0d060c020f03030601020a0602310801060812160f08040f0e0105040e12070305040f1502060a0504050c060c0a230706020705010206 79
    0x24034000740141460402c04800d00070800740d2100941000e0600c1c036401c8138000c01c69281030089008020b180d90340e40741550003400e408812408a10710744200c00045000b6000b80150034050303a03010540703004040c002401903940000c02ca5806954003c0d4100580d4100100e03409040c030a0000c41c5103040010020f0340d10100284010941070b00001d042604a0010344881e1541c602240340c0203500d2980100e0415a06c164080e001141d0b19200c400219071900103142030301000075441461078010262218085001c0b002070599840084421b08400240d00400900090152030780e0141c0031410132101140e00385041c0d00082c491400c21420710302c0c000c03000c2403141301c0681801140d44d80321aa4a400d5a20340115800a01d5400152900155101004c00c44130f02c003003241d03802c2d07400da5900c508031041114400e4401a0056000c103034102d0301800c1c481c00515000039010700f117449500140c0e8a8581c5280402488070030000d051420040d181c20801500000c0c0c003941c0081d0840504100000f940c81c5001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 996150665 1250 996149415 996149419
    0xd1d03010e0319091517090a021c05010b031203010501090b03010e0a2d0507090e090606010f02010e0f0a021c0b0708040f080a0e0909070605040e04030513030f05060a020f09 76
    0x1011900f00e200e0082c3d11000c0200201c40c550a1454025030000e00400011401c0a50b2078900000040d140c0e00c02081074110385900601d02692909100c02c006a01511400308690300d40d42c500c500051075800f0001c00031944004107140390340758108000107050801d170340e0000800803414401401180c11075941030350b00803c0500000b42081c0440c007403085029002084041c02481c20700c201311a2401d0350841c0384900a10341300d1031741c0540d80300c414559124088810130000d03040040466003961080c9000c61403202d203840041008090303094001c0c10f00c000c0814112065010080c95011800c000e540551415040744d0003611038081034580300c3c5c0c01c400c0146414104500d0500103002c03c1204c1203241c03401908068900c0d2500824400581461131040700a0b10800018002420309100050080b081d80d095942c0c030f0742400c1c03900d48a85407480c4094005c406101e4203201070740b0011000c2c200b40000358040d462006100d2041d05102d802c0c03280140683d0350a5004020311900340d09004100d03a900241 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 996151915 1250 996150665 996150697
    0xd020f060f060d121e0f0e0103151e1503050609010e100f0314012a140f0304080406030e01020414091e0c0d0b06160f060e0d1d03010e03 60
    0x841000440d180500c800061000c050051303c83d01c50750b80580c900c5070400e40c0c19402c13810311500039400d96201202c842c1240000d10850749090080d4400d0300402c004410102240d40081c0d12040703040001c1c60070b001d0140d0410021002042aa950f0f048204524019400c1c20030050819401080000105020394100d0303900340b80c04645540c1000726a040240b1200d100410025100d162451814242c035078481119800c02c134034844903019030501c039000007504c1c40b01031145140542054610300e0a01c040340311041c00031f004844e00c5406403802144614440c02c2441d82d40c50500a0140445091b503600e401a03070b00c148030501203d66544c00c01405080d04440300e035000e81d1a0014280e080c00f414000d1151a040d05040c41030501c0300d00080c01420306064400c1c400c3d1540300040c002a406820301d5969070424031480400803ca0900a035190b0300d02400c000300361a004006568170b440d40703921390070b8002400340f403241e2128030910b84d604130745032011002031003070454880c0c02540d02e00445a0100e003a0726 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 996153165 1250 996151915 996151921
    0x2102030d150f1a090603040c030308061002100b060c07171b0a0614090406080c011103031509070513060207030311011e0506040b03071517010803400302030d020f060f 73
    0x2828802e03110071382c030020802c994929280c60640c15070603003440120042003c0402081640c5090820b044402c1c90f02d034010043d030310a41d400340380500f0800821580040040024501001c4140a00c00c06095000c1c48120300c80244c0000600d0b0203035050802c2002080d04c02176042958070748041c101140c03014070700348000800c500440d40c2140304109090394407a14004000500c0b0501180d0240c907075030240ca8a210106848603035640703910044404a511001203400c1c20403510300010540c0d0422682d24045042000d0319070140c582d8212070b004800903a101960400405a1000b1402c180098650080c042ca11801000042d561a01801d880410751154005589610b4650104110480050480d020160381e048045000e8140701c0900c0f000810003035501600480300f142e02030403a6080b0000710300d441e900c40301c0b045044148400c03142480c0c05c00070503001d51100c00b003c54070384196681c00302a0800c1c6140704041c40d08200000350030564001058425090340041442544102603032003800241d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 996154415 1250 996153165 996153209
    0x901050d02070606140103090c0e1305030414030105010b04031221060e0a050a05060d030c0f060501150f1e082a180a030c0506072102030d150f 63
    0xc0291900d03021a80c1c4042641e0b0706000b001d8014400310b0300c9940c43d5107071003140d0000440550343c0450015220009580c010012180340c1d003446684280c122261045254a560340c15003151303c1381d84850101c9400c0e0901e00d80e00d150038403441c0d00400080c1c0105107041c0c070350360f5078603c48800d5010f0007080c442585111400c0d04a500b500c500a015007920803c0741d81c1d03c9516500b6005d0095402d440840e2900d00080c0040c03186100d034500801d1300401d801c3c0900c40a50b82200c0c02d80390340328211090030601c2d0300301c1c1c0000e9250103000d02031301d1074a130f01d00101210a44000c1c121450780c19030400300104803c41020615558119044100951909007000d64903901e81c52003001c50007c00000c106013491744941010052405060390034030140003060411125000c0002d584031600007d0100c10386100100540c1c50410011704005101d02520400c4100b210344a40d441009004100c026810019048d900c45680b80b1444c00b011088035010810036040001e07040e40c0d1480e60207030702e54000403410306611403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 996155665 1250 996154415 996154417
    0x3061407121a03010e0718060e04020d050102071209080d02120a0e06130303020a1505060307050f031509030415030e030f1e0406170901020307020604080d061d0f070203030714090105 80
    0x10349010f4000d02c0505544200b26544002c64492181203c2c0c0340d001040440c074031070091000721070100f8a4400d083e02d80e0707007c1064203800c0352811203c56600b001300200080031b05560010707142098503200c078650310b0014041d00b410000c07039070542150814400c2d015000c2d103420070782c1d8082445140400c0391120b114089a03031840746000440700100c1941002040550000e100790074640700d10b00d0640d00c5980a001001507480513035119606030000034041c009400c1c641150440c03010010708841c00501c11750403d943c2c488081c0ca104d00542c0000030184815014002c1401c840340d0303a8503041051042081d103c90302c0c0c0c020841d402082450010f41c0c4400b04801401042d40418000f841564503640d1f01c0e405017200c90f00074038142080c652003001502c1440c061090380c0c070a10064000c1c2101d030782c031651022819800400740048442ea10000445e03010113080c1203407081d000801014a4a08004070300c2e12294000030403100455004004001003a640003008003110052100d556844420302d030010303a56 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 996156915 1250 996155665 996155711
    0x40b180f010218040c1b0611070f0609171e0a051c090309090207050a020d0203120d02030901060f060f0c06200909100b0f1c0207030503010306140712 66
    0x40c56001184603200d5107060b02c4942081c043c100c60402081208503001d940d0032a41260b0700c0c0d4840a40c0301c6401c0421242c1d003088803441c03510420716140260641c1d803080b40f080308480030f0310041c0da900d002c01d040101311520401e96a04844906d82040c51090030492128003885440a11450108074041c03c9030255090307130341601c0c210042e01c1c21842072006510003003c1d07121060303000402c02a000141150284211780f0405e8122000d0120300c02d2603000d105802241c0002203070507104441ca80c8a42007a050058041746205500269071707402d1600815007507400c1e981001041444190040080b02c0d0403407a0200110b44a040500c008481d50078110014050040f000740e090821044400408540000600300300c0000c941105650310b0f100c66085e18201e85002c0c1111018040003001c1403048510050403d41c80c1c0000a414103a4031b4011880590304112005c1303010500220040c0100003082c020814030709806c090900030341c41c0281008040041c0495101c4002d9601c3d0b0a040ca80c1001c12042c5031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 996158165 1250 996156915 996156943
    0xc1003021c0b060f180a151b0b01091e0e01090c09111608090913050f1b060904020403050a08030f07050a020303060103020903150c031906030c1406070b04050105010617040b18 77
    0x24015a140004407a0103501c030f21010000c4c440c0529101c030515881500d0108c1c94201c2c0d5030710840d0b03091000520007803d41c4c3d0000d1032410700700340400b2456002801540316442c480000840d03154450b00d4a544483d01c240c0250b511700d800c0100030460002d20700141e03021918024a0100c42007600d00b0410868890441c00c00c1d0042d18090030020300c0346c0c0c0110211002131042e41258841d4565461664031071607039142e0008070104840c840e500f1813404401600704050003d00c01131920780e495403411714102c601d440841ea2082e01104204103500e0383e00c0c416500081a003481d42c5030886201c8001c1d07c07403100414050500d980805d0481158a04008030f04440b40c400404090508020054884641046800a03041403030800613101c0e800241c0101e6007126400380805510506060030035051090951000ba0010020710940011070665030415004078043d030000113140d4100100100440c00000c0c40c0141450709506100000b540c105a02e54807568043c1d008055004424040781840e500c590b40b81c7c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 996159415 1250 996158165 996158179
    0xe0f210d150f03080a1103190e120714191a160f05010b0a06090506041a1303080711010822140d12150e010905090c1003021c0b060f18 59
    0x4020007800c8401400b5008954580d0406c030183c42009958078841e804810180c54250300d00c41200c0c90242070424814280200399040d028a0b0742450b0380b0780702e1103034002c0300c2a080031803400a0504060350f0101c0f5006541c50318130011420071002450500104103141441100001e42d070324242c600403651010f80d0f6000404089000c411f0402901030800c10310340d2442a01c00401c002009809055028210b0354040c15640c20146400031401102208450015404070200300b4042d020700343e514140044d51003000c409071181100d0904064a1105080e9181404100e009020440c060b69020030f02e0642c102c4480b801c140014a803141359450400d6000f0304a100f2112503030069a0400a00c450a04403000c082064100e0200e8800782e15001e4440c0e0f03000c20381c1c044010b00100c003054010a81c007094503821100144840c6000c2144600411035200029602184c807040040c6401c152043c8c0c03c074103e5052000c4062140010010300c103004151007119000144092840c003402620580c0d03c034002c00359 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 996160665 1250 996159415 996159419
    0x110a060504121703041121120c03160302100c0201051b0c01060e010f0518160f02070e160e01090b1b150c0405090c0a020703060c0c05010e0f210d150f 66
    0x5000c80700d4105606c0c600c5040c030100380e86c0c502242c031942034044c3c41880004002c01c40c842d8104042540c0f0000c40c00440f8007080040380c01c845844a1107000d414441d600408a40140035a20741c1110048e42000f811641403d061012414a1015118495840e5980e090f919400d1070200e50052100d03520a030030500201c800094000070040304102100c109686000c2081c401c0b80100c0036a040860701d18500000c401c00188100d446141c941d070040d14180110b5103401d031115101034440e10300300c810340c02ca03134000b0580d40001640885908002e810070308100d00900d00304141400c443c05448400405d0307061900210b4840c40e001c101400440751041c51000b41c07420690702200942d4081d0090782e0140d001d5030302055490712a84120764400c00c0950240035400c1c15a518039001c0c2c00c14154070320820031804e0030741020036000c1c0720b0300010703004150050100601c41c0502c0f509141c450910b2482c82c001c801c4200315031603a1001115a060024240012621600700c010058100990032003030030075801c4500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 996161915 1250 996160665 996160673
    0x6060c1507030516050c06220c14120105040c0509070e13060602070506070308010b03072a060b01020307081c090f080306010909050c0d0b0f100309110a06050412170304 74
    0x4018080c10340d0303000c525501350030340200f56028860703014540c61a501c146d00141114042900c120f240c0b000c0c003030009030300c902562101e8401c0c28045d00219100c080d440307d07281161030850a02d081440b0f03002d0003070100d881d00380c032580c4440060f031007124068001c0c0400210501e1154a030a4000c550007014880c1d00d40c0210039150040c102ca001c0d49026200b00304010405e490316100fa541c41d680e0644d10050355071300302425131486410180c81401408034802d015800e50f0a00c070baa24041c541c2c08140e88c4003041c000e0800000b0703a008103440074150741040000e02d0200f414201113940350311070f8401803002080d6415000c4014180300d40017410481d4540104000c1100c0d00d001503004030b009070395100716035846800940499405989400c82140204020784811440d43c1113002032040080500707901c0f04120012400d0203d040096a00283d80c80ba1082e04004c01440044017000040c1c1e4034000b41400d014024085200c1c50080c07821406040408904002821120b0a06038000c2221540c503070501e468 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 996163165 1250 996161915 996161921
    0x90305030405010f050c030c090f13020316030c0f0315082410052b1b05031b0904031809020d1a030c01020303011509050a0311130501050906060c150703 67
    0x1c049803035500b00010560000003070b0203114091800c0681451541d12582c3e006c49039903024240c42070308543c12140c40601035a600310001c11003a030100f4007682e00d242007042d8030b070301070b8030140c0300e50506241101c41a001540321010207024856420000362809540c10a407165140550212020703100d4050321078403c5e0180c1030480e42c080116900c001c20b685416207409203c0201303002c0d5030341048030200b041d4030740c3c900c0200c10080d52210318064500d022079a1074a11508185d0303581c00102203244c100c2003100b4241004089400303284460629032258071540043e0111101820147c00c019422400044001d41030510b6801400e103c0000c41d55802c1200c00e207409450b142c00001110340e00800c0d8201e003030034007140c0403440c100140c1c0a5840c503800c01881c21003180c103144102041005440b000310303150300c480c015240034501541d001c80c0c881090754100940095505028001c003414080100042e40781d90b13100c0c94009801301c91040d12100702200261803c0b1000074501c2582d040a82400901c40e0164 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 996164415 1250 996163165 996163171
    0xa0b07050714030301081f06030f1719050a110106050906100504090905010b1002030a32040305060a4a030a09060f050c030d02030703020c03030c130f03020f01110f0109030503 77
    0x3841e942d11040307803107d1800b140c8083c40054082212041b004000844c0c0c1e031440402c5581d010301e80360400030700035401ca07403101c41c81d0f50080108200141303142030640c000301046c81501d112030080c41803a040002142d101c1c14041c003002d01070f9148006031001030f40540261400742c81c980d4010000030b040c5007829406001041e86442c064520110311400c0d6034070101c1210801e034843d0700c85c2c404160401c698a00503101c0044610b2981303100071201c14102240d403000304000c40c00b0710001c010604015842104444103240c014040c401c0c000b005002c9035070041c0c0c841c840c040d14584094101c20001d102d036440386010840310003d50000281007418160050000010f0710443d946840d41e00f030001e8015143c074070886e040e03203205a0060044a000b038980d0f400443d031241d814a005400c1c1280f221040d03103981c00c1901d480d11420004505200680281203150700205a60604415440e1458001c202c640d024070001e40c0c10000140307818440400f00300440c1f82c44a442d5402045000d084c0d090040c4290015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 996165665 1250 996164415 996164443
    0x2270405152107080708010f050702162c0109140c090f0f0a0e07020f0c060906250c0602070e090f0c090406090c090219020a0b0705071403030108 64
    0x40003080869a007001c10814510001e80844084200c1610881c000380080712007900d5403060343e0300803482032024481000200300c0b0b1070020400d00c0390b40c070150080c1c4000801100031035000c01e48401c4d0111008070386608945803c100ca41048814136406010208000d810001c07008030100009110300e5941d200c801210003208200005880722003005016204000c1000c4e4802c0000c1c0030b0002c3ea1500f420004541c080081c08030b14060380d00c40800c481940c08503000c00158110308280e12410f041884100e00c600d60807101c0c58948050040050460700520014400c5203190044192284101d040c4a1110640240150041e99a80c5000030f5403103106002c0c140940600300003041c800a0002000500c006801014107141c0c0f101000b44990500020710540d00e1076120044200402c6107a400000a003446540c0541d80b01101c840c1101841407005d80042150300c0300703c0b03200116000e100b165400900d146005035903003034181071603d40103020b01d02e800c60714000000001a41d0900192100200c8a1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 996166915 1250 996165665 996165671
    0x13121202010b0f130e011404031106130c03110303070609051f05090a030c050a0c03060506120d02151005191a0c030306101704050607081506070f020103022704 70
    0x2e904103000d00704200d0b080d2140c00000b484c3d079401c090111604206491019100000f41503d140f420380e081001042d141a008111502201404050b041c0011a401b86c03c00303d0302c480c1c4e4038080d03543d11300030f4101d03100c0a400d420316280d007007450f59410710071200880c2d004081403156152a04010340c840c1802060183c0706017039410116040611400345521401500014207a200b00c69202990150406403040b0354a005804810740004c84046510700a103001b884009010b01d00b58040c400140c601291080040d401801014100b0b640000d2444a040321002d401280c0c0d202c0c0040720b40510b58039000036502c400041c1c0c40c10040900700031030000300c4008080910403030112a05180f01c0748201211141c464100300f00144080c24420740800c50b541d10b5141070784090002807130320300c0c4013141628221610342042d01072040341d80c0d2050034182c201c100780500f641c3d00306403200051a1442110030062a8885441c404015680241c2c19103140866001001d946542c082d107c504441620220051090340303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 996168165 1250 996166915 996166931
    0x91401060609080c01020c0402090a05091006090e040506072f03032a041505040b0a0c021306050d0b0405010e1c03140c0d0f0615050a090e07141312120201 68
    0x260005007005400c1068007e000f84401c50420310000e075111324803e503005a82e0000c00205a166803003030b5442111030711000c1022030b003440f1000700103003c150b01411488a00100744808a14045426a0400c0b01410003008018640008801030500310010030a49006c440b540c65042c80302000540c42500500c1c8210703904c000444641c1e1a09485030203110114100b40b0050050403010300043c1314016a40c24402e003042d40c1d49000707007000d92006280400181800700880214203100006081c00d0702d1103a0b05104031400c10020a422452451000d040401c10314080b0b018442c00394004440702841d841500c180f15240040015902000303070700540003038135055601290340e0780030306a58003d0310b01c072207043e26058640003a10050070301c484040b0915a502e400003e035440003030741c0311903400c900d607101c1d01e40741c005504028140084a6006024a05010040209641c2e00c122020703001da1407416500c2c0c4031000509080f05070f4100d03410034042038500c8901c000030700031058001c0080024130750080c4480320b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 996169415 1250 996168165 996168179
    0x1e0601050a1a0a05040f090209030c0123070201050d0906060e0a0504110111100615090801180b071725030b011e020f0610031a150f0103091401060609 66
    0x1007910b10403003a9001c041032440c4903482e1000000c0692810a00e441400c01d6140c0d01040008440c9074825142154001804415410300307001058100a090900d0000030104441c000314551a203ea200c02d4042d0009600c1d0031a8003070b000b43d40700b05841c3c01c01000f0441c00751400e54020880d50082106001228001680a10203400366a2084c1d60050b10301e5a802000c100548021201102c80c047ca4041d00c05106201d100c10b206900090540401c000400d0b003481e280600144415040044964144070701c9c1201c66410070026903005600007031048240d501c2d00c100301d80a80782c22a00b0a00705036600c050003040090340c8070003000c200d846001580d114003862030603411261502819400b00d00910304400d60881d00001d9003403141860300588400c400d19440ea10300340041105d000c0142130440c0c0c8280140035600003801800e130068250b04d40203090842e145141c8008000105206140d480107001a903403091700b040906981c40070070320000c42c5075040c11901a184501401c0001071345820001284 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 996170665 1250 996169415 996169429
    0x1a0904050609100317160302060106030b030307022b050601030f060b0a05011b150c120b0909060a0e0c041a01020606010e100315050a0b0a080a0227040e1e060105 71
    0x9942c00e500700003103e61865481110f2000300c0f000786251401d00303210070984040c0d404004400c89209601501c01c942c101900a811501748092450090344144905001038aa5003a104019032454540d480e05102c00012142013200d0b41c00f0062842c010f48000204002250f03241115581c850001405407410810a10011607094892140068070301071003014000c24855000742050300421420713080004c141103580585030f808070014001083c0c1004080c400840d0b104103440141d00f11400e0b143c1781080e00700e846d81c0300400b0717051081050f0b6404440144000c10030401500700e8018100b800721300c0c03044192a019021019920b0301600410740000c1c210b40c0b0500c0001504440248109011070b85008205e000702855140010940e00b04030300858070b0381c2c402034950000d20342507807039558610383c5400c014499080980710084040c0140311202d802c0007003503100030280320180303c036141d482c0c0039800041c042d20801e01100b5440c05100c0c28180d807000300d4000d5440c005240402c59000e0f0b640c0d035003071100c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 996171915 1250 996170665 996170671
    0x3060b030f06060a120513230c2806030603030e090c030117240417040806010302060c0a060603210905210f0f011406100c03030203101a0904050609 65
    0x410a84400107060b034034003a00a01040007451078048012501e14038034904455040c1c524038001d0780c000a41e0820068920110346003d02c2e58031440401101503c50035544840020000c2d11540da100b01107250001c0c50f11008840448003414502c407143d07600c2001e00240b12602058000441d04c1c00b095809040c8010b00c94080c41b14144920b117182c3c03902c00c81c06505405411314000034040c062080150342112001001c8580712000001e895007094030302080601900c00e618412020103000170445000c0203c0c1490441e501603c8040d5180c0c4508403050800d0b1240100528613481e012000c0148450907481615a5041008180011000c0381080c2c80200e281e00c1002c0c0d006c000224000f0649080071225140d0410410403214150150300c0d031170703040c80071180f51104d46a5541c0d4040d80301035680c030303081500442e080d6101e4040301d410190040c00500b00b41b0010701410703000004209500e086103510740c0201072080e41c000c0600095920580140d10600070548680e042501217400b0740f41006007540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 996173165 1250 996171915 996171931
    0x8190504060f0c1d10090b0403080306011803030f050d0f051906140d02041a0303221505160c0807030303091103061e06131802010f0905060d020d0f020a080703060b03 73
    0x100c42c03041c1c0000c11402c413003042c04170410032400c05400245800d415020700080d502c6040040d480385080800104002031b8400046d110242e20841003001c243c200f014510803808919105944044100c81c1d03401910b40c40940c061450710785820400c2058140d56403c00384e000e495414040690f40c1d2840b1110018032007410341d07001010341020307401442c01c0d40c03165000007445070b02070088040b80380c000303415600720100640c00b02d0f5003886802c400d6020b101c401c40103001c40080030081207e1442c4020124060144c002d0380f101e8001300c00c98207000030060214000d0004c20200c4e80d4098481c5001070191540402c2240c20b80d5440c100700c0d03014540031540741d00c101c9404000021142d440d0400c0d010942003c0d080740d4100b501e5250007402c0594a002d20050402206214840c8000e944001041c0e0040c1b041440e041040c021030a000b1a80c84004584105440050141e12440c040a082005244085440c3c450610026501e0ba5268010b42c06038030588940e18200f00080d60741000e04400c0c441192124 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 996174415 1250 996173165 996173207
    0x81e0a20011b050d0e010606210213060513091d0f0607020616030b04020f03150d0b07180f0806100f080706050304080702120102090f0105130608190504060f0c 70
    0x41d28a01c110061300c0030161085010894083c121121030071640d01d0b030480760010343c101090840c40d1b507040030341400180c000e000462415044e000b98000e81482c80c080c4600700440061900608a02e40903c1c00c05084104800c003c984492020310811256441c02d1208501900940554000303000c20618414186600030300400c2c0d8410510060a04071031805000f1f00d0b030381d0300c0c8292054559202500d03000c05040300c5035a890038001c00342c60744030b40300c1e00410b1310803070b18140e00000043c00740c130340641c0200d5141030012844164076161420030a00350010b400200016000041440000a500f17008030028036040040c01d031142803800d41c8030501d0141c0010350303001200401103d8420002564014007885000e070904015a0001c0c0b41c0744145c0750034200c96034002c07520021502d04100354154484003420b01e1031404251141810107208180f0039034007404542c5001404803842c48034185c03035003448030400f04440d2410707207001c400415904840c1d2680b00c0c501000000690301805400c80030322420180c00d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 996175665 1250 996174415 996174461
    0x40f020910050f0c01020c07170c2407050616111513060b060c010c020f1506040e0a080a030905070b0f03040b0601050c0102040305030d050f060904081e0a2001 70
    0x95805601c03d41c046a090b440030010007140020a00c05084840d40d41c2024050f403603d80110038020710101643c0300071a8000c004410b8072a86e80c400300d48035106203161102d0b40d02c1c42c02c400e5204d280c0502e0f24040c01c1c0d40220010842c100c0c0010000ca007010801c0e40301c154200744c944464940c0d921152440603600303c030800124a41e40c0b00032142418192180030701181d9240c0c00c1c4003044440d0070512418101d03a4481c122000740a4040c040b0004030840500103241e82102a00080407041b005402c07140a9a902c00010b5100e61041c0501a411500161600e03078880a409005009143c2a00103072640c0c020001d021480d01044801c4a43e103100e072040080c210703102c544440702164809042c90303061002c100091400b022080c0003800055026601a5454030740041d4207100f5100b0042030749803050b0903002001840d503900525140c10507000700040303496028150210440c10609000b01046040106030f045a81c1c2d84603501c8040766100b407032404041c014a80c00c0500b40c41380c000e15038059000420003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 996176915 1250 996175665 996175667
    0x2030703110304050a0311090a150513020705070608040c1d0a020d06050907260105060a1209020a171c020c0d021f41090105090907080105040f020910 66
    0x18280a00d15050203803450584c0d2600002c140c2c25080d03200725280004800001c4113407410a96055201d10465001e00c001d914150350301100c01c545010b1540706861403412035240121740da058541d0303d42d2000446c0c1090b82c0b500009040c0c0340b4221021186a0314440703000c078000d08020751896800000ea0000d00701b9032943d81040019410036150802c4265540c1070008640d5100500305010310320540703a40c0114000101d07251300d0040750003500e080448000c0010002525098200c5030000280e00d86000c44010344c0ea03104000e841c1101001c1e610911900d00404c1501d402424500403510300421949102c00000003940c540110f0820b80c005030300020741400e80303418002280107078284000c01d42c1e040340c0d21281440101041c1e00e4141400221031040300e0050200303240c210848415a0000085202000329030000c014015900001c00e205003c5020030807039006000707490075103c008140c0750300c52800700c03401043e03500f01b40304862089090080c00e06081150740708032070340014040c200a4050800c150 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 996178165 1250 996176915 996176927
    0x50403171c05091c122016150911120109170904021204050105010f060503011203030c0c210e0a0b120421111614010c0302030d0c050714010c02030703 66
    0x40f41070802d000340d91808100150114a604110290ba12449800c403e1110b00d01e040303486100400b003030010004401e5591031010026074811554030310032005a00d1142c81c02c800b0f00c0124440d246015420460003800700042001c0b0003404403c150340012255404840c00c80c05e8034081e04025008074102c0040380c0074904201c0081c070076440050000f616040da000c0d001000c004084805803596503407640140541403143d101c4600a0591b4600141154145000e250003028201c50040c103056440340c1c0d141c951405200d01411454012400351040c044401601c080e4414048000b40021203003581c050b403e01e0242d07414810780d49107505d05410000748804007c02500e015009075000422503960b12a603000343e8111008141442c0e4404420040d484007142c603250614080b028a0301000c08107000c110a500744691240c1800d10b0861051040344c207060f811849600c02c071303440507070510401401c1141c204006108840c4a0101d071302e040f1120b103031a03508070b881030000c8000507001041410003281c0300e01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 996179415 1250 996178165 996178171
    0x30c150903090a23100e04051024230d14040305190e090c030403020c2b0501320703020f0d09170c0706020f0a0b271509061302030c12120a050403171c05 67
    0x23091400740c0b5a1b2f418101c000301d28100c8601c42d04d401e070005a05803d88442c0c091001a83c1400c1850704060819550181c11401400000f500f0014400014a40b90340305031200e02000744080d01c1d01c0120308110b0503809882c0e004841c198050f1140d01010805401c001080c000d4030b400e82690004260002403c100704042d40b1841691a5034881140c0c5e04000c0c02500b255007135043d000001c505c0d0b50095405004441001440c150905105010954121000400700d564088201d5000580c5001d142ba0501980d023101c2c980d003803404004540480c2040d40010010140c40d65a0229060410003464890b40c07020b82c1c6400030b18001c010408500c0c01500c05c095580e0502c91204201716040c0c0b24500c8a16290005901c40186201003003407103c0b8040a000f03007a040786e03c580007030202d0301e005d4001c6076495002070310003030160440b11211040c440090000303501800b00070310059981d550180b801001500f00380000e8030b0140180000c03c101d5103030304003241c9002d1006801242181030070000100100001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 996180665 1250 996179415 996179417
    0x9020315040c060c14121e0f0403022b030801080c060c0709180516060e010804020f06031e10080706090e0c070c08030c150903090a23100e04051024 65
    0xe10134089050708244501844680a00d03803080d1203000c0d02c1c7e20b40d013000c0d01c4410800300703069007048000002c07a9810300f00e03019680c055400007a0703504458a080002c0468840c40e041540d04008500c04150f4440070503812a080e0808440120840c4020080c2034031420307202001d240d0001c1d0003044252400d41155482a0001d082000c684081d5219141003506120030001d401442c00410301075560400130403141d080080c038150318103290580c0862120140d0000b1180300b50300100004250404140f406c801000702c4112031801c50501c2504410705555074001c41d0554001c51001081d22031040c1c81d00c2c01200d03030601d410451030704e80d400101c10a601081c01036908a54040c404510701008100a0103031554640003000c00b0710040688000b8410054007280080e0010070401c100d9513a20b20f8420143c0f1103041022000150600c170440d0340303203a00c0a8135504804282104400315030000802d0460010a40f8188603541d10142c803c01602028043d800689640c1e9440e5194102c1050b01d0460300d04c0d007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 996181915 1250 996180665 996180683
    0x904140c09010b040906150c03030b0a050a0e040c0803070302150606040302061909050a0b0d021c0509031e28120e07030c0f050108010e19090609020315040c060c 71
    0x8410041107141000360040d0001c1400060200100080741c45104010003820780b015640003403404c1d008005001c45040a0205038840e00200b80355554101004010000108103c001d01d43d290b40845103004210350660383d000001034001052500401141c80066059000d42044201d2100c0e801161501811313064014206000200c0141c40c0d81000305108900501d4403043d10381c0d00e480040080341a0b80280d401419240c00422480c12942c00350b07440421080800b580702c14445d059503408407030503050001a68101400d02c0042031000c001800014035a03542030a0b40f41c4c1290903041944103581d030900396008524110b408a1400300f01e1607007030844a2404600038516400e003074046e40e10030b40034605c09802041c0e08000700542c81f0001c0c0028002003600d400020b15200028184500500c00d40c0d1655903800d00003a0860f21403450200b03022031811003040f4080c06410088000c00d0003e100302d000388208036400702000c44010b5040d20483e882460004c0603410704904a070103148882080f140401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 996183165 1250 996181915 996181933
    0x609010b03070c0221010e210901030e0a06051e0405030f0d0e0d180504060305190507080f10050a091101050f0d1e360201090506030a050609090c090414 67
    0x14500c8008050003620362410302440d03d035105c42c542110603a1050007415800f0418000303140d80700384207502050841d8011107849103800300060780a04003030070303584c07055014480c0c5800410030142c0c0f00c1406407101c2c070000c101424a0120780b03030f5226019074020b81258401c0c8210349110001c0001031412200491010a030000c0c40941e10b4548044043c410000c540050742992664080c03045000c020301044070140107045c9075445254540e8040c41e0504403003402e804044040c0314080080344014404501100c44601c0700b05885a11a0004134002500724204404076003040c0860150400207a0880303c0380003405614001541c0d16481140c03c1000304a00f80001c10040380d1034440e26189410020008288451f0102400111100c0c40c444903504089800010510980030300031000259492601c3c2e003840c41c1d14001640d80401c0c1e540040c0c0c0c480c03000010070040240c0fa0b04094054003080ea4000082d4a404403000e80380e0139481d008a1f005504c500008000c200d040b003101c44d40040480c1604d00d400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 996184415 1250 996183165 996183169
    0x304060c02060d0605060c0c1302070b0a0c0e1207090c0c020603130c0f080109151b080c13120203070906080a0201080c040803070f3302070303140109061d0609010b03070c02 76
    0xb41010094004079008501d03e110030b810304c00c900180c9c14201c54003c526058950796140001e1801401180c40c0ba0740e564000c1d514103014031801441e0703080040009502030701e540f00155650711140203a01c102c90a20b05e20f902001e020318000440c940d4010505400e681d502c0413406d201d5140d102d401c0e42c20455101d000174203609407a5100020302140d400104451070641429213007503220b400c4c030100346460065035a50700c40759603c1c02c10501d02e8914100745140c4420b0801800c4d130180c014580b2103403001403400181d1882d641c03803c0f403102d0b00c294252080595601d08681c201d8605218041d8503802c22900d003401580b0039204d8551000542041d182000d85650041d0326607041100203e551209038003540003401101e110340101621031203540d155071620420040c0700d40741d403911102e000c07580105503c2c041502a403c40701440341f243d401d03c2055a540d11400010b0412881401e84250415600765201c40c000103d092207840b000c3d00c11005079280100c2c428550f4801010a01046000e460314030050f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 996185665 1250 996184415 996184417
    0x130b01030b120705010314010b0a0f0c0203011a010e030f12070615060f1e090b1809042a080304260d03060311030c090403110a0206040f0e090304060c02060d060506 72
    0xe000c10001d02d082d501300360014045400a51001284100c00c4d0010000e1901c064215001d100c40d900e002c1c900c54803803210903684540c0004000f5459400c00350003481004807440c1107018450309aa81c000b41c51024820b142c0c1360b1300c1082d4444243d8201c50301d80d0b41285a100010044644654000100d90f00462000b02c61460b0382e4000f000042c030159881100347e9401904100e082d0112811000180701501c0050b0a0074813910a181d42120049051200b900da41865a0503025015005140618040c54004e51070441c000801030013601300840e17544404200760781c0034240c802090003146400d052502500c0381d440203400c280c0d46004a07100c91041c00b8070074424110346c0c400d41d890100300f050542ca0110a140f643c1d0030640d02907030092480c0e41c076a6503140e81c1c140e000703605400e00d1100e4103140940706041a0b540000039402c2107002400103081e4451445040c00c0300c1b216005080140c4170060f0b0aa20b904c5075105020025180200386400351030300d680100711488802c0400290982c0d1040030582c6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 996186915 1250 996185665 996185689
    0x80a0606050312040b0301290a02060603061303021f0623010f0302070b060111070801110c150642090a0801050106050f09042304060e030702130b01030b 67
    0x21900d40404201d0341c1810030005404800c034000e81c84c1404d0818421028034041481400441c000840c45034000c0207503001000380320708118250755a80e1a070140701075914081555900c1c024494035000601c440705000d11030508607415400f400c80c4c5104914040c01c00d4149a48000540c0e54403403000801c0065412544880d1400e03400c0f101c0d200301c5410024000c0b850140070340d4103050040040400240d0360001e5280e2001c0242040000354400c0c603007485c980056604034940ca0340c40d1005a8641c5e134210006000041c0714102100c1c0d4a0a142188040c440c409681840c1c0140c01a000c62038500b0816950304d403003c0d680b1030142414032510b1580c5044825500000c21007504c000307400e410600b8181c0c0302101038040340009000a515090000b45503103e88840c2c64840000450007003101e40d00d940280383d2444685120200c400c0400380d581c01240e0090b2411603ca0b4a001711007a400c100c00700c1500c10300c039002480841140d2074554218080c008e070700f82c05810156a0354817100203a49614507a44 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 996188165 1250 996186915 996186923
    0xf110307020a0302070f180507120c050702040b060a0c02010f0e09040305041706010f051207030609061407020a020f01080a1d07260c010e03072111041a0910080a 71
    0xb5803a400360034082d0401403550014030400402880030312070075844a1000c40240340c95040020b151f903c0c40340c01c07500d1801300624410f24030308000842607800e9214020704034441c000c03a010040c90f050182000f4151080b44a1074020400b00280783d000756001d02c0340303541b40165604010031100442c4000903903c100442d1b046001c00c902180606c50051000309411048203842c000f81117035410b100030a18048014400c0600c035680c59018408508070034080b900c001d507400340d030500c044075162410342c3c041c0917080146070901d00c81c1400504a0761000a20400441c0c01511816100d071403040112103030034005141d58545074480e43d02c181d404012100d00c04085242c0350203080018201000c0b00760b03074a030304207000e20b603030100e410082e020f1200450404144002401d220310400d1480000c03c0c1002c140ba0300869601e02e04c103078142003440c900315412498610030b626131190a4a00400c00045a00140c50081801014540c156160402c4040d040d08600002c074440280303951060100d14119580384116 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 996189415 1250 996188165 996188173
    0x803010e0403110d1e030608010509061816090203040204060302030a14100b0105040b0304061407030b0906011b0b04050f10061401091d0c090a081b0906130f11030702 73
    0x100070b15600143c040307003003109280a0f2002580e181801011800c43e600ca50a044003015240403105009a100d40024942c00000340710501c2d10b804225180d6004851240f0225103d04031525924404038100800711003507515180490b06011008000f500010412a00326a0301c05000c03002d81d9082160104082c4200e0801586401c801e01c001d0a0080b020010003810741441c00168503a0b03004002d840c1503030b00040c0003586990340c07400c1c640041c1c114030105058100894003804449589a040451515015200542c958591200440c0e0201916180a4480358022400e4001801c03490400d604603008400325140d0725000c050540c02c02c914400c800341e103150781d107500700011250314101c03041c034aa09090021240e8a8442500000e0a8640c8844000e0030746e5800510b0f80f10300541903403e164030141c02c6240080c0c69120481d903400440c00b041b50940c0e100c4e00c02d16002d103440350186104110180c0400d441000c0101200081c0c02e2110021030195120550f008ae03110840024510440e0150b00030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 996190665 1250 996189415 996189421
    0x60402131104060f020703081c1d0c13060f0305060702060906010e04021c050304120b0901050105010804290a0c180501020c01050a0e19050901121a0705070501050a06091d06011509030803010e 84
    0x40001c0b07400c07613401d42b40b8501c40641a402c81e00c0c4c010510b04500340707054481c181001c5400d0003000c02088680c111b08410019824080140540001d0f451700c50250354007112056100c17405919960700c0c017446800210710700e000002d00103040010290100c00d00103020b140e4001003a070344d014115003140d000350007c80c0f0340c00005000c2c81150a01140c11800c031100821884d41003000081c502a80180044c1424180229a034500408150a10300486210312005400d017400d4070590090243e20800400198480340e40d440507402001c04041141d10507002098003d1001e8019135054001054010910a01c40c0e418042510380c0006000c80201d841c0820b90905c4c10141001202d51041e0802540d641d601560ac0c000140095100e91038000c007220703416056507a02c141154103105440b0300503c59420041171140d80f03120b9030843da06940031010140825042d0011500403440d83c021100c80356408a00104040030b10f0700c0581001e0380030ba10b000d60003a03842e40c56544d5190300aa01864500e6180c0c010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 996191915 1250 996190665 996190717
    0x220f03021006090f0b2403091005040614061f08090708161a070807081803010e0105040b0c160611160b01080c0f0306150120060402131104060f02070308 67
    0x417241100c0341103500064140c1c036002c4003245884545810f0803410000000315044038001c000640d042110311905014920b80740c60b00380041c001e01103040000c01c1500d07011071840e1515200c2d442441004208042e016800d0740310459290350003a148a405014079840861051014403c8214020f490700142e980c1c1403030110f0141800601003a01d01d040e400500001c00002c5440007104c01c80c607002444607460348911a803980c2d003206862060399240d882e0000d145400007064011520680c010300d1101b03a079580c1d071150001709214144990380740b451003d12283c000f6406a00811940c0c04100340c0360300b8070004144860300200d0703001f01902d030141818010010403600300400c0700c2c001c2d415500c0d1a50030300d052010942e01d481c0030b850358803c410403450742d0415074821a40840794240405d101509414032000c6981c59440c00d8400ba030003100642c80b0110124100d0040c0800349065500c0746180c10f18241088518407201d150400440c01442c10001c04101071101504000170303103242d0034507000c1030880 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 996193165 1250 996191915 996191921
    0x60b0d111306050105160303020f1b0d030218040f061a0d060602030702061c15090b15030603071203090f090f0c2a03032909220f03021006090f 63
    0x1201c03103030075007091400e01059900c403094403d9101003960b46204401e01c0d160079400f038081d1440010700000c0c00700303502d001c0c08c10840c0102021003149090301c0d0100c200180c110705034490f10f8a448101301048014000c1e0b41066849000180c000a0001074050b440303000c00e0712403490690046a41d00d0021440001d00165071003400018010b03400254540080c550100d1183d00406406206224403801c0b01c40c03242c00c5030341103041400e100b850008078054442a803000104481c045150040c849041c1c018803c4544904403030090100400030481241b8017480403031014500c20003102004076101f00003606018000421015086d08070f4080f661030b00100c1c8038011650b9184218080003400d1078000b0a00d400c41b03800b20b0000d510485170f000e07408200d00b8180c01500817030030500340000e2501c400c40500004a00c910282c41400c940240c0552104400c95220782d5501c1206071480c803140340040000350480b01a10301103842401074501e11403041030030f00111f40c8c86902a56085480708481030f400e054505c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 996194415 1250 996193165 996193189
    0x82b060e061017041401151e0e1306150905070504210308010b090301060f24110303060f040902030f010506120304030305030604020706060b13090f11090409060b0d11 73
    0x1242043d00c0e03207540c07032480302d03880800342c400740c16283c907810a007628501c00e400240101c22043e11f410304003582c90921400f031051702d0b8410036910540310303030200e200f12800031000d000c0c645060074a195080345880702030007003075541a11601c0e07201070b100c0014034120360b014140c4030300b040d912031540b100c1c0741500c074115107108912448941c6c1d854240d980c00080d08042001e040d41c055245207078030340c15640003080c01003110f82c000703001d0002090400a00302c088082044201c0e0322050205c00030180f421001c0d12581070301c2c4400302e90f42e0400c2c00060594244486071443c2c00b0f10050011404030215004242004944949201c2d603944400030409a0300380304803820304c4141d2550086290900e5030718010805c0c000907084a104036000146a014402c190700448050806c840c805039541d0100d8201141d4801b45204286803503087ca4010043c20f40d192144444804504000510b014a00c50800000b80084a0121080740e41c1e0070311000d05da00c0f00c3d181400031a01c580049040000c1510802403403141c45 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 996195665 1250 996194415 996194417
    0x306040c0320130c0908030408011a220209220221071209260c0d03061421060702030d14070906180e0c0403110409082b060e0610 57
    0x41d40d40c090302a10b40c01c03e03a15142c88002000215aa0740d5031003160a0b20655000c81c10f40d2201250101c1c03501c10650044241c10202e52210300b00402d26010311404005002001030381c3c0c00b0541c9500112070941d0014602a9802004850040c0d081405051401c01c81202902e443c2e0780480c081320041614010700007030b00f82c200200b007114030b41000010080c1512400301010507466085040401810800030324031010b0565000c40307024140c1c405500c3c2500801d03903409680c411a82d681c08094040e2051400b41d60210030b19811011520050008564034400280c0900319802505049040103021302401076060745d0103141c2e200101102041625003044480d2203c2c18080e091028068124890801711800d07804c190000400684c080c1d640c0c1c100c15030000428204000400080a00420003001a43d201d250740d584c06500d04c0d02400100d03601c3c4100200149010003041c02c45028400350100c03040725001c07000d02c1500b80560a007085c0d690580c410961046424144442c61801c965001041038003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 996196915 1250 996195665 996195713
    0x309031605030c042d0603080c0c10050a1e0c0c090510140d030305040f0b04030c0311060f0106080604090c080d0e18070e060405090403080414030a0c02120c0306040c03 74
    0x11040d8040215050b170300d607001001542505070b410b0107102e604500c1c01590080c8405488e0b82005000948481a0701d003124403442d804400580702e40e005105075003100074540c0c0c9680034166489111035100c074000d11038000703005c444082e9200040b0072441580c00b400c20500b0106803410b102480854448940d0020141a807017100c2c1d49410b601c40c070629050854043c640858251100d04100f207420744411070141c9260740e84010131007455001070a002c8a107220355500080c00e580c00c408103413120300c199840440400c940c001002598480d140450b04804010000034003030485a9030060316040320390212895400081c060030419030000c0d078611a2150a880d22007100394419055004210020400e01c28020888a070914940300c45090302c2c050000540440703000d090505004d400c007a0b04803002c0320409071044183c0c141d144040183c0b0f104020a440300c81046041d90b080203600b05100400c48003501c0f0760306100314155810413005000b107024501021440341541007141441c0030201d50340d41c000e10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 996198165 1250 996196915 996196931
    0x15050105121c171003021c02010e0d1e0c090c1107030b0703060504090303140a0b0a0b09190e0711010b1c0c0306060b0a09080c0f01050c0309031605030c04 68
    0xa40412006090425416400318100d41c481d000d4030b152120b003e89075000f40e844420000640c80921849080d80d00851381d00d04020800350000b6140c09140038001e00203000101d1746022420241c50480001d4401d05940c25410541904407210803040803064230f42110360f540400071300245200d80f410b90282c40c0360040c00e29021451450f034954803072000820020b114000109078500c241e01035000f070103004105204200050400401624480355a0446c0c010502c0c0400c004007920f02c1200451880074040e803809919001c03840c00f5540018544a410485042103401400c1100d04450701920001300f603001c083c10940d800030140ca041d04251040d5038074100c0803241d150758050142440450f51244094866000c1c0b80190741c0d8040d59000034040c5043c80030114180b02c8240113407100d0f4216a0740c102c41d03595100441c0343c3d90a111110280c221a02c0c42280308254840c0004140c04d12140046900c1c0803803071300c017180c0340c546051544211142d00c0c450620aa2605200c42c50b0801000c131410f1040038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 996199415 1250 996198165 996198199
    0x1003061d0a0b1f06030c1704240e061015020f12090310050a021c060e0a0c05040312050a03060e0f0a0c0e031e010b09011401030513020d15050105 64
    0x24600c541c0a40040b12a40c0081c1505498441459100c600507224451603a5154400b074090008000b0180104100c65514a410a14818900e2180303402c0380c0202c020700800d0740720114000b41c0a40c00952552540c207901d030300e0baa003007001317a01402410b449803450519184800140c04620300343d80085400109100c2035032400001e412886018820300e9903559030762440041e241100300346030071110606200401994000e81c0d8041c12840000e581c0d0b8100d03002007603502d0320072103445009a00c00c1445107004604030512a900414810490381441d92a00384c694480502e2280307044034020008100041d290b400c15072500506004201c6100070100b1400c0c2007011a40d240001800005c88540e100d0783e0070a41742c031402840201d1440941503a2240941c0d411985013101c0c1403050f40015800c2c11081202c42c04d004d05007e04030340050304503e841451420046000d0203010f01444084c4d52113800c80c0016996161420000c5480b95160076508054451654251a016804030744a018070444c15a460 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 996200665 1250 996199415 996199423
    0x60b03040f111008061e18010501090b0703050313110307230d200103110a0903200102250513140f3c130b010504110714010b091003061d 60
    0xc41000c651001b0703281c25508114120390091395405900c040c0e504040c2c0020f010000020341610801e9a4443e603007500c13140741c4500cae82b059040040008500b040028907554031488140300081c0b1038040b00c0285903164001030300e064680e4010300d51080039100e00034443c81c80d0f1002c204103244161211020000c0301e880d03400380360800340e45c0c8518480744440e0415185e8420f40c01700074004040758000d505c50003a0b0b04020300d0700c195404222052909409611303801c244442c254403050005a00500701c2409003003451210b00c691074a44000c0d1034040300c000ca02551484001424082e450700c0000e51110500c15125500d2405001004100740190a100ea00c2d0b8039034000d40c00c02c52000745800d01c0910300c940003158000c010060885042c1d1620309004054442450420310503000b01c001004a980b01c200308030886810440100041d43c04102c2c1c50000ba060300c4600741004030050000424007034010200340707104001c03162005541036840091040000303905c501801120000c114821550760100c0301651 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 996201915 1250 996200665 996200671
    0x60a0b0a0c11040203070348031103040629060d0209060717040509100f090f02160b0a180f1e1416060828060b03040f111008 55
    0x410034907441910501c070001425406111000d0021580e03032408000042c010848004040700707800380702601038443c4010b00084200d081070b004841e0b050942c80042c0d0340300c1907a05030319141456290701000c842501214040d5116074003611700842c00400d803511345030304903010601c0c80c0a20904d40b6089191500c46005681c07912401e01d0b4010703603648a4900184e001e0045403c0200181c1052100b001e454002c80042c10845030140e901c940907403110000c90b0b80c400c0c01c5024081e11009104001c0140c031000d41c0103004c800624017401450301350241d920740008100400140d07100b0f580f0209100148000d80716448816012031003000d0f10044564440800600001c400f030080c1c84110100e8080c0070941a0700c15085a020000c070740c100000e005559202c80c104100c035003c40300741c00e030700080050280c1011803160241c240f40140369100b20a400d1400840000213140d820350310700e13010810024840045025500806110b810700465261404075000e5100605001d0b58601c008024400e030050310042e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 996203165 1250 996201915 996201917
    0x150702030c0607030b0a0512010e1c08060f1206160909090809060c1204080a06050105010905220b04110c0c0609010c0605040f020d0605040201031b051b0a140d0305060a0b0a 76
    0x1da020105000820410054101c42e0340401c1c0e86148d1080c41405500c240020b00c454070a8419074006a220140007030307000d025100c040303101c0c400002c0c401c0c58101c8404c48030400040c80a5102d0742051611842e000c422220340300d03021401a49488007940001c0e00c10024500c820040c060700c0315035a02d800c8940240007019015030000b152922800d10b051103492810300700f00030345640f1503503503081c025690b5100d4041500d20350318020001c04d240d441940d2074815560050301d0085002940382c58143d04100625900c3c4456503904458041580c890080b26202c00c14000001e46954000006c9801c00e90480182031007941c6c104425415a43c0001095131051341181001500d90380c1d070308000356003200f0950002e41c0000004202c004100142c0d002501803030007070741e040204070146115020820707140042a40464000c0c850140c10f061055050340c12412030806680a200c00caa40c1c0c10b1050300b105580d6842600140d40086415030b02d4820558004022903e003052549001ca24114511030a90311780 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 996204415 1250 996203165 996203171
    0xa0b0a1710050d0b0a0e15160915091701050f0c180a12061803080c070c15020102031602070b121e04140f0309030303070e18040302150702030c060703 66
    0x8058208400800700201405010401180700c0c51404c10746042e42195809186403411030702c50421280002c00c000060100c0301800810340300c0250801507a0580441d640401c82441008220003282600c4440142030546030100d00c1820034511044a410754880f1800680c0341c8410041c3c0d80d0580c868941d0010384c00d00956907076080a02403081190804080329402c400c1d200e8001580702e50304450200d109010310803c00809000c4040d948008610800240c0018810008544030304110300080c6045407040010300e00303050781c072130020585c840d4107810440941d502204100e4a5a15120804598441c03480503082c5242094540021400341780d55403800c0d10702640001e002c402c040411040300c0a95840c030304106191070701c3c0641d40e0a460f000c02c072031355000d08180c20360300013400410b07201300e101c00901035400e55031400e0b81101c056078103481c166485010040301500664021040c54042e50080e8080c4c88401045942481002c00c06420001158410440a148440c0111382e8a8011403549404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 996205665 1250 996204415 996204421
    0x41e110c0f0a1e030c140a0611130e09010f0501033801062a1209060e0a0509060301060513061d0403020a060b060f0a09080d080f16120612020a0b0a17 66
    0x442d241c1c41d174104001c1c00c841c110382c0c040225210000d100500e95101d41400d1000d86661418050309004041e240e1181264410040c4050340131400b20650000315003000242c1c00c000d40700c005090740d5080e801903c00c441070010b04140d01250500301d41032034124005025040c0340d40f40d021801004140705200c01c100b8080707405031003001401c032440301041e000c41031001910994149a40d03000c24015a084c045820ba507400110341e80182103207503080c4070040a544105161a05001019800030f01c0c00c0d031326543c1c1750400f080300d65070401c1b24030215036803a200040c2d4a040810341c04191060340c2580c4c100707180442c00c01c40003c1e80003501c230300780990203c800301d9460b42400105250340602d25090b05855008156030303910584c045030502c11111040d040b102503803d01d900030303075008006590382408400060002001105030b582443d0704000d03c0c0c0307030040041d100500b028003201d07010b0304540706107440c0b417181405528108500d01d0103001c010120502d003040c02c140290090002c0528200d80500d8a000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 996206915 1250 996205665 996205667
    0x310031b0302090702160e091225030804060b04051b070c15031e06120f0812040f0302011d1e100e010212150d02041e110c0f0a1e03 58
    0x1480d00556029180d5031441c2403918000e074584441e10f51842e1090111500080c61104c0110350030301400341c0f407014011800c06d031401e000c01c030343c4201070f1a20050030001580e001298148681240300d4002c1d915100f02e4102817510601340c038651101e4030f110b00d0410741805404404010011060f000170005550740c1c040c1890980c01d01a440d070300036100100802d030701c1301200343c16410074400919200c00c803642081c6504071340c0c0c0440d0080c1c01000c0300e160100305030310000348100240544107401303219001d050106201100b0201241280d040b900706010820413010503070240905181c4804442882c0040e00520030066560440034100c886100b174034501c41710381c60005212001c10001002d02c18052182c0314080507011b940800d030441303426021100002c1121400b45400c0441c0c0000400c9100b46801d96001c01000e81942020a115558100d5584070600720620070807030503e250b034905070380340c81e803000c00b980c1401003400c5444c5460300400d0060340040c0f01840d05651040c80070784600014401420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 996208165 1250 996206915 996206963
    0x17030319091502130e011208030712090f0204230606030703110f0705070503030f0d27050a02101409061e130e1602150a020910030b1302031003 63
    0x70000d0640c2001c0b48200001d20581c1e0001c120b001034240d65400015070740d220b80e504a040c240f0400303000c01b01c2c99140c0301c0060700540c01581c02c07494918010503011989180b041c110b418210702114080015080d120847c18240164040c4480c555488501c0c603484003120420030400510181c41079400000086506000350b00c0503003c103040e08001921110f10000035091a444840291141c0c8920300c07002403149800011241101c0c4080c143c541003010301103848015011a032030198043c54180015403182c0a10014001c440b80608000d1001040c4c47c010300001d085800010303c104415140468640141070f0200d41c038001d0240c0d82d0380d030358200451480d2803043c2c030041688201d15001920a07090244448240709032078a80c6520fa030240c449030b168030940000c1d01040360140e002b80c10304452401c109401264012000c0e50058600310f5148001288034410344401d0010950f120180da90504040f15011018000d00004500c4c50409890050180e90310744002410400380c7d6039148402e00c2c40b00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 996209415 1250 996208165 996208181
    0xc02030c0a0b01290f160b1314011b0c020a0506070c0602120711190e0c0a1b02090609041a01090203041e0c060f09030506160917030319 60
    0x180549007035101c40e01e84807200346420301c2810b50303036a10f01c01041d181d440640e0b658469581e81010b01850460744a140701c910b41c00140741d000c20b2005a603040e070045503050304a10700c9000f02000102100310680b80c82081c101105441000c940e00d484044080c41107103178801c20400c0e07a20704044010401600c0020b4109185402994104c8401b040035400c00c1001d00601e415290b041d02074860b00c849196031000c0c5401180e101900810024800f050242001e02001d1200001584841c408584480f504900260b00b950701e00700b48400050191000c2d54822041e07051810034201200c0070003036075000104802c80c09807006200d01d03080c40100b0b04003c0f90f481150452032544030b2040041d030755041418003c0d00125015220310304c07807660350440001088060803100b81e004411200a0b41407400c101c908840d201e58503c18086401c50100c0410002c11a9a204940d040c0c0d800d482c030700079081d00074484119a800600d40812162108082d0032020003580e9125640e040c41d01200c180343c000e1440500500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 996210665 1250 996209415 996209437
    0x20d1b082806260d020307020a05040e0f0d0e0301141b1605150a0501090504050604030516150603110d030e010507020402160309051c24020c15010501080a021207030c0203 75
    0x41c0001d8102c500d02e04240f81c0700941c04161035a032209580f090707031284900b840c001c0d880340c1c4044080c461441c0070b90100c039214102c0000c9039050b03903001e007002e8503021400d4502030210389800d043e8481031034240250040720040340e081d0340150520103400c660102514005150402012403019000900e690030035200b103400508072201591914013a946200c41030303d00840050910002068041d894025540101d078854024401175503142c8048500d5000f00c4071070090070300b405180101107214140031107034443d402c000004078186940740c01c002d0301c1912001c0501419503800b14030003194101c1124181c0030001c0c05c10039554a40b603c00200288205d4a40ea03101041ca407070300300c0501d540542c000040e50707401d0300d00c0404400025002d2291040f03040b0000c10400c4944d104c039201c0c03113900c000d010001104074405800c0901102c802810400c400c4015410364107240c0c01000b04d036900ca240c0e5504440290701c11843e040780100e00600d6400000d042301c050546070101120a940300f00100e4241c0012 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 996211915 1250 996210665 996210689
    0x6030a140705041e12110418080309010617151308192c01030207110405010e250804030f1205150a08060609180a0204020d1b082806 58
    0x100304060001d8005000d615805001400d0988401411003425029101c1345c0307200e00c16401141c0c0e1000614500c1911898001d40c564a00082c14a40e903921481c08500c20444681c69191904905084074a25031001d902c002c8010009240f80d400403443d00001c440e900c41c0484c240c0c0c4e44158101d103103845c81c100180510800607010140030000c040129480c1501c0e5119a144141022658442801d4009601c2a1448005002c0056000703038028400c07103101c1d402c03880842c0d03014000501128000d9108000a80003201005018100000c0e00c2d0303020340c102c0b001e50151390542c642c0142900001000101803020008000080c10300030b031050800c800d8071070300602c83c0d45800e860500004c12001c2e2805c0c0a41c070302c2c0501103002c06003c210203108020180082403a607480485030791903100d200111110501501191602503201c80c0010800c1c4c5071669801304200340071800c6e4164140903a981a410448444140705116042e80c24226040c03040321100055044407084200081040398090307680551 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 996213165 1250 996211915 996211921
    0x531080c0607051b0604150f0f180b010902040f0e04020609040e011e05040831030803061c050705090a14090d09060809100221101e030206030606030a14 67
    0x94030034028030f0200200102d40741c10020b0311520341da1750302c0d050300d0041452406400c0e035502040c880c1e1240e17044d5034071800c011403050075001603d000c54000b41c240c258908440440c050a021461001034014100007200710316140c030f840c2061032034220784d000e00e00144000001181c00e568a90003992100c1c000184100714803040d200c80340d0700800e10f081c3c490482000354100c8049202903840340e03920454200300b140d8648490320750804054440781c0d101c0d00703131850700c02c2031166000c01e40540e02014610902da000c0d501e05040381000449880304180743d11503003c0201e4040015004a0040c040751000d071080710301d90300c80e020208040c100d12010030180d0b007408010840c00d104000b900618806681e140d009180340c071000300303d440c41ca04440b845003d0303100300540503094a01e5801040141c0c10070140c0d182000c8124111405014281c40300740400e00b50301c00a01550a143c0a036134404142004105001451940800c110380401800d00784184030100001e51a00040e8021008100404d0b989a20f40d01d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 996214415 1250 996213165 996213167
    0x102071a07081c0e011802090117120a0305010801060902040b07030c020a05030a061a0a08070b0f0f0d0b0a080d1202130306020a0f1209021c061e060503010531080c0607 74
    0x19101303c0240b4940c01d05010b028880808100341078847c1d00504011081d0f8204050f2444500b904840e0703d100f40b284d60628014400c0401c00780406050781e40c1d01052035407500b4169400d40710035400c681d40c41d62040008201d11009041210400381c0d16003041031004d400b6000240460419a10450700740c00342e00804020441c482d0321042c1004801d45440481e00640703414000c0307d4150340101451503008000a01043d4048000f502480403510300291900414201c8a81d00f0340103030380b80304d4020303444000c0d0100341d1510307200380da020b00382500c000d1800c4049010020110040d0004401d5143d42c0001e02d00c0b5030160100740071001c0c5400000940d540d0f801900c006000041c059138120004c0c0016000c2190100d050182c102c0080d0014072590301804045465240701d11581c0701103911079520742c0c0e8800e001105c1c19100e0301341000f140000441c246400c0a06017540e02c0200a01d1a540c00c1040c5032005a0178600c04c0c80203047c0c4604c1020300c0980070f1034500c00340e1040322072240c0e0314818001001021 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 996215665 1250 996214415 996214421
    0x210102041a040503030a050f09030106090b01230f0a0201090b07051e07020303191701140307080105090304060f0207031704090c05030405120d09080c0303040b060102071a07081c 78
    0x5424a0404501d0818001c4a040980c092806101e0741a08100704910b0443d201d480500405002c11003000d1400f22440300280c00c40d18242c3c40452846d465501400b1191380080f180c4120060360340908501502c4000f050581e4410701046500c0070304089050407000340300354040c038031044d8010a0348409080c84040905160400e0b141941240f00d0000b000d041800f0500c140c80e0310300e41c0900254181021b0024000d000f05100c111b42c1c0421044489002160300030810050091035803e400a4010f00b80c10b0606050880b203405c0502117138104028440a410b0000440e4112f50103440d0070550022010310490400501d40d10141503030056002c0e541c7c010201d240140115111008204100c40c00f9480030b49140c001210302418a401010441d44204e02c0d17040100b54807903c0380e1000440f980c081d55051019080554000e10b164008000c11041204068184d03402040c240028a070380c0c1d00d01102d070040c00c8210003001c51240c002040340c070100100001600c818215481c80c0000754141c1da2219401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 996216915 1250 996215665 996215669
    0x61c0c090509103c050f1002070626070905011d241e090f0108040b041b0f0e040b06040510030609061104090b19060c020613030b0c04080706180e0621010204 69
    0x840c1d07210306e01c10041850095080d1309410100c0e009090442c0c600417056501300b080c5030070020204668464110322000303004249204901c0c0c0e44450720050700700400105018000c1030f011040e0201c0c402d01400c1c6550320f0043c8070141d0092540b9048002c0b4881042d0007078014641c0110051280f03800c0b81806440308006041603030400c0d6220720040b400c10004498544098038042e1015a42038042000700f10800c3c80d0584580080c0c0010b01c0240c1d9605054031810703101ea0000070030041c1e0b10300740020003000d0500f03280c200004507014040d6090429059140d240d40d84801445260b8551040c410800a9085a0b041c080800c521984442d40c0d43c246c14068461040d07a5403081c0a81440b01103c0140c1d40d100200b03179041a03645103440a071079401c1c49811791001c1404405e81908001c00400182e1100240d44210040e010442c1c40b0351504414603d0200290030400c240103441020641140f90040c00d042210380c0c041c104e540c183c44060204a1112240074440c0383c8444107952901000e00c150003d100b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 996218165 1250 996216915 996216919
    0xd020f031912051911070b03070203040906090501030809210109080406020d021f0b0d0609030c0b0a11270315100b0c10050402061c0c090509103c05 65
    0x20081e440041c0443d198450a80d6903008400520304107004103200e1210101c84003150021208070f6a1a428070312000d4004591180040e480014180910442c90140ca0001d20358000144595411503486034100c0c0241d0304858091070b0b200004118200d4004000e81c0340d15200310003046810071034240410154041e005201c0035104500d00e01c610144009580f0407409014072400c4100c0c110f8180361005841d0203201142c0c400400c11200c80490034510030304201c0d80c480d03183c408a000e1b00e403601e1164654010000d01c1e40e149041441818180700310f0450f0140b4a50b8551035000349145041c6411800386030010b203801d44209581c40402000603410140600d040c40700c1c600c0c2c01941e60079121042d2150501d41c3d0b00d690802100b00051916a0b04901e8000348001c203a0b0f41000c4514540c1840740b50f11344203200d10261030b00032880109420a001d040504001e40d605001464101e8240d41d00058030301c030b40300181515a5500d988182c0b091258810170945941b203000503044002c5d031940e000101e0180038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 996219415 1250 996218165 996218183
    0x120f050403081303080f0604060305031201031b06020705061608031602100b0109180e030c010c030f0212041b0b0c0303040c0e040b0a2406051c0e0c0d020f0319 70
    0x502d00d1602c15003502d50056150707945d1a16540c3e04010f98a04a0003c0c00d040c1d00503031030724408030000d1000c0c000342c203100c994942d0580980d807543c2002d80341c540f40840c005407a801808030a210303507940400c1041c1518820f44400703a80c0d2200d010114203402031040d01501849021043c4200c2c01a1403100712045400c0790700f142c1004408411072400c47d40701808050100d02601d1040102c0106d0380030840d4000c80d211400a142d1003500c94081c203540c050030b0550400c0e50f440c0c4c116041c440c0c25100340b00c124000301c40304504160341d02c81400503e1402410151440b540280c0304a0105072844c0200702a1611250303440d107462172039005e6075403030b041900c040707400b000041400319103007403036501c06842107802140089042d02d030f00a0740e0004000740b440c00300c981781040089403100c42070041c0d603c0040c12560746050f80da04e01ea5401c0c0d5485a1404034040c0141c2c14480103a0075800300045081da010011582c6044c0c0460604c001030003050080300303540c0c01d0302512080f98034165580c00d02d030010501846941c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 996220665 1250 996219415 996219421
    0x40f0f060218120c011409040e1015060c140c191703030c09060703090506120405060a050106021b0a09090605061302190e062a190c0603020901120f05040308 69
    0x1000000b12004a02a13012580c071214640c803a41501c000d9034003102c0c24924101c80000402c0076904500e0300e004c800c1e07100c0c070700c403e005440ca48108d00c940340710a0790012080e410070400074241c0324401006008081c00300541000c8072814031002c40c1c01c050003424070410090070041d10b24a006d45100f1629002200700f181c1c410160040110b070700c10700c56400c1c0c5030302e0583c0a2041050755040110298100603003c400481d4546459008055211000c1c1000c000c03403802d40b80c00c514010300140b07442d65490800004000f1540c002030907190961381000104103190200c4007082281542d94004109103040c0380041050091942c480d41c0201400d441012000c96885e100d42d09038403c817607aa06c80d44c02c4220700c0400503481480b90301c0103400014901890458234004000d0b40090000405050703103100707020b2400300442040410b2401350b441039070008501071600c56048a440c00d120315001d00d500000c655146030300c02c0515200035203c00b4030070044d12401c400054000c120888040f000300d6041e0001c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 996221915 1250 996220665 996220669
    0x10e0108010608120304021504090603060b1e090106030c030f36030c0204110d1506180308030c090607051903031a100f0e060c01140612030a0305040f0f060218 70
    0x1c480304001e15074065500d51b031a25424481c0d030f00140001040e07000da0511022610280502401c00254040ca40202e40600e0a40c100b0000c81c2030b80c00ca40340380078002184900c0c20b07191985030b40c0c115041070400003650146000241d001c0c184204201d0b10180c581943c1034056100c445407024880d2180c0c010900680500543c2040d0401c980c40180c003042032920040c0c0180b91036040404c1120920901504004030800d111064070010b2560200f6100d40d0b03401400266801548414404840b20b1200d9810b880d54070b40712501d00c03010300f40044030351000465aa00d41c8519044510041e400021030301051500c0c0d031103032041050724400f10006820f2000b410909203014000001a41c0b0040000c40b802c2c511450580b032005801d03080c00140281180081c2003981c0d0781000d040300c2c2440800205400680194114840d800101254800c00710203018240c00000001502c0d40d000c441d007400101500c59040510280c0041e0a0003001105811206410041d290700a81450744001c01030b0703c013520918003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 996223021 1106 996221915 996221923
    0x1b0403080d020c16050f0112090203150114061903090f06021305120307030503130f081911010b01140d020f03010b1903090506010b0f0c06010e0108010608 68
    0x30b852251803c0c04e010003070030030410850402c034041c2403100040108001010107410010071843e0511903540c19482803a650341c00404445090010040031540c00c4400d000b143d190031644000c942203814000c0a84100510a040c2d900b007414103e40220028080c0c58003d41d000403010030348038080f525620040c1614006404e40341022400d1405005000c650307107520044581c400c02040000c1313a4403c3c10340e6080754400c5207020070500076041c034a00c03514008201500380040083d11440010a4444a40f1000182d45800b08600c43c0c0d0754800d4202c0702e60f0013105020511114241000d921000010103034607000480060a00ca0901d135061aa0b0700260000301403850002109030b5848805440c3d000c2c04502d46c40c040c01801125a0b62645502041c49004042c20300841c2d911080c0c00351001b52034040d482c40084400542e501c3c000000c05090a21510740720707500c2e00340046101035001c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 996043165 996223021 := by
  have h0 := BRFrame.cov_init 996043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 996043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 996043165 ≤ n) (h2 : n < 996223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
