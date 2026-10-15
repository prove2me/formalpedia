-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4116
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:36:49.084135+00:00
-- url     : https://prove2.me/submissions/0d26583b-1907-43f7-9be0-d5818026d841

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 740107913 ≤ n < 740287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 740109163 1250 740107913 740107939
    0x27010903020904060c030b0612040303150b2209050c0a1d0d0f03020c0109060f03020306060705030c0601170303070c0605070909060b13090c0f11030d09031e030b01021902 75
    0xc0c14500034003c40c001c02d030004503180c0c0e80c98010251040b141026001d00810003010070120707440154950300c650186130000b000b401c0e015601000d01030640c401c0e60708002c0401ea0026110352000100100c011410b4840e01c182e40e0b603241c10040c0c0301e045801c94007024007400600012070284041041250081030900c0c10441c0c25030000302d03030050401c4241d40908500ea0b203d01090340410a0304003142003400c0c200354072480e01c07a0041c40c5220040744542011b4000c1b02051554581c913081d02d0040e81e0103000e990302d0740107403001c080da02d940c02d01c80c11a010f0f200c0518032030380403c08001c490050556680303150070802107031916405080040d007078200b08158038400143e03881c0c20f403045202404008074030590754400d6a949081020b5903801c03003885540b4050501d880142c002001009807134a90034081102c059940d503040c21070040c9402d0200351420109104105130740603149c0c0000c06800c008204001e52030f90701c11012500143c04903409a40030851036070380e02100324940003036984010902028003c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 740110413 1250 740109163 740109169
    0x21c06080309282309060307051215010321030e0d050304020f120705040b01021504020d03020307062c010c0f0e060d0e28050a081305090415050601052701090302 71
    0x50294004d240642003a40010a11241406030140c10a001c44a15a0506012000a4445d0302510a00d4865502d10341c0f904031a100511941050361040707800c4045544e981d051410904801b0004018450100365502c02e07410b009126402e4981803180040170080403c00003036805a0014200341c2e44986444c0b0b0071001941c0c0c03003144101170001800a0304515280c441400140c9125461040c10741d0805802d203201040c1e141c803140d030f0090b0105e880031301400607820f069040d8810848082c0481382408266001441020504402c68960501550681410049072030032270710480040400920048203403581c1a01c0f4480c3d2000900c1d00410720303850b120800c5503403011100c8140c01c0340110b8002c14100c00455041c025109507025050040e043d2445c0c60b17030f40c2c046c0c403103028801c020105c100100705845007403120031170f8502410000d840d0038074074141420850f20010311543d01500803030a1400142e000e502c980251010301c0050541e4140c440744141039154040d040440e0030b8108400c3c6180000540e03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 740111663 1250 740110413 740110489
    0xb1f05120a03030506061608030a02070b0f01051306030818010233090c01050f0f04030605010305030702030709060f09020d0209060a08011a1e0306030f0709021c06080309 75
    0x1810a801000941c9032441d014080e603d00030032280c414101407150500003491040c003003582c541c0c010304c01580ea1380e0306408403000340035148014045800034410400c0f00b02c00c20300f4243c1039400440d200c540200c000c0c1c600009a60850200402c16801805454104c04403c58107140a07036050054680c5540d40240440b4103416040c01405500000f2a0460401c0c00e0f164a80e5041154680949100659440081e11a02c20361524040c803500000d1038586215401c025240a1a440f81052100b960340f4203240760741c2d8102e802c0c260f21034011540d00090398040d0f841604215a6003200480788075280141c1030000f50000808034084039000c001c0c10101c0e50780d14005000700030319621340101c2541015182c4400d401400404611484100001c980290316a140705181c24088440d040c0d503655000d0209007807074504074030307015188200c000105070701780580c01a1440c08021000302c203240380f40030495402e0304c0039403051141d9070b0000c011501150425000c60380c0c0c03094103414254031111850190840301 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 740112913 1250 740111663 740111689
    0x30f070f021503070e0f060a08010303050703212c1c030905300405060f181206090c1e060f0f030c090901050303070c0b0c0c0d080405030c0603040b1f05 67
    0x82c00b41240e2030203614260b002c0006e148019a44141040c0407441c019107155811b0101034280800810780c401054400d040d03240b01034010030400c07082800140300c500050004090b040481c8041456054030104600349038501c1c1c403082e01d0041c610300c299181c0b803101c11049501c14400b0140c4543e850008501c082108480d0090064041180070002c11640c10710364041c84c0b02d146085400700410080c0c0d95032801070310f00d40d40070030f00482d507a210488000a0000e01074030100385c01c40d0314545541c1c3c1900340410301c1842003108501751413003084840200b001141840e0718162105c4524041c00f81d607810140c0140050429114101e071a0951901d052945600100e481c6200300b00f00168041c00ca041c000d03442401440181d00031400d11140c0d6943d201d01d4a441e00840e0442e0002089002481004001e54040304502038008200351442d41485980e42d40300d801002d000384140c54140c0c810b802e02100f1a445280c00413803003500354031050340344902e2011003c149904070f28042000315042d640d0902c0b02c42a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 740114163 1250 740112913 740112917
    0x60302390a110910141003060801142202033c061e010b0a0c02281409010810020c010908030711150603030d230c070302070503030f070f02150307 64
    0x1d03207410404000f40c40e038004004000f03062092000b0091805e071160003582d0024112001c405070910000120300a00007680103414543c05d101c901c8100134010700002d4060406440d07205010a03000d030910b0714607644400001c0d0158800d015802d0003640500d10079001882c03250390710000181c501e52540b0f202c5c0d1820385075112600f0280900555100f0004090045200540b00c0c10542d0314011813220a8001c01804505100160b8030803011035a0300c040740704101c00c1c0c412620f14140801154075102e46454001c643c88107081e172100303040b9454043d1200e41210099801082410706c10b44030318010350031080e1011181d640320000880041c00000140d8450011555214484001051994903108040e1042c80004001405000c03660301c01000311500010b00c48400700e190000d0103103501c0c24078000844120244248401e0004108541004085041c000d034200c4030000d485204040e100d100d080752601040c08104032150000e8402148480e2980c001000000c210141143d10b5906034407c58031000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 740115413 1250 740114163 740114183
    0x9040e030a091517040201050a020a05070b0a030e0c061b1c0c02040c0f0519090f0b0417010612060e0109050a060e0712051506031c0305060406060302390a 68
    0x2803400d581c0d01035210428949008503080c1319100d01510780000252010b030401000150074030741940200001e0703250992150841d40d40a90310300c080307050340c0c03c07200c400c00000341030a000c00007000c0000b0705203000380001030a071880c164043c0e0b0303150003503485404040100c0c025101c3e41c031700c24114a6130b20b494030202c5440f05103900725144104400c58514070348174828001160301c20403030503612030152303441070501c040701c201507079110002500c09000c2075011481c175811552022450310031070b00240080703d080b001c034540d41d0f82080700344070700b41d840d6401200041410511018040b6232a41c0000c41540b05040c00050249100d883d490300304050888142c03072071500c418001d0b004550030029440200084501c02e0700c00800c90317a6850711201d105024170002c0150300d003c1078155905211881c42c0e040d41c00d00c1c00704040710a0b0360240280c00100c8040784500d140c91000103100f03000340203c075100074608a008030b07111444050745000b0103a035400700b4900c50081c080809000d070104000001240074980040d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 740116663 1250 740115413 740115419
    0x602040501120e0c043305040507020f19020d1b14040903080c1b031914070302030a18050a0906140609030703030c051009080901080a1e0209040e030a09 67
    0x14102c202c410b40b070307004101d01d00700c5800000e00340811103006442d4101c0c2c0105021061502c0010810050749801511b00b070070a1400100d124078000d99000c80304140c400b40255980c0c0f40301a0b890b101c2503465045a6040056192034440381010781258941c8001c01980c515045130701c80031781c402d031100745400040300aa00140301c00c035030808401403048411201844200c020755402082c80c80068000a0740900101d507440038a880000100707a11980102100d803241c400034007514545400054020200d003800c00004444540e40007100d80c507d826400540c64440100d00444510340e00b692409281e0071060400310706070b030321801010300a01d00784c032010840a00b4105c28082c1c048078a81e160388560020464445903031804251001100c0d09410295100f0549003059400e018007140d00c10481403a0148141c00c00074590090140e0400a988103001d560381c0b009240210f03045882155940c07125503050007400c0781c107600289040c001c01303800410301101414101c1e00d5501705088540c0480c481082c14 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 740117913 1250 740116663 740116667
    0x1506090515040f05130807020f0603071805010f0804020925020a060b0301201c1b0215010506030a0c09091401030b071407231006060210020309031210120602040501 72
    0x10755000c00000c2c8041065007005103411604106510008041b8080440d016055555070b041d80800c140014080c0f41e075170300c0d2040e0000c00d1501041c1482942e2816114080f6095104080c100c00c03105054465180580719a001c00044400041040d00ca80740343c0c8503d6040c200c0c2c0d01003c0300001509030001e041c409505d15100b03054804003000c032400b0b60314041640c0159800d044c01140354600300550507076542c2070301032a001c4134440d00c10b070080d0240c00c00b2100d480040300307550382550704041582600c1120300d202d588074410010038800d165000c2c0041c00441c600300c9881d4041d503040107660808609240d03039940e614096888000c10b140c500304581c0c2c01041030140d03480307025910000300c0c5090303120708a480012110324058180c000d001e010b6048050f200c410b1b101480c0c00d0407900f000c42126803034403010641d00050b1409010707020050040742e5043e407018070b16000352402000680c0155091140351303403089030010300081c00c44811541f044030005006000c008802c0303c03140504c0000da0703214103007000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 740119163 1250 740117913 740117921
    0x612070e090f0c0a0504020f04090903120501050d0b0c090102210a080f04050a030815280501050702091815040303060e01050a0803070b04080f0f030a11030402090103150609051504 79
    0x50b0148540114803944000c1d6118481482910320807240181c031083c0e4a0061049400749410800d032580c544004082456000300c0098070032200c0d10342c02c3c80140c3e02c403401c1c40402441c1d88002408200d0a03c080ba02100f90240035100580c81841196440042c7c0c00c10042c00948034080040fa216000030707410342d9980c1c00300a41d540502610740c076040e5070034107585040da18920584041c0400811001041004036100c04840001100803c140002d000c003020030865544800418007201d101a030300090f440d40070302c4c2601d01c07242d0010002443c1c3d9507445040700000c00d140b1b1401c5494040c0c9100003c03090880d510f00e90040e4061360f80021440c3c108803041c4003880d010f82045110300745004041152090000840d181c0d150700c034510b10769580310f030302c0c0042041c0104618280c0424020800044030365000000c0e500c80c0304250004d01000072407881151440c4016a800780d0030080c2c0800600101d0680f800c4015640b00c0d5000c0090001e80c0c400c1c44030110341054415aa250030445002240780c641401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 740120413 1250 740119163 740119183
    0x61706010c02031509030d0c030b0406090612061503120c0516050a0312020c03031c0501092a024b07140f09010902121513050612070e09 60
    0x3032900d403049058000a544183c0c45504c0c6088945460001d55203080a0040d28001d45405030706206101d0362900c003501811003080390900031880c00c0300000c4c0d800e01a001d10340c00c41e61008240b1024035026117a50020b054072400210031440b00080010000b0052400c0c0001c401c5940c1e00c04550307000a04c1e00ca428122130301020080071003a26820321035030303aa400040c41100d5200c00e00010316060301c2c0c4180e0801d42604003031030385400003082440c103924141d85820480313044150100038a03a2517071040d20444101c001250084c020340d008bc8144041e44054512014410740100c4103c8040107521011a0b18900c1d4104910045c1a82e40900c400346880c00d240703000c4407030018a40303e0800c064415610400d40c0700700711100e54200301140311038a40440406051102601c1200f4968403a0866400380d413189002c0c0008541c80c1c000110440074214401d05200720003418100c50485c2e400310030b40038000217080c0c0391344600c801030f4030306001e54104001c5005004914031503a841c030b4012180d908100100c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 740121663 1250 740120413 740120417
    0x303040f0e09120304030807050912160911030411010e0d06020c0d030b011722050106080601150906050a0c1707050a050d030b18100e09030721081801110406170601 72
    0xc13040c0b0000a40101106a201d081c6181454985489000198418481100101c4e050081284041c1140001502c16041e250640f40c2400341d420f00b003000c50070600c02114050543d114203a1200c13055886045501c1a51000810a001d4040c140d220001242c0c415136405110707601c09030340d0404464150040d120422000d00b030051910b8030801518080a0300100102188004245810340c1580070b0040500c480c6c0d040740c0200841500e0301c180c90344c3c6000c01e010340912655001c04021016124048800c00d07140303956103050500010350400c0d40e40d41c00d0b07110200c0d81088076400122030303044650090f2640328011401131240f81900e0401900700005042034800b0582092080250307901c66408900003900510244503099440e20f500c030300e08000d00e41050101c1101c40d0180142c210001020f044154021460212204c845030310351400d00510702e9040000c40c04150024080710260144820040e49480c00420302d020032005120702a803141c2c1150000c94107403001202c101c024054801d60054082c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 740122913 1250 740121663 740121667
    0x1b1110050904140114040c110d030b0a08061006080c0417010c0e04050c070209190e0a17030f0c0315060c01020a08130c170f0706090501110615010c020303040f0e0912 73
    0x84017403c801c0f501025601440c0c030341c07240d00358141c8a241450140d44924064982403814a50002d010f0a18400d01a10407545500082000000403c00c02d000b070101e55040a030356450b1031410341d460718008050040842041c04009600c070002c403a14000135040000002d40c40d031a011000d8414419020385901862824003004007480c4c81c41c0c01c541040c0e030129601c800c641d80e0102e85103100004850f04d0301700182803c0281008550014048010922030303d600c51510780f1076524400a400101c0d8090b10340560f510208184603107080045401210b00b00484501072001000f24520394811000c6203c140e5001a0780094a503121410580110010050150210742521603110345029801003404000e000f034904405404200000d40010580b0425941700596a82001e000c0071503c0c8600e40c01b040110b03030b0300311800d4008101e05118036028518104a003519a004448030030310480200d8041c4410030001c2040000790f12903a00921911004c90a81c4c9407102b41075081140c01d0000000040301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 740124163 1250 740122913 740122919
    0x106030f090c051509150a020f15011a120705030702100b0d03200706020106030308060414010e06060c10050406060b0304330207301b11100509041401 66
    0x41c40502d4045590880c1c0140104040240d441c0b0715101381181e055000c05481c00800e05042c854000d802807407400d8094504c2e000001800a8a4542503102c2a01c429500e100503c0100350301219101c66203000400a4200101e142034210b0010301600c005c40800c002204116080703a0410601410040059050004007424408541c1da003060440003814080480b41d8440c10103000300076504041403030300450705c000e1350743d40c8041e00a015030302054000480d01c1d00040c0e40f1342014054048140d11041125405070328240c441e50398880301621041c0d006100300b10209802504006007411034000000016560404e0b2626804441413a440718400560920400000c03507680c01040414001d03a040440d103d150013480d130310b050701070b04100003c42c1d031000c1202c10602c05441e280100134a48007001d4000110500b0135400e03007150b032500c1c03640060800601d000f802054015940041c0f445400381c2d074207070940303040010104404aa01000042c002041040503031a0a00540c101004180c50802103541 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 740125413 1250 740124163 740124173
    0x7110f0307061403070c021801090b01050c03090d0816140601120302061906050a030b070e0f060f18030d1e031a1011010203010f0e0901020c06040f06091a0106030f09 73
    0x1001c03e40ca40070f2100040700080320540a00114400305a00410480752014520001100280203025804880d0300c5c000c0c561320154018412116200f015800171030410340c84800700701c6055051a4100d882c000148500b0004044180240c107031039200300000110b40c4210340e0968a4103205034012030f840495941c2000c007003500071a0560300201d0740d110300c000004440054901901c00e0fa070116811614060002040c001106c0758580200b07025034511203a81c0200c42042441058054a10340c0300b201081240b1412008200501c41049003112501900b4002c1001034204021400c080c004151000d80b1032021294401f0304a04041d42410100241c504a00c0d8102c1e2561307100f140580140c007081c008501c5940140e5a2214a80b0640000d643e03d40c0c4404550b06908140d00c01d880083c0b0480010030203040e01030098546183c4e0320b0009080ba542c498940b1100b0040904040d5006942c84880c1e2012034000e98100d03281d1101c070500d03c40d0f19494140024115103c050b80001c24030720b80010710000034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 740126663 1250 740125413 740125427
    0x3110414121b210d0f021902130911151209070e0606071b260307050604020402070c0e0705250f031103090a080109030813030804021c050307110f030706 67
    0x2a0a9410781c5404070082e980f101803400500000040388108520300c41c0d000d5000f44803440034070381c55003034a483c8a81d41c1602c25070041d0480c002588408d0f01420541c4004950f4400c0020500440e1220501011400440e00843d03035425241290100025100001140c0d03c144540107a13603400149030301845c0c050344440c401c10103881240306810000740707201408201034051544501e0001c003005c921350307102a20442050360109140e607080800080303102c1100e0100680d051700360070074003a10243c0c1d10b039401c0100030b5118a0b02120024900344010495815200c503c520503407042c0c4490380d031400c000481c92001c1c000003030080710010382c24040303800080c0300740c01060100d0750600344000000010b80805095014158030b40d03030492150000000c404005400c412101c1d03000e5200e28540fa100d40c1058060580141405004500610082401801c12100e091000082003100c108a814656034080c150f40c454001a1014680142d0151031450130f000d140710491812001044c11514205015200c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 740127913 1250 740126663 740126713
    0x50106080108060f06131401030c0b0c063405070b0c07051f0e19140111030c0919120c09020a27081515040506060d0902010311041412 59
    0x40c407440780c04144a0b440d102614001102006001c0c0843c000e1f0303182810764014248000e4801c0d555803800007401c4085003080b07400508000c4081c26161342d405c550030b03250304401e500c3c241a203143c1c44103152044006414030200550540c1d00c40d5a150a982408981008080d007290b02e4048200700c4200012400a00c81407110800d40281100c2c4039881c50501c01082000d050f51a240900c01801a12413200e5180112851040a50104417601d50388014200d03110a099064400e40403c0401c1c049424200500180540100048112401541d0782000030750340d6840ba5100031004044c03042003142030344640000d001c0c080c10850500b5111500100302d0039840e100161546944411652410701c81034044019081801c201e03083e40c568080a04600201241d0049400386050004c803113920709030081074003881d401000c2d00d081240c0b1140c0003005007a4002d00f24103150740c80858a80f11b00c411000703000103142d44600c1c0c07089015107006101900305006080349840e0005079142c58018262041d00707001c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 740129163 1250 740127913 740127931
    0x30203060307290307270f030b0a110a030e1e0a080c01060b040e04111207051c121701090501030203030703321801080c0d05040c0306020706020a1d090a020d02040906030b0103020405010608010806 86
    0x49c646920034a88000c200030300c660540500005244241e26806410002e909807181e0200c0d00d200118a8424108401940030020690442820711000c500a480944038000440000082d8071340d5610200411350301540c0407004c440c90490800061280c2520b0035943d001081e54040219410302c80d50b207886d80140d0050502c207a04880302401c1e40341c00310744190b2000e0b900c40d00d564040d0664850180000003d5440c1c0421083d40500202d20410b8034020203040320350140003107040031034942d4290341e020582c903551500f40041d00d1000b000e24152000f40c1c801e5511003101030380e444804042c40001c0c2d4006441c510306100046051203452103040c01241c100303508038200050b4a498614014001040750360020703003a1800071036100c00f4032502e40d00420b80c14078030340c036642c01c00010308a04400354072241050982c416204000175485c209690010045103c0b81100185055140c0b00c3c600b00f12005a00b054408038817210041c0b08608141c4542e502600e4103040503509985014000e0340d40d00002049540 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 740130413 1250 740129163 740129183
    0x2d0d08070212030415061a0901080a0b190504060f05090406090201020c0a0902031f03020d02040c200a0c05060415050901090e04060504020f01030203060307290307270f03 75
    0x140c0d25100380240c014200c07034001c2e80c40e40c9041c00e0078501800b00802041d10307801881c10790006030480c0460780c080f4000340624161410554a1070064416040050988040a441d40e8098007aaa20076240c02c3e050500101400310f01800c06041c44201c8540b9080742480070000342d81030000c5d940b004801c940c0241c0c00034000c2001c01c92480102c0c00c160100788000c1e04162040300100710f511a82c0c02441c840c660300069a40c0340a81001c0c07290b8600401d11010307400401d0f00c50144c01504290f0400300c10700301681032904c0500d001300c003035110001e00c0102c0000680c10248110042050101b0140028078003212203074100350910b114941404861702564045c482d001900404a900416241d030040c44c0d128903038800740c505420100e000d442d040b0340c201d104a801e510050302030340c000d200703990107503030060020082c00b418401c45028a44000500050303c0a0aa06100c040341c08507008500c180f450707558007140a551a03410000440100c01002c2c440203a14a050020314041d40a0104880d000a40e403c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 740131663 1250 740130413 740130421
    0x50a050d080c030318010c050a2a0506090d09091a0d1103070b1b070b04140a09050c0a1d0d03030203070c171309061206050402061b2d0d08 61
    0xc001c0d2181011126081c0404400c2000c0085400300b03008007080b42d40002d10454841c110200d504d031242d0100c2c03d02049002540b2051a612907019586400a402d032804441c2044e440d010b262131401c480c2070032560300141401d40d0403039219840c0401001c542400b80504021f5059500c3d03d620b00c66074030350050159a803c1d005004038031038008040c0740b002e41521411515524030469980c0180130b8100d24a64112148031003000005c0d140c000c542c160007139281010b017402041d01403124150045940021940b40c0440d1050642c454540114101c005150380c981d840b250160658087c100001c040702c460840c00c18080d01c0781c0c40d10007007840c0d0518005a80c2c5d90b64400684900d42c40c80c07400f5092044910f4101050440003005080ca40d21100d840c5104a5480104000340d64250040ca4590b8003110f444d440020324a400003500302c2c0c80213241c90b04000c040400440c03400e4034280036a0b005ea0007100c2d510078502c288001c1c4110320b0035030520824070459903403205560f003021014103010015500001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 740132913 1250 740131663 740131673
    0xc0706110d06151e0804121101021b0d0f0e011b08130e011e0e0405011e0b091302210c060a110f030705070902090a0b04060309030216050a050d 63
    0x503a00741d00340e5981040322584520614402d601400c00260100301091050900c48079031100108458045580300040c1d6500e5940720924101130103140c00500600c054201010103007800901101703202030324000410201400300c0c03850408488501000e0015000811442d60341c0640201440002030910407400402001020311498014201078040000440e42c1403030700000389196012600741c40700850941c0d80300c4511501d50302e040c1195501002c08c41c0020055641801650b075800b41c054000000d4001341042031141c9d209060800d204220b075503154040d1180340c5460015004080307524400360b102c0302d91b80803524092004406842500c1030141d802c085140801c0000c500650203403006454441c07000010303220310030141c407a960600400e035036660b2801d800001e031034400390094018290300d482e2562007402036201c148600c0c1c1060010714040760000b01e43c070003000202038503503000030b11340d07104d060082c00e00521500844c0024801c1504200c2503441c101c21001340c580444011039141c40610304 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 740134163 1250 740132913 740132917
    0x11010f0206010306112802060a0b0a03030c05010e01110c100612151b0c031403040506041401021611180105063a0c0f02010e07170307022d06030c070611 67
    0x40500c6c038580450100410303504061600180c119160201c9000780ca4500c20181500d10b2101001d4004034003032400c00210b88140002c08009001e2000040c2408640c1e1029003540c0c3d083c0d12013007403401c0008408142046c02c02004509200e6107104205041c18041c000c0349800d2103031005400c56070806007039208000c20303a01034420012002c1d41d81c11024100c1c403029007130345c031001419400300d03101d40c0d2229910b22150080b00d2007194428007509840d9240e913200010b03070310101c181c00600d41d800c0c003081c04004e54030042c1c9903406000b061040312a640c60010040b400c4410b01300f58080103001001040241c07541070540f204400c03084d808410f07003110040e000c00740d444440c0d0407010030001040c409200004603840242e041c81c00742c0d5950380585250740c043c2c0c20b94415650b00e002607442160304010707000e030500c09001c41070700007001c5d030349401c40c56000500300c0c5841130601c0b010440782e1030f400e90441060982a10402c2c000340e400d41e04518180911010354003131020702401c0581c880e108000150f0303081301 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 740135413 1250 740134163 740134177
    0x809070b0d14100504290105030907030b010b04090f09050c04020309031303150b011b060c0c1401061509060914120604050a05120304110f01050f1611010f020601030611 74
    0x2c8600031914200100c85083c007802d12845008070f01d4501e04020440718259521301c442418101188400c01403001124160f00080c8909024098090702000054546a03000e00816a00d024581c41d5406d054202d022100d01c0c400c13040710a4640500c807000541d02186400d064941124010f0b00c0e81d54405804d8154800c02080014001c40000c0110401c80311115200c001080c007034081090100c1c2ca8015241c40d2b100c01420b4240d0782d09081c40d4400201c03c0d4124403540400c0e4038040015054507500d0b81c42a522180c214015a51158428007150f03020030040c9214802e18900001094580180500681010f000d42c15840001085803a07458503070150000d10350300381a040760443d10301070034080e4690f001210304460324014000358075491003403d802e0301d00882c0c1003a12880720b90340c01030030003040400c8828101d050001c24040c0040b440403001c06450780c50414807004428907464609922500040c000d40303418484048031030f0300c030943d0001d019030541c3d038080000510132041c000c01c11140c0c0100d070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 740136663 1250 740135413 740135441
    0x804050f0f071d060105220b0a05030403020c0604050a030b0a02070c0f18090209060607061118091003030f110309090c04090515030c100905030106140a060809070b0d 73
    0x14180249441c8005002030480d0f121a003c0018816405021034204205891050000d0828480020240d2141c86110140985c800081001980d16a205d0307400d41c00000d080b40114202004100925405000c80c0301048000c54460b864030b81410009840d001c0d07a40400b4215002c840b001841041c8183d0481c2da0f05038001380d40400072603803240d50f419010310340e0080b04041600c1e103a840d8002078aa003d0114219401000801690340c0c5500703014298000c07040c10740307401d9103440e50400e4904024006020916030741d1007501d00703264108240044000041c2ca140e040382c5403000b042001c25803040c0c421103006400d150180c40000544141451405908517041c1d00c52440010b021340b0740f02080c0140200c0d907015905120661341e849003ca0004c450101c0300d9056000076150070806e2410411a030700b80556402c00d01485034440b00403900311207480d041504481038500a0810914140407140000c100c94645110a85040301481c0e03283c031100d2140d89072016001c18400c4800041c0d4002d00003141d01c0c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 740137913 1250 740136663 740136673
    0x10201090c080a030908190803060303070f050d030b061315050c0610050f0118090c0504090f23040c1208190315051903021309020618040b040c0c030804050f 69
    0x80c1c0b441035200c903040d41d02103011a40da400c00094018011540c8001491420386040c000c81070743d00c880805c1e9100810b61685030200300700c40c10000d00359020442100c0d0203030300109240c2003c2000134046a8000e02d05602c510720a200c111b40c60400031124005540081e10b0700266412241c0c42912140100c51900304280200d80030804a006c1051214080700c40031900c1c80c0400c01001c005440d40e4101c08501c258800d012042800000c2c02d540001071f082240b07181030352810f175550038410121400c1c4011860b0070f98694506140420080c1013640503c988001110a6800d00740d840303c0002032180718a03c100500000307501d0038031003800256920040300c07250300c910f04858048002d0040c507103442c1603e04502082404246401e2800b504658a40524880c034116403d540810400703040c61901040d4070780d1100e2292005888203c0a00741c0c0c401c07501140e0b01c202110608000541c0c410820380d501445c6081a44a00503611a640000454160400c4100d540701d80c10440e0900c8034045201e5010300c40d03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 740139163 1250 740137913 740137919
    0xb012102030321100605030f150a080102031b040e011a0d020403050a0b0c0f1206030703020a030f15141503010b041b031a220e0d090503011d030a030209010201090c 72
    0x4815039240303400407960030085480e9a20300f4490b0880303009000d501700140041c0001780303000c0d00380c07042c02d50815155051110b60b141c1c1d900028100301001d800105460350040103024003601c400e120380c0300000d84c0800300b5003060304090240c80c001905201e40b881140c00c11440c0c51124410b54204e50003c1030154040d03580d50745900380a543c400340d0420032207060503801d000640b03180807082076407504825050300c0c2d032401a103000e003600303c0b01703001d801719500d0302032482c00100680c0c4401d10f000055201d540305504084050034060050302107a00d000441c1820a00c500c9455141c00c40c1c2250710841d01000c0120f0100d030304000c00d0062038041c82c07454102d89424551120801d155480d00d404160780d6406105070702c2c0340d4030300c40c0b4402c0001c403c581d0032034405010070101c20002545e0080d015030000000030310341101c0e03101c40c0c07810641540b403001041142d03c0c14421801e080c098403100300709100385220105800c0300640c3d62071184680c61010140c2c0410702d00c0391130307100390071403194141c1000000c003150791 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 740140413 1250 740139163 740139187
    0x2b15030804080c0102060405060a0b0307150e0310020901170a090204090b150105070f03050a0512012705270c030703050c0f0907020d080406240905130b0121020303 72
    0xc002d00802200d40300d006042c240540c030000d491417180350b20401412103a1680e4002e54086e24041070301503810b0160341f00c04a20806400040d00c0300840707599954144100b80d006150514044002e01c1c02824010042c51440e6600504c4541020400f4400c3e0411a510700d1a61001043c1d40c000081d8000d0500c00240706102813001e80310300640c904000044a80700d4140191210701c00c0c03a0006003a500c101100902183c001c001070041800b81c2c3c02c0c44c0341f4000186206130502c1000741c00c0945250040e001d04c01c1071300001001503079461503400d4200924108040c8840400b0020104d1504500c4c281080c80c04005040c4290541141e014088a100c280c491410503200c01d450028540101d14620021010340b5040c0843e5009408a8002e003034101c648080882d81c5100003031043d590161180c0c0c200c0c01504140b82c8000e800700c0c00050382c03001941004248400c1e100f0141004618007003440d049000314000702c00e400d0444203a41403464001c02d40404285000c2d80c0c048019625020218603002c410b9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 740141663 1250 740140413 740140417
    0x80a03090303050a090506040f020402070b13050633030102040b04030501060e06060f04030f03020102040e040305030405010c08060f0402090f0315041101091413111303050606062b150308 82
    0x1070701ca51014041c0d0390300e0071009405c940903040003800550041011a000c902c0324401400071030b001400240c60404a5201c4405400301a240800070703e078a001000103000b41031101c10341011480d204038208841d440c1c03003507104415110380003440c40d041034068541503030250b04440c001c12100601c0341e100c40d07807814072038001c0c8246c2c82014841d40c0142c1c0066100c1c0b510750101d80c3d4034a01412054202030642d0cda620b500c101045040b03007950b60170400481c00e04a1950983e00c501c1c030913915281e580c80c043c64a6800d40f00340a502c4000d00000c0030910419549022203900380b200c0c1070700e0051b100d846c2d10000a58a10440c0c6910345c0600a20442144011404004520590081000e03c2034000040011a1f00c52402e11488503040700d12141d0200502e0003504041504c0e0b14043d0200f610f2200e030700c0800241c0c0c03080e142c0141090303030110100208001444160b0b44600200c56a07410b103584400301466520f50820b07052884644c0847c1401d210034650721000c0c0b4800500f10341524035840b0b1078414100c3d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 740142913 1250 740141663 740141681
    0x1d100b091f08100c09211e0b040f140708060c2206020a120e0a0501200615010e01020f150717090a0c051c02040e0f060c0a030b0d0f030e0a03080a03 65
    0x140780c000003207074003113150311054492900040c080300d980b4004e0325107442c1c0303001c0e0309404130809410440000200700c900c24824089d81c00380501241e50106807410610150420f0901012034100780e41c100100f80000c83c2d40342d33101c9840d41400ba641c40e83e21010b6809a88010340e102c403c40307001c900100e1031541c00104007000b903106802c81c26145251a409481c01140035688603404501d220041c0400c0d403065040f20000b804e001c0403a0340c2100016402414440c3c05c80d69450001010340100038290f90041104c070f0499400e00140070750841201000362034034041003451072102e800e50302044100744140300c20903c44488040c5190141020003071240c554840c4a13040c0c41101e070003000818a494000d210002820005611803c07417051a424007001c1c110402c07403038031507001c2da115101044006112030303841000c0f105080c4d9544c1c00c0c0341601038111440d10b00311074014101c0342182800503903a000d80495140c0c050504005120650002848100c03107508020040840400c1300d40d545500350300001c0d01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 740144163 1250 740142913 740142917
    0xd081c0207110a050306040b0703150324150b0304080f0705070305070501030f06060c20100c021c0201020d0e04060308040e181f0207080d1d100b091f08100c 69
    0x506541c4008040d074078141510042c8c0b49075402c401107107229010341d20820709010760311107800f88141d2300d4840035003646a402c400440c3e040300007030340c40c0d048c801c41c4180c081c2c40012001454503c0d0030700c000d81016004c001d0005014940000c0d00d18502c69400c3c0590321810b41c00401c03200d02c40d03103c4c6021a1030300404c1c030a0b540401d00b01703200c0551b140c5c1c00d0b0080d030301a1542c554408070380da121034845982d80c550210a540000300c01c8d9928184036219200311000d10402616001c0700c2010078414012071056100c0040400c1541401000040c0c1e40030405980142142c6000c00c19400c08a0000d4010320300ca900040c225140044e0004100c6110041c1c28810042d180c0043c15442e07201c440c60340c5908584072003540c034441100f4603114110f410382c0a018080e018040712400c2c88400103020048070403501b0510000002e40180d00b801910410206e001c40030903060074000203400b100466000303440a0101c00c4680118041d00303100000708203801000f80182421159100200210391005200103055400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 740145413 1250 740144163 740144179
    0x40e13050609010623010324080f01150b030c120a09060e0c03062707240e0934050c160317090a090608060708150d081c020711 56
    0x204009044c0700340c8003101c4901100e10503008043d26050310a420450890303052550302ca101c00302031258001c000203d07050414034503a10608041c40180707002d9507c044440542e0405a61910a041061600e8100d484e003103001c035180d4a510406c0d244500a80c50b0904441c8400c0080100c100b4880d0051010507005000812040303041000003910f564400c041030b13402da44582d01040401840c20140c0100c02c000c40200c201103002020098100603c1d41d0006815103a214007015052040d40003c03001d01c00c480c10701c0c2c100d844954001c03034118a0001c0000d00030020b079200390803540720090015030740c01c1c510b146155100c0281600142803a040501e40c114507200f043c1c0340341c014054441c01c400549811502200c000e100304000d034403196002d900701a410003105040016000c25034020900a0600c88014200c0c0e0301d80701c080144a0140140804243c1c2e00e154080442c54a0709400c104410744c014600ca5078498495001d0789c00310742d02001180559100044180900105200c4000b505e601214214 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 740146663 1250 740145413 740145421
    0x90f02030105130e0c0910080a1b06021504022b060921022a060f030703201903020f120114010c080a030e070504110a0801150c03050f040e130506 64
    0x1007110303013035040030000383d00000764913100c1c2c68620f4005a00c22a41240e50000b80d4464050904003002e020007151010301000411804107241d4050303d02400c014130060215043c0185014880c200190000c0e0068041c003154410001081e111558122045049540700c2e402502e80b070340040200d00740544014188850002034058130f448401d07880c00c01030b40244107800040b420741031040800000c800d00c1c0541100d01e0301440d00c1e0400941051020350281c0ca8491803e00000380c02d841c101c45103c4100c0140c00400c0c040c4071100d070150b40c2c14041e00740d11007580ea440110705030001e1060348011408003070b01280c14402000d410f5460350503191008011480e40c0a01001907070018005540280303551020b00101c55000c0c880e50041e40d0900810080b150f140ba500c10205007152075409000120260010b1460640ca410419080c01403d441c046402c1440c1c000760010102e011a05c001001c0000008a0b00c00441aa2082e40c020700009121000d150402c4c0000186040c41c02c0411645401210005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 740147913 1250 740146663 740146699
    0x5090a050603091222150806040504030503012718060e1b0904210c020915130b040f020c030306130b0a050603090109050f0d0e0a0b0a050f04090f02030105 68
    0xa64080d80c3c11200901c450710f00103551445582100b03408800c1c81803012402c00320700c4083c003400700040c5014010981c3c0180707111401000ca80001303003818000c90614061100080c1d0000469046502d8550b240032000c042100d040c41410700039010a03506030405d011800002c111443d0600c1151103020200300c1c4c024880030311782d21580c0c6070b40e40069060314807500351310710b00302110b81c26070082c46041c0d4141207106042c040c22580c0001001c030350020780ca1415480c11400c100c1203140e00030183d4161424400c0c400c50000700ca03d031078400c10f511f44544900540005072500e40000c0409080c43c0350039500c4843d101e90023996a081120510b100300b05e60240d50302d800b106413041e00e184400141c10104140c2c180b4051180e6a440a420504503650701c0c2120004250140b05112600d20350102030714142d00c0f1114020108000c0c2c01045204680e400010000b03000f0712022034482c03800380d080c40382d00c1d0000400c0c8800a0701031640f0429009080500890401c0d02c075a0045060341d030110740d260784401140c4c0b61 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 740149163 1250 740147913 740147917
    0xd020a021014010612060f05010e03120a030203010f061e0e0d1a0403020127032a05013c090f0c0315050c0703051c0608010204030602180102010e07140310050705090a0506 75
    0x200000341c10700020234000d80d4465132100e4040d05014003202c1c0c00b601c220880103950b03400171815a0000c0d5022005103c15543d6441d1200141414508852450284500ca910266200b925602482034100d110002ea407194070400a115030055501c01c40b01410781900158088111412401940782102c03005441c420723407201c0303510707241c0c1d0208040407624a654103441d01c8580c4800c41140000c1d079500d84d400006141500c80001d44a80004107a400c1c1840b07583c1140a005d144841600000801c4014207011002c9090102c1d81050008506a01a420183c150300000354015000d502c1c2e072000801884000c60010b415414100f90412065881803400c940ca0700483c10020002002040000504030b0900c0281c458462041c0c1e001694982e5180520308a9019900841e0802d8000c504e2411510320304041e00000742080c0003d01c8403a010149154561246000ba08003140c0c0e902081401d588042111030107240b10b40d10200144d00348a00c0c0540b80d44c000808042c4114092100031a441c204241 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 740150413 1250 740149163 740149169
    0x120d0c0b1003050d031a06030702150105150f070c0e090d11060c03010b0c0115060c15060e0402100c0b010e151e06160602030705071a0106050d020a02101401061206 72
    0x28204c0300d02200001c80c0540820361400c07042525074518504d00d540c0d82c1c40107501554058004281c80c0b2840240c0c2c2c42c071600142d215034805c40180e4248200c4d82c8050044075420369000031419582c52561400c48048001074102d00c80403480c0c00c0800070101c400056804800c64240c80784600043d65403c005e94460045420b003460b0001400104848580e07680580441d0003110004168140c51030341907500c40d8003607444000050070042d0300c3c00c18080480c608080003c0190b40c2032000c50f0510502003d20800076200a00400342800c1c0041e4403842103100303191560b0f0005205605d941e49020402c0898019920300f03c034980042c0600010340b50140ca403e40680600c030100c844691348000300841034111b6420258010b21010004000400304c1c4010740c440c00440c1c0b181d903240d52290402d8924081c030203061614803c8510014805540c001050364030500c10134401607030324440807070b080f4145203400111010b400e04103520590b140b03180001071344c162506690340701d40c8203103c90482c00507a240c81c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 740151663 1250 740150413 740150423
    0x30103170708090f0418121b052e09061e050f0106030b01050c070b04060311070503040506130909110111010b0d080c011b11070909080a0e120d0c0b1003 67
    0xc030f058642d0078460070100c0a035000600001d0201e21101e100c500b0700c1006082250303402d6025056000250700241c17080c60f84602d171082078108800c02d9132059569004103844140f020034516019510908e00115542ca54a001c0742c14000520302d854202d02601c0481141003286854444000c019621071080c00d00c190710508003510140d28149094004001c1d80c4502810020104600146442c08026a400921440c10308607074540c40c01800804464241002d40d891010812628011800000039107040e42c80c203c443c035503110031000415284221550000c503070071741040c1b40d903820301c490b108001e81642000e888403803a4108a854a50032246562541980100d0607500e21011a1410300076000c806045000080c030214442c0240202c405104807440004a1440d210700100d2803e0000302c0040c50311840c140980c41c0c1ca691105403a010381203000007040403290000c000c0b42e984020304021110402c09642480011304030042c51028145000e0303903c07074402d0000c16401000d4280c4a41140c0c1c0003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 740152913 1250 740151663 740151667
    0x5010605090f0d02030106050301140a060512030d0209010c12050a02060f0907090e0a0b090f070803040f090f110f0d05180a0b130203071511060615090310050705030103170708 77
    0x50b40c2040403000035a64140c0c0c0640d03807104d0210780f5407400d12078a26212105c03407102a0a250805850023681d2998002900901c5049107100b1f00701800000da0b4a015410315000d07880b03100020049400e0808110050700901204049000598014000304005021582503d0050b594030800a040100648a40c0c0159004400400c034141c00e130b60001d10f800503c103040c0c1300740c8a40e64a4112072002c00352427140c10354108045030418441e080100384c0c010403641c0040c41c105480c180c50036030060400d2144e801d2803511802c000c90348640503400500c4010201d080f5644811001d50411038a800c40c645a00165140030b0100b03000d8484034001c5002d803211003000b030010046564410b48000c1000d8003030342040514102820069400317100040150486919401e0f0303c00d12040700500f03901c142042c0803100d8200400b070141e55100e0b0750340840b10701a00c20280740e0b80c0044c200801c4c680440300b2244003505d4a08424004607681c4000154100c034010a0f41e11203041d40c5070002d000610410344005c0400c1e8007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 740154163 1250 740152913 740152939
    0xb03070e0f130c030216080c0f19110d02030d090807060c050309040c12020301090507030f0509072106021204060c02030a0e091e04050c040e0a0305040e04171306030501060509 77
    0x2c1030700145105022480e0250521044031040014001d141400b1620751703001045007503c0c2d1108000380d00b450f809010080c910294003070031816034800000405010108283c0004240303445400382480e4669000d0110750540207101c80050445805005d41d071032601801c1070000f0301e24032402001b64401d800c80302441c030301100041040014145031105d41c06020712100402200c840368030285000302040d200114492400120080484045103040c1980a1601c0e0501030340c620300140c4030050720811079100203171a901030000070700c04c1841c0d880200b0707160000580440d100405014540141d101d10b0f4144103940348414181d8030f9008045801c3d0004007005010030151420203c070a800a00e0301c1c914041e0083c200300c0000384000b0031035043d030f245d601070720390542d00b41040e10407002695040406803640404130307039005002e40310710302c91031506440917008902400407012001da030020080c4441a0784560400081080c00704500c5003401103881e041c000502907000364212104003900820741c1928203030b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 740155413 1250 740154163 740154199
    0xe0c0a050d151203050406020d03020304050d11010b03030714071205060c070f0b04030e01090e0106210b0a060206011502160b160b0a0e0f0f0604020d0614010b03070e0f 74
    0x1103544101e0050b080692400118001d4030050300c3e83c800e0103907032019a102d0804d000a4545110708510034101841003042002041f00826800e24400c0c1e1403400c022030202d0886054050040f5410b5181e00d400005a03a50410070b051088003640308001c01920f9040d9a039109904800556a5000e41140c1044000580180c0703844010322019100d80103115118130640c45030280f948c411a001c401040036140d00151660b000a4050000e081c003405041142d810310200408081290920317580e003045080c1d020042140c0740d084281503080c0a000b805030103650b403200a42d206000e100304103070564242c0700305180d1403021903504540ca845012003a4114a09050ba40f225440b01068101c032100d5100614009030032811503038000d5031440350100d458500b84400390b0601c01c0b02e42c401d40c01940510070069200001080c8142e00c01d8045a1940078170666041c1305e4090702c80c00d80e00b00480300c0381900101b40c20031400051406042550380b00003a602d0014103001000d083c10000726800a5411201030042da = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 740156663 1250 740155413 740155421
    0xf1d010608250e2103090f01110102070c030212010c08270106080105090d08010503060721020d090c0e13350901020609061b07020103060e100e0c0a050d 67
    0x101541c1d0082100300d4444040507010440110a040007504540030005149003904000240d4146441084061102d20907400d58070321031b44d503600e0301400303483d070a405150f80281200e00301404100001c0d581c840ea9071a0040304080d840c0000ca210310100ba2500f034006005102d0007601c01c04e181c0300c030700c80d07503c803491500506107130300d041001103001044040382c00c0c400c203005010082ca03c00c0004281030500b28829070400c0301468a0408000114004001960700040d841c2e41010b49420301a081c0620301e2607000c0c00100214254502078000204600e07520241e0340300f030507684d02411203401140e071190741001808106441302d04004610916170400b240c011002d00e41c8034a98008aa41503d903a200c10724111000c48031140b01590740807540c0380399035806114499105103000c02902c0b01b860402c18070004150740c40c0c1001aa404049080350842e40254400000340c442c800380001d06180511034914003071001d010380c6040754103000200d031038110400d069400c64000c40c2c03100c4e4180305001007104010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 740157913 1250 740156663 740156671
    0x73c03150525110708010e060c031312080601081b09100203130314070902040b0406050c01090602120a0f06140f0415081b010206060109031b0b0d02040f1d010608 71
    0x1546800610300d06074080b00c207040c0c4082246440d545401c030001c4180314146400b541c445602641464000d81c090140822402d074000c2e00d0740d00040e2680c90300c041012200d0603a010007072a602c5070760701000403250040c0780300d80f02c2d4800740d850075615501c00102d100364038000701c4424100001072080f04e01d0703850030160b4801e00800c0e40c13045a04069080007800300700f000c00c0d4809c0c3c1e01c207a500b040c01040d200c014040100601003409040d0300d010f142184000041c45944680310803c000840c0c1c1072040c034002c0d004a60540c2d0010009e541340e54089003103010800c1d05549418042d4075000104401c0e110f81e015203012149800c8107058441a080140400255220030003603000b035451b001c4030901c2d450706000001a006450040c07040b245201c2a040e004981c0403902415580103901700b10103030f03070b004400d40d056070703801040c49902038502c448150005005030414003541001282c00d40401c070340b84d4040c000300d50000341c18902240d42d400ea0a903180e1805a201c15031401d6410043c040540901050785d00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 740159163 1250 740157913 740157931
    0x15060504091d100b0112020a020c01050c07090c03020901020f061519050a140907021c140c060118060b090916121e05010b0a08040311073c031505 64
    0x2005509508043c1032401c00001060b04503070704e041480582d64048540300340c80403003800442c5408404440a9914450640d18604110000a401c22040700070300005000b40241034062048100d113a4001d0302a4200e440c0c058014407030410010055103002650601130304042c5614113900f19420280500705104820440c101448404002510344070030204000600c294041c8030700c043c084008014140401604600855001e00383c402c14a600e50030007006005801d0078800c1098080c040032481501034040c2c20782250080b6000001c04046901c041131420324541c60420103540c0f68202810305010f8182c8558104803140c1c0028050300000019264130300407410011900c1c08811603c00070383e4031000f035a510f4a640450080d5030402c050041c2c074003500c0c10714a16800c08502001c003e181120040c805030401200e550a640d5200c4140800005480d401122101034542040511101d0104ca0301944046880e41020b8000395620034030350b801c0d03c0e404242c107001c03040032460040c0900406009801 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 740160413 1250 740159163 740159201
    0x103021b03030411030312011509031a0a0e0f0c061b0628050105092e1e14010903060f06170604020f010302180108180607121506050409 60
    0x3590320038112095100c00e00c940003140c2d240341c1807818080300d85608560900a40c418414200d50600105207181901e400086186c15807101c0c2c5030440300c40546600c043c2004030b162900b080780c001c17002c0b0380030304c1004a4174007403003001d0030f011116548d20040c00b000312203a00415140500c03444c005004000c40081e0741500e9248060340c09116041003016242c10320340f84a01004451154001d103180e031001c5204003020801d0758500004074443c0d1000810415680c200400c2d082c007130b484000c0d084c415668900e491030707040a8a640c400c542d14000e441d80e40c80004910000021220b20b0310413080d180030010f94404c000e142c07540d80c4003000b40540e640440300b40c54407030301302059020b150341480c2914140c02006018600f800d005200e10f012481050904040c010481900c3c8412020b00755683e0113000e00e0203040e15518407a1030b90303005074801802c40b00c0380650000d00c0b9020b54001c19403038503108a07038400c1081d03411041d01008040e82d00d11880c000700d00180410400301d4050780c04a100c00c200c08452003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 740161663 1250 740160413 740160427
    0x1205031e1b0310090c05071403071e1703090f0106090c0519020f03131401080c040b070807140f19020904080a0c0606080102040603060f05030c060a1103070b0412050a09090506010302 80
    0x1301030312101507a000000340041020380034060361880001c0308010041c00383d072070b0107982d0300c0b4440c01030510030310090100700b00381c3d8440401001c4c001140b01030751100c503100d0310303401c0440d5083d84545800030404001e6080c500c010076000074a215460080b08c00e51244d521b0940351851200f090042e5240f040158000c07408280d03203568080c8001c0100d0500c41c020040080e00700064a880810407880081c104241c1104100d0042000000c0b42c054440e2340800c01d813208200c1c54901d48500c04c03040010560400301c000c1d004a10000103004904550f0081900d442c220300841c108807260000700041d50040c90303c00481c002c2030240005003090085483d1840a8002c1c540b540310683e003943d4051801698009020000c155052050718042c2606000c1d510000d481c05000940c0c50401002d054860301c40018041d01361030055501170000100d807130076203403550198140b9400c00101100e064480e03c14007109480001e2007030701203550001d00d40c0c9504080c141003030394880040800418050626608209070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 740162913 1250 740161663 740161679
    0x409030507060c050a09080105071d030a0f0c0314120708030a09021c0b0604020406020a151508070e01140306040b04140313050f0a0e040f020402071205031e1b0310 72
    0x3001185444d5203940d0071041d00c000307003d0b0f080e80d8072110190f4500018005041d0f40b190080002144002c0001c205d02c0c03010300042e05081030040c004040303068141c0c1000c03c01003004400340c22280a001d0261180007458900c54680c17070910000701c00c41d001045800c0000e03034044090740d00103407001c0c4000f550303580075804609040d074442c19040c1702e13030701d20142201000441c102c000e500000c10340d815420301e460810080c1d69406c0b9003d005180b652900d05140d10302d48103034001c4a10001d5078800f41c91195503807002a403100342d10300619180d190440000700c1e11030020014100400000f5004003220368581e01c1d403010051000e0b100320740d403480200f4060380039141000a4050007440420004045192208004c402c0a583d54511b0042c00707004d80401c65000003100e015030054000300141c6a100c8248001402841244d4008151011800300751583d540e02070095803240c4541184410010205001c1c08840642120610b030705132a1411410755985014000e03580040000030344280e0207482d0545 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 740164163 1250 740162913 740162921
    0x120309010b04020706020d1505030703021e0312070302010c0212161104020f0c011a01021f0b03010f050105100c020a0603020a050f0313031b0c120305090916110c0609040903050706 79
    0x4162034403900890982c8000c80c040c4290440040302346541d42100340b9140100741c503a407071880043d20488070400850300c520600402204071800c01000d403101c031003107491b0071842c03508412411f40040d868464411341050001039000c00300c45c0d01d0843c060404c00314510340ba640030b90007081110080800b1042c0202074580740040d01700d80c4408103040e520761044010141c21143d03080c2e144034a00390500161b81a998001c01c0200e40054040c2500241c50b40981700c0c41e000e0b09103802c0e4107426610344000070584d8012640106d058403c100c0b80418820f540320400c03120100f03110006035200c28040d07010051903010394010001c0e2612810094141154007801051642007283e5506c1046c13403c407040c00800d6403010f0f508000d00382d000c07103c5162411b40e444018400c0124041d11002114050749001031501407025110140d00080440b980380c64440003144448a05040c140c2c082846c0300c68030450140c000c2072f06522031a0142c441800c1410041c1040041c1021800907001d000c2d00704240c10100d00e440c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 740165413 1250 740164163 740164177
    0x2a0d1506060e0f0a0b0a180e01030b0a0e030702031b2103040303020601050105070c1a070501092003010c0e04090c080604050a120305040302060f040309080304062609120309010b0402 80
    0x444410b5000c0e0704081c40110450010030500c24828043e045c403d400c540c5080d60002c04031131604110004404d103c804480b40c16070042904a101c0100000401400b001d0b11845200079201c140b0031500c0c0c44000541e00d0082c1d50000758581c100000035600d14416040a4500d03c60090151b500d508a0325040300c1a880d035442c1d02a503030f0304001401d1041c140c0401540d4010314081c41c10310300d03100c0d43c1e8590114191007405007203c0c82c403186492071101800c110903a01120f41040082045039014504104002c0b100c0081001c00c4c02481c0c011031692070b06100310103142040703460b0500303100014401c1100a1030104c0044548890615004c1066003040113031510691003080284070b90a424148903000b00002074020007050304003410000000d03408103031a034218003810302801150300e952800780c0c0c907481c00360001841071102140020380c0a60000c00c071900d04000b0802e0244205001e003e070404600f08031248011544142d13501300019030158000c60340314a450000244400b060740000381030f0383c0214 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 740166663 1250 740165413 740165417
    0x50702071a13060206010f1211100302070b010b19110f0a0309062705060315060313170304050c1201060902040f061d1c0204020d09050a052a0d150606 66
    0x450020b411858001c5444040c1000d40010301c4990f151100716000500d050051420f581c0e101b490007800c1114061006010304001000b80c464588140c0008000b50000352065070188400000041d56201c0c00c0216151684071100812440c0c00300740d802d0321140380070412452144100e0045806420061244800c424420f940d0916591f04d0040f00070b0100c03402034010403034052036105400705100c8030b1800c441290b40a441d4141c032943c4141c262079401130904c5095400c10070010800680c0c5025040c07800c4681d01c1190030a082420b5980744010a010444000300150302106c407c10b56894840d00440381d1510400000c40c0054840390941c0c141d81244c3d1000c890b03a03500c01710900c80386800c034140b5059856030710030b101814011030380013030611001c0440084030030080d0540b081c1551607540440d034407054009024010741030f092130301c9079a401c04514103a50a008029806141d03016882010b0202d1036100301541d5490b80030000c0054080400000300d0f428840300c1c1000303100b0340460050000034400d80d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 740167913 1250 740166663 740166667
    0x506010f0e0132040614030105060a0e010e0d151a0603012706140a05010309020109060503100e180d02060f0408030a0f0e010506040b0a03021c1109091f050f0703050702071a 76
    0x1280015281c07621500514181c80c5051006008a031038400c150760781d070000ce140004ca400780c40001682c110100c00500342d0421056002002400603a8042403240c075007000e400c0095848131805194402040340c40150b01080400040160100b0021221080031040904500001c408000b86080740c40e15440070203440300754107a1020500c0c10b2200500102401c1c02d06005c032000c540d0008003840111b028005c14000040b0114000341d10b84d080b00304c0580340101e2546920b00b04440040300e07501c549800203846226889800401074804141103006440f410142d2405455a40d038041003904003d240760343c0e0b07035039801e44161002e40a01400f040034030a42d00004003810040b05102c2941c50501006001d5a8240010001621007140590b04e80e8444d10110401d40c005142841c18120445800c651254508082c8a0107a4002c0b843d1582e8410200c101400d02c142c001a090699a0407030b01c05204c89060303800a01c015010b600f080358824081c2c4160b0740140e0b02c845072914007982c04440c101c044440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 740169163 1250 740167913 740167919
    0x903160305012703080901020d09140c060f070807031209060902030c01020d050a030906090611030f061c06021308160305070806060303030c2b020d0506010f0e013204 73
    0x403e102c0c5003070610140c040c6421505805150420050940300002c04001c42c460000e8440b450a6042d0741e07a20100c40d101303100401c80c504181c0034017421031844c0341c600d00554481221900d00401203401e45001403031160304026141d11401c0180c0c0000c0c10079424008207074110800d03d126403207500250741c82005e0007e9a80c500340181464541c010081d203056500007020003001c250040140c0c0d442c0b0b02c451030045400451460031001400410400401c52400c10b00c1c50f41c0300040354006940f041030894105421552294100040050802000214084007040710800b05106800034090540341c0e90750551005d640346c442910700140400c2031440040a1281401048405e00c403031401002804000c00d02410590300086e00c82c0300c081d09031502401c0c0040c0d40e01800f84017000107008481d5441d020b06503800d0d90501c10000e0342c04407124803001444c110004000c0e6000d803011510705c0c0080d54880301d501404900546280743c0c4482400040141140341c00c2800c1c107151515200d1000758a10540ca442c6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 740170413 1250 740169163 740169173
    0x3070305072c011d070305070905040e0f01050f07080702010204120327091d03030f0f1807060305222a030c150e030607230904020c07030507080c010c020f040209031603 74
    0x402408003006c25040209100c0410340c00643c5400303070b23201110006080c20a010f42a86010003080240c0f00950800f002c10405010400b0020311585c0300b82c49007000b95440300350807400c078461400b48030300380601392820002181c0b19000b0501840d6800442c200461002007814440c910389a028025440d01c48412640c19405151f2000300c0c107a98000640c15400d107070b109074400b007500501d01c1072102210f10019140b425142c03070b6881041a601c0c1a104900e03243d04005002e00300c03c880407103a1061007102044201c00e1300340c02a02294101e81c0102c98070201100090706019018170f10790040384d1400003c80803403400c0d41031f43e005040d48000c030546440c200b803002e441c0c040342911040c8250003210400c00a2504007044040901140d004034110804640000c400d40c0076030009241c1081c80810395401c600d00000e40c031425240510120744a09a440d420130307a4840d42d1a24035400920300001c00b84c0103092910ba42e100c814801080035040512030800300745048080040c603880103440c2002003050103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 740171663 1250 740170413 740170469
    0x51002101e020d240b04090207050c06130518150904060615020127021305040f2102301303060c0818060c09010c020a0812070b010503070305072c01 65
    0x1440200041130300d142c050020b42038019031050340405030700019600e040060a01407081d00d01e0000740800c2d110303e4030740403141302e1006900555010705501d000d203c013030500302c11226110f104807407504202c004210041c8400f1440281048403007540741c80000c24050040741405a0b1040341e5800000c0f1054408142c0102c65928000c80c10042001d03501d190241c0c40740100c940c605030089101091685452524048540881c1ca002e484a500c8640210301a0684151b00221120550031240c090072800080105000b40040d04210000c0000c1e00d031401096039405050702c00c504c03180c12070b5400e680e915140103490501d2805400503840e88200314500f405940900fa00800281c010541c0c2d03d4240103c15051050500032818024048010011952480041340284c12104161010b13003641c4024039015403c0203c0071111840218004503440c04c1c00034203441102d4004000313180039803808140c40c4030304040d041e1404641d06804010f0450300f8600c180b15008180404540c1401c4030000d41c00c82c412 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 740172913 1250 740171663 740171711
    0x1a01080d02160f0326030403030204170105010e010521030f130906150c0819021b03060402090c030405030f0f040e070c0308060f0a03170301050a051002101e020d 71
    0x94100400300f0701203c2d22114041081d01d60109011000e0464042c14040300004111001d404c42d4000080000b0581e25801800840b13465182c40b000c2c0095121185003a01e50901412580030359030300c010420791030301580040e6040c908540b000080d40c460680b0b58110f6100d25004052a28002407410111000301200c60060900640c10002d4900340380151203150b401070141001c2002101c0108140220b483c01c444880c1941d4070030164170400c40c0710281d102c0751041f012503e4541c1c0456505c1c220b040124080784a1540104414502cac2e070f4008003030354141c00280c420f594900c400d0040240c0621404018030844c05000c0b01240c0f0b0310700c1d002008880b580d00918200030051080d1540c4002034100300c7e01904080c0880c0c8260114000c20045041c2c64001e920282c0341e601100700105442e0301030380046060f1101a00c0307207d180741c4c40d44140b040900258440341c00580c4194203003040c3c1800ca9000b4200342c0300c46480710f4002941c000300c0400b641c00150398010915a15181d40e440407c52034055800c07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 740174163 1250 740172913 740172943
    0x1202030a0b0907141c0b030f070e0606160f0c051504290d0c03110a030b2103030705130302060a02060a0b01030b03071a040915080c040209060405010c1a01080d02 71
    0x11950010b46010441c0542d017540d03880e51400ca80141e0090b08290460144054080d0844582e41501c6044036541c890520a01d14003000104c0891000d08002d000c0312039041e41c0881182d88444c00386c2c1e54411280e240341d4203540b900030110b13000c1490303699603c1a14100c01560220740d119400d000070300840090282550b0741002035600c1c04101103942406850b1101c58404001138908005c440c00c0d0f000e03080b4241c5480c0d0804002a52181442c0c05521003648000c2c240d500c1410150310020807555585240740544099006000180c41c20b8441d40051041c007214100150300d499999000c40c840da0002c02d080c2c000b40e0007640800400407000e00c500e000844007440c09201201e2800082516540b00d400340781a04841e030644400300500e078900321001446400001c1050b0713174401105034103980382c6004100203400b071220808924500b600a03100e00001c01802c0c24502860580103440301e00f0404070440d42c4540c140c0c2c482c820a100c12868034003d00c0705102408200000900c002e081184848044030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 740175413 1250 740174163 740174177
    0x106110c090601081009020406180f0b04050904060b06070809030d0906050a05130e09031b0a11040504060e0d0306081905030a1b051603030806012d1202030a0b0907 72
    0x56075445400540205003800c0500c07007600c854081d251030f420950481c040d803d0000030002000d69118555038248016003105154140c1c075022240e800c0c1000d8410b811100d0741c144814445860030424440e003140c810a00000e542d081d44000c12007036000304070241c68124011854191034103050103200d80c4c0080c0c2e480d1081c60641858005841801080c407542c007040302c080b4034035916052000c04100030b0400f140c2c9030300342c40c6800c3c0c000c1580c03a441203a42c3c65280070b203071aa200724a20700103090b400c110f60180d05040d01d00b044000b80002400300800680b4100c0c0c942c2007010700e4002c00d0003c3c025010495402160587c10308102030301d080ba01da0490704440921039502d001150011003501c1c104d510038940b03845040300e03020011101401400d4085c0c00e038010400c0069141c241c60450b2011240320341c40703202450b51442c0c01902c440c285140018a40d103a910040b08012540b805008400c0102d401c0c013103040c2071802d01d05000c90b00304490b040355080c0d40b46149807440c80c3c54903400d81d008a9074030f4585 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 740176663 1250 740175413 740175433
    0x30609020a0e1905070909051f1d04030e060f0a0c05070b04060507060b19090c0305180d0c03050409181106160311030702040c02010203100f050d021504081203010611 73
    0x70f028108610000c00001d0b0744101103203081c2c1c4200d01001c02042c2c15141401a070030b1208880d03e000c0b4851080c3c641b5214071403400603c8600032101c03800d003000000034000c019036a549090700d42031750303c0341e0f2150b002600b0001c20300803a2140d400b0340003403c095aa54a1440600c0c60150315180701c0741c0043c488078800744800c204e89581310044480241d400f12022030b61110b4540800c11020126220a0b80040c1604002c10a440650302140400f143d80e50705004c240c0f41c15220b81c809414139a28007845801180c44110118000c41d0707480c120fa4801c0c604103107010790742d8028008591340b24450b244003604000c1010107000c1c88016034103428000302c465901e80001c4020100724000d401c0c2e0000c041c82080301c08540c024100780240c5103000c0d00079100b403183e58800078009000703600444800c02e00186041c0e010070069440d1200c0c01c196000606250840350068003040a00b5194908600304107408000104021001b8003543d8200440600b116440303504028018100c0032400c19141c085502c0100c01c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 740177913 1250 740176663 740176681
    0x20a0309050306060f04020903070509131104110f0705072d0504050c030f0c0f0304060203220c0b1b0a0c0e1e010e040615060807020706080906010605130f030609020a0e 74
    0x310010385c10071100166074015000120f4189600b55000c0d942c04613030300040000e080c504490480400d8400c03060448100250400c03c0708551701660921010b410600c222030041e0003000c005c0c010b050080088a4880303907601444040c01101c070005955440529040b2641c05801c04900405020211014000b924082201411a01004002258404c01400413460389040d607c120303101441c0707aa120560340d1030242051000303548207441809242001c5c0416100b4920440f021540300e0381e21201d074194440c540045212160812002d144600c0b03807840308110f101100704082491148180010000c00f072400550700086140240890007100780c03450307000c503420904100541550400e031040b0131030b91074608021004010901e0b4152610480a102250f090381016403c0e106191a0b42229002516001e0443da10301d420f5507221001d81c0104014426140500050200c030b640c200001c038038650b03a0307503c0c4c0143c07800c5592050b0b50342603507601079505504011128401074070400c1420300b445d080581e40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 740179163 1250 740177913 740177929
    0x160c0f170c1c0f0803060907031416110601081605060a09090c0c150506120102070507030f11060a030b010216052d030a200a030209010e09120406020a030905030606 72
    0x11851040380c940020303520715007028031540b0340300e9000843c811000304980f070031001da9032081e114244181c20301d0b40024001c42c401d014261020b140c2039625000381d110a0f918242140d02a12044d040c80705688000202c503008000300c030300a05694004000c2624000310400d83d00c0401d41116016407002c11a015901d504169400115011001d000070f460000900813074000c56906001054003d900300364030800c0440d80c12030b80c0244000c41d60441c85082c40c03513000c0d0817441040401480c03900714800c00c1003c41c14082202c4a0705008808070071021070800c0000d00c096000d00b06040100c0c0da03400341041c040d6410047d60340072410782210610010304140000f41c800f00291a0301003441c0e503400041c0e812407085400000500307406801c448154007a031078001d85245480402c20949254030500f17035000d1900f200c010080f640c000d8181c405c56424034400c0182800001c0c28001140324503400d207841400920024401043c2c2e07030780070b0260582c2524009141c060154822440307540300105120480d612094 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 740180413 1250 740179163 740179183
    0x2040b010c051507140304080d0501060807090b091309140d020c0a0b0904092f06090d031d060a031d0604030e0607260a11030c03030615160c0f17 64
    0xf40b61100e030751154411200c00b07186030088041e212000c03003840100041840508a80e140c8e4032000c1c01103030f80700c1c481120403440480710f6000158140300f08208010841005005900c005001005040c401d8400710060303a2810008540c4440342c5000588401001c0c4100b8407000000d20140c10001c0c0031030002140c017100c0b030054800b45640000c003400306a490341d00c2281e6807035106c40b4448800c419190780284031429a802541d01d50003a2107078070380d1481c0140403a54000d400030400c0c81e045c030701903c04407505003180e514001072481b0301820b441c4640d114400360030070300b19a036408240c2034081c10b6048a0f000c002c0b035486406034008014000000d4122003110001c00059503e1501c503013403030600321402040e1410010325610b082c040b4404040007400100186030180e03d1301c00c0b140320065900fa5881c450211040e049400174000b00c0d4892820036050103907060500300841c109141c8814240403106444021100e4510703151041089501c4804014020501001180108000c18244980710000e0304 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 740181663 1250 740180413 740180443
    0x90316390f03080d020d2a02070806091e070e0a09020a09020a021011041707080c01020703082703010f0f051509041209080304270c0f0e030c10020a02040b010c05 71
    0x11818282d8003682c1c1d44205080c207900c7d003806407a07101e4583d03c4c5028540c4604214010702640c1400f084102d00011098016128200100b50521420301c1e03500c80810600005000c0d4001d04200194845001400600a150100e4002601400c1e40b0400000100c980d000d84081030060000306103058020582c0858280c5071072022544440880755040c062041c2e40102071074408045900711a80ca00040c11704c01ea5044004131040703480310340016651010248001411003404000c283c13030250030020310702580300320b410889011551010000382074600c0d03d61003d02055503051000d00c1540540212900140c002401c00c244002e031344045048203900400c06400c1c040c2c00c5207410135541c418140c55004100f14010799898603101d004145942141a40100100d502e8143c0b00050028a100d01e40e0200000d40761000444041c4900350340246200e114a0f526018908000e100344d11400c8404400443e0703a4080d040c041c1e2a8410002110a402080b17030400188002c6c00d0700080300001c000314402401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 740182913 1250 740181663 740181667
    0xc03090519170d08062d030304180b04050705070b04031b0f080304020a1a0906072307080c151804090b0114041109030c01110a0c03080705060f090316390f03080d02 72
    0x72070107e495485036a0000c60402146407180008a080b540f20840f6180200c40c144001d0300c40b0901120780380540c1d04e0180080b00c02c0408100020700422210818605842d20064181c0345621885142d445110b002d48149500100300700840c5071540e0341c50040c3c071805110102c0840f064442d100c45006151881e802038400103242c4c810b10000048842101c03c0c040110714242c04c0b03e080458031440b462060704600d108064104c01d05241540750100303d1b803940d0b182c0381e040c82c0c40194519030700c8070314041040c0c100d036884100c4400318040c0680da60191040c0a0031009541580c1c003400201e450b85001c0540009080c02940300035640424034010025092a2154030720058003040360500518220003004541401800002c0128020141440601030000e40d642e564880c03581c150100011100c00295070800c1121048083c01200c40d5001d090042d904d2030250f00c014415098010b80c541c0e00340c2d0381c02c2d58001d030a803011141c02d41c0d00c1c4054403e948010080900e5a0b5179404e0398028a0801e071001500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 740184163 1250 740182913 740182999
    0x6080a0c0504121b03050c01020d210b120709020c1605031519020d060e16021e03122a070c09050a0b10110d0c03090519170d0806 57
    0x11668258541110b161621030720340d45e8a280042e0354100040001d4054040c1020b00084503005e0010301142040000000034481401981c0c5001420050842c0707031b0080594002049038481040010094030b810b4a006030746a450021441c680200c82c0300c034520007110110144800d850200d8450b445161084000e010394507401c45580c55110450280c40801e440850041800005600044110741750382e020300140ba100d02c0000008840112507100161380620307a404d0750035904200548007681c01c0025a81050000c2c8801e02d401c003010b5805052003040071b585c2d1199482c00242a0720499000b028003450420035540c0c00b01080682e02c0f401140c684d59030000b82d103240b040d400400700004010030030502030b542481e014014813580b40d40c1ca01c1505c9800781044086003d0700398101041c0c2c15803510070000303281200b009290b912003400180140890900001c2203000c485000c0b020040b0140507014680c460803008103100c00c020b11240c402c1000f4200c4011110a001c800182c44c8002194074980402d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 740185413 1250 740184163 740184173
    0xc110103090203030d05010302040c050306180a0b19050f040603170a0302070b01181109031f0b031509011a060306040c0207150903051002030906070503040507030503031006080a0c050412 82
    0x1c000340d8042d40500002544081500c102d80c07040f8140d920131201044a03640160003101e560000f101d40c5030b044680204891900e01030303106619444100a50b0201c0c2d03405200c1d02103000040600911008026240d0044c0b14a18024940c14107441c2c00b590204103040c55070311900c2012030a1402d810800700009100f4440e584a60119a0120b412a051001659440c07031400280e0004500c88241d03940341665841c9010030707401c2207c3c4d110400030001e03e4403030500b25040c0d41c00c40103003070021421640ca802410264800340b1603031842001080c20911140386c050b034072070f0a440c03205507100000c101d22030f03980301c4694610b0207807500a8001c0d20000b07440c2100440603441c0c9041c81e00b005e60301c41d030440011941d141c0c0c40303244803041c1ca00c1603058400d41d24810300c0480c20390005407400d070207541003080022409072064000c3c40d031150145089804090b9a80c685074211b5100303485404289144800a211103a0821700480d00104051400c02400c07a070580001c00c940241d0140460b413802c94254001440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 740186663 1250 740185413 740185421
    0xe070c12050d0510050310090803060411090a080706081f063209010e0405221a09033007030507090509010f0e0f0121020a090212060f0607030c110103 66
    0x10006041040e404d00050b0301c0030000c030503c0395a21034031402140c1c51614005000d0700c000c4541c0318001d1402d5484030b80800c800351900e261b031400305840600c20505a40d4410705000003d00c1c400d00030744140c40c18502d00078003400d001003a2140c07100159810035079070306603e0103d03030445540d03241401c81c1025040d5010b03600c0710141d01800000c02c6a01580d1005059030009044404007602e030070041d8944403040c0400c1c0d8800b13b8440e03200e0009901d220400340c07001100324038814071030358400c0c807080400c071100d41e168175043d10200c40e0f0703600c00300c0c3c1d0243c0001c0355034040c4146142400200c00036010341c1e440d151410b000a201030308141e150707004076070141d015149543c05050003c01454140da102e400c1800559203521030840c42d00850804520308154030860a41039609000200c40000208076500c9000d5602000490304500c0704040003542500a01c0641a41d400745d03140c0c0c41c03850903c0c0f000c104031010001d80c2e9500c90751003000f0b1400065004114805d1480d031152620064600c0400160010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 740187913 1250 740186663 740186677
    0xc05032a0f130c0f0e040c120b120709090611030906040f0203100c110105070f1b030e0d0f021002060105030a0b040f0c080a050f03070309050108150a08010e06010e070c1205 76
    0xc0d420300503590f0000d83c0000f1200748190311030340e0384c215a000c14401c01054950b54101031020803e506504040c41000c3d03000301c800700202038185222180c01c2d100c81031a142059018036080340d41c1d40c1c0003c1c00c200c0303c2d0103081d00400d6846121811810070074142c82d10358101610007002d42c5140c10100086460900c0300c90301c000e69040701088001840e903006000d28411405100c4e00d9480d102c0003555650142e0702e660b001c48402d81c0c4a41d403440c0c480e00c1c8003032141c2d100d00c420780600c0f42100110100d6900c100c001908503103e0030603030008488503c103019107a10082d0000040d900240300500158030006400e00b00305421582178203094a0f1805e2580c00003a140c0b0001e428101d40c0003001c070320400006035982c801c52164088070311039030030b045605459001e2aa4000c0000d00e07119410051580308260181d08003c003901088081142d500c0040c6545041e9800180c05944503e4a007844400a119460042c440d180710b1790352500c0c06403002049110718030700082194103982140702c2c881d480b40e01a40c4030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 740189163 1250 740187913 740187949
    0x102071110110123090a050c061308010f020d0b0f1c060207050607050307090e070e010c051f2f0405060c07090203090615030a0f0b1308070c05032a0f 66
    0x11085560b00304841d850051009800f441342d00000c2112500b0000b04030142c00c0d00500644090803104040000b107500840c80d030100088102004218a036084c45020900c01c1442401692078544000d6541501c03c0c0d444014070514901001030250b444200080c0c0d902000e69444020140551a0060090080707070409061403240c003080042507a00040118000c000035100c503040c0381d03074a50b580704000204903085400580142000d441d00d500901c0c44041480c8504d044d249003100c03941c0c2c0700c00c00e4001a040080b82c2502c0301300e045d9840201c550301100e92070f81002030489502c21b2030180441403007244112030180800040302004141d0500000e0003802000d0b0702035540e4200349600c01ea8900c001e480607180340740052012903007860009403682c006513110100c44c0359a50161507103400020000d200c01d80e90000100703a074001440c240000c000e890300c2074020300c507414201010325140518000d00100744e9101100012010344c080740400490400854180e820756640c1004a10300e91032403180703120 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 740190413 1250 740189163 740189171
    0x90307080d020403031803081e16150c0906080402360405011d0d032a0c0506062d0109180207151b0c0206070b010e010f060201020711101101 62
    0x68050074a4008100b00d0740690349041602c1e184a244502407455480005c01180080007214250f149a50325021005040340d2407031b0402d00c035080550750810300c0e080b080b03680b101e00e4203d05046038004d11400000d10864034014103400c1c28680e0141101030041d002030700c5205803040d000e04090300407175036141022089607260000700484c12244410101961708469079400c1031211000904070050b18005492004d0080002852000054004100d0321560b40707020020700041740f54006440e00300381d100004030b540303040c0b00b4240e40c100310703040260241c0010310131030018003000008142c24004c0d066140040085103120161400140d94404050f4003031948080c2c0b00103070810f0151a54003170032a0304d01560000d40301000201c20b0f0000c4a144542282c2440486070000c900c1501ca803002c40905407001d001d003032401c4921340b40c1d4035907200c0990014200796840070040c80b50b80070610400005015900095041407030b00d0b610080f01465808415008222403440b905e14584a150030318111021000200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 740191663 1250 740190413 740190427
    0xc130e040c1e0305010b15070f0204060f180e12221e03050d080c041e030b04080310080d170a1d01022212020f0111010f05011a03100501030509030708 66
    0x4074100d10f00c8141c0301546412000c44090078850082c0304110003501d0300910307100a9907a28000c5d1020940182d8005179a02000b04001800101403000b0740154013400c070780b42d401c884019082c3d550f4190020060f801c010000b90750800f6a405840b402d440c2d240041c4003c00c00103400d145030102039405904200c90344076114001e40543c200703d4080d00c1c0148140c8103650103066060303900310016104201c1803030017044100440c2a400340120540301e0300006500f80c050b5607454610b5494800e035000c3d40c0790b200c00028031107440c0c2001610b2004143e00805000504c803c00303c0500b54500344507800341000719417000100380d80c84540c08000e60300c011201204652807102c1942e4000e400c00c1c05d4040c182000c0c40c1030380e40d00782601c0d0301c003000311001e03014801030a607250307824000b80582c0303800741a0501034183c1c1040c690110a0141442e11240f0160004503585800c030f44400d0020018001d44110ba020000d00140301030305d00c0f401c02070310f00a0074086250380340e91004074a148900070010342041d001203584 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 740192913 1250 740191663 740191709
    0x60f01090606020f0c100e3607020a08030a09050607120614060f0d061d040201080f04030c02090c0f0c1e0c010c0609030e060409140c130e040c 63
    0x1050690300c03000c204011a948400040c0d996850080c08400640e12001c002280d501d0800064000c1e40c10078a0112001d0300000c0c04a4000c14081c103400c10640b4042c403183c900c0320b07041ca441d41800101206c601c1010b040c0100007940307540140c1409407080310008005081c0c1c0c1c0040d00300c0034002da440821200c05142007071004260842013204140141d06200c40010750116640346004c00a100401e06407400c240b0740c01041c2107510406d886055151030b03050010350710310342c040d00290003080b40501e405113113060701c001480140014185000001c014040c8008681d04c22030b8540440d0741500c018055403200d98038075030140248130800035540b1000038000c0040102159400c680c50820030705d0300c081a0382c0048551954049203860f4001485503c10b100800c20a0304000d1840b070290526141c000035820216809600a0304035803c659110550400d420280c015580e9004206610060034030742042103405a000541c401c16012120000c003040078060382c2c0200c400140b0b000030784460811a201d0031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 740194163 1250 740192913 740192941
    0x41b1401030b040c120f06120327030b04080313020405130506150904081827071106010501050f0d020d0e19030e10030f090b060f1c03140c06 62
    0x485001a003400b19180b4a8141801101d83d5a5000d86844044150b490306500061822045040c140c030346400000038100c0c2c0c8078540500c1d06020303640780786034181c01a603041d5401e11003400070503481c1c2040d5010800f2450804949402542c0520029902d440f0440c0c41c008905e5161302c080d5000780b81070280141e116906003101c0740075115001383c500039501d0151045454a81e044943c0d00100c44400040014a20038018000700030203040340c010041d00c150100305c15000010b00e40c442020000f094844541001a10a503c11400d24014405880007446035417109030601c240c90511a000c0390b00b00c40b070103022040d60750740c240c031072411074882907804001005000c2c20404101d260181d145407840b069034070800e000f40e854045c1c4503140111000300500070304d1051081010101a40c81d5025040d008980c01114034242c00b55003022000d06049080203030415080a4841c030880c494503803010b9140d403001048003c1034160604070742107240000f00c22018401d510100e100c0d40220303c2048240031114070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 740195413 1250 740194163 740194199
    0x9050f060a0204080f1b04090c0b0d060303030e0118020f0310020310061e09121a07110705040b370b0315010806010e0f0406090c0c021005040501080f041b 68
    0x8200c4203010005c10705982c86026101a42d00c401c05400300000700390070160006011b60744140355501c41d841d945e010a000340e401c07200e90003510984a4104100341030745801400b00300a6608002c001111700c0e00b80c5a4840000000005e00960300b001c3c1108407a502440506404803003040c042d0751302d06c4c189120b54098003050080202045111000d030321110f10a0a03010710b100565241e0720b201505024001c1551100301c402221610071814085c2c0388103074901249801404551210740c0318101c1c0c200c643e030400d1119003040740a0303490300c13507011143c0e921080300c109204400c1e40c40120304c031342d5500c51a1400104100c1074040389050140054003190800c01140700c2c0003034804000c00115540011101e400040e074241c0d00099601c1c1c260061440d05929007041c0d04c80c007c000040342d5503502101400c0c3c5164039404000300720403152580075030a061041d401c4040042c030b0207500d03181c1840c001030500700016207507252140082001404000ca2080c05240c0c41001b42e283c0303085c1c4c0b43d450a246488000c285 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 740196663 1250 740195413 740195429
    0x80c01060b040f0609061b020d060f02030a1a062d07050a0302160e0a0b0409150606020c0a0303090b03090114040c031a010509180c0909070303081f030609050f060a0204 74
    0xc3c40040c0940c8101c0c40c50f0192429560b40c001390500445000800014840e02aa885034403004034100044941c840c6444805000d00c001da16440d0800b03c000446103100d82c034850300d001c0e91841c5040c640e0340904840040024005501c04082241038503001030300a6086444048000a66031040c4900040c1007405144268203c1c0c020288040351014140514428204c0d580499408a40c51554a40001c2e04818003d80700207200103141d1601078020b00b42190056000e95501f078103110b000d0b418410740e080018103440d1030101619540c1c00500103c114410100d40420101c0860b02111007034200742c2c03622001076081025030600d420170b1903594405201c01c8400a00134000c1c11012034001442038121a8000c0554201c3e5984a000d07604290403462184070030f00840e0140c4105030340c0d0480b040c0c0110882801001d01c2400d52801501028014002d0f03104441d144001e8203a4007007d000c031b40107030390f8000c8000c2144491450214604072620302c03800468005ca00802c51404100e6002c1c0080f03440c06 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 740197913 1250 740196663 740196689
    0x10b090f01150914060f07021323060904020d080712030c03060501030905151e0103063e0f04210302100905030d0506030f0d0206040c060e0913080c01060b04 69
    0x72a4054480f0621480380040c80000404405580d141420240449440351600c45190200c2c039800221744050400072011900e65a6a208005690340c0041444030703e10045a804070381050300c0080c141920040009100300289591002080710402c292070302d040d440403c6c1d540e10740d048403015001d4076082050100092030110006080d6200c1e001e510f1215812038040c3c007002141541780c0d0b022a0000340500100040b20b0014480381c440200c85500031808ac510001e8a04000c070101100303203805490b4840d0b441d0002e80c0824038502907411790280ba11a440c40707640e480c4401c0040080500271079009090f4102c42c101c8400040003c0d00000c00141d10950982c4c02c503c1209203c4407c40cbc00030300014000da0310902040208220951006403c900010125031000c039594896a15103910a14924016001001440300b00100b07051010042e10303c81c205030090800c3c00010030034800700146180c0108a48898070b00c28041400b00321114811100000d100180d01d030103483d0326590061003000c1c801c50070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 740199163 1250 740197913 740197949
    0x5060d15060e100b0a140c070e150a031a0621060402010f02030418021605010c0203070b1006050d021b0d0207082b0c03050c031c0b09010302031905010b090f01 70
    0xc107002c2c9070f05494961950600301400345004a070451242103c0c0d000c0c000c010006040300a004000c00b000030040c81502030a14a8440784000a00303000010040c00358511803402e00003d5805000b40d40c02c01d03507088080025641d1000080c4a4040b00003070943e40c03a028040200280b00d011401c09d00c114001c2e220340c1d26004504000326528031451180d10809a04960b01d144000301c10780040101d009410404400c03074140b501c2d454211403000d10310002503803001900c00100040741d0486507004188101c01c0103114a083d4010f0018031070211166a02a4001042c0606062003880720406444030705c101d031a0340c081102c000e5900c40c1c02d4011480288580040c1420085001d488441c0404a10900704406000e5940c00e840990041008509100b8117012a08448408001170300c1101d158812994a10315881644030496070341d03440141c0244050030041c00541c500144030718540c2c0c0104c684000c68240c03401d1207401000100043c542c02001001130150903600040403a042c1e9070040e46041c00186 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 740200413 1250 740199163 740199181
    0x3040203190302190c030606061110090209040b130609081c020315010804050f031218010209011d13060909020307050d110409110d0c0e01090209010c0605060d15060e 73
    0x1810810040060740484007184640d01c074052150050751003601c07040140c5d501c0f540e421003503800309e40249000035040c241d0707500c2800c0200034220300088110000c00110440d5000b06004000c002d0010380784e080c8200c003084508405408809401d50001c0041181410758988141e29611040a1800802e281c0e4440c111044280c0b0840c1d024692020320740d07911b14064401980e8203070f8010400d503020b010306651030b00202c038148002c10030380302e0a440c44034a9150917009000c02c400d00c0d0100345105d038414481c485213640c20603d246036011000441d25020010040001c00c0d0f82d142e0404025500c0c200580055510740580100b400a0310071030540b003000340c40e24140003000d8002c5001525101c0c40c41c40d40c440c5410190710440300c0e64003481d588000d280d10307840071980520348008103c5d5411b2b5034040401c03429181ea070156007d003000350303006d500c1c25075a035000900036010b40002030104c5030303100d011900c5c40e55a252a0084998018100605180f00e221600c0c02400248110400b03801c0080002d03004c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 740201663 1250 740200413 740200453
    0x1e050d0c1112031602061b280506070819021201030c150507030e0102011803120e031c021804090305071b031a0402040b1909060803131e1a03040203 65
    0x2c0c40880c0210f0070050118803c200d0b5040640083c5e8100c10104444401c001540c80c408142c00b4040c0d000380503424605071142020100c032071400c6c160b4006c10010500003400880c0c595044a0b90b440d0807802c41d00e0300448541024100c40030b6850082c0700040111024040a0340d2074120fa01030426490147d40d214249200440811900c100007541041070100007805000307044038561040c400002e01620b003003010700b5485400501500417465a403030a94180c0c40a00071081080c42c28000780d424100c0c00740d01040c41200c0d020700008102c2d00800c07041d2401040f500e901d8045140140180302130400790a01920750340c1700000c141c4080310103a140005a00c58110340e001225803102400000e101c0809000c3c00d140030151080741d0044d2161074000740b90b0343d00a81d111903141620580c41e0454501003800c02254555402064a0341040c0240703204516502d0030f1400310b07500c000300741e8050a02000350b800d0b034070130301c2d0000c15070503d40315404045050410069803003140300341c0441c1e0920752800a201810 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 740202913 1250 740201663 740201689
    0x313090c020c1e0306011703031618030f140a0b130807150603030f030501050315060d05010e01020a090603060b0a080717010303050711032b030b0d06050901271e050d0c11 75
    0x15231080000c07035500d40300301c1e62500d0780c070b086458040501c0804540d520b00c04203041d8005d8900210a42c000028010700c4211040c05070002401401e0140e116512503d0b44c02c0000c240e2600520032110301024020001c04503003001c1d9201c002040c00000b0700c0c800d03200400d52804150002001d1a0100821a000303104042c10303524001c005241101c006160410151001407075103030028108810800000c000340561889001000300150300c03801c04c081d008110b12a26440401051f09000e810041501e80c0c0c81110708403103c925009245a031440e00503105014100700407030031680bc000001051607480700143c40c05901c1010f50b0740030206407604056803892200400402c2800080c140680c1c12000641c2c0c003d101c0032400c003ca4020300010003c0d2030310040b004141c2e0419260410010624404c0c4500c40702d840095654900001d81e440345020000301072140109076851030940341c0c0c2d108804510045109501c50100c98071401c02100007000c080903c18200c0b8045c604d803808602c0c80c42c00710714501003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 740204163 1250 740202913 740202959
    0x50f120a02151803072406060c02040902031c05070203010c030c02031801090506120901060803030f130203011e020c0d02010b0609131113080d020313090c020c1e030601 74
    0x152100d02c10007002000c6010307000f401240a40340941150032018405002e80c079000311030100b20402800f034140e20070116507040b011250724002091240b00c8d00080c04d8140140c0540c1d0020714490548042484c003001c002090b00002d025200e80b5000d640d0080080c41d080380700b64002c0c001d442804105405445002055001503001071103446030050071102c00e03400d2030b86e051510010050b43d4402041495102c003034083c9440c0c0043c0c0410491000900800d03000b814070070021459450401801001500064819601e074005120b440303041d59003d4005607404900c11200d00c1e94000000302080c002c2d030040468440c00d00074071550144190040c42000d41e0380f00c0140081345001d081408000074841d0505100c04000d641c0c049a480000507a40038056080300400070023001418141164940800000000115801004200c0101e9500c038030b11811680c0e4400042522092400243d0916181d40c000d00d8010400c0031200c0c07100c4803d060091b51a12043d81912143d0b604d51184407542400e074500c00f00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 740205413 1250 740204163 740204173
    0x15030c080f0a11010e0a031b080708030306151b0123090a0c17030c071e1a040302090421120b06040b180d12030204150c020a18090f050f120a02 63
    0x9155008006620311084000c101b190303801d890340c1d1034001c12a40107046203424040140d00f441000801c11418000c5d00080c1c0055056141501c0082c0da03601c81641c11780e030600b801041503030104000655416017011004002e104012480e01d00d05695400f09005142d104091400f081800c0c0000c80d1300320410b03400183c01d180040c10301594441e480c012443c11145807104000460341d40c0c03402c0c03080380b01401001d01b0303a441110f40c42d464480011000d8004011150105100d49144141c0400301c078100c80d81a10003004e1990b4a08000c07020a1442000e80e03041c16007907000d4071079550f0109030020443c01e0208200a0300b1a034900b031150900907400380e4200020104500c6402d4600b1341c02c5c5805000e801800c4155224056841e08040100200c030140400e4020400348100d00440010b04500d000700e02c1c3c019140600c0c1c0d000a6002c840d0743c8144607000a4100015184201d00d030005408a034100d07104440440310752406603542d81e180c0700d40390042c1c06010b0500e080c0c0c10514080b111500740d641d00400f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 740206663 1250 740205413 740205443
    0x30715051501140c1e1e0d0c0f05060a0f0e12031503120a0804210c0201080403140c070f060c05031e09040c020d08090c130f15030c080f0a 61
    0x50340c50f80d581d48a14261000c00c0c400c66600c0d40d0f0800160545e520000a4400090b00901c090380c500003009404070316401000700c2c1c005005400003000300030b40c9101c1c98081d8011003141804810900411000380c00b50103008104140c1740c04641022810105000d8100a054415401c0945510a105c00c103000254100b0101e01c02c2e80386105441050040203003500e29200d02121070107407540c0300003940000300e45864200010f020030b008040252414006030101c1a12040d80024070a2001c08030080c18440104040750505110f400003e40012000c9005641d400c404882c41c2d60b291220720620f1a5082c40d89004222107210b40009200c20b980000250b003040716802510354080ca81413241404900103110383c03236250340d4901640c010365046401034481c00015101c01401c2d410010948042c640c040400e002c00d03519a04c2c915602000000300c001240160145250060820701c00070451036a068040402032090345941c050480d00c1c01e0084904480845586984400f0002006026000404444 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 740207913 1250 740206663 740206667
    0xc030d0c020f0604050603070f0905150a0503100f0914010f0b03180111030a020306030c0f1e0109050402040e01080d0306081b0d14062e1406040314030715051501 71
    0x2c00807001005210b0703418030b500d03080460a40c0e0411111940080d440c149003140003038101c040c0c000508415248041240c1c900f0010b5040c51090750480300030068004001407682c01a0104540030703140c8a1454942d455803042420081c00f01000000240100c0074000652100740c425500111241203403080d003580d480640c810368425211100c01425500c544d0100d010890207001513100b03220b182c0e00162242400c005141c07402c54505c007024010000107800003000d40c2c400b1610407134a01c0e5120220401450100100e5041c1e40b10341c04070350000d0010801150081c1a01c2e4064180c035809021900365001c03502d0118150354146c403840040742c0141e01501100d80c025641c8202080c0041d1100c0003680309a5282000d554240200040581080c1e080c048600c1922489924000c241c1c2000801c03c411500d800504203410b1044a02ca0000640303940c00548419054030001e582006102020b00442a50a6120303031129408990103110240407840f001500e110300707402045895801801c2c01541801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 740209163 1250 740207913 740207929
    0x5190c03200c0a0c2702121801060f0e01080c0307060f0c1e0c090c170a09020117041113140a050403180305071d0106021b130c0509030c030d0c02 64
    0x702650078015050160f0124900d000703014001c0038a943c01380490340e4019001400e1808804403c0200c90040220802d202282c521040e0002c40220110b1b07001c00b0262911801001190310035014070b0040100040e043e0355100c3c2d40342c12510321006558a50503c0b07400c25403030314042d0041034041070311440604003942c410029014107511400d00745191ba420204018804030454004884490340c5e4101403080d9441030180c005603122908219101c40b40b0b00080002d0144d0060600c00d100e991080c8510a680c130500e08241c0707a1007042c2c05510981040e003000c005031a811003040307000312160b04c1450740d44403d61141032030a211600e541010b58942c0101d00000d044007500680801c04050740c405400310710601004011481803000b030031400c0c54005091510450004544100740010004000e6550082480004034080c5a8a00040d07881c200006034420300001c842520286000070031140d040d001002020440c400318100c80000c8202420140c0d1030302000507280004002440c0c5000500344544c1c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 740210413 1250 740209163 740209177
    0x1030b0a0905041505040f0303150f2c040308100501051c0c090b0c01020711041401031e060203130b060306090c19090905010606110102160807051005190c0320 70
    0x1451804c1d10b007401144150b88054801b40c4010441e480d03040c04250305403240c0c0e59202e61000003c44141d00d0060307641c2e0a04058450545c2c404148100107082c1541040e080054161034603d00302c1c1400c040c00c0083c5103d1048410086807014a41c0c080b030740b0340c006c4013038a4503070156003160b000b050b82608840015103840328140302800350103c40813801080c024064500d41c04140b000580319541414041c40c41000703183d5480c000e030b103084402420030809480e00380c1581e4209003144200309a04030382c3c1c80000e42e21a0f000d040d152011007030090007140c4d001100209401030000b000251194000c0507101c40059843c0c96003948612509078241c28656010b68031003440300382000d4426070340d400e224181c4807414021503659540d400e0a0120742d40210390600e46107820002141085c2d682d641d03079490b2114030308028081900228001040060070001d40300c40742002902449a0300f440c5c220300c954940031030f0000744e035642001051501d4034803901c141204114070b42106544114550041c40c82688010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 740211663 1250 740210413 740210423
    0x11091908061e04140c13021c020304151e020412060e031914040807080304052b020402130305100b040c1d100201021e0c1506010804020112060807080a1101030b0a090504 74
    0x38402244d43c401074004801c6c45070600c056501c00394607490f00100150500310182c036031700c14010b0101260346145120114521900c0000d59014a0040c04840021a5202a492500014020404024103106c040446100380c00030f200300d841c0f4003c2d168a0b030042450260114450000c100f0150784158012400e041c9610450b80c941921134102c2424608241c001111640c03000600704610b0800203021000e44592002c4640e02c40312024400c01000d41400c2d010384a1034011032035800304900200f0341d4006690050840c0c084840e065000c402901144501038448c61410b140424040d0280501100f13030380d0b0300400c588014281c042000654400071181e80c007199401e00600b0f0b01c0d40c102039140c1c10025900d02d840d548800c0a1050b042c5031030042403d60340d04689078030a005090360402d0b51103403c5076090912107003210387c00000c88000d1210b40d01509007482044400a5440000f1561540301c0380115900284000010010360603580101d0429820180d098000c000c0145541d00094009201c2c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 740212913 1250 740211663 740211673
    0x20f0904050a0b0301020c03040314070b0712091502010e010606031107020913080304030804110a0303050a0e040e0115030201180311090405010b0411270a060311091908061e0414 78
    0x711004ca0708a030010b001280f41c6500014051082c0504603501c906d00080ba42c00810780b803810321281e102c403401901d00080416440c0c04a01b04110302800840c0c000d031410300c1e01041c00f1182540001e002c0d02600355503002d0755290420209100d8070a00441210b003200c2451175140040982c06c1c00301d900740080c181c02d017000101c0560000250800e0055010780e001c0c1e03940c03641d642000e051120110b581000100e01c25400c0510400000f0780100179a080300e5232a00b484400b100020300030801502285540381b101d94a040810191112122002415203000782d803426071030078410311135080100d403e0001900701816206031480e5464011440c80d48144103000100e20442e02d44041015104540c01c00f042c90300010903181200c000d041c0c021101c00e0038103200110301c1c1f203807034000c10001c58581c01104105602d60b01d01d070558644200440d50020340142449606080c1d03142180541c003031301d02400a80d80680700211392034a6091500c90090560000005025100c03640c0c0c006007840d0740201d5209034012 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 740214163 1250 740212913 740212931
    0x6120c020c0d1b0b070201080108060601080610051903020d0b040b30030a09051008041113200a030b120304050607020d05010c120510080c040f1b170703020f0904050a 73
    0x480b08440d0010b100320402c003500c5e000c0381c0c0f0025010f180140c0040030aa40220100b0400707a038081030b41034201c0e00c1500d0203014510003041c11101071151b401c02c05060001c2e40c1d40b003549a0360540c0204046804140c04000c03c840440070001a200100301081c3d101c900c010410394200103500c408040c00c440340404944000007094400d003550095a01040456001c1604010504040c04014200c003014600b101d81440c1542d00c0444100080d4502405079034034140c10340313940b04c0b658440c2c202c41d0ba802c0001c12030082586060031150b80030125800000c1d0038517a1410840c100b004c0040e52000c0c1400245090a01740307824070885030005030069a0040b4070005207000f08100307214002402c02c0c1c80e900c000300c1c400b080102006903040a80003600501c08000100440f5a0210b0406410310303084038041082d80f420a8540d001e41284003000c007200c480700c0301c0000c1e455000315101e011007101c048040c580e40d40e2200300398220b00401e0800e00c7c004004010f645910301c0e19602160703000c1c860030030005060070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 740215413 1250 740214163 740214203
    0x120103060c021e010203010e0105010503040f0b1f081c230705010209040501121b06021b03150c070308072a1a011d010506030106021e0a0803070906120c020c0d 70
    0x41c460f00c48103007907580080180503465000c0003460240c0001e082c0700b884c6081c41c1d610703216000450790000e0a20785066000ca072400003a550b0640c0b02180c002c11004525460300178254444005c3c009911095000032440c10000d0300070925151001f0103401660200341c0501c40c40200d80d030080b0001c844a542c00c0003031075078540e5180326107406400c0d0800b26001542e5580b40c42806108a0441c6945000d80c41c0c0d070420040f50b0000741c0f21410301c0d0400d0102080c03561500440c0c6410b00204942003040800c00401c20f86803103510207004182c1c042d54074000341d40c44400058030b40007901980b04800c2e00783c8000f440d09002c855154885510310801a041c1c604014507503c1002400a1300086e04010517103170001401c01a1041c9035014100450b1407901d0b55140800180d61440c00c0c094401d01070940c10410844a44203000010049405c0b924044d524500f152005000351002c0c00f9500104040e03050505440c4118807403111811b00680003406020480b0b4100440b0f001d0005003150a8482a107003920050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 740216663 1250 740215413 740215453
    0xa082a120426060a0506010e0321090d02030a06021c02030108062e0f0807170a06110d1406040f0504020a0302060c0c0303160209130c03080a140a0909060b120103060c02 74
    0x141c00d00b1300041c850034081300042c511070080f441c19105e0b5105030781c44103440f80d4a02002c04201160700300b065440441e60086460842010f2020f5414052050502d00344541e58004000342090b00300d50501c42400d4096040c01c9000a01030f9260310fa2100380025569245014441125010b00480080000d414082c12005d1801c0e40c00500c00e1041b80902001000e0040009070041c24011803000e18202c2c10350620756660400a001038002500ca1020000b1400c1c444100e0381c07440304104090140c0c524000ca03901004d44281e50890181c0e261501d0b00101c0aa45d201d154011680105280e410600d940c0801040360010341c214003840c00b07150403203140360340c0410051042c40091303c640300000e40365004100e2843d100a2040031500e041c0d50041e000104102c41c03120a881d800311040703480b00b0b402082200e00c041c0442e84080c8400c0c00041c0c413500070b60442c0c1d0502c12030f140b0503000d2020079101c1515a105000b1490726025080d1280c0c0140000341d0302e900100400c0c0e00d00c0c411568010041c140d040005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 740217913 1250 740216663 740216671
    0x61a0304050303070320030703141008250302031203061306030506040b06190f08120310060c0816230706050703081e0f0a050702010c09170a082a12042606 68
    0x4207662b8082c000d00086200c2c0c0c0f143d808000441c0c03001100745040c1845445a4401d0180c1c03c01200052048007500c6920346014040c0d40c01804035118a4030400103400d0980c020740300184200390f4003212540c40f9040b07001b400140c90340300018000036180d44d515412048800303000c0ca40d000c003440391501280b540946590008121010354010928980f041050410f80d04c1612422101c10800030480b8220100c02040e0407940e0a10f0803480079000c5041002050003005040744d0300e403041c61110018031003440e062640c00b62403400800440c0050705001c1d40d564615100f840c1c0406c03003c0c03001d81c000c43c0c040c10b04c1e564040070885800c025400c080c211484d602c0811100340b100c1c0c051450511030802c1017031180540c00080c0f400200001c01a0725806403212005100f81444100e0b8503070010280c1d0000d0080e2804140d10800345a101c0c4e0002800051410642c54241805401d800040c1054030b40015541c00035001c1404062500d41004080030510040054960030a05e01440703250f0203e0080003005e01c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 740219163 1250 740217913 740217917
    0xe060f0304081312380c1c02040f120c09062303010c09140d020307030303050f09010501050d061a04050403050405010e0301020f04091d06150901060f1707020c060c01061a03040503030703200307 85
    0x240c0c51080300102c47c0004140d1000d03110320301c103010034400b4014004681040d240b0388951a81c0c0c41c0c56601d010640c0e462150840401907040c40310015007042c0e0108220400c0b010013031700010b01040d14052500321031801104070300040220104001c3c8070102c110b612446503025004000c5a1443c1c0c001c01d05c0d058490b807040703000070b03980e808100c07001108100654000d00290000c1c88a545050000348041491240140c0221382d1000300e450305041207030010810440281c014008c0b460a42005002d54000b8031a42b800b00b2005860a5400c1c54180308550003901410013890030141000c240c0c0b401426074101f001c1c001007020140e00d5840c2c2003044424495162888841340e9050320380c09001214034181c0c000c100780800e0041410030580c000c956804d0004031013001192560310f25804034608034102c01c40e01e81007000050621b20550f410740004064074140d20700c0a54401403549009424170040710040c00d190010f0000ca040e4611135041a13292800a20110240800c0510303484225031003030f281307140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 740220413 1250 740219163 740219167
    0x40203130b060a030807030810080105090d1808060c0904020906070c1805010e150a05060a090e0705090120070f270b030a030e060f0304081312380c 65
    0x100018040d026611030340c01c0c0d840c1041c0c3c92031540c0b801081d0007290302c020148281640080c002d00b24440c01e480050400a00921160130408801c0d9125454920002d0004603010480e01803421513002e15411603804500510301580c1e50f1505605a40201110f90b40c010b03020003070080c0c40e0351440054514507000b10040300c810742c91b01e003d511900480030f403900c0c820760800c0010441c85114802c081d03405148090f18850001008000a02c03101494104ca94441d04c041061540198003150342c1094a13040b0070b03064400e0310b5601040d1a54014506180d0015021400c0d0441040744900000700045030f8008840410791954003041d11100d030b80c0c01c081c1c003100d0a1122600040c50012408288280214007001a1003000010a850304403400001e014440e490007008195151034084031400ea81c29645140c582c182841e10242c15030107040049400034182c2404100c0d001150b54014050764440d0341550040f03a1030784c4680c0c200401c1d09150b90045216560a0408031081002901c00c040c0c00d07110607 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 740221663 1250 740220413 740220451
    0xb03011e230127080d0314010311010c03031e09020f01030c091e03150903020f030a0504090c020a0204060608070219050613140106090617010e06061201060302040203 73
    0x51550920754820740e100c0a40c0070114200c0500540c00350080c0740d080c6030200b240346040b6034410341d00b02d05102e078905429601800098000000c10021402501c50754140480ca0200217110758045081c040585503906030450340d01c0960084174140c00f02d600c82d040100d00b641c3c0c00f92901500c86545802d10105c0c039260f107207040840c03419441c2c0140050007401c081015803051a001001001180121500e03c01d4484c3c420060a40c1c8030341010055034090b041900c440c000d4020f41002d00343c5410110058860f00310070710301455000c4142c2c2d0b40c20345180c0d22107003450301d48004d0401503c0c0a80280742540034106004016842e103001d000c0117004207841c0c54146080403880280351040c10462040241c449161410010b403001c2889600131803c0400403c0008281c10804c003030704400204100700d036103010030006450340141c118908a54410200000701d489060b4418245d4010000400041c2c20110000b00d0742d2030a42601c043c0c10300d02d04000034149481e07a000c40c007243e00644100c2074104030f40c0404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 740222913 1250 740221663 740221709
    0x40218100303110f100c0509030703060e0712080d05180d0305010305060c0a1706030c130b030d0f1b11040e03040f06030204030506070f17070c0209150a030b100b0301 73
    0x2404401c410042c01c0780314654030704a8591007004030b1039020b181c886c03461001c26880350341606c03152480101a200507030758904d09035005064100700701d00d0342c0c00303072030030025034030020040d01030310f05400055051526514611007002410010f00400c4030707110303418210456000c10001c02c108184151800030b503030350441c01e201b8a80140140b1024070000100429130031580c3c4400407954030300b079080400c91079860b0340780020b0500d101c1500803a041105405212071811041c0c201501d08030f070a801b40c9007400400b140891304200124080320100e0065003c843c1800c040029410100b4011440b44070084100b2001409941441208102a500c085018404034950402c1a40242810b090440c6014a141e1310700b605c0b0382d8001c1440003846802c2d10a440c41d64010100302002c503007440d076010501c1c5008980a80f6030500c0d0038069015802c548005100352060a03201000b1007401440d40c4a0149140c1d030b40c0c200544020000303400c844c684d0f03100044542103100a180a04581031070f05004000e4042030b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 740224163 1250 740222913 740222927
    0x204170d111b040e030903010e030414030102031509070c1b0603050f01031208091f0c180e1812070308010312020109030801050603130c06030609060902030105100503040218100303 79
    0x204004503045500c0399441d82c10b01e00364200d50050269408504070f4904070f0920b0442c0076200c0d00c80d82650a04c01c0210b4001070110082082d0b0b12a071000e20000c02590040c503080303010031103124240088030500c496061901d030380c80c2d0b40c1c481c0c418604034110f0001c07503403058119101c800c8280b42c80287d120301441580d4150003896408010340964081940c910f031038440e1594203d0700884244900d82c00414820301050001c6492501d0304090701c1e081118035600c46004084055400002130b14600d0340c1d05c41d034504408102c0403140c108604030300b203466090301426141d002183e14141382c8680c08541d042920100c0203420818001d468107102c80d0f1650810000c02034108031510110b91400e15940c001036008480e0605641082c0d031040c1d04c941e0380c4480100c0c03e070704840003e8804141110300241da5036154010342c0c2a11016801403146540c2d4400b4202a800203001d02584242031031003021000b8864009503920600007000320f008004d11010100840c10151a0601c3c42c0b150400140141030700918 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 740225413 1250 740224163 740224187
    0xb04080f011a09100b0a05120601031802040b01020c1327050a030e0109050909060a060f060206040b070e090702100b01050a0f0810090c020c030c01030b01080411040204170d 76
    0xc000e000d4040040002086580c1ca01c281521816005001c900c010391030701c4142c130103014140566a610140e0f0300b07014026801180c0d03100e2011020f074000410b254424051030712004040640c0d02100310607642008007078004800b8440c1107119120006c29907a40d2982c802c1c0d8280407031000058070141540082c02030307040302003001000840000c0c1040004400140c0c0482c800c1d094540900004644401281d51040301e9205991000b00001031000803000410100d0148a5070401004003a03545d8880c800b03030082c24410000540c00031700000d80440c03140309110341c2c800507034031703000307a00c600008001014a0b00603100c240042e40000400c1002107a5842500b001c2002400c000341030034903844000b080d00111070070708010801a0004207098071403c00030310010300940c010034000c1c120100c0000f5900c03001c222103948a071051014109840d4082e00c40e009030064180c0d81d11400c0e50303445d245e2954060200c0d412903002a030170080022140c4d424105004810140000b4216240d501c440051213440d00038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 740226663 1250 740225413 740225443
    0x180f0c0506030c040e04020402091203310e060607170d15030b040f020102010b0a1409160509010c0c08070e0117070803160c0f0b1345060b0408 63
    0x3448140721541d004d075000c41c1c443c500d0301200c59640e8404140a8014021182d8000c034000f240c2c3c0f80d550304040013a0080003070481d15401c803180515400022946410074040d0002c00310101441440100c0180c82d034845400340135186801540c0d900c0d100007600080d12407808072808034092100103a203008101c580d1078205003c0c4001403c644680c1500000a0300003441d41c24400d8241d411a4000e400c11139203800000c04441c201580c9810040061100001d0148194002800281d407110080a4024444010783c2c565041001e5800192040103080a0aa80070b1000c0040061406420072201c4003510180207501165450410302916014400c610031880d500004020b100c0c010b0300000b0b030f40908410144079040c80a4500f81002d0761202a0800000000c1d801804140c0291000040551060441c25145141c0c2e44008010282c0c291703048824015840041000244c994003002d429078080302c0002c4480202c2d2100400e0803182d25510000300b440000ca03041114600c14008508030b00c40c56 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 740227913 1250 740226663 740226667
    0x9060212031e041a040b060a08280f0602132105100c0905180402010f05180f18130201020709110f0c12120a06090c021f180f0c0506 58
    0x1a1402010110b05441108410005140060188180880c03900c02681c0d0000307681c0001e06081c20542c0501d2012140c69008441d000400140d25100180d1203a404143c200d103d42149141413004142001041c81910102e4901000101081c8144001c011502d4061480740d05a850001252070351110042805c01d07550181ca0098003260020500e6251a40070100c0090400310111051351409100d0b0030a0303401041c4c08a0f481320460880050a010310700076201d02c08100000c0381c3c200d07541d02c1000e40300c840013440740c05041c400d801c200603130000403c0020400504080d200000101040e01103a14071207111407800c29005558060000f10007600e0311040030b0241030b0320b80c80f104801e841603100b88500b40c04002488400c0420912a60029407a44104260344080898442c03001e0741c0d090321950311052500000040340125441543d03070710010b54003e007015001c0b50351491220507401d40500307080d0391161074072175640300c4941918818a200302c2c1c4c1e4042d01b807014107103440d902001f0340155004001c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 740229163 1250 740227913 740227921
    0x307060f1e05161a0a0501030507030b0a02070b070305040b0612070b09040b0a1e080c01090303120902030d020d02120405060702060a050d0510180c1e09150906021203 73
    0x101484070050403104000d80c0c11442410842200c2620070020ba150111002c000701404000818810f8035a85801814404058035003500320801c64000b0f10000b849948011341c00c0001640700550541c0c0700840b000014288034554551050005040744c08500090303545080204000e07819282d81c3e00300005075912400e1880c0c0381c2c10035588103031038003c0104a0b00c000c981c6200d01d540d030b60440c403440c1d03d016040103241c5560351581c118803480c807081a4000841000d000c1a2207a000480f070449220594a03c3d000034903585041d40c214565203040350359191500c1c81c00015840401114484030066401030403002d1410b8402824403800d10304000e4080c008000400980c0d6a00c1c09443e825a0121803060b43c6e405203d41c213403024070485800d1140c0310309140400c0107060001410100b19003146441c0801d121039003c118040300e0200c0c04420104889030310656408002041701c50b5802d025040c641e80e038a48070b2080b000c60481030750364100002c581d203105200c01681401940c0c6c0c0c48605003005030031810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 740230413 1250 740229163 740229167
    0x1309060e0702281506090b0a060c0309050f1207081b0306040f0b1f15141903050a0603060204081e1c03020307090e1801051323070b0a050301050307060f 67
    0xf1001c0c82402c56540d01c1d10070814030502e209200350800b40e00c14200540d990322040031001d09038203101c06105803000440098250b0203108080449545542c0d00801e55041c5420020504240b4113172941044030034002c68022981042454050b1550f44001c049842500c41c2c03c0c002004c4010b01b6a000f60007220500c80011408602805841c0d80710303001a103141e070344d40c207a084902206604030201161103031001071280020b04581400e546c0c01c0e40c3d1758104146050314050284a83d611408089050031030521600d0722942c0300c9504071b0600340d0b001c03403001d9881e1504004d0380c100e500000c9980d0881c5080314480c0003c0712075101c14249110280c425106002810303600c202c84281c0070340034160000002540c1c00d1141301c0010207441410b10f1501141022000c4103968080813585109945c03900300860544242e9847c2507421035449105081c85441626116600041150041200b44921100030a4841040002c1c048112841d91100c0c2c8941c5000109403500c00207602c00b0050040040500c481c00c0c2e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 740231663 1250 740230413 740230453
    0xc0e15090a2105060708040515150411090d150f050603120d150608160201020f180303090301140a05060a0b090907110d030f15061b0302031309060e0702 67
    0x2220b00ea41d040526400784800200314800210091a5005036410040c2c160781000341e0034000c0d805002216aa02c035020389600c80101c00703440e14102d0441014200d94145880c2d003140145048610110f0705000f42040801d403103000c0058210392506111820303075911750f0b0500c151007030402c046c170092006040040c046601e40c603000b9014003480a00049803543c2d00920f800612240c00d00c02d12000031a0b55410005100d08c0090310b0005110382681d0800c98003510500980d050044440b002520381a0f40009429110340c1726040aa010700060000655554081c07003840d8403050440e4141c1040e2030b0002e601300448100130051449851046d034140a088100e2090341c1d03e80b00241c0301c03903005494a140030b603488407001000070518400c0080e52000a94150000035115015100c2800541104441c4002681d0580104000101c545510034412100807082a00c50b40c0240140d0740381800f821010b005000c01600200c440c9038541004000004904a0b0b0035400203483c8084c164002c40f00f0242e503030032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 740232913 1250 740231663 740231669
    0xa06060503400308061206070e040e01020c0703021002010e0d0809010f0504050f0106060905060a050f12070e180601140310170c040c08010324020705010c0e15090a 72
    0x14180164201001424180200c0300207004564440b050b045800301d1202c521001220450000b407041c000b098a80c01c0800355201104c0d0210082d2a8595079088200d5080c450300b0003003540251a0062515580420700c01000006150405004442e046005018010054106410841e803401c0d0740d984103d800440c103600d200190b46040d913074549030140d0f514054007000845480540c609001c2c4000c000001654a22101c440340081c800c4564550701582c1c15140c9119154001d1000c0003840079140c880d10050103400002600c00382401580e0410703241030202181d1000114405250f040d040c0c0c50035466005403981c1c41580d103080d074a040f0000919040400c060454412404004110a4071310152002d020f4054158150500940344442035520104440214086c920f0402d05100940c452440360307050307a4000e80394004030b100c42d00300001902d00030898100690760a0001c100064020f0103021070006080d90303480701c0300c050b842c10044200c0d021203030b0032210301d8100900c3e00c2946503180c100c421 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 740234163 1250 740232913 740232931
    0x23d020724030f020705030c070501081302010905190317070302070b16140c060f13050d0b0403110c060d0c02010b190501050d06120503070b0919290106030f050a06060503 75
    0x703d080c200024080e001d44400104a40000305541d4400300000907220119a8260b8030040c568462146260030f40d411100041d00081d003030b060610650038030740c552005148012445444459403a1200c1c1260407031203081111501000804100b40365040102402a00b01c01c035078185050600c140c840186084088010800546000d41000408003408260001d11002c1c12003580c403505c2c2003250201d40d0100c48900d0400f002e03094042403c1c04c0000752850139a0f0300c80407040060f1241d88090f505090303801608030300c40c821105e182640d916804c0251501c01c0e442c00000c1400e1602d440c003e4292204091070740d0085a20002220307108030303480c4040c0c00b2910300782040c0360345010020180001d4019500f1801082003e0340c424000c000d4004010100a8081d4448a1140d142c201c001500c665519030144c2485100045003804504e180b8081044900c0d0754945003810032844500c400519000d0384105d01090f6100c040e1001e01d9850700420f64070244102c0d040048034140f80d0017070900e0001602c00c2c42 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 740235413 1250 740234163 740234171
    0xb06040f1203140f0a0201110304080f030411031212070e10031d1917072f0325050324070504180501060f05070b04023d02072403 57
    0x249405580d204075600c002189160f500d0400359032913602c0342d000140340c50041d031030b0400e850319000089082e03d004030340c801241803401c0103140040131941c202500603680034403140307104101640c0806c4001502c04001007803c0c0c544484030090070440e080200084144480d0003080f0302d080d940d418100e0b904400718280001e413529080c403690b070402142d11600100f4410b402701d99681c41c1558001c02c80c03c0d889544e030280c00d1044140200f06900071403000400c0548004020211004c0b0200300d65170030460740d0401e110081070301c00042c0c600300c40725268500480c04680044a000300641c04103014150640083c03031100e504030b40400c499190000d008203803840c1074011801083c030460803503004003040301c80b0506030301c00014800c005000a09c02c643c0400c404d50001e9100600841c26251000d410050103103007035645400f84100101c4080d0000100442c00d06038030060b500d000850340f510b485050b24038200e60083c5002070715207241074000351403803140c5030707041c0100c000b200a150b81c40b00d140d07190102e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 740236663 1250 740235413 740235449
    0x605011a0a12110c0a0f14030a0903080d2c0d0e0102120919060207060909050103110d02150708030a140f0106030902010c060501090203060406060e1e0d0606080a060b06040f 76
    0x30500340100c0d14250018020f5217201018800398070060000c56004411001e5440f560600e066524031845a4034000702d108900c0803c08594910b01404c001402403501180c00b103000c000241d84401c0807241c03071100000010704682c1d004400c00414454140038105044400140d10010303580300020320550503c0b40300015510071584425103440344a004042c1c0c048095910340602179281c070114007030640091000c0380e001440c580c1e03c0c002d0a0490742c001c8221556184800c1c180480c0f118410000e80e000f8404021200385000d03008010489030780104210b5880c2d0a000d1103d00544401d0306c03001019140c1441485000d981c2402c00301e0440380c1c54100021107541c1c41c40141c0d101085c0c59001380000349003000010311380c2082c3e00258480c4004890800c541034481c001a5150082419a1034000d01022101e050342032000310102960f06008001c0f4481c030505560b044192519a00519020b802c11301c4450300300903a6004400c8001012914141424140004182c90024a20078000805440c0c0e01d40c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 740237913 1250 740236663 740236691
    0x1505070f0926031312200607080a020f0316020103060509060f06031003061422120e030102090a0b04030b151807030e060906061302121308040f030605011a0a12 70
    0x40da0403021013100550500e0340d41c00c1100300844007a0050340c84401302c01e0450410101c0440e034100850b401080c942c02d00074030b621820302c5500002249019031041444070b15a41c002040645544800101c5401800119100040607034910b40d10180c0100e40200c140109a514680540c1500d0000c2d905a51250340c0e4864920fa880103d600103080075203403a134208051500705c10b43c1c6103c2d0500115103072501103102060004080c08080c0130303159010180c6044420f03480303840382c284110030080000d810603c0c0700c000a00d020b11685d0020600c0b460003e0100100300c09444082da110318070a09088088885c2804103240c04140032041403135000060004103082d0081d8400200c0800381c0e0210341c0b161811400841e6298403d48109200d800500d000d02c11607070311402110003040e10b00c04205002d84842c0c00c1c0a9100300c040d1402c076a940c40901006ca040c0180c061264001c5000350b1001c1420351401c03000c1c0f40784a000400310303d00c950042114003c0e154109400c1c04410340360400000e501c001c003801d8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 740239163 1250 740237913 740237917
    0x103030f09030b1905130b0a0203131a04050705010224131a0f090a030e1c080f12010f030f02010c060605060406030218030102090109030b131505070f092603 69
    0xb0320480c030800520803800300045818600d000da01c4d03070811254035441b1004142600915008001f0200400050620200d40e0041d41d0001114506061a04801c1e6103150700e07184400400450090311000b040144042004000d004040070f0001c1c014500700300d0080e0610012176078100100e25007003008035081c1900d001e40c0c245400c4d00210a0802d0016500790140c1048007034900c0207125010202140401c100070550803c01503040d2034142c611034444040c48010f002076440480c040740d0741c1c0014004918428001d00a6031009041c280d9110100d00480d680002d0603003107980300f0601140c2c144000354103404e00005040d02400c2010100c1c5140c60641c0141800c1d0704044d400c900c000c140080d1241d056009048014244050601e01824001c1418200d0207a540c0e0a800104001d00401c082032183c82581d400c10554200300c0078001513519003c400511180000600a0351401000441544600301c001146c140e890030340d0800d440c19141002040410b1031a00490090040c0794002c2602002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 740240413 1250 740239163 740239169
    0x3080a1a060a081506071202070501050301140d021c14160608241504050f12060403120f02070b01051c0302030d020f090d0b1f05090c090613030507050a09140103030f09 74
    0x104040da50405407901d0310b8882c031201c47c500c01500c1041000304980d800f46d0203403816244070f00590520ba660140410004041981050340c0040c60700d01c029506181400608500c00d009000070280290f03901125880c1800f0800001e1b42c000c20703c881400b440da88003120a4100c52034290252118520803a60030401001500c255030000181c0180c488401c00301e40074000f21a001ca4020700304030b000d4002e000603140152201c00d1960040000100040d011324247c8040f00c0700d011002540303075500003112080b079000344801e0701c400701c0b2480108007502d00340918001e071600c1d116003a1503000709950080d6a0303006108803182c070150045140006d604440c8243e401e050001852005d0303084aa007000108001c080e85e8000311401030092000d0301031800301680c01160350261960181c0d41da100c4118459411038000700398802d604001c14049401441104401303140070f0009403400d42d1030001040ba080750303d5480110400c0c10f000d64242c1980c4000c3c00c85044a4040c03c1944c8035041d0700b40c0c110303140c0758030f50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 740241663 1250 740240413 740240419
    0x307020d1103241e221a0c07020f1c110d08040f0806060d030c110604030203010f0c0f02071d060a0e09071d0610110c03010903080a1a060a0815 63
    0x10140a03040c20460120900136040b2045070707004807608035034084005904945210b50950704103444050728040010484246005000041c0080c0b40a08050f07160310044e6822004a800490440e040d840c042d15200141c0e581112178050036007058404184a012421000e4103110600f2540c4d403568481e40300420196903c1491550303a540c8414810140714424001da11030b51150f4400140e283c00c11030b281001c0c00d83c05490314040070005a407101d84600d401840346400c01d800340030000060320309002d48481039080441c0031070460400e800052410315152400d0085511a440400980031040684954043e00d400107070107540da5603000c1006580f003544845210141801000704270a000f1407080103648004240d4425040720103060304032000c0c2940c00681c0040034020701c45000340a11100584401d1200503500c080369100006421915440740c02c0c0c1c04103008008002280c0038600c18160103241f8000d954440044031004290b89009001702d00c4203001b44900840e050704100980000100002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 740242913 1250 740241663 740241703
    0xb03030d020c0601080f06191515081f0911070b0906010609061d0108040c091107110603010b07020d05010213031101030507090b0306040903090803030a15080307020d1103 75
    0x329448500960007076a0105440c003c040003c02c1201c40810170000b000c170908020701d05034451864684800c656010300c0d100d0680e50361001001c081c116103041009001641c0d0950302003c00b4003010b401103000401c0503480d03442103da80b518098120010400340d42c2041c100080e4426071400c082140d104428014210510a07820003880d0000010803506076a50f9540300c50ba0360703998520a4400007580d1000c410102c20700710109516510428103d80d01c64018810302685030364800f8181c080700c14483c010500c0b40c0340025482d040c04003060101c414848180c429a01d150701d0100c588001d80500540207202e203400c2010581480000d4054460303000c0c0300d0f640188110750300d243c04540c0d692070041e51170100b41440c0001d82c030079020f41458411140036040c06851503841000f0003000300103d150485c20b001000001041d080e4003000550310030015140700040c0e0b42600c030300600301d054040d0300c0308029501c01c11103400187c1310310914000e03041e84500300700c43d902d1039480024206031030240602903070185 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 740244163 1250 740242913 740242927
    0x1a0601140d0f0216020a0e07092d180c020a0507060c020604080d031406030a0506070509190e071b03050405041508060406052217030c0c060103080d140402011b03030b0303 75
    0x240c0483d052040707108440d8900902c0c0d65100311f07600c9000441780b90021418407c02040844104a01402c030f4030800f1907230044080c080c400400101543c0d80005082a10b9501045440004d5104100c41512940000c2c458858255038640d5594128000c0604002400046000319100d000c140c1e4060032981081c0d540400d0f100307034010000d21500813134a07a07591602c070100b40c141c100801c0031031803160000040e100d582d490800c141c400d039220406160f000404100c03040b510301c00c5580007502030100c03100b103524141410000182240c1c00c00642003904a85406001d002075044001c56044820030b55000c5075941c504900d00c02164501e078464403544c012402040100704096005504c50708603080d241c52000046201d01411940411008001d0000780701c120290180c1000550307401a19401c03141d1604400160060904034203a1084510303030408584d15038124400e0240342d104001071920310800b80b5007500020030807180ba164418002201d01c03000001c0c148660084800c1c41c5018088a659145e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 740245413 1250 740244163 740244187
    0x904060f1517060f09150705190c02030601060503190b04020417210c030406110f07030b0106030c050f0d020903010f18020f030d020c010f02070810091a0601140d0f02 73
    0x1c0428409080e0103203c00003032102804900040c0104100802043c401c0900b445051402801819140910400b03009030103c0c4122150f800039913030b25075a901c00e45442944145440c0410680020301805401c3c4200004212840084400002c114001180c0640d103107010400030310507604030b4414003507444078401126000090f44202068811200007410000d20109003560103600307910b40c01074004000405c02940f080c42c4044a218103038054500780903c0200706481c0440503402214603a00c0311004000e029010b1140004060040c1040ea00c0e0507074140318540300344584200100c6146e808900d0f540d107510250300c4607441e05a4010108190081d0500b08040b103101c10100328403036440c1c1105504603090100f0b15407061440c2c0d800410329104440c0056641210305614001144242440005c000c4002c00415000301228003000030950604d0802001c1850180990400c20010206102c1d0b41c2e40d009010074108044070301c0c0340e51680308100c1a46c002e040034142080c1414004a14261001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 740246663 1250 740245413 740245439
    0x120709030203100e060a09020901060c0309180509160614031e090f0f07080c1507121d090f0f0a0e0a080408010e060c031605091215070e0904060f15 65
    0x1d0398207003203d0880e1b50341940c04042d02c8800a000350003c0145d0300402c8164058011101c0c4c49203c0d040044155880d43d04410348400050a01c04006480f101030250909044c090700040c85295224565001d003000d00180450000c0b0f5480d6070301e0080000051104428146a90800321004940340da46003084d80100355242c8610400c840ba078050705100c03140c0703480005042c0044484910281c1106c2c0880f008110220301c0381035081140e098100103c000080242e0901801c095040d1100070b419801d0701d0031ba0180502d0707210071a000d0f8083c0c1007846100c076039500410742d10201c030038944102d03545c6943c142d9014002581d100d00c1648038a41e044010010200d001c1d0040e42c02d010020000c0039858000140c1c0d400040e03c05550405003003008c03410829405c81c0003e1000503e04085182c07a40e6640410f0b001c3c02c045501c03118a400c0103010201c507104060405411981078070f019409129000001903071450081d2008218640e11032000d0f021002d00d030020b07194000c0340031504100c0d607521140b018801e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 740247913 1250 740246663 740246681
    0x1c11100e0705031617150a021c0624020c041103191404110105120403030e0c031b06031e040b180703080f0307030914011a040c0512070903020310 64
    0x78000c100300450b0034280002c2c1100c030760070700c04411041117107440f210365100380318814014818020102030150f10082005410f0280c151382800507950049030501c05030810b0a80045040142440c10030000d554801584070701c44500c0c00041d030071060070607105071b20704040030b1015a009801c041c00c130602c040601001d1846020790401c01000313501454580000c882040591184440405021602080c48401d010706204010f04180b4030301568103121291049040701c04400003500e0326000780d082681400300d581000d2054004202180806d004d4500c16510f11006034001e040c01720028026442034014144107940c1954920203d00b003505011060010441c1c0c0c2c6101e00100242e940415400000c000c003c80360416907603401c04c0705040008900c1d80c40600521f003015110780c801d1006c80d8010170725002200040740001549020314400c2c00b0304d8507595814910451034845180846a00501190120203000e980c040d03403940d81c0d07841a19a842d06410280d09031040880401c9208200d078061004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 740249163 1250 740247913 740247941
    0x10030b090601030302120d0e0102030115020c0121090204060302040f05100e040b010e19050a0b040c090f030b07091508221a07020a06020f070b0f091c1110 68
    0x5656040c04103503407941c0a00c401001070b40110780340c4e04003038040b5000c0d2801c80014200810745402e488101c031b003a60821380040c00045452505ca9642e00d80402005c90071003401e090500c540e1800d51810b01802000030380b010f1001c0d4648200b24119a41c0350320141c05954014402c00c0042000400c4c2e030000d200450782c141001d024448085401890324012a108a17448a500c40460f070801185000f081c0e805403140b21000400140e030181e0741080d004261151490400000d4280800d5040009580c0318003013010601c0064041441411940e130b80003400c1da83c005520750700c81d4403200001c44041100360700c0008008259000c0084265000310a41c0c092580110b10a0102001100b90400c1114441d401001100344001000441c443c0382c0a80b6400600c0e030050720510445038440209070703402840880c0040c0300015006040040c903200c015040000c003032030341d51281b400840c0750303554503244911000c0d42010354118406407803055000f40b02c094900e0b0b003917520500070003d044010302003000d1501b807 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 740250413 1250 740249163 740249183
    0x1801080604030e1c03030908041203020c090c0c0c210703060f050a020f07030c061503140118020a140a03140303041a191107060509100b0604030812070c02091003 71
    0x244901d40700140c00c13400a44d40d00401ca012900c1d50b03060780241081e92044900304000d00002582d407041d00013034041140280c01800100000300b04020507040000c12462080c41c2c08d01190a8282001600d45440c41c01070391742100280c50100c148160402c40443d401092041440200400805030002c03a9528010982070080fa151184130788144d000b14291032030b460310207000020220344280044002503010702e000040c20681c5a0054448070300d550015600701c0501e411610482c0424411162804641c00e61851070300e809a0006810400354491010000c0c0c0024140c0c1c031030386d078101201c80156401301100d222540100604c50b12504120340c2964080315040c00c013420039802a84040c4100e040d00311a002c0c5980c0415840f0050944101d50000b69038240406400902c40f403040c18000c0782040d00400001108410751000d88094000450280d4403d22040000400000a0791140e00204114804907030320182c040700c19080030000a5441401c0300c0c20b002407441c1d200c0344181900d0240900f00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 740251663 1250 740250413 740250437
    0x12120b0102010612031805040c020d09080606030607140c01150602060906070509060a0c080a0302190f08010e06220c02010f0213050919050901052e14180108060403 72
    0x1e400c031000c0d4031400c91501244564600028450408080c0d104810118006025150400b0500702c0e2001407509000d0b90004202070103042d04070740080010459030b07006200920301000401c1d12090040d0a0800f40045060542c200440e050195010508404002c000400380c0c20300e4106001d501e4031807900903019800c0811100361020840500c54001a1103061034900c400c01800865801069032a0401c01100c1300000041c010100038032400002e40e40142e2a009580210580f44214100c5c0509024001c50105e5566810580f114119152910717411265625800491922110350400444100142013801c00d055100e61042c224510164020001455007015036002c0b446640f051440348032290404011500c0e00c044034581c400c08510316030b034130081041d890200380c900540301401980d450760100030310110b02d80340303e13811082e0f4610141500c18021507070111121040c0200058450241220307a0262940d00c480c6251000041c450304266035144da01a032641401d031001c0b0002180c2d20350342 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 740252913 1250 740251663 740251667
    0x17090a1a071d010905090a02040905131515170120090d020f040b0d140d0516120203040f030305090405090f19061112090c010305071704020402040312120b01 69
    0x105101c1c219079181c1101241c00000300025903034402c100b181c1048480c0c070002c201c0b80c40368868140a04103005000d0703203490a0900303401c26158000c14a01420741c1c0800c5070b001040d405204000e42481d25140040e03141c98000c01c0c455140210f0f0014002c03940109009081c2c03400560001d89088064507000d5000d4603e418249824404c0085095009681044180140c6000c0c4020743d0180001080015201d1074140840c1c3c041c0c800340c40588811103112400c14174024203109100ca00d00c400e180c500c4c41c0001161000000c8848180003412400c030400081c00e800d8020411540504145442c50207059528a03000b0f06680c072884001e0b01403424000841e180d0680081c02082c2e00703c148016281342240e105040c480c0d9041800103607801c0361039000e009081d132019030046c40045131503000b2140342e00e0582d07410ba1920100a40d40c4d81090702d44401c00c880b980e4807080207001e5058400a6244984503400018003a00441e00041c0c0040e5014142020307880d003101c5401e0086500708c0c000d02000c00d02d0401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 740254163 1250 740252913 740252963
    0x204080a060b040c0509041d1603110901050d06020a09081906114603052403030a0c11060301081e06011406030a0e0105040803180c030c010f17090a 65
    0x1344002041007032000d4007181c940b5800c20656504080941c200005546030001d2410340382c1044a09198000300050042c00b444242080124000b030b00c910000d0b500d800d000c5190301905003000781c030860b8081010150a44280b8800b00208410400c649100c0c2e40c2d0015603400758589030f4201e4003d450082403644008807101a1481c1601440d98810921240c0202071232610031800f1305807030f0811349c20750000d280d001c0e0300d0380650603403072a0380002c0c4a24180c4489040503480c030b143d4204039107000c200d01101d950000102c81420362135280102c149002854012100b00300000b400d41e000c800480003040b00784002801d1000340b41c2c07541c120358550310040c0e0203540f6500d00303004059180c030500846100c2c0703003010002990052511180003800781102c4a00e14210b0708261000c450150000081c0b0002c0032000364111320700e40004000d8800410075000099640c8252307032400b0f060144483e00060603a004e640002c40000e41c0c90780303011003441d2401c00a2745840880504a61103c05d9440314010841c00340c0c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 740255413 1250 740254163 740254181
    0x1e08100e16030c09081603110616030e010302090406080f01061205060105040c11030c011509020405010e1908100b0907030c2f0106080303011d040309120f060204080a060b04 76
    0x540c0940e101c00a507011070182103000441014000e0702a8002a80c880030441d1110481a0016201c550750540c50203110028502c0140d603c900d0342885801c0301d0291800150003800c0d07150500d10010f050300f83c016006030040010b2950311070700e40100001c9041c0c0101c0c0360121100740d040208903154a03128180e0078114403c3c806080e5034000700060000d07041c00e0b03001520b40802410000c90355071915824624552207100001000e9448141c130f0482da20b070a8a91501800b07922205505080c103120000f880c14161071003291084003070031900c0302c04480316404080582410002e03100d1480144101e40007034031a491043d030088a011000541d0180320b40314030174602d06a6659210103001c40f5094121500c0c2e214001c0340c151240078141070710042c1c248078440007000c422019544135131400007003508a11070300c9503140c43c140c0c2150400000951202030380094401e08e5040702d020000c1402c00c16008003044c20001e08040c400a0040380601000079071152482c0710750414400c8405071010f1100b5a03411342 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 740256663 1250 740255413 740255431
    0x4080f06011a03070519052a0a1e1a07080c040311010f030e16080601050909060612010902060a080a1505100f0203091905030d03050601021209011e08100e 68
    0x42c0c0e581c0b031500103842c01140c01c0a402d2a00b40c0c18503102c40114451040f8442c03102d0f0129900148103444005042400d02c2991004408d00b0302c00d501c803202c81916000c14001c004c0c0046503824034582c8a01c0d001e415443d41036080381564210b076031070b07001c00002000155034180c04150380b6000038602c3c1903004101c0f002e9030340c00000380004242d40c00c010340700c41c03400d5004141410740f07078280042d01307840411801c1d0340d10f04000900c440c01403515614508103441a00454040ca10b9034040220541e4001817550300481c0603143d02d044184500c030701e02d0040000580c002e45c064000a8a800300c547d1004680703002d0f80300b0034410400d004007000030310703070621151103425000041840010314240c060305100585905c24015079103000100f40006000c2c01e802c950303280640300b00100910031810208011009031850b42402c02041c105000042c2d03458003100358081f02d085000422060300d901ca00c808402d0145409003400d07a0452a0b00090010703082110f0303050302143c1c540c030000b1f80b10240f00b6505020310001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 740257913 1250 740256663 740256689
    0x40f0e04060216110f01030911010807020312010b09010906030c0e01030506061c20030103110609040e010e06060427082b09020102010c0f0e19050402070804080f0601 73
    0x841000080518014800d6031010380c00e001e51011160944a05400d5503c40c0e82c0c85240c02c0e00c0d903403c00c044400d8040b82d45040529215620700000c0d1501c00c41c00d092407090a240e009961598400c0307107584204a04010061050400001c41070344c1c4034041c0200c10401d032922100d2a88800301182100c6003034580c2d01c005010400d202d40c0550107640105e80020020b0019440c01e507407a60580e030b0098030001c5041d03400e940c51258035500713107642030301d4001000044103062031945107480300c01d0400d07040c590703040c8078600000d199680c60766240d00c81011000480024031040100ea4404c41e2100c0085030010300690500030340c8602215a003022035042c0144200c50802940c2d00d07180c074140c0d60013800308601003200d001c076a9120040000444445945c0c1c1d9040800c5100c8184002402e4440550f51101402101036044c90150340200320050040d4007034402035401e0540200484a0550a92005400910005042082c004e2080081040d05c0200b0222080c056582611907a524000d1094107002000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 740259163 1250 740257913 740257919
    0x30307030b0406080a0f06060e0906182a130c02030a1101060512030a031812030905011d0a02010908031305010507050106030804060507140a120c030c140a1502040f 72
    0x20703446421081000340c40058016160f40103c0e02d0107091900a44640d0343e0388442c001007029600801300038200354030400c4c1150400c41e001e0341ea074160140443c0b5402484600b256840c030b200700b1000b0306c45074410304095034501641008411240e0320650f038600900c20050303003a458903000c1c003030107000505582c02149007015010307089602e0410001c00c441c40b0754a0b030300d000802e0380d0307072940400504a0b9400a036917111043c034005404c0f1090302001160a603003185a050211380140c603101203881a508020481101c1454103074010300e107240440c200101401d000f40c2001000140c01c41f01c0074800e0725500180c540355070300c030b40d23032405246459004450412070a2160b941306d1006003001c64410400440c60903100e40e071340a4150800d07086400010404500c04050008090b4044030360b0348100c01038003507100307561902d18040040c0c412240900070b055092000300340c03045038840300444c0c005120f100c00081c803101ca5611115500401d59070207a090b0410340e400d0495200711021152031480c222520b034a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 740260413 1250 740259163 740259167
    0x6020d0b18130c09020c01020901020d140307030c200d030b06090f0d020136050105120c09030c03030d0c02070509090604061d0313080f0c090c0c010618092102030307 73
    0x20012044400740700f156400078680703070300303001a0080d8485900050385a20400700020315040e0208900d1040281006900c00103000040440341c00116515010031030040d00c15040c0c1742c480500084440c00c28070b0501d010130501011508a41c40741d02d5a90a22a0160b030000300841da024104000364414020301100b5501d161500a0001d80e078410304002100328150b40c407140d98000302e44d42040001c1e200088035a060a56111204050582420031a080c0500034a204941c04030051004006510005803081d0b103950400a10114180080c00c07a0790700c1c4259401440548400454600507208040c400724441ca81440c916100d1100b00d00203000c0da07a510b0310382401900510844030045090b54035030762032505050000700481040c0f10441ea08144c0f40692031450191200c0010209030842345240089039280141650803840101100b40c840352044451401030407a80c0c0000c00007003007004105c0040585401400b50706014052544181444210101caa8054030308484010303002040000c04880c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 740261663 1250 740260413 740260441
    0x30405040b0d210e150a110c042409022805070c060216090b0307030312060f030c1409060112150503030301170106080706020a03081b0706020d0b18 65
    0x410010300d0b03808104050f44800c0c0314884010780742e02c40c1c040c0c2040180c2c40150801410048018141d42058003485000109410f5010702e102c02c01c20031505400b4112401e60810210086503c000d100300009440103a50441d8000700000e400c0c000c100301c1c480040d5961062083d0b400c82402e03000b0805038881080802440000b80d515000d007031103020301c44036000c0707201c030705141d0050061900100340680b0a07115010808a4540c00381c00024200144000d01d62400301c0e8400c200c07507050030448854283d941c0b00e24054034483e0040c4090403c091800018444411084011200d030300340c604480080c0c0c141400042c5104132240c9012a11500010906c2c6c1240e5009080f80014581e11038030044d16400080d056a0007a030180003180f028100d0b50442050030711614004085110003402c90b28a40781c006522a2140d0b02c006e0180015100000c00740440549001200c1802807013840d602d800c3ca1034000001d4100e00200c4c040d0a28152081d6520b0034002c02103e00b5000c12103084d4a184d8030218016841 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 740262913 1250 740261663 740261681
    0xa0917010605100513270b33041508060109080a0c0b091305042102010e0d080c0c010905150610092102150703030b0d0b040b0c07120f02010b0d0503040504 68
    0x1d17065a0750001041085556100e50120b5403500300114140c10f5240394050300c55160040d0b00c1901e88044840c1101c03e80c0000c9642200c05c2d10b0408151035000e80b492001340070715405182040900701d40707600d4055201014510601d000d80382c0c1e0701d94617215225250364500341880103111101c5d845041c46045038800207010030b0040113021221346020320035040141c0b50191001c40d4605400c81d8100d10f01c140001000c442150b092000300070400401e010345a58150000803c0705010012010612407035a0703004464031480504001c0c0094101440d08950b03d4a41c0400f04402c445440b0105440d072500f480006401040740d61150009403d0400c81040b00c03140c440103801c904104139003400141c03078030396003121b5601c25204c2e040d03121107213400c01809030340c2e0000b18588521071940c4110002502d928403140c000b81c112840c40705a640d64007840c1c4913440f9115015001606155000c0c41c51540148000c0c00341060340e000340100c140c50340a12454034180070005100b50401d02050080d030606034003003451 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 740264163 1250 740262913 740262937
    0x2010b06190f261306091a0a09020d02091312021615081801020904090305090f060a050f0a09030f151401050a50030607120c140a09170106051005 64
    0x6041d15602c03c811130380c1506c03040315411210340d554103031586101003055224844140620901e0a01e03130002d400c4240545000b44124182004101d604400e034000441c819070044c04146906112403010f50b84074209038220817000740c110030124040c01140850340d011001c64031452420707121400000607084040780140000c0d907080c0030800140c4c2d1a4080c440c0a10b009480ea1581da012280138010200080000340d8000d80c010030a414170395500c80121455008404040c3d5150200c0d218200e50300749040c0d00103082082101000d409011031091410305644040c01c080102e030903001101c039245902489140e0340004c048e0070030002000b104000c4c40d440042c090f0b02050303000c01c08280c00c1c0f1016648400002d14500540c1000c1039201d00100c0502d500ca003200104160b00d42090003e01c1c442041c2c16003c1c11070f03180d100c02c0c2d2515001e10980880208c0000880b0f480d0410203200910340344891141412040d10f082c08805c80710418032420080d51006404034454981001d016180c80e488106808030b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 740265413 1250 740264163 740264191
    0xf100809011b05070204060f061407151109180601090b0d02120115080907030206040b0a05070b0906100501181e03060207030e04060e090c01080702010b06190f26 71
    0x149449084100350000c000b070f40c6505440720003c1c018002104d000e1b412481007107009500a000954000c1c070b02c15503544000c0141d40d0b64401a103805002c03009050701c200c0700c3c0317418100312180c00040f05010308030401c004c1d9580b80d40080307004000803240f00242c0710345001c1010340c8014000c0c20650390052a403901c6141e0054030300714200340c038949403800c00d0340500507241d0104024032100d40d001c0140c0350041c03988002001602c2c00c6800103509803003541300340c141c0c05d5000200401464058820380791041e0300403031005c179a0319091058a44035030085800000d0141452404201c03036000310b40d15041e6140b00c0c14019071182c00c100b0301504502d42c0404a11f00118030b5080040000c80724001419a144039645824034540c407007040c030003618099085000208a01e03420800380d060300142550300e284013403922030080c0d00c480340160700601100402503000500001c10300075041c0e0600c0c1500300d2440c02e55403188081d454030b01c2298654200e07200c00c400445600000e112100544060642145056510708 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 740266663 1250 740265413 740265431
    0x9060614281115071106160f0c1203060806010501170408030405010605060304030f0306050f130b06160813050d05070603200c150105060c0705150c01020a020f06060f10080901 77
    0x16241c80c0103803c1c10f01541078903900708080c040c0c1c880d5005004000d004014650350800c2170f949412032411500c1d100c2042261074000000310704ca034200307a8050390401420504221550f07801000740c82e450180701154490a4000552940300d005910f21074a1280d6500c80152116915855280c1c0050001d9442d9034954a0103c0c0c2c69031030320011400b851181d11440c2a9104000780541034414940c003592045140c0d03441c407a41c80d01c0b441078000e44060088800500d02c3c180c0c80002c1c03501d0169854240c00b00c4011100300040010083c01440032512000d52a20001d075200100007501d80300250052003030300050820040a40650443c12003400d1903c1d05940d506c2d440c024139180d980140c0110011070384000d498a028655882426002d450309036a404c0c68450300104150b601c061310301c2840c0c000c0154480ca04401e2010700107a5035420701983c020740d511029074400039034070210081c403103a65019040c003240e0646014000d07807001d601e01921100c041c1d24404015600444014034507005952904004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 740267913 1250 740266663 740266697
    0x9020402071406091510030201050d0609022d070c15050c030a030f0b0907140a0207050409050c030706170f07110a0507060f09230105070c0906061428 66
    0xc801240d80a0003c00007858400c1c07200d03250510514060312148290828800c500c0380345a0300100340c0c3d0702030038a42d90715054010b401004241c1d940c03003801e8091000c995540408040754209031103174125205100114180107403100644030380d4000034014012120108142407030302c80d00603100b8071641010b41c24103503c094540c1c11035002c1303810000080d50750a0f10103041403042c4501642580d040e1001c4c03602d032900c01c0780a000403050542d0030083c540d01042184c0f107e0700c2000440003038800a40180300c00051464041d0303980c001461818880e000f80c55002c1002031141490607042d4a40400840081e214154080b5001801401283c01c0240403d041d03216540200b00f071160184c881d10050009030700c0c001d402004007403c110050704002000004001502c0301191030b2100c8821f124403e2150440c01c00169070300d10070307018010070510214034002110b45a540c03180040b203809495040c01e071810b105c80c100c4103100b091041490581c3d1305405d54080a2440654100ca40075420f05410350320490400f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 740269163 1250 740267913 740267933
    0x806011a0c0a0f150b0f0f0301151203020f16090c0c02091003031e091a0702090c03090c0a05030628020f04150c2a091805010b010e130902040207 64
    0xe4802001116001c410130074000180b0040710900c050400c00f04ca40c41e00029100c0300c01c100583d100b001640d4200c1906c0c1d600b035004103a0054800c051035080760b680c4c1c80d0310032030b0b001000f4241c0160007080143c00040b9404901c0c04e01420039219103004c080c0c02c1100c0e5000070a0105c49400401498000d0480183c6884d1940c60040001035100c6108615511f401040007072210700c402549400d00c1f071071100c2c9642181b46101035a44544c3d50714103420400d299050107020380107020f9403010f01c1100b880b010403510f90040d80141d2146098510307890115041c0117102d0050720541c0d4141d8090300010b1014801c0c2d0071541103c0140c0144000718581300031a010903a00018189801900001001c002400d01c0c5880644a1a103d0503c040040b402e520b0380c0701c41c04a4040241a25000c109080c1c0186200000710b5000c0c1600f20420000c4072002d0120b00610400202e0807a0190701e80991120380b507001c0d111681c0780e03660003820750002c4078030401d04401810100c40300700c0e081a001e00c01040040c6600d40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 740270413 1250 740269163 740269183
    0xe16090506160506220b09011803090306060519060e01030e030a0f08061801060507171308061b030105040e0c0a0618090c05070204091b030c08010c02070806011a0c 72
    0x390028142c450b00304603041c00005882d03080200302007a014481000852100840c0c05c2d04901c081001d990361401040c05415018500103176400140140c40030140c11010000c1642d000e40000c101070740d103a41c180040100d05c0440d10071208149081003091a03c298000141208103250128078008a0000703240f540d04290781100c0490030907180c403548558020401a07124100300c4910342c01c07491a995518000c0010300070882007110008960080c4110391902412501050300d07000c0e5115891241c0004080c03590280350101c1c0200c8000c40d0781406c1c8000381404000060a4403807443c1d1a04081000502005406104a0040400c50300490f95071741c00100080100c2e85420b060010340d801c0344805911a9001500364a15046116006c25840010740e03003081c1d41500c00140c242d90038141114065020b12000c000ea035032004020003005409114201207403400030007070158580052060762103070303900d004096035544010010020008018451103100b4030941c0da451520300f0b0810700c3c609040c3c14103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 740271663 1250 740270413 740270437
    0x60f09010b3303060a030303020306180901021309050906062709011a150301140d06020c1c0e1f0302040e0c04240e01030b0f2d04060e16090506 63
    0x30030b140e001d040040d195103905454521103614510300304000840700c4142d400b0103010507501200042c02a02e4190f0b080c04150407520100d265031500850007400f07907005c4d42a0a50b03032103117140d00144000c2c01e40145030181450034043e120541c4d840003803040b10b514498075000d495182000740c4158158146210780205403500002c03440b52064506094010b01071640e15019034003c0c00c880000e645003806490660b0f62103c0d50100784508000000e03015106c402000d0300941c070000714940e02d500c001503e005004031200445003400cbd0344403025a540d620b0144d1003600401664980d803280920038803815488081d5040043c10039445200f40380240380304941700056403000103001c2c00b02440a240c0c0314604000000c000c820740700c0040d401000303940d090f10100c2c103064603152031a02541d0340729203e911140c00034050307c80010346100f810902c458000d90100d0724103c40c1c4045001824540079072402d03078124080211046d118044131040e0503401034680c5040210725100840c165032254000c05481c0100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 740272913 1250 740271663 740271709
    0x510120c0e13030914041d0a060629160f29100506090a05090702030405150a050703081e0114091806061201060f0b0415090305060f09010b 61
    0x185a01c040c070304090b140e2250780360a806041c00296005032078209482004075066000300c0750f0700118015140b01d034515250310300010700d6401c268a0029080746602d0003031205120266944046c8a644d10410218007200c0d084400b501170100f1901004020200d49410103e83c51156070b150344a403002c1c000000c64031800c51b012102c0c260698072080214800c1c0c140c03501c01c81424600740d00390b44140300d0b120b9035006400c08210610207a82c0c0100c40001458042c0a40101e07242826000f512540701c0d0003034920458400e502e40c0c040032820700540f00442100e480c2e0741d00e4140541c0b01619211401480606030310080481c101c6607450681100d402092009510122541d502c1c0030131010400046c80708080500280b0301a0302c004c0001201a00314400b40c881c49840801c4090250161409802003602c10f12008000a00840c0c4040240f0446003001e60b44050700700c0c4010211011700051001030901e0344081c0225807854890b02c8074542101901000040385501c2e007020448046919000402d80105 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 740274163 1250 740272913 740272919
    0x905122110030b01060314130305090a0e011509050922121205060405040f0201050904020d0213050109080f0d120615030f05090115031403040e01090632040510120c 72
    0xf00c105015040c6414140308000e5001c0e00506001c40080c4201c202a44408070322040c1030003102164240640903020300720031511400c24403a512020720400044a581c1e07418a00313458850740d860380940e01d0082c0300b10f01c1911580902445140c2070707245090410403c06070480041d1220441039003413181a22000040c04d444c017100c1c0211040202607500079030a0100300b000044000c410095840e0382420040c3d00c0b00f010b840850024040c1c440d00041662000a070104e20540b100c61030412900240d03210b03514075403a1001070343ca81d14004000b240950001d840003001c140203031090114114540030015580780c6d5040300c00540c0604145071408a56206152030b170140c003a000351903101508200074031072454520100c5040c40c91900c80504203100c803a620000c1d40c0320a100311401064802405d14032075860b460b140008285500c10084040e0301c0118003010315850854030740d0109400394000f80004000c0c002d00000d0800248100081c0f410030310046041032640f104411041e015960300411181 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 740275413 1250 740274163 740274173
    0x5060f1005030a030309050c0418120c05030a050f07021f030e0601080307020618090c030a05071d041518150b07080a11010608060106050703080703090512211003 71
    0x4406815480c0645104600380595100001c080c8031980e4145070004000c1800c3c20a903007403445a51800f54480e042400f0211880003040c3c40d5042e017805188206801c1c0c2010000f6a00d51941200c010b000d0340081c040381c0d10860080000d4280d50b03400c0380c840381ca03103031803a03002a05201c0300545410702d2140b10003010101c55410f00c00c550f81040401c00030002941000c1d02143d5901600700001e00c1008000380e10a1f070074403c44180c0e00d4120010313000c00d20501b4002810307a10781e001200d0300203c0700d14120018800d14401c5000030614190900070446d0036516206010150004c0d02c1444c1150f4448000011226004982c4000a02130701030b000500307a00358401e0001c501c003181d102c200f144500f4800240410340728001c031182011241040201c1c0d00c54882400d014240560001519000d03100c000034a1540003002069160b100342c0d10b4480d66526104203400312441c5030005000c50780120181a8400114401403c2e403200381d104079510041c0c0400010002542242d207aa80c01c04001e00801c2004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 740276663 1250 740275413 740275441
    0x501060305101a070809060a0903290c162312090907110f0a05100c030c02070306020a02160314010c020a0b060d1a070e090105060a1707090f030506 65
    0x80e100b640c960040c1e10b465a40d1440031201120041111000192501003000c0601180c6401d50060201070f00c40d400070001078204c0c11030344801c2d03811007007281034520070820a40240340d0440c1c3e402c0040c070700d54995a4104200d031300010341002e07410700a0845030003ca011001e0843d6050389803401803c02c502c00c860203c0c2400c441c448c180003a80ca0034405001142e40c1c41c565954440001d1070401d0312160b88401c0640340c00c00c62603d08001c0d000d071086520510601040d0041003501c903001c11300030801350302000c80c2120707102c540103001a004242d0a000180e40c0b5001088910710034812154102e0354101000684005640220341c40400103014800c10349082c00351045200d090f0015010114042e11200c0c0c03c48801001684102c8130403000008100105518400fa00c03030014280040b481c01c1c0d04082e04940010107034501c5002d0080002600b446c019040303a48400d4141d88040b08030611240d109480d01010302018288a21440042120400c1d10404001940560020a450308045081007901 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 740277913 1250 740276663 740276671
    0x14190906031e0e0114040507050f090c0703030b01091a0c0d02010b130c1205040b150402030c1602030a08071a0903041a03070201090209090f01110306180c07060501090501060305 78
    0xc58144668100e1154921455880454203071502060f07041c00d10341e06074014411034442021001194041c04103010b4001120000c0e60302c15111903240c010179030300b0001c084104452b61405003900704088400039229070132800a03c0c1c01810020020b5803100b060095040e210030350040d00c0d00001c030344001070107001c110528003600180002c01210740e000c2c010407501d0180340f0058500c60380f102d40450300c2d07602c0f90b80ea80003030b50700a1b84100290308041c5420403292201f40d51180c01b6000310380c0341801c646018800c81e4027405c0300241c280d140046000200e951403480305400d0780d25019200355000801c0c0039900500c070381c600c21514681d02d200e001134000e21004000d04084507607407050006011043e1f400d00c00350808600c607200c8903226520301104030f016000b000300c020340042c0000c007484601c4c030b00020f4804948403124024008030359440e41500c4903000403180c6c41e602400b44803d1204112601c0c00103600b1084d9149070f45d241a10688035079083c3c0e2020303444481d031165207070010071600b0740c544162504 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 740279163 1250 740277913 740277917
    0x906130b040507171e06060a2706020d0206101a0c030403210c0c0504020d0b03010e010b0a06080f1f0308070825050601030b100302040e071a0f1914190906 68
    0x40303c0110144100c20205c010110b41c0034140029030354400e40d0042d600148031030060760340607007000703414105442c000403944100f0025204c0d104034100098000305011b807250006052007940c40380b61600480f0410505c05000c900c80c10104580000d5040500003040a503014910500c210050501580d9441d06042c0c0880108000300c210100050600380014044a804841c0542c403103019110050007000d01e203500d0b561540c68003650700c0e2003420641080403051000c90714696201d41d100400c0e80d0b1180b080ba0706401c0a00e504c0000b8011000d080641c0741e06090000c213a89070780f9203035540c000e8558003ca00542e0030030f0000c00d200141800800320030360405605144640c400100d83d490030742e030703840601004000117800000515903088410030341d0f0086400910500144200a0030244c0b104401c0c040c0040e0845078100c4e005001e900c2508803516005c07144086440d1101c40030711b0403404004290810100b00703800c5208010042542e000c0c0500025844208040c0c000845025000d46115484582 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 740280413 1250 740279163 740279191
    0x60c10091415040f03090e0708060406150219031e08061f120c02010e120c070b0406090603050a020904020417010b03060c071113150602060c090906130b04050717 71
    0x408418922442c5070081d0b40711103c4141c0030703011726041e035564010b60051210214442c08105050ba400325855005075000e803000c00445440d5035032213a84010400183d07002d64800b10404445502e800e00105041d4000d28020401405000711040c20300300140c00080050010300500000b49401801c00e81c2d00c400405e4404c54011840740b01809076402080745501550380c07503400700b101074000e42044111070703c80000d42e03101010071222018140c0100118110b588251040800c819800703404841c161441500c4028540b40f0340941100640001804a52129001d200781c07111900c90b400640054000003502840c106203005000d0300b101d404800640c400c3d031048050000c1c1954402c00c541540350001d52900303030a402c450204010341d0410942180151800e48a03084041250388030030181d403015402d55051b600d03141e400c080e02d405601401580012100e0109078180740212003241c194255000100361007403004006400c8440482c0c1141c0401c03c0076108031051141c00070003e80c0705e60340b013001e00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 740281663 1250 740280413 740280433
    0x40b1201030c23061303050712030207050901080316031b060207110306010317090102011b02010501031b05012f0d02011b031a0909030f03091506180a0b060c100914 72
    0x107654640b07826025000d8240010203031941c51150314105d0103560020119120180d9480c080b08482960440960050154400102d0180b805148441c1260381030b000442c10108500c040048150800204906000500604008a4901c140103410090042c1801a00c404d16820652500103460b072103244250040e200500c00500c5040d1885030803101c10820540f60418800180c1c010625150400031039400303407821119407641500201d05a910445103081d030f42c183e0030141d42036025140501340c0070401035804481081e1101561103c0b1005a082017400085003402c1e03542130110980c15400181d440b805201c4000000326842991102103260800c200350300300c0d600c10581c1d502600050700c51421000802c2d0200000c1054039103004d150b1100d20381d0390403c50704803907481030004928008268602d00203401450b04c150322100040301c00c07200c02080c3e40c5482d14500184038031024240d110b90b0601082e80d603c00100f0488a11301c490b00b1000401003802d090a10010a803041400713196484601c0f03070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 740282913 1250 740281663 740281709
    0x1020601060e0d06021b0c060408060f1312030516021f02031b041202090f07051602030f030a0e040e0a02031504021c0b0406050a0e0a0215040b1201030c 67
    0x240341110654070b40058414108000140b403060319010141c2a140080303421034400505c004071043e01d00c1403500301c03445003c5030401c2c000f850149106900080d04030a0008141c04104052140d1144c00004241400d4100fa5948044408c6400c0c800780040d07918420441c40c2074004080c4004034806000510000404807500960406001e101c0e0040340c1e004000718208000c0004002200301c8540d0000e1303266521f900400290f5190324006906c04d2a440c1c2c0812004410604014014445c3d550341c2441c00e0082500c40582d90881d11007203030180b02c1c0c0c4411a9010009101606401c60640c1c2c03843c01842484d403c03c41600d01070040e105241d0000c12a000050f600010004160012000f404116a42d280006025001d003516491a80c001c3c1ca40311701300308400d90710064401e506c2070501700920f40780c80855004880c04400c0204440d8000c504050142ca400c0d10040e00d5040ca036464240391a84525040700c2a801132a907034413500603014018010052720661010292584502d540507601000c050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 740284163 1250 740282913 740282923
    0xa0b070305070c0e07020a1106090901030609031e0302040f0b0a091a0d090b0f1f06140c07080105091005100b09030c151b0303150906010c0f150e0c0102 67
    0x6051001c00030300c103010003c004076400010100900200c40c0c07843d2940019403135101500d802c403407154409400c4401407420205643c01800d020b450440560300b1070303607a917006020050003601481800c0042c0c802082d0302c0c5046039050a001d603800350b1910318094030911407031065004401080d5091010150850380b24a010b0304907010040d005104045084074280c1d00d10424290109140c1802e0011043c0700d4405822401144000c01903009075070342400c2c2c0d000310990119410301e10515404200809441420300b03e1101c0a542c145034500f40031810000d2400c40d00f40d00007800f5035124820824540030500454040500e4030000b404589456404400341e090b031405008900301d00130608203180e8404010301101c000d00600600c006c010b40d00214400c603004501c01a03514550142200034680c1c0100aa80c01a0304a40b10076100d0400d00c0b007000034180c1c009000c80e042003418040300001c10440d07452101514010700904600313515041c03104091b40e1004411400c2540b00000d9000140d80c002a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 740285413 1250 740284163 740284177
    0xc051b1003090b0f040224041d15010809032703071a12150607050c04150602061311130c021209010e10020f030a0207171606080a060b0703050702030c0a0b 68
    0x3a0703440d0344d65200154070315000358410f4103240d01c00524501424480001801a140404040708080300c1076043d00049c5841290b841c0032024087c05100029400b0f1078a10360024117010070b990a140780d01200d0b55180000401194110b5014400c0321418102403100101502401400c14100d41c4011955401c0b8813442e44110f10103070903840014a020501e01d8040600880201519030303910003804d04590728100402c0c028885c0340f600104d00340081c0c4100c09902206c000781c02070090795a034a5503a000182008805039004210001d00a54907621340001000400440350b0025145902d41c1d002440c25008041c040304411042082c0d00f11680c100107540501d0004541c280c10617100500d040b420011108821880c030320000c1401c0e01e07115000309050702903604400581041c40d8101c2ca0f690350b0344084407001070f4030f0808501d09001c4588908a11507102d02c054101241d1240d84000c1a1856031154609400180000c00c2c02d8045143c18841c04002d818100d41042a0500b002c3c55484c4600c00c0207 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 740286663 1250 740285413 740285431
    0x316030c0504060e220b07050c0f0309010f14190207030c06031e0b040e010e2506050415050702060d05040b2a0d0b0a0806010e0702010501081c0c051b1003090b 70
    0xb0302e5203031180158104074151b000000c00c0f007504040300003900030782194982100e2070080303824a060780280001502c03510799059540071514000c034001076610121880c0c0b01082004200300b45c02c0b0b00e641d8000c1d00300032a992a8000c01006145050182c070021042d00303c24105411b01850740032103102d14190950008800380002004416040050002e0200081c4480c4650070070a62013642c3d80045024094100505000b50f0120070307400a44d540c404240c01110f0101c4c509200038003101c1072000d400a4810f41f2800c1c410300d80394803a00000d07107230b030403a884460165488504000070489242c00da00d41160561100b60340742c20140401442060350034214850f0088041801030380481c29800c2103902d80e10292809130340d69181c1a041e0f0b100c100174041d01e5030a030b2071080811481031051141d00d040f00c1c0d11394060401002d4214600c2c180d070180e540d0f41000c00254154500215406001e50f080d0150160850281524081c0c01d004c200b2404148550074946001040c00204010300403d0384d0020b400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 740287769 1106 740286663 740286691
    0x9132f130e130609030203040e010e060a0902090109090203100f09020a03141003081315030506040e0a02180c1902101406011b110316030c0504060e 65
    0x1038410502c01d440010300c00740810140d502c2140d03500c0c80392042d00d207012741e40d0480c081c010f90301781c01c5403440380c521030280819440c01030081001444410025807c0a0713540700080c100b200c49220792404c0e01d0300040011031700f0200d64002c102a0002c982005080c903100e403a0720000b508266806800310b032910000740c11009500c0c90407441030f00034420f00c011640c116550303050950040b030880d2a0780300f9a11070104d401c4d08d001c01c000f0a125082e660026a510b0000308000c243c5803c0d402c91180341e04a000d40401685854052220f84912600e031f0701807940740d036080010203108051241c085c104100b944101a141d0101d4640125000b4200c20302145100707442d10104860151070107800b050807980416042c0c0e0300500c2409049010b94905035100244002003030402071040c00e00310000403125401e0040026054400000d86401e880400c1243d04000392480c0b07461020704603603c0b00c001 = true := by decide +kernel

theorem cover : BRFrame.Cov 740107913 740287769 := by
  have h0 := BRFrame.cov_init 740107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 740107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 740107913 ≤ n) (h2 : n < 740287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
