-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4604
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:09:18.45735+00:00
-- url     : https://prove2.me/submissions/751ae90a-b9fe-41bb-a8cd-bc92fff50677

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 827877697 ≤ n < 828057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 827878947 1250 827877697 827877707
    0x141216030206071e0f02011238040203072601080a061107060e16050414012d0e2d0f070512090a020108010e09061918030906020709020406 61
    0x45980c180c800d961200140c3c01c0514542c00c9000d041c12543c10011105400c1058400916060520036223034151441c070ba140340d6100711800e01614004012440c032110030b8460140800309c02500490400b03002089282e0049800da03042030300c0540c0881c0b460804031a801c103001d1903000c2d407140180510f2078290324240e0b590f556014000030242800d503640700b802c20f00e910204215203146804c00403d010011480d0361880c1c0d0b0b2412109085000303800c411020030f5900c0c06001c0c3c4a0344c0c01c1c880038000340503400c00100b4614004102d0f02c0300c115581c06e0414802400c20240d000d0700a0400c02082140751520b6a6a404014000c82515940d200c81e903d50302e81e0800028011504503440141940c555941c6400540b5544a1103814104034107602d010081c06d00400214507140a100b84c0c1c031120030380d036551070030000c110007502d048069400c000d00140701500b0340c140300408501684004124201e00d407001e08000389070b144c01134001400300701040c030059404125500040c9a40c05c01140b8003864401c0041c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 827880197 1250 827878947 827878949
    0xc03120c2003040f181d120703260f0a020408030f210f040302060c19201b030d0c0507140414130b250503040507261c05030705031f141216 61
    0x887d030303480400c0910605204501c4099030f91010428207402c038115010441034090120740450700c40307104c20300144a0700060300998040700c05c09401141052036040c1c035025141c121030008082030503042030740b001207030500500a01608034041c0003102070519041c02820070f08020031240781620100114201901500710412040f8840d18111410501030010229a1402c090103102c05100309505014103400b150034030320380028102c0c1121311940c020517054036060503200f0040c2a6402c1401c081194159880e00900e09610040000406484400880108100c203564001303448440c0050b8004204004054503007080008005d1180c0c00400c88a030820447e1820b40c15040000200100e400c004081107264081c0c4941c000103804180c41e4003c240200100c920351040d54071600101c6290101441402180c0660650710289140c1d15400c0580f0140e0000d0003c0c81441c005140c410420040b2440c6440540302142200000744041030803c00c00d034003a4101201a90000346808a01408a00c5560 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 827881447 1250 827880197 827880223
    0x6070206040e0709090c030c0e03070b0f0a0e061201060e151606020c010203150a06080c04090b0f1e0109050a05090621010504030c03120c2003040f181d 67
    0xc2c0950f4481108403200c01c2c0e184c0c88200c4450a20101038442600743e0030100c085405a9900003070600810704265560f031407480b500700340f558200148004e00c10842c004142010203400d100030210b007500c02061040d4442c0d6802c1d00070203000c600500402c0da1251035801c5102045030324420064008000c11528882c0e8101010b45200308441d40d0100078058055419140810000310b490307252070205074004052803110303144100c581038408504240600e495901401034540228145410844030030010134200c8001c5038004841000c03802965103e45000e100c00c4600c0a51651307600c0b00000240814110f13410081c8907641e081c0b000d005541301e80089540c1700404079000b22a49030a01020980750302d44101c0510654204000c200c181a00301d0081c0303816038400d50361002655401c030201d00c00c8440c040005d01c009480584c0e004420400f148524035080040425640750907602c1501004007409944900b140e110032491a14120070a0312800450708004c2c00343d56028200c1b840100c0e11951880100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 827882697 1250 827881447 827881469
    0x150201020307020705190e0108030c0d021204090b0609220c020309150304031115070f05210c22093c09080307031401051c0b190213090b0607020604 65
    0xb1162001d480390010010701e003011320700981e540c4521072703075889a10200e4080100e100e0700310348038203851000482c90100d0295150090802d42000c0f4001b014084100f0381c00d40c4010141f1180d00345684203480c45c0751098000528407420141c0341c4e5070f038050701c00c03c40036007041d5001030119541a0311421160684041205020340d0f41e45e4941c68241c4980203800341048d13151040e4035903d9614240288610301540700d54450049811642000704d03985d1040c401462603181c12841c001c44034000e42c0e43c00a8101c034801e030900d0300b08410011001910b01c030101100c06214044002004004038522a10700565404c101d80180d44101a14260050171214409000003000203115a4103201e9179010910607644100b41650b03900f80508001c02501c9681c0129240040030b400000d190324100c4044042d400041d10b94040401868407644d48920004044203050450040c0c00340100199100606002181070754090742d85051071310000885541c00c42c550b0043c001007040d800540c1d604170958007100c8011180c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 827883947 1250 827882697 827882719
    0x703110d0c11031603050f0606060421050f0f0106050108160504051512270109020906040c050c0708030a0815060306040b0409060903031a01080114040b0307030b010602010501150201020307020705 86
    0x2203850300c1310b0500d610300c1101aa280100070031501050020b0168000e01c00c480300781e21000c04004882c407440c03003110384103825103a01c1a06c0003003440c1d60200050150090769000054900414181410b132164031809942d110030070308c250360308030134200e4000b4011b01504001c4001e5520160540c400c50140f584621400320514098034070900413a4451340e030300d62a01060342004021081c0651120800f103003c0c900c80600b4002400c03052054080198005182e0950f0f900c446044c0402043c1001a031020880d04101c110b00310300c0204000030042120100455840d455907500918092002d0400706010f01060039500e9503540e60000c4d2074104100b1a03002410b1001310001500030b06450600801c01401c00500d90b0a141c1c05600101d1010071a642d0000b07600301d10001101d880c5006d000b4440c002580c807000ca030150400d90b2141b0254440902280c0b001c64a0b900c0300840d400c001d9000c42c0043c0c0d180d44c0144070b42c20803007030103071038000d1140001d40c194144440f010303481d035141e4054180902e1031444 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 827885197 1250 827883947 827883949
    0x9010819020a0518030c03060402061804060311040c08070215062706011b0206070b0c070803040f050706032c07050429030601051c030201021c020703110d0c11 70
    0x400c8400d14444040308642d42e0141d460301600680060880724420007241e40c980f1101c2c1030100b8000d00c00f5030b00402420580da034980c01c0040303d405c41c2580304805661800284c0c01d5440714071030f00c8007450140d04002110282d1808000a5441d0f40308030408005055083c056040e400050303240c61048141d030240328a82da20004039200008412032044d8800b8043d0f82464101010182d950003040b00b81d8483c1444540c001c00c00011418044000b904041c003002500003107914010b5581c2c12980c92040c291030181c403912001010b0b04191402d403003d41c00c018041c03041140801c00320005007a1800c00f4000440040440b200400c501c446840c180321040f82c5400c030170034052000c0c00240c0300081c004c100c3c0a07030a0003100c54070100c080d0210b070040d00c0003403812036070b00c0c001070ba6074101c40005142c01d0070040500104141812160411810742d03409200e9040380100d19010540f4021804800503101d50305420010300c10304417110b244d40c6503005030244141c01e982c02002c11006603084140c4103a0800100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 827886447 1250 827885197 827885221
    0x50d0305071701090c0f080106021504140706051c050c040e060a0905070509190b1b071d0f360a140303100801150302010e180906180c06090108 63
    0x68018140b6000140040744000c541c0d40500108065a52081c05100880c2015109040c080c003848001d07034064100240042481c1c441954094403c2c5001e00310318034400d4059141c15519007188002c16800310703a040c154a040aa0002c0c1e8000301c10048c022810b1813507200f08544114043c01003101014000200c0b02d44600141100404044004000624180500900c9900640f41c540c0c49220300b01c0301004584004c460660682d110a141e9038038280c002000840c0e00c14442ca00501d8a004004001580c5040c0481201c0782c4240744060740d00e1841c0c5520b100307014020050041001080910a40d800440c1410892003c984601d03e8064414035650a85190548103800140a03500700122455461300c04409980100190b041ca4029541c03070b0300d50f150136204481e41d0140502c030403600400c013544c403820040041b42000342542e403455142a00415078130700b01729003502c8143e03c10010320195240c0010309807641c0c0032140242644401c0400003d03054403030500060304001c201340c00316040503007030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 827887697 1250 827886447 827886467
    0x309010f200a0302060a11092b051006050109090c020c19050a0306021209071d04060618090b0c04030308040b0a110c010e1608031c021e0415030207050d030507 70
    0x41c07049403899141450002c0d41c403881158204022814144403510051641c0c0603101c1100300102200c070640307500210b6040c0000310001c40c2a505050501e0100403420a10a00c010144040400b041c110300780000900505440e90060146a00d420304841e001769000c907122105035011169500051401034020001480c603812040d030001c4d04002c0001000a13036030050910900c000d203001400c0d590080070301d88601c0f0f944244081d101c2d9030b00a49414003603845015606c2845020001401c0e500c4a0050300c0c000300c0f60345000300721b9954243c004148030796605076070b51004080c0c1120f03281c6415960000e0903000080d000500e21903002d0080f610404164201058215101a070303076864041c1850b10a001e0140c1e400382c0f0020307000d02a22020500410440344098820345002582b500040c2c5240351550041002e0880300b59600784600c428051091400000e25015050072548a0b400c081004002d0b034050071040007454410440c1000042c00840c486461034100e04000529503120706041e2019151 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 827888947 1250 827887697 827887757
    0x81303020106050a180b121c0c12020c0a090203060307290307230f1c09050d020d1e09030213020d0603060504060f090203100c1404030303060806090309010f 69
    0x40303124045200c0c42c61054170302507401810014403100c2c1c2c542061040303441901c01320401607081b070105101517040504082d2203204151401002a01568480c20790441070940c0000050304903421090451910300001e00103416520f90031465400d041000030358500740f07403203403441101c4c0e45c841d2900d02c0c2281058595140544101007507492400c08802040c0781b45008040c060a606808500520070700c0e0002d51300c444e2821903000e8504020f0b0000c20300e640c10000640841c00b034950b80d10300000344091040b8007046419130002d051509880c2800392081140d1114101d404014040c0583c201e80e000c4941c0e0101e0f50161400c00d1055460b10083c40030388114103051000c00c1c20b10000204000c0e00390300051040340503260802c080740e03940f140c12003552a5240082c0d070551000051045c1311100e40e120b03440000240c1060344000c050400954483d4100340d1056004c299200320401c207061007403003010752141e56500a1454100190b00107400f400c044c82d00c0808002030124000c0490500241d21050b41c19 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 827890197 1250 827888947 827888959
    0xc020c12030c15160c0c05011d030f0102031012020d0f030210060b0a12020a0c11040e190203070b040305030a12024b0702100e0a150f0f08130302010605 67
    0x2d0f0b0f01801c070303001001030b0707039150458000c80f51004440c0d1203001010301c51a408503403030012524000044409011590050210445003145000e05075007c01054496864150000d07032a03180920000600c0405503004403540078154080c040107030385652560064982c401344502800c00c007405d049180c540255495990030b0f18052010644540740f8014002c040c50360703034604d071035403e000700d050080e13016114105020642d0100b090002803e0071240b58501e40c0080c2001030500039102c0020328102082d00c400108090100303081d019403c09014141c0035205642e000c902e001d01e0355850907074034465001d04004010405c5000c40c0340150325011900c110000303072804018014034600514403100c1c002c0c401c99103609100069040f12010300392000c2c50540401e1524209412a024400d15000b060040001c0145001c445155039650100c2600a0400c8072003070092200041c00242139030300300100040500800303110b0303581c2169018a01e81e070b2040d0b40301c1504045003d1494103030f000d800036405c0380340e00030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 827891447 1250 827890197 827890213
    0x821030c0405090f06030615012309061602040f1b0c0606050d2001081003082a032104021e0a05090916120803070f12051015030c020c12030c 62
    0x4d1800c0e2106030240b07a08074260b8445858029810540703000032250309002c1001355104244100c1d400407904040c41e20488628a41240c14000440e181d01010030b0050640c0821071650640c10031b4401c3d91581c80ca1410304001c41d0110b1b003401c1c45000c4d9491b035043c04005404c4141d008011090b00010000d00f0003410300030b0988000e1802580109100748982d5103401141083c5009600c10700040d402101c074000e490f03141074219202d00e20150f00100036400b0241c0c103150480ca0321182c5131003180a1066580c06181c07180202d08155101c101b0760a04107000a00300310034800981c3d914003003802c2901d0020709002460380000d003c21440340b511ba1090303500c540800c0800a0040d004502000310405c8400c44116450b110b105800000300c0044001d85090740c2400041e00c0e55004903501e8560f00064102141400c0140c2848005e54400300c442c81c400e13500201c01045510100344c0404a690801c0c01d0901c258003c00000a545240032828103200301c40b4505802c501000900440d02d850104900380d990302 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 827892697 1250 827891447 827891461
    0x14040b09130b310c12090c0f06051902070501081909060e010606030605030609060403030c180315050c16030518030a1a0105120c0f060c0d0c06060821030c040509 71
    0x3101c0c0318900884080c420611900c0800092103401e201c91180e07183d2005c031703d440000e0140117122050341103900d407102c1e502c041503955070506510b00622a41c1c0d00c0a035240880c02145490a051540303040542d407100070103014a81e042201c103507000c81b403401c07240145030b200000c00c0c0107041d80395006004146013201100349000e06400c4101070300d442e900c3c240029039072b690905950b49401c64103d8400d40140021500203072203500280103a07516450728810300c0b9030301d400404401c092540204d40c0c0d00c4c00401030360b4100c40f160103015404805004424104a4a0445811a20520348008040080024a01c61220040b01d800a0301100c06800c0f194106414500040a115428061000e204034080000350926000710888030606e5000080e01c07208200f07100344404602c0c881d45d840d6220300203000c48441c0310f0080008601c0004146e640b0451f001550404d0b0701102c49640000c16030341c002541d4111070101e46058481100c0c00041070036540d0b5101b540400c1c1e640625080203034028004030a001320 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 827893947 1250 827892697 827892739
    0x1e1903050a3b030a0512030a09080f071101051801080406022a1018030e031e0105060907030b060f030a0905010c0203030411011e0804030908070b0a14040b09130b 71
    0x11080302c8200740c40d40000c1c0000705565416082402000d5500820b50101600340e800095600184141004600343c0c02a69a07107400707070880b0b000d06c0e1130303c503000c10010280401c0c5049030011850a080135441e10007401d001e8010030b0490170915052044d040082001c102055046418142600c40010484090b07240b1442c4051071813100344d103151061100510784c40e180c0d441250301c401e8030b81101c07410350022943e050711245042d1159541c1030080350000c84061001c0b000720000440c4030380000640e071a10700701700724110801900c0e001c00c05141216185d125129070b411942e10500ea01020b03502c95580c0e0003000e010f814800300c010300315400c0c801c000a4030764002001d140198420056902d02042c0c200c011a4603003601842d11f00c0b060a2070041d662060f000e041095000380c00fa2810f128100e4542e14124901042d5500c0450b00d0308000a600c3d20341a40004a40007145446512510b01441c15001e041e06001d0000000c4c4200c0800601350642070003644200b200c0400501240d188240131220740394 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 827895197 1250 827893947 827894027
    0x1303082a040e06030304141002030c06132a0b1e1305150313020409050a0f03090810050c030106030b21070509060d0213050a060e091e1903050a 63
    0x4103034080b06002c290140b8020064600b0b03107001c3c0450f000552910400c0040703a0300186190400c0d40020804220002c00074424180b0900c001114204602450300e44010f954505c41c060040c440781c020b01060483c03070003801c048101c41098000c652a600c0807041d0b0341f1090308240003e000c440b4000f40150a460300c6c540c2c075100721081210703481030091140d51240d4151004443d400b039441010703000140185003070750004003218040c1046965482c02c41e036031003407407118620003500800d408910400c11090100002000100344442c140124208425003502c84e01040c0510810305490305454a2580c690180d200ca0b11310b54948003480c6480b1f01c4220701e8403082c4600510f40507007174210004400d0b040840d04071015580c00b03019881c84481c88400000180f4003d080100f800e0340304c201c00a800c41960003481d004030800400f03000c148840c01144640b10480e608558042e030003014501121280394040b24018a0709420b0803643e0f003c901d40304a81d844a051280301541401141030228914800c138620 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 827896447 1250 827895197 827895209
    0x7030e15040b06010c0f08030c0f0d0605040b0d03020a021c021306150f050304060507050f1b060f0103051b0a09020f1c15141903050a0c09051303082a04 67
    0x1114a450f07150044421100400024020300700002503c00080d000800943d03025003c000300d03d0038604540e0008080d03a10400801c0641501c0306402e11562034203100c4c141001c03604840c1b040c007007540d039a006074841400381c002070f106441c0d4011407a00c18070741000b005e000c10b5000b00b6500d04908035040010003004203005420502240100c2c0003c542c1c003441019401c0388064980c1070035035030b590b0780e002301905000746407204000e000c1c0b003000c01c4000307628050060500b01d291242c040d250b000070001c2c5480c40c010700c0c0081000310740d00104040740010840e03201110341e8840800000401e080891121851540700d1030b8401d100241c2c401614405c04050441c0d12603c80c1102c17070b1880c1e09100c0b0700507a59003c0b030b95170910703201d04e408010014040c801903440402c0a40b0420f0100f4445a80704002c0000d54026115600404044c500308001c002c10f010103002086403c021a0800c0038241c1d1000c2100702008041c048140301058002c03400c2c05040307891181e901c041a138001c84029105106402c0780c03041d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 827897697 1250 827896447 827896463
    0x2205030301030309050d1a0a06031b14300a08032404090c09020901091802210103050703080a030b100f0906031103060402070c0e040c180203071707030e1504 69
    0x105407440c000321142c02d500e805c80300307140082d00c0c4026601f4000350090030713101496035188000800074140d80702d154514803001c03281f02c01c103a26140f00070003903d0300e14030000e128801400c200c00c055800c00c0c0c0310102d69040f114221840e449005d40807480c100c000711003c0e1000002008000341c2d0241000400383c40212030105c0780ca4110002d00303200a0344d00d04500140141c501c90740510080e41c640e8060102e2000516040e60599910441030708000c0008420b49681600058181c040305189803100101c04820050750348190b01d15200c1941b00c80031408020080100010301c40b10340352180c3c0001070802c0c0e004000c030000303808601c005002840c030802c148000c100c200000103191400b80c03140940420101001d2071960b41c85804000c02548804012601c80c0c1c1c4100c40891a10007000e482441548601c00b200780d44c60501001c0c400c0408403020501d0f2180c010400c002d00c1e00d030b000c98400d24446410900d10b4180e260a0001e4020700300d103030071035489440781c13541d07a00115080915586c01a0700445203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 827898947 1250 827897697 827897699
    0xf04140120160801140105040e0c060f03090606060a2c030d030f0b060702010806100c0b010605030118061511190f060b030a050a0b0907050a0902070201030e0705010e0402032205030301030309 84
    0x7000e09071905403102010317074074030303c0b0041100741401d4000000c40d4120b071081c1d8481031309150009240e03800184283d100810003008000248104220040c1c1020003210f2090401c103611000601a002101c1540c0401c19800c01e11141201d01840300522800000c09840b1000d08940008000384140603010740b402c1c1c01c084c0d421a10b801d0180c11540220b4040c0c0d01c03502c0c240c1c0c0310020b210f280c940c01101d0004014071040090003040a29040b18080d042507501d02c1d659525080b60803070030301591481c080b07044d0318140d020820110740141b00d4056140710309050f00081c3d5410340050500c4c02c0420418000080e0242c18400c004000d030031004c2240c8a40b6003000512564001e150f555020b4150003031490b4000700e16034011445503410280c0c09040d90003166441b41d100c00100e20002c0596001d40802d54002c6004411582c0501803540042d190307200805c1070b54a0140000c0044000e00c85050003140e002010800c5c10545403001c1d80e100700100c2640107403520501d03169980c0d5100744019030000d40c0c2520 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 827900197 1250 827898947 827898959
    0xb07030f051b180306010e0f06031c0f0c0206030a09031b020f12010b0a0f09241202040603060c09150c0b0a0c1106010801021e0f0414012016 62
    0x11401d80103141e0400e04601000381901c594441e40c1c008030300b10780007034038600402100e503404214a901800689010755100d00b08000103a2002d000a03100c2072090b000541405283d10f9a41d2549206800c03070300c1c0c441f2485808100560720400a184080d4100303400008111810003103030061890b15110341d98410300d00114000220104005803402580f002d80a94001c000b8941402418200210755000103110850b5000185071400c8584c0400103103220010b042100310824407070301510b09000c1c200c0300e20300f086400030b0020081d210b005007a0341c0d43c400401c04003551981c1d0700000181d0390104042000c0d0039080c102a0600174184207074a0220b08060004683c148294080011030350b001040d90303401c1c0c680f030030100c02608142100000300040650b4944145004100b070b61f00a0000e9400103035031744030f050808030303000003102c00503104500104801c0c0c110100300003c49048905541d0402c90320b4000c100121401c1d42c0f460100500040d6090243c140e00401003001007410305070122405005640d00c1d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 827901447 1250 827900197 827900201
    0xd0207050a032402070606030b0702030c0a020105161505090c01211802032a040c12020304031b080c10050f060922050f0d08191107020604030b07030f 66
    0x4000d058004903403a000700000780308142119810280c4400c44032001d03800382d50f090220b811101082e601a52030f0f0f001002840390072541c45800100307500c0914501440b11078000c1d50b800320076200a0400c0400910005402d056140094119034001010341c5400ca00302c100b030001e4107055942200602070b0010440c000d40c0a5030040c04041c1c44501ca441c1031003030482d035a0006048a07000844c422031403002040041c2c0e0140300780403050405001c950702e40110114482d024140085c85540901d01d040180601c0507080010f080c0350940030040965290b503149002ca60149000b032800c1c0c42103565140640c1009800e04c00b514010090900325041c1111440030003060399420b58445003607000240c045044c034102610416880140c202c0d1506504048e00d04425611015110982e603c0c1c01a041c1d030000c02e0030034005140d0350720241c540803035107042100c1003880005032200700384106680e440170f1032402c0d107078030b02a1007425800621944c3c644d5640e041c0104024002c039039007030020340380410f055030b480118 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 827902697 1250 827901447 827901449
    0x10e060105010203031b160c031a09062202030a0c24031107020d1b060e030c030705100f0201150b0a030509010603111005090a08010603020a0b0f030721060807080d0207 74
    0x4100410003000000d203940e2400c0e072287c45462418000c5140102c040780d08944288000c621820228201c00c55522080c0b2101c00e0242404100d904000188201c201c880d00382108524903445e0b00046025480c40001d00e403c041080c024a0f440040034001941c0402c03500441d20055400340012519940720400c030211003800c2d00342d0003c54024400b0354058100141e01e02d201c40d125040c02c980c4880c000c0b4100064000030b501074400244a4035404030b490078140b0120701c031000140d00030800c40b81041d0004a0301c50078240200100080d04a05050182c403d410103400710030360582104038981c0324420034982e46c0c040802880401e0801000c80c140d01030510400301202c0c1c11444414a60b2101d03410130554418409100307007040414840941c031982c036415044000c141c0b102c000a14903246106109441042c0c1e80901412101072000501d10400d00049a6000c0040d10b0321522608621000a40d105100400c0100f414505440401c0050000604000f950141c00031202581204c1c1e80880e52035643d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 827903947 1250 827902697 827902711
    0x306130b030a23060114130501080d030e15090319020607020c01030c120501080a0b011505040302190b190e060c1c020f0a0f020f0108131101120905010e06010501020303 74
    0x70008003000300d20325003d05411141d04001000c080030341045080d00d003113000e8105d0b0210401e5028041000d2802510004410300780500521096145c1203059444074240d0320322005054a41c0b00c4840074540c18030031441c903a44030981640b402c0c20102429641c0c0d41020382180341078030903070031007440c19030000804078403c45c41a4000d111a80903500110007504030303c08813000f4403e40c9032016080300810700641d4041c020f441c0c01002088191f0070402ca0038003040e40503d04034400c4d144a0307071020703501030116029241c056484c911503584041061008062542c40094220310104542d103103020403021030382801c803940e03442c42d61883d842c00030041c9070f104000010310180d200c160a1400d0418408001d1031030f20341e600540710480180301c81d190802c0550078044500045c0c83c040d8008618281c41140d001040a1801458a04c1d010f404001045498100a0006840b40c182ca0415031310500c0d8ac03040414001070140038290241c80c01d2400b800c010000c0e034119005280000c07070b0a520020544c0c2c85106 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 827905197 1250 827903947 827903953
    0xb01080a0509030711011817011104151d060a030e010c0e0303090103053409060f171308040b071502030c1b030d060f0519150509040609050406020306130b03 69
    0x90645d4401c41400503500442c5e042c062202d43c0e401d249581e00041400a000d0350351440c44c41507100d5034250031516045c09000040d00240014400c0c0c8444e104990307a00e420f1b42c00d10909d0000081d80c3e01d0b41d03070030380100c00551085000802d8182c059054108010649100d002408404825082a5600c00d02d090101d90140e001f03100c0c0c0601d541c42500401c0d00824054182e01108135106c05050750340060080c210300c21a0408100d0001c1e40d408111a4001c241c0d0f03203404020030306082c100400880c600c00104132050000c001007450b480111a8040c24203600106030b035603444d90364042604640182d082698a2403160180901d00c4056000712489010350300e03091031401910441d05100c41020503108880c0388001c4c48010a081000d101c0c40e800303002602c000700001441c0000b041005640c01e480385040b10311402c000c0045041c20a81c506280805040075900c44421001080080090f5444946440c1c00d00f0240300074848540c1c02140140019580d1648000d2401018000d64803000000b0740c05038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 827906447 1250 827905197 827905207
    0xc0409020f010c080c0102030702010209011701080718021c15050121200f0d06170d1103160c060216030b0c0a36080a23010912030b01080a050903 64
    0x50b1203203072440c814031300c1012480e0074885651002d5089800845120700580e600007541c00903580c03c81c54510112102c40502d4001e503051211845e107900310b078030038802c507102946000c004415241d0150703500212071280000340b5455021064010b0107913603019090402010701c0200d041d5108500107541d1420210b499a00007011a90a40017411070001c4008150010545070042c001060002c001c5210b410310401d842c2e41c5005400c2040701c80c158031100350001d1084e01c0c2d109071007011542ca00c0d0340300281041d40300944aa4222411403260940360700314103686110728020000c480307206205640c1164219003c501e41d0080850b040142d900000c0e01e983c4095000030f107402c1c13402008081051281c40d044904111156040c401c0614071204130181c8000008000841410155048001d0255000030301c01010140c0395224004078149640e103101345840001342041d002500700104042d400040f450300800c0c40f58004004040000742e0b43d00048003400440d400403070901469026a090101641ca40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 827907697 1250 827906447 827906449
    0x130e1f080106120f0c15030e070504181214040306050a1d031210050d140f01230c09030f030a0305090c1c02010c0512040305060903040e04020d06020403050d0e030c0409020f 76
    0x103444540040329180c0c100c1c24007007880200220b86c4011901c1503107000c1a0f0500d60032001c0d040c86c102d030f00054040d52502ca41085000c000f40c165031020303908103054071145910340c0012200c034000e5004600f41c0c000c00003800000c104483c3d01641c42000082d00070004034884070402d128010100e81d295085038818481c06007032615154819802c101d165802e1281c4640c1c840c0800c00c0e240c40c007407081e070b400703402c510000b03030100001c2c091400c1c500c019000800c00600702c800c9249900318011080c0c8030032809480000e000345003c4007201d081800080c21100d20350500308045513283e1090441700700017404c00f80400d00420b000240440070020092880494000e8030200040c1d802101005074108080641c0d84004a01e080c400c201003181c0360088142e840f4110305002d07203000406040074020342c5c4200f2003004176880c9408400d41055040b01c032400310080f0b50810202900aa0700058a1030044c8420012a0354000c240c1c00540007099040d80c0107481000204004c503090704c00c0c0030b508100d003248180c0e02 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 827908947 1250 827907697 827907713
    0x180501141f031506052809090b01170c030402011404050303030712180803010602010c0903050a0b090f0709050f0106180b09031002040914100f0b130e1f08010612 71
    0x41c112468009081101c0c85040601c1d10f81c6544140d0210b28005074810001c0d2444a0042c9210444c4120413100700306c1c5803000300980110312810704050f43d90001c082c0180e01c211940700c10604400403400d01420401012041c2da401500c00301d001c03404c104000e00425801c3d4003640d04460b002000756003184d031488000e0f2011900d50324030340701c940d582d41003810481038030040714074111340200c456548a40c14083c02a0844040941c1603050113051403081000032400203a4040459001e260300600792a003120716443c0941c1c03199920401d0090090104880e070380d0740d11451140c00e070f09055500300d0366504400e40f0801000014000302010909042c0800d80740100100420700c0003804840d00f040301002d4800480c1c01c1604140d00450700c030300345040d008001941e0290801070b40d5403240030682c5000110780c510091449017024013800400d4107201c4203040c0200800801c400d076102c27000c0b40750400042c0e01c0980c1000c0b44241c5004003000c00704091805110f40800c1e915042e407000c0c0074610356110140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 827910197 1250 827908947 827908999
    0x30e0312251209110306090d080702010b1e180123101b020f06120f070f17070306050402040b030f0a0510140a08190311031c05060d0c18050114 63
    0x40c40c00c13122000320341e090301e007000818407804988019045d10781240740010039620000d4044070844e0705260511009543c0d00d591000d9001100d4194005070b100440440c0302901c1504440b40305094040c00051b01560014003e46440010308011038840c0420003049450080c8000c080001103d9a044044030701c009680181064001440b03070001e0b8020300000344095002c200d048001c040b0301410f002034902018000c903080400740c248840c00c4d0403d4940180380d000d200c010030b00b1b054100b1000c1185180664060409003202400555840b502c4032442d040c42d502c16990030455541803c0080c042100900c0344038041c8451080c2040700901c1c00780c11030412540384c8529903100021140008912208101c0d40305c6024030742c01320810030071046c10007511031812610300e110190030401c1540340d214442e03020034000c003040c0c560000b1543c682101244003c100707100020300b941034410001c2011071201e505c01103001154202486140e89902c024100c181100340003503000740001e060860301d0382c00420042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 827911447 1250 827910197 827910203
    0x1b21071a0c04090c21020901170610050310120f020f010e060d1d0703121e050301050111030c0a03081f050d080c03120408070b0c0c070510030e0312251209 68
    0x1400d015100e0318450100510300c1707084c0c0702c45500040288940d600400d2141c605c0a60144201c59840c200001c41d1181c00c032030141c1820800000001801c103016806010301130200341c0b200007510456860201c0032071040700401d910500e00e42040f00132942c03040c00840f40741c94029003071034286850400000050030581103803200d00202840000150ba404000101c020750058000301940c94071190041d0940c40200421854022602201c02049030072130708a0f030444500b840c028883c0700e40b500441d03055001c1c2c100e2a003098050141d1500605901c803e686004030440700c0d984040310b07400c05214004030030034800c0c650859200001807010038078080c050400700c40f904041e41d2070800d2070503aa0b00c001800700c0d0300700c0700403901090500601180071021944144900403007071a10b01000740032562500544034040c0f05400381940044d210f8800c3d00030941c5e040700c40382225113400d401001d05030952402c407000c003031000d02d086042e50400803010038a264158551124001c00e2103010fa09009400301980035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 827912697 1250 827911447 827911457
    0x6030b01031820061204030804030c06150e0105030334051e0d030501060e0f03010f020a051905070f080309161203231b21071a0c04090c 60
    0x2041c01d409510282c1140500c95104100404400a11086403107000f8001a0242109102e48050314040b010025009600f500b801c00c00e03a5603030300c0d007104c0301c028a000c024070507800d021076051540b000c01d02c58401c0e00d40303d200b0a916031f0389400c10706941e40542e00d5a03d5981781004034003100c410140b01e02540120040b03000c485001125202d40f0701d8841c030402e0181148628040b0001a21400e2045141a115524042c000d03545082c10041500941566541c8240292100002256800d40c4440c070190000b100540d2074440c0100080d0958001c1e0325203080ca001e100181c410340500c45e00881d00805d9001c16584c405490f44c0e1a01071654000611012035807203104001681e642006000c54001e00e03000ca03510300c44030020f04c0c0007805611010340070380542001401c1404032040c00825160241c1f0001c40404512400c500800c0c908070050455520307410009a58080c5610080000d094031805500d00c0d160b86440f8106490800c5821a40602c0c02e000a00c001e00c0281c0d51a000803000015910740307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 827913947 1250 827912697 827912711
    0x150f09040204240306031101030c02100e0c090c03090712030201202701020d120212010305070302030d020d0e0402070302150a020c07060509031527010c03061e06030b0103 75
    0x31800700e902ca034011511510302e21030000c15000d44205107041c0000d551a00f800901c0c5036503100640b50f01119038050615484114014443d40300f046111004407000100307200a0030344460702620360300e010310504c2c0544110380c000b0300c13858030b52011240614803260051001510b132075000f13050445030440840c215501c4050324094100c101c601c170f0044420071001d850340c601944047d0900203c5180307181126030180449013103aa80c000c40da0131a14000e82c24089090300300004688000d02c92001040301030380d4214004014803000081180a0380d109408940f1503d0101e00141d0b039640c80d0201c040c0005400c1410000d403400c064000c0d000140c442c0c0101c41054141c0c2290701c450300301c102e0b0544145a80030030448240c020070480301004005509003140350940e4000801e444060440d0380c01601c0b100366011400420740d03c0c5a12034076101105208000c1c2e50703180f61150203000021b0410700000e00700314010403e00c02d40700150203c0d0012503c0c4102c202e05c0e1100c00d45c00b80c41c13485d244d1414181d8501d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 827915197 1250 827913947 827913949
    0x130b01140304110913050d0e040b0306190c0516030f0309080d0e07060504050123040b0a020f07060914040e0c0d050a0b0903030402091306061d100b09150f09 69
    0x1000d5400b851007918180e007401400300510009403402452803640318100d200c06008030f0408501042e00b03400d903103460038040484402050142c45940c041d107070144590700800045010b003a01c0140c81108040c0c0038403054584207800c8505000f44d250220240c04014004000280590a0030481c8881e0342004902016280c0321038106800c000c0000751a20784688050815400134003100300900081e007051410b05042c807000074400e01e00450200e1200b841d298180030380000382d01c15a001040c400b104140e540b203504800030b4072060070003903d5085100c0d038034010509034050010b8209482088031680d03005602d00007048003804445141105e240200400a038541d141c0010901d13020780105c009284020151514480e0340740000d01145668100348203010040c1e4400b0001c9401805204071148200300a00785680144200c3d4448007940c5281810311458030655114248038140d4407240d848000c0e501c4242c21041e00c500c01c13099078450305000e0034140d0190341c1006050301402d00310300d00d4242a44d80c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 827916447 1250 827915197 827915237
    0x6040503030a08041b1d160e09060f04020a0207061707080411011e05040f0b0309030412050c220b090c0a230d050412030902130c170103081902060402130b01 69
    0xe00088007446900a440058810340c81546801c031403029294180c87c40c0401c0000d0442c81da07a90400d20500858000c41c1d4140c6e95490041440384009004645c3c8904451010350388400c544907207030206c4c0c41090341d01100281055005d01ca0030241d203805100366115503d85681e12180c5100505102400c00500803ca02d00310387c459010b201a2036240c0e455080949a503003000303080d84800e06940c1c00304200242644080240d4045034138001e60104a030f0400d24019061039216080d140d005a40a1000e0669a1100c0c038040707502c030080d04042142d00040c2e8144003c0074412619141d890030b081042d03007a014400d035070107001c446038035800200000c210072041c240ea50000241e031035040c1c0c6075000e00003800328070091810550f8060a0800c1400c4096000c16a010f0844071003101156a0b01000001240107510304480b444095a8042c01503840349040c410740e800c440080700b40c0c82c82e0802035012180c000603036903006035002810040070302c0c0450310000c068040030800764104a012507010284242c40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 827917697 1250 827916447 827916449
    0x3080604090611041404061202060a050f0a0201050a0b04020a0917010e0a0f05062a0706061205010c18050904140c0d0b0603010b060a05071b1503020d05010506040503030a08041b 78
    0x104442d0741c55150940c45c00302081c1c5c00e031265105a240c1081040351510341c22604042c40ea05860b01500c60070200d20035200350003141d00421407014002409000a58103501a9216802030300c420000f050000c010300c003c9000c1c1e044c41c4404142031034800d11200324020110004400b5000001c64038011845400d030429070140d03412220840001c92240800005001c900d51011400d4080b48040b02c1d1803102d40343c40c0042800a2159810010340001404180c2d04030310081d10444030810801e100500d4020f000341201c0c9006030000c2d5640b4111509031082070200801c480d8000c01c44032094440d51100f410503548000d8096491181c061468007a44400009110550141c04200020328080060500313441200012500c00c000070040345d101540c2000c00d4651041c0c0040180c5c07541d2620910f040f8039050150803601d4580707210040100c0007903141d0020150f05064003400d0000383d1b07035107040c814640102d004041e071642092010840c42c91190f0728603980140550200c5c0c4e124400a941c03d00b4902107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 827918947 1250 827917697 827917721
    0x1a09061309061401150c0303020a03090b0108030940020705060c0d200a0e04090c08011a1002070b030c040b0304080301050f09100501110a0204060f060207060e060304030806040906 79
    0x440d201c142078003e2a51401d40101040a070a441043c0344640062140c006400000c09042d0302040311615588694031040403168011013107a01540c4400c1215070741c6d046642c9052203083e15941c401c1d6110084c58485040314000c600e084510580103201c00b55146a001024041c654203001120202d44200003030b0b4000d44105013150750740c109030030741c00b0151903280409411030a0803850a110022900c800c4a01c04102e5140002c0d045c9600030004000c0c0c1150f45001e4181c010400c0042600b4070194041c59030050006a081c1302003102009220302c10000045890150300a1981000104850740046911000c040b1202e480c0c1600c41c2c598111540080e10709884540004c8014081c0d814081030800d500e05086801c41223a00c1d1402c0550046240750151a04101091525a082d81390812443c0b80c1c26a00410600909450b001c5c18590040d451151400521841000007404d80c0107800f80c011700720340031301310380e00e140e0b182e803003c5e50201d10281040d0b410079900c82d621004241c291140b0161800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 827920197 1250 827918947 827918951
    0x30e061c140709080d09091d060c030717160f11030403030903022706040c0318050c010311070b0f33040c03060b04090b0411030108060106121a0906130906 68
    0x40004000740206000d0300000713081c5e808052181801d0390021a1081114440321011801600c1680000d400d48011008191148592401d01c0f10b07645040c4080c501c03030381d090b80e00d00c8000c04094040300c000d07404c06d072a00710a0107030100c490100c4c0c0303118440d8104410400d090141000074845202440c5601a9000b40d0000d03c10080a200314a00f0740324001230184007650044684031a81c0070102c5412015002c17510499440d80c1e44d000184c029013207104403841c4441e034201c81496a0515039102c0201d048004c2c000391510340c0710b0f00e203241640f098418040d08030b00c1410056460301e1002c18180390113000c418010b0f001040c2d1002044003402c1e6624a000b00c4a4100104000d80003444141c403000340a5505141c2407000610a880820003900e0031903c030f004001c1410807c2c03001003002043c42418109102c00000008191030200241185c100c603615598150410300804007401200c480300c204940c1031070401003d50785071425042c0180c101c00300401c0b049156605180080032983c5d100307801c5034800e03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 827921447 1250 827920197 827920201
    0x506091605010e01030b2b0209070305010608070e01031e020c070f0602100b0a0b031f06030203190b030f010c09230315100f031a0a09030e061c14 64
    0xa4040c04520403044600880555050074000060071800c6007030703402410555039060013243c4d962408000300c901b0782200d01241070540d1403521944404140341041c0e0040200c00007280585101b4440d2604803081c40e03482c14030688400707408840d040701c8005518101034032540d00c107030101000c2c0c01030106180309040c0180d0f1210f0300c0482500f4104240d00c003640c9005820010882c035600843c0001b144a81034100144d03440034500001e0b070000c610781013030f1801c00d004010842244441000040340520b010b11040c1c01c00d030385000880c00c0e44001c4804402d01d05900c4c048150023a460f8101d2a05004010140e40e44061540002800c50f010043c00300c00141300d0b0130080044400003c108450b0010030760701e0516800c24400802c2e43c4529801300b03100805052000129045180c000100181102c01c070009011b42c3e4a040400c2c1000e1411301088090640d2000f041c005602845001103969040d04c4031040d224285c0204505ca401c100c80700160044080c4003419108020b1042020306200340070b101e0390074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 827922697 1250 827921447 827921461
    0x90a020d1a09100f29030106030b010206281109090a0b0a0509060603070f0219031206090219200304080f0c010903150b040603060e0618123001030506 66
    0x80030b00030701102d410501e4a1004d001d4420080d6000c0181d44154041042c1322200c0c1704a4454007155018511421a001c4008604a035143e000112031032001d0b821151540c940410720007032410700c6403a2220640b40c3c0e001d01220b500e01904242d03003c010703000325181032004070300c003148400b40d0403200c0408481d5503454440e181d01c2c1c010700ca18041e1034180d0300084e141c6010320100c0c00501c805000b01007404032250031700440034401c02050030003103425410746404041624003d444242c071204c08038101e5041400c0412103690903c2500c01281246001c01c2506d06030700c0003518100701131100ca070803915600c05000a00c140810090000f061928000c0020360400c0008034200f401c00b883c0541082000d036800c00c040f0f0350701400d80e44803d1062000044440f551400100101800e90000744418101480030703100c92404a0031901c1481030b04028159a01c0f04031100d91204036420408018090600c04020010584500c001d40b4158103001c00c0041c1840a48240700c010090740111840d602501c104681 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 827923947 1250 827922697 827922709
    0x103061e03120e01200c060a081e04051c030f0207050a02030c01110d0f0e0a0605030604050c0f0d0b0604030618110a030b0705031906090b010212031302090a020d1a 72
    0x401030051502030072283c00750000070030a891480e80460291000f039903041010f8818020540c0030400107080030b513210722070300000c1e0440d8002c603950b07201240d100014801e0910034180070340c03003903a01c440078284040600380080d444045002ea580c04161b59400343c0f80e5090014402010300d0390182000384002d10f002e2040500d00b03041d04011904004060000361041c61b00040c80f9410151503042c00d10344112002003c0301e50066020aa5600021020000034441d40050086018100c20742e01804103a591010989241c802c6225520800d01c0c06c01a90018000d00c0d4005585400020302261400d076032500c1d03042c25a10a0658485500140d28a00041148241c0e000481250a407a040a0240346440b40c0d84841e00050004041c040000700241543d018420b541c41d080e41080c07410030003103440301d1a40004003420b40085002d44038603104450400c0a070410740e889440c1c1d400403200c600f07060740c1c00d10a40110240407110441d40074030054296100c00d0180c01412009100010325528401d020018 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 827925197 1250 827923947 827923973
    0x31212050108010621020a0b180301110a1107050102030a030f020705100203070f030b09150d050d0f02370203030c030a050a031406240904090c1a0a0c110103061e03 72
    0xc500d2031007480000060721101a9103023180d030340b000300c10380341d82014851001400c0580f00d00c90b4194600b000520034880d4007805844041d0f01c42d500c109200740c260100740d50360b100c43e01525015034000d1100c030380d07943c1c401c1e08003101d68044c8180c0036080480c95984c07203181000107608141c0c565004000c01104c40d501141125081590386400e0040b602c0303100208485c5500507100360304800705500210306035110102c08180c026408011a4001c1240c414000e103060300346007014005019107442044049841520784001d8009100380d900d60711022041d0140c03e20108000b241c05000c188010007015030240f010740b00c5103c59843d455a10307900014005c08030b62038200b001c2c0000344400f0510035940c03200308400302046441d071400b0b0304064146480c0d1115020b540348250340b00303003004444002c003c100107a510440c0c02070300c201c600ca000303e0b8035280c041e030180c0b2030040002004038a500022800c0c2100c8841d1000d018100003884585a4010034100381d5115400e2103c3e00c045101001000ba00b481290 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 827926447 1250 827925197 827925239
    0x1a1503070801060312050301060530040c0302010f050702012016151206140d03030605060a030920011b06060b0d0c0f0203160305090a080109030c0c05010207030c0312120501080106 79
    0x21f1030340d0304000e400390160007210003540030342810464105110841041400000d01d42d201c0320040d600e8140f03401009030080340000c900003000444000c000720b008bc000d4500007903058560b40042240b00b00806402e901422031030951f071040b1113401c0f0f128850070045d00041c00f41c250342c569040c109104d010f89000c0c103021800e061039161440400c140c1d4074020799081c4020003158240440b00d258107003103000d84410f4100c2c0d07601100010f4a4050f10740c15034442c4803c41d01c00d0b007d00c15010780101e40c043c60044070120150110703601018a402c00c00c1d41c84a030a0503c1e20481d00002c180d502e88403800b5003a0450141d0500b20780d0364030340079002c040d0010f544d2040902e041c8011440c0c110000400d215020122900805004021030a11031980d0703030302145009420002c0c02000048100e080c000d180c2c0c281e590060311414401600800c4c1075202181c3d50040c0e0fa000310105200da45140d80325440000c42030100020004004003d9200d61814001c0b24020303d41080045900ca0801018141c0d44200103014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 827927697 1250 827926447 827926457
    0x130203092e1b0503010b090102010e0d03090203010609150e041514061923040b0405040501050f0108030a0e06030c1e030910180206070c0b040905100902071a1503070801060312 77
    0xb0500007980302c0c0840c2d054540f001d1501d03490701c1f41030006038090064840e1582180c024440240c6140e40d05a03c891a082d000310b000788207180d0b413040c5a10488413980841070b20420303141000c2c0801d1340603800c025007051184003620a01e045281c0207070102c4030031115840c4030110701014880a80b803c0c500000c048220f00c10101130540c034065035580504151000e900072000b01000d0f8018580d910341c0400c04411001c0c00c1445140340500c0c040e4000c202c1144c08010001c807020020500307080c0003054640341405615899039040640c4108180c40d00300400c21140001c0030001e0b60301010b20003440450100c0e40c0c00c0714640304d06010350801d0500300a46000d0042c2e070300d4040c006424041480d00c0d4000141c05544840e82d82550741001d100760001600041c2004a0000300059516402d901c172030701c0f0b0400800345804c0207031182d22803800c0c1d228490002c0c2c2004c4000d03103505850075a4484150f0050748481e0050202001c14000c83e090244940c4003543e6030359205010001d01550070384485003e1003134540 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 827928947 1250 827927697 827927741
    0x1020a0c1d0603030c25090e0102040603060b0a0509012a0b01030201020d0f141308030f040504180b0a15150203030a0e01050f040f05030d051503010e0705130203092e 73
    0x282960786c03041001c0400300078001d961102294038013005e088050200e0f0703030041c007185100c2000030380030390f001d40f10303010019141c4240003c8510300034054038032250241c2c0e0741ca880c0c843d0280044070101901d907125030020303102c0b0b0b0f5018154075400a90003407030f0f0301c03e02c00c0e40643d40c5503000180c18403c3e200300150520a0910354501c03e41d520400c81c641039260603038a1a11106052159008007040e6042a0700d079100002d503020b04c06507100064400c460007181c0c280070400d29510b0751149080c01610041842c2902004943c0c8100c140c0c21819912301d0410811004035588c1c07070400d241140009880b80540c00020921012040500401c00b41a1440000307020508000200d0740c413403000100040d106a003c03182030310400c030082c000c44960038042c010511550030211318516a0403980fa080600c03940ca400b040d0103002801003010421950010901031959049201c800c01179440100003410034000e0003a502d040a41032103007c480c2840c6800d03404580c00082031150100c41b50700765040360754000520 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 827930197 1250 827928947 827928967
    0xb10020105100b0f3f0118110301060c0f020a0605070303270305250311210307051312030c05060a0603080d0e0a0b04030f031104030507120201020a0c1d060303 70
    0x884221000312030380706109a00c4840442c5e03100104014045000a001034280e020300c4622620398180c0380700c1410b05444940054584040798403010400112035070900c01041070783d014541440066025402c140407150084c1d000441030800f503001000456130210340c203414140c2c1440740b90080441e802d0154800c0c001c64110350b541701002e110003001c10200003000c59202c502140b28800c50110440803000c903020310301c0c01608100c44002406000e00c035581c076140c80491070003038600241c04203a6100386542c031000c90448490384910b03220700e4010303200e1000045007a1519842951240650750f884c001c400e05142050170280080c00c64070980f41800d04c2400451401d0080341c8500d2048140000c1034110380c104d25040c4900040050b05036130b0402c041005241d08650300a054904079581080300001070084560b06000c1d50002416035800310406101c1c1030841824262042d0050049926034447d80c1e0701d0a1100405422140c0c480100030002c01550150400654000030210302450410301050303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 827931447 1250 827930197 827930227
    0x130206120901021e1e13030506163b06070c0f05010207050d0308010605031e0a0b0405090d0923120a020f0a050d2402070602041e05010f08060102010b10020105100b 72
    0x4c003034209003107170000f04106d0141310700030310717200070340c1c0c808107565491826407018444041400314820102d04903c0111252160841440c91820810000c5822152030b10304104940550040c566410400400888021484c0340441c04000c01c10b4010980321541401e000a04111041c3d00c024000c1c040301140b01c001942120300c0605503695450090f03143da84114616103860040b401098810540b04103001211100c0c2c2c0090103c0081a1000e0000740c81d90b440301c0f580e80640685160004202c14000c0c002050506040082c0c404402804034050140c800003c00c3e0020602c1040300590100d42c1c1041142416000c4589846c1d048440a48440c41d10300810403005103500d00401c500c0c0e42503003114041c00c0f440d1122040c0544c00d4811034407000d151900100951060052280c89100c90612400c00c0003140c0b140015074806941c0c0e0b0001d480b060341c0039100d641000d01800d066548880c12000192581844181d09990b90780c000b02d0542815840b1441180c100c1c1c00c000c405500400c01901c2d0b00b14a1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 827932697 1250 827931447 827931487
    0x30f010e060103180503090a0b04180914150a0c03020f0f1c230c03040210050703020109080f030103030e0d051e0a06060b0301081b09130206120901021e 67
    0x320121256a964540048005141404c1d065450551408010003070200000207840b505a0540741402900d4441000701c0b4240514031032040d071005c0141c0f1144403106107400202140d48100000c1107032868040c200c41c1056a8101c002c1c880011600c10000495114000c00030f102e00340d400c0851600d0303008800c020343c5201e02c1040031100400000d403411550458440c10a2441d19210100004116180324911010700d88011100f0705500b0001300310b4032002e0034110b80c0140d5008068034103036120440b0a4810f50092802034056560b40ca041d4404100e20f40000e0118100e10030b02c095496046140180480403039003010360064910300012000100000303024035071101c14042c003090100348980010711703100741404000d0480c0c1c100080000c4e5094014082e40c141c0d9840010764a048210521140164040000044c0d101c850ba8000c2100c185402c40e1144405002030011071800c1d0303036408207031044207003034505021a239400100f040940c142190001c00c0d400012201c50719103200f801c80c101c1c4a41034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 827933947 1250 827932697 827932709
    0x30b03190b15010c051209010e12030304021c120c0b070201090b0f09011d030c06060d03121107050f06090c0a05010207090f15080f0115030b0f04080c030c06011703030f01 75
    0x40c01c1ca6280d480c4e00481c1585001035100b021241c038171b807060a0f01c02031b940151214a001c82e504070070301481803030480d00c10271005070402e00031819a91140c00b04011141c041c2424080d407044c40051401040c4c2103056820f9004d4107840340c1100c8401403401c429040001043c5400316450043e04000080c00c242c420b680122854503000341540f01c01074100d00401021200510051901030052441000030011f482200c0b8400d05585850340c1c1c9400f80588401c4c0100000d0004100d4240c039018100c0b030741e1000c0b94429106100d0b909091403541d6192030880c05150b1102140c0c804420004e03001c10800c10780e10059802c0da2031032401c41c036042c0040e5803220140540103010380c61b20b034002103642803a404070701900c2074189540a07565850401c6070719200c014504800550800c25031a6480c61035200c03010803a58000d0381d402c4141da5681c000105508003070300c00c840d010010007943d600550104054010f07515041b025000a51528502c00b011303403505203001710b10360410701c00c10401e101040030300d504480d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 827935197 1250 827933947 827933971
    0x6200604030c0305040801090f060608150a090807060618060506040b0a0e0d0b012601050403121e111309050402030a030f1e08060405090f060a1812030b03190b 70
    0x402c0c2c50155514001c5801495040d07182032642c0c0c0900410582c41d03021107008103010001c207a00c862300d060300c426141d901d19045d901d5103008a101112181d02c10800744e4041d829050811617990f0b82c00007502c041d41c1c0412030040100380e200040c80d00c184107000050600b194503d241034a010003038070890040310381880921001e2000150540c6544d4050b20826500c401c0380c1140f0768607240c80302031007a036074510803d14102030b001c40b0421450500c5900d00603901626040f00008440080002404070700c254070303031411010007541c404c0056900410b030f0807210046005440740c14102d0050f03404007035540640701d107900345014070016071004902c41030405d80514001d0710001164006071403846502700a021601d1803105401c2c805a440000c65025400448084c40304d500d0320301407180d844502d03081071115908404c001c0b41f902c240c1a405007880301e0799403103900741440b066200c00301038440305c0e003901001c82c2c0c039403455a54500d0180044500c040c038450303a9006000e12131700d400009403c01415580400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 827936447 1250 827935197 827935217
    0x30d030902040608031909080c0102030304080a122904090c03110604211205120f090a0204020c0303060307050a0b030705091809150106020d14180306010f0620060403 73
    0x34a0303c2c0c101401520a0204803544c0790000c0105405102020840d0310000da030092003ca16008040380104110405900640c05c644644c0c8403c855640041000024040c6100c1c0300c402c004000d00461142a1034604011070541c54000e442c02034030112aa803900c918545100e1800091b80401d034441641e422503168038101d070400703012510a21458018400498500d14036910f00e08060100c040f5081c403481d214a61269684001c0e1b88034094020715a404100c0c000c0000c454062a02a0711f0f8800006c1c0700300d03454400e00e50003041c220b80c0090f0035600d894000000700840d6007810000c0000402d02a15440140e601c6c006003800640000307401c107820050001420720b8169125104200b0625265401e80301c94140003120540c4c1301122071002815441c000d0002542d107001288410a03001c0030b031108896100301c0f10400d000c0d0b42c410800c80102c070401b0986401c0d562000c10000e4080d281103442c0c1e00c00355003003200281c5082c45e0409002c4c0300f0900113182801c0c41e0000306617503401981c03500348017a1803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 827937697 1250 827936447 827936449
    0x4090507091e0f06110a0822030f1502040b091905180a0c0c0c06141b100c02060705090d151b031b0504090f0e1b1906080121080a0e031506030d030902 66
    0x1610623910046a03040c00c80010080c008808040442903100f030504400307072102203100d0010385c091340c4601c0a4051043c0002c0481e030504100c226442d50142c0814071403030b501c03400026902d12010226281c03c500d0503041201d800001d00c5691210710490401c25080d0701150f4500c04101701074000c080c10011b60450950654901006461840799420030544450200c4031042d651500301e140407a8043c0d0803e080d80c051140080b420501844190313450902e048200c80074480f20030380700c10080716642440402c049a0310014803c040d0104c4c880f105c102c80800f1400300060036181c0d14010505c1100c00202c03611007441c0c10102300da045404914010406140c50300201c0020702c0703404c07000032640c003841c024586180c02901445540e440d04840301900712078100c1110700c9c5510703036020764008030300400014001c48a001d142c020700c0080c5804030040765109551041010f8000d80c1e9540045110411080800c2c076082c021040004084060300907245450400a55140541042c000616035114050425 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 827938947 1250 827937697 827937727
    0xf030b0411190305060105031612020708040305070f0e0a0b19090e0d090815041e1211030715020a02030702151b030f04090507091e0f06110a08 63
    0x564400410811180c1ca80701000101580040d4540d40c1c10b85401007240078440c06841082d01401041e50340a0650751140c6040017078a00030200c0b00d0074080c605800345070030f25030b41c00205242c40c8640d840686481c07440c038002d850104160440700101396000c10030f10142410070101507004a4581000c2047c0c603403240481c0c00d0072512074580000c2c507903c0a003c113002c119a00f090080c004888115441150302240441e00c0420700d01406c1125000b80034141c0d81c41108038100707130b000b40c044c8140484132040c6000ca050002049003003115295900c44a601005811500c4000844040405185851100e80e603074206400e103c20400c25041d07001c40c0c8071070f40c4d520800985030081d6000d00785075003084105005a0450b002040c0d1440c051800302e213080c0303d4003000b105807007500080e2040541440d0405202031f0203000000c000c1030070000081e030001900d20281111400c0c086180c04400390240c00d101480c01c007088a60400018881d0000c0e910300f0f41d0500060305100e0701e802941326a00c8034003034460550 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 827940197 1250 827938947 827938961
    0x4020d060e030c010516110c04022203111036050d1505090106120f150501170d0302210406110406020d0201060e0105100e151c0e0114070f03 62
    0x307662001143d00800390034154000c5000358104600e41a244150400850780509000b00d0700341c00d038108080c086810b043c590041d2105c1c9551150707494841c03040391010011350343c45a00076901200f1007603001c071882c00c100c42d865510751840e260161402c0c8a040903032211020021107111810460200116005141c2004101606d001490700d0043e000c107082100924004a2002800500e40030120f007041405106501c120b07030644404480740c0401c0e889041030109056025245a80c00c040d4610300c0301308074416113000e04032504d6611450505a1800c030f03d08014070070030343c1c207040c070401ca40740d1441d030298070400b11207280002c1c10308207075941e2030240003501304081c803002e9602d030100d00828516004100c692544107641c1c004c0107810f69175903004010100a100341d0340c001c0350f4841c0048030107208100010030340001415105900a0482051609a101c4140d0344a00c090f000b202d0450007107140a00086004190020710241e60981480781c0e2079440945190240701458101c9108540644c000e82d07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 827941447 1250 827940197 827940221
    0x50f01020a0309060e0a0c032a060801060315030c05120102210106020d1404060806180f0a1a06041403100c02060406052212020a08070f02120d0804020d06 68
    0x951a0910040c0c082c0240400220440b0f9090802840000800380013501480c442e4203c0c100c08032280c07445d12030080c9042c03e400d050020802c510340702c1c003000003c030450f4001801982d6074081c2d19858600001d04031039201d90b1450340250410020008078102c03a030501c0507100c045071541b0302c444000308407500a100f01c07804d01014504420a04002009404035075048030582c0d000d407548400c0408045401980c600360140038468140005c0c4040c510600425038014005411400d084103400c5c1d04103040c072030850740d1240042d02d080c108601c0c48003500412029070361a50007414180c4441c1c0000f81d203800385024403132010b454148120b00700d940801020384072400c103403010480e619030000000e4841d0002c46041d11102e0801c00420841088944400030720508040c1c1602701178020b55a04000c2c4142d01611000c521490022030f02203440c3c0001800c80c1480b03213408042c0c240742d5106008010905160415082d008106d0545106800c520843d900c1070b411500344a17030700380300d140c058000e19991b80c0803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 827942697 1250 827941447 827941451
    0x80c0d1b09050a020901091205072304020c010f0605010309031b0218040b070e0f180c040b0f0d06060905060f03090102120a0b0a050306070e0d0c092c070b0412050f01 73
    0x80f00c02c1c1005540180719108003030341c0b1480007a0b103408508a10388000d910040265000d8002004500c0b11080c58040540840840842c24440c60300050309907004140c0100c840d035510880711004081522400c4010102030030140a4200252006400203407440030401d42c0110036038821b0110746e50111144002802c00758144814141801c0441003a00100c40b002c0100d0701c005821906450700258240458000411580c502c8410441031021040c0150610740c54036000c0c000441c0c244d86c1c0e580030b481e60310202c0c07610341c6d1542e00d0102c80c5010384509611a0003800800c1c2400d2141c0d88501c03003201c82d581000b1030bc6035601d4452500407030091081d10702c0c4469403204007050140120303840d0003100c040041101c0c424480c0f07490318101500c0300010743d40c2402050090344682054100b06c03250a5013207001d6141e1100503540d4020f04000c3c0c8419032100b103214070359002025001c1d103507209280b5580740b0a40003845e056013005c000c8415841b950284064541071396a03c8400c214080101031a807502d100c0003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 827943947 1250 827942697 827942701
    0x140a09090309290f07020d080a0201090c0f080c150d020f0306040f0b01020303060f180408070c0b0331060f020306030c060906030a0c090e010303020a0606080c0d1b0905 74
    0x10b100824078001c0403402c0c09038400340c2c141442c0f844400e01c02c1c0d11454a61503d8003080398640302d65540b00f04404c98000491035000c002007520040039180c1141183c0001c03070405010b19001244151542040510301c2e01b40d035082c0000540012844589041500c9201c404003213908403008030b00030a18221519400014008a81c01580c405140188402e55091007a04107000014091384c107149206401a842440007461600c4c1c05203807418501d8000d040c941c03030440c40d0741d00200304400445003070380c0300e01c00007552000f0050a80d282200074003503041d075141036052051240e010301e071601484114510100c1e0f0012680200200e05115480d031100042116070f60580180340079400840300030348070307004d9018080e1103414100c046944103100203007494519075414845600070840046c060b002c100402e0400300f064002d503400c05019500030f4001b0142c013805490701c0026920290040c04154000908869031500e84100300400640c1c031080c03111400802c0d80940300c5803c200d600a03041c160900302 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 827945197 1250 827943947 827943953
    0xa1a06120a1a0a1808030a0204050310060e070c110f01260108210403020913050a0f0501051b0904050910060b0403120206010b0f090d020409210216140a0909 69
    0x26a82d010340b00c5000c40b1000b503640c0c1a501c074049805000c43d9601e0049001c841e00001040c40000b154031108207600141804d440f0b00200b4034048104441800896842b1000d111944c0003010171030340160f1fa442e11940048180d9a100101c03000380b5005070080890042c0100e05a020b0010b24200c00c81242040141d0360b05002d0000100c031b400e1151b41550700410f0003a00c81c80c0d518401c04502200e42c200074600d058a15428480401c0c4010000f005d001001c81e0407200007141030149c004241d004000c815101c0209007402404c4070006450b460103411040085e0300704184100943d848101c0813540042d01d0747c0c031a901a4103040d40074100110315468041d002c16000c010700040c00035030f40903c08400704207690110580c0c2d01d800a0081e11f0441105100441308034411000910a585024003401c02000a030360214094480d8034034200c03171f4001102c40a0148210f00c80b107400c02c8494910081c0010082d0134910700010364140a40c22080e08481107070b8040361141c101080003407100e85800c024071f444900b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 827946447 1250 827945197 827945213
    0x2031b100c08091f0e0603161b0506090303191a060c0703020306090703140312043903060509011a040c03110f04080d090b041503090c0f0f06020a1a06120a 68
    0x43d81c3c540c00704180007116040c5d81401030560340b203220000c1c1740003000301c1199030544a40340d68454850740d0b1214215508009001400781d24002c441640065442e030410b0071108180007982160741080034500603003009080c0707184100300c1002d003040c2e80c466528000c0600e1141004241e400c080d4041c4102c42c02e100000b40d00040000403603000300e8001e25000c80c2c034405241c0381e114228403041c59009007004500424002041031240e007640d41110b00c80c9624800036070100c801c12055919080300d04003000c00520589000c3d0990200b1650020000813170001901c601e1112140036050103140d0f910700c5881034602a50203070107020702164001c0e85443d12008080c005030b00034011607800f800707200d807401a4603004a600340190307850141600e06090030056007020558080700c41c40e04154480032078402007006103440304094107003510012489402c003c4140c100c0000c9078070140c1154400160300d00407c1340c100c43d02118400300307544900d194a80d83e0024a045202d207a002d0301c20f00403109036104100481d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 827947697 1250 827946447 827946499
    0x1305010b0307030e1606141908150103090218060d0f060209031e0601150302042c01060921020a050909060a05220b06010908030703090302031b100c0809 67
    0x83c0d0b4144131100702091025112901c500e848640c1c0d400c007500034800c46025064284001212405441c103003108100c80c035000007080300240010480303210a0081082c1810100074201600382000d0014219950104085400b4000c000400f101e896012813407980c0e52003400c1c61366941010a080ba00103050921a000394048111640b182c40b50307804118070004044202402c0250800150030280c0c0b0b0a0b0390200002c00c020300e1401003550030400410003c0199a00c3c0c03200100c4446020001850910300002d4000c041e0094001c0c00740d03640b000c121007907448005449480e01642c074244200e03942d1020909070003032608050b40c002500c504000034050300081003486142e903a0400d22183d00e8100c040c2c0c1420018001d40c0c0700ca0343e00203649402049140d031203180c1001040c074ac502c03882a0b841558600b15002110100d00241102400b0419850304103e10982003124001020f061615240000c0c19403180014000911030b141014034140000401525400c11024000c03030b01400b81441000f4608140c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 827948947 1250 827947697 827947711
    0x150d05180604050703060209040219081b19050c01111204050c010507030c0602220f03030314060109180204030f2103090c1a0409091112010b0a090b1305010b03 70
    0x8240108000c08400041e403900554001c00074000c02415a211603000e507001e0100f0941040c0c0803c45078944035202003000340240002d03600c0ca0024101402d10741d002c140310210341c2082031070520007007042009140840c4100303205410600d075640c0c20340c0b0100303015001d0f41100c66041640801e5208900580c0403d5900c501d102c0da0688000703ca01710010f44181c0035020380130f0000b40304801c1301e000040c95640146140d01c2444101003145c11101004602040c4540180c100d406146208108054040c011800c0d01c1205102004241c80c000c0002071030012036202e607040d0029440020000c1400940c110b8001e141c203c0003d54280f0002d0401c1c4a0341099907050243c12094444c0c101001d500c60f00c41c03900c540d98458460244586041d844005c0c5003048440f500440004101c00683d0410601c91041824131035084441c0b500b551004002002c24401841c40301230b4140040d056955442d520340c241610100c01000611510b16004140e04072800b49030000854507150002c03405401c0c680c0550b02c02c0c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 827950197 1250 827948947 827948971
    0x2060712060e0c0309011d0f0f07080307020103090c0b031003110915040f02040b030f09060601020604030f1b020d0f060507110a060c020c100908120406081302150d05 73
    0x40c50003404011507019209908161042001040b100340141c1c2c020f6030800001000800c0050703159030541804014602c0020f42c3d60b00c0303400900c840040503c00e40d2a01c14816002d02003151510b4a41c42d1030384182035009040543d01c01c0c5203820800d0030300c007850181c6507030303c116902c0e440e01001e801003210359400240c0c0e561458540c00911443d00d201d4451003041c0c0281c07464020b040c00f90600025040c025555030203030b038080c080481d01c0c00700640a54400c403a81c0000340114180088450b090140290408e411504008100004207800050701040900107107885c0394030309480c6134001400d202c0444000d510800000290050051104c0c9801005025581c1006282c9640005440100e0a20440d40741c5401251450002c640b5a60204411807110300540e1180c2c441c0700001140f0004280b11580800e03407403c028080303141c081280d18407405c0d50142d96441c203400c0c110003400301e500017070548019440d800020004c64840807201007501c2c0403e06820f460701004e00904020302821102c00384041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 827951447 1250 827950197 827950217
    0xc0319120515030a030e0609040903030f0501080d020d08060103150b131401020d120b040e03030f06090403170402030723121207021e060a1205090604030e0d0f12020607 74
    0x8010302d91002c984080100200302c0103101d55000d403034855001d80030365441401441180c1441d2034078000d4030442480703a980040d0402940007040308a84c41030700141b002d607004040c04910349400003000c0b0702d880010706044545036a0280106c0140200e8911543c150024003000204c51900c440601031500325542c0c01c448150b201c07420300c08480c00f0b540410b4016031020116541c154015400d10340800c04052021840c4220b0401290941d9000e0103a061aa4000810403036051000b458088d0010021202014070b41450307200105851102da068101181a0001042c1103580802c0141c0003000c5440f00c04400c1c00d0342c0800d039908501d2410403240a00d0015440e0f02d6090008240c05d0690180501781030704090103a000d0040c03031400c940c5074141140f44044407900c030390b4a80019080c0341d2090340d0350b8400000421161001d541002d4000007666000302c0034800040e4001d451822141420395507040590b44072f0801000000b07001c0c00280500340b00c031881036003166010403058850801078032003030148 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 827952697 1250 827951447 827951461
    0x30c030f19031103070c0e010e070509060309030c060f1501080108100518030d05070905010c02031c030f050a0b03061f150e060a120b18010504020c03191205 69
    0x440d050200405a9003009404400d80c010030080004024000c3c6003002c114680e001269285600069040d6054200030000b00031042c0f200001074090405004c40c480607080119010b40035016007108030707125210201c0010100d0f041001507400c103240e0f0b0700450390207041550b4034001c00241500ca1202500070101c84204c130354050340c5914102c0c1c1d5050020018249429044030082401504100111040b041c400005940400181c003038140300d4000081d5a052000c00a04205030591003941031040164148000d0b81c3d011940301c00c20500f403070060305542070000301100140701c50000c6032000c901c5c003c284082c0b00545d038400e50841c030040d01217540b144c91b120607541c428070080701c590046010082040c006205da1103030525400070b035814a03042810300800083d00c9900700340e0103100000c410048010b80b2a4150049034580c20058514182c040302058001180d040140200c3c1c0c015070b0002a1001c000d003007002101d2804009080d50b09941051110040490801c403805014450900c800f107031030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 827953947 1250 827952697 827952703
    0x20406120f0602181003020d0b100203120c130806060406080a0b04140c09011d0105061c0b0a0801051806070801060e0d0204060306020a0c0311031819091a030c03 71
    0x44141c010000342642415681c40c2006940242c21a100c18000000112004d4441089a021000094501684522016203103e04640e40759122600c41c52126420303031030f41c9401104490002d20a0080c078441e40da9240074900541c460300d09100e800440724840001d420758042105405203500700c40a0086035078a400079a610780000002030304120a0402290008014915890141d81081c0645a0910791400000e0480d00264001070b19011010903481508a15034a6030380540740c100c0e0403c0c100100d0841c84401c480040704600d402c144d403410700441a9860518a00052402000a202c0c5e0b02d001001090300c4420440f503d00103100e02400b141140d030180303201c58181e81c0c9554400d10104103a404001c40740d542c5503407d9030090b554440c00f202181440c00244100c0d0403944608010719039503d0014520188480d07101441e80040c001e000f208400030000c894222030031942c3e0203403040700d20a039602d680c50030703400502161725040343c240340e149528480c0f0498a000f01c0903185900f01260626032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 827955197 1250 827953947 827953979
    0x150c0611041a0a0e091005011b030207090b0402040314030a02060a140a02030726100e09030f0306061306090f090203040b010303210905030d061d01050d0f1e020406 72
    0x2d600c0244a6003651141001005000900c149240c4000400d50f00000b181d018003055400ba001c0c130458500c04d000c1940c010303041001c0d030043e03107001c0204d1901c136440094442049001d00706441d5211010741c4215611a010b0354050368000c118803031000048041c0350350700d42c081002200540980d80021f03111440d24412102006848480c0b66103903a50b0030000300c02584000e0510090100580c81404a42c42d0361003a59a240c142e00711111281c241040c071684802d0142d84400c00554914040008a51000c0142e5181c8944d4142e100e0303c0340c44d403000240788c41c01450f0422080d07401c800c1c00020407a622480840c12500c03001c3c0942d80f4a91205104d000380d120445c1d0240001500b9801040020f1189004500814000310004164260640c021050f54100c20050707179158804541681401c402d0720509000f000058080e40300e0204002510005110500c03a00d4410396001c182d91050001d10803405a42503401440c40801d11280b0581c1c4000d80300c400c506a00451420710080350300040103000e09 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 827956447 1250 827955197 827955209
    0xe03150403171603020306040204030f200f06040e131514011403061501030b0604121b060c030f050d020c0105180d0c0f1401090f050609060c031f150c061104 69
    0x4004403583c00c0090f4043d503c05071403290010f908100010200e89892900721510303200e0201c4050b607083c41400d12000149401d0f5640c0f098211812040b11940c0d203404840c1201c400c40c25640e6507a40e41d101046001c0c40081c0b000d0080d08400c51444c070981c605078001e10454140a1202051740d0300c420200058406045110b07805074000e5001c1000e0403150450f04402c21014900414890341e10008103080b5041540b003441c4110503071110404220400c56076032405024400d40d20511840d2040060035100300050141c188000ba804103000301c2d214408030742c1e410b009003000750f50382c0d0320040101d07000304011200700c62115078031011f0002480021a814070030309402c0e41c40d811200d21a844111a0521601c000c80304011182d908003071095080c0036081c0082d02540b40d00e4000c44003400c0541c2802001091064660803078020081c00e0000700082c1c94011074024201e5841c4081290a131943c4c11003504040046440c000d200207031340745d02511411403d84549418040b618000b000785900b07000c3c2e40141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 827957697 1250 827956447 827956471
    0x60a1503030c150b13021218030324060a09080c0109081e0106030b01030c03031107030803040b0705090409051e12041401091805010f0b0a02060f06010e0315040317 72
    0x100041000203003010042484420f0000740080007400003110444461030038400b440d0007050204d501010300c068a40d10400c8080724020421260b010583c6a200c000d107884225400c40038140e00f81500012200450100542207c2e50341c041004060074900041c8195085441515594007480d4400c400c250125203030f0748004d00e03a45004c1d2603120103102041c1d1160006669803140000812a000a402e00030350107501c0e9004480d046007401000320803442c003c85010b0b84182e40030000940540e00f117980c46a0412402140c603140c0103011507280c45108106d50f441401c0081031810701501240c40030319420002c1e81c0003080c041c0c91b00d00507241c42101c481c03450711850920041080f0441d030380014000b0641498030b0014561a001600c12030002d04581b008040d9841c0018410103120601150141c80240040c5003003400816000395902c0c40140290b01e100c1c907002c041f40d080d034018100140034880040c180c841614003142e05580d140c4040340d0039000900e16042c05030b40d0780410758a180c0038400340f07251 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 827958947 1250 827957697 827957717
    0x9050a02130e13051c110d0f0f091503140601090302010212030406020f1305011d03061515160b060d081617030103033b12011b02060a150303 62
    0xb0218040070080c020050000303040c03000b10005000348106802c1e060900da10342e80400070701000070101c01c908186142c03d540301c400500c1400390008000f8102240920702081c00550782601180e1070320541e8001050611004840b6090360703090342161055441d158a02242ea503030700401100c2c2c1071940d01c0701901503080340d201880c01700707007000040d0b910038000c81d405442c0480301020740310036606c0104618640804110b0512a560344401307030108440c052a204c10003100704100203a25000050725a002010300010580c8a07920f81a00b0400c08084000072140c07200d080000c101c41200300c82400300d0390340e101c48000a020385000c4880501c3c0ca50015200d609021100300144981034840d50241c0e0400e5000c2002401031b44810021406076100703030b0b070340d0394002441c03040e044402e82e501107070411031150844140740141042c0b440000c000000c5840001c0c12440711040c80c0108444003240750000c40e0340700040e4600380c00103001c500903940100304100d040c3c542c8100c00807080150000030001010303821 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 827960197 1250 827958947 827958959
    0xf090b2d3105040f0e0a1b0605130b03100906060e01031b0c030c08071b1701050702060a09170a0e09070804020f04050402012607020132070c0b040b0109050a0213 71
    0x480300403100020500025441000a010f138039243c0003503403c031480940350020007e10360071003820754003d010394102581405980440c0a492200c107001d410b40205010000031180d04254803444010040c540c01000030540307615000703100313011803a101408641003581440400d0f240100946031401155240100c13071001d650b080342e035100036040548140d04203000c03000c04138510000b4845101050681c021269150400c884a8118001c0041240764504000c000c40c0703036004501d26a014282d4040050200c1c039502c0d2842d0494226407001c1100500407070b60640c681d411022511303ea13013044a10403200e642da4901180c03880d0040368000d42150b00b0840c0b0051600b00f0785c001c9500540f050501c0302d07600c1c0f8040d0484405845401a0302d500140003030500400e1034080c480e6006003400950007090036101c060145001c0601c895850452940c0b04001810091050107650b450a91040e54070342181028100350411540038081c20440c2c074500300100d005100c00d0700c00c994100c041652a62486840c00d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 827961447 1250 827960197 827960201
    0xc150304031808060c0405090a09020a1809051c03140106302408120f030406020915090102010605012f0708100504060c0f090b2d310504 60
    0x21100c060720500c040003c03451003c140305a5125201c0f11034940d843d00d18040801000d403002034210a061403600040c0700268640706465826240050324400d100104041a00e0007400040000b900e23900a1080345400340305580300072078426010b80c0c1c0c00d00c6031424416042e0b014510a12070000802c56110a0b41c1c8003400c0c0b0b00c10216000d402803202600303a403040c034100e01035803041c1c049a0710030100740c4100c80342880c003511540060314404005000780e500049140780c491040001441c036200c40400090300304200340c0c04a0b150040060403007002c00204075280c40703080d0800709816015500b80040482e10b5441150030030f810044000e20003988a8401d1290588200808404d1042c1c0c000c104e8041013022042050f031405c000e40680020f914509420042c044030618400d003002c2104400755516400e41c07142c010410395004800456880e003540010107a070403a140126130302009074003283e12140140d6800b030440540300300d590340c1c05901c910b00300020b0800c007101036800520000360280582d041070303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 827962697 1250 827961447 827961467
    0x813030302130806071707050d050411040c0906030f050c030a0b030a050607050909100302060a1d090a0e210406030f0f02030c0705100e0a030804020d02041d0c15030403 74
    0xe090040c9040300c5a035a211945800ea00854102d61040007800000ca90108002c00016090341c2410f05504059400030014400c10609083d071503140c8012405011040159500255000f0010488080c43c03030005090040b1602c0381c038010918110b180b20f410300c01e81c000c0920811103550094915940c0000d054004d00071541034075094441c0000307400018401700496405020303951261915401284100411410000e210a03d0300c015083c00300010786908064a0701c0d6009401d000c110780d01803440800031422512a665406130464043c841010b903d07030700c1062000d1101041e40c1c80d03504401045040e50320786110282c0c1c0602e08110402a81d4400e50010354408010781c0081014a1804201d0040c1d80040c0da0529000302d0004080b02040000c21600380640100041841110000600d55889100100d009000c0c0200b14001408642c0d84034104100603074010010007501c4c0b0610050050401c00c9607802416225901c031801840c500600d01ea640c01c042c54001524654907030360121017550b90 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 827963947 1250 827962697 827962703
    0x30604230706051c090b041e15020307030f05060f040c050d091118070c08030406180308040212030702090a0c0c082232031905010b1f0813 61
    0x150a8a031088030051042200802566480701d890b441d803800b03e881c00c90402c00300550380b24038108100e00080d15407000d0550064101048012007400e66943c0c80e14a00764541c02040d071603100032021301042c0c10740c0c050f601410361035904100c9843c009105d601141c13030941d0015400130300e0850016441c5000d41000e10716802c030307141403030602c80b0140f03607401030b41c01102084a07402d4410458000341d051001083d000d030261840c002c2814245204064085001c4080c090f1407c18000002400d00110750130204101d071042c00303110381104160800400800c41039404900c20240a0301c072102d0080c0c0003054a25158000f00a02e5560b00e801c1c1000d00105400d042040500210349084404194540d01800803c060004642c02d8090743c8c0c8240c140000803a000800d9070b8400f42c43d42d01c1060a00d114403078202c1e41d40e8074010714138500040001d10349442401c10401056803040507000300003041d0881c0025480a440c800380903012650400382c440c5000c207240f00001d1069001448001c80d030b00150f400140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 827965197 1250 827963947 827963993
    0x3100b032e150b0409020c2d062409041109010e041a0c0403060203060411130f050907051204030c0c320f062a010c08090606030604 58
    0x99160301d0500d864100260840300d84404489801c1044400d00a20281034510311aa011090502d0200c03000c6000e640101c1e1704680d401f10300408645810003004802080c520400011800b40301c4c0040d000103020200103101d4041d040c045541e1003000441001c040740c05820300003008100c00188006050300400686000c00c49060203c0d403a105d001056020300040d03c0c0e074014624050070100360609640c50300b000e84980010401c00750407403400c00d4400b600e0740080f0140c0d407600c0c3c00000402421030403001880529000a9159580030001100340842d080328440b074001c19038941c100260003d0031100040454400c12541680115946007070f42c0c498031a041907800e1a07400d48800003404002d402050088901c0d5100d04002c000b130501c000c0e001c05038454405174990403400460b041d81d4085070028022003010541d00244a90350700d00c6d20030461041d44d0000001c04c00a0185e004c0e240343c0712040080340014010881c40f40c004510680305903c0034000344180c0d00d542d95121003210081d40d10b03e420302 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 827966447 1250 827965197 827965213
    0x513060902031510090f05010c03050c010e0c040e01090c0b0f040b0a030209120a0c1a04030203010e030a200a02091504020d14010602070806160c050a0302151503100b03 74
    0x400385101460050942c40d16441403084120709100500e030980002a040c4149071404000c88109840781a058610038603000483e407100340b0341a50940038007803c5101075400c241103601315400001e60f050070180c4c1107405010320350b0585a003d003284d01010b0041c00f22061400180030500100d0000c0010b02c0610080d5071800d640c54441d41e0141d04618400301c0082e8000480c40c410340343c603004a102098018000e0a0300f07c00e04c3d6102520380904d4882c480f071004070444a20200d00407401078400868010f002801410a039000e907a44941c800210307100819100403940c03210700002c8003048901d040354001401e61281640800c002e01c00c0c002c0400c0810b2040e131500000e25211400900301142d06c0c4840490788000d0388010003500d0905030800b4085600c100d10400c000d000000304142c02144c1895a805803015040080b1000900194003900c14070503021407000f0540d0000301e40c1d1a2800c0c64040e42a29103e504560281c88041c40003e179140e40010b040030842903156108481e840380003003c5901e10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 827967697 1250 827966447 827966459
    0x100e040f110d11161a010b0f0d0c021c170108010c02030a03090c031e0b0a0b0a03030806030a050f030a02010b010302090a06120905060a0b043c1410060f03060302010207051306 77
    0x40052040b080f10006082039176104034100d080070503405010000a82030500340718040180e000d001d184c8540b044030351100c0003d0540c2d170080c015505404004090000c1c94070130030201030081c0c5230303100300d02c0f55010f1144000160f110040c4640034030154540e000e03528042e0504000c6019048216041e288038000c410000300003465040c400c038640c0c2110364003c1110300e8030305040034000d0f4020044500e480c14201010708a6a901014006880d81030504400c1e41c2c070713024082407910307034a020010000e1242c0701c08200310b51400009800200142d600900c0310048080044090b1700038096090f401c105c0300201809241c2c0a0545000040d007100d00000d40c80d1a2a1a0b05140c00000d4035075840c080c1c8e440302344a07400e003018002d4500780342c144640c0000011180492001400402d0f100b40c40040900407a494400b486402c0510109110720720741480e801c1940759116000390030f00c5843d022460700340f0080d0f916402030182004880e0140c01900030146040103002d100351070a041131800590f25180441cac1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 827968947 1250 827967697 827967727
    0xa0f12090803210f22080d020c03030123030307030f0e0d03080a0c08010806060f030a0605011d2a030a1d0304050415032a0302100e040f110d11 63
    0x14040d48103111420f800080402100044400ba229884040c010030400207107030300100d020340140121207442100441e0700d00300641d860007400101002103000140640c0c0e07101c0004007450503500c503105001c03020090142501d1200e0f4400c850203030036070000e010410100e4007802c0c2c1da10704c118050034003039030003c0414000f80da0000403100403004214105c007801903541a13031052013107540b50360801c8545035042c808034640d501002005988221104582e0072142d031030030f005a10b2806d81c413030028030442d42c45032512045400c1c0e174500708214a240f20005050f61014043e003904803111391290514035039840c4c800f101aa4801000c400420741ca0300c3d8002144074200304550951f01034040034540741d03420700d0208003e9a4099007140d00840007040180b0120320f04d9a020001c20900c3e95604030982080c2090200d1031026a0001e54401c0d818401e0040044e08000a1141114116000c0002c4c00c6c1514400c406c80380c0a10700c2d20080501884054002c400b164486c1c2207a10503e0300b03c0d41460302c06000100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 827970197 1250 827968947 827968957
    0x60a0c140a0f0e010315030215130308040e1513110903100f0e01140c0919060c0b24150c06090f010b0d150b040b060c0f0f0a0f12090803 60
    0x7920740c42c41c0a580660000c2c440b15106400d04e8180000680002944074000b45800080c0c818811046da01c1000c1100404481c5191040e04c1c100100700c0e581c2c144041c00c1d03040751207401080b800d00d00c0021700880742003207901d400c03d2004013a48224100f0784a85070060045071049030035800c040080c4207c40c0d9041103400790140c4520b1001c00c5405104503407000f51031414118051a0381810210380055900f030b00c3d80b50b448481c8140194403815010b00040356944404d40940340c011084502040c1d695102d089801c00078003950101480d42c840c4140706002e40d0a200720f9101250340025003111034a8100c062540707910404d65003a0902030440c0b42c15040003030030303908e580742a0310a9a421021900c01c0c0141c1581407003c4490319031140d01900c1c0c5c4034a00f031110f103034001503030f951364841c41c400d40d01d9900c5640c6d100b001400c0d494075550a04100d030b82d40d50241021061603c64021441c5900100003210014030b0382c0002010342c060325981e0b0f4641107525401310f00040c03240c004000700d540181000544 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 827971447 1250 827970197 827970217
    0x70b1305120f0d060b09100f03060308040906060807090b18040b04150602061312030c05070b041b1a07030809030706050c0702011d0108010b0c0313120501050705030702060a0c14 78
    0x15690f0345203580c01d481181d00591100d40c014900b80090390060342c1e9040c0011040a550804041810400e9800c0700200495000203203100c2001c1000b040603442540302c202525040d40314452180c035505400e03140a059840355216000c070405c04240e031200d010b001c0030f048610243c40452290b00040c00981560308280300c44500440300ea04c2001620b0b4100403054002c550401842c11801e4140c460f8400c050400003108140740d01d4094460556201d201110202c3d50029110501c600700762401c00c002a0160588150025000c000801d029510084a840c1400075440f810701c3d03d040e566054440712002048128140170a11507a40820b00c1d41c0100c621a04072030348402c3d0390388640d1001408807074210350040d110404d95040e07441566080358507141500c0402c0d402c0e907201d0015100700d9165110b0140c0c0700280d600740b43e20005644224045d60100c82d84508002e0009a4540c5000c0381d039400115001e40041c2e003c8400704449a52550000355500c065280c0308102c28400d507107031011540410900 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 827972697 1250 827971447 827971477
    0x312090301022703070501110c2e170a1a04090c0b0c060915060913230303100603180b09070f06050307020c04060f0b18040c0c050106050402070b130512 67
    0x7841946014894a17000d84401d0030003d41d800541c00f00f042c1c3d200280000306004950642840494407484c250105540a641912006442199000510b00c082c1c1902c02000c04251002080301d45a02d030050f00b864103c402c0c4460f102302014020400501104242507418035002c042c0454500d84034130050001ca0302080040500e42001c00c0f80300e140038410189501001040350500c1001d035203d40c0c01d07a403c0b086ea40002d100100250a00d00740da0900c0006a101811140700e071300c6000d00380880614491200d2104900300d02d40d5603801a0213481c205074070000e40702405005000011340c04821541c0220903c1c0c11100a80d44412550a03900c0d610741080002c600e0110400041c10f0b8100b000d244e0408040da410311030a0320341001d1010f00c0880d4010310041090120740e20040410b00c0406981e460f00c000c005111001403080043e000c87c080c111706580c15400d00d0b60120b5a42014000c403869594440d50301442540d50380103c94a00141c140c0c2210b450084441e06031000c1e40c0e031000380c4107a1401e0242 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 827973947 1250 827972697 827972767
    0x50c130f030c121709120d0f0207050306012405040e0a0501090b120c010c031205040f1403040b040308091215010521030d0903091203021e030702031209030102 70
    0x4040c842c0060380403a8000e41091040310000b03004801c001407200c0070441c2c40751612a0500050701c8904600c002480070b01c500c0700d8110b2107a90112800c07049000700d03000d5410340740c0c5a2042c50380b40c2c8070900030011882444107c400104905080307800d40d01000e0310340240fc0c2511800031001151040d9440948030b0303100e9005000c5c1c00c9071403162013403001d811a010f02c03858010441e01c5071140d10398040c990500c907075032051005240c02101030144240c00554100894507281c079103080b040340c090394180d4001e80a07012003200c15000000300d80c00d54030451719884c2407919540d154031031940b100000580110951991b1020300d6801c01251075541c00c410184212581031100f8815030740405030811032420009400118402404000c491311928141c2e000b05402e0340303e04041d1820b01503070707200c0c0c12102c919815800501d58007080c40007211030408240070391010720444840e960b00032a00c01039816007008003d005024000c60080c07085000140000d410400d11001100301d074a10302000c0030300365000c05c074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 827975197 1250 827973947 827973953
    0x31205070506070e1002030a0807030c14040b0c010c0c1109190e0604060c090302010801051302130803030709060906080a1e09030e0306010605071e05030f0a030207060606050319050c130f03 83
    0x2c280300085d03025100a60030714503210030003070401201501c0c000c145550b5141c42c80e80140708404075005840074078141c03599a03580d15040241640500c4134a0707113075480d040c9444040f034890060314202581200840c4100c02851040141d041c0c8007402282525800c0308100541780480c1c061340410030740701c2000e840e1918150404d4810348140300d07517400c10000c000707000b840140e82014110b8151042a140050140b0017801d41c0c00003840b076202400d10141508000088400c0c002004510507051382d0748018040d0f40e0f90000340d440725042e000e0030740420500300000703076206210707408081d00c20308400a071015028881c49901c02c5032400e000c207400044004030000749904017080145d004101520b000e40c6010b41945507000f501d1b00c40d1425854154400e40503000307121080050380d1484071110305045c2e841c2c44190000e4000c5d445804100e030850304207500050301f07500580503240302e0425103800c91254851034036040c000b010002c0c024447c02d802400340692142c2860f014101905540b2001b1450a003142 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 827976447 1250 827975197 827975209
    0x150822030c02130c051804140c1c0603031d031614031c08040305070312020a030e0606090f15010c330b060f07150f0f0605031501031205070506070e 65
    0x40485062130034030b1303a03c040e5284e104003103c07030100c9800280181500e8150000f80901210030800d024a0461018040000b5541c0002c090340c044a0060a00d0700d40d034402c140307041d2000c80c4000b034041a0711070381c0030701d00c0807810728000456607004041c0c0d401c40b0042030304000520303c2d0b904150420340c20403448507003d00702000050260350710502c0010100030383e4000104400c01c0180010708000e4003040000415000f501d400d42c0c2410707840e03000d641380c01040000400401100b440420144608170100e0103c1c00c280038003502640c641548070415603951070b029800b14a110240604004d900143c40c804a1403042d0150803001890305d02702d81c0300c11206403c446e800091400240640c9c035007002c1d40c040750b40e14011030b0302e00c8000b9190980c407001c072814010109221980d100410314104001c514040d48d580d44090020400d00800b0456641c03500141641c1d24085403038880c03003049290050000c00d0f8011445a828030892405500e40840b6642e141c0c02d200090300c4030030109104181801b410714040c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 827977697 1250 827976447 827976469
    0x5181219020120071b1203030c230903031303060506042904050c0c01090302010c08070c020a120224130509040201050307030e010e0d05030a06060504150822030c02 72
    0x644000c0c40f104001c80b6818040d0b009072000086a40b0000401d442041045035812500c407607a1503c04d00c80a0703450101c0070001c03601400807000285400c0b0000740c4180243c004d6141410380b40c849000f0903400030103104042d80000182641840180049200700e203c0c0d40030900503510403c804a00c60521800707000c10389400e80985101440c8010200120040828808442e501d040328045010f0721500305030f82c001c0c42039a0440c0825400d100d4007805140c0c05410416071009907968203241d950315142c0c211000542c0c8a4001c1d8001c4c60705900b00f00310709c0c00841c00d103256400140440c61808004506441c481082181148000e201284540d4413110000110005020544131000c2c2403501d580001c00a1000905031014155182c107544900c410960280d0683c9244c1c0048a0080c410b08001400c0743e0011200c5400040c00e1841c0442e07401e100b00d095504070b03144483c1d6907916a038804030544d807201d002068400a51040118501e40c0031190040b615403d01903124a455208240140f040d08401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 827978947 1250 827977697 827977747
    0x180b0f0a4a100215040807020907180605030114010c080d0203041a070e0f04020c0a0c08030d060f062a0804091d0c0604051203040803030412081e0a051812 68
    0x2c1442c4010b02e06402146070510100b030340c6945001951180750202541c020080301a4010003118100400d00742c1220120502d100100c49001065684810484203407209029006011501d100290340d20350241c2525484d640c41519110b0809000b84400d00890700221400d445202c14525541e003250502e13407240b60801803a16107201c0c401000404140310405112246003d2940003d484210399824416060300035031215002d071031b00d582c0300e0500da5203808c0410381c0c0c080580741040001c2c81582195010341100d0701621040304002480c804000c0641081c044060b10060582e0540c00103061400180068001d442c000103810710354010310440c01001560050065004412440c0c0640d5218140c60449a040703030307401c81501c051580386055000300c1d440300845220200a000400a000c01000320b80c0318280d560fa412683d81c00e444520b44031480200000b4280000007042c001d20042d00150b511101c40c21041d442d01c1d0000c1002c078540fa04110502520140104803144070200c824144205050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 827980197 1250 827978947 827978959
    0x50613092d020708091c1403031e06151c2301050303070b04060b0a0905040503030117060408030103060c09050d0542060d02030607180b0f0a4a 63
    0xc5558400e998454012190300c25444d989100d803409011006546e802e56202400350950880c92005c155a608250390064080d000800e08100c0c101aa004481c46120020300078650740006022544141e4030030321480da10002003049084a0cc2060301603614007410340c034100f0b803440804480c0b80101da001038201902c20f0b00100003640100781c81b80b0b0f00e10741080d00048001415805440060a801690780c8544030840c102010401800008000b030b6040750001c5441c0b4181d140f000e40d0194803020119002840c481050005101151290f80803e250344400c1c24280c20554603900001e4a0800c0c00a00700c1e40f0343e1101096040b100700b041000c460100c1164142404202404c2c000c01c203203511680c2d600c022010f40f00008000781d440d04030b84e920321600a815038000382031080c0300510810070006088541c0d00305240015001c0315407030481d6600041c0d244201e003080b960001c129a00300c010400b240e0324001e05080c02c501c031466141882080008402c110303104066111074100b084200000d120300c900 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 827981447 1250 827980197 827980207
    0x5070503010c0503010e190e0109030918050115111203011701270605060402040b132409030f0201021c050408120c0a0305070303140a0906050f01050a050613092d02 72
    0xc00540c03e6a0007100047d020081d042c10b140c52031004107035030203032003446c3c0d820900c0520600d82c000844005440d0800079440100044060103c2036070300a01c1080c203c000610341c5003003103e100321401141e00c103119058031840c40a066241d4843e8000781c01460170315031040b60003003480d003092040c00855090000400301864035001d10b05500c08100d07034098000e580300e100081d020354503a03046070054458248000e0300c41c202841c20f10b0510219000b8552141501c0000d8031200884407000800412070740c3d141404141150f8802c4485080308000b2415449141442c103952800c10500c9a03c110041e50791584440c03800800d1031408014060407140312804000500c4e03940300108045c144142c2500305242d4400c4d1070300d41180203000b100c02e4542619070030000e0044035019a00415200c501404042c003041c0c0700c0881e0102c82c40703002c0c03080381c0d031080c9000410046802c020000d4141c0700711484282403403550f5440f030f8105454817500046921402d0021101d9005c0b100b030060303c0c80300c1858500f14100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 827982697 1250 827981447 827981459
    0x606110d0c02102a120801081612060e010908090f0619270f140103050603060412020111160b0f1b0f1902100e0c030c090402040605090405070503010c050301 69
    0x60707030102c00c07420042c80403040000b04e44000e0786442c030101c08090800ba80d4410382000c81801015050540c0003a00d01c030000941040e001034080782c00c040c8a44000c0c50503140441e00701c01d40c15201c0301198010b44441c49000ca05400380301308115580114003440d40c98020008207d103060203040058401c8006010040c410f00300840d40d006407581c64141082c54600e80042e82243d4440301c2c455401081d4008004101c0280305042e800845e8002403e09a48540d03600065054600499031b41e90141e001030001800302d109241d00303400c0001c107800001540b80c1800803002c01ca520042e41c2c144200000c6000004001c030041800c0d900c051005030900c1c050034604091940c4400e0b07103401021100340445c5080c0001d1400d4203c030002000d0301115180c070750107900080d40781c006940d4008810303850480a0742135600b0200c2d50003495107000b0090400c6c445020108071a4a40103007050343c01c15500c07400030406849034800540510700031030003004841d203850205425a06421215000c01806100400074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 827983947 1250 827982697 827982709
    0x12100f0e0f090c0307030602130f12110a091d0f0316030c081c050f0c0a0c0305030a0204171507090e0c0c120409090c05040e0c01050c07090606110d0c02 67
    0x4503401c003032000c9140c1c40d100d00c4a494100714107082d550500030040d0001c2040b040394014085403000f00d1004110b036503a6440d001800c116403241c0e5104c4440c0300144000907500381c0207151280700003000706528a0300c91903400225149100c10b60004551900340d1000032108000582c000c4041e18029450046005050036407c402254010709000790064140300300725503003040d2000004066410034000c4c141030388043c06031000799110240e00a084000c211540902001c0751f000c1c490742d0300e620b0803191a0b031b9000c0744c00382c4c401043c1e104400d6003400086598084c600403010100040d80c010300f03070030500100c0d91001c590060284001e0103a81c071000c21402445540c1103600084da0201142c55000c60100241000d076220b1130b0181c58000000c2c0860b020806510103010580502c00503804541c64a007404100c50015101c11817030b50141c0a441403642c802c10080500e030071054180c5240a90f0340d11500180c4a42d0341058020400d11b0310141c810007001c1008503168800791820b040c188200c5e13004108 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 827985197 1250 827983947 827983951
    0x50604090c180b1f1b080a2d090806010608100308180a03030810081203220510050601030f0c0f030507180b0a0324051c060212100f0e 59
    0x40709030200e02c000540e0006070f9018028946000d412054007050420341c1c010030410b44141c1d00045041074042000006010300c02d54021036110001d103281112400c800e075501d40180000100c0140070003000341e03e03040100d10035148400036448034030700715080c4445076042c01c005800510402c4000b10400440d0315000c03110170212500000d0113a81e9841c0c51415461b400204542c1f99000035162400000301948200707400e00c07a031944000d4031072440c2c40d41103098458814a0368611219414400704151000c0f01c07904a00190b030001c030556201c25581d446500344140041e2a40a259660080000c0d030350b0180a40c41584c900c5d0002008100035444010705202c01050000081594800000b004507000c0d181d40116125503081082006a07109075464a60381720443e071000090900c039200300c0950050302d03003d404c1044801c00d840107501b080d05021048070320203010a00c6103841c0d5500400301e1068030042000e80f84401a1055528106c55130700074400560340101101c21056500300160202702c1c44041d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 827986447 1250 827985197 827985209
    0x20a0b060d020405150907030905060f0601020c10051c0603080304060903180305030702270705031e01120201090f060e010e150c1e01110a0c0302070803040f09050604090c 75
    0x518644801000c1510100700301d038002d402620340310074404800740f880f04141550104503100c440030303a1078400031020768040b004020700039400400881c40100385503000d0395000790b040c0304a0b1185141d000024800c1109804600007040f000144082034003040000450700004601d42440000d18680c1e4481851000400c041c003220f6030351030103200305481505c401150701208070109011a80740e003000f80d260742c403c403000ca10600785402445841d14101000050075602c807c52010150ba81d00c9050303545510080c0f0052407401610080400c400c040041d0034043d00c64004041102d0301e0300e00c005412081c554002040d4908107803c2044065405110888001d03028a40300200c041c001e400702e51500e51015454064034808281030100c4000066192840241560007150b00104803188908136070300300503e035402003800c00c0040f230703550f0045844051031807007881103c1200d07541340c1c0b099041d50029040109a4405c07240f003044584c0703031802003a0304605d08036001c01c1a83e1940d40c42019241e40c0744580 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 827987697 1250 827986447 827986463
    0x10801120803060d02060c01060810050c0712030b0d03033305190f09050415020301030201050706091505090c0307060306050618060d410403030e01180c0e1303020a 72
    0xf40ca42c1d02c030400884696540580030759140d00c0804c48150190940d40618202841a0010110500d4441c0541c030b0013030610101e0f440c6081019140c1d10010a80408a2024582c071420070b0031040e00c48040b8280318900070347d00020700702d0a0200444524012060b050500c1110703007010803403240660352420489001701c50303100000ca01040c4541154902c0d0740142e4108030013940c0000c100c4400d40020f841644981407000c0c0c2c182c141004c18080b40400c0c00702030300061050003124001038450b80007548060103a41014640c1e50b15661031415200c00325400911604641502080350030108035820242c402e0f801d0901250782080041002406840d045a01046800c008010240c45203411103400440351b49081c042002201502c0380008440d0110000c50320f600305d4090520404910342d0326403c2070070320aa03001c0d40c0b121344044010301206442c00801d5569010201c01ca686500c0c0700340d551900c02c594240c09246403a102001288000340004030004520052000080e80030038003000d500e41c0b04800c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 827988947 1250 827987697 827987701
    0x705040b04020c2e02120108010506060a080a0515090411030c01030e06060d020d170a021018030c0c0b1c0b09061302030405030906040303031e06060c02060c0c031c0e010801120803 79
    0x13445514071004044035403991000a01480c0c600e805481213043c3c0356510000d02c86c986072a010b101c403a2044048447c00280840b02260880c1d09903004141c00c0300341c25101e8403c41030414002181040141c41c2103444c03900d07542c400c2c80725040c20f010100c55a402428200501807891085030340742e5600500c624400e4402c1c3c0d86182c00c40d030f10814a517080c580c12103c00110000040e4000c0d00607804280395201520801c64881b043c20080c0c01b402c920603400441d5840c0d205c040303540c181c4817544c0e03915040314142c1a0402c04204001d098001d015800000e0000049001c03141400703204481040f64258042c5000904100840d100c0c205501d0000720308010059481d03441d07050080c214041d41c10407640c85000060000b042c0b540c103410690b00d1400103000c0e0818520098a418111591441040041481081180d0241c90000c010b8141c00720000142c800e004a40380001c0e0034240d4546c6442402e41d614a0b60307600f0540d000d00c4240c07254000b82412540781d414003860304441150600300404a000000c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 827990197 1250 827988947 827989003
    0x40f0e150a0e0a020d080c07120b01090207111207030b1501031d07260d0c1208012913170d030e1e0f070b1801210c0203070f050705040b04020c 63
    0x100c7d04d0512012058840c000c2c1c40c3c11400491a50076241520038000407000030079408100e2080b60046980301c102c503d15070300d06200307000c0043c0c03682007080020300a1000000102e41e50314102d61090031a02c411550400c50303e0009021240d1607100d590700300c103100601c0c80702000002558800d5800c280006000c1503403082d101040300001100b01401c502818441c8400240c1020313502094910844032412041c441c0790045440c008244202c0c000c0c2d02900603135041645e0451301140d821615580e81a140140c2c90568008000c56507102d1a5061a8a174480c003804a052040316081d00151400303001c83c605043e000d030b9032014403084611441206e59120007044004001484600385a4002d4500d225075602c209403090700400f5280c07021100404e0102c0c4e642d8460710102c1e072405000110301014455150307009c001011081c0368842544010003208021488a00545207013500c1800103048007420541030009407600860dc56010b039006011003183d070b04021031241580040c1c0c44540c0d018034a000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 827991447 1250 827990197 827990213
    0x80f09190305030306040b030c030705090a0e010e0d0923010818100509011808042c04260304020609090a1e02040f06051303060b040f0e150a0e0a020d 66
    0x3416110031019954000010084044040d502c14101101d0420082108609240d240d41c40042483e030300d0340003440c00f84114a07101c5041a007101c2200f00002e407014040311210300f103400001c046400c41e401081c0c0b04c00c120764000030f03890280c2540c1d076a0804008030419114003284642d600a030500046100190118494000c260350703003000314040341c04400c90010700c00010241a194080c80703500308105419030380c144034810a00c6542c005c8205107028030b80003800c031242640c042107854040d10551082e4002006044c1c00780207034010301203131010311908102200390802402c0003d0050000344104000740ea20b0f201620442c4105465400840d9111000803000301030703d40341e08008010102c51050700389051340c00b92058942035141c10b1182922001c0c00e032402d004035a141c0c07807142014a01400080c0054101c035403214006440880d42c03205d80c950301e0040e1440030070002500d034800500810300e40d5100700304a8010703212000030004000300d00055916000d411130064001c100101801007080285 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 827992697 1250 827991447 827991469
    0x6050a03020a1b1101032d0207020409050f0601091407050a0f091e08070f0302030613050a020a060527010909020708040302091f0b19080723030907080307080f09 71
    0x4040c00d041c440900e18142001142c804c25650002c0e01d00185111100c061000c0301114428000500401c0c8456500e103002a40c400b0400706c2c1c0082d04c036010600003d0040101c54580b450070405001290306241c655000c4800c138600d079405003481d1009111425402400301c41c0d403001286044407941c402c050050f40d03c8001c0380e10404c00070001e41e40d09500310341001e00720007d541c0c0c000e0648050b55912820006c03005202d0101030b6142e04428007003580a001d00344003804e19445802500c0c9000981d030002448080603606c020302180c0001024041ca46641a0705c0c41ca40360720703020100201c02400002480130f21540282050340d80d0000c0c02500b03020155081c1c40c01142d0040203801280b800e880031000c03e091030021580aa90001404105002d00500f60781500708070448991308492082c00c1120302000140c007400500000c1280d50341c0407568000c1409062684403403440d942d0928101891030605240c0c00380e0baa03034006000e8900014800720449512914103102681c5070b0312507e0002d0903264503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 827993947 1250 827992697 827992727
    0x50f120120040609050919020c120a03053106050c1e04080601151d010c05030c06091b1f090b040303030605180408121b1210080706050a03020a 63
    0x100708a165030390151001403003615001d0340d80e03080d070983d504240411240c0a980907600c0000c03000c03901c0403c540e1a0b01410b00300c5140c80032500303080303841e07185055164072280c00c060009803110b081000c0100e10090425540e81a503146820f00148280740e503030f0700d1000140003014030b9283d401040c4c088101e0800d03616019400307200c41034450382c4000a42d07216845486085480c0c02888000102290034605045242c0602c0d16250a0240c410400d181510010b01c1c841d414003802c0710142c8045002080a091281d04a800030002d0381040c00040780303010800240c80d0051243c0481c201c181e40c8940030940040102c00780d00101005c1841419205176049400442c19a003010400200389503164104c44205c0da070903500810301640d130b1262082403010449025288640c100b00ca001070f4012450525485003d100c1c080071800d81003c0081150790146d610016400b044005214200c18481319000092103003d006120b907a1500c2c0700a40140039520054081c5640482c0d100c54041c007548042c03526102c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 827995197 1250 827993947 827993981
    0x90402040b100507150203130f02040f061202040516020c0d060e0d0f110303040f030f090504020c010c111501050118032f10050412020f0603010e180106050f1201 71
    0x514a00042454004013010750700340d4891810084101c1081c801c51740504070a280c1d104481107161595030365031000b004c3c1240c009544e580744000ca04440d00c00d54014141140f02c28501d460031340100415030b20040c255103010200b141c6801a4242c0000b00c007004064140c40b010241d498a08144d001041130302d0007244a402000644a84254000386841c44007226440c0c22001030280c906035a902d0000310303001848a81406840c0300401c0c000c0c0d507490440401460309082007038941004c02c0c240e80103014100a00c0c0c1d11140e000d011a0f4000400e03075481c5504000521000000401c81c0280c000184502d40c10301c510144079034012980500b60001031034212541510202c0c007900c051030204070f135140c0040030000a0f403580c80d17240b40c0303144070011600b01da5a95a00701402c0004085907499002d83c120382c011000344c0a10200d444d1403000e580204042d0503140030074075080071504600c00c0c0b460700ca0310007a454550140041c0d5075012021208500a0301c1ca40250300b406490f01f401803141800740c071a501 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 827996447 1250 827995197 827995219
    0x503030f040201020601090b01140705031b07140603130f0f05120406030506030f0604060c0504090f0c030605121023152107090b0f0d1a0117030306090402040b 70
    0x2a22800e5140a03074400e908513407060380c0c1d40740d051040f50a848061400030f45c52429060398050920094401c1d18096002c0d689050190006155000390501070148260000f4808101c207009910900c10203100640700149903142c013000740140c2d05400340000b40018a074043e80c10038003007145d5400413015444001c441c0302c88039104044080d1f80082c8a842c00082c10040020b03007038200480c407041c4c0c0c5400c1400400c140e468554501c005003429000c03034420400240b20000d0a5a118000c0261106440d400000c0741e40e41210300a040c0c6015401490090001000c01d0242e6000000c0d000d40d8422110350000ba02c3c001c00c90f400546a4102004071840c8803058280600600095080320700040c003194030021403c00ca400c403ca03141040700400c0113541007018208003161035074016003d42c01c002804048414840c900240d0041c540b01000e51f030300f4141021000410074809106409040d01031705800b80d0070125100a5500e02c03004103081e00814200011a0454441c3e401403000068000d003401921 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 827997697 1250 827996447 827996461
    0x408120d09120314060a06050a080615040603060e070f0912151118010e13051f0609090e070b160218130b150319030512070503041b05060a0c0f050303 66
    0x9403500c0c1d071100c8511300310000864070310710344030010340b080790541d1312224107103444608169142d81005002540200c0c9040c0c55400d0200c03450b0003800034212076180000d00906203020465084401044007003403103281c00c070280d1480d40000c91102100e0f1480070803181c010071480c1600705890703403681d10300580c1d0802242c403903141c610314050000d840c001c00c000011101401700441c0c8403210b0101c030741e4200600300c40f10340442d540c640003a544100a07082401c80118124240a241c030601e50201001402c034403410300c2650800d0148044602090703000f0801300c0d09040c09880e03244610074801d28506a1183c01d81c0031516030110500105500d1a81c01001d880c00304407040c640f608408040310440e450300c00146002080c1402090040d03005801803d4000c1c034510b8050301300050200903401e00005011180104120780210b030300c100b14503680d0b2a01e80c1450302d040080c2c00741d02c107044e1401218000f0f00b031200352103001c10b9030401070b11840c00c0d401082d002d007040d07190184078010251203404000100314003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 827998947 1250 827997697 827997701
    0x20102160c15020a022b0510050405070605030103031e122a0c12140705010608070e06061813112703070b03010504050c09030a0f06110408120d091203 66
    0x1c0702e03001e0071900c16403003203060200e8440c80ea81c90b0080d40f09020014402c03074070034075120b006a940c14800400300d06003c60745600d46444140fa820909940e1524104010040c0503c454001005582090340c00c2d07505556000c0c042980542065540540307207540582d49030700c6000111001d40234000d003003061040100611034550440c44910791808040d249061a90b4840e280c400031058000e541ea03005210710076400c448560050010b03404401040c070000010034000c4c860b00b401050984000c0418519001ca02051500020000c1d48184021702c0190151494550911481c0d41c003250041c0000c10300030a20001001812036902c10801c010521142c8084842c1e09a80c2030f8917922404034030040448101a601e01180c0a900382d081000d00042040381000d0300440c0d0131624946046050a10031000b081c506911a0b5050700d40140c0d64241314280b180c948101c201112aa001c0c0317510745410103600e40c1d6100c8030001c410340c3c003c00020381c0450450280d8002c081a560144a81c002c0d10703103402000740 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 828000197 1250 827998947 827998949
    0x2104030207030c05010c150e01150e0603010606031407081008070e01170705030703170405040c080411030105011211060d15031203051303030b1203030901020703110625020102160c 79
    0x25040b40d100f0f9000c14658041c4105039200c5d540409140c00d00d4628448a074050b100d40b450081840d9203c21141151040d0350307038540080c1c44000c82d007000380c1c5440340030142135480c0d039071000092501e006400c02c06501d4119406521400d58105640241c5880c00c601c100505641c4c4824014003510a02180c40c006030305a06040350480520b0b00442c81d4103910390303900d540040c0700e880d61540c01050200001000b0b0039061003034058282d49141800e030740c0c002003000d4030540307851100042e404d032080008200011019030000c620030f8000300716540c14462540e440113200c0c4405403060070101005e00e01035132628210303821a440541e00f03201031846640078520070b0406000440c1c2404000e201c940d0114420305c202880b40340040c174900000c031100e480941c01000d4509640b0f801100a141321401404204025400b4a001000059440d00241002488256080070704a00e07500560f05000312541c5ea94510035103c40c1c02d01c0f0b108502e1603140c0040e80203101c0d0f00c0e201c47d88616404800070a105103014044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 828001447 1250 828000197 828000203
    0x141009150c140f070614040302060d05040b101401031d010609050711010c08010501050c0f0d080121020d1101121109040c030203061005090310180203010b15030c210403020703 77
    0x14042d28074868079440700341203200b0880310750050108010a0340f01e00d281c0d110090380b429441b8541501c94010517555032107075604104103501d90080c00704100401164503400502d2100840c01c1c1410500100c0040d0b19900d1040d0400d61240408c0820004180e02ca403040040c843c000c2102590740e04030f580141008842c8080403c000c081c0540b0350090600460504848560314208031f0b0782801c00666040d0446140c2e1100e5200e107029403007059104003e20305a000f50b41d118404150300d48040010003d092060b50740051070340d8901b410050301c61480b480c0507142e101d50305000c440710440040700e03d0701d0005100203d45042c40380d881c1c4c090b00e039140107000488080c4e6081c00800b450442c180d05070700c02a5107161f0884542c1044141d02442000901100080142600c03e804c10303540e0000166031100c0c41c980c0c500070701d070219001146400d2161f40002541aa0250140c42ca00b42d0f0120325030100800c0600364000c002102c15010310740d000d880e58400c4032000c0d00d200078245400c2c001e41c0c07400140006c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 828002697 1250 828001447 828001463
    0xc1615090b030c0717040806040303050f06100c0809060702090a09020117090c010e0316060818160e0c07080d0f0b040b060702060d0b0a120516141009150c 68
    0x114070a9407070703811248520303803881c940d07071901d061030b40d548109100e0308151040004007403002190754081444460301980c000e550224030b40c10180c6800d00d4050340034110501c07541124050310007c58214450300155030700b0a500d00d845108602c0420003d126000d4020350000c0b204040240307140c526800304140034002c0e44d81c1c2805544c603a0302013a10150a8555a280e075103c0f545400081d84100003042c0341e284044d0955821070031426001ca29206260000004180050104034000d004e24150340402c080d070000034891010340079207074030880c0000d00030b05082140100c00160301184140855502aa1000b80c4583d1203a040c00c0d080000d00c011801d581d0668203100281003d803825000e02c0d20580c2008008600c0c000705075080011652000c0e8642181ca51034003940740340ca075604568a0000d10003400903015a240502e08035003000d0140001c2c0d01001c01044043c0400700c40361150310032201083e944a900003206040035900c91a0710f50110000c07448690321200b4040e4080019840980700301c0c07031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 828003947 1250 828002697 828002699
    0x100c080f100f090b01030f0617152a07050a200f01120902010e030a0828020a08070204020d050711070b0c06040b04022107030b0a200c161509 62
    0x108451669680c840c0c1c41c800c000ea40070038400c0ca61198400613840c0d01c14100090031000d80030080003034509581c0030f84d54a1031000504c543c501001d00240d400c0d08000092500580b81203441c003407450a07004031004002d010b811601800f0808603080b101d80c07507001400c68100981c02c0c6050145c145a8420b5020005c0700301f0025000c0382031880703480885003016154403100c1c800e400c1c0703160300600019a05038104281c0c40fa00380442d4409000b030300300c150f01400d60188d075408501441d180c0d03c21040081c81020801c001110f1031984d0100d030003200c0d0b541c001c40c02e41d5110349030b0001030b000e0301401e1001ca0b900c038a00424403098541150f554070881001c0c106880e1070350f685178074489160068030890a401e421100c00a070000348028117480c1d1040c4004e1400c00044010b543c0c10300604001181c100150340310802c04d0080c03220b04109244e0001d440302050000300181c0c2907641c20a122006090001c2d08040b8680010001c140140d0005922441d1003504060b550591840c5002d0311800400c0400d520543c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 828005197 1250 828003947 828003961
    0x503041e091d070e0c040513050105191508131a0a0c18030213060f0806040c051c0605090c03030a09030605010b03010501080c07050129030111040609030b0603100c080f 74
    0x5080e61580c012030700a45070951600d5151034050748002c4c0004003110f1700f000003203501c1d550f07498103100c0380051860029182d030404083c031120289030002003194440302e00c0c00b040300c003a010070380601c03c040c1c1d4070b4031840720740311840d030200c09004030b6400a029408160011259159000340039109860b04031042c0b101074000e042c10317200180007182c2140c40d096005800d00260505146440d012070440000003102aa9090044021807040d002950180c100405000c24041c039802000d0103024200c3e045e61201c4444840454002e10455008201c40d440d400003444e6504103108444c51a600901941c0daa00c28000c0d0060207022180012186140390000100708409010b040d20b0690b034040c1c56001441e140e0040800c04c5400a403000c45d025074981d078252202c07200d20341e080b100b0100d0b5501d04014010b6907000301030075501c03003050318502102c090004000b91a800034500d003c890b04554520041c1d111400880d040180405000c0803042c20007241c03440b1154030222152103400e0303400351440d064542c01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 828006447 1250 828005197 828005231
    0x10f21210e0f1906050f0705010216060501090b0a1701090c061709010b030a080c120a030e06090105042a0503070e04030219020f09280b01030e0102070b0708040503041e09 75
    0x101000c0d83d00d040010b03081c030840740203000800d241c4541010b41402c151040c0e6455080e0390025104c10740203490440c8200411500c0d00426000d881012000d00c408968800403c518400a1050a80744e070b000c0540715052604c01e52140d040a60042d0425108540312140900260300580d034801001c111100002d45040046c824801d1100c00200500038460054031600b407282c102e221070210a0040b0019910f41c41a9200200b100c49040d0300c000c500b0708a065031090424400030900c4400d81d040c4410000040c40c40030010505940e0400741c49403006e54104c110180f944282c11068162040800c0843c0140c2038400e02d500c039034801c0e4201c0e00d03410390407124804510300601d0001d40101500054140910300000002e41c000c04958106002407001510b01d68004c010b0076850071040e9a80c0d002c00d04650780350117140546140400203510f004443e0360b0702d02c411080182490100440000450100310091040744c00801710503202882a0100c00100943e40c0e0705440f60059042c50075003200040c414003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 828007697 1250 828006447 828006469
    0xd020109120807020f06010806060109050301090f060218092401140a120b0d030c05070f0605030c030c0c03130608071e0e0301060512010203040605010f21210e0f 71
    0x4400003100340d404007041a215448003800c03c03c00c0d8003402020f05141e040c104801402054182c0080006d81040c00002d80f100c4880c1d0006d80c0240d040041c580e0100300804054440d039607102c140140d9a41c00742100c040b00144210343c10750302c0720900c414025400394001b400c1c462120322811100078502c40000545081e1200382c10040c0990040c01902d900d01c1c000c6082800c00d50601d00b0119200005d040000c4845240032802c40128a4070300d07010302071000422901e4041c2900310b40880181c2d0400c0c03409420b50000415913841d2640c00030000c0c03200c003803100540310040c80003011a501c4d510b503040d640c0c001000c18041c0500244221001440d914072031500c0121541350b04121440c419114007080303824070101d0490315055034aa4500041b1502c2d06858602d030800a40001038482c05c00b8600710044e1751060f800b18030f079210b000c9000e0000c0c01140a50152903060b200c05000880103600e0264a500420364440343c100b406280240c0145400c10710131030100e0707805c540054103d050481046248809 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 828008947 1250 828007697 828007703
    0x7050a0209130b04120e100809010c0518040b0f0d0b09010c050405060702010c21090806061e01080912030c030105031005190b030f0a060204080d03060e060d0f0203060f090d020109 79
    0x4400c004c00c02055400c19081c43c00b182c1d914002030003000010114540d0004d004440d000a8202400c2002050082c4148079040031580380403407070010307110011203c1c07001c0200020711955646a074903019944010520a0030b04003e00420180400c40c01c01c0255101e04440406095082c1200400d0040c424000c4505641005080c82c0c01c1034401e40044640e03082070300e01240d54070038424a14004032404c1500240213010707a07890303820f12030820306100c2c14487d014041d240103008444c1104490341c5034a15003c8168420729100d8450364401c10981e01c1d000b55441d191814050000c28481c1500d9944019030603240141e0807103104030058003540c0d0886100311080e2001e03d401c0417048428000581192a62060042c115209044075034101400d000000d04120b030300e182d00140400103d901840340102c41d02040c00c1c01c110301d502c3e0485800000400500349407086805000784d41c1000098030045840d560042e0443d40c0301d2a094a482c070304102e040d18850304500c00c0b02d0a004031140b0500032402103d81c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 828010197 1250 828008947 828008963
    0x2030601090e0a050105040b07030b01020c0906280f0306060e0f0a0c0309050f06060406080d0210050712020a09030201140c1504020411030a09020a0b281407050a020913 74
    0x200c0c0071071050041c07503191a040d045004841c10301c00861303002d0182c0b5008600410700c1a1750350509150107400c850f10002220306541041d10612541d540f01e8804960000080d101d201e207055800c208aa0600002d90720582c0420f0040b0012442010180c101425648541d03410000070341c94120403902e1403c202c60590490010100007150140c3ca5040b00e00e82003900d06021400a01c2076807110700703080c28250250190352025041204d6407400740900d00080020b90040c0040c001017030070003529528807400400c09951074001041c0c00324450b00000d0460b40d10b01c0811074842c00405401081c1854610081c2e002031808003040e040d40380d000b0115440d1069040080c8070030031090714020740410000784180c0c2d1050b52524541a41d40350034008501c10074041500254001480c0304002d0700400d0703608110700c61070003400960b500664014620b07007512050501c100002c181d0705000c4904e95907c50144090410218440702000800692004074a01c220313202006541c40d01030003c000c1040e0741001c4c25100f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 828011447 1250 828010197 828010199
    0x80303040212030408010906020c0d050306033706050a0e03040501120b0d02060f071e0209010618030221061b0a0c0303090c2607050f06090613090603050d050702030601 74
    0x85040342c080c40007020340905503810310755210042801c40c0d46c0014261903c0c1c1c0c0021b0244a407200c203010360243d00705141003007400c41c10310301c000ca40d42d03c01e080d0f00d4001300d9945548503141c611003080700c0c001d0081d502d15044228081441e01c0b4004e4182503414015080c10303e8607441481c00044269010748034103039074406030058610101006803c03042c40c01a04251040c4000000d6100e1100820301c151499200c95903500c00c600d0401100c00ca680a481c0c0008008204e40b8010303521a550681152031030b10308042402d0019140130100c07502580025404412460011005241e035000043d190301030b1007c0e140e187d6220083c0504c0041007404a10201c002005104050360040c00403c410f98041e20b0002001441940c500c007208407103422050103030000403803980c1c40e96910140d103000403d00e58041e10003030780340c035000c240395030701404919100300c0c0c0c0807500032501c0e1508420f48603140c400b030442403040d41d960507000c8010b0800d400180c0b91802042c0c815201a400741c0100c6000c0d90780500144480c0e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 828012697 1250 828011447 828011449
    0xa05010e041a062209020412080d0b0d0302010c02010b06040f0b03180a11090a180605060303070807060606090f08071e0308031f0812040b0a02070302030a080909100803030402 77
    0xc0c6140c001c0d014444540141d010042d0716404050000340503419038200291108034180c05440c3c13410781c098901700c2c0c01044244000a0901e5444d514954015002038030351140802a00207007526181c1d080c1c01030756001d80581417503415005240c00c070070b03260002c100010702a014048544154016090b024420031820426481ca00004680c011400100c860680c00074440942c200b5030300d050300340c92090f2003d441e150740b40b40081015812590001040002c45840042c42030f42c0205a02e000e00b0311a900d100003282924107004541105500644460382e51085243c40801040f035400342c0030010700c0014000c20301a030350307006210030303a41904010290145800146071240800c4090080060102e4100000240080e0090348c091400c80012804121810010b410440755907400111694892400d844a002603001250309070303440892415620118040142d1800207687e00007909803140b1156081480f03158405003d1401e001c464148468940603c9042440c04600172184a5001000402c0c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 828013947 1250 828012697 828012701
    0xc0f09110f07050a080d090b100302030c090901020405151209060606120702070b04180b151c020c0307140105090616110109062906031302060d0213030f0b060a05010e04 74
    0x181e035204008039034866244d581d805c1e285800000a01e904561200610000c115240103070303550114006103000441461900081d955070030b0f4581403400b81810901003030f01805d00390103ca0240c54081d0160441d100080103c08040d4010200c1101aa403c00d022501104004c41e509009210091115060441240c080c0c0061708003e04034405500c9540c0c0700207080079008018100400741161070f0600440b5003041603003034411300345c1014803441c0c10050345012614034a094410108410380c01400003044604800c0080c8902c0040400c1440081804820004012080050001c501c4000d000d6900d07600306841d0340d2a420340301d030040f440303406102c004081d11607407000c0e40703c1c0c51031030020450342d00d9600c4030380c1110070302c1c80d400f418100c0300e030101d09401d052140b0104244005982c446c1c0386140c03080d15074242e0345140c28020300c240300004551030252840e8040d46c25a428003d00355503032940e285010241280381d22012a025800c03580004d00d1407030070740c404000302c0e401a1a6020251102ca0030000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 828015197 1250 828013947 828013957
    0x8010507090f05030d05191b03050c2401210501020f1c1103071b120f09050102030711040203041401060906050a050d02130e03070f0c030b0f2a12040c0f09110f 70
    0x100300e00c4103030003c2300b20007400c020500c040c040e0300c0c6c05540f825808851400c1c00c0c191b560b42c0013890450b00c41040c0f03007882c100005045400d64485500200c0010601e58800a40c800029040f0342c0040b440e8019281000020040f0080380c0c002c03d4410b98000c1010780540d2800700302c1c2c1e410320030705000094081d4090424508100c550b111082d60f015001d90394840c0103c070382080798002400c0d4556010f802500810020081c0034240011400e10f00c1c6565204c00300d000b5440f40902981e001700c045410010043c191102401d40362009112940c0c5407070544004001500c5118810b280030400060700d420440038054002d50041e01c3c04002041d03c0c11054064460114030102501c0708014005c0032455069a01c0c40302880303001c0008a4502d9820b110310300303000141c414000341c1c52040511007002640141028002d00c0d060350038112481c01480c050030760184109040b20301c1d41072400c2108020010149105a54481c030003680600c6c0c0310b0078854102c0300b20b0070311001d21002c00c00602c80100c1c56480544 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 828016447 1250 828015197 828015247
    0x80d050d02071518021e0d0f030c0c03030f18060e0d03050c070e0f06030609060403110307061b02010f0b0a030b0c0405041b11120a030c0908010507090f05030d05 71
    0x40f2031003002c90b032204115105414401071120412809104500d032550303000003a0306903900d10780030f4032064000140050500c0c0c0d03001407640354030310b8841003014041d1402c0c4810fa5080b25402140fa541c9041c044c08040c04500c0f01c0c4009130034901010720701011780d4104400d45d103113176940c101e03c030301c2101c180400e0391200501601440414015180c0b03241d020800c1c0d41c040d208a8203045514101046400b1100d00b010b014503200703810150030000e0300e402c0040c05580c00740d00751605481210b0140b003800c1c107512800c04003070200c50078141640c40c00d94a455061210040a078020001c0e0a02c20f40600700311140c02c08010f81c081c43d0341c2d4040001c9842c0703021f4240c00c2100b46000900d07195843c400541111a98506040c00c15000d010813822140c100d80748800c60701c102c03400707815044400403001e001131141050a4040c942d445802c100b205214003012005231400c4802049941810309000d0b05150440c0325115031091b0802d004034890401088010700e15925441c1c00e42084070407481c842600b00703000703104 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 828017697 1250 828016447 828016463
    0xc0a0f0e0312070c0e04170d14072106030b06100212070b01180e030405092e091505061b1f09060606111507030e100c0306080d050d0207 60
    0x1865169002e22401039208104200e02c0e58035000c40c80c0004181289600c080d001010440c1000045004821081103241c00c034100c066580c403c0c082e4100007043e00003103e90805481004024215400902d242d100a1081c10580c0f50600313090304840650b00c2e1408010000e00007007010450a003880107800d401c00440d401607801c80c1030b02031600314854000c0d02c07050700d15540541c010400b0214281005454800b101800e000362403208201996910581c407400e4000c11400e0001030740c0b05101c202c1c0103102800c82c0c0300b5135510044058440c0c030139003960145032501e501d02a9260344040b01d18180d402141c1001c3c02107420102d00151011000c0c20640c6003041e6805501c0b030103400e8114542084410086100c40064400c6031804c3c09411190036030041010300c503408001d05c0c040d00e4001152826180c4c14480c0200c0e558506600320003524403222040c03490300c107001003100c6011142d0080b038074401c0c1c0f41d6400c100303441c0c2d5188220b0303540d8880303e01c84001c41c1d4104020520800c864004255050240ac11 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 828018947 1250 828017697 828017717
    0x20a0c11011b1a060d050c1005070506090a02090c07020f0603041a01091b0305060102032a0712050105060906060d05041b12150c090915080d0207150203030c0a0f 71
    0x160b04040c55405404a40500095031004290720a0802243d000a001d407182410080d803966100c0c0e03074000e04410144a825a00744100e400381c89042200c05165005080d682103080220440360349045111003240316892820005a40c08400410340d541c1540040250742c140400c0300600c01c456201030415103100241c9620240201110300d00c56008103a043c4000428901c0103013540340d0304071101003a008050411041c08101da0b4000306030307a007500c0d144452896054609210000e5072680c003019007020b0180080000341341c00c00440001019000b10021b02c00d903964a81003100001003101c01550109062003101190015030b4060f951144c1b0238030409484444071484d400303075100507a01c12002e24030240d0883c0100400b404c68a040342c44030400510108a030800c01620040050003404001d99440070a00856100745c004900241400c00c01d98042d401049402074480d02e032801266004072403003805900407880041280d10401062405074107050091108640c010322030ba8040d030800480a003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 828020197 1250 828018947 828018977
    0x3110c03040308070609050a0309030308010b040f050f0111010c030204050414040203280b0411041a010f030921260708070509211f021804090c0b030405030715020a0c1101 75
    0x48041c0c829400b94840d104c25500cbd40ca4001d250550580002020000601c01003003d40d02001102c410344d1000c65241d03004030a0a40100d521806d003284c9116950b0a0101032092250154020019100141c070140034a60320040500c203c10390948000707401d0350044940b8003006900124054001c040f03030107031080b9409a6160100410000e035000d4410703124001240c0c506140500c03030710b1400c907503c0e00d0340320406515800180c14070064465003024162510145010071203102d00344620240c10b000d02c403c0d205204013000381840301c0004403569400ca0b040101001c88240c0c5080e40c4102655901c5941550b00c0305011602900480d5002c0d80151035402800e003401c0e070b242012104052400b005140c040b1a084d100884040044240001144100494142c8072449108108910700684020520b400c481c03a01d031154480a92100d5481e080200030b00080010120041c085a17002d0580e1320344040160000200700e00c942540d41020038070302500c0303400260041c8103402c00039005051004c100e400e441 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 828021447 1250 828020197 828020203
    0x5090a0c170108060a0f0c23040b040b03010f050a08070b18060d09110d08160c08030304080717040e04060b0103020c010c02010e071a07140a0f060c03110c0304030807060905 76
    0x380000003d82c01101c100545882e8a2140c0186480c80060901038403000b95030162000f100540c0c009940744041703035080d0490381d502044030028240d6a1080d5602d030740d500d1400c811a0002c0c020781c0000181808000381d1840c0c00b1054505a4198a014703000180c41c1030b120140e26800715001c134441140d03c000d01101540ea107030152240114210300850241c070a440c080c40c02c0b01051202a10808108240b0b0010644250070766000d4110200c400450314001e060110726002240e00c40c0d10240b20000c1084100030491003d82078140c0b0905204001a014071400d081901031401240c0801541c940013501282c41900b1000c111041810010728022540354400d00b900c41002100015039100e42406000031070403c820001041800c1a5825041d080144506540302d85207000c0c14007034920f4041014684188030f100d9a160340301d034500081505a18104024158116189000c030340b40c01600100622060112812020090080c51400e41540c0d9200100e801001e070640b011a901c2c001c02d80022020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 828022697 1250 828021447 828021449
    0x302120a02180901080307110301150e130b070906080703050106051c0902090703020c0c04020f092e2d0f232b0e10050c0702040c09060e01020705090a0c1701 69
    0x250b07024580e1007c403414078001c0003281c40078050282c0e262200e003600241c1b0031700c03031101512090515115541c80b0f840c0d1070540740e2900c010142100045505200e021034102c6019400c0350002e455198103039841040030381c1291003d100b505d000c11020048105840010240c0c40301d0b030b644102000600345c10035000b14400c0350088070510301190340022040034400e410400200000812113095103010b140c05402030450180402c030700c0c0112a400146610b070040c612003899040e5406500681050b5541701c0100440c5d204465041c40e002c002c0342401c03031845804a55070304031b911070f21076000d18a00a07a08660440300110b02074400502e154038800100e10b100014610401d81071941c001c4803840b644e04200030b5941d84582c0840f00d103022052100002d0121ba002c4004150384000140d43c1c1d00c10b10640c00500c03691f40029409890000e010200c00d03000b44e42601661490fa4500d840c0a05031001a0303994426401910780c4201c40200203448074546400c0302c0d81d028443e00d406200e030212030034440708440d42 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 828023947 1250 828022697 828022709
    0x90c0913290702100b100302070f0605190e0109050a24020f040503012319020c030a021506030307020d35030108060c0415030908090a23010302120a02180901 69
    0x8003405001c5103d9041200a06508103041304102d51108100050124803c0700d1202051540100700318040c0030410070008030558100000b03001500e0408211507080c9848110303003a800380341c52a001d0860105126800780c103940071000b05000c5450340c8403040000780c500341c19040011030117240d09440100780040c100800003001f01544641c2040201400d41d0a0705140805655220b000d4007a19a1300549058202030308820001c4908042181c2c80702912034403a528809100004001c2901680090f814021050305150f50803246ca80c2001c2544a102e5000c0180d0710030318252043c400f180012100507808140b8055000c07804403030f480d00d0400b100380e0700407050b0604408401084001d005000750395000b1082c035402481c040c100818101d8210280c40103201f00b554071541c17a0204541c030400c552002e00e00408104210751703a1605114521a0300140c043d400c03403c0701c003c4959500134000c0d2602074540c000035485a81d500d0600c5030094110030580b40c5001c150101820150716003104d114080c4c49 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 828025197 1250 828023947 828024023
    0x6040512031b030901140a09090203070c1202030412060b040b1804480306020d1d0f151302042306181b040f120308090c0913 55
    0x42d0207602101d101841014048041c1c104001002a0b81e83c420300a0208044e144c3c00702e525406182011103541d045608902d060501c000b080c1718019802140700c8807110300c1740e040011007000b002da0417601c90007244a004071510100c500080081da0307642040115031409007000412494101c00641c4005514000110304481c3c0802c1c003081c028200d40001002c01140c40d2031414400c0010f040d0061071030072a081c0c850422200006100500d4030a40c1402140c2110041d5143c400c0c6076085001848408103000c41c00c0c1c011b0300c100c10035140204010980b1840340005e016002c10b038070011b400740b100041403002c3c66424843e070040103a44612076040540c007074241031080300e410300f060b07809089000f50456100b484d46d10310070a114001c6c0f01d0800d40c0100c10f00c2c1c803030940399034001d4281c040d80103a400500c0e210f0345018001c1148030030451030079202800b0380c0c0c960300310780c1300d01141c0d035100d084200e88103401c040440006081090320000e1000070f80d10070a50300e403211514446104050400c003408820102d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 828026447 1250 828025197 828025207
    0x1918180b070c050d0c030e090910050c04090c26070c05010e0105010302180402280b0c060a050f0103050604060506010e030d020c0907030e1f0b06040b1c0c17060604051203 75
    0xf0708000c1070881c03070410f05016036001e920f6117025121400c0b000040340701f1120b90340000c0003000c0910401d07c3ca249200c2c024051410050f4010130301d40c01c98021106a286000c18043c9035030b210b0280a11046c1c880b415511015070528403480c0c0b030001c020020f106100c41c81030f0176400503400740b0502d6030900030b140c000241e0394103520401c0080344001e0600c0c40340100300828031004d030362400203540d0360034805c5c6200041e41c5680012001e01c501e840e8803078900c40002142c81d142450700829824460884d00104100942d80e010134180310400a00000c0c01c0e503846070000800081050740300c940c01c0790741414852800c078489000a86410309a410200058100d0707401c85503141001d62900c1d80100300b81c1000d014070303002e03200702a940d810340b00c5840d20000700d51800d1500c61182d03130340550031001d4003420b41581c40340c0354507448202c1d81c409500040d9451001c1011480703404103106c2d28005001e0b940c0c50040c443e06841c61980d8030600680242d50044040000084903039405071030f41100401d03400a15191 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 828027697 1250 828026447 828026453
    0x14040f0b0d061a0a183c0b030d020a121704150c080603032a07030b18150105060d0b09010909030e040c1709010f060608061918180b070c 60
    0x503048000030380c01020034a07014841700101c400702c800e64040b0700070b0001d1344001408011810340403051b0039402c840140740000d1000340c0c1c0304062510210300c220090064009207418159107640c0f070542c0c880160466040c030380000d0360f035080d2602884601d00c1c2020750541e1045880c6001c01c4261383c01c82c1d186c070510700c08100700c2040c1c8c01140900042030501c81c1080c038260000c60344910460007500110001d4601301181c000c0e180768441080d15040b4100c4607400d03100e2901c4411039106652180000354043c0e1417a0759500c00103090303491a030710000543d20700d07442d00c0140005501b08a800000f17254680500510340d448140559009241a94011403a00054180541990303046010750b4011410440030000f400e400111158a120010501c4007195032a542c04a0040c12070700411541d450800500040381d60303200032a10f000d07010844031400c1102045489000640c6944500c03e07862641aa00282c040d4255102e00e803000400f065400e40c01075248e949010007441107680001103030b0303150211424 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 828028947 1250 828027697 828027731
    0xc1003090204181709060d02030a0c1103040b25021207050a0614030c0903101515031e020d02070b0c0301030b1e0a0914010c0809060901020414040f0b0d06 68
    0x80c102c3c0118401c100300c6481d202c421000f06914004411070100040302039258807902c0494074001100407045499041c2081507001400c2e696001c00006180c802e400700c0d040a0100482c1c0803281c2403041d0038038142944000e060200120030248400c0700804401e4405a10341c1216204580040030140c54041c4c2010204464035525400000811001c01c41e03400c0300c080e803042220307005500d00f11040d85803910900020318004000001d106134500348480710904215000072582035940c051180404004419012822100f11800b05001500506000940b5440300c1d03000301000c0c25803071005460219036841da03204a907010f1742c00003000003000004100380000c5540c0603170068101581502031038550484150302d198040d064014507075440301c91000300f0022042d460182c541580080c0000c181090b809414030b8401c40b001c1055008440006030303030031410310840703065804022400408201d0b82c1d0500c00101070740c2c245039608682e69036410071a55101c7c048041d0040c403544010918003043c1c0342c8828 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 828030197 1250 828028947 828028961
    0x2c0118200a0903150911120307171c020909061e0d0c1a0702030a080306011206060c0b160c110301090c080318010305011d091e15010f06050f0c0c1003090204 69
    0x705252810717000794001482880a04002181111829054002a60043c1c1940b1451400030191050400070624454090307003d42020142901007920469141d03e481e41644102c0c50b0b1359500548540029816240c9104c1c0c4051002132410030b64400307001c000100717030b400b032500c04140c0b007604010008208424280480341c0c0d160144035080d5040065680c0070a554048052000304655000700c001307455640b054181e4840b00440e400f00340081c90b07542a018108200349030050341e070002c40e44002030625071503c1100303e441c2901d81e10b0703401101c000d0310b4240c0004c1490013030a0b8076540f20304041001c241c4038204580500341103405150380341c54120f20b040081d61a20141c0c2d06240c204001003210014110141300c4407042e0004000d51a90b85a200d03e0034480300d03086006d0491082481982c81b1080012018008064161481e40d00c0c1d0b29500800100d0045100740800104104110005101d0801c0a84141c25103c000ca94002603020006501859501c0f031607070004e0756600500b01581341070b0103020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 828031447 1250 828030197 828030233
    0x90c031a030a0c060518030106060c05010b152703070609060807180603020c0102210106180308040b07081e0d1b0801050f030a020603012c0118200a0903 67
    0x11824440b60350f00c005110142d40b046500b8080c01180d82d20b00b02d1480b040326002024000d008000440c2c03214805014129880010764840d860040f401910782803210340c1c03250720090380742d280d07050408815035801c2c88420510049843c000702d4200541d10307182040301c00081c040c43d80320b140c840703810104010200c2000420000400c8001450420994281e1100c3c0c425603205103009613850480303c009501a1080c181d2007c8a40d81e0b103903a88070030035a500f49441c140c40107036481c009040000da280700510b140c5804090842041048200026045000140303010741c80754010b541000424581c244032040081039403141034000050040d100f52041c4194041010210028100c040400c03100510484050088501400c2c040140c006aa9403c00000b460340364010801d079501d41c1c48444441e620040c2c032840090200400700d040e40a5680d46e034016050301c0001c0440d070103005030003070204080c00d4900c25861482242a0f554421a020b007801403031504600d884800101c0d01e10703e0001120740da504111 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 828032697 1250 828031447 828031453
    0x21911030f0304110d201906080c130305190201030b0423190204080c030d080403020312151201020306131b05221e080303010f090e07090c031a03 64
    0x1880003211880990750400e03080480143d000341102c02007002c1c0c04a80b40007a2282c2c6c400020403400007446020600807543c10354010703003d42002c03c624810340649014000100300300c4000102c2e01a45030003c1c01c4401415200140456500c2d140c05082090701701e13217807542420341d02a6605658041c02007a003800000d8404200164084040a850300405080007011100080c00b20385500107007400e007a403441009404560311650303581099590010700000074028044d0050310501c843c020503070784d031040303425030040d43c502001c2020580c11544000d214240c08403503070b130028916461751040c000001c507041c0c00040c0e0f607003803080c104840b400c403045203007281ba0700b0501d9401c02000b568001d4a4164040d080154680300e42c0c01020500c142d80588141000c00440710000b000983c451a0f443c1d402d01800c03a41d52425200c071642c548922003400340c002580046541001041c603160701030340070060002c040c2c414803501c0710f810105944d070107101500000c1d1a07074842405920200c2c0c0411003094200c0c01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 828033947 1250 828032697 828032707
    0x60303051e04050904060f091b05010215040b0708041505010f03020906091b07050106150801030c0603060b0406120e01050103061a0103180201081032060903120310050402191103 78
    0x3204100c4c01000105095114000c2001c0220139800101d982c5070307c800283c510724440c98001880078600d20649005118002400600c58050b00d20345005980055140440b980c60301e909490300600074100700d031001072a000c1046540d10601c07030580a4030f502d00c1c880e004180b460040040062000c0d080c0f51285003007000380002c1c4a40c04a04000500087c0401034564015003842401003000b80e0007545c0f4003405e502d094658652209415060b41c4c810b54501402940b2080308900b15100c90007905507104003008184141c0b4005d0050720000c000c56200429180e41d07400d00c0380e01f91402a07104544071604e40c105080006071001c3e4114280500b86000c1203501a008030340185d415440b400a41440000f03004100300d0740c0d03000c01150151104403a612819581030345200300b03610300c0e01400300c10741890001569461900c68201c40c0ca400008000b41501020003038100742a92000e00803140b0842d002e1300000342603d540c0042c0159a5500c0410206444ca034000071300a00f03801880480d0541013004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 828035197 1250 828033947 828033949
    0x70306061d0901031205070212060108010e1612020d1509020a0605120a020d0b0915030d030525350105030c0d0602090a05040e011a0604080717010f060303051e0405 72
    0x4650f030442c2d030041410000303032800c528261901d00c20b411000e9003001d0494030b8a40b0ba110001403240c12148070400811000800364001910b502e007183c4540204100c404041001960504102e0141e50001700840da040e01c0c15515140e0904811010007d01922071190b00250724102101c040100382c903040051800d083d40401c086402402000381c0074266003c99201203504065000e9107810360040c00701c043c18140b001d406240c0c95500c000c00c601c40e12030b181401a1861080c010a0302078003000601011031000740c003046043c200f889518004000802103410540b40e450500c03000201880300c0d014040103031040c00c20322040030507040039000754088510500a612441c0c2448901a04243c0c010307111005100081e01c0390b40c0c43e40c46164820f00b0000600d400c2c0c5410b622108007428180740303014030700c0c22030f4060000e40c2c0941d105401e80f0740c110a100b007250040d5006c0d54846858000000220980c100f003841c000c0360b107150000d800196020581c084101c10400707805c11340303103d444001d0b400c01e45400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 828036447 1250 828035197 828035209
    0x103020c030f03090106030b2806050a030b040f05012f0a090315150b370c0606150c03020609010b0d03050703051b0102031e09030307030c090e070306061d 68
    0x1112410001c2e070000000300c452000394054400303980e001408d41054100080c2a141070382e80710f482c05100c502c01800044131041c0302d102d41422100080d21000526195440c0c0002c521401081130300d4410540d01ea1030700180080c42162401d2541c1d42e4102c0340b07010164036900c1e4440c0310880000c00d1010401480000c2604245600112548002080c4103031284405a070090308902c0020b400d5242440e401298512600c03001d400401c2401004110704084031712149c0303082d04090582c0042c1c07880c1483c01d48500b882401c0329411580202c00c0424050380e152280c90903d8590303403c40c0300207003115001104040d41440941c0c1c000b0180c0d00280039040700380d0001032504140781c4004040c0000060030004250003803041d0703481a080701c3c01c4118030400b481900c50103580126120a40141c08240b001307415043c0d4034440d40500c89190045045a5858000b5002040d00c24001420303c4010940001e03900c8810200c28440e514990303003c22041d18280000c1c15000804400004c442480ca0045504d40c8400b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 828037697 1250 828036447 828036457
    0x4051e030322051f1a031b040203100f03080310120305092704060603020906010918020f04031407060f050a080406110c0a0506090c010e0901090c020115061d0103020c03 74
    0x4003030315003280769850528138000d10701003900da9011102400f03040405181d0f0040d400310b540c04880e41c3c0e01142003010540c85244810484c44860100800000c07141443e0f406994403014100419880b192200c49005402c80c11350b000b1510500000108032010b02d20328500030081c1a11a440f82c80f8024694000e0403c2c081c0c2c40349140241089411035140208a41504001d0b03500b003c04559542003a040030f0019040074003050340295185000f20380701d9485809170300c08503140054100444424030a010700a58440882c440c0f00391024080840440c2015240c0c03862045440e00500c00c640ca0a00e0103010030800d500310100340001806a416061740028005034082d90003200012020070041c080e500e0760183d03a0380044140f00b00188002040000038045004110b0482150031100c0d141004440d2082e0441400b0f0304811039800400544601d80c000c4008541035000105841c120440030202500c1107900550000c2c610031400c4002c44040704045030441000e10b015858820f003d034141740c3c0d900c25 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 828038947 1250 828037697 828037741
    0x10080c0105030a09020a09061712090f1e15030f0a02180405041b15020714030a08030a02250204050a0504020616021203030a0212010906180507051204051e0303 70
    0x21000d07801d01310350346c40c0107150103007882c8101005001d07100c000070012582c0d0080d01c031540744203036000c00c41c400007690306442294900504484082c6010000e10206c0d01d07410410044100d446403c012081c3d03660642052a802031580303843d16840c14003803c0c480304c20302800f408812841040590040120003445485200c425140030609454034034120140e414401c0120508150305c91011a01100d8007500642ea90250713400c44410f542c82c0d0303a0803c5070988502c81554903a002680300c400182c01b020103160303c4003000d100182031001094008041d1811140e03201c10034454141034030111314042c0b02c0c0f40e40104524504202c9803038035a01240d0b040c0302d085c00c14800580307403c10140c115921541010504030200055980340d003031150042c400794200c50306101c3c400a000001040443d894400e03d01100d0711400c4d015000d41c81d0042c00c800901d8080c211000b041000c0210754032880c100c2c00300c00d000c0c1d4459070040840700a013140c40342c20650030000c00f504981041041c40740d42d0007000181c500c3c41c24 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 828040197 1250 828038947 828038951
    0x10b0109090b03030d0e030c07030b100e090703021504080a06020405040606031a1c0503180909060f0c180607050a020307050f061e1605070501080a0c08070f091d10080c0105030a 78
    0x18608020324600400a03408e0107441100804410070075800e03c924000c81c5022502184603480c3c407040c3c3c91880b002c0343d80e00843c1d4400c0342e0400243c94441d1150a0311142100e001c0d10305512086041e00f0030480a02c1a034641e03400141c100420304151040000a0801d032030200030003030f0f115a00d0161000051070070b074401d43c2c82c2d452101f00442c1c0c43d00c6440480740e01c0f10031240c0d0b6410424404589800e0ae44105100b504503d0025400ba080410000d10a82c10801048100c0d640c0c08182c020940100c0d01d01d0040c1100e20000325010303110a401440d40c83e014000038000040319204140c07401303540b600034a000e10148482040b29407544403d035962101c891030740245070b6420f00c050000c9801440b450302c1c0e8401240448400b440004106641a118280c1e14144241c0e03924007844c3c203440d203c0106800190058000134901d41c401e11070282ea44032140b410700582540d070032103101185264003160302d580c0400d000b842101242400d19600501c55507002e0402001900000f070f01c20302004000e540700c00c1d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 828041447 1250 828040197 828040211
    0x20a02040c02070f0603060801060e01120b0a140403030515150405010302030c0d1b0e06070f021002160803180d030c0b040c0f06050903100b090c0921010b0109090b03030d 75
    0x580248103d101800c2d0b00038500300d540d40d807641d009014080c940f003a041254a85580820071198003a4214103031103079805096842031461307403000c40d1408010034060400b039807515004510a031100800c2d002e54000d0741e000c102030802031803100914040e0200f017441030b1641c00c10581c40c3d103000c006480407560700342401a102d0b59030945042c00c40c0324520b1902c82d0149407603007078034160a211410441803402e90f40ca5500c101844424070205200c0c5010140100002584020052902801032000004c281c03050700c0340311207500b490b200070500c5a00f26401513017012406284201d042c4400010481044581c4140d0549a480290016100e090041c1039100324034009014004004800700c000c00c007840000070a140e0780c0c08001c001d41c000e148443c0c407034040c19002100d120303090300618440c0c4000801d840c2050720b030000360741c40390f50100b4100b0381c014051803c110300d942804445081004400d200203e0185083c20005100d84260340220303001c20b00c2c2420451a0341c40010560f803a00003280c200107500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 828042697 1250 828041447 828041471
    0x204120f050f01060302100f050d1121060105190c060e03030115090f060305060a0b0a0302090108061f030519020d1506020f10020315060c01060302040b0418060c110d091d0601020a0204 81
    0xe44940741c45020070072f00f0f10852094a00520f801041d49251544031210785003080e03c0007080c0d00c02c0c182d41c2a400128103000d56000740c54440c0c0b84400c12a034900b403d2000d60403a540c0c2c802914100f80044101c0e40012004014a2031058010b42c41c104041c60f003180c00d00d01b0002c000c840028103000e21410036a03110001401501c0d030b44c000c00d003d81502c1611a843c0d182201000740130f584080c0455001500050108540c1d08254907071401d0385040c80350001c03260001907002ca0040000803c212484041c0720606410390304184010722851030340f01e00101e01850b07804a1200d07164004c1e031004c411944040469401a1004611070381c02008503c80136a9036107540800001c1d01c480d00307031442c0d849000090390703400740d40056208004581c8290360602c0030684050811044460324240081c10030841c00f58040026050307031110303113903940c54201030100c240c451141a1a00d1810300201000c00c0c1c5505041c02032000505082d8142c50f40c00420400c10301d00000000e496000f4000020b000703039203a8811881c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 828043947 1250 828042697 828042707
    0x1a0f1006080c0318030d0606090501031b0c0c0b040e06031207080417071502210a0c0312140c03040303050a0b01170a331d0c07060204120f050f01060302100f 69
    0x156481c5400705e075101c0701401c1c1540000d00843c4220004070702180e00000d6603500900412a207417900110701401c0310790320383d81074071791400c51101100d0079002e034034012405260060141002e400f82105951080c600101810301c0c04800c3c80441c01001000d110010010312500d04070b03800c1d40d001079011a1003809660089240c1a0391b40c2100c50549490765038580b4942d400550b8619207400b07100d44a941c415202c0391459548201140500000c400c01040408a0301502ca15410f8120300c1c0d00c005203505c0221080a0303071020540c2e040f41140b01c00014042410790502440381c200c3c441440402a1101400010f4a0100304064039641c1074981400a07490074203a40c4098a04c0400c24428000304006000c002c01c0100b458040e00130301c0343e00400125140720082d00c400442c44400d03021080c07076250b400190362250001d12080312119000c010100f401038070340340303d0360600303214005204510b001490010305220743c005078901079a25000003040507a444076540c524044244c01e10f8003c0c000d0314001161 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 828045197 1250 828043947 828043981
    0x30201090605180105130210050913021305150405030d080603031911332805180f1b03071d0702120a050901050d091a0f1006080c03 58
    0x216480c54102040308070f03000030511400e0440316100811a6645842103140e200ea441c0d00c01070b41205540898040c3e0a0040300200080c24006111380007904000480c4020703030740b12481000e43c19441500400c20b41c105510310710b01c0c080c1100c501c60704107070400011942c0d13040600d660800300031a4a001c82c140d034405000b02e42c921404981d8003110b641030352001900d2180c19420003412481103160609820050b000682400b868205e9250400207040d19080c100c0702000e48001180e2801350701c105051440d1080d2015282c042d1680844c0c245002942d0b442400707042150448180c0020f01c0410111401040c40c5030140b000703620f01c8854000c0000842e2a081094003c00c3c0150900b01841845402a641543c400d88099003103070031460168041c5030040c00390001d1a00400c0e01800302000c2580100c0c05424a020401d074001240b00180d2180c01104008040a41c800c2101c0e9061100a0b034916070035941c004000980347c031103285020001018803200030f1070200300305c1c00403011402c12120400d03003203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 828046447 1250 828045197 828045203
    0x60506071515091811040c1b14030301090f05060109030503031b09100201270b010303122a0306090506030c01050f0d052805011a0703140315030601050316050d03020109 74
    0x81240e000362804c0c219410000a44450443d030307113803100620b8a805460a099615030b01d007081425a52039100740c00c2558081140c030002c8660171413149180c108061802004101408103c400c545a4120110342019101c0c0e0304100c045803061021840000849410180040b242d41c803040985034294058010b401509030310072160b520808001da4150050000584c00102c58504a2250841000e4a02c44003a00503c0e05454600420200b03004000c5c8035186103003410045040c2d00c084840780322a03c14110306e20074440c1b102c08101c030900d6240c80303001c010b481460001c01c07503400d003140081d50307442e24200160704100c0d000407008044d4009106136511100d00c010309000358204a0002000b40c14042e080b80b00c03140c0a24000072551169020b014125030201d001e0044100e80c4c04c100b02d0076a0310506041d814030403042c0c0e060200324041d01c01076200f18440000320307418680d8081010f0800006a00c858845d5100e0106507100c00e82100c5594121035003110713950011031540c94181c2c090f1075030300005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 828047697 1250 828046447 828046451
    0x40b100f12020f041515020f030706090515190903021905012a0c111206010611010f05060913030c0b04061e020c1b0a050a08010f06050607151509 64
    0x546450303440c0348481c0c25071003283c3d03482c052016001030008680d842072003038040821105007000b0300b4102d4090054440d0061060b80c00c074000c4200841d14650103040101d442c55030301c401d078005100d02804503200c00d41414548100c5400c15407061285100c404802030740140d91100300c0420907008000b00204010076100a10802803503060450080c03010030601da640048580620030104807400d002c00c00c05500c3d80703c00c170900c41151240d00d80c0b424110340f51034110380c3c0345c01c0c1c081c40b070701c41000481e0007408284d5540c105104880c840030309503901600030514850500b4103106290340c03003000d01d030390041603039064084080003418215024407403810003422036040c410600080c0051038000007045000049076400d2903c1c201d010804920600343c41820641225030700805542080903080d043d00c400401c0300714950748400014103071241c0c0398068803c50b0755841030b00d881c40809014080003018112011428100d003501c441c2001c10384e5800c10350206568060440101504e0741001014018042d81 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 828048947 1250 828047697 828047699
    0x8033d030605060a032f06120a0b010e0d061b09080a020607020a0b030705090a0b0405031504050c100302090a09050601080a0207030909090f1401060b1602030c04110a18030308040b100f 81
    0x7408440249290103841c070411715140340c1c0340301c0c10001f045030038441c440390350880d1660314a0400402030081990060400600361703038000c80f9540d511a4006800d0040d180045ca60f83c024452001601d2402166020300240d401c0c02c216610011558a0810350182e409036900d6202e4800a00c80109a80082c0401c031004014020001d6101000e44404a800c0e940403a240d6101d96020019005e24421158140d100a5504071511118114240c2180c80b0340126020206100d0004904c92150482c0e040040d40c0071601c42c07040c0c5070824408009000d0060200000d080010000b403018100901c1d000702c20782c00182d8175041601c1184140001d046045040006410502c1c0081540e90340e140c00b601c0345e0003240740c3e00040300c00602c50134081341c200c503410714038200044a59048c50083d500050340d050280c16041015610b5178001d40030a090604040c4e0b546084903207000e400710f0310915195190a134080750620000350880400d030b4219402c044c0c15070041e601c1250006000c171440e000b0f00840108544 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 828050197 1250 828048947 828048983
    0xb1522051305040f06051006090501020a08041712190905180609100e0f04030f031a040903021203010e09060708040305091c020d0c1404090c030b0601020a08033d030605060a03 77
    0x3914905488c0903a4900e24481d0b13846004903500c0100c01405070074035008110421811032103002001c08102030f4002d486074050f091403140d01680001092040d0342441c4001101d102c4d5100c086140900412507001c1500d00040d150b0400124005041500420444010500029030f42e8136020040038402110103980c9000301c4001c0710020141c1c1c00301c020509032522642628040d00427030310102030f113482a1184c2e003111410031014000441e0140d0543c040c0400503881030903020000c40c0a000c0300b0125071030600304010700300c3c43c05000078408410020000148400650320400322004000221091880018103150700282081e41c00b1000394020741074650441005086411001120850150005100320480502042da0703041e00c0c00403d110900d903010300001d44250807480d041031f01841110b00d1981070b030b034640f50b1135401aa040305041400c3d50b020102d031020060401484410401031803900c0c1d4140480380324404141c000100311946803000900b840e110449444020f41e0055406940d10414803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 828051447 1250 828050197 828050221
    0xf07120c0201030e060f04030e061c0e0f030a170c1c14010603140c0a020f0304091e02120a0b130c050c013c0b1522051305040f0605 58
    0xd1012408030741030600301c50100c4400b141e2a071241e044001500b5595903241d40c1154120158141690710540510101c141030f0490314459050311810075000890a409020030b07450148100025511588200700f0100415446400360440008995081485455a06014040e40144100c2007401400748405226144440e0440481d440d0b080948241070390f29288224140c40310740c040080d4000e16140850003510070203000f004101030602c151024010214949070031540b10b40e000046064540d4002260601400d1000101012442d0210b203030581070302c4c15116003040104413904895403000c00d0f4495460b0244848050b106031002000b40c0030409401400682040040131620343c07800c042840d9107a03184c0c45428800381d45040020a2040c0610070000b810351143c1c00120544d251030456445880308629511a0321020300c4c00ba440b8011001d0f005410300600810045070f10355a81c1c100305544408921160744107214101043c41c1c0e945042c8200d00010b035000c0240260305c1e00d4108103480f6585 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 828052697 1250 828051447 828051467
    0x90302150907050a0b090604150216150c12020a060f060905010f051c0618200102061b0a030b0d050705030601230f010c1a0601030b0111030d020f0712 66
    0x4042144544032510581c0e41c0701403d015a5810820f43c110034005800ca00000e84442500100342914240e01c54410614402540007441e01680c811790780d4050821f60803440001801c40c00404e40380546400500606e078611613140501140c140e142c503207107294424803800c01c40b19040b500030300200c40024481c20080105110301c0340418a00000820070580f203246200440d00000e1001415602a0088500d10050380f0f00c101c800340d0380c030b20841030240a5443d0701507071140140e14405140c0c07624502070701290b80301d40c01103045402c524100a6071242c500f02821508440081440d02c1c3c0208038815402001c14506041e489070443d031a0b070040100002c1c0c0d00c81aa07409074159503542e40e84010004115440c0110102c03504c12003a40310429041c0054001041c140514102c2030304e070081d441d000c1c0b448000c9980d8103401c1103003404001455806010f1500e940e2800c0c80c14505031011107433004d44900a40c24024001032300080e0300005404024203540d201c64101c1e40041c0054020b58026050940e1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 828053947 1250 828052697 828052723
    0x702060610120516090909080409020f16030513080a0218071205010f030606051014070c03020d0c1502030f0403170c03040e161b02010e120d1706090408040e0415090302 74
    0x17001000c29907a2807805408616a8049a0b0034180f03820602d819010350820340c08010518001e000023654000141a5140c2c41d6010b5181d0b1075032600f4075604010100c842e44c0000f003d59018816000058030786502c0c2106414410344800300c0c54031340b0001260203030041d6414401e21414100040b58080401100070704a9209582c200b1800d551351085c8181d0b18022402003010030310301032044040c075450344c0091100520030102c9444c0940c4a9000906501803018181c9807503000203018040700e40c1c10b00c00c2160103401400118148102c403a040402441030b408010010b284c640c0803141040f4800040e01c03a0105100f0559032520345502c580d2060b940b048916170010003844504000f03950140340201c5d000b05031814401200e0402d600155047c2940b043c01c250060110342c1c000c40d0021042c000304000640603620420005200021803000301005010709110780301480500000503001c0045404449107648040216940c07401c2407a50b00000240e50030302a810940840c00301070303022030001c8807101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 828055197 1250 828053947 828053957
    0x1020f150f1f0902210a0e060f0606071b17100501060903150506130e0c032503030809070b03010905090d09060503071407020303040b19080702060610120516 69
    0x28074000352481c2e03154002039030b02d903032140c10b04248801030b4203400901d03040d000e441c00200028800c85482c02503031003c80b0400c200556810000e4070303202d005d20040ba009041c0315101d030704a0400701c0001e40790340320303c0f100208510304080d81030031480b4001070b130a0020103501c0340c0c0c030200d54141c0980903280c000101110320443d10303100010031018001c0f0040400c0d240c11018000406072f80d08100d0740100f002400c0d0603400366203808903101544680c001d07aa40c1d10458000303082e02c1c00e421005e043c80c20b420103282c03262a0b00d1504403022413003c801d04c5401225010f00c1e00818a40307a0510580c204520342d041b40511410000001c5403424258008501941e1001d00302c40d424548000c044940040c18061003002510170000300380d007148560010704d030481e070701c0b10321602d0030600740e000903d95845036002903050307403004ca560f694196480494039030807071f0507082000c0c9900e40244020340f1610000d04080c810324802e1a0191054803401d181c5000701500101004241080b52030030100208003048400010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 828056447 1250 828055197 828055201
    0x10504032019051c030b04060515030a020a14070b220203061801060503100f0c0c050c1011010504060615020a0b180a0506070c03030f050609130201020f150f 69
    0x8075114030003407200c001c0014040d90008501c0d190b000c8000658142d40c036208208600f01984520070300b801903580035840c00682c1880910910055614640c0301c14460700f0341d046460700c81404035080326400781c40030364010382d101080001075400044a41c0710072040313a0041500e00c10442c9a82c4861b02840c0100c001d044490240704208404058140c002901900700601007440500480881c03405610048001304042da102d4000c20b10303103100c2c00c0580c13400c0740d02c07030108031180804c03480303202001c21051404198403902c5888055561041241c4240900e008440c802c40082c400c05160000452940080c841401d20b0300f841c0010380098094132541030150300c0d10300e007214000150042d0315075020034101540e03550b0710b0803c55491200100e400083c0614024040064010700800740308880c0d50f1101c0110300b0090800400301d511500e00c2d0070000d482e140030300001c0c1c1d03624200e0070b6104901c442c4540040115100403800d11105a20b0142c8503c60160384002803d40e40e81564800d9000158107452030b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 828057553 1106 828056447 828056477
    0x5040f0902062d21062d06070218071e020d110703020409050601090f0b012a081812060105090408070f050316030e10050301060e04060305030c01050403 67
    0x40005902d04c00807600d00c00340c0d0340c0000c0d041d1083c14482d05141205254840702c3c2a503080781140500c1e032003216503500d8040714002d44e8054603e40c04071859068108200d8001d0310f29102054a103210000040620170358240a404160b004200000051100399001d1422a500760041d01a030f1f0710100140e00c42e03000b1512001e10400041140703614160040044800102119500038240100b0010136a881240030b0069248000f2114a050817446c458400c200240c000034a83d039004901c061900481400202c0000c00980e810311040d000c015042d6203c038800d0203065032024108001c030f8007040115001d040054815044000d03044a640c503042e280d600f00461461103c034440040000b0150b0100440e03c0b00701303040e1802011854100005803250005006120400c1506114203040b6513881d0004030007140c101007566698009462080d028210445080d80894683d52041c008 = true := by decide +kernel

theorem cover : BRFrame.Cov 827877697 828057553 := by
  have h0 := BRFrame.cov_init 827877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 827877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 827877697 ≤ n) (h2 : n < 828057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
