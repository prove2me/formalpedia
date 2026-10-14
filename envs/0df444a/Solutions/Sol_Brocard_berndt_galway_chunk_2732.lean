-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2732
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:34:43.238979+00:00
-- url     : https://prove2.me/submissions/2f2a8bd2-fb3c-4f13-aa99-36a96a034d21

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 491187050 ≤ n < 491366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 491188300 1250 491187050 491187077
    0x1407050102070b09011704020307032001120c120c050c03040b0d14041a07090e040506150a05060d0e16061110110a080a0902060a11190308011511010212010501 70
    0x7410301401310640c3c00701e07001c419080c02d07800c2c000345000c5e4818001411505085c1c3e03207403540e05460759060303600840d59640449508003542c00c2118800d14120103c8104010725181c0c100801c012081105e100b042c1e500c414a0000241c46501940e400b0841c0905595a9903950102e518076503001e00055145103003000a2a0028951196018401c03a0451996880d0519000d84c030350109200904440502c0401d09021840000300d481c004e2089108800070806410980c0c0300c55241c110901d005841000d1101c028000e5450300000e0321544194014003050444000c100a401d200070445d0b0100030304062840040c6069100d03036001d4030a400001a01c258016009420301958403803200c000d08400d00b044a4401e0900c074003071055000c90551000101d541d52503000070720303d503c14507440300022200c20403103502c000c0600a041074200010701034a48111141d401824540c4140b0498422429401c4140401800b46a2170012003070b25a0085581d0a03285008001d1f00d1402c0c01060b000a0048a5009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 491189550 1250 491188300 491188319
    0x20d14040806010524070602030108150603030910090302060d062409060503130204050406020a110f0d0c021c2303130306021324020c01090f0b07060207140705010207 73
    0x6007615040030141c40683c0c02d0100b8007054401c2048011000e030700700c0680481001d40c680203012540c0c4540b0700982e90754586404c0f5490000b030481c8038421440301b5814454556000021030f0700c40c0c0016283e4020b01c00da40042590b04d101641d0000c1d400130000620f600c514400f5510100075500f250f0070390054443c82d40160048804484622004140b1540c0203102c0d26000d0b80203554800c640403603940b4250507540c0824283d030800c0c1c4007160391540108602001d150402c1075200249602e400400341950780c2c9492503501d200326078030744090001d001e81c004250b440f2242c0742c0f200c020390400c100c1000e414514180741c2d5080c510020006c00f110840c00c105c0c510724007004540403141400e001c0b08205045442c0e500081d03201d03656250600e0310240000070605140c98003144a40e21041030704104105600002c0d00b400b025000c06030401034004414008984440010001c0c1e5480040160b254038052030300303030001d100da40c0c03010305140b0351211801c110f2400041d480d01a210281d0a0f13501c142c0d613950703400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 491190800 1250 491189550 491189557
    0x12020a080607090b0d0e2e0b0d020d1e08120c04120605070e0a090902040f0204030c0905090109080d050610080910150e090d030e0706050d0509100606020d14 69
    0x22000461241c1d080261442103000b8155540c40d458001610b00b42c144520747c90801588051031301d0752250f44c0400014004005d0411549141c21b030140040f45011303000810030022054002d10403464203104a0078010b0780c54251041f9002c003203d42a91400600b041c62140d0803c00e200d21461008400045460414006440460360b0458000c45480c40a5540c24040c110041007202004901c42030081c155507180d00c135400400e0310b001c1c0040c1c0028107006010903a8075180d881528140100010000100103801c03c03000c0300e155110008054072814852405003020710070103030a580c00401c2e0002c0c0c0f0a5542d0140f03004400441c0c248000320003000b0140c0d02810115240c04054000c01804c2804600d2034008204079100724a00c00c41e156180d030725005500780240e50f000001d07440036103d44500d0342c2521800119428010042151501e0300800078858070981d90300700c252903111404110106020000700b420303000081e03000d03c40743c0d4540400940c1c5240c2c1e0300304480020092040b0440301fa03540d0089 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 491192050 1250 491190800 491190811
    0x21c05012927130503130f09020703051e0f030406141513110903010f0c020601060e06030403121b030203090d091406070203030403051204030c0803121504140112020a0806 75
    0xb041e807840c240003500344010000781428920a40c5192510004606100a181c01065900c5d181d0000f803d2404007a1503115603000900e60390701c1080000c2c00b1a800c001680c041010b045a0000c440400c0f580016050203105c81841c94800c000c0180700800845401c820304441e405a0071400700e1307540705034590b00248258481d5030031a142d55a041d0b803086140d080581c031200c1c0080d4980c50080050042400c4842040d001025965901400400e60f82d040c410640144043c0c07030300003594000c0400284c0705100140008081c488484282528010b480e04a1046001d01e1410201c09200c2203201030040d5101707d801240a010741125024482d0003200f0356010f81c3d001c0002110501144020300c81e130350b071003210700781c1c0c1c588824000040001c034100300c6c0c0001c1101c880255a126450f40c03074001480c031003e070440380c032641060000000315001b0590340c0c0d90003048881c074034806101080200b0000d00c960420048502d008100129015804040d0b28a06c1407003600c00201003640c1d588855112001500c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 491193300 1250 491192050 491192089
    0x80702130506240906030f0103050607051c020d180b0114120303040f06151e05060f0a030f1b23090d0305031f030f02031e0703021c050129 61
    0xa4503c586003802c003c10860403510000a8a40308400c000120135401c203c404080d502034510040c01003240500005030041c50700e00b0268208403040f00c1410305044042e0324200c0d0160b02040d0240e880c045a004107040880c4002d0254164801e803c11480041c424091034100c1440307022415880e0070901aa0840c02100d24040d6056413510303507070003404860010055801d16210058003c0c1410a181204002d050a20b0300e507070b005820200090107005c0560203035114000c14004002400d814008848072400c152800207100ca40920601005102100c00a901c2c40141ca0b5800041500984100300120000305489a14844000d01483d50720034101e0054200c0401590f4400080c0100081c43d00801d042003260400c4004044c0b6176a210415801903800c628800210f5080d4141880082214480907640d125110260b20003d075840ea1305120083c0640070701c009000d0320803410052070608543c046d00a1041d00081d11034054a031400304020f07850310b20303950542e104034940000d0302c02c5100207221 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 491194550 1250 491193300 491193319
    0x2a050403110607140a060b010815120f030a031a040c02191a04030e040b03060405060112030314010f21120e030c040903050a12140112080d09080702130506 68
    0x5a4040c092403800303074801d0700b094051241500080051107454039042e0140000c00190055003000001d5840804070749040c0011002801071502080740745909c40708080e42e5040381c4440400001e490011800900e40141c00f0100e12300000962507004840d40d201d42030051740507100aa410042200d601c00269005a401a079000c401030b0b13282e42400203080c1c0030318264040c12400072071641e10114200c07000c9001800549014078030b80f45c030340300b00103a680d000c2e0001d01f820700d00355035101c0c0d5548040c0602a18044242d006104051080d04101c0c00114849143e0702035580d1090003c0030744490780035400d031014480e059814900900800b001e50300b500481c2190807074200043c00d4800e09808052036030076005162400815840b14069140c40038403030382d40c0c030b6911140088010501907501010320340350350501e007026040240030080316065800000521912a20ba4a032407800d80c841c03850207540c5d0a0410b1302e007406200b40c5402a000f20707402034407ea2031600000542c04202c031022a100340d800380a00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 491195800 1250 491194550 491194553
    0x1103180c0d060c0504030f06050106090e0621030d1401030311060f0f130206071a01090209010503162d02010f0e0d030e010b13090c080703020607030c030c0b07032a050403 75
    0x2600f000f1100480e034242689001d40304d486000b400c0003c00e5094610580f41d8004001041c2c0c032041c140c00826030130060341c000781850070004500f89100a6030700480400c5103110341280005004139504803403020350802c50800d00050b11507113a40709210070343c04101e210046401010010038150300c11420706044015650b204005aa00c46102400c03580290600142442c0103031581001003e2407030040c10070204490440c00b01008008058100c00c21550051040950603600001038076044a580c1d0190101c0c00b41000341210301c042c5803040300141e05040d1a882d0660900001c41c1402d10b4800c0c0e009000719502048103200755800c80158900b117138032900321445040d01c2507200b190041900300000c2510161100022200c01c84a280d003450255078450060420010103c10001060107401038900e407403a42e0000382c401c0c012080c0140c240070300780703000710105441058000f22441e80700000d011181030100004000707003480b5006d04801000c50044641e411134690f072052001c2010313541d05240c507045 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 491197050 1250 491195800 491195813
    0x6090e01090503030109050408070605010602031207053a15030302010e2b2115090507090b070f12080a0b0a050a17030c0102070317011e0b0a121103180c0d 68
    0x10001c0e11810f27410302c8680d0000d5200d0003003a008001d6640150303190f41d01c10b0000c060703d0a028000300c0a101d000c0107440400324440050b4814403540c3d90300002e0b2040e00001501d000080060019041031801c1c42907280350b1940d240314400d40b4041e900030040300c02c120100a81c0c032030164035111580403036038080584442d0000c80030394102c501850201c2d0785845900c54200944500072400c80200d032601044010351700c20305440c038010700c82400b05020a00f000381c0058040a882e00035203804900000703a4205015420a0000f044c540c880d2021600114135200100311074400d890218495003004020141460005400d40640d034008081c100302504c0c01c0b030030081c40700a106c018442e500040c041c00d00005030a1001c1c00a07540262038006c03091035103000c80d400da440140c1048000b585809001f035280c90344240b065042c2c9100044042c2e0743d006021f0280c590b1405e00c19000c403038501340402010b803402d10368050350142004074407520301228a403842035110320051a205800c442134081120200e5130 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 491198300 1250 491197050 491197061
    0x7033f05041509200102030f120c1c09030306080a11061b1207020108010f06050f0738060102070e0412030b0a0f030b010e16030c0e0a0906090e01090503030109 70
    0x104000c844505680648980b090b203070701d0001030765401a24058840c0c40321045034501d880181c24070255203403041625126540f0f0203803140300f0000c0d62032040050b5030007585c20103d400454002500600400c1400b2100024060f1104114000303828080002038100d070004446c1812039203ea0b0310300b85081002c0030f04c05680c004503406152086c00c113070710301706507803041c0288090722164aa81542d514141c0c000504a04010307882002e800b036120b10100011030f030000540c0d6550300300000d804c2da11025410140d031400d101ca0701941c1034072140041c400701d0225070f18103040302c82c070410340c4a01c0c01c0d0f540c1e42c01640c403080e5900c1200b02c41e600c860000382c002044542c40003e0309049040008a0030021004149100450b0300300c00340c403c11424052083c041e01141003070041880c501088543e162003c8d6058003040b40b865500c0a140e103070311000700414040c0c0c1241403100d1000e030030401c40c2a61035680d40040c1c4164440c984030300f4902a1001c43c000742c10302030b81c50859003050086213075901e090440e200806 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 491199550 1250 491198300 491198303
    0x207051b150703020c1005250309030804060309060c0e03070605030408040306090f0308160f031d01051905060607080417071e080f0f1b040608010207033f0504 70
    0x80020007900c28180880240c2062800380d40206840018001408000b10043e40a003041c80f400b0300503445c6812141034045150180e40d00c2c03640500d19240380c2036a1507032440e00011700f03030500400c02160095043d0b00112025001b10307404d00007400c41c9081500c000400713003d130941581040c1c0060103030310300400003160000c3c4100e2000c0e180036507030345450f811a41001d104440088104400405256001917100c1d008203e15440300425441d9190241945562004240c00e1640768540e1054a94000801141581000d002440700340341c00c549201e01c0f09126041c02c049249084c0100d81d55007418000e90ba0901d60160b1010725181c10034036214400050f141d50144148074a40c400f244410200524000307140301d01401ca9900c6081030100342c103103940d4040e440c0749030784110018240b2010000c0e80100c01040c1c3d006040080d000000414083c00c255007003464150300000c0c13003100b0554014900c0e94120f00e20412900901400031400c442c4a200f100004100c0e201074165000403102d5511607600725 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 491200800 1250 491199550 491199559
    0x601050a090902040b130e070c02041d060c0429040b0c07030c0b03010e06240306031207120e030a050a060f09151e0e03040e0c040f080d02100207051b 66
    0x40c2e640d411800c1070b0703032154020106440d0301040c2c10702901c00c2003101802406100b14810184d2a01d046c00810150701d500010f44965287c140c005014018441d401c0c548845400a403016460240c00c0d0103002d0340503220390718a465828005c2c0c0011143e01000d22002c00c004140e661030b01d0300e0010081c3d0950004d030000c4072203004500c000030014071a08134110003400301c0c940c0c02d0340380c0d80740803030040d035228000b81204c0c06840c0d01c016841036a030403c40c9800c400f03440c0c0c041d0719849464041c04603103400c000000d11510040d0000b054800e00c809100f510800c1d012aa480301ea480059a0503d5100c40e00a10020040d41c00351402d040025800d41080940b0b000300080060607141e19114026090b000540030b00b5050345d107185d86059903c0342c00c0c80205151400400788002ca424800503503885c404c030700c180d545005e40c400208000b0b10700c0f1001c58008000d55020003080940310311100340c551034a541c070f20000d40b003220683c44103090700d4000d039070a123034004003e0319240c002c107160b6080450207a0f4009620 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 491202050 1250 491200800 491200817
    0x31f02040e0f010305010606090b0a030f0b030706020f06011d040b0c0906180306010b03100b07110405042d080a030203071206060f0305100f0312021009031d090f0601050a 75
    0x28403005040701e11481201000507495455414050b0845005400020030030250740e0082c8440042d24003250031840d245d25000a442c0c809101d1030008280303070748005505010f06680000c0c10307640081c4035000d0034515025940580d80e00c5100c1c0d6058040440c1d8812030485200000b00442d00b900c03000c540c031a100d40000c610744030308040040e086a2015013040d40018120128503030b1400d040081ba800f52410a03c01482e5007043c901c215141d007124030641c1008500040c9101c1040070501403410540c401810a0200c0c0c10b0070714101d441c1c0c9244408c120410f12105001302407072403181748840d80207074010003020300e0942c0ca0b24040f000303540300030400424424500d895600f800080d1084000a00390b5039549009610242002000e41c0e40150044002e20480902440610ba0070300075036007103030b6019041501a884603d4164204000c030501c2151491800c039802c0141500054280300130047c1d10f45083c0500448020442401f07000e039802c4090301050300004540d94002d1008000030802c9040900f103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 491203300 1250 491202050 491202059
    0x30105010b0c150121030306030503040e06150915031f090213090915020327070e0601051228020301080d0305060639100614010509031f0204 62
    0x251142070784401001072000604081c1c5200c1441002410185008080d8a070f51401240c544980507080f41e41c44174120321580b960400d8066407008000f1035001044d41d445603603421804210031002c03100e09004084104000345210080012680804c100a01403807141d800c01051001d2074000034030f08030454501105070b100c48511070800100401500c0f0000d6511045941124941512540044c1889040407404030025078010012031501c00001e100507100c1da20302c0c41d0f40d00d0b2a49120340e8000f01d204154511505044082000400e882036448843d0f49921600c0c011602072141c0d800300001440b81001146480000450728406030102d041c0081000004c000d281040b64004ea100d942194401101d641007030790180031b0141d10aa048541500307103280e4944016070000510343d5070040e2a542080303c2c0d0300032400000003c1580680040f2201c1c141610950b030010502030240380b61b0001003031054031140d80300c0e00441c0d10200001e030240000c5800081c0001c8514003440032107500355000d000208 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 491204550 1250 491203300 491203303
    0x19060c060b040b041d0c040603020a0302190b04060e01090e040b13150e1510050a06080a020f0403030305090c190308030603120a09060806031b060a0905040c050d1a0306060603130203 80
    0x220340302081303002a2120308030417149151a0700102241d00032400c00d18100090395071040050226901510394a4408143e00610282c1d030702541c0245a0b484008900442c0030b9500c046010360702c520070380781d680c441c5888244c4c03101007160883e40100072210800c00204a0b550816a03010400d10a000c1080b25080001302e6100f520814100903940c1e511102c00744510203621021240c1040010703131030400040c01d1402086c1249058042c150501418201290720300d0f0310341d41100c3e4401c045001c11622962207187c0140138007425660440b45228000ca11811032600c03240429040741031100b078500c550b140d551004550342004003d251b15000b00b400d0169081c20307030340043c841c50b1915179440f0003407400c01c40f003d00100e030041c244501030f6201d04900407040d02c1107008400c07030078801c849454452108680803502c1c1c03840c680146401c14101844a00440e82040280010399071a203402c0c4451145a82481885192442901da01d80c1c8124041011070410200543c0c02401166003112034960540102e07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 491205800 1250 491204550 491204561
    0xa08030d0207051011160c03080d02120906091902010504050405010807030210051c111b1b011b060b12060c030a0b030613120207080708070519060c060b040b04 70
    0x40038254000505408000c0c06100b0341100c141c00050401219550151400c1036001d4001c60500d00420b01e20a0005c3c404910072840007143d000d6101541e4044079009030780650407040700183c1c00d1030b41001059603a50003140d0b00f482999a1401030a80150000306208540c1000c0c905038140007080001041546450060502030003801c0e004010591440c410b2003116407000e40d21800b00b1000b441170348444451840c5001a44c440d403036000c583c18441402421b824460884891301c80308150b202e900c044000440c01c074884403001004a54050f5140c80156039103039980240002120b50083d5600c00620300d03910200c200240504961200381e51213100510303141042c0c0395440b43d2000801086110030450003403800052095000c2c04d030505120300d881c1c0e880c0c022410f00a10820000c54440c0c40c0034420070480b0b0051051b481261150383c1c0e10007035a616200d03e80180d5010324042940e59405200036440ca90854103d0b56801940d060a5120b200c010080d403c2081d60158039100c01d840a0b44c1c0700d0203203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 491207050 1250 491205800 491205817
    0x90905010b0a120b243304261c05120601110309040906020903010c0c050c0a2105031207121515030510081501180204051e0a0803 57
    0x180400c80504200b81a40c0036030081d105101d002403a80009440e80e03113200d402140c1210034004040c1882111022450341d0440c451b0440c0550b0808002c1c55404c40e03090003820005000580d0550f2011100b60303051103a402400c51500c0b030290b410244980e8034810001c140b21800944035401d14003c1110b111040500c0c114000034000f080e1900143d51500d0b440d5003028090a010712100e580b48040c80d128014008510311880c1d48005a2051210380d8046400300c100013002000800c00303040000d410311000040542d10742c440d01102c0d48090034a16142c1c0107998010b9404826030498580c01c1c0000c07420503408444071b000c01d00c12900180c05003003c0c940641d405451718000d6204480704001144d181c003504010030440d0302010426050f00305001c50b02e036000d0340342c042040d83c0c0f01082811900c1ba280d00c03541041c410110000d0702c41c88100e00d900d0583e07140c0d800090404e201c140c1c2500c20b0f80240e0084541c8001401840c0300301494907000c490a420015100311089a0354419190070758010300c18 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 491208300 1250 491207050 491207053
    0x40e0715030b060307090e09100e010609060806040218100b0a080f09010912050a2c18060a052e0206180f150606070b0108010b01090602010e100510090905 68
    0x4480038015014011201491001c1d10b059003036142a80008028114902c9815070096401d00032900b0b0040c207210302c0d020f01c60302007010300100a041042c43e000b400140b00700e1842c1443d00e040456800b0002c030b0081c0c0a540c0040c612135820302d40601c2441ca840f40905140044040d4100004500e0004000340400c14601d4441513414500480322200410005102c5042c50341760680303000000c1d25110340d000901109190a80c0c0314090003e040d200f10302900c0410b4201000c0f5440319a0914410081071a40700b4207841d551420603c03040100c2103a001901c1a82e84040110400d10244c100b24008a0103096000c03100f6003081c580000354009000402e20715001600480100041e08455041038690101038100404c0308001d51180035469110000551810102100c082086540c441040e07401064010301482d216503501da40c0b1600034810311362840c0c042100303400001540d90042c07189a040d14510000350026000c008200801804024030303000481548031030102e03507580a8070421000310300c40c80 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 491209550 1250 491208300 491208329
    0xb10170d090b0c06012106060f09060b0c0c0f010302070b090d0e060c06010e060103110307020102131a18030106081b040e030a0504060c0f0b0703020306130203060102030a0c02040e07 80
    0x1900401140803070b00901114402041080488a40044d40c541111492041c14142001030503810001001144001d4450b50500c040810104890f00c1440121203010314100103850390350b12000c0303040c001d445a90400382c004000d046218240f01040090618051400502d031400d5580d4030003c1a2040e59010342c2940544c00d00e40580350000000d00a4050449a00b800c003d0a980000e50365881400745050705402e840120344c1c00e0f4001d130028401c0d104c2c40603000c0c0c0c691502001c002e00030340004200158003c0c2000d40052440d0b0344110805142940e140564030f40b030f61802e121019812500003058040d0350315900040d40c8441846912040c100114241c010312501d941008259800c2c0c00c41d00a540d0000c200880e4010b0304407003210110b610074100440d8003031007410141500326440c9c03005085500322070200840d055043e030080d4403d00c002c5a904008100d1046948200d02040f9445405a8400c0080490750b501440e0708000043c8000c00124082d1500300549007000c0541c0d0201d0420003406 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 491210800 1250 491209550 491209573
    0x100b0301140c0306010f1b02041a0303120f0114010507020121050114031b09010e13170a1b020901121410051006021c080a02090424060201060e040b1017 67
    0x6d0484040340c412403510044c606807520403a40c80c02a207410080c881c95071168a50f00f4051106540c06041c1002800c5e41c1d11600c612000c1c8070000400c817038018094010900220340e03085503805002c420340041e0740f00c0d824100b07941c1c01521180a0303c0c2e4400c4003003208403000300c640d2809008040c060403505607a42c6030a00f6050a00d0714001e1b0700b005040b0540300160888480792147e4403014110b0b035402e90541d141e51205070302121000b00a01e000b41020b40400307000b0328022201d4000b000000700942d00c0094003030f00c44150540230b560702c81000303500640c01c40040140c905641d510141e020301590780d91110702d10500340b01c0d1514010351480584280c540b1f04205d000c3e01c0001040c0d00a0003140050141e940024094030359242100000209018020003c0f502c5141d069054410701d8001510030094003180b43c105c91128510b4008419400c1300f02d84001c141144180140011a502211004095101c65403000c1c0340410003030504d1440c40b0141000210b1641c842204801d5001520180810841c02e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 491212050 1250 491210800 491210807
    0x807170903160906120f0f1401050406150509040308010e06030f030310030b1b0304030f0905180115050a020c040b18010f1505160323120a0b01020f100b0301140c030601 74
    0xa652100c8070b9000b80384ca40c000030a80c011540d00c00746c1e5000d442240100081d142440342e811022a98100f42d600c0e000c100300400c0110b40c820340e07410703c84110540325245c0e03032420046a200c00300d1b0014006401e03540100003401d00c02c03010a8000000a0640318106c128540f4140355800458804881000c01c5404005001da041c10f2a904410714540d22041800908000105440040c1004080210340926074200b10b219102010107030000070301140e00c074003050b5a647d9a85100707005252802510b219486481409401250002031080d0080e2072603008990800002b00620700625400043c6c1c0058a110680240210f6020b0b003a041d91820000703050000c030644a800c1384508109200c402c01c030550414840001101c1c503141c2c1480c02c0f14146008288140145601840741b410301180899009041c040c4082c1c440d210f440071200802442e400700d0300480c0c0c1c4d02c0030216021499040501459928000350f0400e00001401034001301d1000880c0c00b010350041d40840b500800c00741c01100f071000c01d40c0e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 491213300 1250 491212050 491212061
    0x19051b0a05030a0f0e04020403230106050a051c061e0c020d051803070e0a0f0e01200d0e0a0606030201021b060f070611070506070206070c08071709031609 68
    0x24260040c80120300954032180c0da842a8445902444403402044250510038400b01c250381102402c255100c030b0356841d010400c07880d0302d400c280014182040000a40070140b090b2021104010a00e505c07851400c1c003070100a0101000c82c4281544c04c4400d41c001c540e46010b0f011000c02d0360f0710643c0c4410180e200d460110341d200f000d00380843d0420b03008101c01951100c166000c1044483c0307414038503110000003034a049020740c042c0b407001a444e820040c40c91a40d5201541c2d0401d801001d1141d007900441d032030300300e51200b03100d80d03202d000914103401500c00e00c001500b2034030018000040d02c004c0c0d88103040c2c40c11903030200496105484000501c11540c0c144100c81c645505510480410344600001640341e00450860140c001004281c0e042031002542080c14052400380f402541c0c0d509900746103884240032541c501c0948600b0740070911203445002d40050894000d000503003888565602c104408140800e100c030074140500a85005070350074003000940038045d5414032142031038100c0070804d40302d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 491214550 1250 491213300 491213347
    0x90108060f10030302100209040207061a0112180311031b1f15030201050c0102120a05180a1707170c0604030306090b0303091c080d050601020106091a090702031905 72
    0x40c10700f000040d0f00001c4204420305160310150b04c9502250203d002402403102c050409e034141406800e50310280b20401c850709100303907142c0700701040c001f0040060358098003c46501c401002c50050120b032003100c054141c1c0b003070f80043e03c0c07038020022010550300c008083c0c400c3c40e130703001041c070708c2c000070100c1c041c4a45001d94143c041c0031408c4078290600d81c0480e548000382c1880000a14100481d40070340c1101c00d00c00c580c1e221034a8030b00f46001903030001c20044400303160550b0510142a084040001c0096445910882c1d442c107400400310341c80c110b0342010380112030301e1040b804c0c0d650040101c6009000310300c1d002d0f402090145840e050040c184c0315140c0c001c0502901e4003c0d4400303961004000ca4030314030740c19184400c200303080b511219100144e00c48060085000407805a40507040f540106000e070800764000d00107117443e04000401c5803a141c0c4011201d6034810303d941d629050441103030303a00070014010740303040461502044000451030ba510354005580010945000d10100f84a0301c3c450 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 491215800 1250 491214550 491214571
    0xa0806041b0215040309150e0a0806040213020c0304180207060b1f0c1a0709031b050108061002010e19020319081e1306030207030e0108060f060711090108060f 70
    0x31540800041e45800c1c14240203640d2600f0400010141402001c01d03200070038100d1050583c1d801c400d403008003000da4000000340700d032030045e00018664000281e224000c0f07400402d2120300d00c6800500c00e00942c000e01d0303000400d000500000691661504001034950754160025030f0b10340303113031070b00404035010b120300c25104142c040451903846062100c907064441c070780c0c101040303a0401424115103d6061440c00220015490100100660300041102c1260301c83c1c1d010111809481c4815140001c060298900145010b0006211403605c0142184150001c0c00000307104230130502e070729061112841e8a5842c44802460b48c0c400c40c1010013800e15014040800c0703180d107002550710b0740764500c600e01c9240c2c089101c0002030040c100182084a840160401d201040d05556120260203500200c0068010402d600040380065009181c980d100794402408181e0700025881000001e4103c020309a0b43c099040705e009965894090096019109000044c407080c071302981c1116040c4401066480702 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 491217050 1250 491215800 491215841
    0x60f05010e0105060a03020405040e0a12080112031b02030703061d03030c032d0702061603051510030f0e0a06061d0103060c110d0e09060303090a030f0c0b0a080604 72
    0x800365450710303803419540101d0b04a50341d030309081c10803400390085801480c1d002c1d00e08401ca08515000203020b03440c072031040c8292120040c51240903120480b00340301c1c2d08441100d01c0204130010b1b21903209807480c413005c4000e10440c04480c3e008a03140c403a481c0c1080f24040d544110544130740c0c000001d001401c0c010fa800440c914a440b41c4003502d0350101800c05039001310415011501e2581e07041b0b00c0b05ca810384200c2031030541e1908200080d602c90080e214200b0103000001c44544444c400d00402d8401c007900141c000582e01160180f100c00c810308082241010740d40d2340c03406894031850241201014044004111a911508104003118040d40c444230103e07012580a4582881e05e080c2e0340c0c11070350401d40c000f9030b403019024183c541d540c0b5000f4003201400b6000f07880b0f507101d8204c0300071008480d0560301c0141c1c40e981c890506940e4401c5e4204c0b982c0c001e80400f030802c0010700300510129054410105c48841075940d0700450f106030043e04150012902d000d080108608051141c06105502d48480c01311 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 491218300 1250 491217050 491217059
    0x4171e0d120e0307081809010f060512101e0806010905010e0a0507053609070c11030a0c0e190612031b02030304080c0306010b1305130902040612060f0501 68
    0x12501d44195260150307615450060302801c0107009650348140c015008541d603c1510b0300f0081c116403201c51192151000300000324a1524405d0b40c1c000f580c95a0715940d1070b2210401d003000300000300038050307034800446000101c1c100d03401002c41070f07101c00f5102c01c809926080005460800c2d05c141c10580c031151600c40108050196801c07403513001032030a2000102900c81e0102103520344540540241000320344000d00e020308d040703400d0312040c040a4003085403020701c01008100003180180c2305040000c0030705c115180800d030180c0ca010f445920060840e000044603999038021030300c2c240e100b160f080c20b10008115840c0e02e40100c00c05e0346103250004201d045c0c104400c0d207021002402c4c001d002c01490303140c400c0b02040d0360a101c14001ea001006c803500d4a40d60f8221742e9442c440400340c5070103030085000014600720b030002520f44c40400c102c0d523000902c0c181421b210201c4078100400314500e4a920900c009a2110311550b009000f00030580480c01009007022000d88446034003481c55645000010003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 491219550 1250 491218300 491218307
    0x102070b0a140a0e03060f09100c02030a033b160f0306021809042f1f120501030503031005031b0f04020409060f0302011b030f1404171e0d 61
    0x5000401082c0201e44807503030701600700e80f543c0303021480700c0d01441400103018544182c021114031400b404400c503421903295500304400d80390074a180802607481401410040d84c000d4211982e9400e0700d00007040e0b0500e0700c110f41181e6030100c0c1c403010490680030b012203501801c24032800072002040e030384040c40e00385890070b6030101482503c405410581e02140114011a0807002c404a81074020003c0510781000c1c1015a4500c42940c84c14140c1f5840283c00324041c60701e4440d8079401c0400410f0f407218101d1141d040c0c28104002580481000b1808030070b0b070300d035610920449002e9405900156100e00c1c005030800001a604e8105500c00e070b10400100c1d200e440011070b025038405c41071304c4000c1e0480c03019001c5000380c003c076081032002c1d5082c40e0b004651035024801e01d0048074001da0300c04002e6072220590a445c0445000050005080308061010245c000c45800c0500025540d40c586002d03514000710368105190740d840c00d01904205220190040f41d03603c8001a80b2111015001b2070042443c080c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 491220800 1250 491219550 491219567
    0x72019050c03150609040305040e0a0b01020c1813030207030f0b01090b0114220b07110f09061f050d2d060f05090603120f0403030809060618040c080f07050102070b0a 73
    0x1320303c03401c600000036003050701ca603090701c0040c10030f07a8070142c2509001682e4005480520000d50051043c1c403000000c914280ca604451514184800b0f0303010b440c0c400ca45120800840c40580c1984181c180001c0015401d80d4000505400340b9040500d55050281810a880c1201191410404484c658412b010b54080c11500042001c410046948281c4041d032039081c403440d0301c40d5507075410224504091149481e0315040c41e040456500f01039628200410000309000e80f480c0341c0000d0041c3c1d0000b150a0100d610049007540d504000e420000241d00fa281941c60b0b650180c2d080003002150346030b42059001d4400d0046400c0c1c18188181410010401d03072140083c420a80301d40d0100c2c010a04680307044c4500c1c50303044640c0c9641540d480100070807004c1c651061008600154050000a11006002c9191409054024851001c070b850180212055810162060361803a4059200166086081060114890803d8058040145050300190a01c101d5901449071403200300301d8030603038030f5001c00c41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 491222050 1250 491220800 491220811
    0x414010309121805030715031119180504050a020d05130506150a090c090810230403050c0d08090c060c070510050f0a090512010b0108072019050c0315 66
    0x49090f03122441040418036550303202603014040c044012403203c2e0740c040201e4040c519610140440303264402074036914403d40c14000ca405501c1408055120b1045101d00c0701344075244d07100c1c1a69034482c400a801c8030f00949054001c6603000482140c3c2071680e00841d40e010311031504103200311b4400e0f140c0d0f61300c4e40c0340140000102c480d1551100140c0e070303402d5510005882101410040c1c42c0c09000040d046000c180a6522203110300c038101c4203504840d000d00a141d0120705695074416080410003a42d20303078007600440500c4424892111025820000300700328002c01c1d55460344a051104901e03007008000070455019a404002c6d007900c500d400034150301110015a4642c201d0392030060200c500e401548901c2c0b40413200000d07a140d41a900084d00741c196a42140c08130204a0b2400030a406c81e0030840340180031495400000300064000c80102ca020441e01031100040d42103005040c3c00c180c03400344078030210150015000b05020003003102d0628910b0540041c0105600c1084c0d444040a0080c031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 491223300 1250 491222050 491222057
    0x906040504261b15100b040303030b0402160c060917060c0f071a1501030c0e010807110f01050f060a05010815040b0916031505010f03090620041401030912 68
    0x300b00d000c0214040071124038045801d10600d905a00800107a12503400300c8441080981c01d00c040780c000a242c80f415000c80d25050380f1980341914694041d800ba2145000e056401035007808400c006040c004440c030142c0340f003080b08008071410220b000e8182c804582018014080d00d0f40c0f852401100064038a400a00c40301e2600e0321204846528103182c8615007005044002c00c800d20031f5884614004140500102c608a202d80095200110100c601103041c3c00b00203031600352102d0300c1d540103890141d000100c900d4603100d580c00e0020014a003080b41c4c007c941c0960341d42c20400c220542c003c00c905411690856400c0c090311b107050002001941d014088010300210020f66000c166a558401440c0b0500500040300320f00e4030844880b080800b07407050344086030404a04c0c440310480d900115060b11016110149035074481c5000b00c1c010040303035408664480c0c0c1d880c0101c0c0e08500f0402d00c0104a10100e480300d680c1d038100001c1b90191078280c0d003114140b504040400e40094400c40e40090100010f02c3d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 491224550 1250 491223300 491223353
    0x2042309010f0b030c192103020709140a0b0d0c180605310f1b080a0b030d110a170a271703090405190605090103020a03170f0a0c020906040504 63
    0x142c010030112029070080004035420360807c25000e00000c140b041c00350080d020345107076980da001c031142a41c000c0812001e900456000051354040164802500031402610240c04a00b484c4c0c0c03031811300a030030f8100b000d205c46d000300d0781c0880d031200d030103100060078054520000444000034455086081401025900c82481040302503865803a8050398407038000070030501205e80d2035001c80501414030414000014900000101043c0c8c0341e0185c03503007107000640140f01c800056141110314603008a11070308207021301c40c05100416030200e8a2160030300501280f50b91452424000362030b01c41018903100902400d00f01201d203015500c1c0f000c0b400c8800180f040b07801c01004a8000b4154410301c0525503002c3d103481d050000b101100604400001c4c20000304105058032035040160070b0209200095100c10a0f0005100041c40c2c454440c59078201103149508000b00000000b400d900070240031000102e4030328000b400c0d8540260110f8002c02c00f900c00708114106a25486000490405032100204c1d400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 491225800 1250 491224550 491224579
    0x80a0503180304140906090411090c070212010b100c030f050702060f070c03021201090804090b1219020907030b0d12090b0409090506010b0f031302042309010f0b030c 73
    0x88070031061840c0e0709a95549032038409002c10070340090f040500401541001400754209070200c0d0740583d8110321800202206c0074100700711500024140c01d210241489200b0040e2a00302914619485603030002c90100101c00c1400700ea507001500c11000c000798054a00c2c003081d0403591300104040da41c42c0c8a5940d1205002040407803003182c1c90000ca4000c002091814403030601d1401003641c0c400c45868010451442d5030b542a9482503074090440380c0100310802206c81990301c40b100c1110003070a0102c40c0740c206100107050601c40319100e02e602070002c840008601d04560f505500018600f0101f00100c03640c404907079208001a00100368032401d60180c44054001d0321041c00070310a419102e079495496034814000342c180e140c2c0403501e9100e03441c004203c1a1380c6000b07540c044241000711701c0c156a68901e418004441c43c01d0b007a600140d69400f6249000c25804024203284104510f07800542000f1050a003110000d000d018030701450516103c3d11a50b0200d00c060320302c80120340820404d28038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 491227050 1250 491225800 491225821
    0x1e13061d0717160c0b0c1911030a05090409060509103804060305030301090c020f030f0f07060b0d0f0201020d031a0103090302100606090303180323030714010204050a050607080a0503 80
    0x100f5201030b00118814080180016041009003903e040d031f80310314401c00d9103016098400380000ca251000940050090300d20041c41000600360f2464001e001182032182500c0300c4044030015200d48090350051030ba80030340d6040601801d07200004e07200c481030032031641150610710400503c070048120750060380036440540c0c80c0d800072005182c001d404d480d62541c1d40c1440300018a007007501803015000300100101e1198001c010f03034504010410105142041c66410303915994000d080441d0481d50303900c003041c0507450f580720007100240704202800f332580f07090001a01d0043c0d4032000100b01400d101440300e4000510003420722241080c00d01040030908d0f0314059090090b04045200282e01d441c500180343c0e5403006403403003100d0103601c1d070903010340d070101c0103002074001808007602039000d10a10840d0b8614644140c0d00e4411014282c0342443c40550310701e6071a0101030034845440e074000c24248400d191504007100102001c9a0952500203540c2e101c0c00c2c0380c01580710345000d004000c0002000e0015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 491228300 1250 491227050 491227067
    0x4050d112401050a0602070b092806020c130b13020a032307031d0319090302031608060903040810020903151e01050904021e13061d071716 61
    0x42030507401c1900068003249001409110700d910841403608000380070390001c201202a2400400c040303180c21000d405004e1040407041c40c4003801880500940c044d0007194030798038082c1078181d0141540080c1c01d810420398414401d0100d03502c52070010381c100c0f180c0c0c424070034280b200d0380d0344005070f00c50559000a4005050782d4a1000300d5002070381c64010581d5144010300d204094a440402226811452090f6080420b24803400c40368010044443c980490528070079811146280c8009803a0726a804281444609000c2e4020603100c00003d00081c042440120750020042d03004500740352800005590312034014842d410401e90001c0e2132600c0f610240411030480c1d00c102c445207003604090310094070994891041201d01d4901000100741c030302d03004d1111401160018580015807070f402e541c6c05c0c04101031900c110b500506140c030804030b042d01fa004401c010074101072040c0f00d04074078046440811500134102ca00300200c018994020340815140705802c800e20744000503070004102c030290795600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 491229550 1250 491228300 491228323
    0xa060e040519110904141b030a0f0e1b03030a0509061602180a0c020c090402090a0b1003021b030708041a070f080306030c1f031e0e07030c0b0304050d11 67
    0x1414441d00b0f10b40e058402005042a02d0300b942c3c100140030518191840800c8295407201c40306592400f80524208040095a0404025000001e142607100c545c031044440d1007650030780ea5000310074100456501c044444c0a0600c09601a501d0800325450007481407280e9913507a031042030007041ca0041a411104c00c80c2d541a400751583c80034000d00c10700c60328160400c461020a0071b040440c181403140c0b011411484103200034104a0341d988555081003180b540041c2646e040300c6d5141e86030310700c580e114000011119030076280144d460003581d02640d00500040c06071001540204a80800211458119000c070740000c2c085042144680c0d1101b20f06108640020f4043e44050201c8014801900020750040b14124101d03003000a02c0401c4c00800a104d040700841d4104d802210420180641c010280740c03880207100b182641400a1681c04032482d0898407070007584400710078400c2000d410394110280002e00711050461034565251039032200c051100e601004043e081c0b401164404100d410482e4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 491230800 1250 491229550 491229601
    0x11701150201271b06090306090204090b04140d0212090f03160914010e0708040b1b070b010906050904050c011206030f0b040203070603021314030c0a060306080105060a060e0405 78
    0xc00c5412850701c0d1030f545040c103403040c0410b41541404801044051021a826610341040040c65902c41d48024030440b0300030703030308183c40700b6008d000985a150b0541c421071044000301c6100c0958100c0038a0a402ca020b03000c00d55001d03c40280b44038203100305540507180c044034803140300100b80020904101500d50180c400c41544c080c042254122030b04600c450442c0b409080110341e0303a924900c00c0c1040142c6a0740e000c10462004200455545d138043c0d40c3c0015409151004100e0040410201b540548015038408440400500c198a02da00858005180031a00102d09043c1929859114000c55218506010030480c164223200516007002000b0350700709072036591480040c2014159024100e408074400c0c00340000100e0503034002e10990b2080700d140126000c046040004451780c040007071514a80c588951070b5000c110740d441003d0744d0080d140d030b1b075004a54a883e0004803802d40c0c0e0080c018501c904495401880200e40c000803020300c4500840300030607192140c4900c0d0311a501c8041061040703 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 491232050 1250 491230800 491230841
    0x14031003120e040b0a0e0414030c100510060201050c04270c1d1e040209060f030903040602072420070b1201091107080a1206030c14011701150201 64
    0x1098021203038014550058400384100c1d00f0b581c00b000800f013a1030241355215446c500104020072065a10102851030480450b45844110403601d46000090700c91280301949890811080ba101c06e480b04c0010841e9000a0095003005105164680598081c10400703c4080d040c04000c0c1c0080509850381e601c1d05030013080303261080003009008208c83c0a0070081c07051924082050303410218042e250300e01d1a00c400007260042d030030401c80039500204400742c1c05502030241c1403200d29007400541c001e414117001160358a2a254010f800c0c0951035000c2e00146030344098002c2402c4601d403001c0c0c03880c0818603080003404c0b5410701c426529075045402c00e6040c8203c04000c03680c90001c800808007002c010740a4604ea82c0e84134400300503240840607030300740f160b401d00c41a0001800c89014150280b180e007065024003020f156114100c1d4550f07801580c00f00c1071060100045400c0e40a01082c01c90b080c07a01d80c03000d04900030512110340061091003810b01c850300c0040d00041c0f00313600a1351040300c0398030030383c07403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 491233300 1250 491232050 491232083
    0xb070f0615060903051c09050f0f041418010506010f03020721050a23180a1d0604142e0308031006090b070308011e080105160e0a0614031003 62
    0x80ca03403d500040341d00d0b1003900c81601609014618a903000c5016507075130800b4130705040510450020320f04070150030040c00d1040d01400c0d0317213030b014420500b414144032113001d1500d030390010040c4c540c4090071304071030345014140a0305990040012070022054100580e0307c44940c035001c4c0300c01c592000c032501c000b604070b44503400b01075100008004020042d40d441076006070005040c41c428011089040d100203080012070641d9030300000b00d03440c2403030042040c070340035545404030a90381820070217a41d4800f031607078200502490644107000a20b10140301402ca246005010200e0400c0401c00b2502031160070070108003a1410002d0710000b03140d004820f95181c0c10315103013a1203000c40c00d024220119100c07038030114250090074292498640c040d690851f20741d1a18030008a15982c460381c004484001c6500840d503034409000d050300030b861602c4440902c0e000e00c0c10052413861880104c03486404114000c1100550100d122640300f000740b44400d0340c0f901c031000c0055150b481588001d060344903001100d03c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 491234550 1250 491233300 491233307
    0xf0f150905161703090d0c05060c01020d060603090308060f2d09010e0c0307080901110703020309010305010e0c0f090303091008010305060906071409010c06060f0302190b070f061506 80
    0x3502e0018100103030080d0740d200c918584500b881c03603241c842203034020701c26030074689011400c00940ca80900c6c040712546481ea00400c0c250b907c114080b00c0503a40014200956040030710a0302c00604052030100107442c00350303400a0100f400580345900c80d007d00e000901c010b0752403070f1140191203c40014503022020f001103c40c580c2140c0d0210381d10480c1403c2c0006991101400aa403291080d041e002c1d295507107688058500035409410000d0566032401c00805407200303500141440c0740207400441e142d420040c00102900d10582142e044102c0325800d008500bc1104255aa0881d14003503032502d40d0b20f03150200b861070041b11030941c1d200003130300e0343c4084070b6800a80c454183d0b401041594500c1d17840206469a5017420307640f660000e201e070310300700300030203040d070040e1a1000c414904802140d00503194502595501e0700300c2c0b5070000844800b041107203040c02c0c1c5191019008060300c05554601035688203a030103a5074002d0401103403c1e0b110300c10040e45500c080c04c0543c00211440c02c807501c0302c0004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 491235800 1250 491234550 491234563
    0xa061211131d04050a140a02091e16020c01121104031b090b0612190609020a09090902090a0c0909090507061101021911100501150215040f0f150905 65
    0x140588100842ca5044051a28000344a540c0001c02441c04549541d91194011001d024003d03071409401c1500c00141d0b251905140114030030b02ca100d0054125440120620501800c00098102009a038010454002c501c61104c0e8100f420601080507404000e000503101541112030b0b46400006c01200704840c490031001411540d0075140d00440d140c110340741c03c448a418489130f04c8081409400758160603003e100b6030210700311440d10640007a002c030f03403800d8403001d41044a01c0c58000c5074000c0e070198013800401c0100700da69008c0c4070761801783e004030303250780c1c809000002c4050b100c44900046a0151883e0341c0100310f004000c10075a49941070030781d10342500b40203810000b00180f0410705041814000d07986503441c0340408902c8140901c9042d9040e64240880d00c1441c010807000391f80f04419482110b0080550740c1e1440010f950000000341000c00c0300d180070b41481e20004c142310205500908270580164050f50030600d201d02070525042c6192800c0e1609140360401c4450b03400c011000c01e14 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 491237050 1250 491235800 491235809
    0xa022a010b011409060a0927150513020c1c0306030606050a0b0d0b01033c1407030504080409110a0e040c0219020d0606030b1605090a06121113 63
    0x2000180150401115003005040c51500d004600340104503a5150290081411b01118203100c020242c0d50a003903681c11009018030041200849082040c100c3c1d540208030710822001c1801ca5410300f00000160070182d0380080e4000690f02007130f504d0200104210006000440f0090320b01542c209080041c0509402d000c100d480508040c40001c55082004c940c2c420b4071207083c0941c0c10f101403a444580141011601e4604041d16882a50081d42542c0140c4070200701120442000d103c0d017000c40d5404a00c1c02818180c05480d04a2280c1c1001005079101c8e00111103203030100f842e45542c148110f0a001c2e54120548042ca0603500070008422640202404041c503191990f5440207a1b0411044a103192900400342c0c1128442c420b01001e01034a031080544002c1044407061885c1c1c40741005c0361426003049504801000c01c0c46050503040e04130700090340e25460000e18100c01500440c403840064440c000601032407401f0115680750031740080d070b001051403800c030b501c400c0e0000c0700f00c019076501d01c02c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 491238300 1250 491237050 491237053
    0x908040f090b030a1109040215031627050127090c020c0a050f0120060f04051b030d05070f0b090304090c0908071e150e04062c0a022a 59
    0x2d102034100482c404190640182d494450030142c903080c00217155000300100c0e48000c010905001507071340c003000780d1302410344008004c0f0210131090024011140100c1c1d10300810422481c1508003113180801541600c0003880d090644c010491203450318a602c0c0c1900d410701c170803910004540b007003450340200d40304561079086401d016a80e100303000e80340c00d181c058550488841c08180d81c0e10b5009441030090000b0500039064103906050025040c01c1041ea0082410044102840144101005444203440c9080403080000520000080d914021866881c043c01408079014060210f030b5200c10940d1500300814407210b14240b50200e03142e070b00500807540034070329080105403580d1054041000f41c503500402450043c1c02c00222040c403003158105803883d90702c05000801c80e00e00703222030742e121a085030f194115a410700d581080103a40300b50700310210a081c0441c1c684805801d030b01040c1101d4000c486415100c1d2a0410b01c80c0107480b4840602c1e651805880d540002481e80c101d0700c01c0c01050110 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 491239550 1250 491238300 491238311
    0x60501050f0a09020c031e070c0e0903030106120e0610080616020304090906110f030f130525050409030509040e03031003060b04021908090c0f150d0908040f09 70
    0x50400021804996950360003014480b420300102c907403a80100840b1001c44201c03030a1031a4040c3c042e5119581c541c13044010000802c0700000c110a4604030f00141010b500c80b0070880c60700400407680ca000503c03405003045102d80c000180301c03071aa40910342d110b4848046d60910724000030100f583e02000c2c0700703064983c030850001644458010091500301090351b80550b1520f4a032650300000b801c034040c02510003d580354001d030a94201200200096007141e1380741504d82c541303000c401c005094000c203441c070940f15001ca160300043e400701e619503130407640f41c600081001c0000780c02808410700c0c0d002140c009140621982c107154000d00941050001140d05004000040e0500e50f07c07030105036500d03042d16209210610020b659504070314984000a40014200650f0300c52144c90035110402ca4000b00f03607444140400c40900307004401c5100f2003901c00324511741085011030490600315081c09008400402c0d542e5090280d500072039090f41d002014103880d66103030090a4003000c0903203e1a0350040c50321 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 491240800 1250 491239550 491239559
    0xa08010c0905010516170c150a060902160b04031e09050306060a050d3f02010b09010f05040b04060513150e010311060a022109040e15011703070602030c0304060501 72
    0x690495000c00d140300d80d1042c5000b000e60f12010ba646004a41103c6c040e020b0000c058040420040104990300c000b0f40740340c82c1d081c9070000c407048034541d4000d40812401041200411803800c1742204483e0350014074000f00c1d603110f00f001c54031100c2c010044503410340c48240440040d0380c0f14104e0340c1a076100310103031501ca4444400b00081d44250780301d940c1c1c200f00404042008103030041c1303104842e60344c2c101c4400c040c0740000d00400502c0c407640b902c41c00d2130414040d81ca4656039091007001145902500e10714581e50600c04a0f420000070303032088910903a21658001c40d2a119a0440802010090202c101c0382c50751041c05030140500592031582211007080c00a08110702c5514541240d402501404c05040b6130001d20469600541c04807040d032003003688003000d456000c401841416000e000342d0340c49642c00e800300300c20349030150030703121aa501000301c188410410040071411162000e10244149090328507090960040038000390680b440402000001802072004601c580d20584041003240e072103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 491242050 1250 491240800 491240807
    0x1507030b01172703030907060f031a0906030a0501060e071e050a0f05070209070f08010801060e1501020703050d030212010b0340060e01050a0b0d030c0305090a08010c090501 76
    0x7082c082281c184500c040350b440b21180302c115104098400700c00402160301501c05245034400e442e040d446030311030242000038075803003018008101c003d807401380900c0e00030011102c040c001041946c3d105040d4600842c001d41d60400c480402d06074008002e004581e540e2031000542a000c07100200420300c84010f10500d841203042e2401c1628080c0c441034148203011004031026014003d4920038000b08000c1ca00160b501c01e500c65120b03000540d2400c10126100a0043c06100d06a1100400d41e04114003407048480e07444085601c124840c0d200000c4100c1c080c0107e251003146d52010b400b6010b030070071700c95140380d05800908124800d48031b100c0c9240d81c3d0f682842e101e80701c00c03100c103000062002426a8032099a2075241000e0100c440d401800304510b285a03908042c988004550090f82c1d400e000c607400c402070040ca9841103403900200301c15142038002c110301503040b400c001d0801154400c2c3c8410180290107030390742c0b003101802207240a0b4460b602c190080c00c010500310b01044101000107002c0d1320 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 491243300 1250 491242050 491242067
    0x1501021c05121303080a18080712030f150e060414100602190309090509010605030123100608130602040f14090f0c0f070c030b13020a140105190509031507030b01 71
    0x1850b58031070b140c5d81e03640304107140101200c2e09800c4004003215003103808240b0344400b41103a140282d03035542d07142c1d8078204040d00300e55100c00220317800d80c24103040000144100c2100800c40f03000c464a4092a03880c280000c0041c140c07136107598021006281400401710450500c0403d45406400f1900c0034442413000c0300e070400b882000100001c011080602810029801058001180702d001040382d40d150320009003903602c0c07004040354800078551903001c0e0300b000d558450342205407106a2000d503410042e004001c2a0020080f1450380e50311f4216000f000040e0307040b2402000200300d68041641c480340303200000c2400080071807048603603c010031007070100c00e85030340d0143e03042c104200d24000a8a1500e8a982c06c1202d00361a4801c8624000000c02c0c0100c07100b91040800c0b010802c01203809104022880b6840c0d0001d1005503a4150503950b541d07080000c4402200c0d0f000501c183c040416501219103206031090103415024078040c120422942210007800b8100ca0b85051005082031401182c5414 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 491244550 1250 491243300 491243303
    0x9171201150309050d0e041802030307020d0203031e0316081315061a040801060b03090a020409020f060a1107122f0d0804030c120b1501021c051213 65
    0x1025001005421039218440c01125010b06011403011800d880d003e0403e030300d03176040402181c07010310001300f5890607106052104101085800000c42240c000c40e80d81d0040301c0c0c1c000c1c040c0500400280039940d040007a80c41400e1106180c24450061000e059000d81040d1208001e030103400c0407402e8558020350009208904075030f0000c224500c1512100100481c2e400100019541c0754004a0690400b100c14090600e0100005a49920305101d50742115500d1b80030b000501c00900601100502c0420700a502580441740030443d4082030002400300c00d00c5030111680003400040ac400c451f60040202800d42d150001076503c0345a9488941e6400545207400904081c80101d820405840d8106a00070111a4440c1c4400028030031002c40d19040c1c1c100b5007958200c034085401c0007008030a00100300a040040c80464080400340d58024030b0f100702601d41c064a0110b00c0550115900c00c11200c821038070008014031185c58403240c007500c82c3d800042142e03100445040066119050b0f03504508525 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 491245800 1250 491244550 491244577
    0x30d0309050a020d0201030f11030103110d0b1311060a1d01021c050d06080a1b0b07030e312703020d1d03011104081b090c0a05070b0405010917 63
    0x1145503003003105900b44ea02c4220b0602d641d41e01c80c4803401080d03105000d404c44055079100c0d075a5045081a502c04841c031800c040c49240d400d0106070006042203603580e04080413828050480400381781c007880c1e180c40c80c1002e036000403000c40c200c03c8940d48050030b251161047c0009148403081d58004a89401001c01c2034541203c949820040403480358004003245909041e001580350b481d00011030030610248810380d2021400200340041421100d10303480148082d132451440c10b20281e8014054581c1c3e4400c80f4031446c2e002c4500b17503180054513043c0011441c20f003000d80e4281c207507201030001050303161050301500550108003104c000d02060740000c025016001404803a00c2030b101150041108102c48081152080d007810864a0902400541804281c0e246495608040c00c880c40e02410003014412040e4a403000450790300c1d0100700d03175000101c03c0c0b02613030f5840108000782d44a1141c540b00600d02c0c1c0307480040109004043d030014842c280711308401035010341a0009440d0328010401d0000d501c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 491247050 1250 491245800 491245813
    0x1032316020712080417031c180b04060e0f010b06030406020307090b0301080106062a031101150b0c0607050339030702060703060815010506070c0f080309030d030905 73
    0x3200c0e118a40c160400c14074030403500c580b6201c40c0f19035850f558445040381c2d491000f107801e2000840121001807607001010045043c00307001c19491600100d03c1159101a65480030842144e01000d0581c00e1f40c03607000301c1c03144103a082501e407400082055000030381e158011200d100d60b5412060003140c0b10110300901e0309045842c4d90f00c40500950000d024101844812600058040c018001841c020060200001582032820380090450420b60080c1d090b0082c40101d820032021f40800000d40c0b182e01850280c04c0c1140e030071410381c014125030001e00c40600c001c00c00000c0c0d0810210003800e83c0903007201950712503102d42c0f500340d0312070105541056952107480d2460344e40780c0358000c6580700808480007040814681d062a501198416101400183c011404014210380c250203020300a0100c2c20003440c0900028221034803091041c0103c900c911000240d0b60300340040448910f0281070b801d401704001c01e640303100441da00c1d4020040710380240224107140204500a00c18220000e400c240034144 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 491248300 1250 491247050 491247061
    0x10c0504030b060f03010212010803070303060501080702030d0e032b060501020604020a090f060b07030e03150105010c03050c030d060806040c051c02040e100608010903080a200304082502010323 85
    0x2058400d084e40705401d907500740302e0008840341e41070f4454028a11607020b103a4031070072400e0003403d994407074001905010302c220a01104507800401c50300c1c0b695540d5030024820680c080300e10b045201d6181e074001204200c10040f40081409000b1114000f03e408003088455903440040e619217108a40c042c2d84004c07507102c03c0104001540004a0300110420001040c81d1030b0701d0215500d420618090b40052110b0310703100194142003145e102c1d055001e810700c003250b42c54800020004000980c0040c00c0040c00305000808001c10419104000a000c400780669034440b5021542e5000c100c50980c1e80c0c03224010000383c42c0c01e204040c41c4200c90780400303449d501440d03602804054281c41c803100a49100714030140b0701420071071082e43c024042910005c0752020b844c0c14020807a140151014034401d2402d80034410142c5174030344c080e00c1c2c0000b00940588030303031301c40c10055418040d07070b1915101d012011072400d28000c2d6007001d890b502e41c401d80702000803c9184040c406a250112010100005650f02148 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 491249550 1250 491248300 491248309
    0x306030c0316061e1b0f120c02040f0504111003060312110d030605150f070218070e0303091f0210050906010927021509130204090c1107062d09050102010c0504030b06 73
    0x8907029140c0118508201d9847c0800036122072084000a0b82c100ca00a0440c9040c5c007441c05ea814207214180300506041d281c0360300f00030120540c14424903002104044030b41c0a5042900103540003031901540443c080c10281006d000c0a03101d0100d4011400c2030350350307140a8441c404c10b0f0385028000d0302c00c01001c0c110240d0281e0141c00408040a014004000169611804ca007100350700c0d5075821603d4207044001a000310401900c0301e220b40c200307000442541d191103075954005090705074001c5600101031002d03414070a080e0440b0a00300d0030402048102540090514102c0305046000c20894985003d4020607603000d508800d24619900e040e9005843c0003048815408100401d0b1031a04100400140c0e6000300b1301c02080d1070640109042002c52050b100301500400305080109440341424240c98403039009001728003c0c40301c101040440800014009171240d881c01703404000f5810b9004026028009510980d4019800d02c8103406009100e402940c04503030740002c49028170740b01c007010031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 491250800 1250 491249550 491249597
    0x3070807110109050109020f0a060c06020304140d08010303021204080619110711030c0f0604060f17010e0f0937020603040b1b0708030c0306030c0316061e 68
    0x1080044603104240000001c0c0b240a00f001e2144c000000c10300d0452050000519032a10601e10820001004104c03054000c100010b040340e0101c0c3c0140c1d01c0d600c61505008500f501c0558016610845444407541c03608002028144c0780650211461400c0f0b03038160206600c81c5004080702c507003002d801305807031200d08000b40802030380d03500002c6400c0040c480703004520380004000b0789001c4040c0d0b0301e285150a051152654041041d5000001d208101000c10318500c900d20942c0d08020380352880281c8144190b044a001d50322102c1c224005503991b0385110750400c801d850f206048288034011601d850f2000502d40c910b200c04080300400d054207040e00e0981c060203c020981610304288010005035245001544198440e01441003d4246440742c00f410381a40750420081c0c09040122402080d02d42c02540d0f4803049a0040941d280d445c4000700c0d00381020300141e16054481c0700340705400c00c040d15190909460b240c0d0703a54281c001181da24215062680c11204020621003002e10038000000c0816 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 491252050 1250 491250800 491250811
    0x7030e1009030203120409050f040515040809090a092108180a0503031006120b0f3c18060f240a05040302120a021003021e07050c0a080a08030708 64
    0x2407407801e65903004642000f4040c059041d410f40d00240c14030100420344900c03034008180d0810000380d442c0aa0b103481d9035520302400b40c08000f0352440050204001c40044a090b103c01525000c0142412072880000e8919031b44111110b40340c1c122140c00c0048011203e42c06840103565044480d200c10000c1d520030741c05110042003d000e040d9000c40441c04c108004d40c054100001c905012074901400186076985012446800c4d50a00600300c0c581c1d9521441e07051560740c1120041c010100b4840c1e518140301c9250840003113030340b402c11006c850b5000d110100d29680070540d500111041d164104050301d19044580300d90100e28168000114101030080411264a010b010b0000100d2044407041e5500b0203407603031340091000a428821410401291031003268090000d1841e004030b03500088103182460021400c0550124880d07034080b50541414003012204003102e55203030007905141d1385800304500b0083c0160f5852800003010305002030039010f01a0040f02250454540440843e1006805801d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 491253300 1250 491252050 491252057
    0x60c0b0a1416050f0c0609010612050a03080a09020d0506063c06071523011d15060703020703060b06090102030d0507020c180403080a0c0905061303170c06060607030e10 74
    0xc1410300401078130003003900042c070400030242441c00800e11405d441f13030740e041448004484160140022800505215039503414144010103a9a504030480201612840a540180140c3e0308505010780810454085c1340c003034941c02410560842003d046412406e42c403c1c40c2d003110300c424803c003258280c015440c0b9038001e201d5854002e65445090b500e41906401c0180d507555580342003511074048031044c04001540c04041419032415240310035100341c05c000c50841445910004400c3d40c0700c40000b441844005003056164175070b0781070007940e6000c1c0b0300080343c0765072801403145104e281120603160b212005900540c03505a401c00440d0281c400a0b090303d041d8814031003455095940c0b4510070076040314000c0e510640e841c1504008110324000350109070914600180302c00c2459210300d018050350341c19a0364030b607100005505240312240e5903001900808005d460051240b41c00401085113035500d0b000c607060703511b84900300f051902c18101d0007808102903103242403d50a000b18040030b029001c3c02e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 491254550 1250 491253300 491253307
    0x1512010f0f17010f02040e0106080a0b060d0e070308040603140105030f060714070209010303080f07080106090632030403021002040e060906031e0f100e031b1006060c0b0a141605 78
    0x49a0005c2e41c10039000305810b24032103001801801d51000308a40e1025000703800b80130940b840b002144451046c20150b14035240c846d0b990604030304c010401c84004603802404a1703a5581c0e41c8000034010b16130854030103c50400c0d04000034035443d0004204c1c8603104410042c10300ea07100c4400684004048101285800724240300c21005641c40603612030085000752a010001e01d000002e40c03495180007091b8a040c0040d050040c05490b50016010040d144141013003000b40303205203202c003803d840410201c5407030400406000780c070700702000145014512a03001c03903040f07170298544007007a80101d0091040c1c4020603070004002c3c1c5020084681c01140190a46403074401280c1d00c4560341c0038040c0c04140d1540010f4084892200410556500c0700755854100709070403484d26483c0d1030340f003095046c4001c18084911550348040074046011515060002004a16902c60025119446940d8180c0d1854458000150341c00014001c09000c01c282c08814102c0c0c3c0d50300340f1105a503ea1109410040250a0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 491255800 1250 491254550 491254571
    0x22b0e010203070c0b0a12060b040603050c0309060a051506310810110f0c01150b0f0d0c03020c06190c030218010c0503130b0903010b040603151a1512010f0f1701 71
    0x501c640d08c060030915019560792420450060309440019044540365001001042006280800d4ad25080100b800020483d622440d40d034009079000d610080d94804800104d05200c254a00005031b442000da1545008245115614500044541c4070750030035a0132502540c0040300c1c40341e00a09074507900810315800c003040d8034000225074006684c804c1440e0b640718140304483c1204c1502e14010010403902524211660dc81802280205a102800c0d6074503002e03031950035402030301514204030703003542101c5440c9001c50b1307025000000c54020b000480d01e08412a100c3c6442070003202c41268170802c041c0810011a0011509214000700035205400180010010501000076010080240d07400c02d03a2501003810405084038500814207129034540001003000a103803070101000d240b91004005508101c01c040354a0b050420181d846e230010034400c1c42c68245400c83e018103008600300c0400c1c0203903a282e81d00b408082e170903409065040e06060a00b000003084001050400e1052500081070b4000c88 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 491257050 1250 491255800 491255837
    0x27100f030311010b0406121704150207150203070f03050715020a1d04050717130204050708070215012702190905090f0606030a0507022b0e010203070c0b0a 68
    0x1500114005251003042e281c840307009000f4580041411138041203081d05d0031004501e2010400c100404440d0018001c47c120001c0c542076400400000c0c1074045103c5850301c000b51100d4150182550f51001085804242403001058550031036000c50901641c50840d282668150050701e0304035031002d03c503071085016102a00285c010400c4903129003591240001560034079004840845010358501b50400111580c4900c6021007140420841c681a0720383c0510300d11921400c410103900b02d0704101c140300c440d6034003410041c42040c0f55420ba80e80c01c8a010106002e0601c2071280b030914548c002c5070340f2001c1040c0d05840001c0030705000010315010700c204417062402d40445500020030380d00d14080100f81000c02c46241c0c0800a081c001c040f500d88140081c4260101402c40080300c0e60f10400514000d008110021007242c81d2030300501e07907803188090360443c404030300c1e851b80c00504081740d0031150754000015141056400348442540078200f49145900ba0403000c0c10306c080080394129503102c07081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 491258300 1250 491257050 491257079
    0x50a061a031c020f060907050409050a06020703020a060b10090b030a0204050315040c061b120c0209100311010e010e0607050a140d08070908210f04140f2710 69
    0x2615a480844441c06006401e01034913108468090700000b040104400011818000769442160001080382c0c50f410314031320f00300040000400c660301c002680d009058000880110317091080f20144a5056400f0078818081d00654050b404034980c0315040c4903054241001c3c40e400a880e030401810150b4443c00240b0340003030704000100100040e404c0c4014060070184900c0a8002410035400a00709861101d207030656001025040030b621400751110140b0039032002da0344540041c101c40c0d10b402c10141264a071701443c4800c60780d01140201da251154000c4d0041181440140c4030304801840315001e01c1a80da2048508540a0140110b0301000814000707100b001c03810a0780003450750b8041c8032005001d120307000d400310081c0f180f030000c104000c14001600390900c00d0091825408201031060214480c001c03110300400115000c50080303240c402d04404003030444000c603215108404060240101709150740b00d01410083c291101c034400d0007440c248250000e0350041558061542d0711642c10f0341e00c5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 491259550 1250 491258300 491258323
    0x200a05032113260a02011d190605031005010305060604051302040e04030c03021009020a0314010b040608030a14131e1d1e060901090e0109081603090909050a061a03 72
    0x10030140c0f522a01d80d0710f440540140340b0b210001c0070780d0030715500080e105003c03410000440c50a40b0070050f0854450028901c0190f8103d1414200c2544442000e060394201302e42c11684250154000110fa600c00d000d15030050303002510f11450a410482405a1603605100c0d007105a17400f00300c000303144400c02d40414820b03406540d5540d1144418a002030a0503202585224081d060410030f4002d1303924608184102e90b07118546141542c4104020350150112880b106e82c0549800740001703483c44007200804c4480c13007596030001d140601c10035600d150702941811010810a04006000d0720302500032070707041c0c0c4d08081801003840341e913008886240004100d83e11400c0f808601400752200c030742d011003601030089840c1c1040318a4484c01140c01c6c0300c4c4c148111380200d43c031080542d9000c2c00a42c80620080c0c1c01000180d59400c500040a22000a81d002140000c2190f540040d80c12000d2160314060741e0b00002030024956140c5407000600040c01c140002103002142c406400d0b5000c1061400b0381 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 491260800 1250 491259550 491259569
    0x60f1203030c0a0813050d031a09090c0a0b040f05040b031203070302091512071b08030c0714070303021504060b041a010323130f02030307200a05032113 67
    0x20443c2110080000e9000703803400310300722502950b81c000a000031840350100c0c611840d0018604500da038121000082460386150009130700070070f00403180000300382c02d0140740082e211010400d0b03851035103070040e1065100f08a44241050014403603450b280d0000e5900c17810007801c840c00720102920410443d4019030b20078010076400904030301e19050502c89903007241060354440d400c201000302943c0d0f000c01c00074400f004000482824907550386020310032071368640d00005015141c1c5001d28540069911211080c1c0303000c0c0d46144a01120703840000e080c001e0720784c160301030f00055070455002c42c4400b2001c0c0c02104d03082d403180e140818503126440f440c0b00d50450003c1c0c406d05680403c0000d41140c0d00400744480360703106098030220f40304a0140240d00070740c108a40311038601081c249034019000000d0020b625000004403182800b0079041803031411200e101004021b8a040e50800c184500740380b18640d0590411000400c00340c0450b035003404000411040507240c1124010740342d541941603007004600 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 491262050 1250 491260800 491260807
    0xa0506070302190915111e030c0606120a330b0f03010b180c16050607080c0a09030318051002010f0b12070b0309030f030f042603060f1203030c 63
    0x1120b0b0340c180190001c3d425810094059402c044441d940303810f207440d800080c008900000f61801104204000d1b61900c0b00840f03a01025404202c26140d038042c148058641c811000403c1084c81c0c1000220281071144005054890569583c0072351000c00070700c5034004d015800c0c1308000c1c031602c06843d0a01038040c800c0008181ca845000c1182c2041c040c12014026858180c00c1920390312401c1c58031490345192902c5c5129999141145c202c1071086c00800d000301c01d038002c1d100c4100600060014011140f40c2c6942c0244d135200080c5a1481c0070301d4240b0700c00200d0b5600c0c00c201186c042c0311b0480030310b2004800460602d4542001c01e6110311540c2c01c020040c0c2d51002c7e8030410411503c40c0103041c607070482e42282e4140d1f4907c01240e07210001c2c003030410301070800004500b03040010000c45081800f507102e03480c1c683c41c0c040302840c8064011202911070100704074010300c501c00e22141c0040303a440b0211400e030031030700c1e5441030260440303502c0309450300700324240720881c0020300c02c10140d0b00c15400081015034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 491263300 1250 491262050 491262067
    0x308040506090d141606020d15090209030c060a23030a0e070b1b03040e0411010f05070f140c1e120f12030c07080d060e13020108010e0601020a0506070302 68
    0xe0004001c00c0d80c0e00319008881410b18681d848000403412106065900d80c0701c0301740c0c400300c80611450440c010030356440011028a1f561035070700240e615030480c0842041b1130303903180c200c4416442a04c1403554540c002c1107882a051501c040030349014082d61078101c0c0d142c41042204581c40c0007104947c8170021001c420050b40f240e1501999414004180142015603d41450384450340148000d041420b03d1138040641c0341c8070104182d50042a900300080701c0ba08090400c100c50000c45500c1c14001561441401c0c21140900111140031b03520070280282c0d403c4544032200b41c2c0c55900401007450142e20200c0e25240c4d506002000c201d50b025491401880881c82003200f030b841442150081500110442d030560440851004c054004194615549958141d61015544242c0000500c4041e020445550540da0743e44900c050380c0360642d907920300740c1700c003036035003d040741c010100a0006d1500b00051000b00c051000a542002040c0100c5031a00e846559050a0510441e62400000e41c0402e0f1500d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 491264550 1250 491263300 491263303
    0x3140405120f1605060316020f0a11030601050a0b0702090601110102070c0801050106111b040b0a060201050a0f0e0c0d02040f060611070f0b040e070c05010e0307060b040608330403080405 82
    0x14460f510b992400102520b480d010803114080244800d500401180700e0300c1a050081c0400c0c40440614425140e9405003840c01290361080b82c51038601904c2000008500c40c14031012401c20303129003d414504001a82d420024035080c0200404e0401c0201c4c85440c1800c038003400a0041c15110f2906200b54074203045040d402c40708140d208004000b03900003403c0c0c014202050740306c480001381441940c0030680d000810042c0c0047d1007110307000305541e60700041c007690652000d4041c1e0061003081c13001c502042410310a481d402c00340760308590011020b80303600d0f1030a0000c1000491000c2c1c00800c820b03a0303059072078040b81e04551103140491a00360940320103180902551005c3d11036000701e07001841c1811000c00d118080c1e806401461166900850003443c000e1060342c1c03e0591000c02030026a0b00401031300d4494104840450f034241c10982c003034400c0c1c506800703180240d031000703001021b4542c800071140d100c01190300301e07240b0304142e0b000700b2121142000391260702c100d0280c1c8550410f41854030380355 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 491265800 1250 491264550 491264563
    0x2011104230405130b100e011503050f04020102030a050918090105040201260610020a0609050f0f1f02160501090507150206090c0906010207092c0303010e0403140405120f 75
    0x18490b6140000300f1800b850302c0c0c1441001250001c10445413580d030101c9064004506400c61640c0010200000618541c0107503e40300e54078256600b40311303d4403aa85401c880ea401681c00a0141e00207124041405100c0c0740a07160043d40206015045102e000400e06007a83c103640642e81d59441c0c1040005558100b40e03403d24040e0900e2010408180c1e950101c80e81e2540508400d100e0b00050ba1207080c554401c02c14140c443d074200c2c408012011682c40c1c40b56443c01039010740b14a134064010045852800072411904412a901c60585407901802180307009500c000201200090104d0001d80450024881c40b80101e22038801040150b0904078036190410010044108540c008010061100c00c0805c29880e222070980b944400c50b181c19006038108800d98001240282c94480c1b107140c209048050000203140000034207031034540d07100e059526840240584892200c4920215001a00c030b40058140c44c0407060706a820540c47c0c03000100c072290804c428500030750240090aa01d2003050001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 491267050 1250 491265800 491265869
    0xd0908060712020a0e0627060903030f0d1d0303040614160c060f02160b01080a2006090d03050a0315080c010c14070321091208070302011104 62
    0x14840d916165100a0200000300b0003050041d8000c16210409405a40701036044400248a02d8a86000c0c0f403003820a880c000b0058401201550300e00802802c080e01110b00e00c11024007d0b614040c2e0030034140390158444200b45024a99911912a0414000720040414410070020f19941c2c1000d00708071068900c00c10842d092202c0000c2401500c40c003900440510049078101005914001e0502c2c0d80140300c240c1900c0c89450000503400003020380444da01007600d01c58502c01c01d099883d080c00c256541c0345440004c12807400011451602e43d959050300b5080c010042485103042204ca010401200021400702c0c081080401c200f03070b080b5094040c803000e4001d200c6044000a1030314026503510000c2043c40350500800361002c0003030000645000c0c071840c280c0c2040780c01d0180d581c94900102d19210754101c000d002552440d004d8107204440060484a9105c0c60a005d00000c1e20340815a5101e42d400701c0566581c1e8107190a1118180040c000a150301d041c00d2902c003044440a20207043e10000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 491268300 1250 491267050 491267053
    0x60c03190203070903020103360213020c060f09030408030403240b09070e0a03080315090a0b010915020f060f090106080304152003040902091f0e04021305120d0908 72
    0x100100e05600290303200490f034091030080b611a9100001911b001c0f581c4101d004440c01c89c032081c0102c15580c075054920300e4403e13145002c03000d031614200b004138000c0c049446181d410440201d1040b03a0144241900100301206070707444d191752000340380d29580c8a544125920904a8a007411101480070038848000b585001480280e640c90005001800018565818007a2041d0b004d44685c5920b1a510091a403081e0703044d40d40d080c03101800b42d1301c60111460b188580d00c0c031b10010f407069045006044441d08180c483c56030705400c0441c0c824160540800000c00c520410720024140141040400d0080141e000b94501500306800c1e0542503540c650424409540304200c10040d99494004c12800040140f903d421910110070101c0c040043c4031070b900310680301c00700c1c012841c460b2560040264600854080104c204041c94080000007441d6424012500460042586080a40080c121048948441c0620035202c41c0082c0382410000ca2051441e44031000e001542a0086c40754400741c1036540 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 491269550 1250 491268300 491268307
    0x20312160e10021f0213030f170f16030c1203060f080703030e0f030f0d0201060603140601020c0405090f0f060a11040e070c02061912060609141908060c031902 70
    0x2480a59100d074000783c1009910080c5a40e40030a0440340d042d01c1d000c906c50081c0d688101ea03a410b00d1081300504400a485c1406054003901402c00f900703007100c2040441d8000c180c1407000005410f0031580c2a010241e051060034070050000030310f0a900389220000580300090450700700690340c040302c12141c220035915401098180042500816035148190044660420f025002c0d800320741401030550231440144101d2104000d25034041d0030503402d40d49165010441011a0801c0c4001003034150b8005000d0b820403840b141081c206900f200c2e0303008400d082166020100c3c0d44d5280c3c030301402e004400b85c140d04a0400c0c000044810301400b00040902e10070f40e41460f08018540080038005006103091100c0d0785040300c119100c40d03066520441c24100117101c420a802c03070252025960000800321103103070000200d0100e029540c00000e8480f0680140c1c0325200308820301030460700f100391801e0012400000086d0b00001003007014425070314000302c5a20b80c02c2c180082000820195404034a450060 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 491270800 1250 491269550 491269579
    0x40b221a01090905180d021e0a0308010b0a18080d080f06030c01050d0e01050a0605040b0a030528050d051201080f030307081e0405010b100504050a03020f01020312160e 74
    0x6042c01d540c9030f102d0008458a404000100321009007151981d03c0c0103002c0618031254020441d20503000c611030303847d18a4070308103200c5a11184070420040c003051110005028510319078000d480f540055041510090700c45071400404070925030300c0a80d041d03000c1c01c2c3c03600aa0750302c00146500541860610101420001d0011f0b80301c0101e10125810400041140e6000708a141c006540d502d51501c004c2146003040c41c1c94101805544c014a03004600380f00740c006090034115240021290401e0141020b0042c0030200c0074002010941540007400003c848000b0132006e11501050741c080303032030301d80d030f1030922400e003c15980c0c0c160b00c0418039800c00300c0003076070049010040341e1380081603240400c800d0b520f01100a440043710280301d0034840c00d00d42040b0070450150b00c0001c5901c1e040b615a0f0f522030604104441c40d201e603005007900701345421010070060038500104665120140162410080e1440c171000790344004880c800025000e030b4000801c403581141410581000030794000d58031101c0d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 491272050 1250 491270800 491270807
    0x30a060b030907090216060905071401020f0706050c0c04050c09011404080303071b060c0908060108070b2d03040b01031505040308190b060c032701020d0e040b221a01 73
    0x3244039030440c01760001094982e840c03020121418003940808100102c2400d401c00030307a01c1d8507030301801000a0599441526035070000961860700e00b0480e00030225103081c40c8081b80e003508600c2c026a02e80c8a840404030085c0e0b11805040d100e0144c01003403580b210002800148140d14030314140040c034400300800d010382d00010040300c6e401503840c01d204132841100740035500d00340414078019107410b1601c0b1070b40c03683d10351003203000085402000c11103200766255595030361917107158400c10040c01400c0202050315014034a90716400410425400c0c1c114050248800c0070381d01c1140c08490b1720f082c0c003005004000e199456400f40c012104010005803500f560050111240604090081031081707018120403800c42e04640e18041c4060455600c400480444540d00c2d00480c281c180414810606614801d219800071301d0304450507030081c4004560f80d5000e0781c540c0022188190050344904090000b03494602d02070582811048101d11600081d0340090120384490128102060041048645680c1d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 491273300 1250 491272050 491272063
    0x50a020403081806040509190b040605180901090c080604060f0506010c0206090d0c09150510050a050a020f03031008011a090c0a0c021003020306011404060c0b090a0f08030a060b0309 80
    0x142c4103020f14072101c02d50001502e90190b5840281d201074031a003007115003502111600c8101c040d43c0c50a1120349203401c100700554070703507000c3c49810040340080840c3d1400940c038500d41200c40e880001501040c183c840b05c103840940d8108850941c4200300344400c0040c1441610800124107604001600b0a480000d000c1215100068401d14020507618104d0340e61300c02d00341e0210f6000c69011100359070351841001410f41000803618242040e20005510700b000a5a0502c840c400d45c1d40510b0407450f40c01c142c075135420a41680f801c600c240d20070382c00300100c00c10085010b41907240003010312500e800681c0c2d0944051030540c1c0d0341010855803c0039180c680c40002c2d43c00040d494005070b00c03641401e40481c1c012031038880c01307075100201e60030703a42e421a0940d00075805050281d84080b070504400311020101d104900c28000010118070b11080403440d020151a000f016101c02e4071010921901d031141544400394003078449500000c140080c4000610601d801415054080ca0441c60324448460b103030708 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 491274550 1250 491273300 491273317
    0x809250b0c0c0d061e0204030206070206250302031e090306070f030f02130317030c0a08070903020d1b080c0d3504080114090a0201030b010219060b04050a02040308 72
    0x4022510700152001880140c40c248400360052464000d5820b10030041c1c140c00a0b070a01070b01250888405c00c6906000311400e41b17802030181c61504805a0a2003116804001c032200d032100640311903030301d954800607002038540c066070003907807510784680c00b18081c0d000d040c1403440183e0301041075008645001c00d20980c0141d040c1070803061b82c240081d003600904000311002100e14400902d440c1040c90740c0c0d4105c001c0c1c07401400b2012300ca181904189003240700c203075603146200340140609003841d40320300c44082c2d015080c0d00d000d82c0c0703032070303032540403da0306503101400311141d19011444c030218404412107480108142d4004001000d842c40204021000b8008060000700403020010303902c001042e084048001d011402c820256044030201540e0b420074015a0300ca9400d22005804031500d041c030b2140a94880f50203881c03403044550040d00180300344c4001d01d056000782ca0b5510102840c220780036980500408000c00d00410000801084076801040c00c1c070180c0c4180700600124042c2e0064403181d8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 491275800 1250 491274550 491274569
    0x1e0618180b060a0f0b03100503010507080a180605090d0806030c060406110102280305070e010509091003061a1906020a0312060305070f0510030608060c0a030219080925 74
    0xa0312100b000c1191000d8682000003031001e03000c00000d014018400440c442e800c1d80380341d111140d03154010035003651010342d21200060b44800215403e001e940c1d000215054840007082403d0702070b80e955505444044904014a4100e21050442c450300000403e5010500b100034003850a0448002440360265009800400035030300e040d821144000d50460b5098070140c40c0100c9291182d880500a00015984403c00030741024003050819000d0030a040d14014141c5451f070504514030288080654010710020001c039840300000f01240d0103106691000e0424520900040144070601401c0c881c0e155040c541179902c2c0104000c480c1d800300b01010807030750518098850204070031a03c0040d003041d070000340141c0900003000411010303000407401160001d541030024016001070680460b20076218101450300300c2b1002603141c89405008003114107007410014141003440b6000d000045503c0d44030408a845442030040e49903042000d101c6003d03901c070349141c1e191a015250700865002b40300340c030b000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 491277050 1250 491275800 491275823
    0x90914162c040b010501020d0314070525062c060a020703090b1201090605010216030222021215092a0f0a0206060a0b0c0c06030a1e061818 61
    0x44060300d81c4054140001c0840c1456508060426080d000000c1c07241c01c4c00751141e07401d5900e103240640684111a00ba10559815640d02d034101a2425031103190b0170066450403d802c418000002e41001400902078103002441c1090406030100c00f0301c40681c00d07401110440c2d080b03030008000103100c035403201a602c3c0158990301d0b10300d41a6402080e41e005010350032804244c2d490b85100c203854007812100844410710020355540016601c0381020307211400b04525a050500250800c1d03400144000e58419484195100d580048030898000f000c020f440d4001e00018040d18614003850b001a18000b281d0110960520460b80309a240c000f410900710320010130002c40d0300e00f182c1c4050b0768000c1840c1031915075a05031840b000351202000c540e4188150280ae02c04503450040d071007920f9404030380308020026184041304100550b0001000c0d51700d000e0b02c82e481c415800e07112682c0908030071014880440c0711410300c176261030928042d006218200d407815111711042d02039125810030054106115194 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 491278300 1250 491277050 491277089
    0xc061206041802030f0f011a010804030f110109150506011b350304020103060b031e3615130b0712150315020f032e09091416 55
    0xb400c11800340a5418015004d11043c59200455040c0b00c1c9407104008000883e050020000003401d20700e100fa0014803c10009000640a1075000c203062049080880100c058442c0c19425161141401c441d00300960860003035040356800b0380b070340000d400d0904041d20030b080c08011880c07400c040030140403a2207210070446401492841046422202d0070100c159038101110240980d0041d01c00300d0000b454240c001a0103034518040d28004d0781e5801c0300d2503034a40d41e12840184d541e00034180d10b0440c02c180740c4024801020024500c3d0040b030361f110028625107400d5040b8108288404011440c0d1201c00801600c260b004842400701c0382d0000080c3c44175202c40310215188100707034000818031840c01703006142100e400e54840d811a449407940e44d115848800410050b402080e00e120b1804506001003042461002c52410412071600d00080d241101316800b10300da401140d00284100359111048428072580011140d60400f0100052030f103014034000701c07020b55845200b50468108403000281 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 491279550 1250 491278300 491278331
    0xf1e0b0c0a082b020309060604091e050717060108071e0e150a03050309101403060d080d0f051005010518061309110c2404030f0309120207080c06120604 67
    0x12484080c88081e84280700344280343c10001d61003a2001004e61044000158803440c043c020030f42c040d64032144600e0114200020103500c1384200c00304075824065030401081d40c22030400781089580c80c85000780100c0d4904103840c2e082c080c0c1500721910080c0b00902e8140f040b15110980001c07070301108044003a507503481255406540440c6201d070350041c0404000005e006000000e8100160300321103004556414080a45072a0b0100764031151000e014000148107140050000034418000d103102807401a1a166000c200d5242c0000c7e10031182c1c0d030310b091113040d241540b4148007800c42801c2c0b0a00d040c0364041d0756110007608152991103800006150b814801710042103400600005505101014140070b022041d900b04000e4080c0034403420959411840814503000c12890040d01041b50f01d881c1c0d40c17800c82d000f80c540c0400305d0904d5111040100040e41c1103011031030800040c2c1c09813603103c1c1070183c1c0605040551450601c514001d0255003103180122800a8000340c04580014502c18005c1000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 491280800 1250 491279550 491279587
    0x6160302040e131b031a1003020907080a0605010806090406050a060b07031e050909010605090d0b090c01141c0203060d08190306050a060c02090406060f1e0b0c0a08 72
    0x48144100030028060b860403142c00085500d48160911500004c1c0c103c105100400e07248000b510138842201290910111014500d4111000911b99403c02d9103d0f0007280f100e600694012000034811005c00c12000c55901c02c40000d41004d213021000b0707040c81c90005900f27210250010f840350b40d072076020030f00765026a88400c0043c180800480d469200030b0602400c44280c080c0d40041d16151100501000b40c4a40110340012400070101e541d642d08080c000c4a13180c100c0040240c000940300c1c14400800d080da000780317210b0317032810008250034000e0100040480b11300044082440005210003004054000480440d401d0700a00050b2030307543d400001070361090040005051400b002445071100506c80026030366600050f2800d00c6015910010b03c400e0065600ca600c001540602d0440c0043c5040403005030400d025400c04180700d52100b9203011074070b10581c040c11030303103080c0d0520181003d4140701000040ca5028401410407440d000300d07684820051000820346140090406920040110030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 491282050 1250 491280800 491280809
    0x309150e010b13090c14060715090c090f18020307060c03091805180d05030a02030406140109050108012405010c05032205150c101509020c2d0616030204 67
    0x440646401c400c4110081070020f90644170503a01c80340104602c0e99120880218800141400b8585001600d8a0150086040e04c04100313035110a00b82c004541d0240180026210380d1100180d4403442458050456001c00324259450200583c0c8030003680e000b0440e0421190141040300180d68079182c11107080700507401c000180307281c00741064580051544402c1c032503102d40403003040305482c50508603074854510381e5401c001031041002601c8078445070043c607045403003003030003244601e5500b40076441c04400341c001c0d0301c4c441c1e911030040003105424000d42d1400542040018544244840f03000d4401203140607450500a48801d058204101001181c20f00300400003012450b1451900940760301203603200b0180701d041c00080001e200308c150000c88135130340342c08401420801000040c030b50203080d22101401c3d0a0001c0a00084d614001d4001000c065125402408500b00c60040b0f4a401007a19001020322500081242e0409080083c040c2e403c060104590a06400209801c50103445103820 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 491283300 1250 491282050 491282059
    0x60a0b0a02100e030d050705130605090112020714060a1112041e0c03120914010806030f0f2505010c03080903160b090609011107020613330309150e010b 67
    0x8814440f90080050240001c98080038040e80c2c4170720904031140d004004140c18024810703001080031600450082c40c0003001030614021b140b04006080c001c0742c01c4418251810346410102501130700060012a03030240014004010440354100100190300658081d5540e0f15115000f0600340f00d9200c1e202c11402ca003070300740411810440d1601c09940d29140c03004036403100d1550800391543e40289140000d9541c0c480c1185070024089004561a03035016014079054007828401c212454420b2144441c000080001440d526500025800c2845581012144001c1c080c00080c00980c1c0d100d41a03491454041c60652125102d00e040e003800e5224480d041b1300340074180380d251000c1020615906118140600030b440c030942d5820b0005081c0c070400c21035065200410440f43c0014074060300640401f012604006450301c0e100c1c1050000d80c219038001c0700321455583c0415070340160710907030100c0713001540c0741c04e010941e00d65035a10035116103c00d016000e940c89078140f0340103980940c4040c01c0040002c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 491284550 1250 491283300 491283311
    0x304121e1d12030a120209012c03030c070602061b04030201080c04090c1e1106011e150201020c16080d0e040e100b0414090a26030a021c05060a0b0a0210 67
    0x88605580754010604c960125440004003840094144261606170714180c40e00c51441036591600c04118880300001400e03207808030f480d185c2a03202000031f8040c086801000300360041c14144080d2070064018480b61405446601c60520f5418820991341100da084c01c180e85141c44404000c09e99005640141414615001c0c400f0306075580000c001800c903100444034210018005022189052184440c01c0303254032800c0100065030300c00d0f0380c6c1c2a4100500003084003964940050900b03181800034007000607034000c40c0510605000340445010b001c00107128213015840c1200c80703911083d1866910040c003449102080b49900e17140c02100c07003404030300241c1e082003e609808000071b050780000c460003103107801041400e5000300c0d0340c20b5016030070300070040402110541c1c50f0381e000903105d000081702c2080c2404040380308080201650261720250000340c4c4030303c1c0100088000e0346506030507070040b6080800b80281a01e4901c50712081e946214096943c1d0402c005040c1d01c0c242948c4664400145401c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 491285800 1250 491284550 491284579
    0x40608370515010e01060e0306071d06040905151f120b1f081b0910020109020a0305060a050a061202150f12010317030603031b0111040b0304121e1d 65
    0x6881d05940d08082c000d0080d90300c5103030803101c407d040e0755919015402540490b58440c060134141c0949440502d46807031700d1503014042000c5400a40c0114a00c0741c491041c0141003002000c61911060243c40316282040c4400704441c014546480c40400d005c4000414001050301f40c100342e034280c0c0003600000d03101d010071182541e00d0703204d019083c00040480003c02c00600c509908007814050100c0702d6400d001d044000c0098110220004030250740d81e420f801d0005894403080780c00114069005040c03285400071124041d904002d2140c016240781880c184410400c0151307180354903070103540c800e10038001d005c01081039104810310881d8400303022131042d031505441481681600c4c8140104078442c900701c10b1085aa0106460190b0715410501400c1c2001050807100d828043d403060020540070801c51140704c20382c1c8140c1040c01581d2001080005100d00072070142a418810b14140002c2c070b030804544000e01d1800d10402c1c0400074440412100c3d000742030803480c00114000c240494a101c00f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 491287050 1250 491285800 491285833
    0x50a052d0a180801060803040b03060a0f0b0d0b06070b0f1f081e01020f04050603090c0604090e0d020708070909150501090c02060703020306130519050c090406083705 73
    0x1070440b030405107800c0c0c00116000318180118822100064011400c082c140140d100143d00000c00c1507410860030b190000d011120100050002e0540c42c0d0700356954a00c58080009584e41001d10300d0140c00c0410285001a0f66030746440da000e50442019480e90321107140b00306070a51262003a030180e02c2d96600c046246d2a01080e0000c62101c00b88482500ca02005405400c0c0d000310500090b4060050004001342d091800003182d2000d0002c080d82c0c11258003200148083d0803d8019801c403680c1c0c0c3c90b00c074000140c10405071500440900081489518010100d03a4503c040d01480c100725454403600e6003000411900202400703220041032040c3e684a039804001049640c017210011b11900c0c0104103c1402403080743e0113030001511030701491031104900b034090800a0000141d190b0144c4155980d248544911401644030100381d640d00da55a0781000f080d104240c0195845400110300060075003d1849004008180c9050a400981d1008000404048507180140c803600502d408500e00545 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 491288300 1250 491287050 491287067
    0xe030114010612050114090702100e0309040501080f0709020a09080f0d080718140621040b0606040518060a120c3003031104170609010c050a052d0a 65
    0x50640c3c90245038000b400a0b0401e4800a01c103d40b4000712040d0600000c0c2080c83c81c0da5845581401100c4005000f849824201c500c904100e003078541003c111410b2904e801d008250042000f000140303d07080200003d02d444000d2403095108803640081e07460506409440e0f0480102403400555a420888880c110f454a1000b004000019140000205042c6c0a4000018400a80d0446001090034411b054082800c18211290302c07c000b880f54920751140841b0380c0600f144456441022810b00b490100354000c0040e01c3c10f44070740e41c00c0c0030500c42501c80300d00c210170b8012002481e548079140c600108611880d1604040850b80c0041500c4c000e1110f50b00d544802c0350450740c1d40784101c04149030b038020301c1451503100c2d0720044045d41044000c64401e800c180420b007030080301c1515080d0b039985042e2060207050707030100703041d0000010082c40c01020700c0307030035000c980506003617283c0750005070010040d101e41c0c043c15580544014134141440182daa08500d442026a01980d4803192500041c16200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 491289550 1250 491288300 491288309
    0x15030b040609060e01140103060e041106040b0301080a020a060207060e060f0d020708130f052824110307030e190506030406240501121806060905010312080c190e03011401 75
    0x11b080300c9040b102544640310743c00c22120340c1070144089448941d5625010341c40c00b2400c80c1d01000a00004c07565040950043d4006c24480740203080d921454818031160700802d9110300c007503400844e0100705a44d0481000001e41d0011a4055502c0c0c958040d000c055005040c0d50780e440500c0400d00000308901c1c08001c003005d000c1c0c9011003080d5651001c044006000500a007908a4525451103c08664030440007600030021188031000c540c0300d1031a00401100828114018a03030800000c1c030003500320300c000041d00c1112000c3c40c6401e4003610b020f400d01c1080800c550041d1621154485488582551030015080041c01c059403410705007040e001420300844440c07040c0f190340d10240c10090140500300704551060310f8190300c0610300301c0c0c094010158460740e107149140c14030b80381c00011340c0c9201e07038070241c405404c0000b503a505600344265400d044509500c1030052410500c0700a49060090b42c04036040c25035a20031403a203030360040366907140e44507406400d9824284200080e811510400e03040c0d8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 491290800 1250 491289550 491289569
    0x20102160501060f080f0d0c060b10050d110316050a260114010c02030d320c060c0f07060c0c021905090603010c120509030712020c1915030b040609060e01 68
    0x1280c89045c150346480b03558004100590001218561140c0200d800b40c2c4454060a00000d01a420300089191112403000c1c01c1c001a10000c0c5ca94504941d501ca4480b400c14100c1c41907041d8030f441c001d0752038160786e0000060148900816220320081c810304034440850403001c8030b2a0480321031740652010700028083c0708a80031103802e607a09554481c100c8140c24030b400070014802038081c14415140c410306541340c064000c421028007400040e40060050040080c0ba80310f80e174500a0000c0141004809402c4800e921b900b081103600380140d0700f054500c0d070341d00f117000062605007045055480c610300540094120480501c1da9415048441000003201c90a450a10ec1507a035542007500f00e415140420000c14490101400b400c20680d000503441645201120b1400609444a108409007034800078010f0b4070448078146c00d07003880285014442c4041d003481a801e401d00c1d010b60b0094090703081d81420075076158044101580c03550042070003040d40b0178007000001c0e1600070b04480600d09000e0541781 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 491292050 1250 491290800 491290829
    0xd050706081506390a152703120b0a030609061b1413050402030906070905030c131505060c010903080c0c0705060708073008190b0102010216050106 65
    0x90f41041e804031800c0003260710708950716034810000306070380200948004640e82030b071407940340ca103c008000c0049914001d0303e4804480d2140360340001900c000d0480e0180c40f200c400d2440c00f00501004071841595031504207089201e8040580300d008283c0c00681c1035016640d2940002440190360000c803010340652010300000c02d2070180300415080032600c1c140050440765101c0e40003c280805000c54842d0225400b021554540009080c4d810954088419400020034080101e4120b03c1580041c0303015405003203554241400200d180050b80c8020803100d441e8000900f444105500440180100030400d07030300c1d0420252098000c0059250031804a1405401324803000d20000c103581e150b5008400400344035003480c0501419400c003000864800509006a40c00504107155881c1030b40c1c101401d49a20200e0880c2014541060100070018000090140000550b00185141d81d4041c2d142002c030715842e42500407802481510700c2078059442061004003000010f4101c0800c407005000c52840 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 491293300 1250 491292050 491292091
    0xb03040b1e04030c022404141f1116030503190c0c03030f020c030601140103020a1205091507050702010207060815180601091a07230102030403030c08150904020f0d05070608 76
    0x4017000080c5506c2c007400744002c1200c40c00200d400400b03000098404040c000910321030403040f80c81c0071400300106111107a0030050100030040010b001c1e0020405550711480c607105d644d00d0344950070707007088401c8058440b81c0020380240c07a0811107a610004421480d6034034200201020751024080c401400340f0350130000c0d40d1600181990680d10020171000c083c002d528015002907010107c600c0c00d201100303020b003090440c28031811b03100d00b025001030b08520300d01a07941160214014a6a01408014800540541d0380003030790400f40c0e6030606103000390b91510224011041242030103c0e900410b610f0120020b450320544ca107001e00070030b0702d4410000c1e803141c01079070f60340d41745c40e003403001400c800c0c040b41d80401c2e00d501002c202d04040c2c0701441c201102c00d032805820b80c1e108440c281c0100792035400d4080603950102d0703503903804500c840740708000c00090300002e4940711001d800603100e101040780c01c0c4841c3d52a5690044801e0780320049840303099540e10040c1c40c0380c84c2140d0801d98100324940809 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 491294550 1250 491293300 491293339
    0x501060f090e04110a08010b030c0405040b04111c0602040503070b070515061908030307080c1c1a18040b010902030103080a0302070609080f0409150b03040b1e04030c02 74
    0x1020600d900e0701e00d440c5080c425000b1070450b0050040c1c580e40d508000a4425494055071400600801c10004c10305c040c01c4000e042c60f00f1210340e0031602591130b000800c00822655803005400c15804000031015065480c0021404518000400302803014840513004001d2554000c004440c3c1c1903050f29041940c50000e60030a001e440e4024001c4e820401e194410380f442d642d6440d07804131000f010140d4007441101c8241503000c07a40c20803c404d520000a2102143d04150040e40c4401c011541b980341424800301c0440c800184003803103040780e0b201e010300b400100d0302c0303070350401355400103008015006816900c80c9a1450281d0b02a01d4090440001007507040140c000c4034180c0e50042c40d040e14012181d88100d000394030404080d42c2d00d5070355800440010f22141c00600c10603c2c160700f82078903541011203400c210ba440805088c0000001841000b80c2948542a29801a00130003040d809680b01d5031f6070745c22108162400c0d10420240c000f080304054008014a03003040c0260b03070003c03000202c80d000780c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 491295800 1250 491294550 491294567
    0x9040f0504021f0c0c06030204080c0a06050a0318020402070f0b0a090807021002030c120301050f04090b0c09120102040e01061106100509060d14010207110303071208040c0509070210050106 83
    0x280d007040c0008003081400c500714450401000e080d1030302826910041d1202140c17000160800000603400203002c018030001000610007551045509103a11490310340050180d20809084c2004e0540368894080580c03e0a04101182a001f40041d55030f03031460719000d203401d4076001c81207518600d920042841c100c2d0034415010f03855803258040d0314140240d020003000c5800f440041046110421846031400820b000f101c8040d0401e031115620395042004100c3c1c10102007502601403841c2000e001c001c500c0001c000ba0700425040000340ea134101010219541c80c607602421a0306600010380003a03a08415060541201c00641e29210051000840d0300c0d10b621041da038405400b4101081031040c1d19040584035004a4010000c3c078150141d5511281c8000300c0c1180103010b42d41c0401c49000707002407510214480c0004901951030501199600440c1101050440003007080c0340300000d0030044003041701d201519004100c0c030000d1030600c40080d13403050781040c040c2c0301508140000655134020b0079034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 491297050 1250 491295800 491295803
    0x30307060b0a0b041a0f04120f05010e0a030c0611160c090b010e030604150213080f150c0d02160605040803040c0b1801050d0216030f020601060206012607051509040f0504 75
    0x11605d102101d08000640041d1907040180104000000e0003031040da8018107520b00c6600c0b0380300c01210504000d421100305000e0500e5680007001d000c00000da001e01d1b58000c02e640900d0024881010f19040940da000781507480d40c248107100400800c1c485c0b80c41804e411180b00d10b1040c892100c00800450f4231500415005030035900120100d40044d0744010a0503e107a0350800040c00c0541070100c0703034207000041c1d204a4081d0403c0a001c64682001e0040120f18910700340e0300d040174205214441000e01c1216110382c0e8056010840f1015642c074050404821604608140100d041c60f0401d80c0080d03005907412210b42c1c0da00300f00064000410000d80c2c0d200310540907051720041103400103484651110020803403032a420041001d51001c0c10407011000c84c00bd40c0c4140102c001204080e24099040c0c103e10255030141c1d004002d01400c07540604400c0544600008500c1029180246810095000030398012a00001c107240500c001c1c01520450070211014400048441c06280441d80700740d50 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 491298300 1250 491297050 491297069
    0x513051e0c191d0603130803180601140d140a08030a05060907021203060103020a03090b040c0512030301120312020c010c022404050d2604050c01081f05090a0209030307060b0a0b04 79
    0x10003243c68074100e8003a65114011903034010008507143d807500300c9940115101d5102100202141882400400401d8058228040919100480b81c0b00007007071140c900d0401482081c3c04281ca42509200344040540340f980f10030a5034690404005180290074103c0d601401900c40310009007526100042d543e404000c001d2610b861506e4040044000e0340c0140c4006040c192106040000191703218001e80c415405039200010300e9003010100702c5207152030003c0b03c0c00e82d4400d00050007034446000b2001d0089905041081085050244000290240c030900f2003082d480c01692109194002ca0700d814411031000000050403140c11a03100e401005581c0601560300c03100d400310f00140598102c00c1515500038854040d00031228041403000d1085508450315001880b0906165030046556604400c20310012450207020301d904520304140341c810944100744080204440c40d84030b5040300d6050700040c0c1075903502c1f042424071030080c100141c01c1c80d0040302000000501c0c01c0640e03080e181512240e2a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 491299550 1250 491298300 491298347
    0xf0c0804120e031912180f14150307020703050c04090c150c0804031b090209090601030507050c1605090a0c0203180301021213060608070513051e0c19 66
    0x7101101c80c1c0001080c5680c0611820880807060350200307820462951044800502a0303500040c0148075120608000656005490301404080d684101900503140410001c1c048016040c0c002070851806245400c0000340c00420b05c000d40f40d021a5040507030b406401206c2800b821002880b0881d40c098102030003852540c8424030000c0104410445002c82d01d181c095480c074842c3d00c1e80c1c0c07096400760b4001c8880c48906860110246c3c01c0c0400b0800030010700a0842c2070020741408204413103401450503040513a5100021030b01c13800b40c810390722031a0b1070500700c686034040c505c40340c60080e5583c021f04d4480c1001c0000252100c0041c043c448280d0b03c150301850070016405600c250301403020a03501d034195000e0006080540d0308507a001d128406807003110101529134249401110503a0b041800580c100880600498485820403d440714542200040c2582e802d09414241401070082202010020341400700344807400000d00031100e40c0c140c1007000180c01c40303015100e104a00b00801c3c0c0703850030030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 491300800 1250 491299550 491299583
    0x3031009090807050f060108070501050403110103020703200c0f24030406200403031d0a1404060e0c1207080f010b1804060902180a030c1412010f0f0c0804 68
    0x81d00301c1000c5a1154662508010080e502c0d14200706200c000c042c865400701004000042e41084400002e001c01c0c00c0080c0341504684820705001c032200c0a20341856000611401090f100b007030018a110541441681a8003080b40782d19150041c0b54070b1f0a00c50201ca40071089a0b240074011401e41d44118800c100c000c41000c490401580c100030800d40d0740a40d2200c2c41c4011404c006010702d02c080350014140c0c2c2d42c608503e406030405a410000e4259102070361186080c03601ca0741a403000b0348150707860f46621144000c0010700500403940207044910588800d2001b40c003055001f400a4030b8004c807102c0d0695943c01d000316a8500100c580910020003800108118884280148151501280f420700d444403802c01043c10349a00d6402040320302ea0001d040c80141c1480c00394927447c10707001c8480f12540c80c5541c071034000d60b419500962003460302d0017400d0300e02540d0750f50101c0d91190f100c1e0000d000d620f01941c8048014906900d007204860300340396983d02098400d4040d640b06541c0300f91560100d4030389 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 491302050 1250 491300800 491300819
    0x50606030703051305160f06080f0f090a05030708040608011a03040b040c0e0f090d1409060c2e0b0d03020a03080403030e030d060f1e0e0a09080301030f0204050603030310 75
    0x7805642021452840301c0c408104240706840c6c1040c80120020a40ba180842000908a2a0b80400c00300701610080c030440c4180311146c039402210a400011907a02c40500382ca040680405004109200000b40d0904110750f450103401200c01c951900f074600e81c1d844001c41400d05880d0101841d4031000c200150000f02440109a08039014001c03450802d0b8903004d903250610700a03160007060307010480400100f81010405900c1081070b41c60040017070750b2007074040c150b00d002d1000c11910480c004140200400030402c0000c5200070111308220108016440c80c00541003504522003541d810800c001c07825003000481d80b204a0f40c194010b00d0700351810b403000c42c0c105501900031020107031a120a06600503007003001d044c03030015802d00010300500c0e00c1c03001c46240c42075912000e02e400f944402c03025003241c00c0d6901c408945201c5901c40c015a03515207010014120100000d2a4010202c0084140072844451010203072080d1010406900c0303050030941c0d240002c4034070000ca441004401d001c804034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 491303300 1250 491302050 491302061
    0x20a08070c1506090b030d0315060507060905150a1a01050d0f110f0d0e0109020a0e070e090c0a030f06030206091509090408250c0b09132d050606030703 67
    0x38030100c00400c001c02e05840c19128181e0100303691988850b10095280307801e02c0b901c0d42e000180c0c1020001d41d960300d40121401c0459205c0d540030300201003210010304c6216080082d42607406411380c2da0b4407200d0b140362002540e041d00c5400d062807800f960b040e0020a00940c3e0070098034140c5406081002144001006e4801066400c0300349071150221a030418012000c1e212140f808c08140303032210a500004011a4100c1022a2641e0b06200c500c00150311400380040c140c4d08100b00804035503a40b00015a0549011402e054000800004002c0024607040c082d0034044c200c1d540c20301c03800f5101500784098a20710301019602003010091819a85010502e4428001c080c80c1e07081d007802c07940f200144114101303c40944900c8000200c0c0c501564078040818416244501e00e410020400d480e28559101d890180c03410f40311000820350180c1d42c030100c00591b0342000b0744061100141e042c42d01800900d410000040340c0024040c00d8001003014040d40c1d10a00b07000c2c08441c259a20510220701500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 491304550 1250 491303300 491303303
    0xc08030a020c041e0504030201020417060f070806010c0519021305242404080607050c03030402040f060b07240612110616080903070e040b070c050f031206040f020a08070c 75
    0x8030904c0c00b01c3c0c645255409614452402a0001078540d807604100f03401106c00341e00107103019081030041080305040040f0843d008070162a0040c041c0d40c8410060319082c401402c00f07099071103443c83d640d107200c000d0700042940c148280da15a4414507042c00e40303000e8407000d032a400c02c000121030001d140d2039109401e1904441009103040440009010b40f540040303641d1400d43c0110300002070520003082c0400c51903400038058070b4030900d80401c03040b00703d45901018000911540d1625810402d145503034000d0006080c400c2d0185c1e03528841840d003102140c150b584810400d00c1600d141680e1801c2c2d500c180411100c5031300d01c5139024903403903944221009590100321740c050028400c0f10024400d0b10300c140c1c2e0661041c10100e03a41d00c4940209407401c08143e1040000b000680c00304000942032100e0640c219006c7d0403c058019010314020b401d2000c41d50810402e444041042072400085021081c0a42c0094070104004031645803007405900c66080c0744004500322a01040d12304e03214207010118907 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 491305800 1250 491304550 491304581
    0x130902011b0c0f0618050108040203030a030504050c090a02181c0b100918110907142b1a090c0f0c0f0102130312030509070b07060b06030f040c08030a020c04 69
    0x60380c83e1541c070344100407590000c90000d607602d101042c0d202c0c01d4580d080d014040074203040d42c0c18036095001039030307920440401d90704150302c80d404202044000c0046095810b0300900800881c900300210340003c0d041035903070f003086003010f050b024418181034214038104000c0501c3c05604051030b8503200080d4074050007031030074030391440300002c2c1c0082184124407a6150345528503044a070303141005048082e026900c0c91207031480c0401d200455401c003408030300c20141c2149440e1100040c0c1320343d250358440f842001b8241d180962880c0d11032020707680a805c3c01c1001c08803100051f14040c0078086c06c000212194684d66404103d6011a03408170000b81004441040844880c104540340243c207a03000f40b00c440d8072001030840140300f04104030101c003842414a02e010441c510384180220794a00700d40c49060341c61140040c1c000244401e81c0c00a01d80c40c240a00140d42c0c0342031403404090002001c9500752110381070a9170205204001008881c1100e0043e4018491041e40e81c04010003802c0c418503a80b4003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 491307050 1250 491305800 491305823
    0x10906050a0e091e07110703030e0402120f18011103060906031e030706060504021303060216020901150207050105033705070e01020c031504060c18080309130902011b 73
    0x295600c01d490240701d0701d007042135500d10030060700d680410488040c04140500040406046420030f0000d5041c0c00c5940520348954200390000204000b84185504201c00c0b41c001d40400a441b902020b00030301589402903c4143c0120849031107003208d942c803a004500d40010008240306d450805602900200c004041d40c08008480010700d82201480341d00c8802900040307040c406114aa00c0b84c4002040150390540c0350041c1c85000001015840c00300924155000c20410305444c51314109241543c1d020300300d51260b5842d2030030354000442050081c00103100e10040410750703511900503203000d0000a8040c8448403c10a1070268828004c2c0696041c01806942c1c00041001402014018136036030312841900000d0394002402c0c2001690510702aa1041a4410780701c0b00694407a94030a40003000056134401854048075072018100c58001c0c80301d282200842c0c070840210080808200441e801923502511151001c00c1d0750300400040c0c08680c50410044520940c0d1402030366a6220342000d044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 491308300 1250 491307050 491307077
    0xc07230310050a0b0a03120c050313031a010b0403024b03060f1006030b1207030c060201051315200d090b090307050607050a050c1002030403120b010906050a 69
    0x1a0040c01020940d08603125000d000f40f080481c400d400e943c0d501134980c2103c141c1143c40e6503070103c40f042c02c883d0400c1800b5054809020043c416030743c00c41060b94044c0489592402c0101c18248504803d641854041c000040c680340c100040782c007200d0f40600b4034010500119460701004842882c001c5641000040e00856048190760488001004555045841020809140c82e1500003049522003c0041050103000711740c0c008131030200c41083c540030403c40711400106417102c0010b088028540714004003c0b04000100b4007000640c0c541c0d600030000c4e903a41c0304a140c000408510080c056a85100580018450075080b10400d03400c4803a21003400e21403070b040d51421381d0001200c0c481c00c40d03840c402c55080010444005030003410b0000214100440b40c0c0300c01e034649201a01250a1050018016007e18001c01c01d98094841307a0301951124440d13454440040d500450f0f084000403404845000c02c0c0d1803501c9207011482069603160561070404500ba51258401000c0710306202c0b07800800704 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 491309550 1250 491308300 491308303
    0x31104090504141506060d15060201021e190c0816050c0f0609030304050f01090801050114010806010513060e01113003040515070c06051f08030c072303 67
    0x516003003000041030b00d0541494107180305032022440396600000d11030f126800080e1070168104100700c41c4184c0e02e0783e10303581c880003c1c00440f042503980000700f40005003041d0103502801030360142c83e1801c01c107240f004109021620420500c8540d640c8800d09451180e8400d0742690800e41c41044500d24045000b01d01c00e244811b100b104079456888400b400742181080000c40c10714003c01c4e00c1e1a4180828030340000c0d100c0c01140503e0f4011400004039404030780c0b01b1a21b140041440100800055848400ca0f01d541002201c0103404501c4500124046520078422039200c00038000100001741d013051700c00c403528140310200318104400c2e010800c0b02c400d01400408004a6061040c043c08599161190394000c1e642c2400035829505000304000720340b0105040d00801d80d04841018240d0311001c040d60110000703c800b51180b4a400c08121001c501d4110404c0000c000343d5500d00389654070441103a907031090300180300250f003181008000d00c4c0c113091102082c0015084450030381c81031801c0400d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 491310800 1250 491309550 491309557
    0x2803081017011a041103150d0f080d060b1207030b0604080d170f010f0b070f0b0106020d02060c041d0c0d0c1d03030f04061206150207090f18030c030311 67
    0x32541d9544482181e103400c1010720340743c00d010064900b03009103943d40814090340d0200030520281180a109010300301d030344081500c03005da540010340d000d0400250400d0300c0d0340d402c2000e80525103441e0280104211408409450402c40c10a0303c180b100e0781c0d0004100c01410200000c241c02c12802c0c040440c43d1001840b910170b08500c0b070b81e078007084010303190700304c1800501c044c00029a40c2c403400014042003108e0709041040e2200300c1ca0541d5204880e1405955000c040c0e00040c10403800c1800200d03d956010480403000081c07a42100c0d4240c88410101c01da9102d03c0c81071601c2521001c0301c001408078202811a40003c0d00c242540c00c109216180d841070382e0070400749000040e110301c0d0300f808012a101621080c0d01c826001035060a0560780e040019100b17a000310814003900084102c0681c0d01078000602405220b00720400c01c3e000014040d540d04454010307400918180a540c4140c0b825502c5006155585480907021005940c0c60a540314030b0300200590030103444034008601d00b034000004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 491312050 1250 491310800 491310839
    0x6060a050d0905120703120b011b050c0a09021908190b060903030a0503060130050c07050d0f0201111603050a1806090303110c0a0b0315040504050f28030810 69
    0x84c00d6039551075250050240220b040041e01691604422081599100c642520342c00c0605028107000030181c1071451410390070f045441d6211610400c0410849110303005010084500e0700c1d004106960401d068a0f1000201c40c1c800c0541c3c1c4162041412070240d400418110b0000b4214510744030b15000400d04550000c041d00010074800010f10030b1a5900150764541e602c20001000841986000001c46245e80c90400301c0a8680720782c08510b004039114222038201d54010200c501d00711503600050006522040d100d0095403074000d4a9010b400014110f0300615866566440621865030341034404e600031040a60400c04000c15141130b0300d039240c0c1004090315503519126046495480c0051400c0044d510000207500720549505050300c7e000414410f42c1d68419155440c2d0b5602030384000c4600050241541c094140400c0c007040c003001044100c4c22040c010240c03840241e07094407010031003140d4400e54a4001000d1030b90000702c0d109020300d035008142200d029454aa6a092808280d0614a036 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 491313300 1250 491312050 491312083
    0xc090d0b15060c031804061701050a060512030723031303170c06060d0602090325080303010f060f030b04060b09030d0f020a0f020a0312121406060a050d0905 69
    0x240003141c0c115801da000c9070403048500c2882d000c0546250707510380c0030780c00f03810080040e4509540304940d140c0c1c00400183c81d503411104605900c07501280c1c040c12007030300c000781018907092010800d0b083c03248000b4403400b0a08011031900c0c1385940d441117121210b1034685901e010124680c0c40300e400c00d10060409135407036248800a03505600b0300d25015640d0500036416107208004030390902c40b010031855400350003122000c0c08001386040490103441510001603250007011046480104800e20b011101aaa16004021103484202d00c41d500c0c4000c0c00b4030040c0c003031000400c20200e440b1f1104000c0d10141481c2c00300340c280d80c0c8004101500d14a402950f0210700100c2d4611440c1810001e12a4100040c43d01c1c1d6840410350300e000c0c1d1545800c60010b40000c044050b0041591a0910001d0007075078000d120800ca02c010400080420039804000848a401c0012030038207982903402403402507100629441c54040345081c00c0d1510390204240351302c8a500d89800401155040c006000400c00800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 491314550 1250 491313300 491313323
    0x3091201061d0f061c020913050f0d110106050919021c1b0f0905100215010b04061d061c1416110105010e01090504031e020703151e050c090d 62
    0x500d12000d000d4001c1000d4014140c01011040700f580003412038811716010b0b142481507403282d851000b040d65a004000c0c182c1d02c944d81555204600001d101044403885903501c107026001c44581078241d904510580368003003612804240c0b5042c0c0d540343c03604c030344492500044c40c02c40c0e010300d501381d420010040706581503626403030000c14289914884006c44268606910340c0002114050184200d5019060040c425425079280741402040380a4010882c155950701c00d43e5502440301c4181e20501800c40001c1c0c51502c1200540c8071141e9001c07030000c005000301c1c00e0032010244044a058007013000c0c2103060b00c880001408802d01180c141c02580e28100829001c210f0300400341c030514001010344a9a0314040040081f000c0f00310744141562001040030601e03450740c0c00c04581014226048403201c4c00c1052001c80c505400050b0b55040700e1066401c8030718440803070100003c4400300300f074121080704c11000d81c601600543c0e0207594403181400f4600e00340a04080452880c4800c1a001c550b01017064 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 491315800 1250 491314550 491314561
    0xc0504120c050a12050a08160209011415071203050408091e0f0a06140d0b120307021503071d040e07060503040506010b04030f141920040c0203091201061d 68
    0x804042d0050301d07500c428182c02c4c0503280d88481d43d9000c0000040e00c6034101007140000984201582202543c0007801c5800c0b5584801a01c80181400440d8910608480c0001d80041d0103071026034020b0b0b0b401c1004e0760206141d409095025180090080b00c40c500200102083d580e103040a000310045841c032500c0b40e0104841c2072110040184450920076441c5041c2001800da1060b00c0f102001d01003186103840c0c41c005a080c40181003440c0b81240d020002c4445a04403d00002c090400d4034005c554009100b9a4000ea09081c0e00c016914040014107003207e605d4910420700d965500400c0181000848028040e18a07042040c140c01c1800010700000900003880420028107014121a29085103090b141d5a1104501c204402c402403c072002040b02d640944410b2041d41c140118041c80001c1d22689442d010b0041052500e00c24048190440340b41c400d42000c0c0b1405030b4076001600103610700302c6480704001407002602501d003540e43d00c8210205c2c1004280a5510116803d542441503c0c00c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 491317050 1250 491315800 491315809
    0x4050405100e0106080d230c0a030216060c1113020409150506090a050d080706020d02070311070e01170715020a120305060f04020309030d0e03040503010c0206060a090c0504120c05 79
    0x3508282c0c4a00d84c1040c0080c041080b0100d00301c403410380d017030501080c006c2d4145207030f440b100d440c000c0422030110702142000c11054081408010180b0a90950b00d51101d110082814020700d4061200001e0002401c0000a14906021007110000816014100140304030f10300076a40030750003007110180c85510302c01035003040c2d68130400505400c40324542800c0f0a100890007024070352058034481c514000e5080b0900c00c07440c084419176034002000b550380d40d01b11444000a54014035040340000c42d03070164160624004229203095600c900c0d01c940c0f00364030300155000c424a0444aa2800c0c2c020000000384415a03030042c40700030a039940280c0419401410183c41040020103d030050505210030031610b503a81c100c200c007c2e610b0440c0c0068032500c1c0c2060452860003103003101207005142171096a80c80720000083e00480d80110000d12182d00e254004a8071403034151605a003100050030148200d04050f004100d0490b9145001360405035660130300b070035081e41090f06543c0803101200a001d6402c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 491318300 1250 491317050 491317061
    0x90907030e0c0d080d05100905010603091502070201020604060f0e010614011701080601050411070209040b09071202090c0a18270c05070b06040f021c1808070f0c03020405040510 78
    0x81203c0104031054191500e10b050300c02c1078069684990b442d0001003044116480c21000350008480811156840303400140007003d034a4404e8480c1e05440b200c803001b4270000d0080b514480ea044e030103440180c4440d600c4c0400b500c205944120002e4440f10340385450f4600348508070040c140e0b1882840c00079458400503103c460240c40704908003a4440051110704800036903541104c0e010703280003510f10890072484009004402c0002c2d8029a000280418041000c0c2200d00402c00042901e0b01d0656074520504580321062009400c00c0e01c0ca80024000c11141001d001007410605112091032000700000902c100c4940040e118092484043c102611554410404010802004000c0600300d440040e01c1030248281c014900f0f0288030004049031101d402040311504220000d545801e241104512044105091038024134500f0031103000308000300c0c0041c00c0041d002600c1d14542041038a458141c0001413a0944400d44002130020060b11741e8400c0e54452405400500804450074a60600b2341c3d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 491319550 1250 491318300 491318323
    0x60f061315082202012618061501031e110c070503160b132c091b10020f03030c04080c100f0e01110d03140708011503050c090907030e 59
    0x16a440801019244680064403040003c0100100d0000e191004032890702d1010400f040983c95100d103c41e1800101c00b2003030103548038003039a60075424003003200b40e81c0d034500b11024210100346405000c0203500951022230340c4050203941d0f90000d22100c0104c411756041d441c904901480000307021034500800e02a010150a0440140103501000903a210076283d150041c805080000244040304401c01c1010f0300040100e290212005030f4028183e030b800b80b05040a040c0d2040003500019250302d0089511402a52a22000d0408503420814001c1c40c00400b407000b002d510583d0729100c04c8120800143d4032076840c18034125548c07410010250b04003089800070740d000364803902100d02d9258104a0441c40366241d45071040c3e4030b0b00300c0001200c00100140c00c0c441c403401108008034036260b00d40c20048060380748030010103d5444841c41195004001d21600600000c8014489180e82c0300b0b410480c0c0215658a901e4100032800c00024504001038032898040f980d1800314803000c41d01800f002c02c284 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 491320800 1250 491319550 491319557
    0xa020a170403030203040b09041d1c0810091508030310090b04020901120b0a030f20120d030f0207080c0a1712040f020a03080d060602070f05031005060f061315 70
    0x10324503500139590340290f0141c15841c0700d021401603610b4855600052036141c0d2417080c035428000602c483c90311191015030111000801c250320f941a64094840c2a000d2076082003a01030092520b09004002c00301e14004007030070600c003440054105420800345010303008075801104228a0300c0c030030717004840c850300c0c0c102d0049005010048580e070300050010200208060041400b81640e0700069500e541600014155805944040d0501c0a41501c103801e10450600c07085c10968550100301310a0501d40e0751180a510030642c80085a102c0c5d0007156020100f480090300380312803555041c845400842410303055034400c00101003484070311218201480e280303942580c80d000c03000c0601110440000e20243ca00d0410b8400b0000715240d20400074010740d08440401d4403a0940001003000e4002407140342d0041c415034502284900c951207941081b148000d000f405c0109180701401d0240400034003441e8032520803a00e440150702c501c03000700041c80e0700ca203000406504000c03010031704415428910041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 491322050 1250 491320800 491320807
    0x10314040f0f02060c01060e06040e010e0a0303020708090d06090309090b0d0209130605100f08070b1801030f0f06032603010605161217070c11120c060a020a17 70
    0x318201c14018400705400441c485403240c0240045040b503c2400c030f64001c198a0504009000c50001141d00d0058504a0b8140300c07004c070b40d501140c2030b51010480841590080010540083d0082d8002d0000364407603c071590420244200261038070071402d0090b68001e498964050800d548443d040c40070380002c07502004950400000300c3c40502440030000d002d0aa42030100d2103a0b19501407002c4820fa2140061000380f40c0400d80d81c3c41164548540451101d8031070012420f480003150000c240c0f100f00c9061801d10f81010140301403910b043c101c1505140d40c809034491901c01324091001406514a00450b417940b55282c40e011200e5200c42c036500100c102003104d04000455400c43c1d0440da02d07450b020b44c40b02d44400d41c40d80d84100030321005000740116113007050071640068070141c00c80803004c010921985c0e902c200707071103a9085040007021610070030f4100205240a8a180c050100841c040b02d8003990204089915039025200400c0507900c0032042c182006148140249805080840e0504 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 491323300 1250 491322050 491322053
    0xc190602101406130f05040c0503280816020306090105070207060c0f03050a050d060f0501090503011a01110c040504080306040c0c03080105040c0c050d0314090705090c030406110f0901031404 84
    0x2d20300b10191040380700d000b21000743c0d00a10100c1e00300015281c0054801c110a0400d850449404c2004d0303c1828001d000e041c02602ca140c0040040b01d0007400300c2d44800da084482a0b031045410391080f0100350f90310080c001c509016803420070550344140e280784000661414503000107840c1c800158030940130807407c1c0301a000040c541d210080901c03541800c2081d241c0c044490300369614050b1a0710741000c0c9240c05000100301d800c02c82e001e4100c40081e201c00700101e40312014142655061400c408a0070130221109003554450500c0350b03800e103520015102c004141d01c000806462094500303070b03452007010081c03158610340b0340309a80e82c1c0003a5040c0182090700c3c039a0041d008080501c41c0510445d1340b00b01500c1498000c00c908408568041c0603503034000c0c1507810241c02444c402481d0490804402d0016a10607000070b0440140c0e03000030540186903603402c075000403583c401001107407115110618090322010090140101400303807401541c40302d040d40001012204182055000c0c451210103010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 491324550 1250 491323300 491323331
    0x12020d0219031b050c09040f1203020f120604180606050301110309150903040f06050c060a18020f03010b311b050a0c02100c0309050603070816020c19060210 69
    0x2d08100f1462402c200c4408182041c60a020007018001c0d041503000081204000503004024003203849844c443c2c1d4100d044200403000c0780034251040021a1013000160050040750304501e9100e0002480440d0641070210555410840c14404403645601e45100748880c2c507081c020303450702141e242907046c218500741c2e825550790041e0000d8044007a50342c00101e13500d0340080c011a00541030041d030100c03000d130362808020420b9029101c485090f000e074901261208515000b0000002088000003100002c130340c08020741150b44003003007640341d035942a640c2d0f1281c40e4920310307a01034042e62110700440c08248224083e041102204c40c03030b100b494071059803941100d030352103810b090155140190315461040c10565406008002c00b0794400c540c02000030030290b001c68800d8440e440f03540d0382180295600f0074440140130548650001c96140400220030704100e0905030440d0380c0a1040b19410a004d1011404020390619285121040c80d00d0a01035190104140c4050090340c00040080c04a132a2190 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 491325800 1250 491324550 491324567
    0xf030409020d050906040b24100f0f080108030405060921060910051e060d0c0b0409110705070311060f030106030204030b0609100302091021110a03030801030b0406020712020d021903 80
    0x1585008003000b1900319600c494040b81c0c80c0c4c1102a006c00c101c8404007100ac1d01c031507007030608100000e00c4170f00840c0308184a490014100c6120900440c00c1905280c100801d0741c01030751050350014050b24400310a8004182c0140704891680c020703064600304902803504103023290303611b11100790a10051100c81c1d50300b800c180500d88104101201c05031181000900d0410112038050a103100c441c0000c16600744090007082103800c3c1110070000c04846c0b031420140d41c02205806440368108100c100042001c203066580031b154010981d51600740e041c529424070b07030000c0e0000c80019901180030b00410055044003500b003a0115140c0300d032803811400d030350184c84542c04028080c504510124082038840c4907102c01030b080d1044c2c51052281d00380e554007020741e0400020340e5440c0c5a15451491030074840d2510082d030341c00d583c60400d103a0940d142c0028500d4081e204403a40c50f0300300420b001140d4001e002c0c0607504a564080c040d1249801070092400a4001074030300000d607643c1c9042c0010b60003540a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 491327050 1250 491325800 491325811
    0x1d010e0708011a09030a0506010501090f081c11030705011401050105040e070e0120060f0703110d090302030d0c03020a090b04230a091803020d050322050f030409020d050906040b 78
    0x40720340701520300f081c9140c902490349800d80510800c01c000707040050209406040e01c9007a038981e030210303668829803a14080144100e40254115140090000d000c881c074a100444050401a914052a1405030720350f510550060340c075039559030f9031101164a0b00700e00350b00501003468250304090400c1203030a02c03908044e024109000d500304408413544d004170302d036480b4482c3c600c4840705450740c0c06a482ea2a41030450713940b00700743c48182c00900218020b10840325055000480d6030700f8a01000b91110003000340c101c3c250250300c400d00c0710110000307240c01f03550440340c80c035980580c80303034600c910140014005801c48103800c041400240301d0308280c2044100c060154201c080d1480c0400004641040b90b02c5d000107215030f040081082403241d554200403036283c0300790308a402d00c3c134245801301c1d00b900058a9a1019085960840003d06082000c1d400564080e5040d079000d002070749909442d5902a0b8848c014035500800d900c2034803240e61145980c40500c00c03003d82150318042c0e4601c801003400804 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 491328300 1250 491327050 491327069
    0x7150f0c0302101b12020315100c050607110d0e0619051e0316020c0f0105030c21010503010b010e09130507080109050303060909010e0d050f131d010e070801 69
    0xc1103040c14400c0101c83d6922944603420082140b4150740000300741240011078000c6150400d4040e03c0724410302c2124460380701c10b503810050201b040d0400480140c051000c40c01c00c45d000c0e0345080412000d11100c0e0081c51151031b002241010824600d0621016171000400d0101c5a43c112402d900c4070002c6400c68034900c03591948406000c00b049e01c040c0a46160031810703105204003440750240e1000118003034112019404585483d00d9001ca0765880544000c80c1c008018820342074280d40280302840d044600240000d051807034809201012040c400701c2e2484003030fa2200100228102072003a00c060320310a207000801c803900c0d075020460344840a000740d91a00c1c5038070f03621424000180490b2016081481c02840300142c1410540e689820955080e0310440b0282d0100b00c1c0d5100c14810300c000c907019170000d00841c0c00302d5001a11a500110004110090108050004950740300980c201500100d03000c0c0d07064600e004039081c86160b058001d032018500e8981801711845e001050103045400c03410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 491329550 1250 491328300 491328317
    0x1030b091e06070207050a15230c010b0906030d170907030203060103081210060f18150903061506231e070516050105120915090303010807150f 63
    0x40c514a48030181000e8084049882035106001d840420054054907880d0700721111203844004101e80800c0900c41c02d061071b0b03514110545214011181070040d8182c1c540e00407911608410005540d42c400c41003495981d6503092891041d240400520344c00038002d500a0284da1440800900440c03942a82c450070a20040000b8035004400c20205002d10350141c181c941959682c030303029485070419050044808800d4000400c0e0003500041c0d4003c43d40349070360781407142900400175182e0060342441d08400000454010506880300a4040b00086c801d03913406010780c1c42c608100c000c441074003142c0190a40040400c10000794460801000d80c2d80c0c04010380c40c0101c00c50021506c80c0300d07044005528031000c06903910001d808801a0021600410a54032005240810721302d40840f2401400d002c0359081c021001c821040101e11035001d0b402c10304841020603909103c41c08040300b1180c200590b4030010045c04940710521140008203001501c00b5240707404610040d0030030304600e01580c00c109209 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 491330800 1250 491329550 491329561
    0x4120215250512190909020a051611040c0e0316030f0210031b2c010801090b0406050603090c120d0903020d2103061403030301140402211005151201030b 67
    0xa0040d602024584410107a44082d130b003018008015a85100340d002c9082401c0014020016008682c000d44166070340034034200e40041e6400d00c200380c0c0441980c03400075401e4840c0b01a00d81d845070300e132495169180e00b03490075111400c05240c0481040040d4221000758400c10010310020302c1c034441c0c1c0342c0c1110491903003500180220000c6c107094003443c40c440d0300d0b001840b0540e038000c10800c1208104020307881d84162541c07c0e820500c8283c42c8030368001151070004200142150f80f100c54410001000411420390b903d001a500750002c0d070300e1080355008200360030650301e440c0080c0e2045c1030703400300030380100d0b0b040300405041076050b8803001e0f0040e02c0d240d042c1c4040040070000898400e001c201d04032250400d1a00040042820740950410315196200c8820180781c000152412200b4120140140104030810b1201079080320381201d0701021031042c034103c0d20380c41c811400e00c95605254095011450071003040020001442c0c411030420341000300300910441d1003011415203403c10301c0c40316182c030358 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 491332050 1250 491330800 491330803
    0x60203130506010311090106181403030f0408060717010e0f1005040c0c03021209132007150b0d1110091703030405010b1f08040204060308041202152505 67
    0xa10380186603008440011042181a2040050044007620322070626a01c403081503d00b0000e10940b0400d401070b9040800181c3c4203603002e0071000d5000f80660303060848441c4510460342081c5c20a01d000d4125000b0014241d0784142c0d000d00b8003801e80c1d020740300c075490f284020001ca68054500840d00d40c50600180c01a40c90111a900a10f40500b04118141605000503e43c010640c3e04600500401b80d10444084602d026502c201200918030311600e0203110454004101e4121354040705d406201c180e403404134050000e001e129001d541100210f0708203401513001c884410849074419507a074921513002c01e65038604002c03007082c203071585401044683c0080d030308403010f54041006002001c08038840d40b02d010020b14080c512a00003405000a00030405c04586181a051103001e0405820020681e00c40c610076a0000d001038400600c0380d4403500c6003040c1d5442904607441e100700b01c4610307004505000c02c500e8400075100701a1403d010074815001d1845d2210241c5000450300c203502403040c042c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 491333300 1250 491332050 491332081
    0x160206040e0405010905010506122e0507111002071101111c1214010803090105220f08061e06040b0301021207090f0f0503030d0507020a1a161b060203 66
    0x240c980e0311200d0b142c545000c501801035107000300c2c2c0c43d50078400403070488e050044502c10500110806007103d0704403203281c4410040060792021420201111185d00c03201c0c3d600c6118000d03805603440b5800f2105079581146480208800440114810040c50000c18501010300201c0300302480e0080403d400200d000c1d1030910100c003440010038242600e60180345e00041c2c0710f10881d4a140042c009407490560b940c41c03800d030910803420316410030091103015601c608020000c002c54050300c407000c18000d030a541401790164000d04001d50b4212406d02489100b0054035a00c0b015000d5042c2d021742ca03a16120040c0a4082d0015004580381c511049003545d007034040c3c46d402c0143c00c000b01740ba1b01e80908001d2544500d4418010500c2d0380403400b00c1d0300074140400741c0c29604081d00546ca00403030103c1160040c03c0c0186514114000d807260000021442d40c00c2800100c0c801038070762100d0514050f50140c0d10140031a0505003c00140a41d9103060040440500d10750400700058a96583c1910005c3c882ca = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 491334550 1250 491333300 491333309
    0x601020f2509050105060912030c0f031b010209010207090e010b04020319060806010e13060902190905101d0903120a0608060c0705190c090212061c0816020604 70
    0x1078500c81e51403080da9407612502580001c103280032166070348040008581c028018150054420400d4544605020311045007000d14401140d14041c103c1c0186410110031015503e410707000080c610044007143c003000c01030400c81000842c5080300c10400031f5907070101d41c03280000303a5407034508c002c003280402e6000c480c00c80700180c0195684d1400040c44032011034010b1840e0566850301001145a03140040d1042c16100701040305551511007144071408840203407021070b0714a40303810340c0500584500b03549044480002d070118850f1400c2803070540603214004c221500d80420280e0401c08064154061910000d1160150b1255140c1207065410740c404c2240c840c40c400d1003d000d20440c120f407039014504488505050303480c60344a0701c20b40384180c4140480506558444000c0d043c3c9a40004800c4955a1050001080d8565140c944100f643c00c100d289a00e045003c808000c07042c200360503088143c6100000c8214540e000d0f80d0744402900443e50503054209224a00b14119200d00c01240d010b003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 491335800 1250 491334550 491334553
    0xd17040b090708070609230a18060315050f0105010311070f0503040f0315060e04030c080904060512030a09080f0307120c02060d020d140108100e0c041406120d0203030c030601020f 79
    0x9170380312030b40a46441d800d407180c40540701d11120740b542c40e4604a118021001c00040003911070624052160910f407414104028080d40c0c0d0f140000000750b005811300c803400c0b41a00003c03c0c98600300080700c0c02c9030b205138000c0c1c0c185403c24441c0b507455003004046560195002164242c0c041003030401c80d00c0e60090750130a810300e111036030000c400d0144d80c08902e80c1030388081400b070003015241c600a501c001d6080c0c0e002800300300c58204a00005d6800c4001d006091005000014101d0f528400140b4000140342441e089130000909a4851039102258034042c020700c230018440d0a10102c03070b0380c0c3e89103c1c00c400901403480d800c040d07850f101c1c89400c1032500303d50010140c40d29004410910002540400850003807517103400d0300e0540d030340303101900702d812110940040c080d0b000180c00594003030400d0900e000d4036402200e810018a9a591050924600002550030081c1c50070702c1c240180c107881100320249941c8000309031074540b80e0020131681c2c400c449004103900c80e101c0c0c40060303180c0610f11000c041e10307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 491337050 1250 491335800 491335813
    0x11120607121b05040f15050a110c191401020a0f030e01021504050601061d010c0308100906030c0602012304110a0302090a0c03050a0e03070b0c160f0201020d17040b090708 75
    0xb803552180182c026110040b100e200b10039a0b0340140030ba084440440e40000c9079081c04907443d8680140115101070b8440c4050702c0346461108000780340e141c050900c42400c90385004085c0403a1150070b80c00c0000303020030300003011505420b4940c407007961815a001001c202a00003603082c00e0340b0a101c10b566508080145144d81d040a14001d501d48200f4007419001179442045000340444011000081403010784900c5400c40050f2011200c0d100002c0522444011506c000980400c080c402c40000718040c1040103440c5041c81002030a580407005159540390302c424451050240c0ca02c03030310380c205034001c0351a5080310211010800d80070455001030b5128102008029109801d504280701140c100c1d60300700480d41d03404005604441744a5001000d80c1c0c0103000c00c90000390b600e40d216802c41c482e0303021981003250034845c5507020300c001c2d4001c85e110030082d40719038211b5030100003c54000c10ba0341401c00f4041400004c50618180080c405000d036100340e800f2440a901c2845120301500014055442 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 491338300 1250 491337050 491337101
    0x40305061513050712150512031c0c0915021c050a031b09300309080c04050609060d02010311130503060f2206060509040b041112060712 60
    0x110a00203101072400b8540314003440c0106486480fa8030704c14401030301c0e008140008164008010412913042c03624000011001185031743d241b44840304c58102c0c000c0115503038a80408070b91034400500c54001e841a0601c10b0b0512819003101840040d101d01522409000010a408900c0c10b000b02900c8000500030101e0a200198030400038030509001c1d860a0003907419843e402440106803c0c619400500c0c2c4603410b001031040302010111400402d00b144109210850940030880742c0c2c02d1045021603000241049800c506000c92104644119000c00181c07601d1404901080350081290748160054a004001c42e80070794400004084400101d5894000c401880d0804030040e006451192040701c0000320301803840760001d442141402c41d214800e10030556408121904040103d4080340c0784c030303400f007666110568203e21642c01544411102e00f0142803840309405541c0320745001303a8a0f282c6030510103c002404a80229003850070116202c00c043c03400340104148441156410b4130f00e00d0021 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 491339550 1250 491338300 491338321
    0xc060c0a06021b0c0315181204090c11010603030207052211030a11093d0302040911090d020f040b0405010311010810082503060e0604030e0d080301090f0204030506 72
    0x5940c03a42c440f048440c040c00c060304141e600c002000710201956078400010302c6c1c10300c07101030160306041140200c42616007900c9000c001c0360803035040300001c1170b03076140c03c2c0d01500c0d400310104007504140d0000300b040d02e05580340251035411500440f0f0242e00511041740d1405171060554200c90641c003002c0149180b01d2080003080e03842a00d40c01e50003070900040d001d00c4207001c2d04407001c07008001c007005000170f00400c0d0860a02c2c0658000b20400004140c407029588141850110011303076594010381d0b5074102465281244d003505c02d08160700360188991b0303401e0b2b1203500c406244590104c800c0d804100c809030004029214280f4150b4109040100010030400c41960003a241e80003600c406c04150344409a4a06141103486041c429034410304090414030800808807801d010705111000c00f4036106c4d15010182c0381d102818001d0343d482002007000f4150709c00441b00c840038040b66112401c11042e240c5010900040c0070341c41e517080d551f075151011448143d040328002c40d1f000058901c649170004042 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 491340800 1250 491339550 491339587
    0x9050c040e0a0b04051506070210030e03071a010608010510080a0b0a12060b090610051c0e240c040504111608040f080102070c0902070c03051b01031401080c060c0a0602 74
    0x100c0c05a0701702030101d44c00340c2d02c03071b0791819031a00090201414014a40c0070800f0080440011005259448200601a100a10090000d10f001303200c0240d410f801803c00c24800c007016031041007000304000c014030903640c0d0403400a06110f241c2ca0090030340d844070036980b401008441c643c19480003c0b04000641003a80103041c641c00750060504000600f03d00c4240718108908490b0241e2040149069601d0580294098034042210f05407001103114640381c4201112043d801c4811558010704072100f51150100445000c001210082056814103c5031084a0f008500038203200d0b07030301d5040b034901c00c012140a541d6904160400b684929136141050710744c0c2e5210380142074a0346e12000010032505c60500032254a07980c41040c22600e140780201c400000d400030242118949503001c00000414001c005200b10103011840e6410a0061071001604842c0100c5a610042d6101340042101070700c08507040c0d91244082e01c004d03035140c003520b1400c0d080001c0810018480d40c408222040c0e40c20441d50038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 491342050 1250 491340800 491340821
    0x40305120612031614060601021f02071a15040b03061b0708040e01170114010302040c03020c0105010b0c010b030601080a14030f220501180302010e0a030b040f0b0709080709050c040e0a 81
    0xe5451400b040311049440f07002c200d90480c00b5900249001e604204140c041100440e40c840d001400c06c2633a47d201403c1c2c5600b01812445020804140000c0071800101301c00301c030318222810420001c0c08004280c90789001800326030440f0800211a164417104000c07101c1881d480112941d441d6100c10001015480c01e0003000b068010b05c40f20211504014450805840000e0300010590303861035003044003030311440038940100350b000d21401102e600c0900070316001e410b411034407035204c40e442c0c10034500f183c4440500503c03d070f000100400068a011034031a81080c0c000151040440e100c0500c1880c5200e800c3c0404441500028000d0303001b00440581c401c0100d0401011014a0b515001100c105041d20180220550214003c200541c0140c0c41c4808201c0060540254969262202c000e46c0000700d030182c62042c501500303031040040f100711641d0300010b14105441600c0c1400592a035a040301e001d0805503130380d9031002c6800c028100e0152401050010f840b0481881c04000c0740e8050034034080b9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 491343300 1250 491342050 491342063
    0x20409062003040302250504020c0f0c1c0b0622061d01080c130b1c111f0806040f0501081006080106150507021c0311150403051206120316 61
    0x800d05400365041c81164011501a40148070328440149100000000d01101c0100381900d00d500041584880c000351440584070700103008609445550103080002051085204540c0341180505000c000420b866882c0d8020074540c0a0340c0c0c4401c08981c00f40c1d804199506968450381441842003000e402c448151010b46407c4a00c1411100b84852400801e0080003a580c0090380e5188030ba081c0103034520801001c801000c61100c2c50500402c00001400202d008060804130303010301805a8200c05602e055020340340100d22072402c03000c0140100c03610700d0040400c140700c00440c2981c0c1d1141c1044040520040c03003003080c3d50792020340d02c0d95000758044a80035103040220000307070f008061280360f040740c030901c4038504c043c0c0030a602100d80380d00c8140102e0b4051400e40e10b200a00c80700d914000c0c4641e2084c0c135150400c1c000f400383c02e460a80d40e10030304401e04019104000c0003980c05000d8074a11b03107542c04c810b10141c4800000801d54001841c41c1d020381c0c4008079051b03a25100c00312415518138010781 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 491344550 1250 491343300 491343341
    0x30c0602070602030909011202011403181c0c0201080721020304201005070305130b0717130302060904020705010c1d180103260a0c02092a03100302040906 68
    0x601a6241e0244081442d440b00a03a00100203448c400d19050400501c14074000c0c0b1492801c800e00d0350140c00940344000800c023440001c0e42120400c02405426010402c3e04203d09010100018070154811b04002d0402c011400444c81d501d024550400c8146c500140550b03200b480d05200c40000c0d00207c406807001041142000401d0003000156080000090100203000c1581c12098515038841b07a01241000800c000d030100e01c64a204100e005440084926a9210340e5800c0c641d5002d182d015920100500400021604440700c11001049950590300551a08034820014000703000d50b00000d030041d400c000e204400260310a14880c4100b08680e240c0111000c40814015015500041140c0500c0030070010b01c007140c10003a412208800300041540c4040100500d46110b4000411540101d8880441c4c0e03411841d0503085164058841c08484a094000b02526151030108140b0441c000c82e0010215452400301950030000c0c54020740203106003107007441c10300003e00702c0f0aa01041c072480c41 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 491345800 1250 491344550 491344559
    0x102070302010203041a060a0b0a11100905070b1201061b0b1915031502070f0f0803190c051902072606070f0f0e01031407080702010c05210901020405040501030c060207 74
    0x81087c0161009016844001e060500840d181c2c1d100c9600b40092180c4003600c40000c0404100550084100e580003080d803000620f49185004401c0c1c1165001d140d0510100050b52300e07124000d81161454500442d46a24040204c1d91030016090042e00c115038003010481807034403201c0d4901000c201c40b1002c000001c0012584a0000458040200b40c180181540342481e04290050900c0178050211900e0102441d5580f00b500409100101d554050110400042c01d815150581c403181e07448005115490000000804500c0781c3d0b182901400381038000d030505c41c0d10800604004d0100340d002407605101d8414503039022880f030300b51484c182c8100000149000d120782c42e103071a51101034660040325a0300c0202922418142c1800314100b40c1c1e100008a140c0700c0d401c0311540240b5490310340c04003500381010004d00b900c03c0b4401c030005000c2c0070852145503440d110210302c3c2d07900b0b411030103e00c80e484145110380039104940c846c0340d107e42001700100500011040f8181140e0a54080314042940c8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 491347050 1250 491345800 491345843
    0x1309110102061b0f1b0d080a0f051e19020f040503010b04060506040e090127050609010c050901051308031305090106090e01050607050f0a050c01110c030726010207030201020304 78
    0xb00103050940c0c08050001118403600000608043d800c040c4201d000300c5c0b25021041d00d005041452440081d061f078040c010000080e105e0008065100c40060145144c844901c2d44000040100c5042040e100c0d0300148400059031401000d01c0d10303044056545040950317076071065070003c1c05038134820751a00048095030302c0d00b4441c100440da00507204500f05494221141d02a020081c606e64903035494011410300800103640190a001d44ca10107210b5950321410110724040d001230092003240e2400c01481056030b003210988203114024640155075000c0d40e801d40505d00c0090740501964480880c03444614130900c40c10101340e0f24117907284002c903039840034104c0d00c0180300e10820410383c13030100c014016801d06200a1407603a0090040303c52003440f006401c0d1815481d80c1040d034036174011405041642d0703400340520048a014100400111624800280d00c542c0e05210704a01003141482c032040d060014204c148500c08080000c640313428140c1000390207548101c800b21808500b030815480e16500c0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 491348300 1250 491347050 491347081
    0x140102101401082a06030709090c05070326150105070506040c062319270807060518040c0201060f0605040305070f0305101e092015030403030b130911010206 69
    0x1e0001c43d01e2604070785482842400c0e0306c058050000c0200d10040030803071a00c680294400381040d5175403166540103070704000307000058a884901d00c40c4003201c02c0c00c800c41405c0c104103400000916284500211302d20040c0c4242c4200700b0f004009029240810081c4100d9035031100031520b01b92a00702e08079180f680c0440d0032805c000800034801030280800c2c11014140855400201c40504000c10454510070703e40122100c00c0740c511841c10f64120040c40400009c0c4903840003000d0070709145040c1300c00d400c1c2d6030b403841d045011064021a60303618801c0c5070078400d410000040c05a84d20204413203440c5d0304018800c0d4400d02041d129841140300004015480d8104141113a8001e4050b082c401d5440000c1406008280d40a051105144410503010701c410710610800520545500d0214890700726807408030511000c00b584503000460321418207240f590120790744140d0500d00000c0b8440f05c00f00041c030307200124011120f02460a100e40d810446500b0307103070719444002d27001c880c01903481c2290100c0104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 491349550 1250 491348300 491348353
    0x503061c05070618090f0b1002240a020702041d01060510080c030703140c040801060f031113090b0a0b011b05030a030c03060b0d061a07050714010210140108 69
    0x107029800030840d4600ca039201840e0711508205035100c0785d40c0c90345800f043e1441640c410750703000d590b98a040c0640c03074402c11610040109001038805000f944900c200e0310080b00350030301c444011200c0001c04040c003940c1250a10799000b40200300c0f80b2210008d22046110440300300c9590342c603201d80801c061408111969040300c3c0c56540840c0ca5a80041070022030f0005002c0e002415103d00001d00b220000a40440c030030541d02c203000e520b480c43c21020703e09450459202c8154201512018400304501100c80d281c00d98042d108100d040c460304d0549001000e1041d40548080580001d1013805401c0f90001c0c40c220302c3c241c1e6401038008200240034905908101d004000b94010080c000c04036029401c40d00d008046800e00050282e1384a080b130340705134042c0140d05409966098144099242c5800150341c0106640d0000e05100b4035a031a070b941c52a0754011800340d0000d40e03c1a070801d0f0f108004803108122460001e000f011a200c1d040c029215007030060327004a008102840d0000d4940030014020030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 491350800 1250 491349550 491349553
    0x30907060914090c0d09060603051f020c0c0409080712031409011a01180e0406090c1509060302030c16120914060301091d160e060a0605090415080d0503061c05 70
    0x151541007820201c5d0740302081c144103491321403228034085031045c8504402036009401400c03103041030b420803e4800e0a080100c11100b441801a043c0800340000c0200c8c0303821003540c00054802d010b040044079401071034402080f0f904090900d04a45505820414a0a01124909840740c41308d2031818203803003104103000e0001c3c0172248070b06440d601c548450701d10002c42500c100411501e401ba0700e500210215001d60701140c40e4101c8200b04100c031207400303000b4044942074145100d010340006107000034501c580410560088049a104542d410032512464194030300420300054600d0b1a490310044018404080342e94404001440c1044841000501c00000d006500d16070070700c00d11100406110f0440f942d20b10f03075400da42004200030488004800311030103030350410fa071405040005455004150f0b03801501800000c10582ea00002910340b01941203a001c0382c2404103044411310305180b0340c00f080451203900c15003c84940c0000c010360094409440c1c0f020401c11900c00c3e0400150140c0000f841d0707 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 491352050 1250 491350800 491350819
    0x103060302091302120a0f1a041a0a1b020d020c030105130f0f02030303190c0e09010b09010c0203030f120f010f0b0a0e030123093708030907060914 65
    0x100e520110103e28000d01c01007a01d410401c06015a074035103d0b14030700440d20385d10341c80d20020a00c80c4c0360110350800100c0340c0300c0d911713075207060f541d0101c880c01441c1d048410040c0e55004518071900030f0f00092412840e880b0400510000342c04025514900b042c40400940030380b5107484418181802414410b031944010b08100c25000d6a03180040443d0300e03019a4048000181400141e900344001c40c091109901d01141105a070f9105200b140c0900e03180d04144003103000e60fa40036489201c621411a480b10702015142d0001c0401a9204c22074041c00940c180400250044a255518050140d5100c0205005801c0c4e4903030882c0d000880c028043d211420700c50310410080891640d00a182c030034490700c3c1c0040448011008682514080c07031505c2a0400081c2d0f1000f01006010001588014170030028504402040c140009400601203051460612022000043c203402e1164146a66210060340e40d2860403100c40c82e1280a28020000003402c0c0600c0041c0c10034500e51035000c260b6000742482c28 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 491353300 1250 491352050 491352061
    0xe0d0e041b08130f0218010518010303020c0d050f060103060203091204081507090308041202040b06090a0504051e01030b07080c180105090f0913120207060e0f041407030603060b010306030209 84
    0x4110f0030b00200b1a01d90884140f0480185c882c8040c510b00c680d4100810805941040104240407907950080d40f20b58a00b000108007080e40080c4000d40003000f41ca0491450030a801c203130781031030404180c4000c075200d4440000208032245e402144500795110589901c49030b0701c6900c182034400c2d4400d0300a00d0740300303403c94000d0259401030680c118a03e4202880426681ea54080c030b5074209034030228404e260751849400350309107030141c01501c0300200c135910300d0f00c4640c00024244481a0140720300560380c4800081a6040200003040184110310100c017066030340346056a8043c000300d9901000411800106a00414010503101c42e2582c650040308000384c550300447c1d06800414809901440c8841c480100d92a88400c2900031152201210013494040c14002d05412401c0d05440441d4031800b8104401940010b0510065000725001c602c1c1410b030000050282494500c14a44802001c040c0410240c056008508036841000c040c084440324000640407913a1510000e50840c040000140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 491354550 1250 491353300 491353321
    0x21309050a02040635010209031c081501050d05040302120c0303041424060a03120e030d05210603010b0925050403120f180909140714060d0e0d0e041b08 67
    0x1941700090b540010b081803400c0380000e1801001d40c005000491504540d90641e41c0d0107404650300ca40702c0c001983c00881ca02c40000c003103209074000116800d0b958004034007014824020b0f880e0382030310200c100303440d1841b5801d01c50f16a44207503130459103501c0f0b0000c0904450070200b441c443e1002c4441d04038003009818600d01d000705000a108603880800030b507002c8000703402005408800000c941d20203990040103070500d441d02602d00491014014207018550850020b000f44044180a190b01d5640c9602c844020078050600540c0c0d01d0f81c00070401c000c0200c040c01c844008080e0385408541c468070400c11a805441900c120301014189036590484296860301418241d842c0c01890310344034040a00d000481240c0b5000398002c0039480c1d44440c50f03502400303807400300c90350030a05040240c450315150800781c61150000c5851280501004030301a60341c09082c1d401128a52241300030344e48020221003000f03164440c6480d4141c8034920304a02e0400600b0317403415244c00030080d0748502419865521024 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 491355800 1250 491354550 491354639
    0x121c051302280e07020115080d0c0305160f0c090912030c020a0c06030614061c0b060c0d0c032c012007170d020f030a0c021309050a020406 61
    0x10300702c190220b04100c15010754160300300c0145007408822200d03050803d402800c1d42c1151441c4203002441000c10b000407032021442212080381030420549128180c503003a034079402141c40c1106910303040b00c09407040c000d20410309400c0511500310000080d880340090022500d00c0800501281d28030601103500500952101386440042d004441400090356200040000c01d81c0040000030b4849000308401c04540342110880170301124014208510b20704000740003450682c40d150150b4607054907182036101c600498116507420000da034200d4800003405400c107408a00e089000032240b9494003101e81025094445400a5581f08444c81403c031004580030040d0400c2c07541e5400c1d074207400125605003007080800a00c0400d04054083c20b000c4030341c03401c0054001510056421103440e2551510001c022100b61010500304460041c8160000c103413483e9001441d46090b0b482c0400030410302c200091441408c1e1b01c21101404180e0712078142411145040c030381c4c10303134250320b450325000c41d4000f10024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 491357050 1250 491355800 491355829
    0xc081e04080313030606060f021018140606011407020d0f11040e1501060f091203090b07050c12010c0516142401060f0c060b01020708121c051302 64
    0x149420140c0310a00c0da400d690145101c4140031407100c108004100441c0664001065107050411003a20441c0d8041c5d11a0640a00c10f40fa042d038035149220148007001c2190340d003640041000b48200740440d81903036214000c0d00c106000c541800c081a410000800488441d154040c02d40c0122250300c4d5a600488078140c1d00444a0071118100c4c0212515a84146542d50382c4c42801415103016840c0400e0007100103030004030410010050198459402c500b030082200c8070100c40c0c41d822201d6040407544008150810f991034180013903070209004001034001968078048900910000e40ca0034030300d0072100002c0c802408103105102d41c200d8810034010540340b02d4010883e40c44140c81d13a50403e0709214080400081080c8040801c84004a80d030103101d001d8607250400f181801c590b200042c02c44140c0c050010403013038450f01c1c0b034043c03640b082c402c4000405000080301d0b812031034080ea81c0c40b2078201c141c07030303001c041c0070700c84162170415240c001c2c50b0044680400c00301c420a031036020b01c10201010b429 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 491358300 1250 491357050 491357107
    0x1060f0b0a110a11090a1e0b0a0e040201090302120c0303030c0d4502060d060e0901200c0a0b010e1501020a0f0305300601080a092307090204120c05010c08 68
    0x400c7c08215101c044440600910420001858800c01003040405407a51f0411034246554100300700040c1d800201d40c1062b6501102c800001e42000d02d00c651030031100054058242c040402440541092480600405030440e0000d100b0006445c0540714104441d4100c111070000c0c1000645520380e100c0560070580e001c5070a091400301854020401a90092481c2c180e00750780d40c0c0c810071a5a00396444107800c0010ba100900861028980b406a00c02602c0c1e5052402030000070400c4501008200b607010050f4400c035003005640e5a10300200c1c0110085826502036902c034459620950310200b040840c40e5401200d80424050b540c40803141e540000c0100d6050103a40c800700d00e4148001c0940141e41a00c2c1013042e64585044c0000601400c80680981d84a0b8240b40d034000c0001d1b408001141d0090b60300307024200799101072901914181065104c500c603a440020007140220000d032042c0e4000c0e00844d00c079409241d441c0011114520788000c06814108240b0415035020031034030010720011015034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 491359550 1250 491358300 491358311
    0x12130302040207081e040e04080a0e09130506010f0e01152a03030f090503030a0504030302040f1805070e0102030307030e0109080d0e0c01210e01060f0b0a110a11090a 73
    0x80c0400d0490384460003e40d80c0320307800300340c40468002911400300940910b034a002d00302481d01200308503441019000a0a1100104000200c24801ca410301c0c01048000c092035254141460008451240340c4003c0d03501d03000e0200003003000c400501e88981100c032004061401c5a1800c9000c0d04c2e4990014071180402514542003159159542c040710010000241c1a10a40031a40303006002c1329494200c2204c103d003025410b81c0880e6011054a502c4030f1058008546a59030349001c80080c4540d401c00b41103400c0080c00450b0310341015001030440c0e60180c00c04c0026440304041615141a000300c003900503801000061071f418421307000700d800702c0b01400011801810f02e03650305040d50851401e55084650fa83d1003506160020171004003600828200300d0b030030712064001740c140c0c0300ca00d00d030740c480054403646031000051003540300760002c00c155803c5201030340c1c45142407000c40e4810581c00d0300155140302010301c2c664021807800202980604d05010400b16101402003d840040c060502d003692030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 491360800 1250 491359550 491359553
    0x1020309012a200301090f12091512050c04050d150e01020d0c030f06060806010c11060a0c030f0e030601181d030a0f180e1312020606090606030405121303 68
    0x110381d003410381e1080c042000b103a8486564100c0f00d603408411144280c2c14403074541d01244c2c0300d41c0d081908903007200c14980b44401c4880c0540308840e06512034610340c1a52510825240c0e4031079108880c10300310039000d010580701d51408803068000c40c00390941c0f01e5443c604080000348413042d140e0b16851500c80100340203c1c1c12003050300b240c014a504c034031025101d16480442941c1880381c070320044002c003810000c06007400e43c0184880c0d4000c0c00581445099421074060211400a1410002c0000d220715a5803001410040c010240414110040303511844461811805081c441c1e005110260042010f0780c40c0105090391380745c4200108025990780c1380d18286a152840e801005140100c008545e40d4a094400400204c0d9841d1240c08005507080d05608025071a0030060444213014451022a00c1c0c032848084d1103d0b403d6401450840c600e0704042c09603802140a81c400c01b0101e40700003851380c4020038007c50b0b100444008144d40c10444540034480c60240140071000c10a1601d07004090300c0c1d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 491362050 1250 491360800 491360867
    0x120c1603030306030201110d02100b030c0904060b0a0803180d0f1a0108061e011404021c05040204050a0e0c010843020a05192d110f0102030901 63
    0x250410703000039880d05000d005550700b048001c0f454440010003001d010807403140094032030151404001c030740d40d110481491166005c01880381c015000802c01d03051410319140c0310000f00852903205009112000c40058485804800e40d201d02440030380d0388200c40581070800011140c3c8440490f808032404a04902060440281074202c1004401014540d41401241413034240c1c01012341c009407100111f241c0348021900d401d60b0440c1e140343c15092000d0003c1c1d00141c0030340100028403141c410701c03010018000700c040c0c01a601860003070f101000a500c80c41510401c1ea03002c01a820940d41c0311540042a0754401d1480035403180e41220035803450106c0c4004001d64a4001661121551820304150f5625001400482002c0014001090f038000b1964036262621303012185101c4206240b01c40e00207010360080941ca10b1401d0042c118503a00c8240b441c09003078143d005098034041e035096007081c5941440074001d144400160029403c004c05940119500400c030a50581828060202c5000c12000c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 491363300 1250 491362050 491362093
    0x7060e240d0603080705120306150c0102041e150e06220803030112030801090605011e050f2b11040b09060c01050901020c21031503010b0d0b0105030c010302030603120c 74
    0x4c10301c1407507a03859650410624009030349885060120082091007200d03602d242540743c02030305000307203e500d400c8643c40840c02405558806e842c140010300820003452004031250382a104503107140042c29400880c01c440085038a6066a0441c404000c4d100350102010b020b908203d20390180d641419031a031203c01d01f10b40003a40111404484040440205500040020702400010702e042000c0c516107030000f00006440440940d507100380c0005c91444c0c80c42141101c100c007420001e01595a52840c8002d9881c22150003d40b203103e0400009800d089041d0080810103115042414142800c0400c000d00319845070007c2a842601080b2203840c05d0428001e04e0b1080c041100016240e1080034212070030001a502d031003c15504c090b10741c04540300800140c94010f01209001c0c0100c0d11050003290040ca01080200d60151203000c1c1d078410001100e0603e0705841d016030640714603014110040d0103a0000380c034201c0d41600300040d0504134842c11406030410003015411a1014110141f00c4401d001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 491364550 1250 491363300 491363303
    0x2a0d0905031b0a080306091003050d0f09060e0114160b180c01090e07080403090b13150f020307020607052d2404120e03030f0c07060e240d0603 63
    0x400120310b04003008100c0b8014641210180d0260403248000c2c1e0700c4d1640c03440000c3c01588105035010201c0e818a9003554803801465019040b80c1c0303034928124004c0c000c0080d40310a4000a0444240803e0081c45031055a0042c24180c540010880211445d090340b60040718026098136018040400458500c000303ca0091107246450001c04070b184110b1424100c004105a06000c500201048641d0003050f20590101c6245440c0105487c3c0385002c441c0310440d5400400105400708441c2d904032000c0070312004644500c01034000c29014483c0c2038518110345201d9402581050000e2005401c10350300a00205209405961984200c015030404c03940c042d840c8511962800a03440c0d103005820806c0c0045499060b68120112030030314209031000600920052504845030022802113002c0c3c42303c035501a000405030b980300e0300038014014440c1c1000ca80030b0007501c10154009031090050001a40c0c511014180c17902801504600c4c40c5c00002506046c03404540420403015043d196204440155 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 491365800 1250 491364550 491364553
    0xf02040b1f0f18180b090f0a0515090412030b1e040905011b051305030a150e0a020405131109010308030f0c0c010204061e11341403152a0d0905 63
    0x41380807507540320444440541d098041d102440501c03c508040814540e40000d4100e800b081c5907981c18110340c1800e0154000540001309a018407040200100501c00c0240480e5400c005246060040018070303285500d482c1550050560382c1119800c20750413415034a400f500000c501c07013000b070340380c078a4002c0c1034a00c203030000340003007208404103103070000100041c1402c4008000c00314682e240d009160621a40039174a00f50340c1c9042c408195024444200000d400030f00c200b00030705d00b080001070541e41c80c680846484111107555022498120326250607248c0107103000341180e030f0790315000000d20405000001c10003002d10201c00c601000f4001040503040c0c1d036403a0603c001306401300c4071036500b4014808c03090103000140206030000006d1250940780c1006201c007003895071010301040b080740315036414104080c00c0380c1c04500c1a501a0328402c030080c056080740d12030211800e1000320820705841803649211070b6039031000c09240740a56004100300c3c2062284c54500c61031000c6045034036000e02100d0b103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 491366906 1106 491365800 491365829
    0x901091211030a0308010f1d0a0203130b010f0f1403120a05040302041803020d05030c0904090c0504020a18080106080303010524070f02040b1f0f18 65
    0x8400050b040d074880800504000300400e200340100442412540000156000b4008140c1480038588007400f1481d15404510b01c06507102030f10f0459902490f08189001c60b42000c0514001c0c00b00001c0c40c00c03580d1a00440d8081c540040c0d000c0e5280120200b03c0020303d46001c551580701740d401d2259195070302003112098545000e00c7d040a5001450920480b0180300002042e482842c000e40031102c0341c03140488103c0b05880111100c0300400424403084159040070b402c503001043c824007180c0002034440c4007081c126003054280c90005140b080d54903154604120006000e450000000d1181500309415955644410b1107881c0c000d00301e240c00c415118924141040d00401854a084c1ea42c07081803d10f030348018910002648600d2070204182424a4540d07411194180c401545480300d00d1500c20582d0140c280401601c180141e8080c41000010100120b00c050504640340e00301 = true := by decide +kernel

theorem cover : BRFrame.Cov 491187050 491366906 := by
  have h0 := BRFrame.cov_init 491187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 491187050 ≤ n) (h2 : n < 491366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
