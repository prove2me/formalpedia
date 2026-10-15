-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3945
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:07:51.225335+00:00
-- url     : https://prove2.me/submissions/59580317-6121-4a5c-bb39-718f3f5192c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 709352517 ≤ n < 709532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 709353767 1250 709352517 709352543
    0x8040c0b0706060f1a0d0f0e1b0f2e1107080601081c0c330b010f080601120e032a06070215010b090d0b090a03081005150c030c07090b04051311060901050702030a 71
    0x2041c103025002b861042524220f01c0f40c04c40b0545200000c291400030034801904040e281501842100e440150402c020b041d918801e5403441e166a55000c00c2c0945080c50180d82081c0c1038903034803400650300000c0c0540302c3c0001400c054440200038000300345c905030210f28455105420031952032022410ba0f0510100207964401c500004120580a02100040c00300100c188000790703800a0611411a03642c1d4808182d82080d00e2880d8218002d0300081c80070601c1e80d00c00c2031b820003045401030700803040560844085c0d58a013817040341d40704820445690003442a100520000d41c040700145444200500500261941a41c811110071000c9518090700d82000e03400c1c02c10907078090040364000722a0b08000394840d05140001c1c1c0340010009020009100000350a11029014002d84211042400540f6a016a03030480030b0003500301010214421460000083c1d40e84005295002d42c0a0f0001c9482c594004941c0a0103080c1d8840400c0c14184030b42800440c0042ea800c1103078200080c42005c03014180 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 709355017 1250 709353767 709353769
    0x7090914070e1509100519020f1c0f110321060f0303090609100212031e1f2c0a150506120708040c0b0706060f1a0d0f0e1b 54
    0x1490040081c24403d002c1000500f0301d500404081da6007148040302d094001c20f0340c0c42815140362240b0b08042841d0a0500d003440d00c40e5402050885081c901d800c140d4a00101d007006c41c450420012160300003242000c0300d1108401d1103100980a42460f50003101e10b130000300000001c12034450302c26603851109100421006040002d01c0c03004281003640154100780d94900046e49074056156801d018410700e23111281018401c102e4122020141c400c019901c0c2010848455003083d5540614500c4158502042103041c5215000d400110a100744c0d01d4a28103003410441820555040e2070080c0c0c40e5483d0396030091a1a40b500c40c09901e640f03800040c002103040b04410791100a0784802c1c403c0400b1b00018540c00712000080380d03c00800e10b48461140d56618000c134246402e07070000e000c02140401c42108012a6600c008199400008400701e0a40e8400c036042041025416802c0c0040042c0546003000005801405504100340c101240c0c000100340c0c003601e1b1042c2c0103407242c04544801012411 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 709356267 1250 709355017 709355027
    0x1014010917010e0c0a0f090509190f050610140d08090a0902120121060f020d020304050307110931080708030a0b010c020d030507060e030408151f0e0709091407 70
    0x7402d04c068400044451420745421440151846840101c545840014010400c203010801201c89890348000c40c50a850401001940b0641701c00c030365030320542022035a500440310190084884004581660440c481e082c04213650f00d90100300c404010a10050400e030313407400180409044015401070f225440500c8981c0d0900040c0d101e803090801e00d038542034441103c0c440748007059401040100740b5600e0840d111000344240525007276820300c0407007031204110300030004060b0b00e40103503080b55250801e58104010103000340c03240d0b0b0341c0c290950000d800003811001003041c0b400f61400d849074191465295045158000b440856104000008000503015181714880d5120020302e00308080705115408112001140b08025040c13117030200d0700e0001c218042d000b041003001c0410603241c075240d0300c0e0340b100c2d5603140810520304440c0c0c00000060b00c04900308001c3c001003108041180550f480d2100400c4040030240c12030f03041020814010444000c640120b00005031540203200083c0342400303005107 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 709357517 1250 709356267 709356283
    0x60a230711071a0c1e120c07080109060e010506040509060a09141c12020903120f0d060e090c090c04120201090b0703120b0f0102070315020d11030f0f1014010917010e 73
    0x501060003403240241040004201c07a41d6003640da1904d0b1f540000c0701e102403900302554800b46d020741c01e0070090030410800742c0204043c201910300905c955182c0b00d00300426070340102d40106243d4001d41c00176640419540110441d1405000d030144610f06861056003490341441c00040d24142c040d01502c01264020850625603002c01d8086092110a90000303488501111500c0000b28000c2162800b00103204221003410074079580402c000c3d643c0300c0b1621003040b02162400c000340920001010b407403d00b0801c07240b1400340c01400c40d1906003131450b132100b4052130a1041e030400098080c0805d51040c9403000345082802510382001d10301a161800b000e58042411a6018500c220844e4400380d8001616105aa078058500d185540043c3c2c01c00d00240600340a11820034100034910071030300d60660086000d844c903c0e00305e0000b0b66034119030100d0140306661000700ac07002d8003030070000105174240104c298041450800354595584281318480900c110016445035582d00d07a00c02040000c0007040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 709358767 1250 709357517 709357543
    0x405011e0602071203050319050a0f1503151d0303070c1712070f0519120501050d120c02030a06020d1e05012d030203010c02060a230711071a0c 63
    0x805503908150308114200842413004060000100202c2d40ca03004850b8094145200f0a1080040b80303000881c10020786900700704145104c0c68511150f0200340000381c044140d903080780c040d9000031210340d00701d4000c110050f450312401c03160300f81c02e40304030070103000441c040c5030700b5659070054000b00d00304209140c210b0700816007011801c1001c480510f50981000d6440011400c21480d11380074031405441c03500c900000c9414030a140c0b0f000d500010340044a060702400000c1c010812603032108240403120412500c081c00e000303a51b2000b5403040340b10315812015107201500742c4805d001c00e03a0f9070b94107980111140072503185d00c44c1c410f0306080283c400300240c0d6804440c402d125951415504502050900c071140c8101c403c60002c056901c10340000d0320006590190003000b4401241500039101ea400342c50000300030382000301025030201b520000c6c1c0c11289644901c0c04140e22100d10544070b4520004002060303016801c0300040c4110034a40d860030001c0d024040310350b15030b8008800da0510003289030302 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 709360017 1250 709358767 709358773
    0x1a311a0426040608180106170d09080115050904050c1905090702011401091802060301140111030901210e0703030801081009120c080c01051311010305090d1d0405011e0602 75
    0x401c0f040380e000c0300454011607644506030300c00d104808424094481134103c04a0f590008490a9040c0400140241c028185544150341140c44a4480e802e132440d8070581c1002d103032201c0c0c1c00d1041d8507201d03407540d400520442c00c6560118074000440c40c0d184402c8103c80c403001001c0700402c00e071f0500400843d400b6021384020426403001c00d821400244c2c040c00f5915410b513496051010002103582020102c0750014090780c0ca0b903941e112a520b0000080d20014005001c42050b21300d4040d00000351000060143c4840314402d50640c08995055102801400f0094450960340e1a0001c1840114040c50203903075801d40541c10411050700c1c1c040700d9044c0c038404601d406244c1c0c0100303014011905280c04a842c2000c4000558240131045000f2616241125444e103428001808a6400003441c06403040e09a040307001d0064006508a07036007100c5a6100350003200e00a0044d520541030046415a0400c4c1e030540a001140810101e84090b0060054440d04200c4054001101648200100030500c02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 709361267 1250 709360017 709360019
    0x714031b011407020c2b05061006091e060302090f040912080c0906032403061e0105041103060103050703020c030a030504020a0801050402060403030c021c1a311a042604 74
    0x21030600a5911102c2c0386044082d050086c01c0809a03c4070340281d80c0103000c4541900f801400b544102c0f809104110200b0880d00c40000c0c0c001074220441c01d034020340100340180c070b880c00b403054001e5802a040c1980c490312510001541d80d48500c121882c09010302074084040100c250f0140c040d00c0f0251002c8403002041c401c0c0785150390f42c141280e500501c0c003070341c8003000c0407a8110030143c4048950355075818081c3c1010401144198080351402e218184204000e990743c50707040c1310403134000440c07003154098100b0001340154065081180c000300d035850010b252080443c441741c2141c100c0084000025100d10501045d4540107007108080c0070124000c0084e0b007800e03030000d0464401e80c403000382405560f1602d00c0c2955904820003070b42c003449407058100d4402c5031904c4114151810080c001d0ba080f5580032826841d030105a544000040a00c540003c0311800c0c190038982101d9181241e034601c0101011880c4544442c40c00e020b280f14400980410101040c5002c81d0801031103400c141c8901844 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 709362517 1250 709361267 709361269
    0x30206270a031202040504020403050f0145140f1b0901120c05090a020301031b05090106110127020a06030207020612041a01080d0306060806060714031b011407020c 72
    0x10001d00403a410300341000c9501030b8145000107401a0703409140d0042c40490004144440404d8046014866400801a09861003a4482e4411041307883c0081c031403403484407802070381e00c00c2e80076003071094007400030b01642c24681c0d18012501d080b4144c000d42c6400c401540d9001140800500c0d40c0305032001c2000f007890418401060702560148100680907003154131223001d00103104620000342c540500302e07041501c1d0a00c5c0000c0654828401110700d00d5400160340145510a0b440c10196500107200038216445c2110440d0107485a152003425075585062184c1c0741d540c0c090700c000340320201c00c210301d00c000014010007654000c1d075071102050500400801006070344100490b4002c0362080070b0200d00740c546003008000c149000d03441c0c40c00c00c3c13000d00012840150000f005d07503101e4540d98081c80b140b40c480d50121000c136026200e040e086a001e004000000718020102585520002c0860341404400c80e0f920034200c1c2c80d5100d03a42141d650780000503a802010411941c00f400c0ca00091202d110488 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 709363767 1250 709362517 709362523
    0x280f0503010e040327091a060702181f030c0f0609030c090c0c020d030e040b060903030403140312181e030d0c12090c080606040e061801110703020627 66
    0x40c001420005c00301e0b80d50360107042c00c000b0031710010402000c080b401503d920a0400a2a2001030b00082c07410303201807420207151010803141c00580c007030a82031640001544803041c02ca4007030010243c20f00310040e1507640c6d4013154001c6001358029540c141d013103807400440410006a03500b1150420503020828404204203041040840b1800c05d030000d02d540d4002400c41c1e00d8036501c1030003036000244001b40070505922200c40f40554204980410401851404000043c401c0c1580540c164100b4001080800c07189142c103907800d0000c5007a82d2811450006e07000d5610f4045540c012000710224007040345000400002d1076504d05240305500041100e50312540d20300805601c10841500c3d50714000d4441d00c600d161005015042e2028480b11074107280401b034640042c01507043c41d00c5841d002501c145898000c422503001c00e203014120076101d01410601d1480c088038030480540d214415a117540300200010000c1c140254007600391070030541901c1070a8000f401c1002c89205c810414500061008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 709365017 1250 709363767 709363771
    0xb1503012102030721060609020a1101020a020d031e0c08010305060c070f081b070b04060201110306091305030c1c020c01020d050a1107080a1b0e01141302280f0503010e 74
    0x4806640d0183c4180c400b8200000b80c0c5c003c080c28200400054000110307006000705080c43d480b0700132810f0211008908070701030042d2100051340f11649400d401130203070380b00800c800d580010300042e101101e04c03060309a84c1c2c000020760009400c440100103000e001c0c440d10ba0804450503010b441e21070b0300d0310b42c001d041841e540c0c080c050b9000042c007080d0100d180595021100070920543e20b4141c0d5803207004031250001d20820025509024040340f04509e00000c90b4860301c00209003000d151141c1300202c070501e00d4024102c0d1244010040000000400c00c200c80d42d035500102d00746c5442c44215802802c20105110443c150b5100b07a0906c560700e508a416500036048520f0301c600c450810b6800ea600d1b00d1019845115580110001e40f010310600761248000c507070108181c1001150344c0c3c0c0b02241c1b011001d104a44070305010b03409074031a034039100e180740c124036100302c40140c100840852600307585c6039124006100c1d900d0010204021a810030a81e08020405090803800c40d803620280d00410030340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 709366267 1250 709365017 709365029
    0x11802101b02090603010b030717120705071502160305162909012006100b0f041514031f0503030405130921090e06101b02040b15030121020307 63
    0x965000218107890941c4074004000000b0104c0e2591907032036814114007205140802040e018042c82f5202c0d42d80110221349900354050028040b040c0351000e541002a03a65181004500070085000303451421407002c000514040c0c07024041e20988030061100020b095482056149502e640c2e980c4404262280d603840c10000402051740e0b261048012958802001c100700314404040b2800d01c0703040b1002503500d104203a08030b015508103072580e084401c2800750308186d01e600c0c2d90400040c000c00c040c0c0007504d0907405a500700790b80c004445494440a40cdc00031501c0b030310140c40c4031000c0351010004010704401000e066000d1441d0a050001089001c20400d447c00300494840c0410020008240d20005072160254030001440010800090200c01107101d450311003e90400072981620701030000402c00c01c0e9580f02d07002c001c412424100b0304581a814260390207680e8140403038980e140c0c01102210751140c0304580ba500c2d07040c040d4030b00c0d0007074407900742e481441c44058180005803000a5134100f5610 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 709367517 1250 709366267 709366279
    0x14040f0924020c0a23192a0e04060609060f0b03091e060405060106030c05030f091f0e011401060e060d061d01080c010c0203030d0c050c011802101b02 66
    0x1e94407080c00640b249466803001449450351403405e100351408400107081400301900e40c030b62041501281c0c2c40c000703210090310340c0702007002d400c2c0090340101e1140354510300c0d02110700403800c0005c11000400d020303a115a88050800302004100901d5101d40c001520040c80c0c00c0040604240c48081c1841c42d90068000b44140000480c00c851030420507490155102c0000007003201440c0c800a1b283e52059400b1151403044000101d1020300074004c50034101d4107942d6440c04c5550b0b0380b00403000d0300805400c204440c000d11511021040318244110600072005402240480407000403a085444101542107001500001070003142d41c04018034200e55000c440e807036200c040600c1600010503e036809030452144205040c9401c0c19542e1400d4100c6403400705072603900040800561302e01004c114000d6058208002e9004080700c142c0c40703070200110610b0610301701020f010805085074414807021070085540b5615000310f240ca1442d2030b41d450300a2030300d0038881240401c1040400200c03030009100341 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 709368767 1250 709367517 709367573
    0x1009031d010201060b040807030b01080105060102120901260106140310050d1509060f050108010b030c010f110625050406090608130b040c03120216120503120114040f09 74
    0x10b07100350001d50142c00300100550303641c2e03501d864503555190f09120031202440d031003000148194040c8180b51140c041a000751085154190031100c1c294420364119050110302d0f02e5200f00ca15020781c07528540e0044101d07420255040160290100518901174104844104104412158010516001c5800a4130820103103102d9140c401412b5400a40e02c01c81e2600d04a0f01c20144202c40d084071442c2032210400300f02e140d0300d41d0240c90a83d44100e08072901544085071584503035114600700c00c50b0080350f140668181e141a500981403c0c010340e1207116000094280540524940003220030f1201e4034240103203494a42440a081000b0512566050001981c0040d007161000a0380c6031115500041c4c03c5039a10b8240343c0300c05c9001c124002038404030304944c90741401d40d00006004007048102048080424907203a40c101e200f00c0c0d103c6041f03545000500c00c414101140d500c00a029021814130455500185c500744402c6802e070100082e24a42840c040700041041c10398002c0c0710a94140d5640505 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 709370017 1250 709368767 709368769
    0xc030d020c0f28140406050102030909060301060510030e010b040608060a09330507020705010e12010b030d020318010207030b0c030604110a0c02010201150302030d050705100603030801081009031d 86
    0x8001e140d001001520800202c02c203606044800c0c0081c0c1302c07444850b11850142c0414401142c5942c05031a025920401802c000707442d10320845503014a0003000841c0d0b4649820100e007000740b02c403520324046500c44200c070f403442c0c600b1301412090180c2940c00b0002d87c1d05d8550303a580c1d6a0006440c504900d541d900030542405040c0b02c9005034089002c481c80c00321326116000040590001000e000d10a180c903012444a82c800300e00c2d20101c480c1650b0b0168003c1c00041081900e8411b071104c007034650346e0f82c03007601e01d551810f0012070f54441d041e401440e01d4030b0060018210705651146000d046402c05101403002070b0104c0030740c5070080c0b168410152242da4001c003007402817904c0207510034403d0010601d00b132119070044450140910030f9009010108154505032441805404001e505d6080395810094480c403a1010302543ca00070400c850701c80007140325520884940e50401c3c2c0000c1c02250040c40222000c000ca4840000c0106081040c1c1071152401007601400250044410492100074821 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 709371267 1250 709370017 709370029
    0x8040311010b031506040c02060606181305152b03051602090916050a0b09060a091a03041e1a130c08010c031b021002070f0b090f0c030d020c0f 63
    0x44400c0a0110341210340d401c94044141130007120300301d00c59410166440307500c0e8400304130750f4081d000c05402d56041810b00580020b00e00d44142400350000220302c04c00c088440c5500445000da51104800c40740c0440f0402401100d802214002c002d2140d2000794500107901c0700c1c0c03034540e00340d01403400da91504c10030007080300c80e030042103800b0358046100014001039010100d10818640311300e641e41098190303104207000443d071180c4502030b1144030604c0007150500740703d0000c00100c0d0a41c600b819400f500c400c0c485005943d002280d90302440080204820090050603404608036151600c47c444a0b180e9286440204807460040e01d8040b6500403940b00401b80f180d40031415800488140d81c0e50300c80d200b0900070042c0c8200000000e04101d0b0542284400503030a582d031000540c068580c5264900d94cd001a501488040f507130213000c07200d400c0100f120440078901031001d110250040403206200b1b2450403480d055a2442030708a2100450702c15000102240c100502f682c6ca1101c2003091000500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 709372517 1250 709371267 709371281
    0x904060207052401080703080304020402030703060b030a060302100302180d020103021902010f060605090604380702010f110309010c0510150e09060f01090b0301290a090504030804031101 82
    0x8014800c0c00314031241880780d50f950698182034002d04078141c2c1e9960300300700c0d515010303880090200700301000400c0c05803d054004550025441c00c0c00302d5055a1110350000581c0b080318443c1640b907864006200b1403030710181100c41620945400d60a15400d1581c0348211140119100c2c400ca080820220840e40a501980d11441000c00d20886424680c1d038007a001c2c213100003140019074608400400e000d801441038400104010301348a05090074260122035011400111230301c5000c000d00b445200707014442c8480d01e19190b40031100d4440c0c59a00c0054640c0f41000401403e04c29400e4880801610000586a91030401d1030014104480340c109541001507402d0002840c0342481c054036003844d0108500c2d4211241380114038104c0d44c501013801d44600059900845501c4031000421103104c098001c465600c10050000903210b626a010b071021040c106400c100c08150410b079089145401b1004c140100a814010b03c258546590b0090107140d0060004041c4846030540180e03038002540412 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 709373767 1250 709372517 709372523
    0x2506060510050405090a0908030c0c0114040c06020f0106060e0f06040308072904020a0909050c030607091e030f030f18030b060915092a0d0c0306080d0e0904060207 72
    0x2565140014002050b42d070182c050103000e60016000b2072134102c1e00c2e11509004070b400c0f000890075030321349511502c0e4603131241810745060f41d2900e03001d003014407a0b0030800c0d000f24403589685c0e409611700311010341050201401040c0c075074034001080103100d8004c1214107404074216055005d952000300040c00c01e000e1504041d0000d9008181881008405072030a1011600d900091641c010102060908008201c0d002908034125080c108000c2c00980c000100d040d1050080e10054044200070918248044034035a0000d0b42020b000c200000201da500c1002100380e078000444c050075a111451101c0c04664000d00304541901c0c418034440c854070108046c03e450007071110400d0742d41d003003001e074011043d80d0062080c800800421509100d010303240b44c0c02840030b41403007600c0c0d558100074801c41982c16002d40ca601c0b0a51014403032210403500074003001415070300001c0c0c1488a00001001c848058100d076001d58425080f00340d02c5900540c03403000001080301c102d03281340e0f01d61a020020740201c1c2c00c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 709375017 1250 709373767 709373779
    0x303080c0f1606060e040f06090f06092604060507170c0a111008010513050601022d161d0901090804030302010f0b060f040e0603070e010b1b010225060605 68
    0xc0c00c00d42281d100300540c02c1e4060f14040c0103482d164890a4860b65050b078004182030304003280b40e00054100e80005590a02640031464400b803d0346035242a0340c0750304411a22081d00310302510b04040c0d20328441d00781c08030403c1881c1c2000c0c02c1c100090814840c2180c0504059510600c510381c061190044420403100c030402e450210140c3e00c0c00030741c144000d8918074414071103001004481071190b0401e604941000b40090340c149420a80d41000b840041d00d002c0c118024580c690841e035600149040790030286400c501b84400a0600c03103403c2c0303c082502c004622101240420051200222801d54181020901c008588031000020b0040407410b01c01480c1e03a0300030500009064041d070040010f0140b0103014000141c9e081d0401c8424442e032141030041d0310007840203000c03a0b80508a410340c0088080d003150b4090740c03a5000801241c100364010381900400042e8070307040314160031801c0c000f410f01500030342c03d0288000940b440c01805009094600d101c13802000140806c6400100081c000070f840 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 709376267 1250 709375017 709375027
    0x10080105011704020a0b0f070302010b01030b010525140d11010228120921021539071205121308071202011a061201061b050f0a020a050103150303080c0f 67
    0x7d02141c6e40000c041503015510b819540d403159402406030f9000303a4016135480e4502034041c1c5560080c8080c81c2d602c07124034180d0008080000b40c10a04041c2000c2c00c00008114403405144024940b800c40c0c81160442e074018800300c9501804040c2c240360305800041030700c010160600c402c650040043d91000501402c28140005209400000000010342c02900d140041644036080e80d07505c000101a01d004810030000903c54030080c003410083c071000080a441c40c041810402d241d0825503610a80f906e000000c85004020030510b046007450000d081880c2000403541218000e094000c0140200b10303600c2c1504810004d8003000c940c2c440347c0c000d1810010120341ca00003402040024208040c01c0354a0900100f245400800d171501d914503941c0291440e8280042140d00b8440804224031600e0144155000264148080e80d40d050a220042c07154905600401074052403680c444d80c140b40c941030714501580480108031090b40c2e01030400c0c5003180c65001c82e458aa10819000d40d840e5140454 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 709377517 1250 709376267 709376287
    0x90d06050c07060b0306130b09070f0e01150903050d081b0a0c0201020d09230a1a070c0b0a08041b080708030d0f110301060f03060306020a0e10080105011704020a0b 72
    0xc00b80002c14020241001607036039803c2490703502c610540322820007005903560440051311007000c480c2c1c400c10308000c2d07031034565407a10001f2103c403045e0007450690700300c0070040c450034405400040b00ca1081d072510601c9a499a01e81da52145000d002c90b00c1000100400601071000849901c01c24a480072512640c400c030b08240284407000c004412401070042d110441b104501c1007030408160740a181c1d0714061001480c00540f02d1819a42050f40c03c0750f0704000c0000c24844444a0065500c440d2499555500030303032a10741040802908a0950410b05128829a05038070001495100d0750060390b941c02883d41665054081c01c3c170354004401e40c40f4280001c2058580403016203103080a889051114222251804098035209201415042c800b80010032205120300340b0300c0c2c4500e103641030000c3c00b1900c80c0c0740c10007642c3c040a01c120114048100ca00d00030700b04100500400645d6103040921941008002040942c0e2100300c4401c0f080d0303550201e000d5540d051465001130455444150361105581 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 709378767 1250 709377517 709377541
    0x30103080a020f0102030c16110d0b162d0e090a230405120a05040815070e030703020109090207080c0d0e0a0801110f0a030b10030e01060506040b030a02090d0605 71
    0x1041c014024000e21001c1014140207807070250b110703044428200f503e4010f400505640d60081078421101180e103545090b2100d0b000004202e0180c0c81042482c41c0038a80103200b40f400301c501c0410024907281c00c240840c68007590007500740c40c444811040031074070701c0103c5104541b03204403903110310080b0610090f6038486e402000d1980101001c8000302c0c000d1a05616902c0040314060a55004880044114030b82d54000389421519818030702c0c10a5100c2d580f0354170384a0100c5040a812a5510600c185640c11402d801942d070700460083c0314180c02d580c0000e2490000344120303000d585d000304110342008900803d0321880001d00c400c440f079415100c84024854001000014002e00144a011405884c10b00504618901d11035607946440c9202800c00c0c0c11798408100e4400301130f40c400d0f00407a1b940d00c5c1a62035810080d03980c3c1c0410010b45000740e0508650855000390b03c100c50030042001081084410b40fa40449501c60060b2120200700118080d200e51441c003c00c1c00d80380c5020031102c44048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 709380017 1250 709378767 709378777
    0x7030825021e010930021f0c150e0d03110c06041104141e150301180c0f050306241503090705010c0209190b100201090b130807030f1403010308 63
    0x3681d131401c10350355032400c09600c030344821240050350711080340510100c140c662280714450310180c034152400d0303201c54482c84c4102191159a0028050500c070809100e000000340041c1081c070501085000c4602d000f055441c2140200d080030302d1f0700c44400c00c5045120005a40d072084695040d24542d00d89854100000313500c090000380302e00e01e44400d03200c002c104210b810384103c0c010b08442c0000b00001861110883e0b00501c04480c080b400106510940c800f80144a50030880040d21f0b08605480d00e0806203100c050f40114121805211081241e07a800041b00c40d0002041b1a50340d603a0700005040403050524290015041160844080101c0500d42c0042d8820304400c01134403d2213845070011240d0f0312108001a40c01580d007004905d118400c482c8001d203045041c9000503c0280c83d90100b655560201800301c0981d555070001d9083c0003031512402e42c010448105110008043d40d5088201d0081090140c1008484990148003600490944070303a01400c03541c0d95240d40c1d4034500907501c0d50103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 709381267 1250 709380017 709380019
    0x1c0c080a0c0f06030204180203060d060612060b0103020a090e060307030b01080307150c050f0d1b0c0b1807150306090504141c0e040f020702060c0c100207030825021e 73
    0x42150006102d0f80301e80f0a40e02034803c8075490342000c820240b5014049d400180000e54801044e64600000030290301c0b480e00141280744c0c2d07100d03410b03410781440001ca4180b1007a150500d0b00401009007515400074400007a82d03800014500280c842c0740c00b107441c0c1046500000c2420070352200109100200101800f0403d200d050480700d00398499120070b0544114510100206506102d841c010b1500e8401610078030000c079000007101d80c0c0b46a24070041000095802e000b00d906403820100348a10341c0380c41607214583c1e501c80d0b407a02c1c070750345860f03540c0c0c0c2c420380316031240a1041501c1c5d50401e40b20340c0101e00286211203062103581082e0a192506400c44040151244100e8040030004004020f2210008510b42c0b80c01000c1c0d5240700500003d4040c4110303200296500b0003691006940b80f1000c1d004800c10f41d0000c10004000710280451012038008000070765000900c01c20000d0f103081d04403800c031460b107c0300d0408001c0e07161000d00e00c0551148004d40c42500401d24040818070b0701e0000c200b5140c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 709382517 1250 709381267 709381289
    0x18030d0e0c0a060c0c0e0a1e0b0f0312030c03181609050f0601091802090a0b0309280219051f091418070c0c0b0915091c0c080a0c 57
    0x580d82c0000c1d110010b003480014095280000c5c02c0002c0803000403210b13031104030640040784002d82180c060b5081c0701e420030044116965401d06c1c8410342450101d15034113403170a800904600200290764045400001d2a020412400200007200282c1c2c406171035005840780e2040300c009221150041c0c3e040026405440300347c2d0b1400300011807403a00310921602031101a1107031891682800000e0400c041550f02e05c028060302048459100c0c4c640f0082c0c08000e04d01d1003001c60312801c168000d0b50034910101180ba071500050840c84481c4d1801c18442420150b0442c0c0c40c030380f44c01401520444503100da0340401d42c0028a20106001c1e40c0c07581c0c00c141e401e052965942c09910344c441480c1107110100346000d07a040b60482d042925080c1500d21403a401482505140107270b02c04c10750381d43d5038450082d0889001c2a1021881e0107a9080030b01001003041100000746040040315400b140f0788a526240c0d000190601f4040307003050105e100104000b0b0030108013035900c82c9250707081c810101040d078412002214 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 709383767 1250 709382517 709382519
    0x102060708011d1b0a020109051507170604090c090506040e12160501020910050c070522020904290118061e09050a09091a040b18030d0e0c0a 62
    0x103201d044801d06903850303000c107844400e0429a104000032001880d14445460705480f00c0903408207400907080480e15030340003007840d0700d580c41d0003401c3c2000080c2190301724402c2c0782440041c5800002d103103140b1041420a5407036585110004000e0400c07a803014001c2c2010f030b80045000800d5400c420300c20340c41903d00b40310129010302c1c41d5585111600e5100c440700b00921040904841401c011005240100009810080a5000a042c1e03030740e400081408100005450000144144885002080101d44407001c104d40d010078000c510204170b0440d0700d40369001070441a00d61f00c90340020f00c4040f040d200b031441e5000143c1074080e480c0c40e0902c220302280001e45c0300c40004101002101c01d80d8060754419180b004154000000303c81c2000703440060041100d800309041d00c80440d4000200154a0045114103450074550185800e0302d12420341c0c3c48905007044041403084030b4654010000041c2c8410014207800c0e003500350f004d030303006640d005824a800d10f06040c4000640814046d4110750001c125 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 709385017 1250 709383767 709383781
    0x2060304031d03071815090c0503040302150705071410110c0f1209040203100b03092a0109030809060d05090102190c12030c09030f050f01050703020f04030204230103030806010206 79
    0x5130840b48139000c036424401c0510030b45503075150030082c0342920b80c81003054515203421040301903c016042c0c11000440210410090690411100c0741e0203010207030100c1a4104810001c0082c0f2071000040c028014034100002c00c607200f00000740841c92103110030803555450140380a001d500c01018102c180c841c42c0010441400c1c081034152150141c40c0c0000d1502820f2003e12020790001040b591200c0354490380028568400c00040d8800d055040250100086007a5100400c07008030b003030100c8030894281703043c51590308a1044002d8941011841e80c49842560005900d8828020803524113401c2005215080707005402034016200240d40e011051003d019040340e00618084021b002802005182c40c0302d5402503211002e00300342481c080d180b0325103a455107200b078038044004680c158440392984401e41c00038414203411600070b1900303520748103c0001600041c02a408040c0c0300c1d60f581d43c1200c0c00e03050100094103400c49140c02503032441d030b520f080c00341c01000c007143c1346409401400f0014a0f0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 709386267 1250 709385017 709385023
    0xf01201b010e03070909171209240f52140a090b1602011403190506060c1e1b1c021908070812040e07051602060304031d03 54
    0x40050060010560903252694050141200b002c01f9100c002481c0312079002041404020201a00460510262400c066500514080034402c2442d0451010501940c060301e8210031550080c20007521005a40c0320b2845503054040040c22100f11480b806e90441c0003e200800c1d126000000d800c0030300c021200144158908454061074030000822a0010141a034400b60203030a41c5401407400412040d119200d040891f4403400d40c003020010b90f120303208210f40c5d00c2006441c008000449542c01c500300040c42840d054a0f030b520b10120b8580302d800284142d2a079406450310303412400304444c0c00700201c0c10143c1c1e40001560040c2c82074041c40381413400810195a41e1199500302600941844c054490506000703101128200d07409500c1d9901d82024601a08000c07002c0d0010b20003401c6402d01d428100c03803900602d5181588490340500040000060715114240c0c0417140d400c059680d40c070215940203140800c2c08000b1340c41880481403205059218000344480481c510b01b446411440c0d004140d9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 709387517 1250 709386267 709386287
    0x120609060f0302010c0602090603070305180a050d0c05150a05090d020a020f040c17150103060905060f090c0f0c0309010f0201180206090109030b01180b0d0c03020f01201b01 76
    0x400c10707a031010800040d4441c0804900c4203000711001420105401c0c0000d2881c1c3c020344140c030009841d11309101003417400b02e8074010f01d104039000420f90100035a40301c58584035111124414490000d0837103080c00000c2c81860003080c0312400002080ca0444031702d000030b00003562804241d20903069100002800020210640e540040c0f6140d0086e1031101004064604207200030f04110000e0201d41d15007650402c128010305c2c8500c0009043d841c00030005048900a510400320305040c4020701c901511500c900f0100444207035a00a002d5580340e80307005052040309201300201c940000e65441c0400088040c2080710800d07619140e980300c42006c200d0030b90b10101407200350024024a03a10040c6017071401414031210604001c4060fa50301d4956104000e026400000e030245100700c040e00781100d0744902c1d03900201c1105da103881c500040c1c40b1003103a0742d03203800001e0198501c0300041072580e020b042c201380301d082c0100d40001c174020362222260700c4000c0d02007074a0341c80410880120007980030754980e070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 709388767 1250 709387517 709387529
    0x2070507050904150218040c02280807020607030507140a020a0e04051c120e0a020f04020c071802121302090a1b03180b07080f1f12060b0301060612060906 68
    0x10301392104d02c1c42c005000b9440b141040d0405000113840e00001d46440c054006410071680140a0708005c0105c0d034050182180807200c00b241c910701101001030f80319800e4506094041c3d914980320b046a28098078240f28240015111044001c0810403c0f100040c150704028130075540c90204e07540d0303a070300c2d0319804c601550010400c1d00094291141a041da51058181505615120300380040c0480b4a608032030078008184841d400c00c40d040011760901c0d6441122008041d2411442c01d218004c03043d4a03000f05d4011014956010990340104010a0701503070810074810300801c41d142004c41c0300313489a95480030200d000f0703c3c2e500c000407005000d42c0b007403d00b00d0102780c107d6012010f50010480081555241d6103049280e8503801a0101d0749808600340300c0c44490301c4160503805c0c00c4001c3d240c60f1000a081c17162001c800b4414000040146c01240103d034500058840c09520600c1d20307070f000d05a06641c064140d0301e0300c2c00001e00300c0d134401506100d883c48410200302c00e030380352540070301074803910b000714 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 709390017 1250 709388767 709388783
    0x20f03150303031311041e020c0114060d021e06030a060806060d0c051215270c03102a030f0b030102030603070302010528050301030606140a091a0306040602070507050904 75
    0x100030492044541940c0713500144002813070141f18059003160b1310f0740d12541a01e1940841c04a03600301003480f40c50314821060000845518100001441e041c440c3c10002b030091448490080d190851a414030003401002800d1035223078a00150680000c00691241070100d02c210804109582070003d0380024003604000100703507040c20001800340031035052280001c00d00c41e412180b800010800074090040700c4541142a030056900a165501003182c0d121501035003100e1110f5504c2e40d00012040142c00fa1640b01090a620320415109540100088042140d001440800340c50b54540e001003400d02e184c500400074100048281400c0b4001201c40680640c400e86081c0059030240e0080c0011101118600c00c0907160b1030580c91000c1c10600c00580880d80200044c010815071303014201c050042c102100c80d0446c080d40001d0030380f462900c507000300d542d81c03000c1c2001034881101a13045640e41c0a000c23600d49051034034040c4029403003628207075210301665501040602c1d0000c4498081c0d900301c800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 709391267 1250 709390017 709390051
    0x6010c0218070504050306130b0c04081b0619030b041a031e0a020a0e100b070305161b030f060e010501151409090103150507020105061507021201020f0315030303 71
    0x10018903141c0241018050040610001409503000c01031203201e005240c1c0001c6802c0c60500d0000c00d440ca02405e20400408180010b10500c140080ca01c8486101c9000960040c1c44c041c000c61301070700c19000000d0075014480b0502052503010307000030f003d804098508000341304e41c2d00b9520203000c4140e004107600d9040556107a1251041e80c01d0031503080400401d8a81944055001a03212406503005200c800d95110130051000c8d0072422000c001d2920302202450302c00640d40003040303441b0b0400c0c030584580c1003d01d40c4007405a0321400400b4208846c0400496549a007404034100d0301d03842080b01c40609002c400c869055040c015903048030403085402d440c00000110556032440a5880d0705015182480000341554403070206030b00842c01060031800160a0007510300a5070701c0282910b082d0382c1400103114054a502c140b4200d05009886078649500303039480051801c840c610850740c070a600100b41c0302c80c0700303004000560242001902c035003e60007140d0141504d07800103e540481071280083c0c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 709392517 1250 709391267 709391299
    0x2030405040f1815140412081b04090e0f010912080a02070510020304020405070f08070528030c17150d0203150117010c0915140d0203130b06010c02 65
    0x8002d01d10701403202c1c0030034051020301c00c1d440c801d5041401a02c07020708400c0302d8299540680b0030303d0304010b1070040380040b038505078403680404062410380da4104081c10001034030a0303d0005210300503c51009002d50380c1c0b03607100b0040002e002e202c0740741440c40c0901d1002c012001d1052080122940c0c0c8000000030020020740240d0f80880e00a0081c04255000c206400006100f8490000715440d43c00005850341040e0040c0411503200a00680502900c00000e450440d08145000d03808400d44c034100e5500d045610705004100250100c01401c0b0540c15044844160183c01c04207461a4590790048058011107251b10310ba041a01c0f01c2c5803000058040225905024400010043c005000c0344c5456003c640c0f0b81404003026031010f0740c05030360601d0b00700c010740c5c0c2809040c400e10201c0c6045200e45040c2000e2190f13600e60b007103000041c46006500a060480700005665280e40c481c1c80464403480e1100b010350513480380441c11164950f089000408c1d82d80281c044429542d0050000d12801344984 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 709393767 1250 709392517 709392521
    0x6011818021b030708131d060402090301020d0212181b0d0807080a1206230607020109270c03050f0a0b0609060a0903020f090601141810050310090c0203040504 70
    0x81c00d040300314031180b5010301495040006142c102d10401c1c0031079442c2012014441c00c12225040f10807030034400550108894045404181c01107000c130750050740c0e44106c0d40040d00a1085450300c000407800811f07a03440b400e90f00c0c1d1686100700c040800e00354907003160046160300c40d40c18a82e600384030f8080228042c0c240c10488000207610740305a003400c0c42e00c0c8640d10303803244a4202c1c1c10309100041000c019501d960f2500c0c01160001e00d62040d01040300c5e0400385005070480c1040444600a2201081c8032095a1150f51110b00400080201580315003021155514503903c80c1300114140341056100c441183c400d100d13840c0b10364529003d1490a48450010344050104603002c290b00c06814808214240d0703900d8000c100c2a100303911442c03905480c41c81440702d004880301509201d41d001780c0170809540d0b080f4400c0703049450000e54013a942e48015401c2c0d0307445100c0303c8100390080f003a996225a816006401180580000541720000c00d54413403140d015a40c83d60503e400503041400204420306042d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 709395017 1250 709393767 709393777
    0xb13200607060e1e0c100311120103140118032106030b0a150806070917070906090f05130203030405061309022a031218150f0601181802 60
    0x10046440c0c2111610390b401603c15144480f01c00e40c010400031005600701d24044032070444c4040140552100c2480000d8018000b0581003052641784e05c00c1c11308440c2c2110031124a01202000d0f05540d50710380c18005481c00c45c054602c00d981d0700e424103946005010140712802103138140e50303d20207400341181041d00b2100140071b406a654a8030000300c00102030480d480d101703002e0654000b40c0305100000e460042c0b8403660064440b60444400c2c08030303550307000c03980710161003008540048a5080c1c030451443c0465a620000c40246042e6001ca1180f109400840110300405c0d0309200075141d0000c401c85003000100d0082d450742c420041000f1900b8100c0c00b80920100e101c080e41080b5541d00c138180c1c160b0b030100c1582007002ca400c12003080c012341c0c004c56407580b000550b8019401c00c092111115a1410044d040b1400301d0601c0e140712800740f20400c020501106505401c0300c0c6814060030b10400d0180c151281c5000c0350041c0000700c0344603491130041048840c41104100c50f8201d20414100035408 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 709396267 1250 709395017 709395019
    0x60917030f0c07020d020307140f0d1a19090308061e0f0f0415030f0c0e150402090411220504020a080f041407080a03080c2a0124030b1320 61
    0xd0308285d00e026030340c14040e100060130700b8903d103503005221608018502c804404064810b410f2013000304081501d103c0f01d007401c5a4014055450380d1205009041c1c448198007040150908082041040550003c13405010b544103036144080c013200c4105515203501000780d299000881900d001c0c0061410807442c00103400003400c0000c205142a4004142185542098a004603046410420011084840c030000d2059031b507000c4039410183c404004100080c450039200701d401044004041c0d4907580401c4290316840c1e0445d030783e00d40010360a0380280340c032105607942c8004814000b445050038000c58070441443d5860b03d056603240703148145003080161083d100c0b084443c0040325020020002c14000e0034801009220a07000e520b4000d03c0407400030400400c5090500c8040d06d541d01003034103c500031031441c40407210190521841401011000e0038540801c022400301c0441c4041c080d10003042e0f030f004540820142e40c4e10f10ba060000782c0810300c000c141803d83c9030303034003a038000051007242c040d04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 709397517 1250 709396267 709396279
    0x607030914010903110d020f12030604061d0a0c0807021e0307020306010611010e07031a04030e131a0904020607080a030e0a12200d0509010e0d060917030f0c0702 71
    0x9641c0d52980d0071a007240c20200c0c0800d200000d12191341000300440f60120066200030400d0480c0e19148035101c4005810341a8112000320100e2016607a41d005a400303130036404440450b8180913144000101000d40d0351003200791424075006120391088c20389601c10f50054004003c0715070001818219990304070780d01c4d10140403e000510040ea02400058001c0900d940c421130443c4500628601311203c00c13001088590005600700009008510070105909a28200041c20703690790400381c2d03141a54a910719800341da008000305030144290301101c20014a24058480480c03030005100144c0e40030b88010350301c110b0a0014100040c1088020000790f40d5526003c2000400c81d5401c510b001503184089441c290340a00e01e42c01c050744401004400701c0b00762107404103070020900494035030b00980c10003010043c0c001010f02869000304504005040c010340511b2a0b203846080070001404200d20413201a90311440211006201c18140c0307000e046000d80c03081c06a255120701d000503a214090485c0c001d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 709398767 1250 709397517 709397543
    0x20d0c0602040b12180a05060f0a0219081f050a0317070c031518030e010e010314090f060112110d0f08070609050c1e0904140d0525020306070309 64
    0x1100805004403c80c40401030f113840c10182e564200400d0750f00300c00e444c2e0b0b6100a1290700441c02c006003141d003008035920140044d4840d2082c0c000030303200342992040e10901c500d4066038100e901075a454803d10090003080460000c41803440707150201031017060380c4030381b4406c0d0030300115102004a80c04040100c2000c9d180a070f041d645c000c840c01490740152094084c50310207580000e028090410001c40541d03101108003056030340540401414140503041080039120503001c1d0340681d220413501130025603440d200d441d1040610782d41e820000b401c401c1c54051303240006002c0c0d511240344c03032505a004c02c0c0452040c87e25005d00c05040010b20040d900c0e21011855040450151002044007070301801c00495103034258200b05241c61000240e440c010100c0d190702e415104c0200782040f24540e000c4811481ca40c9039418100c00c1e030700c2050803455490195070700010f5919080401800324910003011440210f46a8075296519980c80d10040c0d0990807020000711020b1180e84000442403245800b40750035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 709400017 1250 709398767 709398779
    0x3120d09050f0a031d010c11030f03070f02120c0d03210207050c0f01090f03110f181b03060109030b07030608070902130b0c330a0b01110a03020d0c060204 68
    0x400d82c800c401030520b4000d210310030141036000c860980c04401640011011701c444c400020039008540001401880e0b422107003c6090b0303018230460a40c403010034100c80d00c5914500b003040e8000f5000000300d10500410184035400000429903603520b990040040100c01d006480a8943d03e400088028000494000080c904d02551001d0308000340074400500c00c000303022050081100700e15900c1c50500419450800c03035102400381240c00e482d444081e100d070304d0b02203c012036506644006c103161301078a07007800c10f00c06880d0104058807602c41101c899040c6240c4000d42c5203a840152031840c00200650400d00c041640d41807083c0e0030040c145000221036a8a0700358500305401500175010703058001034a02c540303100d1104601c010f00b5064100741c2c83e2104540115a4480d00e0b0100054948400d400c40c0c0343c4035100010764042c42e50158621030062411600d550010a00007080e00d0200706003910080440c0c000007038400b22164550001c10f0301c1c0b80811425110207041e820b0444119800b00008251 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 709401267 1250 709400017 709400023
    0x10e060319110c0f0f21040906060c0209100501020303070f1106010315060e06100320130f17061f030f060c0219050703020d0215210702030903120d0905 67
    0x5040d0b40901594454820304045800d1a040e990000e04ca64041a004214150003090700e4000c0c0341c6e8400300003001d0041860380e103828051039010700f0030a444e000000900e40e81140309040f1107803080b07581607410703913940030400c001c0c05e5540074650050b0310500025460b607015a500001441e21818052200c40c800410385242c020241c00403210241c0f840e02140f10a81c0754020600500100c08003080180703440d201183e070900900080e00704150300c60106141324240140384003a0010a08080c80e40e90085006201c0840e44600c520040c51200c1c0da0005400c2100b035610b40c000d01034103009800903860b0302540700542c514070b4002000110f65000c000000910030341c14a141c541c800c80002c1030318660f100c0080d0415800d03034002e400c804904c580460018002188900075a541180c0404450516001085000c50000d0360305001000014640e0103180c0103d00d411080742000801e40844d5690120498407402a203000d55050781c03180c480c001c0c0050040f005820b44007821100092001003d4803010301d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 709402517 1250 709401267 709401281
    0x703080313021c050109050f010c02030f2511010e06040303120c02100207060515030c06030106030e19050303060a09151205100c0f0807050a05031501030f1b030e0705010e060319 78
    0x4d0b05079582c6050744208042030102c011041d11820003004035001080d030103500d030720680700c14440022000569030701744407201003002040499210900c0e40c6e0301c0949000080c0e103a10700501c2e8041552900150b1043c940042220244d075416034440100d180b090b200c07030001d4460104614250700a1440007074450800c1c1c4041c01e0b0450046c240441d00341072014000103103040641c007550203508103000c031024688074031040760b04496140c0b0300090f103902401502410440148400f07107080300d84071040c2047c010000042e41c002c0204641c20a5400e0f500c208040444403223080041c0b241c40c80700e1f020821186000110728001e4011001d9030301740b2145007009011500366041c242c1c08035200042c41d0f41c92560203030a0a501a15038107049150540c4000050818000140040705021603200500305591203500a44150780c82900c081c810803071a901c1304000b040b24010f005c80020b18040b0b0728528440001010001c41d003043e100c4000083da414280021948020003d0003a40340108260341c0d072000358880c1321 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 709403767 1250 709402517 709402523
    0x302070801050c090a09180308090705030706090602010b2e020a06021210150e1e0a0605030a0b0d021c02010507080f1830071707060207080703080313021c 68
    0x907650000813081040301043c503003184662a00d40300c0d15992079111718244030403040d003504240000d59200403c01e498000c0079000035400d4042c91000003100c941010b130383d20994295400902001c44030301d0134440021101e01c1281c2345814440c604004894018902c07003000b0080b441034660800c07040d101c2c1c03c2070340e05c482c9582d170015100c94100002d910482d0482c4006d410f420040103060101203500402206000800034428045869844c0d0b00c0ca4031035509541840018003a40d01243c0d80e410040c0158100311601101c2d6130400d094562180340920041d002c056006010700c641650903545101203040c9440100d0500804008c64004241032101070005034401955a41da1038000400b0101d1190006540314001c4910380710411515078101540d008110643e20441d040784a82582c040c50081190310880c40c80e005141c06070800c810200302d26080d07481c1902100e17281d50340c5030780c038030354030602c911010304003860034808101252606048600034500003410005001444110540d0f072500c810012 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 709405017 1250 709403767 709403791
    0xf090708030414030606151e04080f0a02040e070506030c0a090b0f040303031107021311160c0e0c0c060a0e030714030a120218010c230d27050d030207080105 69
    0x40f06140c2041000c0e445170040e03507060801501207244490502842031019810091032401c0321401c1d4418050310000e107a2203007110b00c0003100c4a1501d0700c039018039809a00803800c080440179028130004a00c0112840130341550b00d942d442440c0c0f02142d411021122080104440c00015001e054034050040038540d018950341e151314500c1c01904451003125190b410304001d214080c090390311403070414089403010001140c40c5c0007030040c03c0c5991103000302041403035110045d907505014006a200d401e944c41e18503081003a4a80a8445069004040365040d50385d004200103200d449103900a9030051100d04100c17414418180e448000c61400ca03a0304002c50350020403045240c981c0400c4071030052101400c21481c2c9040700c01200300180c0d0381400581840001c2c1a40c0040102c100c4103c0740094000e1403031001c2e0001d00d07480b0340d2268004c010384800203804d101d10340070a40c031507040c0d116040320240b0060202803804007440141400c048090b420740c024100d0000340540300703015091244002c1001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 709406267 1250 709405017 709405049
    0x901060506300c090409151b02010e15061203090a06050d150f14010912050607020d030b0a032414061005030411040b1207030503030a1409060f0907080304 68
    0x12414038040e014582c0100610074006008800e207064040707403450502500c000c01c4840c21410542c400882e108644c00c400c41c5000f1200b10141c00c00903103156440a00d034000d00c610300480325080e03920251040014440c1c0b2125002c9a85854145103d000c454001c03010b50b801c1c510143c0c00600d8002c40c5034841030100d03000240f15001151540f24044404201e040202d01840c104800c0c900e4029070740c080e800b000070750192009100ea000c0c04030351300244207206e02d29044510b1490042c0d1103040940c0c10714050300c501480707c0c2d0300c217001c1c1c010f80d0b55401024200d00842c0d072540c1c41d000c0b214841b45955000a000c2140f0602100343c4a001328100050b00d044030104a01740340c2c05201071960311501c40b104004040c003d0000051007a038001d2541c0c01e00f01e0300403401400b11b000280011000d81800c4c47c0d039202d4001e0020070481d001c40550300c070341d0602004104262607090884c20002c01112910304640004002982401d8900185d64000c00d80e802220360084e150704400385568041d070440c4080380c3d0350b004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 709407517 1250 709406267 709406317
    0x2c0a03080702031201060e0102030d0e03130b19120221101a12040501020c030a0806041406060d050426030406152615180f0111120901060506 62
    0xc05504118244021850044403032220041448180200e800708000d80ba41c0d20f203030b81e100b0010745950500024042000c003140901e490340c4d0790310003140603041204003900054042ca05a054800c240e004250140e140a109201151444124182c854205500340590a00d10214410803521074000006048150410b06502d105e11912540802070000013044149000305002041d41c4a49003060300c607000b01d4643d841c203540a40607401c02260766210108204d000c150380480380b9405418266010843d03040e050404038510a4102c9046403c400100304803c112442544000d6200d400741c040b072060840b0500140c42044001c90f00d82000d080302200740824080349110380c06401c81086e00d0100d810b1300d004140510a0244501414488004507260010400602c81140288108500d2180a00e0110341c8102082d260480c01d94207442100c2c00445800014071859030080a51109603081c61404410003050200060030001555240d1500085948601c009013035280703908813110300440c05250b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 709408767 1250 709407517 709407527
    0x712020c01051b0c190c08010c02030307080105060711060a0e03010f1d0607210e010213031e0308060f030a02030a05010b13050709030807142e09152c0a03 68
    0xd0b1803811600c01008034400611001600010441c002e0fa0310f00617140003070030302e101d40320034590000c50594201000340481560120055100e4034580d2140301c11640c9410600c40280540c84000b0304484440080507914503200c8040c0c0501284c61900040c17807402e8002007401d5440c1007000782100c540b6901080320032041054640c1011030404001c160340e1900d41801401e400140c291081140406a041c3e44a80182e030401d4a8404508009554412441e0580b0394000010311090300c2c400034052208041d10400c44440070790b2601a9505001510350a0410204260a01c00c007a0301d8499001c0700c40c0161024860140c5040c050340c00001c005a4035001c0c42420042c0205d0916024504800c20514a070000402d405a0341c214200549a03a014501441140c1d28200007280900c5011464000b22801c58440d03800340981085a1034003110103030403030054410f900b40c014800c1c18070981001600010764000c40b0100b40740158003501d800341c001c0e07400b0f007061908000720140c0c000300500024546c0203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 709410017 1250 709408767 709408801
    0x20a0305071a18240403030801180e06060118120503042402060417160b06190501080c130f030303320402040e1606030501080d09050d08030712020c0105 67
    0x210321058503021aa116042014503640503591007840011440c119540180380010810a50f0132903041c1e03100d4032803d02804090302445095904904c480d6070105c0c0c1c000d203008405000350120001c00503034450310010341d00d401c280700038802d031649000000a00c2c84a125024040c072801100692b80e00c60a044d030300a040c4400c002c0000701c080c140c00f0390f41d9000e03500040c01c2c2d910940110320341c520783d490312408a81e01d00c684e00c1d24007150900b0039402c0c000d20440c01c800a0140c0b20448091180f070801c4010b58248540e5403040f41d0108010000003800740c003401008143c28a54101c0b10700c0525118400003940080c0f03034000b500002d81c1c0d07003014515514400703501d1000314009440c1d6116a07244001307458150384000c2c0300a01032919007020000b1848101f00041c179910003680c00c84407090702c4070001001440248240115803003074501036207441e40918415001e490029001500101c0c558440d030b90700f0391010705900108160501c070b02d500f401082c4082c0c900e440c00c510011a050900c074501180c40e0000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 709411267 1250 709410017 709410059
    0x30d022b060f0603150527070810050d05030c070609090b0307050603040807051c0c0b061203090d240b040b010e0604150e090a0c080702030c061b07020a030507 70
    0x16040003808480205200070040311011314000c25604006041e4841e0108184d02c160741000c541012908a080c058828402c004240d183c01d084613540d003e41240d0198040d10803110f05040344000344160705000c00f1b030204a5005804585c41c2c00d0b03072007582918164480d4481c80000e004c1c20824070061019006051030300d02c08400420b8a9414030340000e00d64800607000426a00001807141c08100c020f000c0d4011286000605881103200c0e91405809241c140c40100c8050020000041d00c0e071404903c0040c0713040c0540010f40c10024084280152408030840541e10808107903901d02801c0c420381c00f035441660300c40c800480d440c00208284001c2d2505280d4040c140301035075551000503102c90b0250303030031901d40c9161400c2034890321805031024682c5410440d00318412000b0402c02c00b21580040b03603051703d04e685030603413076603002000c070b850740a08803c000d4950484030125060341c0255002c1032520060041e01c0d4039000e040c0d40025001101944119000d0304001c10070005025540b00034036802e80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 709412517 1250 709411267 709411271
    0x1e040b1003141e011211190603110708070803090a05010618060603020901020c041a030109060b0a08032809050910030b060a0302010210050c04050a231806040905030d022b 75
    0xa80f19801c503504205020304040340e002000c02d8010b200c15410807108503039020744001e2444c0300ca2201e204152165020f4000828200884805000344401c111000c3d41e401c22042401c000095607071032084d50010304220202e00c120b01c4044007041c820710030740e070081c520840c0780c01101758407650440680d240c40e40800149441801800c25998000c220700d000b12404482c0056504001404101100b1544100360317015841d151112082100139804000e070300a0490301e240c038440d96038100b00d54910400d10094100e0b11143c10700d90301210724211204c80480e0f28204030642585800114501c0002281d0200e03488082034000c0040c00107072004142c011805880400c5414210f40001c2d607280101040b08402c1a9558001450007003254292005050020504042c907590350301c0345940c01d0f8030582504128895840b208074189084512107508074030121103000207980d15010800141191001502c10780010004104403000303902c000c4c11b5640c0000e90030320041200a041d24900e654020011403000c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 709413767 1250 709412517 709412551
    0x40b0c01110918331507031b051c0807030c02061509041b031505060307050d0615030633080a080a020304080d030b0f0d021e040b100314 60
    0xd2035080c02c0f54101c0030b031103020120a0300d40c05055988100030150000744a042c06600d00f6029040c032a0040260900f240c45030000103052031008414810305000401207144808600582401c0d001d81100945c024010f275105040003081002150b40c002c00060b000418080030802c540340c0600ca20310407024a8030003880d45182c41e0b18551040300c1204110b40c81042e001c0c002504200601540c826000c910310b0503405210355030b107040952011020800001c1c2030031300c400101181030000e816000c03910001d1056134a48142e4440000401c0d1681c40110344210041011011690b14050882d21420501880c1d03440c40001110380c1c96114548400e201c00400803c0420500703d000803402070142e0480109940c841d10000168503600c202d03804050349029216002ca6400e401d030b48841c840003c1655440b203041e00900400200f00b0458070000e43c40000384822481441d51078180e00c0c443c84d4080d1001500c100801c0004411882890301e540019482d0584007004000d4116025000b002c00240c1c51001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 709415017 1250 709413767 709413769
    0xd0204051c0c0b071104061212021902130f050403081605070b04140a0f06061403010b030d0f200c1002030f120c0d051807081207020405040c0b040b0c011109 69
    0x541600c03c0600401010a02d1018020510441158a10002c0c03007003154907515200d182800c0740d440b1041c1c41140c2841c80d0288581e001040d07010b241d0220b003090046080481d42000001c0081508840600340da6a889004000076841914080c0e0b01a0f12211840d00d81403030035415480f019160700d4204a41800000b000894400800b40c02c00d50000c0d404446504000640e85010040480902080b00800303808007480304551004003664594808400b10032280703001c4c03609881fa4240300c1a0154460010042e2461103603d10540d400843d00d01882210f011041000b081186a15100c01580005d0240b025034540101c415400000e680007450503c1c01090f03440c0381c9030080c0caa80841082c1500d000076810702c00d003c1203440c0488041c104000d00d0070400c40c101c0d200a2040008803e51140b07540129050b840020300e81c3d0003204000015240001766801c2c00b000d090041d02c11502407148150100f18000d1100c090b201500a20741320f507842c1c0441e10322190a50f40c140d09032520f0000204016001d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 709416267 1250 709415017 709415033
    0xd150f170c040209060f040306050a15050f010f021c020319030501051503070c0206070308040507081f2a110709050618180613031202040e060d08040b0d0204051c 71
    0x181c4401210016103908082001c96914450744000e4100404005004402c0101c10350100d400349400f0501001000506a2850069a020700403035070b1104c0100340003d01d540c480e241c04009074100d841070320341c44060000c00e00f03010050300c2100c1025800c0481c88001506c02c0d000c00c040031211a240520882d490100402c440c1c07491040c600421103000000580d2050040d01411240c2e40c3c041c00080d90781409043c02042c003402900d00700c40300e0040010000e10a54000b409690700b0510503505207e200c0c04180400050040060b01000f001900d066040c640b5081c00494003100420784800360000d039200541e504000c19500061030241ca80014401e003600c1301035003220719060869446960340c50b9011600d0700301000c48034503800b901c50041005018600f03084da0389003507842602d598041074002541c020681c0030f83e004070020340c031a001c0042e80034500035260300503903802200c0d01c510381501c8001e41e20050f030050244100c09070700040e00f04410b041c00d07034803031314515200c020500141c1015550540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 709417517 1250 709416267 709416283
    0x518100b06040302151303200f031e0c0a080d080a02070c030f03030207200a081504110d0b0705030f06030d0906180518090c030d0f050a050d150f17 65
    0x4010440c038070101808149080c100c8083e5003440306c806145e1940d80c580310003121110200e22210759904125041c45041662801d064804018060312040d000c01e800000da01050b12004c1000e071080d600724400b95142c000e0b1034000792100d40007401000c030001d50b0140003440c02801d24044c480c07040080901285402503c0000d403076005020002c00b00190408902901401202030000d4050b01c0210003182c1c040d101e0f207100390009651449165580c0d20144e501c829000c2d00b911250518030b8000307000200d1641c002c05180500a000b8444a8941d231250228680212001d0700810000418072a24075440c4101300d82c0007904030014031380068800001080c6554511a07042403162600141e48501062802c035006440098041010001404045c2545940503200184180129000302d101c0b42400314140c90f02e50f11607101c008103814200c038210340c00ea00504600301080f07403d22543c00c0d10904e80c012009206034500c007a01107581490703d4050050f003641e020824084181010803c044004140a4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 709418767 1250 709417517 709417519
    0x418051c020606060a0302091215090a23070b030f09011409300a0909050a0e0a0807060b06030112120519050d09050a031d060f0f07050705040518100b06040302 70
    0x4c0c1d110541c0b850260040c1c0075500c885680419511400b0820320300c0010100c00d8065a44280c601503103451603039507201d01c0e6445001c0c080c900002d10104c1d041d243d50a50741c0b9003803075440c201c410003603030b030102d446083d00186c03805400d0244c05414040030392000d002e20041b900007030b070503617000d4282002c80550b03401000c007441d01080401c0d20003002d513510001400c1312030200401040d595050401008040c82000e0150200007031900d8041785040c05284106040310402d03d0040c81030f10031549031110300b6005880704079030039a00c0300d00441e081c3e01c4160240d80248145984c000c00708880341b80c0030000c1000701050508215091040d440e000041901c50104403c0750b08280e80c0d5048030500c1d60740540075100300034140d84a031042030410140d000300010240c04000d07418081100c000c504020882c4109550104200d4050103810b4a60303a6250003003e07035603c6641203d8026540e44003107420f480040380d0000d001114503050b070503d40c400b4807880b001588255401c010040e042c1e000245540940c1c040a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 709420017 1250 709418767 709418779
    0x10c08070e030a0b0a15080a11010c0f0c0b0c100c022109031c020d090b030424050403050a03150503150c0c150703060501020f0717010207020418051c020606 69
    0x200d040d40b01407008091440d000301900110f4a000020701d0050000c072076201d00480c294110003d0040300124071a1007003580564011915894040112400d1504050944580c101c4c80d240c24001440d151040c03004002014415840300f0344a0a05818204003000d481e01c0c49040c03400104045d40c1c081140c000c0401480603044800122516203403082c02400384030394040c8546860821002c00e06014811860002c0c3d080300c81d0221003090489081e5107a12911502038000c1c000701c0d00140e0300b0080b090198240c1c51000342c02c4200e042c040400c0d5075090310290046400000c060301c2040d17140c0074401c082201080c450814a107001c002c01c1e40c1d25000400e11342044140340105000c84044000c50b5440d420000803501024500001b00d0500c400964140c00864500a8001941d50012600d041031102d18805407a540c2d16210290106000701c8580f041255820041c0f0001a552031180c1d480d1300c00120809440c01034249400707447e211208200041d01051208020411031380024560f5000d8420350311 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 709421267 1250 709420017 709420037
    0x1506010315090e011e0501150c030f201605010206010f030b0f1f060306081c050318100903030203190509060103030e0d06050702101401080c01030b0a0b1c0509010c0807 74
    0x9a038018200045c000f6050304040e0164015600b80b0780080c1e058a00130ba0650504410210082d0342c4100d51400041c00700340c2c44846a004c4038091480700c101c00b1003040c912100006031103986401e01d10100720014540070780c1d11080c041941c0c1040114003504200c0c0000381414119200d020042400400041504454100140400001c102076100940030020304900c100d84031140a4050b040701e000c1c00c001440f8940780900343e0f15040c030020103140c400d500c80f01e26546032540031101030921410401183c4c498000100790700b45051003044041402a58010780300d085c003400f142c510342d1280701d41185880c00c2c201407051002020a210341101d0303050820795100d003500e401080e20302100c1100a0415403a100401141d070b84c020400302c2450f102d59804110b103003000d002c03d810081081c0920111076100491841184d400317580a0040400d004101409035580c9285038201607100c2c507811069001c00650560724841580181c03031704081c58400074800c401c0c100714003c0450800403c15000c01c405400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 709422517 1250 709421267 709421291
    0x17071b050102130b1803031603031a09010906050f03010b01020613030314010b12070801081b1305280e0309040b18040501020901020c010305090d08090708030408150601031509 77
    0x10440d120103080b10f000354500c0d6035a2610708040d40080030040c070600d244402d142030f203107800f000701c4907100e10890442d5071420654500300c009084255640c940f400b402140d01038140d443c200610b00070524080041000790504092103415090f41030100d02988c140050303000c00340c1c0c0220b072031a480000351041950011182c03c04030301804505c4010000803404d01c0010445100300e0004102801200c24401603984422004450508091051154941010b0795031180300c1100d00500d114403100910218100d4040110041141c038296039a10424129034000c6d2520414058a06e48191718540100142d801c040e02454a070b110702640b1506c07407039685d41001030304d03600c1191801500c49908010b245514003460014000d500030794406016100300045072002e0362003170051a1142102c00080d107034501e0080c0c41551442c07800340500d84140030307030b4030301084074207080001e840240801c5004081418a002c0400d05500d4003510182c1003504100301d80b840204810087d00c1180d00f407100000c0d141200c52 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 709423767 1250 709422517 709422521
    0x80c061603110f070803090a06090b040c0617061c05010e0f0d0809060609040305250b130c030b150d0507060f17070e030c03030406030510090605010c0807021807020d17071b0501 78
    0x1010060036146010703030800510407610bc0c0342340f042e0f01c81c080003440340703840b840c059481d0040c00034100421075804000841d24101003040b110b1142e8000c1444100008030358445d400d40300c15400280245d40301c3c42c8130011907130003009003035003030300180c10b11308294180000c1b2180c403411b0003000c280c0a641c1c50400b15007014499402c03102ca0f9207881030382d04d104000000003003d030b07110000d5050390181c29200204906e2a914030200b80c04030b84c00940f102d0b00d28510760b110030310010002d040c80c0c004d07079440618401c0c0d87c942c40281d1031401d110b003016011a50030b202c0040d003040c244c1c12119080203400304d000801d000084000e940c100394513080c00307100380070f1810003e46004e1980a01c1605404041070001c1c0458142d0041d41c0500700b1032265004861310f411900301152014820180000c07221007032040460288402408403c5c00035100c11440c19002c6a0401c00749002c0c3c40c0c54006030f0200d5846030a0680c00400540740349080d6012014a05110000070198400d020042d5401d80c081c001c8041000425 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 709425017 1250 709423767 709423783
    0x702030906031602011b0228050304030c23100c02130e0106061b050601271e1401060504060518040e032d040909080c061603110f07080309 61
    0x3418555280f9000c5048a105200e41441d04050340c280680c240d01055144404180141158000c1501081c503150200c004050480102001c44a400c03002000c14000d00007400a14003d000480c0e280d407802014400d40700d000c1d0f100034001c3d0210b41442e01c00d9aa12503d56150b5403039803038203c84c01b17006400002c1808060038000103026150400b1002440019040300b021074506446c1d0a0714201d02049079822000c800800504a4202000600c0008080500d95068200c5003000000c0c12001400c030800f102c1c41c820500c1c10b60002010030070780001c184e000380100211000e1030214554034080c4050443d00444c090b20044c0300c00480d010711108810903010380e5006004005109408030500240d13140d40c0446c818803a10204180190080c500c0d540094014041c1c81d407016180034034040485d0b0080c0b00c3e009089a1440c8100300940701d40408214140c01000030480c140310040780e40354060121074030030000d50420301c828003a0131740c5107800c1001d0b94901e64000765110703540d07933a2440a03800d000c2d103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 709426267 1250 709425017 709425019
    0x14040b0a1107060e030c09040c05010f0c050f0304090501080316120201140129030c03010302040f0b03060a050f0a0902010507061503050d021f0603200102010609092009060109090507020309 83
    0x5111000542150311041044c21501d09509a81204603810306012224404031005440da10080300100410752145109008506840c94510303032410242d0b85250421112101e01c040c030381d1010405101c030512610500f801002c100c402186007203101c40701d0040080001d000500380034500b00019030214000c1d0090b18210703141d104604020341e10ba041d45040314038560740701d10005400d842c00090710849003080f80e0140d884040c0c100d0135607185a080102614603c3d400014060316040400b00e40e880030443d40b07000780d0301c600000c5254078160040d800c0f1144014942042603003449480da0160760803004541030960000c1c0701148196500b05042c0040401d40c0c4028124892055540c800544c0882c050808183c1c6428455800c1048079400064500034080604081c3c035054141005a0b0261103542c0908410b000204803655124030602c2142c102d0a0b007540ca0214009242c2a0b00300110640f11941c4000c4841001c1401c00304002030280c1c64601403092119990004101054020419a103030980 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 709427517 1250 709426267 709426273
    0x81005040c02071d010806040b04060f0f0c1d0d0201050f070f0503071b0302060904021308010f02040e0a05040305070209040c15110f06010602250b0c06040209010614040b0a11 77
    0x30055402951401c0500c03d1440c02c00c542013003264520403801c2e10904a82c0050010b20054035075403130360155004090000c840c816915a00340d01c480300d440c0030360915007510b481e001038216806100901401040d500d040c403600300200142c0004e5484402c0c021040340c0a1801c1a02da091804c1d40301030074070130054090248180c0341594020000000010180c0b070344906c0d41c14001c11000c5c088071850300d40034000298000c0d418030a44034036040c43d034013905070320211500031150690b0790510035084070b54a046500e1190b8000900344030003a01084941e07017007900f010b030030003007440c180c0c81c010101d01620300020b200300950340225051103001410140501050410702688070803548024010030480c0315440010700441d44034030896000403c0d10360481d01540c01070001c4518000c40351008458420a07002071061911012840714030740700240540740301c640018030060030280104039120308140c0c45442013056034041c100c6441485000e840844400b40e404540740c10040d501038034003030b000c0d00710012244 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 709428767 1250 709427517 709427531
    0x9050f0a06020703140a050d091b06020c240d02130f0603150b07030e2b05070e1f0608281e29031f05150612060108100504 54
    0x2290aa005003c11482a125180c0682d16150004440c3c02281c8820010039014000c12070715070001d8015a03a03c1d0f1060119100882905908201114007074002d880140e0002c00c03d01c145080c414404595417403080c80f05090a800800e101031980300310000d8843e19038000c21550720031140036040c01c001d003100c290a40e00243d120300e402001003640801c01d0381540510f001c0040d080c54984212405181c240d540e08821500000c2070107145500070440410301c800740d400c1541c0407d00d140e151040688140d0142580398601810002c07007640191480c8e415090300040a24100c28040710b80c0f0880f40d2904040001e0f030790f041d9103110750028218219849560301120f1150b8088254003441842c01a00165042c041044030400120b0b001039900300d0004120713031000a0189213100c00310300c074034100a0460340c0c090058040c0c600c03410910340135101220b0300d40b0306008020100d00408424030b5400ea50442c14645520001c07401d2910280505040c04281c1010a014801200c00c04029000c0a00240701c2c403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 709430017 1250 709428767 709428773
    0x9050d02030a020111030403050d1a0a0b0702120d08160909050c120a1a09061203120a0e0c010507060c030912021f18030f020a05060f01031203050f010909050f0a 71
    0xb54400450071006500e08075040e01d140822038180c900940c1c065440030300302040300705100b0080a0a03640c090361003507107624a0310b00355294800c0501405046508030740340da607c0e1050000070342280490810680040300102c0086603c0412141d00804100c0c0b109903400b000c010030340301040c071600504a524109010000c10745c0300c03038000305200100500a2000707583c8002d2198126005040d40700c10f1b8411000240c0c0d42c52504201503900203400a0100440c50314180f0300601d5940101088116101040c0402000e20180d01c20904ca8005e403e02074400180e004000814a01c00e120008044565400c0080c001500c29400141c0495000c03034800a00305810001a6440003100000310b241d407155058161250311a00600d8869a030000721308166000e2940c0689192403600e040004600c258440000032803020465240034460b4601d42c1500c84d41541040581c00c46076407085000e06003408207000f031440c3c0c1c00c841c1e24111141c28400242c0303412280341c020300788034807085100c0c400c1c4103900c404014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 709431267 1250 709430017 709430023
    0xf1103070b091008010e011715040b04140703020f010809011407030e1006300606241b031b02040501030c05090115052a0f0606040c1814010309050d02 66
    0x1c2ea140442c0c244200350400b510446460f80d09000310032084549900401400c41018000e05109224100350386603c200d1441070900c610046030251800100c07c028401400f00750800c2c1110010300d0030103403030200d0030f40e00440e07108401e044030030b810041d82c20000b840c0160294001d10801e00300211181142c180f40b8001000b0b4094032036032071441d0045640b4140f9001c00c80c81458212002d1844481c0703110080c2c403104241d403100e070040c1c59000145415020006a4510818014000301e0f40040c40a0001140c4c228595007802d203524240301050b410803220050300111001800d5161400e940c941514032158059040c0f4840000c0d003050800c0d002208010500c803410054400680340414983e0341c5074840380c84004648110b0021407400c0000000281c403455403000c00e0740c1940d85450614180030710191415001e070f200411250440350501c04145003074050083c50390154a4068958103a041188100b5480c510441c480307130400a4024140da4040c2e004000129040b2050311b40e0315200700c5002c0d407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 709432517 1250 709431267 709431277
    0x3021b0a090222080c03060a0c051903020d15180c021f050901050c090109090e011e0c03150f05013501140915040504060f0e0a0201090503010501030209040f1103070b 73
    0x1440f018180105254030000f90001c603421008000302034a03242e4141a000800c4400c90742d07004c00034204140d03025501c201c0c00140c03003d4507070303a001659180070401c104121400c48112070201519180c0801c82c0002d043e4400412290040c80090040300c0e0081c00c1e4074002440c661000a00220107101d6140215644810f216095070070081c0010764840b1403c0c90b0b244900741c0c1132404206061070511a00754103500c580c092003050800058500c400e80c08154a003485512140380c901e88900c0d281c4101380c0d141c00b811303c001c0070305511858100d0510100403140c0c00b080c00703114100810745800d1344d8030200c0c05540452203480740b610703007510103864110000865000d008200380b003000800d03481030360f0400e03010303403441009800d501c1c2d1503444c070840c02c0102410b00684280c0d1a907840300c04a9501407800d200b03811554840d1401040c0c0c0d4001440090401c0310294499031082e45814010000f60325042d403034980c00703984031041144c264940c1c640101410308200400d901442180c80224a81e002000200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 709433767 1250 709432517 709432567
    0x906080c1b011d1b10050a0e030a061e05093f0c150601093803010603061202030c0d02060f030a02070b090f0714060f0c1b06040303021b0a0902 63
    0x94144e02014940180108100142c02d0300040419400c02c60544104040c1c00001694682188484244800640343c549401401d40e0802d540302004c1155064442c2e194102008841041c030541c44c0c03520060341c6276200040e0098266140d02602c408109980400707510806120f201c2041c1c8990380c0e00742c0f10150f0045900030700e1520600305040c00d400b0035200480e106090507910064224102a0f0340c0b0000600d02c2e1428800c601614500c659291420102101c102d02000c030481d06d0b58076222300201507520342ea000015040c05980d051000d42c40c082441251440c0c1981d6030081c03001c5500c00701b241c620603190039a040b0f641c0403090003820140354000781001d9001c0d65000307813a40c8170003004d1a1252490b00300d151050744151010090600004940f103a50303030b001450300d82030440640807540c4a034031150030b428554001c10100d4a0008180305850b9a006040c3c60403401e0a085640103035860060060400400000001c581e02c1540c40700d1008004d0240b027001507480e2035103907180307800e00b282d1050b000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 709435017 1250 709433767 709433773
    0x1090f0f0b070213020a0e090106140f13120302010204140405090a0311010b1306030213060317031023010e090603030909040204140903070605070906080c1b011d 71
    0x154400120006005560106412500c85490141d00d003219620291040ba00300302e80200114200709070744040c0174000465100c4809550318602041941e140c160001800d01940a14600b038688180040d222860411844191384a1582080d0100c85505034003035100814071050030f404140d0306401600448060108404400311102e0070042601c000722100b01c656880b038101a40464450003442c00802c00550001035a883d8440c085110a8008666060425101c400400c21403c00d50342160502d07001100800400703040d941c8101c5070217510901030950541c040040b07401451500113000040004804000718001c1c00d04048003c00084c10269000c40e00f03400048145061001c0340034440c8500401451a001e01c0c10100091000041e00a0380c0155031030034400801008a10b0b0a401100000e000b96250710907880c104041d12001400001000181c9004011040d00f000d84103400511114400380c40c1c21401c161341c1e042d1100901001115800c00a80e801e15600108031061075036030340300036 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 709436267 1250 709435017 709435019
    0x3250803011805090c1e0d020402030c0c07080109020604170705031c0f1815090305030301091d01020a0206060112020d0507120f022d0d0504080d05010e0f0402060c030f040f050109 79
    0x1c1d103a10703045c828422980083d1a1140000384d050480600070003204002c000ba0409640380d0003045c121781045990480381980041d0000c020340b000c01891004020f140000d001141150b40452028011845503d40c407541c185480180341905020020240c14003600b2039862010342e03c0720316011040c841c64000818101c1c0040d01075036204a5220800284d82005039034203d1501c02d60304100200c00000500700300d54920f020000810500c015070007402c100c200400c12003141080c01f135440b103118415151f20303071041081c454900c0d00403c101e03a0100d000d007000b40306881580e01c1744000e4031a01e90840c01c0d41b49400304001310103030042404140b0300032101e0208140c28200c1ca0441c1240704101030707c85441d2002800f280140784040038400c090340d4001070340d401c04c114241c000301620341c10344003113581d02c5022403c0c05900d80030384942401040c41c1a441740450a0141d540c1c03484640181020f03004070740002d5001a06c010400894070314141008103203603115075805a141145080c0d004e01c0e40001e8803104 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 709437517 1250 709436267 709436281
    0x204030204060b0a080c0f0c070e09190c0e04020f06070308090f0a0b0c07020d0f260403030f082a04051201020f0d0e16030b04060506060c03250803011805 68
    0x584a1010590f05d907400305850342040080142c2020400b02401c81003008886040c1400344026001041d071401489001c1c14000442170802908041103010b5400300701321140480c4501071048211004000c41d08103030348441c0040744008100a8217140c0110300004c910040551184c0450712404550b82550380c81d0001003145038030b641613080080c003400340c040049150100e8400061144501c0107000c0c0c50f440c4001d649407030a00071a07850540d45645054410158902c0410b0040c5401507201d040b2450903045642c00341010580d0003445040110714400507134608111140250107000c0f00203a110710110814035198207a0150190741d0140048400348102d10105009490041c00c003174601c98100b45441c482c000040c01405a01c030802c0c03081f45580d03030886280c40c0038603000d14080e019030341681c0740500b0070f00d054400291845000f0349007003100d0603030814084195240b01103001040142d1900a2044503415042903c02600b019000000055664030a001c0e501c8101c041c06024801c5580b004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 709438767 1250 709437517 709437539
    0x3040b010e31062306101704020a030507080f012a0503131208010801150303090501050c030d020c01090302070f050120030c0d020d11241003060f020403020406 70
    0x5039454602c4071545400e050512044600c1e4550345408144041d940c0000d40c41c0c403400d6401007101000400d89594045100614a43d41c15134810000c0d107444220184000004241c2d482205c0c1004045501602190465841009140041d5080012200301c03680721000f0a480f0480c060008104e036107000c0c04108034220f0a000c1c000100503144000350190100d000654882e440140740342150408410250002211a120341030311400603540c2c1000ca42c1040000e508644141c86100b8410001d01c40070000030354412602015680286025911030140400892442c050380c0d000201141c00894601c03040a01540481a00c40c02642220b105070383d0359901c2070326404180206800110300e1607408032500168103c80c0f18100c0c004049a1600304045202e901301301d89204404010b0f0402c43c00c0741900c41d03000f101c10f00b81b469480d014085045240f1450a0194588180c103940c80404d4070001e807035440100c010304001c5402c00000c0c0112103001c00100001c1d030040c0001ca100310301d40680454400291 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 709440017 1250 709438767 709438771
    0x160b01090b041104141306060c141506040f060302060c03070308181005040804050915010f030b22020702061c06060c11130e030f0304141219180b03040b010e 69
    0x14880b104c0c509030501001c0404101210761440e080901c83e0513284070103020348650001441c0d950b684052240082c0303001070031031148284a40c90750f440380007103184600c40808410f801440899001460100361a01c05000c1c091550000e54130050110b0034030582400440280f02a03446a0344040040e42c0f8024041d40d6224401002c01c0103520290107843d095801e60b00c600c0d0400d000310b0303299051030303900c030005814100c0c220740120351603520011140c925600050694002e0400d81400d002d80f004100c0032940582c10ba1603048607459103804200402c1d003450741107800068018100e540c4e07890303210880c00c006c2110700110f500702a02c0d2103c00180c4a00c01d22044a003e0790004240300307104225000c01c03001d02051001c45070300e55070b00e840301100c0084c10001020702002c1100c280d85c41e0310b0a0b042040c03c20b80d00c0b0000e004542c11400761050b45005c010115842428440240310080d81c0f200703003c039042280c90310400381210310000042201824200550b100340e105010301070701aa01c03200c41c1c45006c0d5013 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 709441267 1250 709440017 709440041
    0x1050109060c0f08091e190602121b01020406090f0e0403140702030f010f230f1306020904060609090b2e030b0415291e160b01090b04 59
    0xc0002d1140090741e10000000d8040c001c1103614140701c00030703001030f50301c400c0d03028000c141c002580c414a07420309000821001d17110a03c1172992080c0c1c517242d0045d49518a1404d942c00d54100010380d1031a42c0c030307560380c41000e442003a4000c40d15541c4420004d400c4501a00503203003000c5250400003a903111840c21903114540c10f5071102c6200a820030100150703084680200e0b40740c010f1a030481002d100902ca41e4040c1c800418010640b403890f44a002b01300c0da0f0040741c4010084004080104403032680880d00c1d005003490700c034000000ca039802d08900a0007030004007a84070b810103200081c001e034480d4240066940c040c400b000a40181000c03c0b0381d01400081c0014040309029590710840416520f2400301440e5003408200310310384000060485a1891886404c0e03202d205061003990060071541c1c90f0640309008034405150403154602c0383d070203100744030078600000c107910550304600340c0161400803100c2141e034103422030b86140c0f1a4456600f401031102c4d6a291144142075468603004110324013803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 709442517 1250 709441267 709441277
    0x706090b09061b0105060a050307080a230609060402010314070e0402090112060306050f0c0c060a0203042a06030e0d0903060216021c020906060a2f120c060105010906 73
    0x4500450510540c12454a059100000307000010f81401161022000001c0c6200001090b103040010454204e01981205000754082081800345020004600c0c100035000302000c082c0c0c4903600c030b0940c010181701980b400c0b58060a400d0011205000030b003140214403d0324103100d114a0343d80390300d5000904440c1c02001800310030403520181051381c01481c800c4018074141501c170080c0c0103c0d4054420b10340c01154440d64810400c98440400f100e26500300401d129480d10f0840d601c50b5150343c1d503002410102100b64008003040412688884040b9031a200b40b110550203642c0c2c07200366104100c035202d81404a810004504041903000c2a03a02100d441c60b2280d04c1038034111b07200c42d4000d410075401985030144840d000380140e034810040d000c0c401c104410500c2006258814010101009818035004050901060f80311541100c00c80054a04010400c00c2c403013020308507002d6921070f002d0000f0b0070340184441030601e200703d00004e0941e00c50078406c40d0304503660f070001154840102d00c20175000507 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 709443767 1250 709442517 709442519
    0x3010506092401050c030c1f0605060304060b0321120f06031906020d0504050d1701030209060d1106031f0b0301080a0b100518040605060d080d23040609050f070609 72
    0x25418070984001c10750189012824416115801c86c90340d4440481012942e115080304051941460882a180c0524103018810030b49003101040c00e5000250004203016210055844076440070000301281da440b105110b90b04502c502e86c9002c00d80d004440000300030301079800040100d5403e011f0a4015a00580100310700207082e40300d0304401c801c0c02130031100c19400b0060085400c2943c01454090341c050070150101d14000680940f00310040715121b04080d98850041000d6a65070ba041988028161a14070083e00c00f0720700303078080389132924185074024000320a03c424081404401511180c0088404003056115070407880203001c01d01c00c0500d240d0120745600001408200d1164021103030907118446c90b611000010b01d041e04840c01d1781c0c09a11050204070500155000e071035041081540c40380c1d10559280c4030b40065102c0c90640040c01521210504414002d0b04900e400040088403550580c0c1064500703000540402c2d0340035075032881022001d800c09040410380c03e040750741d96190a015a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 709445017 1250 709443767 709443811
    0x1a280809070f1e080d1e02070f06030e0a021509030c0f0607021917030d06230910030b010e0a0c1704020d0218090d0f0f0905062203030c020301050609 66
    0x70950601d200e03c000b855040010460803c215440c00341c8082e8450f6840140310546c1600d0701101003d501046520880041007500c01c0090a0415540e0a107404200041d02c00e41c0d2074645145024000c0d080035680183c1004080520b001d018040303801c0b0141c8030100b4440013000b000280c40c02c042d5a02040422090006182009001e4500c01d01498601d070013903943e05024010400c101c0c60304a00340c2000491780319001051041401400035060380329400800280800c001044000107240034a0155001c50b403000c1c410241c1c4030040d0b030b00440145266845540c50742c0c10300c03800c3d01c00d00c03207040c104422848a140180300c00e04020b42d144028801c4d5036215000c01c02040c078900016030b0800c03c6507122500804912460600c0741d1703041c2d4010302801c3c5000100611219003c1700341c5003007080203001c0c1c4602d254400c891608455003201c10549503100303440e404020300b02141004400761301c2d002c400000c06410001411000380228000c008a075542c0301072281c0c21604461031007105801702404940 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 709446267 1250 709445017 709445039
    0x60c1809021303050703030c032c090a0209120102070605060906010c0602031504020d020307020c0f0d032307030801060f09030c03240614131103011a280809070f 71
    0x1d1071141c001000c02155494131404c0c285980358105030000340358003d00e8002e064004152601030034a001c40d429a50003c2070000082000881d4068070070416003004c2806081140c050b0b6440350001045548414a2000b40d58001d44c04060100d400606220001d001c0c0e11b030901c45944144c1c81a19901c00b80c600980d2148020760004004207007841d022400f404039500e0300c2c40902082c03050b141d00160340c0d040200020349003030781000400c0d04ca0300c000d9840c424503450f20b0681c81c92065140c1085d11910050090141d03005d0050389040380034941c049440c03400d0650180503e4103c51141c1c50710400c11040c1081203074194000d0101501c0303014a03000400004000314135401000100100404c1c1c01c6620a80040c2914240e0f482800c4960411600500c507242c12003841c3c1004409030340800c000064405c408103d030005100d258202e41004c000302ca45e84a60100310b0303540f000c00b80341c050560b48115041c2c1d0742480d090780060f40000c0030080020310421000031004151854150007100441c90503103070020b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 709447517 1250 709446267 709446277
    0x130510110a18080d0e0414090309120a0b16080a0c0f1202120108010c0212070c09150b19030f1404120509040614010e0108071706040608030c0a060c180902 68
    0xc0c5a66280b2000926a9000d2103030442e00c5460345d4440703103161542400c1106895a0000300707040c501c8060144240e400000040b940c80b543c0a035074240412241c5c041450070400a0340780600b004004d0010005020a4440008100840c03030316481d90a803030300a154800c40341c203000d04d8030101d8801840e90405501443d40c01d490400031450151400204a0040000520a0b80800140d03911440420030807a014045508501840c3c40030320300746107160300c0d882510b1354584145824141d0390300c8943c49848140046102074801008419075510001414000401c180455600000d10702a030340314403826140100c200003504407090180030b460f0794544d0018942010344403401e016082000c44d83c0c0d45c03038600610008010044044500007541000502015401940e1604105000c401c1003603035900210510f4840410f4801800e0964600303021800030071043d044110203200c0403030a80344400c000102440c0c1503100d10310900881043e41419218021100010750000c00d110400f0720110b101c0c1c0d400782c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 709448767 1250 709447517 709447547
    0x61223070e19020706060f29090103020c1c2d1202130906051c0804060f12020d050702120c0727230606090a12060b0306130510110a 58
    0xb08070207100c04500e41260700103142104d0a58603000104000b81d06441008000c02c01040c440070199102a9010503041540001d1710b4185d4010450003d103900c40d506807800318000e042200c1c0c076034a041240310108109088440c000502040003001c0082a041145283c0d0781c2c80d80701c4c202404450b08043d42e081c0881d0f5004c4808a90038000c002400c4940104c200041c0742a40b400105d4034281420700070400b041030000d0000b81511004030000555880884080768540d10781850744440342c031808c503220281a10300501050001c119484011481c2e0b0103203001d40e0240d02240c4a440101c1d82c840042e0044000c0b13500d20381c020010030040001014034240811100c4802c1d440d641d494901d0740c0040b0fa8903d010720147e045410204c0540000010240b5000402101c0241c28069a9000101c001010f400361180d000410a481400c000145d00084003811004003550624a071906a02780b0610f10520241d8091195409503100300a4910403041515040300c3e101d40b070070f40d400b0001c1d54000042d00d204 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 709450017 1250 709448767 709448791
    0xf1a1e09010c050d09300f0c09051006300903020c030a0b10060c02030606060a0309060e0606041107212c040b18061210061223070e 58
    0x10000280700703110400c40000349031117818546050002141180901e0f8416140d450b21074541c484184e00318030034014403e940070326844140c443c2c40c07429100f228030542c0610b0035181440706020029000780a000c095501036601d600d080360200100c3e00c036121800c3d54100c0304000e6158070f03501c80d40150700711003d001d000c0c0c011180c0321219039003c00e2130f00d009104c5c1551220707002d00a201c00c080c500f540c940001c007001d03d482289540d0039000252107080250130244070702304c0010380c0314002d8001d8000f81310341134000303c00700110541095000d41328102150940d204a107080c91403e24500800182c0315402d40040c8004000001c5055128000c2060540304083c03020700400011030084c124881c600d5484900240c407030560031601444292028800c6d40d5200e226040103206500d864078600d258059011503210381c4890b40000301c20f04003100700e140760034098100140806d101c658510f0351801c45105500b000a07501c40b00c5000301c81c0442034100400e5540159004024210150b41c035550404403031000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 709451267 1250 709450017 709450037
    0x30f07120e0d170c0609030d0e0601060512151908071205151e0a09020108010e070f0f18060302070b060a03200102010204170a0203070803090310020c010207050303010f1a1e0901 78
    0x44030f442d1140441b126512540700064010000301180a09200b00e0182402441d40c0c2d4107100f0054558007039200c40440c03820600c0300150740301c020084a20305022024080e00031036194507122040901240c0034401051048000008108850a007481c00d42c0307402401038042c02c1000d0760f51140d00c45000d400c00d00310080312001c3e00e9000e2100c2c181d0501440d801200082c900300c8a100240900005034041a5110042000c01c0309054005d0704031502291140340403040c2c82c0d040e41c02070b00e00805489904007a02c10021010510603019030050201c58000d1100308207030340c0c41008000c0508034900006251384900100300d038101c0c024106800c02c840050001504103515811040e50003141c0320249501c1e0390184116034158101031041e10060300b420b00103146045000c3c0082666401316028405141d6800901807c03101001e60640d1503903548503040d03a03078a580d108450020900c960191a90303201d81d004549441000480072505c1e01002018403c480444100d00030055811214030345040c001c017620 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 709452517 1250 709451267 709451287
    0xf0f0302040b062a011413060b19061218080f0a03020705150103120e030c06070201030912020102070c060801030b01140f0307150906081026030f07120e0d17 69
    0x440071280700b4003c50300041c010f07001401c0c242036510300341c5010f54600320b5500b40070104042505c039511f01a0008004600418040041101340d503410b40800140c05030828041f41c0e499000c0b2480e0301a141480c3c041c40b406480c032106040c142d4031110001c041d8142040888110401e030b40180c4080c0445003001401e24546444490070110750840f4801c01000e810014005c0140c1107078211029041c07464030300e00c104c40e00030110f80e840f0b0b032100c40345108a40100308442160320982060810710703030103402c802450384d001001a000c6e4020032802c40e44003212100210f140f5109440d0b080c100ca8102c42c46140c2d507407134510040003074440d1042464001064406041064904100c80d8005008400c0550000b50060788010310080468200c082048a12014800b50f2140070240c20256543c0c20304209604070313449404080826a810500101d00000c0740740c4030344840c010054040302e402071800003001d4109010407100d84402113101e80d8407140400f41d00c00422003005d480c4525600c1c100c480d5160590044c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 709453767 1250 709452517 709452547
    0x1b0501020a050d0c0305060a0326160b0708160c0305040b031603061a0714010617101a0306070f02030d06030f15020304080d1a060a020609070f0f0302040b06 69
    0x10708040840c000060403402c03928140304a440640017460304005a081035400151080990b03c0b000d4142c40f601c101690200c04104070440001c040c0109280e501c940510011855110201080d5002503040000a103454012002c880c841d0031412100c41d110a840315055903c40f00030241902001414000410000000340055020b01070040d0b20f140c00c2e0b140701d40c1c020309581c1e1940100070f4840d01ca1120b20084000c0c123041e909816403001d41c142c902c04500740c180c1c0c0140025800280078183c0d10000c00200c002c0460581c2901c001d00b0414402c405240848490303403d101070760030f0b40681c0044000340b51241b044850918460152040c2d91070006103001010584400313070015200052a01d01d00c1c010072070507000d0039035005c0c0e04401c15410b501c1c2984810000d401800b6a4959041d01ca840c403000e28101c040800101303600040c01d181d100c5107641402541c1740c804584100c02da20a0355030100327408440d5000e000c02c4883c403030000300301d42e82141d080c04080d08401424940090051200d00d1b2022620 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 709455017 1250 709453767 709453777
    0x4031107180f050c090f1c0c0b040602010f0b2b06020a02030c0f0f030f0d06050d0605060f0a050a1a0f16030f0302030f010302041d010c02031b120a1b050102 69
    0xc40760104400c1e801080001c211080074298500d42002003000d0706071601e03030445944110000311030307203c80c1c0c910071a400b44620014003c0105408508880030610903c1040500300f07440b89a4000c01c502c0c00c40c446900106e40ca070010040e4014148010355560a44c000c031010300105146107840b10b0b2512640c1e8130001c0e83c01014102000d0b0300085840720507002c007088901105d111040040002d0340a1040f240d40303070301c50042410402400003414800072500380d0070103001131101600310031400b1013070306051000b0842964010f104031840c910a078050303d0060345c14030694a0041c20001d5051602007178049046030460072404204051003500b00350703002003028190313900075040008203c41440c03038014043c4032486280c0050520601c1404240460030300d4140c1503940c1920300085070b4100c03030641c1c20440105900f201071903003460a4611026400b1010301036120392942014042403820100e1911840c3c10b940025900500b40700311a070070380c440c070008601c0f00c2c00b40c21100b68120f01600c8903401d903480 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 709456267 1250 709455017 709455059
    0x6090302010b15071e031b0b040b0c07110105031306060815011d01270504061b090b0304021c020303070f15051e040302010f06091508030c030304031107 67
    0x1481c0701240340c5080204201142040f15540e261426280d681d0342d40300b16011150940000081c00c0000b400c240c01002c0c0002462000003c3d450400054586200400c508542c00c81e2506c00c0c1c040440c9420f403500342900c0e1032692003540d844045210707000440c0d4a40009180b400c400c883e402403c004164070384188400340440c00701800240b140d280b07200840190607070003001c1460401520310740950f84401403506403110b0188010320911035800e0142500c1c400b05a0048445c944001d000070080c49602c50740c0f003041c400e000c842e1858442a4155015560307071145464400c010000100103241909070807002c212041d11010039402c45802013480c5400070b01040f0317601c1605030503090a202015107102252070000c0c9040c09286003c3c4650310101075440151202e03601241c012a0030103000f074108110800800f1010450180c1d03801c801e8010b010907421403403080d00c84250100c5c5000000c01140c034000d601e00011891500d440d81c0c02c80300c0b11110480c9203001c2c010410089038040400e0840c50645070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 709457517 1250 709456267 709456271
    0x605060d05010801240314070e090a0302010b040e120705070b0a020d09140a150e0402180f190b0a2a050c0a0f0b0912010c0807021908031302010c0609030201 69
    0x2042243c02c608480e650050001c0850080711158194817003221008140c07540441040d0140e00c2101440e841c002d0300303800620100c1d071202c04008058a00281803901b0354044c1d802400200b108000780000c0780c0c101d00e00e84250382c002a5280001b070500f070700201030340d91080c0110303640303140e540d0110341954211011890068000c0e4002080582d8070444000c042c2111181d81c0c1150040ca0000034035614042c4541c0c0207a0701510b0b21040328a00a106008055101404c25940c2d1409500c0da80204200c2e0445c2510820b0382c40171154407401c160160315007524400341850781150912400d1050743d00a1802102084040240c42c1480d0a40d1250740300c1e05514107152100088081c42d06a0070000744441d241d0207034032040d0301004a4480e018403041119a0307015001d69038003d103004030748403551a6045440a42c00c001140c0211030b8082006441b4400c01e6096803002850075103c40421100c800c0c000d05851002d00205032103c242000c4004a540705041440070304246540d0074041d1403e150b07095025035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 709458767 1250 709457517 709457519
    0x3011103061801050108160c0b160f03060807140d06060e010f0b07021809070e090703060c020a1101120914010609050c0a02210405060309160f060f080a0605060d0501 73
    0x10070300c0842c00500d442c02075a044090342c14000000c00c4920020071951080c2460a0324113843c0340500c0c4201c80c07040d0810000f24080c40d000d000d0756004071110b40e5600005a01800b041c040510a11925040c0c43c00c1402900c64503180c12585060505007100b21940014524002c030000344161180700000c02000d0200c4180398901500d001840e000b079805212000002c201080042e41c690160000c07a14010018140380d80f078440c091071034001c80750402c1040501110601c280c8000000d18034003103d10440d0b05114110800780100c1c3c85040401c0c00503e40b4a071350b803a0908643c01038429540fa45000f82c400a94070540761181e024801c0b0800d0b204200d80d56614040c09501da45018944d03104105594261500f00980402035071040340d0f80c1d03050402c0c11102107505810b8011000c41c0d008010080c81180c4900b0041411910b8130350314008002202ca181d03c0014a604040f0204811100c054840e00300310080d80c181607810010044c0141c407600d40c1e550b4042007559400b8060100c500140320006029 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 709460017 1250 709458767 709458769
    0x602120a060f05060f093a02030d03111e090907170f060a030f0c0b07080d05060d02010926030c1f05040809130207080d05090c09041e0305090301110306 67
    0x44030342c9030455806508100107404c4240e00010403a19a458151804080d52140e46504c2d298000040d4441050306810f0b01c00780b0410785401c0b00c45604500890070f0302e000181c41c800980403516a03610601001000380140f218591192905100b1400c511902529040c1c800c0009114103208331610400300f00c1840c0c050114141e804450307a40020b5000500e2000e0406000041080e100c520000b030001c554802d20a0410020034201030041082c0341000c1d441d10802d02c2c0c040100d40100003108d20140c03401c0002003544c907041c90342001d0703507806840c1c0d020490b050000c3c1d840c542c00303541403081421000e4034400d000140100b000302020101000900b00314201301d1040d1052404400b0f0220b402400c241c11b020100344040c00b181d00d02503086541000b0304280d41c059102a0061020141030440e0100f001c0e580000305070004c91003040f060084d01d802440d020100040c5d000c042c4c4014103290241c1406280c5138030000102c3d00d00c6402070030320301d0078200014006802e4404003c20050b02e06404000d10041d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 709461267 1250 709460017 709460039
    0x10f09150608011401020c130e0f03091c111302041401020105010b0a0302070201140315012616141908010b0f0a2001020d05010806160e0603040602120a06 68
    0xc003440380508000e06515140000340010b006014146103640482e608981507130080000054050001d00040e8000d800030a061000707150740810700405028009003035030100e90101c200c40102400511318000890b50130066a00f046a0312001c4840c500b40000814003030f51000d12100d6140303000c40c4056034a40c18010145842885429441c1c15681450014860702400300305480d010a03040c43d0042e01c40c040390004840c4080e0301140c80341c2401c0000180150340c05c091481d403607290404c0c0c0780c0800c04200e5030742c043c20040c1140403192009200e41c0102d8200180e40c02d02010710040e9151180011440110030074031580013510005e1510390910600d00040c0d0000c880c0f40c01031001809041c206801028810445d00c601100502000319140980d003030990400050152400a04021501c41000d04040030041c402030040824911031480025a200c8519003c401441c00980d1000c801e40b4284041c44240e400160040300d03859002d120f89075000d032041d501a44206c15110011440301d24140c2c034412 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 709462517 1250 709461267 709461281
    0x4020909090f0106120f170f0a050405041b0519020f010c02010509060615040e060105070602040303050a30050c160b10060305070509010f020f121e1e07050a0b010f09 73
    0x4170080e1580905000c01d00401d210407299030001e80966503c80042e0507401d040c031645140c80a0032202003000603070300358000d000e881510019070f0100111001c0c683c41203003d410700c80d60100006c004101c0442500590041b1588803131580c01250200112501c0349401c0d41c003000e0706540140e42d11010000303503101c208681508810265155004120301d2070300c2c040248114001c003269003001d80f005c14006e92280080750040d035005031045488030303264a4001c1503640254aa14005040070344416080d900070b111203100001c01c1160504280700c403010700b0700507101c001c00d150b070740240c1404002c192118945413070194910030f48081e072a614201903003a92003446508104101461704082194194110084030b14509090030000c901280a082c00c0303241612092014681e8001c0c003c000b001209100082c18036040c036050b0007100d00040c5840014203014210300221024040b070080070b1101049801040d03c035000340b0944c1c0558650340c486900c2484281e01c07801580040c198104900f0a15108080b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 709463767 1250 709462517 709462529
    0xe030114150f0a05010f05031b0403080a02370203120408070f0e07050412050a020a0609060f051e130e010605030a0c0c1a310210090803070b040204020909090f0106 72
    0x1c940c03420300000030a0304c0a0300810744103107c0b000011410350541c00f91000f12003001e4001d1503545544034686440b40d500070700307a424054880e94486407120b40cbe81300c5520030300214140500c2d00d011840d0308880720b41d42c07850300180d8041c011030303d903600d054080500030000352841400600403d854000ca0384081716855100c504012040000d008040740c0c014129030407921032011100111200d42030290800d0b1030248002c0d4481e500d000001009600002d4440458500342c9a080e901010660252202d100304a1002e4001901d0704880c0b6580d022900640000c80c42c1401303540e20940c6071341c0c40c4820802d00382c0000022400c04420080618000d01414400007098902428080c80f9540c40700c1c80800003410703054801e0200c0000800c01c030b00c1001484035800107041400f250314540c250503968240790b4141a8000c00c11850b6003480e481c000c0e04060110f800c0d6000039480e0824903114007041d08006001241e00035001c1000400940c1e40340840e900450180c0c0c081c08200180340b11031421101541d20507 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 709465017 1250 709463767 709463779
    0x204060f080708040204020a030b0319060b030d080a0e0a14070503070f1202130e03270301020c03030c031f09050612120d050a090b040c060801080106150e030114150f 73
    0x2d002c0d0f5012840c50342041d8165800f41c5c0700e00e000c2800340c0c090080030005a8143c4620076503800c0c802300380302c0501c1800d4066541007142100780300078184c0303c155005c03170880402c24610204003040c085601002070112100c064400580f180d0381c6044500c00c1c1040f0902081d413000310240414a824131058005101c03441030030400c1e500d00009140740c0c0301c030040c003c2d2140450034003000d200d0550340c111401070f082510541b0b94519004000204200c080311001415941c17842442c021824140b00320345150042a0040d415643c40d000d144da041c0d4002048040c0e4100795442c80c4074801c0c0c0e00d0300c00c40058550100081010b15041c010710400c643d448070051007da0040003240d035600840c07002c0313507161405400086001d139210012500505600c800040c80800f0701000c00060141c0851a0340983e5846d0b9030740c0200d6681c401070303a401e80d5071a0090040e0002d80e480c0302080700d0301a05007004e51210150000c603117032887d0745030304190410469901202d02e034062480c850a1601d5a40d2060804c8100c1c0c0d6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 709466267 1250 709465017 709465021
    0x708190b0604051e130b090109050c190509070207120605010e0907230418031e171603090b091b0a140105071502030903070201120507320c010204060f08 67
    0x705074408540846160700f16203000020540310320b4030020f564017a9400841010603410182e1561707009044000c41036a1a010f01d000c25007041c607244400c03e000a030a0000c98552900b407a040140c0c0ac2401b500003000d41c0309440b000a0284081c0c00c1600c00640100310000341c640c9041016100da400003840c290050304420f2050012510b10020300282d183c5440d0b40c3c0003402c0442011070000c00200d205401120b150208010405034014800d00c1407200b020442601024441819642c21030f8180e4200d4504d12924001390700e00c3c00040054020155903e008544190117071501d40c5280c00580d2480c0d1030740c00c01004070360b0069200d44126000d450903220242c800e4071b0007c0301403918581c1d80a650400400041c50b03414003403076514032a481d2100500c2107640342020a45196a0703401500100d000c07a040c444881004509441500d01c02c0b0010385032003080c045254562a00c0880040b1003498507200e544020800c2c01403040036203e0098100001a5640c0c1000c40207000842d50350511010014039000f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 709467517 1250 709466267 709466281
    0x7030c140c030307120906080f01030f030c02090f01060e150306060d15080703060f0e06042406060c06050a06080a1401020d0203240a06020312090708190b060405 71
    0x20214205542065215000d844900d20007800c000a20301c0c1d1503494407000c68004140013404110620619441c0c9440080aa454100341c51980040744d0300c0700d044207079100400100355500180c6035800d202e8503195081101660000c0c07000182078aa104050000c800140900703a004003c6141094044075481c40c802e410901c10f46540c48001c040600490011444c101090801c1d0014000c0300300c0100d6034880e0f261606060342d40c41d840c520051700c2c2c0f54280029074250481b03904c05e204031440020003a242a50722034550315000b071001e6902a4800d6034082e150312410502d4410b5001914169030354580d0001c071802e000090b560041e08240d07600346044030420030704a0000740e24170081c0c3c0c0007240005140c0505642030081c0070b900011404c05000004100205c81e00360414414243c21000b42c0c42541c0740342090050460b4079008a2001d80d000300a05160301010a5405500c0b0300f105086555403501c0380c071220b041c401c1c283d41401c0030034044d0807100e00b001100c0c1e80c000d42c800c030141e60410244c50003030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 709468767 1250 709467517 709467527
    0x9010e04050f0f0a030c110901081f020a0903230f03071a091f090b0f09010c110c040b06070204020d090c14030d0507140703110a14060904151505041401050703 70
    0x4c0203042c00781340f480d44400c120000c803182a65880080842000b50380d0b401c00d0b00d84851001101001e84401d480203441e00503400d20990f88290b001e0340d00c0070070700d0f82995200d07248150085680080841a40e10b81c2d10202c6040021385032480c491800303103844140da0b1030202a44101d49115a0404035003804010a007a000104000d410708800c01c01c80a0b1140da01c540301c003d05030b602d405004002610100021050715180240c028a1450000c00c0f2080212404841c035500b11103c15040f900700c0500c2c5da8140c98140c0014170303c00d00017401c191030110194002822684103071100c42a8540794000d010900140905001c0107022007820059500c8495001a41710041c018001c0188075000c18003006100520341201e0480103803c04550080c1d45070b0078807212000d10b003c5018407454020034003040c0403441c5c54a0608c2d4000140400741004a484100f20252450300c8100407103400a086c00030f4882c90101203041e1801070344c0c69003a51282032002c10f070052203181c254503050000030031103140002c0e0701ca = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 709470017 1250 709468767 709468783
    0xb03030703030506060c01020a02010603111806060901110109320a121e0905100e091302010c170c0705010801080c0f0a120b0a15150c050c09010e04050f0f 68
    0x5140001d03c50303072604005000da010341c610000760f13584007064400b07ca030340550003201034a000c1d01c11003480e05880401c21020500c0800303896852146100865081d04064002d8415440305040a0503c8202d41400302e084a80c002c40545184c421050036910704803020100c4002c90080e0000d0303584440c0000019951040d0682008080c1c810f00034014620912460950b0400b00c0440798103480c2110311080105038a0441c001c0d68412900541104901401105072140c090000381c84035446030350300100342580110303950060f8180311200c10071400092200b0380a03401c1094510076591036000620b099860059142c0041d4103200403480140204840000c518844510840b20380300e41010302d0001c00c04070002c0d980034144041002c940d41042005a164407032040d000850104805003486000c1500d8520500c2010074441c0d150104201c0640301d4021000202d0181d400c0342c1000100384041810380100740e115a0441c10008140801c1003014085c2000083d90f040c001c1184040c4009859140c0140b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 709471267 1250 709470017 709470023
    0xb09030c0f01200a1d0d060203041a07051603051b070e04030e010203041d151e03160501080403180506070c150c030e120a02090708091203310c03060f0f0b030307 71
    0x414410b040c1550b1b802580015240d2248003552281418a00f0000003031004014041900c1d03041c0002c0c43c41c0d0700c200f0036295101314821000c0c0c42c070300054506803503d6101a45801850443c82d01e2030461020802980c0c2c010000d11060000c24585804c0c01401c000384550440d0454100300800c001845030218000043c0e12940341ca140c05844006002c1d20110903d41c074150403501400f01c0c8400b00c00c0080c482350960106078155000c00300d1200c08205040140e001d8030b404a48c014004c2000300340f00e00c000a44000e92101034050301503c90300002c000350020281180c00500c0990284041c100220702401c000c080381c00d02c041c045542e1741c0d010381281c0800c8807403801070204000768a041801085a80c1040340c0142552645040080000f012103800b124080c05138480c004c45800301c0700302103007100e1280e88400403110b240d04845103181040390a05035a07482d280c41a1030740b0800300714200c0825004602c5003100240e644504040039054800c02c010142e120f40c5000b283c0ca00e0f98402000f11008558 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 709472517 1250 709471267 709471307
    0x60305030928181406030631050606011d03070302040e070302040609020301170708100b010e12010507020d02010b060f091903050a26070b09030c0f01200a 68
    0x82500082000c2e80300070062402190304000001990b035074404100c1c1d50a4000d00000d00c00da20080d2590040c02c202652040d03015800600003440c5500302c0246803140b10403210858400382c039095400b14215140c007205850326045039007808015a001700c281d490748600741e06107504207030a010000b030300e580383d03844060b015540785e42c10340844607c01d0203034401030f40d802402082016201d105c42c20081d01301340141000c200e01034848494800c400030704041242c54000080419020095842024095111005060043c402d48140c034a60f40c2000a1041c846464000034040c6404103009240000380c8140c14196498040111019100d49080b2252840c54425540d9103031040c134049640401e581d506a00d400401c56400700400cc0042500b250780350245800303044c22041d07030b45000900d04003804032120f41c61003000404001510b284d48161b000701440192801d1603000026a410106020900962130b5500c801801c00340c01d0b45032080110002600007103052101c06040907040130030003091100144 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 709473767 1250 709472517 709472539
    0x1b1c0602030f070c330c030b0f0109050d032a120e01080108030a08100f080307051006050a1520010204050414040f151e02090405070e03030f0a0e09070807120603050309 74
    0x5c2e000640e42e50201203001404c000f020f4045c680207005002c8110743c1485155140c006022030341c4030f40c80704026075a0003400789007400c4150360152a010b0361050282546214850541c1070810046c9a070144a03024810510750307148520760040c058120607680d1414010030382e005001c0410000162200300009045c05070a40d280c06c11404034030340c0e01e9806082036208031070000c00c800f00d002c0080c194040c80780e4121003401c58083c940c10151440342c0507031b5400818001e4100500340014000107810503060034074000c0c0414864030310810313054100c10311105a4000030204201e040c68801c03941c803100104030610726402c140e030b48e503803088000040c040d10034030408100800c020619448100d07201501081101a171054505c40c80294010f503040c1845149008000703505540201c0d98140e0304640100a1441e0000b5420b0303085458000394844001c00a00c402d03038014640701c8500d27041c01070000e0b4807244024908600014100c139501708900690604002080000034400403e4074400c2030301311480d2102d2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 709475017 1250 709473767 709473833
    0x412030207031e020a170a1101031509061502190620030702100617070509190f09060b1e01140f1801110109051b1c0602030f070c 57
    0x200c40c50b04040c0c60111441000b6080d060a2038a1030300c02d9200b84e4207600410366800c070001000d07101203030001c3c541e000b4600342c0c400900d50315107d92250405060001d115240d511004d41c070341c2280c3c0c1284003c03d81d204010b00c10101c6201e100b038484041c62000700152407403441042c11112750311000070800e9071103000d05129483c48011034000c614640788a036880b498101b00c000c0d51a50100a845582840c0c6440841c10040c00d1840c1d00004585000400240c0d1921060200d0b0940c0140f654280610344400e408800764a40034010317440d528800d0105844006041c100e0450740d14005251040c035100100c510a18100032a07454489c1007401c0030759044070a000402d903140b0a10505864204000803001c4a008a0740c8000000d007a0a980790301881c840710802d1303401c881c8101400703031056020b10650003641180d440003550320f04002c0c040102c591512450804801c003144411a41a9004010032540c64811520346c1d507c440319207072a148025007511460b9803c0d10030610100d000c01d449450b007240b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 709476267 1250 709475017 709475023
    0x3030e0d0210110f190315080309130e0a08120c09090c03041a0a15080606010918021e030f13080306010309020d140f06010b030408040e040302120708070209091204120302 75
    0x10071041c813189660384c1c5940600c141154a05c9800700c00310b4905411000344440650090041e184e400c401140f0348445482040b8440d17500d9096850502d88034002103410039028090170803840d10802c00c0c6500e90035004c021400084006000c2c40812200b840b2411442d03a03404211038006008910b09681c1c0c4e1106d05246903071616145c00daa13040000d4106022080d041a0f00600c9184102880c038615103481c1d20185440d000c050300c115000603002c250920416000c0c0303008140c504035070340c001480e0030700240c2c001e10f040344400c003c05044840442003200001c1c0030403411340d0000c480c1003149400c264030782c0d820185000141141741015501c0016101f19285c5101500409420448070300810074040009a07450f000003240b10050301800c0c0000515500c001c095a01603540074001c0750402c2d0512a17840c1200c14018070690451180020b0f101102c044000244500350041c11840d907100030500600c0041b9a01400043c1150300c1020b00b101c9110f1840e00781c07411384a06c4141200d080c185403c1c00c81c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 709477517 1250 709476267 709476277
    0x617121612050309160e1807031b060f021204090f0f090503040807062606010207030f080d18051002160203030d0203072006040213110d0903030e0d021011 68
    0x400c0c1c0800c035a00000858211020790f1107084004119001500c1240440092805c04e10072081000300d0714010032840f00d0b114403651107113580b00d0121660207617641c4400c080089404115212207402c840c080c480f0729400303e068003042c0b0040c0014000c00c0015411828203204034071900307003800c2d43e07225500c50900b22034000c10040c102d07003031040c807070780d001c40c00d02d561264454421014244551000020041e02036511500c0b2000010103200641c018081c4035404104000d10b1b05045010f5403c010000840e90306d548056030f0302403c44c0503180e1038840d803100211003c1555510301607050740c80410000c2c1c0000341e10255044c5018001d40c407004940030010701c640f082c2d80000d40c54000440c0c16108a40103a000e90303c500116920030120500e03c8264200981a065960415400400000d409800d040741031014400c1005400601d2144904c4100215004440f68080d0143c48107054814541d140c01440c17001401b5001078000c03510418006550340440440944080d5101c600c0b024068140d002078507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 709478767 1250 709477517 709477523
    0xd050711030a021b03010612060905070b1308010b121c120c03050f0601050405180601020c0d030c05120c1009020d020301060b04060323010501030f151806171216 71
    0x2610340140000182d04c5451404038442c4030681c00c0c400701c0862074140280720803100081d1340c20b10003205a803120b1001e40001c060542d65441802070008043c8810801051b04c800c01d40c2d241c11003741050700440c2500c0b895844944182c20042c064142e400f004515940703000800b182100f40c1c24940101660510101c0740307140c030f0f15840d106280146507019001944204940c1c1466010fa948000054a00f40035901604d40c000f05440305c00003605005210442d00548140121000c105c107003030001d100d00010790f4044001504050a03070040250402941003c00304000c0c00d181050042c0d901541e841d590710b10502c3e466521401c2c01c1c1c0541d240c440120081e190003400a014842c0c42e50610852031f8058460380700041c0c07900c01502030544a012042aa13004104c95002e8540d107880011009880429401410599100c000c00000d02c4c16203001c400a02c0c42640c04202d4140700c4003501c0c111001c40d40030084050f02445a1041c0910100e80c41a030181040d40c07894990025200243c0081100c00d001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 709480017 1250 709478767 709478773
    0x5010f0c3002011d030f1c050a1a010e012f030a090510110d08150d060f0b03061302010c080d0e0a063c020f070605040b06030f030d050711 61
    0x80e458035044141e1041002141d0340003408500c10700f034950a5010700716440c2c0e5a02d500280300d01008942080c004000107042c03548480c1002004401d20700441d1000d0b01c410744500d41d104203021000c016214141c220758003d00b000c100104080c0006029503e5803a190010a040c610302c1442001c07070901c80134440c074410400c6a8940c502c1500c0546081450701a00c1d22464081e4400d1b007081d8850f680c80d00880007030501800c40c41c120b00c0720030340d0303586400b9164500700181520580b2150701c80d240b107461a140110070210360750601a01c030000700d4020b80000c034000c0d0044410008450000840003086c5917080c6840a05031026040c9810f0704c0c05003a11080700581062085035241000080c1c81e020f46000740f104100d03122070b41c046007503c4230101d40258803058410f2882d10b0aa10000d501032180c45004002501d4803504080070505a480f640040303c40c0f5503220b0500003030162030304040c0d61000c0300354020002c0d80030329660b8070b9582c0582e1a02240c00d81c0c403100001c030003e02c00e1a40c000c1c203400980407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 709481267 1250 709480017 709480073
    0x803090a050f0601030201090e090307120903020409060b04111e03090312010608010303120c1d15070309030b010e011802090a150e0405071404050616020910080f030405010f0c 77
    0x6090f02e0340d4083c881a0b00041c0c0c0f1800c04107102941907007181c020341d5000000c41c07902100c0d558900000b20444a14000c2c0300703248000201507200c90051642040c81404000b0305c0c3c2c1034900c200003c5071446c6440c14181b05080c03202a4402e2004c41d103c8a100015a0b03415889581e103201051451050003204a0220104000027542c15000050302d8140d03803003501c8503000c0a056004000403112a00200e1000030001c0300110200c0c600550f015004040107000c0041240950070a00c500b070f4007a000440c00600c04040410911054140d01405850450075403c02c5525150090f003110785c0240303590070300b1640000d036500a9030791211710350f0040c0700c0c051036840010308400010304010003100701c050049061200044415100e00d001c003503280d034004900c5081509240078030010347c0124149204003408005540050707134890310310a208c0c0c6c00c0591a080d0850500c00124100511510a4031680e07000340810302440c2c1c0c10500074502618180b40c00140321000e07040c01001040d540084001070001c600e4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 709482517 1250 709481267 709481293
    0x10e12120a091e11091e060109090c020f070503030408071802070b01141002010504030f050c010204180615020a1a0c1209030a0314010f0909230115120b040803090a05 73
    0xf07181010b20b4003031001c080d25041c0784420700050300012100150900c4441107400014010154055003102c0c0614108241d503480b80420001c440d0008020784c09a40201095000403204104031070252506501460400d0314240b1440d17a1070345107015568000b82eaa020a819021142d81a1440550000000e40c41941c0d01e00d02d004283c0c1003280a50301580d08100200c20807401400317140e01917685580e0740d992a81d49800103c4058100f0325100314255000c0100007143e441d0000200352204202d94002002890400a0001180101c20080954118039510000700c0e841c84d18140c1c004683e034200e101c0da0760311940c00407000d1041c00c6004107d040c41205002242c000000508400007107a03c0070400126860090031030300720b09101c1d4241c2140e2030f036070030b02080e07003540c001d00010b61244941c880034500307404100c00c00d1140b0f50072440d0169916a0340d0070012900640410041c290500c00d04071501c89134440403505540280081c01a80e400000300d44400740801182000c650402c040e030f0380c2105d0140b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 709483767 1250 709482517 709482563
    0x211e03030a2d0203160e0f01080a1401090e071a0d0b04090b130201110313050d140a0506060924120304080a0b040218010e0a090303061a0705010e12120a09 68
    0x34403060101721000103003000442c0030301911042400024981e550041c810750045941503c0180800a03454460f50242d01c11407003006d825029180c1031002180d401128850b05162203000c0c1c1c00507820100003070880312a041204110b5040310701141002c1103803600840483c0190a1510b001031031840240108558045001c0408480520076a1000c034550848285aa520b0003405064080448145e800300080d26054054120452051035052108030341c081c0303071038280b00800360243e406822034000c001d00e9140150700181e0002c013032074541c004034024200240041c5112010540641d82d41300700d01c0d0b0700d14810400d440c024184481207803400c201910b030010021030251000c81c050b080001000d078100b6144058181624880c068030303401c1b681d840801704040e01012f00190306042d41d403400802c1d098031012400c1d0140c2e0074441600e03550a2945051401c54040b00724003041d0345c2041e102c405020040034102c0f060644000c0d500c010603160054040c00804c00701c0300050004001c504400c004280320 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 709485017 1250 709483767 709483771
    0xe04022d030c03070f0603020306040e03040609031109101e080106270b0303070f1502030103030f08060f220f1a10030b0112020a0e211e03030a2d0203 66
    0x15801d0b25012244081810b035240010700480700100b41150b402d00401c0e00c02e41c00f07150310020082001c1503008074a0b18403030450b402078005000040c0307620400d00500031005094001440180c0710183c6919000d03460100b0340c01e0500a540710100f04c024041c540382071803501e11300584100b4008201d0217a480100c219441500d2012000615070282180102445440754841854000d0081c61400a80d503646c038070f5403269460220384000c0c5400056650788914400380d13020310701c2500c035521001200b0704050410f030b42c003c1400307100b1811035480e0042601e9402c82c64000304100c1e0b4142c00700308a0581200e000c2d050f50139000e5106441c0600c0e40700e510303105c40310410030701030142c44003141100c8140d82242500c100888583c045220102ca41c15040002c2d4000c1450b540075290005145803a00c0009080c04190b0b61840500da0101c035040c0740c903480901484ca06812048811071701c20444a0007103843c1d000042c00700d00400d41d100c5544507070315400158103d126580d84040c09901a212041000039002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 709486267 1250 709485017 709485019
    0x12f03071409040f2301080d0806010909140618041101030203090c0904080406030c1103190e03030a120f0b030c090a200c060601080c0d150f030804050306060303070308010e04022d 79
    0x4042e48202c1c808032042c100381c16900b50702c01800841002340c0003500c0c51440a0300d52410401107040008800038070f48504107000a0441e81c9a64a080040810141c8440e01d01d4204002c90490700b4440004e00c00c130100641c92100703003009612a82d80103849401c0480d460081904004c40c0341c01c00c010069140014420346845803001c00480d07090780d000301d07074541c0b814010440503801001039030092900c0c40301745200c0c0604c81c47e0a507003105400c004a03003150001c200d404080381c140e00050140000d80e000d17040034061160400c101000c110000a030361201d9001c1b07628051380049020601200d000e800c8640c460850508001d910140b41d040c11516034408210080240522000b08480d0b40c4a8050b503401420894021804e107403c4c07080010061030303222202c40d00c04420910015440d83c038104d52000541c000c020454485141c18181400c11200400c81ca01c07a8100b08641310019420200c11415142505041d04007a695840410340c0d555401f41078110310007203041034503481e0141c140300749500d4030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 709487517 1250 709486267 709486301
    0x4110f040f1e050601090623300618060d06062709080d0203180d0e030f0a170a021011040303110c090a0f0b0a08012f03071409040f 58
    0x1200850300301d0f141524418002000200c007005020b02c208481c424a88005c80b540d07007400c0402d8242c48096102c4800000310480901c036240703181c0800140007040040308162030460346401c000041c0e00c2010404001c09400f0709501152190320350b181d2550384164000b508002c11511080c0307000683e00d149181540c4113846402c0c0c04085441801000c0750320b580a528076041030300c420084001394200410444000c2d003005219011081c042201c1880c49401c0c0c4c4810030b008001100f41420032440c008070310b1469024030301003400a411b58201c84032181c10203c099445139203040c0704034101034000c904854201c0c103041c01112503507074190040086034401c1d1a0030746515605007656031291f1600c000154002010300c0001c1e81240c0c03640104e92800c020503000100e204020000035200d03551600020442c2c0e554410055280d01c1c49400070501c0501d0442c90300c010921710032020783d82d100040c500303c00c10643c0408503d00b540301d4819a100c4640c020420303c10814940058030080020140c0195101 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 709488767 1250 709487517 709487561
    0x70807030605100816060f02030c060f091005060d2a06080a18030804230a05010204080607050304110d020d0819031a01050318031603030506030c0f010804110f040f 72
    0x1000060070107005d40740390900b080151811005440514106200c041980010011000204814454240301e0148001c0d1410f003402c1c2007240c207180c015030100300c1c031000380f41c80140b180ca6a07564a10303100107a40100080034194446440345c141140c00051240343c19144e03076020402e15040420a13100b0322803000100311002c1e1118460b811501c280002801160160b00802c000c038101c83c000b10110b05402c0600d00140d190b24401a02e00011418240c0e420303580410180075001007030040640050030b601c0c00e80c4c11424146c592006070710301e10612511440c0c040c0c00400071921901840d801c42e5030090300c0340f03441d120705181e00a102e0300300c0b4801100103407800e1015488200c25184080c0c1e18070040e035909007540c1d2514044550424081d1100364180b0081c0040340c0c1a070034035140e18801510030f1b50040380c2400c294060616100888039013912440c121071721910b01c0e90707001c01c0b40381d44990000c1d901c0c843c000c501c0000c00e0080d4075103e0300a030810f007406d40900132001c49402c00c450550b40e40300118512 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 709490017 1250 709488767 709488779
    0x50114010305070c02010c02040b0a230307031a15060304030309050709061a0d09020306040302030706140609271905070506070b01050d050123010819170c07080703060510 75
    0x141c4080303c00300f020a40c152145805540300d01e44121450388013601c001060010940003a031421500e07408407495042100c144564256025440c1001c401c1c00d40003001c10030304503901c80c1d500c940c85840c003200390170914002802c0c2803010600c1d40d18250010302143d64030f0515040007009001002015249441841c0c00081c030440a4414241240c2c1e44172415603028003844149807065101104d40c006039038440500c01c002d83e806100303003030080344250019a942d40701e40c94218185c56040d4402e05100c0b29400400500d91200096203900016894145a841c4401c0c81165090880c40607124201d12904540c10040b00490b1005100305000e5021242e2070f95580c0304125040c4501f00700202814680001082075062000c01144810b200c2c0001261404419130200c01d030303040b044020004626044010844440c003800340c5000b9155040c00701801304c03225210b5100c40000c12203568015040003460740d4941006000000150503900d080d10007a640c0c038100f601c044d000c1661944c04410341c6020000d14 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 709491267 1250 709490017 709490021
    0x607020705010207050f030109050304090209090c07020310090303180813090204030203030906070c090f1a0108042109244d030705070e070221030703020c07090501140103 75
    0x12100c1c160f004010060403c000c0c40505900c507102c00d40c256484070100c03070010740c0600103040540b04004005849403400c10400243c50300203040441074074020800c0a0250300d010800400b040300d1070308040780d40c0d0150320f4200d00400810000414003480c980513441001051001010310700b5552942c20350854172500c01d44103d1042e0711000754180d100304007c14050810a002d4082c00d40600c4404005680d26280b1000340c0380d4019404031156661480b11020034040c0750505000b020a203001d5030240340c10350742c0401c61a0308454130a0300b60700704c00c15891150f1181c406007024110917a00b113080c003103404039072100d003140c00140b900c041b5100c8000c9040380703504842061082c0380780c1713140c001e50340000030f45c041580001c50b0f00d00b1910314031000f00d03500c920600b0001820010b1051004042852500800303100c030750740107002e03181150420804081001c43c0c411031507048180c000011507407515a00405d500138410340992100d40c0c002c80c9400201c2c02141e5120b68100c58451210980c054040001142 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 709492517 1250 709491267 709491269
    0x8010c02030405041d030d090605010b073c2d021e06041d0a0c050c07051c0b01060206090609060c0a0e040f020d091103030705070e0c120112020306070207 68
    0x580c8140020011450203800242030703403000045c0300c18644ca0034a68a030840d8002c26032040f8540c0c4641a2100300718583c801c4030f0041c50002d01c07050400c015690f4100f280c003505105110320406240c5040c1400650030392805481c08000c50410a01c1510314180c0108a00624802048002442140003600d40002d1511606500805c01070846000940440c901100d03d964590441e00901c00420110760807103e81030561041102802d10707181105003401510355030882c500401c031060142c52003039000014000162002100d5022190307060b02403001e01f81c0040c40d0003500c801001000000d4403130300410024014407031142580c841d0b0303645908085c0c0c2c503001139441d0101c10a04015014100d4490240c0540740300d8014004500ca445800a40c41030343c200410451050341c1d10585541048014400c1ca900001c083d00558100f0701d09845058844449101e907050207040d0000190784000d1641c1295580301001004023080d50316945800180c04140710200e000c0d12401001c2003450b400050104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 709493767 1250 709492517 709492541
    0x9040c020c1c061a0108310807122118060f060e151c03050d050c0301050f0316030b06120106061d01020f0615060c06130203120a0507081605010903080a060801 70
    0x140e035549481d0810352000040e07e10704981e0004030000b044480e10560b05518941c1e015440e210381301d00c82e81c10f1a03e80700018414060902c043d015500408584841e0078120030903d503d00020250b5005007106c1007102584002004140b45c4416460300514992241d401e490160f0384228040e5103e10344c0700c0520b160720038450f500089070a0412010608200700e120400d110385045414450b444d000d00007520000e8403004102400800103101c10b003070040034000445000c0340182001d040341c180c00000d40102d070002801e548145400100c007500ca4005445e501140070008110041ea81e2030024081000c03000708a8200003803805411003903100103204100e11507c4009054a40c480040c058128102070b0001e640010060284c84a0941e00f40310140c411003c0c4400201d804c105132041605200110038851540f00f401d11551165a40c80000e840c0b00e0f40e03204941d25aa507005034080324090254900c010425824056160100b40d40082d40502901c0303203a0017400a0303a00c0c1e8400c28241c4030561006 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 709495017 1250 709493767 709493777
    0xd05030a0e060f25080c0a0b070207030804030809040e070801020c0105010509060f0103052701050f010906030506011404060b0c0c1206190203270d1103030c09040c020c1c061a01 78
    0x42400c0a0248001c4c2e0076403095500d07040382299035a01c2c2c083e5000f88032010000e400046062040c844925441070b0b105080d440544065410b5603109101c0b8059404080d10402012607244180d8079594018100d000e86a4200d400d02961444d10300e010394016031a0116950070b0800004040c01d00402e96405a60010081082143c1c14001140240380003410524140e1412515404920f1a4011000b007407680c0000420180307010200302c0208003040c0d118081151510f08202b0108001181e003905603442c40fa03000d2a0000c40314000b030b000c0d09903500201c0b00032500142c52040c800001500510324003003a50130700214980814031640342d000896200700f49901282145074a000300350700850b4015859240003c401100662a40340d160110341c140a03190303c0030300750410317054000108448901e2008001c51542c506242006840e0150659644c0201c0c0c69126101041c0c0c000d00c040d281200c00904800c1d2040b000007184684140ca498041ea0780a05d4500b801c017050580b2420140000810785070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 709496267 1250 709495017 709495027
    0x3061009050411060f0403020102011a0a051002120d020a030b01020a0b0105040914010f051e01031e0f050d0f0f02150117070e010b0910030905060103061a0d05030a0e060f 75
    0xe85005800000e10071281c02c200c14a0041c0f9968999001d402c91154401103591100c0c110f10001e400c403a40900c00512203001e544504a0a0340c51030240e400f030315020380300c140c8038900e0f0354000e07032524220742190020958086050b175200681a80600342103007290784d0074041c1545050041e616041544000741500c13030303c90014050b80c107154200f080000c0c8107501000b6446c800c90031041c02c5507804c10381c41e80800d4644050240d01010300c25203030100d8200860a00c120f514560b074001000d51910340e6080135445040040090000800000400c181c0003400c0c1e0304034400031500241000d0070420500c000c20540b01071080302c10304c00110a0708898951006544503420300c5032144258000d0704910159104819012aa0282c1d0152280c0281070b042407090b01d40340038004100040c188045940101440c0101d81c0000c2100029020304407a0403880c001403008841c915004a1591003054940220422085a08100c00000141456a81075845000d00d003a40d5042080d40e2240030310740b100300350003808 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 709497517 1250 709496267 709496279
    0x1020706240b160602120a061715130f050a17040605030c07020a1e090b0409031b02131103010e07030204080307120c0c2c220611031602010b030610 65
    0x10429030750707484400c030384041d00c6a40380300c240c1e40400503646d102403d21082c4075101d10b007070084002a0010020000307068200c0d030712160b0360741146031000007200c040501141e501e0304035032042c215298005003000c1d0741a0580c1000303030340c03104c40c4902143e424000340081c2c0302c2840380505803000d4818540d02c69140d5240c0c0862140c0c150002c41059034842c1c07115500150f4000d081d038001c1c0c4c0a076410b400396084545420072180c00c83c0e11501c0d5017800746040c07515a200081d130040511910303d4500f414081014000d001007010404980b483e007824904d0071019807007172200e05d009541281c02c20b540b02a4503646280c801c038164007451007501040d80c0140641c000013490041303003c007100850300c0d1948003050680c84000000131150720103035801803010b0702071b002900d1007110f005580380503250410550034480703094045806d0b07060a9030000601395031000200946a04480e840f10780c0c0310715454907400c108004008560524015201640ca000c00040d034034200840d1035407180700c8034214010f01c070f03207000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 709498767 1250 709497517 709497539
    0x70e0a140f040e06010906080a02060d0221070903020f0d050d050a0c05060721051501110a0b070f0f03110909040302010b03060103030f020d0203030606030c0901200102070624 77
    0x2022480d44490102000c0d001c0d611140304000700a00110018515945482d038042c04499050b0070190554101118034809a114501122002e003880c2c040160346418030042d5042044010403542d40c2410210107003c6043d92044080055a0007140d030f4900803482c00042100100c1c1c9441c000b05590040d0520b0426180110040d011012480c14038000702100340e41c5090410708100d5980b40400c004003082c00e0341d15003070034070b010002c00946010080c904003180758030781a4464000b40c5040105408003001c42d07000c184a40034565034000f19444c1070303080121014064141d030490780d0f400a5248550820200d00c60b010702c0b4900503264006600d0002e8040030b01c59100300060080d820740d0749405e03100055031003c104150085002e55580704001c019010001d081009800d501400c41d4400d2080c0070792940c80200302c0750070610a040655683c2d00e91001a100d248904401c80c0442c030055134206c4a0701d9041d0000e080341d500c5000d0400008500c08044555440642050014920000e4003402824108 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 709500017 1250 709498767 709498799
    0x1e020a020f06010305070611010903120b03010204050414060f090c0f0306040b0306150306012909240c10140610020c030d0c060b040501030f03050a0c0c0305030a08070e0a 75
    0x38810740312692441d0850310b281c1002039100b00c07025406543c08100450f440204c400150100d000240b0030425140c40080c550507583c420800f41f80c1d030708c0015401655003541140e0041101610600030101c041c10428a0350b100fc5400500842941030040000c5c646228110f01c505000e030080c1d802c0400044082945800c0140100d07001640c650b84c0044640e1b00f006a584a441d55203445d07100d00c00810103141c1040c40681c084805103010011504881c0e80034400d0201144880002580392551030000940c002c1d001411400600341d41061400303a03404000080010783c4548045035040b0014503410812241c1150441801582e0240469007a00e1709081040c0f10714690703c1216240020440080d09010f500c140c80b0010540c0c681500003000f006014034102580e00f143c0420a0358519211030b9640481460000c3c100b000008240c09604c0c000d080350800c0d2130f0010b508101c101d80300d1825659031380c00203c4800100c0c1c5420b000443c1d1621481c00002c02e4003029014005862400e4200d014109070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 709501267 1250 709500017 709500037
    0xe0a150302032202090c090a0905011212030501060e060304260c15061003050a060302030712020a080c010503070c051204180e070b0924120612120f09060d06140102101e02 75
    0x82d4000004c9d9108841c020203000c4c0a04444460b031411052900c03180303910315021036000b41401e1000402040d03404c141070341403080c02940c4440d030341e580324905a050300040090b020442208807000100141882010303240e0707a010801101c02e02510035680b405020f204541103684130035900c0b0704200a40c482e4200fa504a0410900415000c3d01d0340d001908101440c2c010312100c400c980c640b0300642c2342a14a40b001401868068070b03e4040d030400007405480000d00c1031050003120416001000410000040541d08003400710361540e84400003d0161448020070307841040c146941c580507080081001c10071141c2404c1d500740b0f40f4071b1a2040c04102035205100301c09095032449640ca0310704410009142e070348a04803140c415440c08008102c0700b0384101c3e104510706c0d4402152440c081c00c40c41c00300e920926903031b401280c8801055000500324822220303400701560412000064800490000002441098080e02c2c02a840c031080c4d5421514002c8036484100b5441c100c001405469600a21121507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 709502517 1250 709501267 709501279
    0x10302160609062301150c0f0605040c03060c0e03071e0f090b240d15051309060b120c04050705160803190203070c030e0a150302032202090c09 63
    0x45281c0750041241c16220065900d90380f2440754988181c0907504c0300c0200c4603018039010440d4104540c0340c04010f1000b0207031081c407044507101700c00d00901d0469621499413200c001c1c009c80c5000d00c6c00e5035441c0e4061008071020b070306060304000802d00421a4a80c4c0308000380041502914061142c05910001c0c1516014410058000720b89048420315100283c00c0c0050045004403440f4140191540c00d80042c0d2006910700720300035503900b50070302100c0c0707240043d0070041482c207040315038030030301e0707416940869400810f040d0200c52075141c2e500900380d003600480d810002c290401c411321068250441918072560800031041c06103142550107a5000750791440c00500b08058034240c80310303900c10302d8001c1d180d142d8007104020901000c88640300750184000e1f0194110306101001a003815141c00006040c01120301c00b540594445020940040035500820700d1901c0b44054050020350098882400941c00307020740074507030034034400d240b0091980030300907201e1a80e0b156505803282e00102880c40c0c0c803135 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 709503767 1250 709502517 709502557
    0x10509030c0f01031b030e0c03030f030a2706050609060312040314030f1c0b040c051209010f0f0204060801080c0306040b0702030c0d0e091311040c140408070e070914010302 76
    0x141200c121010721081a40700021103501c047c001520f000000400d042c0319600400881c0301c80d000000680b80c024813140c0010441e080c2c5032000102c09080d19141c41c038004050714001c4140301c46500420700641051742d0003003142c0c07107420a154a034007400d008200c0440080100f0400035a103101e55000c00d080f04010b50b820000d0407d00a0b03060b0f40301d8143c03e07000000e030b40081d4401000d5031060181d1408100c1e010000c243c207012004d440c070b0060711115900d20310301d5000138054200a41024050b111481000c00c04891508622130081d0071a0243d80c000170009400841c0d012000180000540c90040050140e076803150b03074581c542c10b8000c19100840c00140801c1c10864410000203101e628681c444450440c0090184008580010000e00e080c01010403414042900c1c074250409003401628041030000c6021000d580c50541901c0203040500300282c0080c441c10046042c500352106503202d04040d441d588401c070750b291540e000f88401d003030180d20300c0b5003151700175402000024102c0103000c0c030031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 709505017 1250 709503767 709503791
    0x914010b0f25050312010f060e060f160c090c09030b0a05040f0804060c030305250f03020f040306151508150f030d080a0c09080c09070504080a0c05010e010509030c0f0103 75
    0x78800c8107000c0f90b4980c004122025043d2a034201240540402c0c40360005541c07a2920050134074007010107807805554000f405001c160603000440e12504c3c01d80c80803400080041c6800402580c0d03070310070080843c0c540100a620302e8890039110303080320340000040545841da0210701004200c0900300312038094045004600288402d00580010311480d182c42130004c2c2c0c2ca041c0030f0103959004100e8060120540079030303119013605401d0611a0f14403890161001880075900350700034401d41203020742d643e10204001040064940000d414000d040d269200e0842c1da0303616000940c4541141540232a4800c13000401c01a103810a54000340310041800103982611000f0a062145420b07081c1c0019450700c2c20020a54014080c5070b150744440cac03510034019031410190b66102d0f0304103c0c00f644980360b00300118400d41d10410585000c1c1c0402c8040d14172420b02c40c03505c08088406d46c8900d602140303d09500e1550b41d07009a05a881c0350380060040c044500a110402000c106084000360500d80c3c0c8181c0751690b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 709506267 1250 709505017 709505077
    0x3011e05120102091f05070b09030c1006090b010c0f0f020619020d0201050c130315060f0b07110118030b06030f0118051203041a04060f050705040914010b0f 69
    0xd00000c00001643d5815044c280310000310008080320410400000b243d10341030784a400c9485958000ba080619902c9204400c1c1c2503110f103007c14a214414041d076402c0c4212141c0c09442201d1041c1d80030041d41c401e072401035a50540315100038020302e0a000c11000491501400920410710040101e40342518807407491b44c01d000b54054800c0160700c03159105690a809102c0c503034014041442e40c1e03090000b5408528104066408028882c114a003031820588610350001e6010740400c41d0b001c40307401d4a400c800540740d0000441038401021060781c02d031180d4050058031801401015185600134111f4442900c0b580d8080c00040e0076101b2801500724082c82845222580c080c2814001e02007121070401030301d0201b448001ca40300610410600c00010481d4400d100108403030412584182e0711824007500510b84821a8042c0c076043c84200401c0c194070000030816264424401c102000d0303056410860110240030340400c1c042d0400246c07441c8034480c409066108848038584000641809010203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 709507517 1250 709506267 709506289
    0x70806060a031b050319120e030c06090f280e0108030703080408090a080d030b030102161205120a0f0509030712030b061b06040308060d030e09040218070206040312090803011e05 78
    0x7441e0081051b03400300843d021b4818030204052901030703920384100000940300e01c910001c41c2c0c031410000414610720746820200603210314004000754505507618003100381c03000710700311440c01c41c6244500108020b142e404419060340c5d900001942006960780d001d50b90500c2c050016a079040c800e1040408650f01e84842001030460040038000301c41c001000542558451681e6601c41d90041c0000132510148101d1111600c0d0049800c00c070714543c0300030646692007018000000714260381d042042d4110181c01140240c0c0c45171004100b0b40d56120b00c1c494a81c040d80000030920382210008050ba184a43c00ca0300751850000c00aa02d44000003400083d411980141e41b160b903080131080200740354109070001e5102e07100742c810281001b0303103a600509000c008141c140c4903201da01c0226065440700c00c0d85030303000d03a07505000342c2d56030030402c2c07001e503403681c085400720001111001e0081035007a441c02103442d101c0e407142c1240d00716401c1440c00d0054181080501500460030b010018880d9100300f0805 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 709508767 1250 709507517 709507543
    0x20a03110d06081011030f18030d0506150306130b06040f2c16080a0212090a0b10080d03050a0b04060f060e15030a021602041d070806060a031b0503 65
    0x6007240342c1110039003001d4031080004c80c801e281c41c481c21326503101081101e9101c10508100c9450f0f60303515031100c0003c1c0d0b1640100e1114400410403800c07030003040e84205e00031142202c5904017a00c011b0441085840103c035140d07040704100d2820b4081c20b003190001c61410800518060403e501c9080300c20b1b2900b000d5028042c91002e003029010300c16041560320000800581d016019071810108081c00740c1690460101003004060005002c004260705842500850360f141180c43d04003129080d9441540600a43c0e588903424081360425455092550031280b0020161541454104e8141c009000007009888442c1d20340c9502c0c0ea0302c4d40c8034801d51000c4d0088100c850205401e0001c004d0102c0f0380096000c3c000e4100381c5240840e4549003040c0ca40c4401003050159507604130302d103409141d0401002c0207410a0800c44400c60003048080d00d02040e0241d08212500d041e07a03031000a40d509019580d8513008170103080d0500124054444914911200450381c2c80c086d680e03140417a1610504401e10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 709510017 1250 709508767 709508771
    0x1c030503270d110703030906050708071a011401020f060115020703050105041218050105090d1a0a0f1529130b03070f0c110609150706050916030c09020a03110d 70
    0x2111000f40c0141044007200100c40040611900319a4042d0190155000c2d502c2444804141c0c0e5041114030303001c6480d490750052140703c083d40050341e0345012881c01e000d251440000c00c4140761065100003201c1c000a02804028401640781c013080c5003d686402504404600a02d01c0120106809010702c50150b0710500255010b104c0c4620010205001098510358403030000c8410081e9a901600b80c500003542151044035009a61400741d00480c031001441e110081c03080c040006460380340e4000040c4600d8030900784540c1100c1a19008044000e00502c00d400c070b002c000030384203201c8491120402d0304403000018905505407101c2d8200c50400d901c500441031000041000341075104044d400e000714141400007000e03005640d08489401485101030181c030380803800003205e0740c030300c02d001c81d020301c455150541d0348803281060800f40c40b084034015103a208507510900d1001c1010744035070499411040d03a0000c181400d0a6030081d40c4280000d4082648982300c01410300f009030b009164600c412100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 709511267 1250 709510017 709510033
    0x60c04060305010b04030305121909121209020319050c0904140706030e030d0b19060810080f120307020109021503061302041211040e15010906051c03050327 69
    0x8000c09846050b00480020700b0117000400001c2d070004c0130382d04030304400300364908995180e25200c511110f14908c40700341c00c1e003000c1ca01414019640108200c01d10250341d812840d106195584094450700c1d44025019480310448100354085142c480061318440c8054804094248000802d1407000391003e607000c01058042c69511a0100007041c024049814144180300c40408441d850740070b1a110b50401d40d80305c2c9404016556840070050450040d03502c98240562034017001031150008440e9540c100d0f000c07030707408200d0311800180c3c800078060f007070002e1a0346608000410307601c0c0c001a00040940d0341303c1d10303101c00603520b82101558200020001c240c0302d15100c41008400701c0030030480300e0414410441482062a400580891181c0209802079108110f00c003160051410b204515241d0055140036070b140258440c280e4100d071070340304091100d1a214001c221441c4140850940c400f00c41d2411000020302400241d6030103401b80c966240b00380200300b405a00004583c0044a0581003420 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 709512517 1250 709511267 709511279
    0x1908031804090804050f030717030a030f022b0f060b09030d0c0b15010909060b040f08010b0108010608040501090203070303081614030403050304140111090a080a0f06020d0608060c04 80
    0xd900d198a950880d024050080c140d00c4160321403189001c3d140c01161042c15040007601e0400882c801050044da17042030300c0340b510907515100d13000145041d00003400e082c0c00030380c4c8481c40c0c029603d80c80740101d5805480e10706402c1d0014925417810034400183c2c0c41e035001c4c2080480510440e4020154922102d980700e007401d04060a08002c0b04003c01800108e42d000d1002c05e113440c003010b038441d6004903200d1800c3c0307075140160b03610082c9502103504182401d10100c1c0c400156000381044440c0341000045907500c9802103405e80d6080c45036140010f1780400104400c070301c1342050380e40140c0240000030b91280c0d0380c0c0210342000c00350741060380030503125000d0040f40c0c0505164000188024a089031940b060982c00c0300f00391001610240030090301001240c10b0141c1c0b5000c61141c501c0300c00080001521441507104c440e000254168420300a618002442c0040402d80c14181ea600541c6c207102d82400341d48200080d000382c2816610650354010201c3e0b0108104035040c000d0165000c21a22145400c0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 709513767 1250 709512517 709512547
    0xf030d020301090b01110c0402090102010207050304030c0305070f140603041502070b0f060406060512040206040f12030f0f05220f091514030a140a1a0411010806130b190803 76
    0x1030099040080d2803060006c45940454282c1c014141210f0250b521226240101d0281c007400c80050042c1c0030025000003007181c140118821684100e090702c2400350346182c25520001584606500040c03240f4000c0721a01d0800015503005120300c85180103c00303c1c5055200301d030000b5100301c507110124828030101242d000c02441e44900215000d01c40702e414000014114003543c1160781114000348041011980d8140580d009468040000c0c90700a654941d0384ca66406e10786401d8010030240c047c00c440c03a03840340c1c0c040940707030140388c84042ca00707500c409482c0700205c450948501404141800420081d03c050305c5500205419900403424520040c0b00c000c1d040e229500851500910120082041e2004203a6015039500072030002480084518403c4c146010400001c5c03c0011044c50800c02c0f0b11a060f1981c0250300814484903021a94001950307025421b54249911205801514480b8540d5422102050201420200240564001d5036075031141301e03008200b5139080801c040700900321507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 709515017 1250 709513767 709513781
    0x6070201230402150f2a070b070f2f01301d0c041401050d080c16060c05010f053303061e07020a080720211603020a06030506030f030d02030109 63
    0x80190110404404074001f5035a020a02c10b0092120340808d40000340241200500c40864002d1700002542e0003102924445204448a0340c4482c0ca0550409403030b940f00b400340d00200c0c1100b41880c4c82c0c1c10b040c07030142c0d06960a035031001002c254035080c940302e01011103003c584a250010008140c441c1c2040c040200362003504559052502c040030042100350382e015021100207802c4851240c1d914270800d10710341030106d62440c0c0700c2000c10600c80000c0c000c2d482000100407900510082190342890904841a07450507602c01701d503200350f050318a141e00341c103102c2e1450403a03606000c41e003681407030000b180c18040c1c01c85450540c498040380e04803c03080809441503224035240b016081411007545e980c1c0c001e01820303401500d2068000b8181140c401c612940184141d8024000240c156286401d0404c08840000d613030258061582c00040e14a01c0c0b1403101c0a9a0303000744035464a90414008800401004052a0b490307c98100303c5009600c00b80010400c40c0c020398130141e644e60604291000313407400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 709516267 1250 709515017 709515067
    0x211e0c0405040b010501140706091a0a150e06240415050415050703090e180c0102010c120b010e0d030503040302070b0901020c19050402040f030506070201230402150f 73
    0x400302044009003e2140141c1583c0090030850101c0d110301c20030410b603009105e001000c0501d0107180300c061111042c00c41c074105820214504040d500c0740c00700f1055840502c68618002d030341500c207000502e12101603070382c01203001d0b0012080c001c100588003601d078940c440850038250005000c0c4544020003840182c40307072690070035500c1c1500d0410030817000c0e8640025901009004030318002054450f55215000b40104045440c46003800c040000d00c1400034840ca0000d031050942000c41940180200301e102d5034a52030301040441070b024080060071142010904001140c03603d8580780d56080c0302e9103641030090360b644c1d881e45840d20300680b414490342c00440700e40b40e090040c1d40342a030b07001803180c070002d00a40b24240044421004007540e2011904055400340c00414085004c800b160010030407680600215807554690940a900b210105404104403c0070f83d01101107059140501c0e5411174401703014904070655510348022a6006190344d03804c0307120300040c80482c03498061050442c0b420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 709517517 1250 709516267 709516271
    0x20105090a080a02100f05072007030204020c030f0313060e0625020c0307090c09051c1e06140402240a0e1c06060501081311211e0c04 59
    0x18816001662076442640c018000c4000058010419100340b040c00e120280c1d5040c140550640a0b5800b03014060480e01840001c203103040d6590840940341041c01811110009070900d1410b507000d02c0042d50001e61854402d100400c5400106400d400c000e52150320b030320460240a0800745400c002341e0714001c88036641e07607000500380504e294800c01a82100f203c911020901d4ed409110141e05015128a0007a1b040c081e10000103003446094000030712080032951030a9406407182c0030000584d41155100c4501c0d07486001c000d0010300c4100c008180c01c01500d004181400b82c1b42e031110241e1300356010042c03081341680c00f44811401e0144c0e00b01c0b071013507000481d00003542e954891120ba40c043c10904208203c0741c0010b429840c2c4502c0c1041c503881c04c224030183e2032041c050400702c0180c4140e00c20140042c50705030000c0d000101100c802c86102d43e02118031107040310181c00f04100d200c4c06000342c4c201036685441450f0040c104000d100070344c03044403c18201e0084249069810151200e01050150b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 709518767 1250 709517517 709517521
    0xc0a090b0315010c02010c021801060923010f021036051b01090e131202071802030a061e170c01020703060c0c08070b01080d1b02040b120a0606030203010c020105 71
    0xc199107084a514003003031a142181300b0301400102e03204181014040d4200e200c202c050490400c18180c928142c41464485010540c0c0e206105c011607020198812419500441110320361361045094013050380c0d05204a80c00804898018001c68960858030355000312842c0103011418221350a544820380c49400380404107140b81c0b1265241ea0241400d08806540da00d0315100c03030703030040e5000c078040c0c8910409026140750100c082e201c1c5204000f0107660103c40000d40e0800e40e403000440b00180d8000d01800105d641203054040083c3d080504603000c4244c40340300c040303242d80001e04160414090030b09030020992501e110086210701360b40501e207958016491459403070340c0008002c0110b0390b104000048419070154220b0744509511001480d0010008040c41403000c02d080982c103845041c020f4601003007118030700f910195241e080b4000c400104120640c050710740f9038007441d08540d000d400b2581800042c48030f039084c488418411200c07180c0e00c040c1442941003d00c5000001d00180c00200228 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 709520017 1250 709518767 709518781
    0x1209081606120e010608010e0102030907080f0706120b04110915031005090604060b0309060108241906180f05060405010f0510110312040330020d0e060c0a090b03 71
    0x4000d6008505502c0e501c6800080d90b0700300940c0004020040100200701c400400110715001c0d50081d100074445120300240850300d981c01203040422298031100030421146401c200380d50700440d40745407003d000d1341e4004610448d11240944045140d581c11542d40d104113600420416500d440f00d03c0741c1100040c0b080001000300c4030644001d80e1822540f2003202d554520025010f000d4507003000c1c04005012043c060351850024039181139a8450013502c10300c90b200c0054001c041c400d00500b2101c0c901c8140070070504000c140070b01c8070354502840d020450545a01c1c0c14805803090300400035182d5511790b09032982d503035180b0a9941041040724280a50351401102070880340c2c113406154450a040b81c262081d250246c10780b11404201c0b2429203482d07844e208000e90001d5805c40b005d5001c1a02030012071283d200344801e9828101c240e18880121035200368200b0000d400002d0f2882059985110256013061704120300387c420100c0084482e907030800307000300034050400e540c003407035055005106100754 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 709521267 1250 709520017 709520027
    0x9051e180f0106180305240108030a0c141606050a020c030c03100c020a1505010504050a0b1e0a05041a03190c06030c09170601061b0203060408090d1209081606 70
    0x1107405038541500c01e441c60300421390800b020b5a000a01da0320626001e0001c491080442c901e50380d000e07034503000c01a0390f00c031111070722481303021140c030f000440303040844001a458001982034219181c04845982d036030a900c0019100068008101050011807040c820b03650400003200c0d5004107402406120441d03801003662602c1e0725418414082c1c65014015000380b08001d582001500008040d01c200d0740c400e0a180188000e000e1030303000707030304240000300c08104602441c65141e102500300195442c3c090304000e150785034038690701d6205800c0d440000d0035a4a50141c1c1c1e149042d400c480c425050a404101890f000070080c410fa404051004480081080850301e442150003a08000c91501e58007039044602d80c949410019042c00060071324000130200145d124140d600300d449903100d04141c01c081c89000030318200000d501d54040c1c0006000a890328010303080810026161510002e642d64a103610000300c8141540040c41e255010480724004100b00ba0903a80c0049001a8040c04c2900080c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 709522517 1250 709521267 709521269
    0x60602100903020309060703050903010b06040e040210051605100e0708070b0a021c23090a050d110607050a0c050d08090915100c03090b090603040f0309051e180f01 72
    0x15032180e40d15045010b0500900840e0079401d0b0040030503650700220700d8013030600c0e044694194001d43c03809507090f0f21402d280c4225401e494640003640310b1580c4917401c2000a0b9240b0400c0010050184000404c00311051014074840348a5000390000d400204403c0d0101e83c0f41c00000690381d0b01c80c0380200300c1e100340850303000c0954050703110302687e81071a0042a481e040c914610000101e40c8601036050140c0c0c08440100306c022401b841d0403c01d038203034401c10424014038080a0f4040c0240c54100b01c0c910b00031502291442c0308800c92400c4810301d800103042504105c02c1138896030012034002040000440006020341011a10507014218544800007580200c1007698000c0c0e102c40081000040c2c4400340702c645c00f10007025546000d07401040200710314500d5800b240450001000401d511070510240c0d00710040141c1340e00d065aa8648950103601d04049090341400b00300100842e06413100107088907401081d031182c41c210441b840c240055114107070102230700c23003d002d01400740e284101c0711124 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 709523767 1250 709522517 709522543
    0xa02010818162709031d2403070f11060a0525030b0f0105120402040518070801140a05040203071e08031c0e06010e040f0602040308180310060602 64
    0x15003280c0807030109510b407118200307115072246007082002990003072000c408071010400c0c0303440301c19a41c0702201e5030f004d461603000300401182d6440d80c4c8441000c0644610881d0321001020103440c8811500c1c1440040c81040304007a906000004101e02990030803c680c015800e50b1a200030720512000d0050b0319241b0141c210401076840300003103060b04000501c50021411241030800d8400e40301c000c081e009041084410780200d242d12895136071076005000351405910081d4402210723950783d500308001810001c1888041c8204d00c0c0400411150410100000d41550300c0000340498090321141d006407402013003000c41608080802c0016140420320b0400c495607110b070203440000760741404031210843c1d04540341d10310000c03910300c2c0560f0704803a009885040e03030031003080082507050703801c2d4403503801b4041e452054a99002003400a01842c0c42116a54080c01300141016140d42d26440c1d1603000301e110f40030442003a80d0241d00d9180510081d441c01d20800010410345103403500103074542071180c00c44 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 709525017 1250 709523767 709523791
    0x1503141c050d09020f130f0b060702011d03010207080d240b0711030316060b0a08030304030f1d06030408030a05091b041d0d020f0d031a0d110a180b030a020108 70
    0xc1003103488512400d08081c90050600340180c02030072841009280d607007d841042c5090194000c10380c14032500b01c92081e81c0694410150f103403050b0480705d0b00c91031040b03003d80540d070810855021500798409482d44080107580030881b21132502d040c030303600c036800c00746d4400400160303004001c42c4082808494131036030b1003000500440d40120020341180a001404200b00740110201c804005540c1d10a1a42800c121401d220305511080050368a0104030b038018045001944044c1c10503000d121b1007501e188070724614242c110100700202e50260030039103007241d04900110602c181c0407014002d86038443c0c00c6400070000c600550f024100c035039000a0500c3c3c0170b123595980b07005140d00318000a0350004003030303421505441220003000350f84114403135510030715029502d10002540d00c00e000c0c1e0783c4d248003008400309143c080981001035072002000200c070100101070302030b03100c0e40318506420001c0110206000a81c00000110703002c0c0e400b03584102d442500017040000060781c00c40c0349a5000b100311818 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 709526267 1250 709525017 709525031
    0x81e0a051b0136021e0a0e061018050a030c05032a06070804050409081b0309030705060a050d050907080d110d03180506040b0a1d0a12031503141c050d 66
    0x3e80440e1600014000e900301c400390b0350300800030000740344228040c0c00c00e40d4503110103a5106c0c010044c6078000c1c3c0d50203501010800040d0901c40c8510b400c2160382a009001010301961000001d10340b0145500480314203801074130801403071030b09200c14607813502d91619880081c12000f03181d101009500103d00d114500126130351003408004820f0301d028010103032080042000b1401c00030303e140c0285000c0c060960644a09804540303020081d611007080140042510a00b4001040095041461540300b04801444172030540780842c0030300c81c000d04092014024241c100601c403418000c0c0c0d0110301d8240808032112040200e400962031180c95950715000074000381161074070086036018070001d0031030310684c414030042c8418018058020000d040c820800106041410b030515945521074031001e401c0070720824049081d8118075020140107103030020f010151012114580700e01504140e036000311507403c0c2400d80e2410072500f41c0c92101c40a58046240305003074014640e10030a040c88c4021500c03003a03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 709527517 1250 709526267 709526351
    0xf0601020f2401050126090313120512070c06030515060a0c030f02070e15030f03030f0609060405012106060f08030717160f0303020702090703050604050708060d081e0a051b01 77
    0x8181d40c04030b0715031040900100cad07940c08040140f1140f071405445034064a000c080000b90404200c8002c0d591080c07041c1702c4140780c070505070020b140c0209000c0400b0740502d482001651500010301b8403001c90f4561454450490800610107192070110b001998020001030261130b0540040a81c0f00c0321082d440c43e614036200c404681054010002451644004024440016040c20080d840780c0402e0b0356090840e600c100401007941c0c402c0c402c20044c00080441010003a030441c89200f0014007132540410f40d107503911311000400f400c56014480c583c0001c154042007252040c00d4820540d00c0b926450306004101035441241d00d85007a008200071106d94041041500030340603690031b640c008080030003615024101030082c000c201c404a210358900030020b204240600c81031400360300d024103150140744170783c3e41d92099175200c2020940820801d100a034401b0036002e00400281041d556500d44851071100c01c85030380c1e0301003004a2007590502a041a4900780f415100700c52100c40f00318404a42105d207 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 709528767 1250 709527517 709527523
    0x81c0b130506060c0102030414010c1416020f0916030f0209100f02011407111509030423060a050a09080715081e01030606140604030b0f0601020f240105012609 70
    0x20413403032040d4004020802400f01c8445a84440d58044000340142003030344c081140c49505604005822000c1442030131500d11401ca80ca501181c030141220607030000c0341e07000503004c550071100c1400c40740500c0392081c0c0b0541d050242c9049801900c1d002e41c10038020b1000544000c841c281c4617410410100302130314085200f50010b04081d00f0741c001c80c020906102d42d0041c41d5905002c41414031303105005060800b64075100f5031a1140840034050341c01c1a003044180c5015004120099a0104050001080c103545040081c0707050452611103d5031951032030806000d142103540300750341a8200300c204005c102100200070460f40c0a40c80c014206988000d1035011146807201c00c2c080c800380d03182c000b001304a0254000c40a440348aa55098030b4002c100400240c0d01c118040101440546404140300700103952280ea00060f050040d1070000340303840841da00c0c212400d00c1035107142c507070207612510710113005441c00e000d4042842e11980c002d2200000e004516815001d10035401500000521112824 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 709530017 1250 709528767 709528777
    0x31103070b16110312043302061504020c070801060f0f0e06010c0c09150302012a12030b060d0f0b0f0906010f090f0b0c0c0303031003060c030207020d081c0b13050606 73
    0x9214454560303441c0c40c6c070721a0010b14804e0030702074140300e807801a000e6800000207c150500e42d40c001c250b15960100703103000c0904448501900580c0074002c0004649040c010344000c0e05d55034000240300c88c5060402e0f003402100303038404000e00042410034010340165845080e800344007820000c805801c0340c50300c80d1417986650322074009989000c2d01c21401601005c0c0c0202203074000d81c1c4c4c500221079504048412001c161520b40c1b03040300e64070300003030006040c030f000a256035182d410b0020b43c1070744a0010560f50760107040424891a07aa2a0070b00c445196407140ca000264181c4a060407003003200003080b5032070340180c6003c0c180002da00122650078420f10ba0807019064a640881203a035490b61b0124058128900301c2160340107100d04443d02d41000000d4900c601c9640c0491124180b540e111000100080c24204003019000c20904000d600c90800180003e48103c0105588208481c11282c07a800000c0422104901b070450070103559a40e80b841907034002c0c4001001603942c8440e00015414459 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 709531267 1250 709530017 709530043
    0x21c0c020309010206060a120f020d0c0b0d0f050f010909230309011b0209060909160f0617060f1519080916080304140d0c031103070b161103 62
    0x10544254801940032025004002080e001c44106480300300800403142894002c5c00c940c456005601ca0104813409885010b0314000303411400355020545444001e0324280d00311030000382001541902d0482988107082d12146614010072640c18121000d185851062003500c1c0a15140c400c0c08040c070050612040380a01088070030f960701081008000c0e102d81100388958041040070300c248980d05441409540c59990003030000c11140d451500b00002c1c0d490203003c020303007841003500b494144040c0b00f1284016240c21003003045c603545080d000800340300c01c004882c01c1c451120f405220664841412401c024a4101c6610340120b0041c5003c6240d8010f444e403420700041060f0716120015001009540516010b500350b4507410309503819074103d4001441140c4a5034410401000a00b54098100504150003004d038032080440340c40b102580300207900103441d052005060041e461908110032801401800003942c01c2000c0041c800c600641d44140184c19640d50840e010716030b82d020b01100481e026 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 709532374 1107 709531267 709531271
    0x9060406020c2e0606031b0e0613090902040c21150521010b0d050c06030705120906060a0b0306240c010e1605040b0d06021c 55
    0x103014240c900098019030851100384141101e41c58949201c003641c10041d4007242480104413161540040c050620b0f100d40840c40062030150386103450818244040c0520048010a401e031042d40300c1744041c840038803404110440c60703603c480300c4640240e4080020000c00242034981092508106906150f007400c20110021580c00c00003032051040e014600060340c0e0030100d40e4150303008900004070190305004241c07452003482803000c0d002045484030140d4400ba10703501d458a010301d100a00401c0b0000010b48803e00481c00c5400f00c20320001c4444062038010362140d29408140c8007948104a102d41c0020905648d005882c09480010141d0004544494082690900600c0c54210350041441040d402030b600307108031840305c06004040e202010064800c41c0d00380728242c0010b4403030340c40d02404601d00e03224001120103442d07216100503900e01d140d000f0020328440c80b0245a044034 = true := by decide +kernel

theorem cover : BRFrame.Cov 709352517 709532374 := by
  have h0 := BRFrame.cov_init 709352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 709352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 709352517 ≤ n) (h2 : n < 709532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
