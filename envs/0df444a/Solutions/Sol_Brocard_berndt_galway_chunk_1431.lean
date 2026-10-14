-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1431
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:57:18.303992+00:00
-- url     : https://prove2.me/submissions/65b0852a-50e7-46be-8dee-460b9553f697

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 257194244 ≤ n < 257374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 257195494 1250 257194244 257194253
    0x906010509010c021c050609030406020304030f1b0929030d0e120a06050604050106110a0b0c0f0c07060807021b131b0f090803130302090a2306010e011b0b04 69
    0x1124000c5d445907401a0b5080c2c00316038030640c207212a00403000c40c1c0161703d035128065182d12880c0078031070068108010600104000d080043d86151185812046500148111030b211403110b070820b000c0e0545a903141c683c2c40c02c80c210201c410140b030389100300f15a8600c0000070764441105030300205000d5104071452255861403c03000034115080b09031925050b1628206d802880701b2100c03e40302d18a05030011441906c6503c1c1c001291000f0302c02083c41d80b12a0f2a070a00314240103140d10481c00c0200011254a840b26004d07082c00303000640208641d604144029003940001000c03041154813281e06c0f290b004401ca002151030230780540318440c0c03c4c45c0702100d11002c0d00a1812041100b80780b903a140c10190360083d6070110000c000d6035100c0040b80c0b00c003202c0d5182c2c4540380504804071948a4140090310703041d8859500701005e400002080166400490603142203498900100e8101e00b04001e144d503000a20340a0f46d4009182410708202c130140c6403407940351283e6003d80001d42c4880042c0c10030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 257196744 1250 257195494 257195507
    0x10509041406040308040b0106050a02030d111e04050411070b070f03090804150e09190e160e0f1b0711040e061f0906050d02120c04090f02120c090601050901 69
    0xc4601c202901c4030b614203800c3c0500803813070640f1304030789800b40000001800c501c5002640c0c84410250702551a1680301c2500102801d80f0380e5842d620500300b003068030b01c41c8c1c00f101904075195030890890b5450310f00e08010481224246101150000020441c0c1c0c0006094410b485500014506001c1484074107928201c1c01080f02400050411400040108072044401e841444501513a42c03514014842c003018002c00c100269014407110105001805042101c0d4101203c1c000f0702c04c040300d01803850305011035406003082e80070007030510156041c0451440e000e000b2950103640417050031000d180c0c0c0f0482c43d44a12030014090a91085030022100075600da41102a41a001c042290700300c0c28000103c020405c10031320005560b88141d400090002c20a0094600f110401030012152421540a000540321950340d1349071240543c942c42e00e0981e6440c800c110801e40580d441825811071807041c025076003040e40d82c040c0c44e0792060034900d0b0365580b1020703040d502c040c003882c1250301c07003207000c0040c1c501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 257197994 1250 257196744 257196773
    0x1e0907061b0305090415240206011419060f14040e04020402030c13090605010201180210051b1009030f03090b01140a0911090913030c030305100e18010c1701050904 72
    0x5e800c0800d0751403c550000001c000340c0d4600d08a6000601c0c0403150003c2e904c1c3d89441003070141c1c00c03d1004102d0740101c00d01e000e81e289006043d130040c1c02c03c03448911040c00c045800220205161800b5030201c140d00c8458404008140603c1c0c5180600b8500d51450030700740104028070440d000000113000100940c2902ca5511080c00c85107040c03030b1901c03501c0000c2c08040c00745e42e00540c40c1c41e585c41d64800905a0701c0781050740140410180100411044070707280c0c082184c01814400e1500800403c11013000400d0401c0d00113103001078040c9407483e000b460f904d10348080b04201402c10144a010444d40001a81151100400304684c034010701c0c04a01ea107103403130f4400581c2d60700d4600d000001032501c02c003c164203481114035070700f180e4030151907240707180c00b4280140002d2060701c52080042e00a90010b600440d00071215900381e0350350001c0c22140102110b01c1c03100c1c0e0000b00a07580c50800240902d40400405041469000048440d44a5404814807829209454140c085010301c2801340c4d61040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 257199244 1250 257197994 257197999
    0xc050405030109050c0f0a0e0a02030612030c0d0e0a0803030a090204110a170a0e0a0807050705100e03010e0303090c2205010b0408070503030301060c06020307171e0907061b030509 79
    0x40103ca003401c6803552002200c1d00d0061202c0742503100c482c540b00100c0416190041d0780030300280c1718140140000c1d04024141504900c0401802000b80410030280a40c010000010550400d0186c0b00a008030b02403151036024050f00001404031010201c2980d52090780c03190b00180032521800000e000e4103a40d255008000d00c002070416403254000c0340e43d140b000040300503a01548034600b102e42100c24071049410035422410303042c00041c8540000b4003100c3c0c06001104c01c111b488500040c04090300c010003002080e070810710146c1900f02801114080c05901c809181580f40142e4855100d10500503100d1081012801c0c15140c45180d4021040346903070101b013007100750b854a900c07400541c068040c0c1d021610078020001103502e4000126816215540d60745042030080384e82d541c010b900050110b03400d0001c10700c502c0307010f0240310000c984a2814640d85205e4600c1c0641c0c086006180980001c4507500856000c0c042142c2002c0e61000c140344816600004202e01e0500b208c1c180074801800f42e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 257200494 1250 257199244 257199251
    0x10060f0c15060e09120a0c0c0305010204090b010809060105031207020604030b1006021005010f0e04060e01050f060a0e0408070b0c0c0609071a1216030f0e030c0105070c08030a0c0504050301 83
    0x450441e1035621000c03c1c1c444110034407090342c655003e00c035a03e100350518404402010084c414075180b20306042c420b06840f0341d00c01c104443e01e0b40c3d5100c1c2660042d40242062a584690151466a0001440c0d8008072030002400445d41030402082c1c94003104140e403c0b85c00302c0007403400300f103460707190803103000b940c02200300100f505084480c05c40303442d003034401c2c1c10040c82140569039a000092180504a41c0d01c10000308140d4030740382e0349629841d001813056485543d41d102d4030889004c20f0080a02c40c60119040125514000c0200b0280d802c0c1ca07089513480b01d10982c1000001160042200c0f0038a402c142c24a4050f03441c0341c550341440c415034080020380d010300028010846000175003032040d240d070306100705948110342d1010f4440303002d0000c66000f101c00ca80003040301e000f680c440d0800c0d180682d25010854000444c50601911720003208003005900001e20103100200038410380d6000011840c141003041e041e40c48444180c007001e4010b42c3d40d90360760143c1800300340c058802c8900a0070003500a0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 257201744 1250 257200494 257200523
    0x4020f0f06071a0906070f030903050d14010501091706010506031302150705060f0606070f02150a050403020f0103020a140c011506020102131a0403030c080706110d0c030510060f0c 79
    0x4441d415100f2003204854004400315a4810001c204180714103d00c1d0742d11382c04081600400c4001d423406071000e4091040c200445104400079016007e4003050303000c0b041006501d00b600050000620381d00c03040004032502044c0d608410082440c604691040b21856140d440d1441100da448070b80e480000d61104410805500201c01200601103250041d0103840c05961140301c1d070001541c08544a6038803c9013040b51000245281d201401d0560024004803107101c076641c920b5001d5400310340380801007140403070204114a020240d00003240800c3c40c0560070711070040310140602c1d0941d082151980800b080f07441003444258410781041c01140200d52196507a018080e000b580812030402141c0c403400004622541c0501601c0304245010002507d003525544049030000755200d0102d134601010000800403481ea2300a542d07002e0000100f0680e517213180c551002c11501c0040d829410306050608015000700140d0300c45080700c80500307140c0064802d080045944038030300c40c001440c0501d4005c01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 257202994 1250 257201744 257201753
    0x2119060e03130303030b060301050a03030f020109060c051e0708040b180a03150b010e031c03060b071103060108060f0f0606070204090308070905032d03130e0406060e0f04020f0f0607 80
    0x202c4100c9000313031002c115100c210000c0c0300446c40240103c42d04168805001c000092190464a0126500f48000200700c60507503a100c0c1514400c01d041d000140000c28410308c500c0c0e07080c00d03907030300c0c904c2c59100607240c0038040c2d9451109014a2052020184001ca4100d2744c82c0d208400f41459910010689400144c4030b19088803084003485032030324020302c1c014a0025650013501e100304000d0005008050340300813440400241d00a000340d0700704140e00d440e00080d022003410301070001030b8400c0f6600003085100b002814503100f070582c42207000f68000c40030f00c0b0294484602082c0c1010b248403800c81d140d91824040b070681c4c0310342400250042e16110024041c0340e0311079101409203c859540c0350050b0b80d20700030181e840c0004031001c51a00d442c17081c03190100c0740b80b04150319807444034000d80c0c0c10007032103440c2102c02c0003441d4000c3c80d04914160400003048080d11030a0050803562450700b616061051910031200030041000b0701804805201d4190f40d82c031252559501e0400030b1240d56100b00070b240 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 257204244 1250 257202994 257203027
    0x140d0c090e0619050417090d0f05060a150b1c0603020603040b04060609092004090807060c020c091e070e04060f031a04080706151802092119060e03 65
    0x24400e078080e80d00800000c0c80301c254004c0b60b000c0c5800c500440a10340c21882d40d0303600d581c003900201d90720114944030180041c800400d040d040318060b00c0544118604a4600000d82d0301c0e8403804000e01c00720714010711600c0414025105441680300441e000c5454030b00f40c20004243d19040654017020120811003040a031003003040c490b030305c210410f100d81583c4002190650704c40340002000349207410405034404079000b00c1e00d40301140050010680400c1511000080e503c0008142e40107a1200311303080d2f5041d01004040b1a02d0f4081e070315154149800c415040311240c003c0741c21105802c284011843c41440f50b0500750030080001c00c104480da507074102c039024203031161008582e048001d0404003070f4005950352843c404c5030031240382441e0200c1e0340c0d0b80e240244444001c820403001c5100e03000c10603140071080d01c0803000342e034031005a0303440e00c000c200039480300c00c085150a41c11040010500180c00400d588000100592640030800b402d031070000e001d80801c0b480351103e8800410081840307140b501 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 257205494 1250 257204244 257204251
    0x1603050a030806240307020c120c09090c0a080a140d080c03040c0b0a0c0201020c03010c080112050312070309030206100609170c1c0b0a020c030304080a020307051606090501020106140d0c090e06 85
    0x7000c882c2d81418101c00c0c012601d0911101e1032258200500c103c4507030030701312f5440da8014107407800d07220012800400210902c40d150007000d00c0350300c0400020104808448402c00842c12000104800e582c0c08600030400540209004100310f008004602041030501c0044064080d08000588038056040000c0c048450090144d0052190b2001140641018808d8a507c0046655132640a030308110380200b245000d00c0d006c440b00c0c402046000e001107804030005014545550f00451f81e44082c1c11f0013864018042c10141910404020030452260084100707001c41c0e29240d00750511510100c0b4080c24002001c46664000c0120580942d02d00c24050155100620842041d0316503181c0c6c02002d012405005030a80c0c483d8800c10104020840a0000d401c03095076901c100d0345411071980d9414208024507506500b43c41c60840c0521039690080c030490060002840200f08440c40c02c3c01306840120f80518090080a0700024001030000050628002e051011803c0c00403410f1921a03903501c0300101d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 257206744 1250 257205494 257205497
    0x6070503070c240504120807150623100206070305100803030a230103050706140d1e060b090a090b03071509062616090f030606081603050a030806240307 67
    0x101c1040032030f0780600c3c02d0760282d4044038990206035541c3e68440d5038542c04003009075500426003d8524100119000d02d0000d052030108049003a980300105007040541d51910605c10617248210415070703980000c405a00080d01e24006c525502ea80f00300320844446038102c44401e01000042100d244207036046511180c000403601c40c03000e65505842400b003c0c003804003c00d160000d0038200403540c0b0808801b0000b03402e1461003860020b080c0c5040341251103c1a40134a950000c0107883c10320a00c80c403d240003001e140014a15000b03162000958841c2c0c81d011b40003a195540da400c00081e142040020040c0801103c00080e00914041c00b07800000b803071143c040050b19040345061080c52542c2c0d110350180d00350620f044141c503001c81010342580c00140750010082c28074400540300c40082021001503014800000b44103041800d0380303040844012a030003d9800c0321400b0800510700040f00e200301601072038070000c192124400140f100c8885040c0f0350900c1c074201c01d9003c8000d103502c010341c01012207 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 257207994 1250 257206744 257206799
    0x1120609020c0303061f08040308100902071113020307230417060a11090d080901030e010606030905160e0c030403031b1e1806030f0b030607050a12060e040206070503070c 75
    0x80c06c60000701d805a8100c801c00081d0114007003400240104000c0340c200403841000008035403180402c030700300d03007042ea0107480c0054040300200843c00c0200540000250510095146292a0101a10031003002c41048501c202d04000020003458400944000e0f080507c4071115284828111665410041da003018626140c98000c0000c0008030b000c8450701c610240c00c4070754080365030b100c03d91642c00c2500380506050311100010745204082c45603001401c92501c1c001240105402c22915182265900034074020003408284840c4c8000300030994000001084165240c0d503603d02107018003200c010105c00b48201305d0f040340e0250f400c640151413206807054400000b40f110b62003220071001c4211490b00b15041c0c18418800140b0035000041400c0701c2d07540119000626501003440c2081c22554240000c1021441050702c0b9846000b000030f0070032085040c007910781030840104000300c01a00082c802e0200140030341c100701040c401d0304c0c0c0d4950801c050100040d502d12070349400503480c50440070902c51 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 257209244 1250 257207994 257208019
    0x9021306030612121e02030406090501210e16091d0105060d0b060303090d0b010905060a030302030909100305060a09050c030f06040b0603030f0a02011b030b060901120609020c030306 80
    0x100b07102c0e0030120b55a03019a00b100001c1621040f00d030080650100042058404142001c881201e044a50641c243d9004569861401c80000c02c01002034000d2410003003c0580b161510300b000d08080102031900000080c0c0010016680340342c034042030304001084115090005601440c3d60180c5080008190044078081c080c940182c00c0703403000c4510550090443d880c5030b000c80c4600400e6a40454040c0889242a003d10b0018400035240c003822200040800c0060184000d240a41354000b00191001c0034203d04550300a5128042c4035081c03406800b100300000c050404945954000718ac220056030740908040354150040c00c3d41d604159041c0c89418902e26076402c0009480c40203e004202602d4580c503203a55094054001411285c1d240c4010b2140080c882018002484845402d030000513444803524610411007800c841d02800f85803401c01401030725110740d011034103d0740c42482d01100c440d0504d0700d00002001c0d55001151003520206001c5406000000114054107044803d0842080d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 257210494 1250 257209244 257209247
    0x8100f02221a090d1202010b04020711120708071a0708040902070b0f06030c040e030c030310060813080d051b03070e12030306012123040b0711190f02090109021306 72
    0x2c50800310f150001e080148040118a042e0700044961000d440082004c071040d20004e0141e0300400015540019040c81540061510369020072002c3e00440c00380c0652480c10004945448031031140c0d10b070440c480c030000d440c1c1e8444581280c46140e4452561501d031510313000c0c407030025040304078102d1705501c50310007240e904144110380c24492400100206151010b110a1202400d6000042c00042c40140000f03007164009001942c8201c006c404054045032510400400c4c5402c0030300b90390050030b200e21152021440319011110300c810703414001701da25211120301e41e4400e00d840e000314030381e0700000c000c1c400b2a41d402100281014801c4480400085210800e20707200c1c0f100b40c8090340441e030070030384060700003e14400082c1050049080012880c00c03030880100b2071100c8203441a09181120200400c000100f4070039a0010090b240049185080b20341e116a01c0903031a10000764148010714440c2000f45400c1c040c5132095014000f20300650790703001031001035000400d129a51190741c0e6004030f0510b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 257211744 1250 257210494 257210497
    0x11b0804090e06340210090605071d03030909040302150405070f170c010f0c0804260312011403010f0e0606041409060a0b0a1d071808100f02221a 64
    0x183e100c81e038580ca0b60401d903c846013000b01d6481901e0a40c004d41901c210210610f2044019582c0118004502480c10400052400d2440300781540d00e0802940d60039207541f40007094504910080d0ba513460140c80d2820181e18108229100340c0e40400708408100800c0300208400d0b04903005800c0c2d07111540d8072860034485040c40754212582c207500903072800d503480d80300d00c403403400110360341c1802901c1c802d0035103511100c1c2d0710a4010793714120400741064078a034840760b6518040010040650304100100750080b48005041c8038544a2400302622200c07540e40a511407181441e10314010810a40e60070f8050391100000c84480e4807646c83e0412140c6021005920f05101c0d24800380500070559800313050340c004003004013800b90004409080498100038810311810b01c2c44017a0030665907898100c2d0001d0060001040c0700c0034451010104000488000031000d4444410308400309220b0050130700e0344002d004242c0309a001568001e080034044101c041d140055500300264881e20001d1429041c005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 257212994 1250 257211744 257211781
    0x9070c0b0c0c03030c28030c0206010b1c050603100c0207030b010602070305060c070614070e0f0a1503110903070b0c060108010501180c09090c030218100806011b0804090e06 76
    0x203900104005001c0018910040902100c000d041805072041b107040102c103640c6218146000c07a03682c52614280d160100001c80c010000c0c4182c051820a00c155008204600004000d81c17042d200c1d00420300d15a024081803007507142e00c1100b0050041c180400035520101840b0a0b00d14410003400819054400300707500055a07004402007525441d001d18045d1182c0c40141d00b81d403210740c1c1d00341d0070032071544600906028080c5540c0b5408442038600403c039240e40b00504c00c6200d000001c41c10000107001042e11210540076060000300b010358104480c8203882040f840035450b02a2480204102604402603c0c0701d0890504032007903030780c03100e00305400c845081c002c0419000002010389d180703460070b800402c00800c035031601051103565466007606680742d2161070804a070300407419205800381510151100e910444a0201c03400405001a000742c00160070103040000720011100d00781c001c0f96907500229400480296901da8070000f0300010641c0000c43c0c1c1e40c601843c004105400d0000d0b240c00c0d103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 257214244 1250 257212994 257213017
    0x50402030f0718031b05040e0c090a0914030304050a030f0302091f0c050115081b13181703070806010c21090909060b0414070903060906020909070c0b0c 67
    0x50340e211110700b9074209001c14600b00d07a03d8050b420200c000340c10404601004010000341c00c59050138601000f041e102100c040e00020303030100d8140e0006554400003150800060580020080c04a0a04001070b0b1130011140c1064800003060000f0043c00041c150501406a6541511281c1a0004a040c1d1142c03600304ca9010b42da000c3c10003000d002c03004185200c603501e420035a00303c1240b0381d509400e41b12a0107480070b070203510300001c201d01a010f10440c80c0410700c00c00c0c10006000d901e03001413000640c501c00e101c60256515150303c8008a081980090b8942056015540207070054000c680341c2e02c00c84a1100240804c8040740b170b00d5009078030311103002c0d5220040b019203d58000c00c4c0203100302c5d0034440d1010020480000580141503100d1407003024023446002c66880052000c0c0b00c152604110201162803400741004607155000c0000416280e00c00004030783e80d9030034100080030b40142a40785a000012b50306009038150050500326509102d12140141c076a1140240503580c05560503c04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 257215494 1250 257214244 257214271
    0x1506090c030105060d020d1812170a0b0406080a08040f0e070203030609102c150105040b0906450d08031b07050f0105090601061704062a0905040203 65
    0x800d914208001d8000c00064880050411fa0500400e2003990b0212510303503140750280c654501032102440c2d000801541604041c6070044090a820303455440003418040010350301c80d8144a55943c58100748010321101c000c55101e25042d0503e244281d019208800c04407806142c005840031483c100140300e00745c1c64025506503036540c0140305111070001e007406000302d050100410701c3c1000c0e0180b19003407103e44c1d10013200310b111001c1081020344080c01d4150b4100b4101c12152841e0303071180442d81a1410789402545132115040440e501c1e028080d0a440801070381a254100006d50301021a4081110b62128813503102c09640000d241400d001500d0300942800345541c0030403404402150001400003000b1011545201a2a001d80000100320390300d81222202d0855403109020b01a04108072502134207495240c02c401619040b14a1284011140520006814003c1a42c4030f845211059600340181645c10716550621380a071500810101e8068a0045980e04151003a80d00c509203414481 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 257216744 1250 257215494 257215499
    0xe0c0105030f1b031302040f0216020d061103180d03060503070618080304080a020907090e0703090615030305092416080415021506010c15050601020309121506090c0301 74
    0x80b019603500501c0307103048100030841c41600b5040b070030066110303141d00000c10032031070304a20401098455104083c2c844074010b0024040c1c0b0104401c60102242d41150b9078490302c55240b81503406844c0b081c0c0d401d88114004010010a1321914107070104015000098826035000b020081c0c017100c11601943e6015032214030705002c1140074035807ea07181444100410703002c1c0da852284a103035034443e40280003070b6000a41c60200b14204070010b19008045802c1c43c806050078200300209034880103101000701922040307408144222580f1050343c98041e81300c001200c6849040c0540705500c51400c07d406024558601e00e030003c81c00c26442034010500140615003030568284031805440040300b90b82c5c0110800000030b00c941070f401904160310540d005880c83c0d200444420080580050071141030003040c026000000344410038005582903138680004aa4445500403407840c0030f00d20000ea041000a50007507034000c2d00249002c400d1035800c1001c4815507070708061290401c42070350300403c060710604c010f = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 257217994 1250 257216744 257216761
    0xd120218060a1701030f1103030a02030a0815100c1202070515130b070b0103060605041406042d020c0d020a150915050a0c020714030a02011116060908010e0c010503 72
    0x10003012515183c007400c00d200e40302150042810030383c000c890310020f10a83d41d0402481d40081d00f4142c400701c0180d07042c450042d030b010b9224811044940d040010000008606249003000c003000120060881640e0403500342c005070442e15048025110f10484040f03008005200050100540c0c00c05032103918100006400d1040540000690030500300101c0d1001c5010360b014000f80042038012100411f5a5142d410040c0490301c3c04e802c450300032400c210528103d00007072802c031034005030107444c0050040c60040505007101b1046103140b03410084001c001c40c400207950007400406510a050711801c4020960987c0c1d510031001004241c22107003030b122030000300d4076408110003d0050a00b003032030300100151242110000c5599070314880d61001d040d0310391641001103078080d1403c4210041c40480e01000682c0d1501c42078002810071400008001c0c002109000c2a00c0c0ca5020b4003413034203559181d90024001b41c480b809900b80030b628003c040502e03030b1000611040c054006840741451620385603007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 257219244 1250 257217994 257217997
    0x1104120201050c0a120801090e06060d03051602090a0915060e0414030409050106050417070302060313060204120602040828060b031906020301090609020f030c1605030c0d12021806 79
    0x83d0514500132002040041249090643c0111980e55103004056041149400807034170a219040d01d1a880307403040141c0303500d070301e5546542c494050905989949804460403c0310f12140c00080d08581a0800d103d401900d94010b8100303035101e011080300040e5413041d41d008031007043c451003007002200340214005c528940c0843c42141d200c0b4081d40e10700703511012104141d034000e900010000d100020300f0042146600c40c418410000c80010344249481c5400143c01400003500c003000b020326504074101049266411034005110110b00c03890085d0f03450030000001c4d0418410040b40d801100b0403c19500c00d1a150000b00f40005051182402d09940b40c903401080b40802c9117402d441094240c3c440881c1444415180d03503c241009030756981402c01d124251a219030144100900511007900241c20340380a903580034200880081d2144028002180785107211000a403060000150881d150500490300091100151301d807600b0050359000301c030040784200a00070255a0602c80c00f6000c501e0180c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 257220494 1250 257219244 257219257
    0x1e0609060b0c0c01030e150412110c0d0602220e0604050108120a0503060a180504050705040e0703080901050f0f040302040b010f0c1112011a03010b0d0c030f030c060c02030d110412020105 82
    0x212440026007110241f1501344c103650941e00201c1c0280d14111007680405007801c0c00c540040500408202c0d2400704c0c00c40d190032403004003103503004030b18900d0148a080600c0100c02c0407244254017203542d40030152310b12000f42c0700640914204400440c250100140f0f040c0d560440020103441c10803180b00464590300040d100c250300c40100100018003100800948519910505000031982418030340300e40703404000c0d801a40206e040400500d8a03d40101e4541c040b0794116001990300d410003001200c0500c51551000c20b0703001e011410250741c0c5100c00c00761050f0303442600c0c1005a041540c0066075900c00e5040d0090006030b0f141a0030740090201c603d864030a810103880e00d004100d19003480350a45600700c00160840480b60820303c041d00c2e09000e000c41501c0c043d9040d1483c04115243d294000c42e032070001800c84881ea01c500d408140c8140c0101d000250812003c020f10309504000071346035801880380e441d00608080c190000c221070300301110b0484214081901e6088503950054650380c1091 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 257221744 1250 257220494 257220521
    0x40e060a05040207030206160201050c041806050402071506082d07051c17090904080c0c060708030f07080c0306040e03070204060801200403110906041e0609060b0c0c0103 75
    0xc000503251164005040000e20070b0b0041c1025142c1045540e550b00010080b40d011a8101010710041900d00c4085400341e504e091154400200c84004c2e101c003030f10b9070b80d000784d410620004400301400300b5000507c00c508103054003403125540d1550400c0d0b0304d9046001c1c894030708282800ea1501c2c138140300c0700021100b51901c01c0d1418540d40744001842801c00c60030030714000900d4000141001401d02801c3c000f22500c0000504090702c11022070038500d001400180707501d6000035089410f200030814014441002880700b40d884060b441c12030f103241c0040d40d0210b0811407140201c1c41c12400f920030325101d401030fa0340b4281507958180410014010354040318410340030400480d005600c0b64000c0c82e001e00314220000c140b0110171680b0401440c009920b03800701c102c040c00140005031101e0f1180210a5003214291121744030000020010642c0030007203081c10201c01c89003c10310f0919041502121800c010401689580780001c3c1c180384100000601950490070000050790f020307511514005038507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 257222994 1250 257221744 257221759
    0xb07020c12064308151206060f0a0806010305100e190219031b05030f030705100518030d050f060102121e09150d05060607020f0f03030d022b050c040e06 67
    0x101100f18204040915007000203800003080103000c038403034902803009200070781d043c0450743d044008650315128040e10702440380c1441c804080031507440d00a40800340040c402540e1440d6503034070344079a8442c3d0310b250701365420341001401c0e2030f288404030303035441c0f4107034103614501c80003440d5030800c103031540c80069068003044103503000701c0805c0001d41c0c0d00c6925011304405840c01c034140740030545030044080b41000180d10811644000030004140c507a807100041c0c0c03011805482d004181c6841080407515254a4800400c00c01c8184a0f66005540142c002d981184640e45503d0012610340300505103044a14004204604c9080c0050742c048483c444120062030407c68074a001801001c7c0c00c00d044030444002190300c88460f615803085980002085550b140b8140840c0d000c1340d041c410340c8070414410514078114014684041c405c9541031b40d207a04003155140409154210400558403450301c01d911500e81a441c0c0c07a18901c5114014068040c0040c2080c0c42d02c4100d0000f103000030444c5130400d0342c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 257224244 1250 257222994 257223091
    0xc08030a0c110d0507050120180a030807060f050c030106020717010b0d0309090507180e13060501171011190e04090807140a0308010b07020d0b07020c1206 68
    0x4107111a002c005241d035201691a001070074500c3c251605d16408c0102c079217841c0410502d0b580c2007011500d50544e440c07014401005201c0008503148000e07031000d041100005a12800c0207019800020f42e509204005c0049032903248882e00140000d028840c090b03408038806000325905030900300840144840003055085640010821000415600700c0120301401d005021942940c001c80e81d01480502d00100507030007580c00b03000c0d46080c2d4031803800289a08008104a000d8070318000960781d400910602030b65948854034100c80140458000305c41c0503141480f10126074030b008440030310803241d00c014184100a82010703012011125a103080c041038851f2407221f9121805125082d40c02140721903101d0403c1d080051141c0c840e00d001c07180a801c07032080c101c0001d8028001c0341c1550310000c040c1d6228200c62004c0398003c03c0f0000090f24940c8181d04000c501c980c00107400186a8050380e40340f4000c0d085c0850701d070b9280002d84200e1114a4800702c20030743d000401581c2d00440c0b000381b004002001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 257225494 1250 257224244 257224277
    0x60605060426010c0e0d0f060e0607022802220507090f09020c12130302030a0c0501031b0c02010e060d14010512030f160f020a090c09060c08030a0c 65
    0x3071240d4440000e5240360500c058005200341c00c0500d050900c80001e04c0050700040e00240401108040907101e140600e20107814480004207000303403198400810811b1400303d2010540e0348104451007801442000c0840000c030140b00c03c0010410180120f04406400b1503013005183d242e004840582000c40309040c0280e10b056008260052215403110300c00c06040c0011540b003240c0c03e801180d14103004201c10905060700042d4112003449d03044d440341d04e502c00c1107481030320b408882d0b101960511507620801c0920420010440443c0c20981341044103120305200808249400034010303020a8070f0345078040155028843c8510b4440b401030069141c213130004a404100c43d608402411031090f074000620941c10004141074101600100071400c1c810b044805a0b07540c8110310f035000c4440c1004c2042d50030404c04d548181c50b0035034006c0180034416110700b010001403500307948405c005201309000242044c010912510400e4000c0300c9280745a0350001904040d00e0104002403c200700d000d111141503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 257226744 1250 257225494 257225497
    0x20d110301020c0d050c120403031e02011b0504141807080408090d0f052e020723030706050109021804021c0e0c0102060a05060901180b090f09010c08040201050d0906060506 76
    0x1304030585943e03407682070000e503251400310858501108103104100601c00b20b504400700d0200345042c5c04214405154161041340501000c42c2c03170000030003c84801c620281e402601420a030b815030b031241d0000c20300035010428503400300e40d0081038410301000490381c141d200e403400507400381c0100744040c0351800c03000119220300380052003500d440c0381200740641000028001c60036600e08500c40b450090050a0b684001105402076901410fa070000320b00382040296001c10243c50300200da10952a0250545140c403030b4026501108e07094a02000800d01000d45d10030340388000e00d100d51180d00f11580005201c003d41c811640121004100003c01031191450b000301001328007071802418030640c0c62000a464001d000d00180c0e00903081c041000b91079101c02e80c0786e504441094140121002500e14460002c10802c0c403200d4118013035a040048146a51a41a000d0300441000f0000140408000ca5100f4001d9070000d0000d06c08209180d0030704013941010070818001c15000926607550800107185 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 257227994 1250 257226744 257226763
    0x312060904030c38070201050702010c05090d030903021504051507170d02090d0309080d030608060c0a09030515011d060310050c0408060a09030306060f0e04020d0b031006080712020d110301020c 85
    0x1076621384020001c038141d080c05010740002d8640000d0098100d141000f40c241d001e40d128890089007203008032070605d40b0540c81c5000542e00035040b0740b40d055880b01628040d074424003956018429525040c0d005091202c03c072240e844e08208507075804400340380240040d900024031109940d409000744103213640d0760520040031501c42c0e225481e4240c9441500c9003400048000c40003414a4240d04000d12400440c0f0154400e4610b0b00c0d49a8030380040c00142d40d2042c5681000c0d140d07110340303122502d400407a05106d6060701c10244400198400242044503a407a00312031854154104061400b040c503001e401042d00701d441c2e40078450600340c55510b0305182000807541c0303103d01500c03240341c036092540500c02e1102400c414a8070301c8200e04511006028420728014075070150344d0000f2041040c030465407120101503001001c1d03510121607250348101a21560040040b0750250420020788110f5003214001201d40c050031a0444440c542c80c2c00d40c0307051040c114140c00d95000c0014030240c8000340040b9a4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 257229244 1250 257227994 257228093
    0x1050c0d03090b0c0708040b09180708100f0b091219030509190617071806050912010b03070b1b06010b031603090807020603040606170312060904030c 66
    0x5419442d401c0581e4803c0d4080c0420101d03c6040111001041d40141117a003540d0100001655960f01a00802e1540405c0340710131103040a40c00030300000c158416079a80c024108449038032010b940f0741a15130683c104a1142e0401440200b003100d4071404d000181408155102060340c042c501e01d20b980c03440c003801001c0100e000070400202c240c0d040c601140700a45440030704040041c01400c1c41c01c00f40c0668005a0b41c007003c0b107a20300c0010145846007983c500942d1002c0401c40f01d180c0d85480161160304002d030250711508032a0300c0711504600503c113000d0700b07040043c010000e02c3d10308250800c0c1980b0600f076410104079081c1003180380d00c600300720071402484045c0c1080c4e541d02d000c4803000503c031440520101054207044002010a901c501600c1c0d01640441c0d6907540c03074a840c94400010b00599018485007480002d42e0710304000c000c005002d0b94440c10f1002c21040d501c0c001013014148045400a021030901454800411404481c010450303034240b0011224600102c7c026200030f044281c03842 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 257230494 1250 257229244 257229251
    0x10e03090a080d0206010303200d0801141926010216020315010f030201111903111b0603040f1a0c0706111206040506030a15020c06060a030b0c030601050c0d03 70
    0x4440c200310508100030b1030403401802a182c40d402009440310b2061202a0420440c034101e81c03100071054038011041c04c07841e812240354079401d4034050f080050174852900da800c000412a5002c0c18820b4007805101e20f007400308d101843c1008008100340c0e40e409881485400001e1085240c01300074401400034200346040140306400c5841018030b050b065480c0c120740c00140074010032200038070924041c02e581c0e090a040070b0303000e60004110b03e040c600300c031107102c0462507501100506400c20080712080c035a800a0314070156958a4108030194000c102c107401c0141000020f0100704e915040c075040300c0c4162598200304c1100044064038010540d8440c1c65002d00261050402c840352041c2841e20060900040c28610000500c0701c0032800142214041c588540004070030360340501c58001903a91140003640c52100d0a00d80c1402904001c400020900c50303907002c40c40c0b6203040410700c41181d0348041c07c00704640e5a00191000c07908080c00c118103000c1d0511528862000601c003096014a0956002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 257231744 1250 257230494 257230507
    0x21501081606020d14181309150905031c09050d0207090c0813030c080f07030507050111031b0901170f1b13060c0f0b10090b03010c0c23010e03 63
    0x103030a2001c880c0c1c0028107540c0080304a401c16030304030705146112030301c5254413030b1601042441820715080724200d131a404100c00d05008000405507001c004114020400003e4107220b410441003100e113800009072050348180103106a400c02503644140d03122911001241c1814280d4400f4900a0030002260141c1c12140060104c0b041c64441e0800000b41ca1500035800d081c010b040c518010503140002e0104002c0500c44000c1c0300045c070032900401c200508c100d03a65503640c14001c0158000e80700859031542410f1046034856480c1066034080d144008038803890004041807403a0f15413002500700d05120f880c03921500a040d44080c0144644840300c0324204501d06428495075000303555118100303008051001500040303040341c0000a0f00c030541401040b0200710b041142141e0750700075000344180302c95010003030050a0801100d0803140329140c1407280e022440201400c0e14019004080041d281c08200c1c404240800005100915048404098800152100b0303084d03682402c02d030340c007075400003505 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 257232994 1250 257231744 257231773
    0x60b07030f03060e0609060315010b220602060613090203010911011b030e10031d0307020109080102040308070210050c01050702030c0c09010302240d1401030b060913030f02150108 79
    0x5000d070029403034108051410050054485400941890301655039180044d03400d403800c108040c9602e0a207001d02c2c0d060340c1e40d000c860400790b01000200e0b121629100c14600c86041d1185800281d80081e0040d109942e60350040c0a41240c14440105003191502440800341e2400e124500c5200e004620305480c6000e0480007425090140d03450703d2449040d544418003013544a4801040f075082101d99074a041019441240a4400c031940e00030307211403100703504075400b4001004000c66031007a210032105a556132895400c038021403101034a01e0008019031001490071507001543c01c04075080c92820f00c0c000314050b9085690072501440540d00010300c07014000c404100c0069511380c11070740c406141d0304590210303110100044605004601e01c903404103c4011180039a541400e120303108120130324840c0340745004e1200070311055501c0c0309510b0100f151420700c484003e1107484660b940901828007580c1c2240c01581d45c107001030450050041096035800f1580006000340200d000a007009041c5055 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 257234244 1250 257232994 257233007
    0x50603070b16140303100303052a060709080d02070b0a050d02070c0f090207020619030e0f0105070915021e0c04091401050a09020a090b06070c0303050307030507090513020d090501060b0703 83
    0x8a440507620a101b0001c0d18500c0001d14001e80c0d41c146401520f40314a0a520144151800e00d101500090340e84502c08140c1c0c0000c5045c401e459030ba607054007549d0b580424940b100c44038600403005810403c0c0a00480100c080101601806490040d03d081d2000e02414120b03003207090304403800380036501c04020728080138a4000103800406411844c001d8250300140180c03154020b075100c041070a628900c4a43c0c0251320221609030030000340c0e00755001c40c00005008100c00c581880115175030900101e0b16500701c40b4111244055500145204603611a02a50005d030440140d030301031203166585040d9498074000c04205900c95203044078900341c0002d2003403d40798028440d07007019290070650340159a82d014440103c4410725000108160b101c00880c00328417410f8009449988503000000825070302500540c03040d50380d81c0e02084a51a0710000b22110292841141d5000143c00710244031956582c1c02403c1e03111078014002001e9849540c0d0711300f0f5a40a40c490450454013040e04d500b8140c0150 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 257235494 1250 257234244 257234273
    0x20102040602100b04060503061303090f14060714030d020403060b09310807030c0303051008030409020d090f030e0108070504081c0c0c0f061b050709050603070b16 72
    0x298140350500c0c1c070095841004041d030b52100c6440d180d01084607280e5904c103070081c07c8042c007030300e8030b0b0b190070240300c60021281e41c001c0300021103960000952030200740c0c122040d1241c1110f0120840d810300304101c202c1e008030700183c03520380d243c04410280e548100002d004051000f83d001da00c4070314504080d0304444940f46d00c1c034081e000c004200700c485a110081d295949540080640c03200340b151004045050840310000d22031080000e02030107158200041c912800e100b030340d090142d60f0b02c000a050040700706106191150f40103100900c00b4007629000740043e2940d0301000203189003a034442d120b041404010a501040301c4801d140d00c1c55030b12011840c0e200d406424040d161628191500b950b88a1001e0300b8408141e09400d0610000d00c2440d0b1a0100c5400c040c0e001c1986840c0d15000e11b1400b00c0d48503007004140e444210180003a0544007940442d0340103c054034280e4a031060030400341c80010421981400b401201003500c03e040f0300a41003461b00e04002c0c0940441074644a04a8074100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 257236744 1250 257235494 257235497
    0x10501080c0d1505091f060e180f010c0306140d050c1e18012912040804091506021014061216090e06130f021003020c01060b0702040f0207030f0f18060c0302010c 71
    0x140103203c008c0c201039905401249180e00d01501602c4100c0c0305040a045042d251003035400c12140c262802e6250f004070041d0303150100340090090f08030040144141e0040d1004245411403610340e00185814011031549030507489443c103110303012000149481602c0d030403000415982c240140001d9480a0704400c11010308811001d180d80000703009010340c0500f1560314003403150940080d04220340e40c1d0684004180c204800d01110a440404402d0b440190040b80010300c02c81c1ca540d1030501d030038041d800107010f00403038403a000e845840c00d0103001000303000c0042d507520484028841603d0030003c9107005000501d40014007191540b138090034800040c01420040f61004c14107030100c0d40903c004c107400c0f0b034100d0780d0155104c3d06620030380190045640d40301c041c2d4030b4400c00080810301603000704000352080304d08200b4005810400c9040340034012004d4000342d138020400304c00c140540d0104840360842e040c50b600c01003801c08600c0085a07982c12620018044a540c0000c140e024000d4a9896009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 257237994 1250 257236744 257236751
    0x100905032a070e0f1819030c0b0919110f0d0305033408070e040e010b0118030804180b030a1a0604050708070c0309050d06050711010501080c0d1505091f 67
    0xc1e00b18030560580142030384048400781c0105034040315040086140070b506c003140361030040a4506000c2d000400e001000d44803807280e40e0020b1140d000c0841d01000203101d031203a000e520001600c0d42d9052416001c41d25400502884211106589070311301140341910a81da000d582c0e00c0c02e0702076850320f8a0442c550009851143c10444109030103080b28600c9180e080c680b415190751500400c86110224540c0d06070094034003040c0d403124500640209606000c02e032078208014581405502281d0300e107100c06401110709001c1403006009800024880e0882d543e00440d460803074000080c1440d010840880e5a82000e032481030b208448040c0090340600c00711820081c0d407a0228000e4188a40200b0010402c2096142c03803003050b01441c4030001414001d0f010920080c2c0c9403030204001d000a0b50000081008546000c0c407040050190700e0503101e115010346a40d80c1c401091041c07098800c0c8003250b001c5603000d00003003905140d114030f41c85101c0d100000c05012000001e10312144021010707845c1410b04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 257239244 1250 257237994 257238001
    0x120412021c0f02010b10020609011a030318010c06110307090e040b04060c091a130b040b1204030e030f06010e07020703020d0b09280302010b040e100905032a070e 71
    0x12811041c11110030741c24111010000c141040b070041003011000c07980140201d02c1c0e86074a6600140403841081c0d8030008200144a0441140b070854440b64001d1b4158410420001d50700000c1c0400001c107a0181440e50581c40c0f41c0d07440c20151000c9040d211a002e40101c200010642e10000010041221590440c0641481d03290380b050701c079004201500c119200c01c04444014414040a0002d1040101d4a82c105601d600e00704007542c03082003036034550790b50b1300404601031642100316422a05c054101a240000c003255840071800c000340260140441c0014841c000d80342403004244400c8441d000c2e105030760401031103403000d0790054440b03011948441c50074001a2209200d1680c203507041048030029542c0c00941624040c90035541e00110725140a075415180e009018103c04a446a0024000d1042c0c5030203000c00c0b01c400307010b415901d502040c0404524003150b0311550065010304241c07448d15500315103d292003401700a502c840b0340c44a0f0440c2c4600c0c4014000000605a1700703105140030305 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 257240494 1250 257239244 257239273
    0xd050f13060504170c0601050915091902040308040803090a0f150813020607030207030b0105010314010501050c0111040b040519050109050913060c0816031118040f0212041202 77
    0x68034900410345565500441d0a00c040144110300c0b01c0036030310240c0c0e50b88a0349038005803250828031510b4041c200c10390100d14006400944031502000240020007641d40d54a09080482203040e40c940100c1d900b0440480868807a42c010700c09028600c0096545001c440103111010200f54005a00d2190b03801c41485012450482913003114181e19141e05c540d19149281164181d080c40025440000098220f04264001c540c180480c1d0190b0f915451580c3e8a00040d0305807050174203c80303034160040005100a40c01440a01078600d0f07004d00005100c601190921926403180d04861ba40e03050114041140b4909950750740d5201c002640c000d11100e05e41030020f05960660300403248504090000185141074428600b00220380001003800300403c010030182910300240c9011900346180d403141104180603009148610103c61a01450040b46000014242c0080ca01182c0e10948400c2c03581d80c1244180003034000424030038950701850400e4500312010343c20a6900030195002001c0000401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 257241744 1250 257240494 257240521
    0x20a1101110f2104060506030d020307020108010611030d0504060b0a09060f15121e111305061605030c161d0402010302070c080a050a0201020f1605040c05120108030d050f 75
    0x40b40c0c020007040d02c1d0501194140d0511807000026004075240000700001d01c51140c00c650301070b1400f901990801ca145200c201c0c1c0301d10580b0800b03400704a2150041090601c0344040910580a80c0162800d03c8030000d0b030041540c206071029500325840e07510341c14407494180d990304020950300c0b00030004c0e1490819070004e0340340a48201100c00416207528081c41d40600c03c00840303000e40c200300708415500d9581080889900341075400b055032510000030211034a6a0490b48803000007980b07100740c2c514200402655910280c0501c5240c0700d0f448205001441c2000038184010409003d450400030040e22001000c10325840804a00350b139403200021940c08a02d01c40e0014bc080c070b00560368603a00c0c100f5241d17608113035201c02c0640c8a2803151206000001c42c0b80b24100c0d10036404d403400c2039090080702d65a00c01d080f031441803080940100b04120315065028001040700c60400c50f092040e03585542280d00e40980c0329400d20b800c0080c0d0225000c046100d1554056090038108016003400129030000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 257242994 1250 257241744 257241757
    0xc050105090d1203110d0606030b060301051f02100606090510170c071112030a030e0309031207020409051501080d080f1f0312050408060901020301050306130606050a09020a110111 79
    0x500c3d2903401c01e0303c100d110350011141e0711480741c0182d40d100c5071104004010580da22403a00041c0c03400081652528021044070304a5000400580d5907495000242004006144c421420351142590206180d005070182400070001c0b034890030101442d0030b0501040c25141410700041144201183d05055418040c2d260000e400555803610356905180c03042d40c9140f008140c560000c0a060354842c4250000003d008482c1103540501c1061120400540d8134001c81071006ea25030845034500c6c15003600c0328003526110b40000c00109020f032650b224181400164840c00c54014980300c014010141e00f04244400018580b401040e5413814005040100e580a8901c2d800c0310074a01240451804950a40d0041c40d0002001074007100c1c200400742041c0d1103413041501c6802242e0000710401010710a0301d0403a4800750107001d1745e030794034075100b10011000300c2d00b10340190b5281404110760300d9611400000e841001001a038400c0506e4000d040525282800445681007000240c401c0c000542543d05 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 257244244 1250 257242994 257243003
    0x120304061409030115090f0c0e06070c050a0914130c06050c010e0d02010e25090e0f03030702010b1813120203090603090304061e1d040b04050a090c050105090d 70
    0x165852852241c00c014814603040e50303810341c2494511101510700892142c1200c0d0404000c022225200c0c600000b650103845220b804240341c43c0803034140e41080030040030401d02c030794102c0100c25199000031320804015040000d100f95503208400340c5ca54554035154001c0d405855010301360f520303030b1f42da0700e0103143c1c07070282c0400c1103808984104008000d4118144a008010a071424450720400081c000d0030340704003141092107568107043d107410a050005081d5a81550801c28090514918001603c0a0300131003905101d9070031740c031114010034000342d4020b4209600103d16080008100100c10a5046510a021078840c0a125414007200c1c032007800140d000c0302c10101a20504030076402c502800b200d07241c225a0000821100398004070003001580c4071501c0311440b240841c0c000c15501e08501c1962004a0880074085000c41c1b840307440c0848401004001044403c001d4021034155001500d030101c1c107544500e0380008200c407030701688020b00000e2070410304002c0d41c00d00046040342000703001340 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 257245494 1250 257244244 257244257
    0xc0503090f0402070623011d0a0b01051917061f0e04022a15010b160206090a03030e0f01020d1209020301090f080d1a18090705191412030406 62
    0x10307041e221901540d0406801040410219041c00d662a403119a00c1c030070b142d0100c011030004180c80c0c181103050040b074016035103c82019641c80e0303a50070081141103189814880309104000c0902000a10440146d0240d51402c0c106040140460284000940414804c07008078000420109201d160505c06c0541d40c42c009240c005a41d01040084c800c0343c1c455221003e82074080c1703158a080242d4000101c64090132152507026420b06170303244170000c2c0034070301d507400e401c0001074014000e01c2e18545075180010919072800c0800000070701710300b0b00d5030310440103c3d43d8440e90301402c0c502141a100e800702d00380054042c00f03010780b134010b20110030f00481d400b909581c0c048039800d41d2002d60294001c00d03031006000401071003504000a90303810800207068000d04004041001c0c42280c1c000d40c4913440b0203407240e0350401441034542070902e4010420541841103102c0051503645928071041ca2900907401001114189400d01000540800c40035004513403099120f41e8664000040b00c040314102d10706a03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 257246744 1250 257245494 257245519
    0xe0c04050d11151603110601080a020d0c0b0406081602010605030c040e010f020304030503040c0f0302030d050334090504020304080f1b060f0a0c11100b01030603050a080403030f0c050309 82
    0x150714201c2810340b01c5078000013046401d201c81c2c5900b03d0a0f1880d001c2c0d1600c440792400040d055664000900902c440d6400c202080c1005091801c80041028450178a0200007516220010010340042d88000c000a030b407403080c44941c10000c0b5009075a01814030081c0540b904103400300c0c0c0d0340c46400d81610f00131907841814803000c00003940460592104040c1c00d65603400c050400600c01d4006880a0f00c040140c15800111601060903502c201c0303a01a000d040404003544c82601c07960002468410803852914043c3e0128151000b0781c1100d01044104500d0803025003c000d240ca0520341190303019030b01c108140700103c0d0f0700b6825030f4520300781030240d2135480d04480806406689202c001600c079120304030900004d80001d4400a1051045000421890030060012506402c3e04100c0402c580c2000d810390f038900c00235800248058506050100303009030380c1d64469191211594054030899400b0605004240d400703c8419419500e81c60303c0b40b00c004858441d25100e00c200c1c82258030403604401c08 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 257247994 1250 257246744 257246749
    0x3020f030615010f051b01050103030305090601060206060d021201050702060a0e1902060c0c0901030b010e10061e02070f0303031a030601060215040302070b0f1903020a0c0b18160e0c04050d11 84
    0x46a0300a06e60342c030086c007a0f03907100c2c10f444c1c0684028081200880d041100160102c00c002603194102c0d005540140419200c1c2d00500600020305002039030080703103044082c001c0070400d004040c0141c0c5c0640c000d00c00381c0707024015001218103451018100e50486e0300c8401300c2e12402200c008000350126507003669103444a203080d01e0300544110098001000c031000006000300d45411504842c40c01c002d100491392000c545541c0042a80114808500c1001210356902d042c0a8441c81d070608034011507441d0380d26001c10402c1d1a105038800c50002c1c0e203614440070b2441501d4040412030409a0060282e94102034010392100b981d0500100000c200c840010181342c401c009240c0241001900030782c1d02c00c2d00c801c0741c0d03c0950140580442420f078410003550b46a11904c00c59401500d02e070745400d07109525650303c849081c0c000e8807889850340c00b010140b8104c841888510f400d154107510003865145000e403140e081c210300070401041e4000c1404204082e443c0e030300c4040842075120344050083c1000400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 257249244 1250 257247994 257247997
    0xa060806130507020a0507051c0f020f04050a0b0f03060f010b0c01020f0d06140d0206090d062007031b081227010b28150212120103020f030615010f05 66
    0xc0344030070341001d0070301440903004034a0b890043d0080043e14015610380c41448981c040c0010750080111030041004041031528101201446c402001c022040320302c0c4000400f41e95065910100880c4e540f034040131036181c01c007101d10705214260b028140d41d140001e900300e02c11030140726002c4401070014003031654040a50469038030441d128500c07510382078229a40342c002c0030a030041c030700110300e0b603005040540782031000041180e81c0105100d10704202d201c01d01c400440c42c0b240c221101c54a40c28424851600722000a0f48104480d05141c3c07501642e0074005d1021070b0180200c80c16901c0d2029500116030604111013885031040ba42c50301544031028503201e8407806200782d03500c8000120710550004011b4100c0c445000b41154110303031041c41541c1880700251514800b820a003102141004840c0758001e02080814143c016542e2340c00300d17040707405060752180c00450902c4143d08010b0046140612516260040580c02081c8502d400982280b0b400540d54140e414054212140450944901c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 257250494 1250 257249244 257249269
    0x40504031206080309090c0909240a09050615040b0720030307030f0e03120412030306050604030b16030e0c04201318020a050f090f04050c0717090a060806 68
    0x104200003490743c1e0f55000c1c0e100d8004a1980c0e10901c06540454000c2c401300040c0d42d0300c0c070380060030042241c940b084000403034426806003804100c0ba1001e26061036440506410060030051030103d071500c0c100c4100076441003290341c1e00000c03034000e00040c40341d8803425045c0c90743d1590103a01e8074580488803408411a40010070019818400010b02004042c2d0042e031162040405458004844e410b6400f0141c59031a101c401d0785082d00700348010003502e89011162865140603007000070301c0b00d8030344001c14450b0b80725400c1528510101000d105106950314480d505501052504200301448803501544981d44944518411600d4040100300c808a450480c003004e5605401d075035640b030500d4900c103580d080c3e034031581189000c0311090b10b02e052454000c503414000c0c1a40c0d4140740a11440810203030b504001c00c000d41119a0302c00389105515507116182c0192418100c0e40c0e1034004c1c5242100d08004c020b40107205008007400740401c00e8480ca43c12005441190400740c0c016030383c40b800316208050b41d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 257251744 1250 257250494 257250527
    0x240106050313060e0307050105010e010612050c090604080d1403071e09080d020a03020c03060103030c03081b0f0d0b0406080d030e100510050306100f0626010e0118050603070504050403 81
    0x141d0f00302c4d528a00000140001031049001303024903a690103509000c10005d2041c0f4000c2501c2e000c500d841291958001079002e02031000c020708141c4030300301044060b082500640d180b5840300688440c00d035001201a5011160840403d280d89045503004140b4219004d84280c40004071012a0708a0300400300840980b000310b044609a00402c00001d41e5250005001d50140c01a051074842c181008100903041c0c1b41c050302e072400e0649040d40c0441d41d11000905049a501c001c107001602c3d403482d030004001144440d036155888611010904003218001c1500c0b500c00c1e40f801104000d00c460108a11000c0d440078200040e580808000031403d0a114071b1550012914190030171003e1000041c582d001c0d5041a802c407002c2d55121078030b002d0041d0b40e9000e4940a098168001c0244920911929175110003040202c0041d0b103409030312200441082c0c01003c10b4000321801071001c40c030449000100407420600034001810b10b0300c040380e00c03250b01c1d0003480e000e5030305c40d400501810f01510b03a40c0c0303046020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 257252994 1250 257251744 257251751
    0x20609090c041406040506070f0f120306090e0105150f030109020603090106030b0c0c03121510031a060906040506030a090210030605031c02190302100c02060924010605031306 77
    0x28520122103076019025100c080d88100d8052140ca0500d0350540d0107541024120354900709940e10390f80c891840e00702003101d0364081d4ad038914002464910f111115480103840c0801c220f403c28080b403082c1d400c41c80320160140c0c034120404c03030f03800d1a9031411100f4410503120300f8251403224022031b0240254200c040e40150700001401440041548180e04490095030444495224101184003a100f0400c803900f15a00074001d45000d0814420b4494004112014124203208201c001c01c0c072868203410300703401181e03480f0355100c201044100030b005c0359401207a41c46e02c0d1801510000e00140030324060123001d090040700080795001071764840e03909590000c2079401c140c900c0542c018050f0542d805018000c0c024092005c0a9200e0355859012041c0f141c1c01800b000344906081c0760700c1c80f410544c161308600c40d9040403465209140715040c0c840c604c59000d40780503d0b103541100e250260604c8244500c087c3da9501d40071b004038044049045d0707680c40c0303400c56603074a50080040b00c0524000c03018101074507 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 257254244 1250 257252994 257253001
    0x1b03050415051801030209060712020a0f060b030f0712150e30071109071e03061d0903091c02030115140a050603060d020a030506011202280302010c02060909 69
    0x2085800f0f091940c11041c250040c00b4070490044003030b030145c040c8298000c403061042c2e00c00980769128001620308684100d07400d01001d034451140014039020300703403070300ba41e110313145012810184000c0f002c602220340101211441d020010403203082454001d40740312056088951142d031281c01884e0030708036000403107030505580642240c60060444090314948503c4000e0f082e10210700b000c0e203503401c0e0070190a040401e010380901103000300052400c820030501210103280d509005a68501d680907d0382c000508508000030060102c0f20042040f02002122042229a01000003100ca00d0f01080d1541510341c0c0c07801904624541d88050000d515500382a055080c0c2d030401e804038412a80b00460410708200d20000b48000500503020703080d01303e07400b0130004940e400d10031090119544081c0c101c06039243e49890f40c50a01c20281c1012000d5507008030080d09500c2c0c07900800e00c04040d410402500070f81003034150300004140d440003d0511a03503a00745019507490304165040d407400540101e85524 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 257255494 1250 257254244 257254247
    0x4020f01111603120219020f01030203071206030813120c03030e010908030406050d0f14160e180a0c0813020f0402071a0703060b0702010503010308090d0503040608070f0e011b03050415 81
    0x40d00000c4e0401803003810074083c01540c0350080c060096402034210310040c03400c1c1c80114040d40c8001d0442c1c040c0b003400ca0403003030080d40600c1900011402213845984030f140742c1d4941c00c0008030075030101c010043d004c01c0c81c902107032000b54a0302c112503140c00c2c500940440a0300507207481c4419070003041d0901010034005001034210000701080c0b0700107042080700d034960310b10074003c0354216101c60045801d0381000403d4030400b820b21456509240c20114181c502d0040025505416403c0c521840e04a90303080c40404512800351807800392545c1071280f110301d27020b09540918101c00c2c3c0e020744a0042400d40003861b841d9036048401180d0450206034a0301c80400d41c108000000b658904002450220001000d00c64203080da0301c003a074142e5501345980d00e1a160740140b600906d42540e408180f5040000014404000030300040c046910303240c0081c94031040190451038103000c0c0c0000e1143c003140808090fa44101e50a9403072140d00946010208281000c44050086801c041c00514406110340c5c03049 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 257256744 1250 257255494 257255513
    0xa0f0b0607060b09100320060c240a0501080a030804170703030507020d030e151b13030605011a030c030a061707290316050903060c0d0b030604020f01111603 69
    0xc0291056402d40c1c584100170450550680310180c07600150782c5881c664a41c108100c40c00044004080703500b094600340c0040c0c04d01442c070f018803444480d10803d202881106801c400c0d4000540b00080004d50b151591590325040000c80040c01c22120100140c100841e1803ca86076902010007030b0383d150105860003400500c001d1304c10b44007510036503900b442c00503c80d0050b07009a0b01d0100c0a000740f12003403410b510100c0e1001e00481140c100c10306041c2034076040c01d00540104030070030013250302c040c0c694105801190f1041e0007520240c03180984105a1b20500350460741c2003d040700e0004e41c0c0345e40700b024610040056030042e814030030b0401000b5842030030000b1280169814950070600341c1d01760700c4102c018141900350348040d8803420f00009091060031005400c2000349810450b15080e2180d0000b405c0040403034144200d50301c08100c035091600c2c648195680d032001a40240000d083c160009002c1c0c075074100140d41008825440149807960900115001c51031101d4428641c80d100c0c034014908 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 257257994 1250 257256744 257256761
    0xa02150f07120c0e01030908040509360309010507061b0206090f0102040e06060a0224040606140f04020919030f020f190927050a0212010605090a0f0b060706 69
    0x140d0340c03044840e846103003446040c1509443d134030f510502080e040c0064020303280040041e00c204c04140400100c40d101e00b0401d910903101c0c03581701a00c4080c1540d4840310030903ca21204240303040e4031941000c8000010488110760402d00704183c039401d140c0780540280ca0306800c441011410003464807015500041c02c0f90151300c0303000c15075280c0c240c800c0d0020700700c3c002d81c441d01400d0b644410114646042c03110060907620443d00c143d0304600c11000c060303507040d4030340e040e0309110790030f05002c000500c8010300c2100c0103401082c0545400c50910400940401002c044951041e40e000441500e150b840080c4500d4490300c5603072005c01c560703803424103041c02c6810f00b0307050703005141c0300c0c142d02601c1c0303403244005000310010407268100340c3c1007202400c020400440cc120551611841c0d00f403a40042c2c55080040510039001040070b035841d032040c03282c00f44000e00308202e5681054400d0080b591405006c0c0d500c0100894006005c03111004031700c004d40326004040360088800502c1c50248882032300400f61 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 257259244 1250 257257994 257257997
    0x90a0b0d0608011d1b060c0f0604030f091d07030e0d090306060e1306050903160f0210020601080a020402180a0b03150a0303080a050a0603020a0b04180903090b0a02150f07 75
    0x1c410713882030f00c0b459114030441a000b160019003850039152501c01c60100400005407405060550940440f483c0604901c80e1040b01c1c1c1c03140d0100001c150344050300c001d1007040344c030b0003007a02e900d08004102040d45000901120203e04c0000039491446948440348404c00b94013165001d00026001400e1424940020350300d03103081107004503c00001e581c2e4140030316800c080519140c19262a018010306000c1c250700c0c2d803070204214076510070050322101468a0b004101808490449104029042e0342c13118030001550031503401000a846c002c5000d1281c075405840c0941e03204641020303c5100031324085441d60042943c6804180829140080e5202e0040302100c8500404014104000c0d59180c0c88024000740d070740c900080408090b0f4104c80d130051400440815816280e80c002001c80340d0b103412524a5485c040b808110f1903408581c901e21542c0882000c05c840075150f00c0090680c1401c5c052042444c0f000150024481c2c82008500c950741c421a111021352705189400a1004038203584080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 257260494 1250 257259244 257259251
    0xa060f0905030d02030307050706090f0605060f0d23010207080301080105070908011b0c1e050c04063c0f080a020f0301150e1815040b0903120a02090a0b0d060801 71
    0x207002d080000d008107400d10542c00171415039640c5d0008030b4490303001a00c2124000c5c2c550040790001080b441200880c1031080b43c0c0443c0343d00d019001d02280b00400c0040c940314200400080021404918182c44004544011000012152a4403901a100d09040280348210000000074045030650125008503191703503460b04650398a00c8031718240c0322400300c0b80d403000d14049008481e1364000d00c041c00c14280304445901e002c0c00d5407594030510042c0003070251035030341068441d101545054803920014181c59000c0d11701051142d20340d840266121868441c45596020b8214030a1200010280041c40b031141201c180329101e0440b6901e4003401402203010350000b445403c414501809074040c6000b030318980d40000c41c03919400c00703400c1c03002030402c030f0a000d2030205d4040d00303060a03c030035002c1d01907146213034540d81270610308890b00303802c0113180d03c81c9900180807200d4500e000200107600032001041c056264a1003000040a40300140c0c002014a20002100700281050344c01c08030869003244000c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 257261744 1250 257260494 257260499
    0x15090c030c0d08040501030203070309051603030801081b0f0d0c0315050c0a020c0409060f0c181409070509010e09070315090c17040c030206270f0a0509090c0a060f09 73
    0x46000b00b8a008000c0044070248070a03c403070b501c00d9001c0c1d6441103103480c0200e4680700340e4a0b081e0505504038001c14200c001c5013414400d00d0341020000e40140905001003007608031060040880542000110713100700882c03101010103507035003901324903032035002440c20541030350703e1424605e001d007010076103e007072810314000818080c0c20005441d0008c0e03150b00900b4056191a003000300519600400700e0300c650707880c9000d24449810344035103a80c06a050b00d909000f008031500000105007280c3c041101d889803e04013008a407a05424a908036100741066070b1105800d40c01038515a200440709500030300382c1c108201200398550801565603100137a44030040c0e80b100c10380707400d4619401c1da034808121503001e003420070102451426885801202420031081d2a40d0000e05568001d801501e5002d5410a900720f004034042194282d0901c00c540c14581d4006a00c049a40380555200b4607110b254041c0000b00070b58014040070481540c000c15040400362604000380410440080582c0002e1201c00003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 257262994 1250 257261744 257261749
    0x2031914010b01450501031116080c0f010504081909060206190e0304090b150711040e010e12131d010306050612010903020109020f0904150b0315090c030c 68
    0xc0d28080c80c07041c1d44c0d820221200303a90010324525072030b80b035003011090004921000e014000e40f04d20100560f90500c9034061030800010103480b20203c2c486030400e01040014804c1d0141410f4850301d41d4060721060b120310381c0000d100e050141002c4c0001455091008100c06c1145100040c80c10b0800c0a0480100340d040c1c0c60b088a240c42240201005a0f00800c080381d06502c205942c58511a0075031000b0500401020005056400640c05601c595865200c2003041c1c1c40c003160400b858021190082d0b040880c1078440a80041000d0141c42c05203981da64114102007080d0803004070038014000700c2d104900b0b5641e15010302d901005000100e00140344c4041490038011a190519132035010041010343d0031615031400402c4003816a0b5844000e1500160765031000303004014401c0c1c0203800005802c9034500502900c40ca04e4441140b2a4a06004010015007901d00701c601c62481408001040c89804021901c0c100c41c840c000721114400d07400b0441c1c0c07101c0000e0340ba404507000784d0548000c4640a800d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 257264244 1250 257262994 257263001
    0x50406120b0906060d02040302030f0304030302280f030909090b0f010f08060412090305070e0a140103052e020706051e0903070b131401020d060b16031b0203191401 72
    0x140c0c1d40c8105502d01050345454410302030103415402070001843c0a46d17aa00003407920350700170103400361a00b01240400a02da018043c0b14010001401d6550b205044d140c25001c22601c4400020145088246581c040c14890400e80700078040e5000104242801401d084103140f004650310214031070032800101e0070b03150315400341c030865905a000b0106921981d483c42240c10214a2403400c1210b64000000400c404220442c01000707070514031241401d14072038140550b40d0103010b00c50540101001080041e10001d078203082142d10304442c0d0341c0c000310710000786032102c0480070341100c3c18008174000701804000e500c503d0203203415994003201d00c0e44464040390300500c200d4200c0b4041c0c009000480c0422000074607a40e0114804001d0b2044188540d14040f190040d0104000709070350208100b001010103110300340c041c090b207040007420103104a84501050307200351001001c0104055160120050400c0800b41159004040d07403e41c9407032110121811000d240705aa9a15510403580d080c10303018030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 257265494 1250 257264244 257264261
    0x30412020f190203150c0304031d060307050d0f0c03020a020f07120b130803040b060f090603120c010209060a0f14090306010e060d020306010303020610050a0f0e18030301030305040612 81
    0x28042c19410316628820b540159074480d0698050140160302d26000740b080c00c420344102c0000240b00c0c0c503030405045c000d040888402c0d0f41409000901e610b200319035520310650380c0c01281850140e079554070301c3c400e550103044e204505103134550405031202e04560300b42e0041c09840c4d4440c0d08642c00b504038100065581c0600744500441040b51300d002e54042011204032a80c0081800c0c1c01d540020703000d0b55400c07a80da10445054501d0303c1100c00340722071440c00e04810000140200e0303250040b801e210700000d0301c2e0510000c004c0207102001031070028000080d0191040c100c80102181d468200803070000e001404071903035840010b4881030100c1a034480501c00d40305d5911001c6e000741a240e0928001640304900070307000541c031030000541500182d40c06c02507980a14801e0b80501401d04040c100f840d100d0308940c010511954040000707028200800452000b220500c0c0c00340310040e01c40a4091140e0070303039403075000d6046c00000000710502d5040402882102c80c280c0e5920b48811051112030116007010707 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 257266744 1250 257265494 257265523
    0xd090e041101050c03131d0403021f060b070605090708031312030306050d060902030712020102060a091112010e1603020607150608010204080c041b2312010b03041202 73
    0x2002080c0400c1295480404034803040c10400d01c2d1130340da0303020310b842d540082c10b6000c82d01e02d44000510181000140300c1031403c060001240c1c003070910380e0700a510742810310b1b20b555440b0090382c640001c2c102c0e144c12050051000c80304081c0c4c1d8010908203100a80822107040038144900f08000420100000449500c003180808505500f410080e0f1404108807002e4164201030301c031034020031207581e10140e540f0311610a00c0d0018003c0309600c14542403100551041d0000030b800110b84000d43d80200d04140d0000b0001d4001581c0e480d60302e4011041340c89110304c2074101d820100c0c0c0f0b14420368150300880d000c4200e441125180c01e01d0b418042c191031014000250007075810300c84100040e440204030540103004000108825480c2d22000d400c9801540c00040c0f60740c0088034441003401d281c0b0842d41c1c01c02c1c03d0412500c2041080002070b2001d88150502e0084401d400708400300c8404a00698402c0e0222244800e01942e40b516401203540042e1000d403224031051000c09041c90000802180e1010341 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 257267994 1250 257266744 257266769
    0x70806010e0a050a0213170f010203011a16061e06140607080306130e151f18090204050106170609010f120203030c030703020106230a03080711030a05030c0d09 70
    0x100b503500c001a100190102c140d65400740700210202090f5500300000d8840d01a20220340c43d4504a07691030501ca04070044510703481040180300c0d06440b01500322540b015200320640d00d04a216150580030f41100b40608100e01e070003100400300e08859507250a01d4080541802040d0319074044803021103054403000d0f80880c0c2044240300080c4104091540503c00a101c505080b9079803181c1ca0503500201480180b5805c001d094200300c590104920360400d180d48070200419407070310980310110300240543d5450340e00010008101d50700d01d070050f07030645074068014402d03543e44600240156490043c160b900e2a00b41c03000030214101064080e040381c0b030032503a188005103001001a161402454240c0e0940800c00c0b07000502e40b001c000030a880c0d4130a40c00040c0840ca06502181d035400500d40181800c41040f298103515600d68410700306076900545001c0d911001458040c4075204552100c5815004001e0400309004011001d0805060f0802c1a03442e03016088004a92030b104500414084130726 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 257269244 1250 257267994 257268001
    0x50d02030a020c210a05010507120515190f09020909090c0a090b360105120303010311011b0c030210051e030901060b0301180c080103080702010c020f0a060e03070806010e 75
    0x401002c00100403480300392850040b00c004c001d09003002c0f8141e10946080e034403507052100c0f05900483c03111691402d404100b00d01c0c107284102140050034407034034610408031080421440b601f00c0c003113000249591402c1008003656580c11002a400c04100140304101c4040000c80001002c660500c10343e200900307451807941000014030050031800038440e04000400f074400c0c90043d41c03491a140f05d200c480180c0c04000d803840b040b2030f005581600000e0051449442d26011010000700380e03410360f5800892a00f01400000040b583c64900c50000310002d09030741441c1007480b1600c0b8601d0f041d03134025030751900b110041d14420b84007482402c032603d21000c420f010010640050074060358005081c4d00010890564030034400e41c1c11341080e0401d204202c09480556102c0c07001d4031807200c415040d401c0c81d482646c5035407150f031000c1c06084000313414000300d40c00c000d0440da41d25410308009078004100c10480703a140c600c000d1440c403d00441a019104008010800355000961355040394540c2206003110359 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 257270494 1250 257269244 257269249
    0x70e0a0605030f130501060801150504050601021c111212040203010609050603070e0405030904061d0a05010f12110a092c0a030f0c020301140405060f0105060a20070e0103050d02030a020c 82
    0x284c01da031040d40c16550b18040401e030000700f8041d481907170040c4020070181605040422040f150041d209506551001c172068000c4440f9080d02342c1888500d0505496010701880d410b41000d142c2c1d04658104040002e01d9414003404d00e0200740500d000384d008114407070712185984203e800c10388007103a043d0b101d05002c104030486104500ea0291080d81940d0902c034000700460203a030500e401c50040d44084500e01c4401e813042d054203580c401d400e000c0074050307549800d846480a4000780500c0040242d1640d528041c0104503c002c2115000030344aa603090b540d608055000300429000080340101d060042c04001051206031600c11030101c014000f48000b0750350584690000e40355200902840644100140e036082c1308000300e89075040703024919441d0510b80f060034030300002c01d600081c28006005002645480041da4691220380c1002041781c0003600c10001e14441c5001c13070710080d01c80c00d40003250103c9142e0a02d81280e1050702122103802c0280c82c166101d0084031005401030740000304000310351 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 257271744 1250 257270494 257270521
    0xa020d020a030e0f180a14070201050c0403062316030c02150c131e150804031d030f060a1b0206150616120309110a06120e07080303070e0a0605030f 65
    0x49030010308202e8040803140c600c0d062103a04032486d0040c1a900c620040c0002901c1715241d1f4015410710081105140140300c1c0d41c1e072801280030103054555512488540c000410f584004001814041e0800074517203541d0045101081c0300c0100300017030401d6004d280407800040e48aa42c03442da45001c503266a22452400e07015008400c1d203441c003045c421800130380301081110081510404640c2c3c26a440c0c18040802030320f680c01d414450030801c00c501088042580301d90030000b07420402624a0000002038000ba00e041d040484905090060318280015000c2c56840002c0c21088611451101d550710b103c01d0b41c940608842581c0588be07400b40c2040d1600d488001800080c16180007080055a55100c486071803510041c0c190120741c3d079181c80c00074002c8903078461105e40021551035071282d04001005208401172454181540d81300c86440d00d2a4600788a8040500002000c50f600d9107021791004000c080100c0006026144a14010540b5071180080303074404e036141001d0020701d032585044100807 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 257272994 1250 257271744 257271769
    0x15040b07020712080406090515070201081f060201140606030405061914011503060906080c06030c0705061e0906100b09031609090b010f030b0f0a150b0a020d020a030e 73
    0x11030040c54800f14076560100c0c060402203000d0b50302d0948960400d01c01428247d4280c20241c4034894902c00c140000380005d0440341000d90a2a16202300e84844000d072003004082d030007124251285100102d109681540140d0a2042411501095441302e40c14004644410382e005032980e084100020800000340390110700c0399440610025410140140308044140d0030f070460311400042c0900721403090f0341806014003800d0049420041203103003540a5a64601e25840c05000ea40044009250344c01044142c0380a01d412505403a01882c00301514a000500703040c0440c82c52000e60080ba211100019819100724605151a00e815081582002c420703003205419075414451441d030f0b0420b01c1c1c03803404003a000742101c01000c65081c58030300d1300a0101c0c50580008218002d2100c1c00c00c046662940c0701a0042101c2e00342c0031441c1c980340342241c05070541001400100440341c100140d034440c0100102000d0000e582540c01048241c44220b0310f80c180b01c0e07000f400140520105078003600d4120034840ca03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 257274244 1250 257272994 257272997
    0x220b09030703120c022106090f100b010c02030f070503282a090b10030908040509040f06090312060630180606030302061f0b030601031404050d1115040b07 68
    0x3c0310135142d4005090004404c0c2c0f0392200030501550300103107900402c031440d08a00c1080140c400120500001c5035105c00e1176a0b55400e03240c030340e4100301c480c2e409011400002c0c0c1d0050242d0301c0c00d0381400d40041e600e00852088902078850480511551500e940301a404880184892000e40005465040052031000000b40c01c4080b0310b03201441145200c2e24081c0142017180300411024003203401c1000324030b810840310341030500b080140f00000e008041103c0a81d44121200d003500d48a07401c0011002379054402040e01c0c0c41e041c0078605041d000341c0c0d0090010301c0118140403660b280d1804540c0903203d08452444c650382480054480358505244031040103c00d4400141d18440480015200262001c2603590301c0d0303101001d00515505102d41c0364040403440005080041e000441e8100ea86203204860380004c020010034a2684a900102c94042c0078400c2600c26091604009c1c0d00ca09441800754085850300d003294455000105030301800e030801341c81e0251155a1600c89181081d40144000c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 257275494 1250 257274244 257274257
    0x108150f0f0402071208100303022805060a14011a120606091905150a0801060309170703080a2f032205030a03050f060a1e0308220b0903070312 63
    0x1074951101d20103045040d0244003a04c000c104001c8001c2c101001c00381c407000190a68042c1400465000180407c40014801c1054190803555800428541d0380960051140c09071405005d2a03501d60f4100114109064802c0801c0740d0ba501c804080ca00e50110100e0041d54050240200b5001d100c00c03150360100303018000510340204a40090f02e843e070101c501c0380007082d0a00e000e03c1a8200074500c499589a482c0c03189180160540d00079128110502c540030406489000510400440703000700c3c0005400d140415031103141e1841c0140c5440421281c4d140918900003010144060005035400440a618840742d20b00080e0400842540e04c01014a0b03e000d8090182e040ca9400015180300003d010307801650b02c1320814003004043d254094416064070182509000030341c1d4490494808035080d038401000607040d0080d03102d00c0102254009010300c2d03c081400320900c4810008091001c03215450f1004e2150bd440107014a0f002d20750340503401d82c2c042e40c02400042d20300c6980000302d007518240340e13 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 257276744 1250 257275494 257275519
    0x909020306150f040e0c030403090e1906060503180a08031f05090915151309051e0f010f1802040509030d0c0203041511150a02070503040b04050307050108150f 70
    0xc8403d50049480c0c50703031000b00041c104181c225065040c0e4020030f030009924590308107514010310b134004501484030103121580214200300f1401d840000480c1d550801071140035550040039049401c101e40140240c412903103003049a1a0100707201180036807201109003540c6031012180311008030038000081c6040d0900003c0341d140c1d1900c0196228030396400003004944084c20020740c080a0142c05d4490450485420b40003e0f5182d40c1100200554410000790000590420914003c8100c050b13640211140c2d451050140c070220312240021118030080c400c6002a8082c80e017181c90321103e9400d0074a1041ea08401403400360006a0406480341c01c980c00c1040b0b0304d84003021204805850b1000da440080d080045503a800f8041c0d0018a1303034208050081500c0f00455116050070b0140c0044400242c0001c1034039025a042d10800303034018040b070f91110b4588101303003101d6104e401010b00c00d1040c0100000d2541c454051148103004c1005600c0c60340d549001840b1840c414050061f90060904441 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 257277994 1250 257276744 257276779
    0x30706060b13050a03030f030903120c080708090c090408090406210b0f01060f0305041707150b030a08040b070302030d050411040f11070b06180408030f10060909020306 74
    0x40c00e01420707006440301e03030740c00c140e000011240c05183c0c0118007618201d03100300f000c2604030b5103100c80000c01c0c0c2004542d50119141c00c6520581103070040b1840da140c20310050540ba030040416114000780d403180107064544e1140b4940c0e031a000c100d9164820021000900015100e1018041c1c0ba400504045502e40c1c5070b044500341030001418444600c00c1c8103010105200b020001f1540080707071100640c0c2c8030350400d88010302075100410100181602d54020404104002065004480044c02c615450b4401807a20b10030304511416103804031410701c00d224410349000b24588021560020401e0324092500b00e1030f10f00c80d00a54070507400d601040c484c11102003420300445208a11070740015590200c03040c1004100c90a0351001907419281140d42c1b03181361302600899281540044c0030201c90740e0786400080304011005440c0185d05032110a0108000469010358003450204800c4500e594a806500c1000a41c0344102c80008581c003504200600c1d00e0783c011604804041c00d0100080400140d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 257279244 1250 257277994 257278001
    0xb03010b0c0c090105010c1b180c030e0705060306101403070f1205060604050d0f080a0c1a27240109060b0c0a08090d060603061a0103090309060e0102030706 69
    0x805420600001d1501030160140064240108201c032107003203c3d41003900091082d4034003940240414244440040b004c203007161300200a0040b0103514114112491004001c0c104280c0898003190512188032404900840c41d9025a14054561811940c40400300303c120056207500310284190200c07044254100780005510441310b5803a42ca08550380d0050050003c1020300b270300b0860a01d4181402119682c980c1141c04507041220f107010341d0b10751810f00c3c0180090100000717010800019906041d9600800811181e07802a01040b5007101031051440d1054400c40e42d44175015a4240410940442000c45003040c40a0500311841100000c2e078003062801c0722003042030071b501f411004204208690141c00d02414501080508040d440c040c0d56a803884510002010300402090300429500c07100da40c030344a150031403003c3c844c80e580ca040140003020b41c15140355101c0c040c4c4454201c01d50190080840d00396160740c80d040c81901c0c3c02005c5946001c4020740a0440c001004000c0100f82c4030300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 257280494 1250 257279244 257279249
    0x60306030c2b0c06080106020c0102070510020f030d06050a1a07060213030510060e07090803120606071b0509070f050703080402031e010b1002070b040b0f040f03050105090f01061512060b0301 84
    0x420340c04803d41031140103031a00c03205034004405c6521450001150780d9001c40c14004441007500e220692580300d820503818408900090070082c400801c200d4111040303a000041240d070306444909040c3d480d000036500d08840c810345c001038990b00300502800188268014020a82e075940c049081c0e0b0385964515050210b044491542c0f0740c2c98603401c1c0084145520001d400050b9410b06958547c54000e10648a000d540c0c007814100400d000000e0807a204c0d102100c55050740614040c500c600d15180c080100f003824003c40c0d01030110f20300018150390250000c01046142e98417507504001081d6011a5003440c01881282c06000754495850f0182094443e81f61018580c80003040c0e07141200c0510550141500280b403c5600c0031b0802c01c00800c4080480b0180c0e508200241e80d00e51140c4035200007031280358015214520400400400e01c130b8198442070207a81d80c40180c400b201c400d4841d45c5d080c0c0384031780199410441c03815241d10f4164000c07022050303c0c2444400c0414019a41c03441c2c04000d030000d9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 257281744 1250 257280494 257280503
    0x80d0605042a020c100302130e07020a0c080105040c0e0a0617030903060606070b0c0d02281701050a09090302010b060c0a050d0503090706121b1d060306030c2b 70
    0x103811041c1e165004409030601e1076803c2c03005080c140034803000a000261189145801d01d0350004081141104000984002d0544c0000c2103965040942000b9603d14080c10103540d80c26000a02148201c41030240350300031a0040e26101c41c0d6800e000c0398210401024045603240e6a407040c00141c8000940719210b100003118000e1a128220501410708101c0000c0800b4442c4408101000004107400142900301c03c107101401e0304c4000c002241c0e0300034031441e2909003040c02c50b4030003242d01406400e00481020082d50f9058990007110500545290782800b4003680b0142c810340038489590070b98800712804c0e009200100780000301c1d5001c20010b074081da1208a09400c03400d50501440001c000c0c41c0ca02c508240703070151440c50503048031926510b00c1d0140c6d00c1040524104401e080d130580c2c0100c140640c0000044d5900c1c80701400280629044c520b0103042540303803038058401c0b840e050094a11501c000780180482e07403135070310412078001100a00c2c110f90403004c44400b81c8600b0042090414140316 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 257282994 1250 257281744 257281781
    0x102070b150a05030c06030c070212030708041a03100911070b090f0706020604030c0f0201120c021b12060a0902180f010303020114090d081008030c06150a080604080d060504 76
    0x407428411004000e0304058007a40c80b242030800542c950f24102e0758401d1600c080185c54a00520004001c40e2402038118124400855100c1c00d00100c8001003003101c1140c10b070703502e6084403500000690300007150507407a81184103404105242003a0800303102c0c444070f1000149403282a0b80d0b24400c14500b6a0f04d2074080e0b0100c21113020090040000c4000751851340024a0146096900144020808000100741080c1140d0b80e2045901a50f507206200301440303424000e41103801002580ca510542c034800f0240d120105281542c1002203000e00d804070304c8030241410750b80d120085800341c00001e1049030040100045004044002d00c02e031406141007428a080f1940745007002420b40d6050303855142c0700442c00c0f05200610710005041103c9035400d0414061954413405030550960907a801000c0c0f5010002e4840d04104011407034034410282c051510410006240c24029216010f001c3c1010940c841004580490b2800300075202072503071903600bc03600e00e890300003140954040f034036454043e030b06 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 257284244 1250 257282994 257283031
    0x603040201030f15320604090903050904110a02060f0115030b2e02010b0a0b031909080c0106080708010c020d0813020d060b130506031207020402210405061501080703020c0102070b 79
    0x1500d6020171320b161100c04442040403040c4001400030b200301c0c8140742c0c44a070b60b07802c1c0d01c040500903419a510020002c104018140800c3e0704c940540d4446140075005000350700009115000040d03103241a504011741c4200040500c08046e001401c1c00d00b0010342c085821989002c0008581012440d50207900101225002480d200a401d444601d1000c0e44260122502880300c0c071114000c1c0c991160906130425132410801c0300180c0240340c1400060444800090000da5906054004c03504842c1440200c500a42d51100100d00306d80070442800d005800c10551103050b14481c0d4080d41e0031240321510025100d00f90360001d00300c819004030456046455021162007443c01c40030300e41d40c1c0c00b031074030701406a0300c1c10301c0c0003e490340d180032400c240707001c0003040c1e10066440c1c41d81503c1c070305083c207585000641011414141c3c040002c8400b11818424a800501c03049280c000782201603006031215a907980325000207601079000b1140100c065942802220046422407241d10b000d1040000c4101c83c503403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 257285494 1250 257284244 257284289
    0x1503050a0b1501020a0602030601030b0a0b03180127151416030207020906040c050d02071103060709080a0b1e070905040c090e0117010212090d0e0f0603040201030f15 73
    0x784000d149203558806601c1c15031481e42c0110340040841d034401d00040c1d42e96241401030300203082103d8026040b1206640215403400312100442c040d044035158582c8003015041100e090702c0324503019214007219a101c100c020580304442c0007031503104a600600b0562010044001c9407044000c104201140004ac40000c081e4030a1444120f00d00d45070035442c0c10081c1c0c003c40e1055501030122401540e03500b403189562441202642e20002045400f555502070700d0a03d80c055a031403400c01ca1183c01840040b07a0068000d400c1c0c03d00316100040900b03810b0a030764a84407410f003001821081d12032641950400c006c01c44082c0a0f03c1804551124100d003400d0000303110440c1c040410319000d10100381c1c2c0500a04000500031811102a1441c44082d6110f200b06180680141d0340003031150044c82c0203016a020307020451155100d40d9544082c6505c21207030800902e54402c00680e50060740400108004d544a608026940304034060040303813103081034000ca91000b103d580114030340b9015840740400e55 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 257286744 1250 257285494 257285513
    0x15050103020a050105090303070b09100614190f09020706020d020a0305090d03020406020c060c03070204051017070303050304140a021e0301060f060e190509070305040203102703031503050a 83
    0x204002e18045041c241006c000c07940d248500075020f00707010b8011001501e002c03030801440d0401b00d0004c0040c010583d903108071038405d046100d6558842d0710f84280b14010710200080f01012105041028903580340780c14490402540112020785800d6020810002c03802500d000400149040e980e000aa9280c1010385500b060540f0000c4010940100401c0120316800071301100d180604132411070f50341c3c1010001d14510321810340000c1d0410300380020001000d00c038500759400c40d00c0c6144080d004100080000c4d858002c94040140424402e002013800f08000c0070852003204103c004444060701103400040220002100944500468100c1c00c050303400c00b801418010a1f91104040249060100c080c10b601418020789000380e9041003022068110700c0c111500421000d000c12403036040015009018000448069020b8400c040c0503a04018142c421507083c41ea00401c04144a05004014944d4030428403003a420161aa08410218010804c50b03100941c450760050401801502e4620140d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 257287994 1250 257286744 257286749
    0xf02010b092811030604240303030204051005160320060411100905030d11100507030603020114160b09030903010608010525050f0a050c1603050f010606050d0e070315050103020a 78
    0x560f04041402881c0304003078056a0b080032040f2004142446803c0341165580c881c403500c10300c0c45501010000a0542590007403096070003d031001c2c0c0304d416142c0d800380d0b02c070700c240340319040c060082d1510000401e1155440c001d0b802514107805a0b00000086500e2800c00300f0303901034449100e44840d407005407424600310400c0d2001da04112408a01d0311000940342c030b0004685905101401410418211090285007803a44001c0f40c20051410b10f09170040092400b400100c0c0030071054041103844000c00000e44040d110705014401103245582e5074020750800c0a0456015031100b401094419039080c050440a008034100003e103501c0e10880c8401004001000e555007080041840e090766076200c0126915440d507071070590740d190f0380c60710115900d101e1034403001039902821200024525410b111181280d00810880392400060364295080303480c144119008200200304507070150b0466003000c08800304d0001550b8100d56640c4440000046142e0103100380f603903400040c41103141950100d0702 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 257289244 1250 257287994 257288071
    0x1501030b0303030604020c0f0a030206061003020f0306010c02120307050604020a0e010303120207051006061e1d1201020c0d080103062702040207110a080f0705040e07060f02010b09 79
    0x403008100380482d840340b00181c481e50242c0d0700007540250720740003001210040d8080c0d030100c07100d21105050094460400f580e0f05442244d20320300c80082e4900c24020368840c1d500c0309800515548600c4015207424940503001c03038005c8201d05600358543d00501c00760070140d0042c40135040b140b41501c1001103511494200c0d020510540c00140701007940a0401c285c100c180c1100165100e00b1420314514003920a2044174026051000200e0340c9035101542c511015282a0060540e1007022020f44040352601c0503101c4002d0440e218540501d09054103400065650000628140c0d1807070906044c4400070b005140464200f000400410030b07a881201804110301d00e488040380c07000015980844800c1002074452500450110284144003c1d842951130000f0a0008031a41e01c0c001e0300d44440341500c550b8414021000002450308003806120306003201900039000140c1001c0082d0f0700645584400800c643d40c55080310056119039105030b00603404d114100300d44d0500d840d50760f105015840300250 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 257290494 1250 257289244 257289251
    0x223c0e03070c050d08091e01030b01030902150913050f010f06081329071220030a0207050f01020319050a020a0815150304080702010f02030309071e05030114150103 72
    0x310714004038001c10b60f8801ca400800b03482d09818600c00780d0050301041a032240c1004145030951180c0d400385c260f8400c0a88041c4080f0340b0381001901103a00001002c0c0d0000740206141e8050030241004011485009041c81500c00180003040c04423034003140d194402041d010010310074040000003403070040c05036140a01440c60706042c0300001d211003020040031424000c10450072412010035000d00410f120007a08524035003110000e20403540f03100c203242d61034a020304440000c8030a05103a02e060b84d221103050b286840d4182d0700d000960211b441076401d0f00031403120034001130082c0000c50007a20342c030700c0d5203041c00081c0500034111000a40f241108500c1004441c5240c0d800001e040d5004c0d0022200b0a800382440c030124003e910350b51070649012400000700030070050032a0141401078001c1e640c00c2860542003000f07030383d244400d0301c2c0341d811684002c01c1006224030f045280c1c9102c0c0c0c5980c5044050a0351800441c0c213550551100000b1140020100160f070501101035144880b0240b0b0180b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 257291744 1250 257290494 257290507
    0x40506060720030708121204020a030f05070f120203150a0b0a0303080108011a1f26040c06020d140a0c0206030103050607030b040c1b02030c1203030108010b223c0e03 73
    0x20000303107e2550000685030300c042c0082c05659500d40d8072401190800b4805d802c01206251050f01c8515900480904000c0481d01041003600000b601c10034641c094000c1a2800361041c0c2c04000c040e0003055880c0c500c2d01e4051030f600781e841da10402001584030780c55407441c03941041c183d1801d40c0c070310801c00603c440015901030042e907110b0584070130309280705d0b001000040002c0c1c01201c0800c01c400c107019880c912041901a8a120070144c240715500504407000020f4440c50304a85500c440300704031300028000c400000403001040010801c0704000d050221144403d9408200305410903071041d0f840d07411082c1000b680075054042c4150300c42e0112000c01c521044410050903524000740c403102c92900080117401151420407840151520080c5400a5418030100d059a00e5009014540d20f40d4200f510400745803d106a800704c859146503104585070404014200040005da10101b0700d14400310194500355080c801104041000c0202001c40b03003039500e0081c0261542e150286503d82d1040114 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 257292994 1250 257291744 257291773
    0xd031109010e1003060b1303140a170d06090507111608030a0c110901081606030606090b0a1e090614030405060a0507021f02070303060501030e0606040506060720030708 74
    0x418038002c0480d2920818550342c0011002008035820504c0710301400a07440603e5010744100340101c81c46601203c02021320704441a80ba40384003d0014203144411900c100080d0481c8090500030341c003080d002840c0b564400f0100150303802550f12502245503200d058107500c4003880740c1305201848581d20a00c02d450310000035941d220740c081d8101041460101d90341004441c060428223940020840007055844520040d1203400303c1d50414240e00ba81040003134254000e00400c42121001e480b800b91081c501f001100c1c05a06c041c0b686e078200198070805080c0c0008070800d140d03603180b07141d660984090a010016212110701c8074100342d041c0302801000002100001c407240e120039502c0e004a450380350311006902d00383e1f032070b806886003003094409018511002e602038543d0a004c7e81e000d005080d511401502100c0c107802d460992608140001060ba0800b90049500040c0141102c0c2c07500504d41ca5210f83e0350031508404100640c44810030710307a451304102240140c00358070080c007800016500f2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 257294244 1250 257292994 257293007
    0x14070b060f190506090d0f14060f102304150503070503010b03031803240f0109090819090504110403020306010911032824061e050d06090e0d03110901 66
    0x20244504c00c002031035612a29800520786019a0000b1091030390205840c0009000b2184044444103119183c001903108071001e085900401c2c0074884130b80304030b0502ca80d070641031092607030740c0072244070303400c08002183c40724410305c10000300c140348480050b400c1500701824508507500140c420707070610f000c40d0303202d544c04401c07105100884418446c0c050b0111001c241050800e42d44420342c1100f110b42e10240e85002086031748201d0092901c01c200c0ea8880e1040740c00c0b1005210301418445e01840811144201425111941002d505240d40301c1d55441001034241ca00c0300a0211883c640400c081045007801c1207450301401c501d0390180162254100b0035401804024199407242d1039200700c1e0100c4079007101c2e610701c030300c203070107070144030042451160000300c4081d01da1080e0000400800003d040c0e02c80c00c0c80701c5180240142d211054040000d084549030041d40d4030b4000b840d96480001000d00c0e10b841440d001d100400d010741000d001e054000b0702100d01d15002e41a81c10401c110b411507a0b039103d90b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 257295494 1250 257294244 257294249
    0x10203040f0b13050301050112060506040c12050a060503030a030c03110f0702060706020f0307080601021b060f0d06090207030c0201021b030c040c0201140103030207170a110402090114070b060f19 86
    0x9503250345941d903040408890616a07407291742c15520309400442e010394501d00485034140502014400c540f202c00521045981d61200440000c03608100b40311000d03026041641c22107515440401c51544540001e13003554000b10802011030f82d542c042d0400c10382c2600424000e4880b1840150030445060300c010711512038994000c3c030409000405030108980c0782e040d10710918412031502d44a18003e030b03025104001c1540c1083c058810842d0080d14032a00024038000305501400312400c1c14004161010310303412074404614015120000895880c2561001c2e046c070902a0b620700038260624000641060200c810315121850b1702c00c1141095200000c04602c032420643c2e00085600004400f2401040c0c04489004001c5105000200780340e400549101a200c00302000e9040690b00d5403c03c0c3d03116010880142518003494100030300f40340507405424070300d0060621500c0d00f00d814417803403513650003d64102c4402d00c024007840000c1c208001007031542c0c1000e03155003058040c564099035071803402c0e1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 257296744 1250 257295494 257295509
    0x306130e0d050c0703053a020a0b070309021302030a1d030405060706060b0c0d30090503070812071d03060a0c12020d06031727041409030c0c010203040f 67
    0xc41c0c00d41a1420841d0200840d0044241c1c4c81c50303035598181075841d14501a007000681290340422012007e84c880890000a964009100000c902c2c0c3c0d4410030700000404082c1410740d0b503480c09000d61035000316440181c140a500507940d2407d011890121008a203175040100201a00103250800001c1102c00341e61041322001c1c1c580342c039842c010000d040d05802411140c080800c0e80500b42d100001d020b040255103855000c440c65004190120340f00b828106c591030f0902d03140d0a10034842c0070303900142c0601d01503020740e4a4810203468840460f880020102610703041d100401c446143d002100103901c12403002400c664107020030010ba514800171b00300d987c3e2a070740c601038203a4071030060100c4d501c64880000c040d502d0f800001c0152004103158401914a0316061040309240400302d021198095041004102c080d0300b00700c0c0507a9600d0700300d2034444c0c0141e40c49101d64505480f6580301840307424a20021030f03441228084550802c0a4081c100313066500c00c0c4824811b05460300d0040c020390340c11 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 257297994 1250 257296744 257296747
    0xa06050714211c090f05010b150f07140d020d110a02010504030305090409061b0315050d170d0f050103021c0c120305091201091a04020a030f02030a020a08030306130e0d05 75
    0xb060b50f582903071a03070343d10800425403400c3c8140041003029100c100c1036500801c02041954050001c4c400c03284a02c1e0783c400650041000f03c0b14004142402811546005510324080e45070000c0d0118504a0703800c514501680c442454240b5042c2d0240e20782c0c80300d05e100c00180a01c1c1a956001070031038040d1340402070a10002140d8505c1540b603603444180e216030440d07414801c000342d6686014400310840140000203090902c0da03403065881405003012034902914003a241b0300385480b00c01c070020114007000d8420100b00301480401007035015098603000107060000c1c45514500c1080a19201d469800400704135510200010801004081049401c0003ca14402c49070615040b55280301b04425103a0154440500d2501d0090550040802500c40c0d200d24109e80d00300c6083c018084800c0380e000b03603c070800b103c06000040d80c4542c18100e1510107400ca40310071101e030780014240000b540100340d075a8004420404d003843c081c1644940e0310304140040001400342c103441502c8024031084c1c541406070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 257299244 1250 257297994 257298007
    0x30a030c0e03060a0507030c05090f040504050a0c150f020c01020d1817010f06120507090b0a0b1c0f091a0c040b0a03051501170a050a02090a0605071421 67
    0x41d440415001c000101518101c1ca456460030000b000140d03840c03000646414600381585000700300b1103a00e141c009020154a0704420300f00b0010b000b000700b00312100d000c0d910720b03c00002c0081d610785002d0b24494516070140e480305c400007000c120368000c014045620040490719141d130081020a010b0a0515109401e11225407200402e44416800310010441508518010b140d065004a202d84881c0d001840a160f50701c030220b07081c800484c03000d041c540100e28100082d40c107603440180b0424001c3c0503628615034850844895402080390381802c0d0340c1005090258181ca84110029280125001c004048103501c49040100b0304c0c021140c0d20302c4c80b400100c1c030010100426200201040c04038103540d880c9602c00100640020b40301021011141c40b1044c0041d07004059000e80c0985140940c049580d520446001429025003803041c49035080040c181c4544070046c602000d05510340300d007591b5030b541e032a02d09406402400081015003040603061520504280c50381c400b134402e100800d0300c520 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 257300494 1250 257299244 257299247
    0x301061713230f03120f0c030603070e1314060703050745060f111b280f031106030c091302090a140909070b0d0c0302040504020d06030b0a0e030a030c 66
    0x100c860f8480b501d00c400303d1004044818181854801d1005450200700b0b9183c0d1030045105000c2660341c582c2c150040032060203445144a41700740c1c40309000d01204c2a22941d0340741d42c60704c2900e030a400702140d0084400c000d0310a4150041580245040c6403182d40314088117041659039402100c540000408003801e50a1b00321404400e072401808603200320320140c0d84060141c00f01b213190f680e0300085030001101251801022502030741a00c291100a0300c049070207030800c02c0551303030440402c4070440c03443c60a902c0740a400240c0005821030f0405d04090038150308094032210f5608101c01d10410040041003404034640c0c06507070782000240d41688002d06940e2845002e40905a1419048502c8140019480910f5103555201c00419030341d101c82c98a80031420b540781c20903801101c175000300821039038010803240e82c80b11b409244149001800c0030b0f1114001400e981c01039600c507646584403a020b00074800603020f6540c0185500c60100010440c91108546034041c1a184500385541c0d000301100301c9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 257301744 1250 257300494 257300503
    0x7021b04020d02040801090201081308070b040f050d02030901021015120f1403040e07050705070e060604090509030d06050102031305090c0408060f0f0601140304081b03030106171323 80
    0x10007010b9055446070703121001c46000307202d0400b00742e0018a460012950f59420301134440100f0b0f030460003140c40c040c019110400e0302c50b000b90044a040c0160941000460428800698074140c207502569540d0312070000246000f54048441e81110301d002d452200719012030900b24101d0385101200c500c01841c1c1d04000c1c2d5003040401005d40305541c81e00c645100c4101c08401071007960079510b24140c590b2a603110448460003041c01c02080e80e031110300c00380101c204c1480c683e40e20100040a0500d800e031110034007804d0741c0c020307030340c61030564000f00f0003200600d181c3c05044d014020a01c0114101005a0851003186a191190b103006000601c0403510174680242120042e0081104607441c50911007415a0710010841d43c84210003800d81c00b19082d0761103507032603100c844800d05c0180c0c11034540d80c40c0c02c0c1c841e0b40214040388540f80261121350700d1200a01c0614000d0200c1d031280b6452007034420782c2285000009200340c0d946038081005a002504842c1040050a590200440b0341ca0781c02c8401d6103003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 257302994 1250 257301744 257301757
    0x60e0d021e010617070612111215120f060a1b0804020102100504080a0801270b04060f06080a0c02010212010308070c0302060f09040b0609060730050c0f0607021b0402 73
    0x11004c88007680003c40703400602a011280f899503030b00c49015560480c0400c032284c440d041d651049040248042000d0759818403500310b07a4401c0c01c0d1440103a040300080c10056040e0102c44180c1001c11904144281803241c15405100303c0c40600c80a022000058040954414458140400c000100d404e59108004a5140c01c1007107a080026007094282849960401d242020018161000102c0c0c642c0c20300c644110044810100c20703e5030640d1030403510262455010864200f55188000258884480c480d0720041c5001e840c0d490841c105060b03a1004d980720070004c00c00791b80c01044581e107595111600b030f0303044a400440a68030b038401c61a1006040b0300700c0d400a907000b0800f05002049040143c01010384600488080111124a2007485900d000c0d4110741c3d0352042090100d00f010410f0401246074943c28150f40c07860f0146072400c55469030340001c81c00f00c0002c1c0003240410729507e0410418504881c3c450085c8564031707140200075601c20940c044c1100e407102e1110004050740302c40d01640c05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 257304244 1250 257302994 257303009
    0x403120c0210110d1403010909150c031d0706080c1c05071107080610032a06031d1c030c050f1b010c080f0604050c090301020d0603060e0d021e0106 65
    0x446203240d8000400302c91a0600303103c668000c41050811880c003d1080c1440304c48090952070030740e1700c1c101d002001800c6c0004c0590315428500c244c180c1c559414814403580a0b402e071000110944030206103a041001010300d09a251300c00142071001d540c000403003a5202d01003003041135a070100700c1000304034400398540c2c3c1c6541c2c504203410300c46c4442d041080341411100300320443e664607664245172a44c615058441c031100708031b05607052010410102e181c0940d40e2100d03d03000c81d0b0550726040c00082215a51100d000240e603892000d031030140c0f81c1c18501200f41c0fd14020600351400c03460b4451136124a880610a255503032140c0480c1500400556058841170521240c40301401380c0810a94002c0c01407039640c552820610110440c01b40007210f01820070312001c4640d6a0315a000e00c00200710140256440500a0010ba138a59400740010715100381c0120021032814a546007250960f41c8854103400c0726080903c4151445500181815500d004880216080e20760804001d00502e01d5800822 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 257305494 1250 257304244 257304259
    0x92904110409081c060e10030309050904080c120a0e0409030807030c03060f26030a0c03030e10050c0712020d0509010806040902090414060703020403080702040b032b1704080403120c02 81
    0x200042d1155111000300c4403039280d51503a0740d0303aa014100380182923000060102cac143c643c090246052109111354007500c00e1070a103181c09000f1086905d000b00c1003002d82c2043c000040d03240022a0f201c00140304102050390188420151a0b50141c0281d40040900e41015602c00c3e02e4080c080c440c1d0411001441070500b9440c2c007540312022500628000d01008494124080462002c8800001100d10030311083d61126142440c2d507030200c0c09800004c1c1c10b62814810601c00059000e040e00c11180695158545203503074603130328900740a00040e181000400e54002004210311a500a41120010318003481c082c01c1a83e12500020020240104007941012481d0100030401030701d4140112407140c103400312201e03603891200880a0f4070482c00010440a0184000c0005040681000340600ca0040030388030000028603107000401d680060181183ca02051181191904155103101c1b1071001101c1c0392292920780c4030407016104a2100601440d003200042e40c00d14030803031003441259801880103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 257306744 1250 257305494 257305537
    0x1f0507030e0405151f0e15040e0115030c090503030d09020a03080c01020a09080a050717010e0109062f030c0a0507050307062703020a1b0909290411040908 68
    0x518039030222260a601615801032034052211070f11740c41c4000c400c002d9603000b910401c01400d10030355118800105255540910001c10704070030b01700c41c442c00b8100b94901000c40d0346a800d070040640d40002410024010b40c01030501c020344011048032440c1c01c41500110b02c051541c404982c240c44281d002030440c55020441d450061010f40080c003244807030b643c810b012161280b10040d26000c040e100101b082d4401c2c0000c000108180c81580c0d6101d015200004161103029280b43c01c1d140600e108032003403a03891000789051468000c40c0754511400c5140221240383d80981c0b07084510000d40f030120400390118a041d9410320a404540074503602c50252605d035006071030900082c102181a40000103100c21100b40311504010341e9444441d05940280007180403519001c03104000c00210407100100fa40001c925011140101e002c0c8600c80e011162001320902c60951100300700034400503411058600344404104440038851310703400304580c009a100b020f4600354200d486203d02c201e207030011300f1011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 257307994 1250 257306744 257306761
    0xc151905090c091806060108040309120c09110c03180409080409060509010e071d0a0b21070504080a1e0b0103050d0f0503190905030d1103070e1f0507030e0405 70
    0xb040324035442601c04000d03c1e2038130134228508850400380c00000d80e00c41000a0610342c1304901e0b040c2c011b400b0b41030001c205900c41180c6c030038001c102c040c19108285140303030810014400b0b02c15481d051006807030050800030107420031503c920491070b0044803071414140000041c1d849a03c510001644890700d556a00e640b1034030000079110620665101e419160000140c1c01d4032074400310711800c90340d900c0745113022403032802d5004120203c1410b9080100f40c82d000c61441c03015402041c1080e68040c0a1458403101d2008100e0342c00010300c0001000350a0108205d03000001418200300f90b405038099241070940050611031444d070300009481181aa0000000c0c00804128428100b046070340701e000c10541c1240544e02880203030b4618041071300d600f08c1e101c0300c185540e05c1140b017030784940c040e240380c200119107400a4070f0007205007400b609000000e0000c800d411030704c210b90545058034240318492101503180c0b43c10440781c03400030501100184880070548a2202c03407802c001c00130030811450070070154 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 257309244 1250 257307994 257308003
    0x61d040302010e0c01051219062d050a0506031801062612041a1c020a0807020f0601090507020c0a061e1b062d1407050c15190509 57
    0x5003500503501c0e003c803559808402140d2007040840685485280c800810502007012a00034409410000a0820300560398541c0c02060010444c0e40002d2600741c85070941c00d001104d4030801003079003010840c01080070b0f0321208140b00c112a030480d14140c84c2c0e955107034003081e101c030b90002a00c542d510341580803854402081c880603c45d03c0401003140600309100005030780e50359100c040a4001c2c070030305c0304024280800808400e5400b105090a003002c1d00700b00380781c100d01d903800d09007601d080d00401ca48058950017641194005010f04c02441d44c10000e200c403940f60741060090581c0b4507112400110007500800c069400a00d01409000078280d40e00b9000f0218200003000d11141c0e290820036810040c41281103403140c1c7c0c44040d003640044440d03554840140754a6088070020b05500707014110075031429032124254a040030002c207843e6404490380d680140000c0101007403007014400d48400e410009107900800d02580e07004101c9450780807078180000070029048190301e09180c108a0704185c04903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 257310494 1250 257309244 257309251
    0x11010c0519050306030a060e0309030106090212070903030804030e0406080d090e0106180905150904080a030f0504150b0f030a03020309030705120a030e040209060c010b100305130f06061d 82
    0x8840030300c1da203000894aa100941c0d900e40d1581c00480310001184c40c0f684810502203200c0200ca1400d00708501007400e5600b250320030000c42c0e40c00700e14004240c014500b040c2e07100c0c0103450034109a07425554054a040030180010f010495000c0d001081a112035012802515801c01190300030080184020809015070180200403e402d2000051050058101c9a04045070600c1c6924840c100f5074141c0060800806c04142e4a90b40741d1104c50319103c035200c9a0045000700d160903500d4494403005410b480500305401d10641c43e0104000101c0d400980c3d44c2156110303880f020804169003000600c80c01e9044104945c540103c4648108060300007000700301d548025415602029610401c010b1039880d84000016290444000d00300000e20811003144030324001080182003103040b801140445d008607203144031580d51400c8204c041d01d45003541d940e0941d0b0701d103010300580c41c00b07107050340d0303101c1524100801c1e0780e00701c0800000b002429081480a8407d50500404040c24090600e9085a040c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 257311744 1250 257310494 257310517
    0x80a1e020d03141308061f060c03081f030f0c060c080904020d060b0309010b0f1008190615030203070215010f120201110102191103040e0f04021c050705040605092511010c05 76
    0xb03920600f1f012000480d410704440c1c0c1d1b13460751400b0410342d440c00e40d03d4032030041581f1751805400c02141031014a1101c1800036501411100e0440a071924284c4039031580380e00003905005d520240c0c20001620413040303454a40b810354015889194280c20000986060b421000d44003070080f0400900c0e10056000041505d411154120010380e00c2d07080c032220f00c180aa425000803100b0000a0740708407240f030641114429042c00245950b5292501c2c140c40c2c240064000002e5000014071000d103504000e44401c1140e01d00b614007884d45044400401d0301e01c03034071841c3c820b00190300494095a01481100c500c154184000b903607550b841d0354000b018544c0c4000201c0114007400100b0301071810002c01e54081c0da544940b80300c005c0d210881c00e1041c2c4134004008a034048004070000700d04c80c440c5401c3c10349203403140e4001e0250b14100003c00041d074126401c458090200c107800c0041c1c1d80d0880c248801d00f00402c0040c20001c40808408440000b05032400041940c2089902c2c40101c0d40200104170801d0744 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 257312994 1250 257311744 257311771
    0x3100b030706030207082208030d05040308070e03100e01060b0304050c030616080406090f0510290105030109050c04051002030a0f080f160216080a1e020d0314130806 73
    0x481805800300e021700701000d04180e038148440c581d0500d040c0c81003c0c1c04040d02c40704800007071f0348902c020b21315070112131038410746502d41c002d02c020950006d61607a0000481d0801030074203682c0b1004640e42e440b50300071011013542c4411b400100b965007076000201401d28410215540d103000d00303181d03642c5c2c0d01400c030300d81c003074030071000020304403001c40125580c07015180c0c0c1c41b400c1c10341321034070703500c01821960105071143c01100a0b54070000d8801c0059000c8251040c0c1d01181200010701c4140d40b50050300490b840e80c0044c2564850668ad004040324151480e5040c001100c6d1038148400c60787c0d02642d040250860862095076060a80010140114804517034942410340341c0800c04807404001500d00e0303d1090700d2440400c08903048050200d94a00003841140c9540d481c038541c05942e20001c0c0c2c0103010640151900106004070642c09500c88155003240381c10704041540416011843d1900240410080c0281c5241405c4a0301c202d503416078151180381188c2e52038074401c545804040d507012910184 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 257314244 1250 257312994 257312999
    0x30a06150e0f16030f0c0e01020d090501022503080403150b04020f0f091203041d0105040507170408040b070b060118050604140f0910050111120a030e0c03100b0307 72
    0x2074245980e1040c0c10781c0402280036110242c1d11188442e61244010a150b1148001c80703600c501c0744514140c3d001d0a0b5600d1880410140000e814940d84240724010030000f803000b481745036000150301d08003c1c5049450424620f11144940000300203801c0280b01c03a000080c00000c2c84009041182044c4420748200203007182c20003000203d2103603200e904064001848001032181b0440080e00606001510280e6034100040c0c840d425984160840b08045c1ca0880305e00210070001c2d5049800b400090700c0070015410100c44c00f81c105580300c800074240c2240440003070208036004003a14003c0004251076a20707404246070807681044201d0360746001480d170076105800c0140c8400358804032640909000c0c6040e08105035001c5610001c40d119422200000101d0001c2d12140c11840c0b042e4025103242280302d0500000412805c0c0034001e15000340e2085900c8001d0a0380d40341240c1c04aa020308001820310070740e64405003465034080d04030398036015182c85d05404003100d0b004044112000c0702618600364 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 257315494 1250 257314244 257314259
    0x61c12111e0a0204180f0b15010e0916050d0213140d020a03020108070e030604080301090b01050a0801050d020d06020c0d020d0504030b0105060733050709050924030a0615 75
    0x5681d108240d100754011100d000c05403d081e8001c4001032207070214140800d030262207401c2c402032202000c55100381402c0401043c0c10000c503980d031101074246013084080b005400000c1c04848050030f0f140074185007152180703541d23002e2400c807040116020003d41d283c00c0202c01c50104606a403144003400c40c40c0361024259841c000444080c02175004081018150075a00110781000000304214242301b04510100807d035010484140318504c05c20600c0d54947c1001102020b44001c0d074940c0c0c1c18443d0910a850101c0d4100620a0541e581030b0b5a10080d6149030001401c45c0b40c0a0f0009840e1078400580c40e410001c011801c03c201d403850303400301c400fa4507130814111803500c00c500c805490009820010310180c80c201004200c0c0600800b50102003000d80380001c02000746000311500114941d580e00d0400c4251070086c16400780c582d04000061602c6e1030046071a00100a00f021952045490714881c0442043d26203081e09601034100e441140280c90000c2c010001c1e00304500350401c0c0e400c070006694 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 257316744 1250 257315494 257315533
    0x14030702030607050a0c11150408070801060e0f07030902011407031d09070905040504050c030d050315031504080918100602010f1b1209060c0806180c03061c1211 71
    0x5d41c441c1e85440e600e40039070712100c00c02c410891029500811020341c0118080844000d4005062518041c0000620b0a038210303003101c005910a905083c1d0100030004004003d421041c1e0155150401007880d0a07a440103c2e441c0d54000710807140100c01003170000600d035004a1070070344d044841e90407a21074280c007800c0115034041150180d00150200324284003a04282e041180c10038403800c05c42c0c01b40301040e000281040d00c500c48100001d0800300812919803607062140007040340a6002d00843c80c6c1b4503440901c40c1030003e2026004540000f40002c80340c403065511805801003121b002c41600f418100e03120f690701c03248640c00041d030900008510605451055090b5000f50f03078060202404041c034155854404161007941503561034075090003040d42409408000340040d552100585040030411000318610710b1804070518580c400c1090034400c040071290400012603035090641c40942003540001041070b4002c024401c41888a890f040d0401c07144c4d00d030700a09400b5900d01c01007021044069 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 257317994 1250 257316744 257316757
    0x140f0906060121200c01020306130b060406050a2706030c0e30030f0a0306080c1e03031c09050f0d050409050403030b1f0201060503030702090103140a1403070203060705 74
    0x2c5550088501d8840c1d03101e0351000782c8040c038094000d0085124141412480c5d000110040c0460f5000010000b0303e14203c003601c220100310794000c002c0100c100c00440c600b40030314010402444000151181950b00030410205a624000036240d5040701c5a030303135905400214490040840c0c100101a0071482c010600442500f001518031805440c42214121601603c1c40c2402402c1c07608000c203034090201440182200041e00c00407a1381c1d151030b00d0000b002c6401c1075001c00100d4201c02d041030781d035987d4080d240300760107420510220100c0c0080e002a0940c8600c401e181ca181c80589906d41c04a402c641014248601a0066944040340404900d45903080c00101000144042009001ea000c241d40105e801602a290000302d12141e00d0224000040d861161000030205030315280f0021360901415002c0c0100340c000e942018030035030204071401c006010060040c00703000039240c1401010070100c040c0c80e03008101a940081c1c070362226600d980c0400f505a00034020b030800144820f00420840e0740 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 257319244 1250 257317994 257318027
    0x60308030c090f0901060305090606060c1e0705040609091403040e01030b0901060e070e09160f030915020301030c09060504020301060e060c12040b0c0105010e0105180901140f09060601 81
    0x2550792854408491a03100500c0c01d68070550f000399124460f151141d445010300f41c81c0d00c0000b0f10782403001c102480e10b2002800c541c46660308008812417841e02203041c44140010703c2004000002c503a40603410504c0c2504003a4015150890004180c1066040920894020203101c031001c600c07410710320784900c01e45c0904424108520010400180e0340c05003103034042007100c0002400c54460584103900c020540b00800001c1c1c0344a42c580041c40d068000c0e170f0300900e5030f00128201c0d21a104002d4030f8015055620014107689c0c15481041c052001c40340341044072540c2003103641c1c0da12880e228412000c14000d02804c203180c26030201e0301d804c040c0b0880b41600e0407a21900921200d0340100700040c0d0100280d4911800f0340740c540d07a02034460768050705c05419525002911807420007541d60131604140d2200c1c401c8031043c001003280b5191490038015040311140c05200650314542800d014049059101c3c882240907801c100820310718001142c042d0820100390740a0351108001199100c810200680 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 257320494 1250 257319244 257319247
    0x10080304060c0f060c2601050330040806090f06060906040f200901020c0d020d0201032307090509070c0309170f030d020904061a04030605062d040f060308 68
    0x401c2d028521120001d4400d541e0901200202e9582100351282124030901003a59190041000c8104000c4921001e4280311000025031524000907520f048400d4111148100603042d1030140d8010081e4880146244501c159165555501c1cbc41d55041d0444210310700b800351038000d400100d80814944e020b13102c0106904055111901040010f001c26841d58140a076519407402030ba0240030180210361509801381a1030300c080d4400a41000390790010701c0d2040302c045540c200140c2d1000c0341410104d4081c0ba00242041c03030b50303148025031401883ca0594900c1e4030300030010346c076602c04c144a06135041540c0c4070907252540c6009907000c0c001d04100402068110b00140708005c1c101000d114540006002c441341300076100d000d141143d1094000b40e03402c54001039202c08600341800b4903c0105032500140c42d0485580d105a00d0b98040ea0000038000d82e11400400d01070b17a201068641028405428400780d06066280c260710180020300c81402181468101e60010119110f00002c82c0d070003070300c0d06 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 257321744 1250 257320494 257320499
    0x1e150f052a0a14010e0303131a340206071101060b21060d020315040303061802030f09030306060a050c03040b0c0307030e06130611070509090106090510080304 70
    0x180c91541115100011400c1d01d440c103003820700280030718048203040c000050448800d5a06101590707845040ba0f00903140e06007054400c1d00360002080760780c4a69400300c07103041c012092500c0f60980242d04426003180103080305220702c11100061402d240314040c4805072050140e094850030411301d2048040158000000140d402401004074019030900500000746036600c0b01d01440c02d40c2c01400c40c102141a405d4030442031a400a6078690704031320120344869184c4031960000b5942c0d606126840341d400344030720103d41054040c0e00107601814611f010000c1c40e00800100030300942003141e070326561071446d00100761032543c0882141e01604001c1c09003454100c0c0e254080e185c640c0484140702452000b000700203441203016024050318148000515550103281c10000c0410441e906410310401040015640740700e24410b0440440c0d01a090906043e6000d0900350700700340c82c641c0019001001002041800b84040d44103509030341072143c0412658441e02d101481d04500c86c001d40002d0b500c02c1109 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 257322994 1250 257321744 257321747
    0x1060507050a0818041413081303021f1205040305090d170304081e04051f0201020d0903020f150412050f070f0602130e041709030c0a1e150f 62
    0x1010318900500c11100005200c0d680c64981381d001c40c03a80204a6108a500c161600d018000d00d01142d5002034141d4003400c0c803840f104018102124010104c2c6400079611301d0304443c40c1000401075400411700c48010165441d8400000c51400d02140003e01390407110900c958103200d0340b0701503905559414203140401d414048000705444040d500f41009482035030719055600b004500c1144601061074649a5086c20018038000c203540b55419440180b1040c4000e848507d21280c0d0300040305800703210740b00d008005038020711421b80045841820802404145900002d0741c0c081411940c003120948458101c044881223000e4900a000764203848140a1540c17040f0040c0000c449602c2d0172628042d00d56585030600440b207201103c0390358010412500b00100c0309501001014081c205c01c0d11807510f81c0d21030144401d18031000ca44008041500449503d0820512100a001401070680581c80c0d05c8010104050f080e001c3c0c682c40110700c400318000c3c11980000c07111240548401c2000c0c032403d0380 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 257324244 1250 257322994 257322997
    0x9050d030807140c0604050d02010501061d0f0402090306070c0b0601020c01140702031608060403020601090e1507030204050d0f0204060b090a1502030f0d0c08060a0f060302090d0203030f1b0a0209010605 89
    0x6504200c00c030078040340f04d9403202806024002da100d00001d03c440c100a8001a080d950160310840a009501c105150030400f81010030707090700c00c1190354250038844c4000240082c084c10b0000c1d034040c41850308015a15402c80b5041d40b00c0e80c01850400f05590b201c07401241d81e800e1048240303000a8030040309041803046a806040344920003415511000101590744406140c2d580c4020020390110046c4000c4c10b40501595001d48001d0b9018086c1d501d60480c200d50b18030050452540c41507061000a46c458031960596010b081d00600b01a03101146007050101142c4c40c1c01d050f032007507151800020740c80308154200c400c20303500500078440d040d1402d0804070380c41c282c40d100c0c0700641c003040061481180d12400100322280c070b0a600040c4014030860b0050060744024030071400f4240c407050601c412049207504004450240c5805031b40c07400a00045403406843c0c0500a40510010401c07458440c0035002510404800180c1d2907150300903c0d44059403112003041c041d410001510041c40603038070a40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 257325494 1250 257324244 257324267
    0x60f0d0f050d0807033605010b120d09090b22091707060b0d170d11070308090d050301051e030a0209011e080f0d030b18010e040309050d030807 63
    0x2110201140c6180d11914102101c004401c80011454810130801c2501845807045424058815902c0d040341c0030420315100680b8811071000120408050080001c2500f01d82613a000142600d81c000000c04007880d65250038001c002e02060182d040410080240d206080b1080e200415070302c85080040c288000c00580880c0d640019501c500700b40001c5000085e19503104000060b02d20313900c0034203090800031a40f4900e440c501c94200345030000c000c1201189016040003000c0b070869502c40c411981030004204102c820340700001c01003003610a05800021180c82500814260f030305003c05040201c9452000b4026103921000d4204001d200b00c1a00c1d0180c10b2440010302120348072496600040c0006200740d02c0980140b01c6c403000b44a010910320101e000410741c400c01000c9180c1d00c001c0c0d00f51034840e040440030030035940e0390508110790b86403060b00c102e80488214800301c1d961585080c540d400422034003940414540b100010705400d101c1040031179203805035240d00f259150824103c90624810 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 257326744 1250 257325494 257325503
    0x40c110d1b0501090b04060f021602040b0a081510050919090201202b082202100e0907052706210f09060106020a030f0212042c060f0d 59
    0x5195100028109100c2c00d144940101c50174442840c10313203040015503201850881407940140300914010f061080001301d1207504807000f107410b000b9400401c0e100238650703220402c288184180901002e10043c0418000c000d1508084001921401072048859050301c45a180000480c508040746403141c0c00101c400c1d00c149030141d55010007482c54800032980081c1103078560403260100306040001034849410700f1700c114059950910a480103407503000c000b1710481780480d074082101803e0b403030007401503a20390707001340400c030848240c0340002e201d00c0000300c2050044801c0c001080b52a4002c0302031f204254010000c030320901c03072404005070f01480382e0011241c104130284803200c101101150400c00004500110251900d0940c3d4280d6140070080c00ea804030f50050401442119408503640100507058107011501600544040f880c02a00305030380d8503820008500400e107005a40344050311072410000810a9840c09e605d810320410058620030b0344090012030700c405c28201501c0c59203186005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 257327994 1250 257326744 257326787
    0xd0f0902091315021c050919020f03010204031407140105070b04030e0109030804082109030a03050a02030f0703320a030c050702151b0303161215080c040c110d 70
    0x403c80d045060741c2209102251010b0054010010340256103d034603884503d100042c0840b104e03041103003101c14141034010f4003030030402036110615242501120015980085105607801d44c0708801500c40c4414024040c0c3c01d0f00b0061404070039881102500c0100740c004400300a191110395003550a40d0810b17403914140010a0350020101d410180904018480e0718060082025840c0080e51582c9511405441c201400e2021003101e4034001298240b699040c00d1a0fa0390302d010200613840c43c0900c030f20849072001d000454030105503201102c903103a005a810302108010040b002c0354089041003503811203540381407203070b40c0b1f409100c3c0c0c2012103000002d003095442e19040d038001c1091007601782005000b18030001216014184560000c41d1003424050103182141007a051005501c00d840234603000f0841c0080c18541144141d601407045100b401c4100408242c0d81c15a031754440b0b4026080c14130441c0b8240c20a003085006030390301c0c80c40b044850b001c0e2480442c803c0058a82c401200e1402400c0c504 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 257329244 1250 257327994 257328023
    0x6060906030a0b01030b011e1508040305120103051501231009051305060a050307060e0d0218040c031103010903081303020f070806060f1002030a141c020d0f09020913 73
    0x3103a86204d003e98040d0f40096031035818040b103000600d01640540c002d00b1814081003008201a8144640111091030910502c0d220340c1002c903282e014401003074048040400002003000f80008a1184415009481e42c02a81c0d940114074820104e4144001542010b0854240c9500c0d103803031182c1518246040200200740c4030700100c0c580700c03c00100c00310469650024040070340b41c82c5103200010f010450060004c00d091a40040c43e025103850914041d50240c24400210740e10b22442c000940200d184049a5203094100146211001d10041d41e0f45040b050101200b0700741800381e00b1181e90503803100119511041c021520444002c141a41103008602d0340102e100402d02210000300030b83c500512b5281407060410a100f03107442696849038160624120712240c01009448102c95076060103038100c00200070410b402d109603c1c40349001004021031014860880d40a003040d42c80d4602c04110501c001803a8504881880802079071140091740061000e6040e81d001c40351407407103444201c18072403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 257330494 1250 257329244 257329253
    0x308070b0a061e03060612020d122001020a0e04051e061201022b02040608010605091206010b041e12080c070f03030903030f021f180c0303030203090d1106060906030a 73
    0xc0001000a9422480e404204180700190040c41d000c0c0044070340003c01a4610b600103049c451038a80002c0c495803490086104048c052200d8880c49030500c0000c5500401c0200440c0c000d43c440640340c4041550140c00c000b00e404c20340300f001d02c1044c00820700c800449030035810b60850380e401010b2543c40182e82c007001e0301803002030001d008081c00f40c0780140f48800e4526011a9100032030308103181d6030780c814041080587d81c03180c101e504441490920301e0340d502c44040424100c00081c808a1814807603c0d0002074400c0c01800140219520744170b0992122084c006014801229842444c68501c0e23155010b00114070064000c04540280b1002c0b2511165101d49100810b00039a000350041070714060100f0605811050004003951103101404001094510031550f003503440356600c4001da601c82c5500154581c103650328411640000740e90642903501c1c90010040e44c000c480200450060348100f17682c16000f0701d01d48581201d80c0c000b5003040e0351400203001030b0b2400280703803950502c5080303008070110703 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 257331744 1250 257330494 257330519
    0x501020c040e0c130b090a050c030127050c03190603050c0f0a080a03020606040b01020f120c010906060b0a031d0a0b1e040b04020307060e030705090912030c040905010b03010308070b0a06 82
    0xc0103c408040780d2060a1010006c502c0700c0107104030807003410b100c10000f122001c0d00c100d90540d08174513814084403d0000740c80d40e0081d29a05c0383c440d410324100a10102c0c45902000d9131182c2004101c200d0080b42e164000016500356110040c03099104030264000c40c07514121103454210302814841c085030f903c0800b9480c00c400600c0a0b80560841000e00c81c2c182080e0084403504203080c0010440c0401d0340100c2561001d542c000803d0307542c5d01049c4019042003c0d00803008907500f02c0014050651154006100c0d85e21031a1140b002c686010640c040840340700b100c1f1554460364001600d2611450f84a01c400c1100045c04080b00744000c202c01800d41c81c1d0400101c0c0038501030101180c6510b440e10500d8908095034120500740000b516624101d9500010218140c4100b641c000c2035a48a49043c00d02c1d041c0c0400c0d12105d142c5010040100100c003007009042219070580d414400c0340d0b1380ea4001c1025100a000242010034200030403000706000009030f80c0c020515590019600740c0c2d813240b42856 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 257332994 1250 257331744 257331769
    0x41805070315030818010c1509050c0307030303150e04031706030313031a010807050604050d141203100b0301050609042a090305100e03090112061d07030f060501020c040e0c 76
    0xf034100403c9058017904090180d400b07441003030030309039030030a11034613034a541d000b1072031041c0c8410342c589204c43c007005030501c000c02ca4290081c046034885a00d82c94007030060401e000b268141c1c6145100c0000b800180038102d41e00440c0c050b02d450213807203841c0300013025215005184035010b100c1088940785603d000b0841c0b0f002540035485150701101c0285c20a040c00720b041e4052505680150300900a95540000326803c0703c9003140d21501005140c54000c9029103e4001c41d031650141c010541c80b28a643c0d802117214411040c0460908e62f11200daa0b1141c0c0001c0c050b440d040482807000c1e0481d400c050b03005c034030b607a000c000301c10090b04141c000b07500750407070603c400b20005500f0240810810500b0800070000d0348c01040305100078085a1821071340c4c0d000d0049130b503040104032407050f0882c00d0694007010103419071000341c1800100a10000d10034030300603030f410000285003038400050380300e6611882d0180d52050f40034010389021801000080e01840f8201001409031031358640c055521900c04d04070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 257334244 1250 257332994 257333003
    0xc0302220b0a05100f030608060f0106021603030207260d110f060c09010309020a0b0a080609070815101b14010e0a08090607110405090604051204180507031503 70
    0x2440e1003103a400c50305540300030420720700403001c0e004240101e035181003210790100c8140c0760a174a14110030380c0c00c078041e200640c000a55401504140f15100341c815019034141d68158080b40c040c00140f080b0103107143d0540c440600180c11807542030050340c4050100c7d058034003086e12409d5502c2c002144045c14049024330140126400b0312403254203441c144155031000758464050003e503e00040700990703e20441c0302c0d2a04240c0d490000504640d29040c604000c0c00000a01544500b04464094140c280507950300c4d01c60101d0b03400140009209403010341c8070780f001549958a07061642c0038021000c80c06c00c001c40500082100100b031a0000482c03581e0f455010b1856800c1100d0000e040b9400c6413600907105041360003600040021618040858522800c1070b10b2180e0350300c2040c1030100d481c40e000380c0d010354003038180428840311460016455014900a6055508181b802600390049120301c0c07081000e0112405d000502c8111a035104640c8640c5a003000708500e000f140c40c0500c402e010b41c00417034 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 257335494 1250 257334244 257334289
    0xb0301030519060209061215040c020c0f1c0b0103020f09150409060b18012c070c0c03080d02070204060905090d03020c190309060801061809090302150907030312051e040c0302 77
    0x10307141c0039a610301d08c2080070740702084000c200d0304d0000c3d180d80d540403c00e8080c43c5420324507100768540604039800600c040707a0a44c21071b60103240a940007102803101340e200d9880840882080d150900300c1c2801044844219281e9048032010703c0007605000304255401c1b41c2c0c07020b90074959201c81180848452201d03a5100003903040c0604800506401a1b90751a03002401c3c024100402455907480d4008001e81412040c1c0c10035031030b1402d4015110f801c01040007401042d0188144070640150104900c02c80c0c0c14044992076848540031100100c801c1d0040340c0c001c044054080c0e009074020460880f81c2c00613540180c6803030101801000208200700c0009040c400c04000311036026901501420b010314042e5801403c1d8a408400303010103001e205001542c0355804070403d4000c004a050070094010101240d2415030056510b4a2080c0310503400b181220110b030a40e0328942c4110352090000b854080f8603c01d40b0741d0600c19038100144200c81c00405244040050f03500d80e41e86204802d440d00950 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 257336744 1250 257335494 257335501
    0x509010c110d090e181e19030e0f040b090f0609180706110114010f05120303060a030b0712021909080c1819060f0f0b03010305190602090612 62
    0x10984240e0111450035038105100b14407000307502c070341800f003156100003c03510306480e5001c90a400004d07103581d1011601c43e40605555176a00d090400014143c50001d07203900c0156035024200400d140480180001c01c600890041032030100700b13440d080e00000d0030010b194000320000c10038021042c0d030715507141d003102c1c010454145000201d581e848480e14241400302040e5996255079180d560141c27505110910402c40800c000960000e008803050120004155a5811400d10101103d014a9000d162040390405c02824000100c0f806880040d00c0d103040645107403101120340308054052000c004402c0d40005001c8618006011860840800c611514000030005003030560707140e1100800390088a994041e41d0340703c03609903a03014116050101c0c00c0e96282d220861204079981d0f502c0d904c0f49040001b2900380c050302d00c0340060340c4a91115150b255100e500048403400309100003002c960060508007956821804840b005501c6100050b05000b0f1280024100342c00ca2020124141281403c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 257337994 1250 257336744 257336747
    0x909051003020622050d03050a030c0c021c030909060807140a1203031406011e0c02150c01020c100b130b030709110a030b01111504080d050106050c061e01060e130509010c 75
    0x1000802c2c00729006c50890240d40d501416501901c1e01040034140d03030320203140d00a80240310340e00c1e20f00d07402803440404e0303929440b407100e081d240c20b5030a40000703001c0c2c0c0000c181d5800620411b0141c5020800424007a86400d46c00242e089141c4410340d0011400c034000a442243e440801e51501d1107914082526203d070751040d05900c80041406041100c858030b070b01d00f501d40c2e03099500440d0400f85401c40b40c40841c0d00104903940e9000c210405c0784000091800c41c0c81f074040d8007804149a0780c0040e122540d01c00c443c024141c0b100300c0030456000c40f110389440607413242680060790f80c0202074150361080e6520340b800001c5507014505440c801130001058502d59615129170300102409003018841001ca4000580d038070440551981c4c0044072100c080b03002e001d04503007903403581c0c0315102c002d102c00d607101c803001030040d0041e00c0c01880d035108040c0899401c50007116400b10010001e40301340f01a0780b074540c0440d00712040c111125003100c000200410840790301c0c01150300c034048000020600b0042800d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 257339244 1250 257337994 257338057
    0x90624280e0412170c160c1206291e09040c03033209031c170c0f1c020712050c101505060903031303031d030d09090510030206 56
    0x44401040a6055007000800c1240000c40e00f040c00c0c480800d403185501c00391051012081d0b000905429100000056081c9900700007c3c23001d44118424000b1200050000d02501c0d6451001c1120281d0b112a203812814410000541d034444142c4444076038480c0c20100d051107005880950311030a003290705205064000e0f101100101004030141101d03040c0040084400c2035018098035110000290001e007a5410001d0310030348100c0503240c09424001210141040100d0040f810085660380c000a480c00c1120041d05d400c4020650100d140c0401c10780844880100d80960a040f943c2c05e12039000815840100c072804000261229540c80340101b10070707840c003031101b074090301902e04200032004400e1454444c00b00301c0340309039a03403612101d030240043d080d070040c4410030101a980c41e00000605030f00040c22005149001403c49104924905164a61001c6205440400d081c62070400100607181e2000360310402c46245241125101d82c0003403019400484042c0c0c141c540a800c0001380d054001c2e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 257340494 1250 257339244 257339273
    0xc0218160f0e090103060b0402070b0a060306050112210903120206010e15030a0212070b0f0301090b01030e0d0c021903030806040608030a02060f06180a05090624280e04 74
    0xc110000c1e0764000c0c00140c3c10001404028142c0da190301100d41c0315140c03501540c0e111648001034151920303240002c80001c1c0308500c41511100d040130700001e201920014070340c1c02260040709416011000001450303413240101f020000f000300000000000c1603d100005c00100c403d98080c1a19514160480002110103450544c1c08001d80309004c80036600040c049141d1039041d0351581803980315400c1c40341041c00c668480144810000341281200d44c1500c02503058801d403c00c00c0041a124000442c11182404013500d8254403070168910039901a0400303d079081e100800e5030140198510608803038841a0703008401040c000004d0103868a0302e1f0299401605808004609109010070300a540700c00103030114038000c49210209600d0340352801c0c035061007402c500c0b19a0b541c3c182440c5100051100b00e40c00700450003000040b40b01500002d80c00c03c02410318912054001c2d41d008200040510b0181e0608161001c0c044d480920940c0c5a14800085ca03000d860018645000e0511602541004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 257341744 1250 257340494 257340497
    0x20609060307030c1107320a0821030403120902040b10030e0f0607140f0405030a1a1003110618120d090911030109091104060305030405010909021602010c0218160f 72
    0x1b0060141100900d0444440035041c01c50391200780088040d51182d6542103240b40e0012144400401c810303400052a6900032070404101036060081d120b100d2441c0000e07180100050b0401036a4140e40d02c0c142c2240074200e000620006a81d03100b000018520b0131914180e070702003a11499004402c80080c044004030b2855880504101c0c42c21150040c03981c0b4198010345404000803860000391800b002c240c0d00a004040c045a00765211824852412030703824680b8003500210b00c0002c0c0c1e101005050301c4080b80e5010250241c1000f080d810003c1070f412200c01c2c1407591503101c03042000b550741c0300545d2080d8507250021780881e4103040801410303280f0075002105c9607800c00000d01e5507013100d9022641100c3c0a5100000c01220310f103800c06880003905803855000f810044013005110b4080024001c50f0000d0700d071007141070341d82e991703400680c0206948120b0203031141171071002650240d250909420301c01000d582c0d07000008001703141c00403002d48840040041c19458206980d41011000254030f00a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 257342994 1250 257341744 257341753
    0x10c0504050d06050709080706031d01150608070c061503020906101d06040b030411010905010e030a06090303020f0d022212020d0201050408030d0f060902030108030307050304020609060307030c11 86
    0x425000c998580403000740203020321355450001d80c2a0b4440c0040d1400b81c040e1a00340d03601b690b581c1c02c008000d004943c135082030030406001c0c4401410720502c02c45840d400030514281d0310358a41217041d14140d400a00368818480b222040301e000420070320801030b0021100c03681606036030079030040c040c102000400c5580920a4141407032215038202450004d10450441d807000d07803480510200e103181c0156440000c68070f0f004400d000c01c0014101c07500f1005a403c1e6a0500c6c02c5680d500115901801c201c102501500511581e4010a055801842c5680d009090241c5029005000004594040844040d2555010940303402421b0b4202c1aa00b28200041541081504141c01030b01070810b2490024410581030004008590040080d04d000b855110141d0f038643d143e6401500142822030703034400318640707400340c0401d20600c0e80c426681a210b41c04025415965464401e403034903400a4016a4855003c1c8000e059070b55501000303500c1102c1c9641d000c9400314074110058041d21551004c404a81c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 257344244 1250 257342994 257342999
    0xe030d091502370b1503010509070f142b0c060c0809040e12030a091505040c060f02071a040e1b1c0605030604030915030b010207060f2f010c0504 64
    0x2101c540008a001c0402e540390f241050002d80c038a1045860280100b04504e048100000c092204411400c0001c05030002d200b40d0303944081c1d1a0300d03054203020f10300c44001000c0003484041c80825280c1130441e4003a00c0e010000f89805044c6080d81700c0041c50a0320f01d9200244202084070903070000c0014071140c101003105a000b40c0d206500da00604055501999072429001516041048140004440900703510390380d041510204000c0c0a042c5019120700d0400c1080001005061003501d100d260411810b11280e41400380440b0000e80000d180c2c2c08501c625440451001d60002c080c01e1700584d11900d00c1ea0b1503103060301c03681c40c030000240f200c0c512030f011968000640c0082d0040398100c2d00500303960301c41d02545100484c01010160010781c0c05101e040e042004141d0030403014815030b4030f5548070314148400d41c3c50843c00e4500c0d6400c1140143c0186c01e04000d0603014042114414402e81800200b02007002c04580418441c640100c03004558081004d404000a01c240c400d424128a40b451800b0b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 257345494 1250 257344244 257344273
    0x80d02030c070308030406021309020a090b090303041208072a0602010b0f0913050106030f03031416050306060d05070f09050105090f09040501020f19080f1302010f0e030d091502 78
    0x380b00c0c0710240218400000080420a05070304991a1041c215480c420440e201c02c1c5000c0203401c034191413408a501c02802048208001c400c2c3c5034540b50080040d80740504000d00c500e02c2002c0440100c038224414890000003c552400c1c0844905a1034014619100400e90361034045c016980010196450010708001545600c21400a8a0f9080d6141446500e803807502d040400c45000010302154a891404010403070860000703400c3ea8000d54050041040c60540c00c40c04110580b128041040321450000b01035000c1c0d07016580c0003000404603420103154948410a84400310b4803d4001880300000b01c810940041e1103030050a820320b0074a0401141c0f1011400c651440602140700e501404001000c120007501124400000e550708d0680781d03031f0b8509400040541c0c114000020900c0c0743c00144014100541c07942c440c040006041807448241c0d001903403112340d0070701184100300400b811490191000c0040403c00c5c1995521018034502e0108804e1402d1014221101190021034a0220340c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 257346744 1250 257345494 257345503
    0x20918070215090f0a05061509010803030406050403120216262a030a170c03060f01030509010e1903170603031b03070510060e0604060501051b010605060d06080d02030c 74
    0x10b190b02c000510707468aa84104a141001500459860344255481c51040210120301640551185403102140c00c00c654200a000f4109028082003944103000040110380950010340d0414064140340749a001c102e4442030036039100c00101078200804c0c8031034100304600c00e0403141d40000d21070142c2800c11407000c038003a202d120b0411454080400f0b45803003030794041011840145016500b045942e2051a41e0000d41174a04441c01c80c1321402242001410300409101180d11490005280c952514600070047d8028400544000c629650756208142c11038420070003c03000200429144420180038600100f808101203002c8100050000900240740c40020941d1a01e4803440014614005003619035031542c040c1000141841c8250460180c0481190303001e0300594400c1c1c41c200e40d071959400c00780800d4407460702c106400103800300000e10156a121030b003070881036440b07030010070700c030b07640d0000144184c000325080c850150b5155000c20840c0d008104440701100f240c0040c60804000c01d402540701c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 257347994 1250 257346744 257346763
    0x2011b0803010510120c0e030f0706020c153a090c05060702130f0b10180506031902040e06030c0a06020304030b0a06080313080705060915070204090f060209180702 72
    0x1e80ca8413030820545402041441d103110a9028100324460015034000c0141c018408014080c2c0101c19114141e1440811101d09aa055070020038081c10311106100c803a6105105000a0900512090f0003018070501d0220280443c0290600d403c4444401c06480c0d01c95a1204200359207420101000200c4129440c01100c008a42450b1613080380e001041c80b240d500d080c2c10640307a140440c5910041c03001d5102220304802030b100500d031001107420a885400fa184000c50b0790742c041d024100b100e464034400455200d56000200491155801c100748107070f81198104040104400c007c02c045030400700005d85a1490865030007003054078050010b502c0c1d100f18000540070b2a90403002074000a00c5422820042c00f01d40116680d0b8444126910f4100f07a0034003904030f0901038040d00003600c0ca0308100780c4a45140051006031011402c82c0381000c20f5000303080403604180c071038140001044000c620035000d18003030000543c1d6040444104070700b180c403a41c1c1007078181c084102403001441c1d001030207910 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 257349244 1250 257347994 257347999
    0xf130b0f0408070506160206010f030b0a05090708123f0c16050f10050705160213020a090e09060c07021023041a03251404030c0302011b08030105 64
    0x550740351400c1c2211103102d0030001400621448060050703980c000482c4c134107442c0466081c0c40c0340382d0303c0b4140302210028500c03000e4041e2440f80d000c100200c095600450b0845c00303002c126007000c1d580d80c1e81c05080c007090361280040800c01049005020344069802e441c0350131120750344e50341254031414080300c0c1c01e40158040c100514060000c1d00c0d915010f001c442c1080c229284401b21440d4514102d6a500103500c00482a400fa5401c00340e200506070060900400040c3c60b09030070110071442654a0581459040e644045100440d00040c801c510042940d040345944c0c0c10007050030524200c1d98000081c0101c621644040c040103419941001a11b03009036049030f00c80041807103190115801512400680720200c6c4100300c4601d11070b00d81004104590918240000104444008400c130f800226910595503603224201d43c1d00368104042c9070500401d505240f408224021581c145540103604100d9142a01c1c0d4801d0055603080344100d40362010b241070280305a80c2941d40e02d0f2141c04180300d140d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 257350494 1250 257349244 257349271
    0x40b07030f0903050303040b160309171c0204060201151707030b13121805090f070503090f071203030b03010c1d01020712050c0111190813030210080f130b 68
    0x5452040c080302c0001c680040450741c490920b802c0c01a60518140d030903200e856207002040c44c00d94041d0007480040c0343c20000390036403840140041c480e280d0220084a040e03800003542010313079030041e102410203022a940005508004554452400c400326009600d0100150149285503680061000296a4400b807541c1c0c241d00c9186010050500c410b000401d6200c0d822949400c02d640403041900705425580490b21142e070382c60600204103400d40b6240c4100300d0200006500310701032801140c2181c4100c0460340140c8a01030784905101141d040085030300c2001d8400400e040d41409580100c5408030000c106200a40102410070980c1002200521101d000b10620981c000e00c50100141104031840c030f0312100614140e629808601c1c00c3e28080741545481c0c2c403030105c0015500101c0c8009150f07120002d0816184c200381d40d080710a0140c0d00b9800c00902000680b1240c0318450700360000d0305c64040b141852a8207100d54003005001c20000c00807240d202000c110f032001640d820443d07005c40107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 257351744 1250 257350494 257350517
    0x20a0f140d020f12060604061a191b080c120a0c02040c0207090f05061302070f060e070f0914090d02030a0809071a07050d03050f013507050405010b040b0703 69
    0x14a5004042019075000f1351004084440c054040303170140c03041d6000c480400449440d440c5c8490752070040000740154080500550688014949014100d000d91f403c103450f09108240c0d840903048c0000b0030071109850041040010302004015411103400f61521b03039400c10301d03107010003044405800d502078442c58807507603000c51381030081c41550041c0141003405c4c4003070450444103601600044d01e0841c000d00f03902109800c24101c80c401c1c1e8204652201e511540d8480985403400a0194100d90322007600031544002445260224031800503c09504041102541c170760502100d900300410316002d503000f08010103a8194048112816140b241c24010201d40b200390070949006169001110342401d00031003180719003550805010410701c20000c40318209410711003141540c07020b903250070301e07250400d005005010012842074442081140c0c062a150b0284050b07004009140f600580560002c21007071025080c0741c010300d0302400025907583d14061500100009501c100340018041083c1b04044 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 257352994 1250 257351744 257351749
    0x4050a0b0423010813020d05010c050c0f030a0503040f0606090504110f0d050d0c061b05130b0a0c0f06140f010603110c060c030c0403080d06051c020a090209040f020c060103020a0f140d02 82
    0x107807e1002c3d0020b000f08407044900314040c0c03081d07000c0c1d05130205501c1b60503480c416000b400000c07100e021301d00740c2c0c13030900715142d654842000141c500c1044405039142e5201051030f110310702c40e10303200358040c0880d0390031008100c0920402c1115141c0040c020395071580200081340000404000310001c030310b03201030559054140b01c8010703c0101c261400f9446c1c90a0f00319400da500201401d54141010080001c4a07524003c0000a2207480200c0c0e010904000058000c2820302c108859800e00404001c503020340106091448000210703100000e003548203006110b0564540b00300002100011017503840c1c900c0e08201544d403904020110413000400100040d1058081410340d801141c1c40401d9640b81c1c4142d58840c800b8007900d0040301c0c041c00c41261103007007003600801c99032180d9030087c0c0450074880c241000c0b00302030344c880d407074031038000e91194840c1c1c00f45506031006004c0342c64200c003d80716650441c810040507071416800700b400c2c0e4000000c140110f200c0001e00440b804400c07901050340805074400b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 257354244 1250 257352994 257353009
    0xa0f0b060d03080c0d061e080706051903020703030e10150b3903040303050706050a06050d020d06061e031211060a05070e0405180105070f020c0f040204050a0b042301081302 76
    0x1c9501482c0203002d0880b05ca030742601f030003415a5403c505a0300059210b600480d000d00a6240041943e010070000016041c007a5008002e1603010b441d0206000c92041c407150f00d4404e182001041d0203558503964140d1400c24802500a03140307100c0c003140740c000620000450300703621648409001001410300c01946000300240132450760228150390321540d581c200908103400c40358080d16003038100070001e80184024850b03c0700340c4100a088480120300c980910020340a408011504540c2d41c060110b05107540441041e00e043d03110100313480141c02c52611319610f80752460004244500100500008100855010340c052085da4000400da03641c00003c49600380f00c00140b1342c20038038100a1111103e14096130154203090000240300c6900c03134003000c031018904240c1c0400143c01c44648200d15107000c0e004015054001000542007944810011f00141c406905c5101501d600180400800070103205603810044603442c1030240b10441c8001a004003401052684001140c11b8104215550b042c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 257355494 1250 257354244 257354249
    0x50c0a050927040507060c020a090507030b0616020f060301060804150f0903030f050601080f07030c02100c020106030201120e0606090603010f05161b1a180a0f0b060d03080c0d06 78
    0x4084505100c224208040e0b4064203807010340b01030054407008601d8900420030004c860b070b03000d82105801854941c41c0b40040030003900c07140030140c50352500c80c05956114040c0010b0002250b814403941e03907520400460012003c034041c0101001e0004001e0150006411580a80c001c0c030006411445440e0100c0145078050070710f40c0711441c0150010a050f4540d01000c1c1c036082588007000705894040042d80e4084007103031401541c905410004484c24403e800c80450f091450040380c0081c41c420742d102e402d903800d103041c010040c1c1d90741000700159a07110080085c80d103510641001403000d4105050b440344001040103005d8101c4102294460b10258451807850712450307020000e904144142c000207004a0417144000341c0021070140b51015440d05440e54107502070303a500617524103880803098041d002040355140c241d80015508201c2000d000d00b00311184544002c038010300562800703900b940780180c82c05015404d40544d10000a8108200c1a008840843d00548a0562020780c078064045034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 257356744 1250 257355494 257355529
    0xf1b0d02030c120f0615090307180c08240d022e0801140d0f1a04031710080a0b040204020c030a09080d0201091a0402010915080a060801050c0a0509 65
    0x100400360b000040905100c034006014411a500c1d51801950428800d5a00d550b100010001d280c00240380d80000300710212000d8250350b1a40c0d80d0b5601800a20f18440441d070a164580d802d200c90680d00059482e8072800003031410814000b1144500c40c102c645003911030007092000e50303d005540d240400d480c003d1607030305000ca050980d00c0410b003200003074004480d800f040741003002103924440440722040e0100c000d801404c01042c44e4032070401401941800b5100445010301589030b044400005a214500a0300c4172502c0881c4c8d8202000100e45c01131111a40e1001d5420034056186d010446510458004504141d40c0e141c07400002c000b0320401d07101c0000380c40005041d44180d6040940b00003161021825180d104924030001e0f820385030a441c0c010851007945e90320621001103001a80d4000b801890011142500c0f03202c4025041c031000000008140c0036410010902e1060040390081d10f0a40024445428440c0c41c120880c010001002c052240c0410110810f4071107000102e20503124 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 257357994 1250 257356744 257356747
    0x2030c1603030b180105012c21070e04020a031209080f0106230616032c1f0e1012020d061716060c110301320f1b0d02 52
    0xe07140c0580102001c03100140681520b0241d1065280c1c48001c0754103c40042c0c554000b060380c250306443c440c1005542d022544840048000c405031102c0b10b200101104030b07213035040e00e02e03c0000c80c20704d8460705900002041e0044010800180c461f0b0708001c007220b501c46450002c1c031092080a4035040803541058000e0303c601a076418082c13030150019000c40310000300c020201504402c1c9003070014081c49a154204030204251204141020100c09001d8040d1030f10450420603e500ca1000648000c000038038a40c551451440031300d02a03803c3d4010b040e0588104989070a20400901b10720311851010340325030300350185200802d0250700708141c4800246811540d50242082e280c000b040c282c01007404045051079840d019100000b10b0010340507520900070513540c034002d4201d402c0f8040e40300c01c41d00641400441201030b102402a02d40500c0003140c0d410000c0401c2c2403540c000e0a00c1d40c800042d014251082c010740e41c11580d50b50390004918061480c2240540140145a2081c42094482c1620 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 257359244 1250 257357994 257358037
    0x302100c030b100f14070206090904020117010f060305060907021005061314250c0206030a0612030e01270e0601020a0c0e0106030f0b011d04110703020f0f0f060a02030c 74
    0x2c0c02410300c400f04007641c60f215440645605d100d0321034025404000d41200d81000350303100d10304d00985000e0b4800d06c140f5003d80030030006040188418402c0e403154045410040c4148241038141c010542d1209056800c100549000d84c0c001795502d00e9400c88600c0642c1d030b98041203c0c1d071a03003c0300c00c14a030200d07481031110213225100d101100c44110741e0b10500d1050402804201100355444a00781000c40c0d850501d04c204030f808022440c0e01c00f40c061240c2071303603400c1e0004206612130040c40703505011b900d802c02201e59480002d000c22204122444000f141d00c00c907100084c800c00760355401e03110361004513091540c98200507132400100d9240503040c1c81e885200040ea0864400c1030f941640c03425501032010207042c801d11402c0e034000d0301c641400315244001c420300c481c40007110300450000013040480d522000101a0302c4543c032402c81a40140c001503e4015007440401000c8d1100350902c000341540f0720840e103034a4950340c002c0d1240f403200740c0000104141c1051082645e8081d190b140b8048203000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 257360494 1250 257359244 257359247
    0x20c0a050c0a05030304060c060509012a0305070315060c11120715170109090f15090605090c030309120715050a020d140a050705070b04030f0b0c070302100c030b10 72
    0x228249040b4400c50040c0d00c0842c60342408400e903011154151906428800c01d55981d001a00000307181c808950f40e0703141401c00d00e40c04400e0641f44426018410003011040e41002010f0f101c0003010402490b00304401303846a21103802c1080101d071490b2900b940f07900310501d8200ca1800c0c131102c00d1503001c605004003143c5902d0120702042150721603015280d50055010045d40c4081001900081e0000b031280100120501d42d0440d48020344039000f0984c20441558441600c002240904c846a960f56520082006803510507680c020443d04010980e608540001940e24469012001d0094070000ca151a40840c1086111701a00421080061010500e070000b007554000000460051042d003048114003800341801414160034400740620304100210b09491661025030112070303520030800c0001e98041d000c406000550320840d400f071102c8915003084000303074801625031041c1d0903080120341e001a80008201d98298152500854414040c2c034003540182842d00fa0a40c2000c00c0404039492039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 257361744 1250 257360494 257360503
    0x7090e0a0807050309130b060a200607080709090e0601030f150501030302150c0c060106050901020703061506020d02030c03091306080f0a0c061d0607060608030708040501020c0f06120a020c0a05 85
    0x840c0282c444504106c4241240340c01d459800301c80c103030000c2c02088104100740c40707030b0101c1544820380521040800e10002c0303223620b80341c4121108000180d100c01401140d0b9030000c1580010207000000380300d08a12500b0711303038842d481844010220038000a21004210700800c010782d15005681040100f981d5904019407506845d0030900c0d0440c0e291000240040310364029240c4c020a94001040d441c2e080503019a419400901007505504ca41000000010998056030441803c1090140c8459203410806881c003881a01c400041d500140301c44080d0701000420340308003100440b0240101c250f01c0e40d424008146540086041d4044c02980303607040b4000164810305c8900ca086401b4583d50740b500d0803203004000c15600c4918042d4050121514034091001e000400c0c001c41000031002d03500c204482c0f855100c000c0848400402080800107580c050008000b1000c0c180c400a0015216100160851140e4101241505c800388089002c00301c103a41130302c200b50a0441180c00e032030312505101d640c6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 257362994 1250 257361744 257361757
    0x120d150308040e15060304050606090403020313240f140304020109150302030718140d060f0e060403021011220f0f050f0d0b04030503090f0604031110050907090e0a08070503 76
    0x10002075080c4c10300b03241410030450b407059400c98003a0000352181c10070442d461101078425411403000f407100800e14400044004001d00c5291000781001c41c080703144c43c3d1140e04100881043c0540b05504440240c1c0040400c002d8507120101c0035039a81e501c0c4010303241c500d800c1d004050750204282c1100081a016402940681c084d9101d010800203800880c1e94401100d024003030031100012910607160800b0394030071100300d22503540842c0c443c0024045400b160b00303202c5c4425555204509000906406100c1c1d080720100724001032223130300d60540400300703948201c1000c4110903000716085044442200304c0d00001d01a240c80320515655a10319030143c3c144070380074440c032994022003061058904645405582c980c84101c4040d10354550714147e80c01c0c2c00041a50742180038601b900f85203a0300600401d44034510036120384c1610030300d14200a142001400d28820700620300018000f40716030000d90700b001c4440719200450a2402881d046051090052004008100209801c402c010740032014004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 257364244 1250 257362994 257363011
    0x90c0d0f020d0e070303050409023004120207080d1407140d030b0a080a1b0e0108010f050105010309050c100e030f100c0216090c030209060a0f030e120d150308040e 72
    0x15403000c20f08040d0300c0f0301080c40002d011500800c0100309a5059801a004240103100c481d4a212001084443c948081c0814138a101d090441084200007040500c11581c5500e44002c104040c1800351030ba40c2d500c00341c1c01c07501c180032401c4184001c100d01542100c0714107034449141c0075001c4807113048660b140c00d03030520780e004a428034400580608103030600e00d00311581840288951800e586510301804110954116407020072200401c101c00280d200300d00030800e01c0c00000c0e0301c1c04004459802c503401a0800c50425042c2003000003c60400550150303100d0b0110b4404008901418041c0d51464001c82c2d440d406001d11030440482c0c00307000c15001d803c3c0c3c510b01e0080c8405030b10444101d03142c440610805400001e901b00c144000e0030590b110029200043c14014548001c0300001411134003c0d49041d00024a070010400c15560705003d5484205070400062072900400c01e008100e0f40645c3c0605184940d50b01589501041883c0188000711780009446a81d00d860709550460130303804584550 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 257365494 1250 257364244 257364251
    0x30b0f032413110402030a020f0406020a020a0b04050603061003180f0507080d120e0a060908031f0b070206091503070807090e24030703080414011b0201080105090c0d0f020d 76
    0x100c50b03200c2d14220001450b80841c01da9102c0402c0c100b084020741020705141285a400d11402c5403100708071000b0005418560000c06100d5020b2041081c4002150007200d580e120900041200d0345554082d290810811540014480c0312140b044004000e21524440c0048604015400780542c0307040d043c0101d4041c88c1501c803c80e440d103003da50f5410709c40d028203001031602800040303144100d81c800f01204400703000351200d14045495407001d0310940e06095604803c00800e00c1040781c0390007103040c5410480b0480c01001c0e460000840c03c64041c1e2600070303008070000075a401c02075843d041ca050584546140d07680c0c0328102100001c001c08005c90321803020a441c05001f01e210200040c0c02d621506064941100e031181c204040704034441a100103540600c610350b008000100c41ca4090005010401e0040741d204080200042001607a030b44512403407003040d040c000250b42d02c8503280c0c0c1503030000e0710034132815180e48120003400d10031044c441c0e841e140340481d0142003501c650020696140c401c041403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 257366744 1250 257365494 257365501
    0xf1e02060409020d0b0f100c0f0b07082d06010c15110c0d0804080702060d0b0d030201020918040f020d02010c0501090c0306051f030b1005030102131a03011401030b0f0324 75
    0x817150091415194851f6100d120100d10390321510142606511940710700c030044503141e4688100302000d81b99140401c16601c00c01c488900d003080003144140340803501c4102c001c2c4551300c540c1840000b41400b81000070403500f420a000c540020a548005040b1080201d00b0448a804034190031020003085540604000100e4440c8500c01080c001c0d07403c568503503d00b080307607070030091103505c05100c130560103407101c841e4406681c642514010160090700007507503460380c0703104014043c00c10440701000d0301c0014043c0004600b019a040b0495a410b445040c18040b050005a40028451400034810b40c00d03d00d1362820000000e4101c000c5038070a04060025171036440174076106219008007100841807950041020612000c26103400441d4000302130269621a070100b4207a034030101c01864241c0310984101b14260040b00030710615401c54420508650400503401000b11212419038105502ca01c1d408890b03548035000c150700000002c040f20445902080b102071580e200111010780c0c0704150000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 257367994 1250 257366744 257366749
    0x60504020a0807080c040504020f041b09170303160507020d03050c0c0103020c0c10030e0a050718020304020d110301020d020c06090f010209030d08090c030102030c03150303070f1e02060409020d0b 86
    0x3140c09545141d0094103c0d00c180d0300600c001400008c0040ea484200c000c6902c0c3c46454a06c1074030141c0844c0000c80d8007030421081d0180c402c0741154444010750042e00d0080340c1901c004010307660020545108094000c140038412182801a000b000c0e42c0406400ba03010200b64001004041161407501902d030441b80b0034005404a01400500c0f084036002452401c00528146541020800b61030800040110540c0410f81c50074410032030444242e401402c003400b03c410111040d8090310b180582c10361451510754003182e2140c2210700018010700c0b5001404900383c1c2e0a40603078841501e0108215111858020540e40e030315025981c6030720742e02448120400d9541c040c002c41e407990101030020410302c601c0c4c983c22074003184000d00712840381c065400d04c18000d035400c1c0010f41c0922400700c4803680700d0600c0080c0550030071010301c20901c641e00c10094480007880300480340c00495000440c0c204010100b08056996503120400294003940025010420b000c082d40a024071505000c0c04014400c0407905 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 257369244 1250 257367994 257368003
    0x90c020a0309081b060913050109090203060a0b0f060309280b07090509010b0904020d090614100f230a0303030e0d0c0503160206070807060c0f021c0809070e0103060504020a08 77
    0x91020b13885048145000300342030400040c000d607103028000b1400c4110a050040c102c400070303082710340320310b072180740702e0301540741c200010341c0c0003006031004002002d4042c0025044e00300203e2400c1c050303040480010345c001014030540d0a03a00d41080f10390024140b032652412000c0b0400c500f143e01c44100804252641d200c0c100800030781c1d10103400c50900c3e90800080b007909030400404254406c0d000c1060710000b041d680a07411180c0d100d0407020a51000c440000c01004070000c12203220b40308820000c016000009002600319400c0380d01070401c00c64060b0b4599510f0b843d041c0b0003600014840760000c100740d4590f00c400c01c4640301400f640c55484035100211541d43c062200a071055009110000412001046410550b4401410f4a1a01c04540e035400601d0f0001c200c00c0d2180399489205899032a0400f0211951402e144040c00e294000c0480c018510350440e1004002c00c400c0100240c0f80141c02c01514004c0c081c2d103000c900143da503a180200140c00d0880e0200c1c040c802079800000d043c900040d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 257370494 1250 257369244 257369263
    0x61e01090e0c15040305030f09040e0f15101d0708070518090901180b0601020c011e0c0c08120310170a061a0a09020d0b0f2404090c020a030908 63
    0x806400102c660750108007844000c5002c1642c030400411001000900070070091000d524180e8189031507582040400040398013284403a02d41b60003d0580300c0d4001404121406d0010070003000c814261540b45094940501c1a0025403c0d240f803841d070b2041c40b020b0020b95520814695070f4410140e070312000104c13140d0041c003050407032020401713071011024a000f40d9031aa1090b2440d00000307500d44106804000c1020144050b10004041c00510071156414010704503210020300f024000c0121074809091b880710f044581c802002501c6c850350007004034203022200281650f4084810500c541603072142e42d40c2c405e550712500780290ba0000103048510103000741300c010600c00074000000a03500e030310014003035807183c4d40000d4910307140c01c02203650342900c84e0700502590030340140c84016015652044801c03c183e0540314040d01002c1a100f561a103454030070110075181011810340d140310950342c450049411500700582071000c22100242d0015550508501a55a15040c95555000303161140d6011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 257371744 1250 257370494 257370521
    0x10506120d020a0b3705090105070804110f03010509010204141002030a080c0702031e060604050c030c0906071e031709060705070213110d06050a050a03030807090305061e0109 77
    0x2c1822020900f0040407171317480b600d242c0a070b40e0200000306810404c500708051074804402450350520481c025445415884100503008000a080121010340b1095004000815a62031603e039007000ea180c650700b044924202034024815406c102d00818042e4020b405220001c4500e422180628034000c81d400080d0141074000e180b51440c1e1000440e01c6c0c03d0000c141020f8010100503000040c1c5007040f000314030300f00d000701001e1701d40703044041c0605012015210512560528003445080070300c030303000c9a8000c01c02103100c40e940c40202010075410b000d28100a0135082810040344003850103180600302a500c25a08e204280382c200c040445401811346200080d980803000068800d030098009140d221700091031269503000c2d241d20308081d5010039900081101d00814081040700190169201030481100c0080c10b83d820700c00800c65031070031448040c0400c42c1400c041407000e4064200900a103412805484d01c1c2e103019080e5040d0007401440341d0500342030210000402c514140300390407940c40e00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 257372994 1250 257371744 257371753
    0x1090209040b06090f1c050d0302070606050108041a060102071d2509050423090c030706030b131112012301030501050f09070207080f0601150504030c0e040512030702010506120d02 79
    0x410920104401d442c0514841b0400891081c010540070010303031803c0401e903035025a036556540743c02402e844440c0d0050381072016810078400082d0340e1350442c21008582e02c2d01c50400380e98000040f03290210f075603c06940b4640150001042c2c04043c14894420800e20340c00d0b1000040c245213140903050b404d000c900010b50b0b0071100380058645904041c3c1c64011761184013002c0190700480d0409503070280d89a026940c07000e80d034030300c49040a0003404010300f01410304010f58907440021889030050354040801c40e90b92000310300018242c02c416144400d0050b00e0361b90240d82c550400035540d088001550130380b031090340c0c481441507100e4000c140c161800900307440881e40050040c01079101d0094010001d50040030300101d0005c00800c400304d10840c2100042c03010354586000960100316000860302004030800c01030000c51104d03e18403045413054a658407560351070f0304041c4d0404220805019101c0f00002c144400076030305411150090364216181c4c42d09034a04900907944e00d16008154000d030300b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 257374100 1106 257372994 257373019
    0x20c03031f05310219030f0b0a0918050d031d0303040308010b0a0201060510120506091005010e0f030a03020d1d01021f02090901090209040b0609 64
    0x40100203021410040410070610750f018503d8451600c007204481103045240300d442408500c00380c215254403082110b4a000b20400c19403400180c2440b551841e002254400c40046010080c1200002840c2c100315902600c4483c040125900e4250781610200d1418001d1403d403098941d400204608106601206d030200000c6035640d030360003841000002074002446a05507030110a0151700d54000c031008074003400068000e076400c8403154240c07031039080d00240b030480c5503c3e03c0c00e010710481d6600000e01500b04000c49003401c0e0381d0380d150b20811295000e00110301c00081d02a1403800d1381e90007040400c1c584240501c00b140103a03c40030760744c942264000d0780400b9808102101c50052084200001d50703030803840401003040e1f04507260b0001e860102c1c1e0f0407030700c0c000405007660810390380d9544030b41c00030b4006207041c030300490030f03c140b0035010f1426108a070440350000304551085c10 = true := by decide +kernel

theorem cover : BRFrame.Cov 257194244 257374100 := by
  have h0 := BRFrame.cov_init 257194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 257194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 257194244 ≤ n) (h2 : n < 257374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
