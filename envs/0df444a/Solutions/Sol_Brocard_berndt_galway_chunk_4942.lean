-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4942
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:13:55.063718+00:00
-- url     : https://prove2.me/submissions/9fe7772e-7215-406d-8ea3-67fecc457e27

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 888669064 ≤ n < 888848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 888670314 1250 888669064 888669097
    0x60f1504180204050103050f0103030f141c0c0f14120a090c061e05040b0d05091c0e091305060a02071a0705070c231e030a0804090e0106051005 63
    0x940207550404501c49059003400d9078001001e00c43c0e5645802100d0744a07540311590744041d403641e90010302844000140300c041014040d801004a0070b50404c9403200180e40090a1000d0652410840248502c1d01108040ba0381000c0500c02203000740509014980f126050b03d0400c1c40885000f0b02d840001050071108070380d0fa0904a000800b05400440036005550354107124403100c4031340c0c3c65022170700909042401401d11003080603003190012100c05050b0003802048030f44070605424680000056041c003c00c8081c902c1c04d220130303480480388032584003c03070b0110195203882d01420103060071401d001d07129800a00001d1000407041e00180743e154801c0040d000c102c40080e80700f6000e034005640c90800a2000662101801720459500e0040c0c04083e00e4904a058090129441a241800814000c980c070711000d00d107002c02c503000c035800207030b01505030f52014010b444c050400d0744c401d00400300e860303181080045400b00144580e105950b0058408110600701400a9035079800401980591003003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 888671564 1250 888670314 888670319
    0x50c1b0c060c030307080105030309090412023d020f0717120a050412021b0d0309090f020304021309020a05150d090303050601030e1b0909100603030c0b01080105060f1504 75
    0x11541c0c02040030703020107070240d0b40703d0800100c003c00c044010b07400203110754000c2c002083c25a65807241c03950002da0100c12020654030014043e42030002d5042e4502c100459200c540c0c60001101403036110115005000303415665094403500120302503c2490790350350f1024811040011281060f02c02014800c010b400e00701110803d050500050403511052259250000d0004010f50f85100010041142c0040d00c400300400c0c00c50401c54460401d154841d61080031510b090600510101c4007038502903006015100c4e101030000701a500a035010ad0040c90354119604015600d841501c071000d5004001e80b0416150a0420002ca03504060f1000603000800601c0f0f0a0318240c4514500d9034843e40303011800c3d1400300300140845040c0483c44078550010200072040c0140d8510401c508a07007120050020f458130011a40303000ba002c0070014801d86070031400300915400c00c6914132503503c81c0303201c445180e88510103d030a864080d01d0507500071640340402403d515116900e440041d0700840103504003903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 888672814 1250 888671564 888671569
    0x5041805180d17071b020603060111011802100807090506090a0503030a030b01091e0b03040303090b09030d0c050901020307021021050114030105071e020115090c0f03050c1b0c 77
    0x800007038040c08070300745010803c80d0200e0000d601c0e80c45412410541845840c80d2a401c030900281c140083c0304450000000f003282c2c0c081c050340884540340030000c100f00341d8121643c811810604000f80d1003080c04008800c0014444c0440c1807003040c80d6a00c00500c14078110a00149802c003c0c1c2d0964014071800c070106994804002401c0404042e84d00884c0c520b80d003c4c005000780c000d54000f96041500e040750403007040d40000c600c004450250110a90700d40d501c1c00c1c11070041c65000c500404150740c51041c000c07850b81c00000740c04620300c201c03820000340f011103105842d01d20841088901580043c40548058500404082c142c1825401c08090701c007007559580c160310b80c802c1d9260812954a100500540400c0c0b146a80098010380081000e4180f6680c003620801d0800002416100003544003000e0354800c1d0410307000802100c045220706a01d504481707004d000c145c400840040d40c0b00414454080c803c0c01034a004a001040281c40c114a40304021007680b03410700500202d206040d4141c80f0354 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 888674064 1250 888672814 888672823
    0x1e1308191e0f2f0d0b100b04030305040e071e050c0f011e0b030d0c0206160c0e07020c1e19081b0901090606050d0209130510090c0504180518 62
    0xe209078800c82c0496a15003c0594603400c007405072000782c50404000003503882d9008480242908800c06407402d41d01e2820500c00c1d5021900210391604001c5000410540c015000e00140c50710300b0f00900c0d0940e5601d4003101e909510034405d98403c0e60250071805000d000d035000b80f00340706a031415600840c00010855003900c0c0b107032102d020600f0341103c0c8099800b030a8800c250100000f00c02030300c40c0041c2600c0043c030381020000007900c039842c0002c1c0b105071008440007160030107601c14100c59105545800440750031004844c4070025000d012618130b00c52806041805101d91810318603481500840180158070a040c0803006800c10300700700110b1445c5041042d501c10307070700b00315607040c02c0010301040c0682081c040e4400b480c042d062000c2405155080760607911410a0440d00688481e4034000141c00035076030000d000c4a441c9002c0500c0b040f180d25901c0131060329500c0c00180b00c0b040c001c850481e25441903202e8210120401c41106903822140e0700010740100320105404c2da04c02001d41c4003402c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 888675314 1250 888674064 888674093
    0x1106010e010f05010518090c0c150402042403031817030a0207170706052503120501050f010804060c1103160c050d030509040f021e1308191e 62
    0xc000108010021900e41d805800081c2400380380590414140e5003504120030703440403c0501c1500d02c02c0000320600798080648140b0b84048080b10042400f0110f0f640c2506d0081d82d00f81d01450401c48116950000d610034001444420700c8820109480d40d2821070307801c015540c46d20745810401100203480e01c4070100c2c6070080c0798990081c60340c0d4003111304c0181c503002c40c0794850320103000c40034043d00c000350021820b002110f07460700300265108000d11000324041040503058020542d00c501100138182d000002d4112110031180c10440c40e40c0b0781040202ca2403901404074005845a000200056440d41082c95510700c14203000c1c0011400d00f0817142142c00c4102c141c24800380841a40c0240b22600c2070001c01007106507180042070b4a640c1b0b005200e8411100ea19014507103640303407484040030640c1250f14408400d041442d000000f0352050207140c1c000c05a07045211803104021607040e0002c1024506040c000a0760840c0766180e55403244010340640c8203082841101107004007107204000700290 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 888676564 1250 888675314 888675329
    0x1d0718060503061810061b060c030c030f020405030d0e0d080406050a02061b071b1e060909060e0112080d0903090503010c11060c1c0f02091c150b01110601 68
    0x2100d24258050001e0642a9100420211301410038003054429010b01c40e4281c0e4407a180600e2200400709040400a03004040140341c00d28000c40d07242d21b581c2c16440200040d4591794140414195070041509070300071030043c15031540129120440c030074040c4054100060024041c00c0141007242ca8564458110742d2104c03000c0f6800107900e90b12981d05100c0b00342d0000030030342c030790031403d01c2d00b18100044d005014004103020341005d542114070034040022001803400880801401d0004030010000300e0980c8149070100d800c0e500302150f000303010300620301510007a006c5001c0d0b81c0e1900414840384424a1415108003408101461003100d0501038017014078000d4641c08441481d20043c103007101c20703078211441000503629000c070700ca80f008100181c01506a01000340c0311141e88035803010329130010018080e2640b03800002d5080300100d07009041603031000c036424180c14a0b030700240500b00c0d10200004000420001000c8a90840d55105d00e1140700c040c509032442e0001c01d10b02c6490018281c11040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 888677814 1250 888676564 888676567
    0x1203040b06011b1a0720030913141f030c030b06100c1a18060f0a05090a11091b03040b010e07030b0307090c110607030203150a1d07180605 61
    0x85030358000d0f00e0f04000d0f410460003035007401e5040d1194880c100c0320b8452894002140c81c04117500354805c0c80d803156006a203000400c821140310070010340c1c07030f07100d0a4424015003a0a0042144003003c1c890355030091140c0722449110340d201011000a444007080c40c4c0016403c4840101c00708499650040285207d1080e0450a0408c2810002200140d444140c00c01110600c0302c0700189407252911484603010240030410744039190740d400600e00403c842071750f502c926400c1021068400d104540582a404010080f5464219840b602e4803101c0001800300c4585505000d1141402c036400c59008004004006442c0c11f50100d8141e40d51040e0303400e407841d4140f140140491148526800d801c45464141001000752010209031680a2032080306d401c05c0ea00c584460945001d0714012001814190a4034050f14007488040d00035001555040c82c480710b01b140d01503040c101040c004055540c41c0e5900d566030441051012000c0900818000800020070325151240c1c030000805800390502ea12510b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 888679064 1250 888677814 888677821
    0x304021305010303050d1a060c0a061d071203051b0a0b010504052206090b07092c0a0506030c0a1503050a05060a0302010f05120a0b2110020703021203040b 68
    0x280c4640c0030144810514140c010000a9040000c45800d52251040811420401d0540c1c020920b0440043c94115200050b4100840c102013180d26105100358030402c190410511110020110480076050b42ea01c400018081500c01139001c1270254800d02c0c2040c506001141d00c0c0f2802c0101ca00210b01079440f8030218000c000c10320010a024082c1030303408011520b00380c0c641030240d0500e050860140800b001c1e1079800c1c41203e070415104130b030f000361441e00f080c209098010860300242c401c0f200385080400700203000d03141c000e00c8a1141e040408889850fa1a800c3c26140244000340030f150b890f104044500405848030030910000740345103042000384038172074500901034813030061104d4425890002003000c203030354a0b184001a41d40a10b4044541d640c402c00a80e0b503880ba40e0440f05503030320f0394410004018a5a00f00666000e0300703880045502c41007403984070340b00d90307100c08c3e0008a0704114180395414409501a0801e140640704448403039240c06040e07545548150f5060f00c030001d07c83c080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 888680314 1250 888679064 888679069
    0x9060f182901081f0b0706150f030209010909050a06020901020f0d0f0f02060603070324180606090506012709051006021c0f20031b01272a0803030402 66
    0x45035000d4688007a1813000f500031541100520602d00408498040100e8584141303e4254402d1010403400e4454a5a1a4031001c1038881d2005904c8128801c054400000c20404610700441c2d4402d60301c04006c20781070300240e551030040d4010400c45811446650240d4810000811032654261115181c0101300e40c20540d00405000702d450540c004e56001400b44003042c1c03400140c210489810101c15518401071903014804410071200382080141004001e8130b08031440110300e080a4400d08080250580e50611682034420031503009011a0a0380300303001f034100301c0c1113a124856004c00403000d0416118000d079801c45009569a180100342c105051021a404000400a0746540000700703144c040d6000004006008501071942080040300b458020300c12444d00040c0251405001e803619441440411484015544100c50280d8240707241115412082000c4080f90344100810448403c03e684070fa42c60b15010101000e1094421000c50070000203034100708000c0c01554010310b650341001d004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 888681564 1250 888680314 888680327
    0x130222090b130c090b040603020a02060709140f030f0d020a110a0b041a0f12040b10080c0402030c120906090f03121f05090106090303030609060f182901 67
    0x304840e5890400300c1249075030756498240b201080c5500109144031a04422501460a0b62058030000400300b800b00f1865095005000807818036822281199201281116102c500d4800d05046400c004543c0c4000c2c00c010080c0201941d0280880d50241c1c5400000c0703241005652200c0e006030803056078003040054910086d1a44102100c9440001d4140305100b0400c1c4900e10a11303e0800040c18075148081c4810180d51041441d5880e49417150427191032034000c5a8102c07022034088012500040b03800740f900e1001d406541c80038004201e41c03020034043c8002580064407180d0403a03006c0c803901072041580380406100e1101c500c0035003079070f00304000013900d420190351461406401c24846008044170b07190f0115032118640305020a0031005292200c040304581e006075070070601c1000042080e581081c1d00d642180d10995040010560340e07403003001107600a001d62140000c4a035000c00198a504e0038402a201c1c82d0200029500900b6403204d1244020b482c0e0001e81490124040c2600c0d031b0003aa = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 888682814 1250 888681564 888681569
    0x15020726161410020a0c1d07140a030b03030403060501080d110616030b0d0516050307090b090a0903140301080705041a0d08030a241502031306050306130222 69
    0x1410340429400d1040d0509a9a06180d850340a0015000214400c0741308004138031145401180642480341c44044a0070071040b644c0200307030348048100110f43e00c3c0303114158140b180c0780140e0400c4d0600309091011005001681440303903042c0310034400032010504501c150b41c000c0030420010070401602d000c0c060400030020070045840e411036001c000c008509000304811158092500064100ca0000018035206203032001070507501c07a0100c900714074030301e0544980581350101e00302ca106a5940c0d41e0a030030781e18107448071900701c0d0350070011501084454020081c260300c80d00384840740d003100102d08110b40e00240d10010b003a030f1040d542044a0700b440c1c0300300c0051410340c4c02124003584042c008150413040190005022150010014101412036800b441640600c0409840e45041484101040c01b41501917222558854400741d40300e10300000031198100d40100d00e20364003501d41242646c03141c000030000c6c0e40080c0001e2005040b14030a10041c01c81000c1b11f050b01c455025100d810f0002d608054 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 888684064 1250 888682814 888682843
    0x1009030b0a060b1305010e0a180b150705060907120309150c1e110d02061e0c0706021e030c07060e0a120303020a0306150c020d060902031e010c08070915020726 70
    0x700f05000141c249c5801c00010f0300e0691021950030034a0b404940d030000c01528403050403402246020400201180b00d03030040d60b12504590580b0b46807408809200020540240440c203540c208112007489840081d10445c201c4c03c20380c856042584940031403490320643c800d0700c075941004881c100845845c4815900b48280c803c26140161607021429030320805041d4003c0b000c0084181401c624040c3c205d54202c10040d00351074010b0395034600699925804149802000301c200d0700070740c64600010985544c07400b920010f00201e0300e0100c00b40c07101041c203140940c0000e03038480041500b10422038540e507454400c0d500160795620413400101111042c0c1c00130300a00402c5a1003c141d9903001c440c0d52001501200d50801d4500c2c00c5c94000010003d40d40c000b900b40c083d1f160710540c507040b0a17503101c80317041b00400240050251414102d882607400c54a480100380400001d00c0351404045000b0b090000c076004a0340400d03103403140940b000302d9080401d4a81c1d580c007a09613400001c148032a00020915 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 888685314 1250 888684064 888684079
    0x60f0315060b1305120c060d0b0a08010b030309120c031f0507090f05010e12010e030406110601030f080306010c060f020c240f19051e061009030b0a060b1305010e 71
    0x200400f00c00046558420300c1c0c4128010104918003e40502071403032003c030020041543e42c2e0410a03130030050280c400103d80300e461140000100c0c090180242149400c0050146242886e601c0400c60503070b400410000d03440c8542c024110362a141002882820740d04d1210740080ea1031045021800e07918003d01c0c00c030411901100030048524130800340c100341d5109080c214220621400418010000150b20854031b60804601c0c10415030040014070a070382c180c0c2d44568601600c40c42d107684e101800e2000400d8800ca8034224400300310041c000d1034011405241101003152261074a000b0f036000060030181c0c4550014a804460404001c0d010040440c02030207030020341ea003003d0700d008040c01061030810b80203aa000a1b06140361010400060f400e401c401c111a0070700140243d40d000840000c42440d1f000c8001042c0a407a10b100c0c441610341040c2c4c0c07000c0581c0e0640d65603000d001c0010300507032003140d101c075400b24040f010392000c0c0c40b20a031040c55403500145800c00051115803000c6606019062 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 888686564 1250 888685314 888685327
    0x60f16151107020108160e1801080c090c030a09020d050609010b100c0309051e28171e010b03120304060c050301081b01170705071103060705070605060301060f0315060b 74
    0x802060f081d610041000680c50f110200c0181941c403800501f480a5201303814a2445c004460010040b40c141ca500e0000c8400b40c45000051048c404d20944201500c41e00c2800003d4010a02d50048580184098415506428150b4030949000400e07030f4200a9030751205420501c0d4107104851071903900062400c2403600300315442c0074020304040d00500380110a018181c10640c0c1a1288840000501500c28148207010140100f041ca000d0001d440c0c12007407000c00000c01c81001401c03003426098600161000c0301038030307107812114605518031000b0b954844a900ba240d40e130074403800038504843c0d240c0503500d00c1e142c0340c540102d07211420704000b03200c02440144004440000d902400c0c0b495061061081240d03000140ca0100114001c01e001d50391500c104030b010340e0322030003a2021911480d8040056036468042580340c0000312565000510140a49000301d0072680119821400c083c000080032a120301003610b000d40b82d5001615880c2e45102300520703200c0315104d07000040c00c4d500d000c1e604105 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 888687814 1250 888686564 888686567
    0x143c040b0a140f06030c0c0c03150a1d101406041503032105101424070c0803030403180f0509071d2e090e06060f161511070201 56
    0x8082c0a034880700344420859600d00d0320b07101ea140041500041030207880303103031010365512a03a1000202c0782d403600512800516030b040c0041d40b280d007880701c2042d40d0400d81c0c1c2c0101e100010140c02d4818148484440341c011190b9030306000000f11620b00c0704003c940e038245030f0319004036144084c1c0700380e000d5860401500da85944c4042e034142620b5140c0303000324804503600c00120804500c030610075042850807041c0121880344a841d0002c49402d070300e0301580281c0400c100510300c002080c000b1803d1150454100f100f407600720081500b41d104400f0513410035215204540381d41c100310380880200d4600320b40091130307000403480100200066204d850a840c203000101d184090090b01c924203000c04035180b084840840802900f0040001e4202c01004008500004071004070350101140c0c00d040c0100703c89001c0c46070028500762400004400e0094a601042c8107290380580003010300d00005014402c544121010503024040c050021150b9007402c0d08011000c581001408030b002070001c02000d40143d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 888689064 1250 888687814 888687829
    0x10c0e03030414120d0c02130203100b090d0b0a020703090f0b04061805120604061b0c080a0c02030a0309030b01091407030c1407030801030b061504143c040b 69
    0x6803c0f800c0540c0500d00918081481d150051465401ca030144a0203103074030a5101080c1e000d014000c07100000301c07986188184c4103e02c0240c0b0840903503c95441c042c49982e06c080300900c00341ea0090701d11100501c1c5900c1c1c8650b0711001791004075078190009000c02c140b5912240c881c02814012150b01c0040d440d0114881551040c1e1003a0b006000381d004c034940c140c80b14840000010400542510124004030840c0e50301c42ca821101160340c0d6203401902c030104d031420389900003600c0b0703261a0303240010103507290f8902c690080e8141c882000000d81203840162020703c85039038400d22949a264040742140344c00054120140c0100c241146002c820028070090803201a41141d41820005140d450004085804206101202220440c00104942059130101c41207049074010781d41d640107900d0715420000e000fa810415100700e0b9800780f009102583c00ca1070b000d00b1200c00202089100d0320401805042000c1207034210712440c00c0102000032100718121a0704400300b003181c0800050787d0602c0081c000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 888690314 1250 888689064 888689069
    0x706050c0d0306060203120a02041502030717040f0e040819080a0e0111030402120a08031302181003031805150414090106051b0106030b0c0a1b0c0b091306080f010c0e030304 76
    0x49501d000040b40c1132642307642c101c038060b08220b070040301020702502c1e01035a2980411400c64000d200104005803061100303040d1026900c08441900c4068900084101c612101400660704480200708074240b01019800d10820800f0a450f070150a16020441c03400712150000e80c01c40590502c008240215403810491342c0c8030390f040301c2c100c0748656912205441c0c40d100280041c5011030000c2401001c5070320080c2a03000d207108440d22051401407801711140c21001ba90100c906c000700c1e03503040c0000790084080700c00319800503d030300300301e150f94500298200070320040548002d403001406000740c0a103003008030810b64041d20111a294034200d17004090b842145881100302d110030310904c0111100f900510021038100418034850b003090021080d06520041801c8082000680032407000344510507910704583c1c10540e103101c0346143c06d03078160841e8000a0040e0b4042080c01e43d121a04402d44075410103804044010a005441e0700714060031500c00144000c00d00062500d8034079256400030440d0b05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 888691564 1250 888690314 888690337
    0xc060a03050106391401050106020105060f0301060305030315131407030e030a0903230a082a0a060203040614101806080c1009170c04050c09090f070e030706050c0d0306060203 77
    0xc0081042c10075071241003980004c500d05e5401c0900006115505400180c020b083c1258540505503029040500302c84092000030225001400041d0b603047d04c42d00100554680a00040003544413049640300b281c40110341c07407100c8a00c100501041c181c0c1407050700035401d03035880150700d000c041d10401f4003003440c40c2c80020040c01c1030500c41c044031020f45030306941c0350300690300b100d2841c9420300d03040c2c0b15500a0440e0451010304401c0d40240c00ca00b24a6029000040d1405484400304c00c0d103c10010350301c01441944c3c17141d2511140043c0d0314540030003610a48030451100745490900e2a003044840341c00c5468402d0070b040680070301c984640800c8500b01450b0460b10b114480d0035401c4d080e503411440e076002d900091100988210280d002051101c111003048500300030907540c1c1141103150f0301841c92103030b82200c440c0c0300140104000c21001783d002102820615a2158039400007441c1201c1e5800c00800180d000c81c2a100e20413041040d188048003900301442003a0074400025600d00840c0d00080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 888692814 1250 888691564 888691667
    0x601090c260613020c010227060d051b030f06030d081501110c030a14060c0a0e040906140711060606030603120f0910211514030c060a03050106 63
    0x488959400041c81030841c1102011340d1210400c010282c001e400c20790040e030b0094140b5800b04441d40c0e83c03582c4111a00780040846041015456041000300301c020940d040314040315403c4e282e1804007101441c805c0584d00420b040d91f00c0c1020500d17082240d0319400381e0910800c5d5040c001100c10504058a2612007032900a00c1c0203403030140b103031404100c8940182c05000741d800407000d101d0401d58684000d14150b0440b07203103407603d000c0d014051003440303500d00c00a402d900044056160580100750304501801c0c01140310714001c1401030300c0c008151002408100790002e41314800d80188841c40c1e015400300c40070303400c500c0c2000100c2d84482e45840d44c2c2100c00000944511081003200c1500c02c11032010709141c040401d8510b020b040705c50b14044900d030b84d0329145440c0142d040b49004c0e072030011200803010840a80b070403100100141071000d20b5540b50160702da690401c0d407200c0c0c2c0076048a440740d0703030041699490140d014100400c600c031000410501c1141c030b40e07034100d1071800d03604030420806e030b046 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 888694064 1250 888692814 888692821
    0x6050303160203010b0d080a1e0e1539010509190f050f0604030801090b03120c07032009010608070c020d020a0b031f080f0c090c070b090601090c26 65
    0x44e004042d40c1200ea03034032110b442046000d00004402810300c003401070303c640c070301e00300c0c1c100740014200b551349940e4001503502d0354812607d080241c411303142514050007482c248002420911301c4015a401504c0010004101e199180703104521007604104a000c000c01550170b1420925071100001e49042c012543c5000e40e0b1410410554400401c0c29000400d80d001a00c8803000281c54a506480940c002202400041005c6089120b91090010014010b00759588440c25100d074507007248401c00710a010b402000000b1940440440300c69030616510344e103844c6149800c2201b0700c1c2d010b8000408106480082040c601d40000760a83c410b1f80488858406241e944002004422603811520713034482c000c0140030710394003104030302181c00c04041610001343d52140c0301c06030349480070002d155480c1d201c80c620011070304114510a8000e4810302649250402c0f50f15450a10312042d20603407002d40c080001009003090500c41c0780f0f0744204619000301c00010030044080000825220b240b260082007010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 888695314 1250 888694064 888694069
    0x90a0e07080307080d050604141303120609090203100203040b040b04050a060e011505030c180a02070c030f05060a090f02090712062304060608010611010b030a080d0f060503031602 79
    0x525004141c900100d90340c0340740914290410360044444031119a0901c00400c1c9589010701034207490000c9110442915500da1610480f011b1140340c003035050000300c2c9108014a900c0d4003400e005000c2d01c01c0d01245907a52407061618200b90400210203161050003484005030b81c400c0140e40081c0c0012191089440b0703401c106040c1400018000c0ca894039194204901c004103401c0200401085040788540960310701c18980c407245401503c583c0304c0784140045c42c00110350048160840c0c000c50005040100565a038048819190402e036100b500c640c00070740401208010050740010241c42c14440b2401035550b4884040c1520710080c8120103c1d0000349610b4401c40c641480c03008116024070901d030b91000c0c00c940d80103103070401292407c0800300b084032500301400380c0012541c1c10399400700242e180107800c90301c855103c49040069500c3e16400907066078104902074100e801442d0040c4c0d24008005c140044452080c0030003a1103041c01401c100990f40802980c3c24195042c600c0c0711801880e100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 888696564 1250 888695314 888695323
    0x509011502030409021b0c010e030d0c060b0607080c1216060b0d0c0e070215060d17130303051207110d0518060d0b03010b060403120507030c12030e1b090a0e 69
    0x400c001a05c045008440182590b034142804c50303044064982e82541d4100458000c0708808120350198003040f4200c44240c130847c0b41c0101d45003e6640002e410078010000b80031548060780503509040301180c1000b60b0b0400f841901b82c8e11001c0e01401c1c0c941128030091040c003444282c40500b115a540149190035112040c2c1d1403499a400000c2c80c045585800d40107030b0358201030b1810001486101c8503542010844000300340901402002c0036424850750303484e038480300070100c4e0703d000300281441055480c014111491000d5842a144c0f543c448100300f105d1044040300601070030130028844c54840c07564001007046441803100e45001541d80031741c402c1300f0540303010600300b540c0c1000001071401700802e42d952000b500c0c0382d411002405026000d0042103280d00403400b001e01070000900400d00c070035010310010324416200c2d00340b0540b80c0390203880b0f40c80c200e22070044510110340c480300d43c04031883d01070040e03958032200c54003602500015040450314047c0020803d10129a4894070201703000b90800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 888697814 1250 888696564 888696569
    0x50d0309031b0c080f030711090601020106080d0e090f01120611040b0417010f11030c0c1513050609070620010e16030b060a030209070e04060905101a0405090115020304 74
    0x2000d68440200c1c5240c000580e078941d01c5005000e001d0f5030132005400e40048211032480fa081201d05100700d88e03103000c202d0102e402038401030566603039810000e80b5140a0010640003201525045e0111240005022268000510f405071203540e030350051108031402e001503284246c104100141c029200b45421409210715001041c02c2c00020a000030340584080c0300e100c0d4030b01800c0090200c0c60540c864241a20414911404004000d1000a9104121101804081c00240116000c0c00b40c0440d4501c4a24000d81d074040d1141c0d48120b01c842800803c122480e0007502c00c50040450030718041c0e00508641407074a81501c0280d10211000001c0025080070012001c808251030141c856864101c03000c05503440219001130344000040e601d8039040744088210707500603040d0860350b130352450b08680d01d9400c0d8551580c0195507200c0032900c0c81c0940b0a00b0f128070900025042d1b801e0420b01003041c1d82c0c4040c080c84a82d80c104200c02e20403612103000b80e90440c1c0411594220040e00c03000305a041d4000c94 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 888699064 1250 888697814 888697847
    0x1140924030f031309060b07020922060b030616120b010512070203030613060303050913020706140106120911150421110103090b07111207050c04050f04050d030903 72
    0x12003150015400100044c206502d4911941058a5982e40980b090700c07081d00c20b036541220148201d0002d81844a6810340c00f50400d198003800528012014441c0c845051050702d410fa5100d02c0013003a0300b010009a60046990f540c42c0280c5116004000d000d030380d500a5004105845005030481130b40284182e070b0700380d010f0244c41c00032898040c4009540c2c2e08115040d038450084611070707042c041094454002940d0b0580d603140e05e88940745e41802001d602900c0c540407216400c200c0000440d0320b034403a04481c180007529109072540341c01d40003031011907030700f0403205401e26115800340010111035003404082030a650140144095250340c50941c0186d601c0321001c81c1c116149800354443c0e201c3c10241e035611070440d88440c01c045000443c00c0380d04000008044103450004180b205000b1032040031003482e100e00700c4403151490190041c41c1c0d048403c0445442d40910302d680721624050103844d5000c0482800c100785072030f00d61240f661343c03d00001c0e0001810f41d1000703060207051203214501c0c508500c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 888700314 1250 888699064 888699073
    0x20a1b0c030c06230d1e1517030403170f0a0c12050f0313030311070c0614032701020c10150803070201080106030b01050702040914060a0e0c0f1906050c01050114092403 74
    0x1840c01d90003d05010140d402135247e50410204003d01e0100a002e8483c0310013000f9420306d8107503600d8070001c0300124400315642000303005098084030810f0050a1800b00c95480a1192880345030000401003402c800c02c0030301c1020304c03441d0340e0182c0034000c3d650b02c1f440840300e41640e1101810143c0003084034000d00001c0000005074034041c0103032050407208480095440d01280c84002038081c5c0070b804186e17100444810901c07010301d044a200c1790f6a420900c0602c00040c038103072201c40c00502e031001e9a52030030807960320740a200e0851031644081d0f500401d0480702451404040d80d0000380398000500490052694039803030a03c6903440f5405494483d80c2c0600100410f940303a080451a40300403c008082c28401d01c0c0004086056034090b030341d002501480100308080043d002c2041c8601c4031040c1c55040941d1003a0229000174001c43c4034001c022a0316500e6507490300300426420f540050300000091020640d104600f40c65440c43c0b01e901007a00304021909090a0f0303038001510b040c1c08142a4980715 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 888701564 1250 888700314 888700361
    0x16140702090f04120f12051504060603150f0e0c180409080702041503030e0609043908070e0d0f05010606020d020d0e03030d020a1b0c030c06230d 64
    0x20b19031460090b4018010f1844220b50f049088840404601400e000546520b401d03a4122030b040e007003117070019440641981c10303d9510010408a0700558400710001e03496020781803044a00681c503801404290b0b45080c0c2c00c0d81400c2a04140b41c0001d4000700d2004800115002101002801c1100ca100010000c2c05a0f2800b8241500b07243c01110003a03202d1442e1017040a10700203181203000440742c0c075484950308103564104002d025001340020641103034840d1410780600b642030090161803203180040c030600003600b402c2040a11080d100e0030003480f0401c0284180960403094180c4042c10441d44031070071032514074280d1041080020003d0031982010404070f4240d4000c0b1790302203042c51503421114000d11003007046800308084030185416400411240e100c9003419002010400f500e0304000760010000c5030500782d04e01c400720781a1100c0600f50410b0003001390384000361005041e40e15240d90721503030408085100200c0e00b43d2505200320300007652000a1115003018620442d0600600c2c2c5070308 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 888702814 1250 888701564 888701581
    0x40303140c031c1d0d0f0c061b080c031009021b0a030e0f040204060801050609030307120e010212040e0712180602070c081203220b040305070c09051614070209 70
    0x50f00e5a415540c0c14240407200241100d1446070103c1390342c2c8030004103800030000c0800c0c0d03111540048100b040040103014540801d04070302030740410454002464013010081e150040a1a401801031700c0c100104000344450071013100c94200685444002c0103941d0003000c14110900842030101c5c900c140509910001455080180c40a22080c103a50301d4510740c100c0d1003041f0480c0300314065240465a03e01c01804142000406007681c0d400180c01c9a14200942d26501a0000f6064290b0b00061005a42e40d40950341800100e00d0b0018490100e0b003040d0030400d40321420000100f04000700b150490f841d0b00d80402c107401100c100358405086000101003410a107002e0350003000f0980f0b40000c407074400a0300c40d1000031100007004903900032a0030754649a0707803d01004055120001e0304010200608040750100c4082d034004c500c01c0d01c98954919440c580400c01c001654402c00029240104004501c41a50b80300c00380b50469241128840d1900114602580217948010750002100e404104094 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 888704064 1250 888702814 888702847
    0x40b060d17120108030a09180906063f030c03021c0504030606080303040b180708060703021b0c060418110a020705011106070509060f091302030106140f040303140c03 73
    0x11002100030b2016070b882d80d40595503441032210f00c5001424200080040c801c102d8001c000e0148407800108220070107031209803d98102342c0103c83c05c40e01a415501c6034843c65055101440c5124100341601c00344041065625a40b2440c00743c18402c9040b1201c0c10140309100000c4982040c034040100302c80c0b040e20042194001e0f01048030f000340303070041c003090750500002075900c5a40e00010902440e9035018180c06a507100c02c241c0e946900c11100013140f458030900c41a40709480d0343c1c0d401a11062000c8c0c01d040d2401e10a450030106410100c000051500c6d524102d5041d00c602503114a103615469011100824140600d035501c16404501d1014881c1d02142c0102241d4099940403480311004042c207483d40019513800c00403540c204210780d41c500b8082c1c0607000c004070300031940d8100310324480440e01c00e502c0c0c00c440c01704003a400401400150b40151002194a00c446541400e00c15608100000341c81a4000902488144076020010005034801c807012103250b80c055984900744d801c4002c404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 888705314 1250 888704064 888704077
    0x1109090a060509011a0a0b18190305101b0e01030506030f0703050c01020d0504080c100306090906140903090d0f020d020303070501051009050c0a030c30050c070b040b060d17 76
    0x240c0790f0070b020000a614020b80000240d070f07c1c240503e0301d01500364088407003920381d406500d500400080040701107103280305061b500940c010400b505108c0c0c0454203040880c2d58841800c6120b101040c45026003540c0701198290981e000c1c00c000481d038543e04002032401c0c01000000c0c007a8890280044104030012844041d0200b003038007100c91680f1304c400d055540780241c0c000d64401c1e0f44265030000552808400c0340302d88540b10b00380050044d40311030216056960b180f0042e00c4203601c4c1e000f182ca07046260821103600c00c130b00c0c4003e1814180700b200012422803101d4405001c145d5013010910a540c2e90b060300b54441030b0300034100c981d12000b915000f4045c2008503174031505901c1c00d40001030005aa80038481c442e424120180d450107000f40025001480a440d07030b9020010078402c5a003281d81d80d551204070300a04010714a501040c00c004003070907140024500c203c40359081c0441030009280c15084c50300158050000100c44d50f41d007020880004c1d9420000d040b000c1100d086154000140b402040c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 888706564 1250 888705314 888705341
    0x90301060303030e0118020d120311030705031f0810020304080c0d020a05010506090708271006030b31031704060212070806090106031503022e0c1109090a06050901 72
    0x8000540c1d503800003000307030b10340d000c0e4210a2001a1000181042d130b45403101027140d04000a1013141e826200c1416002114954042a400400d004080a60f8891540441510000030504608005002d929481d24201c0703007901c80d8011000c01c0c20800c00d82c050703924084002084600001059000030742d50414000b05890951070000810345504056990910518040d180c2030b4080e103c6032004c400e089400b101a2100c000323602c03040302d0b100800344070f41c03101c500c40194081003040c114244000402d101030206400103c0309850340d6a645014100310f12280e03c00341d0464a0880b29040a985000169406140324a030004c06c200c10018994050080380146c8121000c890356443c500fa60740550607164950b21488040041000502c203070004902030310300e03840e9203015640e00d6010910b00c4203441001458803100d40da9040000240c3c0480103445162450440b100020540310203420501c01c4c406c440c000c000c00e000040403200200a1480c043e0f81c0440100a14500324401c4c600038400c03403a5000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 888707814 1250 888706564 888706571
    0x3040501080c28052809080708070311150d02180616060b010e030303040c06030507051c0b010c140705010206090f030d091106120615071a040602090301060303030e01 73
    0x2d4a5044001c140c40303d001c030039036030642c00880351504660300c9401e254009003088000c00a100e02031662500e186001444d80460380e1440f151903002424041691300407920f5a80007ca0420104400140050441e504105002444c43e0b2480100c1c100360640c450580c21500001035402600800350700500a89540e940c01c11070100103e020040e89202d01c040100c100c0704030b400c2d600c01040095000ba4007040050400001c1804010007203070031074004403000d0b108203d000c50200241c5030140209a8000c41c1c03845c2081c81c20080d40400018410695186e05c251075842c1c401c200c040e4025101340b4121900025010000481245220b41e81c0e101809014014066103010480c0904001407441034025030384040d42c00c180c00180d46100800c02003900b901c050b06000d4082004e619414000c062b0002c1c10040c8401c07502d841001d201c543d1100c0d2240000e1064100012800704080c0c00c4250321f144425020101d43c1e495504241020b8050040900d905500c0e0440000c101a01584060301441c8991700a2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 888709064 1250 888707814 888707821
    0x306030c0a05030a110a090e060402270c0708040504110c071e090b03030f03040507091505100f0e040c0f020717060f070327050c0d0809060a050d0207050304050108 72
    0x4450429104040c3c1560041d07070160001080e240d0640141c032005030010a1260b075405e003407425100c0a081d81d44003504820248030550500b640c0801605841c1c400071380700d00c00c00c3c0c03049a020341e02c0148111b000c803e000c04c1c2c0b5000c20030340904483c0108230007042403040c0c0048031042c08c01c2d94032816400d0854401c1c0e40f000030326000445c01d8111a0400d208000000710b2030310310100081e003a07030680142e050000b00011034810340d80b14065401140254020321845042c40355190413500749548852038041905420400b9941f178800280209040346040c4003031015161081c5d4858000c500e04aa0041c1400002000715034802d1003207042782c45507401c4482840d600c0104080180c000d03003401c0c545421060014114010780e040f56038101003580350024140382a0107541ca0010003e00030401d2162400d40f512040c0581004080e808100480d00c03880078204e659503d00c1c1d07074401c50503c1c0340200000700b440441580900190b510035030f41c1600640d45d07400a03151840e2294014007460340440c0d40003020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 888710314 1250 888709064 888709069
    0x90702010e07050607020607020a030f140303060d030e040b2e480602070c080102180108090a050304080313120503091e0429011106060d080417030306030c 68
    0x260988481c200c409416400d0511080c055168000401030360800b0082120b80010303260500317a40e0040d4000c0c07582c1d110003200d0f46804150341d0507000340300c2c05a078803e00031301c1120740c0c484100c558030a905003400c442c18a14440841d01a1007a002c401c0e92060102c0042e8901c01601180040040300fa8413002001504548080c3c0b041600c1c4441c04451401180c1d1004640707181c11a40803030388141d05000780c2c1d03141080188800300010801c040700c3c000d401040000410109510a030301404c02c00001b0350501e440d2040c03108403001da039007055040008070404282c0d04d203401d001101c40c1e103410405a030f039190380340c0c43c1140d41d0740d00050200300989925075000420880c60004400c440d588103018524181c40d1601b00468000c3c1d18101151078081900062625a00c600c0b071418900601e4051003080e4007124034101da52130001c2010b0381070040708000c4030600c03800440e01c1940b0000403149a07100003110708100b2090700580c0c00c0b103041000c1ca000810300d848000006944a55811000c594940240600703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 888711564 1250 888710314 888710321
    0x1817071707030f0332100b07030c030215040f02040b0103060b0720060a0f050d2309070e160c110d0506090c0316170f060c0d0608010b0a12062909070201 67
    0x1c5c0010120545000d5400000500c011250080c6040803168003c1e6241c200d01085039020010860116500d140014101a018411030f41148450100701030103103465101c5100703038078884400a215994900300070101fa8000e510540160090304041a1201c21901c0c002480004240c3d060780341342c07030318403030040240b52010849002910550b07403001110790903074080d51290841e401c020020390b2110000090a0800385403580d0154420702c000c803040c1000070002d400c24409402c074909444441e01084084250400c0b0346000c05000d14001504d0221410442c4205840c040c280798003000608955043c0034001070b070a4050712802d410799500c5c018140c201642d806a03c08001c080c02081c007002c0010180621808800003441d0080c4c81061030540c2890b42440c10440f0303141d0300d4902c0814190100c00061056002800340c0c40d00030454036040d500043c90340350941c45100e000c40c12841c10303d810410705400510500c940101482040c1d800c4e054183c80e01103400241901445803040050201e510501 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 888712814 1250 888711564 888711611
    0x31a0f0315070c0515011d13240c110c010e0a0e0103050c130b010c02011b05010905010f06050109180b1c032a0308360309041817071707030f03 63
    0x44402c10030741f00b0700c06115207148009140c00032100c6007030000000328484020a03c0046000300c03640f0f1070040c50241a1045811410100c801c00000d6086200000e40001e4a5030f0f2804c002d0034408065000000021400441070304400c0c01d02c1d0081000208002d03000444210b0f60000b05c622082c540440c0c000c050480300f12100340d40c001f84071640c411001d54052900e1880d05040a42102c400c2c0042e500c0d046c0c01d68007104401c42d12a9550590b03190301c400c051260710050a0f0034a4500c0e07000d4945000511080164000002c1c580d80e614420160381e81c030041d03a5195821780c0903000c1e982c10603504010388000940c80288182c4590340343c401540c1c014913101c80303600d581d050300d03401410780320030b403070b214030403012048c0c298071803a06c900d00051a980d4500341d00c83c5030465600850340ea081000500c000c1d42c0b40710f0746480c2004407039a5084002010300400114154424601a441e02441c1c1000c500b05070884040d00f54035000001c200301030541c4000070583c0c0b10121b440500503000c0c42500c940c40d40000a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 888714064 1250 888712814 888712829
    0x60708040503061f0e0a0912092402060a0c0905030d120507031b121d010525140a0e061c0501050316030b040203100e0a0b0106031a0f0315070c051501 66
    0x41c0400e005d0000c40c10501a00703c0c5502070300140a00180d030f24480a00080325425001c9000510300704042c810102c1e5210400605140100030b07411a941c01955964028080d00c0e6000c0d25071060f020614414849200140801011150703c011401e5014080410300b15044003540c3c1080000b4840902230b00402600880280b80d48030b80622804040340e18410b03043d50f0700310b860344035145003041c858000d2540540140410000546043c541410b26244018007107c503a452003210300602e415400007000b660100025003180d82d20081810116442400929155480640450a4040b402040003003891041e103024040146980341c800301503484c920070aa0041d182448030702440004c10392441c2035007251000d03003110942c2c8091080c080946500e01130344151a44001904000c1c0800f80840600600f810b0034200b14084406806018481c8005442c2d809402c3c3c0060030381e102d0b00d007003051541c0211100b0301c00000b4105140c000384482a1800e090301c0030720404900e002850419100b040c1201e060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 888715314 1250 888714064 888714121
    0x50109090f080a12050c0a0e030607020303070813060c050406120b0616081b250303080142021203060d03030902060708070b040c060e090414010b06070804050306 71
    0x103640d41c000583c4030200b12020003c9003540c256034141140038040c0540050b600e256164a07500d48000e0146d10304403092031081d070005051190340c6030040f040b00d070861000e1420040a0f0384001101441c07240543c0010b06031490316107076114143e44240504159a902e544220360300402410364401d0341c4c2400c0b8000e50010040084c803242424454807032012034070607000c19040041e40c40140c455083c0507003900d00c0703030341041300100750280711742850503012042a107040f9105030468800800740e5505019165141d1414143d241c05051401085000f960001c8101c941c0c20300c07010074043d10f48210500d4100507202e05041001c0e48080d00041c2c0e403141c080030740003208100e602c0c1c608030050314140205a8000b1410026000031450000044c4080350152401903014141032400c040b9005803980014204284007100e074425681d12110503401c01d4100311440b105001c0c103020540105180c0c022a6030041c00050f0103001c11044601400032150120300355401a60703528000c0704006c000d009185222004d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 888716564 1250 888715314 888715343
    0xf150225051b220501050f0616020d150e071e0b0315040908030408040e010e06130b01050d060e01090510060801090905030723070b19230a1205010909 66
    0x2c00c1c03a920a841c000915040007854203115000242600041421100d80c07241c005000710304002064600050003624034510f400000020404049001e100080c800c040004082003405060499001c00c0781c0e20f400100715001114014680e1740c070b141c0c8600d2080c801403410404500703c82900600484041403081f51651355040810301500200a1815610596a0505002040144000d18810f900c50701940b40d80e5030401c2172078008140140d12002418a00504018035600d0395000603070b0144181e100800d64032585c20060300c040c02540c41840c1800d2a104002558110104545040711056241000b01d9201c0006490700c00c5040c0c000c101c00f040700c54004026145460b4000713032005008500380e034100211581c400c01c0500b107616030042d0154400887c4201110244143d1000f031200074900e600d80043c81010501030b01007407007040c06009040200d00080e0508429811060040406065442c0c0d0380241c090620f111110542c21a50725090000c50381cec4600d0301c910400c1c40d40214221346480c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 888717814 1250 888716564 888716593
    0xa1406060a050415030803010303093303020d0b030f0709051305120310090f050103021201090314070602040806090f061014040507020c030703060c110105060612040f15022505 77
    0x28013600c0d0070342c00315100380e001000c80e540c02d000d540130350302c240d50354510280b622100c4040c044510036001c2090043d9181b8046041842a03200910398441c100983c8500c4480c01344801841e15000700d0b03415000d0301c84000200100070541c00165190030308104080c2d01c071001c400003640b0281c940200940c0c45201c00c40e001207402e2000d16800065481c0e5284840e4960744401c00781c03010002c90300c02003070315180107000b1850560b43d1307136512245c16002005030881e0350311b0080802c032070010307841d158100c0041c40c0c2043c0b05042d01120b02074820b00044030300c68200715072000e69a202c40e088036940c0740544e80c007050015421011000c00c8846891700281c08000020070480100400760404c8203622030504020741d20384050003090000c2d03000d14000130b4404103141d006410448003c0c021341940e40360408028040d903a000c142d03503012202c11a113140556480c0b40c0f094440c00e180c1b00280007102240d0710070100d1100c41d001412120065603114041440310f03c00c60030b50ba0058400203181e901b11102e00208172 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 888719064 1250 888717814 888717821
    0xd0e0306061c08070609031403040c0b0306060c030c060406060519091a0315060112060b030415060b030411101d01031a101707050703020703120e120a1406060a0504 72
    0xa0503911030302c5500540e83d21880c55520039035046941d50786520605007410341141243d080a441c83d0705581c590714240d07031002c0c14805240502901c902c0f020010550036111641911403100b0380404503640d0703401035155030366114400c8500312030040c1404008101801c0c0b410000e90122050044212120704060126001e41150401304801c60030b2440c030312886580070412a82080c82c501c100c0d02450038000b00040c400b210f001801c01d241814903d0810101c4108030443c2e601540115045807001d03440764540024150a80c0551007002000c004d20003400090061401d80c1c00c0121030400810740c0c80d04040d50340428454000003c10428007c10b6020b5000e0b41024a080b0788603140d1102c002900c0b00002e100c4a00c098030b40000841400702d008520300b041d0102504002d240c02d280b8240031803903800079540d00d41d43c08010700840000d8005105180504c500341d0103003800402402c1144a5540000c0c1d540b03e0240041d6403500700c50303910303407000c0c0b001150705401402c0186c6441201d509010912000c2e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 888720314 1250 888719064 888719089
    0xc04060b180d060906020d0c030203013b0705041805040c03061e1a030601092d0e0d0512100b0f0a0c060c180b0301080604150e0d0f020d0e030606 64
    0x80b8072000c080e40b0000f4103a2150240740d5100380001a1206440b00381c20007203d007040000014584100014400700c28031000b8060310b240145041c070804c01194800200c100d9a00124204088000e02071000f926004000341003034035a91940140d05a00024004082c0d071400e807001b5042441d801414000704440b80c0000c000781607010503188010100c5100ca00894125101c00c5290802344901d103280c03481e0034004140181401c4000340050b00f580c0000300c00d0258003070740c102201600420560b0550b8031982248180c412840f068800306860100c0c05080c030703032000e40d04000311140e100010768545814480c44054035007002d4031500b4142107018551490348841ca4000070f1042c16081040012054080d0740d0070380080c0d50b07c035008010300002561042a0035000300e013800340f0a10050080708400141d1542c042e4200d0408a500e5100074043c100078007081d0f10900d0360340100c405040e000c2e90081142c00110000354210b13aa14007030b40e101214054800010254503801c0030340821518a80450301010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 888721564 1250 888720314 888720319
    0x60305090a0b10061214060f011803080723060714070b0114030705150f21040606060806010e06090d02041e090302011b02060612120a030e0c04060b18 66
    0x662100a4a5441a1107003c0303a2004014140110a01403c1d5010141245070940b024040c000c40300d000b4194001d00100600c120301541006000040300c3c0e200350040c0c01081d42d884c80e041c0383ea607200d052010981e844002c064a13001000e03d200b06411030380070203c44404890101078a950784410720f003203441000305041c1c0c046156050180c040400c0540030f01a000f060a442001c454130007000500d800c065a50b80480d20402c202c15454249447d46030841c1c1c402e024818001e603560010191214019240c04001c42190006408110401031164043c009030f50a64688408030f540720001100c001d240c10f18101d80001b81442180d4880c244042100892031000300042411080380703c881008007114a06080d00301c0d11400048240754080c400c40c6886112651a5840500325080c00703969000c025101a00036980d49402c3c4450300018400c03688000c1c80313a0091584c0300303052040180600f80718100040700d030240c880c1c4540c40e840c092196000312000b01622608004005107160078503203810a0294 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 888722814 1250 888721564 888721573
    0x15050a0902271c1403040b0c0d02010207031d040609110a030e060c041215021303140c01050421060c02031806040602061b0f040e040605130c2c0907031a1006030509 72
    0xc13213024092016001070000ca54007507407242140c1800c94609080d0700d00503001d5900c10400750700403d51003800d48400084880420350b0b0119801c2c0032600510940d03000440d103518000d155009800124001c041c060f0050b9400d11101052000068454074240c41c0d580c040c4500300700420a500944d9030301c00c0454001c140545440705540d0100c03060382d001001d10540b1603a100c5050080248150100d50429440c1c1c0040590462200002c0d202e44101d00030203130740445030702401c80c001d0b9285110303188180d40401d00f0b01801e01d070700300c0180da030b90000890000d1440b54444181e40c0e604218055900700e0303110342e0040c40940c0758014110700a100004424405110800010988a020100910080c08000c0e55030111b4034203410003104485000e881d640521102008200205401900c09000d54403908c42d00c8880501607180481110307090507000d42022400e204001032540c000c2099400ca0340600c844825460100e01e00c800440c038112101c1d120307440f0707001080c41860710a80c08194010080d40849 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 888724064 1250 888722814 888722843
    0x303170910090312050106111204140f0402090307030b1608130201080709030c03080406080603030c070b1815120c0708030a1d1501060f0c051015050a0902271c 70
    0x10185c40090700700d10040741c1016801f510501c402c01510740503450003000141420b06000121412000010300d4900c00d60b941e0301005441d0381c031603048a88405005049541d15503413403401e0840341104a60340060008000003070341038240601c002074400c0300440030282900001e0380c0156941d02c0e01610f500204241124080700068100e078000015502600f482601c2d145001c0c00107110760320003004036000350003d1240340c91070000007a01006071980120030a849610384c00d600d85603d120182480c4d8041c0300f100a543c49100381d1340040c96102101010342100359074015040a55215141c8001c00c0200100f000990040d1b940e44040000907051000c03003036003403400300c5061a040070a000b52030640a0380b801041450303000060000040050f041204006059894040e142c000040031620b0040d201c89444142c002d002c0d00300d00203400024481d107111034a491202c0006c0d00640fa406100e80c1c4600c140c00007128800a84141000000b80080c581802510508814041c03100c0c0c1202c0010351900c90 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 888725314 1250 888724064 888724097
    0x30020d110a0206191103062e0521041a07020a0f03021b0f0105040308180619090e061e1306091e0c1b0c0504050c030103031709100903 59
    0xc1286420990040010b420319040a613082c4a46204038500580740641c100400c01c10503003907c4c0e00070381c111580c411701301f18107800041321624201110b000c9541c3e02c691541ca10382200190141114902000c8a10f550040c1c515407d04400d0310040d2541000340c44c01d40d1500a2075880300c1c1d20044600c180d84244040f90b48d84ca02142e04000c0c1100542c0108400b10b0021b0442c00c64521001400c40300030182c09150320000c0c015201d5400094982c00d000107040a8811a5440f034081003070000c0c0080f035451500e4030101c20b0140324041c0d1200001d0100500140301072100c01c425015440081407900c0c00d03c5403c3c00d5500c48210031541079003054400301c150a400f0074601c0b581c80202060900410000d42c0003603104d2980c050034a82c86106403a04800c0780385140e110640c0c2e642c00c8500701000c08001080d0404006900d0941d01c95a0b000341050100114500c1c4a80039504880c4a03489206048020b24555800d40c1c004a8450f50f469200240f03000700c40203c2d401c1307025a6800b9050161302c103907208a5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 888726564 1250 888725314 888725317
    0x320031e030412030309120903020105090d0309181508010615050319050a1505062125020309040b030d0e060a050909130203120304110907171630020d11 67
    0x1800d40210740e44506040c14064200d07c00360300c0303021503d80201c08078210360020f0410b00820070b1150044420100d05000c140c005c500d0030f070103000200540881c0042111940d00500014010751600081c0450700107003074041402640180c1d0700303112011480442c0e400302282d540d0001460066072489440c428120000c0714410180a4031b4006000b190015802e2582144418258000350003410100010b8103446c8265403281d4240e0296140402c040d120004140449030102201000c1c10795241803003001140c0000050020420a64003400900300c107000300b6485002c44038504000c2481b01c0020302151510000074101c000326420a142070501c0c81d000f082e500c450446050940800a41d1900c0c19860204000203400d43d03002e03c101d00c0e600d01540c400d442110800e0344140a00301d51404183e21034020705050901005508031500240380140c0b1919101003810329000101d407020f10441811200343c0b40004000d2200843e11400c101c0c038032a40c000952203101c000d00881d99030760004000305407840 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 888727814 1250 888726564 888726599
    0x403051909060201050709030c0b030402030c090711010b0616030806060d06030c05190b0d11120a14250507080909041b140109050f0117100320031e0304 67
    0x1a80c50700100e082c00300103400c40754050408000c1c0084044c0820014a829a0036400d45466049190700da403643c1c40031905d04064080d1055001d240c10082084580c0d001000c0f0b0000c15114000344010207110050052500c101040480c0c0502d0707020400012034000d140c01074020034090700d194608201a8201c00c00c599040d00100e407000080002040700345049903444a6071203651412008151500454007694841d0024465425032070700c84001d03d143e121002d9070804128125902d9041c0781c50b88a4130000c004040355100a04156404a40c01d8034824032811114190411452001c1c8042d40c0d00780c1daa600301840460300410704016134489034940b41e0003035003d148980782401c501c00c80301044050140b603c0d00041030550001c0111403460703a002000c0c1c0100c1d0f000341e42d04654114800c0040b0340300d50441c1001e03c2800d0680c42880b80c105444190201101e000304015040445180100207800303a440300d45c0ba615034080008030031004100d402c419040c20346182100e1071700c0c1c0da6500f02c0d40c40d90000c8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 888729064 1250 888727814 888727817
    0xf0402030f071e050f100f170f040605071418030304080f070e071b060203190c021e1908090111060907360e1203010b0304050f06011d04030519 63
    0x4030340243c50000000e01c080d01c41110310b80c0790b458041011030f5400a00b207001d4410000569181d0080b2801001801e0342c240c040b01406100d0324003502c0c2c00f201c1d4081034500712811450600080c00151056188080804000d80045d1032310054200079240c00652044d0369516000402000030718100c10032035204a414018041c08230a4034040f05401a40b00050440c3d085c030a0f40001e500e0b2210540b0710402207564020341c0140c5a40ba80352140300c522115039030307401c091450b040b050460303250002812074003840303e440c0c7e10459012660002d900c8861040b804903142c89400a980700184c05200548510f50062518807036410720b1a01240c03410b4030645041031a50050178041c0003092280c1c000140c3c0ca04c5c1d03020000c0000502d541101702c40800d08144481841d911004a0502c1c0c4042c41035140c02d040345003100d5102c4d42c48581e800b50640c4165011070b030034450903606040350840868501d0481d04802065100d140c420701940c0c00d400402001142000f804100801c25241e81c0008944121480e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 888730314 1250 888729064 888729089
    0xf07030302061305060103080d060803070c0e0a06031a0c0909250804030f0f020c030307240504020904060209041433060d0e0c0a0b07050d03140f0402030f07 69
    0x25030a000e42040750151610f665140d454a5030303800314600150702811254080203280c0d599180e008114001c1070240c0010f9200c0c0000101d00c2c0501466400407419030b441210000a41e0b12340505003411507406100051040580c92002c46880000c01b014942c407015048810345005070940c00030b003820604440052187e00c0321055078800c1e040300c4d01c503400001107070f00300680c590400d070f180a040501244c1020741005440401d154910388203000d079400c0c0c40d0b00030b802c6079102e84651400d1090a80c07402c0224449e20b401e00251030408007280141c2d8000c640213400b007440343d12a51192030196010210f0356420503150400300700c007260350500c028412101c25841d110400e00c0684000710304580c501450040c00388030003201130190307507040c1200c40211402100040011540c0d5800f07041107071001c1c54079403003c0d0070100000c3c8071a14400505070740f840350081c2c441c100302c000d40680850320300030010001d15061600081c5440e1a9113140c94019000400712401d10031205101880d0604580011a08006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 888731564 1250 888730314 888730319
    0x30902061e0409060e1e071206080304060e101b080c060a0504022d010e01120e03030601020d0807050421020a080c01030e0109020315190c0f0905030109110f060c0f07 73
    0x415100e45009080030555001d15400c01c03d0030542c4485001401c0014030401e0300c0454001c9009594403011008c0300402404169600e074880c9071a50003601c03988001c00c241000200c000e14050200090082c404d448105016050a00c400040b2070f40f40740c00c8900d00e03004c0022003107800d01007001134860f442010f404030311441c103881406081e0500ca204000ca0003181c07464011100090b5010300703507095003840c0c428035061360358004840b0311451180d5030321110301e0100440c0d500c0e200030004510a800a80840c0d080050360340040b00c2d282c004452a500151090000b4080e00041c5054042511000004c403640120540c001810000b400d5000d450641d0022000d141c0d1541c05004a01e4041404002000141b440d030700031a440380b800c0c0c0708032031901907440000303680d501c0300742e078140006c001c0b46204008154020724040d20030400c1514000108074007000003d00c91605001e4100c002e64802c0e4032400d20702d803130070511000711344012f1410b501c804180510418000100280d050f2100040000c1480c60b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 888732814 1250 888731564 888731579
    0xb0705100b04051501050c1005040f111e0f01030212070906030609020c1510150507020901230f011b0f0c08030405031f1e0f050106081303030902061e04 67
    0x1c10140c0c41038080c074100001c004103ca1821204e0100f03c4081c00e00540d07910801c2da403207003044005c0c810ba103206450a401d100c1806848603010400501c61811501d110b80200104a805034404090181c1e042c0705420003251410194008420708038181000340c2010010030802812a404030341d01b000250a61500304095035250084c80c00501e0a0027086140400c031020640e02c60014640c41809110250046000040e0807004070b17009125207502a21704102059009042342e1000b10180c0c4103410010000c00c440315581c21a860b09664030740c9002081d111a007c1c052507115800b0114144145c09400e20348420040c16161045403042c0100e401d0780c0702529140c1052940f40c5c101189503030040c00300388529100001c501100799401d0002507100d007940c48103603004d099001343c2c2c542c0c00b0b50440d44c040c00b800c055030010900c04903c282c0038080c40c0e807214001c070350b0340008440107000c11280c1410b00021a000740d1024490310300150240c1c5c600b0351178000b070196148641e50003003240300b40010200000c0707 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 888734064 1250 888732814 888732821
    0x170301090b030d14070b0c220e0f06010c0b1b04081020030c0f0405100e130b15210c0c151015030209030f0105090c03031306030e070b070510 62
    0x400c9a003804e80388603102c6000402a030090200013401d0400c400e01103605113040a0503603444040361b240d440d403140ea60340904a00c00390720348200ca04883d00480483c003d6001210b07864454407040e500c203c940c090b5521003001d41040600604c1c0114801500792441025680c0140007074410803006001442030b40d401d10003280c4003c402000841040c04c0002c06004042040343d410801d03004581e030310394605013444803c500c51588082d034004861000038508035001455441080e40803182419106280300d040350503036895140855002004130b10340d0607a051280e014110640045110031044144910045d0004501307660b4044880c1c00881c003403c0e4010100f119940742c1010445410140c01c0c81100c603186090a0302800d00e1141000c5045884640309505444699400a003213a0310f60480b000b04c41c2c02404103645107040c0f40601c40140685040c00800c444501041c610414840e515141003100240000c509941c014028001c2c002010b6800320003509030b9600560152050b0040018480210b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 888735314 1250 888734064 888734083
    0x51e0304020f09070f110a05030d090c08150103020a05030d140d0b1203130b12010501050702220506040b03030901051611030f0d030f1a040e0c04110304050d080c0412170301090b03 79
    0x541d481410704100086e4013201b9130b00c545855410100d0030300c049181c2280c1486141c0c1103400c0a10684000d00e0b80c902c1c1441545040342c0c02516034b40c2801d034442c070a15440c2c021900e2104041200042200c040c0b0450000900c1c04d65a04030000403088024030004051002094000c0341d03030343c03000c40d170505401d8541c004600200581c800c481e103000c4d03107a41441070420051041c2818004041035010964450741c242c100100000720320098500300d8800d000b00280401d44810b40200d02c0d18686c120700c3e0400004951800505071034207030a006070b60050640391031100328100da403100044c0c1807003800c1d1000c00901000441d942c0240400908140c0000d00b101c0460811007003150614116500d0390002c2020583d14401c15900030444102c2c000b0500e1030810384064213500540f8002d9117408200310b980141d4000c510600980e0308025010174104c5035840d0648210f501c1400c100030400c90469418511003040c0d1080d03485c260f42445031000347c0700d1078000740d114109207a121000320b0301c0c51806100b101107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 888736564 1250 888735314 888735347
    0x80109030305090f15070809010213180605030c0f06090406050913110103060501090323060711011107030e2112220f060513090906090c06051e0304020f09070f 70
    0xb03000740300010710721082402608006c1408802408648891800c0d01180c0440e5404d01c41c14100315640d0241d248100d40c65010481c5c03039031a001000c540c514020031a040051002440000ca082c5500200316040d4040c03552a80d205690b0100020952600750401e84030341842d0316050040e04260900e500e40c00c64621070241014941142441642e0f004403070002500d4005a04010b159411042c1c014000104135280102e48504010440c2a55020844036070014a91000380071010004601d010030f07004805006010540006254010742407046802c640103040390100311844004590320350421804048403000c3e0301000134402518544081154480c0c0802615102e4040c0341c038551920303518141c05040108500080e152000d500320b103003042e0180c01000d4003001210751500c2d02600408600e0b0007140c3c40001440c0000b01c0c540110141c41c500c2200740c0d41c1c0102c1c400802e030f02040d07a80c8000c0c03080360b00020721b500d0428141c40e40f80c500c52207180592a030070400c1d4107540c1d0185c03070904102c0d607100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 888737814 1250 888736564 888736573
    0x309031e0201350f0601020106080c090408091906031407021906020310320a0602070302060f0d050a0e010e0a1110140a0e010e0a030506040b060a080109030305090f 72
    0x2401030342d0001080082d4412414019064001c040e8038422503003c510007040d142040005000408005804903030090009800800c20540e0700c0c101e254440c2c029256480d48801508000360100782900c00810b00004002c00c102e41790303044e07950114000141600300000103079a4414403080d09140e5000542c0150681c00145201540541c032101215110303000101215004008540300707008000700040588045840a00901c2e1001002441002e02c0d041135403045034881013240f80741c20303d034100c4010344d40c1c154081c00045045400344040b55000c041100c10403901088a4190400e00c0d100300350240107445008a030500340307010301609403950795001081c1c030740008524000040f9140b11840c0e0405d07003900e05100c010036405055414103040c01c0b0444040c003000500b2024158801d01020ba0030340c00344c980c800c24101070014807001540b2400000c24542c86280400c000ca07514030041c95004c6801441012030355102c00c0c20500359074180d48100e0101b51241c082c040d60030418030040314402ca90074002d2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 888739064 1250 888737814 888737873
    0x90b0a0b12150a080a050604150504020105030c0f0909040f0209010501031104050d0213110c06070504120b09010e0f0f06010504050c04061b02041803020d1103030a0e1009030903 78
    0x2181198010b444800c568100034080c9460f40c0b2411605001002c010301903441502950404584503441180c080b03611480360242c80c81d201195104003030040b034040c0e641ea0b0a50b52001c0340704000d03511208051406a509006150b040e0740e443e2045442281704180d01c503a05000d91051101c0300300c06801c100e051608040882080200c0c0200f41d40413120200c2d0305611840302800482c4850041c450401070240c02c4c04502043ca5507840000c202855101086030460b1b510400100c0f07050140340101d03510741604907621400b0500d21a8010382150002000152100b00442428503003076a142118000d500b1110715803180c101c06003c224010001a103045c0035074900403516421030711803070081b10244002012550030916281c00d81e41403550f030140003004006900c0c030a01007040814407040b0010300c103d502018582d8450103446c3c85a86000000f542103885038418000584140c1501d01c6243c41905401c0694201500070307a030501d8042d890340c5600d00d0450600c0d6401c441c503046407100907019400c50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 888740314 1250 888739064 888739087
    0x15010f020f06160309120504081606020c04020703020114090715030603080702042c0c1e0109090b031f0606020601080304060206010e06060408010203070e01021006030b0103110402040f090b0a0b 85
    0x2d5481440150b19041e10030940c2c105600400500c0806000d0f02c0402c07403a421170641001c020700903552000d048407032511001c2101c440160720790080100580002600c401d035414513070051b0243e2803280c000803440444020800c44020811107600c265503011210403c00407904c4000920540210b00e411f200302815504e50358900c0c465250000c0c052580d9180c100c8080f4424007000d0b0000528000406400b030f45e102905035030f03076042c5410522070302c1c0f40340110404144c520903500b403022041e100c0300700c12031171310110b50300030b0081c0071001c3d41500031000c05e01d10364003c140100841d19822040028401c3c20180002d02d82401608101400d5000b04000c2c40099000a000c60448041c040312a0341d5940d05008141140200d034005012507001106200105400c0481c09014003030030781c00c136801d04203014001c205482c454400034100351218001072010415040c0f4400c2c00840150025182035900c8150450040c01c0d44c0c84503910564503100c5584910b00211440c0091081c08000c50505800303481 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 888741564 1250 888740314 888740323
    0x1020114040212070f080309030118331103040512070c140a030f06091a0c040530060930070c03051c03110712080907030b15010f020f 59
    0x7074401d4500e0410702c0720603d02042444e001d40b089000d005900e0360389141042e90394104000c4c11f840fa508140e11681c0c9070390030041d6015080d40020aa00041c0310103111014810a00c95001181071003100c240c80c7c92030690b000d41d400c8071541c405066901d2810b8201941410907100c51024070304400c00400c00429500b40e43c900a542040e00c0c103c07590034000c00000e041e00007680c80105880c500d81c0c150f0381070121542c4000c590501482c010b40c0a08080404480c41e10300403079180c0d04500c400c0c0000e100a0500140c02c0302c00310f00c08152502c031110400d4200c0d410200400740241268010002c100b05c0079814440881d5502503800080c202c00290391080f801d550358040d030141d001c0c90114001c0c0c02c0c0702400c07808078001e40d0801c0a40c3d0030011101d0051500d00765060031040400d003072040b20303180c120780e900071925010341285050f1000880300a080312803180c040e090380ca0901c203003400400851081d807007141c040d50038070109031004c1028000140c0300b205082c90180075904038403040a0001d10224 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 888742814 1250 888741564 888741571
    0x23030c040e0a021602090a090203100212181209010e12010e07060c0f0303090f0f0309050a27111b031806090906010f050c030409020a0e0603070c03080a0902030d03091101020114 78
    0x4030038503481e941e201f20540040924400103507041c81861940039501a80f680142103900c1e142c1142401c035a20452020381603501c244c02d551003540300b24580d55030001c5007006869941c50500d0200e450b900d410001412100d080002415180d5668003000c481d09000c100702401000c550a1481c000030b203980398501c5889107804042c00303164503051200200f001c02200f0744942984507521003c014058200200b1903459805164011080082c020441c1c0d1408440882c0e1110180d1484402020040e203240241001f00c0c1030f0301003094144120f542c4d05900d04113000710030030748500840d01c3e14054a0b10506e00006640036901500c410485480740d0345542542030f52240007030801c000d0308032250f40110b0b010f115040d80c10902d4080070502084038030392a00103020500c0a036030b920401070140820444075102c1032b03032039070007080070b0075030503000240118a403d502c0800704000003522a6143c000c6411b1a00030070610001030345d201e00700d1042101182c00d20100d04028802008140910a01c500c82048040d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 888744064 1250 888742814 888742819
    0x1030b070903050102071208071110020f07020a060807030b01090518070203160311060604060e1f0506040e071404210606050a170d020d08040323030c040e0a021602 72
    0x40050000da0291441000459011000f15501c3c401030524208003481c1c1c0b505e030070005120402044c0030a00c03444506a4206c0c41501821141d850042000c00950042c000841c00c44000e12004026a4407650924018501078861415600d440c00b8024200d4500b1410b181c14000e02c11814402d83c0c0754883c00046099001c08212107076114108142d203103010b010350380000c3e41c140c1000307041050380c0315580055002410085070385a44a0100300825620380b80940ca8200d0407036000180005140d0401444d0008496800201e09844001040072503200780c21803600072401600b80401142c0c080107a40080441c110940c1c10141080c1c9440000d5601c0480c010071403003012020028444142d210b48010400180b403864907503030b5009441c00c50702c94207650480c9401001141e00100e40080340e80d5584110030390f070300c3c09180e03615501500d00c2203400c0d07150440118100117050b140708440f03009501030710400c400c8981702d6250414008500c0c50040400420a006000169424180880882080d40e04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 888745314 1250 888744064 888744083
    0x50409120e030a0206040b210405031e0c0d030501050f030d120f0230160903020603071205010e101202060702010309050a1709041d10020a170930030103 67
    0x9070000038604007100c04007a500c080001000208203280900405a03032065140080c01c0f508105260f00703c04008840252068101f04800c1580400909030404900d8034420b40c10b04010f1102d04040c43c184914040d1740119580c0c00c010701c41854110040228000100c0040088021440c0c004114030070450300c62a0b46900c40702c002c2503072030482d0140c1f04a0200311000e020003034003162065030841c8002284c0003209520720301003070080440284040140c502030f243c4e1003c40e40f4607400d00419510042000c0200035141001c4107a41c04140036243c02000005001d904c1400c040f107100d1001c01c081d6012407402d080020031100140c44032029283c0268090a001401c0381c000e06045080980542004009030f214104100030802030502402d00da1000b03807070410807003900c0d20540304000209420728803d44c0c80088405507001c1c0a80007007090000a140182008940c120565940c075000c1d94204085d4214064151201c040341952610070441640b0602c1d492000c0d581e855024401804043c0c6100c19 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 888746564 1250 888745314 888745337
    0xa0e06040f09080a0806010503040804120609140c090903040e012c0a0c080109091505040302010b150904050a1e1119080f060603090c010516020303031303030605040912 74
    0x50320740c07209000e60581c94060000b214680703030212080c0c0c0320403a5100400c02c201c001c94a5544075030300b540d12480c4d00401091901d42005d9480f0740000041e407007107900da41c441000c580012500441a01e1044c4484010b01100502d0010070404200091411902e544180000c200c9401c1c1a03000034111020003c0c80c40342c0d41c40b2000b404110301c4c003680c4501c9605c0c01c00014050750010030741c01020381d401540d941841c0d44e40c80e411882c00340d07a15a00054465184201146040e420310b0340100e4000748240000130394064200045030005100d054048494800800d0103510b9040c103020b81984610b000e01c08020394800f0701c043c2192440058009004035903a2504190100c401c2c0342181c0c04843d140080028540b030340712004100306400c91300e01c070394040300c8030100c2c00304d04000c41501d0141d40b0301c0010b030041c10050001141d068004980c080c24400d214a01c01c405610300b80001c42c0a00c0d0ba42400c003080764110300340581500c03050303132140e070107280744ca01ea450102d450302d0b020f90940c810510f000700c1c0504 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 888747814 1250 888746564 888746569
    0xf0105040e1003050f060f070e01080408210c07140c09130f06020d02030402190f05010c111822030c08180301110a0f0302090d0204020703051c0f060b090a0e06 70
    0x2042e0b070700028035910560a00026074200041c807248520340c1c102541c032055480b103000301d034a9552000000d001c28407090210380040c00c158080e10000354540303912050301042c281d030101c3c1c000d0140d070714400c8003500064041c2802242d0481e650880c042900501d50801208042007101030001c0c07003800800d001024000411506012211080d030704140150344078020924000000d60003918100d00c5403000301198040c1898800c04007048400c1c041404035010310300001901d003064007882c01c565940a040ba0385e4415030b21102c00341001c1007000045001132422400a884130005898030003115200e02644800003070f0701182140358207034000351440d1654607150b031180c0030404a1a106905500786140416007103001c1001d010980103503aa0403008051840d003d8040340b107144410b40d00321801c120000c0150509030000c0400903c02d00d00b440c540f51345044241025581c0d90413041240c2e0301c1c0e0207d505c0c05982030207020060300d100200b0910302822140004c00026403031241c000e007100c42100180455 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 888749064 1250 888747814 888747841
    0x110d0503030103030206010f082d010239070803090415080d020d14090d02042f04031106041202040e190b09060f190209040207061d0c0f0105040e 64
    0x45500500312034482d40c5030714010b134403180240200c40401001020014040383c00168068001115110804480c4200c036244041c0c4411900441c449640800001d40000d42507100a05904519001c6444c1c4100c54803c020034100072403441703640382d4881c89080c0243d802c080b0440760700f40c03002c4500060000050008040d138181c964003555041c0106031600e1607080e000301714140310600d6607448000c07180720089225600e0003071003107840d089100e9083e00001130905620460145001031880c8481b001400e108104400b441950308140c560003080804c100110070900100f248011203120741400e0601c07000c1b00c0c0031700060b00c0103441183c85910310310010f42c0a21480c0a06404000e21400585140c1408811003005466915291003601d001403a5078007400300072401a4030140e42c0c2841c1d242c00b150036401a41011040b507500076802c1180300b0001c0e4082c03107007014540c03c90810071000ca070704003080c80c1040b580e89034903030161101129045190781e000040f1415100c40350039070713109a100c482269045 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 888750314 1250 888749064 888749089
    0xb070c0509070f0f09080c011101020c06101401030207082505030a170a0b0619021f0f0f0b0609130603020414061c0201140307020c0a030b07030c1b11 66
    0x3216440040c081c61540c01200412880c14646484d6040b0208003400c841c034040358840d0009507000420245c2e0258810444104040b00040000d41013202801c50f0a0401c101501d00c00070251f1008010000084155602c904180003401c0860030f1198a4666000500c106640c0440d00310420a14110160707200c00024043c98000d81203d80300c84849401400d164112a10742000821060010b41c03072640354080c4410b51000905064148448400d0305c95140610b00420f01c1540586002035554501300300002c81261800030010030a042d0521610085812103040c4c1c200307483c105504d040003501e80f00100c980d8140141c1c0c13000341c14107800c203601009003100d820003076004d404c2a20920001c1d1100700d01314002c2108503290104071121024940c0320741e410701c1c4001c0c0032846a013601d01140024101559201c00c2da4010385a031100840700040000f11903030011240806210240078200d41c2c140701c0d0f4811081242030030301e40406407040310407500340da19500512420144860074007135251007018020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 888751564 1250 888750314 888750319
    0x93d08040b28050c1c0510120804090528020c1b0a2607050111060f0a060b0a0816020706022107020d0809010e1531080c09010815010b070c05 62
    0x4542000c540c00e4800d81d203d100101c2d000205c1e41000e851009041c070610b0300620980d003090740d01c0e921744003e420380d0b606031200c01c0c0c41019081c400000c28424600071039204200403443e0301d550028403101020004803401c54405040d106114000300c41c40d00007000c000300304407040f140a40002c500001124089680c00c08415280002c12081d0f02c590300140301800c0c103c0d010292200c1c81e0f20342004540c0420f038802401c03415030013600810345901c881e42000f07800901810000c00e000703450713a901c4074066000f00180000207642e80100613480b20007141d1079107419154800760020900c3e003600259904e1070b00f208a00e10181101600c00d000c40034004490803242d0150208255000604103c2c44c50b40044c00c00300d01040382d40a03090907502c0d1101150b0502c18404c6c41d41804c00700641c014000505501c4241344441003c1c0d1403620198101c007440000900d05000148050752260091120281d8181e000c00a1944000d44505107081d000c00c003681550a8501c00300d485015500344282d6a0744168400354 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 888752814 1250 888751564 888751571
    0xe0f04060b0c0127050a0f0224070308010f0b040302090c1b030c0f060c07060207051510050312092110060314061008030f093d08040b28 60
    0x10380c901019088084164401041d0040848101c0c0000200a11016000341756800c610a02d1001035910303500f41c0d101c640003401850403500c001c401100c070398010400c8111088408103040d4100b5500450380c80c094101020300c1000540f802070368551500890000910031f113000c400243c2d5043c50501650401d04803041204484c0e00c4c421030641e09c1c4d50124000c4180c6008995120002e000d00140c2907000b403d00950040c5020900d03203072000203400c1036208440c0c601501d0022007000072038000083c000c2003004140f1741ca55181400301841c00c510f656400f40712050911110907180e44000b07102150600080e01c2c1c0146004902c00c06050080e03001c54202c1e003500e010408404d11490080c4028110308010840c0c0441d2100c0c156494121b0300c0344240a10b5600c20825650448103210103441d86440c060f00da41c4441d0020441540b8041c0261080c058410880c800c4c41048034404059540500480c2003815203030416403107286003400001c000030850b000450103081001d0541201031621001d034901003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 888754064 1250 888752814 888752827
    0xd0212130b09070b04090c020a0515010914010302030c1020030a110606030d0f0c0803241c03081b0c1e031201050d0303060b040608010513020a0e0f04060b 68
    0x20103061442025503010001c000021800c2400242002c243c0300c02c400132030f041c0362401e8008800307018040a89000c5002e003101c20000107100b04015007003040107946429140d8104403820b42190040440c2c03500a040c0d4200400158130b0115810000040c00d66499440ba16075410a48041c0d02081640d40b29586000c0c21030495203002c00904811100e03941d89032011104480e0311a40c640090302ca10364150050703042c007000c09008203040d01d0540031604007403107040c500791950055a001110b00d0101400c440b58051014040b1054102c000c0204a03507a0095408129038102402140c0400809024841012941001810201c401d01480f0141d207581c0e00d02171282143e0f1121600000c408419075040d0340c1100349074000c015922003074010311702c15609038646000c02445a103401c1041d41454ac0e6110041071711340134000200040c2c91691910545540341c801030004c41e461600d0684072892051003042c2c8403540c441d1010907000350071038251030b080d98298001001003115030300242c0d02c01f00002c0e55 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 888755314 1250 888754064 888754081
    0x301020a0507110a08070e1f081f060b070507093606020708031603050106022a04180503071101050702060301152139080405030c0d0e09100302150d0212 67
    0x800d2080119a155148884143c8c5400300c0100d024021443e10f0b4000009001e460f41c4020411203000107201008a180790341c940c3c1c4c10800c0d038040030054500e5000100180404841070007900700f85545104c01c002040381101d42205120b01d800b09412500c401400344c817051001a07010350b24050b4200ca40c9a03540e08000003800c0c1080a43d06401e001b090900d0000200310b400424426080001387c902038900d03041400008852401c68110755600c55900c07058880c05520f0385000b200c07075034455030040d682d6060030304011f80710456203400a410040c04001010050319070b5410b81341101d4042c3c0403842d02106502c403e071540070100d920724810800d064030010b079401185d00420141040000207140d4603480c0603004512406840c01c60703020054004120204502c5a48104d45c4640a4415281003544600010f401d05284560310800070701c40c0181c0342ca06141c0002d00a8002c950960520a40c6d45568082510b24283c1889242003640205042da902d440782d40448007071501900140b1214a4030740c40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 888756564 1250 888755314 888755339
    0x14030c190c1a0123031207060618021b031801030c0210050f150913140f01140a0c180927050607030507020601080c0f041e0c0e0301020a0507110a0807 66
    0x113285500c0101c00954900305980d02d40990000c1020b0301604205031841800301c91548102da0071030340a1f544040000d15404040401086107007000809a61814011030b50030a031192181e8a8003140c00401a18040000c415001040c00c202824003090070142c45100f030b400d280700103c0102c0e00310b092000304000502d078200c0031445001c0c00300040008072a810288000010708440d040c1c0b044841c45403640c08550b1062070790360300107015001c8480702d02c6181001c0f400c0d9070056011f400304180d94014000c0c0d00d80707540500050340d0054980604141d000c0b4480c0600b182c00e0344585049107a071841d102c100c6a0090719048110040b00c1410047d2810516000350364140c101c0d000000649801d0100c1d01ca5440030030514126244040200b415a040c0303000c04c081d103a043d1014a80c0030740c1e90002070350400703a45844070290348002c0f007000034480740c10b4030081c3c10b000c070b00c6808a02c240d20400107050003079001402d864106800c480040020448040403503e818000d0300115980d11510400103000c440551 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 888757814 1250 888756564 888756569
    0x2070302100201020a12050406091b06030515100e0f03120c06010e010b070314090907080702151608060316030c1d0709030b132114030c190c1a01 64
    0x440e590728424003481c00301d080780a90b003c000c0010360f042c0d500c0c02e008151034010b550068011038001410350260f540d1400d1890000c500701c010f400440204015664042c8505540116030036114410604400009150a03107468800800d221602042d0b0516848d12445800e4041000d001c0360002c40d0408400c000a41203880004504c0c0700e0034001207440c0380b110448a048a83c500201403d144041d54107407041d2807040d2a09000340f2003032020b20515a40d1403a41805000251074060560420441c000d082090705900030302110054418032a0600d81c28002a02542c91487c0c542c6450b21064006818004c00c6114a100005000d50100901c050b601c04039003142c2520405080f400c605105500010000b100c00c20b020038158030040001c10240f504040c0c0c060703503002902c40c1686081c0e0301d002c682c5241d00c201d25540c80d90303180c545e5501034100d10300d43d00b10702d14001d8082c10351070486501c140c0343c4200300384074141c1d2458403180b40d806400355500c1c41c5015446266144160140300c5101030440092 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 888759064 1250 888757814 888757819
    0x506030705120a02090f010f051303060605090f040c05120a020402040e0603071508060114070b0405061b03010f170a0c1202010f030c0909051503010e0a0201020705010f05041a0c0a0302070302 84
    0x4149400c3d014421103140c0100070b0003140f1840150401517480c01211041241804010006550403d820030b40e040051407060301d0014903207041000b0300c14004c0004091154480e0103000f848003007800c00c0500000ca400885101910304004032000d818468030942c020b4004d400880c0100310180b164001502c9118254111040740760341e1207410801d1100c1e22042c03008100b507000420a03a52068840410f00e49034034640da0f1820500b55500640f504c0103c8094a42381c001d041404440710b00c006880800d40040d81030f09080d541800740c4841540018850b00e04c00b20b03100030000c50f00d01c1e0140141c00c40d194010030160405640c0f444e2410007011888012800290391180e0150854046d2242204c0792201e9920340b2015400d040e581c00c001d01028107804c51501092203240941c0d6800d010360750380340d940c3d180075042c02c07503403031001903d401e840d80c0120341888440d03807504400c207a002c400c0e0fa08403074000c6100713507407800600083c000a101d10322100c4040c7c01200b100b0300c00c0c190001440720480e8400d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 888760314 1250 888759064 888759097
    0xf010915051f2a0b06010c02031009061107150209030f0312040c0e0702100b040b040c05041406041532130b04061d0f0a17060c030105090a02130506030705 68
    0x3d00b5100200840d91030386a1401260802407804180302d030002681c80501030402c4014840d140d00000c1c500780003001c1011030507443d801008200f100034019459183c1c042c1d01d400b824040c407a618401d01c0c98011402d202240d50205074030981d55401c000d02100d10703000e04181e0741d513422040020704541004a90580d803002803102d0014042d030407008041d11510499010b41f00020701d0140d10405031041c03844590b0b10548985180144d95564820302c09800180c0e21205d69861410310001e04031242641c1c0144a1a400e002c00c00c41d10071200103d4030800081e2800950041009580300c105113149a801004082c6000c0e0703503181c2201d59401800c0e106494a0070382003240d50344500c402036105602881c0300185010089031281c0013024540741d07003218024074a010707080a280c0032514164a55005c900005400e00300d801d81c40d002844407c0d00b00e0340d00480d640c82c660506022418190018080e8000242d0014803808020300c16800c103400740c03000403d2543ea03400c12200084c02500081c4040d1170700c0341d8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 888761564 1250 888760314 888760337
    0x1090e10051c170f0a0309150c050904061508040206070327051c1101050706110c0102070c0906051e1305070806030d0c0f12021f0c11060f010915051f 66
    0x60f01c400f500c0f5124041c0c01464502845140120050000c200c070444043c5000c01c41c0082c5462a402082c000f54081d5450f5900c440c403880c00c002c160f80ca0350380101c60300542d84103442480c682c04080141d0007034050701c6c080da99000a15045404c1818007207642031107a1310700c0045118107038011001c0100d850031a1326100481d0140c040590303103a4800c0000b0200503407204c0d291041c0d401400a004120301030340c80010b8000354074200e411359034050072600d0596540003030280d04000458403250040d1400d00390407c2401e083c1008200342c0c2004940024801400c4a80f000c402c3d500c0b410b412000e280d070503800f4803040c185400090f10541e419502607110b4080d5180c07034141c03a40304038000002180c10415000d004130781600c0d511280c0100015400841c00354421448020111144d09005034118940010781e803950410300901c90880940b401c80c0d203801c203100b070080005983c441141514920300002503175855401031440f1440499101c142c0001601d0301480042c0100311006100101c141c903201c00c40f83e03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 888762814 1250 888761564 888761603
    0x60903030b010f030e0c01080c0d0e0705030f16050402030a06030525050411120408120f01031a01150e060c0d03021201090b0319051603080d060501080601090e10051c 73
    0x17501c0c40440740303a69000c0000c2e00c1040d071040070070030381140458070280d1411041c4810700060701d0040394112895070003c00d00300a98201002000e100050840c0a040c4118454218180c41d9110f403045d940711316008004140308540c6544140700455019040710740740510340c0501410f0941540b945080a007190100091904107070141c01a40480441041d03d0070511561101040340c02a2094034941030038041b0080c0c2c051201d0321180581004070207841c3c0c039071452800d036183d58240001c000c2d4547c180300041044240c4013102d03000012207424180e8101040d030011820074054079021042c1845943c1d407600d11941c040d03005184140c481c14403000541e0f00d98000c0304c191525441c1c00c03900f66200400114500d0702038003103100240e2040c801d89a0407220358160101d2040150010b580c04540050700704064406445200000d110070700705286a0710708a00060200100d900c10340812920b980000390340c139001c81c09110090013000b00109240c442640824948103c00a021103565440340d41c03510440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 888764064 1250 888762814 888762821
    0x140105010f051315030c080a0b13020d0b0a0e070f050a08030c0a080309011e0c021b0a090c0212030408041a181002010b1e010e3703060903030b010f03 66
    0x1a080600303070256003222015043c0c01002804409000c0303001841000c4009100c5c1c0d140c880003440c0704002001c0f0010541001056242c0160460030f40090b600300240042e141d6002444485400c0003c3d410640c6d10b581c08400900076098030150b150241c88008503a000911603203000303231803098411080f810345440a581d503030b00c00c46101070034684c044400040051001401140c3c0000b50707100200f02e280c041c1a04070b924500003250391400c0c64642a0361110107504021107081c4901591144420750a2000450703c0649540151480c0a8517020342c900d440d0300070808141024401410140d4901d00350034005980c0d0424010295449140101c2c0e241194450040e02c140e41c2ca01d201e41c1040b1400102004082c420b150341490940d52144100c1c5142d540d0f8100c102128500c03488120100c200e070600050000310050100740c825402140d03080540c00340380343c01208000031541c5400b01ca00e500602581076240c0d592000b000641056070480406606070001c401e540400c1e02c42243c02c600012042d01503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 888765314 1250 888764064 888764069
    0xa0509161406131827170a050405190510140a0509310c02120702060702010e030d02031e0403080d0b0120012c061303120207140105010f 60
    0x164501042440396103441c0c2c0007090010b030080103503028969925213048100d814016140091a95484a003020701d900f024600115104010203401816559440c824aa01800c01050030007002082e510202401901250003906004011030b0003100e24034514031601e20b181c007510f400382082e4080410401d0045e1178001c10700d03808040460802d06581003c80d616081034521503808000100c0801044100800c1e02d02c0200800c210100b01502c00314204043c0c0742a54110002c550002e101d480b10865140181c0300b07041c1d4101d50300c0e1764a484a000480b201c4105680c0e4942c07500500044034103981c4c00100030003070502456116540d0b03035059804c001490207036100182072000708004c61f03210303e04582d0080d0b00218050520902000100e20544c1f00d18002d1803480895a41d030741c4003843c0520201241742e100e07000000c07003108010b84084c2026140e0704068102088007141d4107601041500840401e0081178000302c0c115210380c0c0500384458204000c3c0540002c039403800001081141600c26100709 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 888766564 1250 888765314 888765329
    0xb04020a0807080c0403140f0c010504051003050604110301060c03080a140403030203100b180111060105010c020904031b03030501050906090105100f020f10020307080a0513110301140a050916 84
    0x90b039403102800c2e079611100030041c0310b203044100320210000e902d8403001800da00d407038030007800150903040d9268981420104154140300e0280400c0207a980d4104d424600740515160200d800c3d101c0c4004580070306007080c0d10041d030400200000c00d456501c48810810350b4087c1d030781c3c4ca90700c0e11241b0b0003404803014008181007424141c40050042402500211307000010352040707a803841c2d9243e007141c9042d0000b0010400081c55250f0110310713582d002d0f241c07046d2141100040c0059515000002c0c2c00c200048000a0040b02e0000000342030601400700c0401059820340d4003826085289002802040240a5188608440c1c4003040741403c3c0042ca072030503104090703c503030100f82c90001d003602e00c0813401358810210712a10164062040c000d001c510781c412502600561a405c0c58032011f00f20081c000c22201c1a00d181c80104a11051901880040103410000300e84e40203d1170380120780984928a5420615036914051110384185940003d209a0382e51042d100c0a800300440350500301c015100311031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 888767814 1250 888766564 888766577
    0xc070302040b0609150c100b1023071505180a0b10050312031015050d0f0b0405040c030302010e0d0e040b1c08030a18030c260f030103060b04020a 64
    0x1030601d944040518a0010499400d00800c3d40c00140c15010705250100b0801020804120f0110104416007041c094841d040c07111700928800b00d200e08010344220750404c19a00b604181051120245403804905040066611826410b0140c0729281c10840c83d411140303807000003082d101806da208211010100d003e00030405060b07c90316032103500600306640b0210101710001c0c00e80e4040000d0b0b6211b0703545480381d644901e400d1001c2074100340f0680c0012141d02140540b41c0f03665a11200711204540c801800003203419410300701c03900818001c43d80d550058a85024413003444108414001140c0c40380c0d000f801424427400d459920b031005010310b01c000c24080c000f200b249103090b40244444510151000c140e04a444403a29000c1c3d6170700c01c4c180c0701c0420002c10700150401902640059003428820304241e01500e540040416981080140c66140f003a1120310303442011018501c210b103900d00940c0e40351400110500b42981c428402100c80c149401e41d10000c5040c13074000e452999415850380b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 888769064 1250 888767814 888767819
    0xf0603021207082d060310060302031002180d2003161205121209070602031611190803090a0f0503060105010507030c1209181a040f09120806090c0c07 66
    0x640d03d481c000f42102941400040c100c401419150340b9024014010702d0358042181018000d150030183c0c405c1914007003900b400d00a10168800040c3c00c1c1407260301e42e20059644408a0f00340c80c20314031410340164000300d662408414000c1e5060480320003850000c0c140a030b103040320205541e0705680611805481410181044181001000b030341d009400b60064a4041038100307142c9044da03001814100d2005800c00a05c6480300d000c01c4183d01070a0310740011454000c10701d8415600c898400c60050200b822064011241d0301c034000e0088600281d0160b10110319100c2c001e070342d101d4000400d4640164803250b800940c40e0f000320f44038000c0300c401902800c002d900700001180d0079440f4500a0b41400100700b41500000d1111a24111143e0b00f5600c4820007828840d2881c04d160790404801c18950520071180110241c0c001c0014103208221740000e0602010042c0e0000b0b890b801c44081c0020800c40038400009030018280f5205103003c41e00a8070075a2000c440318054000c04246000580c84001e00f03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 888770314 1250 888769064 888769067
    0xe010501051e030c100309052e0209030a0c030c090f02251a040f021c02031e12040e101a0f0313151a0a0509040b06061b06010f0603021207 61
    0x1d01d10000400f83c103481040c5120008a03d00354640d0700c20304002596031a00e8010b010741440340d400c01e0384030302000c0340d07804070f0301c054008102081c03407600301e945039001562403820f03501042014003090340080c1d40c0582965038204803a9a10851259050442c00e081c2c849512084610850703200380900b125041c803a8507180742c14010695180410bc1704005946842d081949502003010300c110b10620610010300740b284180a0b100c6000c00000c3c081e600044482c60060b94040b40d4542c240800030110a41249140103031460048034000324a00c00b0740c0000c0100b0918840c183c180e00c19a10704510a0b0000d554201d140c072a0002d0055103409070100380a400304507031b01c0500964120350b0700e0054030040d54407500d41851a820116485810711b58650003803182d1100c000020301c80000494481c40420b10b0309020859445009000504d000b0280e4001406540c40d0301c02c0c0d452800d422140b03054030240400200ba0748120a00070460000d44906002820510900072511503141d1000c4208031a00c80540 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 888771564 1250 888770314 888770359
    0xd0c1203051c06060327111f020c0307080c0307030305130f0602060a05070305060607020105161a1f0b0415030e032a07030330060e0a0e01050105 64
    0x12020004204906460041c05142011009021031400500c1d94a041c030b01174100c81c00090751491807001c00483c1101068001012814160030050082e80c40c04c49030005404004848480c17142c6004040f4892403465000030a85041c185c1034049910960b01c494080b90741e940d420380c619a042e4418601800001e21880140c0f0428803121001100d40703445011030b6442090366003144005074000400c1144d8040f440c0581a0052882d0400300a0360030b111f8042071452007000000f07410304c00c4c0003d408a8a0b111111140d04a40e001460a0382c1305524000304280088141d454850b40d8500d2000b81c001c2e4602130b81c100c400c490029562500e0140351070400b0110b505504241400c0c15940d1015190411041c8000c2146480c0744984086280e1040c802c0d0094001c09401c030b00c4150321141d4144002600283c140c402410114820b03100d102e100194420f42c0f5003031004a50f80c039410174000140560010100c140210036490b0b0611001b8200307210182200c001344102940b04011060254000c0003082 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 888772814 1250 888771564 888771599
    0x1d01051c021903051c120c0207121506030b1e090604110d020301090c06143109020a0815121e07090212011e12060f062c060d0c 56
    0x1038094401e241e49403600c604110170702c540715503502d00c5c2884050049500c03050414050480e000200b0520a140d034009586c0d03030441c003c02c20307640544562101445002064008a00c828280500c2205e44a18200070b981d00140d5400026042c002c2d0540d2501a200b200745214081c1c0e02c0c000c101c0390b0b54030b0301d4000504000d051060b40124500e1292005a1400c0c003964810901500042070a1440c0c0980102081c042d00158001b02d80c0c1449044104945062070228651010036101c912042000780c4102c4e42c00c05600c44c0500610000f81d40c00700c6500100303401c1c861618440c040751408034900610400380507441d45d01304180c004540180a007000760034403001d403049180c11078a01d181c03203a0340e403000c9920034010148480038807401001050f401e951680454012080d448407850314012410b00c1040664500410f8240c58161001c1e103191158024001444880c1210f440c1c018072080401880003040844176082441900181041c2070804c402d042280d441001001c1140c40c014802c1080301641 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 888774064 1250 888772814 888772849
    0xc0604060815180a0c020c06040605030a05070302090a0806040b060603010321020c0a03030e1c0c12020d0b0a2c1b04060905090303100f062a0209011d01051c02 70
    0x614099a1440442d80f03614030449030158000b80c0030383c03050b030042e182c1a070020916106038020402806143d030301c103003500d4000380b009001041a440e0000290040d0281c6e6145a800c60354100002501e280001191030142c1c0c00340c450019140c59040900003d8402404064221900ea0b0221010608107001b0304103c054640705071340e48100944005112001241e10990000764000844011440c1c0400a036140c5401c1c00706e100c407101da1641c0c8d500709090b10752141d8229008401040c0d829925244d002c810441e0780294401c40c076290002c00d0000501c0c00b14400468103c8500100f0312514600c030740d40041030341080080030420442c8148550500d200c2034103903001511000002464425800703020b0003515044080d58491a080d1004000345c81241e000d015501c10003034040140c142c1007001481070b0b41207014102240080b012680c000c48a04e400029001a036140c0000f03410214016085828488411190401d0343c0c0c81d004c100481c40c01f42c201c44e55500280f5420350052504109444078003144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 888775314 1250 888774064 888774079
    0xb0d15141b07020a050a17100b0f011404091509050702010e1f0b210609072102030f100e07080a080a0804020d0501050c091819020307090504090809030c0604060815 72
    0x105d20105142d052946c2c0a00c5a00400a501c059a01c00600011f0b07980d0f51a00c0381000401c240000050720b101c1850041814071003000e8400c62005c4038801281e0190030300c0b00044c070005103100c1030911003400c20300c17603011a24034110202c1c486510600440302403140c0c02000705030407041259a10410100c41a02040f039903030300c207446540c40d1236040d84290a500d044100c95401003100804904060000f05094490b41004900b802014055000ba5507249968074808008480a1010901e0042429403041c014841c0010413026100e50b5000380051039030240555010315034030940c642e55815240c400420515061102d89449440380b140c4503807090000300714002c4035100d0b851341401c40d00700b9207a902c29402c0004420165040100c0340500780708095800d680c2c80e19108040070091141d0b810b4810000741c0000c0810022440381d06d004010b000020810030200d07410f032521400c0c940c4101c1c030950090192f01102d03081403500c0019901140c08646a4100d2a5140741152444c141b006a1182e4030204 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 888776564 1250 888775314 888775319
    0x60406050a120b07090308070602030a09060509011506030606090b07020315041a0f041a2d09010e060c1903020403060c08060301151202040504060b0d15141b07020a 72
    0x101c0e0000100240300003481107049451900300300b403401c41c005000509201c4885000c000185420040318403060308078a0050303c2c0d4817100c0c880c0024181044000d4600c909080500c1038003a41075100b50100003840354101c485560b500303400e8040e10a54841c0d080880c0800e60100083d042400081c01114801000e0b40c000e400c2000c10080b826106940942c1c0c201d44101d0b454400b80588040c0c10b40040480380d07c0076107864107545010101c01c0c48104c1004005102000c0303140300380d880c081c482c190064404009501d00c0e0a0700a10f41072801100c1000c0607608004044814003400300741d0134000e412060000d450189514504064003000c0c81a82c3c0070183e0802c00040820b1141c425504000c1080e030b107803a19030800c0b804041c2036030002003680410f03941d1101d0401c068801048060031195050354003244a554a0800c17400400507803640d1a00044184110001c002e90585101d040007180e00c0208446107403a01001c0b083d1500f101e26442441c045074000c03403001490700290020510013001c40340101d8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 888777814 1250 888776564 888776569
    0x606150412150606090f0503150403050703030e0609030715061a0c0f101a090921090a080a120903080301060c1b1701110f0d05060619020604020907020d020a06020306040605 76
    0x10f42640c4120f0010303150704c005026114107100707000010310b003c600130126605110701c403000a510240c03004082c03100000348882014081c1d0003041040300c2c00c2044da0254a00444180d403a45c0c08074000716450307116490100606412032088100355211081c1440400201d8981e950083d48110b81c40e0510b44541e0380d4819104d4402c121403419180b5880000c101c51445521112401601481c294440d0341d1042c10019900c000007039010642d00140310b1003040e0442d1108031410351103220f0080340c010070082008107400f04009105524188504005072101ea40718804444186040c04002e02c90f0714200010888140304e05e1010941900814108010601d90908214468010f9001011032101000d105005c20000e10540700d10114814001c0d02e02100a644151544070b8480c0d401c403031a80d1080840c101751a02c9090350402c0000111004003082e11200c0a562000101d80491107102e01c0c50006002900c007240185108410b1f40041c299070059940e02006500000d00154000c1d541d0300c3c0009155 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 888779064 1250 888777814 888777821
    0x40902010525032d0e01030b030102030a0903090f060206062116031b0e0a090503040503060103300c0b0a0e240105010806010c030806040f050117060615041215 70
    0x41d01410b140d030044409180240110482d103210724044d001c18456086091400a003003200e624181c41c0a11110140c0340060700101000308103150950b02c04400c00c11950704a80c4240e000c2406a20707242c40043e5282c4540396064600e001c0c1d0001078102502051301401c0c80e9940300442c01c40c1c1c80c00a102c000d1802403861400d81180a0a40c60180c2d08100f0400c1c1301d040b8404440039080e1106541e169420282907c4049501522081070243d039900018107101c014400e440c040c5c41c004080e80d0f0196900d0030441d101c1c00403002c680c44c443ca591041040320031b500c000810031054060711008200d1089413141c0f03048100041c4003000c4142c40e000c1d0204030b12002d101040010010903c1c40c4802c005c000202c0c2031300c00c4142c000d0b5043c07001010901245a802040d40c103407031540b502d024600c1d942c4038808107000d0403840c01110a46401c02c000410207080c0c000c120b0140d602a0022a0712070303903038142000144e004644102168a804100900c5007500500a86000a0086220345250b8803945800002c9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 888780314 1250 888779064 888779107
    0x1e0313150518190f021203030c180910060302070f39060905060a111b030c04140a0b0109081b120319051c0c08010807051e0409020105 59
    0x1032503940d01c20001072024032441e60440040c582c00a10141840c406900c00000c0f01c44005030444070000d512104558a0910130780d4031940b4030003900d40340d0800b02d041010503003208442e403484d5000000320391042d040c07480a03a03119030601240c40418a2070072500382c0c000e50040c0000e550781c2076100d0342c64022a031590805400446010031303170150064a2110003059200e07a2030480c1c030508102a04001c110b0303220a4007810794004980340caa54140c1c0c20405d90781051145402502c60252450141140401e4440c0070001c103400c1c1c0035128800d01da081084202c69105030160898541500171803031211441d4442910300f8018140000d01d0f80c0c0741c10031503180000484040880b202144200d14190900804200b61060818015802d001c2d000031202e500342c010141000801c000400c803010820406070100c052103000000420004110001c0205100e50034000c05071140304101000869003008004485070030860420003501641d41d1081002402a03550300b40d040090034000c0100300c03180204900381 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 888781564 1250 888780314 888780353
    0x16030e01141612021309020a0207080601060903120806100f0212041707080601030803060910030210080f011205070b09030a0c1701110703020309010c05070906091d031e0313 76
    0x22941c66410b00203101c00e0304040c01c0810b80e40140406200d01c40101c0c43c0c607040d101d5140e005030710b0740581e42e0128502035103035016015900c600000042c2e1507810907189419240149038004070400c40070800d640c084420345507240c002640c00901098284a0003454405003a207206840391b070303c607640c20170340207800507048070b60301401c0e40c540010704001c10401c407801007101c00050040f40d80345803140c2556010042c12030b03018503134500010b40301100700300e00400650340c02020070400480030b44008041a00c22142c1940a80c03031783c4000320700e17a046807160480056100000b068800d00303214072204160403c0c44215014402c0d540b04500080400c60458084d1580301c000182840c007181101d0709450403401c110f2041c5c40d0820144c03000c6035010045400503202801e040c2e203036610515089180004541c00050042d291640124817403856411540d0880c0c0c05007115a00c1c03d004407005900c2e41f05038000203000b50603046a80100741c1024000d5940054000e441d101c03042400d8442d14400644c1c0084801c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 888782814 1250 888781564 888781591
    0x150203030a15120b09010204090203090d030c1e030f0e0d0c11060a0504052101050901140f0609011e120609150608072913050a0b0316030e0114 63
    0x1541c075126100d803840c42e5098840300041c1524003510748000b40498607018000d0000d040000382500c001350104c40042c18850002c565a00d00102e0054030740c0c0141207900006410300301803251152268154840084660b400414049507000e415801004803400840301340b038540404082509090014900d00c8840f0748413141d8a02840ca0604120100b81d00e245110300018004120581e0307211041c2c4d4140d403015102c00310b029140040f00ca445070780442c0400e0740d0b5800c200410080c00010340105000c404402800c01c0d05440d048c03080010100100d84141d04140014010020214030b0010341c0704882c89000b64007230261710f52021380c0c4a10380a2005172801d0ba280d00b0010f0401000b068240926400440c040100900b08a43c158842c0e5143c40303416030f07203003052403980800006136803a501c542d000791011a0b0388454084d50202800440e100340c901c45c0e100030900140c12410f0008403481080030040c1c038a81c0c01d000c107109400030300c1e0021742800c071590f8400ca4940304e0703008003d040d40103142c400c0f00074 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 888784064 1250 888782814 888782821
    0x609030203030103150c2a121d0901030b0a1d07030506160507020109060e031609050a050f09030a0c14030d0509010f020903070b0a0e0a0f081504020906090703020415020303 76
    0x1e0000d54001c1c518441e140c500f082c46010940d020504401030000c400c0815001171007d80800510020020080c100c1c4260f02c0b0552202e98002a0010762140201780c04800d6001000400503007560921000c0e02d1000000c000076046d0a1079030005800c1204004020041e12034000c420b0f15180c15500210b815034040c0f070500000340400000320f08010110b19220385008401d60008000d00710520400040c03024064541c003180e070702402070b0042a05084003507001d440d43c40301500d0180400381d940c880c0380c81c50480030500a60749200c426105440e80c0000310b152600005045403200c00701d4200b5200c100100350500c0039224184000d01c0381d0407007050081054101800406c1c01c4981502c8011031240c030401210b0150346020840b0002c039130348041010f46942070749006a509100c2984055804100401d011581d080288500004c0d501d07031a0459070250300f032204e4028494026200a58801c01d0300e40018090b18000700420780c80075051a0260900351f56009001d600400791a400000d41c1021080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 888785314 1250 888784064 888784073
    0x20d0803090c031b1309032304091803090315110c0f01110307020d030e011104180b040203010b03010b0d110406020f1903080c03071704030302070317071d0d0609030203030103 77
    0x2041102c04d0a002c04041c02044100003030f6843c440102c90001040e01d070300c1c0308800e1501401c983c808008010341821541d080003094442958481d006886045d4501800a403a20300c201d168504210f81c59202d0000d100e08544540f59812803070005010b019407108000410f2310885c0016292810f03512004101e804000c24043d0f0a5414510050b80c1890b028000c00681d10343c0003031011980e94460900003006200c80f10b11a0141c81c441d0090b40892070000743c0058105001d04180031400c0f0805c5080000d0140e4508100a0384030038860340114000c10b1005001d180c0d000b40090540307081e803020000340c408a42034031030a9074026030b10103400b50300301504110070b010041c080d030341c11b68851902418448445940c09400d10001604131b680008020000410030380c02045207403030804200122419514141c0b030002d0180d4401d0074202c00091910119480b20904101028001c81007070300c0d00e040c0103403040804c51520074984c0c1800da1001213505000d0100302c49100e005c0056000c0e50181d5030300d6041d81030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 888786564 1250 888785314 888785323
    0xb0105040e15061002240414070302011403090102130e010f0803161b091b110c0a03060f180602091215010b0304030921030e04150b0304020d0803090c03 67
    0x121001c241c00104148a281d4800d84940341c2c0081c0448022000b006a504100d103009a41c680b40000c892142046894103030705042003501c201d1049080442d41c45c60141c83d0303900d58007580b00080c089282102c2c80310060040202560344004001700041c180304909900e1100f601840c2d00c4010b04d0003d00c00103004581c90501b045001e004028011032a02140c038088141001503034030060441814182d000342d421142d605000f005024000d824490300c084001c2d21039840707800c00f178081c000c01c2c640c07008200c0031440030a4414038154001c043d403d2841c61a10307000040c0c02500800080d4664070a081401100c1d0740c04d0740c002c3c0398001c0e03030016102c6116409104601a81e0496294160701109021201070801c06000781036400303865000f0f440307440300d01d81960031034041d80010009950710038220f00c0c9118288241c909040c001d0f50341140140d43e03801440100d604001d0f071903442c000c0d10b807014003503500154021038019201403e584140c2d0555104d04195810a1313036040e5880d01300250900c0035140800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 888787814 1250 888786564 888786581
    0x5070f02100b010e0d02061e0d0c0c0506160207150903050c18130813090e1204080c010518030a030f0314060f01080a0603060c0e040f060506070f080d06030b010504 72
    0x34104410b48500d80007803c3c0c030240102079446203407a141c420046446500a44491103035a14400150f400d005040b8122500040c4451148078607140101c84010320400305a000ca540180140000c0d0300d4802d40303c0d000501204010b401d52044000000e29070b0003031411410115420b913140c20a15007145813641c200109100d500d445941c640c0b081c0014841c030701c0402c0e500b14a48180d243e00d6a10245000007060084414400a100c0090300000c0d002c0c0c103580007070b205603041d081030742e90848407041c16013124001c038001e180450340000c04513440c95002d83d000f000341d80e41c1c24881086118040cad0019103000e94482c0121b00191503040406200364040c021040301c100d18052160780b0b89840400b0030521803280501d241000030036004600e00c138540c2c5d4409030107940c00003000e05c5201e8040c40d021b0300070980b800005005d689480304464201b8800d100700b03002c0d6500240460300d040c00b152503140382040b11300b1003907515004c1008000102c005601ca254010743c0303c5c041c540c13040c2d85058108822141c142 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 888789064 1250 888787814 888787843
    0x609050f070215072a0501050f0405070611030c031305031e0c010c14010f23040f020d230c180f0c030a1d01150f0305070b03071205070f02 61
    0x2018855100c2e000700f02c585005040b4010000c06a640810458881340011100848080890884215040903203146419940030710020310494490b00300b1500103480485001e403050f0046035041c820a032051704c01024401500302100d00345010100030900b235034003a44607a03d46d0000818200035600703041c44805500c800710110f15502c2e0000e1403000362101800b042040c10841b03030400000801c901d40c007000400b5543d510081100101c3c0c610b0300c1000f000005540ba100b507860b24000900c4004e9100000c0c0f2450b8400040d40c01d031007043d030900a030095510811640c06011004188588014600380d052004180000340864020b04091001880d80003e41c1c0c020782482104201c0048080384140c2d411450240d0310036035035a95030380f452000f4400000306144903000044603200590054000c0c54030201d403903000514056032f6088014220140340700c0100150003071041000750403040d0001d564090550f007003154242c141084202c04881040b0741d0800803030000085e9800c22a410055101140700c41c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 888790314 1250 888789064 888789091
    0x40512030705030a020906040803191409300f07180507051b0313080604021c0f080c1c0503090706020f19080c030a0c14061302010c020f1201060905 65
    0x1e4500104a80b0009044004c082d1300002c2e40035150f122501154010001142a01e40368404240000a40801420000002025503c070a541c4000c00001c0342c0080000030801e5100e503200c0781f001d284400040303003000e0114544030002240060280700c0394084d041c985018082481c2481804084c4d95030010400711510710b1b01c3c0c03c11000507004421a071b50300700c100000c0070301845184a07072072540c8100024801e1603e074100001034419800580079008034400c07036001c07140030849060b185004a140c0005005030742010399030400704e00c1c882c00528080070b600c01a0303800f040c40300c03202c1d4031070b248445840c0c80029000410826045014030490015055500c040d014090401c58290790ba070014194000c01c50800c0c0345407000f049411b00454201d0400e01d001d1b80d40320a0f60a101503c40405540c2c03c0d00c0503034dc4c0c0440203d0a01c0040340c007901c40e01e122100d500800c0419001103840780c11071841242c02041080c46481141da40e0001a40344014800021a05a00301605c92007500c0d000341101000689 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 888791564 1250 888790314 888790321
    0x1107050607270303080421110606270415061d062d040f050a0b010f02010c14030a1811030106210f1502220803070308150307030b0901020304051203 65
    0x900003204411031381c16103049002910340c1c0c20818001490160705401c0408000c1d40484801d4001140c42d5066440c08255446c2d80d9500d000e0042405200110501111184940c2106465820182500140160b5500b505640c0f40d9500130101e85150f04103650880d0a84550b41c5640a48c00c0c5840e400203080d00d1040042e84c045400070000c00c40d9044841d000412542d50002c2501c4a50051240c030480140500c02d41c00c00a01c504000e0038590300301c5000480c1e000c12485041c1c0140610b140d540c6107540c41303074200d0910f258425015040a88815192525045072800d103c121040781780c1228098021610040180c100309401c4983c190b000c40b0070300020b00c210003011504203258140340c940180c02020b990b940ca14200c1c0d0258603500c02c0c40c3d40c0c2c62010903a10f00c03010100c10700e0358800040202c069400350f101d480a80c0e4034001d1990050001b181080021849000030039915001701025049603915512a622140c04072403c503550700e8141c4d4080200404c1c400c00f0040c040d0030581302d0401500d90304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 888792814 1250 888791564 888791627
    0x3150504230601030906021303051c080f130203060a32010e06190308130906080a021e100503040209060913030507020d080301030308090f0106051309061107050607 72
    0x40380340108a20700e44048000608690003a08100c0720941d100c4411581c90700324882824140c2c44901041e1406d204030800d52000107010256031464030a20348460700c0035540e000f00c0b501000c40c010440a4400c3c0280d03400001030320108155800381c02c0071000481c40640298000b0140c09029003070210622000030306005000b90708242d141520304030003505495684000100c1c44000c100d060380c24009030000c0b000814003012001410001c4807401005a4a6640b0840401610401d00905186400004d00e80005281400c4207000000d20500c0d0001810200c074000b8001d02102640c120204800204110451820030f1740241c0c0100e080f223200320503013072080d0200242860507200505000340000c87e00300307560305d00c02e280310035590142050b6542d68403894010031035113090700c24400920840c1301c0e09880000600440c016241c02820048e0069040348010029140510080c0c0c1c407243c0c1c882599400f191200c0081001a0040000300054104143c009081060010510340240c0b041c2520403200c6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 888794064 1250 888792814 888792851
    0x20a180b071104060506030723073809010f0b0a03050303011703040506030114130504020f0d03050405040e0304030209010911030c0d0f0507080109150b07120c1203150504 75
    0x41e0b81200c2c4080e107039aa84404200140401c1c0c02c40c96100d44c010040200007540075191400060056440c011700ba1103100084c1074900402000401c1d039880750310075000c0c03c420a4a00381d900c1500183e03002c002c090f6020304001141099401110340c2c0d443e044801c083c3c1c0907030b010340481103400352501c0d41e1240c034603181e0a450340418050f00c036003501e005c02001840b120030410b450141034002c5c1032583e81e5039030b032207000c0d0039046581d041030140007202c25000010105109640c8115005401034420682c02d0080080380650380c0d800310240300e4140000f085585403441250414071002004650ba50b0450041005000b4140d10520800f810890141c000c600458107498010022030401c0e911000c0c281e03c40d0001c3c2009100074200146410b040200140e40303d84002d040340c000400800802031145c861040081072800340c01d0f140c9004020140008860210b4510405050b1602101030b8103555201d03c1c00c9121030042c0d2000a8540340040d100004140303501000b800c0c101c0782048107203001001e41c19413 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 888795314 1250 888794064 888794077
    0x110c18011403070e3610054b04050c09090d05071106191e02030a140307020a050a0804031509021f0203040f0806040b0a091a15040501060201020a180b 66
    0x354180980701420030314090740d21003003040751524031081d8581c4005640741d88041e00307107102d40543e04000101d41d500c110180340b04004004204442c0064041203441c119000c80300204411103508c00d94040005142e11074181d008920590113415580200410440d207030b8400740503084280c00506500f4030b215000000c480001d5132040400c00e5072a20b03100010b0190203942c100d07a02451200e40301e5000c1680c440c125002080c0c6452581f890200c070804200c2e034902609501b6004078a00320700d0f400e020100c40e0b0141d81d01820600c101c4001107400d44d5010b0400c018102d0860b94a0000319040c410001c500e46101c80c01c20f01d000041040c022a500000e00c40e9106021940340607480f10303082540d0b01e00c2401103401900091a400b0740a0f513842710740b90346c0c400381102c0640301c40300e03840049021500c40740100c08105400c850101c058100411851102d0000a000c06a6038030031801c40b0855502c4a0090900a0055400060b1910000c000182c04204a05040c82080c01a82d505101413010241030310720 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 888796564 1250 888795314 888795331
    0x173403030e0307030602030c0310060206190207050a0c0b07060606080c0a0807021203070f02190206070b070c0609230f2104080a051c081303110c18011403070e 70
    0x1c088a81d00403e040c1455500060000da00001c20000042904001035010b840c0d80b00075aa002c540d682400c03030700d544040c0e42c13544000101c80420b06c15510113401030b0070b1075801130094982c15a065501c00881c2c82c03c91744842c41c071400c0031030804284041442588001d10a50600042901d840034140040c1e2080e0003141d018404158040340c00c0e14401c01c540050003101c4640c2c0c6513682003584c1d003c3d10ba060b00100b02c4005109100d00b95071107040030b000f880c110703941c050300541c103040785030381c1d000074481c2c00422a0701000b070b4500e00c8202080c030324012110264080c8101391070300700c03d030300b500341a400001021203e60790200344e2100303101c00002114000f44410200400341d81881100303400c5140b05551200f0805e21841d005801802800704030070003903410350351400d450034801c41c005031010001207d4011800304c140300988046401800144241001d41041d00d41e408928130018030888003101000703081400010052061000344da4001e01c8045040700245801c4d03207002802c00311401e00806421 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 888797814 1250 888796564 888796577
    0x100203281b1407050724170112050f0d030207121112130e01170c0d030e01030c09030206030411011103070f020f03070e01031b0504060b07020103110417340303 70
    0x2c2016924800d440b4600c1d0300c1802e5620942c1d070307a22003401d1b441c0c202550700e070346600c20390850044034011982c0315030206051402000c00d0780b800c2d202003e2500b44d0321f4180d0705800746400c01d500010041c000b03100b014600d901e00580314010340c2000b100c1340e0f94030041c01c0248410703030710149203018001828084820000402568501d0030340c080a08800c0550310100d0003020340d070300100c1d034801d440a48500c50421070045030582020762040002c5d0a00040025000c1010310848018652182e000a41140c4681c1007801042d5560390109580360704c1100d00b40d8103011490080741d440e41c1e000d52000484070156000307600309242a103c41001120000c0000e20902d1541140029620248501d00007000b149072070150b15a501e04050148480c0041d011400c40e80700e43c0e001c40c0ca031a251090a0a8500c90b80c9585c0c14001a0b83c01034009044140c904182000c0c10305c07001a0304003a0280008890651002400b848003122200c050301d091600120071108556000c000080c0280c140d00b1011241c0514159 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 888799064 1250 888797814 888797837
    0x607020f12010b03030f03061e060409022b020c010e060709050402070c050d0f03020609033a0f0905060a1a1c050d090302030f060702030a050705100203281b 69
    0x1540144090aa070315054040402d4145584c01b0010285110301020755880c0741c850301000841020f00d0140415a40c404810311050000001650190100c2400d112500c1d03580c808071845032070464041d8880704400703070300003d06800d40c20081c000c5620708410040205402d081c13285001c1c01d0801c0d01c0c0282030143d0342c0403d5420502260724168001040c020b002402401440d0501d0100c4070310800d8268094401c12001c15403440000003100c1d002c0e03808285d120000044d105039001c2030100d40406890714070003000b0324407000340548504a81c4e144a0240014604001c0c40c15030b0820704010098051907141c4001800f070f8016000c554074400c5d004030303004010030000428418010501c1c80c0042c200d445003698081d58590440d583c0d0099038000c904850802c191405555076802e400c851500040c1c10074849601003074012005050894424800c1c3c500b986059400302d012070700202d5041d01220251551802e9442c586103100b00400701a0000b4020146c100001074000102c0c0111b1a04101c440c480e00c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 888800314 1250 888799064 888799099
    0x3030a0b010e04050a09170901050a0c0201030e06091c05090a0303080408040e16092111060c0a06150b070c0b03220b01050102060601030e0715052110050607020f 71
    0xd00710044000c20070030132814484181c4008100a000031903044c0103841c804020101d0100550b1040c000c1652030301d141401f40d18048440c501e00d04c804a0502d91619048034105200348030140c414503070308000305510051001500e041c00920348860003482020040c45005441d90006142500d40505040306d2680b55403900485a00c0346501c4007001038400c0c400d02503000f01a02034404a22401d0751141141501ca00c20f922052850718107004503000107641000010702d02d000c6030108094024000c0c0e0030140c40300082da0800d0301424084401a560740c40701410448d00c42c218101916102c0300603030030000c2540e541c010117001406030b440040e0020001640d41a43d2030f1207480f4001c1c0e102895001c0f4200d910348100b0340c1000f8000d50703000d03018000c0002d240f94428403500c0c0c41d1640c210010005145003800c1e40b8420300c00b492200e020441d0401c04a8540a640710300203041c2c40c84400c3c003a0702890001c0d0390040401c0203400552250070100304500150b910794960355a101d02c1100d01c4dc0201c8004401c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 888801564 1250 888800314 888800327
    0x405060c031c02041d130b06042309010606020a02010212031b0c0307052104050d02040b0301020a180b0403030e1c0203060712050c0f1608040f0f03120801060203030a0b01 75
    0x400d11060380c20309074981c6020b1a40280007190000c4401a00000c200303601007004c200704507144040400d000d0001d0340421007140350103820040c0030308001030a00c512025004407448100c0000c4111a0b45000d00c65030400912070701c00107101501c007420040a07079500003900c1d035180645805010b200400405c081c256120b4031a1443c000c8403a40603a140b00e500605500e9400c090300035686400b400c0c2440c101c151124500044109050803040e2500c0c0c00c1904001c4020032500302a40c0183e03480c0801c03461610301f440145464005070310740c114000c80d41140d082c080d8625030004e0451145c1400104001b0b034014444141d41b94080f41d01c034800101091000d491414041c0c0040e40c1846404140000349411422100d29010b40c04410310060b65010810400c4d031207000040f411701070040008038804000740c010100000e00c034020040c075156559410150b01c0304641c000c4c0c00c88880c440c008008105422460307101c41c0c102410b08825030b43c9040c10294a038000103002c0140d8030380f20030209110303070710818 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 888802814 1250 888801564 888801577
    0x150b150a1e030e01050f010f091107060905070e0a0b0918030c070905070306060c0f0b100e010306140a05040308181e0a03032d0b12010203040506070906030903050405060c03 76
    0x7409100c80522200c0010090001d00c04000c185518280c0825140c90545500c14180c0e285a00080211894401518000d000100442c94a007005003e0140010640d000d81803050f4011030003852040c0c20110120318a450160461050724640b0345800e00a450708640a0fa002c2c1c1e4035071034110549150b8240c46d056109500741503200b8040c0100114103404a0740c00360b40114203555040014a880348016920100002c6015101d0b2071a03c449400182d0020002035003e0424200d07140d2007551048521900c04082c4c204442ea01d45030110b50101815512580740d010081001c140001e007025140a402480050139007003101140300120301840604208210072400380301403249158112860080d290081e490003180001d041c841c0c6004140040d04000740002c1045003d203c02240c0002520000e200c10075009401c1100410300089045003072028500c214080e0010344040d18020500404812079030b000705003070619101504002c0b9900c0810355003035900640f0750980c0c07100440d102034614044e09 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 888804064 1250 888802814 888802847
    0x11130330409050d08130b04260a09060807030504020d02040e1905011506081009020d11160c38090d0c180b010f0e041b0507150b150a 59
    0x18610810480002034130140a02d103950390b2401500c800d18590740c11001c2950140c80072005001207070124182c51502c401c40c100410000c1c3c01c100c001e2981d1400c0344c00c40c01c0d03044085900900c04001c0c040c1c02c0450300d5400083c40c5400c00c040d18080d400141c035009d0003040139019542e54104150081c0c42000f04446801003080c204010300441e1800b640600420318540515140c20000020285d008025041c00b80381c03100d511560080c10b01102000030f410001c0c6202405440701d9107901813202842c02020303074240000d2190007010980c1008618060f55521030004c01c04100c0036440124481540460b441c04201240c051880810302c06004a000b03203d0069030052100c0340c403c08001e0880e8944045948203840030010000041300340c000c0b5aa4905100d010840741c0e501b000003140f00e0a01c907650904000c4c40010f00300c0c0d9100c91880e455010302915000700b28001144002c0c001040405a4141d44a0009011341568040461850910a0407201d40c1c010f000c5422030f400c0b0700034041a00f0100d0744 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 888805314 1250 888804064 888804071
    0xf0f0e07031d010e0f0a0b130507181b0c111c05060a0617014b0e16030507050f06040b0304061a031605010503090111303304 55
    0xc90703018000c04d4004c010620320700c00c0c035980c6000c1004c04541a4007864000707a0003c0b165480c200389018075043c01c01c00f21140c0c02200000718035503041c2c500f003030480041a580082c4010180511107200350b11030402c03d081c0041510030900203024140202403120094922003003254455009845041081400406034021102000b10b581666801181222101181806040c3c02d03d030080c1d089a601340e0b0501040e40f03040d4400507600d04c820f2410400081504450019801c10050800c1c01d911200038203030030582c079101e2900b02202c3c100a52415080540c0402f8656441c5540b55607862403184035071801103260190011941d600c2805440c010210401e0b825602c0c0340502d08400200700850042c0f451a40600000301d0b0b50500040d0780c10403084800250118505020055410b5040103080c1d080ca076480d0105c02245d0010716020340b0308803034110841480049003000314040320100f100040304004000c010400c108203070f24880031603408a410110090f09402d00e41e1800d455440004a800070b09 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 888806564 1250 888805314 888805361
    0x108150c0c104d0918130c08032503050702150a090f0e04030c020f0312090a060f0203180d02040501180b030601060509092703030109060f0f0e0703 65
    0x4083d074110360302e401850604000c0004140002c403802c140210314040284601e0203920b8056030400038106544010081380700c000030707040d03180c401080c110f0300c445400c44c1c081d5080e42000500302021024203c540701444c205107001640ca0300c443c41c0e2654424680c0341c049800340c00d060240b411200829000340140c42000701c12100c00300e8a41c03144084800213801800001641c00039080c0391015508509800320f01901c441d1002c44004140e00d4003641c1c003140907040c1141541c3c04100c03446850780304007a19601e4054032410000300c41c045600c454103020f003280040305515404422150510f56104071a0800c074015408220f84180e0040002e40082c600000440c1c1c044c02e40e0128100c8180309441800840d00301c1c4103040d00c0700e13000c0c4200c402040003840216900d20380400c5066025840f11505241881440550755610b0402c1005040c03640000005100990183c001c0c80040c000c89072200314501c1c54403090040715112445010000031140c00424070452094000e0ba90b4013501811202c0c0403031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 888807814 1250 888806564 888806591
    0x30907080d0f0c080901030605132c06041209030c0b0304060c0f0207090b060d230a0905100905101e06054f060e0108150c0c10 56
    0x1a401504064411464a0900036200b000c1c001000c8180d695091070512440e40c840c1d40c2074002c0702c0318506040e1100c00c00300d010707140c46a100440c0555030070042910604081c0706900702c87c1c00011008210b0b404094071070f40100008a454000d54804090184900c132b0f03003070850f08100a50070041042c80408000680000400082c601582c0500c1c0c0400021340b00c0c0303c0648041d00610a840050b800041c2c08020003440341d03104500d1800013400c2c80f40360222020b0020708480503150915400012103208410f08207410800c2640f000410200300144101615120742e00e0942941241c412911803400c0701c1004414007010580e0348002c80c0c14002048660381d0047c0f000c03000d10603031500514008001aa82c608018607405109a800e07000003206103103280092181d807183c1e5600742d100c1c9403d80f5544046805100c45d010199503500006905d03003010010307580e5980c1a4800801030344101d100e40500314018840c0c903004280e0428160b511061419090f00701040c00d20a0841245052090320415 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 888809064 1250 888807814 888807823
    0x91e0c0a090207033207051501050d080d050c070203150108120405010c1202010b060d050f0717070e0f06070b090c03070f030b0712050a020a0306060e01050d150b0309 73
    0x55800322848040c250300ca91114040303000714003000e000100207000d052243c203d6007012101c1d695042c0c00314500c80d2000c0b8000d01c45544a20002c0307942354094429002c2c0d01310300d103450b9805010304031034420041055440b010b586001340003208102c5943c500119846003800c0c4220350603260b01400342c0d01c51180c50395030b00f480c1c1d800074811005a170284c544e8000e6400d90180c1220191a8161a0b1458800071900ca50600f03100e07109241040d50350f1005060041e03525600074060451740104081900e2526000d040c56441c030181104007809100340f0f4243c41d15000c6c201003944010a407600305610101d00d00001d03101305400311519044500003c0f0901400509071038103110704042e0742142c0b6040c400c441403580d510b00d00c2c456480302091851061000414045001d03170003c0c91803500c41410351100705900c0840707c056602d15402e03030f07000a6103030485415000d0340c0000d0190342000322214011a00285c03a034460110480d60007a40c5000c802c0c0b0900c01c5c005860080c005001110343c40b807800c0d0302e9496a9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 888810314 1250 888809064 888809083
    0x7020a020f0319030809030f12091501050a050103091a0703020d0b0f011b1419060b090f01050d06092901080a080a0509031e07061701140603091e 64
    0xd00d10700090120386082c001445404030b0b10700c0e844148000c00549003212201d0010385090081d0100300301c90660140703101c000e003401c2d10f000b42401ca46c41c10b00d00750841c9047c040c4e1a1004280c8540301c010051940d5a0340000204c5400f030030041600c240624010304082c21032410751002d03000240901c8450b55059010303144040440d02d0420460541c0b03402c01491003400b850b0240004c9a4151010706d008180002c2c1c66260310035180308092012401c035003400d18030b500c10881c0c090100c003101802801083d0040d48e0000e5826580d100b018244400d00c0c81003c10b05001721030160000d50310302010450709078404208140c100014807244820800c1c40d48404000102070880c40000600126082e40e020407a903a5a540c403440c82032400c0951a420369094204191a580c14050910061721940406140b042e0304030030140501034950034298050015503903880811544031004005000c114416041c5070304130344d01250500d469640300701d401440c7c4840c18034401c040441003103622444280026140c1e20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 888811564 1250 888810314 888810319
    0xb030a18060605121c1812080a080f060132070b04020a050a121101090e0a092d0b2a0a02070e040203211b0c0909010209060a0f0c0b07020a02 62
    0x34400c03419466039a039504003900caa10380e0070034070584120766025440a4440d803034146c400801241e40d401d004503844402c0d0100383e800250000d031045126910513901c0d0ba110310a80c4401c4100d05210300002c204d0030000010980c1c07507203c0e101d914150407035541a20862880c03d18082d6483c8403a140c1914981c000303440c1240500401c14000c9018a8030541c0035099804203d0203180110030340e12400078089204100606101c00e80740c0115020342c260007141c0c820a410340c03020030f0308880c91602e40503003d101c0b10300c104c05001071000510340003071581e8070340003864000c0c08541c201d40b1000001c5001c20050302e0820044000030600d04202e000c542c0c054924a4020380036214000c0d074a0104608480040304c00940c150452039400109210000c060035245888540c41800d01c03000c11303000100c41944452a0040e0303804541611050301e0080c04481d40841d4bc1c00095061090b4400800e440d405050002d006100d00d05005004051050f64101402030b0825081c5005040031036020791030b8402520140e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 888812814 1250 888811564 888811579
    0x1052527060504090c020a05030f160f0f0b2a1c020a0906020609070509010b030a11031005041b202a010314310503030f07080a0c05040b030a18060605 66
    0x100002e00200b440001f50390090061450142c0c01c00941e0190b500108402d100c0b041500c0001000c03520701c4002c000c0b120b101d1072084040d0029400c00708942e00c0e0040c0aa241e0300c40405d0407180100109281c40317015101c9880050f00c480c0c086a580601c410702025607a03409101003a501c549582c8108030030201d5a00e03400b039804540700c1060254a84400d8011030b60012080390041040034045001581e03c0224070034002200380210904842030b51095a80d48008002e41e6400e1025180c14801c03070641d00c041411445510340e540e24007030800002e8100045181c4050101d80017024024080c82e81c0c00c80300c80640c102110b45c1d500790000c04054032074015000928165841e00803400640340d0368052060000c48c1080b43c00240d110005814041c008182c9d40022242183c000840401c05540039013454a204002d03131421103030040107003d00070700c41c48401d810800f50500f02c58110703044406444020910590320780e6004201d5001d084a01e0142402510004841050190319072140090340e00456859 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 888814064 1250 888812814 888812831
    0x207060509030a11030c061801020c2b020f06130314130906050613231e0114070f0201080408070b09070806011203050f0a030b150c0105252706050409 66
    0x15070366030041001040306c5a00200104104100b0318010030003208052002615042005800350700301006040c44030060211002200300301c2c07054522410500103244010a4051101c50495640c0d41010b0074030303c65604228002c005251003515552800301e0100801a9100103030914091a0440b520880e072a441ca80813011940303203001b070200c801e16603402c8000c2200c2c6040c003420301541d003640300d101e0203200d13403500c1e00441580f20101c1d026406a48240c1e18814031501034000740070300075440e031510403034a020031018002402d015201501c9640a18081180350b881e460001c0580c40f0b20781001e0700c80060300d01040004000020b04205403a14041075030140c1e43e0b61074101200041c0c02c2c0008020039803e11464200402200143c410310b402d51a000c900000d20f1404126060006480b0f0b012030311002031491141c040900030a50802600220115400304810000e03207031105808403001000850440d44c8060b0070b0410b4030112520758142c00903061503a40c440980350b680248550000b10f41024542d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 888815314 1250 888814064 888814097
    0x3050307030c0318030b0417090d030c0c090504020901090905071221050a0c150f11040f0e0103121d03030301090c110307031e031e1a0415050103020903010207060509030a 75
    0x41c50300720b03a030041c40d842050300c80f6034230300442d040d0922001c0000708003030003030501d156030350b040c420303e030301d000e515503007080348040c10060a10416500184295401c0005220041c0c8030485030354110360b0041c0c0009401402403400904007011540b000c0e2400c0041d0ba8002d01748054101d52a100d4803c200000e100c0f404c01e1102590b080c0100c1e11140d02140c42080442e01140c0d40402550340f14411481c002825101015043c0c01c0354201e0303403000b400c0031000c142400b48400e18610003000c0c00e075030307582c8040c40e614581d40c4104502e018101c140800081008201002d080000d29801450300181502d03265a104c0d1004002000545685000110080b0540100c030001000f00c40300150075555480c401003407800c01c090325454005540c2d041550710318140c699441c030520410103010042c02c01084030340e505060054600c804901441c0304519044100c3c01d071060480d51003045076400e08015840355041400030740280900352000d844c213401c0904101c075002001c002010240c6003a19481e01a50f401580c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 888816564 1250 888815314 888815357
    0x606010201200a170108071505030103080702010c0206090d210329030a0b040b1005040b03070501080a0f020c0303271f1d0601080f0a0c05060d0603050307030c03 71
    0x340c0b203101800d41c02c4000c150058014410600181070110b45002c080035000d00140c4242d008550031f4001810610500c641e01e1403240341d041241c0f80540c115411925a4101e900c0b821030000e040c0500407821204648401080e1031150030018003040444000b030a014a952011a1030307013801c0f404040305040901d0192080c1d070240f510710400c030f0754054101e0540b00d0311000044051985842141803010018004030012032040d8400c1c001da1549042422050101d04050b4110920a5042600852060301c000038600c3c2150000d00c0c040c0c0007078441141c500d000700584a03105034000d00018004518040c00801903000380c80c55004a505080484401d25048076180d0980c0c1a0b50404040310388030b0340c654411004c1c640a08180011162400c0d00c8a0b05003000001d44c4110580100b801001103540501480c010302e41c4580c05080750130b0440c0d41d1b80a480000c1d0141e0b521801c4046026500c00d074007035100384051640f04003125a68012810041c0c0352007080d5800300c0004030951603210002d2040d80 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 888817814 1250 888816564 888816581
    0x30111040308071401020f13150509030a060f020c030703030b0310180605150618100f0203090d0809040203010618150806010503130219030b01211403041805090606010201 75
    0x107002d94200b14440e80c6030080c083c9800d8000c1c49940d020311064589440080080850711442000b034a00549061041505070340f02c0c80c44601030000501440450f41c40103c0c0324030790542c1c00840003502d0001140900001c0c020342e600090944000b0420500300f41d0594080c0c01420002c400f01c0d0000c120000c02c441c103641c940b03001c01d02410325510350000040c101d40c00554020621900f813105507144034011842e160441c0152007445210b40180400a040c03061400f9452007480c50701c8070107038840010213503903031042e42d8003240100b01d8400f50741d0601089206070b03441c8a50082003503550703503512500180003002d03841540d4100c0074003460000302e50701002c000c440d2000c030b80d0b12084050707502c200040d646a04002c2c80501011b800401c0d05006a0f100318a2b08c10f0000c0541c2c54110440c21070901d800d070000142c020000c0c41c881d00d1072151801d914030107601d0200d54841d410103d8180e45010f01c600f18000c1d5400180000e040ea44043c03441c003c1c540202c0d114041490031210681e80d1840124261200b05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 888819064 1250 888817814 888817823
    0x11030a080c030c010e01050606090111120708092d1c0b0a051b04080c010807050706060b04080c12061f080105010b0a120b0a0603110421140d0206060915100207050301110403 76
    0xc001c003004550040503000c00300033012003901c01c0d0044040d00c04c4540d03480420211503180000840980600d01515903010790202c5190b100c3c03401c903071004a41900c10100801912036040d15540020b180800c80c500e10304654003003808092030070640c140c0c0002e40403d41c3c501500c8440072440421000040c401e071801c40d1700150003041c07040112001551480c0c4058038000070080100018004101c00e07000c0d02c80140034a00c40e06a50300d1078280881d0620f003e40d01003601c01d010b0740700c0501880600040440c1c0001485409505403040324800c07100700c04113a40030080c55400c09000040016804e405080b1400c030a4580d60040b45c2d19601e1001101d03114201e1592064110401380310051295015003400b00007608102e242c0f40e20380c03c4041c6102e0250000400016181c00c002d020850100810180c0d145641c4c001d0103c20007442001e900c1d03c1c001064180a8240b40000a082e0b4107501c1181c0c03042d07039029100c03400700003021078001d40f60310550280900940c205014111144502c00403141102d800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 888820314 1250 888819064 888819067
    0x3090c09040b190f02070506010f0b040e0c181804030f0807020303070c1e0c170a020102060a0c091d0f0906070c060f020903060106050403051507080411030a080c030c010e01050606 79
    0x200c8511140310a0020ba080ca0104d965440c401c10314910b82c4002e04c4030a0194009000329807605407061120080e40e006090094001d100800903203030381c046000c4c1c00c003200c0c104041d16a0f9103040041c22025903500d81a034000380313200c110405a8500b40280c0d0046009a50701c101c91038940c5030640d409482902c41d0b0005910410000d01240d104842c24400c66204450b03068016440c010070382050340c0f40d0201a0307041d1783d0b008402c100792090315040c0c10f01b540c000c001400ca18802c4d900040c1d103420303009200300203041d01c0710100362a06108010100140c0001041824001c0c1c400c01c01e51010726080707510040d0300100700c0108224000000c0d5840c8104040e50301c4001d40402c03695035002510b031616050740e0194090109403281e903024000603002e846241e0b1b5039a00c1c0e41c83c508115203001a4a80c50007424100c0d0341c103001a8640c0110b03407a034800c0c0c105440b800c13041c0400c1c0100f4900400d0500250400c0e00210b00074110010100042c4000c0c03440e50028000c03404180002c901700e40c0250362160303201c2e50 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 888821564 1250 888820314 888820321
    0x3010e0103060605042a020c030d0906020c030c0f060706020d05010f060305310501022107021504030e011103161104060501020f0a0b091905011b02150a050c0c0a0803090c09040b 78
    0x2042001b203040c0b10841d00c1941d02e01c41142d004030303140c02c010700e1211000c1a0b040e48240891541004002c0114038210002c110352165031011804900d160b118035402540c001441c3c3c400c0c0040d0f0f40413038450740d02500c010092583d42d02c10881e440509030080c40002030900d0007007003400644042400f004411000070700c08801c0000703004058001c0c00032044507155000d0010150b43c10750300f010f070341d110480101c5005242c40c00783d034000d0524103a00007000040341400c080c000426030129088065100070b081c1442c0114140721541d1a41c05a00c0201c0400c03001c003600401001a5580d002186090545051020b5501c82005a88840100c1242e9000380c2c4824803000200e586854416003088a0b80c0684180300714000f05030f020b8140060050300d090f034490801403800000c0544030010582d00384003030724040036542000400040301030a0036140d41e4450012440740498102220703003050400c011100f4800d100e10f42510b490700102c07400c0006014035a42e01c2c00c00c3c1000740304280303c0d551040c495440b80c1e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 888822814 1250 888821564 888821621
    0xb0a05040f1103040b0f09060c0a26041a09071a0d1415030d08060f120f0a031707020102070203060408070615091505030c1003090203011103010e010306060504 70
    0x1c0484100c000c80e440714030346500e407101200207601030b0340140c035040240c0c075200510604010002e00800b41c560700040030845110040801e43d40c44000b2481c2c5085025501908009082d001d0041c500904680c803041c0001c01c203040120200a000d0803000f900c0c660760b803d60294039001e0701d1141041e1003002d04121954060298000d00c090300740201c000501d044840000414020101c400c6c1216600e10381c0c0c902c40515080154410f92003c034906080245000710110b4102070310040e00d80c3c01240050982c0c0322000042c01000105900c160841e03040344000c0c100180410001d4009102c2683c0c40400b01e110284103008403108550054003d1000b5140ca035180703207141d070002e8030076602d541e901ea04001001050000744c00c0241001000800e40c00010606c41894488a0f03105c1d41c0710740d00411740b01c000303915030b95034060284525040002d2805000c4c0003288c05407140c070030904c40c100700010005c00ca0803035901502e4183c078091682041941d44070820301c070403140c035088051030186105523001c8945 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 888824064 1250 888822814 888822821
    0x20a0921060b040f050910050c03011a070c2103030b0a0806040b151305070e09040b070302070812160816080a0203060105070609060e150606040303051b160e01090b0a0504 75
    0xd0020304001040d81c54050b868080303030b509486c081583d80142c84880310354100d034001c840c0c00906c8040d08034955490921a41488044102d030f503000c0030784c007040040500903180882801070500100303098450210200c0503110001c41c11080f400304c5c0c0740c01c05003100c9040c20801c100580f549040103140c242c5850300c0b454100740d00141044000708411600021584801c0041300044040200219150504d4900070f0b00c51803010358000c1c0546100c6082002051f040040103400c4240ba00f03006030385a1040c10610210b1040c0e0090b07110505014050002031040e003403031807007400324941e41e10081e80c40d03415240080c80070300c5d10500c0c0085c01150100300d05860550003550010700504040346003c1080e9a030f98140c034505d68050701c1141d61560307820601c143c180803c98008100320090035540c5080000613002e0300660001800b00007001ca004e9902e101d4404c204201d10988500303c4449a480c107d001003904120b000c3d481035a4040700c0005486481030040e0407456000503e001e074224100424031009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 888825314 1250 888824064 888824081
    0x60108032203080c0102070614071e020309041b02060c040806010506090109050301051509060406320a030506090c091324060b37031e0f020a092106 65
    0x501d107940c1c00000080e95910051040f0280d0500240e141e01e070604251048954503000c50351903100c0741c4104a2243c1d8410300101548803a240360200134011200220303d1400341100c0703d81c00618020824101d01d0100802c2020001c0700d900b140d90550314a003421656002d1485011203550000005000724035240c8098004000d0625003000029030341e0002a09451090b2011241d064070b01c5218000d905003001420b9000105980501103145000e990ba4080034000111502c1010000e80e5690b1442c1400184195150002c042030000341e102d0801c41d441d040f064400070a00e2148145400a9003800180c03144520500d04520b00c4c8800c4c0b94640142c65520300107540071038184003801810f90301180c1700d00e034042d14001a41584440d000080040760325403002280000c814540d00040c80c0c00c940c40e81c0d01d221000c00d89070114101055000700700400401d40d4041c401c1c05d040481001441c8400c2c2c2c064100110341c0ea0340c209100c1d03510884c648502084490300d03221000d003c0f12480114100e5002200c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 888826564 1250 888825314 888825367
    0x10605090f06030a08040e15150a0e030a021f170601050412050705060406170108160b0d0608010c27320312030402150f0a080c120906061206010803 65
    0x40802c40380c5c1d01d04215600503049400030340e41150074010110b082e44403400c820f140c00e41e44100b66108904051075513014101900c010045142000315413500d0030700c0088803060307024141c01000003100b01103d40c40719007200680e0005280e8100090b80c0141d034408240104411f0b11703041d1400d800d2151700850014444011b646500c500d003400100d03501e9500c0117000030803055883c4010104c9886510745140810b038400070309030703004059500315040b034035025508860583c100141e59161448028000d4840f0340d000460359441c0c0004c049a00d03821050b40507a03484d46454a43c800d040c01d40089040e00420b0144644441d0040004a185001aa8102410600800c8209901c00003100007407901000c85000312050b440441803001b14289100c1c0800999420000c032800c02581c4601c0910500581d13a01d081002002c4000c64210300000c411600b600f050303071401e80a60314110480f11ba45142c03c0c0c1e10680140001c0340340035040312010039004d0603a41101d01540c9861940340c11114a00c100c40c00748403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 888827814 1250 888826564 888826573
    0x20a0e04050f060403020c1819020a02101401050f09040b06040b03190f05070b0c15101707031e0b04020f03070506071b060e061c0f0e0618010605090f0603 68
    0xc412032001c214040c441c078171076401400b801c80c01c00f052000c8400c5852109880211201c28460300400355074004500c1a1110740040c1c07a038062100480c9004c04481e6032409461501c41d0040c0c00481c20300a031410387d03a00340c0d10f50045401c0f810510480705030440d800b414010310344010400314506a082a1144180201101c100312003000180040c1c14061004443d21001d44c37010404000c020701c000c0d0010169800502d0502000d0600c66880d0138440c4100003009030500005542d2941103041da0340513041c501801c003a002c0c2c90b100d00d540d54007040e010a5503800841681d01803500c0e40d140f0590700355540201082c0b490b80710707582806170601a0b0081c4640c1401200030104080d22984094076400b40501c0c0e440386c039000c000501c1d1a001703000d600404100000c0711040744468890000b1074042c501150b10384010001c0c4050362030010004400302c6ca447c5803c2401c51103142d80000343e41da0146c0200380805440c00408600b1a08844103803007059002180c020010b000c441096040c2a0301c20000380644 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 888829064 1250 888827814 888827833
    0xf0203271305150102061018150b0c07140a03060506060408030c0604262502031204031b0806040f0305120103060903171b280306061704020a0e0405 65
    0x1c0d00c580588540c61811542c60040051200c4402c0301d103014507030280060030460400144030015528107004500700c074900350007504946015544401d0085401c0c0500d01d01f1a40c440e040181d0b95401056944001d20400002041d1150301c1e43c002c119a2800030301d03802881d45150340c0c4030040d090041c030641d03000600384400150f6040600c01040819400e10103443c00e407415103050806414010029401030801c800408052194102150000400881031203460418180ea4040d09240084000e4141c01911202c00c82c01e022400644252403188000d104d1000000003134a52180c041c1c0701e09201a4803650100c0d021603503050355255000c0c000c1c50107a16100b507400400440031801c1e4011030702203030303202c810405041e8031041c014070310408030080b09a28188503403a1650200c5491041c1d000e0b081c0020038601a0b960407203c2c2e1110340411600e91000091504081e00500451103541c0101d6502c0000c040b2281c240000b4034400c40c0e00508421505051400700d8086901c01402201c1611400c0b030103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 888830314 1250 888829064 888829069
    0x110f01050a020309160b070308090c0a080f070b03160c05160f0f06020c030a031d15130f0810020a030e06090a0501290622080a02040c0f020327 63
    0x300c91051103560700159403414904201450140d00c4081d445080a10440912092403100121031005415103880c2c83c0d1511242c0141d400c0c00c0c21418000d03400b5240030300000d002c080202e02c041d2400b01c854180c42e0381a82d03510042405100880318154508040300b00003001c0c40c0a100c081d40780500500440d58a94000c1060020070001380e0420403800d180381c181040003801d005007940107010a880075240d980e41e4030f00425520220a00001e09108003040301000c2c0515102c03041160740d80080400480b505e446844107415803001110302ca102441d01404942d46100c1291002240e030321900501605000d680e03000d00941001d030741c03001019102d441d0701041e40d1081081a000d2824900a44a8407016141883c01c540020402003619500448103402c0410040c90400a1000556041e0781e101800c484045201001c104400304c15600250003080041d00003402e1001240b081e2010070040c402d4142c10760750f40480030720301c40040e4003c0020520f840110f4a45195900d9000d52010000b14010700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 888831564 1250 888830314 888830321
    0x90828060b060703090f05062701050910080f01050913060c020a0f1103060a06050d022101090f030206060402070b0606071104050a140a0203040302070b0c0312010e0603060a1506110f01 81
    0x40c0d00088014601b0300031080451071680c01000201c0b0341620f0840500741000c050494142a00d02410076294004001e03409807040b10390120300103011010060f640c0350003401c4001c0907070321400d0b0050008008a50741c140088094043c24004411003549001640d8107001303001c804002d0002c5009004010300090001c2030b5291180c4e10680150030140544418940350141c0208120f4000f42032030702c2049262a0030010f150030b0390301500d141440d07045543c4402c5000c1d80d250300600c0d2540c640318140c03050020180144201a11a5003500c0058851108000a80c024800c0242c40e1040c003902141c01450034070b00411106120300b912003106c1c0c00880004080741c100b26083c0301c0086d21110340c80c806901292016a2054a0b0742c0c0c218210304042d03c00941e40d0400e03002c0c4a00a0000244400101904000f0340302d803d00c440d4942c0399650f8486421081c43c240540d6000e000384504004a40303042d00034054803401c3d0f0f02c0d07600c0c010b50052900c042101c84070389503000160b075406200710f030f03030a214020f01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 888832814 1250 888831564 888831577
    0x110a2a02190305010507030912030b06091309020108072c030c090901020408010e070b0a03050403111218041802010503061201021303030e01141602041b020c01090828060b06 76
    0x2180041e6a034070718181242510402840d00080601d0010b8000028540c0c6403901910743e218900000d49212400c086120303403007184131003a80402011001050b108680c0c000317170403161003079a174401e441e203420409680c942c078411001021201000717100344105e40888002e221185005007101c00c8168000e000c62003035102582c0c118100d940002c2d052080000074016070403460511001462018030303041c0101014001c84100400301a240d1021038103141c41230501c1c4542c02d40701c0d020742e84032090881c041c002941c04081c030041030702d05c0780c003003050140f900d88541000800c4140000e407291805030b00450321780e80001d040f02e610485100e03181c00c10300c1091003e800a0340c1c41002407191a4151b00f006000101c00c0e034201810020100782105001d007a2006031900b0090102d4401c6010036184000340c050000e0a051200300031000074844829170f400220308048200a0700c1e0b032203400d070300c42180d96110a50361002c0c40c0e0101c0340342c4201300c3c4042c1821155000500807100014100b9100000980a50240 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 888834064 1250 888832814 888832849
    0x41e020415030507171509030c030c03090f0405090a030f11011415060406020d0302070c17030a090b0306030309060d0b090c0d05100e0a020901030f020f0706110a2a02 73
    0x38102401000f07001c02c000c8000c0c000d40f000c003004401c104081d0716601d801403200c1c854905100404509088410010380c1c0d0187c80080a0fa91120202031200e0396a07000403041911034071300308200821070b040c981711345800340c88000060709889226803410b55203003401001c0c46081142118112030100000c3c414031f2404074420b4001c000034104800c06060381c2d01c0c2e41c09058856401003208020054000401c1d1804e104a400d0160b101c40d072a0600b07446106a9600060f8421031f01c48607101000000300c001c1000d4111903c2c3c00281d03a40700c112709005404103e0312260103034010440080c031882d0104c00340582078140c2d03001282160a180c00b041c440c04007a1a0810004008200e00d80366403074500a6640c440c0c9100c01c401529880c02d0038081ea0044040c059022041d4000f54081050740300790424075410001100643d55003200c0c1040c040c10380e00c80b0030b00340c50051a0030a00080079080d04e04441030b03c034080e41c0b420301e010031028201e2000d030f0132882c801389521301441c106001611b13848220052400f00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 888835314 1250 888834064 888834101
    0x2706091c111905040b031204032409120201051006020705060d02190207051e01090e0a1b08060103111806090d050106080325030207090510180b1f08041e0204 69
    0x40c07000740820ba030400e9517501e1003038001c0c0c92142115105001540c0403241c001e410303c20200740c40848504032003003d1648001407810301314038030144a003600131000c2c0015aa4000c1206559403690642d0b082000e001e1100117802c20881000a40303010303c0030f018401c41c140341c0145803600c200b1400c0088802400304001580000e00c04101c149402003142d030b45940000a05070403040d003507000800d5103009004611110000c80042285100d8543c07200e00000403d0b16001c1031901c0020014040943c01c466090009041807841540445041c01b5241200c0e1b02e80162061010a2401c0290300e41107416001c0d0025040d025080124001f400b60f98001c0042c80080c540d41d42f1b0301c040c00030705070040300102c0055501001c4440300195000034920102d8000f880c000615469081070780b280700c0780981c401046e1020030700070f802900480d81e11584e0046d1003241c0710750281260801c19501454600c036100040350a03040001c000ca007610751840c1410b0000304003201c8401441d8001000c94410b1100140600d05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 888836564 1250 888835314 888835319
    0x15050102010c0507152003090a0c081b06030a020c0a0c14040e0303060d031e08010e10050a09110d090b06090603060c180d082706091c1119 61
    0xc0a200340045010280341c49481c004250320386818110a05041040003035586105660740c0200e00d50606403000210240e070758074100004140e9440801c070030140c44011000c04001004200000c848640c00c5e80b504650100f007120400300300d0903800040c01100480c0c0c00b0818002c003031000380440035003284203406211400b410812a0745904403066002c41c062864500e4107903c8210010551b80d001c103003100d00c04045103940c601110140040744e40d030f40b4050074120b5008030b416005000c1c24140e4016109900c0c01c0d0b47c0720f8048a400c4802c034440c0c25007041480e00140004100d94025070302440c03401030318070300d440a524802e01c01c80d00c00000c2a40d40b00d0704002445081e183c0a00030b5500000700301d000742140c0c1000800c100183c49900d8080441c8546000b00000d40d8882c520045500c03500004c0242c2c987d070050341006881c81c000d5404440303942c04102000040d152a9080d560000300103401d10105124104240f440d90890700400d0b42c8404030120400354540d90b801d2000705800280300b00c00002413 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 888837814 1250 888836564 888836567
    0xf0c010c11090c2812050a090606091d011a0909070803030a0c020f0a0209010620030c010e16150302030a0b090c0a03060807210f1401021213020a0b0a0302090301150501 74
    0x5081e56509101584d1081d208150183d00c0882c030050715405582c005905d0322051500c40050401c12001000d96051a4000554030625405140e042403515000c80c1c0e40c8020036441800c035410892030580b040000c0903c0c407051700b0300002035a8054010021501d5180e101e001e447d01c1c58008682006915440c2c200d00c2c141e2550621001d032010507041e0080044085c40d5000516100050288004200b00c081c41c801c0031100308000c8140b00c3d01108184d070f07540c0c00b10901c0c039406410400340c00f10640c460000111002070520801d0001c50340c0209460110014240048000e0761000c1e080124440d1161612811030b92511134031405820b10302121540c0704080d54000d01900c90b264468000c0d82c0103c0800c1165017100210642c1c02805014026501d8007546410030111400301c8000d40500000c0e1003054041c0c0d815801804241c1000f15000c195555000521040311003040c80290071000e210703800c104a2880030080c050001003428050304215100005c06e00f120a10410b84c02404901a000c02665 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 888839064 1250 888837814 888837847
    0x90d0503040f530a08161418040501120f03030903350106090b1603020f06040c03021c020f040905011b0309140706200102091c140f0c010c11090c 64
    0x606483c01010700b00380340b0000c00b4100b020000e205460030303201c108505c0441032141c1c40700954405040c100d01d8807118515003800c402980480064000e51500e03001003001c0c90140d035901c1e241d603070044032042d44250564044015000d100c4007101840000340d11190b10780b103501c1442070700c180024134010003e03840440c005080081a80312100b4004000c0702803040308004412200b1030660300c60700c8841c058543c54102c0c03818186040d800454054582400f08002c410890501102d0080f42c41c40d00368140740b04900c0380e50b510305400075407120700030500e200c00f030801d6002a95124020000022101a40328240c4009619031250b103000175034178840071081080f03054540304c10f02d481500034031600c1d081260140c05030382d4004404150010703030a140303000c00101350100d41b00100c01500e01509100d18007031260314400c1152045581c082a0803140801e00000500c0c205151010001013108180301001035410040c2144261900790120740014010b4440f004074900070b6080c080d0301d47d40c0c0d000b260025440c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 888840314 1250 888839064 888839213
    0x40b0a0e0907090b0f13060906120b090105040509070302120f01050f041211010e072301030b0a0b070303020903012f190e041e0203090d0503040f 64
    0x1407800505000300740e54010720a80544100440d505e96030352181c1646246805101071880ca184400000422840e6200303041c2422030309151030b035001d00c40d42882054180c0c2d100850490b002740300103004000c10f16246e084030b600040b000b001c3c0d60075103450384c011131500104129141c26503071144840b05d124481c00d100d01507100c0c3c00c0482c3c40400d414030381c0d40c2c88a40000d41c40c0c4441048480404401805002e6002d041c0000703000040380c5d24641c7c1c9140381c0340340d1400c0c1400701304023400721003c0c03c110354000e01880990b040024002c65840707052441606c0305400c02901901016403d10031680c0c961001d216400240750142c05030b200300c80c05111181e04c1e9502112005843c001c00b445403001b03912020b440c000d0600520304003040c442076050041401080c0b81030001038148048a4130f450756107003682c000c60044000318141c80b52942d4081d4203882d540f00588004010041d140c0f020310120740080888403100c407840b440d14288490b132070034016007408003110804d1071003454601c070104000f89103258540d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 888841564 1250 888840314 888840319
    0x509011107080303010308071a0907051e030706050f04031e0c08070b090906040908070c260a080c0109080708031e0403050d150506070506010e070c0c14010c08040b0a0e 74
    0x600d400c203900b0a40304e02061000501e9140c0c081951410014568189003207030b803007880f00b41c00c00c1c5001c29220742c0e902070340d10449010701d6804403400e0b0000d4a00030754036200c0741c01a005200c140d20b010000c680343c2d40800c09248102506200c08000902464009064030040c90f448040060060230041c1004446501c07003800c950040604002e1030281c441900d41c0035804588851007642d400d000300f8060004000300406010000400c0c10400c20702e940f103202a140500e950140d10220719441d100034121015540302d240e4032003850300e8001141c209c01044640310203c00440c0402c6550303140b080c00c1e005400220b030060300c088108081c90412440c50030b1100c4190390581c0c020704042d14050140c0c03183c00388090080c0e403180c1c80d103c0c41140301200385004000280803940d4418103800d01c240c80d65001c0c060340001d04030802c04554640c6c4901d2009501d00c0e084050746810740e00d0324a181000505c02000c880c14030010549040200350078001401c02444017003150340d501d410070341005041d440b030b40d2011071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 888842814 1250 888841564 888841573
    0x7140408030f040f05090f0f0a110408030a1808030d020d0e0303190e0c09010b0a17070c110603040c1e0b0f0405030c1212160501020412020108012705070e040c05090111 74
    0x7c64808404440d040140080784030041d86074080341d4800751020201d0781c442c92000041c0042c84030340000040c400000d03d9540c01003140909035031007445422030310032920994003e0018403540c0c582c5a00400030584c41c5080002c00d0310300d2010950a540044695001881e0303991025040c206490140c004000c04480282c00b940c1044070002e141d0711418060500c410310040762200c2010702840714011742a100c0c00d00c1c80998034282200038401c482c8882c085440a0048541546609294056a001e1688000c02c448280e06004655000d00d07001045420320310f0345007070005403800c1ca450051486920303441c83c0740e40d92070800301414a13210308001c0c00f9000d00d40ca0340c80c2d211248804207150301d2000440e202c0d0303a40c03170101d180d40c1d840b0718903507982c0507240d5440068006220303901103186210b920b200380c83d5082d081c0e0762030b0b06082c01000c6429002e00c03401d0011060fa5681203150344426030002c46402c003100c0718203000c8040303030499184025400c04074200258511040d030700403a010303101001c180002c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 888844064 1250 888842814 888842821
    0x6090c0807090c021e01090f110411040b180a0e0708011412100f0b1203030105040e06310b04060b0a120f0f020105070506090105070e1807140408030f040f0509 70
    0x3580c801011780d0b5640e8202d001c11410810400c290002c2c0a12600a1428014501e403411320701428034210144c188594500003000c44810011001c1e00c0840740c81c0002e01d41006200640343c1020000140304903230160b0211004501210b024071802d0140d4145e0341c0d000500d43c140315405059003072aa140d01e108007029622038000c80c100260442200700c1d400303000301c0e14146640c0308902400400c00d0f030551090307680080c02840c060010145040364406c4405000020a91003c0c0c0c0d1103450558852078015400c030b00116100c2245c00f811031050380c51029100341807034161100d100102050714100c44164881407019400d02c2c0c80400c01000d4550f900700c825000b0340d0b50b514451445c0d14100002c0613082000388030002c2d607000700160764909820030192442e41c03910407030060080100311401004603d200d4a4111181490907010082604a042030754583d2211b65088d00e5400050111500015081101041c0d0000910140442c0300302140283d88840c140380181302300f40c21a80000303015411b01d0080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 888845314 1250 888844064 888844067
    0x30207062a030c140c010b0301150b0d020c0705040c050a0201150609060e1504032d17030a110d060503210306010c06060b0703080406180206041503060306090c0807090c 74
    0x400d00032501420009080f005910b801c2e501c10310098040401e0382c0340130407044c05e075100c19040b000304020114000c10100780005160202c44d43e89009003400004180030f01e40d43c40c403690303004120a040742c80480e88201d6452000030161000e03810a440060030118039034411980902911500d0720760030036026061030604400409842c264401e440070080084184d040540368152002d240e14540da00055803070380c503414414500c03110700c0d10002c080e4400807050040c4c800e07014a401e903240c4d84684c44417011651260400c0303054001904c2e01e1440b9503101080e54082950301b000705549101218082107031441c1100b0141401ca4031b107026140e000300d214022041105203012261300c8142420000d540c10b0740c900300071005100c40d81010682d0400055440309050300326800500c210301c42c000a102240e10380c008160412078541009403c40014003040c031110f036400319004540e038203510b8005a0f10703a0301d4a0304803d40b00f00d803206481e01c55180d8814004148140920006403444e0f000c140588201d0550 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 888846564 1250 888845314 888845381
    0x5070c0503071701360201090506070b0414070b0a03020c031c0e0f01150905091c03050f15010f12020d051501020616020c0d022d011803051005090109020a0603020706 73
    0x3031148178400354200c0c0c1c116030042c051500545000303002c8640f02d84040c507200c45070580a88065503062451815242c40320000103204094500e00000c0e24203040785480c05402070b4004a8440701c06000c24044840561982042e20011001d0214049400300f284044141445504040018942d04120035010200b410305400d501303d680039240046c3c1e80c1c3e11480102d0402c0145000c02d0800441c500c080c4020740e6050b0001030059842085609082d10b540720351289082c80301000e103000c00c19109030755051034000c0c1019000a28120f00252a103042002001c04840c03040380d542ca1001210b4031003c5603540d0400c25642e004d8250414650900300c5040080d644000340c40f8800d200e0314444450340c045454a4480f01034140c0c8075034280700110000d07c50582c24204c0c117281280000c841d807104050782d48174444e443c3e084036004005402e860f03039480003220141800802d003c00c9992180c408400580301c8032007450045c0806d40d001a294110352510340c0c159041550060350041000941d031241c48803014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 888847814 1250 888846564 888846641
    0x8030105090c0c1e121611030c0303070501050910050402180c090a06031b050a05041e1a0706110307120b0a050909030714030a0f05070c0503071701 65
    0x181c22661a6640030384864981c071030030001140900030782c1c01d001e001e0007200800085004004054603402041c80c002c070b02d054004c200003040d07002407003070307556020800b15824101189009003e454403001d05401186c6154000007007268981c4d5100f042241c1541c06200464580c81c1d18541440f550800fa000503064032071401c505103441c0840004900700841a40880341106405002c401546a5800c0050000c01b80c45952208280c603134000c443c0300034814070880f84074141a803102d81c03c140c03e002c940c0d601900703d00c01010f01000c0700d101c00b1420742c949944425820004003d2103030740360150715050043d6170440005c124102418002c0c002aa90000b1070307000380b2a031102e0700140d030800c182c002a260286540c882c94205c3c2d40710741400001038000c0b005145042c01044418041052850001e54a02c184409200054620101c2e01c55043c071440c020000c507805043c010b1202e07030b101da0000782804500d622a42d2400c4180d000401d0082082c00340042c004005402c0c443c80900d0031201904d244041d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 888848920 1106 888847814 888847819
    0xc0e090607091215060b1b2413060905010522050c150f030106020106060306060e010c1401061a030402011808150a0f05070e0a1208030105 61
    0x180c86006000c242d40d030703440c11450b02203480c00d07814403030208a54040c1c145400b0745040005001d1000604040d003042507946200700c0c4111080b604c001400070a94001008500709608500402d0b40a000000c0e00054035548516460345141c50100c801010207160905410038448150b0041303215112803003501e40040030440c503002c0300c0c00700030200800650101c1c5030700c1e0032030504c409101030b1000c04807410350405001c10160b280c150400d07003110300180c0d99400104101d42d8140034460003840a8185000e80c0030034140002c0138640100710103859400c410301d0b2144240c802354005402410f41c00c0c0c00400c1c81d0464182400c03039a1041d5000da00040041400b4681200500403040841d2041030080030030002082d0320580610005003241c50142e51a0842002c105040c055580300d0346842c3e88000e07140c01c10000f0800a20f0240d0401200c090455482900048a03903003204d054482c01c = true := by decide +kernel

theorem cover : BRFrame.Cov 888669064 888848920 := by
  have h0 := BRFrame.cov_init 888669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 888669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 888669064 ≤ n) (h2 : n < 888848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
