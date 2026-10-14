-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0199
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:24:31.715075+00:00
-- url     : https://prove2.me/submissions/bf0eb534-7096-4cdb-bbd3-25d0043b3a63

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 35611515 ≤ n < 35791372 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 35612765 1250 35611515 35611519
    0xc010305060f030a050c041b080415020403020303030f040c0927170406170601090302011b050c0a08010f050105190608150612060103060f1508040807120504140a03030c02 75
    0x98551144000202c940b40c01d4944a03515008204400d0104100054031030321043e4259014000003889280821804410350180b9012682490000300042c168007000110345072251801401d0a8507500824a540c00494078001210000024071052000310085d040007041d160000b881065010900c0301d41180c901c0442c0c20703040c0d981080100801882c40540482507400d90704054646603108002060484851070140000c00c1030350101e051944590502e500303494043c0c480c0300303007203c048002c03000f82034070f0103001d45507070145289008503a51402801001081c89100105600386200c0d1071008454060380050720482c100120a81813030108690941220304030308192042d40e45081d5541880307000c082c80144c2c07054000503130049500550f02c4280c000d01080e64100700d020340701c118044402c03105015100c000c0c0b107000b0651041c075108010041d4051302c00d10b5142c5c2443c00c955030701d2603a040c07000c40103000700d800803c0904c1081000103800c540164201c1c2c45103240c074034545015052000d10000a4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 35614015 1250 35612765 35612771
    0x7020703140705041410080109020a1511060705040302270f070507080307080a050622020c07080312010510080402060a05070602090a0f061101020403380a060509180c0103 75
    0x341c400180040001420080d0051140401411814034115011940081180c61446c404150180148a540203042e400380405625504100c050640074840103241d02c1004256030802c1007400e0107000d000d00400700350b1507290703c03103085204000d41d00c41c0701c0c0401040401c8103000e8110220200383e445420031162015442e982c0c60f440e00444403849114005004400d0002c180a60280e010241e288142c01c9101c080200762101001c00586981e90b10030080160030504155043c0800340d4018036000c0032070811030b603c0c01d41d52200e00d42507400034000540c03103035034800042000d410304210700400d003d07084c6006c440515142c1c0c00200503006440800b0300b044400b00b403034810041c0c0da40c101e4102c1c0c40020507082c40e4941d134403050440080039011781d4000550390030f20703d8114001402a02c003070382e5100d50003048080705400e03840c040c031400015144c1789903000c04080d010451003849407030040d000020013150180c105014071001c0300014103c40e80f00e1251922400b84c0d41004501102d00f40001d207808 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 35615265 1250 35614015 35614043
    0x1803050c0a060c0e0f040507020c040203062704050105090304060203040b07020402040e0f1605070203070e070c0c080706090f0b0307120605030d0e1011070b070302010906020c0607021507020703 85
    0x16501c0e219400000402103031030301c0c0b81d210340190400c070b2201e00f049003103600040c194150070501c0300f541c82c2601d500001d80d002140000c11440c06401070b40e400300002c0c215002d40140c4080d00d40d603134078048102c2642070404000348401d02078280a9a580011290000c0d072600f841e104c802540e030311440c864031641c42c074080f03401c2d4110b55980c1c04440040a443d84841c0722803c10a4038640c0c2d03071005a403040364056400080c0c600c9980600191039001d500200a8607040b4509044a600320308024074100406c44800c10010000d0726420503070000d4002c50b402840c0460070200042d040b545180c121258100c903003902003204d00c00800840364000313a13503e030070582c5004803c6c0c3d044c00f40810ba0415580344c002c2402040c444e03548903102000320041210488103e1031680000c0d40c1e280151500142140c02c120740501241480400403c0110b200b80700000c4d402009072101c800700c1c0c02c02403410b44103420580c2072041c15541004401a2511141c094034954140640f02940d501904e100c0280200c0c1c0c01288 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 35616515 1250 35615265 35615287
    0x80f15060a030e06240d1103030f04031101171602011515080a09020a050d050f07030308040506060901080712020109090204080601030201080919060905010209120c0112180305 77
    0x10649020250129071614035001c800b5002d00041c070803c00303051059000195040e5920484032131003202c05002600b0b940d03002020300449400080342078814084040301003645442c01c100612083c0580d0b08407a40302d5007035241c1010060303d18111281044021662030414040c1070291b540c000795851904883d403814040c091740508503601c0b2019903880c15000014031181400c000450042042c2e0b5504000c1e5a81000481200d0740001c2c041c0d004402500107010310b0800d04008804c2034000c00490700540c00e19242c0c545085416001100054080801d00c410090304002858010b882190110119810b10506955031b46c2d843c0f21740d407102d52904414401b964010f0200da005440701031401e40d42c403078954044c80c0c0e0b1031500307200890004106100007a40d008000c0307a110030384600c18221160001454450394064811103406132a155800c11290f14265101d00440a01e216410041e0609118520003d440d40384038079840d903015810003c0c00324030390442e0080018184d60508000342c4414000c14 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 35617765 1250 35616515 35616541
    0x501080604090f12120e01110711010c0c030503130905190b0a0902070506011502030705030901030903050909090a12020304030b0609041b090501090c050705060703090203100c030510060807080f 85
    0xd00030130070f0b080d008081d2aa201206006019182505000c80640c1492040c2240c5061018400c00c01c0280a07090026032528801000b00405240c51070500900740c864043e0003445900481c2d580d4070000f40c0c0e220303400c5030b440648000c1c542c214080106140c42c581c1200c8a41d0140c421a0142d55110900c4940d940c40111450141281e040110745802292400c2a5075050a000d012584468201e03212806840082291061644036010b9801e140c120401580039280500b0224107020040c0203005860325900e6102d441841e83d10000d02ca501d8160600e4581d42220421072021504108400c0c400b10f000751018941061041da01c07140f02d580d50707043c03800c10a0341d1005040104920a0000111750f0301903001141030300c88c40c10f02080540c08620060ba0706208801d0b000300f60303811590002c1d035510300032382c810401a400941560104150b8007404821038003100103040209030703948140b18003280106141c00c003515890510303003400e0511610140c24118001c00d4503c150104400040070707445058 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 35619015 1250 35617765 35617793
    0x40605012f100903020105060301050c19030209010903121d060c120702030f06090601171609150302150d05130203060105090703060306060b030718050609120304050d0b060316050108060409 83
    0x10400c03443d1011314009018080503985940b0a60074600490043c20700031040b0f03034846441c806032405d422911032050f030280d04040300741d9050110301c03040080403540c4441d5103d010b0340349980300781c0c040e101454814107042c80303c40e00e03e0152000303104079200d42c00e000880b48170800400710000d403281d1003403000903c1c18032407400024003030081c0c80c1484003986000904078140c2c0d0b4007219030840c040306400c800340d540300042c1d02421031005014040140c0301e4144d0006554101d5094003890741902c90f0040f800751a0713801c810a0150000144e0940300951701e1103169005010041d007580c43d19030300d0b000031f6540c0d01e06004c2c81c1d02c604000e01c04150441c2c020b0b8031400007136a102800380f04860ba42c06403180c40741c004448241c0800c0c106003a1108801d00c008803503041e00e2009201c01e082c40ca511060144444a120704480144420040032480360354098088007120b1103214560060302c1c0060916061101420070f4003006000d4000c00c3c0031a07a00302800540c000416a80002e681e0410700f03103541043c000d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 35620265 1250 35619015 35619043
    0x1060501050d020919090204030302061f090b18041209060504050d081b0a030201060302130e06010e07090308120703200702010804080405040911010306080a03091502030c060c09040605012f 83
    0x1001700018001070540143c42140d02039001d403134035a82d82000c00901d0400403900341001d200d40c10001d0203880340a50101d445007074007401080e10358050910302c030240314003034806036541c96104e100105000d0740300300214054145458914100b600d81404100c804c45024401003400c00082a44201e160034455900345a482074000c9031440506410083e00910480c0400e0f03000e000f07001c409804581e00b901501140000b800c008091580c03a00382c0d82d441192001c2d10480422544920001c00300e1b403030303c010302036a0500ca03403c00001d040109014040350310800b40400c000b40900440f80d07103580380d8400d443d6142d40a091100071a5142d29003540148920381040d6132181c40d02c645070041c4170f1701406404002c0c00030788040208645032509155609440000103001030403405c000c0c046002003464400e0403904a004523030810000380501410044100c0d601c2610290200e40c00f80ca92809024440c01004203080031658040e81c140603080c1d0000c01c5400703a00d80481128044034080701000441901551 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 35621515 1250 35620265 35620309
    0xc0d08040e150a0f0504050c091309140102070302071d0907060e010903060f0b09090f0309060d0b041b1211040605130302100e030c06040e06094501060501050d0209 72
    0x541120360000c04e224080c1c28000d500c0c240006194103003d00444106120080208400c019403454041c060002c559007100c0305031465104860211090001c0e16030030b8444d130064079000f0700708018500781c4140786a8181207120320f41c0c00e00845500104280e0284d64291910306001c44440300180c928030ba191380001c06444c50a280e06451071386941c00b0342c18000d403c031030504440d15005a1103980d82c0c2c1e00c03103003600b803070b0000c2013000c1071842c09000030800141c100c0d2021500c00700c9040081c045407403005000010003148405141840e03845010b0300158180314004020442c00c003407151085014500516041c002c00140c40c08000302c144910720011a8000c016500c5410303504001000000a50702c094068071500e801d007412031621806840c20340c0d00408007400f25984800c1000708150020341403e260403040013209061a0002c0c60340000540908008048070038102e51407610310620081108560340f42100a020a03030b0b011b0f040302e05600b0404409038951004100081a18206e2442c041000710 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 35622765 1250 35621515 35621519
    0x303070311060601020d0e040216051605031002040f0506030601020109050d020102091507110405060d050604120e100e090c1303060e010506030d09090f02070b07080103050c0d08040e150a 82
    0x1d880030007000c0442079002550003e0701e4240043e44e1341d400c1c05d02881c002c01c001c00c2d010203540c2055800740111040350405858440361036101c05041c24881019585547c00703109060090341020041c507200300c1d050910440c5418a040f5400300444180e0060f503124400000100760f251f0f20035004000850740010554040b030381a007501a0003503104070440d070700892050081a0010b1990400c0d07500554002e9200c954082403d41041700804000304070a50210398600d1600209a00b0800e9901c20b038844c955040e00b40b110f1141c00340000b80c4050040c0d01c110400d10400c00003540c0b02d02001c1580005980c26800350f100e8190044035070091105500c2102103503400001486055042140925030381c1000304a540c1b907210615031184644118080420220041044003503002d600c079074202c640310280141888142d42d25012000d900707644480005640000502c11f1002c18010310126600c12108014a0481c40e078510759280100c0c80b50709102042d04000960300000035500e0314045070f00804142c5515 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 35624015 1250 35622765 35622767
    0x50706020d0b0108100303080a09050111121504090510090602040503011112010806010b070f02060405040203010b1308010e0a0f02280f0b07031e020a0606180509030702012c03030703 80
    0x2003060b802c031a00181c0c04001044e4001c1100030344005513501507071204080c2c0e48a02d40030b0003422481008540f40e640e507a000d11050920b8201422169402402031800d9040c032100d0010b8040900321040e100f545001c2c2d4030b10018200207005040140088030108401c8010b0a00d10003e00641e440203405500b4801c0180c6164a40802400801640f50802d17000d40d0300d0720343c600d58a035001d00030718452110030032038900841c404045405803148001c009515080e1904003003030a81c0c000b0ba00c0300d4040200825609400009850310f04060502003000700b01ca003038181d0041c3d0f55010241000361029004207112000c1d034444c0c2413900700c1c8128030380c1b03c040c802d10103c28458242801e44100d01c00c800e041c07100465524001000c6071420354165441403810001100713101d205035061540c0308154072810f80100e001500ca80242030041464010388051109001c0e440b1003a12401070810321075070010403640c0010707a0841c640d590725991200c610503030500e60081b4003a241001e0402c10382c5c9484085581e100301 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 35625265 1250 35624015 35624021
    0xc02010e12120a11061b0706060b0a05040302040c0c020114070c090615020706110606060d15031101110a0b0c090a120803010510080603060f0c090604080a03090f0308031501050706020d 81
    0x200d50941e00c20031413140c3c10720b110780c592100b07680e445180b0b07a41075101c4800514207000f420809005140c000b4440b5901d6400e95040e0b0b1003840070b01d02068000c1010800c6d0301e814441d03034000f81c80508048008403101c0d070000300542ca003070036901300201c0b0204415003800b07644076071030002d0803242c40108441030b00c451490581c41002e442420040c4114200030405074883c4880030b04200c924030080a403503c0d060100140c54000400402c041079032001400c84447c0c074184003c1c001c60250054a0010110703400042c820680100d03101480e03400f19681800052003103000f580d100014081d01e0791540c01100000c2d581700c000e03620810303000c06500210410300022200460403204112a111840600ca441c2501c540600321296a1b03d0b40001d00040d01490080038031b2036020034100b2910340381061190005401390840c0d0411100c5a11400f204010990413070701d200003811141460158007032440d550b001c12444014160640085c4004a4600a900500c181c5d00d245920507425074940603011501c00003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 35626515 1250 35625265 35625277
    0x207051e040e121903180308010806010b09011202070203031911060609060609090615040b0d0509030c07030f05070f030609050c040203090d0e060405060a022a010c02010e1212 77
    0x4a10702d0200c034120a100c00064500c0304800d00c1d0a003608000ca0030903085200a848415007080c162558030a000418204004122107842519005800d50400d4206441c04405810041000d101000130703004581c0c000000001600000c44007580d21007440c8042400d50290341000c0129181e0f00395500c10071a00107410503005000041116000ea944504110b6604002d85215412080401c102441801c00d9070502e640a100501087c6d200003450b14601c0c1e0382d81c0190300103214240081820541040c40c1c0c06a103400403503003401182441c2d0700505894071801e040c48020306000012215070f04000c0b0500c0b00c4801031041049900803a0765905205000c3c1080c00e808880c0c0c1c2c042c0080021840c0392a209490154511400078a80c00c41c5100b401d8407032110f11815180c0c00801440006515aa582e0050444031803a601408140260b030031a1260f90043e030138040269041d80c002c1c10100d0f42e014902c03070340054091178213540703c1c1128000304034a042c442c1d41e24095400741c0c0306640004c002800090803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 35627765 1250 35626515 35626519
    0x106030e0105160c020a0b0315120f0c060705070b0f0a0201150b0336010608060705040302030a15022206120b09040f0302120a03050f0603030a0906030203070207051e 73
    0x1110560040c40a401c842044812001c0b00442001d004202031280742c203054168400780540c08080d807680100a02c40d0011035003205a40500204403080341480d04068000386544001003102c0d2582462a03a00c0d42840c4010b14006c2c50b02141c00c50070312070204164002072580000c003558800175020107000301d60014004502643c00c00202e5040000d0101c1520100c0c2c8001e542a8203603294031502001c031050107123000c181d200c80003c0c40341003101034244103070388403140b1800024040d1920b01004e0412000130100014030605000801c096100071455503409a0720001191556000c012114001d005a05000380d192003003804400e030300e11145c1a51800d507445626955080c981c22040c0f901130fa80c14020307242d080703070014022900007400142113aa496229005454140349004031040301900b0128007000040d407550300380103190ba20030050a40000013034024600d00105044064801c1110b48211f00405500200092030381344240400340241000a01d508040030004515400c0100d010070640c2c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 35629015 1250 35627765 35627771
    0x30103060e0d0c12030e06010b0c0f120306011803050d11010b0607080702330913020304110904050f01020406051201050303040807030b0a15030602191d060d1b08010603 74
    0x1a08401c40001c0c006110040307591044450340503507030b070003d060000340346100c141030300d03035103552916407080c00081e000c0c15554180300e840d418112002880e19010000b44078154000343c2d6441c2e44101ca0b01d0449501040078208800602112540c01f040a50706038009003660103560100306500da481000c58407600442c00003402060140f9040100c50707ca006001410303100100545401070412450b92001c1820142c0001e4950620b646126103140c142c19101c1d1000390002001c1100d0b15110031080c90030016900c00310b0031440d15689480074901a1038805219103081400603040040801890302d00c01c1c4024000e540303e50307032010b0152031504000d1001103160700398000850141400010f0364100c0d20b80500810286103541c4514000400c00303010856a2a12000e9105403190b007000303940e0085125150040e0303111516002103003804052a2140304201d051f10843e117004181d1441c1d0101d60348c04640c5242d441c13001d0b4110340c000300391110011071402c16031407003100100d80003240b440c12a50180c50074 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 35630265 1250 35629015 35629031
    0x120d05040c05040c050417030d09030f0206071b0b060307090c050a02150f010314010207060912230f09010e0315101502060705071104060b0a110105061507081e03010306 74
    0x1206030b510040e6440c4c0001e40034801000104109060428140d80c14416241760554084001040c2d902460083c1c3c04100035904a211080d41001456030250140c505190a00390080400c10b005412000141040000c4000705845a0303040c42540000c180c4000e00300074034510520043d0094101566110140c010b00c100e42c1001c0d50400c40300c3d4803405043c0e0f00400d0b035a085a035120014104114111403541d400d0100d10f00150051003280a210302404024400a2200c0b8000b081c440411050102100700e0384a00b0500545000c2503a01481003a041240c607060a03e00486101c840c1c0d200710740d4584154480f85900044040b1101d0003181444041072090362181900954021400c000c600183e10060006014500c2440a003050920900c00107586103503503400542074403203640020b92841c50008903c8402a00b100c140000c0085007802030002e860400c00064481e064452821001240043e641c02000b0102c41250092007004200541d8070442c0304600160342c009000032240540340c4049 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 35631515 1250 35630265 35630269
    0x515030f1b0909160e040c080f0a030e030c04060909021f02100b0619030608010506010e0307120f020d05060108060609150d0303023c040501050301030303050603120d05040c05 77
    0x90900c14038030282001d50952407600034004040b200074001c950a002d80e00d01064601150103080d001172070070b6060054541000e0500c10044e0790300f80e01c900b007c1d81c040349804c00300c1d40380404c0319450703207426007031080c046c481c0c0c0c1e4080b0f03042440a80031694014070308000030071345440c66403102043d2802501d0001005580c51030000c4000703510646d510169015492031100300040e03800c034003c4900041c0c0ba083c14404d0300c0c8650000c02d42542c1e00031004c6034450030240280c001c00d1041a60001007442e0032102680b0580120f52102c07024002c06401035219540c0000303004d10b40d0410080c060b80501050b401e4507190400607102c0f6002e000704640e40c000d1001080c0c191420300040ca002c0c030318001c04652038000c5c41c0d00b00010804808011400d164080c0030844c41d0a040c16003007a4900303031099041c1d41e40d5080414000988644941803164088148001d1180d80d034028162419664503040005140e11100002450308001786141c0010f41e100144070b0301c154045e90022800749100780422004541c444003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 35632765 1250 35631515 35631523
    0x17031c090314030405010603020d0f050d090b0717070503070b0f010e0105060409021605070609051306030503030105100302070602040902090103050f09060601050a090f06050901020d02010203010b070f060e010515030f 95
    0x64001108480d0116009000382d004641040c49038000041c0b244d5030350302046038150412400d03030703002880c55045001d0190500c200100e0100614180042c41c1c01e00345004c50381d02500902501c1410180355030704004200408990216030890b0841c1e03143c1c0b0309490b0030400a18112109070058542c0c2e000010050140c2210728140d400042116080c603007003628007402500315004c08104040003080180210f0300500482d4090b0620b44e84130010f003030604090182d4200c0426650200728034108e41040400c01c0441500c2c1034407000c50710061400e80910044000c0c1c060042c010340076510000703002800c5103031680204401102a203080c005a40c40c1152403001141c111024001c1360415400038074035620800080c00d41c000c1d9410458801c5450301d03628881c255035908410040f400c002a050785a603010407000801100a1000b540f40d0341c100510b200c2e0701d00400c0e5005000711641c00e440c104211190f00442050000c1100800031480c0c0003900090090307100000c44c0c0a80102d07501040481c00200d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 35634015 1250 35632765 35632781
    0x92103090e0c04032d050d11030c060a050405070306020a0302030105010801090b01090306110f030406020403020f03030301150f03020f12040201090510080606070804030c0603050a06060c120309080417031c 90
    0x7010b030500345455600e403c042c060345c0101d50f0101c0c1000754000c548034102c40080200c01800b90000302580e1030382030070203400300d400c12050b921150300c10700c44980035041c00911180d0221805001180a403540d01c0c00c0743c6440e05640006200d14004190080b03a551f050340a1030480d40300340e80c1c49141d66aa40c1c0114100c0d81c01494050005108002c18404105150841403640e0306219040e403030001152800c1099400070b80c1c0413070f603a40d0005009c00c250714001c408010129000c4001e94503652502e104810041c800480308000d202018200b44401400b9605640305507002c0d0a5003a035903c682a000c41040204540490214101440c0800d00d400d00c02e1100031500c6290300c170b103011038903214100550754000c240212003030081044007100140b600412400140160340b03020400d0b0078040d0f5404107030f8520780c01a0081103040c10902004c20307004189a02043c81d1810002241240303400d010815100c5c070703000800c01107554800f641d41890000002d001e05070300002c886031510840307000750054071290 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 35635265 1250 35634015 35634031
    0x15040b06040303051909080f1c0806100320120f0709060f050d090c0b13080a0305040302040c09030219030501060f0803030610020c03060a060905070908031603092103090e 75
    0x280300b00f202d11100000d0422411046040c0f100c4007507514a007040c81e101800400c2c0907281c0100b10f801d807080c410340685810780509c41c20325a144d0b00c6e10601040403000c400102608050700c07207035040d41042c4c05080b41c0e45480b0703440c3d01c9180d032000c100d440c0010060301950000c1701404500c00084803a40300710448019110075a450502c9403c10250450f8541c00c0401e00040146c3d40340030001c0041e03080404c06000340303c6603012544648114580307445803131880e8040880740d08004076080009900c8821a4203aa6044800040882c90079034200c1b40f41095801c02500214241c6000343d040441024100460303205e40001c4c4111501c9803004241e000e4144640d260550003400498418640306484924481c0c80d41704031540d20510000091401070305070b4112503401d940d00c04c00d1202010034000c135503000c81d050408800d403a10f88502c050356071050460400c000405000440c0030507208540303420040030b56080d99000d0b4101c1600000640c0c40ca281c0407808100c6a02d00083c0d5191030000c82c1d8030030549 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 35636515 1250 35635265 35635267
    0xd0c0b0106030c090905100e07021203010b03190504050309040b040204030209060907020a061104030210020a02010801090509010e252102060a05040506030907150c0b16031415040b0604030305 84
    0xc1c060040d0040c0003201c0040d403d102d0f0301c0201040b600c100784140c503c00c11161220800c031030319004039a610000080e204400715007140e0755030440702c00c40000b00c90455101050843e5650780c1d803038084841c0001c240c1c2c102c072898101014041801000809048141d008440400203e40f8807401c0208900c0f42d4480290030401d0792000450610700608140e07401843e80c010f4500381c00c0c1c0b40c1e448030225568401801c10000c6d003c01e050056007040e0124a10000180c00140003103c6140c0020700764000c1403080095650300c60002424515080d00820b040314850b400322480940300000d8058607a0240d4100e00021101c140e0001d00607000e003081207144c884210300407014000d15000d010031944130715040340512030204000106c0d616014000d5114100043c00303441a03500701911120002101c22882b4204444541c0c0300340814480c40701250405016650386015010550080e0064040d0001c4034001503a80000c000401512040502e07100c401202c017001401807000c200029806540030280001e08 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 35637765 1250 35636515 35636519
    0x5011b020a0b090f0d0f0c0609180504050f0a0b010302040e06060108070e040213150305090102090102030d02180405010f03051216080702010c051c02060603071406071e12020d0c0b01 80
    0x101c15004007141d0001400040514804e13001041c070f1000151801c80d410106100390006001348112014050001803400000f420700d000201032046000c9800c0e4000e02e03076504003003001c0003c20840040240104015900f42c1001800d2510b030300c03402444160f01880c10024400b0540801180e4680b045105854140c01754960310380803a070405100d0308403038000d40d00304908a0960045103801c5c004113010052140e0404041c13000030144c031405800650581c0c0140852001030b83c003c0141d40d44520b040034011307126a110406440003c00d0902d07201d410a2801d030010644070071325680c40c0103490150085580001d03001c070201e6024170407035555250904080740d508002030f4108004045190052500816900d8503842c0d40d410444046c103a40390240d0201207003594141c0601015030321600403005004168501103c0c0d1940c1c0003d403c03081d100702000624101001060a803400c10401d100a400c02128158034010340344d01510400312000d449030081e40010390344100041c008182d41310040e42000d034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 35639015 1250 35637765 35637779
    0x305120a03060320030c09040201231207020f0d0509010206010603050a0f1b030e0c0603062101020f0703080a0b0a03150f2903070b0304110607120905011b020a 70
    0x9040459003404054558000101041100c002c080703000e00b00c0c42201082070012000c1518140e545054a4001c025070320070000940e0300b041c00d03d00000a01100707408807071000541e20080b4810070403034000d029001c4040c0621158005086283c802104c021140c4071044c41c80191018064a04140e0040e885080140300c0301d8841d40200e50001c0319100c0100307802e030200c20b011040c0d0302a4100311f00c0711a007581da00035a443d07050080c1c804d01034100c0040c1044600e1034001c150240300c008c1403940540d4070307030070100a4280c61701a240064640e590085460b000742801e9114654000c0d03105400040d01000801c034804068030840a014400901d40c1c0c3c04140346176600100586120381f650009a030751100001014240c1c00b41e0110340c850040700d00b24942440940044c031300c42d44140d850180d44000d20501011022100b00d036002500b105805822001200c001100c0c0e10036242c1c01020302e0a0300703039034881c0250420108020b5900988641d00b28004941840b4040008d00c180070358400d02500007007000c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 35640265 1250 35639015 35639017
    0x30b0a020904020408100b150c0303011a0909010b04031a010501050703110102090a0b0c060a0902030a1e1406040c05042304020301020d06081c08041208090c0a0f170304030512 77
    0x5078405003002d410140e8542e0002e051072100319880100588542c4c0030f14407440c0c6030131001030904010010b203040c00c230707818400c503901d02050141312805000401c01d000c51910040c01da6019000c010944400c075038503040c0002403600207100c2222104610300c02480303404407007001c4506950069549504280300380d102212841945400001555400c120b000816120007120030094020654000d9542c41c070340c00c080e8030f030410040450070868684119480103a402081940d0300940001d0140c1e00b00b03824401c4d07416690b20040d0014010b01d03554090340c201000c04169948a1406440b4052840c0d07035841c1072105032524168401c041c1502c030f051004040d08507120803038015002400040c00d0000c0003144004503981c2d60450078480d40f01100d50b14000c02404025088100c59180905d1141080c4d502c004012802d0781c14003051100110000e61a480d08005440c4966001050591910341d03c030718020b011400c900034102081a03210105445500000031074040320303403000052046018044c510a11 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 35641515 1250 35640265 35640277
    0xd0e011b0e1201020d0902010909050c04030201140c01021b0105070e010906030c110601081c1d0904020102030c0604060501051507050d0807050d1407030c0c11010302030603120d0606020c03030301030b0a02 90
    0x8807145644021070703602c40901c094280e450b100000050f5807655030001401c6e1050a50200c94001c0c100001c0011800c1c01000b03a508032982820a40c500c01c481405049460180d03103243d0865610103d004661699004103000031046d03100004c210584900b9802c450b08900801014080b031888902001200c3c4268043c1500b1903041c640201400382881e0503a003054403c0e808081954020078038400c10056044c08000b009060b405c1000500030100340050410b8801e0340402c0c840c844000c00181564024003c58248040c00015078aa6180034904180102028010075000c0c042c081b034800303150070121007120681600207000b0226000d0380342c03045890f08002044401000824042403a580c05203005042e040840701c15000d0640c035002c240201210310f44c7d9480000c202c1c0241c900704c082500d828890100445c02c2c80d01603606d903a088003007441c0104103a1304041d001c034001200180403d107944190141c800039429950054260020103590340021300014281501a00100345684025030007054 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 35642765 1250 35641515 35641519
    0xa03080a0b090c0a0201060b0c0703020f01030b030303040629010215070c02060304080703031406010516030212040311040501050904020303030a18080d051501090f030f02040207020402040b0d0e011b0e 88
    0xe000401080450803440c03040d0f03036402c0a1100814510343c03d0b5028052000a40004001075080c040d202503040ea44002501c00a40104010000c00038a64400d41002d0030203200541242d56a06092400c0d900400c0301100c6140820f211080d07091000680280c01d90034a20141d00408203130152480d8003c5284e1f01402160500c85541c100000589a1030b0245200e14007503246c10361115201e08010f010f881c8145292000c1c0c000079820445183c0e00801030304c003e80c0d4a401c054000c04100c0c03030140d141500a1000c020410000f103400401c103d00300c52001034612040e0b0303081c80396998400074418210000d9600a5042d0001d000180e401c46c07895100da448040514140030f125006a21901c0303030380e0b0042340c010301c000342c590081003180500000c040f100004e080c684500c0c140d1401c03006c40081442e0f400000d00290307901907002c3c00c1d9561501603c03e0301d0b800400865803142d031070034420041e43c0605011041c0900340489c05443c0c0b04180302c0c02c035103021141194192502c103070008850500c0d0113880c1c16 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 35644015 1250 35642765 35642771
    0x41d0a0207020a0308031f0f03030804060e071427061903021306061707021b03070302060409050402010f03021e0c01020d050405012f04050f1203070308010e0f0403020a03080a 77
    0x1d40582d450140d514010342c0980c08141c2e0780d0415510f1505110319401d03880c0c1d02843c0700c0c44104680031070780820b1401c5035018034101003070351945e15060b4042c100c2c180f01c07a400c6100348000440c1040b1804901140a10200d420032800380180030600c81c0c0d03402c9520382100c3d00806400040307550a141200b50404d41040503824011903c2c0d0b40024a2040320442c032503403480e6655814800300c2c1c0c10607140741c1030000a0800c185a40381400f4029900c4c1c6070202c10302103044d0040d0410f52a51410070501300038543c000c024580320703601c4940d400018042140d06a001604007040510014068404c8905003855101590100050304e070402c1c400f030340b12510882c1d55650070807140030300c10031511400b40958484d0002096007981007016150111800e924100c211821010bd070fa04207100c5000c490440d2401d85650040082c1c4800141c445800d500740034034076000005880c0b00f0968000384290588a070140f580901c1d40b601c161140380400211001000369000d402103c0c0468010700c100303507104075205004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 35645265 1250 35644015 35644027
    0x20312010b03040c08060412030f060b030f070f11030403080319020309010b0301051503060a0b010203040503100c080a0c05030714090a030609050c0108060102071701020f160201030e03041d0a02 85
    0x162440000341d10103041d0752400b105000c20400c44507100401840404010101800c050f1204600b00260407000010700d907131203141440c60505074010400800c0e07105800f07916450043e0481c0c89a00c0c1c100c40c1c040000d14004c8103c1c00c0d241c0240d070386401500e0008015410a0300f581d8512030340740d0000c0c2c0448c03040422291514a8850b950000310302c1011801e002245009100c400d1500352030019041080d0021010003400542d100055010f41c850010304000c5103204042006030304510407500306039014024502c1040f240803158006604001d810b0340d5881d0f169403190564402c96049281c40400980d0400205110b644590f500240b010140c0c00c1051030000814006171b001109a4000c41d0010748801c0c0d48424410180008035441c0401e00301010246080b4000075100d9009002d01c90880d199001558030228095043e1079101c00182c0c001641e5903a50003401c1d0f54420450812070001f03050240108070b8500c00300644003140c07825428800c040a00e05c0d0820000c0000178845903c0c607a0038411 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 35646515 1250 35645265 35645287
    0x1d01020a081209120c0c03010b060319020d0902100503090d05070317180f0c0307050f060f0d1b0306080d0c0507120611030f04140a020303030a0e030c15070908060c0301060c030203 79
    0x24600c0f403008074010014140c095050600b92940409e116108500070700802c26082001580b00e4849801c40c407006aa504403480001c000f008800c201135040349030a58200a0107030040b0003940070b50314180c121808213150220441c0c541c8240c80c030040005000104c0f190307014403142811600900c41d80c0e014801304c00c40118040c0380c50704500c1045003542c040d0501c2c8009007818440003010b4002511601890307200c2c10080340d07152107514206004440005861900745460380d100205140341882c4235010101901f00045c0034201707500072001280a03060745480c0e0306000f43d0074100a282c0c040007910700a485e01541141142c05070200b51022500c409640804d901e4480095120b0080003012076400d04050401c03147d182c01c242c5800b50036503c05ca9100016907000010b49030f200c0c05403000441d101c80c10600070780c1140903026186000b4440d844006801c03203460341d207140c403840032503840c04860743c0d0b680059952810705031503005410342c0400c01405100c0c0301c0c40455030307014000d0044074a04070608203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 35647765 1250 35646515 35646517
    0x50a030504050f0a150e060402030735010507110109210210020403061a030a0b0411010e030d020c1009050109031104110408060402030c0103022a010e010c1d01020a08120912 76
    0x103c91052029004045c403100e14480c0d070b0140c00811b03000b007416180960100741e94003000d000d24210309000604220003c0900349044219004d02c50410384910040040c0a000e400c3c01c0d5130100c04181458031480c4400014880e4616a1317400c00c04061414020a61113440150080000f030214068490401c1055285000400c0103500c0b5040c001040b048080701081c00a40c0300001c103100f504a22004000310f2105241a50801e80103140d1460200c1540016641540c0380e60b85541c05001c0c80b42c01056054000c07401c00802102914528092025207404407022501070003502c2c04116018010f0000c5200005038141d05d25014000040f60485148500c61075003142d801014564006401c00045040500900f03450010a0034158100038004c5050121000b00c0c64000c1e00d16040400e00810860094000c0050b40020100800000c0f018800003803084400780c2d82022205001010009254400941c00000d0340c2c0084245042c0902e600c400c43c1c6862002d040c2504034860808411200d288800c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 35649015 1250 35647765 35647783
    0x151201020f04030605070206040b0103120c02040618060b09031011120906040c09020f0a03020c12030a09110609010206040305070c050a181a03030301150201090c060503061503010501050a030504050f 87
    0x381c40d4495145240c0001a0703000204001d08640042003404005030401501c039064903400403160300342d604480b408070780070320811303201030740c00350900500040c22004a000803400302d40c41d5000740503140d11104031102e284603c1840310b825910007801058a415030b50b01419103000301003d95468407a0803454541515001d40e4044000d80045081c4810441004800c0c801070640800940c01e0290b42d10300b8150758050704840b042030503000540c10400304014080f4008a2903d0203159407207041600b80040103001d40402107403c2c40c0711501c141071a00d4003d0980e00701d0b00c8140d00401c15a596540c040718280c00c2240b044034010900c140100d200d0340e07030310300020142c848083e13585003001307911b102403081ea15400d148080491010021401d251008070441e4190761450084c1010a0059401280180340406002d40a418900c0340800c8055101d0000d5006aa0440c0d115110307014140c1c07000068030003845102d0100707108101400c03c4031f01070342205922a0249054400700c5840d4071281d42426054 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 35650265 1250 35649015 35649037
    0x5060c01240501120e0c0108041515150504050d11011e0203030a05070c030c03050a0207030506160e0108090a06320711010c0905040213050a120c050d020915120102 72
    0x1e46414486540e2010a085941031101d00510509002c841100d45500798124a41e04203c446000100ad0018520b125248558005020051601c5030304042c0d803410454008c80c02594205000810514807807019542aa000100b141550008a541d00c0041030400300480303052210b0528011181386401a40c8141c091198010b503547c0d20b0002c0310201140c40c001c0c0410f05002203c0d52200100b9440700740c3c102069410b080035a912910344a043c1c4c40d140d019400140301d44944410854a0120000310702e0520016071500d0703e400e9042e80054641301c9048643d500c0a500ca00c4503140130609541000c405590701407800b201c100054800c60b071803800d0700990300c07040031440300900451943c40f89820401c60540d1008218400c11400000c012940a1182034401d0360041080204a03425840c0c000003020020900c00c84941d444450421100070240c080d590981e480e8000504c41c10501c2842c0c0072558010621070950350340220014460308150701d5a80c10890101e40c00107590001d100400c0302c00d400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 35651515 1250 35650265 35650331
    0x308041203030605040612020112150807050307050a030b1b0d090302010203040b09190803090f150f090111030103061a090705040305120c0307020904050a0b04080408010b0102010b0a05060c01 84
    0x5035040103003da800590142d40142d00c0d1140c01c1018800312640c0c0600035034240707040c8085c40c20190703030b803030142800c0c0c60040e6181c5c80c81100001c0038a0009051800c40c1e00980544842d1a6a80d003003007007410461002420f982c1d00040003800070100c82d40d40d080d0902e91425500d042400b10b04080302143c10444c0f0441c01344c0c3d4000b0501051101c060302882d4082d103114010b158182220420407080400210020301e01036021010400102d0140900d0f000c501142e0221503941d4000814400311440c00d50306e10f03440201f01004103143e00411301401c052460400400e0b80303940d02e1503030307204014038440d05400104100c400700000c05646003510b590252895a84241c1c40b1410342c00c08174142084025102203c041c104403100751510040103450b19250100d58003006640d41d0700340715041c01806c803001000e40100c041040300f04445240500151101070000b00881c40d038100042e8225254000e180ea80240040410803140c40d014004103060108500040f42c2581185540405110b26409507881041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 35652765 1250 35651515 35651549
    0xc05060117190201020d030207080c01050c0a08150901030809030109050607021b0603090606010e120109030201090c0503010e210c0304031a1006050304080a030912080105040b0d020310020c07030804 87
    0x1000840b03481e0a0000c00c0b002600900e80c0080e5441d01001c40010505402182203070a05c1184000c0c1d13648034000400034040707884c01040e5090a41e010701a120049501500801d8403035100340f0304540780d8003001d400e01209900319180e0604a03003241100075410b64a4110140c0045c1c0c0a002060184c8200c0c0c000709480c405c0c9032295801021b0b006005d83c05440180104a04401c001801c00c0e00b040003800c00b400c1e070503000c10200314452904a1140d0156082245144c10194150310400c1d485000748003a414450321241014280e413940103640300c0d1640301035540c4030b400425103900d003201003502a0151910484550190440d000f5520a075034041d107a4014203a0746000034461030307005408001c507505043c1480d00207401e50002070005001e000d800300740080e40502030341c460500280c10591a11220b00055402054600b00740265401107007051844016424485803160045600601074400c4001e40080800290055520109288106a4008013280c0c0603001403019011620407c06a90 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 35654015 1250 35652765 35652809
    0x6020a0c02010f030213090507031d0c0108180604060b0301020c07060e090a0e03030c3a11040b09060d150608070e15070209100e0a06050a080a0305030609070c050601 73
    0x1043c1018020706050040064103e807071280e04106095401214001a65858030076045000301202000510031018200560100c494001400e00011009a0710603000e030390b8186151030802040107800e03000e940004042000a00030350030010000b4006000103040ca0840c002841c54220960b00c403e0124a030300703242041c50b04080c0542c561280d0385c82400c0c0010900c15812507641c4c0300062482080301070126030607415000704142100c04401c403021000600d01d0003000d18084500c028140070109d03140a100d4544202c0c50004d940032a81540c121a003480300801c14441150300000c0c00b05c1a03240d50b60030340c0da692511503902401070442959030301c080c2c0c50700d8580a045500340020f82449080e0300d500c0080b01c04800c03011261f01c10350641e0581c001341c590f1210100d94821540203403c0a03100c0070200410803890358080d1040b2034013169601c003015510b80200b51600d0b00f122002d00000c2e4101300103a100d09010b40e00941101036481c0c01c042c90245612980e0038000287c000241e111040c0034080b40807 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 35655265 1250 35654015 35654027
    0x90117060a090b07140d060b0405120604030f030b12030703020f0d09031104020d0b0306041b050d023102070606060908030c100e0a0516030201080f0408042106020a0c0201 75
    0x30301500c1003241c0b40355a00e62034095403000700b1200420003880904c00029451500380c079003080f15400d0900070562504800001908180145801041c048800e180b065500007052401950162100c00c20703421080411409808515070f00c1e50000641e044882c51564201700500645029901a24078202030010560a05001042102c2040351411f0b0910100c0c10004039010018000c4900580c1c80e181c4141107406070540c9010a9894000c1c1010407003844100740714100600c070440e041600c8940c85008004074080c118001070b4002007000a454804d081c10802c84841c50801500c007819050031055400c240e0380201801c0b1040b03501e030101003150303581000303a42003e051080c1c007550801b5101d41101d03507121261410790b0031854650a2800b0b21000a0082d009030f80e404ca801d444a6030004907554050a001e07100490008031050300058a081038441c10070701665102c1d070190314250ac0d007102048086d444c002101d444100d030b140100001032080c401020018132540340d207105401d25000242103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 35656515 1250 35655265 35655271
    0x9010c0f0b071e0801050603040609120206010e090304060e04113609010501020a030c02010e060a0216090c050d050919060c120b06090904080c060c04080105070e090a1a09011706 78
    0x1855624110601c00d184e048004541903074810364880ba141d0780d4030704008002d0406450080c200c1005440305108099000c9460f038140c2d40c000c04000c041c0c3d190030803020b550307205d5031241ca00000c3d0086002c030024646078222100e2001b400343c4860400010700710760700702e9404841e0903000c090141c08101500c0c442e41960713140440303030454080c1015850540003035102c001c4018010100040c0c030144c441160b000e485903400c80c40c0080c01c0c2c20784a8030700c1070001c1c1d50707401100c1c01c529820254240001d0030716124000c003400d410b6250355440c2030a00704da0803180038200240c9100300c2d60082d890104940038400d6012441e81d40201e00200350340c048040c018103406c0010100091150070062009941c0e203e20382200e000200580d01c403421170f5900e092240e41030041104000f1580218414440040708000c040c0c002c0c0c58801c0004c002c03036100c446003660741160060f40c2e5504540072500207140c840d02ca6104031440c1d030344030100d8004d450760000012540300e401d8010080f03440d038a05114410344c404021240d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 35657765 1250 35656515 35656547
    0x50111030a0b0f09011202130203011d01090b061b070e04060b090f0c0415050d1503050d0806030d030203060d050d0201150b130b160503030103050105180109110609010c0f0b07 77
    0xc94503840c0111354114014003900300820002e441000454840c41600c44042c0313900c5604645951b1a4445032134281c00042c1d80c01c00401c50304c0000b241440320752044450300c1a00138400c0b4985151500f8409001220810b18440b0340600000003684141c6400038600c00c0b4890400040d600840104000c4042d0024000352031340300c41c140402a21660b00001c0b9010b407200c0f441c8450b180d01500d80122958422200b01c00319484c100084a4508041c1c0350725901564031500c1602d5034030900c079608a40d5040c00b150f81ca03034503a02214032107071440d00a9005681296000c2c003a006541502c3c0c582c545411200c01c5000010313903488040030790104441420b035001d0400940818079280194103118040e1031076000e021800c801c0001c2100c4d104000d108480d51560307106056944a6035281040350081400b1900d010604031160400c42c800c800c1803051800c020b90102c1d501000e80300b41d41c18880c10b41c00040b07165042c0507680c400500403174150600720006030704c00d550f2100c46103000c00006040c80c00384441070f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 35659015 1250 35657765 35657779
    0xe070201020c0706110a0206041d1806070f1403070f0305070504050d0602030702031e0901030b0108091902011b0804050a050406050a0909020105130e06040b0a06020c09040f050111030a0b 82
    0x11580c0039000c20f41e00112409450701c4c80c2800310b001c220604020040500a521003400200050205270f2034010910128003610302e900955a060345c520600c4a00c1e03071402400f6042600004e0981c1d003c1e0683d062894424500802c0d158044450181c090b4820b0310006c02265000301c1003000603500d8082d5517841011850805c0c00c1c03510381404241e94890f800c00c000c104540220001d03c20b58803c2040d6102141c03502081d21680182440034082a4802054180002e044c044000c2095024441040c01960710200520060031011002d0401030200d42040b410801b00801c0c040c504054608441100307805520015600c1c4d02c0e20b020040140560740c045402541040010000c036a99050728008940d60b040e0702060340b203500d02c0101e60f20322540c17400c01d466413466200850064081003119106074001e03101003046130030721030401c0780e400b900d8410040145d01104080f80c003418164080ea801c58800d984441000c0025911142900c610b824070070200e049c080100310100010380515424200291240 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 35660265 1250 35659015 35659027
    0x110307050f04050408131203090501020106030308011809170904140403050a080709050a09140604060302100c030c02180403090906030b0601030b010e0d030906030b030f15040804080d0203040e07020102 88
    0x124050201d01d8071600e1145594100103002d2045000c200c49480090001c41440c41c2c0d00d8062007440b0048410302500061038004002c0382c107500510820042e01c8d01a1500b04a0740e00e000c04a4402012949041c02c0b590b85445d0ba14001601070201281d07101500c05910303441d85000c1d800d01041341c14001c0041801d005030000d000229030490102c0e92005820b1402402c1581d40c03040c19941d16005511139900f20b011024006001090707540070180b0f4203840388610003207880f040200700a5660902020f50710441c01240842c85501400b4941a010303ca0b080c110202d4100d03400164601c0d840000b240c0c031080300401044100350f800746045001e45084041001b00700e007103450b02c2c4801ca04c01400541815501c001660040e070182032280c00d2a040240010712000d06458010a000e440717210303400c0802d050650b03115403890301003641c0050035884030050060314507058410320030a102800a8070b10040801001c102c4a100380030000303818505130002c581d12450000c89001e0580d0040c00c6c3c908592043c450 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 35661515 1250 35660265 35660269
    0x501090809040b03010921020a1401140901020a020c060d060e0c0703080603030a09030227042a060c0204050a140906011a0a1706030f070905090d0201020304021c060603080309030711030705 83
    0x25510341f4840942c2c3d200d11840a12005925090f400c45025020f03a002101d03080504070150010304052803055800b4213662100e0025600740e0081440540245c1c025090000c0541005c00c06000c7d40c6c50002c2010403016901c41e01d0740e200318025111104200d0340052500241900105069001403003500103610304545024018043d41d031030b0000030f05c100c42045844400d0700c1d10300c0304000451072150328100d02e0305003443c08400e480c141128030011007096450800d402200c5000a80c11035006403035080210aa40c0d007000003e0000038004160555106204071007525403000721881101d07504e0043c01c465040c501c0012100c4202d0710103510341e08041140c050345591107541e0201040603101c13694410b0700c40100003800c043c2000114400d0b03104006000500100580045010350b00c941c081c0c50610f000c0d014224203074807044801130740000641105600104054480e404041d024007000100d9907200e0f501c8000c1644262401482030b0b102285c545c090000c5803131288007100044000f00f00592030500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 35662765 1250 35661515 35661533
    0x60d0209011a09040c0c0501050108070810110c03040305060415200309010e0313030201080f09070501081801050c0304061505010806040e030c070303020d08010801151206090501090809040b030109 86
    0x81021038082c260b201d5516a040600361620070400030302c00d11081e5003c0000800032641440c081da0030350300b407038000a106072001c560981560a00710150400382102452040038103460b040d02c6400580c1045020341c8100c007880580080c41c850805400c0c9804c080c2400c1d00e03128840744008101c03500d490310889148041110303110440801160300d5440e540d404d98120300504c100358100415000014040e00c0904058503440180d91003625a00f50f16242c0224030400b214040300ca8018950168106101543c011001c2c154400c0c401c40200d0409130b900c010310381c03c1d2441922401400c54010040c0801c002e1140641007a000e000031203442014640f5000030040345024000d240500d1f551021501a02c50900403101d0051804040786d461030355a19009684180010404000562140000c1090501805000111620b41c0d00060513982414001c60400208003021911590b583c08510300103070b02030041051203402401325507101d105420501c000d8030300b0201c00c1d0b40319926003070b00c900c00a18180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 35664015 1250 35662765 35662769
    0x20a1706010f080601021009080a09060804080d05041b06180503010b030c0907030204030804080a0201034514060709050301060b040311030102040323191101080712020c010e0105060d020901 83
    0x3ca440c1060b900c0d04001070b0706011080310101c00d550f0805140c0c1c400d01c514174000345400d9045a4900803480d940d12000c0b80c81130030503100140517110422505030b40349001e400103a006070207440c03044080c030803500314504200c086511801c0454180c2041124210b090100b0f4801060709800a2100c1808440025150441c1524107441807042602040d00144a58181d40246901209150340c907611221216994a03140804030b001a052814401c104152a511803107a02c80102103010120411001303c00d14410955030300b0610382d01d004031900810000c940c20041034bd2a4400b40000e801e00d101c0003030a02c0b00303641050380268100301d03080140c2106d0b807044a089075007040072401030f101d80c00c0010b80a4800e48e440540001c410202221003d20740006040340381c01c28404461401100c000d040c50881d00000001d012110301e400110f2042d405044ca00d94403210900e4103554203543c2c07201d403504a81092000700007581d55032036104071a02c024880c064110344229031500381021180d0014985841c14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 35665265 1250 35664015 35664017
    0xf04020907030f06090204030303020304050705060c0601061b02040c080610020304060e060702030a0c03050304090b0f1008070c1e0201081b04060f050d320606030703021318020a1706010f 82
    0x80d84100d201e9460325800302c006405e901e0030a43d551030352408e005010390001d5400351124010b0100020381480c203041201c010781116406031401e40c6c42c00034183c03520341d03108122440300c4c007148500c00d006a50b140324480d842406038461801d14104503091010908080b410142550b03c00c10051090b00c1d005031a2040002044410740da0340d04503807000c00e0406401040c01050488038032008000c001001c4007400c21354214500030050b00710700341d04004c076030a00096030301d400041004031414518851070000b580103c090820f551000700d43d0340c814829001c40d00d02ca5800c100203040b110119030340540781903001007182010350010310168558034010b125600c180c0040c4844410b8031034000c2c1c007d00035904414001c40c0c0070030810104140c0d40080c00c000b00240600c2c0c9206120840b100c101c403044c00b50041c00084c2c1124210365610f00c0941c000d50001c141c2072020700e9802c0d030002d21142c48040300c841e400140c00025841c0c0300c141c54090800d00070b04e41400c0308ad548030b1080001d6a61300c010710b40070f18129 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 35666515 1250 35665265 35665271
    0x10e090c0f030613080c010c05041a04050904020120060702031c14010b0703300c0513090b120307062703020a0303020f0c030a0306031101090612090201020c0d03020705090f0402090703 81
    0x9038a0500002e111b902518041c55090100000341c09400c030019004079555191b02c10009251030258013000c1c419400746c15400f14150001c1005541f00d40d07044009100c0303e405c40c1c41d20b020a0000c192800d0411110000141e10000d041e4280204981e40c050028425100c14489130a826078a05484c03d414000c00994440128900040c10310034400c10490a040d41201043c040d06c894005110901c10404c060002e428000380c45d200510030000c0b16904903016001a11560802031854080e007021031072103520101001c41c45000e18401c0c40200980d900c0740d0400101a45000c18101001d14426915180030031000f0404d004290045010f404046c0d25260050f030745c0b060902585c0c40f6010300210750009101c00f05d40a903c0e650503512400c2928026914a0710604c0d11000440368030312070f0f01864000500e4140f13845000d05494000100392072050041d11038260300c4a010583e021101d0006800582c001d00040146047c030b45100e9401281c81240c222040c41d2640204156a0002d0008010155 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 35667765 1250 35666515 35666551
    0x3090c0315021209060708070c05030307080403020c030114060a050409020616020d0b01080a170a020717010603060504030c0606150c0206160503031e0a090309061b0605010e090c0f0306 81
    0x101c0c5504840c90300c2c800002d00811803c0c0021420b940e01c40480d910b401040d050b0700400e084501421213900f51645c007100852640d560303000100c0f107041c00070740100e06510a00542d00c001d594207005180c03059407040341d0503603507151620821440104583c4110300a074030340080341d400340e100c51080b91140a600354005204031014400304500704400903001e03018550010020032030001c00305480c1d111701d000e002c10050410708003240e50440e00c40c1c0d050140260384015800c00450380010042c400c1c60390403500000d03245070b0300d40750036054490840342200018903141100c81000703841d01c10030001c2d200e039524681843c0d80c6004054a44039a080d006071082d0404144d1141c00d99000340c54048059124040c6c0e612403e00070700f90841841c01e03034580001034410074005a40641d861150b1100342d40c05030b44865155182403019140c051049a56410b060980060759021424901401e8003c201c0c04a4040061500194940c109101c0c455550b204100500b8962250754000540c00e03040304107444980c060360 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 35669015 1250 35667765 35667803
    0xd0e1f081303260103020306100609170f01060b030103030f0302181507050106060807030b0114040501080c040e011212030c0c020405090304090908040608180a030f0c050a0605011503090c03 83
    0x840030301401e407144031800c1c2503c61155a00d090f014101d900c240d080300c40b141c41c0c45e80400b4001d035160203480d0000300a0001045600361007201c0b442c0010b5100186d90091100c1a0391500307443e03254100740c41104000004004060740210b51103891281c902d0f0860602400108800640c610b000c8103c0c460103c03500380100308a0181c045411040e40100204522036544101400301d031002c403112400320380352104000540d40200c088900e4014841c4507589424140001034907411009005c1d442000d0302800301090b1080c02042440c003030401300c6811203044000345450010816011300f80010103080c103410380701c00d98022000945059040381d0200311a95145d0200380340d801142d02180041e030512241c0e00a0010460080c400d685080e038514a03203666030b0000b5001490b9800075000b05034040501e07030001c00e1081c012408509442d2070b000d070164440780c850300e1825180341004d5400c01d551700010440e18403210b0881c800351945d41400c1c041483c103074031101d801a04070720001d8140303080a142c0841074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 35670265 1250 35669015 35669027
    0x50d0b040b0909160b0703051603020106170703020a060518040902030c0a0f14040b090f07020106030b011d0601020609030706051b03010b0c0c040510031407080d0e1f081303 76
    0x710360181c509180d40c64a001d03040d40d6000c01000c0c40c800c60701d0f1100f005c500703000da440c1110307100d50301a11258600304041c080200c00c50703019042501107542e01e40011400c151540c5807880c2003440b81c001070120b60f080d4010000c0303400141c4e1141042c0a810050440c080c0341340585400b4a1504880020f0a0041d0f400480d062040e5030500550010f04604046070007281e6410b8002a2500b05514170102e8040e402400201e551300d01f91113500c008224005a808401006c135154007a42c04d00c004100d0560300d40c1d03140524602030300803200301400340d098241524912424294850400d10080040d82030440181d0740300e214015028000503100c0700040c900c0310203038032403160802c401c01485540f0f613545c0c01141d0141d00000034040c0d25005545040f0749030302d000c4c080c2178007840715005c076203903491710b59503421604490716031446050f0b005140000400f4403003440310304040480d40d02d07480c0010255404000f038951401114009138140100d480745002c5c0d200012980c0031101c820300c40142c1c0b620741001d60700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 35671515 1250 35670265 35670281
    0x901030608030f0403050106050906030307080d0204030209180f0106062c03121216090e130203100f0b090412080702070801150306050609040b0601051803010207050a02010915050d0b04 81
    0x40752100007084040c018003030000340200d0303029030002c100e52911203042014003c07090303890a074036134801d0040744007241010009041d240d50b0300038010b01c0c040da69404545e2551084030103040e8100c5013201011460401e010f598640341d5814020010a41440c0014181c04004031075038008440c0300e5078040003180078190241c0083c800504448a211400340044079aa0001c0c6a088801088101007105c082003080c85030012052611150030007400c00700c0405c03508400411450580c0c001c025030101607113044c06070081c0d80007054008902c4003500d650841c1940c40030510139009040000c20030000c1000c2e910074403000c024070300d009841717600d0350001249000b02e01c3d001495039510300080342da14038035002590005c0341e03c2071005010b076545000c1040000c600480d0090003c1c107920b400641c540d071040c4c004041c2943c0e4a0a19005045000f011a0032600900c3d0211415400f07038000340f080d503803c4994100142036107504170340000010040200f540c010b41c14000c01c15500c50209401b17980e216008454 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 35672765 1250 35671515 35671529
    0x2010605041b1418010f030207020418020901080a020108130611120f01061d0d0c17150a02091e1f020c010809010209010905240a05070b1012020609010306 68
    0xc0c2c0250701c4504482c04422003a034000c03880c1c600304603c80300c3c502c10a4400c1c000454100810b6200c0d06030042d00c0140c4c3c0c11100c5d40800d5401c1050703030b00513540c2d8030400801415041d00100c5060703840c4103000d12030006030000060346d80040c882d84010707170303100c0402d130741c89824080e4146d0b40c15040d10700328000d03165000314220360301c101140622204800c000e03018441c40802c605024503999420040d07800d01c0031070b01d641a07500d1854400c0f580034104804201ca4242c41520000360190351105072a002820b00b070301c1e8034407070740080c0f841851403505d0b24640b40c0c00203500001103150000000000f1084440700c81c201d840380104004000c80c565400b00070709020f24201ca400446400a0309000303480e404a161000d020600c1000800d025400500c00d40304521010f0f110240101c0c104001c111549120010080c415001c0121000c1d146811401a20020040391a60750301c4203120702d410090302e44000e025040040f01c4000030030103801e0f41e50941c02c1240e01a44c15594403244030740101c024218a400c404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 35674015 1250 35672765 35672771
    0x1020c07030b04150c09050d15020d0e0705060301050f1302070503030a020d0e060903031b040515070b150307060c1a07230c07090507120609020a11060709090209010201060504 77
    0xc01d200c010164140704a104400b42c00e500c0690004030400c0303030445800031000804944003885141018003400300c0c50350250004810307218005002750181d0784074100280603540c5502c0400010f000400c01c0d00301402c01100c4180c110342c14600406d401c000582d8486110b0f10310003072400e00c0110245d04440f00c164021081d240d03a4541007540384013950020a0fa4124140303000c51203020910f021811500400d4200c1c09540395440e480f202404400500d1840ca42e0104c00f0400018180d66141c4c00084e94010710700415254651410414442a0020706038481c02c011034550074400d0f94003160040c180c0c1d0080c20410004002410003102110984281c1c902001403142800141e0b6000507000c0550720035000c3c51f42c0d8100c0c11685091440c024000818400d5100003800d02c114522a0081c0d82c0c04186464210542114604008265412640240d040640c0081c900d80c0050f441160119488901c2000f0440d50a0402009000c40303540d05c19580c030341d0340c080b0760725425038801e401200003450014018 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 35675265 1250 35674015 35674019
    0x22203060212160c02060c010b0604030606080607090b04030224070c0510020111070f050a0b0703020307030b0105040602030910030f0f020306031006060918060902030f04060b0f030307030309020301020c07 90
    0x910003580660507045000c410b8000003000d40810300c0c0246060191a600d240d6190034176400d00c40c00d60003811940f50f5030f54031004118090b48400001e040218016200402c480d441c00681a040c040060b1400e010011108800d00c007202a010444046940c1940c00080c04c01c0c00407009906800450011190b02c94000b6618040c4880700044070155441201e01c80b0f0500a07481c0103908031851607512140c40030062001c5c20200c2e920030141a8024062419100810320540d00c0b900b2000040f201440420740c04414050641e9051160503600142820100d21302070078000d020790b4030700501200ca0301c900300701e06018032614072a030414103a0340c05821040c01280e1052035000c01a41048480d1406441100b5880b007a01c08203001d201d048074503a486484c903942c2099003911401000070300e00380700103880340f50000c3c1380c0000380f000b144940d081c0301446940e41041e141650a941544096522545d419100f502042e03901004039900790303505081c001000045071010a01901424030000c040780620480 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 35676515 1250 35675265 35675273
    0x1d0c011422060f02010506040204050d060f1805060708060306060d08030a1b03020a021207110904030c020a0603091a01030803070c0c030b09030a180305150c0d1a01091a0a03022203 79
    0x140d4483c800b042d0b00240b0050782d4030303c140012805284100b82d80440c0c0f01c1c00d01e1f40890000e90241140c1d81c407442003c20120140e00342c80328210320025080301d69a025404100d211035101000f41e4004104034040c002030309189001401c00005d1002c0500001300010115584211591040600d1140603613018919008020090020340010920704054000c803000b00541c100080c045a948946c071440464010900505010701600018412028032420941c24005039982807400c4005040c184c0d000f059410146c03400801c408040c181d83c14000180800510018802d94240c07544990320b450101c2e11140e260400f0340245441d0390000d0118005202130040054000c001861040125100c25250300c1c4800f401403040d400b644000341c10303504203038001e0103204900803d00341c024201423007150501c0d100d1441c020849045c0d13407280c06501c54411401d07050356003100e581801403006a1000b8a40100105048058400c04110038101540040d5401c2d00300c1c1004003200e1000e121710010a4241d41f6450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 35677765 1250 35676515 35676527
    0xa0e030f030408010e01020309100c0c0818040c0806090a0e03040b130f0b0f0301060e04020904020c0615010c0b01030f0f05070602010905010f0b030d0305091905011d0c01142206 78
    0x1c1e1901d00d50801c1c2807024017034030500803039019036400001814014240f00d400380c02803201d00122810440d180c0701000118107a60003400540c041c003150000d820050000300310442e40801c1e0b0780c10074003000804110041c0d480690850f88014140404a44013090400090942c41a600901422000170a4000c510001c504026082d1606050100e00d42d40e00d0740703a011002c0c000c1d446694041c000030001072227001c0c07080e83c40307a05580e00a8005030910920400080c141e8000da40e10300c00643c044c808100320320402080c0484005000c1c2001e103003101094880c903200f4039050001a284515400c03880c0308220402c6a0b0080c0a03412001350392030540c59503070080c0070304003240003902c1079824120400b00e1401d60f031050f200f01800c000e00509101c011018240c01401004108040b140241c2810400e2100030b1202c1c1345409208800010780040310410540480c00740f416004915444100001c0c0c060740c204488404c1000c0c81000181c580030300708252045d8900925200c0e00c814442400042c025070040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 35679015 1250 35677765 35677769
    0x60609020f1902030705070303030209150a0c050c090105030a02040e0f0303070c121706040c0c06020c0705011805010e060c0f1504060c0e1f09080102040b041a0406050f0a0e030f0304 80
    0x840c00081e1042d1260103e03034900a2400107403082d0085a403c00000c3d00a90042c4060840600100145402011300c500560407807903a1101195510b902141042006d1149512000c1e044814800e139504120210741d640440700e00003401203a0303074170010300800c40801c40b002604681c41c1c1220f54914145100822203c00c10808440120b200d450007030381103000300c6244100e40c0100c00059015520340c1d0402000c0d000900940040c00b00c2036011201140c41c5000500317000940314000c100c0a1f2801c0001490720b40c030040307040381040c403400080c00f49a0b800390800c480c0c840e084840300e4031441d02c01480390074200e024a4900f040d100f99490042012042c0089611460040c2410042009502c0302039482c81c088110b0258042c41c00c4100011a40c107000f07074142d125503e8504111846c0d01c400c0d50a003281d00640040c0e81d4100d004c9002c0060040c0c007540d20040c000c80120050900f0700c3c0003000303000c6000d203a0818410f0301004c260544140d11a08a030704ca580001000c641000f880e90b00700503129441f038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 35680265 1250 35679015 35679037
    0x60102010615110115090b010207170a030e060702090a061e051818030a0206060405060102060f0606030703020c060a050604061e18020702130507030506030d120e160f06030c0f08060d060609020f 85
    0x240c5001440450602c6100c0710100040094420f418037030b42d0803540c410200c410f00394031030f40620030302016855a01207a4820191603400082e10740c1840c1074008401c0518503c064460082d201c10b02080e100c9441304c50050b068115031810645840c0603c1d1200303113010040030402d10000c100750f07540f25400a41c06018840c143c03410001915a000126198201210000140007480303021540fa07050040055500c086e8034900142001c1c0d0841601d82000c40c161000c1691a07121018400d09203002e1003a07000401d0300403c0911501c2010180503042031580c8165010034000441c44a141d4810303404031401554010101440c2a408020140041a040e06c148000910340700c00070311541400107429450200300c0d1640d60f580202940c80728050110b5400c84105400384c81c5a0341000d101042906003d40b02e4045024020360420b03600604880d00c5d000d0b01d400300801c0d004804102c50b0041400b030b800060669441d51002024180440608050340c05450345910028000e1005404000500a00454 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 35681515 1250 35680265 35680273
    0x7090519030c0504050402060a0f0e0325050301021905071509050d08090105060105070609020d05010c1e0206010f090b0d0503030c040806150609090a150603020a0206060102010615110115090b0102 86
    0x30b8001384000c071281220f0013900b060081003100d2803140104034403070b40540c1d9850244041e4180e480840c0c103102e00c3d01d082213a02c51443c3c0f11711225001641c8148040c18099008600300a100381855550860a811190030f1150005404040c80b080800328110710729041000d01c94030a00d450041c2e9a8a0313001c081000203031510b8045501541d0600905008040c143e40c0c0d00d06094490725007000600410130b080f40d00504415201001070300c28082c10746a00b959803110200075582440d10941d0390001d412510840d0002001800514007203000724042e80c1d40440009002101c01e4041020140c0d01000608248008800c110f40c0810b03400080c1305544bd04000c1d5105500c509190200c91b0101d82c01140e4420b00a12820405091191080b0740c05501d015010a42203000d42500401c061540c00880019800044810b0141c0d01044074580004081c4000c01c0124500120b42c06020400e03002c0100700b18585d003100d41110002d4028a003504506490882e82c40e541d521a90010010b44800c00d000d801 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 35682765 1250 35681515 35681519
    0x10c0f1206050a060e040207020a060305090f07030b01060806130f0b030d0206010b090613090f0b040605090403090b0d0624020607021506191508060108010f1d07090519030c 76
    0xc0c240101400c0b41d40251400802c94104001507034000d10000b82c558000390700348030800250355102880d0004122945001505040507000241054038022501c1250381c0805420000180f840c3d01c82070443e00d0354945150151a0540015410f000d510320741c507000c600700707144c81c1001e451a92068165a4044044440b84965003c8c10303600c801c000d1061641e40d020a01000c403036030030090010805c66401c980c10201180d2a040b006044076444009210101e07911040c05240d41058440d145c081c0c44c00b21401b403068605641c0050070514640110788604a01003401251082143c0051000c0d0841b55140c861203151261581c00d5500d512401d00f00500c208808940050300200301000314081100701162a9501e8800348991032152426080003207104200005440b54500300c4011030290366613070390300c1031704103a00014a807000c103130043c41000c06184d03000c0007410010b1001490142001c1000b09182c0e42d00d00c025120250107601c216040000b2442017440c6155424072007041c4e070303c2500c009074000c1d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 35684015 1250 35682765 35682797
    0x7050109061b020d050304060306030b0c030402100c05010b030a0f020301050114060a030b03120a050304110108011d04020301091e1502040b09011d0a08070306060503190b07050408010c0f 82
    0x4039188035a03030104040c41c0124112000c54501980c0090001c0d00b510007a01290b0b817164695801680440006a0744000c14401c200313010400c141c010701c8140c0745504504068000640010b480745200050040d800710803003c0080a4001d42c980000080581d202078a541c101001c103844460401c0f8481e51030b02c1c1c000314541560a21100201c6406410b890410300400c800b0350061a240060a40c0740c880d12286865048881c802001d02c9000d45c1c1d10745441c1d041501e060030a58040c0310400f4140310145006021710b1801c0d504000d003994006a1001aa880d2800440d0041c21250b00c0540480300c0ca400301003070394140d25107054102e8070403d5821001c0c0d913108160000c03400b40b40921501c0081c10041454158410084241c555034035400b41f0b5400389032040014040b44a9a1040e4104d401107c000c01c24001d151045d04001e2400b50080c1206880d8070814803d901880300d00103289101c00360104803420320031130540e0060400a002081104aa81800b602040c480b403101400611111030b0300003c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 35685265 1250 35684015 35684027
    0x7060506040903080c0703030e01020301060504060f11030306131107030509090702010603031b080c0a050715020307080306040c0c0b0703090c062f01021e040e01120c09020304060b030d0f02070501 86
    0x40b6805507608032441e100d40204445503403100e5016810907440c3c4000b040840000e100440c0200301c26101d80743d4a81c0351100183c810810703a001407043c804120f115501440c808030440358403181c11a68070050016000701d440c0100218050a0800100414403c0406402500500030b6a0b0100c170b04e07008683d5102403c900b0780782c1501008000a486040070561948180340309240c0c0ca00c1a40b11034186240c00d031105251649404080e2071590000004010501c50104105200d10785031019510b08001034950180c1c1c0d101c05030200780078541e40c04220074824401e080d5070801543c0b00b41803802904000708001c000d0301561100392061900250002076250094850782082081154551034480390002010b899242c4100b9103c065502046031600d01c1c81c607041107070003030f8031181c0020351a9400c2007101d0310003081c142c100c02404465051300402003800042043c084500442016a0f25a5145001c01c040c02c0300d8420690144602920040c180ba00721a40e140c814140d075081b151103661f80c4c1c00440321 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 35686515 1250 35685265 35685281
    0x6170112060b0609031603060e0c03060112050a0b13060b04140a0509121204150e0709020c03070f0b0a0b04182d0b07030507020304060914150c030706050604 69
    0x241210320850900010140c1d08804003050004014500744000d01021030709020105443d0030b549450984140100300c400c0c1f2900c40202182d1004150903642038000c40c0c1e4602c018061800784c034910704106020008204003002290760700c4000003040c0e050a501c20b40040c1c2040d03100320f4005040081ea11401d0505100b1460ba0620b4440e0600442e180c2061180092001030500c203564000c108404841c078500340000e24a505a0300710b10035181c034050074000c15048043d994841142d080c00f4550078501000110340f020350301c00e03c0005a0302c0c0d9004e0076003132540c894448000c14004c0415011010312a2614032076104180c2d03c0000c0c04408040c9003000100c1c0c003401ea180c00b4004080000c80c002c2070480a8441c2d0013007103005041151103442000000001d805001141d803180601c0401801d9030741405525001001400150304260902d0300240c507850300350041440d020420184450203666404000c1001c094041100d0381d60b4008200c041c0e100e50061100b0fa03596801c050105240b4141803242c43e00c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 35687765 1250 35686515 35686529
    0x50301090210050705070503190b100503060711070e15100f080c070804030f0b01031703010b0a0e03031905041a03101511030301060c0212150601030b040222061701 72
    0x300c405034005043d903842e040803000b62414400c00c540442c46403420801051145420704028502c01045c0c6800200b4010085c40c0400c004030048080026890000b0780542100740c45c00e14003030510507001c25a04c0c1201542c4000d11282d9100c090203580380245000c00d202040a44155403c2444041300b80d07170761000c0b40d52840004c0d200b0f40005259075071440260004912800000e442c1c19a00e40b240c142100b5450403e6440380e5441d0700400070000344a22110302003401528940c1507601d464801c3c5680d01036000c104040c858019580010741c0d5080c0115488600c2072000d11030340d003400300d5009000d900305e800f0786000e0b00c00c3c6c070851800f104450f03c15284201d03041c0700a4601d41d801d00d240c1510200034460107005000d49070a45032529403040c0003541c080e050b80c0e59103103405400c5004212a100c1066050b005a810802c00da000702c00e21800c4581e0712900c2801d011484102940100b40244544ea409421000300808032039614190000101c1c1200d0441d030b1461204800403080010442c1c083c81034a07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 35689015 1250 35687765 35687779
    0x61d01060e030c010f030603020301060b0d061512020a0905060c061005030109051207050304050a0e07090504090f060b150c1b060c0a15020405040e0f010f050709050108090a08220503010902 83
    0xf801903214001403201d41c0700700e15002ca08940d4950109007510442d0300100c402d241d0204840039480040d01c2804014518904429223106ca2a00080d10202d2040e01d4100400d80000300007240d0760080040d41c00505000d08455a6217034041c01c1581c4440b000c0e41c60300c20704440c00e0400250b520b014012494880c0d00b01c800781c0f1603582420001d1030258080c10040b40c450109200c00036171030342e4101035200180700e80765102c0698a01550000e00e00406500058800c0d4500b0000a011401c00748280e0200340d4044800118512040000740d203000305c43e020116042000101816074150104001c1c002a04510403003621101d45401c2203420b00400404500a41c071610502c400b1071074068070a0508294400014545602c03030001c20103480e00c5004004c520b0344240400040d4a60074421821048a94442040282010f810041c507480ca1482220704000c071000104410200900049050580c0b00d112950f4640f07000414000c0c6c0303481c1c40080c0c09881c480e090000340c9420306001d000000c030b500414030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 35690265 1250 35689015 35689033
    0x1060b120405010f0c050705010f02030403050f0a020703140703020117130803100506040605220302090712110307080612070b121504050708010906170c150d061d01060e03 75
    0x100c10325030020800e68103503490748112188a00c039441441c143c5c980558030141d884190341402425141c0101c00c0c00e200138030400400c004030394088240d0303c001c64a03145071544e6404410341289040c7e141c1e000507080b410a0020020b2548002540f4800c5034401e0f03d400c007a05240c0d4414291141c012144143c3c0d9800c1c240c0004000344182c001958414007051001c406261590007003112900310b0b1300900081040040c1c400429041d050103400701104a951802c0c03114110340c0455000d260241890050180c207440c03400101d82c0c10b40004150003440c0c8080c1d41c40341b610a1000700064010790f00b160143c0b081e169110726601c0c02103588420344403d2004079160102c400c59580c10000024950540d20540226030500d695071402403a00034503095883c189154180f54845003180c200754046001d904036548036000320b01001c07502c03120f004011181d140303007900d44403500006441401000190103240184c0031a410003008030008070a031046223001181c0c0e880d410155414081012030700c1c0d040e070004402d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 35691515 1250 35690265 35690287
    0x10e0a11120a050609030720100e0607021203130605030c040618050303030403030615020f1203131a010806060a2405040b04080a050c010504060801030305070f080301090504050f01060b 81
    0x7400d038441c1c0c50048030142002ca49030241050800c3d5034428042d000011002d0030300501064003104043d8002003034214524003400a541030b103030110360300c0c103200110071240301c56a10361054032a0700350098898501b0103820718500d41c030b075881800d14403109001c072080455024403a41c1603901c6015015182c6261a0804000341d034000801648140c0f040000d250108490300c00b800a18000c2c1d10a48001c5001400c14011100940310b001c001c80840d4041209062803000024003c50f49003145c640a079038948400200300342640d00d01c030001c0c10030411860b40c2d00011807000c201074100d40682c01500c503651034000400010301c1c2144039510074521151440342c107055280075110140c421a0400038603003541d40d10483d1268100d80d2002226400c070004e49020f216052201c003608841c02d1030000e00d041d00308040502060418040035080200100c0d10004008582ea011820303281c002c41c0c443d8a0b5a55000d10a002c0c000481c7d080720140200e41c1843c80500301402140d0a503040850414280f0f2800c0032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 35692765 1250 35691515 35691529
    0xb070b040204090f1101020105090f070611070314030c0c0f060415030e06150109050301050705030f090a0501050c04090b040603081602040b09040f0b010b030709050d060b03100e010e0a11 82
    0x40140d80c82956070b03403d0000190780c00c0311011500d21642c001040c02203a03000190031070710300a00500f403540158400c07042c6e51070089040c5c0181c40540c28240c46501080e90f640b85419901d03040204401c1884107511a032850001c05490030340074078403c0b80c0d03108402c03030280100c48000036501c1c4d80003802400103021140301d80201a0011842c1e05d80018008001091245010001e4545d808070301925111030b852941e0107440c15015013804c0d8024041c508021100815500c00107215078002401003000c10f0a281040c804d4003199604080244602e0810451704a865440343c41002505c0d440d01317042d84817a0900c0c1c0900000c8130f400c848054100307040040000d190b41c414803800c0760b000e07a031880343c6c0c5413940d82c85000034069070084040c0b891111007803405004085041e00226001807003442000803103076011490b02c00b614401e0798810300700f03041c41c5441e80203400284c20203503143c060341c002460010050b0344844c8024141900901030360420400300d548a2340f0300704000d070030074142c00010701c0a030401706 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 35694015 1250 35692765 35692771
    0x50712170309100518010e0309090109090f0609030e040b01020a050c0103050606040801060b030f130c290c01090303060504090507090b03160b07030f0e0105070b040c080a0f0204050f010b070b 84
    0x11007500c0c1400400e40a10f4215203003141c44504041060340c5a282c200e0b800d120b19038140045000852402030108001141a081481070034482c4e911100004e08002c040c41d84071052a9000381c003801003050610740a025010a2200540650329010505401c0d41c8006500e01c5502d800070081c103000200c4000450140000400d4143c101d4810440051190700c01d101d00c1005003501d40041d43c907410203600c10580d901e000380240f41c02c8071443c840c400114003040c03030710001c90782403c09000007200781d5030a0040c00c502c0c1e0b40c103a816050001c500c19071218019081603c0542c03095a0410000c6d48690401044074400140a041580b001c4420700c143d101030342c00401104001001c50703101009200d804101c0503055040740415100200301c2130b0800d500f0010350f120044c0c4c030782480340201070f07840d000801b580070f8070101500e8100b825020406015041d0341e000702a160180540c0e0b21000c06041942d205480400c003240111702d0180041d0745c00c0d06500304503060320011000245805002e413200c1f43c50307036006 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 35695265 1250 35694015 35694031
    0x4030810060c11010509061314061201062a050a1704081f11040303020d140f071209050325080c090c070503040504090606050f10020c130608030304030206040507121703 74
    0x8122010f01c50347c40001400041e90f41d41ca02d034a0090804890390701d8842e108140c0c3d4040c3c041844801c0004280403002c90651380c2d03529004900c9491130074140601b8501030400c001008241c0c000f1020320001260b08100d2900a402e19494600e92205c1c0107014400c0b84640c1c1480d404c03041c140c0c07821280e01c0c2c0529240719002403000c10ce41c0341c910b071410842e40c00f5602c01c5015921a6041e4084e880c0c1000002d5440b58811920034100100030450910038880c40310000c0502c1c1c42001904010f0b0700807104400500806012200841e0b86000007580c06100e583c071b0b106030150404400910180c000824490f10000035119414988864a40441d40c0e081514100c580340014031022441c1c0d00d03540b040050241c01a0030201e40d0f1880c11041c04101007008403103c0c01140b1120b035429070b642c0c00082e02c0d0b0700b000040e600d14000707026540c0d41c90300030b20b1590003240701c41c01300206100c00c3c1a4002403032400b0300e000e007065032081a510300d81525080c1c84c0c0c4000801c0030004185803141c5d4104503020315485050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 35696515 1250 35695265 35695267
    0x1020a02030105150319150504081b010203220f030804020a091a01030b01050a0c0b0a0b120303040218010608010b0711190f080102270a080f010504030810060c110105 73
    0x899000a083d20030031140309028040c6105032400500d070822140d003888500d08442e840303011094480c0c2d081114000c0003685030b40d803500c000c82d0070000608202c0305070504a09500c00c41d0503401c54868083d500944038010348840c00c03072812107810246804201d025074081410003a41b880e5681c01e5035483d00051003a684149206400141030b00c0701d008491400d503541c0700100181007904000b404581e480c1800340e0410005000c101030070f64001020941e03190300a1a00c100713a9a0f9007583c000607181403410030f50001d10040070b05055a40c00005103000d1882140c1c1408120032404200014070400d01c82d22000401c01c000400c560700094008043e45401042080b40c10700b540c801280d4880384900300a030158121041c10010412004da050001c0c000150082d0310384403d07118a05010004000034204129044006880c80d603540e83c1451b00402d0341c001560300341241201030303600074001141c0c1507001c1911800007d52900d40f800e9020300f074960350f45441c0441c522030b4443d441c0c1d40541d21300d60740c18000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 35697765 1250 35696515 35696533
    0x10306052d011e02010507020610140f03030f0406050403020901150507060b0307050a0602030d060905070c02060906040e040b0406050f1902130506030c040f09020a050403030807140403060203010303020c180a0b0102 94
    0x10301009140b802c0c003d19000800d80d4140640c0007494200010000e80480d5900d0000380501c04400e101e49244000c12901134910b91050f01c0000d0440c8516200d60f03001e10b400040000308243c001c006042120f0007200c1000ca01d0b070340c44004146100407030301c01c5800180204103c0000079003e9208040c0042c02604403010a5105d1000c0386481c1d440c0d4024602581c004110100044c241e4020103014102c960011b00440c100f02c42c003c0d00c4003150380802403281501007051815510f07650152001080d00384070410071401c0c1400e100743c00007019034054030854185000a0141d6014098090144d40c01100b00100220301088000c02500030900950030b02e0584440000c1a982707100145014076010400396584500d080311030103c20140c1c1c2d0090103100d0040c1704d10546290001b013a10100d030341500782900d0b582e8500a0468002ca85c1c001c22100c6449c001c540030050068075400385040e00c0c4281c08aa1214090100300140b024005000107010804940001c804034815008a0950407042c01140d018003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 35699015 1250 35697765 35697797
    0x8071401060e01030b0603010b0a06050903011e0501150f020c04051e09010c02010608070503030f0c0f0703030509100302090d1104062706290f2502010306052d01 71
    0x4034950b0110480810110043c410b124a210540e03400c000b045008014056040000c100d03450320342c2c420030062210116899107940ca01b9040b0f428a010010100500c140300744041c0402054280204040300c581c80760040b181da8060003a408040c14a40c0007040c00b0005001004060b010042c112894124100c80103005004d220b000c05000b4054000086051681c0c0c0c0c0c0c000b400c6410540c002c03c055404032100f0010341d10040100c8e0082d5205d00c85c0a81d442c1440500c40707140a51000ba169818482e0714000018940d00101800c001c49007110503008038420104102d00381d00a0040c440d1b408440c1d54803002c00148602400c9002d08005000811059680c1e414000c0000502c001503103201c03200d0f00106000c0c2894442c001c082c205c1c000890b0b4500940f071080444070810b403028030036040d5000905880d10b440e00030548140350042d0602c450340c0b500c10400c1202d001742015080340403a0808401240d24900b001108128071545004500b5103c0314828400e1a82c084001c032505018250b454000c41c3c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 35700265 1250 35699015 35699021
    0x706090e0601200a110d021c0501090b01060908010c09050f01030e010b0a0306050f07020a03051b0a020603010303020f120405030307060f09080f040303170403080a15051f0305060a080a08071401 85
    0x4030070030f020300480c040d641460900c21090441d80e62081d0907506200b001a80c5401c019000101101d103550100d003414501640100004c0c240a8606d04d10500001380260740305000000b650756180c001d1016030506070003924000c01d02d010321030744032140186605d8154429030200c440d4002e80d00010440c2c80c9050f02298000e00c003a0410745289450703900700860207001000303254000f6040d200034403100b00c150314000d12034010014600c010b60b004c0711050302a54002c00083c51a00e40003080c2c156656507030701d40a943d0707000b1030450007501d02900380d40d410000c0d9090161400c6030805070246203042e00303964480300140701d400e921101e159075900141c00810a050050700008040041003030f0707902c3c01e50402425142c00c20001264214211040000283c1e0000350035801200000c0c000c281610498041d4258070000e402c0503410808070000142280030b2000211050350036600c0801c11600c4180600c1120010303805910101d910003000300000541441c010803070306005400030074104009600c0c0d2429 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 35701515 1250 35700265 35700317
    0x507060f0c03091109010803070305030c09090a0b030c090601022d010501090902030f0303070509150903010c1808030f190903050714150c121c0f05180706090e0601 72
    0x40c0c0d0f03070710040c000c2003d405252500000b0442d0039400b190316006a155485c411004000c0c00c2200100221746040d9074041a6101400c004000a0451400301002c400034058490814440d101e003130040081810140318150080f6010380c0079007007840d03240d10511496820409895102d02200c0f404850b407440a1003194060151842d001c40e468400d8010980740440300302005044d60010801d05c042550401c0c00c441581001382c95162056091030104003050140f0341240e50154282190068101c0d0302845c130001c032421b02c1d01c0c950709060f2243c155a40d03e0084020007818800100b1022074680c602c080010038400e032900d404c018650700d030b030340b21801e05c02c980d40707c441c26a240d6040d860040c50074007540c440801181c58900c2c1407500c0420060f5845407010401490450b0000c0c5451040000240003144d00e01c28480134070011041c00a403100030b01d4104c1d17110814038010b42c5400d01d140c401040c0b10044900941e07900f00c01e1400d2404c5030400c400e014110605005402c0740480d103400c2c500340300c481 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 35702765 1250 35701515 35701517
    0x70306090f021002190f030c0807060f0e030a0804140f031902010f02091e0102070902070b01030c09050c07031b0609030e01030e0c01023013091407080103030507060f0c 74
    0x169600076481030040c0000944111410364002c0c035000d280b181c01015022154540007400103002c20840c1c1401d84041207000009009041c00250388414811b4903002080b801c0340c0c410007000251601442c56032a07019500f460b400146010300805e0100c0d054010070418102c45800340c618000b01e00144a103103a00415241c10035527640c1c800c0d80c035102e4080c03090300c0301d01001c1042503240250404c0090000007180f071618925006800510f0903907442001703401e0241c11810001c540e688144d08041c0d4048800744001c462160390304601180b600340358010f080c0100807000c00a81003607104da41c252004440c8429000071070440360300c0a404145035000c2e000100c1d000b51500d95248164800041c02e64141c2030a9840c1544064100c02442c0d90000d00518002c00c2c12080011a074952401404807444406500000c0700002c500008010745020241084400d2200c1c1000072002c2d400301c03811032820403580900814400001080842e0041009100d489c4c401c550014901403030204503021550030380901e00c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 35704015 1250 35702765 35702783
    0x3030c050613030c03030c02100e070e06030106050901051302190e03010506090405060a0c0302041707060f08091506030a020d140d08010e16110706050715091a0907030609 75
    0x1800030620065811000c007010808000d601a203000d010840b0b090801820507a590040144d100d100340700b04458240d4158060210300e0004590b181d03140b8450040048442103903010030781500d0144907a1080398000f038011441a072070442003115605101e24442c3c030302902000380c0d0401000d000044010131100d5210500019002e005140c2119030040c40c00c1d000d002c0c0c29040c080421400500709074000d45414000c146040e508404502a000725408100365400c509040e46d00003d0100c0d090003a5011aa607050010f800c0a038111180c98096580700c3c042d03040728032510749081c80c81440320362011010f41140c849005560203e4824982e03240c040e101291003060100e1210818440e03190b548519207050021541080d0280c0c804900141043d0701c00c030030300e951482095000f103140c0c01401c100c0c5810b9038101a90b0340000b0380154400942110304807520410302c207030740b5050711480058680041c030b0000043e440100400d41d400010701140710358402d114000000407a5400b0303007113400e4400d071010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 35705265 1250 35704015 35704037
    0x21070b0c15040b190203090a080d06180f050c03070e0f1c0b01080615130b0f15040e060409080901120e0a081b03041a0310030b09030a020c09010510030504080f040303 73
    0x10541902461081082e5680100f06210780007400160901003140c100312100da4504400f03151000034900d80e0301501a0b40d248607a00e102843d660fa00c00341500b3744418040c07040c0d640b01036082e0058070007241c0130000314000340520009424102d5a41075003801c0034003020441440d04080e409a074058180495015050900601c8052414044d0503001030b41c40c0d60701144500c0305400103e4802c400c00c416001d00342d0b615100b10050383d420030341000b1400e01a0456500d1110486112803580c010301410003503400704004186103080c244900510160400380d03840c140003580c0c004440490800290320401504d5041c4443c00c0c2da414000040c04601c5141d455a84940e1010511700c500040c0ca025a12034200f40402c0104840c4a03401c5000d45600403565640e03540c83c80c505c15158030b4650806444030011000300014403900000030454841b030b13902201c4507075a1440c204003c00c1024020a500f0586452680020902139002240c01511600768182003807127803503840b0100c1d0810380c400d8001402070021 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 35706515 1250 35705265 35705281
    0x150204170d020d020615060309012c010606020d05030c090a0b0c031c02040b0301120302030d061d0901060f050f03010b0301020703081902071a06010c0501090305040521070b0c15040b 80
    0x3543c2c0b0341a400d4009010203150a280c9050910403030100309006840020024400711002c0d0f01000030100f40090307100441e122500d09a924a45a86c010401036180000200b045800061003440c80782a81c3d03a0035103156101000100103820441141d500300d003c038180441c10b1041c40014240544100d40155140c0000440e0030001340c61402184190030320400040c0b10385104070303040b0703130541c0d810b4101c03940c500580b450120300c1d520480d02002000f40c908070000c541008203168403001c0120290591056848241140c0d01b01d940c1032103410408113038014200070900301010081c1205100034000546001e0787d0b00071a0030f90303104550450004401508000c2c0041884020040050000c6011401d01c0f045588403039100000394900d40d11000c000000400c9a03225040c4002d05a82c80402031110f440940340c0503005030018050343e4403960822019038800942c1042200240134600c00070440d4503e0042c9070b0700940e10500310200e99001d03e4054690000100c40d4150046100e490721444900d0070f214 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 35707765 1250 35706515 35706523
    0xe0a0f0506160504080a0206030c070b090c010801050103021602090603100515030d020d12020d0b041406040507050c0703020904030903051b0a0e0420040b0d050609010e060603060103150204170d02 86
    0x9201804410300c070174010307540c0014041340c02c2541500c1d110394079111482408014082c403103000301120200e40400c031000c0d1021400c4100001c0a0302d48825590300c40d0015000d90195420302440740f140340090701c0251400c0b51400b50031150280655a000e0080d007040410707520b084a02115040c1e0089403e10681420003a1644805082c406882407040015000f05203000350701c000b61070150089806046080b081d4403140c19968020030070070016030300181869500200300e402910581c5801c0c009107100340a07404989186032104050703e0910305541c00c2280441029005904001c2041d80c04400200204002001d20700c491710300c6280b060803681000182c92058004407079190303901041c8000255240c032070201d0408200c40c0b00044200542c0420000e012401c030403075000c021140310405006000c40c00da809400720100a010b01003101c6240b0303550f42000d4451603010762103a801000451180d0000c2101c148a42c20003625095540f2a640c80305182080161070740c1d004441c041d060395030100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 35709015 1250 35707765 35707801
    0x4080c030c01050d0b060f0403030c020102060a02090f04051308030f090d020d0e131512020a050a050904030507110301110a080f0105100c050f0a0606030506070c08070201030e0a0f0506 81
    0x3401840940c0c4807500080090040e0030300d0400b441d1301c41e6403c0c0d042c3d94a0000344c072449000c02e02015111340d0369007002803440124030783c01d80c0036002e500049442055a8001c68440b03800107040c5a06a000c03007820300c4014480100900d20050440d440f60000a404030011400b690509588400b103050180100f4100300c0c00e044244103550014410049646c1c100b12500011031049a0450281c0c207800d030407070050441e02c11041041036101001103000482c21a680c5d10050090f101c40800584803001d018070700446014041c3e0007019280002d0000e0702ca24010200e03d17100301120003464424402007420f440d0301451829a44401040c850821540000440d0307101600602102443d49401c0c04685030803480e000981c20000407100301c2c01488810091039102e14603101c01ca808d100d1103801c045009140d640400c44480c0201008101d0042c440c0c481000c0c8190021a218600280303680154020001c4100300703a01c80c080d607a4006c010841c0b8034500c1c41140d000d00007402076440e01ca80d4008801c9102 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 35710265 1250 35709015 35709019
    0x504060909020117091c11010c020d030f0902061905040e0c0405010314062107031403040515070b06010315031e12020a03053408040801152706120804080c 68
    0x131a04000c1e4041e0006002c25607048620114080700d00b4101046406060040031a140e540c285445035440c40e40c00200c40c0b03444400d580e010440400b2034030a0304c05494100c0790180d8040403d0060341841c0506002c9200740d101181403d503d882e035181c01d030002540040b5450107640c880030404000c1540c0501405241e0950300d00782c00700f03524080000680b080840ca60044080780300014505403148100208005140c001c488070989440108400343d0300e9000d0301400f406a0f1500e8a4480c0c40d900000541d0352aa9108400c0e40c030542d2080b0046000300f00c1603d089041019002c0000302181e000d40458483c1c80350845020b1301007a00f0b040131f481d0006a01c0341041154022414040440d81c008260356180d03011010082401e000030015034a11609103020028840e8800b05440411060b24000c6c0121003000b4024050f049444e0b140304080401c80c840c04201ca5001111700c40c1d80c9010a1640c081070550520001ea038a0f240c0d80f014600c405030250803281c011001509000c480000c106c3c0308494201 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 35711515 1250 35710265 35710307
    0xa0501030f030311091c020f030706021005040f0b0403020102070b010f06050901120f052805010b040501050c0f03031305010f0b0f010c060b060d2a0509130605040609090201 76
    0x14541d503410051141c80000381c10150313035004040c1507902e410211200c00c58010700582140b1600070f02000d80c1d60105600700d21400c0e107400c40b0300072410301280c00f2044032000e4000d005400303082c000c510080c0400810880b5055081d4407001c00062184c0c0744207000300d02a034001a110a00ca1810304201441a00405400c00c0100002c00040d80c1c440c0c2101e102040c2071070083c2d40070140710001e00140c210103240c0d5008034102010041184010010200034641200502214030100e00340c84007212000c2c02003072000c40041100340300c6940900c0050040d85c0049044840c0c480c40d540c0314074103503041660540740c0020105803207818003409029290303600e46448002c010b210047c00018482d5014103401c0c906002c20f4043c10410b00000742c1c8084509280034198907a01c0440807040002091500d6800c0800920451031070903040b45100d0b548583d0070f0343e8998524003603080d002c02a4481700000f14032072641d1961000705003902d1328082d54004210103840450384080c144000740c894107032a2102504140303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 35712765 1250 35711515 35711519
    0x306070302040510020c060d020f0403050111070312060503071406070b0a0f0b0102010b0603041412070615080f070e09010e2406060310051e09071805030a030c1b0f0e0f0a0501 77
    0x150742811142d03001108c8400581d1030710311842403910790096901c00342c80365103420a0202c01030031340401400c071329100f0b03a942014525260340b0b04040302e405000d1140c05034841c201c1031042c01c0c115602e0402c88038004103418100340c4550356815443d8011941d41524075200ca030841115200c50281181011007400240812030085002c60440e0000800203895202c401180009500090000342c0c0201c03840c0c81e030241d90f803980d810a08040e1151207a40c640b418040000000d00d14404201001d680f00c800000d014224034041030303e2603880c005080e0080c25542c4408282000d40208058004903103043c40801503c507810540840c100300061600340034240400400002c98890308140d0705030750049551208441c0310800c40b40102c0442500c068002400c0300620408981140d40001c0320b50754031500d44411030301d9409243c2c542c01c00b042d004011545520300507000aa00d8800e03028850171086a1024465540e200c2e24220b15050744404642c1d80004c040c440e0101f030a00d00300790302224402003481254 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 35714015 1250 35712765 35712769
    0xb150703020303060913170702090606070302061501090504060e090f031201060c2f0306010801020c0d0507020f220b060301050d02041505090109020406080109090c230306070302040510020c 83
    0x4403000302800d100d056944001402e110240d204110b4864004018200900365868031f071000341e0101c801030f8443d098009c00a20103182c41c508942049601d80e000d0402a110006030103202c0c1d6410411034144001048041580d0700d861050700024640c4044011140c1840d0b907105081c14800404403015030400c00800001e00c1c000c03102d01c0c2c11a0380514190303070011800c1c100301349030110b15104881c41e88802c00b1440885420610364441e400d6084041d10941c0c0d0f640e01c0054201d1145403051807068100382d101030744442c00f542c0034000990000c1c0404140c4020b1100041009a1401c5000310200e85034200c903884551910501941c110281c605a14550520300001d140500c0140000e101d5601d030956014150141040795001345000b030300d500c45035615103c0340030107900306004a00002d000702c030000400700100e0086c07a0310a9089650b01100f20301340821601024036011621815660401a601c901d403001c00410384504482c2c2d900580381c5050408001c204003c0400000441d8042e941d103c1e069 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 35715265 1250 35714015 35714017
    0x41d070e060a0507060204060302071e0b130c050406030305070b0a050601140c010209040f0c020f01090b060f0a15030c090e1e06030a08040e10050909030f0702130e010b1507030203 79
    0x5088076002d80350090300c0002c48080c840c500c40200034500201d40083c08981503005021801d11030411906001d485034000303541c0c6100305801078103a503090344c00310780ca0f04505000e0311074060003156140c41c07058403140424262400e0b907004400003800003a61a0500c025452516005103d00038140070034102031000811144107000d205120f1100000c00d04103842c82541160040c1c60050300601c000d1005048113002425201c61341800b5010702160030b1440501807040c0c1c01c00d20303404003084c02661a0503051120b40700f0381041090b08844983c2d00402c0040300811600e2862540c1d03075002c11002c4a181c0f0052003140554403021b0242825400d201c0b50703071280c95040b00103007a20f103e405515900c00f0002450403041c12000b502e40000010301107240003030541120721903108681d40c2c60000350380718140000813100701c03034503d00741e0018442030384419425402040442c0c00240400000ca4590900d24201c030b812260b44a8640e5441c171159519060825034062100c00316181c141c10034070640c80c040e4403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 35716515 1250 35715265 35715287
    0x4080c01180302040e060907140a1505040e180709020306010815150406020a050c0108071d01020312010b03100b0a050928030c0602060105031c03051510020102041d07 73
    0x60007809941010300c1109003280200642e00103100740a0300b02c80900e0b06450300030070741d5010802d014064001c01d005034140482858088090681e01d0460b140c0419aa03402a000c100c1004104040000051301d10240540c1e50081100b0b152440303c070000b04000c0d600d403081c250300080e65240103200b084601d030382044007580e204a128003141a4403c6460008045200e0402c178420210704c0428041121070780080c1005055116108031035604100340c0041d205030604403481d6000684500500c1c1a07000218038030003200006004682c2070880d25030f0740c881c04900c260401744151101104118919a96140f408020415440740d54036100300c0000040261091004e014080e200c5541100300300041441e41c03003400507008619a80c699180c1c5071900b40c03c041c0d0720440340180708880010075a8603010850604943c0c042540c9118041c240c80140d02814005065031800700880c00a00407540780c840c4c0c0054401040c2c0c4c00169a0390402244902070305070300705041341842101003006141034101c018014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 35717765 1250 35716515 35716517
    0x20610140d1b030204060b0d050a060e07050c120301030809040f0603031b020112020a030204080f0309061c020c01090b0a0c0c0f030309020d05190209010618061116080a030e0604080c01 81
    0x490030b603000105410307811950b00c025006440c1c84800600c05245a001c0c207030950101e1000c1c4a65200e40400201f17075289406212040c00441c800700362202d000714010300c0d6803911002510813041c082c84010b0110380090340191070508000810005600e0b1a1144031121020040c08003c0d050643d00e006228a10700710501c141380403189501c2d01075a0107003c42041c50488500190360340c0b0301c0c80d10020080c0d0410b1044c984144242140300d0341a5070b01005903101c580c07001c0c14041c01c1010090400c80421f013072461040c01a60b0070841c000c05001d0a02940c03030710500943c00d0146508000c0b034104102e03194060b2071410051116080000100c5003440c2541d01c80d098503000c50100c50358000150071800c075070b000030700d5441044800040c80f685148104403040c021501191240e99500301038034089011110f0b0240c0c03010400d42440800d00428202d0240e00000f02107035600e01a1585250400e8102d41091089911000204003010381c008156500c042d42035030040d013801c0c0303000300450b91800c080461314 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 35719015 1250 35717765 35717783
    0x702070b0d02130b0d0506030613020402090111032a010e0c0607020102030417060a1406032e090803011703120415140f1501091406070203030705030406020610140d 72
    0x50081d040e010707200b8a4454a2210390300a942d6465091035900940c00d441445040c4000107441380b40125030244121004c0000442c84121542000b00a6210050441c14020300303513101490442c04101520001c0440361071010a0203035082c401c0e985004960340403180d1382c1050404003030000041200d00306000300744c0f612601d4502074401070b811070146420101c803844001e80d00700c2484c5c0d40020178500a028000d400c00814803402d14940b040b00e07049460340e4040d44003401e44450004d84800c10b603048240090f11400c038008190800c000e54180740c400755204030f07010005110025a240425940c0010b10008603d4800004800c5e40754007401000602307844456410059140d10319000b079654050601146082031400403040721007008159001c020010300f55070410301c0c550007072219000b41c401a2000882120845041006d03550080078102e0b01408240000c1001410810280c4090000b94000c0c04080c0f9142e04503103058161a40209903140182c2c450f941152100d042960321150450261 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 35720265 1250 35719015 35719027
    0x90501060b030907031106090108060909010f0509010b040b09040b0115031b0909050f06090a0e12030103050a0302060703020315010302030a140a05060f030601050315070909141803030702070b 84
    0x6004004660003203001100c00010000704460120303031141034074490554028014121070138002c01d03000b03050403140882c8021000c96050305d4154941940040004000f05e04445070064482c142c800c2074a080311241e440d0151050107260500078503501003c165034850707003841e03e034550801448040c82500c04600071045180320280c46a04181035070561b02c0040038880106000c000c1c201c801c18401d948510b4641004901d92a0010180601941c00104254160b481d00c03d986002080c0c4021610920f200701042d81e025210361201a500850244c40600a515064140a420a04000c0c054001c145c81001084420a419440e829101e50280b030016220f076030b242501001041c40c40003020023901c0010400c140f5207010b41180780305010541d06d04824040790414581c3d103160a00a0b81d90540000c510064051240da1060b80d000c0c1c034500d000c40189a0303510000c0111030450105861880c05d54040003001c2034500c1d030303070000490404010741c41d40c500408000e46501e400d0140a0070540e00080c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 35721515 1250 35720265 35720273
    0x9210b15010c08040e0406050705070f080c1005040503040501021c0516030e0303070605101508010306050a061a0c010c050301030201081305011d070302040c050406020d050c070314010207140105070c0609 89
    0x854802c142c3c0700c990603944940720a801810721400300c4007214240d043c800003a040a00c60010748a280340d100c3c0c45980c100e001603581c0050b5400c8200c80500a00c54411140300800e00d6020342805680a20082c1d039071281080002800c042241d501000e003140824100d0800f1071340541203e00110014414030340d904918036045502241d501c100d02e526100102d542c0091000503800030303000703140740803050103c160307100558146041040794800200d1041c01c01000804e14580100e60b1000189100098550b00c410b0500c03202428181076290040380030444200b075070303024480d0aa9048150510f075040d503245034002406064000d0580741d442003036070341650800000350400000c00307910301c507040d4000788071a80c0386507203140c2071000ba4407460600264000480c01801200c050f108554083c00103186400c00c1556294001302000341d4a1160308000804030f203040480950241d803150000d641c65130349080034604015085920781c140d9140ca0117015244d50042801014103900200100e5100f480b030034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 35722765 1250 35721515 35721527
    0x5120702160e0a180b0a0c0206061e060903030a050c06061503060409020409120f0e060a0f110703050d0504090f0c09090f090b09030a02160501020a0206161209210b1501 74
    0x300c00b1140c413040501e200400c00700703654051040d145082c0c02c211540e0420710072070340e40703100b542c0581d004400284600268501c1c005121b1200d00e0250005103800c40c02d401207481c40d444041120009100828400403c0b6000d00c19650071804c11224095484a80a1145d42512001d02544c0c1300d03996614180381152142c3d0010b80354280c0009110b140d80d24000d501400340d4111ba194480000c0055030350255518000303080d2285c072642c41d41c51440c101300c6c0c001c041c0c55403c89030f4400341c81480f54220000000b0400c008d204400d403110b90302c15454618000d601c1c400c3c1c401e01900c66162600701090030f07510300d600104000407941210401304010300d864072200018418410080c0c440700702d000401c01c150400100600d12003003030b9401c50304171911085c90600c0024940c00703442c3c010780100004101500c1d02c10f000d40580a07511503d42c8490f030b141e0f80e588030f60b0710780c07841490040780300000e08100482102100082c0d404241808500041d070960f03130305a205000900043e8070000f480e40448881c1d110358 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 35724015 1250 35722765 35722781
    0x3100e0c040515040b0409050d0318170a030b01030902100305070504030b0408040302030f0a0b012601050709090b0a050112091b0905040b16020a12030e030a05120702160e0a 76
    0xd0000c010a080c070b00c4943c2d0440e440426181d0044d4244081c80501e8101880b0740540700d500480500310034a00e920381100a022000b801007441c0c40d0f0850785c131003c150045c000d00c8405c110240e246554807541440681503440380207159041c0341c41c000320b100240c0c55614600405000c00d1a001645036a0381c0016516030180350009000c40d12000d003000b08000c0e00000030010f4078000c8003102d80d258520391217182d85003c1c4a0004005074441c0c0010880d40c44e0080340c0c5909001c070a146403402030304584e44142150300840c0c0000004a60120400000846200d518440320781a40c41880e000d0034680083c01882d80310715001e40c400ea440c1d40c0e05041c03110000c503200140004100c4c125100341c1d11094880a00340c2907a00781c41007103425001c0380c56504400505a00b00c0190340241014001c0c90f107030480032503401c0d102c150500d0340714804001e803640c0500c010710404605880d40f03030721107112011102280f00003c3c0050107545c0b001740d64900078801d08415000b202c0c00080d02c10320759940c039107082014107042 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 35725265 1250 35724015 35724019
    0x10030201080423070303080f0f04051905030906180906090c12040807081c060803030103020d030507060b030717010e01060803041802090a090203060f030106211b080303010f080102040503100e0c 85
    0x1132a02104040d840100280a5200c00191102e1901d50008403c3c500030259002401c513808840500700068405503801c0c119406081038034104100503001c500350364000115141001103000c091626450b220640907084101138501400310b161a11003501c03544642005003211208490000701040f0002043702d20540c1d001c4d80c020b46510702403800d0352843c4007001a81c00c1d0f050621707001180c1840c0020990b1b040765002428400d000c01d50b40c030b09540f01e03442043e003034441c9501c4800c95100c41d00c1c2002000010144082c070008022201414282111800c0078070b80d05690414004024140c000030645054441d01707007444c4910303175102e03020400130301c660300400390844084200001c80003119405188600c0702520200355080c41e4904040c2280c906000740c0c1200d240035038004103042354550040303007014462400c10800304640d806150404025500204e110740c0004010301221581800000007859080c00960409040100080d26402c070b41c0c030220b000e20307030760200c003001d04608000c006052840 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 35726515 1250 35725265 35725273
    0x60403060906050f01080d020a03050304031209080301090c020303010e063714091b03130512030402010306060906050d020f1c0609150f030204020711100306090510030201080423 78
    0x40d8a00b81c0042c00d000c48001d0891410038000141000e00443c005040401640c0640039900e010354040c0c402d50800740c000d8040018040c3d110307040107954410701d40c0f8980035580c0c00742c4a40c9441008400c1d200e07804c40940c1150000d01c01002146c950501050b007001003201c030480210484800002da868040300d581c02d244043c1030300740216014001c14101660449002c40c64070342401001c0c0891040c040d144010040800300324004942403040c06940c0100b5140119100c610044d1100380c5000162060004039a1001003132104540c0c01d44a20b0004101394202200003d00d4520081c00c40e00441d10440103164001405a0740d0580c8001101c00d45109403981d0400c010100042c0030051003140903449209241070141c0e603007522000d11030412168000c0d0a0440142941d091101a4100039022200100141285101c035918007054054000c0a95000250700e45040e1840b4250740002c2e140c0300d040c030205002840540d0303011000e00d80c419044060001c074540300844440d0704030202c1c091004079000b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 35727765 1250 35726515 35726531
    0x60504050a050d05010e15040b06010807020c10020f030403050309120f0a080c010207060507020d18140f06040504091406240603040c050a0801020c0f010b010504030b0c0f040e010504050a1104050103090206040306 93
    0x50390b0010a07015034061000c0860b98ad40b100d005440b198400d44480e0056480b4182d46010341c5000300302600f10104502c155070100d10b81c0000390b4950342040d002103542d50000301c0c5061032810411f20f00b085e00c2c20071200501d2480d201c9640310780c86104400029002210001d0003a2104000350110780c050340c0c0c841c0d010041448c00e014025204e02074040c2c00000641c07095401d200880005840c4015203648000c10300c01c03085a81c080107980310541c1441d41c0c205c2ea06000000e410307542c0707108003030040780281c80102c040c4504072a0312b4101038008004944680500154103414030070f4500907100f014040d503915989441d1b9060414035600355620407075115002c003202023400304041d00501801010442196040040c008805080c1c0fa0400012800944140020001301f0300c42240e054000380301901003803400c0c00042030790700203610541140c0845404103004101e6401c0c030381314091307000302030316403c0018403011b07100c4050900c02d61040a040588420070041556210300403207004684c010b40c1001000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 35729015 1250 35727765 35727793
    0x1809070503010602010b030f0c010e0103090b070906170403020604030804020f03011d100e060610090807320f060d060b0c0a020102070e010e04230a0f020406060504050a050d05010e 79
    0x1e03109000c1c000065081100c40001820005240034241c1000c5001d4081c0f21540c40c01111186240d20415042588520414000c280c0880a55000f0300381a581d6070442428008060110b01c2581d00010143e5200b03130070080402da0201c0e84680240c0d01d0301c0c04070076a8841e40005447c0002c403210759039065280402da451180c13440200900169582010b44034620150300398007040f20750306628061903400c5200040c140d440c0600b02000b9210003814041402c54844000702e140a96a4100d03c180701090007a644071040c0b8000ca0396001d408801c001c0e038180e00c000021815154075030a00500501d004110390080804030381003c40903000304440c2c0ca40f034240316180580d0707685107010103278003600444501007801d010340754005040e44c8030b0100a8015403615038580744c0a21100440da03410800751103c810202c58240f058004480c02a65503601c0b0103d180104000c07a40d01b03038480c105100d4100b01c200800d0b160003071080c0443ea01100c0c803807000b030070f00c0c01c1080c050030524021000c64041c14294807018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 35730265 1250 35729015 35729017
    0x405030607030903121406040c03090f0305030f0c0f07020409030923090702071d04031407030302030901060803090f0603040203032208010b0402030f0a05040f0c0602010c0305060d0305040b18090705 87
    0x29501990303601401c00340030700c817a9084490380030185c00300c442508000340e95801d054200c034214090030718000440000f10340f0307607400c409083d101c11000123000106203d6081c40d001c40c0701d500105503818503031a01c452070508108911410000a000d25194290081814021b0850030b009252201214440b02900c100950100c0c0040e000e01340b103050301c3c4001c6007165100049074415680c0441484d10f400362101c40107440e80000400c11000c000010688060100c100006445409d2082d02c01580300e044c064485070035a01a034000c1180ca034000d10910300d441da51520404602407050b51402d60fa0348aa0000c613047d03101c0e18200b0000780440503003648800c507840100c0d4040368041d100070000ca0003040c0403c0f080e40f106844003080c000241001c0346000701c1c603902c21904103114950016132138001c1d035200c41420609500100260755a091408081501800750781d42c002d0b011244060b506d086a5006000c1d1f005d0360242c0c030349211010469030400001c0818420042c00e009000c0d1000c3c2c900f00320001c0003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 35731515 1250 35730265 35730281
    0x7060c020414100e0c040503010204060806030c04051b0c190c0e130305040b0a020a14030c01060806011d07050705370b010302090a0f0204030f0b01050316120305040503060703 77
    0x51407802c41040303080c84141001a001e41841541007200c240342008005541c14003510b814a84032040000140c82d6034244002c000800241d141c0a0092410a0800d41008442c400c40b81c080c50030031040060200f00c10300d085c00701411841e00b89032140e00400342a131800d80c485c500e00d000d0703401c1c0c20012400d0010000015007120040381c2c10082d982d490000960205014810080c04180140014444550307150082e28089070284110740901441e51111803008105201c002c485400000703030b00600c58001c0c020300000d00401802041c0035454280080d031222003038184c0c0c3d198030841c2e00109003c18480c00844107016000740807244a94030901c500d01841c0b00c45540501d00e4410004101301f1407000340d00c0d0103189a080000040247e103140c081c0400e03820002c107034180c1a5900e4400d41c0503185144040c001440c040d03980a40c4e03001862600c0148904181c00a920a90080c2010343c2c44003920500c0d9010359994441240382092140340958041c01550032182e4140544010031a14540c10f5220000f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 35732765 1250 35731515 35731519
    0xe04170f120c070506090d0c030309020d06090f05010b010201200313150e0607080402061209030915090907170411030a020406090f060b040602030a1d06030412081e2707060c02 77
    0x62520b80c00c0c101b9950f6044c0c02103460215855200042c0464000d90004805500281c440c03181d01ea290703a1003c084800c0f40e8070448100d04c02c1607001c000d1140900c81c1c014420021300081024428864030003542010f428181100e010001000648100d8100010083c00360310070720711811100d80e43c5204000d0490b403288a9034902c144400150580d02c16081c0740c0c0250380142441e0b00c0e0851000c2c20034800b80c0c00808012082c80200301c51009901c5800c0040680c1c0924179039251a54400410414000d0002c0c1c5200d041040070440000d40ea0a454101904035074001c184801c03801001c00882c0c00c1082103040070f50300c540303080c40005007205960040001c40401c2241001299203860021126004902404005a205104403088c4e14010380000403652800001d00c000c440c0a000000c0303050b4030403a011500c40102a02030013280da00800f610b0742102042000c46044031912034200140301d0010426260300d039a9200c1c400b101d24801c0b0700b424040c16040b090f18486621071401401c1d20701d24a400724 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 35734015 1250 35732765 35732773
    0x2030703020606010f050304060203040501061512050109051e071b08030604140108100b060405040207030c0302060c0c0d0c14060709060207050a0b04050111030d0f0906060e04170f120c0705 83
    0xf03816600c10209000100610b0300c3d40c904588554403080300039003004008486940d6505400f1554030102c1340c0746183c01049030340d0b4019060003582102c040c1d90040c1e01800a19042030144070a9010500d04043d50007510035080701c542e030b5045400c03506013001d82c02d07020080741015594408c0c00500c50007113100f4101030340c00f800003030101e00240c5096913007482131390101d4100e40e007600c0e682d1403d500200c000400c0205030038203094480b4002000c036886440124045641801c2e080c0400d501440016409001d450039141006103501815455a8090f9000c10801010b1440703d004c02c00ca0203280c0d045d108100d01111a14a8072740400f4010040310f0007550050301c1440c4000806240408026090300c51500189040500d010300540d0420708040b082d01e02c0340014020401c891100e84144a00304a108a000c01d842405003802011240250400c08000c1e08813010040460041784d01c00c1400c454896989a03580c0d1034500340700c03082c05201044e07414210326500f44a0300103000350181c50114040c0b801d41b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 35735265 1250 35734015 35734021
    0x50d0c0206070c060c0c0803183003040c0e040b010e09010903020a11030a150501180b0609010c030315060c0506070c020102071e0b0c06150604080a0b060a080607020307030206 77
    0x603079580030202c50481c0065103d0030b42c0b0001401e0b030303003140010521a003802800c101003659401600d030002c80301c92541c145501c00d06282c1280400c941d0a0002c4e86103082401d031894003124080d022095030b0800b040c140000040780c2001100082072000700010343c03620b192170420b480c28050048080c82010328640070350740843c0c0000e1040c8074102a01d94150014211041c16030340d030b500c030910300002c102c0d40b40c011100000007081c0500c00c03210300d003988030500080b158102070015850701528000c0c221190714095292445403540012030394540c509080104004010b4034088010b4458000342880c800404500040c1d0302c1d42100321080854440c5066402daa0f483c03040484184540740c8000c2e0060b40040000c00c05030b84000d000c0030a1403a48441e1022051700e50b4001d0045520001ca0301860742e202e2004c01051441c144c1c0700106110046070070600d0145082c0d0075540e1081541005080707944a50b01195055030303200749203001004450242c440520703000b007000c2c0d00d17604642030507000340c0100000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 35736515 1250 35735265 35735267
    0x606040f121110020a120504030305030a0b0a180911040b0a0506030903073c0507060e01020a0204050c031902030103020105040e07050c0601030b2a0405010c020310020406050d0c 78
    0x1914140d4528203014030650345801e4048800394610002034500762a584000d0440b9211070603c5003040500da00140240d031224a4121070220b640214002044002c0c001400001d5210046a411880c4040c0c0172030182e07a004005503401708107500000c44920b00240e007005001054010042031806489690071200c00300c0d040c002540c0400e8a05a4850301c01d010034000303850721401541c1c00401c1002140d040000c103507504140c0c1604403408550440d4003641ea01c8003482c0075580c10b00762050510740381d0800d40b400e0740c840340c0d9904240070b040c0900c11141c200540c507910070854000c0094000f881449141064209850315510650314403089801b43c4041402072000c1e4000c51741240c2d810303540c0038078040c81c1010900074001d010701102d0800900b0050544040c900f005074502031070040400c6101030409416070360080c40d02c07080b160044c0d1a8000c2d41c59000b900801600c044440130700f401c2190148031b09c0064182140006603c44842c0302041c082030282d4000c01400958080c9541007185c0c8100d400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 35737765 1250 35736515 35736517
    0xb010302070206192015010501030209010f0f050708030f0703060b0a0903110a09020a08070e10090302060708040e0a061505120601030f0209060403030c260301120804090603080a03050606 82
    0x10b074010f403040010614007403030101000c08540840c600802d104c480f03004400c2e5103041502c2e40002d0b950140e8184000c140300c04043c81d0060100b420111320f442e0081002030001281400420305102c0030007882100360f4098804c0f03440e81d983c08100b0683c6ca1800504031003200c0310640c0d5a00c000303803a00c4800f04092404a04071600da080c9521b51816580c030b0f59403001c030a5120044d5080e00684202c03000211500c081c0007401052425482d60880c40c80c3c52203004101d10b10240070340d803054032001c0d07a01d8041900912540c0a0765010f840701c0303584d410036080c44400f41c0704a0f440003c4401c0d49008010301d00b0000d600003010b4502004004042d1450880100d41500540b035600301c5504a400116000d98001c1d1300041048815503809810300e204500040c400d9000b550043e004680d965903010104000c1d01c60200048190403005c49101520380e104054074001406240368625403092524180000103054030010101d00d10b0510480307450303142c54043c0340c0206110b0380100741468003148031454400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 35739015 1250 35737765 35737777
    0x60f0e07091401021207050a0204050f010b0708160c060c031202030c0301090207060605100203040e0603030403050604020108040305040801060321080f070c0213020f07050d050309100f1d100b010302 87
    0x652000c008074145400507072030500c2e00030054107501c10841d102c0c08030b0031500301134410385000d100a04600b200c41e0042c00b0540320001c3c60004066400401441204040001c1d2070503e82c100346141c5d110407401070701c21104101c000b8050690b9551480024000340e0118070300700b9142c40396941008213046040000241c3c0000d6030020403a401c240018846250982c3c0a0200d2501860300807410302d54500105482e105021022801038000007000c2c03005c107412210b16904480141c0c021031529185446480e01e816015000030304201042010600b49403144050324040c107841d00003041200ea4a28002c1c07614a0f803566a801100703400564180c42c0c90140f00c4061051801e0400760001d65120300d4111f0b06680c8148080341d015540e0482c0f003807582003d10203003100804600203140e441000c0d082c4203284c000789540302c40422004004001c0e00a4020651441042d000d41c808200d4070b0000034050040e004040c0b904040301d98503280014034420005403081ca40c6c0548400b0031420b036085004400780e102da2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 35740265 1250 35739015 35739017
    0x503090310020304030e090408190f0e060c030a0503100305010e07060e010f020c01080603010906020c01020301050109170d0302161a0f010609050906100509061605060604062108091201060f0e07 85
    0x34004808030342c201403401d10782c82403003002d0342803600b0155002b124503001c0421041c000100b1848805810701e800c060000700350803046591500f458404001175a49100b5000700b201007200c040041094410058180009150b110b00240300780300b000192280d03580d800713219880001d10014001034641d400340011480d50801075000d0505618150010340718040c0181c00c80350503641c0d500990003c95501c0c4058810107911400169480d4503000005180358980c0d00080c880c9540c0d080703003070b100c2d6800140070070804c007131801d0241c1c5516030362034500d03030f68a103500c0060214440200c1c2d211a5205401c99648921101c0c211070b481a601e0340c80c102c456612030301540d500305228001080301e9180610360310321304c85810329205203040b50600c0482e0040e0054000d242088000c1c0b8615010420280071940d03202c0c5042c0d0b000c0101c0d5241030720f2191803021104082601c680c14810710703824402c402c82100c0300100044c2540c800d1800d41003d0a000f00001d100382d89030010b400b00c000c070340124620707003060194440b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 35741515 1250 35740265 35740277
    0xa0809121002031005011d1e0301090f02030c030f1903120e0a0c0801060602070306090606120506012301080703021602100c020a080c060a0f0e09040f050f1c0302090607020a03050309031002030403 86
    0x40010300181c232041c0003100c5a181c0041d0070f5064950360074003c02080d940700c0c00580c2c017110140d2051514016030a0350482c402c0d00f140b5500030401400040d50840200181056034501025050542d006414081e850b0411401d00b00c0c4042060000030718540301c03a02c6100d580720402d40e40c2582c2c0707089401c54000c500042c4c20145081000c42c00d20341068011078028540019640d41c4e035210f10403110104c0c031040b0344540042d40100806404a040480740c16021180c12548000801c002014104d00401542c2450790115843c16404116070700440c80075809082c0c1b480c00401da08010341516211070049124501110000c61401c801003007400c86124040d010904242210344143c0746030740442c02c03500801400c04c0808526945201d003a6018174007941007040d0310a018108031f4146102840070031185c6e07000e03041e1244000012054404d2070b07506441c00607210103a8000141c5c440c482c106001c2e503c000b200c0b201209004d004802042a1941207003211469003048117800143c0c00100d4014000c240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 35742765 1250 35741515 35741567
    0x8060703060501020c10050f070501050601020618060402060703030e01141f030206040b16060507080402011d0114030709050d0c050406050a0b07060504020a0b13050a0b04080a080912100203100501 86
    0x10719810341941b615881c1442030134401c461020031000e4003c1c1000361041ea442e41c0600c4181e50f01446015001700300f110120b088942e00380c003130a1790342e10090030003801860300246c0704080c14400d9100300d150100d10402072201c582004024644408140c56860f1050008140d81d2151901061500216540940901c2c101490403d4906c241d0f0040303140c0404410011030003000040d400d2148500c15501e540711400d290078507000041c034014102035a6501002c044201125aa03000001a20b0180b401da5006541c0d6554400450f0303424220760040d83c100005100e920208111200030005881c42074804020a60303036902081705504203842a644001000c21401e00800c215170000b0f035112b400989070903080c4d6520744001c00d10fa409a410070050083c5180c0910039807408201c000000c00a07170711124142410f00300b00300d4544d4a1807100030000c075000691000d003900c444101c03100010700c0c5001d440c07282800004000195100303c0b8154424500184081b60307540c02609000821050801105142c82c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 35744015 1250 35742765 35742769
    0x6080c0604080709090614090d03050f010303121d01090507090c05040609030f0804030b011202130516030203040f021008190603080a0e0109091104050a050d11010f05070501090c08060703060501020c 87
    0x114a1780c3e0207442040e2074601d42500d050001070105d014040e0003009014910b404440103044810140507c0a00c0950030010404260311251060250300c050b0800074102011240a6030307120308240c00f1440950814078410103104000c02c40701c1c1142c0014201340f00e000c103001c108540a02c1280078041c040b8813086c0003880400c100001000da4244203011461400c0c0d01c13030306c81264140c0240c1c0a0b00c1c5020101c0041400c5041c110301c60b28610030382220510a070b08001c504051452081041381c0d041590100010701844000321142041d15000740103100d4860039004028881b5008840124280f800c078a0308000021740ca2041c1c0084a800c0300110f81401070504c23080342c0401602000604100341494042010201e91041307150402010440360703070701c030b242800b4001008042ea104a104822444840c0f000c5103403100e0b000b28588003484c01700342041e41e0305404c0c1c85034020320300d001d0088d46ca00743e04d46042040c0305402005813410042198403980e100c2404a0940754507028150050f003100660740414 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 35745265 1250 35744015 35744021
    0x20907050a0c0602030a02250206041701020909040b0609130f020402030a020d0606020d1101020f0706050405070b0c01050103020108060d0302070b0c0309130b04150f0302090a02120a06080c0604080709 88
    0x10340c01a252070808000143c4802c002d0344c105403000c0a10030341c0000c00c08407080c00076003818003001080260340c1c00b0b05421740000d0720900035032103804101c10307000b02207800c4500294126040080003c04105081c00c26080031680321108032011030140c140300e40030440c81c0b9883d1060740381565000a04000c038242e65400d00020f5000030340140381854080c884e8214005540c052100900b01c194000d0031161040314000304100440050702200e0303481000564001c1c01c01e1000c0300c01c2c09400410110750398441d458400d29101d03444e4070007010780c2e40100f185045c16406410007412a4000da9404c0e1131900d801c0c00700505480d002800030b01513801400f007000005050700103400c21240d0002940d00b048802808207290441d0510f1141d0584e5580003111403034034181c801c00800c003a468003004041c03801d0a45a4404126034000a0f1040c2c001000086100000d90110f0350420705580710f000031418804540e00207024203000d5582c0c140a2440e806e40d05040900645d0201d4404000401585240180030401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 35746515 1250 35745265 35745277
    0x403050109020922061806091a150906120703020603101517040308060103110a03020c010f020306010c060b04020d09050f010b06030603100e070504020f0c0606030a0f110103090204060b04060e090402090705 90
    0x4154100c410506c003103841442250b062500405010490034008a030a4241d000d00628904418144171400015510740d80c8600d07501109c00d4501c1c03250102c190301c1a80c50306050b6400258841000005c100b00d8140f40c091040c105c038190310990200c005640002e072561070b1740c030b100444081003000000f00468407a5404641181c0113040000c2d03448004c1140720401d500034120100441e4000404100c290401d10403000c2100c900507003141941000700000700242020311001e0509904c0b01040515031340c80350b0459402141c80d40d01085001007500e001034461001e0802e40b41913519240d8030b2000e41c105401120700c1200c0044c06005500c1d0030345d0156008100e1811410703941c3c801c4044c049019116480107100001c1c1d002065038581005035502c0e0310342400100302901030b8005c280840001011035080c5c03036015a1141940f41041840da00490003004072080203503001d400c2c40ca0004683e0411002001511240c0d0740e07254204007104103002c101c00c000e03607009401882c41c030b0010700441d1050300074001e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 35747765 1250 35746515 35746541
    0x11070b160b0618010626010806010611010e060a090201080a05010506040b0703050d1a0a06090b0307050f190e040c0804050a0f0503070f1a0624030702010908040305010902092206 78
    0x3024071060803c021200c0f000d80000022401070160030310350704000d0340340d204146882178500c15250304180b007164440c5410321a00040c80080c032104c0b020a20290000c0f205070b800d410840d8042e16069194a015004005090703000c82c0400c408100c05000714020a4142e9401810700c84c40c003803516607080c410b5404924198108030f000d12000c2001070050048242c1568503070340b1002d10341e400500300b059041c029440b090512014000800180c603604c800d50354001a107080c141e07110704100015590a2244002c3d2508401c00303c07100e04900e50b000018001c4926056074104021041d2110566440710107850241c0079a02c000710040004941c203018405441c860000e0382c1c2004690794516045007054001150b201400031414078100c604100c4a0354840b400f201c241040c0c00010006c100207010760018003060000010005820078000d4000e56140e82c0d00c6518169150303501d0400500800c20705000320720400000000c9802100a102c1c804038a41801d45103004c045520364401c0010b0a801c21a01c1d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 35749015 1250 35747765 35747779
    0x121802120c090a06091d1b01030605120d02010c02120702100203040506160b06010c0209060405040206040f061805041b03090204140106080402030d05031012020a031211070b160b06 79
    0x41040c2c0310750070a81e004402920003c62100d0400002409039140d07075140d0860f0ba1020030b84010b103040f0010310100b188030a103c2e22107260300f0002c0128003414058001c10382042d05000c103442903440c00942c02c0d540a4480e402003101d1b04080004a03111002044031644000c410700035480589001510a64100c24500440f85032070f59840200f14290842c210000c82204111012002d100d940e00d8615403243c024030f0f00e005100010303030008401400142206024540c0c3e030b00003d04540341c910899000c0d04800f8040001c4907a91507004098110390740451022901000340020141005e01a100c01142884940c0c4004100f000d021001452031010580c3c0c41600e424140e00c00080080b68180a05415a50806507150a00502d840c214440070f1100030002d08008111507440032100030030503103e000d1550b2a02e4042c078000961703801e0594101a0000358070304072100f01c25400c2980040404009026180b807140d0301c00031681d250142c481c0021040c1e1f284c0f4030b10000901903109856002100038a04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 35750265 1250 35749015 35749033
    0xf0f080a0f0e030406020708070b04030b040609050f0f071224020d090b0a0507080903040b0702010c02040c030509060108030406080a27031809050103050d05030702030c0a050d12180212 81
    0x2002d880c8100c000c004150400202403040340d50500585028100880050901600c3c0c4003501b280c0d41314510025040d1b01180d800318081140c0ca400a80d18a6040000c41d4100040c4080042d00c0d200c40b041c9401c010300c03400c80d000603600c82000a03803e00d150060401a013100d03041d241300e0a81034440f02030f4040c03158200f002c21000e00440c8124140140100e003010b40c03e00e0100c0c03698045600c00340040c0240f042c100100150780034008220703420340e0461a42940c90b0003d520060b2030441203140000e50050408608422903603142c1d0000c0c1c030030f04441084406903603851242079164856809410300007400f5000042c0744120707903005003009030300040e280c8182401c2c01d5000c0782ca02607504800c50000d1111070b4004114085454400050030b911401000a945955101035844080e5821b450503c8004400504524000d00550300c04081100580c1d0322a5060701e03200e501c0302400d0007210003241070740301d454071300b03040d14441c40450003001e04c45c0740d6a0807043e40811185420746490502c19114440403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 35751515 1250 35750265 35750291
    0x1403041211031201030b0603030315060a02070906080105070824010c1509030206010602060c0f07021003060b0a030203011a030103030c1416090501170a0203060a11040b0a0503090c010f0f080a 84
    0xa1209103d00d842181d015411864450442c081c050700d003512990051040c0003640c058668640320002c3c0032170748556103840710074084c0d05002c01076010311842844d16000148240d019040a4420f04ed580d403603d210356107034020400341c0c4042c4005444003400c62a0900b101d540100c0c00c0443ea076000302c00c0c0c1110070b41c0a1200308151034034150308400503000880100009501081500d03044480c44100c0c500308442400491140d000b0101c0c00b80c802c100041035100014080c0c1e1100010f80800c01880790355404100c40513010790f0086c440d0880900b480100b03024009800d00a40e030589a0513568100090202d07164541401000c0020b04103a01506404003482034500b00b01c3c030700422202c10080344561412210001100100b214407038503030070103025100143c0d408155a80d0012070f131400002c0c1c2c01c200010120082c01240c004004c060000144141c041e07070000055031180d07070030004840c90403a601004440002d01c40d8504000f03e566400e40421003405400800da07c01b1003030000141c4060072440d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 35752765 1250 35751515 35751517
    0x50405060a050d050f09030a030b0a0b0c03030f060d0209060f040e010501060c1506030c1503020f0f031503010e0c060c03090a0b0702090c030708070e0102010b0a06080115140304121103 81
    0x891000070070400a2803c07224200390088683c070049090420060b841c0c0102100d80300c0c821040510101685d5107003c0d20700340c0e50b801c0608087c080f840b01c0c2d583c80386400b0b0b11031070340c035442030b100c0000c010010700014101b8541071481ea646681d02600d11034145d02e800c003d0000c154034021449034050388440500c0322520091041c28004c1c80c0c0ca031788402150769035090824024440d14401c0d51018186102480810039566102c012a03003008010020724451103421030080c0030740000080c1100d4001404c0701481c07600400345000340d01c12480c00b1580015442018200c80c10303a491003010340c100a0400400f80340c0800074080184400c8142d91500b001e440008050202d00e800c503060710180840c0510644c2032055440358003076080707000b10703207182080200500450300003440c0d101000550b00070b0076082c0e4401e4000c152948c0d409080034940a4440502604110782401418025013050f2011004588501e030b00e008001c0403030440e20324545070b40c0c407000030715032111100c003081c040703c806001401702d0104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 35754015 1250 35752765 35752777
    0x105042709061b0c260c010507050301050901210b0601030f06030606080d1803080306120d09061206030c0e060a03050f01090204140c032a0406020106080106080102070305041505040506 81
    0x100003466804080320310390801c000c00d440c03c20081c00310744240000d1082e0f00d44000604400000d2503000301d03910013101c01d030720401a4000c07665080509100c030441d0000042c6058600454100c0b00981c0c0b5a2041111030342c40c41d0040441c80b0042c03107518046846044100d8100751b0603d03000c5885000000c0c1401a69096401151600d555040c10008118180400040d0182c249082d1146000c4103041401500c42e5000152940b200080810300540d517482d51100d12011604c2644c120039861080070300750340d9040c0718040200f00040326201601c1210300c1104127a03a0300c01100b040d000d05100c030805588000400b0150040743c220000f00100e80100b007441d000c500c4010020800002c54418482641c0c200b82500e0301d10000c2009220f004100b00d4252036120b201400f08450118962010200c036044c810301c50480140001004540e03e035041d0451410703116050020f102c0581e80e0f40a5908034400c1440280011b1400c0c4410b02c0141d10041165140101c90702e4034608290b140c000194580d072000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 35755265 1250 35754015 35754023
    0x41b02060108012f03060f0405010e0603060f070f080606040906030510060b030103020f04020c0a02100c020312040b250507090203090c10080711071503050103051b0105042709 77
    0xe040100001c4009000c0c40d001424689494140750b400e89580e18000508501204180c04020000032082c0e2a40d444169801e0780c0148144000d5075a590b561031012015906a80680a458001000c0d40c00d0303040828098030702941ea1090941030618100d0784402d014001c0c40c0d20120800001a0355501401010040d500810150010000350b1000504a5400c2ea20422954030240010409030340c884107168940b040c1035401691b42c01040b069542060040c3c03034001d500c031540340d0385c080c00b03554020070001c021071090302111140051a44000c0560065200d4901501d030708001350764205007148000d41010201d100080014642e6a030b5083c02c1c050b0780e8000821042c0d002c0104000003000300040495860103440f00300c002c2000b07030b01c014400000105690140121343c081060020000c001e540d00400b4a80340088207000140c0c1d000b400f0304400e101c10741d12842240c01c00380c072039034001c85100006a0f058540c545090724242d40804082e854124404c91541a030522024420b4603000399031005101e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 35756515 1250 35755265 35755273
    0x1a04020c0309130603080a080c07050114160302041511161401090b130302060c1e01020a0f140702040c201f02090a030b090309031c090b190806041b02 66
    0x301c0c050000c5003111480420f8910b060040c104081050380088510001e101e107000b00c000c0c0da5100e8540305a00c01d94000070036a41c82c14680d1036500060040c824018184200441c03490081200308a05a0250340500e8014038508690003d078107000b580c40103c4807090b00c00f60341d0680391284a4414001c41607112a40a0380030070310f02400e561f480000c150181818400d0326007070143c42504001d2480c524000240503050000d11900703907040070402044c481510f18008940c804907544c009010b074000d0203106000c00c801d100c134001e806003e089070340c00080202e00f1250402c1c515408010250130320360402800d1046007519500441344068519014054400c003d0041481a00c00b0042e50012442917600c220302c140180300c00c65072a441054212904940800e03440d1303c0b400b2101e03055100e40c80025500d8800e00000c4040a03c04403541120300486840c2d03905000e64401000d4018440c1548450384041f041c82c2c281e01d15806480d500c1d400142c0076100050b202000c000c80c0000e15040c032203880150340 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 35757765 1250 35756515 35756527
    0x180a0b0d051b1c0c0e0c0406021f1b20010605011205060118030b07020601060906120218030102040f030b010b1206010c03031b02030c011107020a051c0f120206090a0203030405041a04020c03 83
    0x41920ba02ca40040042c83c6e100d1402c2c0c17030042c0094441c0c1d0410102c54040c030298031711007440340080d0070040e01c91a9590000d1030201c0440742c058000c203120020000910000821002100418400c881c1116410384030a514140e060504800407d4001d003060306114442000340045c1500010b264003552240082c040e0b40e040a0320040c1c1344c010168401d40801404030003d00c145a40a07044445034262980b0150b202c0d255000c1c61804e108061030841d4040d0f1010800040e200c203400e1182e011a4084c1007000d4031a600da401c2c0c503009100d03110f0015903030714841021500381c0d4401d40551150b1400f03490002500030700f1619481082c084020b0f01001a4008104100c1c2c01000380300d5849043d01e9045140d141c1010740d80856554113042c0301e602c0c42942400700940b014075110f2800000680c0c00f58440c0d60208180c6801403040d0f40c1105041c005106000000d8266900011000705064000f001141803a141404100203130000704404000c018603400004d83c0350b1140d002900c6074080c0480a0340d2108 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 35759015 1250 35757765 35757779
    0x4090203040f05010f0606210e192a140d0f0b070f0206040c031211060405030a09060503060108010902030c090603130501110a1205100302180a0b0d051b1c0c 69
    0x1c05400c009003170645000c400b0800260000d441a2440c01c0c590060307100e1510b5080a580180622114a0001d016000700c00b13801d00285440c540002d0720400c20717030012038003501d88c507400744500254180c101c0280d02c1080c88000008543c210604000808030075185150b81e45894681c1486982120340f0384245050092458102c06103a00c1043c141c4000c0126240684605e081241c076840054401e4a684140e070348024410500056582c40e503000326603c038100380c60602d43d01d0f408480300b003000808040d404504a031046040303070f000362016510000540d0134030190f04001c0d4006460050082000c10407200e19460f142d000d10300c90440711400d18510304d16820290f0a4131001441091190000c1182044554201010281204408e00002070b60395400038207041170125900060340c00724100c034201500000000d0b90521032038202c081440060b00d042e00780072585120314002009030b0085e138091a00b5100000b1603150f18080180300504580b00240360001100d64070005807801310450300e045c8890 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 35760265 1250 35759015 35759021
    0x3080105040908040302060306060909100513020408031c02040f0b070501110a0f08070201150b07060b0f0d1407030206030907080d020c090a0c021507030b0a080a0206031b04090203040f0501 83
    0x4000c29141484100e24564500243e403181d404024402c05011007c100380e611117006035219080c02a00e800c0260400894440c0c6003851486040d100d5008401c4109482d8803500a503070444070810011410003550380c0c004409004850506007466500340300014a1500161071500180b50500c007060381e64040b41401c509442c040c01c0020051703181044012050740d80500c071280310003421320f028032a40c0c95141040340505038000c548030105206000208644441740003c5c45290310500d010065441240207002220b4128441c4a40c4800c945071580c2c00306006d800b01a600c0c0c804070b400d0b40c41075912640020758540080c2c40088070369011f600c052001e5841042074650041d041e00003803000307907070320000a0030740d080040003486296111200c0394003050003044001107140d40e58601c00c501c0c0c40c1c0100024014808420568468248803000081304c1c480451651041d83e00034048603e10347d074022014040141c072032450b0034408400c2100280300850f0303201450080c2d103d41001c6860150a00303200d0700f9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 35761515 1250 35760265 35760269
    0xc010b03011b05030c0403060507030b0f0406181509020d0903080a1406062104121d09010b030714120105090f090604020918010608010c080112080306060d0603050d0c030801 76
    0x103a858401c0400d80c2d6084100701908003425490940d50300e54419860101c0d9008a910050a06041a0074051500d030542c00021800b181680c1c0c5420182e440803c11068410718420b5004401e941c0303804a2200c01980c104003135a8860401e00c1200544e1440e0740300c100d0703005c036000399801992583c0e440700300340d84140819006801e5032400c0c400394042014000c01207102070171040c451440083e260141705207240c14542074502440d00107201b0726003800c1000c85500d00c01400d50004001020103803c40c1700c9100c415010400140440056a0a10815406540c005001d4138180030303503403240d002e1030f41d83c01000f041160b1601d406071000f545004e0030320051020180080001a142c2000c002e1012400292030740c0c015011124404540c4864003000e54001c4490005070865080000119603c403054000094265a030f40d5800d0b010f84e6200c80d2150400681000140341039403c02c0403d54601c0e014019081e07913080000300043c07440c0d482d91650304e001610301070700012504101030101450741207442c00d80 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 35762765 1250 35761515 35761519
    0x10e1c0b040512040f050418020603150301051e0a0207050a02030706020106090506010e0105070209061c0f050c010201050702030706090c0509070806010915230c011401230a0e090f010c050c010b 85
    0x400c1900b01015a850010316004860040f981c6140e5234039082c0c4e1111004104a801600c2c4a6490a06203080e0204c0c0384034200c0301e03002c2d40c00c00001c0748800040d08100c90810102e80c0000950382c40c2c582010000c0c4d40182003d480611401740300401507942030005100800e8650000151249000200010fa40c0000c2080b4140501c803200c16601c1c1e42c0040c11510201e0707049075040d1140d42c40320700041010222082d00d501c0d0306240c0e9550001c02c246503004810307441c040c104030740b0f1074203415004a080e16011941d403030060300280411000682160001003155110b40e44581d185600d0b10301085443c54100c4403603000031f0f03100040c02100d580100c034a00180400220313400100d04118030142007820311443e086002083e02d90703d03d0313040c00002c0c182d40300c507007410000340441010740407400c462050070b001d2200f0744443c807080c0219030040c40305080c0c2070110191401103513034a86a0350341541407004001c00424054024040c802e03a1081c0b08210b0904030301d80740c89407a0904004c261342101c002104040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 35764015 1250 35762765 35762767
    0x1060501080c031801050c0a08010801050112020d031101021204030e090402011e020328080c070f08070201050c070801060f050d0503090f0102030403060c021005090102070b06010e1c0b040512 84
    0x1020a99000e4041544580100c0c1c0041e500d0300d514410a00070048616800b44652070301c0e0900c5000032000004001100d06d964505003c8e90700c03109958202d0340203100d00b240c400c00e200a10001820071940100c0918002d0a004500012000040d402e99026010040b5590000404c0004241d080000852042c100b175595110a240c00d90001e00400307402d284800c0c0c801d08000ca6024024400c00440b1010703034440c420b6681030011b903040f038511010b100c048500810140b400107429040004150345003141c00c4507150a90b1001ca44914400d54002e800680c1001420082c80c0071203071003008510010b1040400000300185440c465485450b5503420052189180c0a80c5801040c0004241c0c2d601c40800c584407003400b42148010307441c40c42070b544010882801d003080d41000075000310340c40c12010403400b414070217507843c90b04440c00c07840381d800700a0a42106101142c015403245002032141c20f0040c221040842c02000068100d044090b070031140f1080040401c03040000502803084503070200e140341 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 35765265 1250 35764015 35764019
    0xc0803010e0109111c0b120f01050f0c07050d03020f0d050906041104020703080402190e040606050310060503060a0507050d02070503041509060801060e01120c2601060c0b09010204090c020f0f0106 86
    0x81140c0303000d11000141040c6e21841c1c0108140c2c1c601034a41181400b10084030000c0688414180c040d0400b11840541b0615900000300614055001c039a41185c2c0f1102410850802040580c000d4108007002c1d00d4522061012100091403071041e64021440f60004094928017860160300d0803807010915400343e4014040c90300080e0300406100d402a5044440c142c103e00800d10030400961603600007200e2008420a20042c4409a0300030420703910b0a5098412141c1301c0c80724030040d9400d0b48a001c1c1c00d0b500040005200403601d03444150000e07110315019280802080c03048060343c000d10030a40d40f030303000043d08004101450422420200e00da0030244103c0d498400301130302c2924140310700c9060107880c60040302a40c1c8502406181d4140a003410400c81809840080424480c10012008100030410700078140603e5882e080c100d503000e0342d5524450720b030755079020520310000c1c0122016640901010846c0d0085000760290000d0960081c1100441d54440c2c6182215044101070143d24021007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 35766515 1250 35765265 35765287
    0x1003090b0a022119110d0b0604030206070b07230a20030301120614070e131509020a020703050102040303081b0c0304030204020318070602030904060602150a09030c0803010e010911 79
    0x4485008000d003103a00903c2d41d01c0c00021030740d0301e000004061a45243c44600790780c5680150241504184100c42006000d54500500c070040c402d500019501c60070601681c0c001600c0c8a50300d69102c1810b14105040c100311501c82c1d84880400700c40c0410994010402ca8070b8982d005449294000d140405044d40907142c0d824203459104c18025080090f8124501d641070011f144c1010079000790720812403a280c6031124004000c501c400c580b2904c907000c01060811407800314005c40150681e0a80c540095a2810803188025401891401e095002c2d9034400408110f087c03001c4c1004501035120200649061806050f20720a480c481d50711001d02480704a502d1a000000e603020b90758150f80050f600e8490420309a444000040941c4d10b0f4032810202040050b808005030080020641c0c062003036548a4a0981e100d010700d84c0c00c100c1c11503165001440c00c00482e00321865090107420070035041c083c9a29001c1c0d00c0d90098000e0790050300104010040171525219400c15046020646070601e00003040b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 35767765 1250 35766515 35766547
    0x21010f08010f090f0f020102030f040b0a110f060711071206051f030506010902030c07080307030c0e010201061a030a110a020303060a0501030203090309150f071506080c010f031104051003090b0a02 86
    0x30054a486540c066176021039008008881e050749650842c80e484039521001c4882a6000300050800100b6912020318462400101401a01004400340c01195039180088030420395a004004d180d11801c0e10004031004c0d880c040c850351300d0041c0700114542c80c0409a0806090320740c1e0300c0d51810f030380052007000860004540c66054402404001d43e50340c0380c80c08421a240203502c0c02405106000050058442e0035600c0401400156100c50981408800059003240c1d690b120340d000c500012181141c04034100401564403c0c50b0480000e803125407a000044540c01c0b5a01000150b4000070600c8500e2a0801901c00140b000f441c0c258554904001d081d038681c05000312490150300300b507912108050710301d0151511408103c180e1620344100d030902040040000200c1004d0526010000c20019000314444001a8060710f40102100000c40704030f004007112584002020400d10002c25980c0e121005000b80013095500030a9000030303800c4c82e00a40f00003a02501c8441e1040000c4403400710805 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 35769015 1250 35767765 35767793
    0x240b030105130f030e01020c04110703020105011a0f091302071a0a05070e01030b0a05030615040b06040303080c0c030702090705070605070f091401090f0b04081b0f0621010f08010f09 80
    0x205c0e043c8000c0480d10f0060303182030b90054020b94040d0611260009203c004009060f0b83d034040c3e4000d200b143d9030f40702000100030080c0c4c0c1010320100c08120035030002c804032000744080c00f006000702c050007402807203400c100e030801201103640b0000a80720b200c401c0c5040045030380040c04508100170505000c94040c21080319414010305044d1260929502951040d818400401c8080c1c180e0b409480d084100007444452640094480e91404504030101d04011040d80e05a95050f200c40324162284c2c03041c1d80392600700324040c02d6144000c001e1280140c9a403940c1d28046c4c001529050b07110700c403924100080d80c9000b0f20441c10000703280c0400c070489a0101e0901c0c11600e002401300040c00d60207004907110052a00700803a101611076000a5801e0028024003c80704680141e910290051741800c0c0c00212090550340d0140300411950081e2400b00e0080038107513100d187c0c800440c10755189244442109034840c0c900c4007403003641040407650030700400e40c031715607461002c001c1301d2096660b840d84080a4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 35770265 1250 35769015 35769017
    0x1008061918060e0105010906061d01030b120d050405040b040b030a11010309061107020f01022103180f010b03010501120203120703020f060c070302010b0904080d09240b030105130f03 80
    0x480c1c03418040c1408680740c021603600180203205004485402c1400b0348828400c42c4402c91030a13000184840c46901580403002210040840100341ba1004401810007001c005920070780601010b0305040c0100b000242c1441d60b9248c2e151150324000806c41112354071040c85001e00c1c00d103141c174543ca6401003000820294401c03140088041644012070050400000003040c8914007104202500c4070603020300388051003100c0703104040d1400001240c0320140f414050001c0500c030007000b080c810303d82000c7d5074014664084041c5a400c80c0c8451490700ca8450407440392a507403001c0081442c10280100c0703025201030601103039250342d07a60100342c0d6500d0b0040e90304580d4401052450070076209000503288000359008891a03801c0c0103030820280d501180b021000b40d86001d0341900d0300c0c204140c00c07500c80d075040080f413410f003c1c07140403a4000d0080f0b0301e01150705490f9845c4000043d01050030000c0c801d0000f00c000940640c0e40c006050860b803002d010120344040003184000001d920307000039042940c2c5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 35771515 1250 35770265 35770271
    0x10e0d0b04030e060409050f0c1903020913050f06241204061b020610090c0507111f030905010f0203011410020109051507030c08010501050d020906120f10080619 71
    0x702d080c202c80300302d00300080300c1c2d100e00000740008080032142c10090103010300c14400160350310b03199898000340c450080c22030b48114100d01c061260307e000394060083c400010340101405a2910049030445a0440e0b044d42c119000718140b1045080c0145a24050030a2900c00c1c00d4246a00706841c4490040d000c0b4040c2200060000070100055500300c0200c1c010745d000c82c42080c40800380069190f071011100030404145060000842c40e0042c01030039456012a00d6252030030600d81c075080300c5146250401c0b9003007007011002d015101c0c40400c0600d4004036660300000c01a026240031400d40c0c001035501c8041a00500040c084454503c003450360b05201107400101503d034a40c8242d000d03150700b000c05060b0b4054424405400c04007408002d215141a51741004020b41c04181511869020302640c0d0014500b0702c0880380210031540104201c260081503503041a1002c2d00c03a0950110484c0c007a80c5500008046c0400001442c0d4400c01810904020308204d1410301d9080c01e0070004401c05076101ca403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 35772765 1250 35771515 35771521
    0x1050a0926090a030803060907050a0f0e03010212090313081204090e0a290108010903080a0c090806011212020d0509090c0405040203090c030615130b030f07030609030e010e0d0b 78
    0x6010811246030403005080c00c206036a8a0170325800940089a84ca809031b864a00020707403240c4035000700d5201d640305480711b40d0010706152089074100a51048160559801c21052404060304000c0c18416109000196035400310b0786131194403d006030344040760b603900136620008841201810b42e800d0312650100081c240c200e090500b40f170803940320405080502003aa144140c685684010120314144054420250342d80c1c10080e403c0f2409600c01500140b039440205040b0145c40d0421100d080c09482c0c00c444068071b0300040c609044003170344100010302c0044107000c10800d842c285200910214005021141d401c0b45000d0034501c18201480d100d4000c22001511411120080c0e502815000d0011500c80c908411060f66030b8440120042c801d05c103400004815515046480035480c8002d0500f00354440824100405010002c9040d64107005903911404181d40c20010800254002d03034001c80c45803210304000d005e420740d8001650410420308114001070b252141c91900742079010b1700186240d9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 35774015 1250 35772765 35772833
    0x2010c02060a150b0c030301030b011d0a0b031c02070e0f0903070f0203070b070803060307080f0c0f0301060806041203061509030305070302070e090a060506091005010c0804050306010902040801050a09 88
    0x200450f00900728413000401e004104580010145060b17922841e0045903d988500c1050a15600a00d1800c5024030710702c005020344140750002c52100030064201c1c0c2000c0c0c02d42d080c50100c0c840070300980005900003041001a2441290f0a80d0040b040184440e080d05108010b1130f128410500040e01c6004008200001c6407010000c2100030600e10821a07180c3d805482c100340329a000380c03511031192107105404105824041282464954503000911440100c00c05001c00240b0660390103a040d5a0307128001800c4406000c2c0e0703841944039a2403070021010f411400b5085481d5604250948040803150489040d08156614240d035014206161513501d1454128508100c41c0c001c09003100501081c4518298001403030103015203d01d5003403145075146c13000c0c461242d000b10342e031240d0108410400c01c159405007240d400c1180c0a26000c0d0300c2d058580001c20724180c001c0e88109081035002a082041c00000e10403c0c3c0c0014410409001607501030320b50180140d056010000c0d10b40001222506030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 35775265 1250 35774015 35774051
    0x40515030712060608070e0406050105032d1e0106080405030703200a080d0f18080c1203190b010804030915030207020d0804030302070605040315180203010912090602010c02060a 78
    0x2d014042424070010752107103801042244181e80d084003044620391030078010329141c0229025038a040e920a411907498840c0c03031541d103203842c24010b020540c000400c01e01c03460308003016220700240c1550400781c020412807505002d4050f8803c1302044008070a100c00908003008a54402d5098900392340400c000c4400300d9410400342c20110154032414040c013003000030002c041e103805846040d041007890b0800304d0240554400e00003100d0380c01d52130000c810020701030300050601152160202d5903020f4040b00301503810351050703968038207410350304c02043d1000500c1c1c0101d0483ca40c0a2a0110741428140c1d0058050080c45c000c00008070344280740034581610030384c1a10b10380c5030000d16031421040075040140c0d45501c54002035005002d0a00d002c030384c0c03d000c0c004840444e54042d220300c40000030007100200038007543c5c5080400d403262a0602001d0707030b82402003000040c0031354000b101401140e500a8020311082c1d00050540e41800100c2e942241c010030041c0d8007070900c40e07000c100c1c036284200241070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 35776515 1250 35775265 35775287
    0x40f06020a11061018021305100203040e010605090a0b0909040308071103040e01140402040b120c070f0501020a02061f03030c0206090a0f06031104030c030f0c0e010612110405150307 80
    0x10b4441c0c4810404c07411140080407084130800020750707043c03050f104c181d6416403052841c069031100c4441c8040203a410724085401c001d03041c51051b01e0074591180f000448441080c0d0040c00041c0340404c0c0020030b49012a40c03a4000d0501e0000c9500e09280740c0d0220300c1220004002400b030010710b40008082e240616803801c06030010301c0c2500d64450300d51004100c1c45000380103216014012031040c00b0581840e100b254144c41d10104114108102d404020300c9155004156640d049401d01c00000000c1513184d0b5000c603507100d90000341c1c8030304c2e10202c02454888018080076580d815040d5a01c4100a020000002e4a8040c40c140001c181c0c2400070034800d220321411981c210040e080d001030362200003001481a140381d5a0184904d42080051203418010303400091316a0403240410000295091a05404d645c0308225800b410342e034452210b003071070000b6440381d40460000c441ca0760f0b000d500f5200e60b00501307040b400082c1c180383c181404100b41c45401064914422000070201e00b87c01d025601c0f6500c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 35777765 1250 35776515 35776547
    0x2031305030a0c030207080f06040807050c0a1401030b0d03080112020409080a0801030b0c030105011e1e03020903120c070504020f0c062d1905070306030b040b040c0e040f06020a 78
    0x561090a0300b0001c14000d1003d805a005000f42d203000306000310040390940f62070740b000d0002d1034151101c0d25030701101c0c0d0107000b007180c0ea071240b001250407a0711654080030041a0ba801008001e00400b800501990b82042e40c0d0351040d600c0c1c2821200094100030f0542c19a51b001d000051740941910115004042c1444043c1c04c403e40400c0388071206a010000c14143e03441000041a00d0715020b5070016580406c0c01030701d0110300840d001245101d5043c020b001102d829191125803ea0340d0180030706805802070314180040e0300019000c405003010828100c0c81d109070400a0b203842201d40115407904124040e50707120700d8000401c400c8a119030f0094803940f071241d0043c0ea9441c141200344041c03140799040c02e450010180c80d0035640031300d010180c5034484c2200c8000071810340501640700c00107041c001c0100c414160b8450020000c1216078195902c6940300780010390441c20141802c584030080d5034061130729074119804000001e030000c4035125000354440307805a01e0305105c1c8020789042128264980f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 35779015 1250 35777765 35777767
    0xe0109020402070f050c1002030f09011b0614010807030c0e070201060e010e0103020f04020306010206040f080c030703180b0a020a0b07030906020309010207150209010c0b04020d0b0f09010b040501060e040203130503 94
    0x7105000b01c0c00c1c004c00c00944a01d0480c0c1a00400009000072041a80c0040000d6002032042184100b1030600a200007041458010002100459540700c4900d40050a860095942c0ca9481c00c0c0c0c2d415559490144c03080320000d160b00f600d1651040818842030040d40e50902000b07010860080c001d41203070300505101241e03e482580c42e80000c56064a091000b40d104000f4208640c0840c01e040c0308590161106a02030406952540c036070440f900510b06040b1a4646c04000702c6241c0541480a4448980b01e40d42d0322000381490140c0c18840c0d1a20780003000810000c00c041c583c4a40c0000d4440101030340300500c51010b94440f00e003a0010300c41500050a03180c000401c011103058198010b01e0240d01c140043e0a6031410a5011000c0b40600d44240340030425503c1d0301c0e0013040c06102ca40d640300740300a100b0100c3c00c03a5641e81c0c07211004151690030300c45031410284030010000b0701401e03103281000c1d5002c000c07541c03600100621500071981414041c0e907000000c141c0c1880f03100e1500c0c1207241c11808403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 35780265 1250 35779015 35779027
    0x110304050a030311070905041e020d0506180f03131a0c0307031707080103020a14030f030c0601030201170f0c03041103070305160f0b0403030f0c0b010b1c18060e0109020402 76
    0x107010948854040000707400ba4441c04140b01e0883c1c1f01d01c0c1e0155800c030200a01182c5040007840700c01d04040700c103a074040300c40166440010340420505100c0c00d5801344074600034041405151410a42403628a41c541080c410207115480001c1c0340801c4405014805101013000c5000195510031492200c855020000e158001c0c19040f0303051320509482800b8240b0103548109048401002c00c1c0002135005480c00380c2042126a0341107030310002c03403009003a20f2181c160143c240349168005400038507030750040c00c010800d5607085042c080e481c880c04820000b141c902a004c50070401c0000300f00103d0075002002040c1440200300d2062401c0d04090120b6403615101d081907030351540d650f10410794131105031b01c0c0410044003190301c001c100c8034852040782c00c041c2160b406450046002c042030042211041c145008190103110850090103207103112035844510a00c860000c0c030506941c0c3d0105402c018041c0324060000701e22440054200d00b001443c1c00600d040c16026007150744002c1d40c031a00200c4c217 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 35781515 1250 35780265 35780267
    0x20303010b09042d06060f020604020307090c0e04090b0703060b0a120507110102070b060909120403080a031e0603110105160f08041e08070e0907060503091e01140a0b030d110304050a0303 82
    0x840d009403100d41e282d0030a447c3c0224403c0b070741d90804841c0250940c221315001c0010765500c0d0402184030301c03d410b001d10404103078404101102c9034840d080d6a0b18000c0000d0145d055003501c241c00260618040d25450a014080040c1c950100030b41a040300035034460006000520039107881d07000b141098000d5588a51508001305007107000e0b10103c0c462818000854845000040d0944400c0c0f00310500500300782c60340c0c5401c203590b0070010050b001d00d616400d001109a4038080c0c0d480d29613800090000d2001d00303609000d640d203103070442c0703813418000d0030081d400c080c0e9610004030070840d50005078240704048078602402203010b40c0d031252015401c2c0d040080040c00d40c0d1449402a250300d042154141591180c0c0300d85001025100c16a5980083c2c0701800018800c4004551220705070088440001c80e6014a240c00034102d0040b40c400d0750b4501907031810f408030a0406070441c0ea06c6009200301c0c0301400009032140b0743d4418000501c144994903011100c0103106843c01000000c1000c04da459170303820 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 35782765 1250 35781515 35781521
    0x30a021c0203060610092102060a0801060f051305060904090602130305160308120a0209060301090203060f09010501120e010603020306070e010f05030f01030206070609060504080c0706020303010b09042d 89
    0x604a2281c01000c000a40600348000d05171060901581c440e00c00314034007021028011b01c00c4852011000121000700056110040108241003059450036580c1d07145c220014113080e03403142d9172403c11008001c1880820381c404000310913140c0440e11145e88292280c0007070020110440d00405640c0085030103418032080480358812240200140c1d00d0300824851903202c0c40401703010041c90130409004a14150031505107107644028008030051602e840000040c10a801c02d031720011116070000100100d6081c50003c600803201d00340e8450302554100800070f0154000e0550b0b6620840e920030415028041c250050001190050196191401c1514004141100d0501250b020407940100d8848040c410401c81c0d10500069500c14003507402d55081000d103501400080c2d820584450300344021480a11800707000d0f031321501c48142e4035084840e03140d040c502c0f258000f0055420900040100801000c04c50312142030460340000c810031400e805600400c00d151008004000c40501d54030400e4140c0c1c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 35784015 1250 35782765 35782819
    0x90604150f15021c0e060c07090c0f0e0904120c0f06021206030a030c0201080a020f03090606040c0504210f0b0c030702060a0504030e0d03030605060c070306050106031514030a02 78
    0x640b0494080c0b00c680080e40e50704042280091a01881a448208a0300c50069a950300400030300c841e01d06000700301d189240100b603400184645d982d800740101c910fa00a944000304005c00d01b000040c001c021000250900d074003d1001c0c0c50b401200a43c00300a51044a0054202da409400d0050200e110b0811034025007003040c24030714544144011580925000521050b420303450b41d54002003c8451780110f034034020143c4845c411390b809000c01c4840c0611100610302ca40143c600519852900008020550300c100800d007061000c108028049900182c62514075000c0004480780054040c1c80c1080030032405c500007408220040052005207003a5000440c0610900da007202c20b2511038420103030480c0e50a0798002d02145402144c0d00313035800c281d08840c9699019080c0003c100d541c5002041155101107c09546500407803030600801071030340318440c00741050385000c100d000d14400080501c845580654248280f51400946050740c08100706078100703501a1056001c9091440359243c22103400d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 35785265 1250 35784015 35784029
    0x203090705040e07030f03051c0e0717030423030706081503010c0e0d060f051501080a0203011202060705030c07090204150f120e010e06071809020414090604150f 71
    0x940d00060245003e00412444001283c040c04601c0e1035030756000401215071a04030207102c4180311111605880240100301c0d100b034440003003648107006440c1400d002d402d1f004048081000d00d0035020010340003041d101601e60040b0340000c1c0e031101b8448018400f40740391000c2e6040c0308910001c41c50703d5110340000d009a40c01c5400700c0a0082c00e4080600740d66140210708001400162041c03081e10300022082003043c043e0780c0c00551880c00041003425240c003200c8801d010101c041120b07040b0f59002c1150307580400310030021425541800706141250040c0c803c080c1c800d270b102056880c1800b40600803500700045660859220a40d518620b00194006104a8461003e42d001c0718002c5070103000043c0e26031b113050355981e2400701401143d80c0201551064075010351340e19890070f084240302b00f00003801603146894415050000c801501c06030051900b100050301d0040c0820801c6c0514840d0b01603888104665001a41d035038007000c2002090340d42c1c100040084008000205030300001d44030f5059600c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 35786515 1250 35785265 35785273
    0x3030306050909030703050711010507050d0201020415020303060a030206090a0b0412020f1c0312062d1d0601050a030f020a0c110109030201090506030403050f0703020d091203020d08060301180303020309 89
    0x740da0f00868690180001c00341c00700d80100042c0d400605401109120300405060003030600803079440f0701d4a0308502e801082c015030b600280500c00035450b10b46901101600d440118034514044000c10103400305448003c0c051240800c040d8060760725000c1c0d00d805451210704480e110782c0c6d1104d02014500d0b40d004264007407811001c00201606000c030b04518040c0181240070200c24182d5422070345011400d20f5074003c82e035107040101b0540c81021850f1b0101c1084140462115174032a066540310703000390f00c6140c040d010010140071000454603460307030040c03090801a0b101d0442c1101900075001d4101350a038131520000311891a16041508a00703164059541894041d02040040d02c0d00529408003038041240c1784820042481d02c6002158014481c3c40c0c0281007025401c031099644e08003a00443c0560800242a60a240d01107034201c001e082c40600b560a2440688002c0c0d1a5920b40c81c40c0e008001040e4000f400c04e89017500704d074015504242070500c149106050040003504181d40402031401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 35787765 1250 35786515 35786521
    0x3020a0603020301030b070c030210020a05180f0a03080a03090f0b0702010c030b060702120703060c05030a1406180601020c090112060608030403051207030314010f030203061f060318060204030303060509 89
    0xc860700c03c0d03134141d81e80900b5424654490a405807505500313440100d04610403002c20102c07200300c50029000000150300c40d55120010341001f01060b07c415a41e0f00e0165600c44bc05180c1503490041c5e5000301d035000300f901e5940d050745c29011006040100405040305454120100c1007088100b0340c24800e400300d5000300300076207400310103d0640c4d043c10500d0303612007410700c5248054500420070200f4158418119085c6540c0c03030366941c040c3d030030a440131004074a003c400c0081104c0c19002c1c09040301741c8510074155030715040c0002021484604500991848507900141299008100c0c000c0061001041c0d50060742c1e42e140340300c980c210140c004481c51401e10000261902000040d00d09582d4440041c0c015894039070303d0f2078240d0700484004d43c01c040d242c22170300307084214a0511501038210540b0742c1000d10f055006152910102500d603615844610440740312101c5003040308000d8401501c2d000c18950301e03607483d50384620010140030741303500d200040010415801d90701400c11628141d0322051940c1d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 35789015 1250 35787765 35787767
    0x1170106090501050d060906060503071713170903010516030c090e01050121050c0409050c270a0e130308070c030c170c0115030510090c030f02060f0c0703020a06 71
    0x40080c8a00008030346011418007480d030050014251104803d10005000781d40d03002c0381403e692540d848500415030020501140c0340d841180150100e000c07500c49102d40c2456030110380f40c4400303050090004100c06007040c01344100d140441c0d1078404c0081c000d101a04040d8a00d4441c1d04440c65241d02080c0340a0030b00c04801c2c007944048080340c02a40016025030b00e040c0c011b4440010348241c0f8001c000b001d140c1400b05100034407401d806551102c1c44a52034908041ca030108a901c060001141104140b00105c3c0681d0051500e4103004840500100c1c1616001c000c6003420449070891400402c440c010401010241d9424052080c025560528641c451003000d80d07821441030f40c040c00003090709041002080014107c40c40543d0310704556454242d1092216017151450070703035150520b448070740400c00d001c400c000d11020700070480d4040040b441640c2c0c0f4010b40000d5480000c02c09110321031303510250741d201426541210107045a6658030991010015281d5003a4001240304081d460360106400e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 35790265 1250 35789015 35789057
    0x130b09060a05060307140f0a05030703150f0e1c090810020306040c0305090303070809070f0b0a090b0a020c190f080d0807030c08010915031b0e0c0703020303160c08040303050901 78
    0xb18842e50b2624030344041d52042c41524080c15001d560230900e03d440001e080e840c1080340d43d0081d40640f1060704860707803c40e00b05064804e0381160903807403820712604003401c48020901000030a514a20304208405070700c0165941c0410782c1c0011b4150043c0300d4003850b44103c80d0002c0d481031208850070844007030800d60076012210190352005c0d09030b2050000480c0a03000e00383c00354022141800f180c2c102a0740b140403070303c006a03039000485524008102c466040750445017080260400e0340a05013050182c45c1d00950314012140054450f4808030410045015880f0342c0f18041e00d020707041c902019455441690340c0f408400d04000001c0c54040000d10050710070b00c10110700140300c0e511502c82d0303480c07c0402d030302501070702500040c0021590341c00400100c0b0020008a62140261080c160303515140f00150a0000103000001643c001c21156001a501108495110140150301c955020b80d6543c201d402580050004040702000603002c0203040e0081d000c1c0c12090400d0303031004d0700f42e00f6440c3c4a1080c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 35791372 1107 35790265 35790269
    0xd0f02060304030c020f0414060d110301020c0703020307080718090302010b0d0302060702070b210c0409020706090605070302070f020909031201030606030b0702031201050603130b09060a05060307 86
    0x318100071031842e1006d00125802c10285a0308035250300c24410040c40684682c5d00300c0031420402c5040b207460486000090021902c80c0d03e0840d42d555100361500040c0e20038820744a0015002d54002070840aa804124071800646060a80300c00a0200344000320159500da903155081a03d0304000c440500d4002d50041c00c441c10013541c00313828200c1c2e41d0410000342d4010130114450540d00301b0781d00c0b807070141100c10300391698810240e400d180c001d541000503090b000150700b10078046550851040a030107410104200d072030702007065003240b05807d002080788511181d103001614080c10f4032640920081c0560b4940400d480c0080345c4500309030800c513090741c1d46181c00c0c410300090503002603100728203000452618400b00e001d48282801403080c01e11a940020010740528440108148811f078400400d0300c05080810ba51512010121a9151024900000103600f40b0700040c3e0402 = true := by decide +kernel

theorem cover : BRFrame.Cov 35611515 35791372 := by
  have h0 := BRFrame.cov_init 35611515
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 35611515 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 35611515 ≤ n) (h2 : n < 35791372) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
