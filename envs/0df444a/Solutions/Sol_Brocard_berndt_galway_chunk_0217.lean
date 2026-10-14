-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0217
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:31:35.115881+00:00
-- url     : https://prove2.me/submissions/9c8e3b8a-09f6-4a89-99b0-a455e1f5b6b5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 38848925 ≤ n < 39028781 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 38850175 1250 38848925 38848933
    0x60c0801030c1a090103020903150709090605030303060a03080307050904020d02121e0105010c0305040305070608011a07030206130809030a050d031a09040f1a07020102030115050a0e060d06030605151002 89
    0x6070401c1c10702c21a00c00b20401c1c2400742e264012040041d0424038100030b88181440c162b020171140710745c400400025654031140403c845626071041c15039034002100c401d60014400d12040c0f020802c10301c007660f403100351440e0480c68880860081016600090703400c10b8050303004074940d05d0345d0752003010582c0d01440800a000c40000390a03880824003206110300c50610040c1c8060b0320034144281c00701d030082c40c0c020089940d03daa88503001003010800b48295100a8020546010344014000c1229400f5030994000c000c0ba844404c13505148141c0034604031010300c420005e45080e40c03414418100140e014501400342070080001c00781c16a50071b0108107400d0400280483d019540d034000483d0800e400c203405203030501e000c3c40c1c65082a403049010003804030304a820000303859415001141681c008482c0266009a020810f442c00e001c0e00c0303e100080b6180d100d4152041c04c4c9080980040c003400c5201141140d92900c5402c100e0303c00707461a1400d41260072025401382010400e803804000c040c4014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 38851425 1250 38850175 38850209
    0x70309020112181704140105040b0304150609150e0106030207020a0311030f03030405010b0f0a030809010c1104060303030617060106020a15150e06150c03090f030109060c0801030c 79
    0x300842001c402c144040b554a01c602942c01203140c00c5807411590007660400c90300400b108000c80d5410030b110f20442581c2403900d840722941b05000303880454400401c0f03941503441d5551050806485030700400d10b17007590350030005000c0585025020b1105200b50348007480608009168104c0d8005800207428540108503110058403890b42541c201d94006403070660b59906a8002403c004620301480a14071003c170a00c418058191710580000004807150100903206400780071180e406032101415641060090300041d502450034034044038814103074560780d84004800607007215480d402c15000130369100000e1120149401ca0070880c20b1380c060081290358913200f00250354070f400c082c00074401858541c44041e4040344d0b404c0784071503000340d04010a030561038a14403074210b60300701c034641e1142d9981c030511484510b1540440e08404001005103250007a0342c4184194014401e980580640d6900181c4c000b090700b9101d0034012072102e591703542003540346081481541d00984c215421001d1030340b0003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 38852675 1250 38851425 38851427
    0xd02180703050603010605010e0f060d091b050103090c030303090507090507030b0922031805030106140112050f13030212030f070f03020309211204081b0a0803060d08130807030b0703090201 83
    0x640c03278075282e00b22031000c40d00744005c0c080792541c02140140064582446101000c210703646003021046006594400c0c802642d500044080c2d94a012004d04502461201072003c03a100b50069400140120f0440381303100d0344c403029142104c0c0c045032030354002070fa544d1084115140513161940c000d6140360b402040303206002d20701d04080c0707072003c4020144400c028800510760702c020f8100c401828001c000700311103036659030052540120300c000d81d40003404401000b04071420030b1048070b00520744100321b18070590b20402500304042c286241602944a005091807240c0051801036210301480e05160b2a1800c1c034541c09060789602040c0c0c003051500601c104a000d810000d041e014504044e44450001120011032000c14840d14003959100601c100400c4203222141c001461450300c61107030080308100050703490b500d07401d44c20b03002003502c281000410100d26054021800c014040e4040d14500140840401459046c95128500c1d035001500c04000f440b190a020035840400317418180702140c40c50780 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 38853925 1250 38852675 38852687
    0x10509150a02070305030403080901080a2a0201020c0a14070f1d0402060c011418010b06090607030521010602100509030702010c110d030503011503060503030a0e0d0218070305060301060501 83
    0x10403440e0580c408035800205500c2048204025904101520f035560b031282840200c0c0da21180080d4003152400c400b09001e1504e520074062003c4c1d190a0740d90380071001c440c0b0400c20f10711403e01d840c00c6640074000e401d0030100c1880003280c260304c208110038490414001c502c1c14200c055000088102020310200a03000081418540f5101d501c0281840d9a465100151150042f4080710540c4d61901241d02281c4014200040c0a9140500344810801d0420031250030b8500c50020160404801d003d06030302820b0401c0a401400c0c800d0900c5410400d6902096a5412884480709503e400d000010001c00b5014402090308001540c0280300625108501942e41c0c03180d400002e04200c1c8102d800c5d01400351401c0790044c0900e00410343d0703e144002d8100280550000c0c080c0040c0b44440d500d801400a0103481a1000c491018000d14208000303041d068610345080202180c002603201c207040e0050fa505403000046024181c0280b201e420184402400c845000300300ea40260f240060901a0340c4c0c00c06 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 38855175 1250 38853925 38853949
    0x3020316080409020705030315040614040f02041d2409010b090307090e010e0c0d0c0323010507030203090c030705030705040f0b04020f0a020d090f090902010c0515060a05010509 78
    0x300040e40682000d00d800380a42c800c0e54080c8030700b01c0c03000c145030080040200c0114018419110f00714060200c80007000301301d41183c0715451481403c0403d10002e1700f0300303400580751a44692001810b0a40d5000c007214100100f100068404015000f0003208901c680c000d00e1410101c41e460210103c0c091000c07900c82d01c818042c0082111323010409090b15501000550007600071400280003400c0d0031105e05000e0300c0590100c0c2014010826a40781504203810040800da8000000e075103030610710b41702e00740300c41c101e44000c4002c10710703400050702c4911090051902488043c1d400603039130b140c601002c0c0d080c2414140c0c861300c41d41104000300110b540000303040701502d400700c030001154400c84c0030a200521541d14030342e420034008980710303040030910400303043d04200b15020382c0c210790a0002c084070000d00c1805204c42031201c0e80f030240000041507108001480c07060421854011090321102d14003070504d03a000401603456401c011050810b240a600109000e007401810151080c0c00906440840 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 38856425 1250 38855175 38855197
    0x606070206070510060303020105090d03022a030f04060509010801080613031110050c041a03010b0f0d0915050901060609080604020f0103060b0309010c020c0a052d060408030d0c0804030203 83
    0x400e40005100d020702265200d00041d02c805c1100f10b603a8030b0040c1c003800c030071500c0045901a1000d0302c9816402030085500303460a443c86400010000032980300c3d1400382e444d002c07019120510003a201101c0e408000c10140150340c0341c00303843e40c18190004140010503041907401d604000c041c000f1405041441005541c1c2c181030403800302d54040344061620180e003140106450404042c00a010840300040c015100c40c61250114405441524420341c0300030b11640d56102400c00c6000c00460308007020307140b685581c5a021400c00040d48440c407800791801d032092003965481041c8040860709100b10f0000300014140407030414130306074006441d00001030003e0300402c00002444056882030f80244017a100030000d00f07841e0706061040d18001c00003031500c00098407500b90300310501d00c2c0910740d220031200c3c024041c00905c2050030341503a8820740d101c035954000140a130740c442503580b00c0015002a00c0600000c1d80c031054408040020741e1182c0c4440d4061115100a100101340d0110071101c4a18135 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 38857675 1250 38856425 38856427
    0x408060a2a080405010f050f071107030803010618080c010e01031a040501030b040606080a020d022e020a0308010e04030c08071e060207020405100602060a1802040615080f0606070206 80
    0x61030000c01110701416104480c1c81d600d0807906601e60005001406180a00020031a80c54103020001c1103400a6515103514150340c0c0004040e6842100c2040058a204007903800303450380c039513a602594000fa000500402c0d0701d0a040c904074a04185598000e10006008100c4454000000b07401c5015030800241011780b100d00c2070071110680781801c001b00b000500200955a5a414200b16554090342c048601900b00340000031980ca0014410102940003001c000000106500300075088607401c80702004916440015038220783c180c00b0012600b900c540140036504d1b150700e0003e00c0b11405800c56034584080f04140808a41d01040803800d96902402c019a19105070500c40d07c00003480407000c510161085182d4104151500980380291094400b48a640c4404080c40c01d403041ca0b0107409c0c01a88580300061020701c20750492034640c2c80d1415500301d4540c1503004034007600c0c2580c01a400b46a00e0000841003268003035421580300d144884500f0f66400d210000400904c281000030b842108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 38858925 1250 38857675 38857691
    0x50106090b130503030c0606120601060806010503041109010305061608090d0e010203040306020304230d021f110c070305190c030f060f02160302060109090803040b180a03030e0c0103020408060a 85
    0x40d054030b4405410014100c0c0d840f42211460169148400c0324500c0c02a6a108544480900000b4015040e6006a110000140d94510045070607400040c0f003a110701002034204800717500c3c1d4032a4140a180100050013091401d0a85500715180208600c0e08000c218410030960480110b000140e030901403401c0c1031200c2c4001c004074594045c0e900040e103a075100209010030014000f202e450404141c8640c801d440f01c0010760980c64106500d21000560444925140342503003145903940b0450720144006002e4a040f6803103101c0e60400041034000364804002402070040410124103e0601d60201090140701a034030a0480c440d10310004008001400c0002c04024941d000004030101000c4115242d02040c91440040d5042203000d83c0035000c0c2c0400401d886007e80507021b036042d0003018092440e1240c0e42c1741000304100031b0480b081c018048400c160241010300140080b64080da401042508185110b01e050011085030f06041c1441003104004400000c6003996010058210015071f0030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 38860175 1250 38858925 38858947
    0x807021801060e01021002030105010c0b0402060d0f0203040c0f050303040b03100e04051f05060622170a0506060a0302130216080d0f050a050c0301031e02060a0c15050106090b 77
    0x1401010158920100210000c07844a0388680110f412010036801c07100b402d1480f0b49202d040348030a000d22800241c0118000000c40c090141ca541c10501c05001146450410101c2c8812076607c6c014005241d82c00009102c1070024030b8120a018281800c40c490400d03160800190b0f5a1086114991001c540400014070240040e1030210041c00440000c402c585020319107183c07206030491400075050914800c14206042c0b40c89003034498030010f840d851800c036102512803481504802810810b0080080200f101e2021483d0820b0034203060005018882052034406c0c04e2903002040d0314062186901e003080540e403020340c0030300c2e2140d10190041c0d55000d042d025440e6881034041c0544040350004110040c5070050380001b4022403e081c1c01c0090391a841c00c0d10003a40c1d003c0d1040f1044810500c010300111b125070080380340c0c00d601d50340c0c1108560140e60226540e500700c1c00807000030907071001e0740c9000d01c200c0c1a0a40c180c00303102e600030840741d0706011003d0540002402940883e110100d00e94801e1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 38861425 1250 38860175 38860189
    0x108032502030a08040905150604060509030712061d0303040203030906030703092102010f0209030304030308100e0901050105010905011110050c1308030310050d1109220b04030e01020d080103080702 87
    0x200381c0141c191400c01e226130030140d04c154845c6c0700780b031402450031000608032140241c01c1c01c0d9090000b80741600d03151401c00115541d80003a0130060b8140200314001844100a8005489031807041c5e0b030110b10200d01d00001502062101543d0145810070000c0200503580402200c0b0740c4801100e04a0703c2e6282c00808078000c00055400600d0b07070f04802c0c5200d20345030200d080d560350803d29500038171203020b10040080030b030b02510101c140c040c0c1c01404148006401414000d03844a2f00e250702c0c3c05450341d5541400610401500d461480b03035503810050105580c045110009000c1c20708014045082c40c103002075030340003214910901d4603a600082142495880102e039011804242942801910b03030a805460341c2c015031315405400c0c3c0c9440e0001d502d050a07036111018540100740b40109203840c409008211b100100780311f101d03a000c000101442c06001d64184252030003080c102c0c0940c074003860080e01c00350484000a055501201c2d0200320750740e1000820f41900d5003c0380711511074905101007560 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 38862675 1250 38861425 38861497
    0x5070f0606090e1005060a0303020c13020f030109020409060614030a1a030f0c030d080105090a0f0f06030503180609030c0609060c0d0f0f05030f01060e010c0b100f0806010803 77
    0x8900d0801440810f90180010f01ca02c00c1107000d00700b0170032078985d042006006001c1d4800180036030802940c0344a946001410500c81289818001d450641d40d01017003401540240c100103040c0303502082c00d00c29204541700e1103001d0800d81c1007100c88031039181003c8190340070081c80406640e44032140c1020006401120419002c805012616290010103400fa10380c0a042140740c020310545000c03034120b6100c1c24846040f298045c0603040c0988880103a81c0c0a41004c40090a0702922035074001d1040107188030f00c40c02140194082c50f00c0f00500500c200a04002c000707002d10844060103051003507900030641c06040300d011148240e44840042c0401c85d0750249820b01c0742940600d04101c0b1708250031203800c210110050b9140c40740d51410120a0300c49000646240d0441d00600c0014042c1c6030051120840a0105050120b03460702140d541c021141c1c822136090920682c01c5404000400208480c10080c007590780282000e58104610250b403805410f05040345100758502e150b0034040c411100c01380d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 38863925 1250 38862675 38862689
    0x90b010315060909150b090d050f060106050403050d0201060503030d0b030a021305040203070801090803040b070210050c19020f0604030c0804080106060804110409120e0402370f05070f0606 83
    0x1c1c0d01e54038540038003c60120f00c9200c15a0b410f00364a000c003d9101c0b41801c040d9443c200340ba5081113444000e220900118030011a03082c403070b64016400a2004001c01802401103a490990b01c900303520f03049081081108424041d60704006041c4032654000c02900e410b1050102d00040900000000902e441c00311003000c5c1d080008282d400b0700c0c07a151604158400ca0080c1d00f11121142d17604180c908888902c90042c5c0940310034004100062200410365411160354411181c07610452007044c001c8030740c02d48803c0305c0001c000408215114084e001260008424009801001c10b100d002646a600050004040050303823101c1404000241050304d02800c1075100800506450300d0018148003c16141607407061030380389500e82180b406014440d080c0da03000300d40c0b26a4034045e5500762440090085100d900036024000e510b1170088006040030003a40ba81c18204082c00c405000700c040d071240c580c0ba581008106040d02020b079400c00c045903681e561008414611944d103041c003e000b480c660304050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 38865175 1250 38863925 38863961
    0x102040e04080904050c1204020d140303070306060932010504030c030507050103050c1c0b0402210619150f051201030302160b040501140304020d050f071707060801090b0103 76
    0x1040c80301910240080c03001c1907a080045407600202d0f804580661007610300f40410f9131f00001e005003002c0c40c03060000ca20620075800c214049185003800c540084170b012001a0351010100903075039004500d1402840104080b0403144081d02000ca49110410001898907010350b0000c081070740b1540894000b1508000380c0301d01c00362207240194032001288070f03ca00007420280401c4003850f01001f16581c03192003c00008005110b003c2d10800790100d0442d2581c41a8240303c0084880907400203080c00c89201440740b0745a10308602000781d40002440181c10318410600700344540c000701812245c02c910b043c00c15040040e40d59004541c54804c484042c12500c18403400001015000510100300002e01400c607170b50301d0389079030070100b00e40161320441d800120354940c90224901120011134000c0d00103040d05199815a440d0a0b107400c81c804000c40c1c40d54001c460401c112140118201003040c40c20019168881c6001001084442c060081d003182996501c903a0013641c2c0282d21500f141c00c0307441d56031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 38866425 1250 38865175 38865181
    0xa0b0a0b07061a0a03120207090204051806040902120a03080f06060702190f1401110a05070915030c0803040501080703020a021b040207062d110a030902030f01020d0504150e07030201030e0102040e 86
    0x107040516810401e1b81c016115104011408058a0085c1c42c182c51018100300c460090345021140c54803030182a403a00503588015400150f12002d00ca4206003220200424030100a4500188004401414501001c00800504c44130340e840c001150f10054044444056500c582c00d0040c4980c4500d920001460500c51000070304031412819040698070241c80703410780d210203641620380300c43c180d440c020f0258100c52418003c0c41c0031a4820504411200c035400a2140c40766105184001341f030300405205d50012400700076541c1e101811680c003400a180550030b0414400000c0c2da290341a40b40840c800000c03101104460300d4a40c10f5803c05904032905101550068450305042462a0048402503000c07800b06030040000340113a1940004030384610f8900550520210010502468201ea041c0030342c020300c80c00c2101c240047d00301620300290014181c1401e00e030101130385000d4120b0841840c02d00500c001010ba006c035920013240d80a081c00f1a54000f0060310f03034024820340d001460103240c11014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 38867675 1250 38866425 38866433
    0x50603041a13020915090103080c07180e010b0111030a050307170f040201020c0301020a0914030a0209152409101b03020c031501050a060c050106050d0b0a0b0a0b07061a0a03 76
    0x90500b1030b0090303e203004691107401400a4401d0900c6500c1c2d04003d01e54010000103000070020701c3c01120f0b4006a17440c0945401400c10603210000a1460241d210381030600c4410081c422084610002d080080580039401111030f180d011b800c241e003080c048048002402c01e03000788003902017a0840881001b0a140c070703408902504605913404d038010b10800340b0340d41c024141442112000803040e10740082c82841e145110909101c0b0203002500360049480120044e02c03500542c60161681c90fa062406003445d4050010012608052140480192400c40310075103c4d501150050181a10038141641c003510f4203a450815031440030740001201c02c485020703d50b000c10b240000a2048060711000c4031212541c503a83c4200380155544072069204c1084046e00034078414841f14401c400200b980ea588100240c80408684026034040079044200003070003d0310b00c14415004c1c0304440c010915800c1000c046298000d080000b818507541d0340103408060031304480040b03032007001019102031584900d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 38868925 1250 38867675 38867701
    0x809041d06010e09100509120304050304090b0307050a120204090c06020a051c140706060807170f010c05030105060d020904020706020c06100b1215030d05040f080313050603041a 78
    0x2a10a10740903401c00840d036125005000390050b00244003c0a8011010301c42c0c200501d0090000002d510452440c0403080065a020714482c6000380c0c0619100c038a00801c40f01a9090102c005203e40c02185081c44550349005601c4295801e004c4441c0d81c410451001c9002880700d840040c2288611850005000703500050707101801d4411400c0d2000605081d062070303081134000403c0c0e00800c0e845528111003001c0e071005405900d0103050080340315550340441e2410010036030807140d845444004180c0c211001040422051200c2b00c00030000e021110318002c0c02030006020f02445410001588602404550140c8806042c010011940c81c00c4904e048d03402544820b4141c60280501400151005440f21404c0d04441c540d00e44c0900d48102902c1902541000518400043c030002c0c094014a8604010b0146d070407950b5120159a03500f00b000d030010383c582c81d03440502e03103510811000460460014422003103904c2a90b407280c9075195072a0002d074a610088900600101d4076040105c40b0180350 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 38870175 1250 38868925 38868971
    0x1011010e100f0f0b100e0112090b06120a11060a031e0c08010509041a0402040609050f10080c011b03090503030f09090a020708090d03090f1e06020607020a0609080904 73
    0x1182c1005403200c0044240c1c1610038000b800c66003e001d4060203010301740261540400b218051500542000880040c0c00496404100564140144908100882c202035a400c03940d16458001007507403a0040c0e4445000440b42e03180e0038005c5501142004c1300302e000b50041080c2d0100c0407400d40e0049144d06911004040800078540028098000041e003030400c1c181c0103018940113401e5101c4400306010362409081d0113441260010358803c00050b103547c5600c500ca0043c1c0c0703545000665410940c45c40014140035400c00300c22034000d100c0010b801d0f07070090072403c20300815142070200300c07450342000e40300403c2a601007501400002102d0200b0314640c00206504d05085a505400751035201c4110124040c1c1700000301203074403c0092005520b085221121218464540400026112141e00c0b14108141e4840c94072901040729080c850100d1520342c001404842c4000c2001307180150000b9aa20320442025200558401104041c0505031048868540000d0000c2c42030421584411890175915 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 38871425 1250 38870175 38870201
    0x606030c01090e070806011b03030207021513030209060d060c02030304050d050708040b0c16060c06050a0b060301030f060605040203040327050120030c0604030206061e1011010e10 79
    0x403440c2030326507004007400c800340c5074501008400c569032903100380d48100b000352016060280d1040c0c0240004d0030303110a01005840f036680543c40380d160748184506106005d03a0005080020b02c003417405907c400c1103601c1101d03011100d911041d251032000c0350741074440c2d000140900303041c402071942e580d4002001b540258416011225007800e0b0707000488070382c080e000004040c0720782000200a02c500c5180900006014402a1000171500c1404807110720090b0b1b0110010481d101c224806222281c4103843c0e1084210303106219400407400001c010b480705000c01072000c2e040320030a10a00c02035500c144040d0101410465032070900b418080d0180b110b0b9010100d9482101040708100080b01c0f00c403604403081a11071941c02d089220140c000c014015031504401d11050180311382c50b1108000050285001750050941e604040c418018034600d0341d58250100201d0040d5560952103890101005194a00e803295100030551917290140051080c004c40034801c86e0070040410911303030f009008022403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 38872675 1250 38871425 38871433
    0x10204090504021507030e0d11121e01020f0307030c1e050403020a061814030f01050c090406050105040e04121709010624140c15100305100209030d0c05031902060603 73
    0x21140344ca40d0548602c130001030000d0400a00d03103c4500306110b06a848502c903814901c58000342d9004101e40480c0b00014100c00d0384a0305401c0d0360115060215502c43e41110002d5181150034088505280f002916110416940360410302c01d96129903c104003004510400b402007203628a4001c001d60042c3c003090741b0230304090400041d501d00840030036500c80180c840d4450000c1c0340034502804601130710440c50300360080e1201c0c8403c4107400e00c40c0034890001a00d41988445110040c0411503c1079002a0706002c0304000a0194400304010035921517441040d102280403b08001c55144103101c0080341e84c00700c10018803022080640000060701d00c80802000052207014445810484141c0003202083c00000007040c2c1c046078900a01ba4802c1080c00c507601d00c0910071840d90440741c215003800340d081c035a41090042010600504964189000c001d43c01e00700d4003000282c80341d401c21601005d00054a541c40200403040c800d80d0881d0001661044212440113806503d80e10100d401d2403181c00303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 38873925 1250 38872675 38872699
    0x1503050c1009050d12050c0f011e0b03070b160b0103060c020609010501060f0809070803070510060906050a05040207021201020a0306050a08030f0a1d0604030c030b0a0b0303030a0c05070501020409050402 89
    0x40710342ca120045440062401d20907842c2034941c00081c24151a5010811100300714030324152404008000c01c0c40040000011600942000010310500c0304070095140ca04014040c011550002240401d80b002244155500c03940c9540d40120003200d144005d00a5402100000a00c01c09074401132480c0401c0d000d644050391411461801c8907424003484012a881960101c0014401c00b00150b0140113501111002900c5031348003031640e0081e141c12111640090741213200701c2403601559000b00313403241b000d214103824200012325696540c0600c3c3e000b07580c0800e84100707643e26484080008245003000310b650b1541c8440082c0544028012a4010051074100080402c4004100c0e404160401038240c20b006614000312846003486041540d9442403400419503580e40f000208015445104c0380b1040900e5454080c00d6044001c0050144c40e1908605c00001e407008030440e9070001805d000080c103800034802c00d035458000c041002e8019840454041883c2c0030540c0071502541c003c13036135445035403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 38875175 1250 38873925 38873927
    0x15010b030106030e0a051b0103020d090804050a1413180c030606091a150307090315020d050f040c0b0901020a1703060f03030c0c0f0d0b070e0901090905060105090601031503050c10 79
    0x85c19004000c205500041c079044c1009154074080780031380b10526000d032a240204a0107010790b9900d000036601104e0001c1d00300b295140c00c80e002e00c02000d4081407281034909040c0000d400d948411080c02c6034540b946440000302041100214070998001110380c011512030911000520142c02250902440c10300e01028440305c506403055112401025403009015075540c80046410180500c0180906d105002c0001150b40c2e00c1c00128808130280180c94802d0448148140c400150a0340b1004502c001404041036501c511032003692210302c152607803000325100407840c0c4a0900300103481600c02407107070f15142078600001c50254400b100d40407075090800c0b08040d00c84c4541000901c842e4001081c0d0007850518489441e40303001c00174800040c0c589140c4a081d440c070821039052000403a502c001c0d192520700007451901409040d40100700f089200e6a134150303101010300a082c401d0444200080386a071003a041548100701030710300d0500c0e003643d1707180c15070382d80d000802d2181c0b180c00c076600e8130f144031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 38876425 1250 38875175 38875183
    0x90604020411090d08070807020603040f0b060103060501200709060909050d0f05030406200c06041a01350307080a080606031006030903031d0a05070909051203070215010b030106030e 80
    0xf4490040c030400c900c03d0070f070752505a280d10862088416a0041c0845000350303882c44055441070f4001c07002c59410038034520f080046450010a1103040c03600e022803d00c49641d101e821841000c081c00a07060f01403413641c1105140040d207901c881d606174200000401d44001c103800906034640300e502184c04100d441d0200b55082c104078001d80002550500000e008268540c120b00015150b4180010030301901204443c1990b10496405070107510070000e1004004802d42000c0d40072500c0c80301000c103541400070000c000306038600c201ea802d8880a840c0000301c07020501444080210030300701d9a4810759482c04c000e850b0030080c01e26010881d500e002901908040007164450131003070300040d04080c00e03c4020f40040071220390682c20141d50745a8524124883d100a454440c081c10080642d00c4848ca0036515000c0d0320782006a44038100380041000400c002448a00040380a00c503640780e6032106000ca140c0039805032480c007005400310000502c0c400144c010b605865181da002d115241c0f8200390540c3d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 38877675 1250 38876425 38876437
    0xf11040501111912090306060906140a0302010f03020901170709030b010905090a0602180a08030c0709090c120f0b01031a0106030207030212090105070b0109020d0b030f0705060d02070b090604020411 87
    0x240c4a01c843c03160000f0580444801da0121905203090041e4903074913644101c4100740c2001c528103590791000d001c03c0b2003103440c42008030001c48503007992905650000703050a1b4020b01d5003080c0b40e000310b00e07010641c0c0214184c0014020241c15980a0b2a140200038142d98452105030380500c18140082241c459501410703105010420081c070342c99545907036000c000d47c040440c03200c04400140110243d584c3d081100703402801810000c41c1c6628046640b00d0a010f132a0f84811074040c98142e5040000383c0b0400c41c1000c8922400b83c0c40000c00c2a41407030a104007483c6002400603281030004010807040c01e81c6c2044041d141410060340d44c3c2c0b02c80041c0c0407071240c0761011f000350788443c0c0021034800004009018902042c901182804800d69070342030461000c0e00403419031034012401c880d031449580b10321181071504600406010701803425864a550190151901034240099001918415901100e44543d03026440142342c5c41c0c80c0340302c030303031210420380e01244228242031640039214520416119 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 38878925 1250 38877675 38877703
    0x20f03060c0406260a060302040b0a06140d0209120d030506010c0510051b070303020c0c040204120b0402030c0607060506090f0912090a030501090b0a0e0105071202030405010f1104050111 82
    0x403800c3d04104056408242800725081e00d01040107902c0064031410000d40e0142c000b61501084c503d00b140704120036a0451a5002d001d81150039007002415071204c590350126803120700a60382d4161584140e006803240c1d00c1100c0c0c22034420704880c507100c0030000e00120341e00955a02005680c0b80c2c24011601010514070251080d80543c442508a074401c0c1e010307d4125241d0f10408504e0001c58803881c0040d0801c060a8011990106182207034510500800c40854411030702180b4060a0002c00c0084590551001e0306022040300000d0440d103080010400f045401000c1907115a500c0c07901c0d901a103801c0b162140110020b0011509140e000110750780201c4c803850241130803500c544d15001568009229195205483e07000000c0818020310844c4043c60041000300d0841c0b0f004000202030700d15421160700b02c0d81c54002001a11903000400c4a0207202130140540e0303d403210b04145014180061074404000e1030f000c1070002c5814400001c104648080c0c07554101902e04000e5030743c44144d1003130020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 38880175 1250 38878925 38878927
    0x111c14060606030c16020306010602160f0302060703210f050402010e040b1003150302060d06080d0c020d02040c0c05010507080717130305030402060d020a0306050a0803031003110301020403020d0f020f03060c 91
    0xd0a010035680117002544c02900c8901080800c0e600001d18000082c0d0000d005a00280c201e40c8441100300b6000000d0302c81c2c42e05c1c240c001c0d4515030103e03002d4410030201804003e244a000780c0114a4840f500202c0c00c403803001030106501070703035604008113004e5400f00c0c0402c03c40005045a81007071300482d1407800e80100114450b4804010a502070701051882c02c2101144190120042e9103142c040c4c5000b10040400180443c1015001850854240025000c0c00180124800160f0342e41e151011102c0c0c0c1514003043e00704a0f5001a164082c100600510039402e0904001407294446e0f0324074401c0c00c141d42c40380031403015160031194890051fa032000c3d80d03040c0400d01d1000310b80900e004540262000c1c03d0395282c05201c100445c100d8204800c20b10000ba00c51204010758035089050304090f02c4800051071460400365007000751410503220041039880100003e0490755020345c151001141c01a24441001d042071408041c80406200224400c0e00d18180002040c2400181c1c9441110442215 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 38881425 1250 38880175 38880181
    0x9010903090e060609060f03060301050622150909050105090c010e030a02100c0813050306010605030f061201020c0115090501151b1b0e18030f090409111c1406060603 73
    0x48495110003090f5a40000c001c10040c01c142d00d0728401844840417a4540036101c1c10074074101425214064503440c4070b00501051919411001d1009030f41480205d030300001e610003000d2804500360700304c1d40b011070b40528203005001801011340100d4803a411740004ea03600110321000540b11804076021640c4c140c1e004181250041c1000c5900f043c1d494490304080000c1e9881d6520400790b5030201c0c0142d4030400708442d0400c160300741000020f016104d503052560540c9007034543c407442540c7c0201040e2055440c20000c40718400294122202200c01c000203022148408030382c075202c0c103020700c60990124500f9000003000f45141c070444940310240d40e90f2486255800b13980d01c92023442008151004003031510304404c140491740d0000c00400391400b440074145040601680c0c0c054007410809a0703500700f0043c00042d110310030222504800d003202c001414182600308030301d8120100411a8100ea10304034200c42054580900d5842c042c8a0901006074003101d125160f1980029919940c00050038004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 38882675 1250 38881425 38881439
    0x1e1a01150c020f0603130b060603040f030c14072601020f19111005090c010c02030c0d03030e010e0610080a0c05040b0301090c0303030b032406060304081e120901090309 74
    0x110706070150004005441c0c016543d400502a03600a80341403100e4028000c4000801030003a03621a44003600703c82581c00c61406071070799102a0482000103041084100c0039000704090080000c15a410b020204c9400603200c1100001611a80e4441c2c1d03a001043c0580d000040c00500854203428514081207007000c94011a43d018240341c110400180443c40345404c0407194208540340c46861206030201c1d450030090352050900c1c06e6034001a040008180441c00980c42c0090007114841d0141c8180a82078400d0500f1401000a141032031565401e18004420300800080d0050051040741c2c42c0d018465561400603668501c0f04000070300318440741608020516099005d40303e040409400401c801c00983d680d084400001d82045011075603139031404806080c20800980b0110703150141c0d048444228130110b41c00a0010880c038440c50700000010100005401070715030782c4150407031180710005081000b52903034001c8a8450310411a84c1d0000762035030014007030481101e425456810b011414405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 38883925 1250 38882675 38882687
    0x24050307032607110f0105131a07080408060f010f14040b0103090212010507030501050a0501020c130219050a0201200a11010209060703030203010807060c051e0106031e1a0115 77
    0x54002c2d2142a465680c41510805000b031000c0e501c5042043c81c003c10010400c1800320040c0350444c1009401d00080c4202e0644186900a8031142200242422050041040c0910545400528a1001140002c1c4103d00020200c0c000e03a1031700c0a810382a03032604c0180c01c040c00307684075804070f59a407055076044c1c41c1070a5100c00300a500601d00490349244c25004980c0d45007205001100f070b1f030341d01c804100d8080d905201d02405440c003100c050051300d1400f40004c5d0b841000d04051403040e540034500d05054285541181c215070945c2e01341115880c90300d04050010b0b0007418111001d9400c00d2115454020030080c1d440150800444c2e040c01e000303181e50100c540c64100380d42e41c41e280d0f60070080c0207030a41d503410140503414481d98015a982d030510141500f4150190311503401e008808200c4400520046101507411031b400c14a0414070807003803c81070240c030480d803001c0c1c02d20b00b00c0c07181c80e07282494601e1208480d038016401c082c008414001b8001c0d89801c02d2040300c2019003c40d07a0607102d184965 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 38885175 1250 38883925 38883953
    0x7030c03020c1e01020c01020102130608100509040302031b1c180e01080a030905040902100503040602120c03091c120908040902030a060501020706080c0702060304050f060702012405030703 83
    0x441203921400074040450340045541d082040c0701e26030342d5191030f169a4104569074a60340288003e508000b020400c040b0310480314000c120a02604030002020200b042c0208401040010180000c40c20142070181d16584014407081c0143c0440038801451500043c107905921261032100c5691403001c1c000329281101100c05400c4440c00e14000190708015205081c041c000345c4014181030758052401610001c50341e8000c0303008a00700180703c00543c2d80c087d00c04e40b08014604002d03607280d40b90f10b0f1940c02807045080c15591072912400b40480d80284002961080d04210211070901c01c5c46528071b1075a4401030a800000f485900504000a1880d0448020b2501c84c0031043e04090702c032400c550030381c1c0040f10b00307101555442504002c1503070304108a000401d000d0400c84020b0074203079440c5925203d00351010703020f2880040414200002000300c10902c4120741305072803140c1400800207000c3e100d000003807428500d2840080103101040c803040340885100074001c00401e40381d941c661038051411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 38886425 1250 38885175 38885177
    0x10050a05040b12010606090501090e0f01140a080d0c060f090f06020d020c120c01050c0a020a06020703050c030a0314160210050601020c130905100203044205060301060510020307030c03 81
    0x90303c1e2010690b02c01d0182e600a0191070703c51103000c0781400001022000a903200800304000c0d242880100000750f64060b0650744c0c0402d180c40c5039643c07200410002126640a4140e911501060594481e4495900e2129500c20f90060240c0e460220300da10a843c004400503011040e50111782c0d001540c1503004081901e07440201500f0105101c0c01541001e0b190303406000407400029500c0180380081c4030b21036008918030340090074001511802542d5900caa180149031580c0041d1250901d80a503061310440790181080700d17aa4010a0001806440c0e1503040700803c2c48901c000c80d0051030440d8601038032900c16070003894186051801640500000341926041d80a910480d40568032179010612608114581c04162100d140c0341541c41c14900b00c81203079a0910500501002481b012144035281388100b020300c10710184038946604000140504c42500d00740081d401c012042140c101a101e454114020009242d817202480f5040301e056401c1401608100805030019008c2c59981045a001e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 38887675 1250 38886425 38886439
    0x80c0a0f0b120711030c01020d1508071a19120605010f050d0f020d0903050304050c01020105070c020105030a0e010515090903070f12030e01020a03050405060612030d0b01121803020610050a05040b 86
    0xc04e01040e0650380b103000c907090700b079400182184003110310340a548990795107100450070051402d10076645880090041020070785072807002c5682040010240c48511005003007424021440c514090325156140315100c907540d060080000e815800f03212040031004954840500d00701640c0003442c014a94101c800342c01e5a4240000c403003161452295a160b24440c0e02c0c1d481c1c1e241005c0c204546040701010640341168104000c22003011707440813444000d01d90a0034100c0c2c0f2038a030055464041c00a65554042d990719000405c08243c501440c100d09560050b180100c0e19250040f80507207030300c00c2810203048200000241000941c40142d041040702c50380c600003c2c034904040707409007a640f08215a40c0000e07180c9040c0000d00405101c0070350421320488954200e6141c00780c1858481c0908840e0f407603010760b550400f1480c1d0b4012058402d2204461404110240c10340c00a6245880803110950045c0715810000c1d0000c068210b1740300070795500401680c0302610705820000a4480070b0045908030320 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 38888925 1250 38887675 38887697
    0x106030207170a030606120606141b060c0d0c030e030306150403170706050601021b01030e01060e01080a0507050a1206020702040f050411090a1509090206070507080c0a0f0b1207 78
    0x2000600f02404103075038082042450200020418003e1175110341e0b840746031881c20030616400400c882c4c3c141082d2030b03000d9207583d0705460100c10304110025098442c001c42e01040300002022000f004c1040c18284200409040c0200c00c50840304090504005075008001107071980c9030403030030b0700550480e0070220762030a912655400741d040c00d07a100c00c8800490215014041000314020680c0c460360038402400a54001140740d041c40070070a685038149951104041800603080d0003100c00b400e16a10b00c0c074501d5a555003c0381d500c05035900c2c2a1850b01440502140502d80320314203800b1107008425039603090880380c5494009500c500350403030303100369160070300f0381c40349007600030240300e2402a0107244040921b64288404403100800a4040341c2c0382c10428006910000e9100d03007614050440041e1801251022039442c0c41464000341c800c2c825280c2c001800361001a074211328403800e43c2e0040c0b1881e0394035455480b0010f1030007456601e6500f40003100f14084c085400750b50201d198581040d01e14 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 38890175 1250 38888925 38888963
    0x601050d061b08010302040f0209060306090405070909051005100515030903090a03030e030d0305060d0b06180c0706150b18030c0415030308060901030b012303010f050601021005040305030106030207 87
    0x4440340d40401c01050403c401001503140600c941004101e10580951500c8401400940745101c0100310510503031020000c030341488400c02c810400780400280170070070103a15080007961070b210141c0014200c0d003420002281808045030703010403144060103101d00400300c03858140040e01300511009013480180f00ca845a0751b100f400c4d24004600a4481c4041519240149400c0003d415400303000c0c1400c0c0f005104a42e00e4608414424130381001e00211281c4410300040ca1800c030034844140d002d4424014004202e40440003012032901c2543e0070410303410800002191040940710716828805c0621152103003082000c03107445012001001e40d0a4008078500040444048446500c40c6400b40c079000d004060704148030075040941180c00000c50743c5180d0381d00348031401c140190003820410f030824440040c07901522508080004000340000041004910014101240e2031030041c42011000e00c800303c82c61203598040c039015a00c0701c0c075507070034a0700541c080e501c0400104c4035031007110b20482c1a8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 38891425 1250 38890175 38890211
    0xb0c100510050102060a050106050a05090f0a09021309060806040f14060103030302031e0606092404080a02040515010e040e0c0312030709080f060112080409021303060e01060501020601050d06 84
    0x800020303500c1003440381802d000902e071410044c614403440d0310344401071007500d410100356040d480003890215560000423010030007101800034a10380018a0000c080b580310404d80240c80f0402c01043d2030502283d41d040d5030310a03111988200345e100c0d008403002c80d022070b0028240f515514025000301c03400c119084078851420400740e00681c000782d804070500800907100d11b5130b28144205401c0b0f20129003402400107090380301300c46400b40305141b24000040210000820303212710800c00c2c400940c803150380d001174544600841504920507840d00c0005090031508c0c0c070240001003010303550540203c0810041c4001046400e03000402d500c244000351455036410000c113060310801c1b80c00c81e6140d04125401406505440c0c010b0070030740d00000c11401307010030001091070445000d140200c40460080c1401140d512403900302d990020b000003402c092401c8221084004c480c410300003007007952140341c0110b00300c0d482e6004d8540180c219100420561400c481310060190188200180703142011200480f8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 38892675 1250 38891425 38891431
    0x1510060c06090b16020f070b0313060b0a0306090308060603220312090309031403040b0d050a021c0b010e061303030e1305090d080709060906050a0c0203120403200a0b0c1005 76
    0xb804803031030f021204c6141d06000c0098000c0c4020000c03c81c0c541040103031007880c0030090140c600301140c4c0b42648113116194100020040001d069400c2e500e03221b04104020b0403070080254003052490000c43d031542408004c882c030070301c50b030a01c04400c94100144215560b140060581c20001b9580515292103554030035254003600c2525031103070142c51032a0020303e048010094131243c0d0010f1000700641c40195084842000f000e4400040550f21070720b00c04001c0c0107016105400508a482e00704848000d54083c801c00e900c243c81703900c5180ca00f4810800688282e114039a40104000703401c20000b4045d58503c1e01d074034030060407000f240c01c0043c0e0a008a440c200c8003601d15501c0200d841403d280c10800080d006100341c41c02004480c14803801402d10b08240c40b512040120008820004a00c01c040004001d903005041c1c8220745109c10700302041d0b0b0032034081036800c0200c80c0d5003100c1d10f00b004c0b081001c5800780907180c89029881c0480c80801c541180720380841034017400d142e205d216001c6104c2c6900c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 38893925 1250 38892675 38892691
    0x40e0a0b18071d0604050603060d0609050a0b01090e0a051c030f050a140c0c07030b040318090509071217071401020a0c060e0607090b030612031303051510060c06090b 73
    0x5100881000340303c1001000c005024029a000c00c81400580c81c3c00c0120b030360081d0140c1c1c40c403540c5c8144e03252120003842031803006400b600800c1a035104001c1c6a00740503048602401c414044034030420040c0e40c0b00c00890000070043c1e031182c1c0c0c9020422004845080e125821810b0015005040a19000580b07104880e54085d4556503202e01d0503c0c3d04a400d03064014612400c01402d011800c80705a5842e8032500002e014a00000c0c0042c040500c50a402d15082001c01603001c200d136a258000c00181c00140d400001c0c9005020001c10001c0c10b282d204002503070081404c1d003661202d030188110b44d0307001030400e82d4200803071850010414001d0004005548496a6a0161a1017820004111040001c004005400030403d0042d980d502c60340c514150345140c095140e903501c130080011440e124842d03084400d4040481c0c0d103410401e41c122120201e900910550b00ba01840b00b84c00c01100c9012030705011004041241405018801c3e2088500b00744126000261602ca0f40c4500100b01d00c2219185 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 38895175 1250 38893925 38893937
    0xf02100608031e03041707080d0f0501050319020d080d060510110115080a12051903060f050607030807080702070506040b03060f0a1a0d14040c09050c040e0a0b1807 72
    0x1d8407014100d1000080f103100381205800e41c1080d0b661400d45564007074850001c503202080c81400c0c000c40341c0840780016a120801c2101d090081000e001511003446007038803a00070309500500e400c0d6065000108240e00500301d40302c1310365507540d012a503003007200b036125120b80c0c80b131000c10070303803514006800c1e0b0f48840d403280155100205222425100480044040c1803c0200d00b08298040080e024103890760028044178804070010044884c0c0c000c0001c01e884c41e100c014480802160150b1000307003070ba140c002038406040e4850041c040300e8400c106c0000c0010b203c0d0710025402c5071085c0f0056030006264070640b0380e90380d0341c1d0002401c0c41c3c0040d086480e49042c0003003448924a408094001003000a41c0c00d201140e2030320000c240340c109400003904d4a41c6d80001c1004074015240c0c08500b0100401e49051424102401c04660395040d80c003a0403030651800022440c0310410b80180c80440300c824581d00300b16030340e0b1074111015102c2e691501d0340001c081c1c215441f80102450b0507603c0741400e40e03141 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 38896425 1250 38895175 38895187
    0x50c0307030807050601080d090302121203010f170102031522020409020a0f090f14180a050f07080115110102070b01090b0f01030615180b1614060601020d0f0210060803 74
    0x40b038100170041c2d100343c446d80d01505501c00c0d040c1c2c00c038080340c04884d01100c001d9581c00401040d903050011a1a5070085984000008964101c00700c80350700983c3c102d404140b00c000d0220b0141400c0348025100140d040c4640d020340030440c0b03000f03544286040e401035004940880201c0e100b400380d0300b2540024003800e80100300032034055401449160300d244d4074508030840610b0100d03017102e01d0710a40078408107107082c20031011076074031685c0310004540c1000c2c009402c0c030b02c2d00222107402800c013036500c640200f003d000410b12852140300968169200c13180313a1203200c540c5030010b4449402880300e90400303540034840030001c94500b0030140e00038006418003041c8030051b2020031880640c415075041c14940b42c51010b0005500707400c3788a21640d280e08184079500921700d900100d0b0a8943d001e1382c0781170000541c89210418020601d4080c52040040c610b440c03400301c0402d07071100d10880c0c01074016408281c0c0c030170416110303038000c20801c89940181d4848440c080d10302030a0716240d070441c24032540000f0721 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 38897675 1250 38896425 38896433
    0x240d05030c1c05190e01050708040e0403090f0b04060804030c0b04050a02010e06070803190e07080a030801151704080417060603071d0103060c030f0204030f05010605010201020906090904050c0307030807 89
    0x10b41000d041d51508501d0001550f11a540b8400c10b035068004002048080030540d034002d1040b6408143c00c0001240c80b0360383c94403012000081118100c0c00114520000030300030110301406802d680c903003403601d414941403480c21074240000138025810807140190940c003180030b0703c01850003640564081c000d4412640005004455041341941c002c2408020b20300200b0320a01c00e4940107003c6050006071640c0003a080c2000d080c0180c3e00314018002c44000040300c80000030040c0c030745c0e4070036260b0070030683c0d031040200c88840e101c1c1200004207421004101d50208100786481d4042d00c9441c034281401e4440281d9069150403078055822035011000380181d510302001780c2c02c0240812070304031061280340324441c0207209041c400104002d486500013501540241c1081c240b00c14800300c21074030fa03592810201d00700e00d840b1106542552811401245079403060007202c0d0b8503039000d06520315052468080c8218600e00a00c1903885019544074441280e9051080000a50244c0344242c1c4451150038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 38898925 1250 38897675 38897713
    0x9010501020f0c01030e030f042d050105070305030a110d061d01060c0201050304030201140703020702011106090304051c0f0b19060501020d03020309010f0606050d0b040203240d05030c 81
    0x10003415503015208940360314100091040b1918003e1902007030030060000310a145021b4811407550414001ca4081107e140b001c04481c60701c024286062004900e04500001800c014052140001c208200040110b0301801c0216001841014009103a1000c1c0740c03182d130b00e41c1201d05a5018291201820070010710204041c55000c0013501e4a4043d5502d46032001e4505025090000c0c103200c80400042d00b450b00071f51007044024040a9851514603024400900a5001d41d000303d000c981026024016283d0009500348601c50301000bd524142c108802c0105040e0327a42d1034100070904002c075240000f80c007400e01300e064501c541128032090400390569100c60082182000c3d80a1600c3e104201507a8002078011400c0d1050400581da6201c044405000d803a1181d40c9285e620f0600d4000180304e0351100083c0340c6140c000004108226601e4200000c1c1d100503586800095400700045904d2000c114a000103010000d107405408011a0742d010700f55085450700c0e50303c503084007101038a0100158 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 38900175 1250 38898925 38898929
    0x3090807050a050307060c0203030c0604030c0b070206071709030c1b040509030f0f0d02160302061b0f090415030219031101030923070b0c01060807050d03020a0312060902040b07020901 81
    0x4902c46556818440400d0341c900301031103442d040180112110b02551030070301c11101066406d40956100c1d00d050f060180000401d1130b2304403070702d0221000140c13501e4408a007560061129603500810380390405c1e942c407a55000076040304600c0c00100b003400c05c011070401403c484100940e810002ca60091020442190801017a00b19280c00401401124120f1241101c04d007441301d80c06d051304c92a18507c010001e02410050694150700c0c1e140d81410b154000030128030a0203481003040803058540c0c4508c025014100c50081c1c100b074244100c20340c03464036400000c0000300c20088a02034940d60b40001d20940000c5d2032614040507070361400c0c828049180042116002c080c2030510182e0340d690358113292520841141210b1084445400203191418442d060060149460683c0c40d4844c1c60044c1f4001d21700c07441002414440c2d500001414100104c5111445400d034001d89001d4505407000e982d206062017031040203640d100d802082e8042c80d4400f80019281e04401c1030f444e03240d6441400101501a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 38901425 1250 38900175 38900179
    0x6030c090609090209070305100b0304061a040e1209030102210411040c090e060a0312020d02150f06010c0501060e10090c03110d0e03040e07030b01021212040305091c0309080705 78
    0x710400340f004d6143d02074110b800c02880c0c40d001400e030baa1803401e40308410560700030360a079600c000305100a0040c1e80d001b40140d112030f000c1040d0703403440c104104011241d002c4c50780201e03030b0031038a41d0714400c1b12120701920200502400240c54500c02c2c2000d01e8031601c840010f1811202207005020601808206040703a250058800701b240e003d0740b10010b40000c010b8820036034034a4001c00001c0c01512003841d51002107501840c0c4480c800c00c42d02d4040e4070342041508400051144441c070b4801c00d445004403e000740c002500404054440c2e0004445001004c3c45c20340c0c0c0c030764035031000003038071108103070030380e01c51108002c83c040d001d401c1c00c0c8420f060703c02285071103040606104d450062800001d04441c0f0f2595141800074103541c1c001901811800b540d40300412850060080082180d090f82010050390426400c0d51a2884042e004400034001c1c00b1382d0460380e00006c80004d002074058030040280380b100410b880d020101c508105200890352100c120300041008208001303060080019801030801 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 38902675 1250 38901425 38901431
    0x1213152c011e020a020c27040303051e010b0301120f0b0907030c0b0a020606100c06021216080403020307030f0921030807090506071101050405130506100507050c04090503090406030c090609 83
    0x400700081d910801b00030b2007489951126041d00c402080c4845900b0009404d000c0c422082c80c00d400c02a008010444102141e0084c0365100c000d00c40210a1403816101a08209030440c0d003040031089610310b02e040304036100880300d41e454000c03a41507103070035104065510081c50664110b1500548070442c6e81d100a880c650180460511560046543c0f070b445441900c0d1005900707489081200e58208141004d402140b0000d08021468000c9440600c50203009412603440132551004880c9100d04a0700540180c1007800b40000080c0310b000301d007600c68064034100b07040a44480700c042c1914110349816214041c88000300f01090341000100390f01c1103aa08045070000d10b49408950b01d4891880d000700032150404c03240c41603a0007542030340e0281101404103507d440c842e00700c1e200141001d8441c0e2b8851921142d140d0400342c0f040c412030b45110b600c1800380148466103c1408040c0107545c0b0100c405000910255940b07880340d22584000798082d0408000c3c413441c0c02c0d90101103544c00c2c1c101c000c482d41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 38903925 1250 38902675 38902687
    0x101e09181208040201120c0302040f06020a02031906021209060402010201050108060610050c01020d0c090e0121021e120a030306050d0804030b070203040504060603021213152c011e02 80
    0x40e01c0203055035105507030406200035500c0b4401218401c1e00c0d03201904985141c0178500541d80d502d5400707007095a010520308005103032141c8059982e5110380320000d6155000d691400103c00900b01c91005123031084002600305242d002c0c070700d03010f2241101d4410080e44440104801d5690900549004009400280800d070a2000121300903600710f85190040c40f000040d01161001c09504031a4600441d42081240340292399005050543c81e1081c0c50111400000104480c03007010030342a00300f00c01c0c00000310540d810f40d003488100b5498801141c0140d10913018250341b61101600074000c0741071036000d02100c8580d031a0103400c41c3c0d040e4202500403040501501c00054201c0101c070300352504401040100ea41d036840491a620035034000ca0781080c1000320000d09140c05070040c1203200390200c0c039400b084e03031443c03500400c9101020010b066032800d03071202d10b02201154403c400041c200700c88850101c00b00310390041034044460a407401c50b9903410f0050705c00c141440d50b016a0720b500e58005d619004c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 38905175 1250 38903925 38903933
    0x30807030e0a08070b21090f10020307020a020f040b0406261504020d1713030605060d11010e01120e0d230304061109031006060207090605010504030b101e0918 70
    0x3402c98001e01110b6000020480c0c644c20055410700d40007801c08942e90000d1030241003035503c490700d49180d41c1c001d10611080314050140ac0c001d2fa441816598000c1c6504000da800b08400c603000d241505030014bd407000c0310805515207004843c090301307080306002010a80b13601e4081480000310070003031090700030300741e034484650032815020f410540450f101140c007020743c18180054070010780c41d00c03910140003500024a00410050004481c0074040070040781c1d891340140000f1201f540402802003500f01880e10f410b601401c401c41c803120040c500800b2001076030340d000e000c654094488601ca80c0c08810440401a03115100d400e0800301320031544800081c0d01002981d0b03000107480105200d440c0c180340000c845051090b1114400c006089481040c04000d550008000c0d500414006004a02001c55030b642030703008036001c484041c8c0d5094034141c60b5440f40350b107004e00075081c60000034907158000b82e00c2c420500f0000311081d40341c40e980b91540c1703840d40700c1003101c1c001c1403100d00c0d020042d074002001c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 38906425 1250 38905175 38905183
    0xd050a05070206030901140109090c0501093f2109030b01030f020102150c030406060608060d080d020c03070503030a0c030b100c03020f0102041403120c190c03020901030807030e0a08 80
    0x1072541910744503201d0301e8403c104c60141074103044010b102401c41c00000340000179504100c0780c40f4003c0c210a40c1541c0c1f0b80c00112080544c078000c021a203061714148000c82c5402c00c51200141215001f100f0a109100c4107900003038442c1d54041e103803a1000940380c8030989a01051036414005810041402481d680e21424020014840a04480c0e0380140e40300c19a4000d00012481c003001d0145034071185410f00c03451038550415a0107035944c034500980400c60034001c4c2c181501271000204400c070701c0d0420743d0760601c007540700c401020f4130b10390207011983c0401000c1000e089094403800c095902c1785003c6010b00700721001000d006040500b0440b2b801d0582d1142070071250314880360315003002c0d2481c4e04e00b4140e1038400702e4040414903620004001410702e410102d00b00e1820320441c2910101c0c1029984054240034a03071964506410172640c12002c1c1d03d50030b00740c3c44001d102c0c0e0b402548075607694000601c2400e09a0040e02d000c0800656481010340c002d0101c10055400c550b0382c045c0c0c034240505244d41d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 38907675 1250 38906425 38906437
    0xb010905070f0507050109080d05240f0d020a15030204060f030506060d0f15090218011701170a0503030403120b06130e06010e030708070305010e1c0e1201050f07020d050a05 76
    0x14420f00141080a010003074011115882e0080c800659402543e0380d640002d1500722591805e401486103c05903625203061030041d0480020402040e06c880310003080b8541d001e4020032a4080e010200010f4040e002004041c003102032a100141c9440c42c2040c00b50080d2090401241014174110030230501e682c2d891701362042c4416030000000c441422860950041055502c9982d00b045140800208810260018000703110f82d6083c00103d5049200103480c03040d070340c0c00c0300580f04107030340d0050203201018800318041615000840c0c8000c20552101800d551007620258001b6603145540c02441c00b590003901828207081c0c1e40a4500060b4444181e8100f85901a10072140040d01c04903103603a00c0360080c8008403070018240c40500c0e40d074154040c0c1d22482c1d8802190315500b000007481c1c002034040707003840800c003010741d40710000302007001c00712a0a00c00c4c0040301d911802024168644440902c1420701c40c00703614140303a04508141401918000b0103162035010010100005800b442e4054140e400c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 38908925 1250 38907675 38907677
    0x61308010618053706090911040c050f040504050705090d0c08010c05210712060b0706050a11040b0904020d0203011706091204060c0f0501050c070c0503150f07030905070f030b010905070f 82
    0x5113100c82d2a501c0c3c00503090950000c9802800c10501c0ba0900240040c601c1a80904039400c0103589031145041e00c01d40541050313941580d070248810011401c00e44c2000e80d0108152400d1407515004000040c5204d40d0b541054600e5121b102c020f001000702482944800d0805040c440e00b002c01c4030000c000e100c402c001c0841000d040710800314a080340a6007030603140d042c8884d0144810742c0c841d810a0003035001a1001d0340e1490902000c03139008003803403040c0310b0360040100003e07240c94184803454285501036100d06811550070002c0010310708051008c2d602a0a840c0e03801003100150301410780c5032103030180c2241c04607000b560482140d180740e501101c00f21801170030f202d00a00c0300360802c010217880300c0901400c40e5003042d0400a5000a280c001c25a02e4401c0320180101904e60051545c0d800011020516a14191000c1a03a100744001e0060b0f0120262402003810f041640d101da050020030303807090400341104003051080100c03007404940500240310040000d807400721001007a019a04003084 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 38910175 1250 38908925 38909011
    0x20f030403030209030c09090f100c0e01080415050f16020c01121107050a03080105090106020f0c090c09100809010b0105160f030c0501140105041103090c06130801061805 75
    0x20454409100039444100000c01f4207019181208016884141882d00386103180034210351104050464499106017100c25601c3d007021010400040d5200c04000d001034810310450032041240c4042405014821080144031000720308005200104806000b6074001c29500b010f12842c02a1740c0c0b060b106c0560240c980c0010a0f07141c1e103403641d25164400e02d08083c200b80280f013200c03000d068110000740c0c100c620940c1c140d6100d030b907a41c408036202d01941c0b1201c2415000040e0400c100e00c0c080c20f02035008002c802800b032400e060b07140045c1c02900e140203098086504003040000c216000c1c860090382c05000e080040c64000c0c0032120b0b0383c2409045000600c4001003038020014144507012102c2e1903580f10000704540811080300c90501482441803d00c283d040140c1240754000b074a080d24000c401c500c0080145414450800c03645402214101e21209421080050302e04024014180281404840380704810b42c0e051081d426075000030100ca00c1d0020070607080c102c0060450a00800084041c040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 38911425 1250 38910175 38910187
    0x12060f010e03010e0304030b010602070e07031a19030c05010c0b0c0a02030c030307030b0a060906050d050c0d020d09020411030103031d030307060507081014010909020702131805010609020f0304030302 88
    0x40e52140401c65a90390558a0091808900c60001000708296405002e04070780680c0d950004a03540c207580e002d0498196500c030042000103001e42c0005044011605520405044210100b6910039024400e01806104410208103106403080f00340060402031910040c602140d881c1c0611041003e02280c43e58100003440c0002144240103449401c1104030659035641000d03180140074100c200c0320148512a15100043d40c240646d0002e01241c5460b2151030610118144420040200500c80b980d440400c100f180c2c602c5a140c4000c00c0880940000050f603484540188411610a04072101d8450010001480403a800408144800034600c0d059140f10001002080c21801107900040a1038104024400c0698006a005120b585000c0301e5401030759035070680062086071020360602142c4010014002c01d03105030010201c090000d04518045691000c804044481d903c03d40c0d40c40030042144c071000c01c0300a00440004201204055041c071020015195132444040e00c001c1c281640042c0c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 38912675 1250 38911425 38911427
    0x702030a021b130e06040506010909110d0c08120c0c15091507060204060c030e0108070e1201060e150a08060106020c0409050f0f0105070e04050103050a0201030e120c01020403030e0612060f01 84
    0xc3c3d0f04035900801000d2004414500f5490b079583c10a413001c50300c5000c2e002c004515201203100d508a61034108d1080d80b40d6029100a000481981c220165044c0e410000301113541d00b006c10004c5211072031100b0301592403020741c00440c1032002c03510180f4494814241d4221079102d82c3c01c10385264650031a1001310017259100445007a108444000309481d00214001480d150820511507281d80a03480d5900400d480c400110f170109800c65502d004a408901d0f0103410703003041e2000d04c0c2c2525411000090305a19981140300303403071003228107801c40c036880011003565040281c2c0d401c004020401c000c00f01c40d414076801948030440a8600e0303002d155110903002c188507003006a400c0c07120380750094400a050325a00b40c0e002e00004c03113000f4003043c0d600c141043e49040c1031294a040b65000006400d903008a03500440240c00102104401407081c18103180013910908010809010341100050765603240d445c1c0500080080c032a4a4407900d000d003c900c1e41d20540f154050b600c582d00f12104e1041d4150030b00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 38913925 1250 38912675 38912689
    0x512180d020a03120519050301050108060402030907141c05010c0e031501060815040f0903030e0a020a0b0901020a0c060e0a090b010c030c0507091409060a0905190c03080c060f0702030a021b 83
    0xc40d901b8a520b0b000c1031480f00c20b07081001036045c2e901c20380c2c1e482000d40d240014881070f07100c142c40320760391980a04800c006400d418031032a00440001000d07810000d0404c28001c02c141c1e220350b030a480a03507440d442c40008642210610341200400d8004e030410032412241140b0b21501403040b031040c041e4003c001141500808110b500c4503400410410442d0725651440c0700070482c00301e040780407a141014500390040e0009220340d0550740141b013103447c10300301080031510f60080f40584e815845441104800241051907460280c15070341d660107685d0090304100041413082d60300c8101c46600d00340c00041c1599100b00000019505070602d13110081e4240b5103549031240a40c0301600b203d203040d4940449401441c0301c3c034000c4200703038200c80980d00c1d644200412200f41c00001001c0390300581c9808401c3d25049014414a40204059900641c1d0b07a1624501540494100262a00302c40c0400c03101e05044801c0e1a080131032440158200901000080d43d1906079194049203800c51542e82d040c42c2d52100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 38915175 1250 38913925 38913937
    0x150109050607030f0206060402040f0308090a03020a0803120c04050a030308100308030a0f0b19170a0602040e071d01020723030a03110d08131401090512180d020a031205 74
    0x1d450203a0300d54150900030406461082c400e070060090074085003507854140241c600f914600400b941c0d466181d41d81389501d60380a125400e800207007a5200201683c0c510512a005000410246940d88100310030705500380e100070005011004103000134009914ac0300d400406a0341e0505140e055616075020300c5040f0001e0754802820000e00104003ca10822900502070301045140c0a201c988105010400780f000c010101c00104841000100409900b0900c1d0b141e2840781d800580c0e00e000981e0312030300141e034002d40001c0c44910340c490610246503444207043c0410424410800038503242140002d440741020300c100201640d1010309100008400ca0900c00d0010005007141c005003d00c1c81d018100e103002617059101401600c0845800d9806001319a219550aa6801100241981ea00b4880c04013940c01c0d04035640d626401000000c00400c034051001713901544098272002c00d081020410002281403e00030300d40000d14500503201c1d8407016050720b0340280340d110140b040846c1110030307016003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 38916425 1250 38915175 38915179
    0xd0302130b070f052d0303041e0f0807080a1b03080109110405030a0f17040f06030c0507060203100f0b071106031b0d02030703050f2503151d01080606030615010905 72
    0x4020986417844140400c00520510502c05c6201091601c601c1a02c0c1c0c041160003600900d40c0851034008091090220407845108103114074101003a6140c0510681020700c0c101c0307500000103601c41c440c0c0d070005d04600d1890341c513040c003d01c20300041c2e50043c80f445040c441d80c14001d0300c03040505110901c0c142910b000e0003000d0210344584509040a0007401c00c480e0003a1007580240b88882403407003c090031203050b28122040d140d8203602c0c1540c120010002680160f007009018004000055201d0000b58013440c804280c4c03c1800d82484115414040560b01c40c10761003108000a00001d424031001e580040d4013190415240c0d61280e40b08080f000600c9007003610070100003880b03101c2e030328140d01440c09481155030401081e030f21403000400014007582c214840c00c3c000100512089001d900c4480742054524022a051017000308a200001e8150015007080c2c11a1803c0c03880c4c000c610580900401c00c0200400355030034454040781d00d0309070181c84402014402003010b43d0070390080c60b400c3d00070000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 38917675 1250 38916425 38916433
    0xb0f030d0914030a021c020103110f0306010e030304060c060203060d0b07020303090c04050c0304080c0c060d020d0b040228140703030204080d080f07050c0106080a0b0105030d0302130b070f05 84
    0x285400902040740760241c4000e0301e507a01c610704881d0500289114140e54054141e21043c0341e03a514a0b001200c190104030304158036440602c103051070240150412aa002144507100d0070710074009021214034407007642c041c2d4001c3c03104224195100342c0381400c154106000580d6502d90070301045c0103400c0568050401030802003400002036000004501c101181000c0d1303000a074001c1d0400048d5402a05e243c05038010600210b808940c0700002031901d140c40900b00c400300102d10001c07d03110341150110200059001c5030300f0703150030a64004e10350310321002c503007c51502020400c0e10307000020b900c44c0100c0c0c503240007404044072405507070484102c110003610b0940360002498010043c3d40705000b070103041d01841713807881249801403a2160142001c240b94810035910301030100e849400100100f11999203440000034074520070303c040e980d414007605e0240415070400c0241460b2035290560401090300c104050a484040b40c0346410580d2803905020b03580780e802e0b0500c5002209000405007103402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 38918925 1250 38917675 38917693
    0x303040608041e02030a0201080a02070f14010c050309060a020a050f0403081314090a18020a0909050f03030705040603020904060e1006080c071e14060103080408010b060408100b0f03 80
    0x280095440b8815071003400c02004080f1142448850382030400002505544402c1c0071000540c058031002e980561101700050515500e512507180740200d0b0b5000ba19568081c1c2405c0035610130a0066040320f10241c2022861801d29004465071680c0081c47d5400f135030750115403030040c20301c039504840050b011240591780b2a52642050b420550003400000e8060b040d54000080301c038400100c04042c2c0c0c00060250b0325580c0c580515001405421015001f1078482506003001079407610703604005881109000181d1018524020745004000c035a03a891540c814400c100c40503074404125420b481440c038001d07032078003003c402250142031690080d4020a075070030100290303640c048020170125600c66444e404c154070303601c0c0002c00e1440307055009080214014000c030304800015203503014882c4034100100c065804405518141802a0801c03203914100203820015a082401a940f09200444410386082e140010041c0e1301e2840d60310b542c0b4142e840d08000086e907982c20300202e424400241c03d40e20180 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 38920175 1250 38918925 38918927
    0x608070b031501030603050d080408040503030a030b0406060207080601030f061b030b01080105090601091208040308030702030310080c0603190902061303020a0f0806040b0a0b06071101080a090314090102070503030406 95
    0x2401c01ca03503440801c0350b480c0032a0030942c400d000d202d040301c1c2c12001a00c1c00c030f42c16640c1220b00b840003c20070b90f1a118100400105900c040005100c0c41506580005802d0300034004c0005850072a80088115800448103101d0840040383c00c50440f40d0011641d40c0b209070701d2400c1001b6001401660a4510001d041034440d160140c0048148010980e40c40900743e88074000c0004180003581e00c6800038003007800030b004203001047d58550203401080303002d040c2956941c0d2105c21703074000c07a08900160000300600411000444c1b424025103c850040c2c0381d000b40250200700e06010040134407030b250225004c2d240d1031403c3c0380e20164015401618065440000b4034504482040501c07080b400351a459400042c09054440a1030551740c980d0007a0610351a03130784070a040c0c0720000c0d088442140c0d41d02e92610441d507501c4020288507100d404240c82c0c0713041c0c40d8005007442400901000c105410441980002540324407034030b1041007180c80407902da020540040b0b1511100f600442e40521001a0101e111 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 38921425 1250 38920175 38920177
    0x20c0a0308040e0702071a0c030903010207231506010f0e030a050607090602010e0309010302071e06060302010f030b3a060203150a080c040b1309030c0506060d031b060608070b 77
    0x961002845041c084e1140241269103030050300c0342c001c403610302c045070800e4448420000d0131140840004c0740e092420f140006400c907842030303104440d5122001000350b40703502a12007492200c043c0002602e5041c000207101c1050b58001030800e0b04000c03801c800003094a00450340c41880c0d100240840b1a00d80d818900300c0d94840003610000f02140400320000b51a6105000300454402e149014504145400d001034010350003010b0221120410b22080b0614401a900b0502105005d10804100e0074034600024200e21103615509041504103094070903152903da900020845010143d05294110001c005801c58141d0303190100820659030a070f0280710140c2c0265016008031540c68140c1642d03802003100d04140c030305c1008200c1e00101480e4009240c65801032884000140446450b20040e0580c003049a0903104200e01050000071a03900307100341042590382c0110300380c601c52008103444d1000351007600c0310381c40c89150b44645070329201001000d41107480203040c110211080c1640f107005a441c6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 38922675 1250 38921425 38921429
    0x9121b01030b0a03020a03060f06150201020403030305010f0b071103030d0903020c0307050f180a060b07050a0c09020903030f030c07050a0b150402030403080610030b060a12241203020c0a030804 85
    0xd08000d040b0010f481c00355140012680d00814240003545140c1d5407901405c142041c00e0513141c2d940d800096400c0071070044d802c0a10b01035000582c1c0354158a0301604840c0103810000d020250901e0601c0152200c4040b80da1090304187e17280b12401d07001c00007078510b115101d0003026440c14040e8640405400040d0011240c0d011070940e003a0a49543c240200c0c02c4020240c40d500c04910071180c0a0b580b04d12000319040440e1080100703480303468401c29002580b10843c2202d4541c0701400d03120910010103940005001a10010751401900c0c0740003940d00e005081c40101d200300c1c00404145000c00340340440300c00e15400015036a44c29983d081c0300071409001c840e440003070b10303841028210324a400e01c00c136071180342d15445004d0b280e1101000c1c844061030584410080c1035880308190704683e9000081c0403104459031700c611290702010510001d852401688074584002002002c580008100d0304800303031155003000390408900c0b420103d1804000294950308810001c03c0403041c80010b000400c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 38923925 1250 38922675 38922677
    0x30105040e0f07090b090105030f0d08090a0c060507060c11120c01060e0108060106080117030304030c0201020a0203060901150911030609040c09110301031a100b0a020307080301181103190209121b01 87
    0x342c07580c2e84000b27158403240302c1c411701d02c040c0d007203154a6030816000d4010150428580822103180481690703d100c0394451070b4003e2400f2030700c04145003003000580e009410284a5078a4141d6446058550003941c40340c866000300440c1d48040b03074402003050b003540490000c10060300409460b5a43e910403a131100b5083c0607881c0000c0030407001044110a0700784429041044400641c03550391643c504948220440740101c2c114040c0078039150160b5020070041d40940602c500001e4120780b0200b9a020305c0d034030740d4803070303805a800c000c081c1041905440540e6800001a40d140001d80e45070300d0200401805500706008151504a10410004d20780d0007841c10389100301420003c4a10804c2038148114080750b180e00c036041204020701040054601414107076400340102c0b4201001c5683d8007074203401c241c1199580f44044000400c00c104140038104030108040070703041c5541042c06007401a10400040308290540000c2c1c8442141c841e401e030291481080404e0b90502040011501c0c80c011200c0a258 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 38925175 1250 38923925 38923939
    0x30c070302070e010b090f01090503010207060e0105090c011d06271305040b071112040e040b070c1a0405190609020906031207020d0f02091602120f030105040e0f07090b 74
    0x204a0581103c01c95050b915616445804d1020071010048640f106447c4181007041c0c0c2c100c0040c807601c3c2400a4201184603100100e0a450014419400c450000700f11038031660000880c04102d98000c04400111504000c00b00e0064040c240850010301c1101083c4601c145084000712221000c0341e5000200a4100e8003000c44c1078401c4515419244c0a40c2c0180144110001040d101d078020f01400031040a80d4040c1c4080713002c1e4004003455604039500464054820404110400080c1198641c0c000c08a0621007404a502d0f102e00ba128042d50040001d103120b0400420148441000001015a00c5034480c0ea1119820314240340900b0740c07040d00724040c0c4648408107000b071401051003581c217541d0750041403c00495408010b41d0313404845e02502c2d03800c04110383c0340c05030300c842020f54840c0301d450001d003d9032030004c0d2000b0314054810003c190b122100b4411450105910000c07241100d0b01140d0219001ca103508215080010b0080010b0051040303401c00144070354644c1251202c2c40742100d41c9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 38926425 1250 38925175 38925179
    0x305010b010503011d0709030b0109060504061d0402010c050c1003020d050a1a0f120d020706080c0705060f1906080f0706020102090a030314190c0b010501030b0d0605071202030c07030207 82
    0x642d09804280a036003412201c88110000384510449000ea02c40114644407004a640f0348807038003655070a0304441d0500343c03903481c284018202805a18001d00b6900d000303002c41c2601b840b032100c28040152000781000880c110742805d0240c2040300001e00d900040c4500840ea4170a100617000394011004031810781d080400280004080d48501c40140d90815400c01c008080642080f03042405201d0b05540400c140861100140381000112080011500204215420104080d2102c03c0c018444842c6000810209001600102c1c4594000a540018540313640b0745c402038003843d401d900d044034407035032508074001240b03d4002055041d070392500017a118119110320b0100d00380d1242c075041e00d800c641083d00c1000024841d03100300703443c10030007400c5c1c41c01c0103620b807900040702d8001c0c124a00080e40c2425440d0502141926450041c2000d0808000c4e04001001041d04c0d0440040050420703aa59030004a4071801351003144003014907150115030368034107d915a87d00e50424501940103100d01c2b100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 38927675 1250 38926425 38926427
    0x5060316030305030702031e2101030804030303020313021815040c0e0d05070e010305031e040e0f10050a03030804050d080106021b0d08040905090c010201060b0d0f140106090305010b01 81
    0x2080410841261245080e03085480c1580c99601c00f030607890462000b0803d070107030300352010749201c44035001900a90380d17920403075402c07141032692118100c205000c1e00c00400001748420121012031740d041c00d015031030380c0d205c40e4105040a0000383c080d401c038980d921080005c4003507615082c802c080310481244940c1000b01484100c403100684540800e4128000c04002d19014509108281c41070045a561688484090301c02c00c2086c2e000311996800403480d80c440c41d090984903030700c20031101581740c102480c100f0a100b1141000c4c16a600d15207082c0c0115080031400eaa200300645070141000315041d42e00e140081481d201289c05072000e0290810700c0c140d1038860030109049615650080c11036001d01841c1e0795910350a1501e1581c454601501000068520405800246003c8000041c2441d10800c40e60500c0003040d9000d04592606506001020b0101c3c00e81d01168003480f000240900c0c0044c2800040c2003000d03400504036103690000500d141d2003990309050302c2c40741d40248829224800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 38928925 1250 38927675 38927683
    0xc011506080c040306180512030106021c050a0509010e04050907031704050102060f0702031201090218030601050a0603020d0204080f0a050f0703030203030a0203190603030f0f0903020a0302240c01050109050603 92
    0x6075007003040404100410110300c2da50417061048180d840f010314802c0b0746c0e54880d481d01c4150140c3c155a100040010000650140078141001c00c0c2c1401c2007804401711100148a44507000b17031401403002c041125880d036440f4020200610328060000c12485c1000ca03071980d6100090b10046506601c01c121840d001d5048405030b80494206030010b00660b2206880814400002800340c0114442401691486100025810700070a45190016901c3c51400c010081040700d2f80d0015010b544410010801c030f86601c1c40000031241c0c1d603d40103861300d0101c031400c4041d110342e41c4201c0d641d128500300e00e408507402150201c1d000f440b580032201d450b404202c425403070b461148006000740c2c01c280002036809001c0c2e001075501003842e04640c03044c1140d07034620b00d040f14001d0b0810340009a21030343c0d209102e904008118410111070400a01c224030f10390015940403058000207001d251144000690102c0c0c0c40c85030016403d02c0d058054840780e4003c60107009007403d00c41e424a55080102080e00c1f0b06000c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 38930175 1250 38928925 38928931
    0x30a0606031103010b1b0a0b070801050108070f050901140c07060801170604080a0e12060106021204050f100203040308030403050c010b0405010b0a0c020a08031c05010e060303040306090809060c01150608 89
    0x2205141540e20f0300702048296040b13581d800001b40c1d040d10f200381c841c000a100e0200e25901c01d120002c0d803806c21120042ca003082c1608400e040c04501c2c02030041441e005a1103200040103442c000d0390760424200121000340c0140e200c400c0c46030300860124200762020484a0030340d850307035813034031402d03039032030403200044640340901c1c03070711500031501080114444c20001c104868141c10b042c1406c99014000c02c01000303203400804082d8200200500110b5818085440210300c816001030a090501001aa080c2c01c0501c0003807041104a021009160007071055134001e542010a050b180c0c5850b060141c404d80c000314140e8050351900102201c249002e209050603211003124081c1002d20081d0250781c2400c80b008241da12000e0103400242c04031040008102a04180d40f1611030500d102c0040c3c01075030410380050f58601319020070170209480c00000c1c2c82c200c035000302c00812428008d007021721062040140c0560003100001d0403120460054008021181c2c0070f080100c0c899680d5007046418400076 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 38931425 1250 38930175 38930201
    0x10c09050a06050306040902090108060403031a030c01050c0703080c0d0216030827030601080f010506040504020303070318080604120210050f180f06090d110304030305030c0d0b1203030a060603 85
    0x1c035018403800d88560040c1d81e1101d0081c100080002c56900091480d4009a0010b5407660180e4100020598103000f03007000c15860362000c448400814000a440e079002d11a00c0c0e04100000c20000c07416036081022500564201c0406680c0f02204000e59484494540e8813202521442f0501800d1102404108080301d82080ea000d08190070594009000840f1940320045070300c0c201e9115507a650140710240c020a03107100181401080008240c1c251440109414462490030042001507107000c070860300300c3c1d98145045640403940394116900042c2c99000000144a21001c000401c0b4012408450800745c0c1c3e000c5031a0707544101100e82c1940c9003191144081071008000c40c00e9110845c4044000c80c000005a503681e40c10b480c185850701c8d80c05c44230760000b0ba1100d058001525003018044a8042c0d041000e94038160441d00c1c0034103244000b07000001901400207030110141c010b903003c2200f400303001303111f80c0780242c0b56003010782d690300140d401c00040b610b403410002c0c0d42ca00a100300c250380040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 38932675 1250 38931425 38931439
    0xe15070f0809010b030f0c041a0604090203060307080105010608040606080606010c11060408060c040e010501050315012303040606031b05180901020919031208040305090d0302070503070303020f010c0905 89
    0x1aa04101c9040314003914200040d03480e074002030410ba0b01841402e9002155400901e40320500c0c0f010030054840407035015030300d0100f00c0314440c11621403030100c03016180301c5100542d40c0d4036110003003407070200a9400740c11079519100010941540c0511001c2c051400303000b05121440e2904140354680000713940c1e1030301248074001e20000040030750007600b40340d1400130407560610340d4400119040c9441140d103004007000000c1e040c454460368030019805070000303180c401e0031032410070281d13080c10840b070059906101000c207034649880360300741240440c00f0720400059180d04051070408090710507800708861621800c25010703209100541c0803004c0f02c100800600303101d0201404030700d0500c00501200443c1d5000c0000100607201c03a01c0021200c84104a5420b0061840c200002c0901034a6542c904200c4013030180008680c0c4030041d6a00100c0890300d412b017411681c40d080e0300d400010b601140c1c06000d0140e000040c90703008940c510200012070000c1c0220001c440c022140000c8071300a551740840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 38933925 1250 38932675 38932697
    0xa0f020f0105160b0a1b05030901060609050a09020705070b1207030606020d0c03050c0102040503010504210e01120b12060c070b090304080604121b110f0117011413050106030e1507 79
    0x301e50342c2404d8005171105d00c00500603041c00c0100301c19042800030000456400810300020800034820f1100416003450180d4459090000140c2a01d401d44108110309070086201d41c10300005019244c000c00082e5400c0c1e03500c12214079041d203105400c0f140c2c1c04c08603103030110000710140040390003c5a45095030700c0e45070715882035400b82c669030040c1301342c1e010742d66091002142c161001d202d4640114010301c50030a52140702c117900070314070142c24000c00c2005110240c03281c05d40d030031a00390344050700a40030106401403040c02013100e41035083d0602d0801d01c035500a00c00c01400890050501c6805194003500a5541c0600e241c0c7c0d070301c118803c030100780d448540001d0104841c2c401203404e004003498105400091207440300c40c50002d010054441e03044411300c102c45841c158031000b444003020f0801a50b0408640b0498460400c14810034105509940c04222595502d456450900b40d490008201d2561a250018003c000348400490705101e485500141040030071041c40c45400c00ba0303030b0303101c10b10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 38935175 1250 38933925 38933933
    0x50a05280e03120108030714010c0206040206090d0c03031d04021e0306150c010c1d18070309020402120108010507080f06010e220c0917030403021905030a0f020f010516 74
    0x110418000745240410b20520410407203090710b8a00038500540190f49076a503d0415104803010414a101643e15040321604450b03000300d810b607801a01103401c25100c001800100350000d81c17400d4024280350040c80301104060b00400030031036200410751120010311400091204138420184112101041140b9a101e038642c6900150ba000740c019000c40070350742c100324284d407054008010b4030121341d45400112480303640c0f0040003c041e9445000c061001c82c040c10101d5078110001c1c1050386811440b600046110b80281c000c1072500394040e100310760750f400c0303044215900c210138024022030303500f003a0104808134030611b035103801030b0200c118900e41c2e9100d0100640341790824040d0243c00c0f90040c04449030b054030b8401c03400a510001040400c0d904c1e80c0a200904100d016001701d401a03800c81140182c0440000555043d243e040d20035548401104800e41040603441d8003059141c882d000d101d004022104a20004191003070324042c1c504112400150b849000d028060080004a10b01d4074000c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 38936425 1250 38935175 38935181
    0x204140402070609050a120215060d1704171b1009090f061a221508060f0a06051909050904030c06141302030601050402030c12040303020c030d050a0528 67
    0x380f40714040002d000c00381aa541400c1039074002090b20001100c0c54072100140c3c050010020081503006101ca00349402c00008482c5070700600c0181c07211041d0740d040e60580514100300e602034400400034030803900181c400c040d52107142d455107030760002240c080c1d10740c20300b0130305c81007000c41d90700742c0b10700003d982000c0a1070020305c0361812060116131600000519418ce0005541c1e2600200b420980c0e1020301a000e4207010721540003030a421100705a08201e04540021610000c02103450519001c1d22003800203105201e4a00d051988000c000d000001c0250f00000140b50550801d00c0c001c900e614000c070240e82c0b50705030303210b410380044950002500092003008541201803150f1030000346421004521681180c0440782100002a502010010340ca000c01c041401854119402d51441c50950308482803400b940400c06507480c44100031030100341c0203805a030403100c01c9500300c0340c5415908844401602040c0c03070015500e8030b00000300704405488104108940090a024825140046514002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 38937675 1250 38936425 38936437
    0x3020d030201180308090c0d0213020a0e090f01030507060e101110090813080a11010f0908060a021209030705062e0801020307020105070c0b0403230c0f0c01030204140402 75
    0xc5542e01e0110303c0c080344424070850003241c02a9030321840791901903001031420400c030500902c646120082a40180e99401c000c988110102030701607203985143d001614640b020295041e4811800b104010b820b000c45000030381200d005408503484d580d515101030300d070300c0820356260741c200401030140d41e0a10701644858140c25050011030b43c01180d16070030f21084850040048552040c0040c640b0b0320b0f0050b8ee021000900722040207812265a070b80c0d64170354402400c0c0d005078107005c18141450040c80c09401c40400400354441070f6032007440c08500b00e600075484111001c00345803c46020030f0300382c0307400010b8509955100c8010042a15190641c540100c001102d41d00ac02c4089070b112101136240b580346000030b150007800940c890610030b501a09565008040b14104030004a006000c14611070449401a406007044c40301501550003420200780c0840142801c40300c000351452480500046050310180c80f074040d01c1411404000450a910451184600844465800b40d10924282d030080c03034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 38938925 1250 38937675 38937677
    0x702060714010c110607020d170903040e0901050603190206070b060f040603050601030507170303070f0c0804081c030e030d0203100806070c06060902040b0f0c0a0b0117010e0606090103020d03 84
    0x500c568007012020700307648110308000000f03038211003002140b11007001501d41200890020340084d0080e1207004142d8020302401c3e1241400d6032000c50344403102030040307074050020401c1109092034500c0c3c080d400b812043d0740083c0648610084c04041041221500c1091079000304814a450703140c0d2190840c10f00003030000c0344d20420781d554400c110780e03503880380c50025481503000e040d29626506052741401c0c2d0350b51009414000f190841100d8160100841c1e90200090a2484100000840c121000c039404040209010310026001c0391071080026064201c160f0200341e44200054402c048003524401c44044840768000e10588000561980103160f01400110119212943d1a0340382c41c6070810070b135030584c007085a0448070801c3c4280c60080744050240200d065160910300600741c0202e00c90300d0a24181d0020109000503811000c1c00000036258205101c070040c0e50315410307030312903801806104894031340c640100e4100e55040030500030311440d0004c00716206686140c00b401248030040200b20 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 38940175 1250 38938925 38938943
    0xe0103090501060b030901150504090c0b0f090a0b04080d0212031b07020907080f0114030a120c020a030303020307020c030c0307030b1f08010903090e090a17250308010e0c07020607 79
    0x1013421085040514400d80c1184004200210594801600141e03550007090140e81816205c4000c2013882c03903044200c0d01800c0b1540e0b40d894000c1100442402000c9006520402da0640060500036040140007903c4550083d5104440144020b0360b0340c0c1c01c8584946d003288024400121040d19441c0740c458202050203805140204590020340d80000442d60400403400c424280881140300802d202e024145103112060741c0c408000021b0359644500710000d11000781a010800c06610840c201c1c441c60b82c1c007600d48040d003901d928010740070703410803580742c00180704410000031a80750015540900c4d1034040d0150802c00c0c02d5480d404a0400010013001020128030b0300001c0c200c280040f124010410f0f500006288103413850014422000d95120300215400c9a061140100003c0764444400d80c6c410300910380c2043d06041241d507405524130502601107890174800c0c480b403030709440440c201c0c440d40d2214900c1c0c0e2144041a03841e4403e4500c201c400d10f051084030014200314004100450280c0c040e9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 38941425 1250 38940175 38940179
    0x302040302031c080709060203180f030318040506060405060414010e10020604050c060f090d060b0d11130606020607031116080a08070201060b09040b04060510080910020304030e010309050106 84
    0x129103003d0041842d41c0100e4030401c4004001540008540d400904034139107156080c0c60854025507900400301c4803440001d440c2c900c0302e601d03942e096540d821041d015007640c1d10b0340000050340c60111900d210041c09a03042500003184d0f4500317071003140c00741c403002007603141042e080652408100c906c0440309810b1182007101004035a03100807074204210119070003090107140c90316005007800456142c0c2c6018503001d2000c1054282048150b8404810555007040c2d41010780c02c007138010748160340d142a04580ba130380d5070360140811150b8403c000c40007a101170303007000fa40a40840c1102d00301d00c107060042e00301c1408250802d105c0d41284040c014010703112030410560034128034020030302c80c204a031080400582c50100c6504200034580c40781c03144c00200318123444d1800f030784114491202400c0c804e079a5020190042e50700c80d403001001c0c00f0302401440f90200d00c404054903100040d10340e4561880b8184803619002c0c034074022284515410390391220554441e00041d40500201c0300101c0f03880d500e4801c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 38942675 1250 38941425 38941429
    0x13060f02090a0e0103150203060105220314010e010e0a0302030a0503150a15020d09050915031f0209031209010507030e031509061e011d0c0c030403060f060b1305040c0302040302 78
    0x500080e00070f4003410b0185500d549012940c400508016505950040c0204002a0780100a69209013100c00e6500485824000000c28140d402d40005102d000402e000a40c8020154011402e40b4080c20003005081d03101400a0b43d43c4841100c0180107034400c208005203d403041d005150170803000c402e120008003140d00020702400031504240d00061141510000095041040d91286d1426007000342c05d880c10040481d40441c0002c04035a03849100b00d1400d680f58030208030890301041c440a80c5054039070300500c51000b9502c080c105c64403c0c4280012004281404421514680c0781615103500e4541c45540c00d80e02c1d00400391106a05000d80404103121085505100c0c1c4160303903203006000341d4a031205900061070300c00340f0044003426490300148200300d507441c482c002410820795011031590710f60354541100d108120340c0c0d007140d010101d0000304000d001d03003025001c0f001401e0103001c042d4664034200c505010b180c501080340150032008200604080d403000d5035102c498a400352400b516500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 38943925 1250 38942675 38942689
    0xa0b0a091b0318020f041802130501060908060f0a110c0f161a030a02030603071d04050706030513020f01030f1505040501060302030c07031815050d110313060f0209 72
    0x5101000c400d2036100c101100d076810720407044a580350414482c002c640f140c0205500d10180500c0c06e010b1560b03204440d201c10803d2105e00e6102e580182801c00d501c02107038005000d80380c00c1c800d1401040d040d071000326a40e00c010407814411300c1d001040c200b00780e486021403c05030029420f03c5c0080c040402c860088201d062001c1c210799401c1000400c0c468051101c1b040226031150700c50341889240360701c48800340c6058000c407900703c0c020000c09600c94450b00002800c100d4154065000900f903444040740c0baa00c10094644100e00a5043d10344060b520042603050350303402c0300c080b40c03008107400c1c624006140036a0400178480e4107240c00107100b904001a5401c4076070b50302184014541c0c04204001c50701d09402810b000d0041072170b0560540c20602091041c600401c0d000805105003618044c0360003125112280c020941d0781002d2104540b20140a40345a0081c810742600381e0a00c07004000c201d1402007183d020f210004058480600f59880c1c0d00014601d90b00c4401d40160200100c00c00e0b030395804 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 38945175 1250 38943925 38943941
    0xb0a0b0301090b0f0618040902060c060405060906071e0c031101110c0f0d0c020d0f0f0f02041a01050301090c030608060103030e0a080a020904060504050a020d0602040611070308030a0b0a09 83
    0x300c006641018102080a18030f013813038005200b45d0081010700469040084517889030903065401096034042480002d1441c0100d0300c0c00111485175002b00000d000000968901510780072050b115140c40f080012100300c070f2841035007054a00300d820244041c51042e42112421030081c6003030410202c1403400d03203082d14400e10f0040c00450000c900401c601c0d005000d91b001e000c081c40d008004e0505925005403c1e41e1041c080a8801c480040d941c03014096622541503466074000c4070180c400605240645841c6503070322003640070318903000c114a0b0914440b030441c400443e050312a1825a80f9004902000d0001e14440000f01901d031400095460020407070240690711907180c4505a0041c10103000c907025980c6e03c0700b91142c0c071030b05080c1e01689034202c5440c1c01a8000e04042013603620703420030070300e05140500d00035004507051044806001480e4058410b44140d66100140350160074881981d8644500010b051a0b400304040350800410380c0c0411423150f0080c00450806a03501c10003401c0781c40c2c030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 38946425 1250 38945175 38945189
    0x60a08091c0809160e0112030c0f03080103061a0a2714060103240506130806070c0501050c0f0f030919150606050c0a0b0901060f0b07050705010e030307060b0a0b0301 73
    0x1402c1c0703e5548030a0203100452582184101100d038548000c005006070113200c0c80381c4000c800e072100e105240c840c0c0701c00c92580750000f8408100c003a0398500104480424030056521501d00000104c00d01404220f95400060042c6401c400605108500070040e94407980e00e42c402c0850001000d0f102060300800034000640c4205103820b14000001500307541040002c124484d009140180400300d90618900a58000350781c50740c0c031a00c20568130209024190040803c500c41d03442001442035208210394000c0344103200030310a507120b21181100b5406100c08403102d01000380000c241c42000038003e107500082c9081150038440029014400f242658042540c6044812054441c20034407801410000d00032071801c1c41c9006c40d2030070350075241c02d140c01004289410640100d182c0c0741c4250841d00240c940000403a2055640f054a8a40c075841080110381901515000113907030360080080001f0000050041d52601e0340719583c010041426002543e4000040e000c04a1008254805140070781740d8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 38947675 1250 38946425 38946437
    0x103021c05060f09090601062f030a030b0306010803070303051b0f0a020118020d0201030e0c040e010b0a0509010b2a06071d0d020a060f03020705160e0a020405060a08091c 75
    0x400900007010035010603140224a040240648240e0000307586c5c2c11035030b2511b440808011703550600303400b403500c08528014204808003150b00c522004001000d042c030082d14200304160b00d4000b495280ca41c00d00c40e040305500b040c040000402d00980107207a02c0b1080c1600760354054820300405203a03402c01c1c08451403002c0041404101980c0900c1107051b913002c0c02e0300468420403640d00150f206180c0700d0300241059169202c00000711010400100c0c014801442481100c0a000c8030a000705134007507886100d04903500c0001003505285132003034180c848220b1068503000c1c010035401da80241d5024030340082035400040001c810002c1c07003102d0241129684000c0c2d00c804e20300180c40001d1400310f906104407028181640140d82d0201d24001f180d07003600300b1004250780c829003035000b402483e07809401d03801002ca411203692060050403081d21213100e19490390b0b44407102640704074000c5005e001d4001e0010000070010714041d40d0030fa50310900d20002c842d249040207107484403d5001864000200320 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 38948925 1250 38947675 38947681
    0x3010905011809050601030609020103020d05070203090310020315010309020109080303040b060a08010209031b01030b030601080a050105090a08120c0405060c161d1807031407050108160509010e0103021c05 90
    0x1000b07410241507108088000c3c44604465210f454035818180700050220707954608643c11640642c054508a0f1040c3c00100660300e03003540b021b07440344c2c0040b03c1036100740a100c1c3c04081032810f03882a24015a0b404d80b03000078403629500154000e086025040e818051440b50001c3c07424410402076100390b1040000440904006040c40390600303480d00f000701075034018004042c0700c0d20001034103080130404c020100060b03034208005170000d100980c02650503000d004000320b0f0003c00084e8007480e00d80300390020062035413188040341e110322000c100182000c00c100100d280c881d240b03100441d0480440141140380958800001351035034819a44040340d50450316070350740050700c0315500c04020725144595421100805204403441d090017003100c1542c030700c8046400c1d0382c4c6108209401c051540306007140c40d03002c5e2401041d5603980403845400d0000f03224070005410380311841443c06c42180b00d0b8603201d007031080000054803074000c000101410582c0c01c0c80801c90f80b6000111240a054000e170000485007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 38950175 1250 38948925 38948939
    0x11030102040b13030213050c0a0c15020a020109120f020703060f1401060e010801090203010609051905030109030207150906140a0210060605070b060609060a140706020a09170f12090a0b0301090501 86
    0x2100c5111b5401c0c00d145400200304065100400b00e44100c0c8541c5400c6100c1601403415032852446000300c880d140d40302080c5600c001c0c0d0154032070b41da202e028100204101201d00c0c0229402d140311210100140c0100d44104001001074000e007612204821000c1120003c800088454070001d0b0702580014003d480d0074841540c01204160140c180420103516540c1840d90103402c12403680718050290540d12091401701c0c0346a00642c014000c028002d000c480e10340e05009540e0000383c069070305840d071035201000085020303102007002c6601c103407201c0503c00b107031754002c90094120100340400d50081e00044940c3d24158407940303005d0907190301c403591510300780d0134003440039540200131600900d410002889959203000c10760f503150345940740c1100c0785024508030140c0d501400307500410b0b040c0081491445140c0151161040d40d03803454180301c400003000b0640b983c47d04400c440072030a070010800d40b4103043c0382c04024004c011014081144080c3e0b103c80015175a40240e11507100145c0e02c2e00144200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 38951425 1250 38950175 38950189
    0x50f030702240717010e0606090d020402040e160c110609030a1506090e06090304210f06021b06060a06030506030307020a09140711060a020304031b061b020a0308010311030102040b130302 82
    0x44d416201d00d010166041400c01c151495000d84628800c54022664034810f54403120500405079001d4400e5450b59070740c0348401828501030302c1c94100103036a07681e060341e42481007000555039038002c0e406585810060090101e90b038095102c0a1301401035011510202c0d82640d10400c000c03415000005100d403403d0481403c030f603040c480000490f04060b0500210000c00810b980a55500e00885103081900c01480c1a001140d800014502c8922882c950700f0700c01c2503409000701011154081590342107079680039407103000480350180d02245021040c442c0340d01c04d610041d130040000e000c0780e181c40c01a03000280b00000e030b80d0040e141c264440d01c10340b9140800840c60368109110b42402d404500c60703400c40c180c03036100081225064990110008081c075118a0440c442c80714110610f00b00c24085003880c0340030708020289881d142081c411614905031000070301d41106c07a09a82e450342c1d164219564004400c0041c2c0d405c651564090001290f00d850120083c02c040c2500303214081080e14502c148040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 38952675 1250 38951425 38951447
    0x504020703120501080c09060640050d0b130302190501050907060e01050403080307020c060706150b04050f01110c0402041502070806190c12020a050901140703050f0307022407 77
    0x140313412540386105651500b11f42c90f600580c04481980d159034020394843c440308100e08115082c00c0c14030880b10510074440740107080029000341e80056841e260001d01007155440c28006150404c00c4001030b0303040e07000940206946120344103440d10035100700140c5480c100f42040603030b0283d549106004d002c12040044000900d902d0800180010b25200060440e00843c0720252072800000b00040c01c140c4207102c1244c064130018840398680c8000d0030400c00401921120b450404601140401c580003c2c4e0180c0d0102c40c0000c1c108034422450034011a04141c45c90040c01c07091007041148640c1e0747d92800039001619286e40e851101d0141194000e1405185901c00803068000c03c09004031400846034006040c012008045000301154108840100c0f4200065929a101003000c00c1090b6200000785800c00090b80e80011080e51404034010621481200402050b010800f245643c000000515480b034183e00544518000002c20340c801c01320b419006070501d1004404000c502c0b42c0242507004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 38953925 1250 38952675 38952689
    0x16080a030b18060d0f051617010c02010905031b01020d06080d02060115090924060e0111010204050a1203050c1002040303030e010c0c030e190e06150304080301090203100504020703120501 82
    0x41a81000303c0407802e100c0c580c0d0005403030703000c1074001c207414000704100b02c9003008001c011884140391b56803200c01400c0080b044400c543d50030840402100d500c1402045080b940040c081c0d490034040c00940300e0046403055403425955003d11a2500100c160711802c03009041c3c030030141940041040e07009007804016001201a29104003991300e00c0713903110701001c0581c0d00e260000a006450b4400700c04200c10401c500e40283c40b80900003060344c0b60303c8268094542001c1e2107000309026200807013420703400789000d041c0c0c01980341b0004201036102900700c002114000c2c20081e1414100840700c60405401d0708582030000d40000f010400c15500d84a21000900031030001c002c1c8842281008203614081e1002a0070410b91908218003035640e5448081145401a141103032950703106d40400c9030110840d00c0e540709541118540300780408800480f0721590b80003090514582c00c043c0c0d0400207400280c0750080004c0c004d00049030325240c910042c03188600076183c1d2803060601c51084410b0303d4050304500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 38955175 1250 38953925 38953969
    0x1020604081905040306020a0e03010b01260601030207050307290c07061a2106090304030c0905040c090207080304062009010503090307060c0f030c05030c0f16080a030b 74
    0xc0041440e440a0703074207080124081c0040360960080407540d601503600081d010070310000c1e030102c81a40084481441100917402400108001c00041d2512009141101004000c81500004c0d00c44801c03060380e03005805040060030b2248a4a800d80740d81c0280e1400c407102940c4408a50204040c80b2002c1295034604004070000d01c0e1003208030141c1d00905070000c00c440d0b200c0c18450581e002c0361a55007400303203001c0e207403044481180c4414014548501c544c691540501408141416004412035041d80d4101d06012242031500030100010080140165101100707944046015030041c0001c01c20b00f8080d10f00c643d01c904040c10600111450021200080c403100600310302103e000340c056486201c02401c160b03490f540c5101e0054154403500000500862412900c00300403508041d90001442e00396404001907020404d05171003502c001e0f00c81ea100c4400601c01c090080220f10024942d10910200d40140200d041d0b1ba00c100307a400800c050004241c8401c004c140d14200001843e00d02c000c001180 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 38956425 1250 38955175 38955181
    0x612090809040509100e0d080109090b070f050f03040308090f010902090a0f0608010c0915050a170a020c010c081b0708040501050c19060212060102060f0105060307090803040807090b010206 83
    0x39011403240014090082e03844030b0020f4800e031814410700c1e00078496444180001d016280840d0303100c00d0154002c40102e14220000308a0003042e10a81540a5104a20421a45440f0011350340030340856440e800300a41080034156003a50341018501561080e183d03010107040014000f42800030034480302a19a151224810140e91282911070304101010800640302040944900140c1100d8010b91141c5d0700f0286050481c5501211400440700b00c140103011720280d0318001c031000d10903184a5000242403501c0c1c0103a440c801d0814540040d0007a90051421402190907400c0d5580c003400c0101003a05502003080c0398804c000450301000001400c1444e01c2e045a680c548075010f240aa14100079001c103800000320410440d00e00300da1903214035154055002c3c0b81c240065804041c041415401d0319012031007650002408038054803c800c5031443d00c0c1e00b0b29003440035a800c02040c503820482c256000190303091040c002000500356000c064080d8506281101003560342e015138142c1158030903810 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 38957675 1250 38956425 38956433
    0x1006081504060f0b0a1403010501170a0206090d05061e09160905061503010305060601090e0106020c04320906090303100308090103060b0d05040203010608010509030a200601080601061209 82
    0x1020740d220b64080000101850b10b482c281000304600400d041d04403000c01c0001c1098044504944c003e002d003100240041c3ea01c0c0c485520300c107224180c030714103141d02c240800e00061410b200a405103140140008112803c2c644426191000682e4104c0210b06038101c41c00c803035000c076101142d02102c100010841d070410441c6038401c40c03400b846559004c0d543c0710007181003550f48003090500d807016008810380341d507103a003007040d02c40b402a01c07039501044000500040c0f0b0380005d96070340d040750700c240c0182221108410a010251441d082149035200022031005840f18848062000900c6200c0714000c180ca0b013001c5261900d0030250800690364020310821000c110101c1421094030f6000301c0060300d0f0040c1400681c0a0f002c0c941041d900c000001c00e461040001d59404648aa03008400900c00300c0c0d42c846200d400c1703443c240c0f41c500441d0410030506121034080e603c0e40000e40030f03580b252481c640c04400454100802070300300f40310310b4008400401810764405414004c0424042e03003001888010740d2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 38958925 1250 38957675 38957713
    0xb0408091206070203070f0807060603150f0c0905060a11010515042a180801062d050102030a0c0804051201050405100b09040f1104050c041e1404020702060706020a02100608 76
    0x50007d001c0040d02c01c10f9001c200c4280283c170078080d807001003401016200e29100101a5256019080d09858925012410b0006018001115180d501c41c1c0c0c459605100521503030b6030000b0981024070120304540c81ea0f001091007a144906140702e4940c0a0154540c02c02c030030f848103607480c0d07a9401b081c0c121510514103031240c01c00010034681440501d0419411040c1e44540240d400504a546060380001e43c8e200c19844500c07840e07039141001c034005010802c520042e00514022240143d10900422400354020100d0140303290190b1900d40c1010ba48600140454140c0c072002e01c0903175160400d20080050400c6100c000d4a03403844103004009140e0042071440c200204040d00c1504541d03140414404c81241160744120098404d004a1409a01a85071035005200e80d84860202c8464140d01d2140805800241c2d0780da9443d0903403d469000401001c0d4001c84405c0e64407000070071050000078403910040c0340d004040c0d0040c11182c544440d01904483d420303402041e41c0c0d0401140d241441010038 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 38960175 1250 38958925 38958937
    0x20106090501030b0708090a0f061d06040b0a180b0108031b0d170601030906051303080a0b010509061813061505040305060f0a0e0708030d050a060503030708030703090b0408091206070203 82
    0x490040b035959561a87d032031800c410480060f00c1c0906030f49800c014460540c01000080d5001a80f0f02400c2030720740d441c59039503042110081c0440401174042000c1c042c0355082200010f04010440c1046921500c0e0b05004050030303072080007254070000710b112081310201e8050011100c03034405406c4c100025500501803140c022001c220401070381001400c82c0c1c0c02a4082000107402520030010761514400b401000c224655040d00070550440c0026103050113405440040101a9101400c1502d030106000017500104204040c00044040100441e11030206680b40445516030100d501454003c100124007040415107080003000c200034004581300103101600200e80c51300d604440e83e10440c0040042105541d1a5000c0c0604c0c0317030004134580c000001c0c000c03c03004000200903e4039041460801c80d1001c1c401e00381c05410601900c00030484450141d40d01424a084c0442c00d008036584450b505002200c045540400120b440e41e87ca0408a980c09001320844006185508220380003039600c0c0698 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 38961425 1250 38960175 38960177
    0x30b0d03030b1507080a1707020a030503130b090601090f02030f2409070f2c01140c060a0606020114071409040e01110301030b09030a080a020a0e0a0803030601020106090501030b07 79
    0x4079560105511000004a001c410300343c4070036180c0159141003006948040030b0031000404450100a0b000d803400802c90152100d45c0007001d2800c0180c0e02a19a900020551000305a8030019080800c4a54400c10304c03412841d0054072896040600220803944040080702101d441401000b20040b22100d00b00d0700000d43c040704072550307035182d2040c0142d10f555000054000c140c01c028031019640060060380302e035100e52200300d00b010f104401c0100c00d0034400703141111400d44403640e0030f065001d04c0b9a2140490045c0000345040241d1181c80d280c900107580030301c0d8079556000c04100d000d07420f1045800020403c00d0f82d20927801c02c1e2078002d1000007900c070315201040d00014508080c1d941d55100d04031008161000340003401c284851404c107900700340720035680c0c58009030018a0b05507000c000c54222504a1f19411156110207503600001d40103e4595010f1100303020b81c070035541e500d4041440003001440025980c80c81d0580009080d201d456125040c1142824014400a80840c000340c1d801619 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 38962675 1250 38961425 38961431
    0x60510140a200703150b0607020a0506030c070b04030c0c150210021606090c03111002190201110609070321090308210c03040b060d1109181002040e07030b0d0303 71
    0xd040ca070b140b10103090080c90006110b2100b0000801040b4011601352200c510420404294020180406803013411402580700311240f8080c4010300e0424051500880c0c030b12103060401c06c080c4e0341d126012100351400d0380404c00c065040d004004645c01c0e030304040c182c0c1f00d929400c1418003230006903076444203418400e03c440c0c000c00c0c11008659681281010107400c007d040c000d01840d4105569104150300003510420700219950b5401d0821844200c080c4896a005011840c030700c1044865501003e18201d04100382c0c4103c030f1012500412103903000741007601c00340ca002859403421001c8400d84401603800360102a080301100707500010703806d04584c1c002c40c8459a80d02030340507040302c2d41e0400d03400b078114007024400d21442da03402902440c4030354401c1581c000745450324030030040d440341441d100400302e01c0d50640015050814003001508a1100e2680050704102c0d414244c0c14007010340c081041442e40803070200a940b40c0c02c6000c030b03004a00c81c1001c20151044001041e80c00390325490240515031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 38963925 1250 38962675 38962697
    0x80402090c210619180609020c060403080c0d0c081501030b030a0b1f0f0e06010203090a17010905010c0302071b0803030c18100302030108010b01140a14070206070303060510140a 78
    0x3900940b00d100d03295110103a1600c1341e19900401c07031004d0003100a20750035107800400b0483c0c1110384202c903100c854205c0201003039607407030b54100d950307500050011001500a200802c51403400c1d00032009111001e031541d01c0780d89403603d00722880c0912402020f04140c01e00041280a850126603001c00c4e582091061080355034601380343d004c0041c02c854814500c45c841c200001c0c00b41c120090b400990745403014044036529400d004a95900413400d00035802281103404000b078001d07c10f84038580f02740000020070811300035140c03a421079052582e0b01020a800160f02c101704200700091040125000180040c00d9007040365941d0b803808000c010200e01400010701610a401e0b13400a03401800009004150342c003034140c4000c000c0c1d01700703108110881d0301b81124040c80d980162030300c0056099480c851400d100b0510021102c5030305010307074007842c000104451005612040010050b0a000752800b2548610304800d0240410304010381c0010010095000c0c8901252807044411035041441c00c804c01e42 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 38965175 1250 38963925 38963929
    0xa0e0306070f0e0117040305030f090606061803010e0d05090a050102010221100b0a0c06060603051e060f04020d06080705150901080402060423030c030304050d0b070c08030106080402090c2106 84
    0x200e00c84052800300d0082402c20040523441401144030b0048080700c20a00c0e01c503c00e001d5940d000583c3c042c0d42c40300b0305100c0c41032042c114102038814420024004030780c590600381010b08204080704900c0c0001c0c0c1c00aa1800b02d410304560300401018288000c500d41100f203080d886108074042d10b00c1050600c0440483e001c1159030322a20007070180c1d4031038680d03100240b023805082d801c1809001c0b1000d5062100020b00c00b4001d00c00e8900c10b40041c504202c9841c00c3d21038051082c04024403090b4411030445015400c1e86403840540741c80c00c407020300002ca940c1880034503464105540d100d40e1098001c3d50104004010b403038241d4100c507a003820329011a031102d200040050041d40c1016181404c1221804010120300c00340203204078094003607503441c6a1036800d02d51a8070460084030740201150809000041d0f1781540250700440070301d80791003051050764441c0314660003a80020b0006a000c0c003440154035201420700d40001801d85900e29251050007000c0c440f0207a01814131080c1e1040c40000c1c41a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 38966425 1250 38965175 38965187
    0x50603060a050a06020609060106080f040210030f0c050d1104060c060209041d0c0a050a06021509010f0606050703080121060c030905070f061701260f10020a0e0306070f0e01 76
    0x5400b004203000425600d4684c002c1d5180000c44101d6031900c01c171400080c103030b405040100d002d82d940320ba8031a510f580342e40910600541d000c4c107000405941300d022444105081c41040e407003202c00d9907219561003440d0a40c0003600c81a0b80c0c00024544200010012560040c600002c003d40c0b1500150315604a040040c00034504880e410455555070807208484a2000c14901034810084401c400d00030f4450090007800c0c2954050080075900c400c0610360981c000400035984844400008100c02e0007044001c015981503510000100d080031a86c2010550428042405041c40f0500b21500311440050741d4042ca1103c0c0001e02003a0351036190440c21840b0760021000309402404444c2e4660340d408144900361a10310070080012600840720105a61802089040380c0c01d0300101c40c3d2078850544501d04072107000c85502c400e0b114207404a200501300b07100d544040c4402040068070740356452400b5101541301003010f4070a4000c00308020600e50800344070b901035281841c102d185044160700607500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 38967675 1250 38966425 38966429
    0x3030f031509050a050f0f2a0c010c09060c11040203060d0606080706020c010e0f0108060607060903030209090901180b10080109060b280b0f22030611090307050603060a 74
    0xa1080507400104010010790000c0d8040c007203200d000c00ca2607403402c18118544505560340013640b8a040041348000000020140b80040d008000e40b900c4c4510340e01c0b50105600c03440b0810701c00e0351212580340d166034000007540024041c500305001e80e002d941c1d40d8102d04690081442c5c0c403aa80c0400403075102c0e111700d855000d007503920410420140d03444120361580c44041d84114030051250240d00301595210300544044140082d140040c03044040c2c0045d81c420100802040e00003e09001c400040303243d50107500c0040e4001e440059030380101505101c15244000c2c4100c00b140ccc10400111503000300c0b803070780c800032940052660b0819190b00304008054200d5a003c05003940c00d20b00d000c030500c00c40350700ca4402c0c40411074025601070300c0b502c00c84005246142111103030000c0b6280c10440403411a00070151000c02d00a02403801c81110300800740254946003006d0450040002401041020705c11499000c051481441c1050b0328400001d541e0815802054000c0502002182c1141c6507c030441c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 38968925 1250 38967675 38967701
    0x30712030f14030702070801050108151504021603080103061107020603070e060c0f0304050301051506030a0504030e0904050a0c05031c0309020a0f030f03080c0313020904140d11060c0405010903030f03 88
    0x140d42e00302041300955901150059031140d5290600015071140000b03141804001c4034962500c46548413550340c9103040c002c81071107030001e0b000c006003a89003807076101d0400b880c1d200380c964003902e5045013020000c0300e8052800e0761001004005a41c09a500c02e03069980c0f01c28503140c03d0020403640404500b441c01041f8548e80300303208101c40c3d18800c800c084060300596009900822641d0b0322036407401b6282c1e03202c1079160b80050041001c12104a80398000c1c40d800350181c1816021004504046880074000304c80641d407039004050b1001c00c000300d48054200070f001c02c0b00141040744e0b000c00c02d102810203c6400109050b5505000c0d01151900449000108000d078081060a070faa8180140c0440032160103e00151006002440340c800501c10f40b8010380200da5508208240c80d401e004003031b54050015030317601d80d904801801c01082085054060342c03680c0d44035030901d80f4400c811071508d200030308142440c520600c0144120390b845084601203d4141c64580c440008040d000d40c001d00b120b0603101c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 38970175 1250 38968925 38968927
    0x150b060a03020c150112030c03020a08190f0e03030405011b0f050606091605120c0c0a060209040b04020c0606090c0f04060c021003140420121b030712030f14 69
    0x300410360940e010b40f501207815020f485000c0320070a06840c415800b400703110015000801c40c100401d00c11034828000c0e91080c011614041d00d203465032020b50b0007024010301d444d4400003240c8a06540038450010b41851814038030003841d041000261a4069405182d0400901c0c00702c00b0607241b80a40c1a00300301d60070100c403214406103410051b13168407048a0880c068141c000120300ca000c0c1c2000d9100d010900c03a900c150500328107815070751540c540903001c6056500188040c4807040300904c0340030750561080b40c005a45010310070a04c000d81d40002c50007440349206012031044410701103669a80140700312046c480340e99582c00c40e20300d98010140d013000741003070100f400b140c4550050358069030180219543d10001d140a2421426038000f0007502a42e05140f03400710700081c02c400410701144040600980000e03400501080e42080c0b4008d0009840d40600a001d100729405805001d1120f41500540180e0741819000c1d1000c0040c84801020400c2d0f003050f59150714031407410102d003421090122 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 38971425 1250 38970175 38970187
    0x2030a091503022a060f13060c050c0d0c020f1c060e030712030605031009031704020f030a0506041707050d2a0308040201020f030a0207061803060501121e020d150b06 73
    0x26510241d511303200030000f8070a00020030f154034420f56800384105020741c65800c0e0265156204c0010745480c1c4961001d0000503c4100c4a0000604c50311b00c540300381d6551800b401c070280c01006450002c0d90501801030003554a07131044502035036141010250012004a14034040c9402e4901e14459003101401050028030348070030030f40e4560030040848604500706c43d0f0415081c00c01504036a580a070003000704d44c01002107004119034540f080e511500003031015041e564404086820030140d01421110b23500401d08010800c03074240d01400c00001142e20031410701030903036a1a642c941d055440e02051044035801150b80711400000a10f240ac22800b0f00d801034005803030017800d0b00d04281c42c12405800380361851503548500200f40d41c42c00e80284d0052407802d19040d0309403142d0144100c401e040d400b900001201041d600e004050080160700200c003d00c0059003070001088000b800100d9803001403000d250050b0381c0d52240e00b00c1340b40e0028010b2800c4207464403114000c0440f607901681150b404140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 38972675 1250 38971425 38971477
    0x110406030b070306090b01052508040b0408010501080109030f12060810020a0806010c020916030905010237090905060402090a080d03061205070e1e2502030a09150302 73
    0xc894054190ba0710203212045d03e4040a41c2561100011070380020740c144401002c10f41040c551510840000700e21080015440e203513650658020f0b00410f1100000080410501d40240b20703090051150b07100800000034540c0e40104044908140c15080204038102c1c01424446070388160010841902111004110800b04e007004c0d401280c400404110060300080040d40a501d4616145500404446295489080055201000c000c41d07404050b5940040c2c1c0001d0000d200401707480220032480c012034960901c04040d03908c007078070081e5031a040d142d01c1030b8403040d0032246030000c1d00c021480220700f0fa601c003c04103009014107523015038420785400001038034406c08600200140000e42d4180041e0b5200ca11050780d0761140307500203010342c0c0404820040b03e1003180d00703540c00540c3d001458440300d00409540c100681c05454200401e55040e0024150680215008030900c281e8006542090000d00019140c10228402d4400d00040340c410030310b4081c03180e4110303901681c0c01070034070301c82c2c85008030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 38973925 1250 38972675 38972693
    0xb01020f01180c0909050c130908040806011a0403030203040506090f04150513090209060d0303090b070f020d08060112110904020f04050f030c1011070509040b07080f070f0c11040603 80
    0x103003510499030303c0d900800e6002680c05402141508000240300c2e40031504180b0804c07060b100b00710b01c4416a50400900001c3c4607000070801440840300030070300c55040029400c051501c030256106c03189001c010820001c1c0d00172064070100d8204480b0182c0701c41c44c107004140798a542245941c0c0c480e141860820b006154400c1e00b4050302e005480180407070808c1d40886080304c003170b06070282d480801140040c01902d07021444a402d21303c2464007141c540d506540e08041454140d03020301c00b251800010990701a8100200003011120f803400c00824240200060070070005c040042c40b00b11744500903060b42c80030050071200b16000c00f07441155601d80e14003200c1c685070880d000c0c05100341c3c2ea4a111004034540041c00844002000b00095a050413521040d50820b03000142c3c050039004140d00021159508900c2e07912860190b81c0e00046450161401485088000c00b11400c400d4400144421194040c47e080490b00303190504081d10b4815081c040c11242010000c141e109080000200c20404111 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 38975175 1250 38973925 38973971
    0x10150e07030c08060a0501050d0b061201030c0806070206100302060a0c0c0602031309050105221b080a0b010201050103031e0509040e010e1c0804060209240901110309090a0b01020f01 80
    0x180c1d4a10f41ca4031030004004100d0003500c03603540080c0051004100105c8a84d10481c200342000f0a01c510340f00078000e05070034545e026801910b0380c00e040c40081014200600c8180c2d401031a40c4003801140c40c111004425040c0c0c035001c043c3c06411301041400105002e000d003840010703000700485450603502c1000070341c0c0386d1003407840c220520019000000e65400500503203040e00c03002040f191840c2586264042c0e0150306030401c80e006501c44a002e030300d6140e8440300c4400060181d60310143d62520b1034040c0165405c0701d2145045a00d090010400f007580705100a0080c13900e406001c1c04405020f0003100c0501488000c55032241c901a40c0e00c8400a05602a0318185c100034107a0fa5681549440c09100f950a800543c2c0814040360020300040c0c03c0768001d180154004064002c103201c0070041107104440b04640b40c40402000428000c90340c3c00c0b80440f8210b4150304029450040c2da4800b04002d01c00c0031b0b111803101a02d8240002c0f01ea030082c00803010080c00c1070020040c02d0f020007100d0706542124 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 38976425 1250 38975175 38975177
    0x8091005010e0105010207060309080a03090305070f06020306010305010803090d020f010e09090a0507060f0903020d0204060305160905060d02030c09040311030a120609020a05160611040305070e0105060c10150e07030c 95
    0x10200000c0342360080c040d180c4025007000f200e83c144682500e09802505a62100320700304001080a200054002c6800d0003846004000041e00c0746003841c0054211070703042e00441aa0b03030cc2401220429a0360190400065506456682801ca46040141d4800b02028482c65101e2280d07020054985000075203046194004c07030845003081d035102029545004051444000211035440a2000d0309203080c2c020b01c00c40c40a03100040e0b007540d039203c040c2440c22030320703a242c0401001c41d401c20a4400d00c2c05031a030401300403240c4840c81e1019a000a41e0f071a084220b0310700078014680094140b5015503a00e44800e81d004007070360381d00c4064003802814000d0b43c0c2510310a4501d08140418801070b1403007078600c0c460407516a90720300b8012034800f1000d140c1c4038500300d0700c2c242ca6019400044490101401c029807140c0000c0245a041480c460a0300c6016001540200d80030701c20801c51000014038241e0055a44c900082d420b04c0024207802c2602d0b55070030a4a0300c541903000e00401a5140d07010000440359 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 38977675 1250 38976425 38976433
    0x150a05090f04090c0e10090e0f0d02070f050d0c030204021b192a08010c03060608090c010827030304030807020c15041e0909050c030d0903021008091005010e01050102 73
    0xe9004000449080da030001d8842c90f02d0500501c5902007145d019908144030a0100d82d1255662164000b51641c1105884403504029007804419034200584505500c1c540068071480e4140002441e5424117031003210f01c5880102e1010b410700c007248061001445e0081e00640d903d28110144c10b00d2118152014180391040084403a0040e10313509821403110f40c001403500008501203112055524082002c90f180743e00242b000880e81824414003030104203a84000c80e100b031500310041c1041d10000c210271482d4100c0403840c00c190b0b901840381c0398001c1683d40c0c80141d242c1e855000c407841700b802031424140342c8000001e01c4181600180d01358803e009130b80c01c0b614114000c1061005106d20144541c08112085c0414801e2907280308050200c00811040301c100c0540d184000021380712242c800f6545908111000c14660505204c02d4a04d907586092814040b403640e40812000340002c0300b9001040304280100e2003d40041c486045a00303000304c02807005503100c181602a904081c4252070152007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 38978925 1250 38977675 38977699
    0x30c0b09010504152f090a030b011d0105061b0f0102040e06100f080402010f0323070305060d08070201080c07061a0307051c020f0120030d0c0504050618150a0509 71
    0x613050098000c2000c8610610b0300241d00000c900400003024400492000c6040c05130b18010788554040100960064003040129490505c011200c8001c010100c82c000b01100010301c07898513522f04807201c41040d000700f4034080012400c81d9007890001701c1c03074071803550000400080c010f030b00703001d034038041e000c05c45000002c8144002c051700c100d80324a0080010400407400207001d580210350b422454021070402054040c40f1016400e0705c00c120300c4015084450100c01c2c00419540b600c100c651045054940110a030041e0702e69010a0050800090410400c040080e2903142413000f924509070340007905200800c188041d0703910700140c00c41003134060b102c0c2100000b10781c81c2145020005e004e0070300140107241656001d115807000b0300d0700c0350303814003d03681c511400a0230880e440d207603c10003020285444082d6154114190303003c000080c0308000c5d05010900407039076800c04840c601030150400d54202a08003011600c00c104000740c0c0f54000d0f202051010402e41c1203401000b041d00b0496844c07142c11 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 38980175 1250 38978925 38978963
    0x13060f06180e190803090d0f05120a0605060c011a030309210307021203030709060c0305030a15051003090209010506040806070f02010b100c020f030111030c07030c0b09010504 77
    0xd11688110540c201c92a15101009161580078400108884007a14444224180ca0a0000c501070600700e40300344000003081044e14003480b040c10503070218a000c5450381d20641c00207120703008e802d0146000030002d0012070709640e1103511080c014100540155190407120303420b80c2c0206032882c5d0005080b109031194005515010003101c20142000300f0f51032256085d2000040246c0c69801810ad040c4001c100b01c00c0942c2d03c42d8402c007000e24101005560304d00c2d0890008181503119403041d820300c2410b407200300c00070341c008094070b6004904e9040040c07040320340988100b1201d500da00c415048900008602800703940f54020000c224001e4078040000d0340e0f0381040c01010701c40c900c81e80150360080f001040800e07101d1184040785081c6c510020510642c00b2000511440c0c14001940200b42500001c2c4114105590001c892000c214000c2164969051603244603103c0207090301103310f40010200708050040015813081500252424404e1a1802c4050700805050300d09544409481c0030850350a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 38981425 1250 38980175 38980181
    0x16140310060807120809060301030b011707030f06050603150901020a090509040507061413090906050106050703020a03030519020316030501080307031409040f020d14070201200703030603050613060f 87
    0x1e0342800000e10b9a90b04d484651451441c10761412034002d0010004088203580d6040514043e40c016180d4030159494100d00d0000c0c5a00c2031880d043d942c024030010008a50708003070700344d461500007002040940e0395800080c10301414020007010300610707400740a440401580507003101403c035200c0c0e940b0309031114204a21018201d60080c040d62201d6800d2120f603211718000d8407031000c0d0603609403c218041007021007140c951b80242c0b501c2d50303581c007800041c840c060107454014070450800700e10344103954030025111184500301030149034445e008901c600b003000041c880e04d280406011901c905112900b0303503a01c1200011600000c1c01d040003c034003d007000c17080310000c0358151030f280c141c4641d2551000494104400b80396005541d40204403207940280001d207542c41a060000602e2581451801204280a821841160b2414003030345203208062032104814a100103c1e13a854860500e0114054205500010024040c20060014191018103250702a0b81304035010301c200032442a0304411 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 38982675 1250 38981425 38981429
    0x3010b0a03080a030209060403060902180f04021207180501030b0f0705040608070201020904060608060118080c0d061d0a051c0801050603040c0b0a170121080a021614031006 76
    0x11040024104200040c0100003c2c42001202c2c14003500701407031000040c40a4006901c1540d0003038943c08902d00710300d40b14080032209160344400b03170382d903080202c01103d211900401c02801240c84c5000200031190401680c00140000164402d52140189a1401808083c80119044440301d008203901e2030200641c140f003500a6610142403500e06401200d44030f4010740040e00703556080001404944650003140c0203030815850746480f40c1400c4000510400c100000103000012050043c00003d80100d60844620400c03520000740c0c0303c281c00c0c500003c0040400d40710b0341b5481908918040403000c168020314600541c180c0c0c2c101400d60a00c51910f8000106030000a54410010b0003e40b408002564225000302000460076444001c250180c0d40171a210f80d000c100010700c0008594000040e541c0500402c0e25402e50540300d800760b240084898100082003850302161802c015842040260501385031a8a001c400a070b944c25410301d0200c845600c1e03070080c000c0344248180f4400b28061001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 38983925 1250 38982675 38982679
    0xf060c140c01020c090a0b09070f0219020f1216080a1203020a080402100c0c030b150a0503030d020717030106030516030b030d1b060e06010f0503060c031902040905131103010b 77
    0x110101080130031625201c010b1400c1d407450b42c0d507007103840347e61110006244204560f440d00403c4507007907800a841c040741c00e50008800c01c040201400183c40307403c800440312005603100303001030202804003410800c1e0340e5043d40c0724601c4000c001a19507000100314080302d01458803208050309140e0120243e11a011103032020071600c8012400509100045065100c141c0ca4034200500c210b43d5105e05a1a899005444001e0600d05024580d28507002c0b0740b83c040000c03a0481c404501c2c040100e5140d008241c000907105602107244000d00c1010441c0d451020380011000d96691f031180000340080000340c8c0d1190709942e840e500416424000d21074001c034103000500814111031b43c0d4000310f4114004488e54108184043c0340c050010302a80984be119a401d840540b10941c10007d02c14190080f5900c218800d52040041c041e40030f00c04011290464164031000003180039981e04030019104a030b0002b852035140808100007031100541c0780313003040d128003c080d50000008081501b41e42049528035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 38985175 1250 38983925 38983933
    0x1801090f12081c0501030611090306012d171e0309040b060d06060309050609070b1b01090c29041d0405070509040302100608010212010b0703090f060c140c0102 70
    0x20062109000076405214894103050b07103000c580d480581c080390242c40ca0149015103582c0107004128050045600781903c83d0302032801d2003481e00c00642e9802c010b128408045a1980240c0154030600c3c039140f861501c6400c0900301039a5600903a1800c801094503100540141c091001c00b034560216a111380f4030041009509011060b020040144400980194405010000303c00540c0103809100000d080a850025500500f81080342c18035900510980e141c0d0045502485462129416120481507020025498140c100d01160040c401ca88020f0120000c20000082c001a1800310a84c101c0c441d03002c0312005e40c20040c0c2441580038a02940e6075038a40e41c10000f464103105600e8552141c005c00845800595840104112240c1940c040d4010782094826042c601003c1c05020001d01e03464008604c0c207020010300306245074041c0928201800c0010380a418544105c0c00c9074003404982510301034060743c0703540c00340c0341c032a0b0711200300ca03444203034407440d01c044c0d02c0030940c0b0036100c1042e0050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 38986425 1250 38985175 38985179
    0x50402150c01090209010f0e0c12010e10030503130501020d0f020705010e0103060b0703030e060708010302030a02100203190906030e030c060411030f0304060503070806030d091503020c030f1801090f 87
    0x140da65500580080c0c9495962210000d01580d82c4401180c002e00c0d18003c1925039500b071560301514481d000709400880c505c200480c00e010104000154111400c05200c0e004035107820203800940001c941c0090102e200118520a002c52200340c1c50049030001d03008c540030070728003400a462a100150320340c0050b0300206804c0069501481c24002402d4051600140c0c3ea516076420201d150445c04013a03001070b5807082030030203c210801840e034000ca0303e800c3c01c80003585940e0001e41d840715002c1c0000c0c011107014001d0743e0200d00803c00d587d04411848600340210b100c0c62402090001d66108840009040c600c50507100d900c0031003160507408210380a80003a82c6e6503261001140c1030a62410341601c0f4040704034200c03402c01d201800282c069640c1d42980e90070502001016002e001e0314040c420b420184000d20855000000182240e0417510003060071000311030241d0090241a5506205003c00101d2208205001c030041804041040c01174407040c144400444050a080c05400180703030703401c501 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 38987675 1250 38986425 38986459
    0xa08040611161412030f0909010e01081f020909070c021003020f04150507020a06020604020a15020c041a0d08041502030406080c0903070f060809010f0c050901030b030a050f1e01050402 81
    0x10480203c0c005400040c4106031030300c80c9895035000560304003606102103001440c510304800c0d441c2c010544414103888950501c0802901d40c41d021038140e542d29601e5803412000449a01036943c40300e0000c14490342c52400c800003914024141c64100d1144084c0940406010700902c05d0700d0340d100d0700c2c515427030800c2e0900d44c40040300110b080310741017809018090000180c1c3c405403148040c1659038040c10b81030515205100c002e8403030380c0110040700000440c5810702940094100b403010401c44001c5020b404600b1898195617541c1c911540103d03401500000740700f201c07c01001121849200105a4004800e04980768001e60003a8400122490301091034038224001818000724002c05035201d00780c1e51800070340520010f0b032114010a0412040003807481080c4074031000c17a41201c1c42400411381e418001082031049010382d82c1410754400d2144890b4804000e07100c682540101110844228030000710fa9507000c3d80340075110600f003044804007101040c09942e000d170354042c04d0074140c001030b12a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 38988925 1250 38987675 38987699
    0x403021c09090911030307140601060c08030708100302100306030308150a03020603190f09020111010c080c21040501140702010b060403030f11060406060503070905010302060d021b0a0804061116 85
    0x1c02601d48050442004c8200e90302440249256403060101e00c500701c203000112820848140d10920503c81107000c2c15020802d8402125400105440c10003c207036901700709040c020030107070400781d001850444038000311078060348280280d03802601e40c4100356950b0b015001c040c10421749404d4000c4801c1e0420001414040c01035508111105003035001d20f40d030400c0b213508036902c16503080d2406456020711020340d6005030304006007218410081c000e11881c3c1c40c02401c0880007501c07045003d2000241280d029040b032045010000101c03298079010304141c00d101f4081c000500b40046100b102070086540c01d0b00510a1905001018040f0381c1001e1030340c0c800781d59014180c401e800501800748054040d018050140a10551241e42c00092260400003494a42201ea8000d1000301f8580001803016a4600c4d00f640c01325100d500c5d000d640ea0301110720440c6c0412100142030014411441200700b00f181600140c000d6840b113030f48480002144c0c5901039515240140441183e8511042c140620100c9a03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 38990175 1250 38988925 38988941
    0x91902010c0812070e18010e07020a050f010921080103030305070c0b070804050616050f090409050a0c090b0405220201030e03071b050a0518090c040e0102030403021c0909 75
    0x1040800842856803a6401e070b50b888206100d01d5206904100301016410940000c00c01805954035400990b035001403091211043c0140a0482c0a600001d946e03580708100c050708550703020b000d44448402c07005055018010105080315030701e00194100b040103685903a8880017035842d40d2400b10692031a1001d400030200900070504100514898001041184081900800780d0384c3e04c00070701d0b00d8641811428090042d0424918840400042c0a0365a0200948018a036401e400641d85e021400000e80200f4040c1c1009005d0f00418550070140282c80c0720040032640c2411091104c2d2070641e04104c12504210b40c03680700c5003901040e105014000c4600611034070720604000034504175504580c1d10b540c010740c40c00c81d4040252080c80c007a040c0315a841100078407040d12411885800e21000032500b400103a9011800585500014140d480401034040c203c2c0e00900104484401c202d420341c040c2d0301c00c81d425030151180c404843c1c2c001100c40359031400c8001595501e602c890800c86101c0c0680401b0f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 38991425 1250 38990175 38990177
    0x906020405150a0210051314010e070b0a02010e01060e0c030604110c0115050a080d08040c050a0b04051f050d0209031e010501030201081008070312111609060b0309190201 75
    0xe00020505860742002c2c950300303203680521503885506405000b031414100c101c0d21000036040c142840702e100344000080b00c2003130380140707808449410102000d00400d80728004a1080c880c4480001e03c0f5040c0b20000c150202c15036000340150703500a00c1031400e90701d00340704050b02c11303043e040010000d1041e0350156070882401071020a01444040b0070303092a80000080b80400e0755141540c0e92410715030040c83c80100b406440c1800c0851a01111a80320044401114240248a0002001c00076a081c0010141400800f4010031a4850184211a81082c003940d800743c1054583d0746800000d001c040c00780382c01e06640711480c0000ba40e044501940001d1042a0544901e1890903030800c8a45d42c0a82d03004044000040d00b98510700004092002c064280c07044107109101c28881308201045010603203070404031482403c880f44a040ba2110b150b602e8044290240d0001248800d481002660441c0e082c4441407000907190450200248026178110b40c03140d101c4443c07001d0300c00d2620b5000c1011401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 38992675 1250 38991425 38991427
    0x10f0b0307020c1c02120303220807060908070f05070905071821020405010b0309011b0804060221070206090606060901020309040e0304030c03120f1d0f120102070303050105040c0e060301030303090602 88
    0x481d9000c41c1d1742e039040c6c100c02d001c15040401005000d400c54a03822901401c0c61580e10100d00c916100c606840c4102c0c000035000c02d8071900c032241840b41d00411a02c500f41c0c03005415088030354506101d03841e00854083d140d0081e0820380030460983c810160584040203039500248030030700d8540e500b8404200090722101c0005070019650140e5038a1041e140285202d400f0f555591920b603e20508454a54040226a8244151850034150301040c1958880d80c841c1c2c00580e211880c3e0002c04194840030700c400c0c03100b201503081058069001c0713007590160800e8030450f0180e4403008100005402030780c0000380140d0080c041600945041d40000394003240000c02d591400d5140d450780c0c044200160025580360040f00d040e406a6688040c40300d050030710ba49050052040706c020401c2504560660311482082038800c01001503a824800803184c0e5048002155192440d2501902070700e001d02c02d00780f00318901a0214020303401950710040400c4014402803540c5e0a56400390001c1c0000c1c41d00f0b03100c0341d40c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 38993925 1250 38992675 38992729
    0x1021c1101020f0304060f090302030d050a06030807030c050706020105010503030702240a020304060f030c140307020c0603070c02010e15030c0a020a0c180b0d23010f060e010f0b0307020c 82
    0x140a100401d88820030740300441d1369160905058080e0740c50b02906a034514680101580803035804001e403424030306251804202901d030064610041c1c406600064064540040d2400c10107070405481006a032040090304c51107030f40c03000140c0c200c0b1800d104464040d0403c1240c00b00629101010108101c01001010b41e41140000007130001e401c00c10a40016070f20008050055640002c3c03101e050002c82e180900c00b0600c810740041610122003141e07100034201001007005640207100045600d60043c084503204c0c5802d0700c00401c504a200400d0380803585140000e207080c242042594400012080502e10319200c1c2c0d03c01540d01d92046c81030704114010354140c4130015085404020040c07005040107003140c102400c0c25001c40300c120722030034815103203406480000707205603807405038603901c21700303030241c0c0740b08070501c0d18050700d040005565050314240700072415120b44581d1034181c1c1c07e6000d0030a0392a8603a60407100d5448107503140c6002d40e0282c2d058510074540340040d180440c40014603525280 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 38995175 1250 38993925 38993957
    0x6100e0105120702030c1005150402090d120e0a080a0819020a080418060801180605070306090203040609120212041a0d0c1706010e0603060f0a0305100504060c0e01021c 74
    0x80c041e00c0c9100160800591b0040c00d21702004881816406050b003001130781445480125440c071300889042c021a0007168440440d500c2403514403106410030101d08403a45601d50007004801e410114a20a43c0d1100340030801d414009444202c440d0311403059460840c0c4040910131031111500104210303c00e12032048c0c001784500d005030004105030590f52500c01c0c50b5a0302a410360b040d581003038000b0303858601001452030b4034142402031290440c00001d40e64441c0c44044000d005540c1111078403600000030b2208220050b8012515140500c906904407030307484000f2600d41a8051201018890602c8203210098221040e040395240d10307d82c05140c4070b4440c0b44801924543c0200e400072400d48020304207801c0a03104400d41c0960246408180391a0b064006a01408054101d50003985011914400c6482c0c2c88249409175402200b160821140b000110000d0541198111545030a0440400409000c2c940e05000d03054160044c12138203140d01d02154083e4191000c400410401109001c082 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 38996425 1250 38995175 38995207
    0xe0a0506030c04081005090705100e01081f0b070203060105030304121202211206010206100902090d02030111040305010b010302090901030f170406020c1507230313090b090f06100e0105 81
    0x85c0348104000c142803404d8001d05081681380d5100034010050601024161544030040020000303003404c19501d40e80311412847c022401000d200000030b4007410300030819111030400b52420500c03c90840340d5581c2ca51043c5500c0340194402c0f00f80c090000c002c60300029104100035a16540300e441240c850f0f1503c00e1300841891b6200c20710042c00d9000013000780f600010405400d074400d00a0000b0201e60030034816114080d0174600c01c40300501e5001c50104030990f00d0b102c207101d469800800a1181c134180600503582c0d98018802200d06620340b056891803940240241c0d4a003200c010290707101a860740c3c49035141e06002c44021a880d05100c16600408040c920207407000d82803550042c407a032450b400c280200b1804026907441d8883c010b0290b50000b1707604189000c01d14401b8118402c0c0040d202c0f44103842c50003041203144041191280101d07a20b210b641c0024980d8100311480b201648411400094102c002d86442d60030a41d00300780460140c0c002d042c42c2c48074802c1890003500d828101d50b0340e0080c07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 38997675 1250 38996425 38996443
    0x60e03030f0609100803160f050f03040f090b0a03060e0a2001090602120d0c0909050705090a1502060109020a0905130f0e0312070e01030e01050a0506010306060e0a0506030c0408 78
    0x80c890150701801032508100308000c0e40f0420b00e4402d04c18003030620300d256176079000b5041e201446000503100e80e0100001c0c040840000c50b03020007280e1411040c01c5010f070701c0b0b801c0750051408000c00060009603810550140a0314140060a000c2c1d60609640f5440040c2070788c010504214801e0507004000500e40250503d0700004126126564041d000e000602c140c2075070b8855011548039800004480000d40304840b680e10240d440020426002d0400b0f80309003801342d1221051624207c00c00035000d8010008040f42c1c00c00316802809980c0b21400103400203503114042c8016486400144048a100c0e4020500100d042c00d02c0c8071110359070b0b40012111031180d80e030b20008984622030305030103101034000c80c0320294070075014505264141900025000006089504110041c4c4410080780d0095000c42e0600340c86c00000d0010b4500001c0f52009040251144ea0029260034000030b45c562052540d0b40c12000b0007031941d601035280030300b005800e400c081d00da800148020400000c15800821074121 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 38998925 1250 38997675 38997691
    0xa0312022a0d0915170a0603080307020705030c10020d030e120d06150903170a0309080403120f0503090304090207060e15040303060e0f18011407111e06070c060e0303 73
    0x34507080142c000400810369540801e4002440025900b40e16030048484220041075890b0441036560714003003a0301810b1158806800004004203111484c0c0d8040380c1041a620700354103d42840d04100240044801446403420043c0c200d4810001c0c600c1c0b00381c008025210320602122060300114881455039030107a00b40401003699040104600c021003146e000c1c5140680c00d1001213246591214810a0740700b030070048200a0000d00f4884840c0607902c0790003ca07070003085d84c5882d03540342c0c5010202020b12820100100e54030745100222140300d001180e1040c90611701860a09180c081c01c43c01135001503404403a01c603102c80070b03041800400c00108464aa81009190003814181000f81c112445600302c1c8240301e0300da204115035521095000764001c071601d2800d102050801700d0084c018403541003904590740c1b1110070b2211840d40400a641e04000410944680303807090744640c16051040880c800e17480d0880c80005458030b00800716051502d00541c408180d015102c04c0036030950f0710071034075a9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 39000175 1250 38998925 38998933
    0x70e13020c0a050d03090b0c04060e0d0812040605010518041509170a031401080d0905010c02040b0a14010e0604080a17040305060702030d0b010c020a051504030803130308090a0312022a 81
    0x2001d00a1f0740d59505c2d0880000710b403091800c3e0030580c3c01000c1d003040c502c000340241c05080000b020441c1da90104c500300c41c82480d0000c4241401e117428005800c00b1300c103083c441c907403042c140340048407060300040c040c0d9840000260030051541042020700800e6209480d1a003425400d50240a101001040040403c2d0f80003d069020300c130703070700152140c180c03c0140d2581c0292581000c2d1a004001c0a0542d5400d0030464141003c520002e0007415108460300c0d000807007540d000132550070202a0a51841d82620b60a0604c801d030000e0000a0290388600c4032035907c40c1402d003010604001c80c8829100c07a1408103454140c494940760b04e032041c20f50354076005078000210010360151a21a4950070031017440c1402d8000181d40005400c4803c030700480c2d215501d1035140350480c002d4101202c0003158022941c0b0340301c1c40c2013113185904418410342070b00444d01c29000982c66510100703428880c0350f415207a684a22807161121002900100e029001e1010030380f00300b84004580f4820200c03d040340304020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 39001425 1250 39000175 39000191
    0x80a020106170604060203060a03080d450503070b090f0c04050f06010e0a091e050c1201150c0c1503060f08030409020c0c1c0506070e13020c0a050d03 66
    0x34211040e65018401e10100207030311440000300468440d4000f500a01d001da02d83e180c2400207190b010320750380011710001e0700041030b150340c1c0c40c680c000d0051310100e04c0d404c1090b0100c0748410a40c4410380c3e2151080309062020000c0c0306c039815905400100e008404076800d100495030341d101103003c06d8070b0074445640300314130310b03a1034881c20001c1d06485003055505110500744103c1600d0303150310141005060205001c2400007036100d601d41c0b24010607820400f840403000f100e0445021901c01c210300d1140d01d0812001030b80007241e10b011144101440c0300d100106a01c1c080c0d81c2941d1042c0250f40303d003045030052400b000f10b0003426844000d44001001820f9a20b23000e080a01282c10f140c0c00081040900c10080014000120a6800312007490707038050b9941000b04a214144610103580c9d550060300012009644c4c000909120042442401104d010b501d034004142c4561550000381a8041d51341c0407120103480042e0050010340c100141140c500c100156503140c01e02d041880365400299944c401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 39002675 1250 39001425 39001427
    0x30c1a091501080d0915020a20030c030d02070b0d110a0302040816030c05060705160f1502030c03031306090204090809030c0f09010e0403090902070305210f0a05071407080a 76
    0x9401e00510340b403401008502404c0d400642000240c2c4a9600c240591560600071140240450103084e80d01011700030a001c0c450032105444807986120a0003131181d000031070100d090000e444203241203140c00a05000345008040d0240d03901070303030341d02204c0c41e210090740199a803030501410b04c07107440d40c03805030b11039042480140c5400f402407285002c02c80c202c2c00c20008214211054000e840e0143c4441c1d96561150920070b10b0001c1d0010309403045d00c0b5143c400074006403105403c1007a2b401c154480c0d0500c51201c0700403683d0b030040d00d40380040ca800c20000b04942c4204441441e5010344076060118220b442d42d000a0110390300c1a500303a8610788002503a40c607500c1d0902034152108801ca4400c0b0010304001d0104035189014042d404041503058089000e1600810020b0000d1411a00c159511300540c54020295045600340301840340e041406030394008a056555481944200314110040d80d07042c8640700035140251440d010b00291400c0321302010185030060139054090038495035243c0340100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 39003925 1250 39002675 39002713
    0x30c08070302030412110a020303070f0212030304030e01030506010e060a020606090603071a070807020a1503061d0402010c0303021c0605030c0306070215060109051f020f030c0a030c1a09 82
    0x100c10107104004000000b222607102400036001032608a00c03031120b480710545002c0b201130020f0b5040c8004103d440c1001072209010300603038420390750106c204001e11035095480c0029100140810440c01020425501c030341e2006510001c14508074503803c91007070206070180c0c4030700b0000b001030700b284040200301d08044502680028054000b41302442ca0050000400f11450b005800900400182c00c414030116106a030f40b03190f0014012252182d40d8540c0c01c2e03850740700f441c1c4003001c2030409030000f4522103040000b842081d8104415a10382c0c0d43c90303004403401180510f0440074141d0034040030030703810320000906403140c0080c2e000088103810002010300d05010030070020311039403000003086040d81d80450092440d4003828190000c079100d0b500165040c10b41a0080d07500310307064080d140310401d22007203880d1000c8481e4080d644194101195030780c60b8070404003e4145680402d4501d800640329280700340026005005203640f200034485a00f504000c00c1c1c0f0380d01141c1d400503242402c0c00f241e4a03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 39005175 1250 39003925 39003931
    0xb040b061011030d0515031204060e09060f060912060108010f0f02250c03080a031b020721080903011d0610050a0b0a03090501050711010c090b07080c1606030c08 71
    0x1c24010710720b20481e410560769100d110a08012180c850011600618003e0b0600c10b081c48020142d40c03801c0d203040342186c21034120f1721501c000141410a41566410403450041c0500dc3c042c01804c005a17000301400710a5004880954021302c00c0b11102e101e1032828800d8502901c0444004190441590403110980303607201610a400c0d07104110030024048440301d0034248603007209803512009801e04002050036201d0380081d01c1c2c40400078441e2220340e403644c821000101c140714150011300010808903601e003503902422840c000c06019009a0222282c0400c001600c5a40a645800b1a410101c0e00307481440c030020501e0140b090310b1030715480c0c050089a1b8091031440d807602d86281341000050240b6058454442d400000041c1c64030000d01c2030304005145900300c0000d0115082801c00102403160b6200840b20039442c0010903902c00e8400d052101c2201d4460b003010b81044200e4403000c0165001009a0b03c0c140325620304200b100c1d4040000c3d030010121500c0005002e1031492019000e00401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 39006425 1250 39005175 39005177
    0x90601180e15030708030307030b060d020408070e0c1e03130c030b010302180f010302040209011b0c0503070506041206150f080601080105130218040302070b0c16060e0a0e060d0b040b0610 82
    0x3001045c4420b05001082c0e90788100e081c50040780b00b0f194000800c2c25481200f54140c030b2507000060200301d01130300050200448240d2441149a80c3ea0035203540c01c6409101c0c4903203040e507202a0844460f42c20000030b580c01603041d01c60002280081e41d103181d440c0350551302c115881c202c244010010b6242a07908421040d8600703000d03940600d000d100c2e1070100201400000d10480d4041034034a00b81c1d129204080500d00d00700d0f449603402c0340a0901802c0c0030068405d0521034030442c42c02140500340182179030700325421081c40c000c00002947d2a0b0018004072840303001113001360312000401204480c000001040c0300c4018203210350521a1003801c0da1801024541038845a482c010b0040c0c840f0301e032249844581074400743c01900e030380c9000c90628103240d0120000e0503000c144450385107000b00d001900b03014610340c900403141d541c641c01d4400e81e00107c0c030590b04c400350301030070845980340e440712960146009080251b0b0207226030b103015240307200b980c098031a56091401c0007035508000ca0b62940d5505a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 39007675 1250 39006425 39006433
    0x9060907020601060f170703051005040b01051204060207050604030f02010f06030f0204090507090507020d0206061c170d09060b04050f01030803270307110a060c05030405090601180e1503 82
    0x2180302942d1800b041c890030303041115403500e4500d21407050051640d180c80044020a803030510140080182001b1348000ca5a030742c14503000110343c500751103082210030040e103a490a05018084803031504800500a8071003e4080098800003141881860720961103900c403c2c3c0c89141801000f400c5808a50300d800c1034628091040c0f0104100d40c100100c1181e044030701240002132850503a0400300c0c03503448031001f6402d00080c444a1600401c0082d0000040d0b4222540f5945240808c181c2248000d00f2031351022030711201c1c20104c1e82030301e41c401e414038218880c0e03844d004805444d28119401c070001942d142c1d6a403e154260f0745401d020741c603040a181c60391007555504641f1086014030000c0e10249903903c1510f1881c5c820f03640b452001d081541e9907810340c0d8031200a400c24040410300d444145104101c49203003c58514010105c1001054015004508141c20441031200c86500545071905100c4020040110060750404d01e4000e03000d1800c18010304e0a2581c040000444640d80092203608 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 39008925 1250 39007675 39007681
    0x309140f070302130f091103010c020309100f180b07020a0803070b0f09070e010f0303030b0a06050414010509090a0e010e0102120f0408090d0602040e0109140601080402040204080307030c02090609 86
    0x200000300c110a42e5011110f00c40e2a00130012030000801001c03c80c40c14a070f00b829140c506000c003e0030f455010701c4c01035000f40040300c50140d08a0b00e91081c0002c0b554041c1020788060502480342c4200d184411007402c052401080f00b0300000d4080c1101d41c407054240c40c0c00107a00d01142406006040185103460056044c00d010786c0e500400508000e1007507040075010320021b40e41c090200418002452500016480ca5840d1030945501b051540002c0c2c0101341043c1e40c0b1000c0e418860611001c0304e01d56501c143c100703800c004000540180b40c1c0e14040c108201403008410700c5d40e405088501401c1059400949113025100450039a2001402c003a49a4410720259a84421501c01039500c0b070166800034400f6038880c41c02c01c10300c2c0a010045601301040040c85401c10440794020000d90f1001018801d0b1030703a8031111035041e192801c0300d105c80b211355040854040c0d40201c016580040c4010805810243c80e60300c59441c42c0c10490090b000642681c000c0015800c0c6001115046030040d52500b045103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 39010175 1250 39008925 39008953
    0x3041a0c0c010c0f141f050402120601180905100509030702010201060f05060d050618040b010f0515040e070909020f0d0f0203100b0a0512040303140a05040b011511030a030914 77
    0x103201480a00100c2d811443d803845c8010520100b9176503407045800020160b80c48150400401c0b040760101d000d10341103800d280820307100040180c1200c00c6e03010b01c0421944c60201d9000949240e9500b26803600ca6803803604032007811070040034402c2d2a01801942c4510381382c000282500c0d4903030711043c0e0215003038000b40425100c46044a4400310138690114460700c8400125251500c0100d40e0b2044800d22000d00003003003600c61003281200c44003051040b003d5264420030103074590254010001d001d0400041000309040180b865021030746080c0860a10303079800c00c000985c0d02044041c50500c0740000d032400890349a03c43c107d030518520104504525145240010700f2400703000300c120a401c00714950448031710440844080240b29040030303e03541000e250103000f400c1d403500d1503041c0b180c940340083c110500034850a8800c9070441d00f05901c0c1e91a091940100c01001c414810800454902c61030440e00c080004001a185654001400503002d0400c80000a116404014142c1003162145004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 39011425 1250 39010175 39010193
    0x601030c030e030406110705090c041a03010509070309020d0c060801060f0e100c050a060609140a05090a030f0e09010803030603011b020a06050703090203060f06011803170c03041a0c0c010c 83
    0x290340c0d64100169161b611460903854403107a0b030712072540291344100b081140300b40140940308650005441400b10691558101518042401059045500c010004600c14801d8104990f628000362078a400138444c2c4d01c51100901e4150045004280e84000410200d98082007680b28601c50f86006660000400d00050b030300c10800b1b40c0d400c100407048085005200c0c05100c0018007681c410800c00050390b0b42c40710640580b032003c40d8420508600800601c150117140a024412600031010b04010811642c081e03078a01d250a5100d007c101ea40d0400172030307580714100d215000c2c10032034000b940c40345403142c105400d44880780001318184001080c01000a5000200040740c02c2e0300a6020400c7c1d51254403c800401d01e208001c0d505114900c10711541403410850b01380582c07005e07a582c2c103281540300c51550b81328105100052629211084101c800b00c07005c00a003c03000b001300c0c107aa160070755400d41c10f404215003862460080c10000707044000c2c2e407800c020340300703000c0700030f00b840c820311503494541c12a5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 39012675 1250 39011425 39011429
    0x10804080a030b0d0627080d051005040f060906080d020709021c091407090501050d0204020d110403050717060f070513030501020406030204170307020d020d050a1205030601030c030e0304 82
    0x100c810003003001038845000b80c00c21601030754082c0c403519050869007000b0000d49034007807850030500a07004400c07241c5402c11001e0b140d2690003034805d52401c15a00b0300d21700141401400c032000025048804a81d90741c540c060003141040c051004140709043c4203560040f50915440415541d119800401740e50303802203143d50841d0b1750000300585901c2a001807407122003050143d01c11892502044e074082120140a0710345807050802101c4a490711035400304201c5600f80a030a5004005e001540d0040c903064000701a041c0441b4000301c0c40788149003030201d694211f03800803039450b00141d5080c05410041d00c0910000c03440c450081410341801c100b0700101329005414402003240000d80c192100c085641c14000071a8488001c40d61035030b44103001802500310b40175214220400e1109004220b50010644130029002031005458240c00d1703007000030143e114502210710340240c0d0904c5011a081000800c0c8881682e100e19a07a0b107001c2e00014201c600f10070031041458a0300703041d90080e00000080e902 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 39013925 1250 39012675 39012683
    0x301140108071b12020c0d03050d09030203041d09100207020607020904051906060501090603020c0c0105090117040f031115040b0702070902030118110304080715020906030f0708070e010804 83
    0x282d100d8820442c3d20000d00018030482081c004152020458020819480c04030181c0c02da86a40a10604100b900300401d040135000403003d0108500c0c0d507c10f0352022403114800d00440e0f16051b51841100a03807101028010b108205540801c498a4018051101780c03007403070201145400002c1d400039089011f10780c406800b8415000c005002c02c0030811440d0340c070b654044138992203d02030345031000250480b40200d900050000e040003030294045d0081d5540c4000001c054203d24500c0343c011600c0f5013100142c81d0421081c402c2c0010002880c08101c0c2c0a6800350b0303281e5089044034200034201300404271071310f056548504003c030404181e5072103954105071310240050140c1c4803410304034a04040c1d500043c82c0030340300100010310140010f40382c2002d540084014001040c0d51401c01100b404102c2c1c01600c000010801000000c0c001c40056204a2102c0001400c203207021001c01c5654004441c0c02401251030010701c07095035080803030260b02ca000c070310b401d240c04118140028110000584010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 39015175 1250 39013925 39013937
    0xf0b09100f0815150105210405012007061503080c03070506010515071103031b060f06010503040302030409020d110a170c03060303070201030911030111040e0f07080112030c2f030303011401 83
    0xa1146e224000311810408012200807030f004008142d1200403200303640844240d8a410741e4007a40c03041c8014000d00d0050307071014039410101c80d502d6003809041c280300d61085040d036010000c000101140e019042902c032100007140c0720691864454901501a00114030452a85a0240380d0b58520300458184030303403100d032841d11040181c01003032441c003a071407aa020404115825000c005000078409105207030f03981c0c102ca41a1030b81c03001598103100c143d80c082e0044c1c01c208414413542015800910200482c501c0c00982120306000a00d500d82000c2588000a22400301d80b0f000700303881c40729480e08030300e80180203455801c007000002c0d607901c82c07044002d0516450390310010a10003a0001e200018070003400920448800c0420b410040d031190241da1401403900001c5100300400002d01846006540c03202c042c036901f00940400b801c1241c2400b02c0c108001c410103800002d050038007d0755940c0240340c0e544410584000b1070b61109044450580c081c2e40140010000e000d12444090700c040002c1c04c3c04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 39016425 1250 39015175 39015211
    0x10507020301090b090d1d0108062110020d05060f06090d020a09090302030301030215070c0e131407080d03020f090f030a060e0d0807020606030706030f0b09100f0815 73
    0x842d015120700c00c00607280d07080c044100b1048141c0440e1580c0504051b5840c54000c0300b401041c030001501c411042d90009000c20300044140c20f2800004031411400303201080962082d2819503d4071240001c0e5500c0b80d500450062144a041e000e8242c02141c00c480c5105030369038900200e05140105008140301d941084801d00c19911008030a03005006111018001d45200c0e04010359254001e03c4128020701c0e0369110200920200c0c000e441d0f0243e0301692103058249483c40c004210076026040440d00c50049010b000000c0c07400c1282d0b1a550005e03c050b12080f8070300843e15041070b40c26800d8106060040258031010301603841110b40c50320781114010401140d900100b440e1a0044100401403850144200403121000944e481c00362943c0e9100e86903680c0d4004100e860b0303282a1642d0780c01d6400103c00340b000724065000507100007602c5000013442c664903c0094406c000903100d03034200c8401d02c0c20512411002c1d05d0b0180203000242c000308030901c0c00101505004000034044842100c0710622 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 39017675 1250 39016425 39016429
    0x905070c150c0302070507030b0601080121020609010e0d03090e180c041107200f04090206030a0e0313060c0b010801110319060902070818011e05031e010608040b0f010302060901050702 81
    0x143d40c812074001b400c6904064513450080d0380c1d02400d0741d07202d0205540c503000081000c825860400c400340362440340c20840c1c14603400e0180341e4002d1410329051290121020301c0300d40b510009a008075019a46900c040b601d000c6460021000141410307000190f268020080305ca00000e20003140c400c10b86000445c3c00c3c80b60702c5001d0074000c0c420020700c450110007400780030088a590040036550119103240c5121241e1040004031070003032400a420403070600000da2400303900d5200c14034034611601034034a8001a08200c0e0f0240c0c603650000e102240c154269035042c8101e01088c01c0c050400b910003003011840b15504518103000050030a0b80ca15848240320f80700c2c5040b5000311000348188071041d9103c00702c600c2e1228194001c1d040c2c004035001d61280445a542c490b0491040c8440c58a0740c0820030340c0c400c0e504440fa40d000400f9107640035541005e50301c190340b81c110158024190f590300c1c4082e40c141890030101c91900580070550080d1319034010b00c0581e50b40011a020a4002d09001d5175a0b042440 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 39018925 1250 39017675 39017677
    0x130f0809042c01060e0403080721020d0506030f1e0f0304120201030b0901050a091a03030307030c09080a030e060703020f06180d03061404020a09170102040905070c150c0302 76
    0x9011a001424108488001404500305450440d90480c68807a440500700d10b043c00c88549102c0c1d4414030210310b0100340424081c50290380c000010f813410007001450840c506803c102c0c07010400d01039a40c00106440c0188041c13213980d030465421005040c210085100c03150ba070300210211480c09401e00c580c488410f50080000301c0116591405884e01d640c3e0b1240500044512440b045c0d020a0074101e40d108036142001005050380c10040006427000e05051504000300340c01511a03841e8401d05901c4d00d055901040503500c10a219607001c604486680001050807529a01c525643c0d0301c041e5017540001e40200c0c2c80c185030b200985a207511070400f07040403481c3c90b815020710340c4c040c001e010500401300c014003484e402a543c0142100c4510f103007920114200d40044c41400d00c0000c5103e6030001341c0c6070640050912450514002c10800e80304c030100c6900c0c400e406001d02c0275070f40c005802c0086580c00e024481d4407a40070300b403203104003940761111001922124000b080c60703981c0790300d8916130501940c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 39020175 1250 39018925 39018937
    0x5100c0c060f090b01060503071d0d0204020301080304050a080a050607081009091b0f050904020f0d0b0705040504140115030e0f0307030c0b09060c0f0304050a02120c01030c020105130f08 82
    0x5080c414042e508207aa00101510300042e1513114200c3d00100d03445015100300c902a1080380d8600d500c0c0400030000d40c14640d18075a15960040c5040400750159555002850180411f6409156120b26007820400940007941c001c200341c0d007040b03004101148022031700030b501001c503080100345c540c0c0e00d03400303680481030700d4002c4c0c10000d240c40784490500c461a404544079440b4890300f10850350710f4910b2100701841503c190355106038a040041c1c01810902019800310304040c00f0030100403d2569a554039000c1100c1040014001180411061a150262800c882200041240c545d410915604c010f48104000e1b24185a240c00316603900c0e0350200051038a030802c0c0070569403200d507240380c02010b05103100e80076101050680c001c03c00018010804034003171f07241a02400c1c0740c011054851245034100600680781801910030700d00c00f580360340442c540c0c996410303009003d420813045c0000d422240046100c0d821a072400080261425004c101540c480307030068002c19618800f03141410040c030803d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 39021425 1250 39020175 39020183
    0x405040603030305060118120305071401110d0612030504030308090f0706030902011106071b05030903070b04031208070e0607020a03080f070c12080304080d0e0f03040501120905100c0c 81
    0x12400c00400c2c554540d005a0240750b00f40e80d0601c0e0350880b000c80c0d41903541c803809030b03040000c4001c034000c000a0040008154062094541040030503118614030308507a01c51044544134000003400c04045c2c801440342e03074064640c400a4004500b4252401000340c02030303020090602c0103407804103100d1070080142c4451454a0070864000c540c8484c0000c01400c506581240810524880700c0c1c6403803030100d44a4800d01d05641c038071000c2e503a0801000070b1071600c0c143c1030700d90780030420001c1107684083c400d907000b8002d160a1160754621b94584072840030081402241000903540a020005601480703165002d031044071140d8503414180006000e1000f1a40014a842c40016504910a004070050034032580550b8000d0a4642e0b240601c1c450000004c1000b04020001c00014000621100191400228180000401074507403058280307405080d0340150b0040e440443c0c00c002969000350320980075900e08000f4070a8030a9556125516031100d82000103154949400e010401c1c804c001c621009900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 39022675 1250 39021425 39021431
    0x603040807061109040f0203090a1b080610180213030201030e010204050d0c1d010305151806040606090c020705030703060f140f04020a060f0c060c180308030613060305120708040504 80
    0x80d6040207042e541c0180c1c4624045c1d814403440031712020300751083d00d225500c014003034625062140e61b4400b000080c40c40100324417070000d80210f812041046007030302c503500ca240d03041c1d0140d080c01d90921940c000d00c5d510b55510750042012030a0999400d124204507682800c0110313a0b00c44007100940a0700868110300e130401010b4000700c082c000c2440d009403c8400d038042c400381415210005c02c020842c24000608294002d10700991601c03035003400141c1c010303101440c003107806401d402c07039070700b08a008c0d0340c01d44051f6181d0030306000081240c0704c0c0c3c40501e14180002c1000c1840c0902082c0c5401c198403002d0a02c075910501c0e1200ca000e82e4008440300d1031040c450a880c4d00c1e0a41500046190035141039019030390070034010581c40c0c0181c2d5982c107090710a80310030850091590315080900500318515081041400102e0303040c4140d10740301c90203544100c6006480e80740490034420107500100742c0400150400780c081002c41c0d03000c00c14140320008010910761719892030805e584030b84941d510203500946 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 39023925 1250 39022675 39022691
    0xc0201120f180218070906140f03070509100e010207050114121e0a060b12090106080609010f050c070b0c03070905061201032f100311030405060403090906080606060304080706 77
    0x80454442e0519200f214201550000030380003522011084a001c0c02013002d440d001d00c03038035000b00c981c8840081c0500b196441e044440c84e00d0781040d0020348005001c81d901046011480c5068400798200c1c001503c0c000503140135090000350303a4441807040a0602c8810b03403c1041200010045445100792181c50184606221403c550480703801d03452191080300620110384030003614040c14084800c00210141461481d0001d080140006071070a8015036941d0f10000744410240302e45c0344191506c400000d213030010380c0d1051040d02c000808245406404000450014030600306240e0000803009005440380d80d0981c2c00c0d02c0c82c0b0720301e40046030300490108681440342404494a4141c0c4d01c110640070414807070ba00035111100010072487c040c91707214110001a820410715001b041411490049500c40c014a0070410706d500a480694081d00040d0070002030541000100f801005145400c120442c81c11038041d850b00b1000c0c085c4ca10540000011900340300c2240b095641040e04042d041099030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 39025175 1250 39023925 39023951
    0x1b03080601050f28080106050316050f16030504170f0604080702031203040501020d0b0415180609090605011a070305030604180615060807030204050609040b1906030906110a0c0201120f 81
    0x752581c3d804000288005c800895118418415280a04c1041c3d420400e4003000020030345040c2c00081110a155030140b112098100201034100300850090300d0b41d5903114100740001e14220301040901340356520941c0c403200e241100040c0d080c0e0098000c00020b0303e6840520000f410701440301d000c2e196010002c8140814403006500510282201100421540380e6880c18001030b610a1018030000407201c290800c0303150095220b1950906a04400084803900c03800b60f50210f480c4200c06480042c0d8460051005801d400350b1170304d05c824010143c504003005a90010035520004041078007482c1c580c01c100c0203004840c482c08a09a13400081404107071980c19002c00c01c0180c4d88510340000396000d01282c0110702070b10840d41a1500648030701e160842d02420310002d4100115450341215120020003070a010216002018001c40c2e0f802041c0c40005041c40400c0e1101d0701c4007240c3c041c10401a4944407a0060500202283e080c2400a14031050b5001e01c0c00600c000c2c0d070401c0c40c1c6410500304640380 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 39026425 1250 39025175 39025237
    0x50c0303070201020c120f03180f01090503030d0c05090307030f0605010b040f0911090402030901020307030b0f3001090b100902040f06080702010906021303020102100507051b010605130c1b03080601050f 89
    0x49d5816501502100c40000044902ea001881016003682041000703264204094004150020b0141042c5252a0286010030301c0c05400d540300341d55241d0b204111100300000350040a0040100e1078007a810103080104441d5401c419109000e152581d0b4a100d030749a444000c1601e4000d44010821522441c0950546010354000c541c0c840010745840c02d22201c5203448007008010740d40c054403d006982c400c8200c040612044045c2c1a000310b0b0400646d12503510134064030000354403d01e40c0100c0b43c00c010200007100311b62600114900e0b4010301040c081c01c003518468600b10351071031500c503015483e1101309078010314140002500c081c0c00050170800500608440808481c808c0c0d00315942824040c10b0541103070010355074240002c00402040f420011b10f2011045e02e1800c0100006400d541d0b90300040c0d0401c00c902d06d171000c0c5a152280405483d401204000710811032600307000714070f0696a002426208010441e80c1488030100e040c0040c0b150382415144a442c03a80030365150f24076900029980 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 39027675 1250 39026425 39026467
    0xd09060203130605100b0a030f11040b0a1b020105070f08070f0606050f19060806120303010906050a06020a050a1b0b03010e0a110a0903120c120309050c0303070201020c120f03 77
    0x82542000041000d9030b00c0d01c40c04400f04d54000c80400e08001250104801a0403034000c4154650b1721340188800c0381c0d4ad5900184000c0c450088119a550f405c410061b0081060500480302088080c00e840d0150760402c04a8103c6580300d0010a0480e110385410703036007405000c20140c0800c502030060020403119038040b505584086841d481c9407c014010005d05c1d00c90b9040340d102040f00b1240c2000b00c203014a00382c0b03403c03a20040c040740d83ca1480d500d14a00c0c40d0026444800c0c96516280d08100303074117003020800083c1c040c3e403001d0030080f02e103500c0b042d940e986112002455030341c4040f410240010009181000741100d544990f0707407543c2d504180403040d02c060300c11040d5245403100d07407040028a8012101e000000f43c54486000d8955280c0300c2000780e94000f4001406a034041030400a80d004007414281c803816100001e240c0c010742080340c500192400018041d610801103d070146c3c5c0c001403544c55000301152003114800d148100c1e142041c02c500155445448045964890242066403080c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 39028781 1106 39027675 39027683
    0x109031b0506070b07140313150605030f030301031e05071a0d0e0109151e02030901060807082103040b0f060a030b161403010e07050d0906020313 64
    0x3078158442c10040b40ca184d05101080f80c6950040d0105c560410840303000341c00e5191160192800f030386144c0303020340050200e80030002106243e03003044014080c09025603039505010800c6c5076a9800a0108664210112880700303608036800c464511010340003801829034514213444061110000500211605000c100d80407171404c0345d00034680910160000003030885000d0814070100c0c0380f00e40d404005d460400b4540204500c3e00c1c0008081e00d030803e080180e13a5203520312400d0041000d41e02c4403040d070144003400101c02c4070119081480006c00800c10301c0d1240e6000304010548000c072001805810703018042031034000d440e41596407080010f8224848203469889250503400200c6e00e0751206000e0a05017241d4a030b01c004540a0304035400c0c1d100d411541880d25007000c10b48000c0144003088000704225000d651035420400660780c010008568078140443d0340091601ca08209a03 = true := by decide +kernel

theorem cover : BRFrame.Cov 38848925 39028781 := by
  have h0 := BRFrame.cov_init 38848925
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 38848925 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 38848925 ≤ n) (h2 : n < 39028781) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
