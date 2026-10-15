-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5162
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:57:14.675453+00:00
-- url     : https://prove2.me/submissions/a8fb34ab-362c-4b46-9e84-e9a230f1b1a1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 928237410 ≤ n < 928417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 928238660 1250 928237410 928237421
    0x120c1809240b010905100f05070605090601030c1706150301021c092d02010c08041508010801050108030c0a200d0f0204050a020c0d082203051305010f0909020901090e0a 74
    0x100c1c1d0104050502c0300015a58000c41c3e0045030340040d8030f1002031012034015404007000310343c5d40c2850b60506425030385003425200203c8640c02550044d130010000c00c00e12201c985d01404841079441d000082890320a070350ba1380020803003200403201c5e5100280c0d640302035045881c411040405540760000c01d03404d07507015250004044608004540198040319000314454148801490144109640540044810b0b403070361003054502410030000090036404526030b040c1c40488540750443c035903240450040c01c4807016800300c00c0c15082004114543c410100b44011059403041c021002006400380d8410303604049140903070440d5540e15510140114180300352601c2e03108440038003480e502c4004040030790050520803002640001205c0644034020643c20394022181a0b45100384c0109070855044400b180100303501042c0001114402c142c040308030075014003001c0c20003e22001c08444010000f103000d1240829031540401c0d145016880f6130311550041c04660740101c00b50801c240198010720 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 928239910 1250 928238660 928238723
    0xc051902010908070f060204180b030d02010b0109050108180118110a030305072301060b2a2e0203011502010e01060e13060902030d050a0801120c1809 66
    0x4085004810014414090096440c1d0b02c0a000c034240300083e030320a142810010412a05d06409200c086904146148443c060901e0540040303403081c902e006260501c0b844000c01821a4101481c2c5c2c0d0050340c108600d1070445500b0304c2d0141301d943e80c0040d24070b000741e09440d46918a50911041e0704c15090a83c50100e0b800b406090b248000c0c0e9450130400c24280598070001f8040f807002d100742d50210704031003d1154074a0420605e200180b008511050840b00380740c201c640101d0001c41c030b110b090186241c107441064001051100b448001d14200d030f0ba107003030341020500c0003202003a0b1070710742114510311302d108204400c1042d5203958503002e078061640c099a00f01001907107081013565401c0d80500410702211011b602d0480340b5100d031103103403146102440d03090320450f03111041980140c80820100c0401e54040e03603950346403462508018070314641a40006070300318035280c81801140300b00030f00808440d05900084640b1b5001d00100c03024088074071018180d660b4613603e251040e05400484003590 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 928241160 1250 928239910 928239937
    0x60309010b01021002031e06030118031d0315011e030c18240303230304200a0602120a1b03030f060f06050409020a0e1504050a1502150612010c05 64
    0x1365450f0102108a0004440040e500c1c21445910403204050703001d002e40006000d000410a200151a485500740a0090490019002d149a10065030b003494070140c4264048001d4540480480c0d80703803080c540180201c0303880040700c3e00010580031480c0108001541c1c00034450f0442075845400d01c0300c2412541c2e52201081c2481c04841a0130345607010714404080c0c10124030403032411610211f889206c5034070707c0880402c1c1c1207000810701d0043c10107144124070408403545c144107003000c0800754005c4001c0c400d0082515100c01d1000c1d0350003042c48030108240c510707083c1e15100c0c883c1d01165064610105291000d58401c2003005042c2d06812504100c3c90402e401e010803590348121440303c2c50366220707400003e1410f01c014424806a6002000290014505680c040e015840024440c400306a804541c01000140c20012400c0828040c4003d21448031100810b51881c54065101c000c61566010224441000540070780e0b551a030682902120000030041d440d444440a03006520041c0c0348001c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 928242410 1250 928241160 928241173
    0x9010902100e1c020a1d01150809120711040501060810060207060210020c03040e16030b04020301061d010c120315050d12120209041107060b010305060303090d0201020c060309010b0102 81
    0x61901401d80c040c0b00e040c0107080b01c407000810b0481c49042c0c1c1d51045007241e020f00303908000035170243d5070480d10070301007942051202c40794549861401800f07e00c0700d9040c180b060b0b2008020a481000c141c80b02100180c0c03034a16070352080ca00c1c0c81c01c440c80c02c101840d54001e203803400108416a200141504c920240000340a00c2d0381c036003100b41e03130701c1c2d180d4480e00005034032461000040710007a40190045080910071641440c0c0c075a03085640c1c0301d504942c0c0e400264081c0495440e07071a414051114000800c0e0f034114510b5041c4130008284042c100e90a0b41003120012034210103911070a0256040c640125800c00c10317450b0f181c0020080c162030007441e0018815500e01144524210030311070705496103c440004404079642098079100c20541310600c006a0901c40098139480d1801400b808400b00d030720541c1d840f43c0c545490070403200318049880c1054a040c00704141610004103d5104007003c643d421030560040c07004034a4002e103501c0e1113800010110900000100542103006000801d8095446 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 928243660 1250 928242410 928242439
    0x3090c0306140618060d03020705041a03060f010b04270c09080f1f0e0f0d0207150e0a060e0607020a080303060418050604020108040804050904120f1d0f0a080609010902 74
    0x140352404c01c0c20902c0612061307003c50a43d00d003900344c4110041c031030300666441d00d41c0e0b02c0c009411228210107081e5503120320b004c035203107918081c880543d0002480081d1101541020400100c0b4012409aa0040129800c0f2882010710740204800c8241c4518014481c2c1108194000d10342d1b0154404ca62151144021613138600002049481140e81104000212403842c0722208019090030030360b1241320301034070f0012000c4450600180c00380180c1d580040207a24a00b21042c00310720b098185060410603030301d00580c1c1e0f5541c1c0c503459800300c4800d0701d490790300c0e00d04460020312a440380e240000d5200c098101d00154000e00440514400c4030304075010890303200d01c020703000a40c1000303000042054208a001800540c000d0300710a400500174106a401c203921400881c050810a840c1501c0c60708641c401d18000b594000034041401c0d01500d081000c000c0081e016036003950729118642e209502045040820b920703000001d0005042000442c3c246d410041410303402000403400503030250601001c01d1031f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 928244910 1250 928243660 928243669
    0x102070501030902090a02030a1b020115051c0312111c06140108130f0b070e03010b03162d15020111130303030513021f02191e0303090c03061406 64
    0x304404e401400c02042a640e0000d90030007540002e1031000215510001c4c41c9040ca000307203140b1480c3c41d058000060a100030b500b03400d1103031490b0f84000d00c02c548084841000715211210385100a60604164492030441c1c40c0110182c05004805080d05a0101c0c14807035080c01c042d0f0419080704040010000e541e1140101c1000159508075940800c12140103c0c890607004060351155a018044079030241d5240c1d601c020400380180d540f00c1c0003690403140d44529240030f21030341c107420000b10001e00f001d41000d40c840711410035038496002d014030101c0d00300c01ea40201a4041280340150440e125403180c0300e0140b481e80c3c840c42c1c4210801507103041100b4202000c0c100803141d030b003c014900c0c0460306180d55022000f170000200741d01d401800644000bc01030f1190003c844550010307101e40342c408030620000900d049130100310320b150318804d04202004261860400c0e50001e00301c00d01c4007050300682c101a000750151600040000c02c4c1484000300f4840654013403240b00482d0300e80894192140030410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 928246160 1250 928244910 928244921
    0x90609080601081c030b0a1701290f011e021c0f02030f0309210d0c1403150316090b0a05121209130510031110020a12030204080d0e010207050103 64
    0x5002651000804080240c1c0b11310740c074640c0840d1072401083c0414418042401055668030100c01680e1181004514041c01e015280d58010105070b0030b080805030245441000000d40c00f018001c1442910b1051240d11690262504000034580724400051902d0000c4d610054000c2110081c0c3e4405505004284103524124103204198011070030030760503552291644c1c0c00030b406c0490030302c0b400b6001e2107030810045030700056802c105401600c2c0c1e0082d44d0b88105840e10301c070040c420012215059100c1001c02e80c160780e08264500024001e1410410100e4078006881025004c0b40303500e104009030480d82c5800c85c03080c003074054a03004440c43d034405c180b0007081110200c00301c0c641c200c0b07502c1d800130b940100c02034804032034010420032101075154404401c0351400d540c82c0e004007814090a0052020000100b94006001d4520008041449100a44900c80e03044010034050790b001201681902c00d40607a1f000d03180d108161801074014541c0176203030205c100300b190b026000b00705000030250f0007880391 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 928247410 1250 928246160 928246169
    0x506030a1101030f18050c10090609091107231902010c14010f060803070219050604090c44150603090106171f061401030507030912090609080601 64
    0x904400240800c015400790101000300e9994640e42d1707489a0700003000e1103494440034026400390469222410503c42c255120403000b10a03c445424100401d0343d10215943c1266044480010003001c010b200354014410040c0192050f0202510880032090b060381c0101002c8041c03048400014281204a040d4078001070081c2c049030001d20b50303101141002075a18507903400b04000040c07003038000031240111a1140c101200d29070010500c0401c41c102268450603154500394200400c600e0100000c01c280708600501843c59181ea03000701d611070060807180908140741c803403d0f0300818203020883c507049000462803000981c1051215078034801c195014007610303500180044102d0203805110f96640041d0143c08075650781c0f403000039040d11400d0303403885508001025102909000744c0c0d00e01301116024150407034624148042101340d400391450345d02c020082c200801c042e80e03885070035002840512405880e28224980460509600001e140d064803100d45901582603102c415165540c4400d005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 928248660 1250 928247410 928247423
    0xe010b280e010509040609050f1f0e060c1e0706060b0d050f06100f0e090108010b030715080604090312050705041a07050d11070b0c1605010e0f04020f0c120306040506030a 75
    0x17145c00b0a1480c0c00800300315016030102c4001040c0030300b085140001c0880003002100d000182d078843c1151501811070500d02d2032004007811308004030425814490303074a00b03c0401042c943c0d425038849003039081e911210f230009000c02c12035581c1c10940030540c2c08440e071142180d02d0200000c4030202d0b919002d9000f0710000d0455800341407803030f906444214268071144288644480d410303144d60340b10301c0b842d17011784070510020404043d200c4c01e2518140f6582c0140c031080240040c0c28080a5000540c40c3c0d1108080702e0100f4400103905042c0c1c0e1070590403a916809908003010010714940140045c4202ca0411824406d45070013503000d100746009004005140380c11500b547c6c2d0441d84078030030000145030f0120a80e41890354030030320b141c2aa803000d51948116040401e54040f042405550316004090130709040a10010050004403200c4019004a20032903001c10104a403851010030b030b4422901d07400440f1a500c9203441c03001440d40086030724030b00c01c0c0e0800c40044c26604001ca0050303441070788401c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 928249910 1250 928248660 928248679
    0x80601090209094005010525020f0d180810140709180b150304290f06040c030b04020a05090f0d0201050a05030402040f061e0f12060e010b280e0105 65
    0x90610f0445100c00e00032a01c51120803200d4004200f082c42070324007854640001098007404500d40c01042e1300400c0c800e48c20354201d851384c05640ea1010401c0003800285217010300141c449d00140c12840ca41325080586188110304404c216104240d0000580c0b0619401900407640c074000c2c22507100586c2d0103400600d401e15a03291a030021075030003001d00c2c0301d0018510301142c1c0b640c40420b0040c1c0c208442c10384005402c0f0f40c108241c503510401f01c104422100702c0d440041d1500d4600e51806500c06400c0d01d00541d030fa01d0b07035224014800d074000b644041c0700800c00e6503502480b110041035500400174952040314507000c5503040345085801020705d69410f031999401c10446400a85a0ba0401401a0b0304035032241c02080041c035083c4901c0340a400c502061171000c02b600380150066076000d40001038140d044101c1070251490039025114603030384c4001c01243b812510354111b4050070401d40d22a410481c244030f00c05e001d0311a100f45c640744c080c004030b00c4d010700c07640d60001c007459000030b05c14940c1111029 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 928251160 1250 928249910 928249981
    0x90a030f0204022206140702060306100e0424050307060c02090c120a0c110c0306011a07080a031d01140f09031204050609070501080c04050603070908060109020909 72
    0x2011060080ca00042c00141050782c0c0c1c0006948070030340c2e0038000703c0740c40e1481010300903240c0040c1c1c10044603981c0c5059900b45003075540030608911014004500c10070f6051b6120711034a104540c03454038401d011b4020300460b41402c800d05010361040220a1001549201c0406c081c200000c5510844105a03600e9182d01105c5d000d0010b20031300540741d0f034500401003254981010303c180440740503040210b800100b4001401d00101100c0000d038056446070403210440c40b0694000858905454129901c041103000405082450b4410900700070000703800814650141500b5901c40c04440b00d00041c0d40755410240e1051900300c51458240340d501c500041c0114008810400d004c3d9440b226220480e8600400d1001085241c00c04031022a0070798040341c1080107582c428022080203140030b0800700c0a50900c001076110301c0c0510300406018030000320014912621444090004014850036580656191400f0070003941c04051464000c010b14004541c0014448900f0040f00d2031824124130a1400c0303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 928252410 1250 928251160 928251173
    0xa06020315030303101e170706032306120f060a0b0307080f1015030219090f020405091308070f0f170c061302010905100e04050a02040b0d02090a1203031a0303090a03 73
    0x442061486d2401c4101d00461415140c60b20100483d00707850080284528201004096a03c07510340414140d010400328400440121041c54112800311a18001c41031071071089482c0c0001a411890184164410b0000c09211944020091030045d026540c2d07043e00d5410840d500c45184000301d2190b4000340d1544a4040e00f94040c12162a07803460001c83c003036684d00000d0390041c05800d80c3c0c0d443c0c15007800400050001c4e202c0c84600000c641c80550a040c68500041d85a4500070590401000058508802c01a403c4200c0f04071076441035203842c0c2010a41031402d400001481c080f203201c0c03941108cc00480354900b003a00c20540344c0b4401000305595004c15034140a0040504038144003107050081126a40d041070514600e40964641e000d44a40004120540354040c0030008100d204000a00082582004445d00822000c0000d0381d036210550100c0c0e82400682e100f41182074110085908041d815002201120841d804031031000c080741007016280d12032010150343c4501180001c00010b0308 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 928253660 1250 928252410 928252439
    0xc0e06041e23040303020c1605010f0c06020702090103030203030108121305120114130c1409281406040f0b030730051e0316080705010b030a0602031503030310 70
    0xa0744214160000e5030300204284100b000d0b03604130003081c0c0108a5901140c000c200031190403003c2c06e52900c0b0a454140080e10105007051001c0030016015502010302040e038040382c02d5107034054800300d4150f0f500e040013501c80c3c00a0280d0f22182c0960181d511040c0b100b6001e031247d00a901d407991140c0c520b80310402101c5054500216215503c45808006569005a0191040c03d0440c0081c0c4a140a0f02d030450340f05150350001d4903001c1090b042217019441c0e00c101c960744800c1c452001c5000710440006401d40d4501e802425925030700b400481220fa10003001e0040c01a5802c0c1d60612900d54882548000d03600d2124126402d030348400c402304001c42003944d07244206d4400f040304490b03800c001c048180d0001c0742131000355890b5014144003504100c41d11040d541014007480514105241100002c155062000002d001c003080400c24105005081d40103002c4000002d003101c0121149241c07050103500100d52840081000005031412800e02008591180d00454941d210241c140b0704684040304 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 928254910 1250 928253660 928253681
    0xd09180506041b031506110705060705030c19030909090b07030f06051f0906080f060105090f130f050604060806060628110607090b2b02070c0e06041e 66
    0x40c3c40701c0e40c08078841c0422644228038021a81e02044034045022201c8000201741d00039002c114508816644030a00402d452040d110116402070350f0303100604001d0302d14060102140c44502907051070341e01c480300c0c00c15030411141c400d07220000d42c1c0b640c40d00810110781400c107020300340f03001a0b40001c914521960045035192480000000e2451300d641c00b04601e2105003042c0c0241400a4002084058115001c0001482d90349414103c0c2c1c90302e042503501c0c014000d08100e041c40f6000c101c20030381c1e82da241100302040b00081e0605031007090800c0d0720000b40c0000e0b154651514a054045051820b00340155001d803501100103007560345601c002c0c0406503000d604d00b00d00c0030105c5410aa40040d4240c1802000c0075141c0c0c1e040003403540b9000c00c3c1e0804101402c00000c3c801d48081c108200e200701400d41c1d140f100311078403400c5503401e000b00c42400007042c1362804420510005a14040000c2500454155620b642006c01681d990b45c00b170004035100340c3c918050f100d080c004050304140c6240c0103280c844 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 928256160 1250 928254910 928254919
    0x415021c0509010c0305040f14090a020c0a170706020a020d09090203090703030c050a0206032e030b06040504050f060a02130b030c03041403160303061410092612040501020d09180506 80
    0x7d950f0b9000c000ea43c0c44c05410400e03c100c4a100d032141c01e85400122160001080c030300851516284034a96541c0d0840310400034801040c0700080d1b484080d0560a03283d10540080041d940d07801f0b2010002d483c3c6000c2c080340004113a0498020031450414820741348924034040040440604540b81a1030118401d0003c9400388100d0f03842e50016140d110196000700410f80d003040e01d068a21402e5a1b03105203055070b0315001e00110b84c0070008100c1c4101c026401c001c1c2540d001801d900c450074014100412100200203911840080c400c94448950081c1008130000100d094216220b80d10080280b106540110800c0400c0c0007080c0412100004000710303410400480c0d1a0807000d600e105140c0c03209140c1900840d9565004000422401d03e182c03851a10403034840480040581000d0011036482c0107000400c42442c0100181080c0110f0302036086a401c000c490304040141e218814503440b0380200c600600070240d134110454000c1184800340d802c103020307007031202c0803004107140101802484503602 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 928257410 1250 928256160 928256167
    0x607030f060807060c021e1003020313300305061f02030c0114061e1f1107080f16120f0305040509040c06110f060109051b0415021c0509010c0305 64
    0x14900c02c215440c010708158840b0090240280100601f0750390b040405e14140381d00c4a080b5040e6a42c0c4842d03499018264100140c41e510340e0404a0080c0300070810041c500240b000130f52480003d0550b8500c10041c111001c0e481805070700748201c05550381034980e550030021a40450704040c682c1d840400b031024152046a0074000b041e40e03002d09450b04100034400740340401c0280116030418041c0b50704010140700d01c080548186002280c01c849604103070001c0c07a80241039480c403451003400039500b45606a021240359035216008940c8413042c0003043e05643c0300303031849825400c8050b003041d011161100c0b10480c220001d40c480d0b00405030a11804c5042000c2000042071603a2010503042c0500d005111030320030075080c514080e225407a29016104654010780c40c036803041070000b5043d410f680c500d1002182c1074803a40080c5441100c10b2003130030824400480d022900404d800b94069500754680d08658024504040c82c454418418103000001882003011a1403540506031840b0106c1c4030740750080c41c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 928258660 1250 928257410 928257419
    0xb0115110a0b0408130f0302130509030a0c020a0f0602250302010804080c100c03020d05010b0f090f060d0e0a0c053a0c181a09071409090106030504050f0706020607030f06 75
    0x465001e00c6d0084018460001d00600641c14032002910103c03070b401d1002c1241e4100303450740941c0c0c0e0045a24030010405030007401e000f15243e00c0a550010400c80d0b00880e074880d15214081d403184004000c00308219842e401c07044034690030f4040c00003120340603120201c2a03282c9454140c0182c1c4203110100c054484c007403441100f00958031681d10000420b540050300d074109400060152001a400f2007080501400380e4511100c0c20422a03e42840c200c45041c1003403078140118140d80070311030006198034588600c000305000085401c800c254403c9440280c1181c40d041003002c5090842d2141902d0300090200c04a802e09080c1c00103d6204441d003001c407103415035a03078002c401c84541c209004400c4408105e00d07880e016070268026aa0188001d800ea40500c0b4000c60303050b02008080382c08200400c6004816079100c041200e0652001410342c100c1e568403142c02a003e85403d80e000caa6a209000c6030500c0c100300031407814141c2d0740c154083c208907120b0400c1100903100c1580c00d410055902e580008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 928259910 1250 928258660 928258687
    0x203060112031715010f14030a050105090a09050c1c0507091e060b0a080606040b070c05010f03051005120309061902060c0a02060103170909040b0115110a0b0408 71
    0x90007005444800340a040c06890001c05403201000c10b040780010200078003100340560500305128101c2840e001c201140d582030704951180c510b48004400401c000280140f8070982d802050580340181c9124040e41c5030071035424121112002c015100fa040480500010b01d02162002024003c1410840d03e80000b03844007414140c1c0c540c0070318401c60361001300e800d628400040d1403825410081c001c00c00030340341c007810007480d11078051000d08214400c1c00041c59692020142d074041e000f1180c0e4540c89400307524101a4030072450007442e000c01c08081c981454548039000d818894a0a040e8001ca110b160006000490b00072a441c25090300050160046030345862001d4111008400e8192800d901140c00281c2040320150003500708940400044030b541d5000a0354a0440340c0c0f20315402481040140c2a108a000b8115029408680c41c420b20040c040c1c03554000303040c0d4030316020326020328220170426103c1c103500301700c808a6900103028010104d002c0f4030078681d0040c09808050320b800318485100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 928261160 1250 928259910 928259923
    0xc100504050118032003060a060803030f07090b070c060813150e01061e0905010b280306030c091b050306031b15070b18010c0827031c1a18070302070203 67
    0x28030b0010070740340d10401c5c0346010018590401403031a8200681030070100100c4d00c1c1c2c0f100400c03408940c4800404100e2851003405060700801d450400942c5a00e00e900e04848418005d114807000124043c020699500c47c43c00f003d24820391001c8160003125044000300c0c05410b5401d020b00c0036560700c44c0300250f4a4190007031101d05071f60520708400344a080081050031581c040e0010740002200707202c01ca03000d58440ca140d00c01000409184482d007031402c10201c0150002e608005e003a44c00d00400000c085480d03410486440c48400e0b070174454842d404004449500080b5240b40d0f0651069402801080700d10a08901c1c01c2006402a228405814a00502035000c00e1b400c5640f0310340d841c2080074900070001805c090300f440d10024040d100903031a005002d0703a0f003c3c1400c2078002e03a03030003001031090b0106001c018a070720001c00d4035250b40e240b043c0d135180c24501c2005045014181103005c400d0800c034032140d0900c2100280704a4010801661496080000030203080605508103c0807025a601f0440b1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 928262410 1250 928261160 928261193
    0xf01210519020423040327030819021209060703170103080405090f040507150203070203060a0b2416020a0f09090317131403070605010806090c10050405011803 70
    0x20101a405106200403102130305550000000c20f41c00c040c401c00b0741010220742003030701494103200a901020001c40b4003070401805c00c010b50040c650000811035020086d1140401c81da82c040e29400b485034003642c40f8001c4071080040d4000400481c407007071500c2800340050f04e010f85000c034003801450410303101504003a0019505003038081010002d501c0c160174001d5000c040c166500905041c1030741c0b00c40d582e102034003e01c40b02139035400102c10414800c1098031f050907001011a01e040c104000b2500040241102c1c85004d901c5280b4a5100d41c003c0c26024101888004402ca00d403000500808214440e180800c030381c8840348070750001c0d01486c182c503204003074048014002009405882e01500724007400303600d8001200c4840c20003203070074140d042c80c80b00503030400c01e20721026100d0b5045a0441c4118031005000918000020990402c0092020f00c60544042118403900c442c07000c110070404d800f5441800500c0410080c801540f08405803a0030100c130601d03444929803a9950f42c1c4d94085d11030103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 928263660 1250 928262410 928262443
    0xe010305010e0c1516030314190501120b0406050604060b181003090b061e120f0f011b0c02010201090209150a0e012105191406010e0f012105 62
    0x280c0002520240183d01c00c0100440b40c0403070500c1e41079406603441c02034010560501c0340d40340b07003e002d050281d040846400c2075120500f91501d010340d172280950401d2a0b81c400c000d89444004175900210240368481c42d504802c0402c0541e443c0e41d00c600c05443e0050007290059101c0800044070034030a07001e045684480d048102e0034040707100600251462901c0442c00b058185003643d8003254195080642280c0f085c1e40700c0e00c0c2c61002201429100640316030050300b1540b206500d6047c18070103d00f880c140d689080076600090300030440309098030f814000d04030710036a50700c1c1032010385801038519110407881070001040450050300000d001043c100c071816a804003094841d600e40c40d000c0700200107018214100f900340d504014148001548039030100801d10317614151401885410403e441c1c0b9030304007440000e1101d0103468800c0d5410040d035511080c6100c2c0d08000b00d001c01c400700d5118891061210407404507803904400c14141c401400441c1c14402d4860485408240103020410307100c1038524 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 928264910 1250 928263660 928263671
    0x206010303020f0307020112020c010908040f090501090c0e101412011712040b160b0a090b0c07052e1401050a0b0306090705031906081c0e030c090703060e01030501 72
    0x24042e0038803462424140d0740344c008011090050780c00854540d10301010501c01625050b400349140d00402c079007040500000004240081d07001280c24114003910b8046400717110b0f60342c0c0c9600c00400c1d1015031605a001c111040c5c1301a4a90621207e081035004191502210003400c8130f0400302d5641c80806d0010076140c2c0c5200600c10b2081703e0801800300c1c00349034002c100aa509480c45003180c0183d009001d20013400103504403007060000c0c0d003042c0c1541c2240a400c0241407013102000182051441141c002c2003800028104818003030039181225004005440d2808141c1221201050b013442d0b03240c0030381c4600c11715659501c45481745014800e07890462845650401080002086256015800b41d4000b0810000240c4800441c0e5030404000c2c00c02c2510781d210041800144403600d180810354034076050001491240004094070101182401408900e201d440101d035164440302000b42c02d0b90004080685905100c258170394425003d280014a07541c5030013040078498801e070310649260b91540c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 928266160 1250 928264910 928264913
    0x1002070b030405160611060c0c0a0218010317030c0a030c050d05040309060e0d030215060402210f0c16020f0301020c0a030206060a090b0907180b0d0203101a09210d02060103 76
    0x5604600181c040c0d420005000c030032400c030311b55a9600c0100103401000000c26001800301041081e50811540100902c038444201004200358040c01d110998812940c2441402c00340601d0084900030745c1001405403401610120640203419140250350801504000e034000a04043c07044500aa1003561031600c014500b66005008a82d89003d06100345100c0c20104002600062189405004018810404e0b80c401000070001d0150b50009038002c060507009818640b5030701c844034403848102c0c4900860b034865009e668107500034099070f88200b0303203c415500c01600e8031001144400c44020b002520b820710a841c45424076100d6801180580e025500b48a06407511615003006044500030403c03a0dc81032071300061b4050405807019092100ca041d40203c00c542a0011001412032001c072aa540d414100108000303600488403544240390210780402c020300c0201041c195192661507042c1080c902104001d10319000060441528941c0c080d030f0051081d042c41102d1914601d500038002e9507156 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 928267410 1250 928266160 928266193
    0xe0103051f050c120c040b04061119080906130b040617090c09060904080c03121519090e030c070608070206010603050c0d09061e1a0108010e061002070b030405 70
    0x180c001e0004909080400c050600c0e00c4090300e48400d0ba000e40ba684989030a003c490031489560800381c0c95800019000c941190480c49420302c941044040740c4a409421240c80060f0324010002404694208008007240c5040c0014000c6020780d031003801885a545e60040480307603c40c0d40141c021804034110310019000d44040300b0b51104500c8040c00d010b545000c0041c91041c07000301108d10903120800030030103100c810826140d204140e901100c0d921013081c107940204490880d102c1184890801c3ca0000a0400d2241302c00080d0740c00f0788000c0e02e1410000e1245c060080d9000d403244130711052204480c0d01c202002580018043c07515203041a08040c50000d00381401604460103040c10a002d00024840e50400c035800c1038545003000421800d01e16000010700111943c1c1e49001d00c00401e242d0720094035610036030420503000700c4900c40c48a502e00550740712809100301078418603044001202420f00c01e1841c0d4000700c540c41540c40711901e481104030503400664003a201584115a00c5070040d08 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 928268660 1250 928267410 928267453
    0x2060108070e040b010b1b0607080f06180a1817030609091507120f0c0801080d23180303030f040204060b030c07120201180b090106150516020a0e010305 67
    0x58190082c410b9140c0b503281e1103000700041c0301d841c00c030000004e020548084507072800100d455000040c1e40c16401c06240003444050242d030680448140000424110310702446160004d0002059000c45540c070102c61030001c2c415543c10701d1030580f4003010f40000070142301d02000340c0780307985803115140d003884d000344084c01c00000d0a49107550310416000001c110700748580c076440b21061804041d020040b00c0c02c3c401516150750030549480c2401060315201ea044414107050743c0da804111007002c40840b0084500050725040c4501e0111050080745c40300d205c1c1e03c02448800b11554840400c0c001c16070110b840c50380700702c80c0314400461410034801149010301aa030000d20b41c440700e0a081d400c01030341021091181d00b80c01020500d02d60440d0020500039000002d0b20410820842c050104508144000641c00c9a030014a03510f4294007046100c00c1040074424800d440d90366a08250800d015444d05c903058030401d1ba40665181e000090156003d00c8950181d0f108034003500400c203600285240083c1c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 928269910 1250 928268660 928268669
    0x3030c0304080f0a0f1502071e02010e06190c080f03070f030e060c1615020d0e15070509121c05090301150608061c0f0c1d1b09030313060206010807 65
    0x811407001360003c9211003200c11292900108581101904101d140e00244a00c000080804a01103a00040c440506120810f514001e80b154400001c2c10010002c0510a000301d4160a141152900300424070560f0020701c1a0720a210040c6803450403d00aa003507003045540c2000100302c1c103800300c14590b16000d41008580c944009201c2410300c0b5200c091075005e5206031050048558200c0300901104840dd011a003861440c11580e5031400944071000d000c0d10041480c81c8d00c00c0400c2064051070940c802441400b183c0e940c213040c681c8101c10000707400c80c441c40d46c10840c17064915008800300c0d10300307050345c4104094480c0d5640b01011001c2c1401e464000c0b400110810760a6010084103801010655010764115511031604649800e40406005442c002170308082448580d041003100c16908002960346410b43c0001861a00000c0240108220380041c0203202c1a8041501e051640c005020500d000405076802d103810410040c640c402d05602034001a40420010840401e00380034a10162 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 928271160 1250 928269910 928269913
    0x10b1003060605041818081b060103020619050c010606050a030609051b0a0c0b0408031f031703130b0a091101030c0e1005130b0a030501060c1e02030c03030c0304080f 73
    0xa52820342c01409900031403254203064410361031551030f48a582e900c0400c11044001c41d035008560981041006030300a1480c0124155003090f0b1201c10b5840058124109c0713500501c4c003460f00c030600c2d01c100704000a0401d41d5040c01014000c2c80b032803640030300440d8050860b55945c141c0b40c03000c10304003c050f222280d0082031400d24000602c00341c005105807600fa14030340b45014564944a40904894120f00c0b48030103040d5000c0762080c001000340000043d0b002c5c500d40130741c035543c3c24110ba400070521101c80c03100038441c25609406d0781034492072102a50f4044030041c07403048941000e840b040f03807101080b00d43d805ca46690b081200d08001003003400d1f42840a003881c0070025014009005403107815000300146c4248250070308410020310a4085079459242010704100c240c0e030703c400e6030000390406154a00403d0070500041042440340042c4112250803100c1d05d400700e5004040c030104c1120200c030076038050050005840c95a14204003c181c42004140256078a0349400d00d240e0810a0071040302815 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 928272410 1250 928271160 928271171
    0x11030412080916080f100203010f0303141b0307120305102304020c07080d020a02010e090a0f110c0c0a08030301210f2004090c0b0705100905010b1003 66
    0x424000d45100e15000d00c24103011085403140180c0515003800400705005102c0c44801c0842d04400c081210a500564a0121905500d411240000f603002c240250300302004140004c0000c81d00c03440105e094a0100300c0d2039883c0085102c0400d17200e61402c5542c412540c0005595400c101a94221500508203032400f0029400d02201d1a5088010b51140855514410409444441d4244140310040700010700444d510340600001c50348522a6200e810030038000c90000a841c940003160350341007181d0580d40c501240e0600004c012498001800c0c0548040c0e8860301072180d8200740c0701c1c808030b0500c3c400319607450340081011a4609005240c480740514183c400c108500840002030f80d05544400e1448000443c92101e16601480083c0c00540702e06161795060303050040100020b2200b0303031101050025030a85c1000c1c04162001490020140c601804e006c0002d81c80b000d0150209d14411416616409071020300700741512001c800a95586c1d54400c240305091502420f0301c1a0190b131820b0a110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 928273660 1250 928272410 928272413
    0xf1e0903030613061d01150e130f020d06060e030d02010b031c2d082d0c1e0c060106020a050714060c030c10050112170a1b030e04110304 60
    0xc0328003029101500a9924110400c520600c3c0d030000006061000c0d4410180c032144410041300074420310582229000c0401240c501c030b4800d140030300368590090164070640b20310078082002030a44101081c60300d5401c2c000c601d824407040c0103510080c503681da9410b1010b481c100401d41403440040051055a2400740c1d2207040303440c0032440d0006822a0b040750300321072014100584403c0c1d40410001880545030104407a004440240e240229900341d954600b1503503203084107403c011020f03117242400718015240c04086c070542c03100c0580c800401c0645905103902c10159008a000f1340000002c01c03c0d000c03407000c1c0803d004104a5005150070301c0148050105519025110a180e0040010000e0408801c1040d500c5060888134003403658802c0741d81e0ba40101c0d030b0481d104c1413007080d400c5071075041070000900c00d40c001c40700f003d901d030300000300741d05105c448184900b00f40c0c0036a903002c061003194000c00b0440b0000c00d00b500201406620344104200d60030b000c000c1203413025001c4400100c0180188030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 928274910 1250 928273660 928273663
    0x61815020403020f0f0d0b040b161b0f06111c0e0303130605060d1505040203070512030f0c1c02070602010c0516110d020a1409090102030405031e0d050f1e09 69
    0x10704c0c2c14000c2d80c00782d09102100d00410241e04519034040c0c0481c100e070342030008115201070346602c03842c0c540d119903c94103156142240c061403010041d0510002c1482000080b45044030f0f104921803184c80002110b40e0050075169007900090028916448031610b0300318460040d0042c60340b01904680074518603d480320000800c1c0501e0480075101c0d0b991a00000d50f40d88600981c4444941c200c400500c0c8540300e016000e0290204450490007401a81000140c5003422480f50b80b03048440307400340d030404a481c90000341035003240fa1020800e02c0349120840c5d9601c0d6540881d00110311913800707880f0842c10600040d0079103920070001c0c0b0410108200315001040340016495070700368000501c54681103a8000a020002c080b44040d500c0f103101080010a08040c03000181141ca0903140054665540f0011908038041203401038110340003044100407080c0020042c904018200303141c1410444001e0303801c0110750040fa15a10703400049001d03c090751140003034094164510242c0e041103483d0082e88503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 928276160 1250 928274910 928274929
    0x15050a060f020c0d150f270303180b010816081009030512010806190213060c150f0f0614010905010f0323180f0a030503060a0306181502040302 63
    0x40c010000038141c0c00345041c0c8207016205903444010551800c0e160340b030400d9020a0002a10759609a240005120f14181140143d080310310710380c1c0101860400e0030005481d01522400f044040603607941c40080d481400496540d1a10701030301c085600e540c1080348062800c82001500d80d40ca0041e80e208200008001410050070901400b02140c51100c40c5001d8030b040c0192001e015810020400104191030000b4541d8481d01c440760100302091182c10a82080388249840f000d04841000028070025000b0b59107140441e10a03000c4e01d0324016002d406400321940d1103075801c921611004e0f00c40803a0014016800076045500b03909007001c4000c400a800c40c1000e205a40c1803040076401186014000d60240f00c11140d1310318000b0101c00030300f01000c0c9a04084403003981508024903840c1400030f002400d07044451128000701003004240c3c60a07510f507000200300310382c011895400840010b4141c09125000841401c218180000c50f01e0102c081890600303203000803900c144002c00140c1c1d10203e40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 928277410 1250 928276160 928276169
    0x203041101020615192d09020f120403170a0b01030b0906180603031b1005100f0e04050c1f02060603030307020c120f0105070504090605030102070c1512060b0d15050a 73
    0x10304c4911031044105c03030140c8030168804d010900c4408166155480040a940c5000d68030050b28103105803910300060407402036050740402458184041261004103040d0b0781d800901a042a280301c6890900301070b030900003103071034100144d1070308040e01055800d4091260301c00e000700c503000340c2480d20401041241c9140010f00d840b0f50443c4002c14180d031402c0c02103580c02c02c0701007000c010300544106071075a2142c113101d00401191607c40001d00c40d41c0e2407100c0b03c0c2594401100014040e00c0d00610085601c009001903603039019100c1801c101d50b451407400030a040580022055001c0e00d400f000c2d0602c00020305c918001d03041001040035559011a00c1c5011f100100ca01c4c004503650203021a00c0c14190b009031100c15843d00c42070000594021340a8821a0265030081c860a501e803002c6c1401d0707024034140103007011007580040c850015149e82181c44a2083e19080d156268034a610700242d64031a4450003280e10b0004040301c101c00c05001d0103c544016074510141e0380d2030030b40031420100c101e114 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 928278660 1250 928277410 928277419
    0x6030e0102070f232803031b020a1505160804030e04230f060102250e0c1903020a051c0e0a0c05031902150307020a060204060f1e0804031b0f060203041101020615 71
    0x285c3c1014060352100c4240400b0b44500e50b48080c0c44d00b000396490f10b1585060303e4036008100e1100c4801914021640324682d0b600791440c0d000c60b100416141040042e0044080c80b0250112070420340f034903c1803100c1000d01101505a8400000b2500500d039405404411040c101e4020001941d0f000505883d4007080307641c04101e49401d00b001c102030880c20303070814840c0ca0a04000d01c60a56a100c01500307602d080d0000f208488400701806030105c0c031603d5000404200d051200c3c001c181461010204c0558040e207011403240400ca0020307003450410403044400b590401805d10080c01d04104225049030070361444800e0700b82d03d80000d10342030347d01200504152000000540300902c2031010b920b540340e01c10020340d00c03070b5204c00001d0600d00c618184480080e41141c02c4419a600c252041e107513000c55912480c02645503502d04940d171a80000e40c031040094508e411000007000031804081c4207015100c01a01d9040c82c0c0761058550f07080c0020941198041000d03c00c1d980a4100d6003a0885002c0b42c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 928279910 1250 928278660 928278733
    0xa0309032607050307030801060f080106030507030e2a0604050a0b0d0b030a0b070806010309080d0b19060c021903020310020d06090c180807060906030e0102070f23 72
    0x316204420852801400c031800e00810b504041040000180511920035196010035a0b2510000c0341c80b4a5180011800100480010030803c1c0c041e510503138200b4054a004103890b10980c2d40e079407030b181c8010f0000f044010046004942803541c101400f007528021205523140615000000301802030074014103140c0580003500e5880c07001c0a0380710420f10100503040c0e03a070710307800b904100e81108001c0f100b80e00403841e15000191690302ca8482d2401950348140001e040481020703031a40200b10b51000550000302031803180d041c02c990340380f0050050103944d0340c0130100180d074030511411000a07103d2150010084c00d00b840140e0380455100300401e8500c50051b200e04603107440801a040960007410324914050403a0b1b81c5a5009100c400d500318031a01c4000361940e18060b042e56400c80340b00300d50018501110034007203680700f41c10481d070140d590000541400d01c291112864002c07410411a40402c804080301600d4414a40150801048501400d1180c68225a4100c100ca0040c036140e010350080 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 928281160 1250 928279910 928279943
    0xb03030306030c04024e10030311070b1b21040e0a09080706060608100e1605190f0207090c090b28030e0118080405010309142b020a030903 61
    0x1001500341c11050950981084103c6d00046403100d1048198180d5107101410080700c281503200c040e0740254880643e080005143d510101c50740d40741c14454038110f0007040340001e09200050050103040e2024088040c00b200a130503840d14050a0340145441d041400300808041c403a03001c1034408a074502c000c00c0d941d60b91520700c9a0020041604e0040101401060600038883d541c3c1c000000e0303071a240c544100c50b0b1507000c5907aa82500c0e80c441c2c41a020140300004054a09070300c44210f030b005503810058101441c801c2e440284030040c107030b01000143c05034600c01c0f545038100801802000184001c021406002c130700246001840d000d00e152030100040c80d07402410400300c2045c50303a450384c003607450301c80c0004100801810b460b89255001c1e40c00c00302c80201d0340200300060031006501160252520385440c0065014110300038055912840c03c000e01d03203101d00c040c0101c510702d0803c003448503641c02d2941d22080540d03484500702c00440d882000c01c840005e42220300903007520703048900e051301900305 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 928282410 1250 928281160 928281187
    0x80903030706060b070c090506030606040c1206240809030a0e1309030e041a010207030228141302032211040606050423030d0c05011404080705010b03030306030c0402 73
    0x6001c0300406291801c2000038040c280c4602410546100c0c41c4000e409070358898510b420384000b80c0d011507142d04107001040051405070301c5078400101c141450440c980094680030104c440540c0041c44501c240c00706142046c2050040d40c00c050310504001049081035006a681e0f4041c1c03030b60f0702c01841003150154441e0b95900c4202200b43c03001e0031060100c085d06103401012a254200614000c5061010f1400c80b00c406104020812506900030103e90f8699020080008021003400e15448141640101c640741040010b00140280a0b000040f0040c01ea05106d400d280d8561700c0e80c03040d44140300f44101d00142c00c05220301c01c64019450340311401181070440c00d91020703405965000b46040e00c002000c1d508200600708450f00010110682035001c4203504c9080307000c1850940c036801c0b400c0c8a0680500410b204010140201c00002c0d400041c01da01b42c1c80c1c0042564241e5404c4004100c880802009004010402606401560850034100c001c60b5644001c00e80030740c4690780101f4501a00d540d03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 928283660 1250 928282410 928282417
    0x1401060813060218010923060d02090901080303090d050301030b010e0403020f0f0c0a080109030f20030f191106070323070302120c0306011232090f0a050a08090303 72
    0x40028003156038144081d20745407400e0b1165441c41c007042c030b0300f00005042c031f005418442120305400002051242c2c03200070001035910074003060302d041c0d500307015840e010b4440700c020707c3c040e06d1914021596420615949850081586010300c02c0210810040c4005042003242030304545400f501080d05449610301641840105d10161402e0b00c03490180c1e030599040002c00da038413601706035082d1101907100c0301c2c1c0d5400d07a980c00d02c0180108071f144410300c400318851414160480d032400109640e03601700400c56401d5621a08503142e1030f000100e1081c2d519000c0708100b100311010390402c40000503d003020651035031002001d00d800e00d5950100032080c00c0751800100940c28040403d00caa0f0302d000d000240c02500b09081c510105208140041c0c01407031900308a034007035481611244403e0003510301010190044012201032524040170f00d0005d40c0080700c03898010700101c203105c0c1441c60640d00662400d80e0308003c101d002d910410030709012501c04560320100c01c1d0031180c81e03641e60f55080c0c042442d510 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 928284910 1250 928283660 928283663
    0x2d11130e010c09060e150306061605070306051005030d140f090913030206010e240d0203060a0e0f032a0c0303210606250c17010509010507031401060813 67
    0x508000780901900d90094503c0b007554a5920f1700000501d0741c000b0f000101c842c3c01101d00d08000c0c10008034580307251441c0540b180c24102c0e00c002a1030015507443c2403c043c0c20b46c0c401c0f600c02c0e450f50180301c60944400c81050103000c0c01d070020103003214818401401d11501c5d0701c1c0e450742c82c8000184001306da10214225051441d000e4001e0b00b00d818084100710400e440f072034042e801401604000b00380204e000300b2060084e600e10000c1031621084c4c60b44048584424201c0300d81c01226030040d400181c030180006441066800000a2241d48540940d41055404c494580c013a4004101c02c0d030f89417450908800c03003400c090b10707550061074130491020310f0179079100720f801d50612002c20050300020742c80d0b9100603030f1241640540c0198807440c1c24000d05006042e12480c13094201d0f8490030903a811800221001405480e40c3d80d0495a90300f00c031100740c072102d94100b1140c0d44403410030085c807200340101900003d5500c0d0070814150465295266070406005690400c52100081826100c43c030b8480380882c1d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 928286160 1250 928284910 928284913
    0x30c0f08061e0a06080402100906090e0c071a1006230906040509090f1b130905120a030f15030b061306051c020f22021608072d11130e 59
    0xd5144d20b070181040e01d04035002c034803462070100e107050751030700c02c401c194100c90094490316801c0d424200d980907004c03070007018001036003410710015000c602010314044103000c1905241e803c42c185821040804030700c68000c2020b2007120200d083c00c41c410558030024031b00d0000001520351901c140016101e1195030b0155034890009000c0c05410200030900100e450540307011035902c480031003006030000b03411f803002d56441088047c40c414015040e80000e030f412486501901d0245007420941c0c102e0341c0140041000081d641c0000181d021840d20417501241c11444101c0409403a541c0c0b0f2607920000142924001c15481e070021821000541000c00909402020b0a07202811090101c2044c800c0c0318040c2d124039801c405800e0315003802103038035100294904c010f200383d9407104c4444000e58170a43c0c070850440b00341c0300794030045480308010300159071144441011a0010800600b000b0004115405004400080500c0001c502241e8124031010541d441d0015602d4544024010701400c030700c09041d0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 928287410 1250 928286160 928286179
    0x31302041d06250519053a020f040506130e0703090b070e0f040518030301080307060b190302040c03230a0f1a0913020a0b0a030c0f08061e 61
    0x622002084003071164100030030540002c44400f078214100e6400e40c40c1c000104030304020104010360201408034145000d410410310b407400700a15010440812002000b01c29800b81c04040014507800392003541000043c03003581020305500480206e4400d40c8140e0344901c500184100c00c0c0034241c050b0710010a6414000d00941c80d00c0d00340900541164001140d03020001390004900c00c3c000c140f5028040e1000d000c52080344100402d000041170301402c00003a01041c01e40180b0507900820045000c4c0908001031911034980d45880c0041d01c0000035290300c40c3d501c0a4400c1c01342000c0d520000e08a0f80c04a5021039035050b000d50903402040c00c001c0302003103101c0d18690b5800e480a180c1c0214010245840d04100c44800d80b1100800c41d40c4005074030400c10380c8030b914645203261100c41c1c00d800490b58801c002e00c1965a60000d66100100e5020f04000d60011440ca5060b5816100c1c0d15540441800c11910420110744000c00c1000d004011078859160320600e1491029001140803400c9009041042d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 928288660 1250 928287410 928287461
    0xa03021504020d380f0a051005151201091e09080d020427020906180f03010e0604120203030c07240f0207051018080a020f0a0c050108060109080303130204 68
    0x80c61004145001180003825071310b020040c3c1c501c60268402c0350352140b01d940c1522040741c08800742ca005051a1070b052002003010400c0e69034041d1b042c680407502e94401c1e550325403114011034461816480409070347d2805040d070b000f03100c0d04a4941e103d20120080000c41c0402c52505039414001c0c01030327290f5841d20101d004580b1846120a40e01d040200804a0350f01040c000841410303413148202550704440248560700b2402c03401c44048590b42e80007824100c4606800000c43d003180c9200440e420298000c9042c0300c240b00784101b4507030500100b44080c40c50b6290422000500d131245a00081a849081800d02c00d0740800001c0740602002c0404148001c5100d1481a00030750000340054071640252802401055642c0c46021042c400d040d00e1090072002a0315545040e410103120341042d03009414090f03100e0702040c0840b040c001d01c61011505424101400140b400d5002000b19051150198080c00039035000020303654032000d032800480301c8102e03a101080240c8460320703891200c820180c0d1030a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 928289910 1250 928288660 928288703
    0x70507090c051c050601021b030c04092319030503131401020c0d021c0302030601140d051005060a080604050907030204020c100c0f05090f040e0d0c12020a03021504020d 74
    0x1d0f00110030210f000303c0d20640c0ca001811980c0940300c650150f070040d0501084007418803c01e900030340300203085d19981d104c004041015206841d20880b001e02101840c08641c0b107880d000091866038110007005910300b50761040180380749800020b000c1c41780101c0090744880a00c0c410f00c18955100055410302041628028003031341100120b104140500914401c010744002508081c101c120003d203402c070046100c0a400035070001c0d04e00f074108003502c10358087c03440000000b061408030f20740c400a00c0707251018981d1104456070300007a01c00d40c400c001010030369038008090703074012508a9001801e83c03900c5280714900704080e440250032a002003000d0280c200e002c61001741d411a0342000b40803882d003004c400c60360130004a6004000c00c0c010321945104e400c044d5210110080098000650018ad0035002840d1440002c180c0b0001030600020204100e501090450240c90f14002440481c115a030042d407142e040ca104035180060b060700141c1550355149070040c466422041c0103040c2c254040010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 928291160 1250 928289910 928289917
    0x10f260a050a0507050324180f0a020405010909020f040c110a0809091003050a081e180f0901080c0909010212010611151510020c062217030a05070507090c05 69
    0xe071003074061350b000010281408500801a100100a000c00c0300d1070b0011048802d0801409040c0760700c82e0010074115174901040703903d040f032441c40000c2c00c020849104020940d241600118005414000701030016120541c091040410440300450315060310481102c041c00d510b0070b00703500340c8140000c03070041c4803501004024200098811045664410124061603042d61000400d580d0040c0312030004a940320024208101e0040100581914803800030440350308081d94403111814a02400021450240d0b207c0069150a8681000a603d020380e190b4036492850202c500500103140001c03100751080d030460340030300030f0b010155890356100c020050041041c00328141c010f100da61b02d43d019040c184600584110030074030301035451032028400d00021030103141c2c2da141903106500b0708805036551f2401130100001440700790807070700b5076041500101c00a503600800694800d00074085c0011310100803600b143da803038203180380d48504034a4a50715007d4140d02c1400e9040c9044d0041c0241c55110004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 928292410 1250 928291160 928291163
    0xc050f06070e03070803071a1308030403050a021c09051005130e1e060d030c020f0406030620040f050609010507140102030403030c021c0e040e06090c10020303010f260a050a 76
    0x103d50307146881d541502c0d03907441a0400070f801e400d980c00c41d407100304007014007150740189c00110801c2c0100075940c5514032508195412004954003040c1c1001641e0304104110342d0525412803e200358270034240241041d030850260a00810041c030b40d0f0310040b801081141d01c1c7e40c4030201c1c90001075513107040c0700001080c15914810681d00c02480001c0e0962200c4034a07002d418020302c003051400103650143d80c840306014040341c01410414000046550b28880c510046001e0707403021818407140c0c0c0c0e840703280d07405080100000c90380901041c0014212401c41c081662000d43e8100d50b150350810040e15103000315140180112130303094400700d6441042d006513028071321030b440a003c01020030741c0a903110030480740780151aa142d00c0701c01001e50f01c03810316400710101c06040000c451603100d05850400b0300440b400202e5070300c4100040d1190a0040d40b400020003a480510304550501131161169040340c1305d003004940700c0c08040000b40c403000b0030229110b81e0071400c4038a91191454425200d07805d03103a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 928293660 1250 928292410 928292413
    0x509090f1015182310080f04020109171c0c0b040803060a050a0305010c2a020108220308040c0501080408030a0c05040b030f0a0b0a050a1a040504060305030c06010b0406090302010c050f06070e03 85
    0x2138080c1141000c2080101e101c1c01c68684000d250355407030034902e8100e4010800e07410081c2c40780c000204c405c0b083c090418050f507810b019040420460005500d02250300007000100711902600c0c8000c11020303607220340c005602c00f00300d40d5240c5403607000940d980392942103071b50322050340706001007000320551040061b60701d184c80c1d01c074802c103a00000342641c0e1004030700c05400c2841a94448015842110b9083d8004840c4810368000041000001c40440c403111044011800440034802402a010034010080109107000d001700c1c0707031640d00c00381140405401c44000d117481e402c40c0010b00380250166005800c524030a40d07100d1070f204c0c2034403217801d500f0399401c0f001510340b41d0b203018142041c0d40540240d27240600810143e6180c00d801e81c40b44030b0001043d403c0032006102c042041d985070b004000055016000079500e80b11003061a80c103220042e40207100490f01080104002d0b0341207103481041360b0b02424121014010f40c2005400c29860f1000f00015000d01e43c02c01c13012a4100181141c518410340 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 928294910 1250 928293660 928293719
    0xd050f030409050c032202180112150e07031b05030328020a0c150c06051512010c0e010804030210060801020406030c021b0906150a0509090f101518 65
    0x1854080c5505c02594220641001b072680740088080521450801c41e00c043c0484540c862201030030341c4000030030b80081a000340c03451400f100b40f00c4041d03140c508551491004101d640e80f01070100d035070ba00091000a001154280d2100030041102c060b683c02420042c0680b60749046411402040710703a800380103030f200013045102280140c40099101012a0b0104080f00154100764105030007400c0f9000e07070020424041d02000c005000f0303010700703400b0742d40e5600d03e024450080b804021111041c1002c4524680c134100c0b0288200d540086401e20240c004c0c01c00c11096155070508900303200442040401c01401c0036000514960150300500880b407444d5400c02c4003884807201243c8503181168080303000c80c81950b88205a1401c4036034650000c40042c01c8614032401400c661005800900b1101c01280c0081030395102030401c100314036440400f41c540c0d541344d45000403a140c210303c510b008000b00c50b100e90f070b9a078007480d00a6a40c030b1403510000b0088402184c3c1c400d0340034444070401240d13070140e1303e20301c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 928296160 1250 928294910 928294921
    0x1030501080312181212090111070f0b04141b0a0f180507050702030f060105040f0c050d050c04080118120807050304140705040c08040506010b04050612060d050f03040905 75
    0x441500c4901e07035050b0441081d9101c942c5281c1c0d1451000313074003031070314020801d1401c228032000c4000d20785201d00d08588613040c500f5001003401c48001201c20031903918101f200700000346501c01500091948000184680d850350f08020240100e0f2a8404c000c900c1407420121000e0540c10440002d000c048445c414410380f508100040b050300e03840313000001072040141c4406e800954009545c8040c840c5400c509084c01ca40001e0310300008542c00c0c007219040360006101d00c0c2068041c450710526002c4061188204007100108548514007078103058039503d10205400059040803240141360000080c0800149010210b41460700c80c1e40444403031000c4082010a0783c0100441803095845480342d50840e5201d84541c18031483d0810450350a0183e840085180d0340d491040710040a259601c1c081c983c585480c02d00d182040607044514810401c2c841040310365117040841392010002131401010791215408030746900480d0350000c00038040c0c402d03a031601c20000000b50080b42c0039a442131100782c840 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 928297410 1250 928296160 928296163
    0x7030b220b1b21060d0503070c06030b01020d05090d0c03020310020405092a0f1210230f060906160812070e13020703051603110c01080c1207050c060c090103050108 72
    0x8075504200c8040c0d031058402e103003d031203c12181d07100102500341944698a50b481c142182e00c0340100300d84203800e94000740000f1390b0602c02c24400031400c0c00100310a516030b001c041c00a005d001166417041402152003000c0145c3d0034904401117501030304442034403002c214494007035040303401801e0042850380000303000280c0c04100366101e404000540c8034080ca40b002d1008075940410010050503404111100c080002035164511600080103809251810214031000003815860001b0121500800740b010590760704003070400101045510940d2010351101003226401000740d24842212541010b40500c004200240300e82d00a4410181d0540c0da00f81e002c0d80d04c0303030b030541e0003d800c400841098078544c1d05035801000164004d04003203085c22050002c0384510040594200d0000d503000308a0f2890190400150f00044402d0a01011610f0031070394100d0356019170b401c03080030900440e0101e00e903180504102d40b00c030070442003641c64501d4408454040340d4048600fa5001a18090000840000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 928298660 1250 928297410 928297417
    0x12060e010504050403020f0a03091409090c0103020307090509100509010807180c052203022106060d08070f030302030603190f060e0115120b06030a0507030b220b1b 72
    0x865400816180d00382010300c001050010822015480f4260896040031410088055042e1003596100b031100d00780341c403941d840c3d03291040c018014080002407241e0700341c001c2202045800700380707130041c1c40340d43c0e40a0440d894111907021941020007402440a5007445010000c1901c10603501a0601c0c2da84e0f1050356500d800034444e0300c0766036000703912004a0a40343c5e0401000302ca1985030190400c1102407101800c0c420408009000c4070583d58100110f0525250140f000391001600101c0700c00c42ca404240c403004004d01c0c0c00d02c030390702c0e5142d09402c020780030341038411042d00444110065201c03860b000e0020350042e02d0451203840703010302440608201e01d803559105584005060940120b680e1110081c1919100201c195500d400740f6900384081c1460820003008090030388030705440c0a040c18203240a0140c20107000350450440701002c5540007030fa040840358020341e80784443c0da64080c40a000c8050303090b0070350082080c003110003d106150f58124005c0c0a0102c24881d011801c1351004100d10 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 928299910 1250 928298660 928298669
    0x1302150d360b0c040f1706090706090311030106081e1006050616060603120e010e1f08040521040806070305010302130e0a08030c1902030708190e0a0b03071206 70
    0x192401c03000107000c5842142d0807620312030085003015200e142a40c1050300e9a0000300d6414810710005207080c008001061f009241720016294542c10071070001e200c5481804003410fa0510102c078001582c03800d602400c011b080d01c4054a041c000203081d145910303a40c046180026100300b0004e1110304802d0302c0754400b1204010022494104404c56a0081e40f00264083d9151650f6000000110f00f440c0901c2d80d41110954501d001803032201c00142c1400056205180100408044400c8170710395084219600340ca507080103501d41e640c5141462501c1080c0307111a050310922440c400348040d04801920079581d0035015149107580c0c04070114100c0b0400d1002960100302c40c4410041d00800da44080c0f07101d000d031070545000f8456500c98160740e9000382d070811039402e000207400342e20b040c94420f6414121420701c051843d0503029101c84205020b42c04414000031b01c04500e1071100d1380602ea002c41c14000c007400c4504042da07140070040140d04126040000326a03104085a944481c0348200340584 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 928301160 1250 928299910 928300001
    0x207060f05030907051c1401021e0702060403020d021309030801031a07140a0207050301110c060601090303020d050918070f030c0513030b09070e040503030601120b06031302150d 78
    0x90714050800c9814003c086c3e400707600320381c2e4140e45000318800c5512003515030241c0b8000b580ea201b4001040c0c145a002c600000710100041c0302020041c1d4407a400c90302240d404446e0a43d071b0001c03500015a0064007002c240c0380c0c291a2010b44420160803680160490380508551051002905480b040320503007110040001200c0041001038005502c015210f10b21551040f200701648501c0440e003180c1003240012a0100042030114040004110301c5078481001e20303180300181c4c82c60790060341d41c00390080940c060110224140e40f80da2100c1b420b580900d04510305104050900ea54003401c65404081c038640000d0401000c0200c56010304110366210f829a00131582c26440e5032a054020480688100c01c60b024481c000200040d15903540e80c0102d0184014507660305000300098050040840701100c1a4240101c000050b5146810b99620402e00e80c1c40b0755030f98101d8400280704050a043c0803106050202e140d00c40703284941c2c0140e0141080c0100440c220170302052281840340c0b90000449075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 928302410 1250 928301160 928301173
    0xa0906110921010f020c070306060f060c060504050a0609110103140c09120708010c051b010501051e030f0303102d180b03030d02031509190c020316030207060f050309 73
    0x409990b0580a002903030100001584002007801c1d84240c1e88801c10450040d8030401013841803010a120f401c00500400e0364121000385000d0014080c0454160041c1a0716580c000240500909001c48030020b54049000c001d00e15481c03601e81210000000d080c0e0000c1c2c6003080e280c2c00b015600010030300030300000b19500d04201b0b48204110212141020b1740035503000320500001e4030724090268052a02c03041d00c1c2d0584070101c0c06480343c0c0c0000203240050140e8181401000503403240c0c904034484600341c0711507068084c07048022a10f4110004d03c001030f1884000100403440c00740c4503400095071a001e40342a413160052028180035a481e01d0402d121101611042082152001e404802032508420201304607610034006400c41e041400c0c507100d5944c0010801c10850007101e034800f650201207420b030115040c014003045a001c80115088002c0350744105102d0720714001c00582c0c0200c21403094031580b11141d490005e40b030300b806100300c07130203c0c402c20758100340700c0d0044040d0f030300c40c41151004084 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 928303660 1250 928302410 928302439
    0x7030c0b1b0d0c0c022e090f1a120703051909080f03060307030b0f04030f08131e06181406041101200d08190606021f020c060a09061109 60
    0x24402e0300008814005825501340040e21a01d84d602090042c000e10700d40c00411548400381001c111521030010841c040d001807000144045036a001eaa0012100c5890218071200348401032083c024405d80d02c0566000304608545d150300924030070300c0c0740c00442d00d8129049584070260b0b095000018003461040c81701c6080000303039001465010304000c01302c03025580e5989480c0c5142c41d0a82e901041500c0080410040c90b4100103a09080c06880ca00100c182ca032681d07a044501200741802081e6032441000c2003003000e1501d82c8120318a40000b801c020080b10303d00c00d980e1102c0c403c0ca003140d5240300e00c1c1c4c000000802c0400c2d05807186820207462159402510011500049040c00c043c200c06202c501a00d4a503004000001514a850300e911581c0d04200400741e190011380300a03503c00310304101c828004c06601240080040b40c00f07024125842d8001d00d4100d02a020746001007500384078000410008044c20741005c2c04480c000c010030803040c0f400328134288480c45145a41504040107040d20700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 928304910 1250 928303660 928303687
    0xb0105040b3a06060905130f0e010606050918061c020a121b080d020304091d0a0c14090c030103080d110406020a02010e030f070b0a0908010207030c0b1b 67
    0x2a41c0407115042128120580c0540080201c10111681034401d00d400c1c2e54110520038070a0030041e003030a080c1140c8040c58100014200d81040e040b200d6440d80724074180c2004c1304103410551052191100038040c0d1911010010440e400100c4420b108440e101405403c07140d148005d98010340c0c010b40201425810072002030302c80c102d04042241c12542d014400640701c00b440d1205070f00248100ea9103003c49000342d5102d0314000f40342e006410b85401604812504a800100b201c0c11211100700c0410401030303400300c000c0510f144902c11034560040340a15810001440404030030340d14840c610350350801460040c4140d18104030342000c6906010801030000c04c1244029040202c00e0701c50100d003e4028000c041145e80140c0c1c066009a03000c4403031841190b1308002c4c1611482d0040c0c000341008403003149000c0e03860680344610b1071813040018400000070300c11054000034100b0500255a56401450700408040095005440c050102000300300c07980c0d0b80c0248805001c018003070550074101c103902d644 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 928306160 1250 928304910 928304917
    0xb09040f0c0e0a02091f0516170f1207030c02030406080c09120601210f0b06011101020301061806021606120204050d0507080f030c060c0307030915091101030b0105040b 74
    0x80d20304041012000920b640b560b00510f1140200507405a21076072900305000c080c280244440f10702c3c0140081c00302000d54403800fa298030a1404496010901c8981002040e0803142d00d08400c844100040200560386406c4c024000c4160407486600d843d40d07444411402c450f904003400c00160030801c41004150710030344089070407855502206207000480000103140c400c518290005541008004200711074859605400350007602001c0310008005684481105190b0b00c00200750a400c00c0105929900c1500a415200300c894021503a9586031a4050301c0c80c01ca4840301c05110300d00d0100451510720100d10f409102000f200c0b5441250300300007060b01c03d6400305a43c05500d5900b80300c0050a40e542d04080707100350b03001e01c0240901c03e082a402e035040ca9059001800c10fa482008401c00b102c800150141d07201031090181030322511010b00c00c07000f400c0042800b1f4a548031ba0f184000060700158840008030b0b1007059400c04c1410031000540695030520070450101d2420310003000004c841c003004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 928307410 1250 928306160 928306163
    0x3020c060d020c100c02160605040b030403170a1b2f011b050d060e0903192105270705060d02160f03030b090f06040e0a0b0115030f0b09040f 62
    0x150500f00d43c007011070325100c010500300c0001038594080e52401134060141500c11208940c0f4440d26604001e0090800d00c260b02c1202541c03080000001e0a0500c03415912301907180c0808001141e0401e0b001000103841808018842e050301d8082c1c410109010340c82d020b002d503c0080f61768106841400c1014415000e01d40c0d1500107540300d2508105c010362100707200f00904069181c0e40d80b02d20500d800702c070460303580750083c0015007810702c00d110700741c2e0001040c0c0351012070318145403000d50b07084603080783d4038128510f441240c501801c0d4011001c104e540c010910586c0c11209c4c04100c4ea015107600d0440420101003c901d6800194081c0107030b0034448010611140c494a0143c0303426100421002c0e441152141554182e1090400c00201a81360292402e45602100e0315001c40c00c140d0703081149807130f016144c3c521583e542e06a00721140c40030700200840c2c90b00465400250f60f55082e082041031824162940043e141000704035500500d4400c0d6040b06001500642165403241d4820054a052560 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 928308660 1250 928307410 928307437
    0xe0601120b0f0a060f0801050f15131d09013e09060c210a210e0106031101020c03010212150d060f061d1311041103090c0f030a03020c06 60
    0x1203220391922240210303c020105641d0b446141025000002c24400c0103030007440c480e032001001c034451030703480501d60b0740d0b04001d10020035980d40d1541000004031a480d03000b01d541c070107141820f00107a5801c61401d8465007001c0024000185002e4021003107003c40581c41110b42d0f815904441d1080700f900280d20540c022503d0709180044003400240c260b041420102800e60240340c442155105107444174009004a00c0300500b800c001c000e01820070a0a480107810310110400000889050381d001451200c1b42a030003002155281c0c10102c07607501a08136854054803905481f22540c0c2814400c880c01062000c0c5886540e40700c1c82e01d241d282e091126296075000c20003848540106e60709100301d407a41c00101c50001812498100c541d501c4030800302d4004807010f88401000303030000400082c20042540181c01105d420000e0300001d005050384e030a800002800803003041200540050709030311000d03040324401c3d44c640384841010341d14440d0440090060304100b040d00c1070303414508003600011201c0074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 928309910 1250 928308660 928308679
    0x32a0207030b09030304060c021f0b0406120c1401050702060301090f0902090f0f01050d0305090d0804080a1b08010e070b071a070f030c030204050d080d06080d12060e0601120b 77
    0x2207038a40c072400b0076211100700d80c10010078030040200a10680d10b40d01c090b0300141c04241035009007150001c01074040340c40320f2900d42a54240303554880c1e0000000c1c1c6101d200c3c0b40c008103118101018440c500380900041c1140c441e0b003d03d850b60065081c0e940440d402450035166070f08050118001e40b9110b02040c0d4071a444001034001a0386040082c0d20501110030320000c14600f09401c0b05604006a10481c02288005855000700c1e51090071103040d4142690a0710b00704041e07241501c980d10a982c0306000c14012903008400b0080e482e80071102100c850495a4400c039202c8100c03508a07107600c01e000a040d4403900341003000b41144070152042c00c0c054500d04091003060b4148043c1d001084518400198054640301c1720303150140310321481e0107110718085081500f0500481d03020b2009140141000c40007241c90483c2d89010703003000000c0d04105080c1c2c6c0740d03112500d0003c0e080c003c0740c9010204244c2410804540c030018050214841e010581d50304a4000701101e555004021031011560415001c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 928311160 1250 928309910 928309913
    0xe01090606120302060601170406150b0427060b04030b04030c051504060c0c0b01120c08070b0a11010b0a26121801030b03060a021315020309040c032a020703 69
    0x10321808000b4006030b684461082141e00d00241401c000070103803414001e103490040e841e01000c81680303a0090340040e0000711049201807443c5081c40980c0300300e520441c00500455070140301d940000707045003080f84107100d00d1403002042007514954018041c020805120070404103411840103501b0034000d05004142040070b803201070034a0043c40c0c11000000791401844101b200a1140c00d492a08502d8051480d00c1196601d596098040c499146107141d0030151b402400003040c203a02c001c1c000070049403641c07a40c0d20381d20246a0000c42c500300c049805d00020840004060080000032103009280d44640d5044c41c1d084d04803104090a019011016503030103402440c070400101c0c500d48292058541c0f6140382d080803840f0900584503440c109414080c010741c440d14000342c0a83c111101d0000941c0f200e11220100301521a154007509000106003456581960040b0013080d17012410784003031080c0744541c581a41901c1000b226400104031052401400300c0012449c1d407174002c010b1041d181119520f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 928312410 1250 928311160 928311173
    0x4080306271e09100b010e0402040e010314060412120b030d020c0405090d0e1507050604030c17030f1302151315230702011e030f0c02120702040e0109 66
    0x18054046401024882440122651400300040c2c40005409651040c60110302a540750311000c00c035115001d4850040380026030103060701c90701d4100068411500c1e555100c0560f41c503d1002e1106441107000480134081c114400f0540b644900c3d0818030f0700f15074055402d401c980c090b0075042c0c16105c4a0382c1e03110181941d50f00703015524110319a507004002e0300c0101010001168800350240344140e1248201c90103c03900a01c2003501848111440e081e141d071103c42a49246c8903598000b4040c0c01900100f00030135030080c0c40034407043d000c3c00059080f2000c10b06440b64601c0103452612603041030900094010303540130300000c2c1483c40609034400c0c40318000700d091555044540242b030722003414041030110004031070400c50507220501c0c25040400c03110941003e0851010625401490001340400559010310b010900620312074542e15002d00310031400030014200d010f91a070101c0d09000640c090300703100181c146030006e0055511407601f01c1030f03400c201c020201401050419500c803034003040480e01 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 928313660 1250 928312410 928312459
    0x20105071d010e0a08060a0c05040810020d0e01090f060b0d031d030a05072612040b0c0109230c09070e0409031202130303090b070b3409091a0904080306 67
    0x2102c001b45032505041e480441076800d000d6034102003000511081000d00b80005940100c020102c10040c0e0b100704600a140241c101e140c000ca41a41c01c205000041006409155003010301440003002240f015104014601d081c0141c060300080e80c8074828504441c8119075995080c00c014210381503110240c3d20305c0d09101140e48000c01e070204600820490040780c41c40f007902d800d4100090452481180b4000b4002e00072405452003071500030550142c600f609500014220340c01040316860110400c50b1450384480d1500d00c803106024022514180c3d041c041c98440c020581500d500d0a1105000c0034000200041c03031040e000c00440301c0042c1d4140e14248001c02d88640600201c1040c00d09504028002c0441c5500040e12460f00b04404808903000351551a045540920b00002c09a844100400051400040410380e081104e181b10340301600304002c03400300d4030b000c5410b00807250400342c405541600100550b070400e100c480001c001629030401542d1140d00141110000c1e190071a020ba940365 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 928314910 1250 928313660 928313669
    0x5060c0c1e0d12050103050d111005190b03030901020a080c070e01140307080f060a0f020d02030a05040b1509150a1701061e060c0f1104020d021306020105071d010e0a 73
    0x100b101c9101607100750b100c201901c200a0603e0140025403556594594601240c040b81040201c4440b40342d42001050120131840500040d0501c100d040c28581c0f1603d0000d000b0407041d0b518980610507120b0300300402642e120320700c16000780103404101d0700c40a00640c0081c00700140c9001c1c0d05008280c004100a07160b000c3c1030780300c119003e1288101e09143c500405078000a04a40c44025010075280c170020349550701110103413010a044600d1781201d03011780581011442c6e414008410010302c0006940554881c0340207030404025621170340d80e8900010307054804503822a58000001d0300f0510800c442100050300603200185c000c0d42c841c2c8494420b07903640780400050f5165501008001032649800158000341202040f10711705c1d0081c041e02d02d172000c10005011203800c4006505000e043c40c41c0e41c0007508090320a5665218449524000b5802000c00075800326041e000810f0207841440740d1031041002d902e440751a005501001c015018110030400c2c100700c0341b90098821604d0780a1042d0091 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 928316160 1250 928314910 928314913
    0x90604030609060b030601080715090e19241e03020a0b07060509190201120605130608060c0a08010e1504090b07020615010915021c050301030506010608010305060c0c1e 74
    0x20701c480c503001050310311010304e85109034458001406152030210321041181c90059050108807101081035580d4500741d44800c001100710703001c005070418044418514501c0d60f0f1020080440401c1900030591a035151119142005030340030b21044003512101d80c4110801c0000c0b010040d5a036000900315081034100f05c0001c2408101c0504002041c003445070410703800801340036014280d103d60b00e84503685440180c10400c030241500b40f02a05a840200030740070103030004101444020b0083c001e4201c41c454441030344a0140002c640d45800400d951071201161b4980030f0f5a441e20a070205d03036040c080d001d02c4100c880b1004d0914541c1e240c0c0300e007154081c4543c90000d10f81c0703000d0b68040e0401c0001841000c0c100909840840140c2e403001101082d98000000c60b85e86c5844a071049292030030112030b82c5114104500c422401a41120140d4100c2c1e100340100c3c0c90680e03c038842251403213400c0c4402400d030380c02040800e1100815001905c07040040c40300300c40e01c83c9100c80c0d91030b1006c940007040303110300d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 928317410 1250 928316160 928316171
    0xc0705040f1d0c0d02060f0d1409070b0c1e070b07032a21030e0708100b01092102012607020c010c02091303050f030a0e06060103061d0c0906040306 65
    0x4401c021040e541e0b1095000054a911060200850baa501c10a24001c2c0b14400000f000740a642405050303864042c149281044404000e02003061810b80668010245114502e8001800b101c1c000441d01103030183c1000d002a1141c4000e407030800000c551002e50640501e91000c540d81e1300000291000300c3c042d40e565085420901c0b001180101c40754078400e00811024003240124007682040f50f5421f242d621034040c80890301608600408075054000b03042d01400384000748010f03000070120400070392603408102000d403030380043d5000740c50741c8100c1d50b0034500300c1915000310402c6514403400d24018144505160300b0b4941c40906412401180d00a420004050080b825810011810148000c6c01e0025810003250002103883c2d0006001e108442c030900341ca88101845001a40c0300080d1920400d500c23810150301410180c82402c9403456644100701c00142190710038018032007246c2c4010042c2d04821700420704403128100040403942d030f143e41004030702030603103490006000031401034000103070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 928318660 1250 928317410 928317431
    0x1701020f1615020307021504081c02030411010c0b0a150906080d2a1b121217010e0408030601030b03030a020109150204030804050907120903030b10080108030f0c0705040f 75
    0x200d80c66100c0b412242daa1050042020386a000516241c10740c0300000c10840301d654070318000c10356100e00d082c00358035070007814480c0c0801c0300c01e40c0186006071303c148000300140c0e00107001102e070352002c000301400809514003ca4000501903026104256040c0c02190f0002d0f03c4490030001e80d0f660750b00030035003a40400300c5410340c55488043c00b15003030030440038544821048103040a040640d008050300184a1f000e8400040d4842d00481c030052002d00c408030340754000e5003030211001c0b14007103243d00403c08115500e49141403041c12035050315215003002d030882e111030700c0d0300d1120f400061546050543d541c00d030f45d8469074100003501024112350300100d01c4001c68036060b00e01d000082020004580103100c107200080c1d0f00c109480a58100b5151a1459500c428003241c0f160004895400c3c0340c0e00c4c00c5012000e06500d0303004800c1c0c40d0011780300382d84415007940c402c5612004c00d00c12080c82d0f0300280401a038560220b0001c2180c0346005044074060380d03c0303100140c01c03600145035001c006540c1e200b1482 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 928319910 1250 928318660 928318673
    0xe181801020904140106031406030606280f080d020105010501020607120b0a030606080d0309080f0a021603060c03050f100603051f241119060f151406040f1701020f16 73
    0x700c1010308c0720031100850801001003a610ba4000d01500d10441950b24200c41d81031001d5481803511010151119030541e80d024610720003a4a4040d01e07a05029000c0c45240f52401405617904940c4103900411079992500c0c401c8030103400506029400302d03255941083c00d46d1300e8a000d01e014501480d40051010315090043c0e142003a89484101490f00700340c0d48401051106046d143d002c1d0913511066034400c03030701a08a0411440c0d00d8103419220001c440401071103e198001c0c1d0310b0403c0d5403010016610340b05121441081c0803a0008440000083c051040c1032194111171b4110074002100d4081240821104a000d542d50300541c0d01000c02d8105614a0300704907070704100c0381c11141081111360058038080e03a15051000002c80c640d0244410140401280364000c2d4401c251b038003010010400c2c0c00c0b441742c8008501d445203800441d5841d403054558a0040304442c1150300c0d807869402d0041c9044c18480d43d0710199000e80109540c02e0003090805400c000003000c07042102d00400721a07903554500030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 928321160 1250 928319910 928319921
    0x9020f120f0715021504030905060a0f17061e01052a0d05040602070b181008151e040f091e0b01060807080a0b120304090c0e18180102090414010603 65
    0xca01040d0345504048180c0c4c2c012070444110081010182c89a55640c207041d940785889600054004400003612100158040d0002c1c0388499180c1e102c2803e041e01068110450300140c403129403203018101044884464584d0300b41c2e0128043c10300030308289a8000e606050005c101c4a4404042170070b15400c0398580620600400c02c2c00b50a0440c1010304000c0000d42e075100b140140d412450001850455130007400d0b1400742d811000514a0030340c0016a2401401601c0c16545040980d6000305020018039061160340c00b1140070b450300d110100d50305e40801c4003902744041603405407a07858612501050321300312542e000114090449419400e03c1c601641a40380c141d10500400044900b401900c80e030044030140c10403140340c4007144d01d240036000101980715403950103145101c00103000524881035003046014404a8485070403000c49101441011900003109070629845d40c0e00040c11043c00c001d080443e1407070400018140007066010400700c80408031400c902a1a042c0108000b69240c0240d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 928322410 1250 928321160 928321169
    0x130f05060a02090f1c020112063308040302030a0f091707080f06090a0b0603150103052a0a0317070803150907020d0e0906060d14010923040609020f120f07 68
    0xa4420603000220380c2c405c4003030f80d002410408070b010785248121158003e070025110461000d66038181011001e14075900603c41070002c0c007080380c0d44900203801980428407903505a00a18507100404100b214100e5500a020040c0001d40c2d4010507018451840c100ca0340c24200d00070004c80b030030816940d00e0003041840d030305081d034001c00800284120109696600c03070380c8000c2c41341450701c940c07000034105080325451400c4ca4054000000610100040b100042843e40030843c1c000070025504079008000310606d15008440c4032030070400034450948110742c0c841d400000341d00300280f666807250a50b00550b0300c1715400c0d582c0042482d452509655142e0801a20300040039048010300c8042d051603120130546201d038030008001a0f03543c5404003152641681c80404100001115903c0710301c400007130240d5000145407084d8031071140a016009070050182291b0b030030f0030b9680c40c1d4521010b00b4100f842240c01c00356031500040d035500c0e012800d610f80c5402401800400d45112003061605820b94030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 928323660 1250 928322410 928322419
    0xb0d021c06030501291302070f060b01080702210c160303020a02191217090d060509060601030905100203040203070911070317100e0408161a010b03010e130f05060a02090f 75
    0x11810220140c1241c2c0b172031a1001d41e8194102c0c01034411400c028083e82001a00000300c14000c80e0412281d6849210120300980744c141c11034468001c2241c0e41c1d40c41c5041c0c10319105104210540c640d04010142000031100d10480e5800740020300403012000c0300e030380b003100544c2c0400c0446045107031903401e24150081d90303603030380000c280b8144600301500941e40001d440da5100501120303042400e00210360880310058944c2803820b02903e00b01c0d0040c6002c5603d46458056980410345540c464000c240095400000800c0d0400c070342c07809000258000f82040745d0500c030340e1800166620140c00380540481800d200c594403054681000392400083c146000c41c1390089000f0480110305141600c0149c03800e10150420703c0c1e44030310300000240f16408408101d0b0b41c4403181e000403c002100300740c0c4214004040d0309582e90741c41000f060306000078018000003038240c10000d12802103000305842014029040e800004505407030b50b40c100503050310b80071007540c1c00003108176035402c09100c0c0b022406020345 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 928324910 1250 928323660 928323701
    0x309120c1c05010501150e10030f2f0f2208010c030227090a020f040e0f24011e2606031603080a030905030f0d020a030f0c090b0d021c06030501 63
    0x1032140320f103e8240c7d4401c0c0040c20844045610035844440030000d5110104441c21000b44164100f000014810302c4d00100420340342e50004c0305034252003d240c841c090b0242421716003c00184500350580342201131107126000003901c01e4007402105d101801c95140180c2d16000140c038461901521444c00d2000007444c1c201c2c008030340341c03010021b5200b00c1e140300058403040041080e12061240d40e10020691441405210000e110518214001c0c1d819001d02d1450310885003000807444820070600780840c080c8605210041c42e450660f4503880887e240013005034030007005280340104c0410418118070664020081d075400c08002e040b00030307141c88000340d0100c2e03e56a079034a91441012031540c10542c56080ca1000c000d010001e9549001c4c0d050039044d02d814020590030f0094003c0c0d51440c000070300300461500c92194a1007000c0e5002e40d540d03101044070342080c07000301c07141d4070007a80862002d40c2002205d00c1d500800124030f0121703007001000301d00305166041c5107007954101100402c51003900c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 928326160 1250 928324910 928324949
    0x60a0920010c11030a0206070c05011713030507110301020705061602121812100f0b09040305090f0a0f0b07051b06070623010b0306030d030e0309120c1c05010501 71
    0x10a00440c2d040c0d00c0102d00190041d04400300341001e82c003580c020740200c00856504100701040c044441a180c0c00c0e641d0458001a05140781c07080d40080d181c0d101d688a5540014010a102c2c034018070082d03000300d00c021038103003070407020234220ba12022054449812010901201c80200300c0188405a0548010903018231980c80c0502d0794400c042200d01c0d09590780b21582d070143c85d0100c01d071110a41403815034017251509065003028240010081c03050a140500d40d850728501080d000f409a6019a01c10b400d00c3c41c80310520410041c00c04001e50701c411f030410300040d04481560f10340b0140c1450300e00d0940b03840361451703e280b07132107841040d41d041c0c50b01200084566454680c103a40903990403c03000700b45450798229110a51014103030030306080c3c803168004105c03c41102c0c0254040c03036060341210207c18a10360120f080b40d940c803803902d100c1d1700108000c400ca803824928420380148050159882d40304210002641080180c0501401d01a41e20a41c0c0521030b0030301c90366004200d001014080301841 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 928327410 1250 928326160 928326167
    0x10212061f030e100e061603061202010c0201090801020c07030209100e07050f0c060709180608030a030b060c0d020c0112090503030c0304081207030e0c041104031202030c060a092001 80
    0x8401d94142015680e41d8020a40403003001645903110403c1010055103180892580c0c45070b0f802c03102180c020400550b03031244c01e0320a1142000311031a28140742c0907102203600440c0d8540c4074071000ea0400955201c0890b28000a200030401c8284180c01080c0a514510500000900003407501d5840c0354010070411a000203116103503440031036450b000d5a82c0b00e000c1441100c1d806902855071a92148804111540e0b800c0015402500c00507031001d0240410302c07240c00140e035010b025201880d0028400c40881a001c0c0c0c100300030781c50b0018805418240c01003282450140c554040c140180c0c41202100c440d56001601d903109190f0309a001d026424054503030581c0e0344005000f0f21202c580001c0018140442541034600041c0c4076140803d590900b100010041c01c00a2034006250107603198002c0385140502c900900f41c1280f04686040c240b46407251143c1e1a001d00741d00d019400100320b205440c45050040c64400c5040c0980000c04800c5801c01402030b215619031201103002041140702c16a80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 928328660 1250 928327410 928327459
    0xd08010e0117120a080613150e070201060503030d02040501080c0301302004060f060c080702011e0819090809040504140304060512101d06040b06030901021206 70
    0x310040b42c0324010603200e0042c90300401035640c80e410702010910f0300409900400e000e002e401c0c100c0f00b24650703002089161040741d600c03084142c45881040410031001b11f09103021503010a444c000010590303510350101e421540480324058103280d0001d030a000030340e0031508c0141c2100100028030705640c14080c4001313141d200412038401c1c660b05001c0034802d4010342805000020750040040c008801c2a0306803980c000001400c5502c550700f401c0e804207140b00e60320341020482d2500c3d034408101c0d0169890386a41139010040507810440d81d4200000e00440115140c1850303003d550301c002d03403403500c07001c0000240d0841031440c0d6040d092101400c0410082d00c15142050f000300c0e07002845480c2da01d0982001389408034224043d0001241c002040ca4101c0060203c15502c042d24180d6030f41c030001c11440441c0e403802038000b101548080c1c100300c6010841d4140e8840409400040d103840b2010005100c0d0b04101c403986213aa4001424880d500c00402c2059080354090316100e80082c08100d00d0410340b42c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 928329910 1250 928328660 928328669
    0x70f0308031b0a08062112090415060210180c06110703050706031401080f0601171504230c0604090f090f0302060103031b0803040602091915020d08010e01 68
    0x2034000c00440c034401401010103810103209100e1a5503400c00d00005440280100c880b28840c0043d8140303102190b0b00000f0003510044a10301500c2040310044141072281c002c1c121054100340da4001c40003e5400360402c0c1e02c06003820390010202406c2c4900b21906030313407019540e40d6141200c0300000e800240b20790150b0042c2c642c642400884461500f0841d858160305030300103046c51142041c0040d60036010340c012240c05151005110050f038842103200c0c2d8038110204d04402c290f0058004110003d00150b07000914080c0c0026110200c595190740081180252400e4407100040500e420076841d0321900b4079548170044000c1c00b074594952001a4080c011032140340030302911403801c01c5c44054190310044020f603028541c0317541d141d0b80c0c2c10001d668480901040b0041481c03100034000e0794902042019181d580704074418615500e65491101942000e21029001041584c00140b51f08c2a426640c000d4141d4140b143c001401407540280350030315450b070010600c900f0f4001482441d1b500e02c51103040d41c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 928331160 1250 928329910 928329923
    0x102070305120612060c03060112180201030b03030c0105071205010914150102100f0609050f01150c0c050d260c100c021e06100e130201180506070b010f08070f03 71
    0x65603030f2404103400d22420405044903001714010840e40703c04c0d06010350f001d140c0a030703101c41c00002280340400031a60035000018820100c1e400307480040d0300c40e0300a05960301014003920b05021510030710509644040e00d60304082602c2419945041c0502e10a0500504a00341c09000b0019034005070000d143c4080c06000141e05100c0c0b84a9850b40200240c000d0546019000c01500007040c0b882c0f0f008203201c1c0900103071541010085060300c141b1308241d0f41a40d80c0d043c2c41d1069448854020b5515108118040303480d00000e44000500d070ba100c0340202102c6020301ca200300228140140711943cbc1920760360340114268103100c015115040001d03088081e0a40520002c0c1540f2143c00a900c0c0ca901c0d400e03441c201c5002005801e0080001152940c0614108040c01002c1c17610b401e90420500001c95151b1040003414111402540c400e114040e06407000300c4040701c1c040d49800105059a00055080d00c40324180030041080004110a0200808414011b0711311281400c0010710702405038800076041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 928332410 1250 928331160 928331197
    0xf020d05090d151113030c0602060417160606030b0f0f090a06090c080706050d0e06071e0c02031009050615150307110a1101020d140406111e0c10020102070305 70
    0x800910782e02401c0d4803100c84d0441074071054140e000741007265880c042140d802224100000fa500d00000708113008650046044c9001c2400d100e00802a4014150601c1d110a00d007040c00c01103911441502d000c1d42c05201c040c010740c9005003c2e07004464014007c40d94545c00c680406c42203d90110715400d000d1b9118002180074101402d1a000341e20164000d680c0030f026020000681c9274002c4010074150600103410301440516418064850303804581c0907000c20090030104c10300415132500a20040c042d4207060124a48507008a4074101c0e5a031004080540c1d128111340a104081000c2c2d5801240008012213800d19140441c200c1040c00100310480300000c07000c1428217005285c14582005554101c6030a2021406c03c4007001b5403819146002d4001c413180c04900324030403007016550b1310b0581c0711035181c03a1520204075061407400450b1003584c054040004842c030407419a441941400754010404070810740100440c5280d03440c2100e003907a104020590000c0d4010701075968030604d880b03c00c0346 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 928333660 1250 928332410 928332443
    0x40f1a1501031d1e060c0a091202240408011d0d080601021e070906152a020d05030c060f07020c090c04270c09060c020d0602090a03030f020d05090d 65
    0x3d0b6030354042d02c2d440e180100d03407007584000c012428510a00300030b00e0840e44103485080d154101c901c9801c0404c0005010b40b0010302050544548200c203880c070152240d0450481d04401040041601c19030700340e100000201006460070034014a00300c6d40800d10351414460075240016640c0194108240600c138460001130075a80c02808100144068010400c01680c1400f01a980b00c1001d4040d0402152034045c01180601c984804400c2c600c410340c8840ca00003a941036204004d42d000001c403095034220041c404010f13243d480c0f2200b00c1c2c81c451001151200c42034113225040038401442100f9440110f02001103895000690010715807080c1c030404840d0303d451146070a181b0441e042400b0250700e40104481c00c841e035400c540c514030707050b078000c01116031501800c44600800f881810700207078a403050745015113880000700311050304c9950300528040184010944002c440c0e0b0055003c20070740110048500d40500100175580a0361a002d403411030036000250b01000e2280300901135072120000900b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 928334910 1250 928333660 928333691
    0x2030901230c1b1914090c0c16090b0306060d150b061209010e030316120e150a14061f1709010902010e0a061b08040e040f1a150103 58
    0x8980c0c094510903150b4907010759020310706204440b2403d5000c3d90b00741401030910310050300c0450654810040205032030f43c09500304480c079180545503481030b10741045602022007003000300d2514010001c4082c2c45040c54000d40a0445480f82010340c001e4202c0c108000b4150f80b06424040540d5012200c0c90100302d5040c4814001c0110598658200800080442269812817489842a8134100c000e002c40803040711001d807240020349004080c00003030180c802486000b240078800c2450000d8000440809941401703207410030f8048841d00c820341e2407043c00394822030360141ca0b08a01e074155042015050a0002c90015004064141c4950000c0d09450b8841c6110340d4001030300c4904000803440908000555a008041c0700004a012880070030041d40d003420400082000c0301c0340707601c0c1c0c441522004074030315060a901c040200c96100040002091491061800c2c6004a00403c906547e81029103807544850414110201c14090b403503041288541000012042e0401c1c01e1a011400c60380c04030519 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 928336160 1250 928334910 928334917
    0x303050708040e0f060f040603020303030c0c0f10090b0703091a0a0b0414010819020609040905190c05040e0a0b01150e030f0109020f0d0b40050c010203090123 70
    0x106983c100305410311501c42000121240940801c80d0100700041c0540e003004111035251100a40541042c000030f44d28900c1400074042c5014a2019101041e58540c1914144501840f410740100d545080110601a0041d2003039480141070a01700301d03080441d107410404140660303803100050280c20005074800999005000c0b102c0c0c010f0b0051266504811480000c024240a22784546c4103203004500140481810b00d482c4603000340c1040e20381081d00b0244406800016016945c1e48030b481c6200d10001d003180c0e40c1603071050103680386904e00c40c2401d00b00000d03075030110040a000e900203e82d11000c00c941030171803411510110341300c0c0c03020100030350f054500c0c100865003168903004403c0400704440c410741000c680d503482126512003810b585800c01542c0040400050201002500099100c00d101c00c0c010b10a203008110001f1420aa2010713185080c0300c28603c0c0d20803940b84d810040800504121011840d8001d0014600701540980001d00400c660f2813213881400b1050340c141c8032405094100c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 928337410 1250 928336160 928336169
    0x807031b0e090709050c0f03040b0702031e040311010e1807030f110d0528050901021612020c060406141e0712080a06060f0f11010527120301030305070804 68
    0x120304070345042000d1648030240c130301c201c1098a0030030002a040f80c2510007142c00d00c10040801c0e0f429500c40da141d40c02010b100800c05030942c0310800c030322140e041481c0641810030035408880d80d542c6045180c05081a01518001c0707043c890100d0030080d0319500c21907079980103890800c0c080120707950b40c078049001c1c00350300e80e032046041c3c6070905902e482c01c01480100b40610a0306000e000d152258030800c240090300503441e4142c40c00016202011215903000107402071700c0c1c20009070900041000041c00c64004500844846a0365114000003a03010700c034280c0b0b414012501c40c0d040a02c1c009021300040c100003040c80350200d0000d00f000d00206120401c500da41c11a10002c0d4032204c140c03800041c14880501590049440c0c6000552540c451b805058140e849031b64621901c13507003510042d0b610041d50540340b410300c40001c0000c0c0ea909403d206162142050b500603809010911608204241e0110020ba225801c02c4548440c51507803a022641181c0d418503045544440d0b5040080c1140900e800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 928338660 1250 928337410 928337429
    0x40e041101031d0106140307060905090a0623130915090311030f0307200d0309061e06090f023a1103040c060206060a0504020d090c080a1406010807031b 67
    0x8410703941d1078055001000382c601d140003841c1d045410001f01540c0d2181c0348901c0b4000303980c081c024030450174010b62035500301600340b1010a405d600c035000d900c8106411489007498031207651500c11310345840c400d03035600014105420060507030281c85100d004100940c4d11189592030300c030f14504040c419492480500c0300802a030340c542d800d440d4110320681c0191500000500c400c0511080c4440c5142e42c804e400030b845005044003004010150003030040c140d4196101030340c2d82c4030400400b2202e41c0c003d00365001c800c0c001417001e0600d06800210307030464100490542c414407146103929100580800d2010301a00e006200c501c18160180300049100020986603046c40c601d03da03120020700c0a540110f21171106c8448564a0301012656880301b110780e55400f058980040215040c51390003009a03040e42180440c0070400d07900c0704802e901e6030782e205245c4c1d035000400301ca0901208844201c0c2d402030b41c9004d41200e515281e0703c69960150b9000141c440034038070321400760140c0318160a0004251170701 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 928339910 1250 928338660 928338701
    0x10b120a0b060c1903030b061c2711010f0302270d140703020f10080f0c0412032a0b16050412031808010c1d0a0504061205010b06040e04110103 63
    0x2c00301d900202000713000c8003c01d0419a55035210b142200a40307030300b8494500c0d00401800803043c0300b40606640414050381ca071080b400c21401d850381e99000320688ac06400b4140041241c0d50004182406607640d0004041c03041c40450040c000e000303240105403103c160301d940c0503204000025402940701200811171303003400c002444664004190713402100d008072a03141220ae04d02c0d0511421911944401d40016400c40010714086007617501e45401c80fa00803038146c01c2c6501c625842114500c02c010940204205450400060408a803100004c01242d04441c103419059a01c3c0c011100300540001f2405482840d05e0240c144518180e600800301c0c4000c41d0104400390a0140c410000c020421f0426003001902060b409130500038503505005035030303800c40c2440109001000c082540800294062030f05800081c1d190340354001d000150845042c80e0b03480304610701e811401c4072505c440d07040c00342d901440b04020220744017001552003604070314071050004c48880100c000f403c1c11100001e43c40c2c04c08 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 928341160 1250 928339910 928339933
    0x8100504090c171f090507030b100801110c030906031f060c05010b01090501140901020f01020c0105061206070c0b13331503032d03090209010b120a0b060c 68
    0x1103007041c201c44004440744003100d110854180c40744c82c00503c454020440500751500c0742540d81c40b4005590141c03050b98000e82c0c0700e546a800311601600c010103004140c030b005101e603c0c130a104031550300c1c420350754051400100042240d140e00840f04540c3c461503022000402030350801d01c2c1d40e03201e00d031035446007804203441d584044d007420050f083c03e031441d42c0b0b403030410003072940a80b510800b580c2058641000ca503520f0103507040310350310404510b4110300408840c0140200b003400502400c500410001c0b41c145080c0c0180b02d890441d08042d080940d005805100c40c4681040c204040c1a410001c0d04486564440010203502505c540c01403803083d14020b00e110300d60407006213910210092a100d5241d5503004203030350580e90285040d42c280703404098100f0029024003000e00100c0fa441e034480c219803441000806141d84500400c0d0042610707151818114170b030026615000d42100443c403400d1031701c41001e080400c8801404502510341d98169401c03190b80c1c0005a4160401c02e008644990292 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 928342410 1250 928341160 928341173
    0x51b070801020d0506011b02090a020c030315181603050c090d0c09060b0a081929040f2c07090204120b06010302070f12030603120c050721030810050409 67
    0x240f4044801d0910340030129815600c45c6000d035074480c50352854841d8150340340d0200460300e08080e1040c48040d80c04c1216010f03010b400e10107148103001c21380300d071131140401809012010780b4541c00c085000000c9020000d00300016075110f0400039141c0340000344c59455103200c806070310644540950000e00a04d00c41e040061092450050f10803500d820300c40c069581500b000a401840b1118001c071f4040c0700060407408080440302c11000f01c48a001c079131072540064485000008200b0101360500b10320036422141458019180b025005907020001104540c2e141e5013001112201441615202000180c1c0c80100300191000303801c0b403a44c1150759030b03914940c80f910071315000301c11220006400300180082d80a482942d0030240c210121940180c40f5948808010801058003824180c0d07615012010543c04222030603902c000b625140c040c0713111420050b240000d40d40c094495030303d15540d054214141205030f4807909905080001d110303111400d1580703080b59103410054000e440c150f05039090003032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 928343660 1250 928342410 928342417
    0x2703020a090209011e020307020906060d060e0a0c0f08010e040c030b0a0209010201200306061b120c060a0b010e12010b030d03200906030f060d060f0609060e0f0106051b07080102 78
    0x50988450103d88900410f01c0070302c0001401750700143c1c10031300040015050400d10b2aa20035002408a4503040f00401281c0480d0025048801070341c5018041240722032880c85164030300d0b070060400f0114408952001001501e05016810800041b04040340030050a2001c1502440c0c0c0102d1981e441e281a5260314025040340b22560300660a20f101005a40244149a03040a00c0c40b00361525542d186800d2083c19030241c2104161882d0300321043e064401d0601c12510014120074000c4d07030f1503903090540c0e0300d04080680f421001500c0c1614054003a0380002c0308008150302680e644075800b040c02d2003603004091440c0c02c603030180903a0b2403a4050720344c0365000f245030b0f0003030100e801055401c40b00030b280e060081440340740c0c1012041020a0400301c5511b005071748008014400545818a0795840c2c0a07034820260340c455444c0c07288000d1105d94203070300400002d05414001e11500740390181e00f0814a540611035002401400556809626000004907200b5150002103425140c4e90b1301c03880303000f50b1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 928344910 1250 928343660 928343677
    0x2a010914070611060f070909061404240e150a0806060a1e14060405040f0b040c0c0230060106020a0b0f09101113030609170a2703020a0902 61
    0x50700001040d030501441d54070310006050002448507070740b00c0421102d001409081c84091080d25580001c16441c81d026583c00340190140241914290205010175110f100b60300b190030940390605490843c85071007030041210ba0041007101f8580740c50640701045050f0298a507003120300d406c0042902c2c10001020344c00340c101941d4078076a00741d64425201480341d00c45411101000000d10800400246044007865980010081032070030b59610006400c031440c001c003032461642c0760081c000b29803500d88980c0b035580d4203604069040401c41c0d8000346414034550941c20056903541880d00740788400080c440700c098810000c0700d44658540f400a5652103040000311a01014000040c00c0c00d00840c64042c090213180b40184148050136186101401000342c00d80400c82050203107414224568a1180c01580144000590038409090007020f0b26412030240950715000c2102d460540d61020038006110b424680c50602d00051080c4010362000590001c1d44c070075010100410f0100170f681c024113203075 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 928346160 1250 928344910 928344913
    0x40b120312160f0c0b0405150f19050c220306050f0a0b010c020a2c190509240a020c1204090b12101d01020a0819020f2a010914 56
    0xc9a0a104481c40e031864010f481c00030300c1300c0d0394040011303100f0701c151504248540150b640340784c05031006503030b42c080c1154240790032040b02043c0022031803a5081d00780c00341c010044c00e00552620001441003440b035039100f0300c0c03d0704014044291148030701c40d40401a550040342402181071803600101c1e403a805844802c0c19501e0a840e4030150760288001f040d46076406400d10510070309c1d00b4548050f0040c00c2c45800b0f8890f90b0300450404001058004038802e000e40c03911004241620901c4008a4400601c4495250b01004100401d0111380c0c110180540942c03030300350002e54490448101a01a0008900b41e910502001c0c943e21582040a8019a04c1e002d500704000b1008404001041081c045940f4042e0040d201a03542c180f11500305c480b01054490690507428442003407a0308aa00440c942e00c005a0b20f00f003072001e20071510070084c1e40150704803002d5041006501e540c040c2c910580c042d001c1a6810307860300300040d00030b040c149800fa1601100801c0750407070b2801d000c500c890800ca410144c6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 928347410 1250 928346160 928346191
    0x2150714010212070c030c02030a081903060e04080714010507050301030b06040b15030603070b0309160510020d030b0d0f050705010f0f0e040905031c0e0c0d050606040b120312 77
    0xa980c81442a00c03c81c1c2400801c01a0548030601c4c00d44a2001c0c0000c260200030500208a000d40c500300301704400360b0320030000719650b104c05402c41e540c400c012819002c101410710f04100900c01e14450303c10f81068100705100d5030754203540361a4114602c400401415075003001d081000b5590068083c504981c0900c032014010f0b51440200402c81c0c181c801340710392080c01c803549410044801d00c091944510f014044034011515445400204e420441c1d041100f07900c03d226940402490310b04ce08001e041c01e17914032030740011030342c0d019440c0c0003000a000c080541d01d00c10303039600e40d0701c6010052180d90090002004c3d80c180303051041d210b220b41c0c0600340c003050100c0402440a403180d01c07000707116070315940d40300d80300d4010b0010031001c5c0160301404e8899200c1444107241d5518001030700c8550a01c1c00500042002c1da02d4007441c02d04500400c59441201c0884080021450115104d0780c4054215000960003000000144030300b000000344440e03c1c8004070707110007450222510103000d520100500d250 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 928348660 1250 928347410 928347443
    0x80904090c150e090105010210050903091e1801120305030a021c0b040c1b0b040c150c060e0d0c3e0301060b03060607030c14010507171f05010e0d021507 67
    0xe44c0020f22510380164026888050355030244e5000300e8100da00c9070160791400701c04100103204002c07100b2103a80351a03002041d007202845d0865109404802960b2860312540c0b40c5002d0500d10441110b01900b41304000002440090051381200d81401414003044540c150200558000348900031140f8081e41c0b038151344100d554018801d2600411045c4400000e100c515501c0f01a808405072007112040129840428451003c070000c6540c600940c1c0d03181c2407a803541c00d052007610a41001040980c201002c2240d40c1540b19414464068100c90b84c4203510409105500000101042445d181030100c42c40e02000c0300341002429400000b100280040303a1a00c81c1103045100039506680d1004080100a0020f401640c0c204c1165009d01403011032400e031111100e094070401c032490f0b00001c080525281c104190261803e410080300c07050520050303040c80c100400032646019140c144040301c1d02e120032a5a8401c4d544480580c080c00c030740000200300c0740c9000182c0213040102c40b8889104803c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 928349910 1250 928348660 928348669
    0x30221010518190f020405041a010605030105030a0308090a1202010e010c0219021c08030f01150e0907200a05030a0906050c06070c0201090e1312030209030a080904090c150e 76
    0x41200210b5015192a10f044691203600805000d400c441c1010011941000350703403a132103900e1140707004400460407404403144070355a003001600458107100c01440140315036100050358401580e85828084059124440158500103030084c000b0540781026161180c040c0c0d041d0440d03035012460000030701c500303907030344400381c0c0c8803140071151034000804200441c000d031070040d41411068000c041c0100710307040240c481c2c0700a5403003102c0d41e8034501801b100410040340c81e0519020b03041d0311460400f07100c005090010f600400081e00c040200f12210109918441c0000c0c3c07071010516003181103c20070045c51400039142d4018211150100d00000400100c42d800380b011105d11160810140c07400e0703910b8103415a40150607100590401503080808140c03580c030114014090038442c0c0d0400d140e880c0307915192042c0d0401c0700001d402c15006001c071292035100051104403035035001032070709d8a48502c0c40200e0000d0400402c040c0407038144850002e5098901c0310351299242e00740d0b4803585049200b40520 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 928351160 1250 928349910 928349941
    0x30e0c0a050d08030a1509021e0703050702040f0f0207030c1406070903201002010b09150609060309240103260301141302040609050f0a060f0c0c0302210105 69
    0x8580103070303480307030000c000400f01001540c2c090741c04880001d2841c5843c01104416859070000724501d9030001b1003070408848041301e941c030105140303911443c00380c3d96a401007140c098500000e000d10b84a04210302003c00d00d07040051b07074600811046454480300c0c10700400a041002090b1008120728004400d5580040380302c500c100c913142c031641d0401e451540c0d5072840b4005c4054405a00f2484120915aa501c070340e4540401140c0e6030000c00c034641039100300b000d600c4014084249002d6401c00f481560b0b142c110684044081c00c9442c207441760b840010050070400e200f00024080c00e465845000692001d5101038184c034001c08885c0c4449108011111900c0018990b0400c5c009040c0300401541d1140340d082c0c00b0081d0b020344a400441995081d4030241d802c07940020000c20b400000900c454280302070a0071f8203d40c201e44140b5040d02d8054081e01c0c054600c40384108100c41589064140200c1c0703029540210340c060520a9066000402501144c4010ac40f5808075400e050101d0204d02c44521035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 928352410 1250 928351160 928351169
    0x2a1c02150d0b0406031101050a090b1303140607020714060706240905061e130504051b15030109021308150109052a0d150e060a052b021f030e0c0a 64
    0xd0380c002e82042c4015199600800b09c034104100207440701040c0494000040d02d0030702c001940005940b420342c5001060000111540c0304264818000c00035915400282d2100310b580785011080701820410100d5803d22540002a0490307003015903034001e141c00041608042c0c0c40c111500c01e042521402c074003080c1e0300300741c0b1100d5004c0344030305100701e854188145960280d1070090503048607028100341c0105403070080b503090381c41c0c0d0040c0e081e0305030b1a03201e11203000f080001183c440780030202c0498004064001030051a0581b03034046410003150002c045954050104202290020314003041c4821010300240180f07803c0a08000200e079081d60320b09051181c450007a885591081340500b2a0310681d00b01e040d1804e2000d885240c40c41c0c001440c02d5085020304680414602e551900500b4003400401b6980424014400019800e240061031010411800b0000c20070681801050000500007501c1d1844100d401e0300d10b101c144c0b41980c040d0301503152407284a0a4803c40d10401003003040c60042c0703209 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 928353660 1250 928352410 928352423
    0xf13051903020f0a030f150b0a060203030c090a0b0c0f15040f0209190609050417040f0b0904140901051b0a0e01050d1401030506092a1c02150d0b040603 67
    0x20501c01803801032407020105001801e0300b0000355070703030711440e608400681060b100c030000a244071608000c01d00170710005490585480e01c40600d0b040d0020346d2440002c0110f026140046505030135651094407003801488082804c98851401541480c2c0307800c018443c03901c43d1321852a4042083d0000340c0c04521403900843c100308003025035003c0c444070001c002c00450400d1800381055420790800d20441025000c4401c0015241c0780ca8540381e0402e840c10062041e0946003800100128014944010107540d030841c02c1d5074a40b010700001ca006000992041441c0c5040ca00c10807281960551150303100b5002660740129840c0c0c0c0c3c8a4810b41d62040010078000143d5420140d41694010320042c0040c9103606000100310b0300c0721a407a0750021080c2c2081310380f600a58103010314000d00b080115051040d1800700c0d6808094580d5505a0041a104d0640103203201800b4a0409046144c1750403401e030041c00180b124099034100207903c1d40030182410035030b4901201031141d42410310500e001c0d03070360080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 928354910 1250 928353660 928353709
    0xf0105040c09120614010b0909010e092808040b0909060d08041a160302061f241e021014010e18031b100f20030703110f1305 55
    0xd2001003451001c100a54011380c945c1105a080f00d4000e5455000f0b060f424447c0351111145800c001c031a1106030300484002c50078071f0a00000c58030102c1c02c0701c04925254047c1c1960740152600108400c010074014040880c04540090301c00030480c010041e03008200c9a40c4400d0381d0311030401c00c08001c05d0030050000e0f40284030a21a84c020414280c42c11398a0466142c2056101e0140c50012444400102c0041e0480741c103025900408004000c0c550420150070700e00b46061142081c201d03680b4000c50004140307014800d00602d8012009403413903220842000302c040d0380c404d80c084e5407103030304070024a0800d103020306060342b1105030194581640c001c11108500c503200d086c0d400c90303001800d246158050001f003100102c26031014110003001c00320318000c0c1a00b07445030400a000c5440f8015018000e500f46110f200f5000d1002549500007a041c03040a0707203e4039045000c40060852002c0c12242a100103404503a1b1140c01000d010411082e13004c00c0900c9e5115030a0185509001c140c002440c1c8582 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 928356160 1250 928354910 928354919
    0x12152c0c130806090d200714010e09090c04020901031407090e090d0e0d020a05030307050c310504051e032703030301090902010e0d0609050c061908040f021005030f0105040c09 77
    0x204034a41401d0305455000b2058503180307044a0400c00b041d40030323901c60200c181c01c0c03000c03d5802880c00100346134200c0d004081841e19948158840504010781841a0750001d02910168002d07440310308c400c984008698504d00d0451406810814140902c40e600c00c020400030b04d0402001900302000c84155a1b111161402c86003400180c0c00412170490340000400710205254500b000680301c403900610043c15215010401c2c0002000d00d0409100c600c0742819245c1c01c4841c440170740e500f044080b207000189581e52414520306101c1050b035150101c1c07485003a8083d03141c9002020b4405462400034000400c1d48030701101c5a140703600c406442d05a0418401000524181e40c400382d062030040c10106002c40007030001643c4041d05400480d0f0695031150180280320f81080b1602e4030310000d8625524041000360721b03040800e44441d48c04108048040000c0820681069001d8403aa01412490f07100951700307800303056900122103241514040e01e000140b246858010181d4000c3d00392105001181030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 928357410 1250 928356160 928356167
    0x901020c0f0a08061015020705010c320307020414011202061c140a150b160c1703070506070f080613021c02090112152c0c130806090d 59
    0x207181210382d11400c1100c0000380b4a50500082d880b8801d9501c4121500f401c1c80b507807480183c1e0006541c011507208031300c180a10398003ca500e2100a0308000c1d18410f080c40d144003c841c00401c143c40030034034400f5500c00c909400c0000080c10ba160701c03c4500744094890000403001804013403050241705002e080c01c41e005410f080b402060312224904054840e41400e0703843d4401c2d684c5c10110f424259400004011800c4031078840e010824a40ca0150071980707241060503000790007a0481494480070f0004420100b141000348030001388030080394082c1550030b0b855543e40301d40202d00d081e0354501886000480c0280301c3d50f00c0108640540e00c400607503450720307014800040e011000a0300700a908000d65180c40300c031320002e07041101e99000007607079542024000400c010281505034403118208100300c2c5908030a45a410140da1400444010300300910710000c105201300080186101043d0782400610307010b10004240742c0080c5e00e5440c202555130f0342d64543d24070003155228420782060505502c01e910 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 928358660 1250 928357410 928357429
    0xb040201110703030f08010602060702070501031113090f14040b07050913140103060f0c0516020f100c020301050132120d0302070501180201141e071a0a020901020c 72
    0x40c9480791600c100c0310225858600c841d08140d01003844c40c003900d280713640e1041c115400342071b89101803c041e08225901a55644681c010a41450385840443c0d41001c40c000550b01801144100c400010390f5030b5a420004010054941c0040d41c10401400e00d54180c04c0c0c54076004581c020840e042550394020104d440b900704990083d4030a2140c0c1c508001e50300c1e54091020f42541078002a8060351551800c00211040340c01031526070741c01d00360400c01030b5401106640c2c140e4440040c2d14020101480021050300b48911115402a00b403545178001c90740c0030110001c0e041c402e40c000c20959072682041d81c8211039404a41c04541c1802105590814108142d4a618040606482d100b440c111380054100041414860300090740404c1c0541030201c01d010b42034502682260f00d1103200d0356500028201c01040481072184200000c041000303503007502960f0b1090100030301c03140e213540452500500e103580441428802c1914940030480d2a24a4800c60750b405030160003d05107008a902440030604 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 928359910 1250 928358660 928358663
    0x6231f0320040311030d030b150d0e030c0d0f02010b101107030b31020306012309070309032316170a0e010207140607080d090507080705150304020604030b04 69
    0x103481d2440e40c1616100d8001d8005144603000c0c19220315090401d062810310b041100c40205030400d13003119180e440c0c41c0800c0d24803076803112819507030308800d42c01e203001383c219101082e80c80d00c80001c1420318401c0100c1c81030a0291700b59a0600040c01d084400ca00380c5000e03548076a8094156080d0724005402160100302080846098071003890b030b642c442010041044401b00d00c0040d207880040c0e140c07805103122944041d404001896941010780110b40e4601050084095102c100c40c0140c07481d0b80d0000c40c9024900000b010703090340d07280101004003d0014204201e005c1010107da90000300001203020905a041d000140d040650060042560f0406280180c480e42405401c414824845100400d4607003110b440e9440110180d500080c03411502c0e45c4040805194600c03007040701d940f451b0403900c11356009007490340c442200d406028004c1c6510b078030080003441a000000340c25180401c00c041100d001700d031540c0030680d2007160143c03076200844000354841d800300004c0c000150034042070381c0c200707 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 928361160 1250 928359910 928359941
    0x4080d0e011d010209040e0f030f031003050f03040608011d07031e05010e101203050910140a0201050907090e0c0603040303140a05060f01050a020a0f020f0406231f03 73
    0xc90b030003900144070608a50640d407aa500011000b4250038103018035003070107400d5801032010b010b103800d80584034050700200b050320800000104020818079010a0b001d560481e095403210070704030402c3d50341d0f035029207d0500418040c0e0000609602c0c008029440c031800b0f010984d0a659506030100c0c010001c032101003120f050100c17901402171142d4854940a02081c4616070302c982031405000b003041070301d540f04e8150700144468890009511606032032841d801a00c10140000841c002510030b0641c40010351510100400d070b52850075030540200b4002c070500c0b4181ea80701c503110714174613090f28040f070321000850780003c40300c1c0f1082c201040119072140c000c0c0342c001450302c241c00c270301a110201a03c14040e0b040d11201440040e107030041c00b21813901c409092940c501500c0c060040d442d0810340c2c001a00d00c03035421400e2025901c404011010f0344a0040003040b52541f58030b40311181d200d80c1c400f0000c0009034154591103509080c0c20320154140c1c40136491140104600044015011780512090700c1c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 928362410 1250 928361160 928361171
    0x405030c030d050a060b0f040b090d15090309080708120c01110318010c1b020603070e060a050c070b0412081303020a0e061008270307231504080d0e01 66
    0x300d1050001e0041d006500c4404911410407440e40c0c000c0d6021600003641e1403100b0004040a11085000c5408442264113002d407600d2102c40050340071384d03114102400d030f0403881d5080800c03105c49070300540301070348a5220445103d40b1003174400e603150701c075020b152400d40c01801b1802d910503541c80640344000c45070002144500000d90300c010030f9001034504515000b2a80b2031816456028041c1c07051040d45803510040c4000100410001d04001c1c2e640607004000c00404591081c1c420020260b100b10701910480da1024210780003403d50740000050381060280900c0070500c00d840030300303da080740c0c003503a41e0b0000b003141510b80c9801a070210401c18181480600000016169840c0031402400c0303410080400b4a402014001000180101f1000300180d0104012840881c02e42342032100c0b55803088124440d50196141d1300c0e600c144403014103480304a1444d246414620440c403081c03d0001c005551604c1603560f2078222528090344c00034a005000d11256140001e07a5100590000d05000040341 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 928363660 1250 928362410 928362427
    0x7140607120507230303070309030c0f1b0b0403080909070c0507080a060c08160f020109020a090204060f08150118050415151b1e020319120305070215040503 69
    0x4040701d01d1072001c011502c04a000c1c014046007410a50092041041ca03c440514008a19890384002000001815918421038090503c01e40c011038100e948a81c501e180c9000609001e810709000d5210608204a960004030301c400e961130030740d4101ca603c65015403c0901803010000c403004010f00d8202001a0a41d410307001c600f003001142c0081401c940507200c1c421a41c1032440c25a0041d807100f800b4400080c00b80241f0320300c84000880b407140f0902d01400911003200c012030140142c2d0201a600074811203001c50319000c1a4010412180d103500c492070181004131302a105240120780c0c2580c0000c1c070601d0b070815075000302c100200313400884031145111900c5500080854003004401c140742040c0000600941e031034690101d1503810b00b42000902c100c000c5c0031000110802040050040f407518a00e41c1007410010801d01e881c682c02003d0f0750144030026468010780f070f042c08003650b0801c2a00340e48040705020740f14207402607485074068000580800c4402061100c003070b1085034948002c116040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 928364910 1250 928363660 928363673
    0x304081b060408190905130f060f030809090a090b1f031712060108060a03030e04091217010911040b0703020f06101811042601020706050a05090c0307140607 69
    0x188102e120b40521904c440036140d0300210a465440700f0014488400401c0c8003d555241885e88100f03450b100100c0d1207103075240c6180207040d5035030041c1d51404017210041304020681e405072801c440240e801580b25038414200b0710540311201d1000d00080100c0300400d110311840241c4046e100305288041100e1035503a0b50384200c01b00e00d0071414a813a9000b00e008082e000a419000d90010780c2413030500f50300e040110000d65601c005c1e20000f81801b20540c000040341d1106e13040344d5400c03900004d500040c400701c1003010300402c1400e1140081052044008906940c0c144500042d10074000b00e82d908060500c4a101d403941c0c40090700303406500c51030814241c4844200701c01031040948200007a000e62805064050f040f01c1b90030000c1a5030706003c40e0b1440e03120400241c030300f1946800400250450759a0480b01218003209080b0303d2135000044140900185802090007080300145c108031507540e04012548600c140b0400c3c81c1c0c990001c0c00304100c80c90043c1c01040d0741c0c0700c000382440c1c50304145d41d580b074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 928366160 1250 928364910 928364923
    0x7050d110d06050f01090b0a05070c1701050f0f040c0b090102150a0209030708010911040b130f052415030601050d09150b06040326040b0a0306030203010f110304081b 73
    0x6880c000e0702c0701c5040c009403c0001c92040031903000c0c2450040702d824a95a0f840e50b0064a0555003000f0000c00c80354240668140d0010090030700810170000c003101ca58245000e88800c0b200030328808540c0000c04c400c50344001c8400d1049400c006e908544030700713050800c0303129844101007034114415035003001c1012141d100498042d100e250f40050366007200c00141824513007a94048222645051050300101d01e000354002c942c520200c0380011220540f03000118480840c56641d11280d1605040d50300c034545c036510440c0100400128080c0804400a2040c55203a03103950142c0c0203060090040032411241001d10f4000005040103030070040d0f014511821546030729400da42511110011011045441c40341d00c030880d81c09d0b9101c91801d400c64645168590f813540c5003540440f041c0d00a00740f0a688101030340c0141641010580da940f145010090180c01d003400140c0c803039441c21440c0200c2d958540b2400c40302038102100396056940f00c0c0c582a001d43c22503401811602082c07080e9805c52007062219 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 928367410 1250 928366160 928366177
    0x40c0c241e090605010f0506090d08070b04080c0705090c0a0f030209060703020a15020c0303040321050103061d0f0705040e100c0c03030f09020109050d11120a0510050f07050d11 78
    0x41d240d80e242803020965070181d100d1b21000c50035220910080c0c41c0d690460b1841c04042c4e44407445030500d41341441d05803040c54030140c4500c00340e0050100b040000c0c0010011078841c50700300c99190b5128010001d1403a002c2e1000c4000d01d0003040070303440641c05034510405490344d40c1001401c012640002ca041544141760031001600850006420400c9108108c00100b054030b40842c200b0180940581da00c2c407014001500f4001c04541391078001b01f0418041d08070305820141030025580d070740340803009841400c00c0600c43c1902d1141a1842c80b800080485024007039900130160180b4150070701005140400c00d89403107000c2d05602ca0203070f40c0c05009460440040d0f03500c2c0ea0480c0020308004080311541008513036030301e00300660710300980c0e8003a003d02c050b0b6400300c86104009c0c65a10700f0040501c40c26011b2341d000ba070000c4c4601182d072400300700c60074054090000d45011114032100c6a00b100c0080b01d0303a10200c00d5190220302070a11803406046400501440080c00a0f481d403c1d0b520250040c585 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 928368660 1250 928367410 928367471
    0x370c08160603140915040c0f0b0a030e0a02030601065004031208061f03022203020901140613081f0903080604150f090b040c0c24 57
    0x20420400c1c1c1c0c1071140040b02c0c083c0141c6042541000c043c040c0c2c4039200c0d8001410090103000c04103087c44420003450b80105a19a40c1c01d03140340d80d91180b542c4641000b000480868504007040c2028a4041201c0b00724640c000d0107403440740e0030170300180e940a03008d40070303d100844441c0120881131049070340c0742c15014005840b4a4070b013010001c0c0d900a40640124442007881c1440304000085a03d101d40360b5006044c1001c4025541e080082034660644c401c03110001280d45109001180d055802080c217084100204034040401321003d1a800c0098800203400900c407900402c12600300d80490504402c00600c07017803500c20741c481495644801034001c441c0b2a04040790024614910440d0018070040b00001405440c074241c03400703000c007040103098078041c90b250a008100556083c201c030001d0094151407801b0281c982c940f590007480201d0903127000c0c0745002c00c02e20031503009211940101d60b011f00c2499170005180030f0f0406140740401014880e5490742203d240f0140c40200d00b8603007911509 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 928369910 1250 928368660 928368703
    0x1a040f050604180f030f0309020402072f1f0215010f0e071d10020102040506040b070b0903030108030d0b0102071703090a060801141c02030109080c370c08 68
    0x2008100e82c103c000c615101102c0714030410004200c90300416413140c16042c00300e0a242c0d240c0c01078000c0d205032600298080d1000a814003003001c010301c030401c4c1c2c80c0483e05020281003034001d01220000054201540840d0303402001c2c181040c12008070b0b00040444c81691410940d18003c8503841c50280c20581d103025111070b060014418041c00c080e4401020300e02200041d90a800031454001e6000e0450301465040312001c070301c40d0007501154018500641001e591381d5546c0b0404165410030541103500c002d150002c5445c540000040c1ca05903045c0401451030700c49140011401081140d16540c15800b804a000580c120315080c148402145040039560720180d40c0e00304100b580207a0003a03810303c2035002c010320401881c425103201a02c0195401e540d900c50000901c003000c3d00d0001c00030342c19804d14402504201d04a00605450b030301280448002c0303004223032088418a8150360681400c000c0624035503441101c00491000365015018015585850352449410314142e1102a00311450a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 928371160 1250 928369910 928369921
    0xd0b010b0c060f0f040f1403030115020f0106050a0e10030804030606060e092a0f04080a030f08070c03080a0e1203100f360f0c0e01030b0d061a040f05 66
    0x20b00c54140c2c8040203c001d0451440c00807460380009001800c0074021010440e0a00d0400c01c60740b882d1a0180f2102007100d482c0d41e5070f0240110140d005910a41c01030041503200c034410070050080301d05880004203600c0c26182016884210140020602040701441c41400404900a20700a0010718041c060100380c01d410004041c0c07180302030180307035030180c030f070200c204103d02100e0112a80b00308581914400064151010904980a04036850040002c00100050340580004004052501c2922186c0407040a00c0c800e64448201f226507801154013100141c000900c1a000310f9400300e1000700000c3c00304958140e0f21b1400143c948110030f629000024001c0590a100b290401005400200116a401c1c00303091094001341c1d41005501030f006111403850036001185440c141c418005042100b241031a80140c046c1c05d40803814004504001d2482e032640d4440d0065486074000601800140d00380c6641d500010072811911004004c500c144c0311040d07558030301407808900040380020802c4e0070907 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 928372410 1250 928371160 928371163
    0xb21060f010b031e0910140f0105011e0810120309031502041208071a040302100f0c0c11040e12070b071b0f030905061210090b0f0603060d0b010b0c 65
    0x42e0003404040c1d2041c02045103120080102c145810b00f0203800700711580b984140c2074680500007506880682c01d00d40703103084850031038484610805442d0b40035a03031640c1c1c50006443d107203c1c480c0c1c1d1031801e0100c003805a00240c01400c2c61500094040e2004103807a960f042400c1c41c94401d500d08500052001208109000880c1d40d03607401c60105c02011443d1900c2d1803110042041d51400003890380340d000c184501802300300c00c1103210f00b643c0d01031030015520300b81c44d0081d1503008a0f070398407120311b00c1d200310200560b01d02d00c1066142c0c4241c0d12621a065001d40307c0d101103212000300b03a82e0040e212000809010028450004003020144074a40c0351005454801c01e0344030010050300c2001746210307900c09500702c004c0510f2030440d00080e80c903021a2550404640d80d100a800c0107401c00d50028400a80d242283c94151048030307660204030a65450f031003280c094804005a050f40400c04d07010100c0300d454084000c5420500013401e98602c494142d0315080c81e01026031241c035442c02c1c0400c030829140780 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 928373660 1250 928372410 928372441
    0x307021506030c01090923100819020f060702030a061113300f021804030e040c02100e010b1e1005030403090b07052103010503150108100b2106 63
    0x10201c02502074074041600081c01410a4803500418031f88130408810465540840390b841c0b00311604000103903190054100c8900c400c188140015841403400441c400121001c85009840e80140080c034040082c408018881c1c00480099074035015a1100ba4009a03081c480c00400103450400c5541300c0c0c11440060f40c0c591000c0d0300401003051031070081810b00ca0468950300c2c203408a02d140c0686801a41408490100c1c420702c002c0d04152541281085a40d07000c05180c80346220365100d0702020819814002a00c103540107400142e803111040201d41b80c45a0048030404107076400002d03209510800003000c060080050b400301c034070b0310b4141a00d40c2c00d14100b0a804a1880d0074041d1544c181a0b0b07008000c1550744c42540d90080300446c0c583e040150602c40c1441e100200c105442c00b0f003880340222a10340e0300070f00c1101d109110788090301c00e0030450200154102c902e0180070740030b1514018004030203004881c10480c0d100200c0c1e8041c00c486000e42c5800040d2a950303000070255458a8407501c0074100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 928374910 1250 928373660 928373671
    0x2d030b100e040c0905090703050304091d0c0f010e1311070c2112090528080708060c03100f060206040605010f030210030b2b021005270604050603070215 67
    0x103070104000229105600712412074072154000211941c13480c0f046428103031150002072180c000094002006d654940100794844200d905622a03800404079440e41e481e0710000351a00804900110901c1e98000e100e03010382d0200c068050f805060401c0d03042012984814002c0203540c0b4040303451414003030500108405005d05c03030341d0382c0c0b0414156024080c006d003a9500040a601111008004c0315201d80d91400080c90081e02948414a000d41e40301000c0c00b01c01c81013041341141e000002050100050700078100c2e075055001d00365645500402080e990f10003803c0603507442e100d580014444442c2c0d100c500060140340d019005030708251a00300140c0301d040e0300040c0140f0700d0b44424000341c1c0e1401c55400b44a551400c00150410002d4007081c0649e80c400c86540d9080000107200502c84d07002e44402c05058030896000300c10181d070f1001664980291400684001c0c003040c2050101c1c006600102a400c23030042986051580c0c40700010440e0f4801c64451006802c402c08042d03209801e00c15840c1c108 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 928376160 1250 928374910 928374929
    0xe0406090f1a030d1d0315090f0f280501020412050307050d0c031205101a040305101a0909010605040504150c020f0d030c030e0d080402091509012d030b10 68
    0x790030300c02c00070a100c04113640341c1c0182c03c1501c04070305d0b07650341000f071404a004400c101e04a03914090240644801c84090031400c0340c014610050807000c80401d000350b43c401c00c05e07400000000814462030404070540b004480940d030821001c2030300e0f007414003031504491180004681e2241c880c6002c1e42070201c02003094007404a1440040e0010380c0100d21120700031195000010b169079401c032200203410481e80058401e914000400200020003c01001070f02e005078115000864660805003c0f02c10f9810403400d20420001030500514001d00c10760740001181c800480c2c8280c03141c0014040b50f20944084816100403080350700d000080b070040c500744c4d550500150003004181d00d201511181c40c41398107000c0655070001132000c24041e90111450207a0042129580e4000f94805015100b0944007603100e0714841000544910711305054001018000d41b590416904e00102d070713005c0b511b082814018072a1401c132032940b00340c010301e550002075001d80c03407604141c18499500307119003580ba000610b00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 928377410 1250 928376160 928376173
    0x3020a27090201020703060c030f0c050a031103010503030403030e010203223b06040e24180a08090117160801080a0203070e09160603140109020405010e010e0406090f1a03 75
    0x1613078004c41c1c01800c8a80041d400308041c400c40d0b1003100240340462500c101586440040345400d0390100c09014a4030594504001d25412a1b048403200d0000f48140c0f549035200300820700002303209102d0215011418011681401c1c04201d43d1700003640c480c40001048507a190381001040c02c0c0002e0400c56a03452422a041519180e00c4515184422a481c404400d0100301140d51030700c440d8807801c10101c00506842c1200744003203000c480895111110301014030b0081c0401d0440c00300024201c4482c107004010070308012255641c855030781000000360f0511450320150756404103d01d2000d403140b0060580403444c2020458060300800041e08030103072642c41842c6a40060300c0c0045d003038054516201840c1c0280d550350f0007007454003032a100b488560090340c0e0070004089401d034000707007004900d065480e5070680c1c8814080303089000e1403041d09e0004010050801c07007540904c081e2840b0034806840882c00907240e0110070282d03035035034044030405551070795000241c0c0d5840c1100c5a40c070304102c1c0545079 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 928378660 1250 928377410 928377413
    0x100c0f08010e1302030309030109030215071403012d03120306090b0d0209041103010e0a110117043005090f180106080a0f0504030c11010206010602121303020a2709 72
    0xb900c014008803141d0b45101144055580400075140a410700030024070002d005890001d44504405000311000e408403c0803a203914024890f403000c0811081c1d240f03086078685131064107480805441d242d02c4003d62303180300d00000e01c6060100c010314001c90711000800e60406000701240d44640c00010041d2a002d491a0b00e80c0c5d41c98170142a140d01140c104860740c446042000d001040c4240099044d840d10080c800280c4002c50070080060140000514542c100c000650b440070b04180c960020b5849440000c000443e42c540c00840074007000150300b44002115258021007084018a401050021541104902d85080340c4181e44c0025201d130003203035900342e50300d24003440306000309420300c0f5000000511202c0e049e4000c0481c80c0205800740280e08103810b000c4c2842408603029107189040040d02019540000f621504a0341142c3c002c041c40c05002c044802c2c0da410941b1013440800801d880080980c0d505805c2401400000b40ac1004d1920581c141c101030140c4e11810340100da0400d81e02c0c00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 928379910 1250 928378660 928378679
    0x51005122b05040b0301060809070e07140a0e03060901020c120f07080703020a0c030c140105071505070c0c0306050a051308180f1002010b030c01020a052d100c0f0801 73
    0x90784844070115108030a08007a000b5a102c1c01a6044100d15020100000400300d0740008801d00500d010350694004913201d0141382812441160b8410100e000041b4610380e01c44014002c210303c01c082d2906000a0f840c48000a08000066401c0009a900800c1c003070803544050012218a40040d40ca20b0f00c0d010010819200ba4010703180003814080f0017140a60605000b4002e460b18198000e440d11047c0703840749048100e8114502030010090f07071a400604895015000f203803c610742141c6003921441040c202039001d008018050400c0180001904001610444811010750300c6038a0102c0d551502d640190203c0b0785c010b10601ca1006d820950a001c10f481a007115012800c41d00001c00a4100d0340100b662400070301249500000c1c160b8410541540c10341c0603480c01c10049050343d0a590100d001243d90b603091020142c2036400072010590200e03003101882e50743c4404800d113030740c5501003000c030136041005500c0307a1320302c080e20f8980760740900e580b0502100c40c0301020704120400d54140034021 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 928381160 1250 928379910 928379953
    0x3030b03150c0d0f14070207081b12030417030711040c0507060b300d08010509071124060a09060506160609140f07050402031006030911030304060c1a0f0f0c070605100512 75
    0x485c000c00010846811120f41801160043c0c460710000010344240723b215030b56640c0c040c6d2001d6071800c0d1241d0480c0054a0306009440c0c0b800c2c6c0560341e460410300d40c4e0b12960018581c1d001c28a074002044900200002d0200440145500c110082000e800d03d0000e4003034101303010500040100300c1400011f003e980d940804964000b0014900070300c1c111284c100701d500d0000300c0440c1300c8101d40f220b46240b0f0482901ca120501ca11800d40c0c0440203166150120340c15101d0031f00485510080a01078440c960311070503c1808018024040800d0030f210503180d1001c1400d600e408218503801101101031120b0f000c11a000042005460440c50361030414100540e03003029025160400d611031982c0020710140c442400348503e401410780703554540d00d55001d02060081d43c400c0720f0602e02410000800014900501d02ca03d0b4480001d10540e0b88042001084c0b0074018900c2c4490070040c0039038000b04001e841118450001401c01031000780c104020006109220003400c48036a20034070040e0005101c902c403c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 928382410 1250 928381160 928381213
    0xd05010b09061902010e030403080c1009020307090e0703080d0b0a0608060f0913060606020c1306030f030e1203042312150c040e09070303030b03150c0d0f1407020708 73
    0x56000503c04000c03800350102c1064052648000728002c01802130321001480902c0f004401c80d4403a0b031001942e442624640003002e0762642280d0f00802038005075401c0040240403400c00d45003443d4032a900d100103500f000040b404e0496a034038083d003003800c03c1040d40000d005241842c1100f403174598002a2070f0341030200c055025804d0680800d60400c800544606501c0d480042444019110307d0300035600c180064425108004402100c40303003000511843c0c007540d80110043c070f18002c17562801c2c0c54064560300c1098000f0210300b6218181d140600c0500054204140c0320020100804020480302d03680d5000c5c980704418940b03131440c07607840c0041d02014803104009011444d94448017421401d01555000c0110048140e0400119840c0410390000383c074480d1b1010030120003088285540c581019140b001c1190354500444c943d80d20071000740052000d640008103007205240c5400c4c05648182c0728841114540109000d0465018000480540b0110000300201c2ca184105071001d150454031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 928383660 1250 928382410 928382437
    0x6010206040c03060c050d0507111b01020307170408030706050702011104080c040e16081f09080d0513021e090a0e0703031805030d05190e01050703030f140109020d05010b0906 77
    0x3849a20a024900340c0fa00c0201f032a01c200594a4803081c040e02c812000945240c50f40605060880382d6804d040741d0201401d410307401103040a0003940d440c18850100c180c0e000c1c040400f07110020f14140100002c02e00e4034031400d0049103d08001c1c1c0f01a003502c0000340c80341da0000e0107100500000c0d800040aa404030421a80450005081c0e41041d0809030750000c00c1424080c1c1c0c020101c2c4518000480e09000d04194140c40c4050340c41e5a031000448175032020050040310200402d40c0d1082058101c190858042c0c40820038054041c1d000900081000c0000000115800c4030a400c5203820b9410f00d40c04001001c00f400740d201c108000984400c00da020050501ca1260301c0000f06078078151100019110141c12034141c0000b150029149400841e90000c07440c41c002c00451030b091240300c041c2000d01043e180c00342400311680d01a0b01401c0780030079140c46d0329500c0e05000362619540031054020070707400900581c0c42a24010100c03d5400507004002c61010030030107034025464820071140b19510340c10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 928384910 1250 928383660 928383671
    0x30507140105043b0c0715020a0c0f0305162003010903080c1606060b041a040e0402270a0203060406050405010803031f170d0305090d08070f020708060901060e06010206040c0306 78
    0x2001c1c4c8540181800d41c0f4501004040020103030080300140b4840f801440301604103402d5800d030400340d1040c0540000014034071040c1400180d660394901000798800d00340241000700320ba4158140707040c1d04506690411b0990003020800d000145460b40b1600103038028894100b59840181c2400006014003040c4c000015034581d01000c55415120025802203080c040b4594402ca000d8858020b40580c10000300241d041d582d25615690031902194490440d00fa01541c40e0703020883c8813801d40344a040141040c88440d0b00300c2d20fa05400c5441165412001a140d00b0044e040c4002c82e10b090300528099490900140100b000000960b036001000c5002c0c61841040709000750756012503944000250655207100c800c50300008607040c00c04c1e00d1180e070100702c00da8624403145c0e500d000c1074003401c01042148000c1091244030307080130601d44810380110b60354940d03655011450901c007100c104001d0303551040b00303100c8008804003143c0c001009200801c0203003016110000710040e180b01c001d2a00e5940d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 928386160 1250 928384910 928384979
    0x40209151e0a05130605031e0d140d050a060e010906030302060c1b030a030603060b1c060b030102041203091508010602071206180305070b06091e150a03050714010504 73
    0x400024010180101d144003011004135006000540100c2e846402010410144074044800329600b046035a4010b10300c0c00a40c000c25610a0b900c401c4200c401d440c20011744421070b0075801401c0c010b0b0011080020050301e0048041c1c01d01806820200c510ba041c03100810101e6400034025030040711841005035660031582804149070124254800030f8080030484514050305640000c085034041c4105215400d108420007102e10700c0104030303c2c6540b086c0842d003404580c03640d001690f2160094001803605032200c4c001184110020030880000381044002e02c540452107481e030f242c0383d0700f501b4048400e5041c5a00a9192485801403281d20400448541b060060b1500f0200b01220700d01c5103a900e00034107003002441070340491002c1d01e00754112130100382c45007400890706108011400c84402446882e40400007030035805008654040c1c0c000103007400c507913100482c0b80021449003004041482c5007002010b001c1503000a214103102d8140001c01400c14407440b0070780045c11102e62a100040403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 928387410 1250 928386160 928386169
    0x50f0d030209130536010e012a1205010b1e03160c240504120804120c05030c0105090a051b090f04050f0d030c03181502160506070206040209151e 64
    0x10240c0d50707a50020340745e40040c10183d4014200030445c40c0d002800503130100b2481a0995003003c2961120f010741604d8280b54100c0c03085070b1000111207140400b10f00340c1d42d4004400f0340d402a00f00190a03c0c001950300300540011140004800d420001181103103420000030b40284250500d03072040c000702a03c96000c2080440358076220f0440d1b180b003115402841d01c204070050000300d9003201e620655200500d40180281c68017440785901090f04e01800c40541c0d4101e64164174010308481a1009100c040100003080c0070b09842407a1a800500b003044580c03c11516081ca00794960812002940215400b521185d5080d83c0c800c40301213685c0115180d519040d40303448102a654802030199180d16010035505800c07100307910b600366800380401c2c500854940d013038140c2420010214048030804071a00d0361507070068410080108804c0401c014252502801c01104a50440040c1c10000c03c000c118030745919030f10f40144040c0c140f02d5031500c1020204601c03c0704801c1a10003550f4007a4461840c0d5039 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 928388660 1250 928387410 928387441
    0x30301030f140f06180102030f01090e030c010608060f061008060409111c1202031201090914060c130b1207110c280501050712080601031503050f0d0302091305 70
    0x80c2c80c01c403081d0702c40099045880d054259400c6078260700c0340c02c1803441a00d0500a5a0003611003c4000d120360340b0f00380425004000001d400c03400c5d808240140d0144c0c0704203104640081901d14080c294034030304501e05000013a8001c140b54451150b41109800065110341c50360760010040d240000d1038040d03800c00c40d18910b01d580d80d030341c0e100d0800c841180c0010300d251a2640f8051041c0c108100709441c6080c16a01c1e80a892a004402c00241c0010014840316410400200e80141031780000c08600c00700740c50609900700c400200e40900000c082450204080d103000090501c0540c2c00d0a20020f503403080361b1400c1c05840c0008000c20030f00d800f001054103002d030b01c800c100300a06400002000518040355104c044500c0340400c9410000062554040e104941410b0350022210081c513138400c905841c0514054001410156180e1501c841142c0c01254000514040c1c0001c0c1454244000c4542c581684c0c041c540c0100760042c00b141c07038903850703440700c1183c0c00500800100d8650380d10034030b0406600 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 928389910 1250 928388660 928388693
    0x111813050103060209010201050f150d020d062406210518010c0309050f010606090e04141231050f18040c0501270303080901091403210108030301030f 66
    0x925040c00001048441c0d03008245038903080c1c0013804503668000300c0c1d4001c0382c011600a5070280f02450b10040d03601c0d050180503062840148030194400860701e50304201c7da10195909010740426445000102c64002008001c00e10f92405001a40070728500d00301e1011308448080f82e02d502c60020402d00d10040780660307508104400208100010410018003038030100c4070035142801002d6036694042018007500099030301588070b03c1c030340030b25040061801380f400030700c00d403281d4000314440d0142e400b041c0501c1f5001c80ca03c20040d40c85416103a0400d100803d5a541c03010f044110030700c08181285000b042c0c1d03040303800440721224041030b072002280c030b5032018038001081010040104400c011010241c0c100f607500a0740d1b00c0f40c146012004503101d00000300d4403d5021702031010200002403140a00c0c50380000c4050000c195000c40b6a909011394100d01a46080764202240030750440c10720301081080c0524409034405154541080d840d160700c41030101928501c1442e0780c000a001c0c91088148040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 928391160 1250 928389910 928389949
    0x10080d052a10110310031407080a050a150209090c0f07050712050d050f180f0d1a07260702011d010b090f0408090d2102011b031118 58
    0x4003045000c41d40c8603000d03503401c54140c0d480c180d40400361540c3c05040d02d00c104c0c0e081c00740300101030540d26100704d040c041000400350351240101c0440d090905001602c16680b10344000d0400c0c840c980760003070f4400415512109220b10500551303007180c2e03420b031026030003098007031034503a5038480e000400050303204800002e0040d100f0711400161083c035044e001c10240d4010400e85842c0010150111280d201d10f00c3c1741d00302d94106000240c41d05545802d0f007c0c2740c0a0091000c82907003500b00100f03001080452094444115040000043e0840c1a50140d8007641d41d00d00b24202c00d0207080f07002107080300301480716240070360080007a050768000d504c40341080603404002e100c0807e0000ca010301038100c2003241c0e805070b00118041880350502003105401039521205040c18016800180110310010040540d1fa035030120301e151140544501c0c0b6000011740603800410203031070795054010072030500503481040604d0b00440c003610807082800c0c2c3d0031400c030010110113a4051030300015032848020350982c101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 928392410 1250 928391160 928391227
    0x904020310020a081803030415150905040803060f010f0504270e03040f080307150c020c120c010e0303072415090203090d030b0906100c060f0501060810080d05 70
    0x985801580b40e45c440d50b0522028052000340030312140d240d0001b07440041000d9410f12981000118a130010290554082800b00c44030740c0d222201c60070b55900f60b6040c1c5240c08000213000d802c2c01d14610285101c0c80a00300007800302c552502c0149580700d640308450b0610342c0449160020741a11119044c01c400301c5006000301010303980700c552a94440c2c4281c9100d0000c0800026240c1d0010050f50810340e00420b25400301d8500d40d1920001d4804020003008500030722420318103669805c03265001e80c0000000400070b00780580005400c0100d038011a80c401d034030034050140007030100070340001b1a0800703802039410b280103180343e00003801007100c1a03042083d50b050045814209a80610322443d02744003124a8440002d500b941203881c2c880310150802400700019140707040980350130300040400d24280c0040c0d2416114a0111110301100c410403a40700e60042001e20b5003c01c0440c0c1212040d034091003424134040ca80c507aa41003d0700120240300c030119581c1070341c1004200c05446032a01400000b03c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 928393660 1250 928392410 928392427
    0x50c09010e01123308030f0a050c06010608151807030b0d080c0313050118030204180b090a020117091515090a05100f06050304020402030c1e0903060f07020c090402031002 75
    0x20203031850301e400940c5400002d5441810700c4072104c45070884a14401075450a035807801c07070011590012181c502400810042c204a419080024500070000303903485038820f0400e101045110311402004c03901c075513a07070000384010180c41c9d607200360407281e40d080000d0583d030080b011800f126450580913180480c042105081e206011000b00f51000c0d101440e11606903d0b03c0041d11f00c68507001d906900c94406080c01d100604141d44502030740c0a146040c20503030120740ea6190640d9008035210304241d0440f2102004550704110f142c2d000c1e042102106d00c041c9404041c80f0350319520810054583c51b03800000c29506860504240f9407544082c10198140c40c111480301e003d01010f503540b04082100e02d200041c80c4110040c4d81068400696441d0f141d43c890b5000c1201a4001501d0160010f2003042500282400c02140c03840e041c01c03000205446003003800c101428210014400640620750500700003056a0210b1400600b00089a40c011241c8581c000304c1d1501588081c600340440c0300154900 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 928394910 1250 928393660 928393691
    0x40606031208040c1205061f0b0d021201080c0117040602070206030423030f0f0d060506040608160c0f030804063206120d05070f12080403030e01050c09010e0112 71
    0x501c1180120a02c21007999a10b40903850741c45602005400381d041500461030350803000c10106469101c6206d4034500d03680303d41c8041c100303501080ac1c02d20b1466000541c00841b40713007444a58010540c1c240a015001c411390000b90411810700300325640c60034020000780400845038140c510300c60700070300100d03103d10385842d0184080001c0c03a40c0c441c4446908041030810040001117038040d08052000509040060342c0340d00040c1c001c1d1001110498444502251035103691010f08010070665417031400500703002e0f007080710034250052020100800d4224000c0820b1140c440942c421764103240109190b5280d0a00b84000c0c20303401d201c0140d080316102d640e50a00042d5040803440c010b04482c01c2d0190b143c081c10801440b502025451503904030100d51075546005002600595004070354440f00c03440180e90300b1500d881036211703d402086401c824070061651500c2000f580c510305074000c0045080c0410000d11500843c507502c1c4c10407688440c4154030780d00c25481c2a9000110340e01c207001d080340801030ba1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 928396160 1250 928394910 928394927
    0x15070b0f061c021c030e06070302060f0c030c040b0702130603060f0e01020306030705091803071506060f0c170c0708100506033004080d08040303150302180406060312 73
    0xd82c400d4048802c0e620300500103080c0810701d1540203188005000008010240307080c0c03000420380611a1442000400b41c443c00c0c020074203248030384d001d8010b80c0f07002d10038504108070142c281010000140104200c440c0c407041150240d842650361141c0f5580b2078400038580348030444110428a040002c00400c00c5440d820844044801c40e00c18020b1510300c8000c1d50803400304542e0980e05903ca00020460783c02e000c0305540d04506034011401410024031842440c560116000b1112548100740c50410540580b15100c041d140b1842d201f031074801541d000a1400103400009801020941c2c106c41e03001c0340000450366200721071002c0d40c0c5000e13074803240141c032941d400525034006410100014141d20b13000c00c140b80c1d055801e80001c4203541081050103140c48280d4102c00420f0400c2001042c00c100070450f0003544003003540c44062520f0716240081c25640d03500d0042e603034841a20800e2006903201c100120020841b080c085000e46d0362400e05030007420459001416034545e1704291030030903030f000480 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 928397410 1250 928396160 928396171
    0xd020a03090201260103151d03030a060e0106021b0109050d03080105030d1b0b04020d0605160f11030a2a1a0112020d06020d06031b0e0a0204080c15070b0f 68
    0x450611015100300d0004010321310340203045020701d482c01400000d0518012604140000400042100c61244022840c940d00a04520320740d00c04400c00032001d00500a0101134880058604020752600d01d01a540310074038885400c91000c1c081140403947d200d03404d00b030001c150041ca10081c400709801c015100a0080c06114000d01034181c41e08507880c0204400c0180445142005050341400d494800300441d000d00102d0388103c03200b02c50000b00740c4c64004c1a000c1c550350078010304218200c0d0b0000d81347c4440f04105d00248072030b010020712154404070a0b50700c89081824042c43c0c9452803510140b507000201880703a0201c0c0c00c002c1c0c110910810b1489150f00a250303038a145002e0b41c0702c506001a8080c0010025440100034420b280000c80640242c01514591a00400c1ea41e4490b5140313601d24004004000c85020501c1c02003081ca2103581c4400d03002089098218902414a07884a4803a008440f03100e01541d00241c00f8000845694100d8160030b81184102d41181010007181ca840c5506071103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 928398660 1250 928397410 928397417
    0x60309050705030d0c140c0415090b01140313030908030d0b03160e070c02061b0619050f0705031e01090605130507021506030304230a06180e0a020d020a03090201 71
    0x5000c600c0f8100065508503462180d11004481e40d0540e40d00140b131481640444a9030081c65030261140e02c030381c025514204014905401c00c581040740000494041c030380654100000004141096035a14040300e4100034520508115409582070982e126581035212215034800000c42c04001b0520b030340070400d1141c044050711040898a00300d030303070700605901a8a0120890401103140319008011461403144080c02060500d40e10340c401141c503c41903090040641c000b10308104030b50040c070100b01c5441031ba0f04010800d0f070910700d126556004000b04100207210000000c10301c000003c425854480b000050140515038480c5040c13000f07015144120b42c00b585158110400c0b1000501403148940d110b40d006040c00c0f1000e000701d00c0c46000103845a07406020030030010130031000c0c60120758107c08460f282001c43e8102a0140284400aa88075004004010b05590420303e030b80042c0e03400b1103211018030100c984485d0b00c00c1c2c0091183c5402001600d200042e5032140355015048409214000d0b20b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 928399910 1250 928398660 928398673
    0x509060c0301060f03021b0d181a0702100c05030429030c120604020408010f15091b050310090e0c01080c1602040e010605191e0b1606110406030905 65
    0x1440c0c0d9030100b8040c001c08901e40d40e0b54403001e90f200c0e0f8060000b03035400e03142601e94885142c5c011030406001007800c1000038030201d1410f421409090041d0000c103c20034250140c0b50403200c804416000e561030080c400c82000141025182c410b07001c80d00004d03040020750755100d613220a201005050020b2407502448540703601c5150807114410f481c8a2074112030f0f0140b4000d860740ba8080702c85402007078140d02c582d00707000101d82c6c80c00034420380301c0ba0b01c02d4000c005400d00324a90340c0c005180055100d0704241f82003141b40100400c0c05c0c0b152102070406401e000c1e80700d4039400c040b0103030003480d50000350125152010040d4000400181d0500d0701d08203803105441c51310394180c01405c41c0b0542181444504440c414440103051540c4038800030f4484000020340d40392500002008072540d508515030b40240c50206100c3c1402c9000510401070030020007524243c074105080c07695001e038009086111001a29400600c102500280d0b89034101181d9282c1d240d440b1030000d002001c110740252424420300d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 928401160 1250 928399910 928399921
    0x9032203050601080a02130504050f0d020706030e071a07210e04140906070f180e06130b0f06070f0f0303051006020c0315100e070c02100806011e05120a050906 70
    0x41481000190003400c80c24071a1f00d2004080081e04014000710303210701c140210000b07188818002c3c4002c00d10790b41d0144c000745140c02c8008040e58420f0300002c0d0705400140f000c010020b81320305030341d5040503030340c60113070b2118030070708000c10040c0300d601d02051180b488642ca46e50f04e561050550403c444200d6017040700741c040c4940504031600484180c940f82d03202a002c2401c1c140074a15112501c0d0561808016a0354810310380c900c0003413070394000e03d110760040d4140030031807900c448404000141c88408100741c002c800300007804810400c1503a405160002008001d01400c2c413105849160086410300d4141c1031842c0c010010b00088803000d20282e403160010a085101007044011464010000c0c050020546107440480e00007604018145460000014140410344a4903100d031403641c550070303000c850500501c140b03a82c95032201c90810201c8810040540e07004001d9044080c0c0e60b151029010381410b005642d00d101c1c02c3ca0700e12040c845070b0b081000c0c514a40c3c1000d0702c1107180c0c00030b5850903144d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 928402410 1250 928401160 928401163
    0x21f0b0108010b12190b131b0c0b0106081302061909080a0803240a0f08010f27060e030403060b030106060f020d08070201060b0d14070e0307050103050903220305060108 74
    0x39601c210754104130700008265810040508032051540c640000214024400000b5141011803a40000056261407003d680700a840c80103060840e0702d424001031129031030b51041044141405604107104010001c40c41003000c2940c54210942c0c0940b00030340d1508112100010300782000540400603070b0741d40c004511040c02241d1814115400101141180c41d02240b20081c0c0070251200c0080c031a459200204035610010a0801443c10120843c00c85041015480c03e50f03440d144415440c609040300710607070b0201214004052815040d020384d10980a00e4803402070a60362603d040b42e07100100e004400e00110f030781300000c0010210020815103680342015500c0c0e0020981a90260f0422007018131094082c50060703038401e41520000408a80f6103594007031340d0b086040c10301c2d4240d984040135407103990002031094100d2214140103643e84d2184c400280d440589002d00b5041503180d002098003001d0400a0b030380030540d40d044001d0003008009044090455520082d5900d1280c4000001c0310f600 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 928403660 1250 928402410 928402417
    0x2070f0303021b011805010804020d0503070f051501260a05010e010b031903050a0c1a15040e070b0915090a090b131505090903071205221d07021f0b0108010b 69
    0xe000620f05c18985404019103109500400580e048116100d130b4000144082c40107014151081d01c50413600c44070740c1003403440c00c041d502000c901d034200100140208131143d03074440007101e502081e0b8500d00041804450405519420042031036080c040001c042c1881074120221542c001e9044407541070240040000c1403602d03e1001c0e0214004005040c00240b1482e424400140501340420010181e144500e1001c9001c641014001c132400d4088049071520340070350051024081f0043c00e03902e00749441c0d00c00c81d119803070002d031050112001480c62842e2902c16100c50000003400800307616500c05440010781580419544150146002096003603090704c0380400d02c644800c0711125190801e01400603400c0f0161201c80a40310038401080000e4030045158005c1065a4905445401903602c0704a070740d03d514191410310b03031002428440c40500c0d07840740540f41d000c40550403960312a040c00364105658031103902801c01d0000300c0001c041d8803c2c0c0280398550000c3c0da41c81a5a03030b85482c00c011a01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 928404910 1250 928403660 928403687
    0x1020c031b13110904050720011a090417030603010e150108070b04140613030210030f05010503010e1002030709031707110603040302150c131202040f1b0f02070f0303021b01 76
    0x7070f400e0001071280e007800d5018603404802810304682c4141c000c080311a05415501100e1501c1e9152400307080e40e80a85a4150f1100c0380554400d000c0c0d08143c2d84041c5280d0400c0030443c1d4005020002980c1c80da025002a18002a6042a07e4407880d00781d02481d84141c00340140080b900c01e5a0000401c400c2480c2102e04440d9443d0103001c01ea00c0300020089241d0240c85480601042540d000c009661210003a41804145403070011b01100380c804440241e501c160700080c460791624014112060021802c89024240f4500041c3c0d00c0d521144107842205030740c1c0003d4080c02c15001c1048002c12400014401d85000f1002c5a42000085042000c6448100c5000b80140c02c200c4000d150341621800c0182c10400c4080d40500b482d01d04103141c00d003991503078460384106840003e2081942090b200f04484d080c01000b09000c2cac0301c1a01003070310810b130407a500c2a08000801d990091050300c28000040582151501003811030f98900b00203584e8148010000f0000440100c05c1000e03600480001800c00d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 928406160 1250 928404910 928404941
    0x60a1223071206031a04060b010908030d0f09060501081b040c051605100f0b0a080a080417010f15061e0801060f1103120103050d0e030a02060901020c031b13 69
    0x958500c8801c6030499008040301c908643c0360180400080c010000c030050709a44502c65001d689410305080f0260f800501c8200c0c14401c80c10300901200501000312040e40b4401c0b0401f1032081001d1200100520310844080d0410346030000118001700e0104606c00303200681c440622608114a00704030031140a10a10400b00d2820030244150391b2024020b00d40060148080d070b0003028036441040196070040302c1c1c100c410b50b03580205100350300d4502e040101601010008110f001c20996480314544114040c95020104010400c250007109401c0790200707240f080414080c0d003148204201e1506258010200414152841040354280e0b6180c52a168007080d0385950040c2d207071003400c0c0c491250210b840401c0200f688507090416a00300014000e0380f4221104910661640c1442424201c1004070201000742d0403490481b0b88d600010715104854045901c0d56640c082140103078517114081800e560980900116182ca03400c401d44688000181500c0c0c1070711406041d00031004031605400b605400303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 928407410 1250 928406160 928406231
    0x8041a13140112050f01080706140d0b191e06050307080705220305032101030302030421140f0c0d02130c0513031209090606080a1505060a12 62
    0x11a00071842070810311006042072000d80401800550070b0740d04c21584078212005c2d0000422071003d00b00004002840a07282450194440c00e01408543c402c008001008a8590102c10345641d42d4840f00c020f6824405410062103a803018503600c03507203d031110506054401e00d4000f07242400345003100c0c0310703002c40e0b65035160540c0c034810300703407440d030081c10b54142090094040f0000114858160501840c050802103440e031100d0781c03403a07600d5108a040341c02034401010040002a030000300307075802c0c3c1e084031000c0c088021203004958100040c5408c041d1800610f07911854034a038011a001203210305803020b0301d0141d0748060030b00c001d000c40306000030b402502c03c1e14058170100807540142c00301300c541c1c90b01625008507005c2c8186400031039001503a201e2108030b02d8010716604150000028080c2c1c140038401c0c50720300b0744c01800641c401401c1041441d25480c02c40001d00001d0303074039400b901009110a45407200d484004003048502508040c0322441c2c058030001030380f1004944014841000e07540202c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 928408660 1250 928407410 928407419
    0x3030f030908220b070b18010618020a0219080c0d09051806120a0c17061b03102303070512031b1005010e0403081627030f08041a13 58
    0x22042e400d90310340642c080c20f5800100720940c140004141e0a40240f001d14000d0414280c1d0345010011110214041d1b031400508009001111303a950f8100410710400585542c4860016424515810030300c0e094031411919010401c6280c3c009006140c83e900100c43c2103a40050094031502032900640368065014400b610782c040ca072841180d4004001b40c4017800200c184038030b00345042c200380320485402c0284041800704650700000e0b00c001d885840003c0180d8144040700082c4100c00050f05001a20000002400544045850401016040c4c83d4481d84115141d0078050381340802e4045129001c4d10500050345e141c68420ac0b02d4558007400078500d4000f41d90303000806500f150701d8020b000c0c000c1c44213621140303011f0300c106402440e21454003816403425240041011000404980c03007103207040394800056034000c40c0d141004a05074140810300081e420340e00341110f180d03440100b1340042d04441c0001c01c03e0b0240548100c0718a201045000849607940d807a080c000c0c00b0b04c6040400000c1c10801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 928409910 1250 928408660 928408687
    0xe060919050102070c17060a02160b22060f1505100e01090b040f060f0305040308180705040f021e0c06040807020f0405070c02130605091503011b02010603030f030908 73
    0x50001d1289000500d0702c0300ca50341d03805001034944d0001010660300c00805074600000e124190b84200401000c500e0700522101d1006001c65003000604801c02c8000054061542158282208207480000303403648421868094080c1240040e240786690800b22820030485801e010314040d81e00040400c818070390903160413141980111a110704001803000005400380c90071000703001800001080c901101c1c1401400f0340700c0f9030b42c1c001072000c2625003810000800d500ca6405a00480b1401d0500a0070080000b04d62070588281c1011303601078a007291028044c48a03034000c1107401003444101318011202c071441d541501503502e62000e84d8000600160008900f02c00600fa0580300400385910380c003c910114007110b4003110329101148100c400c02040d032804601c0300d007005d031480c1014021503007080d010900c14800589078540c20444c00000003816602034115a1030b0f2180c10700200007904940800070b01a0806100a80c0403d0b0340d050004880c2e88030780142e908050708480d07a503180000d01034030381 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 928411160 1250 928409910 928409953
    0x12060f18050c190e01090e07050a0509160201022101080c030a030c08030a06212315090319180605071109040501060305070b120f090a0807060e011e0e0609 68
    0x2510f04220180401d0502c503505000307000c0c010401c0000780406c4228041442d009840d004984078803001c80b01002282d44241d025503010702605056072815410b15001da029000340720300d210f40d07080122100c1d060b80c075210900324101d8003508119a4a400c1c614141900c4281001001e000244101c1c424408104440000c0d5044100752100060b140e41e11020168015400000215085021701d01c40d0140042140302c1e04a515240a40540d0050b1160900d5521240700d442c0c41107418660b40000d8141500780144c0c1c021006480c10803021458002001f4a451107880e0b000e0b020745000000454a03030f10803015290300c243d12003070780005140c030007040203000800184119060f40d2034441c0400019018007184005114110170f182e02c0d40715082d07540c289030b80d000384109a480e009a08002c003c0c54002941c000164004115950720300e458103001001c3c007854401540c0542c02d01145004000400340d05ca02010540307142040091010541241c039030000340c1d407000c80359003c1000c0148400544040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 928412410 1250 928411160 928411189
    0x12020a0e0f090f0f13020a033f12200c0f060403091a13080303090c0607050a02040b27010315020a080105010e01230a0906020304120f0c12060f18050c 66
    0x445d03110384c1c183e0b03000440e04840d0f0f420459540c05250f4000b0421551100c07210f542c0c541c0d103203046c105142d010b119402ca9100d18405c1004100b1350340c0624803401003e90252a4080348111f080c3c0700390070030509010050b031000c05841003034482c0005400c100d0101151040c081c42e49940c0e5003600c50701d0021102d11070390b0707200c4c3d20311300001d410400803c03440d0b01c4c811143d0003885084c02540e01c138540070702d446080c400c0c08000300e4020002088600d0009001260060b903855040350300095a81c0c1c468080b41c4001e034481284140d09451009440070b480840c80094100d9105003000c1e006100c40340d005400b40e0007003080c14000f18014000501c4558092001c14070f20140615155804d0895200b10035034a20400410700d4400d0030010703010800c280c0c400702510150410b400110b2034549410079000c900c070315041029101c449009030b444104050100c0100082030701311500b1501d0300c95801c10358010040d03a03d543c811585001d40c005910080d504880307805d190080701030b0601229100600a46510340c3d0346 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 928413660 1250 928412410 928412431
    0x60a0306050306040b010302041b1e0516150c030605031b060c16030c0b0309030d0b0a09020a02011509110405040b1201050405030a020d170c0a12020a0e0f090f0f 71
    0x100071036540c50070000c192007140156814505545140184030896900b000014611540e0340f0400b00c10300d402140d0080141c0d0029540003000c40c800302d045501e4040c510024840d541d000c800d403420312900010020024100311810807040b50317101c40650403641d4601c142c5416030050481e00c1e40c080e150000d14051075401400d007616000030450558205250080d5007280a80d100400b0701c103110502d100540500301c031890f00e41c50b60030142c0c44070f660b9001d6401c15040480c0c40380ac280b0325588648041000400c10100e040d51a58030392700001c0e018104a0781c210142040b858000620200c00e03000d017501040c96a00600e20f0281031406000c06091118034940c0c2010848011820a103030034420140300c3c40c011405191900c10301c110003410001030300e051804006031458040c1003000500d102503000000351002c50780d41c0101c07042c01e86220701c04802044009102107200c3c45420b030800440350100b0400c60390070f44178207801410050340260aa408031910016a40061802200140d003d41c100c014a00e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 928414910 1250 928413660 928413671
    0x309120c0f090c0e0d020a1205070b0315040b0f0906100c050a030f110c0913060e160906050105040e1302030709020a03140702243103090b0406080105060a03 69
    0x3019182150301c5a0140c0d11441d40d48102c80c04056014650301c010035400c4411030500c1e20320b070700020022092802281000c550f90388281c1c0411004010031401010308007509601ea04c1c20f4400120740c0f0f1900300d5050300907810325a24a0712480c0c10f61400c0301048005142d034001c2c1d05d0f9141030018120f540600036050144800740080031803020802903100c05c0c426652601440400d40004000b002d00349601e0902341e0201a8180e5240e503500b1010364401c001ea040000055018145080680280c203d00c0d420b9000b14007000b08446054002502502e4021009001e410380c0c88004492500c0303070f482007600b10036200c1c001c103081c4d4038010040861240014221440581c45090940c201d81c004260711021990f01c40e10014111044403120364020351900150515411080f081c00c6030030100255010315440382d60020b103600d20010b20004105014050b54046101c245140404081d4242d406901061200307400280c6981510121303403c0c0d500c2c541c2c41b65016440e00c02408102d4005080020a060301d91 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 928416160 1250 928414910 928414919
    0x151c021c0f0c020705090115030513120206041e0519030e090a02030f0c0910210617060c0301050102100f0f020f0702191406070204090f0308070305010806040309120c 73
    0x41c01001c4880d80030300c0000072034900c104000b80c941180c3c4da101502a00221004208070700918102d4240d4510a050118490303035052190400c0c800b0184004100110072699000b8265001400d07911491056020403907102c00072084c075100c1c000d030300c8000303200340d02c2a0b03c5215018051180440d030103101c0d0920000243c101c0c000200c00b40400c0341e0302800243c3c0481040390f0035482a001e5600200d801c0481450180074202048101c40189416428424550251191440c00c0e1580508040710314004000c90354072100345043d11044c02e51203129610800021640e002c0c02101200d0403508140c00402d42d242c08440d8000190170000017102886035244460307840313140140010003442d0300c1843e9959444107584100f103c02c0140c40c030642c02194111505200c1a10561000c15000804a0700948c072441c0740d10004024000000c4020050410816641c003056044085c0a010348242d4409006580e00e54900c03a40c1e892080742c000c3d0006e4100c07030041204e0200e003d0402b00103070103090400d2400361038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 928417266 1106 928416160 928416217
    0x5040b09120432040204080a061d1509010213060e03010c0807020309220207051c0f020a0609150507021b01020102070809100c05010c020c151c02 64
    0x1400b6100403e0f4186000c000510400410640d5501d480350010754031130410320400c40d103050510512414002d128500c01590310190002002640c60f80300e258018560041c08160442d5420000e41d01c00d8400e50410201402c1551900368581c12008245400c40f0100070340001045503d0040c420705a03800310842d064980c04442d100c4200107103586d4540d000404025019080d480040e81d90104140456018807586500b40660b107008001a400da90000e00d000300746e0014ac001440380c000164850340083c03001d60003100050707640149035000c2421210141c0b0800b015038004c103d007903040c0360760f1107023010000c4081c8003c0d07041c2101f581c0d6180700c81c019480d40c0c2d44250b03405810240540d10a07440e091011341c11070000d1004000402d1f01035240c2031443e40316401401e00b0500c4020746076041007241d01804c04043c5604010b0325407c1048020b4001d8158001400081c54100c0c00c803080 = true := by decide +kernel

theorem cover : BRFrame.Cov 928237410 928417266 := by
  have h0 := BRFrame.cov_init 928237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 928237410 ≤ n) (h2 : n < 928417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
