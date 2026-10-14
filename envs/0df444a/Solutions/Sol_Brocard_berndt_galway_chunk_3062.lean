-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3062
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:32:42.495887+00:00
-- url     : https://prove2.me/submissions/c977bc31-0219-4b8e-b3da-d22bed8317ea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 550539568 ≤ n < 550719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 550540818 1250 550539568 550539589
    0x301060c020a051518040603050123010e270f1e0c0904020a270f0c110a050d0c020409020301090b04031701050a0e06010c05010903270806010b0f04080d0c02 69
    0xf104c0d810540c5699059a41d150320030541d00c6194100c241c03442217150303111a00210095135018009000c15024980c4059101022020068143c04120b000048100d04000c50b80c0c0640920000b144039448640051000d4102c0c02c5445881d9106035000d0242c580c00a120b001000c00003030300c00000209650b09950304d41800e10400790f1180c1544000e200041c0d03501c07a260800c44541d043c00e0700910001c25009044086514011100383c0c0c1413a4580d241141c10b980500c008192903250384030120383c9602800e54035410381034020100d60116681d404068091512009410f100070030100d1a059180d001c40e080d6106041c0803958192a0800e2008158000c030840d1030008020212100030340c507003070000e04110b64038850844404855400f14403d648a02201100641c100000f802101c0d82403500402031060380b0203030200b070703080c100203d82088009040d000c1100c82c0301000b800141d0130203d0f641b6442c0d000e002c00c2c000b5000200700c00140c0a03402c0c410481c08412a071907881d40c03030182c0c1c010f00154810 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 550542068 1250 550540818 550540829
    0x30f06010e090405010f0c0e1f090b03040803010312030b0a03060e030903030f0d05070c03020a1106070803130b09030a081f03050d020c010e010302190e060d0f1b0e06031b040b0301060c020a 83
    0x6205200c0d9012742c8031500303050200301c880035458034611200070068035500200e8104003040d044c00400c00003440b601e1b000070341c1240c0c03250b20040e9034112050380440031600044195503118031701a50400100f0415085000c5440d8900c0075645000d180310000ba2650b405030110341441c44000c611071310855224401c1c50743c410f440d0300301801941c400d40d40082d243d01591a005180035006088100d40ea1100f00a07540300070b911046140d40e070b041122485c4690015404121146402351000420742c0401006440c100078498413051034a49803142c007020740004103810b440340b05100e481c0c0000441c0081000c1070261a90750043c1843e50b050b01c00040c42034468015240c1410300402035414090303d6400500c0c0452300600c3c012807554802000220540300d0f241892034543d05000c4440c8529102d43d22050310001c0c10b03a10400c100c3c52455060300d51501c0d07400c500741d00c031030107000041c0c006800c5040020400d0725110007038074003610782c20030f40030641003a017250b0001401c3c0306070001182410810b48000c1e2a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 550543318 1250 550542068 550542077
    0x6050f090601021509100603030513061b140a020301051609090c05160614070315080c0d150b040c090810050105060f0708090607081c060803030f06010e090405010f0c 73
    0x500310700042d43c0c6095003000d002c0d0301140e0000007100100140800324000d51050f2081c420b066481c14010f20070f0300300b03100c40784030b0514900000920500a84803505903005001010f0324140080c1c65841a030708a40d00c0b0f6070b54502503031484000681c0c0070320070b20f8030500e60303607078001905000324800a03c1500c95811210201e0300c0d2801c2c00b0340c0290450305440c150041c100c03141744a04203616110f00604041200e0700c02c07407e10750742807017601c0760103801c122660300b01e036440603070203075521100140c0d2800c081c8019038024100380718140108555503412403110791076a41c00315040a074200403c045408a08590000170356041d1305205580040c04880c914000c040c40c1800700d5410b020004005104806500d85021000101d060400605509507001441e0042030261a002c007400e040c0c04541c1b200369505030b802e01545800be16040c40c1d20598084da20b111006604682c0c0f01c7ca603820321010007500f07450600070000c42c0c0d20413940d41c2865071032089104c0c01c00030544001525507002980c0d03100e1225810b00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 550544568 1250 550543318 550543321
    0xf1502070201020307021c0b04140f210307140307090e1806060f01230d110309100b1201022101290318070b070b0114010512070302090d03020106050f09 67
    0x140c1c1c3c00001d0f905610b4046070111402138110748080640f09115000800440030b907410042800341e0702c002a81040c51031420f0704e1000380b08000307241c2c96183c04d11142c1d05481c80c8044400000c0c00b210041c2d50b0010355402c0442e10801314003a51140343d0812aa00300000f41620b01c20301607900c1c2024515081441a8070410740f9003007019038107440d800024091806404000d8003100283c2c0310f80c80c810b40c8524080000e441c01640003408041684c0b11880c010450360624085902440001d0200c030b00c11400d0002401200c0d89420304080502100c800080d030020a4510403400000207100800150100d013080101200d22b0b0748220340d9041b8140c0c0148400848090354115040396588501d06290326002c1441d50385e56242c501005161406052010320b1098120214040500d2002406510f0148000b0841680d0300d1100c5907001405000c4940041c03c1481204846060ba0900320341110340341c20054100301c100707130214440b50300c00502640140c1d11840101300c2d505050111000140003603c184040c0e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 550545818 1250 550544568 550544573
    0x3040b04081b04020c0d030b06090a0909111008070c0203010b0402040603051503060118051017030307092103030b01020f2409070608070c0615090204090507080405120708070c030f150207 82
    0x1b680d41064481d010f26850300d41c001c50569075101190b00e685001041085072603191040394000f800713410030442300c41c3d1400703041d258503281101d81241c0300700840d0303650f00b440e5070f03886400c40741c0e450148002c0341c00d5900c5901e50707113983d81e0f68000341001e04426500010240307001000c07809600c00141d081c5000781c0160f0018014006030714440344031455414000f080715180c41d101544a0405548030300c0c2e01e240c0f400c400075081d1202100440c0100d1041e070310340040b283c4444070908503440c80c0c12407c1440312502d5510ac000f0340260496041c2c180c05006071a0b00000e11310320705080c200024184001100d000710414100d07100341215a80003040c04004002044c184840a441e40c50050a0201400592212041000f0300c68200c0d0454105584e04900c07500d82e01d03501030b00a90801d0190900c01c50800c070020300340911500e8024412078110000304000e080e005040c0700c480e8010300090300d14003403c021407000300d035554605000540c4244040f010512050411220108068200100042c010401c0001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 550547068 1250 550545818 550545823
    0x6021207030b15130509010b22051c15110301060f213c1406091f050a08030d0c181401050c0d0f020d0903080f090303040b04081b04020c 60
    0x1501c16003d00c0055850751000004120307400c043c3c3c03107150300c01c001030004900880302c4409080b02c070315400c041d031622018291a00c006400f40f802101e0b04106107140e9254150790084142c6c400d00c0c01030f0b08002c00c40300018013810503294100d151000780c10000004110903a444000c0d940e500c149032030842c1c40000c540106402c0a4800c0c101040040d0301c8980f0360920040b03184203103940d003550040084103085810003000d039050040818100142c40c1081503d2034171003148100d4842c0f0070041800341c0b1070790340c011750035001c400c4242401041c21000c00f0100d20780d1990700034580070b840c4000c021506e548540000034141c03400303010300340b08100001d0780d11414107000e00e080009540000c408240702401b40c00040b60b480c064030380799602921900f06c1c5145416040440100e00074455400d5800c1d1980862040e5003181c03040c40010101d0100b00260030841c1107076406040f200c1c0e4010140d86c43c0a50b40c081810b01c940040d0082e030501d41240807508040b844011103840e1822090b03406504003040741100300d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 550548318 1250 550547068 550547089
    0x60b03061006171f030f06051006081f0f0b030115020c030a1e1205070236131403040e07141204020411040f06020f06060f010c050a050a06021207030b 66
    0x2040c0e080e520003081003070740d0100c038031240c06503032013604001d890b501d0801c4a2851550b81050304c4042c07503c4c02080e0402280c00303042c0b041d110107445a486c20384918840e0900009420317955807090980c0200800c07002400089079000703101003c4583d441c1e50500c1328a40806041001a00956100d80003405e0a03440209422280ca40c20144140700c400c44043c8400c0103e041d64801412410007280c440546604440a001014020342e000b400d40d80100b4030700c5000c90305241d103030402c0300300702d40c6014000d00d00c1190b5540d000d9020960101e100d0030076980c0c102088418030400c002c41d003000c1414084031661f165615880442c41c9003c42854034403880c5d004c51445540c0c05007444441c24800107055407956000880c0c02015500910703510317a5507592004007800300c0c1c040c00e40180a1450002c030011800114113010302c00040c8404c00404102c001541d40c40c3e205001154030b80210ba061a0214009008804000d40208005603403542e201404038241b45d4020103140505241102e1401e0300e8031010440c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 550549568 1250 550548318 550548347
    0x100509010b0a06140c030d02040303031b0909090503090618011704080409020d0b1e030106050a050f04360210020607020a08030703180c050928020307050c0307060b03061006 76
    0x1d262000050745500b421720403103a40060360710002801480c508120b034010800c40e4041e54040207001490001e030003020301d000781071300c00080e0300800c1404182e80f641c0c003100300c80b84108100c2340360030403103804640583c200c04031300901d680414900e03c41950f0401e144100c0703100300341c44940881c81d207991110f003140500d000c0c92601030390214441e020f003611984036011000f40100020041c10b030000783c3c0c2c8604184008001e00079400d120000a03603040c038179805001d45030000c00c1ca64444d410403083c030004040d88494054802d016822103282c95010305c00500c0042c2c0c47c6d940c1d50040c0303242e500501034182c0e20000100f0842d40000700708807070f0581c0407500c4400250302c030f4801950390700c8201003100904801d40d1054100d4003526035000c1003002c009040302c02c40d40152560241130307841c0d080c0a00c52808502c040490741c022042d5104010200ba401143c4c01f82c82c0d8240681440305032100d5602d150000070044510076038440082d0350310710f0200310660b8018001c1c00d07181003590030f02100600303142a08444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 550550818 1250 550549568 550549577
    0x3030504031b210201030614011b11090a0b0a0b0403050613030225031b06021005130c0b03070314060d02041109041b11070b0909131202100509010b0a06 67
    0x102c001565800311203800402903850f0480386081c41a80030395011582500072070110b0b290090000d40e400c807084d060000075905031548251201660301240004032040700894090100404800199480341c21030781c0106140000020044e60038001e000d000c050315040303c00c3c100c40501003040080c200017425035004103e4420007464802a15050780341107041211070f16440c004030010b0300a46204d4007182d007124040e1000c0b02c6074240115100604444500800e40143c101603401034a40900c4e4108a0300b10100c00a451015031300c503150101441c4081d0405542c4490000a000005500d40500d03250707484256a150441d041140c000307002e000d41600000d0007151201d04c5804000c0c901c03030544d41c104030040c1041c800440c00ea0b4100c0680d54154407800c001c0f80c1c03d0b80e00310310001c0c400600403060b540b17210001d5240c111810200500c103440206075038251950320f00ba10000940000e180440180c0980041c05038601400e00081680c1008054144170780c5003043c800210303914409400c003258804d090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 550552068 1250 550550818 550550843
    0x1050c07030c1707050a0b07140c1c030f09050918071e030215071a0901020d0f0b0f1e010509120312011526060a090504080a11070303050403 62
    0xa015040648680c009000003424480008100d06a01400040e9415603010744500c0c81d207a004001406600d4000c5050703128040c014100000d40c000d07414140804c0b100129840960901c002500c00c1c03100c0c2c146103600b11003030301c0080f04045c4c04c110100d0781d000c041d0510b6190182070801080302401c1c004e000040c05c545081d0305414151040c484940a003e03440d80880f249481110008803c10b06880100c0c002c40d0411140d11030041079106907440d00b580b02c001000e9850850050750141c50005d01080d00c255420031003561010396610441544224485001c07808003038007020801101c000361070351130140d00600100c14a100b060030340d000c8003440034205146c954507100d01080a0903d0030710340090750b200c00a00301210019644026040303c0d503ca12200044000d258100c40e180c02e03801d80d0584803c100301306804103070303420000b0903848407018050303080c0e503907075054444241c80701900d094a00107400141c010080e90701a1002d017101c4444030040296510395a0000c05034419484041e180007900807 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 550553318 1250 550552068 550552087
    0xc0312020405061809010e0412030b04140703090c0609120609080715050901060909050d0c020f0315060a05010f050a05180d030e04050610090608130605010b1e0f04050105 75
    0xd060300d01401015150540f10303044800340c24224200e4290240c45141042c000281164400078071500c5240d020602c58590f0350304640c00d80142c1898002c580d44180c581c6400701006038054445881500c4030341c0c0102e903500071814110078482c0c064000d41d040103030f0900b0611402581c03084001159070f00c0740f0000344541440c01d1002c0c1a0054107070080c090458003c641a4200d4142c000d1401407180b0030003080010750b07400001d4100c03440e4140007882030708017482080c2c80300d00410704080100d0010b031032090443c8a4100103400c1c840d0010302460b40e50201d009000190608415600c083c20007030902c1c2030340541e003070340250181c0210580e04042241c0091380410030812840e0340c4150754000b030106900c0005600d00500107440c144e0115010b28941030020700300c0d24001c00069426991601c2d61021035090500880320048018404c4d500305800c2060000042c940d07101d01802021000c070156114480c44a500c450b00c0640369400c00074600c00d01c410411a030321401120215002402d00f1503545480e003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 550554568 1250 550553318 550553321
    0x2e120809040c021609061d0402030a08161e02091906080a03111506090a02070512070c03021002030c0606090414010f020406120509030301062006070f080c03070c0312 73
    0x9a00035007045640c50b846500003404010141c0014049070f012901c58902d0412a1071902c0345114150717401804030806050702c0c804640041c005025601140e0503502d6a45155200c610040340c40ca03801c00c820020301440c0c1080d050180425a200b5103040b0303440d000603035410400341000d460500307070a1001e00004203e0740260018542d00303094800c45441c9090140c4802810554074409025002c0400300700201056150b1140030020014a10b94481420070704c001d4001c408211920f100344042d102c02d16103802c000c1c0104a1140c010601d0726421407060010a0107114405d46c150350052001c0f41600d0f002080e001c0d07000c2c1003581c207407005a036036040240c01c90075880c00130040ea52800300e01c10320b50907c0e40c00500a950050b00c0c0c45c800380543c02013a00031920129020030303458100b4001070145511980a03030390140e1002c945002244640a802030034a4410b581c80c1020800150001840c03e81010001d81d004a4801c40345042d482d0250000e090000382c00310040401c103e140c0c0515081006 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 550555818 1250 550554568 550554577
    0x80a140a050f030403060b1c08090103020721020c090c070b04021f11010e07030b010504020f070803240f090f070203040801180c050f0d080d02090d0501052e1208 71
    0x16044402194882078441d03280e43c407a0001b42c40d0700c1d0401040228600304003829002030612441180004600d81d228626a50031000c4c0050406400b000408046018140d45081420b40c940d00700070f038840c580001914001421842d94055101c8204100f1000d10340c2d410748003480e4000080707010603030340c5100280c406c10805078070344908030710016240402e0340d00038003141c1d824610f10300810040b03221150091b900c00d91480f00030207c405030f1005000c0c1d030925801801d60464420612814090540c0d9081e40c681c10031110441e14009160340c20f14078203c11200510030039410703514025502c0c0e091000c43c0c4118002000c902c0b001030f00c0701c082050584204100c50040907050001c21650b08802250086e1090b01c1100341c407000d10102c00811030385030034500000b18240061100c2840d215070f51764205d050308511882c1c030416a081c081080c43d52505800490383c184981d00004003407030014005030860011840150788030300c3c0030003004451020140450b0640b910407450059008047c60b120805125 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 550557068 1250 550555818 550555823
    0x9040609020a02030a0801080f25030807050a120815010c0f050d0e42040e011202040f1a0f06071703071106130212101a1801080a140a 59
    0x10000b6914100c941c0440642440c0c0e1459955180310790303848490655400c0310940c02d4000f500004d0504240070286241c100b5501311520041140c075507203407507402c11508502c1003a1100c1e00041226410030070b25030845102c2c00650f00b403140e400d0610b400e954496280f1a01103a05103c2040c2d4101d040c0540b901c45880c640717038004100c40c005d1018a00003001e41c483e0028081c001e4102c0e45200300188420360b0300112070207041511002028900c60100e00c0780a24540300752480c6010030000c60307406940c2000c94040c10405c0c07500c0380c1440c2184140401c465221081905445c41c1c680d0314500c080504400d40503068048803041400010040012003912407154002c1009465446001468022001940c0314880540317990895a140d1034020380c0755041103862204001c90820504010314001250400741302641089880e9041301e240c41d0300499190500b90711003c3c80c0b201140d0214541440c45003006144007241850651400c403145540707030142c0c0e90040030402c151641d40400b0b078040029945194 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 550558318 1250 550557068 550557071
    0xf02041806050c090307141e010912030215010815041101030b030712031704240615120c05040302090f090f0a0b040c05010c120f1b05030d060801090c0b09040609 71
    0x810040242184d8429030556000f4026184001080803007144c0300b240c0400060007089828400703030014030700300c1c420882060601080a02c04941380c01050900c0d4801d6103c0d80061107a00100094034100b0300050348094203990040384032403d42c0044040e407541150344400b4070b140707480c5510b0041c0c2c050692424096010703c140100005d5102400050b5481c84e406a224250540020402c00300b40020444020f80000b40290b035503c04115000303c5224090081c11000809076118400845292950307410b950001d05504207422070252144108007801c02e1b14213026192514550100360041002080c0340031208030301c0005410908184241408a02c4076410b80319940c105144c030030041d001c192826105c20b00d5074100862154003a1002e0f031211508030306012141003900e10304452550b02454520100401c0c0781e01340d401040310169905c2c40b981304030301854036a01c404d01031300300300d6507160b000740041e0303040ca13145d039021a250f000110103030303100d14245030794074002980820040c1c0300e254000d00c2000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 550559568 1250 550558318 550558321
    0xe090112030315090c0e0f060306150304030c080c0f0601270b0a08070608070e15030f13050d021f0209010e060d060b040f030203060a090203060601050904090c080105040b01060c0f0204180605 84
    0x10f81c1d105080f1b40112604660784000703090b1101c10f00003070340801ca030459044056a40801c1c4c03406421406503a00901c00d1916420400280e82c071010b80e80c00000b802032803079106165200010800780951405045242c0c00705100d000d82c040d942c050408030300410251203a44028003901e540780c1680c45000340035010215032038036a454800800d0301400702c1d0800002140c43d51070340c425141840040301e603514030902450854968840d444115000039081568164038201da04000035810b01c49400d681e40036030081c04004c0c010398920f9004000c00580c1c0c90b091441013004d4110341c3c0c0c202400107600c500a13a0781503241d00c000321888000b01419000b50b00012004500090b24010140e083d5007641c0c829400c0c1c4283e910b41065917030a84441540081d0b01d50802400903086501c6035020b480c900fa4010008038260920362211442081076800003c0607946602c100424010000050750043c0203900e00401c0c90711483d01c0300c0055041e901d9000b44160340318910196580100012459106c1d0890020081e5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 550560818 1250 550559568 550559591
    0x21c08070c080f041e0909080306011d09090609010c050430210311070f020103020c03090d0503120105120604080304111e0f030c01080a200a030b010e09011203031509 73
    0xa04040170b080351a110300700c800c04643d51110b40207280c032699000708103508503101c0000658454a410f120700003803c08072089041242d507a43c21340c03801590f42e18060846804c0c00d510503807d40b00c10010942c01d101d000c00007085074881001d03600809010070003000360441c201003111500007802d20070152207205400e900d100b80da151604224644406610200038280c501310341e069040c050880c0207400a41c0c042003020241d4000d800912240407508156031901d800c46000a4110342c501c0d205580d968000720f6a032240c401c0703401c00540503060868100b0320085507040d44954944000703100401844010001c5000c004024a5014030380c030004000d20701520407401d03418440d000902005204e81c515501020ba24240400e112000000694a240c0390b96141103d03c0003400450f40c040300c441415001100c4038107008409024002e003aa039010400c0c9007000d0006003a07158145045210390710310030040000c00f05030780810000036031504000c2981d00010801040c541469402900701509100e0f14008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 550562068 1250 550560818 550560839
    0x170a0201021209010b0315160f0509120102030f10050616081e0903120c031b0f150a0605011b020904060b090a0603060e011b0c08130e040201021c08070c080f04 70
    0x150b000094040724a02000e60007c03824400040c1da8031121500e0981c6035086103841003103505044070590038403070301d0056400042201d1346000755510549950100a000303015440b01c070281d81000041e2040303080710b8200390000d00103104d50f00d24240d48240c07249202c420409140c0c10380d418200b01a01c80840a60018000c41c910f900c07082c038140c030a0060302d000c1800001403005071090310388824020740c107054058100481c803044070034140145105d0304c901c40d200c1650400c561300311325612004091030b508011004000799103180e00402d051142540c136440e00c0d26844035140c0039140c0c040700c21b00ba8036155420094020803007601c1d0141c20829041c20407100e1506504880b0860b8465107003001059141c074800b41c01c175200b40d070400070082110300b00d034a1698401c00303212840f40d0180704100e180c24401e80a110039200c25a001c003031645041010442990f0701401040c1d50741c86010ba42c6c4d855410200c0d0000c141d120020704017403e1048196100301481240b005031900c0100801004c3e503181e44078041d100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 550563318 1250 550562068 550562081
    0x5062508120702010e0d12061a0702100206010509071d04060e15030a08191107060201061a16080a09080604050604120207180f020f1305040c030603170a020102120901 73
    0x10440e4200c07004a141c1d18414441c84810602c030030007820030b1412000d4101d9203002d240781c500b2006a2076841c00304900c100c44601a00c0f1a000310740b15a500d885074230502c082d00900008180239508a200104501d440b03511070a54810410720b070070a008600341400109540f0661000e6030424603000d000b01d03810482c001c0076406012401071000034000b035401010382c1d416010100400d091424882c2c98183c284845000f090001181003030154032682045403403800c0203035403100d40180e4540004004480004c100c07824000c001c0701d041403a10080019070011300801c980011305100c00003075140e4441d449410540003034480c0b14103440c1503082600305947c0e1aa0162070644201584031001c003106800055100f048038403600c44042085022440040181288810384801d26000c201c06200c80055800400309070344001c00c01d00c001801c04040c881164100e5201030141464148203001084e45a00ca59480301c104034200c0f5507850800c2400c0303001e4007076041c00340c01143c0c101041c810710705410b42029 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 550564568 1250 550563318 550563337
    0x1c02031e07053405010c021003020903061003260313050102091009030c050a0509042006120a06060503061507112706010e09010306050601090f1d0c0703080105062508 73
    0x101120200c00c0c003c0580d1181841079a000c2080305904400500307004403803078420412800c0042c20700c085540840d08110307041719001b00e00400d05505004001c800591003549460b8a20f003440e00c9480c01407400902c0c030003c4c0030800410303140c0601400b0401d09404a518075034024113a045006408030b0003910b2015140000c403038a0390b40e0000450203042c20092081200d400803c410000e40300d41d1034100c0103900d0310345100b00c02d0250910010032901c0340700c02444c1070151a1b0520007903141c5142c142088a040d0b410880030050100240070840d512440b00190a50170301aa02d4bd41d20b0305803620740d01350046503240c90740100b0b02c4100a8450320421840080040500c08403440c0f681c1da07a00119458045e03240307080d5020b00140010300c00310704507a01041e4001010705288038803645400c00700e0343c10381c40b5611a420000c41c0c1440c642c0d106050701d4003540c00c0074125040f681042c0b45960041e11040c0305009607800f0310004a80d000c0301803004960242c5040040702c410b071040443c0c1c24000015440381141c13 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 550565818 1250 550564568 550564633
    0x618020a14010f1809060311010f112e050a02040e010608070903080f0909160314040b0408030603120f03070f0824010309020901090504051c02031e0705 67
    0x50840700041c5100010300050392800051600d010060b550a882c612514011841da4403000c581064039115440145004000b00422003407000001440e44520b949050304205e25a541985501400240710b032042e80e030031011240e800241010b500115441da03484864160900041c4402945598000e10139501d052402040681c0c8a58050f5004002501c0141c001402c0718000c1000c620400003034040301c04603840c41441c0c401150005001c114090310005000d035401c05102c40d810390140f203201c0010780c0d002d0080d40549001d07116400120402807000e0003441d00000010790655007446003550542072035100b80c1e00e030030302d5030b4001c04590030849407030740032079040c11401c036542e405180110310900d6140300c0c0032510f0319a044a0501c15840c2d89405042c551900c0309540180d0300c0341c010310b028000040b40020a864203040451811100d04d04813000c00042e80c08480000307501008a50110142e042001e29040003450100b6561080c008060401e02a49061904106540100e501129400b010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 550567068 1250 550565818 550565839
    0x130b0402280305091c0e060d090309050418050309102a0309140d11010e060f0909010915030f0804030c0806060a0602010c0f0e0604080d1e1b0b04050703061802 70
    0x8404d03036902c1890a201c04080c0b0b82c510040300c410300c81e40700038a20840103400982052300014030701e82130307888002044000c1403404006008070f0619210b041400a2007120f60f8107161702d02d40794a41c5921071002c045028015000b40c43d0100dc1c0200b25100150703101000244000c1484e106450300c803218128120001460010005100a003000f8500460000148810b505c18a6070b0f40f0070300d40d84610740289044c08040900070741e060791898003500700c180b2400c1d03109544100080400c5214030381604407118207031400743c515100300d143c155070b00156a440319406140264034200b82c000c40c0640d0780000c1251b416600045443c40010a50502600050b2092030400f034032a04182e00340c8203580d41860000d12105400303a000e078411040020f8405000e00b10610b025280c0c44002e0602e911940220301041003003400c0c0c1e24400d51740078811b1415400d458000301600a203030b0121940061500042c00c0d00320700001050178010140004402160310100c00c100744003900315001d0710350034428000d92040c40401c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 550568318 1250 550567068 550567081
    0x819030c09030b07050a03140c0a03181a04030c060f021b0c150d0e1618091e03110a0308090c12122a03090f0609130b0402280305 57
    0xd486400b40c030740c00208141c05945004040b500350700314100500401d0303100d034490398800004100060003855042059541c0301683c46010b003d42e0041c00070000da008404a0103000318803d16500070200c143c0382d00380c8100382c4681c24100e5008803070980182c0814a803e0a00d05800c240394020300c044890880d08040402e00d00002c40d481e00500910950041c9022000000448589004041032040a5800140305403200c1e00240f034200d45010010820359030381e800388000c0c02d0008001c00c0410f0451002c0c06807060660700d80820340c00c4103201c400c2005200c84070604140c05510302e124950b4944040761822219818010040b050640d800080380c01071300c403101d0950030408128840d0074120401070141001e003e01610a5034130840031a20a80c0c2c2d4204040060b80d00312820301c00407080b5800454880d4000c0082142202c48044042d00c51281000300e043c444c0c81c2d2403007650f43c1a02d9a040001c154480c04042030284c8104030346d200813081b00c15070450b10007069030b03511406e65196540070002d0f5a42e54 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 550569568 1250 550568318 550568327
    0xa140c0610151d010e15030c0d06170a02041112090a11011103071b0b0a0503060a060906020a20040e1c020712080c0a2003010c0201020f04050f0a030819030c 69
    0x9180c04007080022101c800f001d5406400404410500071340241c9400e258404401c0c90b640040e00c880c0b9500d58009201824141d4600501d40500ad441e8810b00a0501c103158142c0d03a406800402409240c030b982c8004a070150f800203032400a0400e4039038030381030301c0d0148080d0340f40c3c039054008898200e45c101d43c2180c0c43d4400d2090a100060743c0340198500004c60326400c2c06502c0e445504050040c400101040341c0c0340c03480103481001d03d41d850701a220304280041044040312034010348200300e0091010001c2650000b10160308681052030b489001050a402900020b031580000b5042402c002c2c80105282c000a03002045040c414800820701e003014030100c0c0c0ba142240304952203002544007043c081040f4100612003410404221074202d00700f65140c400144003400c0101c84d030600107100ca8003070300f000c2c0680346600440c1d10003181350200311484154203000c2d9005080c02280e10344036a00c1180c4507400c6400196030004100c3d80c0702c0d101c0000c0c002104002e2610701000030b00b03050b42e6420043c007a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 550570818 1250 550569568 550569587
    0x20c040f0b01091505070f061b080f07050307170712150504060e040206070201050c030904090606030b090d1e0c06090b180d050306010c0204180311150c0a140c061015 73
    0x16644140c41c0178501d40f07500300e82d480d4640c0299040c50740c8102c2540c888050440c21000030452b80c80750407107071a10b02251400003000900d1682881004c0042020711a800107110803284060300c4043c4051b140d038a803c48a0410103034074400c00d50f15220080d80c16004060aa1044802c12602400f4041c1c642c2d401c140301905c01d55000750428420311000c2c4c015030088000e45120918401100d0034005c1050010703003a100c0c018000d4801c555501c0b01401804108140c09078000751050042515007a030190041202e400f00889490005104111401003480342042355070b80c2c1d030408024024040d482c1040c01400b074060380c1900b04804040121900c02c50081184001e89420740c41c0d075030959581e0401900d00d810303c4641240c0c0603569480e034012808030700407800001400b03503459401c0d4150b00f042d035501c3c200c00b4103000002083c485080110180c641c0c0704444117086189090b1316081d1f116144030b0300500480c0409402e034003940c800c01c090003066080c040300701d4002c22038020189518003020f03a6240718 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 550572068 1250 550570818 550570859
    0x9070807080c04090206130308030403120507080109150e0c033909010c0b0f161701030f0302012a031103010501021015090c08160206010f0e07020c040f0b0109 70
    0x4018441041c40c03034182d015040d513500144c86070f03140c14030b00310700002c000c000d640044503040c1c4044244000e00d940914556081c1320904002c001c0303030601d55000b402c540070500c2a85051501c03001c131421041020881e443c020710318400c021425040110118045400841d600240f81c940e00903001140c01180311b00c503140920485015112420b5000340d4040c950010041d581441182604903002a0380540d00a00c2001603040380f00050038000382200b02d0425514007907080188500450781c0c991a400341c41030440758401020b0554001900d8168003600380145081000c3c2900601200504281c0e1103001c60581a0340c1c081225607245040311910780070a0044500681c0030100f44130760380c1100c1c0c1c40411036011001050819991718a0785500382d50500c10000006048401409044000408403180740c0d0b03100e0019140b25070400b640d4901d40e03411440b4400b96682e4940c0482c03101802400034010083e0040e2040c400c0c1c2c0400e03c0f242c0007800301061100e0008003840000910910b14070312074840020b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 550573318 1250 550572068 550572073
    0x5061801030c060f05071203050402010807030501140f0d080c0f0601050a18020a180605070b010806040f080f070609080316031515111006081903080402100e030d05030907080708 78
    0x2403c085007228a00080c88040c020b004c410460080421f860402d0a0f05801c001d54021545142c2840010326103034000c0c1c440414507003003600501c0309122441d020041031406036080f5124030459030003c0d41c550841a00038000e00d1000418001c1ea80c00403503c00c070152020011680c07036136030b10014844020068450041c0b00000704048100ea1070468004118480451420300080c03260b00c2e0003529001819402100490b20004140013046810700c0000c2c0101121000b0b0605840c15807100c2c01500381d00600148072150000f4600d0f4042c210109a032105034004c2000c02845896103050328896006907070380036602c1ca2041e43d41e0226407113405a44010002e40208400c032500d41060500c1d0660b42565400901c0329a0100c0402410704100c400049040054080340b0360b458519080e040c860f8040a64015001070729002020079009116036400c10340c16112103504480f40ea03811280b4800800d5a26458000d48401c00314407640700380618000c9080e40c0945030038a0340c030401f0941d1303942c0c90b2003450043d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 550574568 1250 550573318 550573343
    0x60c0b010501032309070f0603020903032a1b0f040209030c060904061802070219140d020a180c18050112020706020f0d0f0f02040b120c0c01020d0506180103 69
    0x154440e4215000c0250b92079030071031210380c12024141080700211214042039104000802111f00701c106d00c0d0f00100180c0c00c086103001d01d0900800e489100c5c4d006444800d0343d950b0b8251400380ca11302a881e41514803070055031244c001c016009140140c0320344441d0700c22883c241108555192520031110800b400030001c00790880001d040c803915401c0034480b160302075071301e03000003504070004406d11451900c98240141d862000340b04100c0c1422034195400c80c0140031078001e010440b4207214a022003207003240e00400364000c1d4400500c5121585d00030503540350000d089a895030009402c2201100b140352540300584400403a0803580c01614412140015946c03690301a01c5a101d6008202c52030040070301509e403a00b40016200700340c4c002455820300a948107402e020b4070303078648541c404200614005516051820032400803900500f10030798504d01800002c11044e00140003161408a0844020b41d01c0f01540f20605000342022903250b80103140b4164510340d500c400710241410303203a200a40b43c051 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 550575818 1250 550574568 550574579
    0x6031509010f09050f1603031727030a032405090a06050a0b03010f060906140a02071e14040204081216020a2d05060a0c030212030a0510060c0b01 64
    0x15550064403001095589a05032203440e5480e000310608503000380010080b840131509020702d8a07480d0009250071342103608041c80069480300000e000658204500300d0140c80b00284400481d201e403050b084099031b101e448000346000440501038052054900300103000c1c030a0800e1203c20b000c15009001d1002071841230003075181100350103401480c2618000340c983c1d11800820311500c065041101c08000c08030042154a01202040c00179208038506400e085107000d60240082050f0140c10403101d101042202d1114805c0002600038500d201c03001c403001e450802e101500c9507003405244486104805c0c105240c3c10b29008039022590780c000144000584484000e40303540000010501c1c12007429944005a42ca165501000c0c10364014114500c05c00c1408190710052032140445100c00c041d1010400e41e9100303001c3d10340c0700c0210709084548891078a07089040502c02c0b401d03c0d14425012040c0320660741640d00481c8030701c107550890b28051f5110304045da901c1c058000300402c16514030300184034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 550577068 1250 550575818 550575853
    0xf1f05060f0405060406170702210c0312010603020a030c0203120c0906040b0c150a0b0310110c060103142404080d06030501091a060a0501230c070803130e0603 70
    0x201204620142800e043d1504000740856005070700820001b941c0c8400100c04524120384680c21580a0000700b2007520702141107000c804044502c9503a85002081140c1c007404140100c1d00340542c040c415905a603101c00014000f900481c070000c0c002485d0140c81c1c1501400002205ca20030300c5268500c1c0642c0d43c0c9003284001d41c1c02044120f0700040c0a0000190324071024003c4e00a07a1115000340001c44600b6200e41400100102004403c0b41016010b85076a100410500324100c01e1000100c2c00441c00304d0300ca4183c1c420307555824444d100d80d100000c20b01103512521003400e000c00042e03501d04080442036507070001031400d000c0f41a00c0350344c0102e000240000300405a20350340c04000f1070355580c0c2e5240c107030031155600340a84800d04540c150740c200c038900141702c5902c00803c85201402c103041000080c40403501e031619100401d054441c00d404100c0040a03150004a140d007294001525510b80544a030007114291560400028000c20310f103000d5a441c0d07108682c094000d100c1061201c0c400b48 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 550578318 1250 550577068 550577077
    0xc0f030105040c1704060204050405101d0421050c1b130c09120b090d020f030d020903010905030307050c01050609070e0126130314030708010623030106080f1f0506 72
    0x180044001c4e451022050081c01601c91030150b140143c1b140c1c80d1400340301c291100104110101c1016000078000c460b1148a40e80c100e00000c00c01d13401598452601441628070b400c0c8a024582106100d100444e501000400c0074170229816100104404480304400352040500c8580c40550042442903040095004661000d868600940d4030ba69400c24000d00d460943d5050f1075035a045802c012540c0400c00584144041610040c0b485605100c42c10352a4043e5814600f04140c001500d07008640d025084048081e40000569980e0300340110b0150055000710380c082e429508040010714940760050203207100d694180c44803100e404140004492402462038041e95102d440f1001090280303592010320720070405041c940180b41c3c01424098506921741007a20b91040307080080084656009002c03034119819801e00c95880c0801c00428402c80c0707141d060034030a400000c000014020381c0315129900030b0904842c42e61040d159141c6142c545400007034240c1000c54505000c1055042080051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 550579568 1250 550578318 550578341
    0xb030c04090212090f06060a1211040e0114090c0109180f11040f0503121219110d1407083702090411190f0c061b080c0f03010504 57
    0xa46056250061141260071869102204425640c01c01443c0c010411840d0b105101140c000d20003840c2490008030b0980c0d1f0303400717a00041d811105500b800c00001d03e14814034014010800e0081c020340c8a00310b80280304a0140d894030030125004a210250007082c00c00101d0810784d11800f10b142880d1515210300100260350502e10382e101308505806c2d00a200f54052804086c82d2503a031a4500480c0340c10f41c44080c0c005031700c41e4101c955001941d141c0c1c0c204450001c406150781c254295500b0080018031200c104002e0580d0381070100418a8414420080c2500b8100c40f07010070a0485642d0782c8075042004613002404a56840c02240c00d08004401071503803c485440800b40f03010125012101c841020000646d21076008640d100152810740103c3e030300012560805400c12540c90140720b02650362004174001d2006070f5419102d114401c0ba00a59110f40002c4180240d8034070040d985918400003a84000041c20340d8007189000c0c0010003243c0d00c0540f0760644500b0743e42000c04120040c0b10801c40c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 550580818 1250 550579568 550579591
    0xd05070f020909060f0a060e06240d060302090c0a0c032f150c03040206040b0903031b0d021e070302010e0a0806180708070b030109090204420e010b03 66
    0x2400042c0d4580382450720407820540604043c0c01c1c5140010f5031000c02424081c120307800c0c10801c0c0064140d04c03003138544c0300200315207102ca6001d9000c02d540d0120003500300d20010810010f4540d100c090640c01140450344265441103041e5160310511400703000d81d0a0400028081040c1c03000404d2007159465040c5928a142d0282940c140c403107000f44030800c8440030201d800900b1180c18814040d0341d8640e0124070041c1c007510b10316040e07000412034856401240f12400300071480361110344040080e02c1140285860090000c20704502c1d959464070070b403041750018800e10344d0031103081803076401c2540c490506000612855045a00655007282441d0300c141d003001002c0000162034004007c0940100d101d900d440c5001001d00170709600b8100150001203955000c1101000007220a4044030b0440c0c022001c0003400340f81520000d4090700340d001c0106c8032240902c0841011841d2102c800d50300d80c1000b0b0360324100301080d00e1034003000f560790b2191003664250240100444d0304014020766209080030303071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 550582068 1250 550580818 550580843
    0x120d0b04060f0626010302091305070909032012031815040c03140c010512060f030d08061e060403022b060c0f0809070b0a090902040e0403030b0d050d0507 68
    0x62440001100c1e032211001030a1512400e00c0004e03461241840c1690029400610703606540104560f81009059000c52100c00b442141c24000144221000380032411004e000c461890f05001b060018002100078110a83e08000308501070300107659000c1842901c0e180f07007155943c503603045050b4081420441c0e0341c090300c20b548000c80483c3c19040d100f5440303a41c04160349400d5041c00140200039038000c0b442c1c5d40c0401e80c90b92041c0e81140c00d5030042c0e00314120051150341c403c00450f030000c1610806d19051721030018040c942c95044018584035007000e542d64009240c00700100d00b440741402d08401d0308480100701c14009820a501401c000e68642d0041c141c80d858145245135400302c0c4841e095540e5680d545074070f1001030f800b0440e9203014803245010016401e2900300c007130315101d040c4120140c1010008002c00541c0c090200703a8000c121844045445030795602035400d20900c121800c5000034a400030002d9a4a481d10301c031030340144c20078000d0054500010080e12250301c120801d07500f0864414 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 550583318 1250 550582068 550582079
    0xa0506010e211e01380103090f030918090c12032a150b01020c220905070f090207030807080a060b0a050c0d0e010e0f040e062502120d0b0406 62
    0x3c0d020442d003210111980c2c8510040745030071280032649000104c00c058034070060b28510846512440110f0341007203045090f00344016001404110b500070b010400602549013499003006503603040303070481d0700700d10500009101c0d0803040f290651402801440d10f010244003840856202015840c440d007015005952140d14240307408007004810004560044120070412014206090700b0458002d814040d44820b24000f035190031200200c1401400d03100a0f00741c61101d02c02e10021310610b070701004c1100c01d4080c2007181c0c5600040c06009207402115900147d010158400c5a424540543d1540059110188111809107002c0c010080064940d1000b15003860564014080d1104a07210b9603507542e4583e03480d07070400070101e10080510288165000b1180d0308245000700c1a07908455821070704140000241c01020564100300702c0c1e00c984c000b00140804007003403816450704034401964030500080000c0b0b0341d03004264410030244c0000c1c0100540703003115401c0f070018104014004142c0c5510f41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 550584568 1250 550583318 550583323
    0x5040303080c161407050a14120c0405100e160507150905160303180b040b0c030d0e011e02180105070f0204050c0d0f090f1b1502030301030201080a0506010e21 70
    0x800b0240c0720040584003c00c91302c4420041040104820b4038503400c40752408223400d00080c2c40103690b5002c2c881414201001c00c5040c4107080e454003000700104000e0a0200e080324410070306003d00c3c00f003550300001007002c00f940f103100c4403407440c4199522480d08100703982d8000107600b2003141e400255103807204500002ca003840034540003019060180c840500d18240100b0781c1201203100c5c02d600d01448820300c1466903580c11a01a5040e94241d1951481c003544014038521500c800313244051301d040d1911484410641010860300c1c404140140801c15050240080741306102f407601e411808030300000113650152002e00103050149143d29030030f00d0540c010038241c0d88210f401103c50070700010040341607001445613100e503803080442000314501d156250407500d011070f80701070304482070010301c00003000702e03903011101030082448904100035540602035681c2e00300303000881c003182d0360742c001a680300368900c2807602c82c0c0e40507583c1560340c1068000340800000c242e4241440da40b000700310151855001c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 550585818 1250 550584568 550584607
    0xa0e030a0c080d090909050d2f0a17030c1207051b0106091d0a2d0503041503020306030a1b0b1314040b241215040f0c05040303080c 58
    0x2054050074058583c030400410010640e040310390002c0c90b00d040358011a0000414444052035800c00600303040c620750b4400c4c122204045400b0500303a4000c442d9881180200391400000d100c0c55580c0c010a014840e0200c075404200c5440c002503006224803440684c01401e401d41020590030050b20746030ba45c96880350b112070134000c10011a9103592081011034207511410207846000810581e2420a80d007030b2a44620500c1c070041d040c2607000c0c0d00d07490349049207010003210f120410144010b400941c0f91480d00d0390828800c2030303104040f4003101c10f0307818001c0c02268880c580080107008800316030303541d0615030258400d104d224140c600d40049421072150004050020501e4104404580340030394090f04c5035034040d0624065402e2840540d95516a0b40803628101c0070710040080d80140d101d80c14485004003000e842810100c041480341e100303d804114a0b504905540600034140c3c50000c12050315514250180015401c110800101c0c1c441c0c0c0c503441c0c00000c614000c44c6000e101020200714a1403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 550587068 1250 550585818 550585829
    0xb0a0209031b0a06050f1902060901060e010b0417010e10150b0f030f0a1103070512090a2004090605150a1d0610030f1a03120f0a0e030a0c 61
    0xa00040c003400c24075080001c1c82c10790b00c519800566000950001c00c10400c0d09115020074001d0109082085134105010b441034001040b00c50014a075140e007000b542d484054488031055440e11f040440c50310303019558141a01d9a41042529251500004201303400080364040c4e459540e450000228950500c078404200d000c24001290290b002103800415108a0b805481100c10400007586250300c050140c0342c1c000107400000d4115961074003048081d02c0d440f880744d9000b203800010064001d40017006851903401d0300c0d601c0c038000c1e03485e4034140340e0b1901e100ba0081d08090900300301c1c0324400c0c503c11040b00051b05c01b5101181030002c0c3d80e65102681d1007507658900303400d0014071002803070521840c0f0b500241038284444c03500c900720450114030b40101030482400703500c580401c1c901c00d501a0b000807246e0140d06c00e0410034840e1300c00100c1249a4441282c1c2e10a015031040607034031600c6003042c0c81c0340084106407580b0f000b82d020f000ba2034200004d11071079010b000d9045007001240588101200906 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 550588318 1250 550587068 550587071
    0x103060f0b0402090d0f030207090e0d031803171506070c083a111605030123010e1e010e07081e040213150803251a070c0b0a 55
    0x1806214120305503104541510302a0f031050109000695413401c0303e022542d0400c000080c09a03107418102d00300603140d0006510941008030b50862030b40d00040f0307052030549582d001c0000300702d4000d20545030562841c001c1c000448502d01e00010150300c80c20240c0013400b04c0e0303a8284080000002c1481900036400590307038101c400004102e03041c800e000c8203038882040550810031148007684c0310b848845820141c0329104c3c600302400e10050056a010f01d0021860044600d00e074284003c454405c19540101c1c0d02950902141604e4204180d900845550030203440c42100d82c280b100c8400304c0c001c000c02940c400040403ea00b503e0a40090101c3e020b07000e0060480c989107030001001d008002e01802d41200705801c0c2c003e15240c60440e1800036042a4101c4130081c1120150007684041c0c0071540010f1040364220b20300080703000d00080241031480c40d01d0100140602c200420407005407807020060400c034503481c0080d05031083d00e031141d45d000d00c05082001c1248a0340c0c803405030f418400c03203520004a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 550589568 1250 550588318 550588331
    0x20c0703110a0905040503072603090606180910020d02040302060a02070f0e04020d020f010915050408102d0908040b09181605090f0622080c0a0b0d020909010306 71
    0xc0c20902d082e0710140c070344100300340914202a41e40300d54a1007140005041c6009c540e940441002c41040c02030100c49210305072545a00740f40c00216200c03c4103640e0144202045640c80a8524000544500c154841e00160001107400380c01e00b400f80d8068504162259030800001c40141d40724000381a061040d90300400340c403400c0104d82c0540112035003018406542c00010000107a48030001c4092440e070668820116204c01001654054540d8200f00a841014200e02105950110140c02110345aa02700c1d103d200d081c144160484100503001605030100541000b40b00b140105004d0050104500008079084076031113582e600d4000e40c0001c00e511130000340013111803070488041c14286100420301c040c2804c003072410440a03003006c4221010700402013140c02140d9181c008405a03920047c003295614006440b4050103140c2c06020403112469604020418071400240124001805000141620309028001c030003500402c808601c0541c0801007840e050300c81c4c9510038021486900b000c20003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 550590818 1250 550589568 550589603
    0xc030c0206010807180c0320031504140112020a09020406030902130c020718020423040501060f09050613090e01090209070f120b0f060703111908030703050901020c0703 74
    0x2801e0040e4080c10003503004040611001c1891085402084e680820028240c4e4050806402920f0007507607504000d0040602d0110b886010001541700c1c0308000591a690301c17005041008440c07a1407142d01c00c0742107950040c451813401c10785178016a40024071011034582e8030503441041c1d90054015000282d1164200c10460414618128683c48410fa00b0b00c180500c012000396148030900ca00340e8224552146114801c50950440b0040c024118480da0168651400800061440310b41180035038684800020001d204144606100a160359140442c901d4102001010340084405002c41c0311500d07030001e658165442400742000e40c1d0760010800c0c00703060041044001c4010108be0520440f01c247c900d07581d504c0030328020864286000041c00039031000201d0b046c5490144400c1e00002d000400ea0300b81078010300e030000031045280850f0f01001402c902142c4400402500604544090010800843c041e4101d00da101103008001401c0c1000c8510841c0703400510380c400c1d10110481c105000c40d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 550592068 1250 550590818 550590823
    0x90f1d0109110603040b1b040f0905190c120b130509100c05190c0503071a0f09010b06030f130213020406030b030708070608040f0f06020a0807030509190203100c030c02 74
    0xc060310b00300d40481c1585404c0c0c0703600140c51802400e260700a82079200c1c0c8811020070303c0a80700940030080903110f009032100740e0b040007003105030780748401e1300646c81c03400328030448600a40d61210400d64a600d403403103040c1d41c0035000c1c044506540b81e0040b8100700800c10600c0318401c1350300c580b4008000700003032007503550f81e01d0880d58518060030402c402080794105d07110200207220310841591900384000c0e55242030107415801403050003050001320180782c0b04c4d09280c0c04480fa014528400300d0804584172296000e00300d42a171480c2541204085c400201c030030b051007100c2c030380c40380b81e80d80061544400ea60020300c20b051107403c04000551701190a001c201e60501c0b0341024040181c00901006040030f485960320321481c4a10010020f081001804100700030305050102580100d03080750520303607464450069002081c03124002400200040c4005100380542409124075001405001c08500c05007031400706e204505907050310403144910780750580780c0b080c50001d4070f8590300026a011600c100a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 550593318 1250 550592068 550592093
    0x2030a0f060e0d02071203031103070513080c030a03050706020c0105390d0c02031e041a0a2a02060d090b0106140a08062b0201120e07090f1d0109 64
    0x2440d6070310094500f98126000900704090754201c1e84851001c142c585001ca01501c281d41a200b000007011003801002034001029210002d069100c40075056211460661748541c11350040d90306030300c000c1007800031034041c40080011303500681d005841c0c8010110318900399030342606c1511111940d00c41e612039108140a0b20201c0050030b401282c128003084800f481180a0002090382e400d9540c030a0000c07090081045605242e10703621440c40c0ca0240100d140800d400500c0f03180300a40d040c440c40001509408200c4280000584694549002c0e45038400100a520380c2401245c80b00c4000d40380c0540d44500282201c210070300800f00d00302c401e52409206416060703008006000706490243c1031850400d05580ca040001e280444066842800081514403d001e08c1c010055803a030740d10b03802d602441081103101e4001c0c0c8034242000491210721080f90246100006184c000250602c1034a140e41c00110400c085440c0120b0300c99050340404014609140008420369034608802007001410280b09 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 550594568 1250 550593318 550593341
    0x150e0f07080a2d0605150306040510050303030a150801060e0105031e0303071101140c071106031308031308030916060507020a060c050f01051608010f050109031e02030a0f06 76
    0x50100c8080c10000d000300b20145821040c400c0f520000407040c80b040780c0e00250080c031000f4403480d41546240c0305039000750300907200c80c1d007d1130400000408001a42c40881308079030000d0000e51950f511010404020050300f10080301d0007118081c00180c03640240a02800b500c80700c4000c80084d4503100802d868484404030005014152580c2415916800300581741e000c10701d8100304024981251011313004000b00e1060103004492241806200440d61001c2c0001e54441c0c042900c504c00c90b841002194001140ca000452102000a400107034070743c0042c5070082002d12035000300190903907500c0703115041222807107403660004403c0348880c0b02e01d074000002042c00b030401c54030346480c0e0f801040d40795000d1b0207500c2c02d0041c003004090822100b0000c25542c510544020403180c02c01580c80a000c074000c0e81c3d09030000740c00c0c500103e0b050504c04603880403900140c6034809030341e11f199104d078402c440c03200c030042c1c1d000c410000d50000343e1803c0c04400e4680344103062084004145242c070000301c1d481060917 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 550595818 1250 550594568 550594571
    0x120e0c03030301030f0f02092809020a0501030f0e01050c070201121a04050601050d0c0905040b03030913270629090406050c251a040302060109150e0f07080a 69
    0x605425460120489040d241c002c001082c0e422181c1c1040090b92000c000c00a40258401042119800c191542d040900a4419040180f060380d07001100c10380e1041c841c0654040103c03041040198000d030f0021589002007140881c8280d0307048070703413402c40c1c4040712094452000098010f0031907038003040b440b10b900b104102c20044403840701c20f810300c06005580032a001d0781d0b8540114036986e0185090b15409004003600f4800710245200090000e0039512070076006d94101207280215107400700035211026000f401114094004400c0c1d80040d109401c0a84456601041041409401c00404e41d21070760280c10027185160600c000011400003200d46ca4600d030040c0e804114980d50303000300301c2d50840d4100d00081811344500d041750591784194940b0100508000709000503032171240c400c6180300b80c056400140c044803050315009001c20100c83c0200140c100c203005104504c1c1c240d121a1044290200500c0da2540360b5000c001c140000f5605070380c0c01a80401001002580f007640c06030b0000ba404030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 550597068 1250 550595818 550595833
    0xf020303090703020409080d18060e010e03030c16080f030f070f050702010810121b090b031c140c100b060a0e010c170304120e030c0d0807170307120e 66
    0x420350700c500203400028070691b260403604d814801c01d001690484c0c0083e00b420000c0840c95100ba002c0b6900a40342154442d003040010b21500c58103104143c0b044207203c1c069807860307650346060078042c1d2029409801105102e00391300003040d5108003502070f8598900301160740f410700c00f0040f0990718006100c00e003040440c03030b40c200060390b1290a86401b240c0c28209402d160315a908203130a14001504414880c1d400142c031141480514103079038841003613030881c10309403580b5080f041040d00d440410450b05079005040030003ca8640559210311080305117410f91302d03080848144030b0294000c0b6401c00480c1e03c103444440c4040d00710322881910207030454440e0300d031510f080c0b4060071814403004400e0500056100c0003051201d02c00005030443d030a081101d03601d181030314000d41d22241601910000690f03050340c09501e030400080340c0301c0b83c00000b4821030001c2059036908126a100c0002111080d01d070010000511030341380c026600841c0385803a006c3c66080c040c00c84908803690207440c18041d07801401d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 550598318 1250 550597068 550597081
    0x3020307210507020907090512010c030b0a06051606060302090f06030c011701090b120d21060f0504180b010305071a070b0105090702120a080a060b09152a0d0f020303 73
    0xd0854034141d6065440300d51558a1500990710001664023450708940d11628841010314190f2007040c40c6491a101042081c0080b01401441c030f0f141d008134408100c0811980d030000a220301001300c0144110804140300743c490780454020801540c406010801c118280300071071405002c0f600625000b86030000030401c94089030000a50b040c442c940c046540c40d4103d100d19103d0010300c1c15004920801c071100c000042c07034010f1900003c40b00030031403680c80c91609005040742e80103c2d0100d400000801c65624140300412005210103026800020030131003020740059504040b441c002d501410181503610b00e85809881118854a88240c4003042044048000f0300000d03071441c19508103542c078040a607580c5d4401d80c03420102d000c541c602200041200002654007241152007070515120038407009075100c0aa6100b4029011000d602030f074080c80c051444403018005c0d02800c1903441ea038801024940d0b0101c4081041715060f98929044140f44600b01c40e0881d5441e89840d01a100451941c0b4204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 550599568 1250 550598318 550598327
    0x70506071107120c0905060a1a090409020d0b090606030316060509070305060c09041b170601230d0b0901060206010b0901140313050c060f0901030203100306090302030721 75
    0x10010814441056207104411a04200d650040c190b035948200241005080058111400e0310400c1c80c2c150805002520500700f040503482104c001005d541c132100912151205940c1000c1241600f0503076524a20002d80d89060408101c6400b454001109003081c86000d82041002006640641d200b0402c010000d800001103140441e040791000070141c4500d12118200350844c4e001400d680305070380c14000f02030800c07030041c10070032401c403001c00008850070b0a40300c03102258810100400e8019500da0004075001085c00c0d4844414540242981e04150000005081d10007262541e0040400d45002c1014180314002510f403084442c11450340c905003000755220414010640c41780004101e07004144d004242c002509008004a25228036200c0c0321102d488401d48829220380c0f20313002007144141410001c1326035170001c40410030718020291005401960000c4c0188070040030f81807000022490314031807560030500c00d0b030140d40d407003003182001000440d500740e11f0361405c0f170240548640603811 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 550600818 1250 550599568 550599571
    0x90a271a060c010605180702070e0f04080a03060504020c030903010605040207022b020303030106080906060d1e0c0306090803040308102102040e01060e1e01080601090e07080a030302041802070506 86
    0xc45010b941e403800302d4156405000785030300480d0000c2240d42c00720742008a407541c4910540065007145d50f415a641c901c5194a130040d110b00c0c4c00d50303a9000100303000c580c03441d00516401d0381600b00030821030382c0d400125040360700016003154550000310745c03090186028001c8500030901102c0950030640c0350780010351000c8032103010300c40446192501040b04031131100c00d00e21090300141507a84a60b902e610103001004200d84040c1c00307014240000701070f45042074519a0f43e6400004a089224088060345d81c8003d180300d0950b0800c00c0315100000260490045607040342c4100314494580c01d0616000d404084094206040300020a10a0000d1051580705503d101012025032024400900100f801403e524a01c40c80c25404c2001c01708840d116600c20074044d60403407034920300e90010207880104400d4280106442a0000001004011816001807448044400660b01c0300c0303039941c500c3d51504840b84000c0b0046900460100002d41341c5040c000040b400380d5805516040c460ba0b60b0319140d500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 550602068 1250 550600818 550600871
    0x51f020405130519090f030306060206070f031815060e0705120a0213030b0703060501020d02030403021e041b0f0e0103111b0f15150a03021008070203090a27 69
    0x151400041c1c8280304010480c61022140041040720303c40c1c6007440c1032000001ba40c15130100c1d0425800051040c0f001984900c14541b694408941d480c0c3c3c000d0445c09850007448840c10f1100c40d860803004103901c00054214a18100390026840303142a403085050740006144109000003403009201c0e124070140303400c1e48000c42140041e543d005da0f00905021400981015104151540030848915019072141050b40d07800d800300e910780c00080000701d99030b104d14000203420480d01240e10240404003d105007101c2d800030804100a144640103c910b0000d0b0010000000d4481c440c400e055038000e140102248800e20b01442071203c20203180b08988038a03160f00c0e4001d50920801503948009108a41c02d030907404d002e031200c03c22101401c00ca0b20a050341c80310030f01501a00f09044500c0c1c00301c6aa0f045960142644c505101c07801000d54441800505207415400100030410746a03a9031042c0740c01a0142d0301c44060384019600c40f240c14454a8041107030355628180395410100043c0907880f141c0348 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 550603318 1250 550602068 550602071
    0xd0e0604081e0d0c02030c01050606041406090301110a0c0c09060f0b090a0503190b090c090403110c0306010f03061a220e0a0b04140d0e0d1a04051f02040513 69
    0x80d0780c01060b841c0d911800d04050350750761401e40a4a655903010000f00043e4042ca4000d20880c0c903010100030180c400d510442d400385a4406007407409041003c082c01200000034000100003680a010821036403000700000001842051039904001c1d98042c4000500100441003015508101c592400c00c440d6000b004507240020480b51a6562054075600190a02030b0517107a042d4400120003000d10b40100080751381341000000603201140c0044d40d800310910080400d10b16448607101a60a40e42c24900e1450078019000b00e0404c3da102000198001e0100b591180141c07455820900c080b40e041302050000d036004032110798066510b003545050305008031031204d4002c07040100701800030000c180390f440040c003916840c00705010816824900c214012580d0040300c002c080142c0351500c1141041c4400b06040d0b5128040c1410081e00f2080310742d1058405010603220030f102c0c15000c92049804a030380f81c1c80600a0000e4031085498802c080e00561025818682007030001902102000d01c0c1c2481c0301d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 550604568 1250 550603318 550603357
    0x2040617070b190804080d0f020306030d02010e1b0a0b0703080f0f090714010c0b0a051005010c080a031d1b01030605100e0d031b0507140105042601110c030d0e060408 73
    0x86c001c0125800e100c1e01e0181000341d108034103840806500203d456a02c24014a8079211200740103006001354413466001500d81c03016084d20b01c103440d007280942c031600254003080109100421100408000d4001d031030f41440f514061281490712038004100503840050038060001c0301000086d000c050301c20440195842c6901400102d810b800c41d004e014199007100002e2012220382c0c3d900040c040c040e030040da1031a10b03446400668015541150040c6040c0080184150203403090344120540000329000080100200184d94075200d458801110324240c0b202e021a0300c1d40c1c152180800038281500e41000c0081c6020026184200381300e040c90061998407180401c052091850032502c10000e0600716010b021404d00c296994180d0080c1105a01c07143c60354049580180c050310b0032200d5600c500c1ca1409882001b800c2d00b203100c01b0301c10304150740700e16114002561420203440501c50000045407903900e900c400b40190b5410305510011a003002043c0004141044129141303203d8010110061 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 550605818 1250 550604568 550604573
    0x60b032803120e01090c0302031009031704170715150807170a0222230406020c0a08040605091c08070201270b07030e0f012a02040617070b190804 64
    0x5003211400c11a43ca500e050250002c111040c41d00701c0903280294100c440d4120040c0c0e003d000c0301c00395038000d004074010072402a09080300c0c41100794060f100340314110310104d991600300d0700c941103510700702c503000194500d20016503420311131406c1141345080c00e120818501a4680e4540c101c600a05040f00c0ca000000003402c0f10030030501d60328907400760000425980650b00c104040c4003030300c80d004281c1c0c10540c0c1c4d509a000c1d406c00318140a00030780d01a441e01e4545941d14402940041c50400da5802050700301d4020844010140c0001c00c443d4550b20794800c00c4e0130070001d4951610340380b140b110303170b03030110450100f016402503a00721542801c2c05036603502c0c8840850340d0b041d10400450440091018081101d00d25075001d0325496101c1d8a074112004c087c041001258140c1c40a1503000a00b2100814860070000400d1602038100e1200c00c644080150041425a065508107400d072020015010b44160410015600200300003081c007403c000440252a840b5010802e2071020000160082001d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 550607068 1250 550605818 550605821
    0x501030c0c050304170d05030702060f041a07020708070b03370204090b01030f0e0d050d110403050d0f02060c031f051807020d020304031a070504080703060b03280312 73
    0x10002c2c0c0000c200ca84131681c036010b0300c00400e00090458a01d0144070720411609000e1025a400f640150300946016511440f5168540c42c005001341c03400c0700710f50401c0d80c281c45440b80c220700640103640505401e41c10302d1255407070505640c1c0007116001d810001c010600e0704080d584c140480c5e40106d5030384481905030286003103130ba2102c4004601d501c001070000390b03500d0035800840da9a00c2a00e0070300150107901074500440701c42200a03242500000b104003405c0744240002d081801c03281c3c100060030320303403541a55542d400540046a041e800342d40500b0322a5040880308417007030401e2008005500e81850743d440d0500010b0030400703c8841c0c400d40700c9071140710344c0304d803101a26000d050764441c08160400003030300c10402d5500401601506080e05003443c8003000b140c050320381201560558144403224000c441c1d00007441d1900b0082e05010202d0542c50502c078040040d80100c40218828151804140c10125080310f500000001c0014000b0f000b414400707111001078150901d00b40d00400c00aa800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 550608318 1250 550607068 550607087
    0x207091d030309070e0c0708070b09010f06030503040905012907030219080702181e060f060a11011118060d111303140109020d2004110301060f0207050a0501030c 71
    0xc0d000200400a04034030003c0c070481140c184180d11030032030f01c84050a01141c4260340b8040e000d2001041188041501602d0464000869000004c2c00c42c000e170003988120350281d00119078a800014040080000900070907000d001c0c41c0c201c400741da09a40c1e100c0d15002d4541d04400c554054041040030506000340450030a41200c2c2140500401c29032800b0842d503846128224422200c50f20f42000c6444590708088c07250f00404103007800c3d140d0480f00d0a01e0120300a02c05544610306007601030f8940c0f01c81c0040d224181044d22070164003104101d04c1401d48080030400403100070b00f0f100030321202580c1c41d0010042402580c03503036031760702d00701d41c2e00c2c0050b20050440102a4400040341144100c0e100d0780720f021a1700030b102c00320510450f00c4a050a03200c1c8090040c4d030281c0341031103003004200711601c41006c030171112414003900340408021034240c81d0040000042290044010814141c01880c0c808000100d8400781c40207a003018001031002100340203d504059803018000c58040c086c0c02e085 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 550609568 1250 550608318 550608371
    0x5180406140709090c0206160c080904020c030703080a0908030105010302030408090a08030a0e0d0b0402090603071e050f0f0907030b060d18110d0b1909060e15010f06020709 76
    0x7401c07a441d000c0c0000d00740401900c079002600f0718007008250614804036410340030301000b184003034070450032140c1104d940341d09010507240c0031400c1000c10302c560b03120720080c544c092a200207991551801c5c1809000e0301e500410098407a0706020b101d03400103903001c0890303064034001d00300182c490706c507418814102d0023207041d0b8070f401080758003020400c0c0c603001001d07202038101e590f0360001e245034120030f0141111203101d00a003140e00040100c0e00600e0400301c01030340300c07038003404442401c0e40c0d9000401c40702c01074854007510a0300c400d00078004c50806042c0300003002402d90700748091582040c082400c115004145908042c0d03140d01c06c0001395500411692100c08402c001e106054841d074190045c0c0510300f00480e5020304c0d8004810503410612000c0d441c80e601301c404c90400b95940c01003400010000710001d18007a5a0342c0e500da000541c01d00c10f100525803148001c0820003e908071f4015071803010781140c140b60b440c401007044001d0380056510140c402a600c00703d1340c05019214901498001c40d1403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 550610818 1250 550609568 550609601
    0x1c080603060702151527010f05060f0706140a090c06050c03030a0902040e0a050102040e0a0603020d080a020a0b090c030d02030c0304091a10020d030f0c14070f06022d0405180406 78
    0x8105106ca4048000d170385180c1c2500840c03910f9a030344807034080c0c090b11171203120b400c010709205000e8500001d801622617140256408180c84803800c00c81c04401500301c503079220856440c03490b003050040c1c007055240034141d10b080c1149007100741c1c4c032910350b24040203144507201070301c2d12110b00031500d481d08145182400081203174144459443c0c0b0f039020790000e015009003000d1a10008010410034007540c000c49401034403c003085240d6864042e03013036114080100a521408003604001910704240700d02c5440005c000d418100c22a500b0035043c0b08055401d94110352041c0124120700b0b10100840302240d041600c0040d14980c003400400440320319410142e0301015802d141c0050301d030080352011032030720300c1e81d404c00200500c40040c030b003203071005039409002601c20406880c216000c3d40c01441d41034011002400c02006c1e41ea18482a0307405001c0d8494046032000c0035001421000da5110508640355805c42e00703050038040800c16411940e000813210140d0030b400324052180e1a8400e280c3c1d89590401d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 550612068 1250 550610818 550610839
    0x5130501020301120b100b030f10050a090609200409021602060c010e0601062d0c0f050c040605010c0206030a05060114180a0806040b07030c09081c0806030607021515 73
    0x20280c0b10011390702e000f0369007501010f00040c0c286000244c98400c0d136150707401c800c1c11030b04d0740302c07070b41c030401500815074002c0c00070440300801d990380c0382003124004118800c40071420b1401c0c43c1030300c0295074003a814110600d0a01c00f01c4807083d450882507a09079114640300580b103d00c6400c10380351403007101d507002c0c1d0440f40015143c1b40852040d04101e610441e9081261640d1342d81d220110340c944611100108550a0324004101c08148200c032588a10b96524220081d0401c0c4d44651408407141f0b042100c01d9800041901c2680c14107000d107074010035003400d0a21003644a034010506034400104140d000c555128000340841c2c0c01420704510160a27a100c6944800300341080300100010140c68610600c0d04040004440d180059110710841c1d11006441d02e43d101c5801c01c2d005408400c42401c1403040d41000810b030a00e0070400e001003012807441d90240003a80d600d0203080854041c00550003a04488100071101e40c0000c0d010076407169021040000f5903407201c81007900c00c1140755540e0b120345881c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 550613318 1250 550612068 550612079
    0x901090f0501050604140103020310080f06010602060105010c0f0210170f0103150902211207050313050402210421030f1a03150901241401020c0f0405130501020301 72
    0x14425048100c600380200700c40c0c2d0702c40d020000680114401c0c82d4188000e0030a003500f0b5442034000d1500701c2c0801820540c0c0c2c984800314117080100928002c0135990201d4010460541c1c100310050040500303003090760079003501b92100000403a10725070207030044a200c4007000e1524454030030a668254800c246019900302401c85285040d800c1c802a07403480395840b880002442c0034440c99848503802454a20740344041e210481c512240842858584d02501320086035204a40000b050034600c114003441e601c100001a9618011081c1c00642c09548148005001000080002c03000a64100c1c410344140d601ea00c0c154040e076100000c4400410401060046003a4150f044000207460208080c880c0b4580a1085160b000c3d070201d5096041e0f00148503008075a40540c10180c101030300e48000300d2500b1120142c10031901114000e4200660b00007010455100d0350824098001c4003440a0300c0e4a4460600090b07025a10031009841030340e580300414801e0b2008410350500c240d201c80255100d603900d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 550614568 1250 550613318 550613321
    0xa0b0f160309061706010c1113020310051507034503110f06030601031128080f010e0f060402090a08011d1c2f0a21020607031a090109 59
    0x20300c10701c030115244c904081c581c000136000b03140c807440d4107a45441100d81c894480c880c41000f6a035040d074104807020f01e4050b40b88103900045d4800c1300d070046103005240c0b600b82803010345990a200c8185d04281484403070002a40081d13020011000e00e0100b4000070b40540744034540d50b44d10b030342c001c200e01440391079540d9050200c0d00f440e0459019000503016600c100e424000200581542d0680c0300f04100001502980a94009000684140078041c100a9440842a00740941403088071840c1210f00103020910750191049500402001075880554500f03020301507884806081640d401180360005001c6480e070754140c43e980100148640415940d6030301c05070080810402c0e4941c214210414403002c02d0000815440e0441000e042c1580103026801c2100d203045c0c13000c0c04550260b441031078503001c0d4051241030000f48030300c40b014021003242440c000554001a000069100d1144a00102400c0d00442c2c056031240e06424007140b106800e0aa200d000c01e07030000203590040c20303040041000d00c1c69 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 550615818 1250 550614568 550614587
    0x51b1c050a12051801050307020709020f04030c1d010303030c111b030601060c021c080702030a03050901020118030c0f0606080318030d0201050c0409090f080d05091b0a0b0f1603 78
    0x1500005042030200c2c20304079a01c0c442e0315111010350b5408034902c0b0055200301d004581c0300d0a944181da040c01e85489212040c0e034071a0480300c6080c40c02080c10705c1440fa5001c00320f0300030800f0005200d0f041c00114a0a010807005110150615a0340c0c02c840780d0720390040c1610b001446845045d5845003090903400120100200c0480f17009104100c00841c64a0090b4494946240c0007845000d201a503142b000000082221080fa1140300501001005840c1007080c240100c1c03080d150251200c0007440028212892000d00d0042a12669168000b181d049040380c0c1245400801c051480c1a46052003030240c80c46034840c2e60380b07103c0000d501140e056a0b141002e6141001c070140e800c04410000102c0c2680c1050b80e401500d030b0420041048100c41651000c0c42c0710b4420301d048800d1040c5a180c11546403c0220001015511603040020014041c817009214a801004042c40600241c0220301c841003607002e021100d110004082008803600390903501000d1900005a19114032031500409188a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 550617068 1250 550615818 550615823
    0x50c04030821070503060d081810050703030f1b0c0201020c090a0c08010b030403092319180501032a08010e1507050307020a020d1a07030501080c0d051b1c050a 70
    0x240002160f01c0314400c1003201e00450703004207500104c0c541c4d074035025a20761000c04421085d44900c07240780f80d2921841c000a550050a0301c5450700c0e400581401b900384c80607844441c401500d0103240140ca10b070a845101360488542ca4042a041003901c010b0b4036244030281e9036540040d10604201c404031503904454407803542c50340d80721035999a9603030902050100360b50041c0468125401405140e0341080041340c1d150004003c1041e0407420301c042410044011040540080c905000b8004140030149800c0c4040190400f08030075171458895002002084500c103400d00700041214403d040841c02d210060140d810080001c4c2d881c00c02c0c0256900720b00314158110034a00000152054001c1c4183c9200e00641d8001e4880c944281d070030051080c401ca041110424410024001402c50043c030079407165216440002c3c0c02e5041008141c50040e14068551180c1100e40302000010b401050400b007401141d690140440d045900107416102d00e400d10360050075101e80480240480060030100e0a0f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 550618318 1250 550617068 550617127
    0x1a070509090109150b13060309050a06091a070203070308070e18090c0f01020d08010b07020409050f07061101020a0e0d061d10060518060d03020c031b0f091009050c040308 75
    0x99444000c0c1c803050246d803503500b040c0d2900c400c0400905000b40c012030040c40c8210191616400250340300001c50389010030955560084058058401e0440607029070041014001941801595503004165010013840c50701045551030001c1d030303581c4402d01c4028403821100342c200e066180131a8520b0391050f509030b080d48184000c0c6040031165001080a6150001c55a40c40e88103030300385004501755500808040382c00c1952840c1d07d8000c80d00500c540456045407a02814220b840d28070012b04a003070039101150300c1d910411a040c101604180c0321078071030324250b8034104003440c0380c10944000d148401607016000e40d05800c410141c0300c08150703000c0358091800c003040700640307031824000c0f83c0c14041010703002c0d1614080032903500d01e000408041d240d40300784104c030181030180001c0f031b00380b02c0c41c000c8140b070601c00302d1400c0025207411410100c2805081d100c0e1015884c140c0c2e0b00821b42400380c400c20404560b15070100324880c09210807180a141c101851a0741c0f0200c50884c80010301c1d1641c83c048009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 550619568 1250 550618318 550618361
    0x120501090b0a270213051302010e10121e140f0f06100c0c030606171209010f1409150405040e010b0105030627070f1b1a070509090109 59
    0x604501c60707064a00c426540444400700d8081d00c00a841110000a0740c2c0941c181c0300c000c60296050148905c50740c80d03151151183c850a10001d0651001c0002c0c1d248124500f00301c0455059105440002a0030842d00101d180d00c55007004500c0071544c4140450380508000c0d545c101c0d0b0501e00ee44a000b0010034140101582da441c003443c202c42419950300750f116021424003103805d84666100a850ba005101703410380c9941d240e9a2000301c50f080d034480314a00342d04150500c03800000340f05040403080340e10f04241ca0114100c000801c038885841c0c0e00c50034051040040d2514088900945180d40f001a002c00c8000e140d050080700ca80c5c00030f00c20244110b0800301040038450b01802690780f00079046c2c4440d41541c450508100c41c0c1c03c116880465042d1280c014404d04030340020b0341e20b0003101c0c292108000714050b6200101000002500800f0171805003040f0800207000e001e0203030410030082544042c03030302c0d254000c8645200c1d00a2036a4003072644400410055000d501c07412128411644d41c5044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 550620818 1250 550619568 550619581
    0xf060406031e0c170705130f140102030c061303050c030a091a0c07031416090b030d110a020907030b0303190305010f0e010911041716050136120501090b 67
    0x2d580d101e442c1d2400094a104140180c4d4864520b0703550464014240302c6c0c10310000c1c1c01000540c0605500512160490803410891030f5102d0501c681c0248080c03010b5403030900807922266680c01c014040005009484a0030401c2c90b00c52000d55001340082c0c01526a00c4640c2d0030000c0000d4400c0c00f45040341c80c64100f03040c214190a00480d88800e0841c800742501914503100c1850b442c0490568001a014110007105004d501300082d0000c0e194201e40062481803600c103052501c43ea4400903428012220420721140b0b000017a115007155044030000c24544e101002203003e4100c04000607007500c00481c0190420542c8140b40c1d40e080c3e501c0e079007000640c1e83c4101e00b0001c0e260903c076141c1030b00751150050000001c1c0d03820070004041300200e010304d015610b0544840c01651108403a01d036821080b2095001c43e000030401c0700514003441e0200700b417243c03c00c0411a0840208540c0c9841920700340c281c940c9035100e41ca480051002000c10388640c002070501c83c0c06403007401011a02c018030301000800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 550622068 1250 550620818 550620821
    0xc02180601032307021002281209030201050415090b1603140906090d1b0615050d0812010b09130b0f1002030711060403050c10052205011214150f060406031e 69
    0x20034055100c0348c43c8071603030380d5103511079042900419207040180904c80306001a62a010384050076100358000180340c03505003018907003c0498aa45c40340a410045100301098814052039003080c030a44541f280b40034441010ba0003050014a1001c2c0c3c81c01000800c0008603001c03c20074420038011003a102e0945002900702c956401d04210305946094083d9060040741d040c1d400420002c00c0c00308a01d00c01a15900014a20f40b04400203c40054001805010260342d0f000158014442861018200f50740303000080c5007011034008801540341c0d00d080e15001ca540e6260107403429000500901e02044680754025101d60064200f598651420859001d136070401c207048404603038002001d840040540d10400140c0301d60343c40c0100c1089014421000510910740c0380841d030345582c0c2004000c01e441c3c00c1c009010001c150311828000ca19042d0014240c0e501041240c0d4013400c842244d024107292480000e004105070655103401101c0410041101501070307000c050300b05448840c0800d0b0300b00e8407200b40f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 550623318 1250 550622068 550622077
    0x7020721020a17010e0d0206040215090f0d06150501110a060e030409050a062102010903082a01090b0105090403170a0e010906060609060c02180601032307021002 71
    0x80c0414800084140340030100d00328980500c01094080c8803941e460f0040c05666162103007140e035075902c00c29001203117020403107000000c54a0010307152030310300380e00090003c0d41c0b2140549000440011080c05954840710144001100102040010721081c00c0c0000103001c00f1685010b00244d1070808610b942c0543c00c4c0e02c0c2c2e078403540801400341f803c4540d103070005024035034040c940900c401d000101e620314090107620f214054608000807807e14002143c580e1003805038042603a0a440d10107840942d074000d00e1401529041800956624100901c041ca41880c00c101c00c11051044811600c603004190000d04185000d280385003110f0345c0318010003038686000da400038003085035880b000c8040034203020420342c0520340107000aa10511180424251a1001d04c00c0b00c2459542a06112030780d0041c04503000f9001501d805003c1200d940d02181520030500c0111108070003507c0061803e038401c0d001031540d03450b01d11180b000180c2585c0c0203000050240c40100c00b5010f8108804000c1c915442500c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 550624568 1250 550623318 550623329
    0xf050603010225050f0604030513060825050c031201090e030c03031303020c0603070c06050106050405010509043204030207050f090f1905150f0d120f090918050105070207 75
    0x8043d490001c003904550a412a001c070385a0080c00510128520140700c01d0b84224020303110655541000240861200e080344c11850600c0015001e1108103a184001a0014a0325040700803d0100481007a112805a40480c4400380700024540c110b035245078140c1c0e4100c80c0000403c2c022034802c0c4c818203031240503070100b0203043d900c00d00028582130070188140c800c0300d0190054640500501022684640c01247d80c0c1c3c0128040c46500e4041055511506006060614145080038100000200144a040d0040e403041e03444000103c03041d52550013018001c2f443c03191201d040f150078510310204890483c6c003500980111000001e080c1402c545801c0a42002070060440b9601c42c8082d041315080030f0042d1951050002101403803140d28481c0f14020001540c0c140f0f101c0121104100300034a11031501c0707000c7c2006040700f10000f1741440c1b40e83e8139002c050500320842c4041d44803c82c2d00801ea5808030b0085400c211580c2800129501c1c80c0340c665001d000203111aa40340720040e6601c14591142 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 550625818 1250 550624568 550624597
    0xf08010f1b0f050d0603060204030f0b1513020d0219091707062c100806041107080d0203091f090b0601052d0c06090715080f0f040606030b04060f0506030102 69
    0x210702e003a4400c00c002c06130a01040700004041b40c0340d44406049811a030011201c1146981c0324100b8414280e42141e8000c40300c41080000011142c0800c2c96107180400310f0341c08a40201d0031074196202c41e01179441e0350043c80301c218640396202000609040a5104a100f00000c0c603803174804015001c64003005607110358403079034450042034011620140325000300c56403806100c01242102e643d00c003074014064810795911806130415a0402045400400352201d00c0e4000300401000199030100b5203101c0031a4120040c0c036555010b190a04059207070520441d0b030b003000421003556049507480f07405118029a90340c0740c00d5580d9001540e4510440c2100e038440e40005c0c10380301414002c0e005c01c0b00303001c480056090810664003d80c1d49805000d449142058010300000e0100b880b40d900100201606443d02903810300b0000101c0310043d03405007003080200951000203040c0308454021000841d80548a501c5a14060070008010f21041828900c12800d20300418580e01d414001c2c0d402e8880c0e00c456 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 550627068 1250 550625818 550625837
    0xa0b2205010e101a04080d0c060e0a170901020a05070608010e060909100e120c07030b07020a080d110403080a02060702100b1005071424100e060607020a0f08010f1b 72
    0x11030814560112034240c096071405c2001292007030b014040d40c0c0c091401c64440e40008030f50703131401006442540050350f2076a8806130709000810729140300c030208101c0711301000755261144030041307003080300c0c40030060144d100380e50300020700c5644800803a04a50400480c5103981d11000f0802020000c15181d0b61440e900c14512440c0c40d065aa020180d505ca1000807515160b0038200e0002d110f4100c0d0340d04645a40121800f00280203e83c80c24992020300c520280c040300c50790f030392100514060001c41a2440c0d81d01d00f9014038691a100c01c44001d1a00a200310b03480303d0035140c000359a900d00301d48440040c02810204d41445006020b0301140301401081c042c08096640811515900724000030b03030b0803c80c0104d03c10352400b0107121019070088040910074082d440c40e60074012240019003a02d40240f0b00000821604441111258000108807101030741c1d0601d43c000100e0b4500c0d00d40003503a4010310540b00080c1040d05600c070308004580460305005040a41001002c40c2c04031400380030201e100d409 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 550628318 1250 550627068 550627079
    0x105091b03011a1306080f070501261303090b0d1b080105061801020a020a06080103030207140607022101140601021218060708041508070e0f0a03020402030a0b2205010e10 75
    0x2607213501c4020f00f0000041d0780d030391804007070301d050498000d90041e900100d505209035644602e0301014620040019400700d01c8034010001d00d10b01c001c02c017000204400e00b441c0101485000103800a00c3c2d08050b03a45c88800031a8144002c0c400e50180f112a40c0c0c01d410300440c2207001300c4026048404c014000c5003020101c0c09410718070010780d40f02c4c50441c09030b0700c2d103440140e441000082c00362010b41d031252002c2d8110300e4044c1c900340160f0011210b000c0081100f548550b034050403201c8072a41610340e4844032924002c00482c0d09070910595801d5400c1003948007120203005e025500c01e01c42603007110f1019420028000a031f20032032081124a140d801c40c0c0b1026410188002c00788a486000068078059031050b14007000c04150440000180805040c04507a42c0d10103102081b04070116100c4a040e40714400064501e4010710000380586c0d008000100911000e92200b410010042c1001f40e02850206505c408590580d4906d040545484004645a03003404000ca10926054003c050000c0c10310 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 550629568 1250 550628318 550628329
    0xf01060e0915180117010e0f0c130906021c0b06070317041103030307050901020705040209060a0c08040906080a02041b140306151c0b2d03030c0105091b03011a 70
    0x40100641003062074108404a10400820f9402049905900c00201100d8103030070742561f0304681901d030340c2d9220401000c98400c0c00b042d0281808011981d00c0e030490b622901e030341c0143c4500713200034200c0751011072000f8010300036100d401058001100c00308182c5240104010203401070900250000d805c5090200710f20819225140c0c0003400f403540612107200c500002859640210f403503a0008801040c4c83d091541c041007030710b0242c1401c48080d4140085c21000c1085401090910810048200740a000707002c642000ca402902010300b052207201e480d003c4596071450300c2d840481c004c0c0d00e8128a400391078142c404521251000e983d030341e040038145003000c042c3d60300040d1146038846105030043c00c45d6003103603005290040502e0011000c5048050310141101e040d400a54082c3d01c00240b1403401d41c040c21007800440c0340c12418000c680c0c01050200c0d28502411940d40b51940c41c00090001a031000140610808501001d0b0501b20030354000b80b6085e13406900e100381c644c4106c1c00f035062552810 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 550630818 1250 550629568 550629601
    0x1b0d1a0328140a030c061503020904030f120f0c081e13031107090606170106081306110d02031b0703090e09010e0a0b090f010506060405100c08030703050f01060e09 72
    0x158042e2112510804103031424006034401c12004030348200c0d641c00c01c0107550b02400d02544078900045401c1032554001c1a00100024802806c01031454041c4052034003c40c1030b803855a2050504200800d0981d02505c0103000300c03007003800410b03510000a1501010041a0421044800f049002d81c0e01c903000d1050356405046c0c03080702400b000340c0841242100400c00480105103d64011865510381800a040d640308000d5441d104440a001805915003215580ba0081c1c00c0e0500d48080407550b0826400811280032407081c3c0c5500020301003141411500514010403400c420034201801001010985105071400100890701c080d00800140200c4a500c640c05403011001180d058405c550190400c01b180d08110384001240c4207110501508110315290200c0201c000c01c80b5040410010b5680d01481c45401c0c0304100d10150310344011b1050070714040c100d521071020b9442341884c17040900505011102d201542000400000c0c065100741362032103502102401d402480c3c0c0310b20350a0141e410b034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 550632068 1250 550630818 550630823
    0x2e05041101030b150d0221160f12050c0405010e01300b0d03030905010b10090b090a0b042403020319200a11060901231b0d1a0328 57
    0x70100d00e410404d440c038034001d1244840030000141e0700d20390b804e5a0000c0120384540c031910000d0305410080d583c80014003500d441c11705401e0501400e80c001d901102c0d0034200c0c00c0310442150410003808a000081c001420035214241c8424004600721320045445c03441e20003032104200c40c0b40601d009141465240b4030f01d100d0401d080400d44814980c0440c0207807a0303221044000039138401d1064180602803054400203c4101c908860201c42140000c00d1036007940100058032900103003525465445680680050802920071503c9a54910581c0d44902510075401034078a9500400c4034894802e100702d80c0f05404000b000e854021841070502c00a18025130941e1501400c0d8121141800d02d190252501812507170300c4a4100e40d031402141d041113400381241c01e450381042d459940300071524401c41c0044881c07104c0c0c0241c9688002001d040c51400d50b09030344488034002001c5103a14138070380090040c154280d0f280c2080e20303022024503981780c1015102505003200d42c04850001040e2203009100a070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 550633318 1250 550632068 550632079
    0xd110d0f030f0e060f1f09021803070329010b0301140d0c0909030905120604080706020405100c03020115151805062a010504031706122e05041101030b 66
    0x10104902e010407602e118441e00f10f1030340050100024120f00222a80e880050740c91401e005818981310300d0050070041c000c0011040d0007041203403e00f00004120203504c038008048404030b80ea2800e0000740c59054540c0b0018012040c10b0b5500c0c40b110380c0d00014100d9a408130080d03c0c582ca0711283c0c44042804004c031170340c80800201c0fa88085505080701c06c0240120b81c8000609030741f60301d800352441c03130306a00c064010014558603040d24140898132030303407081d0002d01050707440c4c0440c60030030024402c40c1c210310f038840242d40c040783d041a80005100c0c0d007588250000c0020605105006205605a1151403032000280d0001c1120501c2804407800c441042c283c4095032580380c10008040e0341118044800400106685416484580f240600e03001e40e400001c1001d82080d8400a00003d6040b0401d40d0b2200004080b482e00d480703002e00c044510b5071701d03801e560610f01010f00d0410071128209040000d81e202044c803500e903000501c5858040c2d40d1010350141d85001800c019005440301290283c2c1c081d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 550634568 1250 550633318 550633331
    0xf030306130e2a040c110c1507060c0507060e0307020d110d0818030120041406070609061406010e060706050925181802130e01090609050d110d0f03 65
    0x9844000c03030001400081c0300f20184000b01a010f0008844003c40d500c0204581c5c40c42d20381c4d0001001c10740c2000e03004141d85051081004a42460b440e2048403802054245031915010302ea9a20002400105100722000d00000020700c2e0500d13641e0140420295000880c4c001d0f40700095924808440b612002812840c01110151101d906070f030000b04010340314980750030303502c522031a00b0705c03d00706c5840c1d04100c825001c0d80442380e1240e60340140c3c01105030103d03040100c80c070140c0d6240191000691700c66401d010b5a070342c0d0b16180c8048c109900c00e036242035118502140c0d1543c001c24076a40d107088003030b000500300320f25a1185400b911019055041601844010404000c4100fa0620701e00801003408801c152030306550f02202001d0a618030102da00e030105038811000080362492440350115140c4071202c016005110003030541d4851003841350b1a004c0f40303d042240c1d6420204d040ca0040b000d4606a8a03401c0b02500c2a00c0c0182301d40035036400504c0803003d41d41c01800810f000008529001502 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 550635818 1250 550634568 550634593
    0x9090c030106080a1a010803040605090406030611070c320406081608060c12040807023f060f040326010303030509060615040605090d081b0f030306130e 67
    0x844140f900b2020f80358000c801c200c0c052000c80004180d03502ca010340b000503590b140000030340d01d0340101c0c0a4501000fa0014035224280e03160340110001d1a0001000c2100d40791045c0075100d10303031006004481d60304104200040306861500000180c1420103020390440c2c6900d2400c440740c28001000c070741e005a6038040420041c4d41000141c4018aa220404440c10b0174401c2e4a4540314008155801c80403040010003610003503840410380050340715070001c0d1201074510010303481184d109088411081c03040d00e803a00892400c001d08400d9108030065507000202e843e801600d5200c200e940245d0100007601107000030b44507421000c5081c848400030840481022140c2c002c80ca02a44142d0000b5100ca06125035607130144146c46d003005040f01c0081d640042440e02c00214002c501c90001400804038514409880c0d19240c80c4040b13030b102881395a60701c902142d1007120500e1142080051240600040000c200041124010740e00100002d201e0359050f41000003400c02c0300d003032600e02d0050449000d030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 550637068 1250 550635818 550635821
    0xf0a14070807151b05030703020d05090106210803130503040e07081008061006050a03060e1306050702031315031e0c03150e19020903120406030c0801080c09090c0301 73
    0x2400c0348034440141e561011410b000749083c0c01c40800b910094540558148045110b00c1103807400a02c5092081d02e940d90b5000550007800381d48090b10700c4c14188800c02c041c140043d070002080d0b03000d444c482c03644c400030902c082c00e4041400000804146007000800c00b50a201c900781070003140704804480ca001e4903200b400360700840907108080850444005e0000c0800b11004074009003903480010000382c43c000ba6480103242040c411082404800140c580015210780c1089001e0035a1890102d200c1c205a80442c13103402d02e05d1010f8401d245408013080d002c0f031002c4111444818001d1600c0b54040c2840403d041f900c81c3c50711410b0074981d403055040c07500c003180349610b005c004100c000055a5129540041d094a000c1e000c21002701c0850101031240c6019101816004a800400542055400030100c0d0080c450103c0865140c410712903090700c50301180c1c000340284d44503640e00b0301c0001903802d81500d0041c0c0030300546060790007150320303090f1074100008500d5008401c10b044504d0128081c0c003190 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 550638318 1250 550637068 550637077
    0xc0402030606190302030604050c1822061403060124030e1006140a0b1603030207110a03140708070f170a02092d0c0a08040f0614070f030c02030f0a14 66
    0x31176004020461903107801e200d826804050791107000c0c0382c008a5400c1341e9241c90005402c81c80b8010a081003802124144224000002d45440400016494190100c251087c52002c0d82c0f2034460000046a4400904254000ca49401ca241150321034107150a0f406006d42446045e000c0c4914082540e40500707034000c0000419088003048540241c2000340008006950003c0b07039029000c200d400c3c841d603110004040c042d40c140c940161038424a00d480c1014503100902964403405400003c010711010240b484280e00d080340880c1d040c50340c1c52a002d42c450420f48500f0b10152808001080f01040f480b5030520124494015131342c481c1d40b1503000450368181558000540e01c00041c107142100462060200d2100359162006540d103007861000c8003e100c1c000d041c0f420060154041010407411008102c03c069219105010800e842801c074400740008407083e1000607120780c584a80d880c000e2003298003001f0b40340e01031454800f400146201981c01290507a0030480380003d85540d040d07800d000341 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 550639568 1250 550638318 550638367
    0x110102120601020c0109030201050a050d06030524010909020102060109020c0c030d180b131502070e070302070209011e090c05130909030314010b16030e10090501020715020c0402030606 81
    0x980d040d041207000207103440c0a400d5960b040c400300344030510240c1e8020050b151607540070310b801552082120303503003005410147e000500520542c007507280700710030f084840e0401400404204071183c1c0e07035119070002d803403540b140a800351b0849001444012401c0e00104001d0700300c0702c01c88030414170f420701007032404116104240010f140200c1040051201d500c9180091040c03c0c081810880207140041c0f61984502c02c40300d071085070500940d40540240110300090a0b102c8050505280c041400740280d40150b00491040200c4000450740ca5070700090456070481c0c12141150703450500d4800c5005040712a204810311000b88440d90700c10354041c0c0c0240c0900720120000c25040082c0c40c01805842c4c4080c4488040030001c0b0042c002c40400c1c2047c3c5d501e10381000c07031180c0401414141901c40243c044910784d04500410412221150003034012011141d083e0308860340251740e00d0714041445100c6072640700580011400d40e41c0c511b0306801450b0045402480705107810988101c0310040a00c40008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 550640818 1250 550639568 550639597
    0x111071503051e0910051005060d0b04060b0a0302030105030d08040803040b1005060a030603230318040b0901091b030b0a03110a0f1805060604030b0a0216020603090f0c030f0c090403110102 83
    0x700c2c01050074501445822412072901000c0c01030402e0005407403400ac41c0b08624201c2e81e510030f001502d40d1650842401084000446917568850071001006541f09000d840c1c0644106410000d19a00c95804c00b44599003000503941151216a07441a41840280410242e49506140400e555072010b00400c10a482600e0004140d481c5283c84032803444c250702d60316141c4180490300b03c0f586e4004000c42d100d030500c0360300c2d886003403a00c00005401040d4440351103030000000790010038a07101907031000e01c2c52034122480c0207c04100207021402c0d2034850b21250342115199208000281e0980c003030221651005110320101511155541c001c0c1140b0342c0001e21001c102c091782402c6281034030446411401c21b80300c403071901c1e00b161281c02202c60050300e4400495400200343e1015484d01c0014000d080c1c0c0204500d0380e13400d24001040c1e94400c450718400441c0148094208149400145030b11018050005010500038020401003040401402901413050501500544034020320003041c1d2220110345 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 550642068 1250 550640818 550640833
    0x5160801090c0503011b110118030509120a03050d0c090e0c03102111060c010c050d060906030f0609030c0c060f09150215070203090a0e04020111071503051e09 70
    0xd01c0b11500b00d031640002c1c026403400c0342485004800001a0040100314203155000c0c40d02d2041d40e40c018001040c030b406400c0e4404011a0030560f01a0040c603003400103e134440000f83c10ba19404d40c0300c0c0004200240460710030040d1480800e4a50010752304070f0f549080030900c10344c1e64062090b91000c1190410161400001001003100d94004d401c80075100b0450381c10b03400b04003006850020090700301f000c0c11014202e40340300f946990324030403151590000c800a01540815075400351140d00310101011444d8285500030074112024810a000c494000e45807018182607074440600600d002582035040142c080c803080d0224444501c0000101a683c0d10030b0340d44040014010100c1219800901c01c002595260581180c0d00040d180654041071182e20b02ca91554a03090f45184610503145d600450302050028500f0b13420400f4500c01e078000e032585115038480c6100075460f4070103401082c0c91501c00d10180741a039486580055407220403003500f8195248040d6031100d90360001c40b11804c4580c00b549 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 550643318 1250 550642068 550642073
    0x40b0408070e090c041a181b0703020a0227011d01050904030815010e13060e0112020d1709060309010f2a12020d0513031e08130516080109 61
    0x1000800900c2c603036a215040d428101903031903ea09050004511070703911251100c0c032545490f003020305c0742000108030515000100481c0840082d0440f5190f00141e01e03d01c02d410304101c400304031001943e066000d0411600c0c0c036803c008a4001641d01407800c9801081c2000a40090741071341c42c00381104a400da240d2030b0b1804030a0301d030170805812075402407030304d48240800250040d14031608080810042d2814a40c0640100e4000700d034410a260312400e40c148000300081240d1050068860620180c13129a8071801004070030598910b00940003a8a4400040403c41c6e02e0320010362050700035030720351a155607000018003c0d00705554011040e50f44070191860f20301c02d0f20801c0300045c1010500e1521408840ca1042804c00405050341400f90801e965140c14901d54100c52400100340410800780c01c0911640003080c04882045000c140014204102103c100356000e0201e029a0b590486c56034982403100502d414070030341101c1520880d0704807030385c101e010481e203000f6003450400040c1005950 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 550644568 1250 550643318 550643323
    0x1112240103060b0715092a0b19110a0812011e030b01150e090f010e0714031803071401050a1103012102120604080901301e02040b0408 59
    0x98140340c41c000003000414100e02c1665800c940008441c0801c400111408001c1c0c003c080c00184079209001c0e461240340d03084000000c00305c00088070305496588407140710605220b0103074825120b100604005908521a07114404450760910644407600c24642d201012900201d40c4100411142030050041400c3c55010450810700081c41d41011841c40d1241ca480c2c041c10701404592821344049103603030a01518015522180203042000f0701d240c807a204d41e5885e1000c0c014800320020360800f0a1401d4441e5080d00e0452001c1c3c841e076459901c07620164410828110b100109034042400700c00003140700300d214507c080d4040300c0040754500c2c0014840048511820109217100303001d00c0103110480e40480c51030300d000800610520400e4031400001c04104080307084504030711900c401c0004204041c00030300051300302030302c5400c0c0d2134940c0c0c00405a00404c6001c40003c414140c4403200080c415600300c0e146044040c0d40c04400441150910001c1c3c0c0d00a80154a500d034000404020003c001c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 550645818 1250 550644568 550644631
    0x1e15030c150e10140a1709011505030a030f180e0a0608070902040b120601050c060c120c09180403180e1e0112060b040219020a03120509030901031112 66
    0x1c64110a265039060000340000356400444111010082503000720705000d0311194191b4120211400c81520344801301e5801b070020b24421160300c9041d0100050b01e800c0000301906810342c1925140f11810b18030504540420812801441c002180c0c2c1d000503150300c940014500034941803101060003420503401920b040e20651144c1c02003403041108100103080603003961f00b0f0700d0302500200c04a89419004071064000c4008130015070040000b481086200440101281c1d010100800c4140da030383c4002400b5401100c0300c45801800c18070311b01c40600c0c00301c4074441d0310612900b85248846091218031505000c943c0001d84448000d07000e2040c58001c0f203c030028200c0329a01c0c3c0504640c1800181c44400075600d400600c015156010613507030781d0365a0159204c001944040048901c9040340095a5600d041d50640c0407412a00c6000000740300b602600c2d20404c00300000b14540030b020740044006041c0795440c922058414019100c2e2070003900c0d01180941c0000080700c3c40748540d00040400c202e007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 550647068 1250 550645818 550645847
    0x108070203090102070905060a0801020a0504030312020712081308040807080609060103050c012118030e0306090d361d06090402120a021504080f011e15030c15 70
    0x42030107141502c3c0e03030025104056031800e810110319902c410000c5000342c9801e070420542c2d940089607103030b04c103035205000e04205c2c1e00940e2210f000c801c40703104220491181d50006082d09008a00c01c14000b40100134840d0070002020044400d8255034903640aa0b030040d40100200d0303042144100011201000080c0d001800380010384041c0d40346980d0325981d002481e00d040d040c00030128a840e001c030242445012144541102440304448601d010504428080c40842c0450b140d801010400c0c2000a10240308000d42002008840c035a2042030312003060380c03d01c00105407664484041902040355024840801c3e017803000750218144410200c0040e42c1900c0705200100f044d040050f10703651001078a0b040798042d210808002c880c0103070503041070340883c000f941000001660348040c0e2803107002081203c11820036101c000201c421035500703a98210740c03120324402c580c421141c0712100c10360024059203460700d0b0702e01e071840d500d50b222942c0324199404008801015598580b1003604030120309914038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 550648318 1250 550647068 550647073
    0xa0e300f0105090307020907020307060e1e0318060d060314011a0d030801060819050f09070504060803030a05090a12050c010615050a1101020f1b010c0807050301170c040e030901080702 81
    0x6031010640d0354134080c05c0c4000e4031501c8076802140540e8001d00441c0c00f040d4000c0e82c144084040004090341e02c00c03211048113403026040c421440d04440110940b0280c0d2250500d9008812540c3c04111954120030307900d0f0342c2555181c0001001992141940000050540001c40c0144143d44468a1503140116407801080041c8554000030750280c20581583c550b801e1500183d290261401203401c020008007078030a14040c207010700b40c14a4421948141840c0003102d0b82c07562030b00144010782d08144101040da9206001084c5400203076000f403940705803614201c8054513400d40f16019000042804500452030020310450030410a002c1c0c18094482c03500e103040242a4900020954420112040100324141c0403122030000c0c2034046641e441000b4a601c0c3e284c5480301c00d083ca24040d00c0c81146d03801d61a0964440341107015104071440340c0c440341ca0300d9095a00c0c2240001080400900341904c0d8011301032104420303a554814183e20301882c034001d64440490000240074800081c00071025503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 550649568 1250 550648318 550648321
    0x3150914040b0f061302251b0611031c0e06070804140a120302030403110607050901020105220311010605033304020f0150030c0a0e300f0105 62
    0x41c0c64841701c5121083c08041c006a66101d84d0f00e81d030b150001a410646101d00c0c44003249010b0201c4194103d41401c40d190780c180d8955602c81056400949604441e8021703081032100c00f843d10902007905622462460b0080781103480c0c1503034241040070403112503000c00e0400b402d11040c046440d145080b841c01d007000410300300c501b94540c03066041050212a0070190004000750815220306500c3d4038058614040711141d00b4414070150050f08127103031150066190138001a030121400318400000c08910100c1020741c2442d8500300e449200e184a05402036403a080c00143c151004c0008079540c45244441c0c2c0e4400b010031400c091001ca42c1c2138904c803608104824840980d81e180b2407030080f1340d03090070642080b81c0f004c0700b550a0400000541c0806145076015800c1959407900803a5068002e45e0826000d4100c511091055000c151110f4849481c188000507445000c0e5101600d503500041c0105144070410548071414401c281c8902c0c03505414a09001d2082810070129590600e680f009024a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 550650818 1250 550649568 550649581
    0x21b01090206070f02011b03120b04060e060d020619020106060e030d02121606090b091905060c1e03040f14120d090204060302030f0102030708060d0201080703150914040b0f 76
    0x16000e28070340540504210134481085a000780e5100c201070343d1569001c07400e07049600f006410000105a01079002d81847d031110082e25142c4030b004280c86107814400360a494040c00c0c81110341841d242240c108008100e0140390400c09000a0452601d60f030010900900300710009100030744a40032240650320400e00150800d03001304421982c500c8109400d500e841d074513070b034280b03807403180d8100541028074101d145e40500001c030403403a02c02d9081408075450300684145210ba000494000038020303400843c0815a17589407903004115001e001c60030084c0550800c10700586030344c4160f90841e80e40c50380044041c1040561403403071200f4107062300130b400050180280e000c89407050030100c0c00003e03038999100e821076849038018005142c0240c00c440c110507103040791b6130003075000f80e0f5810007248036400000d900c3d1038440e5030b001078107a06a40703041c940d440e001e400750301030040b600c40d01da8000003480010400003990720440000030ba0007040c6040c94106030038108007840d030107040c1104182005081246 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 550652068 1250 550650818 550650829
    0x9060501020c2e090b070b041406010b0d020c0709060605030403112805071a03010f0f121103250f0f0803160606090609021818060f0a0503060703021b010902 69
    0x80f83e004005600e00b00c0d00450400b01d60303e00c41908076507034281e00800c4440c10700c104034029510681c400c0b0542d00c40076500c0c044540c0d079280c0910030728440000800a12810210640113861410215021103050a0f141c1001c0015200340d03411103030001e0004007c200600d075002440d0000114444060724401d0194000241c94014034030181200707916039143c810810404104910050405040e021690144245004e40c85c0c2c2c000c0c420130301100010b010100c3c040c180c0c000c0f40821249182000400e144c960b41d1255001140b02d6107060703040c001c0d40c041d4810001c0c89598041030f4189815039880381818001800c40c082066005541c0855200c6020300ca940c100200300c85031526684440d0a03007294030700c0c0050140080f6008079404034240794000a904100350050031044034038407000112032110790103201c4000e801e080507862050030700340420076034100203594005e0600701030107a110040e1030f000401c6c900541030f070f11800000c1d80056880e140b81c4902c911500e41c410718000074401212150002031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 550653318 1250 550652068 550652119
    0x1c0c0b25050d1b050114070f020304050307030b0a090c0603021c0b1c080f0a0e01030506010f0c020402030705040308070803040303140103170f090d0303050f070e03120f09060409060501020c 83
    0x103003d189042403c04404010300d20f40407a80c07040c02030094183c00c1424150740315081e210030010684854140800300c1c0080181d42c141c500c041c008001d604e10310745400e80400805400071000079a100c1c0c0c02004203030350020707c001409007920302503030302c000423017030307034101340a1080860f030174510f407003031001191f07070bc2400400ca065900140021701e00b1450806031054030865000c03459809001903e00201c0703400c45044c0c1001e1100362020040d81c0d6a1000664406c0c00c0013400c03000003014688850014501b5a02854003e4407628100381456129901c80019502c010070030786007400040f0400081540c10300801c0c0d0215101c1c41881e05651456540740b40009800f809205010004600b000c01514800c00b9200c2004008121215042d134908010300200b43c25500701904800f03210004030498000c2481081919014008001c03070004481d4107220b035046200c00800061081110040540d101e8014101802c502c1d140051700a10b040006031500d41d88007040c90040f000310144d0400540c8401a20 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 550654568 1250 550653318 550653343
    0x1201090e0f0714041a0d02010c0c0b1803070909051507170f09070503030a091710050405030c0c010f0f0e030c090a0c090f0e0103021c0c0b2505 63
    0x41040c0003050351031414114504540354162060000014048444882140c4108000d8404002e541071710f8440280140428107040c2c0c201d07940101d440c0c011352007000d000c0103280c0228140440c280e105ca90a0005511290891039021100400181280f409002e14030040020440412a01c8065559191999491134510b0301010424000640040c024508400c6652031030814481d54a0141100e1103180001d41e6903100b1486203040100d0303a03040000850305040c21f241c0b284c0882a25108648030112000f811540f202c0c0215000c4802c0d4040c640945401584101c000c2d540362403410170350601d001c0701c082c502c0e8100400c640c0f42803845608480781c00c01d00001031411010b1281da00700820720381000c50407444e4008084c0405c100b01c03804507500080c3c08500c90740e1841c40c1190b480c3c00110801106005001440843c08010401031070f04030346851070f0201103010320a01003041d864180c1103500d03a03070184200f40d800140052440d84565440303035801e42001008285120551105a0764103510390b004c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 550655818 1250 550654568 550654571
    0x90403110109060207031d0901050a05040905120c030406020d050a0905040e0f0d1d010503241309120306170705090c0c06011203021903050a0315122402120109 70
    0x3808a060039001802d219401500c1550f83c0c10503483c009020000100840c4003101440c00421401d1034030040e1641220001040706100d2828203040000910506804403400d100f514400c0c1154a80400901030303000e221006103482c0c91601c40040c0c2401000803000d010448100401403100d60000d5080c401d0703903000d5400041d01007115101d1481c0c0b9030342061036582449034048040a03194400ea07625400c85d0f00d00008003d0401000040d640c502040d1582d20600d10007060b01400810400d201c0c0100d00b8004110540d80b002c10382003001155a07069054400b04200d4140d03610503500340c0244401028080303d50854428080d840c10380b505e00701e0040701d120702024004581c0f10b105803419651000088000e0710455650b50008440d521882e076000c6001d170180e40a18074508940441708510f2503003540b140d80c540a0005800c9006180307154038140c0d040c1141101244200c00300800380b01c0070744141c03040e4855000d41c605518480a646100f2880d29004000305a0316940648006044030030a110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 550657068 1250 550655818 550655837
    0x5030a0207080408060a1b1b0209040303140a020d0612050d030b0402250605010e10030f050304032a05100905091308190f03021603050c07080613061109090403 70
    0xc2c41e103201d104981c010501c82c41141c1c14002040c08030307805000301c7c1a121003c031264405513441940c80c082c461000c00c4040c45031031074400260900264455100e4400d19001850351114840c051400400381c1e000d0394002da01058020740e0625a00c21b6030b02400352684191880240c036655146d8504102805400701034460900e89010b1b03c1c0c030340650303881c0003e0b00d41c1c038455605810840302000c189444143ca0583c1400000142e14000711205030040c00354090080200c0d0454807a01d0641500a000b241c00384000c1000002240c6611240842d40c40c032110060843d0140c0f6210f031290352840d404c118418141142103032030140d0000c6450040702c5c02039a550300540d40e16401043d200a11000c05017880c240003e90b030394600310b1403070724980b5941c0988842d501c00c40540c0c0118228015544030a141c516034401c20004640150080c04a81000350100e44105455078151824681c05135110204032040c00300060800c8039074010400010741850940703052004c07007000a200c040001d000502440751040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 550658318 1250 550657068 550657073
    0x10e090601260106030f050a05040c12051516080907080714040e0f010203040215070816231c021203060904151505010914010c0605060105070501060e0a06080d05030a0207 75
    0x2425011115400a20320a140da034414005d4040c2007406c03100e180c141e1404002441c144260f101d5907005d240c22a60481c211824000d1010801005c00c90a4403141305e06251a01e000d8188031550303100d0314160001c13281e0080c100d0006414010058607001c40307600400c105010340c420024211003182c244858884020102c50082002011015407079a1540513812903481c803010150002c60003a0320a40c3c800c440340103102c154070b580e030240c400b00030030b040340400c042182c4940c80d1110305446405840f6611020084030070726104d0f0f642d88800d410880d0410040701c41c0c50299542090221480350000e891042c0c03446d0440406884000c001038403071210000031406000040001c02081181030b0410070108115a103221a0080b05100305800a0a0f440c001700f0041d135040b007100c0b10b0141c1a11751030140d012a40c0c46a015140082c1010b0400c00d080c440003022400900400d401400b240d91001d4160403d000c207003041d10a15007001c43d03107038494100820b503075500c04212944007000000c0140c8484891 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 550659568 1250 550658318 550658357
    0x309140c0f01230d02071a0412080a0f090c05040615171803070b010503011107051b011e030f0c02060106021506150a021615050904110d0603120e010e090601 69
    0x30307072101c00581c0e004135031180d08800c294000c1c000540a81000068820580c0c0f0b00301d1402ca04540003403240380e00038006070001d400b403541c0e5034105a0074840414000510303201d00003140c01c0d4a0058611414840c4e04114034109849100d0143c9a0001044121004c8420151034411451803e04d44600705000044200b0440c2107040c041405480981e0b9940e0014200140068000e0080314869440d040030480340702651000c4406459201d030140010400c501c24120b0050042c0b4600390510442090002000d005100708103803a000c0d60b140020940321190600d000c40d28150000b100307551003d0b006100590b00000c00240c4016800d84251840e030b1150082070401921141240d07102c2800300c0c807840613607004541101300340c0c003446240030100d42d038800c0340404903410021280400d200704260415070074a500a10202c0800e081d0182c40c010154074400110342d285d0340300f42c84d2041860343d0f881c1d06d503503c504c80c030b010200c0034a820001100c12600103115200090310080c103100c0312040c116400c03080d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 550660818 1250 550659568 550659617
    0xf06070f06050f220f14011506030204030308130503120903161a090a0809040b12070906030b09030f19022e060611060105060c030403080a0309140c0f01 67
    0x21103001d02007030822900c070304944071050301e410b11160700ca0364190402d2818491540e840d10b4011740a8180d0b2241502c0c1c100d02d190918580b04d440395264140800c0404030841104014506d582d0b0060f65646182801041c80700b010704450101c400c03030b0110030049440081514030003540c0c070074100a01c0c3c5414994518500c82c000c20250611251a488402d01280c000303e284014519001c03408140d0703c044c0c03030584a1480f03110040c0800740c00c0c001e891250402d64003c101680e0058004c0806821301200240fa003841c1c0d5000e0551716442c1c20381841044603610308103030025086c3c0000d50401265440c1400ca9001d4001c0002c403649090b100c0b41c454a20030030000785403002005a90159824001080940034940101c0c645d0301401c150300040c0c40b9108000603107040c1801c0028000316400c20082200d55400409810b110348418000071010454400040c40d00d94104d890000d010034892a010203e400d1041c04280f2175004002a40007075103c0740c104090206017403808400116440505942c0b4091 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 550662068 1250 550660818 550660823
    0xa0f080913050a0501030b0601031e152601110a050304030f0903020d0c06020607300905070b09030c01050705150a1b02030706060f15030903091203021e0c0f06070f 72
    0xc050034403080800c0f41c0c0c00141640e000317880c9075403d551a00019000c0d50001c0e642001c1d42119403070b140d4521a080d9119403228800ba02c164100c00d541c40003161190b510507a019541000e0048054184010920801e00c10084500c1d00c0c905007049440f020f0720030b00000700090140003500520074000c9108418000140d0760052082e160741c40f60742080300a070543c50151101501c40c840100d61658000d50740000e405080220310110405d2900130035006c1c04041d405c54401c0c03a11091900c2c00980140861406450b250300b010f0340302e2020f5401c03d0b00d0114013070b03d92810b0100030807545000c141d0100d04e41c10180d1940c0440d0381c1c0c0e903d910005038018100920303240d142e8494040f0f0710444e0f550105c014402c66002d00300a21a01da1500f03172034001024a44100f14503038070f461200e6840c00c6d00940002103640e0082c20700585655603041400000b02c0d80c01c034100c0c0181c00c0307009501d0200d900c0140701046031600c0d900803c0c13030f0344581022521032079854440c5846000007040c80030400840c4c0d542e043c18540d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 550663318 1250 550662068 550662071
    0xf06090c050c1005061e0303190f173601020307031a09070512040f0c030807021201060b0906090f0a030602041802030405030d020711150a0f020a0f080913 68
    0x91025401070054000440c0e0110a00070240c0403d0b04169901a1030302405000780384031015001c04003002007440d6a01d040c0c0790103003c18012144100720507142500d000754141c44c0d034100e026521000400340340307041688042e04041c0744188030440c0e610030030010000100d01050000c0b061400e03511703000124120000c85180d800002040407140d403540000301e1120390b44407440072104c00700c800c02084080444150001680c00d100c440c0d242d00c880f0881580150140c0e401d043c3c482500e0721140003021040c0c1080d1411840000e401d0f0850074146030000565807440001c0003481d0801803464010310035070041522800c0d01003035111140d81d802aa034030424100030809160705699141c00400794005110746000000c10f00b1811214846e03070b000b140d00c5241e111018614050072400780c800223421456041e1840003071480c566440d600d80d90b0380000182000080350b919550041c0000784000c3c0800760050464002068040018140000802c801940b144125071104282c102098502030700103480c40c801c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 550664568 1250 550663318 550663331
    0x150f0622090312060807030503180d0b010905041a040c0b0c030f0313061506122a181d0103080a02011407090519050d0b18100e0c010e030a060f0609 65
    0x15000b103080030090010000600030940e170703140c4440c0c5905180c44060400d0b00100100d000d8942d030442550b14281c00201850403541690f00e8a00c0105401d800c80c0104658a00901c824003080e555002c20b00640c0c650300742c2d01341c0340c6070313441008000c1c052180b034001581c041014000700d503040c8107481d801c1400c00441354503880d1800075017030304609001090b10064a824010140c0b9150032038140192410f41c1c440801015280d100c00d00104452803541c003010055a00384041d50440c0762041650383d1131951402c0b240310105c940381d0481b0320142d000303060118005500400890441011604480c1c0200e003180d15030707903002000d9025110025140100351802420044c0850304101c5d031105031201a20300d4a940024400800b08040040c046d030b40d032010003080070700005190000f515501a00701d0700c1c0c40b0012101015140d00c0c1c031484264881103a6200c020920840d00304002c01e10b0074020034030744501c803080d8441c04281c845006610142000303480d0a4142103186d03094004100514241204101a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 550665818 1250 550664568 550664573
    0x50913050d030b060d0c021609140f090a0609080a08010509060a030605040203011d0f01060e011202041a0306010b040e0c1629040b0702061b090613090e010e150f062209 74
    0x35801952403c00c0c01501e00312300401c00f810300c4d1040b12042c101c640a9940e030b54417a903a40d0144600f00801d40d9105214890008000440d540174403110039110300200340d1144640d07d000350822030160801c40c0a81480d00810400350741e14031205084070303005200042c40391618001310b405810a001181804444002040780b0312400003544101c0000c0d10008120b00c0d40c482070400700ca143e00307209a5031008d880b40b443c0c2026203041d503c118100e1200315100909241003802080c14030101f6406030740d00d0b034008641084243d0a0003407043d03106d803482da88203280c104ca544c60022100300140c0050a489c14280d440b068215803407120480c07035824070488500750b2070180303003c2643c07190441e100c0300140070b0807010948808038903011010710b4004040c02070801429100b803110319001000100c2c0c00c2c401c0e00c60005081c10441c0300e40c8991240c20400415603101004031603150401504030101e144480742d0401c4401072002d9071241d004141142c800d803a55081c0c103d042d91203007001c00001d01c2d441c0741c42101c008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 550667068 1250 550665818 550665823
    0x70f14040e1903051b0616050702011e0203120f09161a0f0c010203011401270302060d0b04060315060b0708040b0304030c06020a0c020108090703170f1b030301050913050d030b060d0c02 81
    0xc240203c0407c80c1c60000d80000c203d48500880900a022a1509854039918141010352010b0100d403841101d042003207140903284041029100035014420220a0040d0707800240716159403181e81011800f541440c19603940028000340341500c1c082800481c4160110044c00203c40e40040400c00964681d40c4800342113880802c0e100060303006c2350f100c55000007030030070500703484801105101400c00b466146800b8085981c0c40200000e61540c1d58038500c42c120791b26442884060350241c3c400303100c100e8400000b4001c880b0160021100c05200b4071002000a84403003c88068132440b81200d5180e440e83d2405603150152031100500c03842c004107200703040303a13402501c14103094003d0f039500c08a5102c8402d0f19441d1281400007919401010b0782c40b8008840e2b0100800030808421034131441c280003950480c0c0c21400141e00b000349900b00100410461810745941d0b900450005032000300808190348507032b51100420400800d060322408c00d40243da03504000c0e035801d000884428003540301b041078000d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 550668318 1250 550667068 550667071
    0x303050405040f0c0e210717010f0513140705060f130608070f051803060108060a0c050301050607110a0e0c0706050109020316080414070f14040e1903051b06 69
    0x42c090791a0036941c2032401c040e405407056100b0b41e61034031801807810000340800e1540740e034002c1d614484030303030410702d07000100b04501030003026088654a04425007040c0942500c1120b03041940c028106424010f00040417450b62103050350002c001080c503c91148028280790403a4410359200102182c1680c10502d0b507001420313004060f400c2a60b03010303140d800690300400b00342d90441c0000d6848445440640c0a40d0003803c500341011542021009884000307842c00324242c10a0383c040e0440e03c00e04c1010881c074001d9100085150a00c1130543d8107101c04102240600c1101822102c8200000806030311100b03030b00350140c40b034902d04120a2616602005071303076010190450f201440e1000019041a09200b664091141d02100d005000c0c100002100d00001c05001075822010040025040000c00c0208030010a515424000801e00e0318000b1883c819601c4070482c0a1428101c0130f862011010405942d21203e90f1403100e1030802e5401d04803036a025480b04200240c0c01921960141c410008046 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 550669568 1250 550668318 550668329
    0xe07120c05030114040204180e07090e0309101b0c06110703081b12071118040b0c1617040f12050d1d060a0e1f051c090206030103030504 60
    0x1908680054800041200c1400200e000003600900040c40703901c0c43c0f48203c0c1c0712410000c0c000350900b91101c10078051659a0386660b995296a44070400f1080d0080c01103178002c1c0082c0c00100700c044a2504200d803a840741002e01441030f038142071700000d024011288a81042400d6401c0f441c0d111613440c184a90310410b008620100e034007070010481440000036203500740c035840841c050605100e2486604940840007200c0040c4c0075014602000c0704410f0041c0850a00400d6a905510105010302500205802c1d50000c40c4044100300800b0aa800480310340100c000302456545503e500c07100e001d120100c85000307040030a5803442c003060001034000f5009540f6600d80001001d50384181c0c40441c20141d420085c40e5170020034401d03079450f019250651040700100b000b03c210005800000d80c43c1d43c840668030010401c2034040c80c0c0d00f800c0c61000940040899001001c030001100e40c0a4864002c2c11398018440030841e00280d20b072489504004081a8041d00c5946c80396140c0c0f40103819034000d406075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 550670818 1250 550669568 550669577
    0xc091b1202090a211a040614151e150d0e16030b0a0204050d06020c01050f070912020609060c03030a0b0a0302011209060624030f0c0807050a0c0c0e07 66
    0x3040c0030841a403003140c5240e07000030142c09142e490403400c04d00801040900071226a02c010301500450180f00041e6010b004030401040f49181c949000c0c000c980070300b00e108031884031440c10000385034000c1101d040c48441c1100c2110001032141c41c2c4001e200f24116410f0b8122440340c041c402e05c400040013810186200070402d100c10000140d429035600c0701034400710300e00b4803050750403c08900a040c4843d00800302d1000989002e450b4070200e144520600d00032075000c0d80c00038800540c01400c0c0310303040e08150700c4441440c0900301128000d2204d04079015501d1203d000140d100d0456403484100c0b01070740009080b441d1111102529035803240c000720b0360313035410324145000c440e903510304002035a0030390707034161155080b000100701000020300200d40200d5206560350f001140381c0c4100f9401c0d103110102c104d130781c1d402071801c220001c0944045880c903034030040c18141111480740d00106040e9100c1100d00d49182c5810800d81c00301c902c040c030410b01130440c14048501042248100900030320460701c4d6140c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 550672068 1250 550670818 550670837
    0x3050d0b1323070503011811030c040311010c230a02100c020102210d020a020f1606090501050705030d0903050f03010e0717041a07020f0312010e060a0e01060c0c091b 73
    0x842258001c00f00c3d40d0310001242000148100308503150f101818094038000050542c41161401c03905900558155210340700104d0204100a0700760640070312503c003807912000c00300c4156142c50f42240c81b2615a48030811441c1e9810400004101c0f000c072560300242400680d0060003030250a401910000764014041c1d002e0035082c130070102c81c410040713003800c41c2110b02d060b8010742000000d41140a0540450164211111541030204501a09135605441001d465840d0030000340541a4a500040c1405401c3c4660004120b01005954081c140007401042d11516854216407501c03554405120070740000c0004600343c0714120b90184150441e440d07001007800000c4d10503040c4d503800c90f4001c007021084480300700d4a006511b03406400211a00455a40381c0c0300240090542e005100c2d1100d1301000c400041110300641c000383e54000905a80c0b10b040c0e20704103540d90924440c140908000d0024824002c4100b2000310340d00401003411003005c0100d444339100140400005042000000b41401d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 550673318 1250 550672068 550672121
    0xd0606170d0f1715030d090608101404090503130b040501030612050307170d02041403210304080313080705010f14070906110a05030c0f070e060a0303050d0b13 70
    0x12402840d807407915504150709514000900f0b0140c0205020160b503642c112890b11520208202002c0015030703155129150700f00400204841e80081840044c0c0204d40000c22584000c0030702c0600080b41a6408240c0e107401d81021450741c0320316001c088c1140b103040c3d000140031140c80d0284c015504241da0a20409071b4a01c1c56080c42000d202000c6d01540040042c00e000403071020800080d102e07083c280e5801d105850300d002c0202e80040d444051800c07182c02c0e0203009890140103080440b08880302400060007440c0c2031a800d8040100b000b428080300001203003442c01c1c120880084c050740725010030303a16000c030700c2d00f18060f0070410301050545003807144510341260035030301e468800e03807003a07561030b817150b10b0113404845007401d0b0209083d041c003070302c440d0a02094090004004031003206005101964500c0303012032804021747c0c045003821120b4000d101040e03807541d011004a0741c00d40340241e214904a040800141302044429034001e03d4031003107a002c107140e074101a0084c1d03444401031151480e2034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 550674568 1250 550673318 550673327
    0x120515010f030206160212011109040506091b0a0504080a0606062006070f17010e0f07030c0905060304060e0a0312060806040f0b09031b0303420d0606170d 68
    0x1404000e511000c1404080780485814071440d1719107000603e44040d94040c030340e9041c02c41e080e100b003260107100300181d0000c01c0d0801d07016541e004282a501d086c80e40c900b515004117800003010003509038200010714201c030103101d9010b0742e000d4003005041d01c1000c801031070103d00501640c46903202045d0b80345004085202c0b0b0000400e054800c99029148030794620204843e841420880d403814002d1080c5201d170306949204405000e003025030182d502e0390904101900707540c880109110100350a192a030743c20701d070380706d10751600325401502c0b0070382c50b0344071460580d01902c041c940e5428144100c40ba64414035034000188a008503540408100741500c0e1182643c482030200c0b40602490b806a5074040098101c84020b0f501c031040308192030034501d81928540411208800584c49540040140100c0520030007004510301c03091085090302241303141c13021003194502e60300c40b80304600140d00c04110351a052501c150072075000004200a0781c484944c400340b140700f8844451030f40300301456201da25000307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 550675818 1250 550674568 550674599
    0x80a020307051014030a02030624043006150f300b070207030b0f06240c0102040b030a0b0103050f04060209041509050403030c030501210c12051501 65
    0x140c09812030605000c1884020640800f54008000075220480c901590450240d405001d20700c1001d41d5a0a0400401c40540c0c3c1c1d00c04200742c400141450001a900340341e0071030341120074101d69900c03281e240c40c0e1414030721200350940c1c03030f0040100d9049008010702603000c3e41c03c0c072030401c030036405030340d110780c0400d03100c11941c040e284c00c501c07e481c11204452035079400049141680c40243c0007001d42a901c840d14403605070f17000d10150b40846428420060001c0105031b000c1031600601219103055000590340c40455001e81201c10107030f90002000130041c03000c940b407041c440c000075541c0d542d40f40122031680d802203500c1c94040d440c1103412103003503100b80a01802044000c140203c55100c680344d030780c0213600083c02203901039030b109444d02900241d8001c01c0c2c021b050120340040c46203458100501544c07201610841054034000040c00030b000d5444202d0b0070007900721149410a4418032b061130f59502c01d0f0f00301900c14249a007003e8204580007405105460301451200348036640d521120502ca690f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 550677068 1250 550675818 550675823
    0x6090f1017030705031204030e01080f13030e03161e0605091903060614010e040e030f0f070f0b091011190201020706060e0619120f0302070b0c03030709080a 69
    0x20242007010990400d02a030038110014140d91030802660364442ca1a880101c10f496011005410002815000302001510020a081622480c40c00d940140000c0e40c0041c02c04019084401a03402414410403060840340009812503800c0444141c0d0281c041c0c000f88121101034041e440800c2d5408851003a0384101d0309152100c42c20859094100302c203031420f502c04c0c000c845241072030020206525000302c03001082d40000d0340c8894000d40e400100b0b0303507082e26000c034041d909144400b1080d540000442d204101681d03403890704e407213508074030703180c40c1c410030b0320160168800340102d0342442108212a400780544c01e0840741009401c10100c1c0c280c03800682d400503a11000e02030041a00a480f10342042080175100042c90101039079503400031034040740c00c8201d441c2134060401c00030342000d114803400d114030b01c0044601c5600e410940c80c01404401c8000340095041110b6004250003044000c01611041500546070800c003500307656a90030490b08480019400700f00041c0e5401d0206c0d0003040541c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 550678318 1250 550677068 550677091
    0x9090313051906030b011205100510030e0c041107080f040521070b030a090b07020a150218040e01180303090b160509010815121e0c0a15020307020d0303020306090f 72
    0xa1a03c10103030700030b10302c80c0201818011746100c0b4000740245846401d01c074941611044007114100750911a2039400c0c07460a10a16191103501c0301810400105045100412034004c1078a000b0b80048200c5800b40350f2005124050101d0303417041605490000e00b003581da0683d082c40744141d80f0324044001c44010031171500150800c51082c0a0f4800003801143d11260360500821884200c0c0d43d000150030003101e0100040e0040c2c0010420030004080c20000002507070819401c00100035801310f510050b507012607128681e1548001a800e42c03c0d00000804444042585860380302410013071f0103840c0111040b03441d032102000088022f0302d0a44040d58000b065981c0505000304c0800540d03003071401402c001c3c0401e203004a840e4140c3e450000010290140e0702c05850100140c0400c800d07110380010104059412a600110385529400c40001c21215200c1285216443e8020240e0a510374518044d42041d48c1f88404c00601d41c154008500580d416240428699550b030a09041c0d180d017a06d0b01e19045 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 550679568 1250 550678318 550678369
    0x1e0105090a2304030806090a020a050a20010507020a0b10140d060b04150815010e16050405030601230d0203030a050a02070b0c061f030c0611010b0909031305 69
    0x1124540c001a011807895181014401042c0321103822814210f90031400244140100400d900703002c50300ca500729008103015400e0054142d400f03410313405000c49a404101c4465081c0d842144100005030500032070000070880d07800c0083d0000d4540c1d01c4030000703480d03048403000800c0000c4009440002204c039001100d0441c030706080b00300000351220440540e1502d03103402c8d00c40a507603154860601503100c0300a50706585864144178500303203281005d200c085184890010490310500c000b2403a80f0110010544044d0600a0410b8030107008907044aa01849031500100782c824072400c0d072416102e100342c810820020420200203d15507241402500342d00248002035040c3e021308094480081c107401a0343c04692102d9006415411154800213103600880610400c0b101040480030b4980c1c601412650351411034464040c25807180c40360000300603107920708084595080d0f02074209031034010000746d014104141150b81d43d40085030111002d0714280c1d00095035140c0f000081c0c140000071240d10091 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 550680818 1250 550679568 550679581
    0x5060705071104060e181515010903060e030d1113142b0b06090403170a02040e07020703060b0d021e0105161218050915030c181e010509 60
    0x36900141e40484200c101e121000302c0507640e40c0124005400030214022262034038040401c49041e09843c4010a50801840b0b035101404e44844190b200043c0d162100c44211464012201d60303d06900103408140b61041d14010300c40003200a2a00240503d01070015a54140c100392040c815000750681400d40302100b040b00341520009042c40d248001d0040108800200c1c034903450000c0c4003882244858040520001c000702c51410780d0708000f060fa1522468603281e0303000707050910b41c064050522495200002d6489000c1d4040714081c0c40006010499820000406540d030389550008540e1581022540c0c070315403c200840d43c081c00d4005260428003804840103012940482c0040ca040000c2003000c3c0d201c60941d40c002a484c0c520030240d209100071010001482480080380b2441e038a00c051b041003000b40e5510f000c09030000c004074825400901c40400107031030401d40303000b500e4121111110041400301380143c460720690400e04d1042d107242046000152410090081c25400025240030510 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 550682068 1250 550680818 550680827
    0x150f08062701020c0703060f09260403060c0c02280311060c0a0f0b01050a0b0d050907051003140c0a0906080703091a040218040201020706030c140a032007050607 71
    0x1540303009111000018041c6039841400e80e44080c1c4909040d0784440d43c1041001010f210321162110141e004110355445540d992a4002c0001007041c81c2c000e050072800c0040180c5e41c1180c005507400081040140c0c0d15007009401114203040c10b80c07040d045480c1141c000011014402000407900c3c0790721200c0c0e030859648a001c940744d0203e0710342060050054103441e020812005507114010600501071868900e07205180c858140c12450281c0204001002440034600580344050591076001c1240c0d80d854071602d1514020b036101d1a4004068884903420f5030701640410010444110b0044c0a5500e044484005116102800380042c080520402c03101e880350114541009003032801050048030740e00c81c000681c0218072081c40c0c80170b40209010461801c1040b10780b106043e40e021019524103500041e450341c08510900302030580b90050004580e00c1924803051000e2080b110750703107030340c1c00d4600100148440d050b002e140e8018902812107180d4488155800194081d00402d0250b842010489 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 550683318 1250 550682068 550682101
    0x1e0815060102060f0f1b0705010c0e0312040b07080c0f0a080307182139060305071d011202070c0906172a030d0f090902120a050601050f0706150f0806 66
    0x6d03030203030203110300400502d0a0080d04503801640d592058008000303410141040a991500911140c0030001000007680f144251030b0742a4110005e95200d01c9000c3c00103007060a0b4140205c064041c040d02e0740f08002c468006540600e29580d80c0301010155900e030883c402a450247c150b482d0404842c10702481400100d0313451240c89104503600c0e14118072869164108840d0242c1c01840d1518014514900780000c03c0c002060585420322843c108100050907000d5402845030050010305051402d99010303240c0d034081c0211b094030842d652015420f01c2c00041c012802100d186504200e0009001d81d20414404100c02d00d0744080c02c100460b01c80e0040038a00d08881c01c007a41c0250707000d0100b040c0d0b01484411550400350321401018180780c18010040c030784030703009402030b244180103103540f4402015a099020000b6200007c0300c0d190300d0010f9a90703000d100556801ba103000181d1504014258000e0201400c070021502519034448180f849601c0160180c90000d900960026034110041c84203a0b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 550684568 1250 550683318 550683361
    0x60603060504061a130f030302030705060c18010f1b06050f06091e06030705060d050411012f150c0c0c0102030a0c020103090f060c0e03160f1e0815060102060f0f 71
    0x1040b115500d00702d114021b0b440ea4019000758001180d414107022051000a40c0a004039240924000e01c250201030120400b800060400010151581040303000340c00d0700000301b02c40560002c10a03017928013507018010454a46000640350303070218041e8104418850701a402c418081da61050350282004a4050000c002c680c1c54807a00328000b415071125001401c0c2c14529183c04032301d505d80b600300096003140700f60010b07040000c0900d4080c04102d20246030300c50940f0800c022076150b1044003c90345881012045010114000e000344945404814020201c1c0603c440586051003034030801685c0302c0c014200303c9004286371000441c0190310a83c003640503188148031820b81c2c08042d44400080307035450000200032660600c6c08203083d150401c60000c02100140900e40450308202910407080c07410311443c813221035040d070082902c030703140c00207403014000c02411603a1100d8001c003c243c07260020f50f20540540505070100f407000340b0a04000c3d12038402c0700e4a040c41501c03000300341d141ca1444010301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 550685818 1250 550684568 550684597
    0x17090106031a0403080f070503071101060f1217040f1a0c0109030f1106060a03171e0a09140d1502090d0501090311030309070b1b010f060603060504061a 67
    0x300005681c0c84050b1600182840d0501c40c0d441c083c03401500c3c0650142580b9244038241041100c090360180031aa4031003114500000b014045e0407982e405002207401c0500c1140480700045505c0195002058185010781000303004250b910080300254800c90048841d0400350420911035907040b0110030345105a052841c914104800d00390a0858400c10402c400103852652142c0d40c0c0d90f40300c20703004100710300e810180a181c1031050014031105d04500c07000b003420700410303641d056180c00310701036803080c4082d180041c02c1c4503582e11a80ca074035407100b118bc00224414034004545030480340314001e60001c0c0504041e8403c540c03902c0c0e825106500c00c01c8507007410307020003001c9480d03102c3e850200c03c19440b4100110722080a441d01031322440e5003641081007548184104030040c40f0000d442d00480325400c60642d61001100340d080c0016003d00c078490455030070700300710400203081540300508a41040c1c2e81008266104d604201c20344845100d840d09008003010203114040c00400180040d0046140307 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 550687068 1250 550685818 550685831
    0x301052811040308070c0e06180a0906140c030f010f0501120b1309050102130909080a0c1104020a0503060901060e0102070b090609040c0c1a01061710080f0a11060703170901 76
    0x160744495500100c001c443c400418141004203240801c7c8558000c0800c4581151888070003071034140454000300f403600d002d43c503866a0030502c20b07141d000c400c90300e80800c100145440e0900a251540c0d000b0345102211081d00400040e042220081540c2601c405035144001d0444500100014141c44045640d20111440b05c5948410051140003070b01c0f17116000244e201c0619074424580d0600a9100c80803444c01c00118070005100c00003220035003500e5042081302e0341050b04002a000d802c14a105800500c0042c241203120b0300a0051032050800329041503150b81c8800040350b055414044550150380166010b025503210b94000c7c0c17401c007401608240c100721a8000003401c2d90428130b500008075101e148a501440001000c085000b81d01110400b45945483e000600380a6840003a44031000c1cac800110700001c0041d001040140381c0c04003281c0346004544001c1341c5800741d0400886a01d40341044120b10b43c1070103400c0c1c40328990952541034802200d021038038002d00c0c004104c0e1906560758030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 550688318 1250 550687068 550687073
    0x1b030905031009051c09260109060501030209060a0e0c090d060204060c1e0807080703020a152f031f030b07090603140405070527010e0603010528110403 67
    0x864184200100045488803071818103e0901e00c040040f00c160b1584c4284644885e40c02103603001c111510340802d002503071403213040941c488a09981c8002e49500700080340090000b07640015060703a00031a448030198580e607042001c0f0200c144141c1ca00d110300e05000419080403132003c0c00400c1c002424884a402850340c03103908031380c019042480821004040c0030280000396000c091103041e041d003058290480340e01d982a00e80950703c4000c2c051031000942d002018401d06c844400103501404d051140d01c4040d5241011b004035506254001058841c108202000c801440b481400e044000e0f82c03941d1a004001c100e411103042e009550201d00c5034000000130f0140601d0b510403096692603000c02814600001c1c16500c2d0002d881900605038405e00c80400c5010400004035581102d10180e07032440100414075540c402150a409103640c40c0000400307004011020307200b400c0403030080140b592071900003541c4041060b008203280c151f000c8005016003150780035110103100c0c46010380c240340c2e43e41d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 550689568 1250 550688318 550688323
    0x1170709030c0312020705031f0207060f0e0c040c0c020f0d170a09090c09081c09080f07030b090a0f030809150a0905100608030a12181407080604031b03090503 70
    0x42e44120344141100c1c01e42c04d8020b5045c0201c1c0e020f000200c0242100c1c00d141c612400d810000704444883e850b0340061001c08110b010b612050030075400100c24010b21078510040760311041000d840328006e40c10044c2240d000d6109a807050308480c1d00038402c0400080383c2c1c040c04801100310000b00c1303500c650819032109441001001d000e603070350b042c0e84203941c072070401c0c3c805401d0b00c900b00f92803c240500366606000102002c0707040e00085035002200180c103031301d2002c1141e200d040380d40456100d0081c5545540c1210003c04c2c100c0959015204259032134640f904030550b12004c1020241401c881c140002d00000d11540c041504104002c2c00c41e2100c421420868600405c00d40303140070302540c2c8108010801805104141c0600700310002004001e140c90405500d07880b4800049040084035554040280e00c10f602806500070200c100c84020100f52500468000b018031851110b4880c0440c00540d83e02c00040320382c0b1660f030603628050000c480500003040508650411001d1182e1041c0c08611604c08 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 550690818 1250 550689568 550689593
    0xc060307090939020705030a02090c0a180f0303090f080c0d1506060e130c09121a0708100807031101110a050105090d0f09050a140118030803040c05010302090117070903 74
    0xc0c040f001400c54a20070b0181c030301a0340e5130000e0700035000701c0418405641d07040d0b00c0680c080c0e105d4584035643c80c406c4808407240110603040c00c6c003017000e44001084504d02c410302c40341682c1c03094a80100050315440c03002d2088056210354100c0c1c1e40004040f1002e82404424400304a11503010410246086586441a40c1d00b913040200041e06051000c0c26a10303060003d4140e0301d000140821044400350b10090a4070715034060030502880301d0500604000c100407480010046480c80b00400b41880e113801003001d0400e44a0300702030300c000c2c0400b003950b85010032484c5c00c03130350f001204e0540996403200665080309544403900450041208060100710300f80111f6101d8040705000c0d0494089540c40504041d0781540c01108000c1101014020754440344c50072800d444841a000d440c8080c01c60040720400241c03a9882901340d000e1500000f041098005540254491520010415103810044080f0302550007540d00185113400300d0400100e800c030700d45030442c40b10b10b41a085079440b501d6040c80d1490 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 550692068 1250 550690818 550690901
    0x3180c180501050a090c0c3f020c2701030b16050a050702010c0821160207060815150d09030e100c020d14030f0c07090e070e10050d060c020c0603070909 67
    0x1800c8400c0c01402185441040310742d622a08481d14071a0000080d0b0311680d04402074020404400c40b001c08242c0c8014400e548bc40c0f0840d000c41c150f03100d241c4410440c0082e588a48a00e0f408044820018051401e0f181c2c10402907640b40c0c10b00085400441d820b140303544042d28a840d0410181e00314081c011400c0e01c42a0040b5030101c0d050420078030403282c07010540120f00454108100170302c00150701c80411600000200d203034a41381f000800028021105403901442000b000142c6c1928483c884e0b005104440e000fa20350341c99840010080c0107a11a0440c03144001507100c00d98000146002500c01d03031154000d04003082c0d010001c00b0414656408942e100c982a000171454041c15141000080064160403209001d00d0800d1050591b5800e25809100c1418855100140c8075181000c10000200ba000300b03000d80d501d0702401c06900500c1d01118810060250000c1e40c100d5040c184116030223a5031039034801e603095107044100c00c0100440c94442040c89000c1d4021107080503006001d02d480d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 550693318 1250 550692068 550692113
    0xd0606050a0f030e1005150d031d010807050a03020304050f0609010f06090b0a1502031905070302011b021c0210050a0b10020a0f080a03180c180501050a090c0c 70
    0x8008460141c91200d01c0e002c11800c05013418811445184041007044405250700c0020800fa00c0316514802e0032080c031101990040080c00c6c200c4107050307118841d0b0120140705c00241c0c050003220303001141e20340801c81b01d030382c089042001942c030207a200e903004607403045c0504140c1d500d108410080c0c5041c0841071b60b0b00d5055079120258009c40c003d00b441007000404d0141010000442c0d400d010a0350601d0512800b80d0307240703007041002c030380750b000340103da400903103110b180d495030079080e2006859a004144254010f40c680140b0074249050040c5a518001c1680c004103148080303000b142800000d10030045045003e40d1200f00c505081030b0044a018448522000c1070008081c0140040c40040c0012082103501c1140c024001c50b03030030764040c000290410442681ca4441c8503042d40544a500000c58140800b410a0414481640c0d900415940440840d018005d007103c0401d09891013030089661040404104006080e03581d030101d6a001e40c0360038442c00d040002e444042080324016145541c01c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 550694568 1250 550693318 550693327
    0xa0f080d0615110a0c030303090206120403020109150c140a0903080408030306011716051602060315040507030902030c1315030303020a080106050a05070b04140d0e030d020706051206060d060605 85
    0x207401c000910483c1d19104001c11050a1503140c0c0506104241701c042e0500d40e1322013020065440d25804c9a49011400121040c541403e1800a00900599005030740071200315660807101e81d0240101400540b81e60780e481620072140d00248141e60281055809020910400100058455000c0e200500320380707000d5612480c10b00005842b19151000020f207541c64075040008840015141401c1c9030103c1c500140ca03076200381e0740d41100014500019620150100070442c84040c20800f01c040c079401641c0a103c25280d80c5002d8058503d0704000a6242d04031495600710703418070b00e03030701307001c180d9062404600112070b50704404200d4000d0b0000d400107134000846030034480d001003c9900601e21440c0452501001c400011305034096884000c2c01841c1c900042014040c0d07001c8403046603080a401e03a40a4142560054101341c4081c841c1c0e07000b0b01a0440d600344190010038802d04031522515100e00d0b11030b003401c0908000f54000c0603079900400c1030000d00d014942d94800c0c800903214030307102c140c0d44 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 550695818 1250 550694568 550694609
    0x140609190c111501060816030213030b181c0e0a0306110408070e13024b030c03060f040501091b08010e01050402100c05010f020f04030b0108010e0a0f080d06 69
    0xd21415082c3d00501d0010b200040014552044c403103640711000210030820002c0c2110120080d02c582100007000811030301f0301000b441036040f019409480704010310f1666400c0200101d40b586100910700d40314621100000310020b009844102e0215001044980c1041c1c403a40d51004841440c2d001c000d0040002c18103001c000000c1245001070034001101100c0d42c5012907148950b544910720080c0100c02c0340d2200341a000054030310071800441d5624414044031845d0002c4400c0080507940003648070b45810300400c600700482c0c0c041c0404409400341006a03200d00850094070000380040b1001e41d614840f000102e84d005030450300c05445015040b980c41e1420198500b520018182c0a030076034540000d01c0300503601c40140250442c840d0600000b44031007814242d00402c1024100c03800c1c2400080e40c44e0350071030b190005001303481c410052a01a6601e4944d19800c0b03a121750085240ca60109600c080410203282c8005440b610400f280b42c0f526450a9100003030f07510640c0268011240340044c042c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 550697068 1250 550695818 550695823
    0x21c08071a0112021507170a020d080f131505150f01020c0d260f04030b1003030804151d0604050c0f0123090d030f03050703140609190c11 61
    0x8105601c000303411941800380c01c1ca02d24a031244000d101d60b0400c1d643c502900c0c060340c1540e40309500040100c8038901403c1c540d0b03150754407515080d001405518841c0400e24003605000b4000e1022800210b4140d60311015101394481035081507502c848500750400000c0314502425100d0301810b85603030640300da10710501c2091661405500c1c1907410425040407982c8484043c00d8009821520148410840300301c810030944004001120f880030003d0710887d01c0040c08000d208603803107000320132010780c0c07850742c842a440b50381d01000740090313509001725011403048125903040e0b4042400c0060543d80d003201400413483c03240c001e03402c00d0700444100320921405220707402c680304c010b42d0584583c003d05000209540914501540c0071a03114036110203a400590641c1e000d03610180017100280800e080241030128508242c5001174201000601c0551090140440c11801c0a1102402c0d403551342c100041c284005100d00030a6410540c590404a5640991186d115040d2194012003028142190 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 550698318 1250 550697068 550697093
    0x30705031c020c0a060c050405041523090a0f02090603130c080c100503090a0c06050c0613020a030605190f060509010504110a20012a090f060c021c0807 67
    0x69041c81403200d000316943c0030840030705072030f400b8800040c800f140740301c00c3d0394a000c0c0d40c010a800510f049910020080d1303130440b42c03003070307c000421201030301d23001c2201c002d20440d031120300c0e0340c1001d140c40205940704042d0b00210344d1882203000250030800081d01087c2307103170000c82c2d1002c01025191110b10a009003483c5242c0609080405071400458400204846100301050315041040000010b810f0b55024415541742603030000c1c440d6401075481c2002842604101e0400700c003030044102003203d002600c5140264203501a0a48000c945551102da00900340200040842031985001010041052290301080e500c00d4100007a00b43c04c020500c454004160490350045d40703400c60400001101009a41000c80c040c54154a000c104268207520059204c41e400010340c280b00c1c0b00200d405000307904c08081c0e900907800740391140154108442410152191103c001f05080c4280102c511400c0d8000d4075130f0015045a50094a002c03c001140188603030a658422011404100300072581a105 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 550699568 1250 550698318 550698367
    0x30e030610050f0d020d03050a02150105090703021b0715110c090402040504020d151409030a09090507032d0b0613060c0f02040e060603060a0204030c0b090406050303070503 76
    0x100024500180c03411000d2015005181c0b051005843c482400e540740e0b0318a80c000c41c0e01410501030510782d80b0340a0111380121000c1d101600802c2450300b249038841042604884c0000c06003031050311241070a400a5102c28100b4005030160171417600c0280702004400b00030318503c18403078496401d4070f00c01020704040560722441500700350020b58441d9100a0b02a0300716404980000b0162030741d00c00580308050b0385d03000a1100707800f00100c0d00340b850107174803250601c1e51003100303c03101c1d55425140a84a01c01c00500002040e015041031041520030340c80140d006003107081c00112015201ca841ca1302c88c03036101d40d104140b2640310b84007210600c98080c1c00f030000c00695525040c0720b2540075114950800b4003401c001c001400d1155010302029402c100340141d0040d00401c005c2e001040070340c3d00ca040031152580644600d9000c1000c24045100b16000c80742c121603070400d51410482440301c940e2040980b070b6401030b1a0103020a2a40d401d000034500c0301d1141e0011642c0f03544d003c0900c5009141030291 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 550700818 1250 550699568 550699573
    0x20918160924020a051207021003050705160606050d140705120d0c0302030904090f0b010806060d060e0a240b0a03022803171b031305090417030a050103030e03 70
    0x2004a4022030180310200304042c0401c0c090340031010300c220b16000c41410080d10a224041e600b40c448510750000b0300e1500e0099450000780300d0324400540554605940300d00004030104507809a15203d209041b505a2141c407021a595944800298180c002d128080d00c1c0d18280d4a5172054812040005500509061741c0250808542c1c603603950b00c5540402d410024400b1114400d020944288112501200c0007001005840094107181c0d0440c0807201085074490300a4001042c840710000c2d0851042d03000404520b1040c22503a01d00014240c44507140e0f41c10704c9070312041d80004800305484007c40260340780908010140c400600d0645a148059600425203404184056190342c2c0103400c065180d0501c0301090913081c1c8480c0c41c034880c035900180203285800200c0140340e482c40b00416030309502c0c3d03400544041146048a840c1d2142140702d0305407000c08901007206091012030300d03601c180115400d00d030f03480c10034807280100d5104841048010b60354000500806400500070544004282d00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 550702068 1250 550700818 550700837
    0x406090b011418030a08091327030e090903070b0c0f070b2505031005040b090403140705060702010b1201141801020c010603151b02190602091816 64
    0x180c09103007110b0600816041c005402c120308281c000000441103000307402c54250703001606150002c0d0704415141442190011031000d82e2918038010044211000203a0010340c42e0900c010b1000c0a0710350740100e061042d400c0c500d5045598900c0654440d4034440065540e98801c0e18043e5401403000384882001d46040c014469411001d8040d01e95507036004003c0b503200d485680c500d2118000d403000301010b4560030000514003a0f40b0101031409000e040f00d280101c2c5840701c007044152050b050703045412030000d800241c04603114415003100f48592400c07151074089035450349414180d0880c4c2080143c2c1d1183c484110a0420344000c25504e05410003c0251052412031942c14040c003a008e0030070040c0081210f86c061030294100c074104c9008000130810155249030404040340140000e28a40340b4040d8a12004000ea010760800d000541e4083e00b040700c20450980f82000180e01c007a5881f039402e0042040780e0b1952180c0078403003150040f00640c60315010340c200c016909003201d1070081019419 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 550703318 1250 550702068 550702091
    0x4051501080309040b0406170d02160315020304030905061b150f16020c0a031a0c0906040902030c07020a06110f07150e04020c0312010306060b18040f0b040c02010b040609 75
    0x2041e00c01c40f1a084a000ca4000300d5400010054030701904502801403007070107100300c43c010000c0e490015003200c1d000d0f1980d2003200c55800410812a10024160109410164945020660045a00034803034203060f0070441e2a232000c6000c94200042c1350707034203200c0210319003110082049000412103d4040707080041c50440c1c20021070f44d00140c51000d00340d011040d005456402070001e49003480307010b0280031100d0b50320f04055041b07120030f440d040c0b903008401c1e01083c2c0000c410021075202400181c8610310b13003460084000e00942c80140074510305401401a000181c3e940c0781008010003090b95000382d801141c075003031404d084420703001c080140c2c01a0001c1000e5501c030300e102c1e000304000e410202c01180d150404207010f031082d00300040b0320f80400600106c00b0300c4003a139900c0c107a9000c0e01d808c10003291200181101031040c09440d19440c03140544001c110b14194104803484c5101c01004643d5411a502140980d504030169a02607510703456440304504061040d8402070080756018000000e043c3c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 550704568 1250 550703318 550703323
    0xc090b0d060207020a230414090604140a1707110a240c060204270504050606130b0a062c10080403180b1b1b010e031f02030405150108 59
    0x1100300a064580204100701555604420b5600508403040311440c03100e16414003007403156248505074030640c80c000d031446446161914551040550704014501901ca5881c0e10f4005900340c540500c15204050043c030020b445c1c081000d81c00155440c2103616000303940392401a068051541e2401001c0d0110104541605551072100c0101d6851000c1c0009080340c0e811584049ca0b40030180c0075900014000070070408004443c8801003250740510140740c16140140c0a40c1c006560241c4203070302500201301075250080000080d600c1e4200c1c00a99900070074041004188140c2c0060041031182688028075a82c10320150344842000340308a01e407812050000f0b619200400302c501c104203801c80042e0401d0300541d40700c509800a6000d403d403265503001c01403180d0307000b80a01ca0081d5100c2d0317000c1c55044030000b4055403042d10b000540040c01d602000448100901c001074907458410501001907990306111103114440d06800c0c05070380c07441c0c00d060161034046c81c4240c000203107200c0f400400c41030001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 550705818 1250 550704568 550704589
    0xc0102070504020901050d05010b0c060903070c051009050301091208060301090c0306051f030609061401030201020d0c021f0302030a0c0903030807080a140a0506030c1905062d04030c090b 82
    0xb10b8006844590728001200e0501400007201040f5107080c00200700c00803814042c0180403200b504403a034643d505440e083c0c980c002e83d9001400700380400001d119920344160182c0080a0030f140c58440a41d48400190170355544080503a8a42c241c84400031f00d096100f111a40e000788107030000e022600300c0307a0320514070040d01c1c4001307882c407030f525400325100b4601c80c0c50114070350f480390030b5201405449060520003040c035680c0c1165a1032401101c0120341c00c0c0660001c2c1280d40580141007603113120341c002e480006548600300d0f48810b00855807001400a9071501c01400702940e001612890850815012510241d501c00c05000c900842000003d501c0002e031039201c0ca07545040c0c0c42603100c4007502c01c00b800d4592140f844c908900400c200c86e17841554001031003980100c0c2128030317031600d810a000081c0404800e80214152404003800581000c0009101d000700ca07012040c40e4009901d401d510100507042440e0341d00000007010000c0c8800c6600400c05072408400400417140414005004c8010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 550707068 1250 550705818 550705829
    0x280203040f03080c1c1833020f031317030705030a0f0504030b0112151b0e06090a03030801080f06070903021005090a030b01053309032103180c010207 66
    0x42c0c107044080082c01401401740c40b50410510808070200f0240c10311025944540031650aa0380000d4030708500c111940c192000341002d0a10050b07000b03030f0020304c2c102420003d402e61103801080600044200700034640201e1111000e0061820b000d01d0601c1c08002c0d03602441c0942c01030101c0004150044216805280d01d4105000a101c182900381da41d400340d81c0c07001d02a40c02010002620303158a19a0311490351085420700078888402454004840e04240300814803265003d0129006000d04650790100700001c010314203100128002900c0105650012000a0344050040103d04402c01c40700c4242e60604002d8681480c1c02100204010000d100c007a10442c20580144407460043c02109d80c50b250150004d07150640b02d040080604100f0701c943c0b0301a03100c021804542441445c20751000c0075994030000540784901981c11019040507a1090b49070041c0d0550103000d041c1c001030300d00031440e18030459869181944030381032071052508000d00300750401a0389502c80d0ba4040b440c4021743e0f1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 550708318 1250 550707068 550707083
    0x4050919230106050f060a020a03050a0c020307080d0818250b0a0305040302070803040305100f0b0a090f0b180f04150e0304050a0b0703050f0c12280203040f03 70
    0x1021820311880400707004011030616000354200d1280490103410403026580107561220940c250f1405010451103009003200040e0049444600000c1c070403030003820941120b103042c2c20080d0b00c50300000e04201c1a42d20119095001101d0068542d8001074151360103004000030103070303401d1f0604039151a4028090301c842c0c0d0800c0d403440c0c001440c3ca0301134040080c0c441c03c3d184a4031003224070400741c020002a20143c0140c89103400c00103502c4d034004100d5099130343c024007420724010f000c0981d0014140b503000c0f102d03003203844108280309620703814441c01c000d090085000ca00c90a000080404856404ca40c85005000d025910501d24000c5132407a031700300001044901982d5030b103040000d42840c07041510784400d410032103646261407000029100350780d82160300003031413599425600e03018801e241005020030f00c01d104001d00c0d484c11201030400d200118080c0d0358074601c181c011a1140d40700707480f0800c081c2c00c9a0140154903190208510388010b032400110b01d0310303003002d40c00500d89185100c020080c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 550709568 1250 550708318 550708363
    0x1c051005060a03080705120c01140c0408120f09030102070c090501050f0d030813140717010e0a0f030903020d061d1f0207061d07030b070318030e0103150e15040509 72
    0x1c0400007c50070020042c00b45444e041e008021a020b002c14138051407100e903286000c6502c0d58001012101207a02a00007844220001c0b070007445d6542048448000403081400b13130b008192000c0c001400c1d00d0b486162100e40840c00c1850710806ca400c10b0304480d0140d600f103035001c11107855420103518480c0e00b40c18072550642e100362000d1000009248002c1c028004016040c403200c030300050120070b55210003180d14030841c0f074000103030807165a6500744e09183d004484010204000751441071955000e46040c1d07110344d4890b00892011014110200d035650398440c1116074aa03001c04c0513840210010f000f5200c44802c01d01c103000084010804001050b6000803560f0400090350300c140320b0000718840f00c00c08030038820441d5881701120b10064903c05100c00026070f42034403d03c0352200c18403010142407035040490708e044400c07102801c410360500d81d80e20204400c1e00c0d081884240205060702ea190100e19260401ea0070341d0420420f102e0090342440c040c40400d1001103a1320781141c4c00c0d149910140c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 550710818 1250 550709568 550709573
    0x151309110301090b061509030a080f0403050105070906140c060a1116120306061701090f0b031e01060b0a050d050402060405090a09050601170615030c1c051005060a030807 75
    0x3800c0090190561642c40c10364400d00300708030105214820b44049840c0e42c0569040010320040d4499800d130301da45504407501c0c8000040710b80014090b16042440402d040642781d54070a82101c4003a41d540d13020400c210020404031b6030014401c0e1507403a0810314541048443c0d2083d1f0798910000e0482ca80498451080704101e48501c4103032502c10080c003080000340d4280781400d81e10b03141d240c100c4000103030511a0200d020740c01604011201001e00c124154503a02e007040340c900034100c130800441120b03210850011300b5907040119909465068500200d600541c280d440c2c00c4611030790009081d25810f0210252007038110003981c01280c010784001c640d55031140b002078090301c269007100358414540e00502a103803c0a40c80314100078868800c82e4080d90701c5020003107145601c0141e910443d0300040005040d8100094048a0071501500321092040c0c85400103c407000400c0f4071600700c0c031007541450f0501c0010403446030805a400307810401410480b02080485185010140c14000002101e03c02c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 550712068 1250 550710818 550710833
    0x60815091609060e060f0918070f030506090d080c072315091005010b031501030905240c030402060403020d08040f03080301140114033103020d0206151309 68
    0x1094441003103009040b82c5a00c4954010030941c01892504006030000401d41c0c140144400701d40200205200d442d43e0316038041c00b21101054481e03030014003d0039000111441e4017180c0c2c00155100c0c5014088619041c00507514102803ca41081086407201c20321900352009400ca5800b2500301c140940c84412542c0700c8000301c0840200c0030300301c1c41140a2405180d40f5600c0030340c01194003c0694000c00082501003050764828011214218000c0010584044800c00302078041c02043c10f0220710402c4035101d150400001240d80c0410b40b03242440023501401040e186c907401911500300d141141400d07004194540202d00009014414640c050802e120801c03007034500424249404840003500c0b0b11b080d40e0641c0003071160a01404481c0842c800540c01150341c0d00100d080c07841c0d0182540c0e26040c409108d0744403070a821080c06018074603642c3c0900c002040541e00b50007230300208003600801a000b0b282c0040140040c1451b4050f2407090340382c0c0e075010350610801c0082100440d5908450a00e1413 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 550713318 1250 550712068 550712083
    0x50903030705100902030f06040507270c0e0414040f12140c100b0418120c0213020a080912070b07200d02010b0613030803090a0f030c051006081509 65
    0x4055108002004440c00b00f10303000180e1491094041e20150690084050f90f9140d050f0b9009155400c4003170706010b200080c4a5a40c14030303803181e0016003130800007640c18007290801619500028040180c1c50140d0609000d0502440c8988200003c80d1420761540c00f05201c405074000c12028080942d942440e1040101144c070303c845000c010364624000c18030540e60111600c1c20031000f41400308180181c50588101d58404e009800e42c3c1031440140d584015003034a58010314010305c80080c17135203405a29102c4413100040e511120041e91515141c5010702808001441d03444960b00524003003981c40350040940b5030507648031408154584401030255002c0c5100d00d10b0800d00607203100601c01183c4005901c046c007465680003001880944014071520340f280803401c00283d180c5050802c0021007410042d43d0041c0107105a030030803211960340c1c0034090380d032040940c00a507580550000b8020184011358102e40f42034003c01000d450a41d5803512151122030400c286500b81d40050b915580038803010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 550714568 1250 550713318 550713323
    0x5240f0c150c0304030210020301060206060f03030c03160204110309030a05090a170a1203050c07030e18130c05041413020d0204060602160911161a0a060510020114070509030307 78
    0x103046803030102550100b6400c00c80e0700b50014810840c0c240c800d0182ca1080b1380c141d9400da40a03081aa0700d06050101101c00c0007905a094071003044000c0c512031086c4040e02126000d101c4520f0701300943d0042100b95400b50401303401c012401c20510500746400412204170002d2800c2250300c69083d07800194940326260710152a045d400c11410602d1440410150206c61244081070038040c04c00104500b2540111002c2e06221383c1000b542020074021240310740410401001820030030901032500d414400c082c2c84502140241254490402c40c8091014014040a50f010461034584048803011040050502020110380c61001c500f5501c0b1180c03031782c1145401070424400d155132071000942c0d07011260300d040c484098944010030042000c4c092000b201c081c00c0407041c00c2c0a0351245001030385094002c120344598002d00000a28642a12014441c1911002c00035200c0c0c070b80f105100309080100340000c1164580000c100500a0301000b041e0001264504035031660300c070002180ca03510888001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 550715818 1250 550714568 550714603
    0x15050307061407150c0206102d0f0f150206070905040c02010e0d02030d0b12120a09031403030609010902030f010308090409320f0c04050a021c0605240f0c 68
    0x5010b8601e0358201c5d6411024942c200c0d8240e903a160751150340d0f641d150168031b840040240460700d01030849800340700c110f0358148001801b135685602c1406d00c0e2200d507100e40280048a1000c00070020154160189041d050000e42003c1ca0004802800046540609032040341d660148109047c400d50101a200b0074103811640c104940304070295030b82c3c002c00e0484e80c5d91030400201c0789442c103008580500e40c4400718000d0811742480d500c454001c0c1c020701e584404020858100001041c1c05070f510f07280907030828001d0350340c90030114140082000140c0150b00324500420034440317581100c200072811240c000643e01e8a4240b250002000703803100c020040d00100c5002c002140c41811202c0381180d0310112410305110040d00044942c0303900346043d141d407085e00504988407031410240c0009034400e8440400610b043c0c0841000700fa60801c0b510a03408a1707030740350401d2000d804c0ca12140c0c2c980980400c040b1185003890b52090600d440346142a420503000401c01d111004801c211103602c0441a464 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 550717068 1250 550715818 550715843
    0x203030a081b0703140d18061e09050d0305060103150e06041a011b050313090e06060316140f150d05070815010503060102100e0a030315050307061407 66
    0x600a01500c42550ba0954800d0419100400c541c010340c219440180d040e241e18014840c032640038402e0741c001c110b60907002d0751901c0903844051180e01704092607034400c0c0400900e01340402004022280481c0d8601021450f0a0020011600c00500c0e85840300a40ca004520746c0d40b0000120060408800c81852550720440b0114840d080940c03450300c6000c0a07101003028000b900030012540c6a0300303e8690102721955020344089032030b2003151802038007440480340b800492565401c0441d0701680a991400c1c0d594060306c1700710303178207001b41c64020108400801c0c0044807000d01400e40f060724816420381a541c1c803182d40315511505064520390700c00402074203800c50b1840000d04961b014501528860b490500044c2159015a051038050840c6a41c00400c80302500010360345d903440544039605610400540d8040ba00d0785000c0d401d41204004060031220240c0c0c600601a201035110070003049030051002e204d80e440c00600c2c2c100b01e52041c600000540c08041c0021020b202d0441c01425140c454074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 550718318 1250 550717068 550717087
    0x1603020d2d0227130602040308180102010e06010e07030209010908011103011a18060a0e040501090c0e032b0c080307030209010905090609010302060f0c19020103050709061e0c020303 80
    0x20078003a01030003511a01000d81d6404459280c80d034043d20324181680032900130402100800000703954140c416038005180c151031f40c8852885800a00c28074409101e210008025541e080c00f80c50013150066004000e10750404880b200000c0000b4000410103502003a0906203a10602c034100c004c0c01c0b07000003000000d07000d040b0b5141d141e00174007483e040d00c620070b0385032454200305404890050000c1c2d4821840c4050003c1000b009038450142241044105000c094960340c8078464240241100d003000240c5100b0040b02520225240104911940100b110740e40f213003441c10700315101e81c041880744030f00760120740000b580c0068045401620041c804000c000e51241c00d580180f14001c0c090300c403903584540d10b0f410820030032000c0721610b402c9104280100014100480034003003110b42c4100c0c5ca81002d1100030006c0c90425045155604040012100c0c015941c052090a8103c5032178a04240c01500b06100901094506149101844103a10032071800900c64100200c0c440e07802402d407962405c001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 550719424 1106 550718318 550718393
    0x160602030a0507020d0209130c050103020702010806090603070b040e06030709060302240c030d14060607030f0f030f11030603070f06090308130308040305030315031603020d 76
    0x171a26a801030780d4002d81c50344281450300503012107100a040c0b070550601250708c082d040c14410051400580d03848004298842c108cc2c5000c1200c0d164480800d02d45001ca90040940000102d00450010381e2112050700840e001c404840303c0d507403107011000c02c648642c44000d60156908505000a62030768280b070500c0e98220306010700302031209180074195801403050b08180d640c4c407000001d00d07000b18143c1c0c5421000030344209040c21041e503005400b8400c81700c0d05c10107210020340d001e480380744250400d5001400c6410103001e10808022507d0194105840442c0b2a01800002143e0504000e290384111011aa5014076540c50b580f10992140c0c08051780440c0e1440780000800451413000c01000103510503002990340746044070aa42e104480140c443d407180d08040403030031074000e40f050b1950650703404035070f40100801d41e4500965480303d1209140e018200c4000c10601d000d402 = true := by decide +kernel

theorem cover : BRFrame.Cov 550539568 550719424 := by
  have h0 := BRFrame.cov_init 550539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 550539568 ≤ n) (h2 : n < 550719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
