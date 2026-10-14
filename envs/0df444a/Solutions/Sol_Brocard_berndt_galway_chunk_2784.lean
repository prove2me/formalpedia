-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2784
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:44:07.280115+00:00
-- url     : https://prove2.me/submissions/4c4c2803-6a07-466b-b957-4220547958bd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 500539568 ≤ n < 500719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 500540818 1250 500539568 500539573
    0xc0103150308030a0204120b07031406130b0406090606110105062b0305120f370b04020d090803010e09030a0905010c020622080d090e01030602090d0507090906050a020705 75
    0x204040b441400c029584080344400c014070340398440c84c01506441d10b008080d034044148904020342c55425125038a450003480600010b24580800050741e09900842030781c20b4561103015500c040d842d81e810940c080c1590180501c610340e00c2d110b0003490302c08000c60404107982441c001c40c1203030410040002c20814001e6280c4600c0d0303110b649450511400a40c00c9041180410280b168140b50b254403074082d100c140c0604101c0d0500f40401d1090060440d03441c0741141c1c0d80500792480f855604501c0c003805400a901040c00010640003400a00038440240841c034141542001000341201c02581655100140410b150f00c03010a403070307528041e50a40c40c0c0440c40384441440a980500350b11a4181c0c8004c041a00e44051503c488010102e001c004000701600c1840078094a80b083c4042000002c032403800000180c6010041020700b10306120141c40030341e00003a0b00c10591140c09140c480c0d42d8004088034919076642484a000b050440e0090703d0341e07403600300807074003103c0c03d40200c1c2c2e19180c00c03d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 500542068 1250 500540818 500540861
    0x10315030f0f0804030c030210051c1802180610090614090a0b27011701120501090c06120c03050708072d020f0610080304060305101212020c0103 64
    0x35400381e90511080280c03242480800c4040000c1c08400040001c0c5109800d5031070074919600c1808407801c9800c0000003404414004400c03801e40003110300c20030400081c17000c0303054402d5031612162201c1000c0040d41040200905c0401c2c98286a01355008000c29541d04020320300d0581304480e010b00d2401640b00040401048280200e10900549001c0c0c030010103a111441d590500c09806500c019204449500822004071658059031110041c568084c20102500500d0102d04070009005002d02c03020a100d824001c4180002503002e43c11241c1e12510b203e00440c2c440b64041d1910f00c00341102d40c0828184081c55102c14460301a2600a844039225445070b912440c10958072200c04800c401403008090200114114030755007683c100d02c006802520040001c000882d080c1071300100142d0181e01000810001b028001085404443d03031890f00245070780f03c0f41038400c9003190701e5101492011500440406010261602e01900700300c035000c445003805810300641c25198200c0300701018440303444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 500543318 1250 500542068 500542073
    0x801090c05090d0605041106040b07020105071104061d070c0305190210050c0a120c05090d03020f0a1109100b160203070e0c0301051201110738100501031503 69
    0x204940d448110500706241400079a00100d010b43e50720388401d445880c0c44100344006e0104450042000701400c1d030302c981c0b07001d003840b0301c42440380b2541c10028100440003412000b0b10505940410312440001c2c010300029035504020300c03402c021080241906000700c0d010401d401d001c0e0095241d40c95050f2292420107882a80a81108103401c07070aa055000d1040c4603503204034180319151040100701d01e001d440b8501641c1c004c212525800b1100c1c40c0da071402d4a181042900803040e0380014008403007a040c070108510b801c0303040c101602c082400038840c00c07002c60304001000d620f5980403e030541d0f200d6255a01e6884c1e02c1003a04407403107800c000c13140800074180d108810060b0307144120300180440d8503007550b0b10b4000686080440e0040300411002c0010304c030a01d0300241c10110018100000e011180c4140b0040026120f0060024110f0320103500740c00e11030001340140800019102d051088640e1202140b1007540720481d418036a1402034000407942e0360103403059903a00c02000758120700d0795003141d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 500544568 1250 500543318 500543321
    0x70b01030f1e08041802040812070c1203031e021602060c01021c020405030d081e18010e010e0105160801230607060e0c0a03021c0c08010e0f06060907080109 69
    0xd0307000d41c0c014500d80d000601211a4040b0009a42d10a210041d900c61810481c5803208500b810010034042c0104810030421000040070300e0518000748111b40c0c0d45c0451710300660019103542c422880c14140419100c240b62300740d445148000c0c249400d01518162401514080384128000c2040402c0610b15030409400d103500a0252591581c1c001458595800a1900d5400e02c204802c960150001410702c0941024003428441000d03a080c40b40441c10a40103058a0b46c1e1448075400c50761108a0003c0c0d4080781000200072a100da2038000c00c800c001445070076010344520190034509601744008123100140000c0b001038181075170795032000c181e420182465000c00c0040010480e4221035140c000942d40c0308001080f0880c89464000b0700c01041041c0e5031304000061092174414256a0700400260f102c0c2c0e08200104041c0d04410035102030f06250503140d8000642002c0060740c03070540d00d1901d18000040c6190b0600c10213080f1074450391130070300700f000c0290704031740103000204004010842000e05 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 500545818 1250 500544568 500544593
    0x708121503030d051603140c0702010e0d03030c140306060f030a0b0306010602100c02030f0d02160512070209010b030103050c061b03161407050109051002030412050105061203070b0103 81
    0x3000005002000d50320002072468200d4000030b080c5035910130174001003182d01c4911882c143c801c1e003010300604040c7c1c0300d940484400204045602200043c205046a220f2840c07003c040c00010300c100c00485940c1002030045c50203104607008102c81c41030404014105c0030640340300d1031005040e0362401c4442d80808441c4d0300003610842c10305490710300c9101181d5050240a028054030f500412802851010030803e85403410507941c15900200480c0803907031030000c11564031440c403640169503154808680ca05000c00c001014000340140035058241c842e054004020b400d00859951680e6601c0c1d01c4d86d624907200c2031100800796401503641002078140310b0050b2a2420304a0305102c0040c0c01d41400d5820350707000c1900d820240c0202d25883d801c00c070036400707180c01002003c0e0040099a0034000083d0650040e4000c03544102046601030079402e10800440d0064409504070355022400c91421038007800040d10883e110300740c01070b81c845d5061000003d5600c4150021003029459185484211403100c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 500547068 1250 500545818 500545831
    0x40b100302090607050109051507030504030c030f11011103060111010e1e03120906070f020c0a0e0a0f020f0408060105090f24060c0c040c0f0c1506080a0308011a070812 74
    0x80920200c00400c40038402e0311f00c0d15025401402d014181329410341c443c0c01d1700501e55800e040c40c0400b8040440e5112011414141d0700d03041c072082003820001c0c2030340c00c4080c01404c0b118039070074141100c00c01048000134500520080e04c031100e50a064450b014241c5511390302200240d840181c01c40f02c0d91204085e04030710b20340c1000583e03280503c0c5403c480400f080444d10b03012283e00400a03c906d10741e00141c2c81110200610240c0b110842031400a959900d840c1710304820b01200c14041a102d00060f440800e90700d101c1141150382d40c1e004480340440350054420400e043c06203a00000d014108800c0c9148200d02c002c4c010300d22030781c401c460b04080c1406015074001030511079850040719100c040c0100342c020b00000c0200b902d4018241000b042d41d0120004100700b003640d490080401c0d81205072403070b4681d4000900240c08103041c00303140c01003209501c80310891042501d814145600110a141030700c0443c12a80101c050380b64242c840d500c5072000081c9950303c10081d85240d42e010400b03d640104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 500548318 1250 500547068 500547079
    0x2100c050d21110906030405031201050906090402040b0307082b020f07120c03020a03030c050d111b0411070b09070b09060d09110406170735100203180c040b10030209 73
    0x500840405d0f10398100700d80480b01c0d0f82c00010300100e0303424003044442c01408119400105441c0080c0403992070800548003d00840d15914000b00c1c80e07170b082c4030202c09400701100b190741c008200070b80c4091030780008100290b40040301c510365850b50b1020610300d141020100041220501d4080031080b004640c51003518100c0d40a2000710050751524a200c00440c0a95120b1810b00801e042ca02c0c14075400e08166018484c0680e121008000f02003610784200c00c0903d0740e20b0150361441d002c10003400d058401001d248000042c0314081003000e05d101400ba10064040300d000c0d5445921311407003880782d4800300d940803d050010302450700103500940c0303003144a0000f0a5015480c240071a00355201d5410400b401d03928441482c03108a410803114008040340000c65103003c80071488100465222001c0c60f030015180031110140b95020420f2011107a482c24045641e442c10420301c0504e40607503a000030b41801400d4124182d890240140ca0303d401c4002d1401e00d90110f2601c054009501840c2500d8000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 500549568 1250 500548318 500548327
    0xb0f070513060f0f1d01110a02030106080604140c01080f04060e011505040c03050c040510020a080f03150d170a09030804030c0f0509130201031802100c050d2111 71
    0x24140d004440e0010700683e00e403c1c00401c1e18850107072030340304042d4444041000f00002c40840f800d10500020420b90f0038201098070800402c0e09605000f001ea40c00b030f4040d82001c9001400c010005035080c03259000b108241c0904007582c0c1446e440700c1d5107040d550f00195010005c00d10181e040d103807a5410070b10a01000400101e00150203081d030300868440074020f0741030303802080705041c00e0040691034429031908000d1490084420001ca0042307002c2c1501a252001c06a106203008204c0c80a4040c0c0000700c058584919404140482e4800c880c3c400580140d40c0d14800385040400c0002c2550b42e00200306403e283c8421685400c40e000031400100b0022480d40c000701107400d44009001071070090100c07500f0241842c40400000b02280d00441c02002e509041140080f48540c0c0c9082840c4c0c2440e0210f0318449400c4064281ca00903d03000e58800081507282014541103a00701d600d29100301c090b03030400038003104155106074103040003070006040d0302c1085a0b040107560015030000307003040b821407c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 500550818 1250 500549568 500549587
    0xf010c0f03020a15022d090a030b01090b0d0f0f031e1707020604050d050c010f0e010c03060602120417030733060b0a0e280504050a06030b0f0705 64
    0x1600100d110a9000d60041141e0b2800e2001e4880c9000680078030300070a5191040c101580c1a80e64100701c080d0458801d1b0034000501e245113070048800140b002005205501e49900700020a041c0030b1152891451404800d03640c01c1c20044110b007801600b1030f800111b12045601c81d0340f0700801c0c003d01242048203c06001240300b411030010011007050b0780d682030403407082180700202c80402418000c1590f0100c010040001c4c00002c842000b0486490031545442c0340c410894050007070420042007190804c0c0c1e00700ca00d40f0301584139001100c070a42e02841090364808061b62102c131082c5100409000810003802030300c262030b41601c40f002c008000c80c0d26102e000e072125001e4039005126624688440340048119040310000c2c0011a500b4280030848180340000324840d81c820101e150040c0000c0821440142c0d80754440c0702c0c0144c1c07040800c3d1240008084440050300f4181c0200e034819890540428000e6500788140700540741e00000702d5078262030f45611340c0d0050384001d004908022042046560 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 500552068 1250 500550818 500550833
    0x912021201020a031d010b06030403121803050a1d06030a020a0903060f0204030b010b0a050a0f0309120e13020316030209152205040e0c040e0f060103080d060e150f010c 74
    0x241c1000b0b0758001400c008100b1000c2843d00450f0101c0f17149a0400100c00707000d50703c44085a03049a814180042c02d0040240d484028043c44058440c061480c0d030104c10031b0540020041c80041541d80d150842c41c03c100c120107010006030006a0b80102c01440020001d5501d60700030010007183d070404e10388042d03403503a85100741c4200728404411030b500458104200884020301034094040c0d425200d007008003e40000f05140100d041300740c01c200003c80e011106c14041e034000b0825541003104002600290000030300540780518429010300403040b66503501d45114800d030b90103254490b07015495080d40c100c0407000394102c801c2207940002c007284041c40d20651540142080c0000b03a400c1c800036102d00080701140b01013a0321031400f80d404c0c0f500c5071107040e202040c441c20005080f200000c1032206820200d00c1c15500301e190424900c03d80c40044240300c101d8011300000c2550410034080da540f01c01b603d5126901c01d680d0a0b0f810807001d501681c2c28078101d0580141078a061502211900182e04c81c103c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 500553318 1250 500552068 500552077
    0x90515121009060b0c0604020409030309020d05070806010b090d080306210f010501170604060c0e04140a060f180f090206180f0406060f050927071806091202120102 72
    0x4160701d414420401c0301503601428000f08a2985500d041c8500221020b803542e01c000c0c00244100c0d5184c42400405009501510107240c020b07000c1841c0c19250300e00380b55240301c98020300c06507200f504000a03009200c41704480c00d02c640981050303100000c0703079681400d6810140149600c0004043c15119107a240c83c142c014a840c0305004001c00c100189a40e0308656040e080f0306c42c1e583c56440800f04a4000041b02500a50700404c001004040c03440708031801b0462011251340030741014419100210804115400b80149e807a042215030340d0b403018030300700102a2146891641c0381c85079001004045900880540041040100311401558001012036000865000202e60501c0d89040541009a0b41c04d4a1003400c2c1c40800c6200e00b03251000e4110480ca1451034200503000039a21411780301c410301091107003c001903d14540c45445130a80c1056400ca698000244c00080b21200c000107400001044440300c1d110303011502d0400c0da81e000b8a0102c00c5040e60001c00010b00701346292000d100a2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 500554568 1250 500553318 500553331
    0x10e071a04120f030e0102070f0506071505070f02062508090a0c1508100b090f06090319050f010c09090e0309180105040e0109051b01090e0c032509051512 68
    0x7a074032400f0900d4040c015680c8180381c641158040702050004400914980c01510011100c85445840301d01e020b56040c0707074001d00229a1800c000c10300c5142c54000441e405038440c80d8003551030513130380c030407a0241803202e0a085a440722182450700020a0150201c50f1700320b054041134604591058032100740e00d027101d900c5100e12900445844076190fa0103002e59410080750001317034840314a46103940100d801100010b501ca40140e00102e0b0740d40e510f00c0122036049501905139031508a0040340221031003e0802e003030b1900d010382900d402c0d5034841031281c0401008107403146c943e968180a400c400510641c1c9529565100030803801c0001d945001d000f1000c0220300d0500d400f158148000e110540c0c6002e490321050f030b814551004005035003c1560880d00206d500e1505001400000403610002c1a51126069480c030b50144841207024400030341c070646414041d00031010082c1b03031101001c030803490700d1f1b80007680020044c8840c0c540006c28110001d00c400b4814141001164205884030040c0c80c40c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 500555818 1250 500554568 500554583
    0xd050322050303070f050711010318020a08030304061b090909030e030a0615080c060f0304020402070b0403050414060a0215100819050c03030c060a091a040b04060e010e071a0412 78
    0x2040750b5945c4c041a0a020170800b0b00d00f0504152803a541c504036207140c44500d9041c15150005840c1d103201c150380b1042d02540080c03002c031042d540ca20700c2544990040d6000d66400f0b0403c0c01c4105210400401c001780d0020701c3e5918561705140c07040720001032603411401c0b42080788542c9003402943e0204210071105005c0c280003d5882581840202e906001c0d0f404a9040e030402030384181503688080c00e980c01c160f0050045a500d94031361002500a21030000020010200c0f002803100f8581c0c0100a0025039607075004a641d05100c440400580740101015200142c0c0b14090642c11f2450050007035411020034140c0b0000c450b100c445c40b038201201c5480d41007000304420408024880104401c080c1120190091490411112083c54039007400516160304240c0700c0c098078003041441c070840f098642d031040c4002d9180c1400c0c42d0501702480260b905130b50060034185104202a010710a90030b448200c9401018000e18000d0980501d801030a003c2075064010311000882c0043d0340745d030070b4a0501c0f4194 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 500557068 1250 500555818 500555821
    0x180503070b0d0e2d0c0f13020c011503051b06040f03020f040e0106270501080d08090a12050d1b08010911120c090307080c0f2b0308270d050322050303 66
    0x501403506107000045c4d441070701d80000b80c1c41c031600c80420407d0740c16081e003070250b40c440703030784001034050010305451020780c0c0001c000002c14400b02285403800f0f0500e00040440c90224042005954004d90007540021845030344108010b02e842c0b6080400718001810204242151110440c02c54200707034000310181540b404005080c032080a845010184070b0300b0100019414440d1455171880710071440e4042c056808007203944100d0401c8040c81a03a03000f2500c9503070840082004240d6046000107000660802040b007080550920a1501d5044540d440c152035038038010700d040240c0407500408079040c008010004280c02c500c00154450140c1600e42d95403401d0400c107241c03a1802d190f0107001d094200401d9104955500060800054011240c0c10280e0800360500364000c1e070340c0d401401003107505000b00c078100750300001f500380f04020302041500c40c0305681140d8908074040c050720404c17070b07049040c41b04c2d05580039501075500202444080201884450384811400c01129000e85842d4004030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 500558318 1250 500557068 500557153
    0xb1323010902093a0305040911090103050106020307030e060a11030c1b1f0e040608010c0c05010b1e09090c030601090203090105100303080f0a0f020406180503070b0d0e 74
    0x2201041e18204c004600442d0074407028264000440001c041c00c020480d012642c1d052500ca40300399000707494080810044920131042e9400d440e800301c10200c2c00301c0e04040002a02c9800802501c0c5059015111070315100d541d002082440c0e804210701005001c0c08401e2006250410000742c0a5020890000c0c00801d9400c01015800c440362107842c0e01c25802100342c6c4400745440c2c440c1003810030301810282c0008810304002409040c05420501c4a50321340111004c0c25607000740d00442c12801240200261004281400881c5100144428124410140b070360000d007001c6248a900543c0c91054032a070018100000f42010005e038810700d246d41e008000c0c45121582803080316044020050b44440d000d142d69005418600000d1043c0d000680b048009806c020b0302d50040380b4020104202195556242c0c00050100f82c0e0750031118114601a035000308883c14001503140c03d03950090030090a00130100d400340040c1c101c01090003030602400301c080c8060900661081140034101020700030808050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 500559568 1250 500558318 500558329
    0xc05160b04060b120d0509062502090a0203010b0f0d090804080304170604240b04151a030609061002030705010c030617060f1906030c090518010b132301090209 70
    0x1c3e402284500385600c004455610000ba40b4801e10070281081a1904441400185213018003940c840c8513862081b4800c4481c07500c1500b280c1a68402c0740d038250591034010480d801c80c0824000e070400d5000800c20344141026000103002410640e210200c2c083c0c1c4241e0f110340d40350300075030711080031540045010b010030b901c200605003400720300b000141401c2c50b01d51980a801d00c0a05642e81c0c00130041000c0740908026508070003041b080180040c05170615200ca601c3d86140b25100b60950458058000c0300032207000f00c1200c1c09190000d281030695141c0008200b600d42c482d41180007035120410003e03000400c2809611800041c60301c00281e0740c0c0c40c0c5100d0600281031508034100c290085410800c0d0791141c66009601318043c6e002028000e0884101c000c02030010760805411450310707920004411080ea040584100d40d5040c100c05415480c04445081c1e40d40f007400c885e80900700781403080b500a0f0030350104003804c46489645a8403007210720b4441d00700000ba000b2400c1550005140740041c00c15 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 500560818 1250 500559568 500559581
    0xf0b04060f030b010504150507060c021c03060f0303050a11060a06050f0117181608010c030e06010609051912060b0906011d040504020607020312030105100e03100c05160b0406 77
    0x180d003030500c10503a141000901900c11307402446030310580c1c2c1c0146c00c40c0b0b45c4688c082d1412180d10403002c01180c4800380000c0d5464030b284603000702807074681f0480c208461007401900211034851928152550460b50152610b4000e02800380401c0444004c220701900104000c83c01013054000004103d030810702070084020b100e105140c18007980d00f01e400c0c00c45801d030034101c0d0705c41c9940d4914402d041c04000000e00340010314a885440b8003032000701180041c41035110700403a4200d03032010040c00409107507290700c540c02441140086200c0800070003441c10482803640c40398a244c0b0f50860700c04d032a084810032110000c1c1d81525500d688002c2c2040c0b41c24a41d074408c0d000305003402d00b0010401031400707600c1002010021a4000c548900100d41151240380681d0480756000341610184c0004004070300d41e50f0401d218651081c581440900707481303030045120741d0303281402401810b0009100030080c8081d19504210707100b00718040018102040f020307403105954a100c1c130340d041c095041900b4201d013034035030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 500562068 1250 500560818 500560847
    0x11403120a02060610050d020f0301180626100c0c0203060c0418021b0a0b0a0b1804020d02210a0302010f0c090608101a030702100908030a090c0f0b0406 67
    0x1c004000e03440e50001019a4083d20440e0902c2c442556440c040320b003801100d80300c0d9032080c00880c0210030202440040c6042c4e502c6082500f00558940b0b840c082511058442c0320b070700d5515240c40514003646c40c0215404480c0300345c2114410704080440304200d480550b40d00700083c031200015070031441c1c04e01c0071079040031403080b1040c101400c1813001d420400001100a0f44d0590009410294502100d007030485080450155055042c0390b0500220005e03040310700381c24041c80d1080300049440d1601190017262980c0071031921550b610341c28031140c06c03521001a43d002e2444510100d04648840300c6410b1400781c42d01078865041185406401c0d915008031004500742407502501c00307140e004a1010071101d1500c2c11200c1c9480380b02000c8000d00c00343d0040c000300c82540060386585486000150b00442c015800c0b24200e81c1c8800610046506017400100b8076141040420b50211140d080201160b02030380303004c151159104d129404000e11944202c44014000c9401c0040540042d407010a00c1d8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 500563318 1250 500562068 500562103
    0x5090f060f130311061519030b040201030e0c0915010306050102060c0a0c032003070b09010203130605100b031e01061701031e02060c0106050406090e030d0b040212011403 75
    0xa001500d0326400c540140114054042c0b42c4418081c1845460301d078001045400aa4503182841d20f00d40c1c10840505c60018029119401d2403d0520350800a00040b01d410045000305502c0750350046010f070501c002c200f082c80c4503e040842140d965000b00d070780140c44280c0c1104016011800260983d0250b51105042d504003c040050306a080c0080790514051032420704446d003003030719050f43c418550100c071101040501400006002d0000003c1c20070398000c0c1c0417600d0a03540e5030442801d078481203d2090100c80c03c0d04240000482540000d5000400c030320035501200e45420110f242600110b45500040b2400f00b01504856100c140c030b103000d42050f16101c1401a80c1c0d8512141028041c44010016442e1020381d03507403445001c615000e80c0790300410b101e03034580e000c11031907000e1301160161602c40d914000c0c1c00910040b0303d209141c20b0795408030107542002080150b400003000b080680f0b54006400f0003c2c402c00c81800000e031806041c800e6510320381e1070989401d01d483c21071062410810803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 500564568 1250 500563318 500563321
    0x5010e06100c110402280909020a0f030b0a09110405120c03030307050901031b17310c05041e141e0402010923030c06071a0a0207051005090f06 63
    0x46030b2024140c142d03940c100522075400140c10300820f00170f2113440d84800540c1283d085019140508260b20701c0842d10700d550780d60240b9203134200c840491140c03c00070404075201015070749185001c1d81012088080c000d0545121680c0c49440341d041c0d803115400d0134583d40e0001018025407500455095620100d4070081c0b801e80b44203c0825620710000d815803090050100f00400340307070710030340101038122011003a030711102241500c0541950000e40341000106000303000203149040c0700b011941c1c901e00d00c406501350b0070915080f00c0184890070800741da001d01c0d04400401c0e10340340c1d030080d06501e0009105480c03c00e403d00b0095811a10125440080454031230b05005250b840e00060f28082540000ba011541d1a00e10040e81c44bc00d044d0700c800158003400d1480c01e40c0c2c3c40384074605000034030140c064038001c3c280031041102c51b214032400280200000344080501404d0364003040ea00c4410104018902207050321110310302241514041500c6845108000580ca81440310708100d6910170002c040350f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 500565818 1250 500564568 500564599
    0x30b09010f1412010213180b0a170a020607030f030f0b090c0c070902030403180e040c03060e0c04050916050123091512060429010e010233010803042d08010f05010e06 73
    0x1009c1c428440e2840940701144074a40064013071000c0180c159004101569890131441c01034441c400d10240200440d240141c0022900030a0094030501c8400030306803001651014941c820a030000d0721540c0b1288981207000c54403001c0d80c401035004500035210701c080c0321a81820f00b00e0542541d08100060166a0b0038080020540c21514055aa0015001c113625880c0900a460030740c4850000c0d9109003401c0900c8035070000411810500328002802c7c65406880f4001074800c454220b202030300038841c07100030001190300080070740214200144281c1e0100b40f007910814840c0c01c1008006a0b40c241442440a079150501c130f0300c540c1410301d545c01d0440a2008510311142d45100c2c160a05102110760700100d20380c800e001319050550078034034849c0b5504c80304075002880c26606145c1d09612002c000049425000001030301c084401c2c03458944011000c4007440644214814040e0300641201400454508401e0007910000140090009565850145003240c200310180049000c1c10071110395905 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 500567068 1250 500565818 500565829
    0x41b0b071106070503070f050d05390a0309060e0906010f0c03020123010e060103050609360615041109010c080415020d030b09010f1412010213180b 65
    0xd0a03500080740c0e01d000e801c0704020800c03d201c1c0840040150000107012010412061f4030301200501a40403030321030540710301c001c2d10030f8420114412940c03201f10f03040e0704200c41c2c4034034084030300c400350405000b10410204070389203000c0401c44101e02152541c00306020051f800a00c020004008645401071400c01e800068400c82c00980c4030030811072500c0304c58013490b00075000907040054a03010400700800092600c0080030080c09034012100c0c0100101f100c40d0312900416010303000040c21194180c4400401580c1c40d0581c8184104005041201d0111410035021300c520030441a00a031041e403510f545842c030041d5140c0e04c4644500d240c20100301c136a40b05042550080750003820b00303060600301406d050b00c9130701503948002000385030b0b44540c615180d404a032030304241185840a000031003580c3c04001c2e150b0024050140300c0d000039282040044200300a0880314040030f041850060005145039003a80d01184041041600d4104100109d810302d140741510b070032414808004080d01c640001c0c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 500568318 1250 500567068 500567077
    0x30c060f0c0f030c0e0a080f12030f0112050c0d031d150307050d06180c08012304020703030b09040b1005062a19051f0209101107030507030b041b0b 65
    0x3040541eaa54488245401005c0c85100990003d0110310401e41e42ca804079500c20080c440f5075840d018100400700c2d00001351040da4020244003070040c0031030b824804d1060307080c15540c01c00d41d1148195913683c9095242d03601c00c3c0071818000c1d42c072503a0740d044181e1515081c8031358041d4103000c0c0b20040108030490100384243c1303070000002e241c265990720b400b085001c080c0c03110b03403c80c18800d4002003651501015913031164480b400710303844489090780d8420311084080b699441180000c0050202d0760018a0140e004200440c030034200003a40300c00c480302291041c64115070403908600120140720911801c003080e43d0050170704035030162801e00c40c140300031068110f03c039007102d41024076108000000d000f071061202c41d50010f0707610a0f83c0c82d400d04000760350351000b0203103443e556000300c06020504154021141c80c07000140c8a01600041d9080468100200c0880c1020b035014851021002030014400c2c10025801000f03403040c01d0906040000900204800c1c0c003002c1c000815007000308144c0f40303042d034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 500569568 1250 500568318 500568347
    0x3090604060506030f030c0109050c060a05180409080d0e0f1b09040c0e0403080a05220b070306081902040b09091506030a12050a17060109030b060301020c0a030c060f0c 74
    0x100b016103800340881d150100101442d002800f0206555440240561040da180c90190f01160900b10115007032112912400c1c0300d400020b18100714a50000325000040703d2001b00180c0001031800b015100c400d420340202080c0d404042e00d850340f03581c0100d030401c0320f00c074405084030192410701c500c94425005d0514070400c00740185000d4001406102c80041f80c070006003a003003c0c0414610340b07460028820081165048070b0103142801042814030080b00540d0200b004c100082060079130b81e21011110007004029100705030311100040f4060405104150b401000c41e0680100802240304200c00e550841c0501070040100c00100601d00310b0003e140a1541081d44290520341c8503000402c0c00c000700c24001804108002d40d03000c424651090042444000c1c0c0e546601548603c520224103400c02038820f5400600200300600108000542503608280000d000624007401c6100d03a504280c80b501003035020408590340b10041c001c41c2c1c022080030700c0711201e0400c40f211040c5805400c801d05001c04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 500570818 1250 500569568 500569571
    0x50f16060c2303070f120c03052706040b270a170c090711190503030c09030304030f26032502010b03120309010c110a111c06090b07050309060406 64
    0x390021001100642c000d41108102640c0e5510141d0502900d12202050211405600d860540a08920546402c18410390603900c0394038120b00c01c80f8800d00a19202030300c070341c80d80d113007600b1681d10354804008200914020503c01c1c0c40390206440703c055005420000c1000004503038090b0000d50700c0007840c10030b95040f41c070011710040c000490b00b49058024010305820002d108188070909030440c1e642c4440600c0c00040301d580000300240c40c81a20398030710008086504c240302048130040c8a42c0a04024000074048a05160366500c8400fa400110101660b058603198801ca00340d80100400e200041144400d05d481c0d070234070118200c20311110050f803480001041c12341c20500380c402e4118000703030704009046401c1c00007403103020b10555205171588007042d880c140c00200b55501400042c04801000c1d400b901c4001a42d8840c4019480c84488441d402011601c60a11010056044401c95070107107000080300340e03032407400001c1041d0140044051110510400211020004081c1d0303100e03074003820 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 500572068 1250 500570818 500570843
    0x206041a0f0708031b0c0703240516020d0507030c030305060406030f1a070c03080c0a05120c03070f080c09120304180509061501021203041a04050f16060c 68
    0x42101660003020015400c90074002040300a01a43c68040c0d80150000a40c209000c84200260038091143c404041c030980c000079400c0020070700c024540d0b26041200680d4024131000c00d00d42d10101c520807100441e40304040c0000d06249030741001201c4000480c1e0600c43c0c603200b220386000c0d1480c0b640c40300040c04c04d919080000c0c01c584407038004400959024180c011400309500c0c0c4214000030350303920100b50fa030131034000410080c8200c4829036141d0309903e6400d4540c44044159039194010030410040c001d04101c000c1ea001e0210909911420030146455101c2c240020010180d5400b240c2c004c041158003014820072621410071500701101c1101c83d40da1640c2c0b01021141580207607030120405481c01e0000f100107202c29000366200e07401902c103451031682c42c3c2100608181201d0b940301c1c01680400c0c40d00c101c05c032031400115003040c026840040c1040300d01c00141014082102e003101c1c541c02030000f00c07600c1a0100a247c1c0d10400601032500c240d400c21100901c84000d4603005071a442c1d1119 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 500573318 1250 500572068 500572109
    0x20f060a0c021903030911010306050a0509131b030b1e010b03070c0b01180f1503150902031608010f0b011d1206070305010f0605091e030f0706030606110a020604 71
    0x221000f01400c1902c20300418101c1c500303001d030052401c400300340c92101c2c0141c80e090041d071103032042c031064900c0103250400c281d0401c01800515480100040d007003e001c2941c6001040c1c0130140419402c0200040f0342005085140806030f5040250a8450791110311002c20072625510146d1815941d514182544950311480304075401ea400050152440c4101390001c11405d01e501130b082140c039034200c1c050010a09948010040322500d104803049002c00c03400500001e000c000d56202c00a0b06000007080c601840c0d000607040c034910341350013210b009414004102001b400c0c0100940207030044c10030000c1d13322400020f0301039041c021f800b40b40c40c0324002c04d1203d259501204512280b00d1310084a81c1440c044d800500100300a02845195080b0b4080001d080f922540840710f0840c400303088540d0710706002a201c540200c1407542c03140e00d4040c0c0304004a0f00f4004002441c001c19513680c012036924075040d80138054031400d0b048118241c025001d0790000d0313140c0c4c80c00c071000c4403a404000640e40c407142 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 500574568 1250 500573318 500573323
    0xb03060901211a06040e030c0d05090111060906070e030109110f04020d11040f051e01080408040e040312060609030201200304050a14100c020d02040c020102041e080d020f060a0c02 79
    0x222001003c1c140c0d888200c07040312000042c15403080300b05640c10482d98002e024000c0d5640112481014546c0c0020010b01c80c0a200743e024064030201814005000c14443d0045d0741401c0c812200003c480c0d0040c000c01c1f101c41d0340300490f041c0440080e4001c2000da022605c038000040c0756a20820301a110103809a0081e8a65038121540342e00d6081041007441040032045029a22500c26501c5441101e0f00c08120743c50440750780c0c442c4481101006e40b00f80103503001941d205034000c0c010782c0c10380b00500001034503058014800d485103100c0d40d80c043c41c5c00319184840d0100c1d81c050300203c04112144006100503600400118101554000c07289120f43c41d50311100d20754070882c0c00c860b8009015070310006200b60160800d540d1541d0488444410f00240c1004607800d102140000c0d5104026526007030150030558490000c81c0c0c96840050328103900c403403120002e549012403541e025400c45d20204510b03c824481c100a14000b84040c0242c200407500c401d68403480030349040c410694036441d106409008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 500575818 1250 500574568 500574629
    0x10e0f07031e0204030c03170307050a030c0e1806090a061d0c090301060b19020d0518130510140307060c0b100f060f11062a07170301050a0b03060901 66
    0x9040b0150365958491800c01c0e4039040c2484215032a6801c0e011740d080a810020a8138800c4252341d68042c1409041e280880140503951181c40510400d02e03804601c40c1c846242c103038041c03145d2813000c014230700304941409806003000b0190300d030742890050188465010041c0c0700d50310b819501c05003903050f15072510a404910490244562540c41c00340001000110b44018103540d080d01741c080c1c500b4592401042c1c4c4c841c201c082d0340d0000071380d04110040c40b0702040166204545009400310713001c2c103c3c2031440301c00ca40d030030746404800b80300308002002411400c009220810b0350580c0074010355460f001010b00343c1c84c10004020600813501d8000b0304020406440c49004202d0110301c03180740390350340c4409840c47e0b00030000600000c0750545688075081c4001080c50080403240c0a800b50300d654041c2e007480e010b010740003250b4070075010003071840441c103d02440c01241d45040000c4e5a01d501d0141004080c05041d4807607030030440c050041012540d41c04d80d465044401d5416000403007521032030482c00b02c008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 500577068 1250 500575818 500575871
    0x140a0b09040213091407081303021513051501150c0b150310020d0c1e021c030b03160806060d0f1e05010c080403081003150b1504080d08010e0f0703 65
    0x14000414170000ca00c0c00c4a00c1c081c01040c0c58550098036045082e103840410714030082d0150703001001801100500c9000c040d88043d640404017002c60076a6a56400d1030080381901c210302011500500145211007402d241c90b00990914a00240c0640e8a000403984010310f8100310a25140f18002c481e1401e00441d1410420940d08654030006825050b0080441804500008002e641f0603071405c8203003222099046610b4000300211003105101410030840d0140304400c0585030a42c000054504200d400740c91180b030902c9210542c14002c0707141c50198001c010910a0654032000004201501c00350380c0c0c40b90300035410500d40c15035203503025140510140020400d42c03810f490001e140e0303846012903006510943d25151036403900c804422101c110303404042c11446610104c4410410950311043d42584003401c40450303a00c0605642c041a0030a500c0300b58260445c45036800c00541c00a001c13030140c0f081c80c0a0005030704000401000950008100c841070594030201001019590541900b1038403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 500578318 1250 500577068 500577071
    0x210606190b0c07030614040b0604050604020904231f031101031803030b03070f06020c190509101d1b0310051c060b090f04120c020604030606140a0b0904021309 70
    0xa000c0d8066aa25192000380c880038034144d08011754040c0c0c40046d90180f40c00855005140d11600e041100030701d0b018211075806982042111000d8503140140c1680d15801407540f52142ca10001d61000c0500c010103200ea240c1c45070188401020700d160159081e20341202511000040d11001a03000b03107a2040c0b10300000ea01003a9181c10150b1641080080200560694001c13955910010002c02002d02071340e8056008400f10040030b0900c1c40b1594003402008115481d2141d40c7c1e004603010900980e03150090740d0100100b40009840c601414958100580e0500c40701d1070320321003003000002c0040710100021000800700b420796440e0401100a803e00511650030342110714030b0202c1246c003202c000c6501a040c40700c800d00c1d070300c0c2035008548140350b0826183e01a0341c0e036903180107008100102a1052143e020556070160300c0340c10240000e50b1240300d00040450611519455418902c000c1a2003016522814080d18000000707448102074240d074050380300c070340b080e94084400354550002071585 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 500579568 1250 500578318 500578327
    0x6020f18040e0703030f05220e10080c06030118021306050c15150616060c0f0314040507030308130204090b10061106010e0703140a0605210606190b 65
    0x18001400c40028031004a40801800d1500e420390303612000103200c042c021400e48507094103540c4c000c3c1e0042c00c0001c5444400c04508200700782c4800c440001da0420541051f2003c104607100d8204c24500002d0703c0c1e540010014180e18600050003031005000e1604800c0c441122030741404800d805644101015002c0f0800003601d550b001811600301441080f514480e44894000c0411410105401a40d6140700003082c03152039030a102040d40240e040c440880c25440316603000ca022842800d080100a0f90383d040b5500802070001c054402140074041200b50400034080041c0c0001405821a0380c103040169150b681e100f1403004840c030f450760194001741041e51840c10040c032a080684210214004481e00b0307031b161001100c4109a50325491040d0340040018405030500740503c0340d001c000e82c94085030321040030160a64180c003d90b540a0300310340707030401800507107064100680c030811036041e003400c03403a00003400c15916480540454060355401101520722442c8107070010281108004840c2d94 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 500580818 1250 500579568 500579587
    0x1303030b01121e05010f0b1602121f0f0515010e031c03050906010b0304080406050705071206020c06011a071713080d12020f0301030204020a09052101050a180f06020f 73
    0x2982440d00e080c1c0c400504c1c040c00800d5401c0313960810426546140901810440d02041d242c1003042d1280003a6841190b814800306018010844124032961000c943c1c129064800d60710320a0303800d08198405150b06000402c04a0164003c041e40e540c4024a030465081071014003003420030307061000c04403145c0c040e440c08000035234164101c540034040d80411150700c0c0c0ea8071031110646010640c0d00602e03c203010002044030034400c20161507101d01400c1658030035070740c07041c048540d50301c2500c0881e907443d00030441d0302805105200941c0103007804402241c0364801a40110035920403124010b04442040418046031058002900d80c4e8000160603d03901035203a0240c15a21580c041007540001e001c1070640d440040c590098075201504d04a59905503401d680c20800070350411041d2004100b80d00d0f4000516a03140c00d0160040841c1d844001981c03080403a416095800041a220b1810b00340211000014500080d14100d950002c050030508901498400042e00c9403840d403021170080031845119 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 500582068 1250 500580818 500580851
    0xf060201021209070803030601120b0a03111305070e131103090f12090102031c0921090b0c120a121a0a0e0907051306050303070c06030506091303030b0112 68
    0xb090150181804083daa07460300f52a07a40070301c0d001e80540c40d08144049030745035001e050107880580b1560300c0480c0100c0c007440850700785600c41e0f10654016469140500d40307820590181c4484d0f42c00528140010320700306201500b49058603071220b00550407100c404403e040c80d5131108400104c40941c2e0f990360300300300e03005039a1180150b040c000280a03d40c1e140d05035048500443e28a40740680145003000030000000e0844560005070140413070321540501c000603900c040250b008441c44180d0702001c0500d060041c880079064001501e80401001050543c510000341203240311280346416983c3c201450341142c03801c4054420b4a4100d0800d0318450121a520710100c10f03610040d604400032a64400f04000d0000c2300765409401600014010f00a03410500380c05000c803045d400021070102d40e90300c0428903643c0002c074191001c0a07803600a020b0b05030b06002e42d58001308219141681401c181000200d910420040241415900c1545618503400341c5290085802c0f043d80400c140621042c9601 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 500583318 1250 500582068 500582077
    0x90203060c0c0105071b15060e04060510050a061b020609131a041a0108040302030c1b090112030f030213051507060f1b0e0402040b0c0706030b010320130f06020102 72
    0x1059420500004e13605d510030200f449015a100740c05400c207901d5501c07050b41c061032600b0581040d5858010204905003041503090089201d00b0b070000b49440d050400f000700c0030903a0045171040c0c00e054020051f03143e00c072016030b00c0610b102d00020702c1cac1c0051b880041c16a01c04c0004081c0c0090800888407c00116507008140060110100c0e580e010501c00400045400950701d4042d208541000028903511810025038410b05c240101d901c2d02410020440c505000c0e018a0a4902659a003805483c1040030380c0900510095000440300718059801500d81100b042c02003082580c003080085092003001c81141c01010301518070004803250241e5400b46601408098894505055071a00380b128a403160340c40304c004c0c141d09000c4e10488210b04171100103403c00d290b07a21640922000c0746c1d44015100030002080302e180100750f21403038401c01506a4020183c1c050526140c07400e1650b5a1404000c104806004c0d09a201da40328070548007802e02c0191b9811884d1482c80d8040d001c074600390158002e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 500584568 1250 500583318 500583337
    0x10204120317060a06080a0506240a0905030a02060318071d071704050303010612230609010801050f01062703050304091d07060c030c0b040f03091d0c0a0201090203060c 74
    0x8500341e80d0f640c050104004042c0300c0c040004183c04001004005698030607034100000420300c03003032070f00c0c0d940300e5501c2c403040ea0410805e404000601d1025154120f566440141000d03000f5040756080da070001001c0d4080200580740c6164042c4514180a42c18441c3c10050004000f4084450410000c9800040000ca17042d031b0100c0c0320b44488104c4880d00005030707885181c0c000010351840e802c24000312061000c584000004984904200c1c2540038200920fa06082c01c8400b910321381e140c000100304114206030301c50400da91420b0301740300080011032492415100340d400e02c070304c202e1903075a00348807202c0042040440c0c12440c0301021080000110042c4205c410700314050003040b00e880c28005d130014940752420140c1c0d01c280010841c581c060301c600c1035564003a00380045504400d440d01c1022007421101155282924100102015000017400001d40300ea545040c0340c1c04016030020001e00c80107071218603400008140010411f10035000710000d035034040c0503903a06041040c1145419040802070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 500585818 1250 500584568 500584607
    0x308030c1b03130302040f0f091406061005091005091012050c0a0203120604060806040b270604300e040f0225020a030803010303020a030e0102070b04090e0102041203 73
    0x100340e50090020994104020f03c400701400140b0b90340c00c000c01403415647c00482192514845041e10040d8855031208074001d050b550b140900300003005041c14801000780b8402c0d00413103110342480d1b03404400c0c2c81e074291069842d8a11200c1e040310641e150b00991020661040411407203a0201d944056081a0820b9841042c821034494444031a403c1c01004400300041e8030502104251840142c1443d81044014000180468039154410f04222080b01d0645d010144a03050000e4401c0c5402d8030004096111f62910701c9a0003440c0140d143d00001d003000d00070803a07000b1070950007402d14000440d40a08991850b8a040300b41c800500001c4005018600c200d15011501003100814000c46000c15220300300d48007142c0001d14544c0c1c10030002882030307810080801003c00040c11140c0114080c6000e0740042c41d0740030381d52a00a1001485900e040d0454001ca041089841040300503a4141e400052b00030440c104020415402030081e03510170b4114000c00c0c004181407503003091488401101103101d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 500587068 1250 500585818 500585857
    0x14181f050616061806110a1710050904140f0a0c05060a090b031803030a0b040b150301060f050904060b0a020d111c0203160818090f040b100308030c 65
    0x10002103010b4030084000152080c41c91a001800c103511a03c18444002840403001c2d40a459070002c41c3d00113640d070001c2c16030002d01d220b01c180e0004506201480315840b00d41c880d24000030708900381642840398500403440640809d0030041040581d0000d40280012034843c22289442c503507590101c841c081d07603a442c3d90f98011403541400300c12552000d6650715001354041ca0204160320303e0b400107041e40c14400c00241e02000401c03062000b03501540403500045001c5500d10200800c44d803110032003904c03e0380b214540051000c0b501c0d054904448032410b008861071031003a01074840748100001c941d44070349030810101d00102210043d040300f00203542190300c82649010166000080d440000f00c2c1a130055405c640301850200d80004070650f05d10590341000b00303c0070218007801010f0b034121216040400d0324142d1001d0304407110303401c4108440c16402030a01c142240f00c524030142018004210500014641c039218001c14030003158400344035540c0e0314000c40d08008541110304d110100038050034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 500588318 1250 500587068 500587079
    0x30e1305190b18070c140309091608070f09080102040305010218030f06060d0f06050a060303020f0703020105040306050a1103090d0e011d040c091502010b0301150e0114181f 76
    0x100c0d800b6229400f400041c61082c0d600700714100408014000010014502000c0c80001c88183c2c40c0f005000c402c000071921010100700700720384804003e1981c103c00d80031401240c500c0394821040b0b0342200d0182001c01e02410018400c0b156024039400107655507000040005c05c20505600408400200410008104141c40d04258481040c0c415094141e440580840c106103000f480c003841291240180383354660059481e00c2c15294111101d00d00c0741e0b540c0710b040090540500901140042100103015010306590019205000b50300001c1c003599928000280700114a0f801400a50f40d0f00b84401c2d02e0b481c0c1407120907504c018481e01c5400244030280c8218a130750180d00741c06c105002400c0c0d444441180081484024400004020100f00500b02c1c0025409181024120600b00325400400c0c24801c11040c9829140345602c0b0543d41c40240300308110319400030085505545200600058a00400c2c000640c5071210300305801c1181c6030001070009454040c1d00030b8078030350b001e6202005c066580301e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 500589568 1250 500588318 500588321
    0x40c170705091305090c0409030815121203100f030b240d0b0604060e1005090f0c0406051b011109040c0207140d1b03060507021603030c060504030e130519 68
    0x30702c80302c2d8000030040000d034510086508143d9100d0015030442c0c0d20146064002000c0d9212104c0540101d91008107010040c1d0750448200b03a50b0b40241c6602d020311190300c00150381c50441c001502801480400458859030390200c151006081003100d80c03a4450300c0b4282110b0b121003e0310f140b040554032511880e40003003011040101600300070072000340c19481d61070f0410340310700003452a40d0240e40c03800d0114914000c001e12502911481c0c0500f05842c3c200018071801c4100a0001d01148560350104280c5520f403c08503000d403034032450301c0d03616001100c94103005108008050380396542060038045101707081c1d001601001c1001c40b410300100c000084260303103d502c1030142400c80c014116001740a4104040c00e090000e101d031017070b445c8a940c9840c1c4c40441c001140c0084a000d07896070240509140e042004582c804c4110710014031061071030b60060030041d07041c50000c00d45602e0b200003605050141c910310929603005030140907880c403855900401041e0841e2103007075144001c4036189035034506 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 500590818 1250 500589568 500589577
    0x10e011e0e0613030c02130f230105011836051512030405060f0c0601081504031d060a0201060512072102030f030c030301030b0f040827040c170705 65
    0x30721001c1c0040d521884041400040c0480381a01400031704041040103896141058024032060f480c0081e400003c5040d04c42a2000150b566603540c44844005c0c03014540204094110343d82400c200854044d206e1072000ca0305550b0b401035a4003001113200303411a01000b103110b418144210700a440b00f82100b140103003240c006940a18803001c0010000070681442035800c4a101201d074122401c040c2d680000400b0381c1c0c00796a5001c0c5070706001c110203000740c02c200202c1e0f000d800c148014069219103003069620028000384098200301000c522803800c143c00b0f023407801d80d820000d080e1a5881b1036041000e8042c098a10800c1c0c089d80c3c0350070043c1211007000c81c4000645200081c2802220303600803071100700c40700030842641d05008080f501130b10000c08000401d031100f410006982c0725071540c1454000d5082c010030512080c0390400070400000c0e0640204d562914125401e400b00b9000540c07050541180700c40840c0d0000c0c90f00c0c140054040c1c2104003600c00c000040600b24096850300d80c2181c042c081d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 500592068 1250 500590818 500590841
    0x7090b040605190315060302180402120c030a02040e040f020306070801050d06090219030b041202031c0e0a0c17070b16020108090a1709030d08101214010e011e 70
    0x8041c03215102020201d0f041e907240303504138a0082031107142080c1c10300c10740880e41d00a1000c84d60029070590b607000c204030202c8030782c0000c84045091290b4413241040b10000100206481c4070008000b40c0d022000d981520301801c51140d0042d0a85403514060015004010090380b082c810000054075440c0301d2104030303050324406031404a030316003159501c0d0f028203070b4450300326070004039101500c41c5101d0700c41501c402140909090382d52030410342800407951552800110440d0810080429410200b4048003252100c00310000b8070041c0d1600400c0c10414580c900503c4007502d14800124400401410b090014030242598100381d40e82280a5040c8910442154420842c10604e00558000c03003000e0751101700c0c0c20503900b1454443c0d946d040c805414800c604051180414910805e050030001c81c3c00400c0d482c20110018200489003c041d40003d10441c0c27030032642c050315482041440d4a95002103040c1d04024403000000300b17240741c040c0ca00c4070000c251596035a802030300a05624001d4201080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 500593318 1250 500592068 500592077
    0x715021905190f1a010512061314010b10030c0e010309020a030201030c0912030519030b010905091306020c010e12030717070e10080604150e180c03030309010507090b0406 75
    0x103020040324040400b100000d0b100c203203001074070300c020400180c2e44a0019002111039000c644c10a000c1203d0310200c001c20200c10351007841004050b400407102c42c081141c00007460802c026850304031b10b002d450b50b0400150000101303100c111046425400c41901c102483d11900005014074004408807041c600001e54011960788003000994020350000c030b00f2013050b1a101040c0d9840d100454400100b14004030006000055807299403d10282c14000c840100d00e000d100049810b40003d1100c00c0a0103214070440c0c443c4049030101c0081040920b0b41a84107205649403c03224042c00c0c001c00000c461160303980550142031008000c8182107900c584416203402884031120070320072403030203030007400d150a0180c1104040401c0d03941000340c4806541c0c45d59060b00c40c1c40c05405200c1501d90200301500600c41511702840700d108131400d140d03804403c82e0640c4072000815901c8a16154200d41540d80500000050041241064218620402c00c035124140700300e54030500d154032031145107e00c00014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 500594568 1250 500593318 500593333
    0xe06240a03090c060504050108010e061f36060e061206030a170310171209030102090603091506010e131a061c0513240e0715021905 58
    0x405405440c194085150008a400881ea5407480070501900201d02003100403504000c90b6900002e02030142c21400002082800c1050106842940090f0f00204109031503008642c11440390300c8800801003a100c00f880d2641d0b01d401800c4010390818454a0f00d030702403000104649000750340c1c842021801601e841d03d060313100090141d042602414442d8140903144940c0046010030080500100300f100f14142e90b13040068036a0340f00002d5504c502c051034103a000e61140300390003255411a4106641400e0750b0f601d24080081d00a100d09682c039a4080b10220610002c000002008003034509600c1c00c2a005031600130041d504040034600c0309600190004080560000741c4d04041200c40d40504408800f50840c8001545604880c882d4a41c00d050180b4680d40c0700d109006030f41d00b0405000c0038060140c00350f00c441210717802502d01543c504402c1c1d214110520060303800344481c5034081081d103005545500326820b200c110071441c0001481800c0c9650300f580200f580385c1c0d801301e03403203402031440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 500595818 1250 500594568 500594629
    0x91406040b070c1203120e0f06010528090603031202070221010209030a05030a0207050a03080d05060a0305010218130b091902070c0801061a041805040602160c0e06 72
    0x1948490380c12601c60401d140000390044040140010040c4207417aa40602d0512040f0401101d806407030300e1030f82da84003901c005c6090300c8c0450440d041d99825a280f02c140303400004103a5407110080d40e039400300d075030b40080050031205541c080003c0d24401c1e518400305d070520400420a0307003d000d10182d400300408506100103001a2106c440e1940b035200003505108603100041d080042500054655030000a015420964180811005840308489107136100b4110707203d0380d1180c003480460808156548021a89542d00c004440d4029a4271034006c0d50794072a84e51707680300c240d04d50101441c016181c3c4090300d01880d400f4000d400803210301a11056450762101e490b03201600c4134250800e041603080040c0070218001c03981a901504058001003900c9151610140d404203000042c4040368205010601401c104503003050399410740e052022400ba00c07141000002841100c40582c001811101403208001080000404807140e0102d112102d513124810310110b07507d040d84010340b03408070511218a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 500597068 1250 500595818 500595839
    0x10617070e040f1116020907110a11011107030510050a1e0f15090e06090d080117160e070801080c101d04060b0403051b0a0302010e1807090609140604 66
    0x5842c2c007081c0200b60f00c100c1c0c1c4d007400755a901100501050818588054007542010101d00340c01400c4c030320b00f682085038408013280d01d13920f4842c030042c6900200802841e10703a2040421400c081d40c1602600d0030140c1d0303458001c0d40c44c10b01c044038010050801c0005200301c005441080401d8000c000030585054200342c401008010015415040a0340d03200310410080f00030169201034060a8000901000c03c0244103282c5070300180b0b690450f80c05960030300c403d50781c4644028111405040e442510400c2a10070900f0602006440a803041c0c800340f0014403c0c0c1608025800f40149480300002e80e40c943c0300b020344800f1300511003a041b1502c04900841e0b648a500c0f13400b1100308814a23400315045850004c3c0c01c1d1483c3d94000c011541c004182402441814001c045601c944400e860b068000b4040204074500d01070b02c80641801410a4502d910b61030710700729016071690100f8202d815182c483c0300900381c10100c1c010700001865403000070483c40d8088072160b81800e0020802070074586031054810 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 500598318 1250 500597068 500597081
    0x902060a0f20030405120601030f020d0501060e0a022a03030c0919030f1505090a030f021c030c020c0307081015090501090c0809030a2003120f010617070e04 69
    0x42003012034200002c104000300410120600e400c070107595034070714180402844110702005a4000c2d00100010000216203620680f003145e416680c2507441e40391400e201d0f005090b240d11603a01c17500c40703c00700b16403270750365600426142040640244c0002201c0300c4207101d1190080c01ea160692081001c40c14807680a000790038000720082000c000714018440c40f8135100c10940c0111101c42c4244020700070480503496038003948000b03a1003003205103411410310f0b96030780304040c000c0d0601c4a0500e0b244107041c402d003c2c0301002c000604000b0810004800020b0040020b81450340040c0a00541c40599250205001d0308540225000b03201000d5180708810050000e600ea031401c001007500001148820750281c00c1c02880100c80020704a41014009445a103000b0300590483d00100002c00c030745600b044e40c4641000181210100c19800d40b50820b01d1841009045080f000d1013030100000404018034144c142c802c5030380ca26003141e0114003421803041f006e80c0d00c41c021030110044010141440e030b1016 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 500599568 1250 500598318 500598347
    0xc070902070213051b160f05100e030a0207120204090f1506141f09030f05010510050d031b140102180f03030901021f090b0112020f0319030c0f02060c0a12030902060a 73
    0x4000e0980950384070100c100c00c7e5902250300341c10498166070091a244948a940302500b0040c2d8a0201320306000ad403101c005008030320350400743d441c642c019902d40754014140039500203c090032411450403c4500c1d440722084e02d14401d404c0540214000032400700c802c080350006420680380210175058200f402600103230040404c045494000082014003924800d100e0080000003002d09102414038480c40e0b031908080d01500601c81c000000983c4a64074000701c1788660703d00300408103540f8110b040c200b4000361000d200d6001040000c515150100f40f0b400b07041046851045801201051517100e00a4080380740c007513081804c03110020f2004000014500b4030b0741200080d1580715680e0349880040a80207020141200a104021814041c003a001480f03c101d00524181c084c2807a41180451401001800c200c00b21903c5c00c20002c0181c01c8030070299000700b0f419164511031486d107554010204054440764030f004070021446000b403180a881c1500036001910301b00314941c01f522106041010b1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 500600818 1250 500599568 500599597
    0x2405090408190c0314030106080a0b0a080708070603051e012c0f040519050d030207021503010303080f1312051b0717070e060307060e060c070902070213051b 69
    0x20042071014010b20700d071102c2403984034040280001d05000f4003108000b4000c608040d0b04000612407950098001540f1014044000c1a418515004280103010a510000c1c81d80318044000c5103c41c008106401034030459601044681d80c3d04840c10000011005c0b102e658256040052180e408811103002c4a425007940300784518400d00050001075104072240110010a03c091000300301c01071000044880ba40701d00c40c5c0d10601b50b6102e0989640c4001c409906140d400950a011500c2c0e440e2040851290180d840740c5a6070740b4140502852001c40e0703035842d00e40c034141c00140d1425191000307400d00e541000501c0c41d0300c44441415206580131035911206054420300d1a1110f14003004054081c241c0584110181d19600b48114601121500b028500001000800450341c90000310501101ea151a00851041c40c0c0380104285220355031111031075004150300803410079242d40040011510a4405040d02800391400c503003151016551010784440c2c1103440400c1d9000e09015040d6024005c81 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 500602068 1250 500600818 500600827
    0x1602061510020a080f190f021b0f13020d0e12040306050c0c030c010c030e071a03040c03080c0f0d05030c220b040e0907090506130203070201060e04152405090408 71
    0x4c6181d1036401060307210b21407400020340f00c01c424030003884c11a61505070781058181c0705103108002e925494051100b9140c941070030711110150740d900c0c040303850f4800064030002c2200107080700d04020358040754861035002c0c1410100d0303940c0000011020394100700251014105400c6580780c0c409410040c00b40344542209110503003028030148014154403400c0400000c410450b04001303000e440301d00212138031503041070904115030390718005010410003481c8005a42e994607854844250340382c9800180152601090844101000180341c4000984402c1118246038403500708580f13511044600e400c50f44d8041c0f000d00f4040340b002c4851240c084004141150300c035280e40f088051034000d0340c01105001000d03414004c0012052219001401c8400400d000c01c0c50a000800c02040312500c014603410317800000a41a24401e610110140c00602d01e120707207504180c203008482030761014031403003254945841c403081c0010034504410051405220030f0441482c1034100112400001c0042d20608403c20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 500603318 1250 500602068 500602073
    0x106171c0e0a0f080f0c0f30030a0f09090603170304020a05030d03020d150b1608070506010608061008010f1814040b01170c0303180d050f03031602061510020a 70
    0x40b0f420241400e42c3c014819143e0600c213051a1400f0000d0f0700d402000e0041031802c05031101c00e80c14002040c0c4841580040480d10f0300c0c440700b0107000e0302d0400b05002c081851003046a1011603082180030990311281100d480741da03c2c004440c8144401043d04203a140401c015141c640055948180010170b45a4502d907a080424105140b14400c1e100083c0d0014240205d2880340c850100440a0060241c2070a030620501e800d052044811802d5060998241d10301088420303011104502c4e841800d5811959403090044c00481c010b0b01d0540c45108803014500a8911a02c0344a04070390703101f100d542160303290201c2c00306000c0386142d081191070740380ca04072100c8a4008085c540500c2c441e0840e07029175171500444130082c200c0e0080d00e81d0030b60007951640240d0744c0c00005442e2107482c0780b450000e4011a0303800040c80c082411000410901541074608444000440503612504008582c011500c4410b81e007242c5604044070211035051028451000904182400094540c3d0500448203800c4054 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 500604568 1250 500603318 500603339
    0xb030a17090d12092c190204030320010c080408090105040801060b03070e03071503110c0105070f0e04150306021e1803010c090302130b04110c0106171c0e0a 69
    0x400143c8a184030450408011540300a1800c010300517070003030b1743d040100c208030f40d90802c110100c038070000d0302d4a0f0007050000850900800e009400b611086640d0390f40c83c54090212919601c9003041c00b01c3c2015810400c00040c041c1d100300c1d604d50794810005907074690742e146458102182650401001b80b0000c0303003840c424841c04000d0502e0000b113581341c2c0303040344c0002c240402200c0114040d401420040000082262800040041074103000c2070315034104400305d1701c42c024041400415820314042c44440e54109562040003a810740d254103103038500c9801c3c041075a00c01800c4002c41d0b12084001c202050b0076030f019040d0010245051454200c00d00f8400c03100d5080070a4180e2148441c1003c0c06a6140922800d8171b0700c0d599090039510945581c00041d6410000c442c0e186c885038866040060a5407140d0007840814145805a038035220b418038454020049070040500c3e104428500c12420740b8006030a041000702403c4004441c10301e40c9080310174075050b40f001e5410401000d004170344507480 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 500605818 1250 500604568 500604589
    0x50d0f14250e06030102042301031b0c11030325020604080a03110105011a0406030c020c04050109060915050d0816020306070804031b020109090c05040b03010f050306010602010b030a1709 82
    0x11071a804403503081c407000342881c0c0e00c0504080d00ca68410001080800d000303080c1d5540301d08100405010b0003c0039001a0061f050655050301e000303003042d005408140e0015140c0440f140140008400340b4481e000713240d500d00c507a4107000c0d01501212810301912910340c58085100b48068006c0f410326070b030745811501e00122f250044000c1800c84c04440c01183d02403080500400c01e0751240c4d402c1d802d0900140000c0e224074000c0780700309030300c803d911b50115008001d01d10074914040c004216942c0c2d03078030010008241d0f43c0030720b0140700c2c00d049400036400080c0c0e680a056540003000d2210f0b01034680e0300c52031a03038080305141d031503202c90800c00f0000d07941c1400414422030b1580c0f5a140c0078905440c00408540e0903000c0c0d00c070f40c5a542d114403000f60f6840392040b000c1c0e6070342440006035040701000c182c5040c0116409121003040000002c1055114220300200300c1c1c3c02a0200c2c1e010740d0301c62100342d00ba034070400c1d080381d01540301000103400b14201144648551415503080381ca000620700c08500e0304d058 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 500607068 1250 500605818 500605873
    0xa140a1406270f07020d08010312110f0607050d0f02090a14120a1113050f040201080a140103110108060a0311100504030b070306080c180f072703050106050d0f14 71
    0x2000400c9130b100e0301401201005007403450101402e60441c0e841d04600c40512041c10100445640f074001940c2007004030030b225000a4ac101c1d00c0c0c038501098014142d510000c003200c200b03402e107007060103d08280e0099424608000340000341050616482d0000d81e00940c000070f07800006007448131040b40050051200c80d0f030213480300019080390b2a00344581d03081e0301000f0302e540c00c1c0392808011801c2d06800e503150b00b040c0d092070068090707102d011901d4050081000d0300000c4c403082074000420080c2010100248820030780341c4226a13901e0004100c0703a84860b01c005000e040706424494220720307040680043d4004c00c0c3c10510704084c2c807a12800300449080703500d0000f19030303105014000ca801c20840c2c0e0703040e09070480d5040e021a40c034040c1100c860f0406000707161203481c01c1c00411400e50150418025101100750410f00003a07070200c440e182081030341b0040d03442d94a003080106040c148030791107000440d040100d840506101d56100c0140101a942ca40018014800040007654012000032148079 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 500608318 1250 500607068 500607091
    0xe0904060b010315030f0b091e060402091006020703151b0c061103060d020108060a120807060e03160201050703021e010605030f1c0c050304030b0a140a140627 70
    0xc52040026003101c0e04441c102c1a00d0369500002c0000031b07030761030039a484150f00001c0e112207a01d0701d00c1401d141034201201120302038000c7c00701012100b000038400d03118a0084032401410788940d2480c01c3d1b400200d00405006030484401840811500c09491400035569400013501c080070b01400c1240920140250002807400310703960302401030a00403946404002d203012461400d003a0000381c030070490940c000f4140403c030b5000440713541d00d506a100040902d0030034410b01c080c05183c43c0d8280c0d0300c0940100d445a241840b100c1e4220070010a5408940d000706200e0040d400366001940c03d500101c03c22021071040704003180001c428060003c08800350302001103030450500042505181112007600d54a901c842c14640c65008800741c103407034083c2141042c14401d056400c080f0300b14880c0b6000546040b13100070601c80d03d014194000b00c2c682d02180d1146846444845014054070b00c1103032184540c0091802146a501d440300006610541d81046140c3c083c80d402c200010041e0300301c0f0380709c4008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 500609568 1250 500608318 500608331
    0x301060f0f0806060d09050f01180b10080304090f0e01061509060212030a1d0a080307080717070305060a03140f01050609101208070510060807050103150b0a0e090406 73
    0x1d412800c81c40007001ca40c10102860328103500031806501914a20440464540001c801488001d00580390342d400e16500910660015210080101040c4d10040350207266120014011030060700c115000d0b507403818040e5252a1424040300090100c8017580301132250348000500e0220340274072541000b8007440020f0036240545085c0a40080c2e800e50040d8155040036010300020003011088942c0490b0003c4d0000e1019010300c110503d805400c8041e0002c0d20400380d800341882010009148101c0302980d078040580c2d15454115404001c01c4200502d00c004070000c944054060303003103158007000240400c15400e907207446a050a09480c80200c7c410b070488a01c81c0b4020001b030003690740c03058003503800300014103002440f02000015449070300c80e046c1600c1f5500342000002030443d00201d03005401c9550380082070301c1c030100030045445601824455440001090350090048178040014120340120061420aa41200d83e2104040004001c083d00108034207940e13000040e800380e4052440040d04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 500610818 1250 500609568 500609597
    0x6020702130e070503120a0504152303150f10361d1303031503140c040507030e190203070e040515131e0f02150706181106030c070602030106 62
    0x10804400c6c4850b500c508100300d060f142541090864044460714440c0340c4500507640030484d0b8162031843c0760400c4400800b03482c2e00e24040b5001450141841001e0b10600403900001c0186404640d0945500801d03d07040c20a03503e0300420102c010301c0400241e02ca4000c41048100c1801d40e4000181410700706000c5091000c09528a540704110030f404812102c0c2c2d0500440d083c00040d5070020040405846140d0120b40030310b007402d2400156884240d1044851103004a03e40fa01804600140101d02d81800260110b2090090048400038803018041c5094000740c480444081d54a0984c0c041c851420000749103240c000769644282d004e240a420300c10515812a040104040e00002141050909200128010b0058000100d418480c144a001100d142c403c610340590f904c065407140083c0c00740780c01441040000c11035540704e00c50810004400140d40e1000500a0340042c1140100440e90040e50038004000c503000041c3d02c01c02810710b00251381d1401a40d20982021001540f034000349030310b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 500612068 1250 500610818 500610823
    0x810050109050f060d1b03120e0108061e0103021b03040501090f0510200a0606050316030c06030b03101a0909010c2c03010e060105012a06020702130e070503 69
    0x5001e00c24400c1c052030600c1400c501e1400d90160082c0e110310109240042003118155190090316400202000700680c0ca0610482e80440c0008590100d05038000044096100380c040a1103460000c00048200c03030410b9281207003500080c1038505050307080101724840c521030200c40d0701d20001c00340256030b81c50400c0001444280268001404050306040c207201ca6612414a0f40011101c2e00d0000d1004480c5514066254144038011526009a400710018400c2a403c10760665070140c6c102d80d1440d41e48420040800302501c006007070094154820311031584660040070b40c00e08014215542e51480440040031901c0942050700070304100c1d207031100035007490080c00791b21600b4000204810110004050100b6007069041821007400301d8000d0b03107800c443c1c0740301e62107000068000c0040003150a16503584110a0051602103007441c02c203d81840b049400c25007c84206004406c00d01e219070751480081c5d04040c4e000c80e44501ca10a45581c507e8062086c2442d840b0044014401c3e0751400d0217060 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 500613318 1250 500612068 500612071
    0x28060518090c030312130309120c090c0f021b03011d0318010512040f050f01020c0304090b03010e1009030c29090f0706120212070504030c0f0609140a0f081005 70
    0x5009130014881449031241805021b07038024100d0580c21104011840d086503500c2d5150407000001c05141210700522010b13160070000da0b00c001c0020400301c115000c003643e0640742c0c11090001a840075034940b142c108030010740141750343c1c007034000309520892424070007213510307068004200c81c0e1000c02d000d8042c400400781c901c0401c0083c2443c502d081032045100082103001040030780031030850000314003000810003049502113403440003107460310a20400b103901c0398840d118854502d8100703030305034405250600c200d0280703c80210052600d04088004c4e0000740c051403505a0a1055402d2404041030b801c10807907509001c4a5800240400d4200d441107100f6000f4100c600c0e5a0303c444803500c1d01c00360000d210030548170b031810520042040c40c40080080c1c8503000a8a00d05000342c0203008015400c44064420b0381e100310b010895080e201c21004401c0d104c1d80c407854000941801080041c01e90404510501882c003420101c0e00644031158a07060f8400d0340d0103000e15500158202040c0c1c1550711805 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 500614568 1250 500613318 500613343
    0x281a130312050c090607050c060309010b0a140d03080c0d111224041a0604030507030512030c0906090607060e03210103050a020108220b06100201052806051809 70
    0x40080341401c601d0403407680101404c05015920008199061000c20040200401d6002305001e5230781c03500d080124042d019601c0103c0c010483e80d900840c03064090410750f8031161001d03040d00300d91850358604683c04c0b080a03080501440d0104004085481c9500540448480b4001070541e0742d080e40a601c10308080040c00008030060340350040b10403e0013021105805c01040b20086003510740005070034244040d0a81441c1d201500140000420001181038002c480c0517005651107030010000d81c40f910301c02145c2c0344031038803420440050713075240800140070b125034054002414010b071503550383c08a42e034500310100241d001051008500c01c00712440b507480c86004142054552444e59056a115000c0340d000381070080c1600001d01211764494401822801c414400004e0386682c00c02610481c8280d403224090314200307202c58582030050050601800b5090080b41c01d00303420841c031002207156041c043d00240d0b100c0800241d01e6940c4008840b01d16000c02c1c065500e8100303001c49518081550303040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 500615818 1250 500614568 500614571
    0x4030326090714011403251d040c2615101b03050c0a12080f0f070e040e12090f03120a030207020310020c011d281a130312 54
    0xc200050300045600b0302155280f001000e600e011580058484a904140309030450301e0110404c40c1c040c00550422145c0415100035030740c41c20710800100e914000e4080d072175140d250b40404044007418a5804400780c124a89026568015004030240d684442c00c41000b0b6000021002d0240b99003e40103140391004003203421500e0f0a22845021300384c260207808240800c50b0440d0b4400c107250042044514120b010003d4a00c0141c032881c7c2811100300c50319500c0001020800051040461455014040d0307402280e032401f540d44060007114000301c400f11350b941154407911641c00600081290842c9200a5483c1a4070b03552030f81c0a00680b444042c2a0503c02e5110f08115610b9090980403241d120034079140c090313590201800480d140000c17007208111101d1001840701881d60040d400407500700c13800301e81d8421003000c2030703512aa56181000785103c10820f104040e00074444c00300e0f40300541440b5208140c480034240290500300f9074112150301d0075403014107000d0201580300050b884d01074034a650 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 500617068 1250 500615818 500615821
    0xc03110c1002130305011d010b0105120c21180c0307032102010b151803210702030a02031207120302190e010c020301090809040605060705030307180b04030326 70
    0x12055454024184000740c03103600091680442401c90385502c051600000240800741e50b014800000041031500211035500c0d043c00041250311410480703e0308440304e200c106c05601ea4104804a40d0701600c0c00030441c48900321030701c0320403c1e0085d00901c180c500301c603401c02c5541c15125540c106081240514884d4001c018240005140c41211983d560020703600c070034608190304402e03401000028a066400240d0b54041141110410000d12044107842200c0100722406030034544d40c0c40800110040c0e0b00000c0340c07445c004500c1e2901500c8e04500003001c0322003400c465000f0a0500c24a114641d894803c009999400c1c04a00c0104444c443c646290840c80d007142402c5861240f004841040200140a095a081e9a00c100381102080350020000c208181e240d18010000b9400070a0440c081c0381000400600d134034050043d100d6098200003e1840c550740c07100d04075410003a80141d1500d540c0e01d43d0010480040301c00c00350014510a0322400211189030f0082c14040b010008010740c454030740d40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 500618318 1250 500617068 500617087
    0xc020102071a04050f1006180903020a030e04020d091a06010203130e0604020715051f03030c020f040e030a020a0b060d08070308100506210c0f03040b0a110a030c0311 73
    0x240308400540071071010b0016480c2c52500904003021280c170144c440c402c0d8000802d9229040c0d000e142203417004240f00b41006400c85c03002060b140c400a001d00587c0101400c0d03004030340525500d500c0204000c100514100d1910380c0e50007107a040c4a001da0f08104102120000d007040310030500d401802c00d000460420300e000400c1c040103121130086c030b40e46038190000700e50300340c48036010b80d00d1349070b07200680301100d624007215030b4003e1204860000d0690254185039904860403421001642e40556411022642503001c1c0240700a000d403046410a5640410503541007081c800782500c010f142d40501000007150910007640800078058074800c0800342c4001d000610b41200301d400c000e525003812070b00e83c2c0c3e49010200d03a05101d41e014682000000414071803001404264900c10300041070511501c1d01c444a4010b424000c48080c1c010015040000c203010450140100f544000604e0021440c0e072128804a641c03a044010401d0200751502c40304007040b509801182140c1e00c034410140c2c04c013043d11 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 500619568 1250 500618318 500618333
    0x5070f030c090e01020f041202010e240310030f150f1119090f120201020f03090105040512010b040c0509092404181202061b030c0a080c1614010c02010207 68
    0x42c851080e4050380c516507903c12031029010348020b080b0301c1d031140e0344495841804040504070480124001415200e84003014503080041035030203c0b81d0131060301c181961291848040c8e001815420300389c3c08944000000806906098980c41d1044840d0361750318600850341002e640e1403d810f000042d007441c14035203581e000d000c20b507100c14182038502c15141d503604001380c81000081d00319001c040d5089002090355603072407107050301c3c55200780c0c202d424461a4000b199101d009910300070b4001101040200020703d40a152b0107888007411000080070083c11001030220b42c4041340c00710100da000720b0344010600d0409080e50f0b01c40d03140010b0303a0117190f80007904142043c003004010721440d51407464007416008500720811440e40a02c2c1a0024084090003035030325902206c0340079440814440303c01d100501354080d280a0b1800c1c118070350911841180c141d0b6282d0004001c820381c0c010030b00020700004e0345554a40740c503d000d401d4245115060314516802e44050002c6141960300401c844000240380 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 500620818 1250 500619568 500619593
    0xa0f0903030e060306120a0308070f03021602211020030601020c04020f090d0809091602030a1d0306040c031e02090105040b150c071401080c0711060c03130305070f03 73
    0x4030342065070303070b540c902c0010501b0000415000d0300341b146940c00c408258004c810503001d0a4a43c6810b030055030b540c90120142c0c810390311096a4a40441482d100504040040019441400101c0d450205910071507915044200c901c0402580d101d10030f41c06565504403500a681044202c601d00e07600e08100042e644069a80c00c044c02503900140c0b0701008120741c800d403402582e0040070081d84403038030f041825440c1c001c0b41480b845101c20b28007051100c22141d0240503101c00301c0e00075600300380740c2080c243c40c2458110300078440d4680c0e40c3d4250201c2d0f0741c10300c8034510980c0300c0e44003c4000d07400d500345990000400e4120345003464083e603003580581e50b40032040717044a504441c0411b030b203224240416840a0b40349600d821071000442d00c514040d00c00320740e4601b501d206940c00d40c031201ca104c00455000105445a41c003c200070004e08000c500711540c07182000c0f0b8007600461401c44c00b05c95032803a661150440d601040050790080c0208a01440140014020101149240c608544424020702c2c1c5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 500622068 1250 500620818 500620847
    0x1b090e1608150a090908210106020a1101090e0405060906070905030309060d021312050f01060303050d0b0a0f1d010f0303090b0a1701090501151713050a080a050a0f090303 75
    0x10005440036030390350b181010103040b08480504c1704011525001c0c0d510780080c040400000101100401c070403500e0040103040303d000b5030042000d010305844040703401c0c041b55082410044510008a00e100c4041405400b50b03101d00000c2900f45440524282404070182200d01044520703802003290740c1e000001c2d6080c2c15000c452640d91421103000c5d1b10000d2103654141035002c51001350004080700400008110b242c014001c1d0b0700b81140401c81d4034203c9101d8000100442e009100c90a01c0e412594407102014802801c0028240c0d00e44d541c1003050122948043e20360031040082d51903c0c6a403a03580d5004020070681e610b500c60840d58040c5c50f087c04d6000e40400e1841c00304500004030f10440186090036036406a8480c203586900d20040a03290900881d41c4843c0005200300d01c05100c1d0900c2c214000c0d1180680b0000e1719408052507212189503c140c071544a45520000801c088a0062940310240c0d12440c0d5580c9410070050f040003003c0d0f81072018090100720801c0401c2c3c00c501a00b4001d00e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 500623318 1250 500622068 500622091
    0x2240105010f050d050a0b01090803090d060b040905060412020c030601083d140705091f03020708030c030604050702061b0d06080f01050906010b04081002030a1b090e1608 75
    0x2055000708079514003030040d51104c010308040501c000d040d11580304010803c804e076186504184c0301c801c9145d9034400c24041c142c2140161105002103400d6a0088440510081c804520300711291039062420b1426035064580141e04840c03003200640402440e40711074415000b4003d00d40c034140005131a9100380d201c5008604000b81900540343c80c00e00e0342302c050102100110102c00310410070f0401132040c06a40004482d40303401040b5a64050001d07900072450041245140042112600441c050071140700000d140d024041d00d0b000941d0040994403c190888810742c503807812508100550b04003034681819500300000340a81c4d2490802c0d210003e08180c040a035071210f840064400402c82c41d0712400c4d40740244941401c0590040d08018001e50106080310150703603c030305081e03c080c460b0340b1507215260700a40c2082c84400c200d4019550041071030500003402150408e80b82545194000b041e0001820910300f4000c00085c2c1710101e41008032600101008100f004025102000c003800a02480c0b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 500624568 1250 500623318 500623337
    0x150f0b030c16080d15080d0f02070503030f030f0703060803070b04030c0f08220b1608160b180a0807062d0f0f090302072c0c04060224010501 62
    0x201c080720100c940406203822019031907106820640304942040f510396580500381000d640c40c403201c069240042e940305101400f541d11010340d00340c503400d81e610003060660140107400112540c2c144044c0007840c181d250b0301035503860807640600c2080300042c8540c084c9440d00100384281c400000c2515080e90703005039020810780756418251404028a500145920314901400c0100040c4801801100708814140e00c0324000070f024081e60b00085000310b41403004144044070b071100d01613489448941c0600d0091385440070000614120b051100415940440c1207024080040c01f401d4485496440c0c0300007421218850744e44856042c4079180d0046d1110741c480c074a2100079485d13031080070040103170302d4409030a1002c1140740c800640102c00d2600011b41c5007800c22111440b01c0e001f81046294503a02503d40c81d824179004022601003a00d110041411305003190282662010000b405801c0e0318080315111454084000d292101d800c0d509071219159582071001c0784102c2e031455065420074204035176070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 500625818 1250 500624568 500624581
    0x1b09041e080f0307110c0904080a120e0f0a1a071709030d0e07091a091810020a050d0b190303080a180f02030c010804050c0d020a0e04050709150f0b03 66
    0x380c042e0286010202e0030000511032810b401c040040446103105054034001800b86081104200c0110790207483e40b8410086007030304038803c0c91303c4008400c04000010b50058840c13500c904c0d005c0d0805a078407669110000410610000e00110401e4805810442102e490410310040c2840e00d4000007510a15218010440c00301c028415600e5100754040300700701000e00c3d90207584e510341407445102002ca1a01250340345a165002e0b440b89801d00250203000207483e42c942c10065442c003080214800d008509600b00386107903500060171b950480740da80b41e464481c980000412a00103030001480343e00c01c0c061040d51003048000c51412aa054105007803190340d0100d0307130f101800900b60307071a400c82c650b0320720001000303070008030410010b000390115401c03540b01d1001503c5841054070040c0c101c1e8000000a0018a84601c07200080c52001e45145240b5682d881c04003002e00d0143c508507800d80041e04140800301643c032408009001d80c8518180036454001c804414a545000d0000c1140d40000003c24 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 500627068 1250 500625818 500625833
    0x70804031a0114060708030f1e0412081302030a02010c0201360603050601081f0509043e09060604050306010e0411030105011d1b04081b09041e 63
    0x15504514007005280059180a03a01d5200340100400e80c282049014114280801030b030f0200d55210810510b5901d65585119506100500a6401d4000e80a000f0355509038150460b014511540056011540c1d4120140c08240010100b44140d4100a0b5880143e9000222000c2d130680a00f440900d400407400101c03140003074034a92503c0c0482800e00d644a0141c0d802400907221804000b100b501602c03a0f40803021b4910690b0324030300144034080030668151810041c0c2405887d000304511304299181e022805080007204c0c15980506100742d00c080c4d4a15540043c109e0302e9481074204602043e0018140b01d003180080c1032070040f1304900014400340c90740030442d40908001011140d036582c1d14400d164161174116011900f50b108000c0d69825410705000f4103050b6085840e2442404141d14104080000c00400e800041d445004807928250289001030014002150140a500d444468555600100b0054007406001107408100c04220800800c00c6c2111280038513102c0d0603c203050490 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 500628318 1250 500627068 500627077
    0xf06020a030b0a17070b040b040e090a1203050703180b010b0c100911010215060f090c0d0608011d071409040804091109040608300c0f10110a050406050708 68
    0xe07007200382c85002085140c181e01d00c407100413007018110f42800340c980811034800c0c0281e111b80d14440710705002c00d001151404807807641c0b10703082c04100c4d400010962030740b1418008040000e400300759074505001e00d45506000b110520041e0000201c0b400100b641c0d40711900d20140300f1050122404184070640039000c1c000d50301d1901c22690107119541c8a07003460000034150240140c0548510846a58140d04040f0320500c44c08000b00032020501e1000c0038040e01440c018000c503040001008445900e0080d40b088c04043d1040d9400001d221840301400c00c1c6421034400780003034603070086008101420b00040782588042c0240c40c000b00030340711440c10074810f00440e00321038005801c0c03c2c0b4207084020762401504040004950500030669588203103a00d56441c14a10084003119610309000051410303042e00c5656154503c0c40d00d40386000c11142d00301a880c02e041036540e0400c1036910154459400762102d042201d0480d90b1408000ca80040d24030b100318800c9600b403010100301c0301c09118400c010398 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 500629568 1250 500628318 500628341
    0x160602031f150f0f02071203030b13050411030312042d03082703031f050d06090b10080a030804060603080307080702071e0302120f070b1306020a0f06020a03 69
    0x4601c0c5074503079507110440490040b0000c00038140c424042101e0b80b003200000518a82c940141ca02075040c01c41c065091841d503d0298241034641140c0c031400e40b5001305000700d41c20b5000d40000c20f4142440d1012600001c034003118400e07031050007080c0d041c0303060410164100c1c8c1e000c2c01e40d0140601803494050203e010024031174144c01c80012801c140354006207403910801503c10020b0f80c8068811303542103100102c0c038150845a006200080e5502c20700682282818065409900b05a0341c1c0c00009801c4201c6100c01c5452a40345c40c02d080400000352502500502d403004403500d0a03082088090b5a04102072018081222000c040790070b0003695807144000d1078116228a99034545810003400c03222040c4e482000500c5045800940e40a00c05140503196800c0203c2c4060346145800b0005140c03c0038030154524052a24410031500c3e080101c00c0003001849101501c40488a42c005050340030b5603c868255040b005d03030400003c0520020820302540300000584a0102040440c01400e20ba40134 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 500630818 1250 500629568 500629621
    0x9040e07050303070503120f01060815040b060a0201020d140903190e03060f0103021305010b0d021e0a030902011806020d03020a0c1b0503010c020318011b0b01090510050616060203 79
    0x2a402d1005c088000c10b0b1034020600841403580720000d90b290400b000344103420005908401295100005960b00040d8010051002c01d21000d10000203116600c0700100c03a015031b500240c03044d10702d045805000081943c408600072103140c0070304215168030614400110a007070f071200c03c0314610300454404418400150440f81c1c20301c0e102403c000707100002e0209030720070040210101c101d50014000c030340c103a866500c01d003802c0c04411210840a9040000a040710007803140c90480f1981104c00030703125881041c3d0b0085040f600c82e00024000c000e92003031400069403696400e01100c0c0c0c0009131140b002950345801070b03694101002c00c0f00c50650340000100020b06c00d60101030f00c1112100a002564070480007042104441c0c0300a80ea00d10274000020788102c41c55070003d045600a01c201012021450101008802e0b242e1b642c003040807091b0448030000f5912010b100321000c00ea40800054402511903500d01044600d02101e1b0f1407110724014803641e0000001540300840712000704c2038015003440c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 500632068 1250 500630818 500630827
    0x215010b040f0503010b010c1209050405251106010302271005150a08010e040f0503040b0a02010606050403080d050c0c0703080c0d080402130e011d150c09010509040e07050303 77
    0x4031214035621038800c580000d10440c901150914040c4901d200c001c0050712107410150b4240e46079034050b82d2081c1c6074014010400030004240e1601c1c051140706502000c182204062651004003130040361316004402c000f030300c05105012a00004500707041d283c04980c0001d42d59130071504003440c0e58100740101024035810080c01503000c1210180c00540b032003100d104452505890585405000d9003410400144042c0f0042200c0082d0421041e0405e004015a00118841d900c80c1490350344650f10040142c1000151848030300e60a20502d0050b002a24205251905e50b0b11407041d11f0181c26400c915480e030342c2e00400c2c1d48042c61401c40c1c0040e410141a158080e9490074110140e0300059200e03c8680243c1c640000701c20310404042e0302c900c2c0c0c003d080e185843d04201d814401803d200829009540d680c06408010500e083c1c030141c2403011040c000d005c040031080181c0d44a141c00f4002e05454103060044020300c0c0c0c6c0140c1664401001501d001800d01e400000482c60a649648066018000000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 500633318 1250 500632068 500632079
    0x3150a09020304030806010509030a0627030c030e01080714090f030d050403150504030804170c011104051008010f0b070c0f06080f0f0106020604030c0501140c03070f0c05100c021501 80
    0x1c015621560180c1c9404000b544d440c0010348580c804c003580c20760f06800200c2c1d907500284917640003c104ca6000c61400e4610452a01c0c00c0d8040b0203840d6003540482c041b60340c030b00d0030144d100c140c040e0603079400e1800d810107051080002d80400c5110115214210300410061203d80314103180c1980f4400c02400c942000a0b000c901500d69031050205940c0b0096640a640d90003080d809428000c0d58141e54083c00c950b100d48420032400d41081c8110145075040150b140b48207001d01580124120070356407566a60300e0030040124442c0f070300c0e000c103042c401c0e074000400c40b035090b0103076010440302500303115039481029152009400309d040c1c01006070845082c0010407229446a465403140b5501e0b80405056180c5070950000c81909101d03042c0181d11280000d00045c0c4646c0e0410400b510407800030610f103031144103250403075004841c119842240402006241c42d40001809048546070038090f44820545e01d84c41d840c0e41d01f4210506007541c1301c180310203001d0320811818800d141c122914058958440 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 500634568 1250 500633318 500633321
    0x30702090f1b0909070c0f05030414040b011e0509010507050102040e0907060801140d020a1805100501110a230304090f0b06030c1903060b0a12050f0402030703030503150a09 76
    0x954405511592032a64000403800000c100c1e80c003540010302108885ea102c02c4105c0720700880200c00c4480301d607030101030000204208040d00290144154400d4a41c172000c0c01d2004482840d641d035810030002d486140181081d030011280b07200d00c44c0ca0510354a5010400680d860711580d0801061984001400903010380305081c034074001d14804003524201c0e0f42c0d508080320076000a004045000e0b01038603000e40f4a140000915408a1002d8a200d00003950340c140c1e65170904010100341d90040d00c07034080154210844107004003401d400d0800b84007000e294102d0540e540380103c8000c000240d055400d6180d026010708101042c0551001c41e0390f00c0362982c6401e80640901115181081d04150480701d0034a0100140c900c6070380325240e99400d00b40020078000710320358180c8003901813558524000c26000c0d40d070300060180d11141e0b1629012038003030750b40c00421100700600803070032054281d043c4001660080703000700481c0d030186480c030f84075110301d0890740c800c0003000e00403a8011304a00c000503489045 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 500635818 1250 500634568 500634571
    0xb0d0302011d0a0b010b09130c021e120405040b0301090f05030d0c0905130b0a0503061e0108061e040302010b0927010506061c09020a08010e070b0703050307030e030702090f 76
    0x180a11242040740c2c0c945507030760001680000d200040c0030b00140300101d240390103000b402d80c0c000c3c064011040707500048400c07181d8804400300181c1001089c12000d0800510455540c03001400410059068031003eaa8900a500806203d42e44518003c0c003240e40c02d401851030b464000c0c0c9490401031641c5807da55039404440f44052503405c01c1030310322030725000d40c910108403200038110002105003180d82e40d006080041f4501c4e40329031b91750390208081d1020484d042c0f00c0d401401808200e02a001c00c40440c400c016404002d582d07008c0c008015282a03600b02030051100c100c10521861303119460182c8c0502401c090b03a640082071034041000311204501d101c2049164841c0b0302c41e005800001142c02d0b501d08941d100c1e000740c0c003003211040d030f242420200c9451030b0011301c0c0080c2441c16a80082d01c100c0da20b1740001650ba44408400426240612070640201141104d4506c2e2600e82c0d580a030041c0001040301050590712001480442405c3c01194013442e80241030180c00d15000b22448405d030700 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 500637068 1250 500635818 500635841
    0x41a0c071203140a020d08041a0708070306050d050a030509030f01090524071707020f10020a08010f0e40060b0a0303020a0605180f010c02190f0609060b0d030201 71
    0x71010840b40c08001e04220b0703000312101d9003c1c10704c0718007206d415510000d01410444030b50441b5500001440080703600a4000c0d81250358400d079904200c034008040c0c2d101904032a2081c50041044000190f000400e501c240d503142c00c0207074580708184002400c2825541c5800310550a100d880c5040020102c1c4c000e450401c407243c03040a40c2111405984800300031205c180114400c400c81d03a42030031544940710380c8410984112000504403090841c1001d4030301c000c61100a80200c3d20b00310300c5400a0f0010701500e880d5440d251560300d0200d05003a951000744c5800090356000d0200d0520240d480c0205250400035880c270756103502080d5440075218007200741510014600100029649070003050310045a4251b401800c031400992110340040c480070f003c410090070715a90101d0104c00c00e03c0714004c404041d2000181e04460301c0c0c000f9040c020036009048802c54240402d41c0002c0c9450841d000d0709402020010703805d040c92500c040281100e1180581c480c429142c0c030010980c0c15048410b480d030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 500638318 1250 500637068 500637077
    0x20127050d0f080708030403141c0e0115080703022b080d09020604120b070201022a011b090812070201050a0e041e0606170f1b0904021b0d0e06041a0c071203 69
    0x801400e10038027903004041410001c2031400202c4581881241c0114504440c01d0000092a8010b155001c80024103075001540a4010500400075440d00342490180c4651480078040420103103484541a040c9000d401400b8940100d452a01d004103580450705466002e8111a611600c90608040c8a1300440d411203603010800d000800036813042c001e84041c1d400e0b14a180340c0c13039034803011030550255000c402d0b10300d01d43d40c83c0291070745000e0b0355882400c1041213481e2803580b681171042e03460900e0f52110003d01128001c10030140182d0b4400e040f980b58103403a10300700e040b42003003400003009003034004240903100000b414503018031100341d440b0b10119801e41d01c031140131842142130103c5215040b24610001000c010000b101a0408444556240c07036980d2180d141c4944480058100e8100181c5084140802c2e0324900880104000c00340110844e0304001040152580000e1502c0c4030394000c58803000c420703584081020170088107849041000d1800e40f031405848460501700410040070030f50004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 500639568 1250 500638318 500638337
    0x9061506071505100801150806011701020f120f0106030606020d0302030c0d0f1b02070e060409020a08060411100e150913091203110301080d1b020603090a020127050d0f080708030403 80
    0x7400d951f42d00040322201300152020381e00e40002070181c02840c5030400c0ca59502040f600955080c1d940041c0406081c4207030360340135414205904a82d11405800001c1851324085052105a03000143c401401c01e0305d142c056500da65802807108140540341a240102d41012121000b4581c4e0340c0242003511440044080c0b0800c88000403a654a001d21032260381c20200d501150403030070f0a800c91191a400030b0603441610b13030b407000c0040c64000203c50a48002030030b10303050200f0f0b140201950303101200d98a02403004030039560004041500100d031841628a00207400d2440c2d455100061603216804074080100c59100e0400700358651101c10840c00207850080c03c0c084c54161001500e06a1b2150b03002445503500d128416034408014a100c0c10b81e0b4200300c00300d240142c0e1440c0080d4460203540c00500441c9005100142a001c4900510032820160110307480e0081d182200b15800c48400300c2d0500c0000f0200e007850131501102c42c20203010607200242600038092440000d60103244070390f40390784d4034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 500640818 1250 500639568 500639591
    0xa270303081e040f0503040f12060b0d050312040302010b10050c0c03011803031a0a0b071127190509060f0108030f030604020703030b0a060c020909061506071505100801 74
    0x5100302e00050700c404a64000216000c28100900381034014485d0040341e01c2c0640b22068030740e4900c041d503c0104102040301450040050320b029a08803142c054816a82550003503440584901a82011942c120310b03107130010342854801d4000e42076821f0050180188580070210040c02584512081c0246106140e05030030ba904051041c0c100c5140210512501149071f60340480107003c60b007200004480010b018089540e4410081c0c0c001049482d10081c0e03603115603d440c04803051504852481040c210b4000355046041040d184800e0320070768202c90706992541c600340b5402c01c0306890381e65124580307400c1218020002030100d00455a10002e000c1d6070380d076074070000d55074400c28420010021050011a0f8079007000d40140172881d200c0e06010032113582c0e19021030b0b075031249075202d000002c600162003000e508210a90a4000c5200300c0030b400c151030306109014240c04c2041710700d03024140018030355040c40b50300000c0d209000c040d10024482810010b03000e0006085030b00440c10154030b00512800c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 500642068 1250 500640818 500640841
    0x206060a03170a05091504090b0301090c18061a12010f060210020a110a0507090b120304051c06062928091a0d1d070b0a27030308 57
    0x100c0754810500707205102140c205011540000392410180030007440004403d640e02d00d07507004000c6e0f098138034546451810803060103403080281d40e1800380c2d14001e03100001c40d504648041c143c415480780b0445118041d6240340c000c2c407440e071141c1c1c200d412080781e20b9158a41440182100e14102c1c000c11450f9807200309400a05c00c3ca84244409603104e010310703103a1820aa00544050768840c00e002e4844003050141c142400354150f81100d940c2c0090b0014064001e09200e442540c01c0c080c1c402c07100030b00900d21079503078034411801842e208254a1100e41081e411023211082e000e40c0c0600d092120075a00c200f01408010121455241c44120300816100d0303d8844003503907041c581e040c6031214801c121341d08004100c0021701410302040314810707003c2a445404641403400214480c081d90f0790712084c008510481c0d600f035003910b003241c80c04029100301c1e40e0002041d0742910000b010080d0b969450200070307141b007440c600d001c05402c80194072981070a85100d91180450b400b80d15441c20303d9903411408038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 500643318 1250 500642068 500642089
    0x106050a081b0120010c0305100308040306150506040801050f0c66161517090c150903070b07060905031306020714060a1d040606030c020606 62
    0x407031540001c0b82403910151021060ba909201030404410441110301040702440110344a508141c2d103601404a1580e410b1203060751003181c1c18000402c00c1d0856681e111284190300c0040d20950b00e41158004d501c6061413940010715004054a07a256070f5006601e0107400115038401804400c00700092044214804a40040000e032004440d00740d900390600109501c410705900e44800c04050f0444002e104844003c0c9899011154020703210003040b904e0403410307070640141600c0d0015017145924122841e205d00542d06130200780704040c0140403048030840000080b605030b80018505205008101007084228884103661021145c0d0703c2d45111405441005411a01503208041c10843e80744021b0103060020321030030002c20801c904c1d4607190b19540086900c4041c10f0441c000c01c00216404001c074400508400c0703141022010040c0014980703008024026040c03100030034500008502d18007694011600040c002c1041c01d444141c01402000d03a021301e04094811000803030f40d507140c44507030076 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 500644568 1250 500643318 500643329
    0x3020708010c081e0a06172a010206041e08040342020702010c020402040603050f1b0a030b19080102031e060901030f031b0809010305010b030f01090b0f210106050a 72
    0x4113104d455250b18820b1508000c00070320358250303541c070045102002c944250011140381c40046c40088031174112581e0202c0011080c2920040b0204840c401c0d0b40c002c100c85620030340000f0401c00600401e01200790324111a40000c180c03030400600802048841e8500c5202034000b09280c1d102c0040c45041850f845013040b19070036aa5075511124130454400b40c00030a400d07803040c90980e60422580e40428140d0b0400e0304600040707502d840070800750000c01c600695000310042c11200320444030303450001041c410695041c0405407614000c480c80c1d21501c0d00c1c0c22501c2502c0e240e80c19000e981e49200c900079001603864410b640d09104405191561042c1d03034078080c20004082a88507465030f611806014080c40c4201c0a000c16061041c0c0c692078180c01488066000354002e079503458103500010111101608910f010000074401e001e64088850842415580c1481000403074000d9100090751110340c4242c000e43c001200c6003600e00740280b0020100703810850301c00910003184c4030010449209000d0050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 500645818 1250 500644568 500644591
    0x14010c031704050312070f210605040624020a03090504051803030a0f11070305030105130905030301060c05060f15091b040b07020f0f011d0a051507051005060d02120f060403020708010c08 82
    0x2d10043c81c41d000030b84a99040076000540c1a130307500082006e13a00346900c440c81c82c0d55483c4000004c110500a048003001490ec00b9204101030b40d5000360080c40329008030f0b80125540c0700014807a00503044140d206510300c1044a40b03a181144042029101e4000214501410304408810070300c40e18040c1d8081d65416140c4a08580c2000c0a00110400c02209601200d84030000400414010f00c0294042d00ca00d03543c01d09807148a04107d231800201802c1c00403640c81c42020803141125506144003400d90494503801300b615403401c101315a00d8450540c0311690000580010700a081e0001880828030945112514070407a030301704144041c0a000300d07408a4014030040c0c44140b1210a40410280000c24031071200d5202c00c04205001c03624010303500c4100340002d03c2800e01100300a0006071030352168080c0010318004002c40e001e100d0181001303000b0380704155840081c250500505072a681c0010841d102c1c1d24060a00a549500385e01c1844040c1d480c04154244032442204101d00c140003105a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 500647068 1250 500645818 500645837
    0x164509020325090e030403020604060933080414011a03160e1b1201030303060509104e0c06030e0307081b060711011514010c031704050312070f 63
    0x500300c02401c102c0e513a542c50382c0401c100c04801070762440b0240001d010980d031150790301824059511000340391031085085c1150201542d01c039404111400c40b86095907480c0004450302c461401c1b1044e460441d005c000c1039400c0a240d405900c00c043c0903484101da049044440035007001820102c0034030980501c0d4101c4a081e00007920b1503068860141800310380c06c9410b450000460300c00c405007102a00103d0010303450390380821070b03407422503c03181e04920541407040702c040c0f41c0f0b8041441c2408a100074086811001c1c2d01810841803004004032044c00e0140b11000c14401030154400c030182142c048401e0b0301ca180700400c1e00b500c6482084500d03480c5400070361800d4901d0712410056040750121007c08100c0c082055000710b820300900d406020320b0348072196410014000e072820b403501410400e045662800c0104141d0481c1c04c84803004400a08120320000010304040b601d60341d40010070403419409805101c1001320000040a5110b0500f12550030341d2110b003400c96079903463341f5080340043d21442 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 500648318 1250 500647068 500647079
    0x51206011103190905010905030c0a0e0705070b16110303070804030c060204230a090207020a090504020f180a0f090525050d0507030203164509020325 66
    0x8001c072500d1100401283e0600c2d02e00010800c038411000e19140016500d04820002940c00148290240c08100d0251904210703003030202d032243c016445000c540a081002007070515000340101c40c1d40b40c4c0c10204540d1546410141e1907100c0c003450b500c040010382481d4246000003000310549000e110590340d003000c42c1d103032520f0407508040b6100090365156400c01000030901c14511429409202c4080700410107014a0704100d00d1160035481451070394010015200144d40e500910380550390100400540d580b41ea0001c940c14113040424035400140545802c45490a800c104611500ca03408050000000204406013aa964818028803551001003440d510100040804403580d00440e0412191079803030000420118800509485941207035a060066007000d104a5501c1c02504c0c40c0c8072130385480c0c0030310440d1100e00008090702141031418201e481880b41000701000c9401032510130000e413122a000780003040b500760128440d1003820950a000100d014400000c42e00d201004504103103003d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 500649568 1250 500648318 500648327
    0x21306080c16030201140703060f05010c05011d1501050f1807110610031a01080c130f1e0b040614040c0c0503161b030819050706110c0d05120601 64
    0x5460075041c4071061050211150000c2d100203811802035002040d548603020400c00c5220300030303000c0410181000d0007401442070900c82c28040711000e180c070310202d0446061207801405d0301d0306511822500c00c01e0513070303d5810000c0c040c1e140c1603000c600755030903903610320411848030b15650180303800c444142005002824420b9010340e00a10340c1c1010040040014991030501c803003183e40042d0748060b5401402401440e09a420b920324403244402d00035418100726503520700320200c00e1441500758031030007005140c8a0300100d0708084618428415404541100d030400d50f411401422103e01d40072006e4000c0c070346409208200d0700d4014000d02ca42100300140805400141640802c1c000f41c00c10020018100300014405003404400000d1500014604105051050301c40401d101c1c1102a00341b002c1444201150074440c0464207048e00e810966205840307600500001902d083d141c10068100ca00c16000240508000c08080c0c0d086c5480b16901503503917004203040c50310350380141000901c255008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 500650818 1250 500649568 500649571
    0x1e06032a040e0106031e1b1b020d020d02030a05030a080403140a0c0303020309071235030a05100504020a030906060f03081210030b0a06050f0109230604050303040b0306031002130608 80
    0x11011b01386400c1c1e541e800350400307503444000501c04292a0304921b1920f160712800121054075403440140450fa17441d0001000042c3c04407010f48a042e1078441c02c81155030401c20700c28001da00c641030b42c0d00c036044458080d158250440c0c082d004101450700c003602030040d0408658000f84640c5488060b81807035107048009400007400a4a1f0740700302100030400c0e4550300300440226100d400c0007418030804051800d4a5440304280c5d0280704c100b07280d10451000c0400580e40d000c0040f100000d20b82d41c1e540110070010700c10307620158100c0e100052481d20182e00d03402400701d190081106004190750b41141460302400307444051301c03040051114000c500e007140415600429542003480c0c9064598407141ca03800c0e4140e81e12880140e45010400c0641084070410030b1101090130440605840e020000461808980c0c1003103401c0800300c030100ba1039a900301660040d0002604403901c40c0c0e22410400001ea00a40d17402c0d21034403502502900c0d607000783c021243c11818a0207000d1400d45484000d0b0784600c030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 500652068 1250 500650818 500650841
    0xa0b0a02101a04060807090b1005040311030c0405130c060e0f2416150c0c11030106030503031303020105160f05030c04030f060902040b0102011a1e06032a040e010603 73
    0x2542c0c0510030503641d4502444010304040300141680929118000c000c68918164032030007801c0e860811018117030803170150360449400250039000c0b58a12000241000305c49001240e1261810013031051081f644091003120314401e1081c031940a80310001942d800110741c01c0e181c0c0c000c1001e0004913003401c01101890300152b4441c01032010258120300d61800390060b00c090344101221b4480c0c24184900410070307407407110215004100054a41000420350300b8103040180c06201c941d2010440d40d282540038000540d00101500e403a420900850184e05060320019001076007000049a61401c0300a10101400b94544504240c0161300c0001c3c0c0d0300b504014131000702560309000000208252010500040d441802c00040482d090310400c0304440c648204241107a250020300d060508600340da00d440280201d4604244224107003036a014980b41c01003294001c0d601000703104011400007503100c0310398a1100700c001140c40780b454289450040380305003c90180c82c6001000414041c0e80003109682 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 500653318 1250 500652068 500652101
    0x10e030a080406030e1203090d03020705030c0706081e0105030309010f090e0406140a1401140a17070302040b12060a0c090902130e15090c0c010216110a0b0a0210 71
    0x40e0391681a026040380c0e00141c0480d031540d0703804038020f5060105410040004101c2d07419400c04a910942d54143d51b03a42106040c0c0c0016081d040c0503042080e038240f40c2d01c00048981c400d880720b40080445c0ca0681d020200c2102095412a03181940007130b071410780354090f00860a02809500441e0304002c0d00180c0414070140d154007080c011030400d00709201d24011907010500c040d4050703c07202600c100400000d59103140152503800f95890710030030760440d0280003e1a0007220b1880004000041c103500801c140c200343c032260b118400d00480c50f00c080300e000311810415a0808024407000105004c9800d5517500017400141c070078401c40d8009080c4e92032078544900c12a482c1c0081600300d80c40324045440503003011800b00420466650780355800703880045000000c0e408000424810079001d890b02c3e80c030300d9011a510581c1e103c01d6064841c02504021140092141400c003c040c1c100d8586246018625506010900c00c02c10003c8a016201c2540100180449880600700400b02c032200050300b01d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 500654568 1250 500653318 500653333
    0x1005120601110d050423030606010324030308040c0504050112080d150b03100801060b0d02030415110a170c0702013b030106090b060f030c0f0a03060617040b06010e03 73
    0x1d86080000c50741400b000d0b21119070f520305160001d105841b4182412076000f001c01c10b0400d10b92004035945401034800c0c20302042d011441084c0302c107aa0400d14200ca000c1c0704681000081c16030151040c0e005c0c034010301c4003060054940092105641c02400307200310741ea41c2007041c2400034105400400d918201390703c1c0001c151340f01051a202030551a40724080c2d2110100c02e200c840c0c10389443c18401450070000030484507142682c030341e809010355038590f02426808000a41489100010b880e903c90840b4802c00c0800d11112003500540c100803030b96400039a81c46540c0f08408098201d03180503140030750090f810222940e00448070886105000d40960301d011080404d01c20085090804206c0c0c1284042c140d050b600d42410b086802c50b03440000f10038200588584107840d04002c84220303010040e1700541d659608a07290460340b2502d6075505400100003941c4a400782d01d580300c0c106940d00c80c3d4540301901c94000ca1001c40c030390309450150403e05420046075666014030246c444410000e01540c010b0b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 500655818 1250 500654568 500654597
    0x90c071109040b04030318020a05040c2f100c081801090f050102041406190e120a030203190e130506040e0610080705010c05060c1c0f060906051005120601 68
    0x1800c02d44040316441a1007084c8820950540a088a85c0200c04a906034082c0181c0002d42e08448510032203024540e91044542810302c282c0c4040c004031402c0300d13020000d054507140b01407a80d03820140080c05009109540155089502484804081c40c0ea0b4900241c1c0300c040220895a840e0300300740303101d9960b640c002d80000d50402100e64590303000b500010784803840c20407107004182d00d602006108900c1001107210300c002c0000b1030701c1804200d00d40b041c52584ca24000c180f0080a803182c00c1ca0030321540ca2000c08042e4008020f007516000c06900f400b011085400035200007440720407199010302144080c2c1c00c0c0721480da00c55075001c0e000503c0031902c0003c042e8014100041961800c1d00100c55442c14024281f007007110b41e000b042c00707107085002c8030400e0b110350391a28406003046240440000c0c031422130890905010300c16003c490810030a24800e0f6403d02c000300042c0c4200d0705564200a000903e900e8081c04001c16a98140c4505207490300f40216400400d1008041c2d03810b0140c00c00f51042f4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 500657068 1250 500655818 500655829
    0x30e0d0c170c011503150c1d010306031e0c0b03010501170c0d0e15010605030c180a0b1803070807060c020609040e0d110c040902180702070801020315150405090c0711 73
    0xc0803071500c00c8100950171814510303104160300415000942c00c1800006550f039000e410710700695070004092544002002c0101c010303140c5030340701038010312944164242c8028160500e440c8584030301410f000495407400c541c1428002403007a03901083c4594517903d1079840b80010700ba440445060341e940340c0810850600304031103103034500300e010303921000b18584001104426a0701400c501d0510742e046150851034a0500d00c00c084007100042c07908540080c55407598011100a4114001e036548ca441d0140c0014a614052050181c424401c1040c00036503540c0204d5410169080ba03521080814030603001e00c1190350092006a801075990b00d0803442051041c80f24258040325599150340c19903070612a903141210f03580045201da032030460f40f0001a52880d84000b1943ca000501d10100d54615500380c0c05c2241d00d84c409001c55000008018070b04804680c208200030048800031740020030003148641501403805035940010034880800c46940c801400b51201920075400c079025265800d01240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 500658318 1250 500657068 500657081
    0xa11030a03020c0705030705060702060f040e07030b0108182107170301031a0c0703080403050c160f0902030903120c0d0c02150c12010e190e030a030e0d0c170c01 71
    0x1800268081000c0d203e202041c00001d0040030114010130015007400c2c0040c200b4851000d00911030310002550300e11000d0050306480c000c0803051081002840c050742c1c05400b4001c80c0780c2550003d1410000114a1010030070300d150041c2d02840201039440503106080d025000a685000d00301400b4055200041e1410306016250301140b51341c1900c9501d50b103400d09281c5940c0d10759225118404040281d25100c14080e101e500341c240c540060a82c0b01c40c00c00b1b42e503610512070315902601030074820b21184802c00e0f0320041120903941c0c441c9040d550f41c2c036454040340429591180d4940041007512020040c0f03024454124000307031030407032814a640c1c0911080303c2500c901c040c003580002d84d40c01e101e56486601c05a1140441c036525103840c01c04000c2100900c0b05004d000d510f43c48071004144074954081c0d414480d1910400100300e400104441d40744e898104d440518002424a4141501c0840108522081e100319442d141c16900007640da603002040322070380c1c1d0547c4201c2031001c0c0b00c45440074080c03030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 500659568 1250 500658318 500658337
    0x522020a0309020303040f0f0b07120503060612100f0b07020f100908060703050906100b03070f09120305031f030c063b0315090316080f071a0708060609060a1103 71
    0x907c0c0c8280b50a4450061a0781944071040d4107070f040c007651011a161b0743c08112440080e00d030050390303651140c000030114040c03150240302c101c04410400800b030a10340c1c1034030250b07241d1140100342c00741d444140780d129103d0808000d400007178104400c031041c00c2004004c1030031111410000b008070f0710742702d01e9840d02c2c108403601d03000a500c1d0803d2000441c405d00c10310341c00c510600c0d045100300303040031282c1c0d00d60700c8080d00d500100010003441c800194440c074a01c0c07000d0410103a02d10400340c0760342070080150700280e03074280103001500780381100201c00c00c1494048903401500b09802c40d15200c030996a003944402d0004990b4600c034503a00301a24a428050f8410700181845c0512071010418507252105550700400c0d00c450100034001e14090000c151002c0d820080340c81050303022280740c00d01c258020042e4152007200e02007280420403043c208902030144048410b0141e41c1e030380c940100c03814602503030410740000c0100074484450510720000c0880c00b0f007500702500c4d4880c00c154228950313802903402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 500660818 1250 500659568 500659589
    0xe0303070f0507172821060807030b0403050702040606031e140c0901090504060902120a0b180402010c02030d0206071805032e0212060a0522020a030902030304 70
    0x104200c0d50342040215000d80160300d0041d090110a5640031100540140c0a9607182000714107118480c1402e189407504102080c00310101d8400f01c1005010301e08403010801c03600c0444074841c48144030034443c0c01c04072031880005041203465501c8006501d40094030580c2003003000c0040b500581c5507400f800004008680c0c002407c4c82c000c107040c0b00d402840707a8841c40d1003414203110501d84220610b0380d40c0c100c000105407681d03410a042c01130303840c180140c0c081034100d81031030b0f00040c580181d42e020f40140041842411440d0740c802030408101e41042c06845d612600c0c84800b00854410402015841841030404405030342458000034035024110780260010381c071000070801002c1e80300c0e40c11135404c01030384080081182000c0000b174440c101404048020b00201c0e41d080550303840b80058401806002e0000c6503100c941c2c05001c2c0420100b01c1d05140100c1c07032500e0026040c20400c50340c080070030704c031003c2840c0c2c5540c03101250080e61103c5280000c1648440c1d840015a038240700400c0102030341c081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 500662068 1250 500660818 500660821
    0x40302071e03020a0509310c0b0909090a050a0b06150c0105010503120705071a1c06290307080a0605040204092c070303030e1e031c0c050d1505040e0303 67
    0x104180000c66412080c0116048024801c150f20824000c030803070100404080c3d5000040c4541d030500c013583c7c14015002c13a8040c080083d030040348030024409160b00766110602661940e81320b940d24511a2401040c5a1141740345802160315840c0164011000620322411314001e8060744985400442079084076954030001009189410458038103101c0e44c0c21003090414a0360348485444004620a840c0141c410380101210fa580c07036001c5a0851214241202503080c0d190310300350041c0854002c030300f118403d100d260841c0700703150604000720100c4558140e1442d640c01108450305034001d0800c05035079803130b03c0e030100b00c564941c006003014140440000030040d8440d00000c0384400016103000c03500e40c010184004009003c140c400c10b483d00350030041494401c00e10594501f001745424815900988100c0041c140c6020000b0102e80d07000c095030541c0e44030f0804c0148100c0b640040c100c00400c40401000741c152507140c100e5464082c0044000300341036030340d80100f81651a4070311800d081e03030030000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 500663318 1250 500662068 500662073
    0x2030c04090f0e100e07090f0f06030f03080106030515060c01060f080a03080c03040b0417190c05010e07080601090e0309100e1201020c0c06030a0e0a05100b010201051905040302071e03 81
    0x82c42c0b6035840c02c50814003404100c240a50f880d806c46010303410b520f9840d0300c0d502c42c0002c041e070003050041840410420a036540c87c184000301c030f83c040f42c04a0000c0e1110000003000c0b403207805010300402c588552121201400c804210076a404072200030f0a6548500d8006002c14034502d26800a01f040401342105174102d140c01054810000c03c0341e0001c05040c020700003c1a2903c0300c10b81c0c4aa400205000740d4042007010050314003481c0d82c1c01c1140074107004283c0445a01100c50031541c0d1041c002130110240b11503481e9102c0606000742002c66100c3d400401007100f05030041d51180e40701c0c005903031a0480b0b90b800f1405080141e00c011001c503101580e80724050030710741e070084080044c8000840c2040e02880c4859151b2401509a5110380008004607108555941c818180400d000d411911034008910b000c50305c6510030200c8844441c54090110700039401800741c14401d043e01d24504d16641e0900800750010701000d00207500b14481d01001048201c41e45501043c0540b44c4a0340030005031461 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 500664568 1250 500663318 500663323
    0xb1825050f0103020711150d090507050906010203090904080906070501060b030618010f0308030c0904090308040605060f0a05040c03020f1c06060e0609090402041b171503060a02030c04090f0e 84
    0xc51020b0304040c070400c071500200c0d0404840d4043c6030310032600c0505d05111180b422400b40100c40c8105141850301c4070b42c2041080010300c080440e4425990302c03038240d45090043e602c9006095006030400141d00c00036000034140c0c0014550a03100070025400c195190301c0b040c0c210781568115840c80741c2d000061000d103203050300c1002d5085844652554080d814100f0210540e2024403008089a60210200e550003902d2000c0d00d440c008060005c2101c0421410001d058600940d020b0705c08900c0d100224515080541d076598000030050404416a890841400014102c185031517042550a20500040040d11070007021807411a012038110010402c880c0d00c102ca15540c40b60b02400001026142c076070711001e0544190f180d048541c1081c940d5030b80041405088589800000d1000f00004a6040341d00308555071449040d0075403900b1950f44180d02100500854640903078160322000000f13524588940003143e00450000c0041d00b09555a4000415038907240b0042d100c1c50744840c2d103606005002c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 500665818 1250 500664568 500664589
    0xf110d0b010522080c1f121d01050a0608120702131407080717161214010b070b010b211e010306020a0324120309050d050f070e040b182505 61
    0x710b450b99030003142c00f200900d014004140c0c074000d21000c2d6051940c00c079408d900c0140244034401d01107040100703929041e8001c0100315109061940303400302c0410b1282000a42c40c0d813001c01d0700e0003540b9241140d001c01000d184110030b02409562104084440d12b100d405616019201c10380301c3c0a00d6060001000c0d11004520a00c2040d0b0700d40c95040050125a1500354044d00307500342008070310b0714408192000a0031200040122003100d031400041c100906100030409980101c800504a0740c031124007112070710130031356010802030b03c402d40c0d484240c0040d00159003240e42203550003084180b000c038003190400c0903401030715003d50100d81000e000c0e8050003502402d503024048030401d0b41802c20001c4c030780481d901a5022140f00300c000c940c00c060003800100e0185c9401444108205418988541d407a100c6007840c96a03805000b00006141c0141c00c036950046900841ca020f5a40e00e50a44d44500c2c640002c400d502c511400c81e4022242010506503a07012070420001c442031800c21080c410241c89 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 500667068 1250 500665818 500665843
    0x9063612010203071704080d0c200303010302090109050c19020a0c060816030f0e01150302010306050904080d230a06090b03070f15030b030d030b01030f110d0b01052208 74
    0x400c104520303540c0c4035281c40c6507042810a00d0301705d5100c6003440380850142c941011102c5141800d03494102c0d410502c0188440754614109041503004041035031071340000c1c44020b4126032240c006100300b03d1076402c0542c2c0000740304426400c2c10504400d00710110341100800300503030401100201030140081140d40a400d5504000c0900d007804a1020260001d403441402010381c1c980b404096066142c008901c680c40c0c0000a1000c90724249030700c0080d103111701c070481c082440c220000889040444030b481c0f055410021647c01e1006100b2180b0180c4201c031184003200c810403040c2e591480307545000d640144107003480062a103003800c05e10350449410310881440380d031108000700320b05950194250155841d400010079030b100b82d1142600a00f0003240c0071541030044114034680c2c00d505500425a4034001d0381c00b0300c000e0480014803003c80d80021000a4ac10b01c00704280c100401850300b01050403041890b007681340c0410b841c0f007141e440307100c68101004142c0b84141003105030780c01c21080c0a40c41e03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 500668318 1250 500667068 500667071
    0x10b1305010e0a270507050a030812091c0309080708040905040c080309221107030c0c0e06010e062a01140a0e0c010810030206070b070807090305030906361201 70
    0x200c150b0b00009556450b054003d0030000700c180304c40304000c81400039000510b8098800041a500c3e4505a4001d0701b00e441e01c050711102502c0013850791382001802c500f03914070204003240c045800e03640c210b015016005003a81c0e104010001e00c0d00181c02a40204000d0118034400600d60030a440d2280c0c060745540d0040c00701e58401e2002043c03a42c0e46255040380f01e5082c410070b1103103183e10307041074010340740303800304a82c4200000c12942f06050f003003248044424440c1c500ba41620740c403003144c911540015a0601e00150b9003d2b8081d4a50504030010f100e0075950161483e0441c940d10307845c0484440880010000365114104c07100c41c049110b260b0703500102800c1c42031040102d0086036566603040c80440c2c904010003000410360035000c480b4508007130764020748629511080c5080035030381110305481e8800011b85201c00910039901c21103607601501d900c07101651a101215007000a19005449181a0030f0007454000302003a842c8034100421940c04441c420b0420100c0b800c118000c0050032030a0540d9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 500669568 1250 500668318 500668331
    0xb1c0e0f0c060c07090504060b100201111c02091306061d0d0b0c040b031f171203190f0c031503050601090f14040b102304050702010b1305010e0a 64
    0xa801241580400c0415107a02c0e4640c401c04000900d492815441702c0311582c903003814002070141c40c0d00000c1c039010040d20016900700207072070201e08852800c2096141000c09105820604040d20b00130107103804034400150508411a00203140c0036021800360020f20742d128400c00001350803a440410440071449001d000d203e4190100701801030a0340000c005803041d00005001d880e000c002d0b01d019140440910362a8940b500c01c0c8902030900c0d090302d549054100e9400550a226102010380303040425000e00380b500300c0c06551060540001d802c0807641410030ba81d071000f101007842141c514908441e400706820035244400703003c540005183e61408a500441800401c800191150460b011800c0010386012280400c20041001020080d00c0550b55801d000500c001012040c0c05044074180160001d540d644041c403000c483c0c518521241c2d5140480144e81d441c0c6039100e50340c880043d00022656841401c00200c01c00c40d522082a211a900c40040c4007540080042c181d000695202c200400e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 500670818 1250 500669568 500669593
    0x809120406050306060702031c17010e1504050604231f0503510c0313020f030c0402041815030308041b051207061403010f050d0c0b1c0e 60
    0x2503200041c81345005007800110002152010000002110104100c030181403020070002802c26040c0701c040910600180c0010401d0100d00c943d540c000c4c0c440c049002c1e0048506000d000c040c1200403d0700354400d9855070041031030003800224400302240d0041c0c0170180d15101410008159041070483c1281e0b000744018007051f100012011240d4900c46150f00c00d40e0343c60803541341c40d124003c00380160b14003038040510010318410001c0c0c2c01c0107201021000701d40d0303174554441c6060104176220030026401070204c40145c2045403000b005c004014042d510180d40709400725040c0e030f20a0340700842d20310030507028290b00321541c402c01000b04c0800481004592554030f00070000c580143c0f0241c540c0c1c51a12403074003000b680961082c01088050024400c524503089200e40712740b000c0c401e01e4089880c082c0c0e00c3c00105004003c8034180c0d00e002d0b0000c5107580c2001d042c0420b80001840c1110b00751240e060101300380c0050805004c5010004800441c1c1e0704200c0f0240050711503000648113203501c10303400404c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 500672068 1250 500670818 500670827
    0x1200a03180803010b1308010f060305010b10090506090303040519050108070206040305040e060402091e01140f03040b0903160b041218050603070c0f0501150b1920010c0809120406 79
    0x441d0001a0317800e444640100d0000440b603101c3c0c3c44030340258030380f1a80041800c01600315034100d9000300002c200c01130004080c84106400184c0c0000000c80d0074030144010728010014001c0c1a00150071a42007d0315500880c040609640880345140000c601c01c0001c1d41c2d1007001c0f01c0d80081e03580f0103850203080956001e8514002c50045c21495070410000401540f610b40c10b8450040d001024105100d50303502c0c003464010b402e100701e5400112902807503120801032008035084144c030304801c1b03859959a500d0304203806070090401c02da03502003000807011011071609801985e501032118003c241c01c05240166018120150450034422030400c0425094400f02e10081111010fa03044c0355a130ba1103240840b29030101d41c8000f07081d10110100c000612005600c0382d82440181c244080031991a0788082880b0301600c4c003003050400c10481e40340013480c49419500c44079901c0c100341204941808655600399500d1160301000100300303004004104408020350480b446028249610b0181010f40051 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 500673318 1250 500672068 500672071
    0x9090f090c18050702122a1e07050d0f0204050c070b090f010b09090a11010e131a040e03030a0b0604030b15090a0b01091419080d0e101b020301200a03180803 69
    0x31a40c0380b1403080600d40343c035100ba41100d02c881c90b0235035a6400800c0b060301d1004000344540000da1180704004261801c0601400044030780009a100c410303840c983c2000082c04004012051310901841450001111480000e00440740c510150004405501c80d09003103d0b03010070814400c011280038400200f00210311010b0350350300203006c13280194032500141c0e0410001440b40750003521419030491403140c150f201440e8060400500c2e06c80d9400a02000155040700000d080c81d13401c104040b4128000590000d2050350717000e0642d03814140d503511240daa0320f1003140c1d042c0010350400640b20381c0c1d1034024145a07000012440c1040840154000203103100da82c1e001d0341c104401e22150300c510603910b51040c41d601004000f103260300503855610641d11000c0000c1030001050301c0303c00c40c004600d8400c0d9200103025107540c40100160000c01c05180c1200c00c00d0050b6013556a542e0b104128540c60203000c07110038140e0300403c0c1d651031960002003c8a060780b16044100d603901a00030b0020307a0742002c5a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 500674568 1250 500673318 500673337
    0x5011205070c1416080a051e07030503040b07110d110f2b12080f070c0305190f0e0d0f020f03070f080a14010c09090f090c1805070212 59
    0x5415a22079105442c160310b6140040e00b00d222544031010b5070540000c0c1c00e07803000c84003842c0020290b61540b0040ea076a400c020024406d8000744125807400b8090580031a01160540480712801c1d03072920340c0c07801d5502c15001030803c010001100e40a1002e819100454000b040d1640140100b580d2258001c085200380001d10403041181a040e0b0340d5100130a0100c4045240740c484819035032000c89180c49409481c08480c0e02d104240340034922809000043c0c03080d2030001001c0880d50703a191040360b503440321500c12001d221050103604800c0034200e58600d400e00e09034403019640c0c120301401a00910406903210321601e052189100000c0c500c520b840b501d1641658410502c0c45084001380c280061900328499605000c83d000400b29000501c058003076025085644c50114008052400c0e24820521800400e00d50a8108030880c0d0561007281c0001c0c120000180000151b03030391017040d0382079511646140680c12800c49140525100d00c0e50007500310700080c400b61614101404440c007910780d48 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 500675818 1250 500674568 500674571
    0x91e030b13030917010b120d0e060708040501030c141210210204020a110f03040519080606090606042129070e06040f0306050405070609050a050405090f06010803040e0c0301050112 79
    0x10800c281c0400d410500307546ea40240508030041c08544002e5960288210350000507004000046181c103010b4111a80c09811410300303460542000c00541c06018011018020000800ca0821540d040800645445201e8400e03044041c1401001011682800e801c040507c240c2910503000c1d800000381071004155064030056118842008251500a103a40f4000400d00501c44220002c030000b200030300941e0300841e0f000380c44401c5552001d199030342c0d0740100400d9030700070004a51985080f81e0203503801800201b4072071506899074040c52803901901c41c07098401c02020800020054000c225010500d00d50301258162030340e04078400030480000d0200c4061000c007209100307003521000c088030080e000621608411581e0707480c0c0760700200f034129425150703405072600c0440c5c0240b0500100b4203c0e43c0040c42110841c0c03c11081100030100913248a400340300b44080700e44c2027132003400018003c00c41c0b4000b450722180f52081c0200450001800b11100400410051000d81e8002c10303200c002c130322a00310 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 500677068 1250 500675818 500675849
    0x1051c03201603030212090d061a1905030c0405040507050d1403040b0a080603073507061e0203130b0702040f050c030136050601091e030b130309 64
    0x7034440c1d11070001c501c6200030b008541100e000402050580030403a40f00394200c813004200d10400010a02504400d03a600c851100310440c085078082d045059295a1120300344005101c0c3c0c000200c01c06050100c1803140616010100f1507480e050011a41407601500c0a00040c40c041c1e40d2242c55151901030b242c42100780305064414402d403110903054100f1104c2c1220740e01c0c3d4903030140e407000b83c00000040c000601b4480000f92281408144c04049a0301180711000301b880e241c8074500c004414a922603201d4040c0d420910882400700070900060041c1e4442c9094040011414400b68000c40c0750030341594420041030a044984002040844086010035a100d80d42840020040c0150080701c0c43c01c64206000c1c40440344090000f14101c0d494006841d1014095500c07200210508039810b602030510281e10301e51040040d00305d030368400d0301403400e4082c2640398550842071107502000d6881b0000010418020004040d5613550080f01402c201c8450007504c1d94014407a102034010841c15604450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 500678318 1250 500677068 500677097
    0x4502030303040b250302030105040b120a23010218030115030f08070f12030c090906030302150408090d03030207050d1409100509031e010c0e06030c030402060706050901021201051c03 80
    0x100583c01c200c0c413200704801200010080180d002801440d01c12131038103040b007801d4600442060600021003014141403041e03515541629000d9000751a80100040100c0c0c450310b0081c4000c02084000611900214001000b454210f91595003980f6801c0000042440403c200c060121034255000f0202d40c1d81e1034007898007180717100d030074600206140f011f041d05841141d052380103845801328031341d102013850703603514180004d4135410302c4050f0140c0c00c07100c41d481113904c0003a041e6a02c140203008041c81c1143c540c021804000c2082c0069000030390101b01c0030304014040c0700b00f000b080000d00c1c113402c241a510014090b28443c0c4098140328045203140c50400c50b00600c05d80364013002c028141d030031850380d02c003220700c01242c41c1482c00015440d0180c0030011a01442c11095200b101a044a007107644004a4031095400500140ea022030140051000981d4a0080d01d00c07640c640800581c0302c0342103041c0c0003081001030308814464000704c1d04840d81d241640351211035054152802d03000100121 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 500679568 1250 500678318 500678341
    0x6020d0b0402040312111c11030702120703060b03030f0d0e010b10050d1b090b0703020c0a030602041502060103030203030a0207060b0a06020312160914044502030303040b 75
    0x5902064101d070001c41d0000500035128000100844141c0b00c00300d0341152828074980701c868450500d11961511503501034440d200e0b03a104a42d502c108011249400076036000646084443d440c41c0d8820303489000309004001c032601400f030740f264040e00214240540c3c0d10b440c1000c1c0c00340ca074500342e899075a55481c0108540c25000006040d801426140c0040c03a980401411948010300d002045030900c04070f0402401c0a4040829420b1140d490483d0381c1d04200480401b9400884280d0440c8240301c02e213400c0fa42d4aa6040340118071442e00180e9652600c840b03510300c00e0b842d054801c155003084004001280d00441180da00c224022401696040c03a0701d0030300b000f00080b2020a0b0882c0c800b01c008944660000010039441c1d04200e0750b000d50b5a10100204d40300300c1c59400080018081c2c020070070036440e070f110010310904d034010404141d00d000d016000b904d0380c403144420290803050070b030b180901003070503a007c900030144100e00340ca02800d59000f00b945c3c0e103c051700080062481c50001030614842 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 500680818 1250 500679568 500679581
    0x82a090a02090127061b0215090105130602101a0904110a08030d0506090f011521051608010b16080f04050310050f0c27010504050d060603050601050f0a0306020d 71
    0x7003c542480c0d2140d606004544415140240008204506a68846d040070084100b80c640c4d03004011140c58803010400e10303c90b401c000c00c0d190500900b40410390181c12100c030903c0107400c0325030081604180b51081c600c25903942c0340f4007081e00c40040c20f1060362078503221903655000c2c0d00b04840000c0b4030003031030225403465111390002100e800702040c05094402e50b41c1010340600d00844914042d03844400f000c0c1d800040038898081d07468400e181f080f59150150307620072650200c4100c000c0e5048214003444003030f0340d412030724004400d551003115100701c1e42050016015212503141d407400c00000e5003150340c0100c09040050034101011071070041050421007103802626000c0c007900d5805116007840805841c0c280c445803201c0e10403c000501c00030811095585000c1d0300300340e0700c840740d076a051110b003c01d266001103410403000300004901070304c6040c9568000c6214520008045180d410902c1c01c001c0c06800c090f1040d840c080400c0115501c0209903002c2c2da07088030300141d541542900d0040103080 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 500682068 1250 500680818 500680847
    0x70e0613092301050102330c0c1005070e12030c0a0804080d030c0e0127170c03030901020a0b0a14010f150c0507150903020a082a090a020901 62
    0x410a0116181c03110381c01802c1d0650705101c007005400041c011800d42c0800c01d019150059101c035245c210780514241c45a503901070410283c2c1021103003c14415041d03e0304646041241100042c0d050030300c4c10800c1802154003108a041026040010000f00a040b02e810200c0c425041c03880c0641d0104014412038103101081c000301d07035100c0d0883c540000c1070f8200d441a041e5500074442842c090320300034002d00e080c295955444800310300003040103540341d880d1048200300000407140d190210f440c04100d8403010f40703042c8150a202c5004c140d0010700d4030b03008c40c004038020b420510082d5040c1e40c0015031140c84942c891040d03007a9649810400c4020f0010b0140d8028418485000107000240301a0b06005e58042003000c0f800c0405510080d0b900b0301c227903200108a507202c02e81c01c0205845c0d80c1d200300903c000c14500481c1055580c3c000a52800c3c094102c0880d5400a10b110400c0c0004100028405440c444030700d60300d240c440c1e0010f9000c48008002c1600c80741c00050b018016881120781c09d20b03210 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 500683318 1250 500682068 500682097
    0xf0102030a05090d02070602030a081801050903130602070f0504021e0a0e0a08010218060904020d090c05010e0102061009180f0b04021302090f15070c1215090b070e06 73
    0x26200000c1070151030252241100c5005000e1001c0300f42d840072030728900782d9100e60000c51034010084c03421140842e00402170510380442c0083c3e80c40d0603000780501d50160400c98011a124800c1c0c80302000b1300101907100300c0540d88804002c115038070401030540c003180e000316401a00c03410407000e104007015486004650b141d1000541d15481d940000c26500c200c00305551910640e500d400882d8200e01c00c42014006034001f51582421610381742c00289964800a000542041d40d100c20038030650b074a900d81140c190403110020710295074407909159803c01d091000b070255041c1442c03481103101e80c0b80600c1204d0354540300f024046600b8008062002c81d4413200907042c91a0900385090750490503a022403203001c6040212400c281030380260346001c003000b070840308801c045d0401c000c1102c4501c0e1007550504000e104240202c4c803803c1c00c40303005042500c80940c03032880c03600d080d42407110000c03021a40180341102d0200030465015110f036001069007040389003600c1e104001000d03030180688100000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 500684568 1250 500683318 500683321
    0x140109050c0712090306140601021903021002040e0a0506041b0e0d0b1303170903041415191403150f031e100f110a050313020d0f03020d2a02030f010203 67
    0xf9911210040440380141d20801003507540c541010010001643d10b1801039000c290344074111210400b00c0c110076486801118035480542203001d05a0b08103500c05502c000100d02080710080c40e0740111640704c202202e0401803030b041d640c1802c0719101600c0903242000b050300038400307450310741140e051006a08401200c5080c0303080d03c4250721040e00410100c000030078454640b00c03020003451442d80142242400366045c903040820300201d041d040c4008944c8060442c100f9210b8510040c01861208244031a69280c0001e003500a4030302510050009071200c010010400d584100205120300440200c41400c880c00c0f1401c0021710340041000c4840306041c070420800d1201200046650000d88410b03010300c110004c03041140100c800000b00c010a000c1d0401200310803030321510003554001d14824800703001c10303c00d40104010500750b603001c0b11007242d10104001410780400c03410319030440c00c1c40c00400c8428150700c41204500f000001c15003104003544440110340c1d060010f111440e09030301c0215201e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 500685818 1250 500684568 500684603
    0x207060e1f301a03070f05100201061a0909011e03120521011a160b0709030c150914031b03010902060309161e181805011e140109050c07 60
    0xb41028903a80e003a0f08143d01d00208542008207040080724044801c0406462804013406550600319100d40219540d50f100821201541407039212076448100447c0d407034004c0401841354880e410303008011200380c2000091000f40c004c4e044101965403004000082c405144070580f29400703841c200701014800b010140641000d241c001700d04a81c03044191400d1000c00c20101d5907075110300c0c031500c1014085020300c0c5010880707000e2010303000080d51401084050341c0f501c0b4941544215000460b80e180c6840c00b01d800310b03500030301c80c4024245804c680717a0840604000a50f858900051400100c100c2115443c1c40d40e500794041580260054900e596900e030410700d144d11207000505c1b607050300c122010046034000e1010101110348290f0003142c2c0d0b800d41401c5443e2400c0074401000820903490f01882c440f004044000c9141d0184294000303e10080e412501c0c804405110221000e19890221020310f101880d502090441e0301c40c03580020304d034623901e9803140c41d4070444101919000030b01c20000e04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 500687068 1250 500685818 500685821
    0x230a0302090a081f1802061215091806010e0105030c040f0204050a0801020d0e0d080f0408070f080a080c09100c0c4a010311010215070207060e1f30 65
    0x400c403000c400c20841016406900c1000c00c00d505c0c030194100105020705d50300f01c080b030482103411490702401c1100d00d03034041c0c00017400c0791001c54401840004400a00e034801008000103409040744110300c070034942c1044040b80c0d80d19402161340d4800d42d01d80140107a50358841c0d0441d0040d00d40a441c0d00d8006440358541030107135014819001c03d641c030708000b545298401240f85800c18109564614847d00d80c419428030b00f440181064880110400c149030000b45160388105420f03118001c125280c0007503443c09020814028030301840c83e0f0040006150300c1c0e036441550418145181030060185509041c00c020110302c80e084902001a6141016019015141c58411459114000381c5c1c1c1001c5d0b00d000009806400c4600e40942d4411400520000c0c085072048401c104040c811140120607610108e500707284203036107650158000e804203103c5c0b540e00140302045d11b130301070301e20325520082e40840c3c040401d40700340e410302082078148810324540031003154a10317079010300c01c2000d2980041c00440320 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 500688318 1250 500687068 500687113
    0x904060f06140a0504050403141b06070c11010207030203282019030203030405010509190f140301050f010515041502010203010609080f120901090e011203230a0302090a08 75
    0x521441c0e802d10f00140c03916082c01071512460f4540c0c0ca4002440b0000c100b1800c07604852912486502c141c20049502e00b810402e01b0311a80155981003007024141c104039440e050768140860440d00000c00031f001503100000c0280000c0000c4000700403035101468854a00c45c00d01c04e000b80074242056071403062000340302c9130320502d4008072240170030ba06c1c036a641d10040001038400250180c202384010401517001e5400307010b50310406000711100036149101d140029103a90000365503016282410b20020900f521400c205800590081085041482d540b45000c5c02c14495144130720045100400e42c070701010151802080032101008482d00300a0019010f50024020500010310086000503034030800a240d5a44a2100028101a8000c03141c5200b5036480300d48001c0c18004403c0d000210002120f1a041c000e141010741d41c60380750790304d02d4010304194071192000c440408654403681801050411500b03004403505006030341d840110042900c0303242a502040c1d55000b1440c0c1c0103122a149003425 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 500689568 1250 500688318 500688359
    0x503070c05070801090b0f1e0a091505090607030c0207050f010203040b03040302030a0e1522080304030f12030b03070e04020d080f0d0f110f0d0906060305030a020606010804110904060f06 82
    0x25580e0320f02c2046412108540c4a4001e1030210900c505101d21002310680010850201094400090311110f542e8624004841d02140d601d000308a1400030034404213401550500d010301401c00550f4009685040e10302032a80b1507420304a0604e0383e82c0c0204120341c0141180a061a200e10b498180a5225009100c181004c1103078507001c00d07100e01d044482c00c42c0310014008035500700701c45a07511540b203052280601400300301d0030401054144003040a00001c2d4851a070030180c0700c440c0e02d04410303c11200301d0b00c0c81c141818590440120f50300070426101303039601070384500481da50303034000122425003400020345003000000d140204011200c005220303821640106100e1850303001c2c488011100c0c4880e640c411200144003c400000e580c1c80100980c14891a000c940c1030181d4481c8412508660b00c221001c3d8400103444500396018481d4030341c400400d0802c040d1604d0640c071014080382c81c08540500c00d0032000009810040c650380a260101c43c1c0c440c04024054403032150503001610035041c13 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 500690818 1250 500689568 500689583
    0x3070b040f050615090106080a060302060c16050607020315190207111207060504051203121f0803040815061201060e07110106053a0b04020f040504120503070c0507080109 75
    0x1c4d4220b41c41d5900c2010740d4602801084680c0e00e00340f01100d039500040d0012102c944c0b01c1c0000070240c0e0320a400303441170029081c0a820705407030034240d0300803a4a8035030007280640001d000b0354015a8020800300003513418511460210342e60000a12070740c51b21000401d030320320b10101d9140c3c148400c0300c8240294040c01d860078500c3d0550403402c00d0392502203100d8040051002c210038001c40c20045e25003451154801c1c101ca00349440e80345240040001140d40c0c1c08200056858004d012034000200c00040002c0d00c0594a414141600a51035a280092000c40c9041c02000705501e030310b40010b0380400d8151a0001c001107500c0b124036400d075000036100500011a02108142940b10600c601021100011b1000d885042070f1102904620404c604c4d003134248126420307401910011507000d5122521a91f0865414913062040148070a106940c150080c4c6c030340701c100800280ea40d5078040700401c60f0706103541c0300e542d03040d4202c0741006c4c0c0c074000a14034041d030030001072040415044500b90794800c060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 500692068 1250 500690818 500690821
    0x70e15040f02270d0f08130b0c06280c0f030b010518100507150204031703150f040b0301020d09060b0d05030406030e1515040c050f04030b0903070b040f0506 69
    0x30201c182d019140305a01c2050300f00f00040f14000c0e640c5a5440c0042010740001d8501c000d946818903004507030390056030001d10009900360039240038914107025101b048403160510060221295890034000c041101500c404244441607800300c4030741e094000e0390000f013805602c58003980208a030603901c080b000424200803080d4120f40c0104180c03003910885042d800803031078007001041540040740c01e06c041440302c00c01038100400c00b041c020070000400e28101683d1286580f40680d01e0350007100300e004004106100b4408030441c00c0701d030411030076002c4908440030301c00c0380c1c00a030050480300400355140d0f20019000d00c40103126001410014081c0b103082082d405a0000e00c14a2032002200a1440d001000b09118050281e4030140071a01c44100b110200b0a04080c0a40d61034010b0ba1140ba0400b94466448020319260050a000b240b6a150441c10001c81102002140c06035000041c404070611001030714022302042038480c035940100c0003450908050402c00c81d408d120600036103d6008010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 500693318 1250 500692068 500692091
    0xc0a02151611181006020c0307030b010e060f06031014040c050a05210f040510060b0a030b01141602150403020d0605070318140d0801080703080705070e1504 69
    0x10940700c1c40016625281a01d41295850581d110100c554603036010403449071504401288005140c0302c1c100401d05202c1107404c001020b8a00078149034680e2280d4441d590902c001418214064119401041c5684007600c4c0d600001f00d0034400050400c0e0040780110800c0410002013044608403a05280c4050103980e9034014402030300e1070941c5d03200100e6020004041c280340304030001c0640c5c08010001220f4114806050310a0079805d950745504110a0340a00c0140082030216813101010b00358200501480c0c002c18221138080c070b1600e503003810f98920801000e0307400b0f00030156034048040b500b55910b040e07e070801c03100860540000e82c02140f022003240780b1000d0580444068030340042c0000c03040011a95002c000d40310040440d400c054981caa03e0750f40010000c51040064894002102108243c1d9070040c544502c0b43c0d8040e04020300c41d0010000c118000c981c0406036608500300f40d503648a07900b05035141141c958040b00c9070306000340800c1007880055211080c9036100f00c074107202d850443c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 500694568 1250 500693318 500693359
    0x6060f0c02030c21010c05070605090d0906050f0c1507030e06040b2202040507030e0d031a040207060209130b0108010b181201230103020a050d03120b03030f0c0a02 72
    0x1040c000d4240c1c0c051648241c1c50315210009100820b503145112940d00c225141d59400d580300700e01c040b004100049681c00801c0003074000c01d0361000c1040010060343c0785c0d035600140054004d20801062140c0010640c110b114a03030100c400c450b10581c116450702046988103850901d048038004006031400001120510010420500440c1c1005109002d80c07907031784070a000104400003850510480025003030058071103000c0d40b48202c2c2e4079200080c02c0344022001508044500c401003040614054441070301d1151040f0007103ca00c006d850040c1c0302d05552070078000038070a4901043c0e00030b415181c20b41d0101c206030014042079400380e982040304d9981d0f4100014600621030100d0f0601c412044410300350078a0a1000301c031a8169001040d5000e400903515003c2451035955606400d0b07140c010300540c02c110078114014003081d282c0109101c05602e004107501c032640101c0d017990313488804440c159a401c0054651b1240001901656011030761a1700340d845062410803030040428000164200460 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 500695818 1250 500694568 500694587
    0x506160509061b070b2a1504060f0b03010b060409050a06030b011509081b12070504060b07020f060405090606130f0b0a0807030b0f1203040b030a06181104030605090c120106060f 78
    0x1b01012001c0454090660030007186007070b0907249691180ba50564904c00320814082d0090340a88000903104403440e0446003610104e036a070600a0b03040c24040030365610380000302d500701d441d5002c0c0082c1d10f803912000e842c00380a0f294006080700102000120714040300d0854114542800d4a5040e040780d590304646403942d802410301a03a03280c0c900800b00d4a401c10100940100300c0390415246029105c1000400701c40c0076070071503005808042100c10071818244c061014103581100d115050601d4840080c0c1102c600030003c82c01140d002ca081c80d5001c440380943c002421030f41d40010003960b1141402c1c00706400ca01c1d03030f200c00615008042a40d032802482511200080a4100080c00520600b0700c4140184c0b1110b03101d42d4803040000085641d0b0b2640550b01414030654081015444d150b10080295141c015500b15a890444030007503081103d0b0485007180c0e030003140842d41d43d55218145003003088006032513421070010040c5068081d81940030030103891403521220309144810bc03080740c04040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 500697068 1250 500695818 500695837
    0x6020f061303050a020307170406030c1107030807020a030b090c130902030735161a0702040b040f020a0207240c0b0c07020307120510090506160509061b070b 69
    0x8080201c100440d01c9400144070511213070048074030f401301556504112050121640c40030b10000b06045c071605074140079000c5514542d103070034819244111001c617161b1411780301c0100005030025403501151200c024400081d07400580005082c0b5060052945924038801080d01c5000d04c4880380f23079101d9040c843c041400c1e402600a01429080c00c00307919503031440a0b000761011003030f4412107030480085a4018900c606060142071107415942000b03030f0200c103039002140b07400f10122503900040407040a9404042d01101c0101d211014180410010000700c100d8101c0d040c000503140d10f04c3d40d0009442c3c4201c403001100c0c40e803891104240d0960310700070009600001640d0074505804a80342190007a003020302181610300d00200c690001c0d00d0310109900040000400c07149200c14040305010088074401d28000521101c02c0584d541c9440e0301d001408440401110300030425030b41c0c40346c401d4400c400c40141c13105654070b0302624800b52101c00d140340c1c4007448c810b0030400701d4180d80c800e065855921 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 500698318 1250 500697068 500697091
    0x17010303050a03050a0e0d112103191b0c0203071401021e07050d03020714100507141510080705060f0702120c0301020a120513030801060c030e030a050706020f06 71
    0x40b00088010303001c0035003401e20940c0c441010014480b024011488891002d8607590203c02d8200013030350a20380801c3c5541000d50280307903121195141141145d91001040c0a0400420030300e40c0038030010700c0041d201c035020600501500f075039030313800000d0940114002c400729400c443c0d0302cbe50303904803100100c504035005070402e09401c103104405003104114000000c094805082e1540c012405c466200f60085e401640403500c100b0801c1210307004104404015900040c51006d101f4000d0040d01c0750041c01044036548a422000400040c01140b40150b0300d51110340ca82e00302015002404075460003802c8080c020003c0c005041d29145085820394424115054108041502040000b4030b459003800810b001d03110002503144d40c20f01c010080901e590301e03001d83c40003004512a0854100070042104070301420141c0012135000100607046070300600c0c001c0342c445800c2c41c00300d400510070041a070305846059605020000086005015503029500315448014071603012962000d003600e8801c00d48 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 500699568 1250 500698318 500698327
    0x10b04141207120204060e0403020319030c0c020907210c0318201807021e031e031003080403050f06100b0304020f0411030907030201091d1501031103010f03031701030305 75
    0x4020300081c3c42155400100b00194840d0740d487e40081d030060442c0c003200160000589220b44035000010030f101d0b9965850104841464284c0c09072080d00c950740c01911800800d00012202032003200b088281200e82143c048880301d016641c4400b0f003c90501010100e070401c280d421240c8643c041d06030981740c10a840488074901c0d004440a650541820141c0110050511500b410a686078050003601e05034028040394844104444182c0c0a01c255441c0c076410400102c46500704121820046021400d2259500c1d2505000000c2001c526400186007940c04a40042404404038095904001440a48459a8510b00c00705216034140c00360f8000204180049005410012900c40781300b000544000b940f22500a0856402d400c100d460842907032003080d0620440d41d101c100351000380700f14103a801d600141d4102c500c0085000800e851075800485a21540c1a8440e402079162070440001c2c035503403541c46205481c03080110f400141d01180700013400400c800c2c0851180390417260180d541c681003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 500700818 1250 500699568 500699579
    0x4020409090b060a0819060b010212070c08060a1109040b01020f1501080c010309081e2106040e030a021926120c120106081b04090e1506010e100215010b04141207 71
    0xa0074423910503411807084804180414010b50028078803030b4001e00c04100310034540070000d450010003d0101715540e00707004040030524400350545040354012640801c862400307a0040303180200c19003854a0a10503a0032049540c1e481082c03850580d0444c00585036822105030040d0103403004c0d2580200740e1002080030f401002a00094104000440202c0a10700030a141010aa440544440602448488041c001503241a210b03007480740070054040d6052805188029488015031001c01005410300c9200c4000c11030940301c8404a040041e494440c2c400c8455500c1c640e9401051841c40e00610303603c0818100c09000041e50710003510040e0b018501da08040b011611454050310300d00e90546c90107880400d80d5511805080078140e4103400003034501e041481a0b1900603094910041503d504041c40b01b0f40e41e0100305881401c2c010340d11051802a040000c80c646181001c2031340c103109074440080780d600c00c9000100201c80d205184000d02400510400c030303480486c1e03041d520322a40600b008200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 500702068 1250 500700818 500700821
    0x1090b0901060c06150f090c03060308160804030611032205030f09040b04090516060504080304171e07140303030708070f0e09010902030103060e0f0c0f04020409090b060a081906 78
    0xc1c0c444c882c0d0408103403420426040c0482464a40050750001a072880074403054403207102e4900c5031071716480c0130b0000b507255803203865071032040e00d13101000d41803003100b2482032001c5401280c006541c80203080000205000b944d175510303001580c040822040422184141d0121030408203c8540c210004e586000c40c0c0e000a0f40196100d04031030390b001519000070f0603480e9640d00c2248100ba002e4000b03007040e29400b50701c03400c1041603900070300f00780182804244480c0b0b00020a45054131a5400d404400003050b042507843c011007000d41400100d60003402c030b040030102144540888031007122442c4054102c904040d26400100d070001c0010310a8000100b00e00d1107006a00510b1f001420b00c2003048000d040441c7d4052001d0708028401c540000c0100100301c068800d56140b019917801500d08110b0814000d0b8070703034203070b194518800d0151111604280d51a41d044030b005000c000c100300035501c0c2c00c0c584108400301c1200c0d0140308404000c0e0000302410042450302444030301c02c032600c01c0d22030079a45510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 500703318 1250 500702068 500702087
    0x908160e0f1b031e100f0929190803090102071211010c020112020703030209030f0c01210b09010311013e0f010e0703060608010902090f1e01140901090b090106 70
    0x12482038804403030310380b01c40210400c0e8007640c02110104451030038146151035181040e4045029940b9210072010196a0a9800d0620241109801e0307239000c500030010740c40d0821005800031445405a0009501400000402b240d400c00e0b000e962049035101c4001310080b200c48009001e0f10740384a010700007903200b540034048440c03050608030042c0c0e212440c1c0c00200d030008a401c5002ca580002c641007146003c004950310000c03144020401c40803880c2c0000c110110319001020843d407941d2840200c035078550410840504007400141a0351396a06240b07640c1c0e0041d0b50a40d002c40c41c3c80d00d610410400c044e005200c2c401c44003106110034140c900240724841040d40900c11036000ea110603880001d000c1c0104404247c00400422140c0c0c103508100e001c6030311940c890222685006a03400050300c444102c0c680c01510070106161039950414003900d0440105040c000c540c0019001081c02801c040c911b0105030419601c0300310036070f201c0005c50121200e90f6030041d4003401c00f400400115104203840c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 500704568 1250 500703318 500703331
    0x20f010f0207030308040c2d0909350f040303030e03090d0b0901020f0a1706040614010c02040e0703030801060206010b0c070b090f0a0303021e0a080301090e1905150702031c020a0908160e0f1b03 85
    0x1c00352150b44911011038cd00300844041d90517400090410038142c1c10b00440c000c0703e0b0b8280c080c0d484e027801c0d50001184101e0b00e0300010502c20302ca00c00240841c034290306803011050040f11140d42c4035840c80d0020940d00c003003034050a0f01c40841000c103400e4203052003590151100310741c00d20080c60b02c580040d03881d0075134080220307401600d5000c1104405010711006d40194403948a055095040c29006414007030143c00520074580c1c00e02c00c042c180c0000140e050116070300b00c03130030694840c0c110005c00d4510088000b107981041240e000001003603400070700d10441000c15500d12205443d6480141d44842c40c800d005414400140b006102000c0e00f0351214a003601980100c8200381612402c808040000c0003054400350030409580c18000d00380c020b0103520581034030281d45005000c81c084c0150300304003191581e41a501048140134640a4000d600280410380111190789201000324017040300e05000b0156154003000200f01e0340d0700da01e42010b0103500480072042040b030044c900d822594100a085 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 500705818 1250 500704568 500704643
    0xf20180604090203040b0f0f04020d15020a021b0d020d120903020907020604030806010806180601050d02270901050105180409020901060309020f010f0207030308040c2d0909 76
    0x4244469455400400c01050030200250b124502401c114081080080c10812200e15070420081890910009035a110340d04641c20a0001d50504100300d40e07810084861003d140f0000b4032191403600007507551240b843c049107000380d011aa00502010980490f0001e4028041c02112000165600410b40900b9180d1410000c400d03620780000d075140005481100160300043c003408149a80110601d0303010100f0708001010b0f08080b004a080c101c21141c5041c0300d90744100108040ea88910110361402444800c2551191001011514016216040150100382c2c05509045908092031000e0403140140c517402d092129101c40b0710001c0c642c000c3c0140d48696164940001a500c9000da1406002c040c1d50004000701d26105206c0c03038000c0703211301906103e0416041c0304113690010300e1506072a0301d450304803501d40b0b4525000c04031881540024024040c9032410f101680064048e542030350b401c0049039401c959943c1c030380404484113420003400030003110401c1484800000c40050540701c0c0100c6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 500707068 1250 500705818 500705857
    0x3120a021e211801230105090c03010b07030e030129090403020c0d060b09041a0a062318010803091003061202041a131508060108030307030903170c0d0f20 68
    0x9844c00c460384585003440713070242c007034664891400b801c10031800343c40b094903c001c2c01d0404c044070f0020b50005101c1d80c640c0200000308081010700c508440c11420001a0007844550411a0f92241c0c00c4031034400e0304550f61020244248900e02000b0244c0550b806802030940610700300c0a0020b450100c40059501548401a0030b41c02d40314042c3c0d8074400c0b07010b1a541300102080052104400e00b0180400c90381c00c0c1410b4040c4002175014282c10400c0400c2090300b10322030340031804288043c0114142600d00c44a00d03000260ba60f10110041607a040d044400300050740018900754101c0b07405025003100c00074140340302030060034140c1c82080c451280c90200015900241d0000b1002c18000b07442005181d210308050002d5440104080050002c8001500b0b07250b041c198000c2e500d00000b00300404250b01d8902040038980254102c0f80c03071010403117607809945051014218198490944a02c0703840c50035144c000c111140748103594200a0b0039908021210032121114030980140d984021104000c1c0d2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 500708318 1250 500707068 500707111
    0x16030504030f11010f03020702030705060d0f050a0b01020d05120103170c011a030c04090b0402040911060403032d021507050d06120516030c0306020c03120a021e21 72
    0x11410b058038441c5541c00003004480300010441d0b03958440007420b060040c807107000140e03000705004050b00c0d01924142d403510f6450382e850300501010b544004125241c83c041c8040791103203401841e1004020380885082c89000c6100702c07050300c21210540d270340700c100d4401440060898024844181c500700030b070318104140250f01074211a85030500d2848440c6504d055411030400b4050350018401c00c03507040181c0101c0d51201c0031003080080c4000d10803682c50b4803103420018110090513800c500600102d80b960303168640505140841c0c0ca400e507000c0102a070921104088130861420002c0340c0c2c0c081d019044414203040003000d40074200c2c000b48101404101559601d5115140c01440115000b04500201c1d0400a0034142c12101d480800740518100380041141c20b818201207a03800400166200f844411903800c6015400c000c00d07500c042d020900011948039005400c10261007080a00644d10b40d4201e07400600c1801c040d003005081d886403030340c170b00c563b01403d041e0b1026901c0d00c0d00e1000382804 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 500709568 1250 500708318 500708333
    0x5070b070e0306060901080c01080901020f0415120606120f0e010c02030d050115020705130f020d0509161a0703140c070e01060e0109030602032205060105030c010e061603050403 78
    0x121003280000c0c0030010009402e2400708a002d030804415210000d080d4101a000741e282d40441c1d5007035040c0f00c070401c040341a40409504440c4a0000500d00d141c6403900d9100c400c105141044030300001a550714440c1c0b000541c05d00c1003034211030041d00e4205184c803545100c14082c15000102640300c9942d80a407488111007806000202180c41d40a5503641d0070b44400d60b812a4010303001822a640c840c6c0e004e854441e0002145010303900212080c00401180c0e03100b0350040e0a4001000000d82c0c00030405e80c50100c1c0a80040c0c3c0100c3ea40da050321194546d0851a0b0040c8007144903d800c40c00040d1421050032070342c00002c2c00c400d4085d15051140000e0415515015800848080202e074003840342007050491512005015044510300442000c080c04c1c00281078066602010702001c0d400004030301202503217464a01001880a07400702d000344070f81401e94075040309118050190081a18400042d881014a400c0307114006260b0b03800c0445c0300e000c10004095442d02202440002c01001c008a08407 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 500710818 1250 500709568 500709571
    0xe060904050405061b072607080d1506030e0706210216110a0e06011416120807050f16020f03030309030702180f34120c05190c0305070b 60
    0xa20040400e81013065082c40d040c145c036035081c529410103110700750000d020000c0080c0d00d014401c01c0183c8004000c03010300070303511034003130010b011245c0060010003c06460300031400004145046102c22503071600d090301039441d02c07450360016402402d024804240501c5108115501c041448004640500850012a031044101c0040400c11070001c01c00c0001c50220040342140a03158003082c18076000e040111004042d11b05414422151041000b8040002c02c1c3c0305c0a19284c004d05d00a0081410110101d2180300100c0e8000380c1141e00064160340240c049443c40794061705614909007020a07070035a10fa6025504030b03401030190b4071400d11980d081001d14002e1a80c1c0015540d03c0030b40e0f104120482d0307451050460003024002c1002401c54100c42c9030341d0301501040000311030200c12410b014035060101d42c03900b40b5054210042c0d40180d4840c0c21030910128102d07080040030f081c7ea0007034900d0b000c0e9107010b885150805840c3d0110920500107900c00f10711900700b2700d040420319078603c100c0980 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 500712068 1250 500710818 500710823
    0x6040608040c080a020102120906070209011415130303120605090c12010e160c060908030109020403052503081309110d05060d08031b0903060a1b031406010e0609040504 74
    0x300405200034002401c030010000c000b00c00040001c05425400030351192070407040da2405510109401500342c4a403012140f025600510056282d80c403503a0b090202c2100e003684078064140c1441a1000c081d4a10494040c1802c41401410051075a9070407684403203041005840c8a444402c0090307140c44002d01c0c54055109110b20903211a0005400300341100168070400403198001c05108411428a80c0701e480e0000c01d01d400800c4c0800c0f030a010000c0d103030440340100040c10003c0001600d62450b4094019a0320034010751b00c0001481d14040d81544502c490700b0808028403c042000428040080c981c2000e40341100619540d5441c0110484004625a07021071100080710449180d85100d003544c0808112640710100c015629201190300000300051008002000030403402503000c01506d0041c0341c014110340d000e19044421001521a44031942107000881015284c01d600034013501c02010011541c68405640d003000456000010850a6800c040e08000d680c0c0301d40c84900415208e9030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 500713318 1250 500712068 500712077
    0x1060f051c0516060f090501120509012c0f061e040c0b0708071713092c030d06060f0f030b010302070807051507031112041707050106060e01090e1303020c060406 71
    0x1813030014050184940814040104450404144102d030381056914580000d0f010b0005050b5681041c903600400c04201c00161520503000201c04840325841d444160f001c0345003d540010381c2d02e034590b540c1d3340000c1d11038400c03611070101a0300d5050144040207a0045c0034980c1c0c11102d0395116200c00c62507000f20000c0d0b9681200203550400e00c594980001c3d480002c0e444444c1c604005c90380c2d1510700742000d0140c101601d888541d00880c48403441c103501444051014008074445c0380c9900580d6036401260b0000846003440c1d4006460340c020510fa5505008030784070010203410803042100102104420541455030a0011101042014015245a61044008240810001c40425041200280598101410a603804948109940c143caa072185490403405031034540c0d241c00900744258001035060a5004180801480015045541210304540350b001072000c070070b8011941c0410f18050141c05c2d072640400715000c00903002e4842442800f82c41590291311200b80001c035640d105a20901c0007130f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 500714568 1250 500713318 500713363
    0x30f02030a0f0c060f08090d030e01150f03121112030907030c06050a0207170d120f02120a05070e0105030f07020a060e031c0204060e210d03020304120201060f051c05 73
    0x982108103140b2440090416007147d2509040d55995001c00045042c1019254451b0030381c020720940110f408585031781d20000c04161140c5101c030740358a00c1c0c0b000f40c80306480d60340c80e010383c540100e80c1000c60411460141c901200101c48074062540064841030140c45010b400102142000d1420400340c4100c1c0c0c1c0f62603450280120007850000f4075003045440c501194840490303882c00141301d207007031002c500f00340a02c0c51012030108020400622001c00c00313400001c061490b001030807061446a0b01c2d20000300613903210200708594052024228034041002000440c81d00000051041c1d800482881200c15001c10340d601c0350180d42500c9096130180d031004c116903404480401c135025100c907921608508051904200802c4181c2c0311000c1400740180078000f00e507003403080b08000f0116034260308403800e41d622168010001d5000316402d8030b11100214ad0480407910601500b400c461220b41c15400135400c0408100350900300301800c1c030345001a80c41e1310001581c10311201c215524160604100c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 500715818 1250 500714568 500714579
    0xa0204110c0616021011090307060c02010f0c110f12010c050d0c051c020306030f1605010e1801060e1306140108060a0e01060e0a030219140604030b01030f02030a0f0c 73
    0x81102c00b80c000714403414000c1d07074901460f43c0018155615558450049031010041c84440308500c038282c1e0198040c041c074840810240c0e0840600481140701b0380e01c060070289444021078210340100c000412460050000d02514985411110354900b002400007404031900352a66003110981c0c9400f802081d0040b43c01c1c140d001d0745203d04140800f050030114500751900c0e48000500c00c074000711000701e5178044041069904c007000200d240035062001c840d240d0b07116240b01c400c80c40052144600080c14007040c5a002d04160b1100c1d51003052400d050f660076403c054060740c54194881c1950f030030140c1a405c2850030300c0980540c1c00209415201e00c204840100001041e00200a068902a4a16407010030485072003035483ca0450303000c2e02d40071100b0421040028005020b6030303c083c0d8000d018051401d01d0380d8034008620b04803640001c442c10955000c00503c000b50003103200c05059804004010804221a00e5800172039030303c0101520f03000748160344e417010309441102c420348002600c0c240a009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 500717068 1250 500715818 500715823
    0x6040b0a110906070b13020607060501080705011d0d15091a010902070308070f050d05010e060a15090b0702150c1b09040209070e0a03060513050111040e01030f050a0204110c 76
    0x6007250302600c491400e040100800e81c40e1040b07100040c582c10740c80c4009290762941c3d5001d00300d0710354014011641d43d400c0d0b00304000508002c1c01b5120b40350042d00340c001299030184900480d14020041d160405074454810410810300d207250540e40800f4003c4500300454841c800c589580d0f12a03114404a80b00d14400d0051880050304422820340c4100002c030b001c41d40045545503c1a55494140101400410110360364058010031184903402d205c000300f080c02280040600c5541e081c1c0e00314004580d00c41c1d801070050556055500442c0c1d4402042c04526814002001094009412645843c1c1c2000131204182d100411181d031582003101800c8507030249030141c070940d0301e08481d902d501e0304043d000120000d0024001c00240028400b0b08030003030b200c40c45940300070342d0842000c009602c0d0010340072a020082c5c0c90100c4040d4a048040c00340030192200342c8013542c10000c0b41084607030840c0d858000c11201000152346500ca000c08000040e51503000c0c0f0a11007071240341d065203995020352140d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 500718318 1250 500717068 500717081
    0xa062a0c061e0218031b06030c040e04110102011406100e030304030c0f080607030b0306060906011205251107150210020d02040e0606090f010e12070e011d010e060118050306040b0a 79
    0x3842500240b020b21b04040060100340815074046030095901e846014280995100d1503000d00d4508002c00200000e101d5040c52400b1440c8080e0004d0000c001c00c2011284000811190070b80d01410800140c11010301c281100310040d04050f045902e02034580d16a040700c0e400c10381c4011079014504000380010942804502d4100b20340342800e1010005280000e070711030764020021409200920300080c001d80c80307501400c40d1a02c2280c0304214600b00222192001910800c0b030044407400309030198006441000000420303e070a00c05445d4985c2401c0300e41140d4920010000d00314030070114004072105052001b0300d03080f03030310101c0103030760380d10f000191008440028000c0380714000c240000c0346562240944981c81000900c4c00c050303d281003200281e040020b05d010f04a407841506004035984180403d000d050f03030400741a020700e6540009408281880900030543c0d212002d10105d84554000d0038000c0c101022852195482ca0721040400c0c07070081c04490564203800301e078040c031201e60f055220f00d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 500719424 1106 500718318 500718367
    0x121309050412090602030c06010e0c130e0a0606030b06030f071b11033705072d0e1005060304110904050a062a0c061e02 53
    0xa1800640100c000040f41c051200480e03d11700000c1529809030140d002000c0ca6803c0100c1804925405040d40c07404020900202e0000a9201e2200f4042c101c07840c240c249a00d40740c0406004c1e0b44242e44a0340c24140340001900c00d603140c8000704d0354003050b205480189501c4044c401c1350100c1000f1200740d0182c010240703040401c55032454081440c0c0084044601c69246181d8511041c01d80746110300f16540300004010001d1400e6030407800003070050090311050380d62804801e21011102d403400d6280d40d60250714244902d0203209000161850a000c402203113880c02c00544194040d000e058498100480054100f00206041d0007078117801410700440380c102071400d1596089015400c4409d2401c15920548400328522510002220f0304851440340601480c141c4280030034981c25940079803140401c0307000f040240c0b450460000c0c080030050b652203644000500c25100070514 = true := by decide +kernel

theorem cover : BRFrame.Cov 500539568 500719424 := by
  have h0 := BRFrame.cov_init 500539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 500539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 500539568 ≤ n) (h2 : n < 500719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
