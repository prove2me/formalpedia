-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0238
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:40:31.424333+00:00
-- url     : https://prove2.me/submissions/29e07a6f-65ce-41fc-b734-c4d61da0ce3b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 42625903 ≤ n < 42805759 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 42627153 1250 42625903 42625991
    0xb150901081801090813050105030403080606160b0c04030201110304050d0b19020a0518090114040903020307060f0912031401230d050c0111070b03161101050c030f070201 75
    0x12a200c1c66000b0003484607600b45d240c03040d541c2d0700c505d00b0320581e03402c8048040340c15413103a07040c0c0303200300e81c9a154a01c10b916850100003560300101d03a00d064084c0d84d402d4500010703940c0c2d000c00b030050302200d89050301e0318210f200141500b0340407142c006896100f400100450740d85ca010301810701d45c203e10402c0c059125041100e44598100307207102860350000409940e41039002000b442c0311906c00410050036240082002001e64003071045803014009420030a08614240c0d00c02c1010501c01e0044034504078495940034282d4980c0d40c900080e2075540c132003505c03d00c081c80050300401c4580c1d1504001c58501c090740807280aa0602070140d00307100b1890031880d403881902c03406503146802041000040524a40203070345d10083c1e0003840c00581c0105035903075850350000d115420f82c1e020840590130756450380d415924a450120500701040003410001200203801c0c86654010380032242c1b42ca42c0c0b464800043e40c41048003802a9086a141c98a001c800910b4600d6040b07a20b004403040c0000b49811801c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 42628403 1250 42627153 42627181
    0xf0608220201111c0906020f0706050d02040509130302060601050a0c0b0c07020301020c0d09120f08090a12050a170309060708100807090e0708030705060c030a0f021803010b15090108 80
    0x2c50306610078880d6010b0500c4244c0c01c141401c03401903903010001525008100d8443d10110300848055201d60024080680614050300c0c01c40d902c078030010f09180c0c1e60310010321070810940c1c1d01105090030801060506505000e8035500400a00302035152481d90140105044e14800018000000213404034054074074000495014940080c001d548405061000390f450b45200b04110740031032003015000407004030f541d0581849a40142e210b110800c1d043e01c079030505900040307529074403012040011440e00d503048100748180d4040d8000344954410351800c030a0400300300c20b980d5155030041c0100180070303000107501075110040349808051134941841810074a02c96401c281914018076001083c00790b5998410040c4541b448200c82d02d80f9510804a40c40340709207072025104e50000c1000400320310311940150f41049401381e00042d483d2540300c3c024200d070031982001740308009101c04c41440786000d0050350b028903801c8842c9214100711104601c44c1c0d209420301c003414422024000b44807500142c2c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 42629653 1250 42628403 42628427
    0xe0c0906040911090a0509060a09020309030403051501031101080c030c0a0c02030105184c02040b07140c1309020a03020d030504030219060f03022508040f0608220201 73
    0x31041c4550384215160040c0f0750021140d40d80a01c03640c0b00006071919041c1d111602454003e020442d2090803c0a240003961000f0030980da144070406c4000001441080031090302450804c0707040c0035506500d44646401d2241108904000c0450240903445210108490300540b0a03140c0c3c60f981e14440c02d054517401c0307040001030f50652071304c0e040007200c100c07008103c104041d6090030344110b40300d82d00c0c080580200031216280c0180150b003110810190400500f4042c0c4044480d40c20607000658112060340c0c0550010684d0b04008a106070400080c921011403602d170030700c050300c0840c0b501408500b40d052088a00c980d65502c4100a0043d5247d5088010286402415171001000c450070090440d6110348406c074094100788050590740700e803c1d101c850a507513403507440001d004040c200c120003035009005240450540c080700201d00d100340c861802202d80c418822207848a1074811490b10415030340e0310803800e2141c0a03040200607810401d501502c0000c00c181542480300c20300040701c000a07154 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 42630903 1250 42629653 42629669
    0x1b0302070218040b090705030f071a0c0d030605010801060e0306160c020909060105010806030313061425060e19020607080720040b0411030a09081c06080f070e0c090604 74
    0xb0040c801400210001300340306a40c000200c99040796104289907448034a161350119a030030410080c8010050b8150701c07603c214a07100703414288481002c00724100b400301c0007040c0c08283d68400400c0b1070750b0490200350040c059414082c03900d04126012a4035010001c0c041c0a0b078050801c43d541000313016500130110341c1c0d00900042068075003640c0681d40d0b98400c0c01001c1c04100c010b00040d10764980041110f030305401001030744854074501841070f54040749a910142441c3c43c01c0c4890115030302d0030100351140700007203404511000c0c2c05040000c1100e0308146079041a41102c100c41461103808032000082507410b640c0e031070755542c01d07040c4150ba078021040028080504041c01c002660b404104a03000e00da41150304010f142d110004000840712825160340c103070f40d03040c03000854101c4140e206d1720305e80d4010fa0425142c00408c2e40c1e81d42e045c070100b030000025265204002c0c003510300100310000c14040104010449141015041600682d006011610030140010034285548075101600c004000007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 42632153 1250 42630903 42630949
    0x6050a0f030c110a080306040b040204031a04030507080c0c090f01080d21060f0603050a09030804030305041a0c0408070e0906010b18030105040f060e1f090302010b03100509070602011b03020702 85
    0x1071030001780039441074560b10310403410207400094a06e400d100315400c032171340050340b00c1d40302d007400384001000c040081c415401e2100900c50040880c1c4014001c000703a501101c054040c000303142042080d0300310003411450146c035680005002e00e03580004e410842a849041840e040344480c030f2100307010403114090110b0035042500005820b0454200b103002c0d65000d4405000540e5044492021100d400001400280d05500490041782c02584055001030040150040386191410400c0c1303442c5040d02c215421003000203041105a01c10700c044405401a000c01e0041c5040400c407403aa212810b001d905031016000440044020000081d0414003502400038440d525050031b060407502000d60043d240342d401c1085160180030701182042d94000c4d070b508100443c117410450130008265141c001c405541d038030407181b2042d07075082200c01c00c10342a42101192034078200301c0850808130a5801001907a0400c601194091140ca008400c01411071800684404842c00054816441c8040200045640d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 42633403 1250 42632153 42632173
    0xf0c15070c141c020607060507180608180703020f01050903150a06030c060e31020c10060f0806010308033c010609030f060b010e030d020609010606050a0f030c11 71
    0x1a85050102c0c2050444500c420300c8490b894010014002c98002580030104001c848005000e42d40640d4003c0340510f4803800700c4a621112040c0305038160415408a80d40390b0070000d80d03201a100c0814065150009000039500d15404a400070301d0709000b203410f2000100e0800c1207500c04004021200c0034080c3c940400d420820141401042d072400702b40d9006012803408900c03070f4041c18144040d01c401611020503501e031490240c00150024508102d107088c040c0e010f15080b009030000e04801e1044002070300845146542c160106c94080d8070a26105603620410881c50201003080c60460760490401c3d43d03a03513240001900f1140300d9000050300c1002c101c84000701d8144100c150400101140301c008410b0b45c0760101660003101500c4001c11039107001e050a000035030290001092800181060101c24601c20006070805841351451302c0180d0003182001410b800074000d5200600311420170b11301d4010101d070003e0040a4001d50a010315468101803003045201c1c081d241c03008905070081d00e1209103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 42634653 1250 42633403 42633419
    0xa0b0612040f03080f04080d05040203010b0a030b0118050412050a090e070203030405010507020c030703030309020301021213050c09060d0303021e0a020a0b01090c0906081e010b0702120f0c15070c 86
    0x902000f81e0003e480100060b1010007020340c224001d98200d0039490a000c01c00c1003400240070001c0c000c0b6050b54035101c00c0c043c40e0300c61103103e5001d18030803420083d440d8145400340001075241d0342d503462110700700301c00e0001003440c40709444841c618615180d640c48040c403c0544481c41d0380e82c072a8140807580b6041015060380800518081c034800c50003448207441c0c0580c00c031783e04c1c0495400e142c0d260b08031141c1000001d000398028a50148041e00241c00c0c882a20b1a0700021541221221031103652045001c0801000b80214451590102c37010707800340c2849004075025190008004042c19800603104c86140d01c168404179000801070103803681c54030081c8000b0344a200c00042118500c8400c0000b1524880138001c10001c280f0765951404c1c80c81c0f03880c204489060010f0101c91142c4401d00701170110020410229010b0121010310701c0e130b111502e00c1840307102507581075807400030303000001c8001552401149040b0708410031954040101801604082a03120304600103150808a107070002e0014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 42635903 1250 42634653 42634673
    0x906120603010f0504110d0c0801050c0a020d080906040204020708130306020d0f0b0303070615090f1b020a020f040e010b09090d08072115080307050a0b07170a0b061204 74
    0x2401e8000748400440d030400c0030152841994014030781045201d56040c28184464140b540360b01995080000c41e96815019007101c0c010baa0040d90041d0008401080f1601002180c4102445281c00c0115141c06620f0302d807600c10260000740310300d4001803240d007400320314426180c814056854080c140780e520b2a103180250b1000e2445080e00f41004415100004035104120005501501440ca400050383d503900081860140788141c06110800c0890004803074450601e07180446100022264050781038bc00404d01d04d05170070b13400c40d03100039003902c01038030780d12800728220301b0559011440480030a282409040e018202c81c1c2c000d0010010070042c5480081e15031030b00840358841840c10b803900c3c5021544441820081d50400c54203d030000301014465101b00080140e021501120341e40b034942103070030340d80a101c2c1520140e01c0f402105060228903280d494015096041011071010300f04580400c00c0d400038005249260b0b107080c0c00030161510740032121a03032040b08a00e2850324007482c0412181c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 42637153 1250 42635903 42635911
    0x6010b030601090905160e100203040b0706020415180f05010c11011101240f030302030f0304050a08031315020c0709020304050a080408030a1403060109030f0201020f070b090f0414010b03040305090612 88
    0x1045120510024201000846c48d607450381e0b4059484c060800814041c01d922a40f42242c41c1503080000107113074200441011401c020a5031070041c41541c6058484410350b0316002610b94042d204420405a0782040d0042e140580c407a0300c1c0c840141c201d0f801629a00c20b05103884125500b0181c900b95180d0510008100c4540a030380c107103413600c0c0c560480c50f4030038056000c010301503407003084503440e40360161020b0b5a00900c510100d0b14845d00030b0360ba00325079030001d48403456605441d00c0c1e40003c00c0307940c80c020180c0c280074000840c103103848036050a654641c076120700c030300040d030000208007805402d20260b848a0303000b210580d9100e80e00c1d000940c0e42d91140c0b0341078000500e4160710b525180880d5003100c1c0103510586d81c02e068035065803100c0c01c000440c074100320f065120b4001950040301003444401d00a00042c0c2d0130390307200c000400521140c264003c0386c0c0b80c0300343d14000039610038020064a035415030390400101ea450303941d50318096031244604403080c0e50200b03001c40c1004a00384030300a89846 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 42638403 1250 42637153 42637157
    0x20112050c0405011701050a18060803040306050405060f091f020f040609061e170903090907050d060b120c09011107030506150d021302090105130906030b1806010b03060109090516 79
    0x1c01e0030b0089031000c5417028001e182c0d101c0e44245041003001d000306020304246181581c00522190343d1079801c0d00d994030552045880b81d480b1010441409428840954422442440d1409900c0c01034080c54070380d10301805074020500c03c0100e08a020700c00d941581c1d0380141481a050380c0baa101d040103015841107114050004803820150703c048002804c018090300d40c56119401900598065002d0140d80202540054801440300030f0031a91641b01036801001d50341c075159612507000c080281640c4041e041840c0890080120005403000d102c00150f00c1012003410320380700c5101c0c6004036800b0103852000c0340c1a100700403000c0184a80414500d02445105040d040048411820301c0081e01171144c01a5002a840e80d1640c4c0b8000280c00400120b101450704a192040b080c49800700f40d10f483e009aa01035942d11021310800803000042c0e03800454880461800006007145d0310390320301050040c1d10440d440031000c034520341d0145400c02c0203030004640030b11961920407240c1d5007940c400440900 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 42639653 1250 42638403 42638417
    0x1050f06100219020d020f06031801060f0506030a0c09050a080d02072309100512010b04180b04030309110405011d0a0b0102070603090f0f0507030302060702190b04020112050c040501 80
    0x44050000406000e8448440805056030f4456002c104142001020a0740c00055400c86480c041d9564002940b14406840042c42011450380c0950300f15100c40d049080c00c0d00031030105000540e161425254410714111000c14031443d02c60f0308540b0f145480e0702c4140c20030001384011404131004260b03d0282c1005500701e4103466a100785056080e550f00a90303511001d420a654000e5041ca0407149500035030044503644d8207a65400072900d4950220785000050355140d003100c1c140d142c5402405507403600048038510b11040d98a40004c60103000c0d00c004c05065139511460204488240f156001d4030008204100540e903805910f41c014154075441c9040110050000b14524090b10507041a0079045c0e00901d401c030305083c8254003c008002003690002c02c80300f400000100f00780030884101d0300c9240074010903491460f01038604a40074200505640180030411f6152075203000c0e4507100e40d007101c0c0c0544151140d00050318900d040c502d02002d4641010108880c1c2e18079a00203200b00c40d000c0e61109 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 42640903 1250 42639653 42639679
    0x3041a0307030f150506070c080607020307050610060806121005041202010b180c0c0f0a060b0a09140403080a090b0f06031005090d030504020114070309060809010203090d0f030e01050f06 82
    0x6000c032a03030f00309040c900b1207034902d062241d414450007a22047c0c0c400d400c05640c182c1c88030049841e0503000c558040040e0b10020b0190104a814402c2e0b5800003007111010700e8090800302c0240c040c030401404903001d10070f00600c00c4002c0f801001515030403000030404100d181020309118440a8815071001c02540c02c1140110312802c28021520300e1a40020802010b500c8150140c00641d00140c0d5410481c400c2545003815210280241c02590f0721400000494000c00424445d04c00c0140e07014507000761600441a9180320310905403075100d40e040c031380000d9690303412044900606890720050300128001d4104903445c10404081401243c049003100c8039403020354510015148102e407036905a070084640000ca01d40260011900144141088001522800c00300c002c0f640100805800241701c120080164603040440c00ba002012080250b1071482c02c4203056944901541c0c8080800c86a1400b15070414442d03444000c0021204000b07010f81d0a0810050305100d01c00d9600c1441515456221 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 42642153 1250 42640903 42640931
    0x61f0b22170d2f01020a0201062c04020604030b0406090201020616020304140a1203050d0c03020a020c010e0f1201050105040c2c0103110d09030314010b040306090503041a030703 78
    0x202589071030403004100981c10307408202e8242443c41c680042c0000303940351014030380c5040615035503103540e40d400040e103540304000c000342940c04a501c44c210440d0b0940b580404400c2c0e425450150350307201003401c9615180d0f0320100f41507105a52014100581c0b09041c0010014507400820805000f60300302c03280c80c5c5070541c170135000994503400e400160f481000100000c03880403004000b4443e00030f00f8155025510029a9401c44108000310002a80052000340e644240e220b0160012110306d411401c0603004500655503240302400c1605109901c101d0014035607812000e804110005050107082c1901109602d019003402e0044521460a00d085100201c0c41032414007603031201658813011050f02c20b03a04c810042a000301c0e043c10552281d850f24003021952008108020300c1c039400149052450900404840d0088419079130180050010030519131060151420b89406c240c0000303000c440e61a10600d548120303804954040d416510401c0b002600e14040c512580541c5c805101d820540440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 42643403 1250 42642153 42642179
    0xd0f02030709030f050a0501050c0a110309011715100f02070504020702061b0a05070f080d0903030e120705150403031704080403060c03020724140108061f0b22 70
    0x284070009000040400201d00c02040142c0d1060017031068072003414141d2500303400d40d4811103001103a00b400151016040e83d01003003203040a0b084034040c6080c4a4a2800241000f00e4a450b503001d280141001c04c45210b03412100816a41c4018440000360310900c4020300046901c2c0e08000150007080b00004041c1098001c40d2001c030b07070080c20140360800008110b000845d000164003868410381c0f410b040028001c0014001030118540c085030818070f80009545040d00144884003080314124041000942054899600003003c640c030700c503400c2009121921701042540119404500080d603860039104020081003030340e000b90350341006070148006e8804010001c0e07030001d001303000030001000400c10580c0540ca034140b1034a00035143c000151180500c101d000300400e4004c081401110045540311312407080c503075500703182225035585404140b0391588001429001500c0030b00950f100080d0b402c00910001d04000e10200d40c50756036111401c1c00c00c4000090803410b2107091070000ca000002110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 42644653 1250 42643403 42643411
    0xe010b09040c06030504030207030f08030a050603030705060a0b1c1406060607030905041107080d14070306081b15030108070f050a0e041b050d080903010c0c080304120509090901020d0f0203 83
    0xe403202c01403420720110300600d00200140c0441c05164000f02c005000403800c0c46005015100c1c80348c0381c2c140040c505d0122140503144a2190740204208000500c010507101c0d03002d050403400003413056240001c038582d000c044c8094501240d00f50780c100704020007000291074441040b82112200c0d641d40040c07004520681c480a008a40c0b41602003010b880c2a400c81018201c90100440c00d18501d035445882607003003007034482e0b15545c070348900104800c049500303264002c2203840c05100541c80c02034810344417117550f0800550021703299a00f144030344888503000070350680c14514a40ea982c0d00d189079510703960f10b2300510104109040d00080c0c2450f242c1c01c06800d856052811851545442e074414500a203401d90040c1c9001e40d1910001c0c15554180910100500480c5510f944901c28000c26007143c1c281a100c2c030a110106c1d0064004c076031200f0583c1d40c0150b1044404400c5c0715a4541601c0a00680040c20390215642c020025001010340103070840303002040050080074003404403c0c040c1e0104031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 42645903 1250 42644653 42644663
    0x1060801050102210403021302090306220b090a0803070207030c05040204150f1404121106031303080a02090d12030c08070e04020a030b0901090203010503070803030610050c0c130e010b0904 83
    0x11003001c40340e564810550180302844c03007070314041d0f0380e134040750254043d03031050014140d003c1954050750a052020796484404000b8400250b000030140c40040c0c0100007000d040200c1020024074040402c05c040040700e86c1203424a0b840e03160002e4020f544000c0e501080710000c0e050100002d05041a0094405651914814416031445400102c0791034580ca910314003007004c1e82c00b40e032000044950061015041c800c4984000f01840e0800702c103296035004030203003c0e080c00c0007000707211010600707140f00c1e0aa05140240d46503c5000000e8064003501450650102d0104011001c10505800c80348642d10300751800c0c00070360f5102c1c005a440c8002200c0d808081528495010308614041e4010040803205080c009a000104070105000c004242c204c4040c0b1a800401032015103030401902d8001c0c14514002c2d8614038102021406405035400d8940602c20041091054004180030743c80c0884009402a81d03010140341c81c3e000501501b050740c04555107401106059400c0c08101c2910440d08a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 42647153 1250 42645903 42645913
    0x6150e03060f0c130303120c020a0c0302010c14071203080f04020a14041d07030c080604080406030906092406060306290c06010f0302013e0f010e01060e01060801050102 74
    0x80340c02c0c40829000030b0181e01e9045040060394400b11803500c144003d140280d540307001c08450010f1a40403100080e20042c10b40d400103040c3c40c00503410880410641c2d80c2880c0c9204010128500f541318030500055a00c07160051141c00b0403404442d0b1380810105009685e600c1940d03c0d04c0b200c00240140075100650401c00d04202840340d03000c0c0145945950402800001d6000d9001011418444e003d1010a00503001202c2c104240008520400d002d08030b600050003090034540e0300c124040c07040c1d200c3c0c0d609140d1217480b640c0c1480366a0313100c1d400c401d405c01016011103d482c13448109040c8403070285102c00340340c0350020451611a10401c0180d4060030406004c109c200400300c1800c0642044400c2807503801c0042c3c242400d401e1000c540241410185c0b0084a230640c80054242c03031035040c400207100c03c8184400803005241402048400003810305000840800d602c1a051002150642202d9804e1400d80d04854174158071620407104c41031490101c50740c0311842210030039000e00c1450b0060f405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 42648403 1250 42647153 42647161
    0x20306040210050d020d050f060307060f08060d080a1808031c020f0702030109030908060c0f2d0f130503030c0303040828050304030f030b01091202010309020a080106150e0306 77
    0x5800d2151000b88542845820b08440b078003001c06a91001d1441c0c5016a1120180014442c4402c02113421442c00ca01804019081030710040034511400d49080030403016401181517900c4a4030a1810683c0100b46242d03079084019010340256118030795030042035035a00002541a40210960306144100300044000c1c4035904009406908000d640282c1d41030100140380c0141d90034402c00065611036100c0c50001c500d844840d5042c070a00404039042040c04014022180400004454444507103024010b200101ea440c400030039000b03000c01001c511400a2060510713440d0501819416402e01c4c000b0042940341c0701455100e0103040c1c4500e40c01e90040c00480e002407240d05c040c00141040c00482001c109420291444510440b02c2035030201d003000041c0020f169104080c03075030000c001d040a202d41d1298000007080d80c046841000104250003100030304580c40398114411242d0000e0148891076152442c0754000c040c144144244409007203121420507010344007801c4003c10013000b500da00e5071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 42649653 1250 42648403 42648409
    0x10e0312190302130e09060906060a03170705010507020705040e03070210030e0f100903090501021c0f020102040f0f0906080615060d090218060103050106050c071502120c0c010e09040203060402 85
    0x2a4007a5800d00707164007404401880404903070590300034044000b41c141e2500706800494140007000d400c2d0035150300003030208811616110415001c5a9200701005041103122618801074007174007000074055420841800650745c5c0c0001c02c0015100c0c102c50030480461042c40e00c03581ca105041707000390845030410701c1d0700b450b45c0607074028400140c04c0e20a848240d005019982e044c401d070011f800f07080550303031521801410341c0154484040c0c0000e00081c02c0c0724044290203078010a058111004101036070289042c103038402e40503240106400c2c01103662580c0c8501e10511607d406000d0303003208034580580040c07015000141c1b207024203511015a03900c0c1640e00203201c03055011152072060540c03215520030060b10780090b00d000c2d2614000c140903c80c2444000102a11011fa0100c0100681400320200d102d0010480d502100d1201c0c015401c6c1d641c9401c000e03414500b0786180c4908614011600c1c0c442c441000c1007012182100340d803640418040c001c100001e481040d54040d415510803400680141 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 42650903 1250 42649653 42649687
    0x801090c090203040302010b0607030315050406030803040f02040e0a03050d050705030c0a0c110603041a06010201020f090d06060506120103050d02160501050307020109060e0a020406081207030c080405040f0b010e0312 95
    0x1174024400803588840c1400030425550120230b007180081d43d5121300150100a01c1140030141c4170846042c1b02c582d1540e00c400f20580130240002c1c9ca1711000d0034081c000c56442d0b42c4400304e2a441071081c0d86540342d0700e05021700142c0004508507807150502c000110313001e11400480b8440c621075207200d03052141c423043c200c0301c0464106085a02d400c003c010f00c40b26540340c002652069204c4c89901402a031342180c50b031030940e00902201d066a0050050140213441c64090714070b0b00f48290384401020a5908004000d002103600154100c000041c1552586d510714050a050740d019030211181b10f07807030345001c0345c0d6918880c1c04812003502da900b080c04503600c00d900440d04481d540c40040340d115110344602040740d1540031211203039404026004114101402804010080c41c40680014251074210000c07038072480000508120524606e001005803002c01d45000c1d10300904100131518407840288001c00350714071000c0c0403960000d8403601c5441d001511403060f007404c648503414040003004400c142 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 42652153 1250 42650903 42650911
    0x60e011b032111030f01060e0111100b1309030314090607080604020f0c0f070602010b0316090b0105040305060708010611031c020d020d0e0a0209010b040b03152d0306010801090c090203 81
    0x1589070f0300050446550040550300665590741c0044d8154500032002e01400c10f10340084d1305201c0040744031980e03068007080e851850400c84c0000b298040b0504005020b4030350340d10b03000403407500d0101028240b50341a80000b0b500946208001c80d980c41d40b25190765900c81c00c843d20800034030508001517090801390090f040707121405070460b0414a07985041c070300b0624050000072070b9512009042205a40c24050321480a60641c05419500342d00711080802005038040c4440c925240c40940c000c691240c41220021034000c010b44019050108000700000700031f00c140400541d2402001c40b50245c0882122102031900b00f070300c683d008600210710043c0d002000d601d00c201e07038244200a014105030003039482d00340769000544450007443c4108030a41206030014880400144418440e40c0418811a030f04054549640569044a5000682c207454946500c890b4000d03613032a040c4150807030250702d50400b2001c071f0684246070b89920301c1c5400c9074041c0710701800c002803015080040380a254025608 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 42653403 1250 42652153 42652217
    0x80706020a12090f0318050609040e030c070902120106090501080601080402150c0307060c02010605030d0e0d140a03031a030a0f02030a0507030b01060e04090308010504020310030606060e011b03 85
    0x2c0501c640c03089001c5032074064042d590b00780070304c000904066200d03510b200e00049290080442d0303400c100c08541c00d4020051200e0080c0e680d0000c2010035203013041658204003841c4110b88503d600d610001e0040d4100e803262000c11161b600000c00d1a9000305641820f44034107941d45070490352080011101403034080d2081e6000b0350619043c10428000a0060448240d1a00110380d20402454588112011f5201540840e40340c484107102c0c035640843c2090071300307540380b508485005042c0c000450201c4592001840000210580030a654020035000500d502035207041041da80c0040e1a891142c10b52108070740c1c19049803100c140040c4d101c011440c526030002d011558986410303500c040c507142c1c030394005954001d440801008590340c0001501c503100c0c000c0c3e40501100005c0e5030050645038040c05514826900840014400e04a040b800002160041028820380d6524000a0083c2c00798281080c0080ea8030303c200403220760f0b1024814199076041d41c0303008480080c0d8620380e26202850328a00c0f0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 42654653 1250 42653403 42653417
    0x8030c1303120507140a02010801051003180609061a06160501020f030708090d02191e050106060509030706080c030c0304030c06050718051002060f070905031207020906060304080706020a 82
    0x4003040406400c00780210b680d45070141d9542d200e003000c40e1504006540084141c0c40121000c0050b68048a501d04490040d20291524402c45000790090441c038034030704444c1070907144510203009131074001d0101c650241c075040000070008246010641d1f804aa80b54004904110306124104104050300d60380d4016000141041d076078240b00c0b03d859006903041d0000807640c1e401d2007070480081c00540e090035100d000070820300c01901304501183d00d140401070041d008104401c8081006400302e0222158000c00030070149480c0c083c0a4100d0700a440518024072400c8004140b4500520449002e0104429114156624000d82d02800d80c0000e10032020008104101d000061650051900490715074403480c0b0306051520441758541c1603980080d10401144250884440d008143c064015004040b0700ca07103a504c149066038804103a91001b50188581840034035030074005009002c031360344200c079401c120b91111030030091580000c0c2d9028000140c1001220b000850690081a035003040d410202 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 42655903 1250 42654653 42654659
    0x90d0e0303070b01030b0406060b0a0e01050915030412110d0903060903140c03040602010f020702131a0d050303060312040602030d09020d0c06020604030e0405011202060d0906020c0706020d03020708030c13 90
    0x14083d01401c1c1c1c021076907180504140400c224171400b4420180c0928640141070010f4240d00400c1c0042031086141800b5000038090304d9034407500c50030704415111400340360f5607007007518110190150803903e8000040064950b4284104007241703480400e4556030b20350071021705545038003009144002088051240c0c612112300d500d09180003030000801000e01840d01c4900d01100642992009403a21008030310402080d00181e84518000c0d45501064000140000c241d48a800024007200340c40d5030300020b031040f04820003000000442c03280005078240e84810615040c07085190140d80101400f5820600c4610415161a030040c01c406000514030016040c40381c41c0c1c2074401080b40c21400050700711200300814150400d01d4400000e0007903400300101d40c5802c41401c41d0b054407100c02881401c0003d02d61101d0901e0350802103107c3c0e0061401c6540b200b4104140d599041e00b0301c10304025000301c100c5003850500900c20380c0c507043d4000c07040c540f5582d25140e12550a5101c0c403040b07010f02035460008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 42657153 1250 42655903 42655913
    0xc030c07030c0609080c0603160909020c010213050a0503031b0a0213020d0b09010b0405040b0103020c060f010509070804080405040c02100c02010c03060f05030706030c0c0b07090603060806090d0e030307 89
    0x8002503014079042e4019500703040e001094004941c00c007488039130100034a10404d8540d041240d52000082500c100c035518101e2003260302c18503680c800d800482c000700301d60036125030660092424440c4104402c07032140c1e9503024820315004603c20980d054005000c44c4024000300120a10f440c442c070700582d40813642035070005448440403808407038150f9000c00d49405038000c510500071810004c841180366585000c0900103540700358007a03540169280d0082072240e90203a01924120800d00c1d050f24a10301c1c0080010081c92001d1040300e20a0000101141100d4040c0c54201d001c0c03908107804503d8241800240409018100081400c5108410b104040315a04d4455000124400d40c004601403d030008000c055441c66009210701c0a0f286a041003141d40c00515081111400c0c2004203400040c40c0c4203441d0005810000303400c46c6d4041040165540c1e000016500703583d010349042011035241e0720000d07500c100803100c500869100401122500b030284402031680074005040b80e180001581d61 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 42658403 1250 42657153 42657163
    0xd0f0512190828020a021609020c060f040804030b06010905040203090601080105150102060406090804030f14011401080d1815111005061302090409021c0201020d02010c0e04020c030c 80
    0x104510705211400c100c0c403403503804401140c02041c00300c5141e580c1d9072110907082081001c90010080c0716400100c0000d050700070b001010f64214225a1920380507514001c940282d8800f0150424502412001490388010325601d00d00842d0080c814504050540c1c1d1a00005c13140509a00c0c14000301100004103903444c2d0005521605121010b05240d516004034182903417005409135a00ac807031a0358400f91079038009085613012b904500003007044401801e24a04522a640000c2d0050415226440500034490310000e040100003008001646030710404a40c188c1085c000e084298011540d0134486c184a1445160031b00080760b10b4041c5640d48041079807403c00c4428000740420f11514042400180a0054603c11018007206206174505100061106086d0541d14a90a903000c01c203164961a658090b801c091b078017800c0844649585030403407070030010900c4c04a00605c1098800300443e4810700888100002c40d403900c0e520181c03d07000704806074100400c64041440103000c1c1c4900d44404100c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 42659653 1250 42658403 42658417
    0x60503150a0e1504110a020a060218211504020d030c020102010e0304140a050604030c1208070210030209121506060901020a05150403020f060919140607031b020a020d0f0512 76
    0x395840d0f42c11001c00d100980700e41048050500205000c0100159004217030390803a04e910107001a030300c04100e40c00c020340061440e807994020320b0441c24020030f070810b0324680c1035203a000c40c01c80d40d0010038208861110201228000e4000c0c43c142d40c0300c400a400b071842428080d1050002043d001c0a0010311072541c0c111358450040c851525030100c00504041c90404c01501c01a600580703003034190303107581c0300c0010584907000030382c040b00810800b400b00c8030bc1aa01c0c01540100500c1654601400040103034004281c0c0c58400c100000200c1e102d1500015460001d559041c05a61941c1d510710401516030003800710b07a415800388401007000210184803140c070008510070002a142814140286000320208100d0f00c0c030741c48401800031380e41c000900302c840c845003025402020101441c000f24260020403d0040c148200414800d03002d40641018203010b503200901101c000c0e0141040380c0c0d80c0d03808007001e0b40184005048401281c11a00510385c080e008104440350005807024403016540880 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 42660903 1250 42659653 42659671
    0x1c0618060507030e0c03070e100803190f0323060a091b0305162a05151506040f050d020a030206070f0b011a0d05100b0c0705040b060301060503150a0e 66
    0x404001e1003d03018403602d1543c03410240145031a03001039000c29511001806a96040320007540081e07800c144c02005070000c1c18066050b40c0d240c0603104111000b1848044031800414442004140380710b00c20311a4644180160840344c05a44d0380d12001c554a1700c000d00503035046060008041984400c0d4000e8002000502e11004135400e1018002070403100c004d003100c90003001c0c207504d8502a81e0700202411960310a122854155000e0417138400c006035422200400724000c05064100c03603801d400d030082c8980d03003070100b900d200280c1d0300c10071140c0c1c89640544130811015110902c9030381450300701d5220844c0701a005880307045d12600040d55540000f4400c80d1b0003640d103442e000402c80072001c101c1c0107148a003801e00500305c15401c05c0c2030038080c0140b8203003019510320000340c1440b58040054002c0000c0d4517100d9840c1107001d070560b107075071250003400c4c040d5003031404400c06030810404a81c1203802d00d698450a503200c0c0c5140c601c554600034401c81d80b18014040101d1070801c82c2c980640505149 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 42662153 1250 42660903 42660911
    0x81b031e0d050a05060a090b0301140901090203070807062304030c030813091103040b060a1a0d14010b0403021002010b0907031b030c0212160503070f0c080304051c061806 75
    0x10200c01c103840700240920079203814042484502e403503480c140002d4030041c55000c1090724886010a0040c08040000c0d07288461480a2000390071041d80b281c20010300a400f0354204c00d4880d089559144850321481000800084a00c2124003641842200c1c95594a44592401d9620307242d100040003030f40c005603904070700018550f400c04041c510110041400e80c10030312001040c540f00d80c0c0d00d4040140040c00103104980010b8071662401d8112015041c090551840e0016076040b424058000d202001c110510b0b0407105d05041e007100001d18100d9524091140c5054110341c00d00c6100807811003420107664850288400d96038654031050321508a50360001100290100002c44007070b551804503041c5403410b450744142a901003a040c00010f000c10f03d15960300350f030301d402a68580c000c12000e00240000b00e031080421001c07803420340c8824003a2006040f01e64480105a84074401e912843c3c1e441005005411020a541408601018010000054050080c0e820980c8804003050210ba03543d0791 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 42663403 1250 42662153 42662167
    0x50409020d022707020f1005060103020c100507021209032104030c060c120503130201030e0f0601090911030609060601080a0e0303070e03070b040303090e040809030d0807030501060c081b031e 84
    0x10400f003a94440b00510042081d0401d0600300e5803611a80003600c2c54a60312003000600310f034000e40459004140703400450300f0b11070000d211130000b0b000a0310850014005c502c01c1c0c8000d1260b12054544224000b00501740a100c800c0700041484009030b14500004e20034040007000c50080200c0f0001040d00d900c82d0b0f40e43d0002850300d203030000d400000c240b090100030300c01d001c0c0a01c40c1000c0c0124446c0c0c2800e0020304050490052854a0400d0841c01010300c1a02c00115251050340c110103441e81c42800300c051980f00c5c0c801011384a1608031000c4089030b10440002d54558852905c498000d0000c0400207034004a9024040c00e651080b150079020450380c00c2500f40500b01001080010000f601c1c0e414103160960b500241110814480c51b40e00249020100e42030083d06001c50310300c44002011212a402da42c0740c0a8142c1104892070b0700464504000061020700403807400e160160b01245441ca8160000c0c061800301d11041d4010031184424400460003108000e00715940001c8582d015480e505 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 42664653 1250 42663403 42663469
    0xa12020d08181c1107080709230a020d0b040603050303100e01080c01051e03040f110d02010807050a090b0a030204080f0703030504061d04050a02030105030d0c0c050409020d02 77
    0x703010b440181c98100401000c00e50a00c0459184a200c0c41d02c8100040030244803000c9884a98510034002e803070080420001e4807500020f010400c035100903806103c15820102c00b207101e95031000110603c2048040000e65400c072070707070042c0000030072072000041140754100802c04543d050b4004641c940d02c004180414060030a42420003013074265040c501640c10491000d07101c2410180340740c1400004942d412411201210254540f8207101c540c540364585428162903c1607550410b6440709044021400310f0304001440b490643e40613142d00c0299100c13520211507a40c000020002040150903020070204482c400505a5486a035009601c4a061161160900c1c081d112004032640c095202007002035088001c0d2800c444003401c0800041b40350b15440b072880105000c025500ca89071004001c02060b02d540514180d0700e090303040712802c841c152025160500309205c05170900c806410100024903058000e01c0b109840505032040c02c08565000c40c800b010100034607200108024041407680e4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 42665903 1250 42664653 42664667
    0x330050307021006061e021c020a02010f020109120503040510060b1308011505040e03040f030501060e090604020f0f040f020c060a0b01080c0d05070903020612060301110c1e0a12020d 80
    0x19a510f10400c501441d154000c4c00392210402c20107600100c042188480500921220b01342400e04a0b00c01c0d8109107c4030025251580108120301040000a0041d0b00300c1c0305105440c803c6904c070003500e82445507100103903002d801c010022116445041400501c1e2101401010300400128600944616101c080c2201c0342105403c0741100d40c1c5800c001e1490b600052100d4801c480341901c00240901c00c0444003400d42c480e82d000f01050304002e0f0000401c0040c15440507007100c50804460609464550107151500c00036a406540981801d05050151902040307a031180b10000703000240f888c00140700e0b0390580e088452500c160760003100411500602900881d03107030308424a4100d80da031901c1d15035003080303014854a100540d9a180009190240035862400165800904440e203508a844003611000c0d002c440441c06542000c0da0302548603915000e8030300104591000d0142d41502403c0116410600c65440c26a031041c41c06000200c7c0803040e2403c262401c80e0301600010407040d8000d0041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 42667153 1250 42665903 42665923
    0x801050301090b0f040809120a12080c03070f0509100e09090604080a03020d06030b0a021b0d02070302040504051212040308090a02010906110f120408010509031201033005030702 78
    0x741d0408480000180310010101d500c5034000c00704020545550800380154091088042d4204400c1c40d00e0b000c64943c00500078420740e00c26503050280301e040000031035581d40c0c281e0f108004080705101107030800d80a21242c01d0a0f58640c6045400c1c4070521002540c00040d40307101c4070105003c0345886413103042c0402100c1e0312060b03040040016040a5a40e00600d109040c0d02108040c0e002c5018120006590010350040d904211201c803e418100c200400035840009036800c0c10344184010200d40001084024074002d094001c2d00c0018030715028400a008002d03c1120031b0f010720020440701c4401c40d00541030b0400d5100710b8120f145424038010f4178448010f440e06003140d101c0d011040040c0e92100083c001e0392440d2030000b43c02d860b5400a1450480140140d0002c0c2c015602c004907007002080141048030044002481651100401c45482e84110307060541800c04000051002c0342842005a0100c1c25440c5000820903041072060030426140c0340301000540000184400341e035040140c2c0883c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 42668403 1250 42667153 42667159
    0x5040f02040305061801090503040b1902070501020c0d030306230310020906030138030601090b0906181302040e01060f03150302010e060c010e0109120507030207060804080d140106080105 82
    0x41c09045440e83c96403080000c100c00d040c8140d841035001d103d90203400170400217500c582201d4032107484400c0e40c1c3e641d800880a41c0c2c50341188203001290075100265a404494041c1c010741198190780d003d0241e40b1082400079814152a00800107030088250507161901030008208083d02004c00105810b014034052500352060041c0300c00c1200d65107050840e030441da40307040101610702d200340703941012000c020141c480c943c0d00000d40100081d25440158402d0409030b860442e10341c3c841c4401415401100381650b00b0410a1100c404040250200300041074001400d03080642c80001c814000d90f40150466800c42c051040100174064001d902014260700d2802c0c180454101070445a82d030507414880a0b0400c0041c80c640030720b0b503c40c00c0c02c40d410300080000074442c01503000762a9028259880040b2010000941d2400c04148154255005203038198090070343c1615101c0100c407510070191064888410401503014002d11611400914090311540d003c20340d03151140103400c60380141d0140e40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 42669653 1250 42668403 42668407
    0x100f260f010803030c0f07020d060f0b030f0109030c0209180708010e010506010e0102030702040f0618021905161113020d0c020c03070b04030b10080a20012a020102011506050405040f02 81
    0x60704d103a40009507603880c86d07140c284644a01980c00010381d480b50000003e0100352414154411410041d000301e80600401c0c0c080307850405503007489a00b00d403c00c01c00900011003144200006141c05141d00d50018000c10b48100103009031003009050a0240d0b1020003181c0d920280c0220402080c040d0319400282400e01c5071001c1d01400000c1d417a072048120081c42a0340e620045070411550b40e011101808074001c1c590403020100c0c126400940c029021030303083c00030300a0307001d41e03040c815011940040c0e021803079590418207507075410341c0343c3e50102a5103501c04421181c01071110068805004c00c840d0403400402c1d242040c2c000030b81040214114107001e1b420508003807000e803981c242120110782d07224120003540e540314040081400f0302e03900098028000c0d00421410700c0102000580e22a440104101000d21044010340703040621030403155890100c4d0804a482c5c4d0400c01c1ca50004130f0042c000030803110040c0c03416040303040d0107400210200e180410240b0490605110f504041c3c520088114 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 42670903 1250 42669653 42669661
    0x605011508090a03050301090905010608061f0b07020d0b100302060f07110f01021b0607080a021f090b040605130203100c09060201060b0f07031701080a1e02100f260f01080303 77
    0x20120306c414010a141c1c07903104c010650401009600c00801402d0752001c3d01da0600b0881da5440109121103c100524240d8100125040c5920400c460641d98020103140d441400c3c0d40d120462003400906a41d80205078440000150300c1d201c00410007140041d15455a54202d8600f80d9981840d0780c40040c000e10081e03c2510560760001190700782c9501100c0c604900c5c3c0c0c0780030001025481a0203000b00380c41004a81404156000281d01036100304003a001800b076401ca21454007200e840b040c010301b01181d690b002c240884c0e0242c0c011034020661403048102040d064000c03074500204010100402caa845518481d203a030301180b902c4c0601441e01c001c4c00107134600140407074a40111200e481c000c401c000340803c01c141c015000c0d2002121b8540d45000c02e50b030744400c4551902da602409550809008800100104058170314814031507005107105500d941c001d03002c44000e11784503a10400c0c861540c2100501100780084140c0019040c81c1400561904d49000b00c1c000d48180e02c0007000c1c2c0e0050040c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 42672153 1250 42670903 42670907
    0x50a11030424110d02031b0a2c0d0506071b0c140604080d0201020a0e010e010206070804030e0319060e0d0804140a08191103040b0a0302070204090605011508090a03 72
    0x3214214044200e000c40002d0044000e4010a00303c0380300a080b01c4001500461800680c000d58419910f00c0c0721503160850035806928544660b034140700009440400b14680d091800001205000d10100e400203010000c101041401000740c205a81c180e218408104c526a40402c0c0b203440c69001101d1000c904160750b490000d645079501030103580c03520141201101c0d88074001510020702d02e01080314040c202c0d082c006030017503000724025000540d90080c01c004550040b140300710800b0040e8000c0601e80c1e6006030480d10580083c1044081080709055100036039000c0002c40814107881c010f00014002038900201150000c40007000560441a40d44110a4020140c42d034440e810070b0740000c55242c14445507042514918009010305004a0000c0418a084580101854850300d0700e002c0e18001040455503030240d4801c0c060400c0e0708000d03110007240700b0303005403030303100e2028102041c809800c0d0303100e4043d150240c0040500e56802004040f0242c5d00a51003508a094900a890f1342c0c4115100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 42673403 1250 42672153 42672173
    0xc0105090d140309040216060506090103020a060e040b040e010606171509090f06040609020f0102060f01210602030a0209090c040501050d0c0c0c080607090608010e160504030c0603050a110304 84
    0x2030482c1c01802034100752410140110381c8448801403045548031084d461001c245405644140e58031450300700001c80504041c40d01c00d0580343c000748102001490030303000311456041900c0d010f8225440b02041000b82e101c900840401c010240f001060035070604d217000b0400155500e41d01030b02000300d0140905080802d1100503c200240d44844c82699034000880c84c0c00740380035104e078a620602080000740582c2c0d0b404008558402c450071209012070100480c0c1d10241603942c5228034040c880100300540228003d8000403040000c08004040036131204022604215405c401c03da0300016840031501c0c00446403075003e511030650300d0500c2e08010000700f2600640002c49052607803460b0350152035010300041c0d44000d501140020106484074803040e1159816186040416001c01c0c000c1805402105424181c0324009103041555440c101d5031000e00c0304081c03900c01071220400011000c01c42011480000e0700b05034401046d80e041c48104907040f5550b140100148102c00e1091000081d00d480b5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 42674653 1250 42673403 42673429
    0x6040e1908031618050111070b0316030b040e062d04060605100207030c0608071e0207030510060e131416050310050603150a150303030e0609070f0308070816030309050c010509 77
    0xe401071f80f1107407412070702d0b1500007503400c01e2050134404800c0101c00103886406415034091980d041c0404181403050200b594158000b0440913003103000054801c4061100d0115003803030380801b1032100c078480d811a01c00030b982038805440ac01e071144030a1202d8282444c0d8114074107680e1000344182440c6440300e80c0000c00a00600d020041c0034070204207060702c144c1c14555030031590300c0d100e48445002c1c02d020f941c44130301d0310013181c4034018020103072000c0700e842c030070102142c1c125503059000c4d91392084a034801881c03000c0b0480e5550507200300d000c1d0f4401c0800070a1000300c4520440803040303003408100745c9000025149690b0303003800d00341002216140400c100c018403402317100884440c1c0752254410054001714049201c20718498100000b07055060300614200701801041d02c042d901e615813069181e80c06401b90101540c8007540c1000021a400c00600d03815010304440c2d42011419450094840b25801042c0c0001b5180c0300e000080c08020302144602e0b000909100307281c043c0e800041b42c42c1c007040078 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 42675903 1250 42674653 42674657
    0x602070303080907030804060507020f190302040e031b07061b0305120a110c010209011101020412081b070308040816080606131401060522050906040e19080316180501 73
    0x74022403d1807004001040280d44c0c000c4040d61a60f80740e40004007580c11402c4260320880c050600088242424407202c0104181200d030078002c1c0e401e5800b44400760001c00506200c610040000c5c007d503421150030b8000f030451f103001810300c43d0b192400091448034032104441e0391003403044208000942040c121f4103a40c641041800c01940c4003001c4d80020490404140c8004100240d42c810144c0d040d1b00030098940b003625640c0f50f8240180b00c1d91700300d001e940036805420420424808c041103690004d4403944040b00c04968a120203a501e040c1030590b02d500484010310007040a002a40d0180124400c0c2c80141d9400000d2528000c41150b5403d0041d001074095607101031950340306101c03600704400c00d5000c80c491307120550352600c00504a0788404003032040d103401c0c2d10580c4003200c0b400b4048011203000074584001926904204001030101c030b240311140d441520700e092000304e4445006511036004200f1039440340342c80401d601c807400144500400f04190800c040380c1c03504c0d0100028007551001c8c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 42677153 1250 42675903 42675917
    0xf0c04051e0403020708010614090403030209060c0102040e071101021204030807030e030c0c1c050309010e0d05010e0604030e010306050303030a05090c0a090b0a0501050403031719140402090906010602070303 91
    0x1580c420307001111001c01040c90410035001c10091507000240102113540a00c0200081980c810b14003d8a614144119901610402c08140400d1180d00540383c0702500520301450807980d810800e08903800b5a00000c0d080e403600c0c040100c040d40007148c16503000c0481d4006c0d480e20008504a004680000704003c2c180007484005c5841d40d840b079408054120050404c8a035100311864001c4c0e5601e14200009100c4c410800034000c6c000c81d038000601e070300c40e44040191b0230100c950005541415514049940180d041d00e9900042002401380c66035804c01900501543c0c00d0a080c014543d115100c203c606250a0450400c2070303450010480354803139a60100017a19032200c00189042c4210f5000e103951004441e90003042120300c0364041000c01c8400c40d1031203007180d9100c005443d140224440540414100e00391103010503100030f0300ca07034012038064001c405240b030480e50804580758440c4070204080f82c4000c001c02c40c1005000750341c02000a000805103580340440017540ca0109020003030800a003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 42678403 1250 42677153 42677161
    0x3030402041d15010302090a060b03010b161e030e0402090607060f141e0f0112030c030923040506030724090f2c040201050406050c07091b110f0c0405 66
    0x190110059100310b400d4150740118a400d20745549014003800305038031400300e100c0480c0a5030703000e108550458269208650440c3c1ca80108603030103811403aa40341205a2404040c40000c10917015200201c40070781c2c4000c104031460900030400183d8000b0300e4050380c41080300800300e55440054450b5503070f0200e000f141705545031180c4005441c60395a004190043d000900a5032781e0820980c03580b0000c00509614169140803082549040138482d880c60015400341c90300100b4443c054150f0254040d00b840c50381140d641e062121120380000640004000202a000152515000b02e98100798124000c0c81c0060070020b55441102c40070800124403025101100b1105000b0306246c4000e011046080d0922592200e10000c0c080d0400390822001d480441691180f0a401030941d020755010707500d1601340340c00c0000a49844d80a240e404030144191a000102e0001a00801d803200c02e081600342018008030030050445841c0e4814910746803c00c00501d01d40d414002520309811800300e07004644c03901c0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 42679653 1250 42678403 42678431
    0x608061003020d02030406060303020f010c08010612090c080c1c0503040e04020d0614060a120b06061c180501060605030411270702010504031404060909020c030c16050102060c0403050303040204 85
    0x450f0f1020707400218004400c12062003500c0c0d110b601164020f400b510701c1441104c3c0b141d4200c0d02007480d4400403580c22401400907512070800014508034080001802c56100d40f03c103110003c044d88810f2455114010040190500c01501c1d0542d08140e0305500310103031144d49890302e90195000e01c405020031500060f0640d0307a00ea5212034180e8004a0800602000e00308081a96008440e418042c0126400000320710b401c2404000310207801680b45d403e903480342820011154030011030300b2904058100085034003681c61003100c50b081c03462500c800340d0010f40e250660030340304a54000d03414018240200701c04144803490000221030201c665900d0b6401240e40360166080f20080348100400c5501048401d0341c056001a003d075000781caa0a041e820708524a41d001d10580c0120790001d120303080c0c100900034264011b41035030719241c5c090b00c0c1082454603486241c00560b880380a41c3d004500c0d0f0401480d6010700c102504000c03102c2d20301e840c01e030035510b070300d81d0764840904001d00a0344e4030748420150130 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 42680903 1250 42679653 42679657
    0x30507020603010603020301050a0b04080a020906040b031b0301050c120c0a02010906091a06031b040b120a0302070608060603150108041a100303021e060f0c090904140105090106060806100302 84
    0x95030050041ea120b513100c030001002034009000e010b0007441e045c0b802041d024500d40594080315488802002d41e0042d55007808103040002e4200c2d0380060f140c60b5010782913a41403100d5811001641240c06d01c1d80315140070503080d0f0744060208540e56004101d5011900d00c04c080b41a4441d4a4070080740c0c0e1507910580407401000340c048080d041c0740c80c00c40020100100106414420072203e0f0131082a900c0d600708168a80b01007035081c010350f410780e151078110380c1407942101c00c20030b9006001c0d00c3d00d440e1204042e410480c1c042801c600581243c0e406000403908000902d800803c00e0310350728218030342010401d056040c2060058140078801c400a401c0040020b55051192400c1411205904045140c103135840e405010803400b6003e0908008010004541c500f54404001401041103440d00f074450b4140c1c0c1c40c0684040da40d48000c104402464941c058224065885205421040d04502d10300c142104c401410002050341000c03401c0041c181c1c010455a000b8104480452203030000000a070300078 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 42682153 1250 42680903 42680917
    0xd050a0e1e1228030e090118090501020708190809010903051611040e010c020d020a08030112020105040806091b0616200a080a03020c010908060109090215070609050c150301090203040305 82
    0x40f00c5580c06100010000401e01d0485071007600c507802440100400c2103001c0209018160078180188407070112000160450b40005004400040c502001c588502000b94070410802d1240c08030030100380b00343c680c84181d065115402d10001c0103100c038103540042c42446002d20880124184003500e83c00e100314405483c6400e08020410005500f50b80b80150180207c20b030f0f040c000d800380d107052142c1680003082150290f0b50202c1d1541c80c5a0800d9480041c40c070b8445410303410018140004200c071441044002d02401460b0300520212800040000f584507a40d0b141d2400f4210030711040841d030303009525116855520102108600150003000270b0504000c03901c41c1d901c5100307050300040c510800700d4060030f5940240d00340d030f0f003000302c000055414489a101d10b85040e4010401000190300307a078000c220440c4004c0600d490710309180c4940c483c03604501e0040d140705945406400c10441c0070810503031262410f0342c00810341c0c1c1c880f018441c5103000510a0460b5140c0000010b410144203004542d61 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 42683403 1250 42682153 42682183
    0x42d02130f0905060106020105011403060c0c010e030706020903190816050f1e0105010f0302100c06020f041d071e0e03160b0d0e0102090d1e050d050a0e1e12 69
    0x42c84240d802e055540703140a2180b0009035103071000202d240051808640300c40030b4042c0017006503440d4900704507045e0b030207d01c01d909155620412488040c1c0140010034045005a4006d41c564559104241c1412a000c5005a030100d01da001c3c3c3c800140d94005407184011004148600c08015080290412100101c201001d0051600c900d050130318040c00e520781e440312280204016a203c800c021020000da000181d40482c8804140150030301c01d030f14012880e485600e016081c50940440b08080703400680041022504042154a55101c601c0d84c8a030310030104d10f0039401d00070b448441044542c0c02802072a0801610030062212034800f00116407082020001c803803007441e074408600000c0c0d00903a00d824105170811148c498034000500175210000402407542c072101d0207070b5580d0013405200d140302d8054418024100c1c0c2c089030003488680100c0030a901e8541c0c0d00d9030101e0000b0300160700100c641d1b1182e0312455003007052005802101516a030103444c5242e1000c2000756440c82d05111084c40b1035 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 42684653 1250 42683403 42683411
    0xc17151813030e09040b0c030403090f0303120c020105060a17120c0601150905011713050706030606020c0a0f06050703020a05010204030615050306070e060a05041a03042d02130f 78
    0x140c0c64400e038101c1c10400d009540e9440c000402d4010403240400c15640600303a40d11300b401048110300003a0007142c1140c030904150300e001e40c2d10650010554041d83c801d0f404103100384201c1217064268010442c0266461000300001d00e0200700280c41d42d00140a2405044840802c421344940d0800a10b504809055a442c0d10b59a2119a45a031100c0900507a29803a25030755050014501800000b01510030503100c020f40f503080726501c90280b0a009086c20744d1182e4100391130000c100180509009003805540c0801e0301130a14001929055a4800160251a400c4400c02042600032a00c0090702d17103910349155942e405042c02c81c52b1021030000500705520000d0000100101c41e44a04091543c515488589070b40d16410103849290803142e190110f40c1e081c074034040f00d180078002012080a141002e0342015180d911b80c1103954802a40c41d1500800002400103100130350b1620310340c4610000c0403148080030400c0060f001d5404c000300038040d980c084400d02e001c65440c3c200e005002820b0388204 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 42685903 1250 42684653 42684661
    0x1e0302090f01080129061e03040b0a150303020307020d0201050912061006052802070b040602100b0402040807330f0f09050f0603060d0618060c171518 66
    0x445030070001c0c800d4900030761030180351640003440b6424451181e114840b802001140c1ca0040c00110b601428105d45420104043c0e4601c080290000c0c60107076024000000312450030384c6854048070031030f860754403142c0e040040400000340d000044401e065030554035029040a54030043e14180140310b02154020410074030321210407070024440748645584586000446d0340c03120300741e95a12891402000300d221102c030910329074280841c8401140040e20454400d940c0d922070203001d40d0416041080107801100c92100318200b280192484010101e40031440d040c074240f62107659501d140316070a4941440101c4005500003800c1268036000759a20000401c0c4460704020411046004104007141845e01c0d110780070f61007220b251081e91006428090204003110402800e6000200f0b40c543c840e182c040101c00041e12405120010b4035407020401495900d441d02c4015206050001400c000d000580b01010406010300d49410140721942e050008a030140407598681c40c43d0b84051801140c0005c1c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 42687153 1250 42685903 42685921
    0x703080c010513030504090b0315090f0616090303080a150608040302060a0905070513020d090f05060106050c061803130303050a110102030103080909100f18050c090a1e030209 77
    0x1448100c5203000204042e40c0c2c0e0303140d821405411a100a00051000d01c0280000450783d40000840207008048907106552025621000300c03007140d6888284d00204031700c0099660801189400440041040c112010a000b00410181403480003408000c0380c880402c0f0300307503100d500c10440420b06102030840551121006045070380291400c030700511a140004e01e540b0054490f042c0c219078080d000c0d141240ca03010400900d240c0e4200c2000483d1f60170000c40c60600d249116680560307210b1248500407400c5d505080e401e04005034000c2c4240a41080600e110000c04100e42d03a0101250260341808142c102c0c01610390301806a1000107554006804014590444080c000036800c03940d0f0180b801c0c16155000b4241d001c217200050005005006035803052034800a019031088008400d522000e0352200d8440080d0116804000c00d203502520b040b8052006d8090160710401c0004858a0305a490b00481c20011640c410101d0041982400c0c481c4600011140300003190001d2480005040440c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 42688403 1250 42687153 42687157
    0x1505070c0b090703030f020d120209010905060403050601050f010c0c1a0c060709240c06020912030301030807020411090f130f0c09050a08010506060406030506040209060a0c0209100803041e08070308 87
    0x1d401051b800c2c02007646407440000c0100658203659205110700c0f0020b029080a500144d400d01c0c1885890725021641e40c5511014000a5008038004c004952401d0705005030011905006810032800301c0002010508151400046500202542e03000a03031034180c10b0305038099000c09002902581040c0100300380d0003031000c002da94900b03400c0f1100161403001200301c2c131082d00c0c0c81c001050100300054003085580e800f800c0418805802035664526001c3e5107401e5520036041140e00c5038010404505500b801c2c80fa602114406512107868900c01400090358031700d50140a41c0328103024990068802d200f0340000d11030401c2020f05001c2030801c00340140400302c171802181c4c014401442e0000d030419050140c903004a0001e1b111526003400e1110842c09010300602c0d068109030208800704040c3c545200816800d4440d6590801244492040000000020341211003150201e04144100100807089504450701c508590002c0030b00c130320440303034016055404401e0302d0050320000002e12402c000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 42689653 1250 42688403 42688409
    0xf150d03030c0e03030408070b03130515010801060501140405040216050304060c03020c060f03060105070c180204030b060d02150a0306050a06020d021204080c0d02030a0510020c01060b03041505070c0b0907 90
    0x75440301c01c0e440a001c2c141e4078003880c450407c81d60f0029208000340b140c110011600405410300b0758a11500325201d10749044a11003a40402d14000001045071002c02c3c070851015107001d180c81c414044d9103014040f0315001e01d028940c031403603002404680101c010800410b034150311005030b940782c50b0382e0072016000b90031003502a1f000d4058901c0390003240c80c001c421100540900f214003402c40c1c4030031004403000c2c0c110704002c0314107045407000420002106602c045013108000d001507501c906600c0c0503035424202400b040d0040c04400919801030380d58107100d0703400032150400b15448001400044001d4619a0700050b0042050307031300070801650111b0980303c001d4803074003160604180150030701c400c2d03c224418034445400c0318100b0320705031600217110092a0300050488251201c15140c05042c400b0800b01103031081c2d03000483c40110034080c000c050090002d2851030b42185450380383c0c61050315240c2c40c04840c01c1e40d51000210158010324074030307143c0786d00080c0180782c030b03d0032b00503180d611030940c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 42690903 1250 42689653 42689657
    0x60b030d020a0c060c030207080a0506061011060114060906070602040e07020712170705100902010e03011413050f030c0c040b0d0f03110309031609051e0f150d03030c 73
    0x540400d00c0c0c0001008442c0c01d5000391a15909450840e00b200c82001c0140c3c00c4046004004001a03190010007110040d01d01400180440782484002c11115140a11003641406400c000d620400c103404511581141c0500118400304e00142000551601c80e4200140c0c1c01400400d1000c1800055030203401900c22990014482d40c4450304141c0c1c0c1c0301024407076502c0c1d400359241e0840009035080360340d030910099116440d05211059844500b44107003110300501c1c940e0749205a0096690040d1580c0100c0c6083e402082906c03030b400c8020004087c0100007801410720f14151508200f001c00c00c03a4803151008003500c0c0c488110038800760311108115030f03651250381840c13002c2240f89040c044401059500c445c040010105654055640d0044200d07020351901081c0400c04150700c05000c16510141300c41c25035211141451000e000700c40014064070004400b94810240f4030308403041182e006500c1038401c1c1d00581d110b54045484011100c0c55541207010030700d0b124101a0580c000400084040d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 42692153 1250 42690903 42690913
    0x703021b04020c0601031101030f051e100b0406260f010314030306060a0e01110615090c0906041a04090c0338060d0902030601030b011806050f04020c1009060b03 71
    0x800c0801007a8001c010210020f0780081004000040e80c040d0310070f00340d41040c103002c502071181c00c20760021241c08542c00e00003030403011400180c048030580c100f0780c825110b0b800f499545043c903030070100c14051402004180b045144015002c80c400b1040c9201c142840a4081a40d15104010541041d0203100444a000e41800c01c907801c16000700c152442004054460350500034003000456a851840010905000f40c000034540401c1c0184102032150707120006d10780c105040e1400b800180342e0000c0903030300b561a06204110386550340704110741c1181c00d203c0c0c12001a0031286561113440c4650740c40340700c040740b81c41a003040840e0143c0150802100c000a200114481207814800c040210b02c5502c0c0030008592514032186407a9000d400410b808140c0000c4c15034003a40400d01d859001c0c2c002b5200d411072a0010010382d0006210507aa01002040510605142802158040120840c224480c64000c119104003010401c960309450314034400603c164002814000000c08101d1441030090042c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 42693403 1250 42692153 42692203
    0x20a0e090a0c0c030e0103180b15010203030906010e1803040603060f0b030403020c0105030a20131508040f030e090406150506070c05100c05060c0406021c02100b060c0102070302 78
    0x301e01c1000b03501400c60315514188502961308030741159240714200e06040e030700c00f184890066104040f0b81105e21480c3c054607603041040c1686d1012542103110f604550042080003d0030300081200c0b811a440d0b29036a070403e4985440c99207082c42012504106071101040c0002e003107a054201c582201c1c80070090b220000d8071400f42005034070044401501592203c6202d050652181004543c806180d40002179071004030349551000da0300c1c1e40c0002c00f00200c0803a074000d81c90600030740c220040c034102c1c0c0241b558405600020b00407050080001e000f52210340040c8090501501214200c402c00415401c6146071034030340302c1d00922320b05c0301c2104c98010506011030b8905050007207924160704403803042d1180c1d01d85410051812504a00d103000c101c071284842000035420085103001e1614405a00c0c2c443d0b00b02040285844182001d080040000d820701c20540303a0040f8014103070702001c11001c9200304101011800038407072080780001c2513200081c0c3d002070540c0032800c8003902104004820722200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 42694653 1250 42693403 42693421
    0xa050910090f15201c0203040f0509040f0308060102031b150c0903101a061218032802070e0a060608090c061c0b04020403080304060506010c050c010c03050409020a0e09 74
    0x6641103030001288803404546502c0751050016072100c10b00f40110342c40d000301d6178281605840d9002c18840980d002040a02008201c09040c001508041d40c1031402480c242d00e40780105001c00c3c00160a0200500100707071281d20034000c03150404c01d41442d02d41c0c014200c510f2980e0f40c0251400b19140c0341c901c0302c081403a00900c18104e904d580b00040c000d00d071201d03100c20148000c280700c28160141d1000100204610344503880030b819080c20880c0b944d00d0600e450780c1c14844443e00e03c4a811000d42003042040c80101448400310700d403004003887e502c620148000c00b80d10f0044203410080c2d140c20030b00b0801c007510b4407070707000182500d80a07a54425143c49410700a9610001d07100e40c194000c00902082e81d0308040c16402181038020b84030017169002103640071900704e034002c0c0c00039a1420310008c104418410349024040d0002c4080c40c0544006245481d40c40c0c8922100d170500741000710407482e445c1414850000d0b10064900e00f541199141d40944019020008132088070707003d40302c0c030300000703c8203d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 42695903 1250 42694653 42694679
    0x303020606030f1b030304031a040311151305010e010603060e0c01030b0604090c090b03041a070507020d060c03020708030a02030603010b030d090618080a0f020901290a050910090f 79
    0x5100741006054181071604e1030450b0304142d81d40c40b82c040c402840004042074036850246110f64001020b00118142424020801c0c0e41c080040041759200c0110b040200c10143c0c501c950091404c0c003420210ba4441c07074101c0c0504100215960036600704030740402400080e40c845070710104403100b00d581d1424010015001e03640348610650f80080c06010800200300c1640003007030385d018586403003c5850340380e4804112542080d101a120b101075041004007000081c54000e8008031981811418180c1c0703039000495131100d54a00420140c3c40d4070695000c44e000b03030155500154401a20380d00c80c94201c0c0604000d400c02c4500030706c290700b451034400032801d0128490204181660300e40404504062081c3c4030020a882088a821655040000c801c00c0c180310041490740b2868500031000c00e203004021814006030080185010317404034240398180700c9520400fa900039442200d440c0d8034969070a036154090740b0401074101d400c0068501b000c0b0fa1002403401540e1400c01e10118a80d00e130040b441e608 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 42697153 1250 42695903 42695923
    0x32301090f0b13020a02030403050d02030307080717070f030b04020708090316050312090a05060a050309010b090601090e040c090203090609010515300f0705040f02090109050105130302090c0301030302060603 91
    0xf00e2a80e0f09040150002c4d0010840142580116441c00341c0e241e8030203241c00620f46074032006820110a00507e65484040c541c0c100c092450030024108800e8500444047d02030410340500810803510310406000760441141040700800445d128002814480300c90340c860ba8900e0301c00c0c010490700d440d46180d0031080c04140c4d403020300144444000720b00b0407503040d800702c081603a0012500c1c00025503592003400070007240c640d40c0e880544038181010081d0130340701484109482200c14104001040e64401a15811213141d11408001602d4504100704c1e840510303044407015034000800c00500350f20002d469401407100d10001c218a98030140310350741000c8a41140c82c0c1c409447d401a189007050b200d40d405500034000b80ca44420082c03250440cac82c0c9010900900d0742c94004003003c00041c80c051080d152100300d6040103501e010810b20008000b64030500441d0306121010440c802da6074180c1c81d16402031580a09100c2403403c0c00d00241781e00c0c3e0401d210071030040c414040003a00c941000b040c3c8042d4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 42698403 1250 42697153 42697159
    0xe04030207050112020d020409020a0e09010303050f0a110a0302030406080a150312050c010515030f070509041b09090f061112040305030c1303060603020909060103110907032301090f0b 81
    0x10505102c01103e0f690794501104c4107954003030003c1d900300c00c0244001c1c001000301005c010fa50341d03104d11002d4602100400158840c0320550010800720340c105c02100c403141910f00515580305176001c0280d80f800d885000041c80c03441072022820804d41c000006205483c0f07a5202c000c0c455549088000554420b101001c880c00028141003002a2450100280f4404bd03400c0a41c1401d5403504224211101140d82441c0c10341c004800c101c0f142014440c0c4002c1607483c01c00b070b04260307042c41d01007a0b092401820007040b0461904100c88240030341702c2c070706015088142c41442000c81d076003080075140c4031a007400da030402c0c40c128400b07103031542e49800c80783e8051112001c43d20300c1d40c2c3d07504c043d82c0c640c00003041401030603810860b0b244444041c10750000a0743c403511001030030b17134110300610009503001040d04005906c1000140003043c2c200203c041e40c84000c40700c5a081c3d90f6046070480c0505404180e4011040490040708949031002180f98140c07810a042041682000402482a00d0400c0010381d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 42699653 1250 42698403 42698413
    0xf060504030f060b10080f060609030316030309050a08130609050f190906030606030c090c0504090c090f080f0c03030f0d050402060c030f190f090e0402042d060e040302 74
    0x840002e00c403144907014071000035440c002d4402103004122400385010015151408115001e400c50301401c0e0071540654845007400d031441c01103a980c0c451505104150346241d9400000c05200360405991325910000b500c0a0304254600040940c00000300e521224041c0c170000710b911841018504115000102052091200b42c03050000140740c020909418034203000d0040381c00300040c0175800007148503801c00600a46107050000032900e45820180c0c940d800c4c990246c0240340d019042d40e050301e54109001405049620040e075150318680d10040b400d0b060340c1000111403201181840700c04401c54190b40b941800201015100d10540b0f041d41c022250903c517101c036040c8079500640d13000e8809000c941c0340162662000d4559001629a24083e10b00000c0c01c4a43e1041056444180561400c0c048003112034190040d054032082d01400d480820031000003420756139a5040035000550f00ca0b070048000812103180545101c12401c200d10090909100244804030410807034456501940648 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 42700903 1250 42699653 42699659
    0x90c0916030f0f1508010b060301050105030621011a03060f071d04090c03080c1603020306040b060409020a030308160203070b06060a140f0403060f0e0a03030203090709050906040b010f060504 84
    0x80d009010919a0002c91a40ca1821040310145407180005110201d401da583c8140b0302a49982581c00c500802409811b080c401004107917040b03402d0b260040e108444000c1201d280d1101c460400e110404441700e00e40c2403008003800341500003501d80d0802400d42c10b541141d5211401c0e460058015074808001030100c02c14003080c42c400001e61002e1010090011a000c1c56944910186085582058450314800070700704c0b003650b008120390007401600031015681386256800003031f2550741c0140058054800b000000e4a0b035541eaa0000c8402d541c014006e00c00c00c1c1e1241802001c0301c0d000c994405c00312441344030b01c01900f0700000c1a104c101c0c1d4000004c4080d90340759400d010094100e5000c03202408115203a090181021402804200f42c090b0f0f841a211490b500301755040d02e0741120113001d2603103072005100c03030500f012031040322054240c200981c0d261039800e1501d141545542c0180581440d00090120100c03001c20701c5030085018820810559817581c456403120130f1030f0b200300004a20200030030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 42702153 1250 42700903 42700907
    0x7020a021305071b05010f060e0108120a1419081b16020604030c06020d0f0c03020318280510020606013c0f02010e010b030a03030b0406030c060206090c0916 69
    0xb00e030b03102c1c4140c5001c403040e0314020761603081c841030000c1c04c59541c1d440c0d44684070204200e02ca91001041300001d440b4055151100792501c2c0d070f40c00104000b807100c0c00260016800c2c0030f10100d029100b900c099059442444440c95440448400610000104000d000c80c241c2401200006240700f0010541380c5000c44160341160340d040d10b0031003260000d105000000104400602c0741005040741d0b005092402035a04005190301c103038400c1001800460305942000c00d41c0002501d200d004101da004030000da054000030094003c2c0e251400300c3d10341d140c00a506c8091940e054600303c500580394000900c50000d0262384800086039201d000407050b89100014000840b0b1301d03410004080b44e0000c00080144d86400740c840c088866030081410b9201ca03000c070b01d80c248203007415010140000c000307001110000079141c9800c40000346c2095101c003410f203403e58440d4803241c029035105072601e40d07241d506e1501039281c0c40100c881c48168000d505010b6a6800c1030176280f442000014040351100d1421002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 42703403 1250 42702153 42702161
    0x80105010e13051801110d0c050301060503150a05030709020a0201050a0e0c010804060b040c0e0108060d12030b01050c01050403030b0a0b031e090a0c0f0f06020c0a0611030705030304030c0b07020a0213 88
    0x2c0c1c001a052000e039131072a42ca0080c0f06103142903c04522069481e00e203000200165401903122400708a03040004022065000c01a00d811110301000034500c08094400124407001c0b0740c102c02e9050003103000003d888440e0740d005000d10311094009008958076040d541e81100e40300c8180700c4294014048501e0103610600a16030b1051180000207102d40b00b00380420100e4004000590200e0b0400320300701c80e9982c1100400d64032540403070f250440e08006070f41d91952420310010300414140c84a43c54070f0309038002c0e800d80e455011140000c00c00c3d4035050a0040c040c007110a051070264600c0e1074080380f04400d82c42164442d50607240b0f2900310801c003a851072003400d0700a10f00c020a000c9c1c10703020000601078880c2c107001082d945003c400540d01700b280e10790b0385102c1e1360b00c03500640d0301c04482c000c0c1680303441085504540071400c14282152401051506610406000419030f0100004002c2003540000440d01c0450003074034100a280c0d0794140a030703900c0c062200042c0d40410301090313000085405800c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 42704653 1250 42703403 42703411
    0xa0e010504140909150c0306091302030c15071406010504060b041a0304020103020714011e020702180612030d050702010f02040b03040609020f030106060c020f0a06091502031603020d080105010e1305 87
    0x4111900c0d81e403480c5061781c040f20b0a0b03d0a81d452000001403150501c1e0501c009604022249000951290344c0d50000740c0d640e118010040c0030701002407000305482050340585001c03036040074a4086036504940640c0e1244024068a480740d850a50007240b0104040162002d0310b000b0f20540560500300614615940c1005104030304254007000400d000586940094003815041400801c04501180c10580d00351080014812110302c140b140d0400b50350703011200710300214600031480d002e480b00301c007007014101c112a60b04100e11001940c1528584281d024501c218202da000300802d01d406a400d800f03a206c5c92050342c5079590284045404950507910140210b80300070050804c4a5001011a0a40e803031031f400500807662041e4000103506020203800750020045409062450804d44040d02070340c0d075802004092030402c0b03101060540208211000d005a1040348a48007156160007503445040324000ca001030243c8000003441c0d401404166504d1030028442d804c0c000740e0103c3c1e00c005100083c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 42705903 1250 42704653 42704671
    0x4020a0314120d0203040302060105010305090c09040203010209061603080f0f010510120f060f05030703020109030b070909140108100e0304060302090d020a06051207021c0c02030a15020a0e0105041409 88
    0x10b65039811400060340103124000c030b406400744e01c03841c0c6030902038205072059000e681494142420006c6403032000c600c40041c4501201c800c0180d48681c001300780280500c03540385030404000501e2541d61402c6e42c03540c2101c80d02c42e81e0348105541d0391038503034040c0381c40503100341b2030348460720b80144800d203020000343e60301d40d451b46881110414000c035400203454001c01d030072005580d9400c05215410640c00050301600b4150002e003015441c41e03000030448202031101414000e046404034103118420422040200400d803000d00c1008a110090000e451080c410840c00b481b0b041a00300c090303100d03409640c0c0451b0102c005141818075142c0160069441a0b4905a01000c00740b0780000507500d03035106a004d84655603e076600d500710407080401e41c180280a040540d481384e400c905a010603400034070301d0700c0b0051510090174901440441e25040c80071030001c00ba140907c04202a81d50b41d903020f030241505c1c60752401e0341400c40c0c600564641c03055000d12091030703085c450424501d043c4049581d403c02152 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 42707153 1250 42705903 42705913
    0x15090903020a1a1b120c0306010504030b0103391401020f030c0307050c01110a03120f091401050703140604050405030c100603020f04020a120e03040b0c07090501060804020a0314 78
    0x165991040c04203c02000300402c0190003e000c49880c400081c2c8550ba4403101400d0b1610b800d0305401c80061100a00001503090300000040169208070309440041d503211030302c99401e5842e0f20748503101c92610081a800b8000e00c4482010341034a141c3d0400859405d00500c0c0b900c0b40c140b500020140b0040c80b40706041d807080340000f104001e0300b04001c00b0841010006140c40d4900c03464864109480d2001e8181040171000703603980b5a0f10080b4109034080d84c5403d00380e8001350202d14810281c018960150724032031a0411010600014400c00111207c042c1d0080055070784220041e0100c0e013240c00704455142107200020301508296101c29000390080044a040003101c20a0f18030300a100d00b510003230182c0f201001c00450a040343e005103055030881e02503082184894004005854801051080350388a0000c148011018000c58024158400303030b81c1d540c2c80c0070a00d101e50f50303500c2d44508140035190100005005115030f44850190f580280203540d500c0c075540f0740d10b200c440c841545103800e0041d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 42708403 1250 42707153 42707173
    0x103140609250806030c03010905030f031003060204091a03060709060503100509042103020a0f031a0603010b0c0f0a0503160c05090a0c110606061e0d060e040507091509090302 77
    0x2c11800c0010003011652080e4451a02070245800c008018086501980c18140c0c0503000400c08000d6440e241da0207104240c996550390f0f080303240001141d0000d0180c1b40300040c08120b00c9a240c100da0000c05900c98019100710011007030555511048800200044040600f40b0000e4840d0000b1500a881213071080400b40e118000913800c12015103044400c810b803003010351055807080e03c80069000c07041c2001c505105030002c020708805902806401010b40c1d0b01c5d078040d45d05030b00c1001c94041c48005080c0c3c80d04d0350385502020b00f86070b00c007601c203000300d00c5080020604418000784c1d100d401c65100028604041a601c0721005421104004a904200d0720101141644801e4541d504c00d003907500e40072500350f0074240c02800e14800741c01c082945800881c200070003a1104012a1003114100070b200c00b01b90b00140720b54402d03010b241e821003021410000c0000b40c180500c2c400e94002d900482c19511090f544001c0381c022180d60761488102408100010807020803640d00c100031080c080d00607603510fa08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 42709653 1250 42708403 42708451
    0xa0c02090702010b0120070302010c0501090b0109150f0308070204110c0a0b0f060f03060105100e03190501060e01030f060203060f0402070b0103050705030304230102070312090e060103140609 84
    0x800312595001030b99145a0003642e90381c4091703014190707817541b5480059002c850200b55169140350102074140b02010114104006007542b00382030b2650420008082035031226800c401030807d100824144134041ca01c0810b0703a01071815014100d90f4440c140d185400c482c0c0d0b00340000f1305480c1705460108241404540e208000520000d40c0030b0740f0072410160385240161400c949941c016042c0c030301824008005000a40303000600d80c0c11348408803103184002c010f0031021110090340503100d03134241c0260001c02000c140e83d40c191500003403095000f4071005854400300030300010244005400c41c1114848031010071565070045070441405059008941c2518020030140d82c0020b004a80541d200c1d4010424803400b84801005400218081d614003032900c908246074545003501401070940c8181c607200e40c0da0080000d40b0003507600409041d0f1102c0c800d0f00103042601c00c3d100701441150b0340000100503600ca8844c0b289a41c2c200070243e0308540340c410600c012140000d00d00c0d0210302d14a0441500380d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 42710903 1250 42709653 42709669
    0xd17241002010906060e040b1902090301090506040b09152d01120c0b04081018051204061202040513050a0914030c07080f0304050907021203010f08010e0c060f0a0c02 73
    0x40910740002c60301d980c20f46040c00c01c550040c0d0103014030340b041d007007417000045030b4941d0550461a40b83e40045000490900b00d4001d2140e8242d540d07040d0b1801c3c1c804070420038003003400ea10460141c00c1105c1940e4920940f0b586800c01d40310402515540ca80001d418000c6110100d040b1905085a880d8000441900f114952000b03030840d200d1440d07a40307101c6040008003c00c0001500044a00390f040600e0514004d0780c954500119410395904c1d18250720b00c5440d07a4150b80e8141d60054115500300c01501d030345c2d24035503200e0b02807000041c842040e100d0a18085008039000c90f00d01501e031500c1c01100107028401170101405000c0b00743e858030054008500001c0c07038100500c0c01d00004d1030365030300031980d6545021300c00c0d80a42480e030841e20302c1c030000c1ca00c08001da03012608191100c0c0040e0b074900d1402c07070820a80046049060201100100301c51081042c900282c03079564000700301000345100c00d5550307044071840080e81304804105400005801d900035201011003405c002e21807030119030024104c030f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 42712153 1250 42710903 42710929
    0xc010609020903010f090302190203160608060a0614071713080f070509010506030c2503020c100c02030624030304080105061809120304030c020301020316020d1724 72
    0xc540c01090302035151034213105201584001620801c4002690f0b50701035203501400321803a24840410a0110540d10140101655071414078049500f01c1c0c1c540f0000b8019a01c16140540112420680499500e001d0701424420000c41e808560800700c10703030f40c0c4000044210b0000041c2003020b00c403200303410042090310800781c80f640010b044400c180664552902c10564001d62040041c0401002540c40720700c01c5a8002100702c12280c0c0d240396264440b03642d401c003c00d88030880720038029510709255010803d22500502180d9034034511214500846100c90715001c040c1d03158000c007000c9600c01c064943d008410741500b040e030071104e20724480060b0640e0000c4e4018038069445408000d290310f045c40510a62280030380c1d07441c84a0030705400301c60340c0360601c00719008000030000105080c140195210903210380d0040080d5a0391510003e207101c02044000001c0c05445480b115414580c059012150400c541c0703482c01e00965a481c881c0348403051100016190504005d411206d0b03901c03441681161 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 42713403 1250 42712153 42712169
    0x9110c0c0609040912091e1a09040b0d0c03020f0f01050d0c0905060a080f09030717130b07060213050102061302010e0f040905071806030b070f090b04121103030301140907050c0106 79
    0x3c1e05145c041030f14040c4441f6862800c4402840d1021300c181d941800d8445a42d040220300c050b02d07040303080041002060440310f255404844d403d400c604104080013070101780ca1003540d0228490901009001c03000848007815808214240500c1c924414280e21185e5101401d20780301052568660100300582c0c04150004001070740d600c1000760501d030404040350001d4061005600d07200c0300f52501c8220004203854418a0311001408015502028101e4005444005203642da1013400e03240c250002c1d0f01c400e070b20400407604036500240940c00412a180700c0d07446940c01e5a4a610389900442c3c80120714086503600900103122241c05403214842d140380e4604c10f000400c011810092110341243c2184840260a402d014040c130009000d480003d4110b0101d00b4001181000701c603080c1d03000302031034101f00541407001c0b03400944c224042d02e002c019940610501002c0100030350074141ca91200740102a440e48901c52900c0d00c9040c070300c01c41c0d035002c021b030301d07000c1e0a114a1824150946031150701043c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 42714653 1250 42713403 42713417
    0x309010903080f09070b0304060209060a030b031c05090411161209080a051507020a050f06060109050402030402030d0509030f010203010e07090501030c020606010806030717060109110c0c0609040912 87
    0x20070503802c821415004200c90b00b03031082925201c0c1c02c9981e10429809100031014021000c41c040140c40d4042d5000c048004043c1c589900c214030004004002e1188218400d2096009010f65507422425420086002d0354441c2e1a10403028103000c09030080e800d445940250400a00c60510000b000e10081c0911a0307618090858001000401002160704800401c1d000701c028040001c0300002d40e000d440c1e860300e24020311030b07540041c10b9003007600035000642980601103002c03005a2020840e90311610702603c46520042d122401d01003207010445009405030302421041d0307189805070000d8042984000d0440701d21544000c00c550990300203030b2080c02c0d041e41c600c041c0a1256049800c1c10b001c3d110070b02e020403018440220096481da005000e450600200c04013007407060b207081c401c0348041e00c04001c842c2100e05000c0545651158244100d0600d6494a41040000788041d011206d031701d420080180f001c036030300700100001135009018080d1700a964840c20030000e000d41e11901100c0b401c989800da = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 42715903 1250 42714653 42714671
    0x1110f010f061e06020319090302091303020f010e070504020c03040f0305010204060e0609090703110426160602060a02180405010311041a1008180616030c090b0702090604060b030901 80
    0x10780740035000000705107650700782a030621190750b000060307a21f0b801800844e01520846c2e00c00607151080c1c50340010f5003011000040182424a028409195034400c0d03084400d403510100c1041d089a000440c41501900410410001c52070035030080c00341001c1d00f806591a02d40d484049545091040d0b0007158265000b00342001007071303044204c02c4413014059440b5490890541c0005504481c0181340d08181642c030a54401910f20800560303000c0c00c40e0000c0c030700945c210000c4690b4501d058480380b400f940302d16001c604001c02410401801c8584503001030000b0b80780c039002d0b900650855203100401030340044c00501e041c0d91318080d5500850250380c02c101211802001d00054070703d18030501e02852030b010203a40c0143c44000304051161885c1c6051519916100c2160b206c4000c1c1c0703981d43e103840c41a04184011106000c804003030018040c0c40c01c008488a0b10f1041e03c00c121944503420300400e051210340701600701459010341c07104005000044850701c5131840c880c2d40d081130b06d480110b42c0d50342040c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 42717153 1250 42715903 42715919
    0x30c0703030f0306030b040f050a050f070305010608160605030c070c3203030307030c03090501050708011d09070b071a0c030a0605030a1e0201200607090b120601110f010f06 76
    0x3807a840e56141c0f0f400d004490850300c80c1c3d2403020300680001c0000d800e0b108800184502400b24024403644001520369015007455410b58070069800160340c1946801c0001520403c0020061a86101000c99030303800c0e480c0100544844c0c000500c440f13086081000120f0010301441c000001503c00300c4141d410079034515803413900c1c0d0320070325942c00d01c1c1c191940059461941d0001c1500d40c00041c900e00407808042d07407a0f080340588212035004082d90300348418031640c0b6411111160503600303803020380c541d4402e9110b240103400100ba6071843d002c0c0c200c0007080c402a0508001130071141c0c00761503820440f0180f00d9408030040411200c000898001005011f509261405440020607040303000303003640c01403600e52114201020991034240e04100010800b1a401003904a86104441c0c64140308a00c02c0244940c8070300c01265501c0000d0609040810724180100540d50061454402040e00e5515440151800d07050481544aa80b040c1074504176860340074010011004000d08002c40c1180c0b41c1448 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 42718403 1250 42717153 42717167
    0x180109060f060f09030b091005010803280503010e070908030a080108071e15180806161b0b04060f0f0609060602120f0d14091606020607050d1a03030c070303 69
    0x95010000b03402d6807101c10907807200c068400d0306e40101c0c45c4407084e1583c0c2101d5141440002d00d120120341024000102c0b40c90210103020020030076100451141007122480780c013100203504a8004c25000e1005000041d00c4842240c2d100c107150802e04002c60f140e0301e0081c955089400c0710400100582c0c0103010040301031002200500408103107050188440035640c04c0c00b401e5000b070070302180000308240f01c1305200751910039a10080c04444c02840d44c5a0041c10340326402100c030000c48a0307503040c8d03c1c03803242c1c8114020010440700e000300000c1c2001607a84c0d0030340940d002e441130307036501c2d207c0c1c180e00d01942e128480c044480e4400c040003e2154545150402900c0650b8050002c0d9000030718072902e000c1d4000e044031000e030f501900003a50342c25000c0113580100703601d42030000700c40510000c000c92444006803000841c3c0410100140980e551041240d8402007112004006441400600c0c1c451800c0d401603400d00b184a4480e00c031710a1844046451500003900d2705001d603110701c204100381600104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 42719653 1250 42718403 42718409
    0x504060506011d06041a0415020601080c19060e1201060609031a04080406080a0222060305060d03050a141e030403090f05060304020f040b030604030e1e09070806180109060f 76
    0x9200001443d02000145450055200c0c02c0043c0c100b00d41c0c5014031045207030490380034250f60003880c1001c111a03500295030300c0f824090498140714103200021149445400c050319030840e00140461941015800c03135208403203611036908641c803e0100c44810000303000740d50160201e607031414000340c914140340fa4100103019100e885950300f0410b10000c00c0c0444111070548069051900007500c4000c82d0f64024485c4d0711740010780100b6411288040d481400f040422503005a40611080d1689020420301c1c0c1820000200400c5041041081460042c45081c2101040b00307943d81c18201c0035540362892103601c0c4120031000c2d10000421003015041410030000e408a8040054420b0030314001c24113520010f000644100d13502809051980d079540c0003007954590107402e0f254182468034016180e07400f801a01c1e445008030300b00a120070760660b06010106400103141601540300e1401c29545d81c030700640050341000f05401c100e0748003024021007034000e1611440009540349400740311406101550 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 42720903 1250 42719653 42719687
    0x9051005090609010510140d0209010e190302090604060b1305010f23130b0a02060414010b0306010306020c2b08060a050f130209150909100e0c07050a06050406050601 73
    0x284842c58441d800c0c1c59054071401d071019410b41d0324040c000c0c0c2d481e000101c0d088002e29000120505003000c02e4024024440d800c0c1c8030240201919400c00c46a050028505032254000c95070030009482c10320111a0881030282000030515241c880c020483e80c0100c0e54056020207200040106590013105402140034a2a051070905045054400012480c604640c100c07480490680800000d180300340d801044072869242d80d411003000041c3d202c040c111025100328000406c0380c0c0000606014030504808010060802da0382140d540c04000c0d00104580211449001d0203603c007001400701281c00e180800c0400d002541d41c1c030307030000e1540e08010301490103201c0d8988204034507144c1040b10140d40750101c4401c040420000f128000030300440342d03069403282e107113140c004900603500d006015071542074900901aa544c1c280e1000038040074403509841d02e102e240000c1d032b80600e94000d058114400c3d010358045040507103460081c0c510aa81c1940c096548100340017041d078200702c5050041c1d080d1b0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 42722153 1250 42720903 42720919
    0x110c060118020405090a050405160303170a0501080312090705180f010807030b0f1509070c0203070b040605031305030c120c010e07030201050d0e0106080609010501031403030103021311120109051005 87
    0x81302081c40c030640a44507140d0340381c0754404102084014807a038081803c100c03802c410850340e45e040007025902c407000003d030b1a40c0c00401051410001e4001c640c1a14401c900440c0341103590f414004a600c4010b12924a03030061504c0800c0980e01d030710900e42c107082c0c20741d224010350a00748651000454182e100d0340703050740500030401c0000d204240c01743c3c1c00010102041d04030342d2044c6c000ac01c040e15000c4500d80c4103506d14200041e161704007102d50321030342c0250112046540c40c0c2d0115001c0344598020440850414000030f14004000c11400b10300320300c40e0098034207102d45018600d141c041088110000d5000104000d03099440034801c0e03460000301c4c0d10040c280c1e28516000a401d6202d00c000c0420318684401e10b80b0542c1c134094105070000d00c40c0000b225800d152041186000308000c4c002121603250345030003154030000010a4078141c90300144042c0b4500d212446060080000302e0542e0740c0b982c0c050000b0920f40b1a00304e5120b0003807005100100b0340e0b2415056400c2d0042594006620070842 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 42723403 1250 42722153 42722159
    0xf080a0302070603020306040b0a08030408010e010504020f0607031103042402010207260c060405030705010c0c110402030a060b0a020109020109090207030c080c0f0a0c061e02030a030b0103110c0601180204 90
    0x2000661400700c0f0380300d00f001680c0380c4411000c14058201c2c0110190001e440890001d880d1a00000038411901900000c208240c0c0000f6a542070390300658000e5440b01c0104000841d5141c12402005070901c0b038103141c403a094407015601d0458006601a41c10a24007407035640079200c0244426900c071403a84001c501d44542c2d0742d00c1100c10702c01041c40e01600c02ca10514035a6401d032220450f29401d0180341269403274642858003035500e0340030000485081d402c0c20090510540030744e152901c060741c4240008000e00c060000d01c002904014840717548940c0700c0300300140c420ba101004029000c1558004140350800d03000142c1090300c42e03440300c0603c910401c502004240d0020030b500c1400d40c098011030752001e10148061a2640700043e0703109501a8000d2801000b00d1049420304070b500310b03100e03402d0015110f080584c10210207075a55000d41c1080001d04006842a4400782c8082d0050400089503040e80403182c4c09904500d01100043d4070034801440400e20b0711100703401070b09003144290b103450700b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 42724653 1250 42723403 42723407
    0x14040b1506040602031801030b1819060506040303030f0207230708120906070204020c01060b040f0e0105100e010c0c060f110a020604030f1109040609140a02010e10050909100f080a03 80
    0x49032500780318000740286c5120445a01c81e42040f228075400074081607142c03442c070140507030f002010b86904003a0030100503040c1040045024102c111007006280e54149451502c055015041c148040440c40f13908011160001e88455902c02c40042c203401c3d280003240fa2100030302c4c42c2c680b042e08158140d6110040b2000c03403500034011030300450307410380700d4a889201610110b4040c3c0a00d103a461036079400c1030740102d1100c00703041c044c00440301c81c4812903181036a074845804d80300800303018840e00300c0310b0950866080d0740100b821401171481850700350076101c03036a1a01c140e1600b440c5c00410021340013191081203a036000c50866900e500500192215080d21750001e4031a20a030301c001408a451562a00140080d5520b4140c800301c000c1c01064261409141800041c5240002215050400a18031010480004403000d40030b5068465a01e0901900f041004255421884408001081125055030340360003203c58000c800c190041e202d00743c2015045c07810f01c07210b60041c4689074050b00041c1e001c29 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 42725903 1250 42724653 42724657
    0x1606230a0302030115020a0b1815010b070c06140313050a020405071206170703030c1a19050c13270f0903020d0c0302030d1505060c0d02010c050f0702040b0414040b150604060203 78
    0x11901c1082c127031540c001d507030030381d401d020510711108020030022000249952407a0700500c2ca143c40b8540900c0b41d5a22403c059542c11003454100d02007170014000260351005034408950014042c0f0220713214840d4039800141036510403910040090318140c40511800c009004110181c0601944920325a000ca4905d9590710098400038081080240520703040c42500c024007104c070120790003445102d2410154401607003000b8403c01c2212403405000440d18040001500c100466100700c03019114a400c02c50304041d858000c1d0303074502c01c028000c2000010581c2c4a820a11110030a0214580205003000ba0070302110160300e5041c84660414400002d602004640080200b44000240c1001503e21202c03402e02640000d81c014000080e144c64684000401c0819044142d00074070207500c522804a490340918604404961401d001410051819400128007940043c00001e0200072010204003000d10a83d002d4130f08400c090148006041920440d0380c0c0c19406441880c80c041c9004070081da68 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 42727153 1250 42725903 42725911
    0x6050118050607020609010905030a0b1605090f040c120c1d04021606021e04030b04050c0a14040506032b02100504150e0c06040603060509091606230a0302030115020a0b 74
    0x9010300086c00c0c411a030056150401824025044032a80d028501d00300200c4641660312840707402286c804402100e218800b1212501c0d00079141203048138900c0144801b50400503e020117200b02e01410740a01c6480e4424003031303642019030754141c00381e0040f0070ba48110b20090040900a5004001004a000303160741080301c07050707111000594602c4584034803060800d40054a101b2001d0004000040c0588a040c0500403800341d81a50006000303d41003081e03109a920900101160014150000317161940c00541d11003806002e0311505480300310143c0b0301848070380d00c4201016020482c6a00c07150704121541d2502000d00040000d03041549a1144500980d14100300043e1244140c001e89441442050303010301c03000c1c03c2191629292039014014240c14011a40100b04a80020307160600c00140c03000402c598480c495405c0d402c0400445032100758084a0342c581e240182420340c020840402001c84007200c0d5401626541807681640241d804000c1510841d44417140190204d090b00e4105904 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 42728403 1250 42727153 42727159
    0x20d0e04200c011107150c020601080601090f0e0d0f0210050112110301020d09060b100804080307050310081b01030501090b030706030209010201180501090c0b1305041503060f0605011805060702 85
    0x2c03801000c4085000d002d100030a02854038001c5090740030041d0841a05080d401c502c81c0922403200310b81400c90350b030b000901c60124290b100c1d01c01000395050350303030183d03407003030501030000c50350720908407070249819030310142e400c001000800d10303c0300a5814031492001c8401d124003445207500d0816583c000303110141010b0030240c1c40c0c002540c2c1303035a400d50454480324503618090001a000307092100081051407515030052101c084000241d1748190445446241c1c1703c0e10301411616203c0007224541c1005000350b040a071020008518107000300000a807180412000ba074030102810001400d5a206030f0180004c00c1c00c1c40e00d00c0c0b010340d50114680095440d50724005854900700c40040780904000a20f400f065103501104c2424410103400c0118101d001d1990150324076510f800782c41662141a81505144020040070f20051610750000304181d060369041001e25a1241c13550401c079580c008510b003140e43d407108200b00d90350f082400080c0f90000403000c01c5001d0f2070000030070214407916100a01c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 42729653 1250 42728403 42728407
    0x301090c35030301080d1b15180605060316080a120905060d061802030103031e030227040c0c021008090a1a15010f020a0813030605040c060e09011a07150c020d0e0420 73
    0x507110544c0d0040c00c0304640503c4549c04a52103041c090014002511554001d025450030744807049090ba40c00707402c64800100401030360080792a910320511195000f1000c00c0354040c40040c040c2c0d1510081e0402d0401c88100203004ca02d0001d00350020703503111320603a6100380103000400209400c440181201c03844c4503900004c8490303601d0110002e200d0a03c910101c804000200700c11001c402d004c03004c0341c0c441568204841400600250740b04030103910000c1d0f20280c100740c2044018450b8241c6034102c62048112030301640560344602481844880040c8031808100401c520010781c0d143d081c80c00f60080c213043e40c2065410800a445441000e009444401d0009a043e0488142c1060720300440d00005c0800207424203140500100c10984210701c006040d1070044400c5140c440c2c40700f07040b10040d070b00301c020030315444d43d17041199000900d066990103032201a0b464500000c0c0031b004a400d0ba25030241001c2c0482c1c0034060240030540c0c602e98041c40c40e01d2001c00c4c03040703034800a18281e0740c12070382616 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 42730903 1250 42729653 42729683
    0xb1305040501270c081204050d03050c0a030e010e0109050907030b0d021c170f03040f02010e0a030b01060906030207080405040509070f0311040b0301090c35030301080d1b 75
    0x902606582c030f10b94003c400d4280c014040340c002c440750304601c948904d0314503600c1c170759031004903903610070f5251111080c130000c00c03042025241610302406094400e05000303040c00960200706007010541c103420760120710808580202c9603444032044008084c2420b080104908041c01f150003140010090028540e560704903a950341d861440c034a0455500401c1040c0428988440d0207034000035801c222008d0428502042144207074800351501504c507103000780d0844e503840d240c0d038540380b020000a030f06001c802d600f010201d0300c50358403140c0a54002c8812100729490140010203086495005508161040c031484002459007000c45084070800c03100402c2c2c40d00da42e071420b81040348d994000090505103240001c100209114440094142190200501c001160070f240c00d030b42c0b84040c0249480b411601c11300dd0002c022240e41c00b40000c0800d0f000071100c0c0e8070004511580f0304024189035501c0407004120703242007003110b5a215280e6181c0101d00d110303524003040d40106006001400d610040c4801 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 42732153 1250 42730903 42730913
    0x40317090a0c0b1306080103030f08131509020a0902070f060b031c020106061b020306040f060e030a0c02030606180c030a0f020f0705010608010c0f031d2406040b130504 74
    0x240001a402c55032041e015940d8441c1401160700081c2c130b5840142c0c04c1c1c84002009401401994100c80e095150314045940110045854600c000c1817120003a28403038415020942110703651020b800018400146a20b841c0104103c030425948001c1d45180100409400038806e11400c0d00080d905c1000402e070100803a000a040c484c070140c0740c0380d003200500b203501c00c4c10380e05400070b10450360f191b210b4800080a0204120412410282c00394140c0d100601040000c0d00c0d207200044494000d900c00100c64050845407800c641c8001c01c45000101a25150030030f40c43d0900c0300d43d81000b0116107007a1a403040b002c2c26101207600401940c80c10308040005108a2035070b810608501c949034208650b102036000035115650070020701a03600703620b0b0000115483c030051280b00706800850712540040c03174001d4030440250081d1416012400e085065642080004000c25600103250540d01450304050f001c2880c001800205100d00c47e6051910a010f240c58010004070021800113010405503624102 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 42733403 1250 42732153 42732163
    0x2104061b02040221040b01050a05010f050a11010c090612050103052e090b010e0601090602070512070312020601061806050a0e010c0210050c070e0606030c0703090f0b0702040e0604031709 82
    0x7030103110b13414104841681010f103562151003030b4400c04405a950342c8070014030049011a0107070602103160003440e64003081c000c0001d0505d40c00b413880d00f07001008a031101642903813402d40c001400f00f40110014040c2c0c503049421503441035007a4108019a45c95500c54550320490141c1c0d00c080081420f20708825103000c052170601c0540703403580908c41e6030311610b88455075100034411011100c007004c010420541c03194031107004454169004020203130401040007080c06e0244000740481c131901700000006a00300100c5040350081d90090038456140440140007102c0810f07100401c00c0644006010458100040d14085031082c40c00d40101605c5400503070340c00001d504042c1d40640e40400078030700300e0f038442c00034403689161100362040c2e9690780380100c140100a0312480d50014040c8001020f2007003460140608034040d01d00142041e54035107441e02c040e05140c00c411100d030b400040900550505015801d10055450011705503490306c3c0c9c40041483d03a2074101041d1800010000c070f0541681040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 42734653 1250 42733403 42733417
    0x30c050a200f0102030901080402040b0f150c010e0307050304090b012105010911040e0c0304050a080307020c01090509040b04170c010608010509010b01020105070503070804150504052104061b020402 87
    0x5030809a0a01c003003000d50310400c0741d8a114031180071441c005544040141c2c0c80d0b15806850300c003101c1d180c0d030703082002400420103400e8202102030002106682c43c0411124888010003406540d6006480001e080d10b02140324100b06900401034880098030010840d02100c00b0b80a00050000a1100481f0760103554403262a400040000d07000c441d40741c6600950403142a400100811080001c0e400303c41e00580c0700d54009900802d0000c3d0401e03c0c83d400442d40700c4d1284054400480c42c580c0d03004200d80040d614040164032624003a0400e5030000100b07005004103c034030518915080d5160604c81e00004c1005000f114a400c10740c030400c200f81c040e20320301c035000c8000344285925000c03907900900040714030441960a05440390720300e5006100c0c0f180501e4041d51102c0c610b54078000151000203010704105c9140c0c180441c01c09030980301f440f03030602448c412000760402884440a044405004403041c0c07400980411080103001d400c400310207240d14645e00e0b1003030002e004e400020000e002e812 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 42735903 1250 42734653 42734663
    0x20601090507030f0908130e06151e03091b0603012103090b0c0102090a150915120c210501050609100306030b040b0412090509070503060f0a1509051c030c050a 70
    0x3080da104100c18640a0326901c40f41c40341d41d41905540c0c0c204000703004c3c0156009d0b90002c01101021841c616000c0007040d5190880c0d80c524451030707031015116003d078412242400942c1003107101c074011a40c075017440300c1c0b51142215100c6c115414118110f01e0036a02c056003800c6848000c0d51081050b010310020801004c45400321a124110309420a020750b1003494640d109890050006c1509a14507d0011940d0441d03034504a00c14108a094940398002015010a108200036240c14842c102e01921a641000307644507080e02c01f440c1c881e031481800f88001010076a06110040c4079a455a0f010740700308480883d2191203030f1400312800d80050809800c09007404031b9010401c0148000019014000c91080800d00401541c02d0800c49501001d030003640c0c1d2081c03926000c6000240b1840c0510380041008100800c8840b0304c02c00207100c1c2c841c1d0f90114000013461001c4d10401904511110014001914664917001c0b40d00010b0070195000c440080501c0b0307003450b0000c02d000080060255441d401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 42737153 1250 42735903 42735911
    0xc030105090c01030e011a090c0f03040303020703110c0306150402040801020309010207020f0316030303020912010203090a050d0f0206130c0807030809040c0905010804020f010e030307080904110901020601090507030f 95
    0x11455100c080b8401442d0220b03003414940c1d641d4810510514800c10484201c0181c9584000200618000c0c00303001c070780400405010b00c0d030842c2070790001540143d01c6520016514400c91501030100d91518030044d10603004142d00441c81d4901081203035100718002e60326114240030b00000350081c0620341003440c1941c4040204243c03808154000c0c0001d6000711100301406510b2030030076a07283c00c10360040c140c80e150b54a007000082d02070703006005404001400c000344440a01c019600f242c104032441d01c59640303c107004505110080c840e01c9207541c0140b412805d078120b2540e005e582d8640c00f42440740b8021107940b090342400121a1000054500d010986003030303d40e01e00b0a07082c10340000c1c4a46102d00d140c20305004540d40503d601c0c0c811100c068480700081d030b40d15004c022250801080c1d081c1848000181038410b560280002c00b2a94458200592250f10360802c1c40111100c2c3e01030444000010454002183c0c0c0000d5080d04413031500d14082050f0360751000c114003800022980c10205410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 42738403 1250 42737153 42737161
    0x1203080a020c0a03021e01020307050a08090a0209041118161d0a0b07030306090218060d0f050c070b01050307030203060c0304110d0c0315060605090d06021303050312070315090b01020c030105 84
    0x2003c41d10000b20030300012180351400448806d18200d1209444020200c0c2c4100410384d005400707001040c0c0c0c000782c10740582b024800c25401280b507407041254200d940c84988002c12116250100384098201402d4a0103038041c980401a0304c4080a64180c900a20000201000895610050210b0000409072140f001f00d540c0c1e0f490125030360001481200464241500461541003134400d03a21151000200403c42007108000e01090303612882c8000180e68a4802032440a07156028240c043c11154030785942c0c845450900d40821001a00001d1181e01300610070000359400280e80d58002072640720700c554035152803402c00710101c8152030f50742e0801404074000007840589001e00085902030420481034823781840702013119120700901001c1801440072108604000c1d01c1003c07020322030b04006140080b1300c000d203001c4144a0b1710854650388002003684d0241281090726812100d2400d00b40800000c01c030110404458034003d5581d16580c80c0c802c010540c2c42080004401d80d0058001c11403414 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 42739653 1250 42738403 42738407
    0x100e0a081e10090302060c091807020d09050102010209030c06031f060f1b02031e0f01090f030f1409040207081903090b0c0708041a09060d06030c0e011203080a020c0a03 74
    0x5a07420781020700d00490542651403003850141e0004070ba41580034100503500c0c405007814680004592075001581400005035400c0360303540c000c0c0152003d400034000894245030003000880940c000a04690050010114503100060003c0e0426000c071407168a95844995980304041c000d805c40031410b01908000030500e0b008080302ca100c504680d81c5000c2c07403408006200da5a5100c3c02c0007501075204200480aa500180545802103111400e440c601d885840849095030355030b1710242e03440c0b008003082008140c1c11080034030301881c0fa800c2c9245c0135603220a90080c18052459442d0095070001604401c2103910003c44d960b003032900b110004056100503009008160b00001203035409000b6012800e0000540280c41d031440c0d108d54000e25142c100703900c000b030030207044034519128001440400c03c2541c810018154003c03c00600254003861400c00e20840301d0141d10000c2003e4001e001445060700303248034043c5031a01802c20807042d84984903035a000384203020342c0c040103000740705c410b2080517 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 42740903 1250 42739653 42739693
    0x30f03040605010e09030d05090c040606020c040c02070b030a1503020603190b0411090105090307030b071d0a0f0b07020a03081803010f0218090c040504050414010507020c100e0a08 79
    0x1030065070300304426a00c440c09078141c100d0a03580084145d205000c0101c3e145d400390403070365000f401d4030103544400301c0d084003081c2900c4440c0c000710056040a0b50300201c5061520510003000050f00c0140200c1c3c0c502a001e00b954840500380642c855180d00a41c0c1004211403816001142d001d89110fa072480c1100c00f00043c0e40e60300a2012856091061050380c034034290041c8060046030148203480c182410005582030b5104a035901e0300341c010468000040f03804070071118401c4950b521540e070400f050400b40c40c80074601c40c240382e104622100c02404620f1540c080e050690360070212095a440c07040c000209554080d81c0010415000045d800400c008055410408004154020f00c40465000c2921040e8000c0c8119032a012102090061303441c40c0c1201e40a40020301c80d40e1443c40c240e01c0d5008942581c400322810390f004404503a030701c15425024842e1036440000383c800b4180100401000520711b4200180c81b10400040c052000701d2039460405290051043c002103440362903c000c5070910803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 42742153 1250 42740903 42740911
    0x70c030c06020f1315080402030705130e03160201022e0906140a0b03010b01020109080d05071202130311010503040f030e031204030609020306061f0305070c020306040b010305060901020a09050d06090203030f03 92
    0xc0d49000385c240001c0b8090802c0c5801680d0007400340c1a55800c0604ac0000c0c50b844000505810b901c3c0c071003070b0600c41002e0000b000e03a8549504894014105400068508024000350420010304101c8007481080740a216904000b040c110204801d0f881d414040041c1c01c401000400d00340c04242880b02a4650350300c5006100d00540092104c1e001020069003280c20b582e102074500f2408010022081d80240c0c41160700001d1401c00b031031444880303200e040c01c1743c00088200340e006e00b00280c14424001140d181e501d030840c007481c5c547e1031841e02d0380c2c451000b14090040141404501141220166800e01c490078444840e1880302d5103442c0d0341d0500d000602607404c000d900a001e40c0340401c2c1c0a0500403060000c0d51030b0259684040600800c0032001008001c240d10304000ca40004900180d5080c444180110700440c17240799030307505505240d0301f40300c030103803020352541e104106651146030052280d004507802124003070812800b41c18190044d103000c1000a505001c001041c41482d1140400f071401 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 42743403 1250 42742153 42742169
    0x403081605091f0206090309010228170706110705030d05061203130f0902040506040e070903060e0a02031216020103050408040f08030a1b0809060d060801061d0a05070c030c06020f13 80
    0x5651a00900e8944072300c81d4038115801600042c0c1c009043d090103280d01c401482010206541d8030311140c03514044188a200b4a00b0038500008a4000340f000d24020707034080d910220641450940c0c1e0348e07501581e9104406900e0003094603100007451660f82d50f841c00080c0902c0001340d039a20080c3c480398043c844c0060040c691030403003009020135030a105100365010784001811071807400303040030b64281180c00010411020000c8820012001070b9450142018900c07841004000c5414a80f04050a10001c1c040342000703204184050b400300420351042030091502070078002a1034645040019891140760031001c09131128800000700140008000d20080d1341696800c3c03040500c00c41c41c10204103111401501040041c0003030f20030b61914000402c02c12082c3c0328002811541c2c1c00069080d5400c40d0304c10f002d07007003400144410031202e00000651042a072801041903140400f409400301544200150420400500110420a440d03045a400040303c50751151164480d055912003d00785004200d5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 42744653 1250 42743403 42743413
    0x10602030d0f1104060c0c1220040903090b070c0812031602030403020a09020d021e03060f040213060e1201020d0506011205040c1518030b011d0403081605091f02 71
    0x10035510503c50320070f046808045042c502841c000c400c0b40c10b070b20b40010568091391444000140f1000c0750309165069071107140481007081d0513480000344040070406040c0641d00702592040040c0d840707140181a6070070a81826225069810203041018054100030080d2094014500364594280003652145085c0d26400300c0000a40d0300403616030243d80320080d080042941c06002251580d0007429140c04440001414000d4001c001b01040009002c3c0702d00c511000414041ca908000c2c00c01e003400341c020380c1c0651130840803030f1500d1884281d502c00d01e41008541c2040007202c0e82d4017019a041c00c441d11000355154410304130030100526090300d2050100f050410312212082d503a004075845141c020010001240c0743c51600f50000f00070031404020018440080042d805c6102c850001031401003003070900542c1404e41e51802c0d19810854203520034500c50401000a44c843c55441c4d11002500000b0381c4a910000c003501c0c2400382000c0702c0d900070000341c016000741c0e04220744902c0414456007154 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 42745903 1250 42744653 42744671
    0x31106070f030c0212031b0c0d05120c010207020d060606030b120a26070c0f060201020f0d020d020706140702010507080709060507020310020c07080c03030306010e1215010602030d 79
    0x116051244100c0201103290301038646011a020b11580f280050010741201d244c0109446998296441451240900050110f0035411200c04111a0041d028107582c0d0b1030300c2241d944c582540e1a05a40c2e5000010480001e003803c10b40c10a4040d03651055014000e014015034601d07104000d0003c0e0301400c2e000928040f50b9881d540b42203810f0307144802c5014040d00305070415480c2c460f0880c201e009050480b005c603d8041081c982810000c0c01c00c14041c003424002c90b41000803500c580b9a0a9120504582c0140030110f01c2801c958229503440007041001070b91502c08407aa24003a0040b1080a802e080c41e0038190b10a0841d4104403610420300c1c0c1d4006c001e50355502d4001c1c1c1d002c4c0e5098818000144e01484148403c42c0990004c241d19400213045410511140029009a0b48007520350b00307940e00400741c100301401041110611014084015504600d0030100017800707000ca05042d00d1040c40b040c010340d00030080600159030180c501548500e002e40e100c1c14041d58a902041039120014a019416 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 42747153 1250 42745903 42745909
    0x30f070e0a090804030b040204090206210c04030201080711070306060308030a0b091005060912031305190308030c0d090b100611060108030927040b04060f02030609011514030c040311 80
    0x300006901201031418503046444684007031b000104100d800650304c1c400003016079160750140c1500d14842d895a204600c45180000c4421005403002440320014401400140e070003141c4203034440c00702c0c94602c0f41d070a40301c58060700d4108198001f4181c0341c5041000b0043c070100400440c41200c03044014051004040c0070300c44040c00071203000090f198140d00500c10b6240150052110450043c114015298042000d41c21680f00300304481805409120810490602100340c07000d5610600420384070614584601460748401407504002d14030000341d40440c100154445803005810802c001100d29240034450581400c41c01100d0100d20205101c940714807000070040d050b6221107000d1400c066906003481851a18455192a060ba20402c444c02d0311801345621071040d40a001281510304050600070700300ca181d00710441c800e0707004008100142d11008490350440c0d032446490220482481001c42e1105100320140940315000014007010440280151080c0c07401004a01c5104d0114010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 42748403 1250 42747153 42747161
    0x14060a020d12111201030b01050603071205040c0801020a110106050307031a0403052106100c0f0f0203032104050c0d03020a080903150106051b01051b0d0b030f070e0a 73
    0x20180140e02034515201c1e041e200e00e0032500b182004082c00b00303031409141c00500e000c0d0494101400c40f460210010403e000b41819aa030040c4802e4441615606119030000e0500d036000102141d0b40703440700042800c200e0404070110003000148002c42d00c49220350001000955500240700b071544c2082804a602d103400720302241201d5000034031414500790745003071052007030000b40180c09004040c4005002d104c1c550000407418848254610350038070b8030900b0801c070304071034000c05000c1242e094003000c0068170280c982007c0c2c5400c0100c074820415140f002230319521035010100c02d10b48000c0784003c444864006543c0c0554030a0303040d10028100d03042840a040d1000001078010703440116014081883d403c02051a410058181c0d816901c540d8000e1012200a901100000e24006079041e010b10100710283c5240c0d00703010007400b503400c21840c103210a20120180c0c10341468000f480070f803800080d43c08840401d501a00b80c540c0420040317042c03a101c1e0b410384100c12602c000d041c00256280d0582c85 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 42749653 1250 42748403 42748417
    0x3050f06130b06070204020a020a050106061b0209130615050f0306160f050d0c12050a0501060f110c0a030506010f06020d0519020a020306040b06030f010615050306150309071406 78
    0x450480a0200421008050480b2404607900440204104400b6031181e000502403003e9580007407a08500c1d529081d821500540d01c88420015401d140c800002c00f400c114188042d01100c214134241c440c140c0c0000850b00802001b81445d15288007030f8480f01c51120000f08880e400c8412980668020081c0340d201c200450314601081d4990350700040840c041c59010041e951240380c524104404040c81000f107500082124010442004801150403031a02505507c6481d400c0c05000c0d42d407400d100940581441c0c800c4500344001d0701c0c881040000100404000017400400c40c03c07000d40d6038209107440e00300a020b010103d41503024086000790000a070707850b80e04626902c203403070701c1444a2a58603110b0003003a40340441c00b40d00207480c00350f50204100740c01503015016202d032508009080603e40011650002e5090f41051030810030041b0100e82c0c400342001c10700f001c40d41d903035400b00011424210500c4c86041a80d01106012110034005000819951030200d0310758070000c40c00c10000130f405850303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 42750903 1250 42749653 42749659
    0x5010e0c0d020a050d030504030b04050309040c030b220b09010311090c030f0708040c150f020705010c0c121a0c0703120504050309100201060b040b0c1204030f0609080409020f070303050f06 83
    0x442c10881811701c1903000e61301902070310b0140c2c10240c07641c0d1000410002503400766855400400c03140b60314501441030500c07900e00c60404104080700710000c140201c2c17040400022260408180410651b007030307040a8a0718000803e07140003580c40c0d180c405480d1190240d424004c10700d1400040403034941208590042c650011160081e9441c29002c807440307000100b0844040c000d8400000b0690100181e180003240940c8640c2070500c060040281341040c0780e8403007410000140c00319000f1669a00103131003540c565807006041b45000703042030221540b01c810041c4c5e100080004002d820240040a407a510f03204c0d503121b83c2507200c060b040c0c0b8107030b400941e0701034103640042141c020145042003903440c1c1401a07000206080303945005a8045030031950080c201580000303460b10520364280070402c40c020601a14904150450702c450001007900c10300184115500c05080c82444090003c0d00c0003072000343e8040d9a00c2090a95440c00e0b03410030401140882e04050100c2c00c050b482c0554684034020103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 42752153 1250 42750903 42750919
    0x6120b01261c020118062406090b03040816080307080907031e021f050a0311040608060118120c15080c0906090a0314010204030506070509030304030201030507120905010e0c0d02 78
    0x200c000b40341c02859201c42002550350b903480040c1e2550b002505229110302441000076880954556407040c800f035a00386001620b1280006e00c146a08120b10f02e041d5241042d010f500c2c2d0303070ba81c0360440b05845000200b04030502c0032040081008502c400542c41422140c0c1c0d0b010160300d4040880c1d07034a100c01d01004210f44803c0840d1303502a80d242901074a4103000401003915103241c0002500c400000019130b00024100044c41c4510340d03090f015003100e849000f40e15500e443e00d480f1000f8030102c4054521410014101d8540c0c2031044580a450054035209461503203545107481c002c202c0c1011441141a405c0d100203445c01043d00440040303102c0d5403022080e0703140400d01c2c8204202c0358804c449503940710011800c0440400c0c1c40c4056600d640c845d903000103075600e0a5061252520000800e403608206007088100d00680f40030007520212542800e000c00c09454441c130030b0318082d00500000400320700e005a10b0080c4441500064140001c107825a04200089000c1c003550704400e0002035008140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 42753403 1250 42752153 42752173
    0x90603080304110f04090501050a1503170f1c050a0b0d05060a0b1305041a1f05090a0e01050403030b040e030a050708031b1902060606030402031507020106120b0126 72
    0x8800340007401d4201c01882d040f244d04418000400704d51180704241d905030f541d0300030000980983d110308008000d01c0c0702e60301659882c40d5034000340d80310b000c134214018503c0454000c00302d01440090307481d40240a20460300700307a811500e4100078007003150304200c01820324103800024140708072002c41d641d03008800f41455a4407401d440c40039001c00c004d440c1e00030188800a034090101482042d00a91240e004109003040241448040e03010280001d00c500540340070b00d0162894004d0801e044500030b855000a43d55038002d0007004014403403481c0119400c04041104059040c2e2181e14640d030100c400b00480490000b0340e56403406603400803c040380c01080a10080380d9801301440e841081841d20012140e80310800e98216082a1140c440f0441c030f0a03104240250140100d40c6c0c030600035581c0a04500c2c21b500000d036603e583d00e11840e0f0002c4400041081f5a100b9003100e006000307142d18810b000c002c2c0786481d48409409205600032494004840c1011000a040400081000d81d00411248034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 42754653 1250 42753403 42753413
    0xc2b0c021911190b04060305011805060303070303090206070618050607111906090204090305040e011a0702120c0604060c05070b03250306091a01020d020d0f0c03180308090307090603080304 83
    0x803c1030240b8048542440000303403030f202035000b000600515a0f0200d843e500d0110141340d500007030030b1480d0315036017031034100301c0281c41c004142c54580b90503213000b042024250000c20712a1040f40c00c0540141d06000d050880394094000c1550303a50710039002c984c070603a00c1c6078044404240044c8034800c503810880ca403129401145000242a41c09048000344441e0154002011282e031507900300c01080c0041b8040045800c03085403580100180c07802c00b054408100c1c8504018402d285001744a11501c030301d101582c407000c0241d040d841d0750243c0990b683c3c503210342000e0725440680d43c00719028401d08002040e0f800c0e500e0103690184145141440505c0f0203079000f41913440c5a041040105940c403200054040e51a01407003009015101312560450342c034500080c14140c04180c96404d5510500c042e00078036038085025241501d00b854400713016031152400301c903002d40b03204400704540c42041001c0144800d000c0100b402e010200c044400c126550b10312141a51000c0c400504081c40078400940495 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 42755903 1250 42754653 42754669
    0x3030a08190506031c05040801020a0903030f0509060403240c0305091902030601030212030f030406021c18110604080f0d030c0206090a06050709030f0c06020d050906030c2b0c021911 80
    0x381791420482d040a86071100c682c02c82e0044007c02c000620100420002c0c950490008030300306210b03242c0781d440d05580801041081c8900e200042464904400c82c10410421100e001d02c00c075800b420510041c262207200802030801554501814068420080600710400201c4881c2c980d000c3c1c040d0021344c1c0b030b6408110b05048804011101c42c08100524010114144000c0d4404c500c00c000042e140c14405140403050002c4030400c0c0b16051804841e0120364034086800024142d025407401c0e080c50f540d034049800d0b406140d20100f04d601c100d40020307030140e0012802a0594500d55000c018a160b000401c03070b03840c5015100707180d068103d07558460124006821407580502903041285000380e40e0381d07503685000500c220544000303500d00401d001d9281d0600044c105540186010760501c942000090701c0b0b407002031316a801c000d400007402100341c00c40c124449000c0d10069508030407824601001c5c00504441103503200180100302d01181d0b541034410202d040a90411041040c10710300f041801069 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 42757153 1250 42755903 42755953
    0xe070f0e0a090b0f040515090307020d030504050409080304060515011e020a0b010602010c11030405030c040b03010b1c03171905090a05070602072c1b04030203030a0819050603 77
    0x141d078445041601041d0001d505500404a25014407802d01d0103081490500c0700d001882001070800c1007e1125045000003038980580c1c0448010902c2d200601d01503032184030340c0d4401904a13003071000000600051002031481a8052803050200e5501c225214080c0c0200346081d070301095040b10b2005540c8a090318400d001c190900454580301100d40780c40003950b000f41d00900041c4c0d100c03150094070326800f95030000c10f8003406000394101400d240000e919903600701c814901541da5400c13603403480c1c0c1d025000904261005400e01c500703520042c407c0f210381514542d090740480c500115084c45e078400c2c01081c0d031161410100f540e004041104c41800034240c09080c0e6090792003907000c6840440c00500000d00101402c2d002480614500b8407440e110038600400061b201030f031b00190907200f10314240c1040d44419094441e03119091003403c0d880203809070750800380d01803101151001031182c0040c1114001d000040364413034120a07219114080ea80216806501600160125231515140000a96607 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 42758403 1250 42757153 42757171
    0x24050a08040804180b01030b031b01120f0207030207051e010c02150702100201020d0b01110a0816080a031532010c0b15120307080301050f040f0207150e070f0e 70
    0x151a55540440b2038825551404d80c9510b5902e50317201100390b82510507018105002d601600c148985e103076100220200d14483c4c0c6050003c4014142e41058007603001b00740104034400c04646031800e505000756541030602445000b42400786080800c4640b0003103490590310142d4442604400590a0010308030307140e20f01e144003140c180420801607407507181e42060044240c0c00180c54844064016050310070303010289041c8021000d007141d83c1c0002149550a00c0e4100c00d2043d960802003003031072404500141d000d0920b00e008101c40401c3c1d07034142c00506280c00384608080040e51100481c008e017080340129119220101624208d4243c140702510880c1981418501103451031074889c0c1040180840b070401c00c245004c41d0400280c0340101011032811031100065040a009590341500b5220600480303100e103600d0710324401c1513a41d03504a00344245200d2025502e524040c502020504010698a40034508200d02d40828103030008140c1d0803118003038440e1000710701d4074203002c802480190550744 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 42759653 1250 42758403 42758407
    0x12070807050604060b0a050d02130207021f0302040602010b061602040504030e040609090209010b030405060106110316060b030c04020f04050108060a120b071101150b0a020708060702010624050a080408 88
    0x40401c006011152290b4001c4102003100100142008000c10280d00070740c0c459a0010742e00380240e102e9118602c07125260903001640c501d494000249001c50030750741090b00c01901d49070030039611ba06401507c121481030b0000d00002408008010320303400784510b152031128424501601502d09508207e82241c0a400d0005100035480007050a0320f82c1d98101b058141e84645900c411400c0260003e03004080c032551242c1141415520b15485a07070620400c000c0020052100040344000e104844c0141030400905a15005914150300605094040f480c402d02510314900311904050003151201450b41c1d050710700c1d1600b098015107180704050119908807040c014080346030001d0030302c03a0058600a0005815501e04640c0080220030800161072035070341085210101041502c44070002d48880a20707254440c1c10032001203191a103e80d0081d2902d105000a1010b05030301948040103541010302c2c102c0c040c0101000c8002e160404003030410002d10100301400e4030318455001315412500c1051164 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 42760903 1250 42759653 42759667
    0x2040504151b0221040b0a02030c010c080619050907110c04140610030b0603010302060a030905070e10060c080d05070504080a061d160510020a020a1202010207060809120708 76
    0x740c202c8100742c0781e0107000e44141d500721640d56010068a540b05505800c002c014a0340e90020041c64091840303442105000441c0192985009000f56a0030460800080000d50301d1031a0040242c001a00e10902840d00716048100110340c007600706060b28070103000840d04d034840c0d00d0101c46108003040c0c5460b0385d00074001001e05556490181490715080904408103604141b410402c2e0041080ea40b5006c0c14a480151807464940a09890460340c0445c1d20640354000340c0350940181c0900d2100034641c1c020141d0201344005104c020714090a101211142c0139070f02d547c0700341c070a66520305010f84814400d10000340600410341099502c0690b6240160425551340f103968034086403c8021103c0d81d449100d0006003034800185001d0b1100e20500801c035490f5502082203021300107000d028001c6000100071204c25008100c14a100d0b40e001e0050140c15658141030f90a407452a82700700d00500840c030340000d015218010003405104010040c000150381c500c002001d560104804440004080c4030907 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 42762153 1250 42760903 42760943
    0x909031224030f030a0f09030c0302010503040602040e0f0703050a11040311010207030b0a061509030312050604110a02010203091c0f0c0f0804060509040f0204080309090604060905090d0216050d02040504 89
    0x3448010b607503e0040d920b81c408208080c2004a400f11000c04202c04a0010000f10780d860070103000300ca80a00f00240d0325156810800003138452504115442243e040501c803990800c2c003c180e20070010396808112940b649882d1209843c401d00c1c403d68000b0b0144028000f003a00ea14030b200ea242030500441700b102d0f680340e1301c0002d01c1204550500c481a0707100010031601d08000080e403004056498038000050655801a01c524407030050b4003003803a070720000107200d07441d581d000515541c0c1c903440c5a912031000540c0203002c1d510458040180307000d010100f203000354101600b510100d442c3e855558440d48a440c0865510b1080001916440e0180303120074086001c0d00c1c024000360a81c0d40d1a16503807060081844155142e03111400d0141d4410030041084070400700c00e80d0910b08080b510420552900000540036141d01e4101820a51405007440390000c0c00084840c21a4019001c0c1c4031003040f46c07003844084803001e1040c2c6400120342140c0c03400524160b40600d80c041c1c411600100e0107035201d003003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 42763403 1250 42762153 42762163
    0x405060a090b0a12050f01060510090303030203270a05011103100302010f031e05070f020a1707050f0d0503060a0b04060c02060d020c010507080105030f060c0a0e060706021602090903122403 83
    0x161110340001c06c0d80c80801d402805600c0c09400c041d5008a20f0071030b1800010311f0820716104c0541055030100200759002d92007102500108040380c9010004c1000b020516111007280f2000c4446600e400f501a1681402e030007924810700b80d041c2d42d10542484c6800540b0740044d5801070008041d51010400850900f2242e501d10f082d03002880082c0503d003108001d4982d102a0b441041554490068a030010340604a4000045008014035403104880d01d800c904d4070385911442030403800b68061030801d0702d034450051441a0300403151040c3c0c103a641c01c07a22007d48a240100d000103054440b170795000d401e2401c01000c40c021201d5006181121800401d802c550080d0b076801c0001b10800d00400580c80d0400010409103040000792806050980b00401103105103c1200107006001008031400d1307440d1000e42d0005904948155030b600107101400d140c041000320128480c02c40c00d8041190090000260380581240c9000044680ca44000381641000c018098065400d42c00400403166203040c08 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 42764653 1250 42763403 42763439
    0x190c1206230609061c0204050a0203060109060c260403050a030e1302160b0601140d050a060914060d0501060b040b07050106080c18150402160201020c0405060a090b0a 73
    0x2002800c01d00e00c448180d030010300e104400c0340c055000c50900c080c0f652112203940e000181203c00074013030314080320101101e68003207a0180d40f2520307000c100300340207038203800641c8100b9090b80c440c07080c544c50700e0098904001c441c0c0064040307159034603040d48a900c03101484407070b00003001e00c0c207013491b0b03990751040c1c6805100b03a0124002910650801014100008902d0034908030890a504204072904880c0c10650054405071041080c2000304007107901070002803640c0031054880990307a64000c00440054002a101d6090540c0b82000008020b00390b4400c2c3c42b1908000f46180020352200b20400041240400d000c0c2c425541e1483c0000e1402408001840141100c6003c00d0f07c40041d42001401c456955100009541001032400442d40c1c8110f00c5500c2e401003405642550389a03c048044065120340f034154105200060360a0200701031021020414800d80c00c5424240110052005880082d580150890300781c604c244890310f02500000d51100c03001e0700c440a010764a0312450a03580c000c50b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 42765903 1250 42764653 42764663
    0x20403020a080a0302010501090204120206090d0203010501060906080622020d060e0a0c11010e12030a0f090809131e0b01050c0102070308010503060708010305030f0309010b030a05031911190c12 85
    0x55400804d6020f01403c0c1c0180030780101141003510784142d40300030350070743d0710000d2103490b000989240994480c41d50140725074002c0c00030846982c580301d018000c01a9805404089450040003504901e402800700005000055241e18140001c01c020740281d0800a441c90107643c49060101c0c2110605e84c49074841d1102d2540814850703146800a0440c5c1c03100440003240d0b904142101480038400903041098407010f00010b036030780d600c0c001854000c10503000d0042c000d40c144400c100c1807040900c05449541000c0724203200c0c00007204680001c8130045000301a140f00058924032803e40540d02400d0001c1060412524220070700d0081400c90b4040282140451030080c01804035080c00c10003154441c20b40d0520f00300340d50440e2100f55490050504c01d10300241d000002030b40720f400c2900089182c3c41c0107001c441e0680f90602e091600ea40200400c2c0f01d210f040b0140d25070350148518049410407100001400500401c411307104000d490501c001c2e142c1c40101c50001030141c0e4400300c25070f1194061 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 42767153 1250 42765903 42765913
    0x318060905030901090605070206030705090d050102030108014719080d0e01050f160c2102030c03010c05040b13080303090a020a0608040b150301270c0e010b0a03020a03020403020a08 80
    0x4070f0003d044508160881010400d05000040c0180c54220890340c001e02d107401c1c40703520340d8034410004100c0c2a0216008201e0350000c4000101c24030f0541140450301444403580e8565000012060441448a6800c08500701c540017100100e8003003114440f11020302500c02c4038400410074041c02142a103500a95241d40103141d070a241c0b5500403120402d0715024078086240c410503040e81d40c101d024032101604007504660b07208041060107620b903401004000c11648155602d000035590403120742d0401c0e03029000d6003850b21058078047c07140c1441c0380441d85032581014103040e5100c9040c2c10901442038417070890500070910b03031030810255103d03442400050000210501c14404d00d40c1c0c440e0b21810a1003050020300001540902c0c8203507000444003042210302c40c400780002d025042c81380703550303514241300d049400036030314143d000e0300741d00f40541c01f80c40c1515602d40e141140480f091285c019003440501181641501c00d030010440025980740260500d512034001841151041d03015412960013 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 42768403 1250 42767153 42767167
    0x627050a0e0a0c0e070810061101150b03040308090f1504020a050d050d02010c0f0f03020a0e040510030c0b0702031e0c0312031e160309030201060b031e0c070201020d031806090503 79
    0x1d6000f00382c4c4a80c69207042050760900c08005031b10107c86006d0801409042d1202c150042c109610640110807a50742c43c2c003585940b640480700582c401d440c04d8002036110000188403030741c00615040c110000f2402451201114000b000b16500d01078800c07a400510300d0b0000075a03541c1c0c1681c00301a40d000d00050042084481c2029084800407003d90f0706201d18101e1500c071141d0001319680c850035507420056910960707020200e6104000c4801c00354040d1800d010b03c407205000140d040c013524440c0841080058540044002034060500700940c542d000811380b10742502d461072407607030030200541250082018000020309001c0e1041e695141c40001100700001680382202c1030a10049190314210113042104500b4080542c20f154282490b0319480c405041502c00d40c0010018101004041e8407401c0c1940c180f11081030700030101044030200c0001c1600d840603001107651407a4160020071999404050580c0036007451041d00da414218a9002004111140039034030304030703108074080c55440d01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 42769653 1250 42768403 42768419
    0x10051e0307030c110c0904080c100606080a0c1d0d020319060207060f0e0a08031b0705010c0e0a060504030b0c0403050d020106031e02030307150b0303070b0105040627050a0e0a0c 78
    0x40c0a10301c1d11603000042030017103a1950007855400c01d4100b1241c3d5518613000d1000d526001101074440c0d005c42c41c0a40002d0115844046540a011303110818002104640c00485884051220381010890f0803c01e103034103840e00d078000f201c0c1d1360710107020380e805615100c03079000d91840104010303149260002002c0080007814031076480c910095040400c500707400000180e6035038006510081c00d1200020102e0b460320030110b048500f00c43c1541d101d42d03544042d441e00b1070180c92204d00e0880851440d0503540260300d85500c0400a45019984003400c051560b12100b01d90343c8040c3c10b440c843d140400c004000325801f4000060100c030301e500040385213407441c41d0045000904005101d100c1c040349000800503600882210501c540280e03144100c5e81c51708484000411a80c3c07a0360b82d2601c4009401700811050301251070488408075020040c1c1035540705003540c42603207000481d003409450480710000f0042d580c4165000300402c140021100801c140700c03441e02c0c14442c1c0a94104400c0c10041100d85 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 42770903 1250 42769653 42769667
    0x80f1006050402040e1501030f0903020c0306070503130f0813090212060609060f0c0f03030711010605150702010f0c2a23010804050c060304060b010809070510051e0307030c 76
    0x2005407021450715145c00c1140c000400e000e440b6000203544001c60b0b640c160700c030350400030244404030800c12000700c040c503002e50380d0a001010140030303006500c001043c00d805032060701c1c442d0303018242c094400d020660f0343c1d0083c3d10100f076007160003403418081100d058280e012100b020b0141500300681c0d801c144039060800312002800148100710402003d1019141c0704192105040300c03070020342c1c441c0185c0e403074141403a2680000c007016200c0030040155282c2c0c00000003001081d0640200415902c9d241488078615440d0014072418600308542001544140200d000006851610482c1041aa541c580e004071480c08010009007a65164510300e180503c800001489103108420359a40d139800620180b1428030955418071104000040c00d100041c4205061030380300402d090342d2880e103494460014900e503140d0074001a002c00000b80c950300c0029810003902d0b8000c10940c02ca0490003000c903521b50040701ca0300b82448128402c82031002046c00918090382481c2c501141c0921403000041410b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 42772153 1250 42770903 42770909
    0x3070903060b12101a040e030a0f0c03021c11010911040c03050112060903090905070c030e03060601080a0c09050307030b010503010b2407060e0f0606090c0f16020307080f1006 77
    0xe80c00400580c48041800207044c043c0040180e40454007020414071180c1440703444c403001c1e802038140301500e850381c200030004148001a0783c072081c031901e0b02103104580c0c42c0343d500c1008000d40c0c0b1004034103048006510411050344020301c2d0413a6a104105a03207425500f180c0e10440d80c0080420041c14145024000c100c0203030031500d801c010941c5000c1c6a20607040884e40040c205ca59201c80500038184180307035220141407902d4062005060065005150090400d030131303000500441c1a0762602e140100e0070740d0151105a640444030b0712114658001045250030035410b00c0106840003900c0d80f030a100c288001d50048030000340543c0340200749425220243c03981c0d442100c000d0038000e40c20b00080160072110801c0160030f44c45030840c0c6003001c0108409c0d0a00c010703901c2281c4424081210000e0b28900c42e05055643e04141e489a901d11000c90268080220618500f841101132410b80950400c0300c1e280010202d49003241d17106402424240700354003680c2a504040388400301000b06000706002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 42773403 1250 42772153 42772159
    0x3210c0f0906021b0d05010b15030916030807060f180b040b0a020304030903030e06040f080a11010e01050405042a0801060e06040e07030209120f0c090f0609010512010f0203070903060b 81
    0x1100752640d240c1340f886003409000d40c42050464102014802c0940c0550400040a0503500c0440b0340441080c1c05600210340c001040d206040004851000342c0c0d94981c1120b40c821009400e0001564410024010082040b00001d41d206054000d003078034016481d10f40360144481c0f440605180c00d2007251800c004200e480310714010020300c00001da020109400312501840d041032600c1300d50740002d21034441d40e44129182c00302004085205040072680d10034092203014103600170840c0c2001555513821342c800d0710780400c03c144001c01650806400c0b4601d0303032180c001c4000701d45ca60a2030303220600148616003000070750b01100601070590030032140b04400d0301c2142c80341d080902e031008000040400520800400d900816401302503240d00345078044000c044001d440d051071100240c240c0e00c54002030312a115110510100b5840e019001549014000150401d0384581c204400d00c1140c00030516528100c1d969034000300110341c02072000e035016a0841d80d8440130189541000300565504a180f10302c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 42774653 1250 42773403 42773413
    0x7020a0e01061b0602130b190309030923060703030c0809161a090a030818040e06070c0f0b01030605040c08060f160309020415051207080a03210c0f090602 68
    0x8083c2c00c82040088242c914010069050443c503001c0080d008031421000d51281c15000851921401d4001e008012020060351480c1d5480540031000e130307020040d014021944114089c01f542c03000c0050420210041d1160740c000f159820040781040e81328070011341c0029031790765484030703031583c044482500030f034140c0020200c841c4846401030701c805c2c43d449440f1180c40c0d640420601d1680c070005440e20004028401300b81590380f42000040303988040300b03070f41c18010400b1044031381d85840e1141074100101c03800103001d590713100c1400b9103940845030340580d02c1c41d008005110014100742c1026028610440c004101390405250040d881105a0082a515040b0100700180c05501f481110340c00803914040c40c016803c2007105038002c00061201a41040c00c00302034110402d500d00300e940446a007540c404480981c0c1e07030303000c1d03031149084d000701421500061103900100740b10704440301c0c00c142d141907481c100050420604007190300d801004808120000c51900202d90405001c900401c035a0010f01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 42775903 1250 42774653 42774659
    0x302060609060a0e130b0709060c06090c032301060b0a020303130309080304090b0f0102030c1002250605070f0908150901060308030108030414040c12020706091707020a0e01 76
    0x194465200900890058590500003605076a071158160024100340080e42182e0501c0c200b0110580c02100060b1340744030140c00850119440345442504582040d6580240000c041e500e40014040c00401915a000d10007000703c04503543c81302d01101008648009001e68040c00d40c114256102644801c070402c100740b210040c4103801204480d0701842c8180c10b021808100c0c038040c2c4a541540d001441584400708001c10304050a51104141040846d482c00e500e40b000001240c0d6803003000b09100140d00000c1c1308200c05c040b180c014081080b24421904081c0403410604402c1c00300c0d840055549944400078000c5460b00300d690b070449050280f9141515904040d0300c6507a5560003182200c0100c400800602900c50a500c800095980035010343c3d1380f0359481d064903560fa0064055100241122000802e00303180600c20200001c5080d00e0703540d0791002800049009421503c1c042c1c80d078030b8541490b0300004001054500000305207224558441003d801801041400f0f0740020603c15500c0b0014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 42777153 1250 42775903 42775907
    0x605180d0c050609010201060b031305010e030406020d050a030e0a0b010306051506040b1806070b1b130e250206011409010803040e06060d05040302030d0c020c010804020402090105041e2103 83
    0x1d030141d41007078500c07650ba403c8890040340140183e0f030006855a01c04414841c892190f1f00d0380140e407501880092205500d10705081d03031603200318443d143c0942e02100c185051a0300520140070350103004d040c0041c901468045d20350410032444421210004410014010000a8030a05030080904882e004150b0340800108290740324501400403102c5002c50800c903c02c0c2c1d54800301d8400100500301580b622094904115a03100542d5030b0100d036407044400c40b51310304c501001d40d40a451039013400b842c0c2910301020403210140242821306c94400c11f2490000c0c01645007925280e0542590040410f036141c9442011000c0350000c0141c480c0c05207a00400c002a400400d40e020346002403103511998840000240c402d11400003502021406c1204101c00c0c1900070000d03112007042034400b84600008000e00b240c43e42420a01c00740400c0c4004017140140c145503000c0c201c4114181080c034039054a529210280282131082d014802c04950001d004004d1304160442c4881b000e6080c0310840c0816640c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 42778403 1250 42777153 42777173
    0x9080303130605060a1707090e030a02030702010e1f120506030a050a0b18060a0204030209060405090d140c0106080f07060305061503060402040302060406020105090f0f0307030503040c09060605180d 87
    0xb502d00c0303031100c000c21104c1d0768001c0500b00038503120000c034009441014956884140c1d9100b803103a8549030a411903e01d100c04000c41307005441c540c1c059442e0985a5006403030044c81070300465001034480d40401c0c51001c118104200e00d040544807d14000c0390010018140d400c010140742c02a0403280502000403000981503040036400b4030300e42c2c0c203035862100081e0b20801c401104005807003480184440309a90b80d00030001d690007640c039030380e5a55514050006031001074800c43c0082c4d01102141c800c0520036012028400f0710760501c1480c0c880f114401c542510b00c2504285110340094030541503130b41d8100000802071120342401c0c8040e00d07200000518100ea4068410800c190002c00120b080c1ea681c0e04940c003a6030b00a201d240c4503502d9074030081c02000c007101c2003807807445506a19010000009403100c8140b0090000b1403800c0f4040c0e03000c459a40001d4801c40d042c48013448089021a4540125006440c50f9550551150b10715082085c4200c440013800d401506d100e02920b0202d020521 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 42779653 1250 42778403 42778441
    0xa0e03090607140f0106030b070e0406050913050f0102030a0b03060109090b010b0a050c03030c03180a080a05090a0503011802090709060e0411131403010b031209010c030915020d09080303 82
    0x48403a400c0f22558078a03081c49148010420294604031001c0104140c0080c458014009a82d41007a90341b0204148400c840b00380c05156807081313600340018080d0402c011920140d41c8510151403000f5854030040703003a600180c031450041501ca5040c981917080400c296401000000018840c0031080c0e2202c4080d1801800368140f1481300040c1381071004d0240007112030481e0720104403a6a0714161501ea0800e400a6030340c0c1c003401118680e00c0183c8036001030001901c1d90402101c9142100f122802c2e1902e0307200c1c0e005240c00c644190b2001416507000e00c503034059801103e90204032020184104558a003000302400284039041070248201940300c00350f04420042a030703000406032a400d5000c10280102241540911309441d804541038042c4d0032100c03180d040560090040c1000d403c109a161b1b003140381d0024001c1018001848190b108210620540b4003a00f0070036501a2100304078101c6400c05520140564030214414200d1503200c050b03100103240040240d415401d2400721a140805052 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 42780903 1250 42779653 42779663
    0x60611010212040219031a070801240513050301090501051e090a02011b0b0703060501020705180604180c06080702070905010e0412050903240a050415020f0405180a0e03090607 77
    0x2100c3c03001ea4481064031010319041f240c42900511180c2905074134440445460002078404000015440d2082c41513000044c42c008000600a0308600b0032103480e04940050080030360140c0001802c3c0e10300303105544165008a001044602d0607034001041c00e200425441c02e0320018404005120201042c2040d071158240303408a11403007601e1904900d80c45680010340300c48840e5040c4015180c065205504482081c1c003500d0202d9901e0b4200680c80312400c1e48141007580320340015250f403800e6480900106e541641d110449912621002c1326407403aa00b040010640705020300c030100d07070108150001048101828001581000809025500c01030402800403140401e00c0c1b03101c074000c0c1d054400300c1c00050300321007003802050604c801224262118407154490b60340450440c50060188910454102e15103100c80b21100e0001e900130362210014001c0c9690030301012415a03907181403840c500400300c6408c1c203582050202c0d00100c422121140c10300b980100803403003583c3c69010603611095009 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 42782153 1250 42780903 42780919
    0x90703090503070c0e0403080108060c0d05040503130f06030f0603021302070204060801150603060f050603040f080d090602040302090a1b110c03030c0102130602010b1e041404060606110102120402 86
    0x41c40d20741c1c40c501624800a048000f8980c0202e01600c0e070020145c840c0f4003035039070741070340fa43e980b40c59684900080d07070305411440c010800382000c6407064000340e0300a0b120340c040380d2502da1a084591801601d9400821801442607804c003d4194180500c55808112003420000180b4580c00104010305080d0901c241540104007031042d50b40301e9010000505000000b0700070080542d080100343e40d0f041c010000802d107042ca0200303280040541032015a00040c1205142d03403120f4403800d140600382c6804480e194002c11202e00300e66807900a00c0c124902c603d60258481e41544108081c440703000302850000d520b803504180f145960100a00350003800c608200c0c0d0070b03048098299080c503071300c00b612070b0b0103100028820040410540c020440d00040d200c45101d510b0300e50100700d00340d80710380a01503403204070300d21340648008c42c02c01d5041d0407501c018400542c5002a11582c41883d004a80c141d0364a6034511042040507040010540000c0c0d0a5000b10710300350a00504004003880a44064050081 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 42783403 1250 42782153 42782171
    0x1080415140403030e010c050903060c130305030c06011503051608090f03031f050109060e0618040c030b040e010207020d0b090a020603040b060a120201050315040b0604180b010e090703 81
    0x2141e4480504503000d6040c03074203a40b42070304010700a024000040324213903292544540c1080d04c90320540344081d0005002e0006500c85004641d05500140e8400c1b94828a42c50000009001040100300366031024026004541c9400c3e5007042007111250f052080c1418a0100400075040d001640b07802415030400c1441c54031262240380c40e00000c031503074201e6480004140080756858280240c91180c840b80c86005042d2201c00464114000f40300e40d201080140c403441c010b51404034003800c4c4100504c005501d01081020001302035549200190020035904c1c4c422040fa414240540c0e403d1010f240000e600d02034055020549a070800080502001c5c016400302c1c0f1aa40d00b403224400d000d070020302d101c0e205d0609050001079000250f0780303a4400c450000740015161112620b0040042d0161a01070865442d0001c0e24101604020443e40c07040e80c55600c01500c6d543d490140001d0000c820104d40c1032070b1060a00ea0071030300c400c1201d5040c482c00d5404c0e44c480b0340e181a5003a90080325464049a0310034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 42784653 1250 42783403 42783443
    0x207170d0c11031b1f0f030509100c23040f060c020a0f060503161d0f040912030212060405011505070503091c02030c011806030b0f09010602010204060809010209010804 74
    0x91100c06003649409070403801340156080c5988400e003500112004600b8980743c41d15568a1521600300b03c004c10190001030022034041d500039035108800c04169060356850304004403c5407168168640800c021540202001042e0a080e441c8680d0303520801e4a42030400c81c00d04c091405a106250400980c0311020b0110f403246004240100700d500040000e0548442014010343c00c00c54010400f4500307509410b024500c5090781c40b64100715032045e640c101200d90140689209c2018043e03420686a83c880b200040e5500502e41c0c003500e490f9401a124100c0c884a0440200040c203840c2c419410800184840f441004241c1540840360402d913903160803d1805c41c0c154001c800011f580f100a87c0005615030741c03560489000c25100320180d451401c01040190b62100340d685000d00c80303542260082c040c0600950000b04403901c002c05602c100d1802a000608034503098008200503500030408010003a0032140380c0b42c02461a20096041c4001c1c40c0000f8010b0f000208060124101510340e100004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 42785903 1250 42784653 42784673
    0x18010911190b0d051812090616170c0114040209060108040302070b040902040302010801052d010201020405091e010e0403050706150b0a02010605010e12060c03090c06070606060207170d0c 82
    0x2100182503c0d0030703200840c01e00030002180c541007500c03849039203180d0f06030b40403800c515240c030015074080c1417028110900c441c1c2e4100076001075800956054400c04240421042b000445203021742c150784075424a812400c1d1041d9000c13490300303507590400f4072005039948203060364000820710b0510310a6869050403441c08e4401c1e40b104080b01d10015002c0307980c154a030000e01c2600e0003a203500740140d030303240140000d9180203801c41046030000d00e2010000513401040002143c014070001d0f05150300c4900140350044180c901e9440442e01ea03c2428080501017011801801e0f070401c1001c1624064030003901900c00c13240d005190301e95070801080d07a01d075101000000740180b00e810544a81d41c41c00040d0007011140a12404185041c00790007091a02c950041a0710302d0050213886d55071501911500d581e000907000d00054010840700361490b0300c1c4c1d24041c0c04902e02894012410034945440641040a10b80104600c90030440d0f83c1d24040400042c850100c9610b85419240f00250741042d007854 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 42787153 1250 42785903 42785909
    0xa050709180c08030a031a0f0d050705040617070812031504140103030309050c030105060a06030e0102040905040b0f0604090c030201080615030c0c06010906030b01060c0f0c06081801091119 83
    0x31030346107031010840f01800005800701c1603064808000011000b40300b5505400c45c2058036502c8403500c015000d250030a585031014440c4600100c6025980b0350001800791070326500203003150044180c1c150f020b445c0c02c12403000146510f202510175001c08013030040103480000d090701003090307801c1d4501a9030746903a40030b4850070041d01c0000c82c5a5071a880c00602400300100c05460310f11a000c405c1c4814075062285a0084100400d0001128603015094000e0039144048102c195800d100002d0f60303045a004191003188200c03641c003918a040c00040800d010003904050040d49480c8a56001805150707600040c1d17602400c209600380c0e00d410004405c4080003148801c40400070080c80b4404000c00c000d0000c4854030004c4d10800d0303880d00700035805c8070403c1c880600000b407410010001c1038041c020300b9581a0140c41e12405051151f110388502050b40c1d4089000941c04801300481c405070b607444030154032001c8001340b100d661a519912882c07200f101c569172140b480800d8008000100030204001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 42788403 1250 42787153 42787163
    0x61107030203100c030507030b0901090c140a020705090106020105060109030f0f020d080915031308030601050c0307080a080c160803060303070b09010b0108061518060c0318040e0a05070918 83
    0x90f540020780908050071090740e003800480d0070302001c980c071280070707001e540030800300500868141c1c0e10703101c0020040c2000c12004428040c4a010300c0c481d09900c00010036444a945c1c0040c29810719120502202c040b0503405003085901d0310042c40480da034415010411079801c030003c040404105d0820290031084200001d6000400c035811008012641002d86020f84003107c0c0036a42034203061120031304e0703c4200d80000340192003498140000724150003444d0405010f240c05030074201a00320492a690050000b41c541a0010a81c22441584151071603030116034880c5060400081c3c1c894250004200b400050544102000160306130704c01b00183c1c0d0b00e280e00920910401d00f4040801402001a02c400500080707001000820b2400e050b5031400d010081c60003807600d0107103414800640c01c003c1d9100d0340e03802581003141c2c14008508101503c0d0a240180c0066100c81ca007a003003000300c8404810201c0c054000c15100c01c003140700800c4031403c8480485010402010031403074241c01141c1442e0080c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 42789653 1250 42788403 42788413
    0xc090d061413140a080d1a0d06050108010606092402030f1204060e010b0303070b060d0204050901050f240d0807060e060a0b03071412010f020316030f0203010e01061107030203 77
    0x108014100e8200031049000b00c2a0700107405610740031030b03107607013035980082d1100b04c040101d06400002580407000744030302c0c503c1c0310584003030100004801c0c450382039040c0e462680340d00041c8a242d800384a010014040345c2020900c01d4030b030514107001154016070802d107400c0c0c0920f2004020f4024401c0310a480400d00071255281180b400300c1d40010010f031801d03520145000d655040340101403080d5040980000e0003141000e03141d5980071524a00181010307082160311940b00010b0b1528014580145194000465549412008144ea5500c001c010f4240c46046941c00b600921416464400c1e455090311300345107501e070600b0031480c0c41c0704941d0020704135071030251103148088000c11181e004015522090081192080c1010313990324150240404d0324040c900469202d160440d210028002e8074070010811020304240d840407600115440c5031199800c4002c1c01c0420307070610620410700700312132003141954107040940789040c905010340c5083c400d49986409544e0001c0100500a56004044070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 42790903 1250 42789653 42789661
    0x6140a0909020d091401020a0e1e0301090f0b0f040308150a03020a0f050306010605040305030409020c01092001110105160305070216090b130513020108130c031112060c090d0614 78
    0xf6008041555080d6401d014100c00d084080e603040c000c54074000349941e030310747c400c078410001c0002104c1c20a07000300c2902d0504040d04ea00752801c0c0641c0038614041c01c07a860341965030342010585408001d2005c00c103400d84804001c00660080401a00540e4130302800d051a04408040b0b201340803260000ba6024103020700006031010000124400c0e52415415941c45990b2103100340c0d800c2c041d5000c010520340040c0f0003848041c01a90203070a1381c00f01d0710f0010801006c10b454614440c45010507501030705005a01500055821088007900052040700801103440d01a400c811040302603849601015203400118025030310800500902d60b00f20300d0f01d50f55035a514000000144041032110f0b00401480c0c1d01d0314800300180c81020300c00c1a041c440d102d86803826500441c1c801c40000c0421800c00c400071103050200ea600200c030000f4511074441c00d040e8030107413020046501c0e0316680000c1130390303c05410400c1951a59099514492003030394654081850380c50205c2c05400c1191a407916190303290100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 42792153 1250 42790903 42790927
    0x6080307080c0d050c0a081606090c0f080f0a0b090c0307180501050409050a0624060801051f09060c0201090b0c0d0f050315010c170703020609011506140a090902 71
    0x240440c0d80c02c0300407640707200d485020940d0703e801201c010420302c0d04103a002a010821100050100400301c5030080301ca001c2580d10701c82160450320050b560740381030040c184080c4d158042100050b0500c440244030010801ca00550b1390040c41c0ca0040c02030043e1700c04109107080c1003140000d645001170a4444003a10343d80c00a0341c400c41c601292100c54288000050141001d100300f0140781c2e04140940300c3c480298407901e016201b000d144150000c2d18030940d40c013041c10540c422010b084d140c0e40b80241549060704220740c015201034100c030007101c8569609e1405030031544002c03c80e02242841c914100140c00181ca81c0704490b846817008070000079461a4152000c14480c0c10303c0460740320140c402c545200c044407117000c01c481601a80389105068521503004500f960351b524882c141e8070b02241003085d0000c181d504110b0702200980c0c017880600c070905c2c40a01440c2203007a011020566024502030000b4030340c003001c1481038400a400141d9005880c440c1200c1d0010b044e0380c1405660395090b00b60f40d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 42793403 1250 42792153 42792157
    0x70f020a0e04210c03090b0a110709090c09050c04030213090203060727030b0a1d010e0a030801080c0102060a09020f03060108030406120204050d080a020a12050d05060414040b09010608030708 84
    0x40040d4026400310102c83d240164102115aa05960ba0036900b17410070450030b190390711090303140080c01000c00316503001403000c04c9001d0242c0719143c40400d8180700c900e81a10ba042e641d4002d40d2042e800c01081003212150705042d9421250110342040c284000d4551003001400184406074140c000c120806c141d441d002151b880410040c01c004846e0441c900b6544c030b00150050100500314032603140815403619568000481001c0e01c030301404109204801d4060031540d00e030250356a1034028166141c00e0503009180b03540144001006042c10b40d40000000351201d40091410740c0c130300d903554a00004c0d1340303c0001040050802500b12000e65850302001a41c0741c0251140c040083c05001c4200b034008105c0c021b5500311200603200b04d00c20120755642d0b000b00c0d0000034122045210b0300d0545c1300480c94030700b240010f00109849903581d4584548800381500c500a0525000760f042c14001c40040418094059102ea0400352144564444010080c05400a03a000c007800d0300c000725851050140c0030740 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 42794653 1250 42793403 42793433
    0x10022d0a0806040207030906140412050105060306090708030d1104120606050f0109060c1e0b0f060a0504090203030304060e03041d0610091d09010b04020c0a06051b070f020a0e04 78
    0x803280c5690b952582080240d101e01d0a000b0000b558200080001d107015000320f404264031010b2080c10f150300c0c0d44039948510500750f02600c490313440b4010f10007503003424001d40c0d0300041c20384040c1903907905084446559100382c00c86052800e0382d9410300e143d5440b000068502a2030a4612454212480e0410b6070192000f03000f1148119091030ac45641076004941c24012a68652120586000c240d2a501d08100d20310b0159164250042d12040000318000400c3c0d00c6401205100d00507410400144a5501c5640e0480341c003480c030308540700001d6a00003050b01d6101b036100c100412104884119941580280d5100012000d40085464040360001302014803e42e02602c1d800703112121188111500c0c104e52081218501002c20341003030300d1a0b0303001c005510454950020070a601e042000c90100d920501c1d54441d030780c000048100400c0060b00540b0f4002107401e09522101d043c0444c107140c1c40c40303040c50062184d16030703c6003201103444400d0580c000f400003410580061803c1d003404196007100355 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 42795903 1250 42794653 42794657
    0x7200c040c02010f06090501050a03020913020303130e092a0d020909030406170601091502190c0510030c020d0507030c05010207031e02010c0507020f031608100b0a030510022d0a 78
    0x100104546c2e04601c00c07281281c000402081042d4515002d0200d000740c054101341801c2040c50965001d6101000149159414041075010f414030b066040284114041d200e582ca036000264884450140d000c50341140d032032903084510000501000048420010503002508000040c040000703404011000d041100c8081c0c45503c5000c1944180100f03000b400c54074140882d0801c0800c1c8070610506260000000e5140115070512600c140007090600070202e0440d030140680d0f00c144010308000550076800000e500b01032016884840000c0d45845802c0220000c00202040940c01d06205045550485406c84021035440b141410300600c44160005405290200203504001980c41481603424074070407944c403a42004159820001c8a480e03c1002b940d25100c1c0c0e95046402980f103c4102d0000c0c4001c03001080040304802c04c5400fa0388108100501c254aa03982c00c1000c1100031919420880d402640160b452100c200c00c0c1800d0f203035601110015802e50a12060101e101f08001c0c41e01c60555 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 42797153 1250 42795903 42795911
    0x804031d03010e06100501050f0a0f05040b04080705040c020303090c0105030915010909030e010507050303040b06060d020a0c02040606020706021221090705090f0103020f09062b02040e0607200c040c02010f 90
    0x401c010b42349841042400040003204102004640b4454045681c41b90441d1030100d103840d0fa114520344181d04590040a0603030001e42003003000c0c0c5031921805010010a0005c0c0d17044d45061030700302e5141c9c1e540c01159414800004001f0b0000c5000b440001c0345044410036880c42d035611401c40300010040e8070802c40101c0c01c0c6911014040d80200c3c280d64450382d02500841c074541c1c0c0e40d648c82c201500060000c98004e1000e1140003d004850b0005e0110440780da030300c540c20030401c0e004002c1500e0882e0310800544d0000582400300350750100388824498000c0c40305a640742c1401122400e5940441c0d2a900201d0090052019003140840c10070101d440c21104808107441e16050520144000c0c030000f50710a100400000c541d05140742405e80c4400300800030745a003009580403203031031500100d508400e88184c83c02c0d01c046107000c0c4a00c02002038044000e00080c54402005441401202846001020102454425041c1c01c010b5107451007805402400145c101c403802a010308041c0401440681c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 42798403 1250 42797153 42797159
    0x60f030c0605030f010b07020409020a060f08060a0b070b0c09041803080106080c070609051501060c05010e06090303060d0c031205030132060c0106090504050d020601080d0804031d03010e0610 84
    0xc03a00c16603004d0901410980341d184d00e0300785203010543c00030004a8100b0340324000744001d84d8414404200418942e11010740070841904010442d030030003002d1500c10641e405051103030240780e20079109500d9000024556a40314030a5561980c0507000c04a64024100a5134a0388160450012007130719201b6120300b0309590301c80409032084d200881d2000c1500005208420100f24250000500180514107031091062751006008030400240c2001001c15001d40c42241040024461b1035901d2401c48090b00c0c5500340f98504d56101e1002500d000d1280c80c421140780188440040381d8802140e010001d0704e014092600e025013643c000348158584d8001313200780760192085091150f40c18041044500443e4112681080030b0b07a08048a5000e65641e01c0101003004003481c0300702400349000f0401421104042d4900a1411805800c00b0342144c20a029410413190810969034006505007020b0705480e120540613070000490346805903240d800d00001507000300300451100e0140c1c401401c901d03203641c0c17 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 42799653 1250 42798403 42798407
    0x130501031e140708010203180a020307060c08120906040204060909020d0b0a0e03030103060b03070b120a02070f0203060411010f0e0603160203070203070e0718140d060e01060f030c06 80
    0x10003444003400c610032119007030800200d07049144403032a1266018180001914039958600b460071340000300b480e03600000340080d20b483d50028400c040540002011156141e9000c203886803800e101780300c10701400d46c0180081000500644040ea81070b0340c1c02c0c0c10a03280131132405940300e4081d501030b4040d034980340b8007044403140c0d4001c09522a40207000b58100508665034101144401020100710f5a038840d00b40c0a400c40601c001c50003940120004a4001000000c047c103010840c1d009103203003402000310001128080c41c0b00342e40f00f00d00550050300c03900305040c03905401c440910300a5060207580b04010400074416007190803481c1c03c0c0d84042040d500c9690644000000c482400d40c041d80c14130005500c4c00d40a41c0c0d0800396030941c4160b0b400c0c00d0880e0302103450401c081d00f004545030200c50410402c5035000348031200c00c0c4072404118a2551401d040c10f4030780807200c040e00c0c1c0200124541c2c1000d002d0b07960001a48241c034040200212030361141c1d640801d0065000440f400300f551980023503114 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 42800903 1250 42799653 42799661
    0x1903182a030503030f0a0204050a060504081507021b0f0a030b090d0905030c120a0b0906070f0503010b09060901180b0d0f0209030303012d0303090e06010f0e01030207020406030b01031113 82
    0x81e50001c003c500e103456101c11030a110b0030007441d0b12011a020071010459440e000e100c24002c00117031b100c2503184d5040c003048038280b41d500e11894022550303100c10004c5c00d43e40001da2070420510310580c0d540292086010402c080101c44045030050b044040000401c0885003800b8803851141058036070300b03032684e10300721030b507401030301c5a43d80c180c2c040040300265240481d4084142ca072180b040702c4451038660f1300c0c0c03170030900d0440d40071f00c941d0411000c2100e8590010309005030188646082481d6604214500d640c0c0e01034400542d00455000c21000c4682e409400b108034188800b42c207001075182e603a500000107900500d040c3e01074a0608005503020159802550900c1c0d00007400f0318210381c20680800c40484181148618501c0b00451400101f2903460700310f00903501030381e00d4070039050403c00d8804c08410701802d11410801c1c0714418504070741d480010306540c002c091a0251b40d950003030000402600840d00090884d01c61040004108a0080c45444802c50180c0c4c1011030865072119103000c071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 42802153 1250 42800903 42800909
    0x1201050105030c131401032108060112111303060b1801051507050a150516020a03080c03070207050415051504030503040e06060f1206030f0102070302031903182a 71
    0x3681c00074419103030a2071308500301000c44014410005000b00044007180c0808000e0740161001e4000c4201c0355400740c3c80e03004118654160341401d112506101000034200e100c04510750b8925075440454080e6005030008032404129000015101c2e10344038200030008000c0302641500c2001044040c0626007504c040450480304000d00f00c4160035444008105564031440c4215850b000d003400e12400104c2c03003441d405110707985140000301da25202e000650020700450020701558031010704030b0002680801066402500b040b20743d601c0391a8480260700c1c0c4107403508520703446802c100c680c7d1002d1000300c0101048983c11100d044c14118003002260041c85140800380040c1c00401c070030b10054614048854200c8806050300d840c141c514080b03807900b07030000c042c80494610320f44148403e52404124180b500181203008514150913542c01954a2041105032210600c100e0490441c8501030380c0007221500010601680a04803850004042d600e410b03d08841c01200c2c00312514803030300c04aa03900036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 42803403 1250 42802153 42802159
    0xc04050108071a0702010201240e060d02100e010905030706020f10060302030d0809070b0c0c04050108030f0d05040807061d01050705040b03010e04110a06020d020609010b010207032306151201050105 87
    0x50b154040082c3c0c0c0752075004080a9041d9900c03440340e844034034049004001c0c03215020300072082d007a003016107040312407130081d0501e4419102c0d00c040f0380140c1d645035a010303148501b505005491000000068500c5050742d03020b1036250062a030f000892030340100d000050080c00c070041c0c2c0c8115440054100491320a400081c1d01544003009401480b4001c161280d00007403403604441b0f40d282d031550802c0c4250b0140e03034114801c0d00070410f082c03000c0c00e140c0916405800110051400e1881c000e00c0843e01d8007589880520b404c0c3c490005c00d00748291141241c01280d00305c00e0a01c1901605621a0040351000c03502d26201c0d032030000020b1f4658400c009036419206100142e91440e40303080a041c64400024005a525907100440718146a481c00164801080b458001c0d00a01200340c0c80030b41000790050262036140d04080c1071180c01e80c1d0114070a01a41e5202e402554200c1401c095288a03410302c2200d80850f00c00da0082c400b001c200c400d01226840f608803004803082400d40e00447c2a540c0a00c16550 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 42804653 1250 42803403 42803429
    0x30d1503050a0b0703020d0204030809100f0e13060302030f01060f0b0903030403081c1a01030f0e030304080307140403060b0a090c0e13020705010603061a0d03050307050711120c0405010807 83
    0x4000b03403e5070709803908010113140150400485100600480c0e0240d4012a00d42e280083c408030113003880c3c5226420441c0c5070400170f40b000c50010000c1d10f200c810320411449098003030f500c0c0c0024400d540c411000355030041e04030360300d404126504074001c0010380281035800c48180030009001000c80222168020045c014605092031a40c51000582280d0a94580070001400b09020b500641c490304414003001380004551102c6903001408403401200c603001003906003000344d03801d02e40010440360880c0d4803007480743e42c1c0d07600c485080312116201c5020b000c0e1044002000410b10295030400d054a110444507100340079039500c14401129220001c20007c6140200b502c1c3c240d14013031300280c54118510002500d0b04a071a82c8140c2114142d40044400a94808204001d00441000344007540701c00c5e00d4041d03c03034100340c8014100703001c01003024042020000b00b039400c01007605010400d56001030211000c5c0803944880544070050320180a01075072514000180e0508001110340c201c1d61001c90101c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 42805759 1106 42804653 42804673
    0x306030b060102010e0a110402090a08070e25080c130b030109060906030f15020904020705010f0c03021801081008060f0103030e09070f0c060b090702030d150305 71
    0x1d8110381c0341c0742c206440c00340c0002d8002d401d02d400000c0c83c0040300d0b40c9000036002c0d00c0713800d030b105401c00c5103407200050390280012820107945880014420513502c001c440c141c254000d4a40003440e12071054270b40409405881f4681d00280040c281d2454010400c0b60602183c0c025404842c440e00004010060001b0512403140548064441840601d14544600c0d41f048249280a01002160907649000b02d0085d4110303040c1041c0504290349450351814001d000700f40b881d004045490501081d203003030350302c6842242c2440c0ba10300304c0925402049001140c0c02d860040841e0b10981004d000403800b44020003d551013030002c105009030f01d40c11441c0084c500800d000800d0301804c404005c3c0060f05030014003d9144009034070b050321502d4454117101001d02281d445294111b10408284142164003000524040a80c0501800f01e40041700710601d20704414030014025030860f000034 = true := by decide +kernel

theorem cover : BRFrame.Cov 42625903 42805759 := by
  have h0 := BRFrame.cov_init 42625903
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42625903 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 42625903 ≤ n) (h2 : n < 42805759) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
