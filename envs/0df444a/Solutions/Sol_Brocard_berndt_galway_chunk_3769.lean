-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3769
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:37:34.201524+00:00
-- url     : https://prove2.me/submissions/92e95a71-a23f-44d0-9751-31af0fa0b303

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 677697841 ≤ n < 677877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 677699091 1250 677697841 677697863
    0x30f07030f08072f0601060302071506030b191b0518030604021309060e0a030c020a0b04240c02030d022a0f01050a12021909060815010509030309030601080a0c050604030f 75
    0x700b41d144c1141e10030302800e02661003642e0f40c1e500c050000d41041106540b042810500b0b0128809140304620680794007071880300303294441844002c01c0c40c00ba2444031f0829503940c98044c07481d40044c40b03945010301c0e5513911540c0d9200002102c0840c500000e1195001c1d9000b0001d00005a45034030405130a83e190307410000364401a400c1c82c00c040c004207400e81d552401404208800e056108448070070050007030314000c0103180d0ba0424044944114801d0b181c0050f901c10000c0c040000c04003029941041382d2a04d078458420f5600000d003010355480078480564804001c8868401d1420030240b290b44441c449100d1039003840300415030ba884003030001410030000058000c070707890003040c840e070210103603202c11500d030627000000c0d11440b0010407c160104e034241500003845446459560b00c58188419600c40b10002100191181d80141c2604c542c54041844541c11585040104500070b041141c01028107900d142000c181c9407010342c00490080e6400c010500105d04541d00c00c2c1d804990158031541 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 677700341 1250 677699091 677699147
    0x603240b042414130b0f090a1a09040929010e0711032d04080f011a1e0a050607050606130c1b030c0c0e040201020c060306010c140708030f07030f0807 66
    0x40d0742500740d0040001050042181c01e03d986d48140988842070081e2030380c6038041d072a05881c036900c0e02310f1150b190580d80100141c0e00c550506412242403244a16035418000301703654810b40c8118910490600303180816001084444e80e940513668114045017017032020038446a44468a03442841160401c00080b0001407121122801d0031144903140080465182ca46820055444040301554820150b017072550002185001e6880300100040c010600c0402d59019544203980010008149038000c99011001909880b0320b0024840d0521410207040039140403c06c1001800c10f46503841045460140d00c900c0303058008007159201000040101c000a1042c501160541c000d81801809035198000000344c11603007941c000d010390701c01d03026100c0210609052000c030380002c4800c036000946807050000881c00e6a4400c1c00882070010680ba801071300c2d01403d034550303480a1402c0100400024040f004e15a20000c01001003219103841141401e192400908560307441d0354007161a56680803881c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 677701591 1250 677700341 677700367
    0x41d0c041128030501050618100c0510090201110d1403090a0203030703050403052b0e0d0f140f03040311060c10060306020901030e030903070603240b042414 69
    0x3401110b000740d600b220300710701d90080d01d80e400e22480052001ca814000041034070b2601c141511408201c1c3d111140c5403540b00d00810060b00c1c06840c4c09e50a1000988503200410801e100c4c05030030940014021407894030343e10004291000340c1005140d0b64000b040d03050f001c3da80c0244003003001c41c0000026a00e985400503800c0c01e16210b004000d41c5444005201805c1503000005401124001c0007a294504000d000c0707891110f41c0406c00100b20858041c2d50380c4a0b90160011141c0020301401300001c1e15204da940080710b15401d00d042d0b4140c650003140840b403240400c03c43d640c0010310790155040901c2c1d50354280cc1c030074041954a02c035220215491000c00402c001101d000070000405008240d540d01b0704500a6100103410b9000a08200c4602440c190000c2207800444000c0d00a140d26403030000102d004125405540502415203130488c4071249812001c20098202500102daa4a1030504030104c40c002c07801e43c1c1140c0002c40421500b0507608244c1c40208411042c0c4a2030b03031a28000101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 677702841 1250 677701591 677701597
    0xc010302030f072f010c11030a091e0b0d020d0513050a030c02180a0f0f09051209310f0e0d0c1718030705041503080c070e15041d0c0411 60
    0x14090442d1040c0c1e0103004d400541201c2c42c821410b456000c0c207200c0e81b00c001030700c034841e119210300451640700381042040f044801091680c0751032205016420340b01c00305c0180d21b030710280101c14029008203680044002500c16581c0280c0c0c4100752118241c2c8607034807a511081041409401e100082c440070040d511a80305d440075044031484509820b29198400c5030007040a0700c0f800c0e4500703141184445c024445486024003960b044030060049034804892002c669210015094201580001d20300310b4040c240d480520441d00320340d183c8a61b0041c1500c51003180d80d5900354908682c28014075804058000c6401c4814a00600d4041c441e280356090034850b207150318010071880007000840d154070070301d0090341c0c0043c82011000c0e41c03d8580d8820800090720b1818000104200d4003a40c100000b032007150081c070649504000741c820659a0742c4a000240104031103015402103005a240164a8903102d0720a420315030034071b0344e040c0d005a5100b050781c0781610381c030540c000c0307507035800101c0800c1210043e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 677704091 1250 677702841 677702897
    0x140a0902130b160b1501020a060b0406030218040501051506030406090201180f050a0f0b03010e040311011811040c050301050f040b03190302070902090f060d021e04080c010302030f07 80
    0x82a0380f940758070142c505055454100740c501000072004250350140c0d001c0c81c800d6081d0b05030300410780c14401f612030700000c0251411841d80140d03503060000c0161517880401802c03200001400c2c4580c0f900d0f0400c2425688000c15008004581c0307011480f0f00d0307070703800c050f20342040e080980065056001d10050b6041000880c8045403050a1500082c44072140500303001950015200c452245075205010f034400040b90060058441091006210000c240400c03a5842402440c01c807138140310740c49007603003140c0b041074594441d00101d00001c010301c4004215501c004200b0f40d070800c805400d0200003085c0307000600030f08e4070510907141d0f902c00598440c0c1090f103170702c08014281d80d40f8030f145010500d402100001c0441c0540503041e40000d05d00c00b076100b504c2c0302c540c0160000700300010721020445c2590008043c0e070035103582407042000f003200b11190451084c90604181e41e40d141460601450b212451040130b04050041017089005210f98408503040231f00d80c100417084c0c00700c440d024070a00740000d00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 677705341 1250 677704091 677704109
    0x5070203010f060b04050a09020c0727020310090513030c03031e150503061e04081c021801021c091e080a08031f050d0b1b0c0c0406140a090213 63
    0x4004c501e118050f00100203ca004540b001c01442d51030b810f0006902030808402803d0f00a40410808074920300114800952100c08001303018210340300500481e00180c414210200c16640c090141d11050300c26a1b8002d8900205187c607041c8079070b80100b6600980b01d0007400c154440410010800034400c60b0b060b05034440c501030044a41e901440c2c60000c07141d00c10903120b4855103001c00c0700c0d0301c0d0104018021600d140744411899035582c40301e070011b92240400a001d500c1c244901c2c1c0045190b0b1002d0098030f5021340c21683d10a40c00000203103442c400403000c50113142d030207032483c0005030403100340c400b280d01c100c84400c5088156a03003516585440d611204003400741c603000724104000100110300c200c212801004280d400380042030051601030107815040400350040c01c02241c0040d4825900500641046522451040d1041c001d5000f00402c85202c3e4403030a1080514a414055503000e000448a018000301c41f040024074215454850312034140d40c00900c620184000089000141070600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 677706591 1250 677705341 677705351
    0x405030d0c060b060715050403050702060c0a0201081b090d0503070b0709060305010e070e090a201c0209061b0c060a0c0510140a020a02010b09040501090c0e090a0305070203010f 78
    0x1406441c10151200840b49503190008100c1c1030b01d440c0341034403503840d045502507499050080d00c1d9401003001400035002d004051090380c0c016501c1c03100420b0300015a00c05054505c14520000d0040c40001e8094001c81c031b104042c044582096400b40c50004508441c10b652400c803e080281c114807410401806501d81401000070040d000010901120031a6804100680c0ea8a0300214080f000303071800c50016003148419800f030700d040031005422208491000030382015890b03c600d03108003d900d60000803030021500500741000c0d540b03c250f10700c11081c070940c603011b0544000b404611418dd1601c0b06051466840b00a51a0402c020a022040640070940d207101401c00580310a9003075900b141e461003103d0414081c288039004d1039000c016400010200b40d11110340403000b94100182e0582159a120803002081d62904075403406140280000180c0004905040c4401d244c141c103c480105042420302c007009800250b80c90344030742c06191580d250001440040d01600d444159800010704007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 677707841 1250 677706591 677706613
    0xf01141204061407090311062a0d02190b0105010f020703062d0b150d14042312160c090507030b03251404290414010e160302040503 58
    0x2c0d602002a000c0c030b5540d114000d945240c02243ca0b004a03000041c6040010100300d205418550094402d8013980a070a03005d40048114408480c00f110360905150350101d15150061a01400046801007910441c0d87d110201c940b81c160403004184511810042d0141810145074070a11002014650090040c03000034001d02c0d070441e1b811a0314003503842c452009281c0484e030428501c0741e54050344c2c002e400300c0080d902288d0740322510340000c42e101c000540c4501040e640390059450030b520480c40782c014540070740c0c60703a4890391180204c3c203e554500d50049407184102c210000a031412003410074403071030580040707181860f0300c0c0900d2790211100500b400300340103c40e038044c2c21080c50848140c003111107100803080c8515000780300800481029022400a002c007083c520100e111202c801f51000c980b490441000c509210342c1e94881141601d038000c07484d81d191134140140c000991281141c180903505280a00d82c0580c03006e40280064180b622505d425240280c040d20000c001c01010703640c4945031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 677709091 1250 677707841 677707853
    0x1e18090206070f020901060f302d050613090303020d14060306090c21150103080408060a110307080702070305160f33170a061401030b0f01141204 64
    0x80c3d00030491190310001c0c0085040b511403910110783c18403958413000003403030700050050308544c4964039914aaa0059042e0020102c80c042c480c1d04c40203240140740e2a10030100c031791000080b07190382242c4050602d403d024142d0360b002e240400d5400b14a2000035a0202484c1c181c000380f25407150903145504146002c100c1070000c240d207030301c10ba00560603180d255803610365040d00c1e0700203003450550008494070b07503000303189410031120302d201d070b0768000c54042002a00c2c0d00709003001d00740e0040351460700010313003441031030800e00c8a60381080301200c0600092040e0304020005000080000041003601ea0004100c0b80c401c014160003107401c03205650800008001c2201d141c4040c0c002c0c035401c03080368400015240e490701c0c85030a00000d498941d100205900e07688403090103030824440204245034a0007841c000c550300d41d060040c0303112840091803070b00c0c000529803041506900c040c1410303d88012a42d5131340701c1e54a000c8001c0e1092804034807108000c40031070814051488201e000317104030320820041181c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 677710341 1250 677709091 677709113
    0x30111030106021009120f0210051515041409060f0a080c0f030a0f23010f0c0314040c05120123040605060a080d03021b0d09050a1e1809020607 63
    0x2c8590994240000f400000c1c0c0c1a2514028014070010f00c0c1152015800e00c035000030552040315105460f08801000c07281802e07203000341da50240c80303420001000004d24115680b0703680b20102c101240e003881d1600d8221420001e4a52505e801480b40f1000195030340e460b112100d860141c001c0c0812411616001401da5a11428011500400c04103601700518600010b000c0719542d404400711003050b805644170703211300501d45e0713142060704c042d001a540d1009080c0200f440e061980b10340040c2c00c100303002c0007c05503040b4040a50a02d8840d40a010101d20950503160950b04c00307460f40040d07600b108000710f004000807442e040034a40d40b800814801c400996030300d80254001c5070f00b4070054445000b000100c81031031103500015071288044002c101d00030713000b900b255100844003403081e50700b00b0700c114103000750791006a0009508410a01841c41c0c4462850041d0120105580e4860314441010002e42d401e40100708035201108010540c00c90140c00040c1003a601400c40c2da1511018076044903000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 677711591 1250 677710341 677710349
    0x30c0b090601050f030102092404030209040809012a020f0111030406050304150e030a1b150912030204150e13020c030d0606030209010801050108090a080301061d030a020604050910050301110301 85
    0x2250200b43d00c03901d86814000e581d18030343c00610141000c041303003c01c0c0c8027854941d249090030322001d100004c00750f50b840d964944201c0c02144120f58800c07441000601c040e42e004492054841c0c0c40010900e46d6034a102c0c81000e40f80e042da52401070f4520000140d4150a0755410403545110001c1c0201e0220b6109020b10701462054440d10104c1c40110010030036611500402d0070035a1062010401c1c2510884408081e40510000002c5001150719640284175401130180000c545a0300b40404110b0100842000d1030b510785411410039087ca5840c00306900e0440c1c100d4104209101d14040a6486c800f0341d4002100c02c0c0c10855441602411107501c03034108018010f40c0700d2400340c0000d507003070190013207841440b816903402040e83e0a01005440c2044040c24101c1035105072210040040c01d0000110f018022684550580c0006520000404134809036810702a070041400240161244ca090710250f071303400c4840c104190350b0040f0400c640e028035440180e041d801d0600d049910707690100218140c0d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 677712841 1250 677711591 677711599
    0x30a050f0309120312040f140d1e030504030207060507060f020703110f010501030807081803060a0f230106200304030c03021302031504050601050f07050c0102150f01050409030c0b09060105 83
    0x3c0c2540340341090312030052a1807481038840c400700150003d0a040030b100b55180c800d08003100f0081d2080c40d9286010040d0007440040380d0010400013410440c2101f18950640a14080c0b0a92600d942c0c000e407202414410700d4140080494071401300903c607040602c2c81d0131a000210340b9507801e818000d1a481761310803050114001c0c10000b04c203084060103030741d042c1c3c4d40009503039280081d10b540700150f603480049045000502c00403038001c65a8140210382c040d48000c44081090a0666002021202401c101c0c01c1c2940c6d00c0e96100c5601a030004286046a0050a020004440c3c0f180b568015844139154960b05000020f401300412002800d01c80070b5038000c0c3d59102c621143c45007400100d02c801d444080011341c2880107009245030903044a913010006240140c104402c08600604a0700822002c56440c3c03c644400613407960304114481004800350310204840c00d090400055159041c0142da000b070307071540c2c0a00249802481e4016401b40d01003d80051840e011803550b84aa4007070040303900c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 677714091 1250 677712841 677712859
    0xf0601030510080303060d0206071209170123070c05031c0507050306010509120325110102030721140d02130503120a08060a03021008041118040f02030a050f0309 71
    0x9250450b4201809880d0070400035072a54841c0070800c285045541c80c00c0341d101800700b10070310000704041c1c402c41012115031030340d031010f90904030b079268158600f0848111aa00d019030102014101103003000c078030320085240344155101c2c0f020807100301000140140c01880300061031814001c1840788e42c1044003210f481040310740c456030b030b00700c400348000d680690014206100d4200c81e460308810090140c0000340c01c9038505808805482200882c400c4a140c0042d11014010705001c100c0012001c0c0c1c0209101451411810f030365806110742d40c0c4462900995020701c040c80c000d40c0905100a103941c84180c040c2d0316003508401d00380195000302810305450a9040c0005150304000888004000c05005514200440c1c600c003241e0f0a60021b01c03c2e1b80c00b0b024400000701580f00c1c02c01d503030400021a511050286021308250f81d1304010000740c02e002d04120074440d40410450280b490b00243c0c8107201441f8040540002898030094807400352850041d00d1020441d28400402000040310640d01540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 677715341 1250 677714091 677714101
    0xe0609010f06060f051812070816050108010b0f120a1a100918020d11091e03030403080a02010e07080106050a09021e0702010909051501030e0a030e270f06010305 71
    0xd03900700b4454000403507404100c0c40791585c020000f8021191410382458401101d100002c0e55203072800c011155550801301d01885400310500181100501400c142d0501a01c1d101c0002e203150790500c01d1185241001c1002292400d440c011a00b06c00100303a1191410f040c07601c3c1110081564864805001c2c06554000140703042005403441944420744501c031805141000d0b8501b8000d180407006000f41e030820803440d440c078036446a18030400081d103056886034480300034800c2c0840e00c800680c81d008110071810b449941c0001c11901625441507500e0744501e220300c0241e0161404c552554590301a0001c04900840c0551140041307807402c6521200702540d882c07011040f8420028842c00b00b10303850210301440e010403801801958410b14250060310350b1104014102d45081c0c035031724030233141c400d000606580e25000d4000c040c80b0cc80f002d450740051640e800790003952901d1410303024004210b50542c3e50812451241c00c2861640c19501d258500b0036800008080c00b11402c0303020a2410700812 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 677716591 1250 677715341 677715371
    0xa031406031b190b0f040305060f010b0403030c03050f07050d091509050d030212040b0c070537080d2006073e060406110f0a08100302040e060901 64
    0x401203841c801c500b5000358035801d201c00c65401c50380981461840c1440007598032a400000e10751200416101c0c0e490b18110700c0d00f1030400c80060409080340078142c0060140000090031142260382c5420308120301c0703000b450b00382c400307006078400841e020001064031001d0200101d030401d4091225581c03c1d4041d52955081d80d035030f2038039086071400250415014092801d0868501148602074012120101c0121415000c0d591083c6c00c035a00c0b660000c030701d0040f040420041c0c1809440101c0348001401c0314403c0300c4c50148198a8000d0b444460b07088103144c5090b18050000250003090182d84200aa1000240250b40080d461107820411081c1c2210700c16004514503006042e5903a5808803109064188940702c04188009111640200a00391900d0403014028042e044143d0181c04586880d08106040356840d440101e0800002c0046010a00c440741c02c940d888100c6044c1808076854034068004444500e400094100d890900f901c03009450008940d40f18001c810001e010400040c4151 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 677717841 1250 677716591 677716603
    0x406110c090a020d0c031505120f030715050c070b04080912011b1404030c26070609141008160320040e01091808160b280e0703140f01020a03140603 65
    0x84694020900c024004c8d403412203a0b91403d000040101c40791001d4403031989082d5409001b040342d01c0106040c0340c81c2861514061240e100c0c401494084c10003016841d0100d0303d050007000108544d00008100c4c03500e60b6a00d0211402c149520020096552840007061601044268060104400c08a620f0003006c034001102c0660b40e0180d5000e0b846441c0007482050300c10300030b5800d62400c4001075030307a0300c19008010fa94020940ca5071185842d40c5824140650080800c0d412401208034000c210070054115125940140306c00f4100710045145207000c4000b0404039820381c0860011495040407103400d540a4401c0d200c920500001d5a41e0303c4101408460103240c4008513002000d83c0032020841c080c01415000c3d40541460765001c4140e034403082090300440302030714940d040d0b0b04100d400440100382e02c071b8084040c400c00c00c600382110f18425a038402c1d034031000f48130482c142011000c488090004001044049000f90340311200c1410143c054000850840b884100303601c0080c01a00d400560 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 677719091 1250 677717841 677717861
    0x9030f06041209141806030703210e040c0807200a0507090e1c050d020403080a0815030c030c19180b1305040b340201021201050103060602030406110c090a020d0c03 72
    0x1000c1e0580f0840305d21980704030001814036902d4002d580340040072681c02c0c030450005261412103140001d04074040541000035007c4128091850003444440039600a4a4650012110b00300900c841c104501e104000d400f050a030b008440c0a24065102003180020750740c2c00f0b49999213018000410444031441e518012001091510361614181e21040382c040c030300600d89020301d44005841c05882c1d440b04101640108040b00000d4600010048082590740d88246000000c0380035044001345e400000c2d568009001c1c40354800d074541c00f50fa07104c6801e00301000000301020318400c0a051600900403008140400307003a030141d040d00740c03002001c147c0340c81020301c126480b0031003d2a40d1101c080b80c1041c8400daa40c01c05002e10901490b2100e050140200351002020341e00240c5c1d00c86820b8071440312080d060740210305041c00c008090110940210980e03050b00d02500e00f0b11000d0244814107494150b00b822203035001071480d03041c45000c05050700100303000400294144a44480f45200f10121584146 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 677720341 1250 677719091 677719099
    0x6060901090509030f071a010e10060e040b0901060c0302070602370b0a090c0806040206030f070309060501260c03100b01030204080d0309050706170c09030f0604120914 74
    0x200600c92003009078091030b080303502681101d0501c03064002c0e101c1c07075604c184c105840d0208000b0030262400000c50603140901041c05001e4600d09044071699220703100d0340110428001c013a01065030765165580708010248004000c1103465940d00390182226000358011b80041c00b91510214006000048245800031030000d02606ca00c00340074507021001c100b01140b0b1031030302e44800b90000310b1941c134007090103420203020003e05041c00e454045c2008443e68031150040d003200c4100805a6101d1050360303800354000c0402c00855480401c202d00170045000d00a01c920b1516001180803040c3c00c01400031002202610041c40f240105c820303550381140381065a06a12820000d43c000199411600032030406049c0035007410f4881d05214105200e032070b13100c00001d81c2e0380440e0f400e010041100f2001403c2c98200250100c0c00400134442c2c054008001802400c000902c01209403800c01412140c0f900b4101a903507682443d14081c41d445030f4044950001070185c420228070041071400328072040c14010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 677721591 1250 677720341 677720359
    0xf070c150f200a0605010806090f07140603071106011203030e031e0a0c14061b0301030c0905041505041101181d09030f070c0501090b030103031b08091504080f0606 72
    0x3000c5121250b4188a000e903640200e15245000403280c0c00b40c58040c1c090800a000c0c3e920700906818030704900e041c0c0c01101a407020004109000c1c401030f100d005500182e4025a0300d5440090a4400300ca01a80320f00440c41000000a0210400c443e13070b00001384030380d605120102450386642e959000d03051110811403400c54488042010100091901500c24103029520342500d0700c1e0030310b12400b6100c0701700e005c2d08983c041042e0300c442c5070078a04403160b801d10542e0840d411510340c44000250341c028241d81581c0e6002142c280304031040d0300029000013500520491409107440c60b803181140004602040844003c0420f5a13003444541042c3c07071812300c409500f2180d001c00d40c0c4140d0406003004840340800c018055141c2c0c100d0000b05040c5018582c443c8456107020001007502c41954000c486104c800d000500000358405141c01c80c8503103110401d08183ea031424120340e2841a00500703580b280e0f049469514084101000d0400c8071281d4080d00c00d0a0030a111103600c9070740c00c5560175403280c4c101d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 677722841 1250 677721591 677721617
    0x3040209071d06040305061b0301060918020f0705160e09030d1a0405070c1b06050d1a04020d150f080303040b090a0503033102030c060f0f070c150f 65
    0x3406403004514001c400a402c418004404240c0540c050303001514590000c00401c03100c0101220008038208200301c4941c6150f140c03c8d0002d1207407181c2e0081c503164912160805110000c5601a40c000011f11021241d85949510b000d5903550b0b041740c2c004d0030303241050b4000202c00d000320304014422001c0001451420704005040c40061011010401140040648200017902c0720300c0380e140318a40c1629120011041810203601c03210051401d0145640c00400500500e0383c81002e4651007035212801054000d2441021806141c000340351030780062004c10101d03000b1700316800c180110402044c13100d280075101c2490b180341010901034143c00e948100041400140110ba4607035001540e1070a4074146c400d41d5661606551007a9155a01c00031048000c2c90004068180d45120703c0004921a0014045a000c80c2d15103592464040c4904800324840c000d2440110441d981ca10701100041e680d1781c207d28246100c5110340c001d1452500e10303003c6203020103001c0c859101403002c41d42c40300c101043e04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 677724091 1250 677722841 677722847
    0xc1002250c0504090c0902030702030307140a1b020d05010c090510091a0304020d06020c03090f0f01080f090102040e25080705090f0a08030d050105120a08073c0b0c0304020907 77
    0x1800d04548503005d5900000b40f00c0b040c0c1c0301850103000710b58050340d600d003000c90005040a0301901840201d120400030b08901d5608460340d40b4448071404d5500701c0d004c180d4000169056607041025021f54200883c1408095000329035006842045440440510b4011400c45800005014481124071252140e02e42d8100802c080c507440780c80148601d20700c0c0441e603510006c1e60400c43c414400c0b907001060701421131902c9e003220300c80d9410541b030400000443c100024900c0c5000f80040c1100c41805010a043c12341c2901143e0182c0300c1610007104c50700707241d00d4071000b480d807800f00ba404040c0e40e5403040802910859001e40261450390307030340d0b0030010721404000c1c50300c030441c01056001c2600e03000018100c00c20b01c0940815142180c000800b5898102402000d9020074000d030280d0b0421515540050008020346945030f4005000112041d0380d60441c811022200d29030b5041c0c1c0400e0b074090b0b103641c44074000d8400c46600c0f9081002d0580c480303042c540c24030701064a00a502c52100c1b030000e021184 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 677725341 1250 677724091 677724101
    0x1261f0303021009020d050d0801052103030f19110d060e0601020a0821070806091005010c0f0f02030f1b04050712020705010603021f110609210c1002250c0504 70
    0x1c0000c00c0c200c3c0906c0b45036221444e1058006040e404101c0e83c0c001040706180c0543c2c22401a5100e0704c0c140300d5900140d10054403403000601c03c249500d4000c2c0811b030010100301901d2030b0b1900c0100100641410b800b0044410703040320000d40903403404c10b1404104102d03c0e00000b030007184c060700103010740f40e010b07074500d03c040d08000c055140f07043c0501441c040040303440900074010038007a1110722480c2014010700141d02030042201052102614040005907444031506d0b0314250001c2c0e2070501860b541c685840301054003540654140703c0c014805507110004100340350000003103104424007400c02c0c0244802d40c1c2040350f0320000304e0b4041c2c196903080350085d0003c06149100f5400010300030340702d40c0020841860342003003078103801e082c2d91510b05103504659500000b0701018001c211a02d0101c504c0c5648008809a101c440c1e0300030b86e8005210350aa03015900492280300a8482400c642007a0500a410000030090310040580c00d030700d540044059840001500664003803141400d140c20301c03002d0301d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 677726591 1250 677725341 677725343
    0x1b120e0d090506070525080d08010509010b070f050304060f09080715080403020c10051c09170c0709110306040b0907170c040b19030b01090806010e0601261f0303021009 74
    0x101a15080030048002c4c00035006c641c0d1641800c0c0c18006040c00501403811840340310040c00c3c00311038001403001e035450500e13441c1141e040030380443c0d46504500d0584400c4124501c01405440082000301e10a6080a01c1161504080d0780e40c00310030741e0780c00c200c90752450544650140800c0b404c07030804c440b41c0f00348501d584c0b081c06401245c1000010780081040c1e9000e01e000070000130004990740000f030700610003107403591140039020b1108441c03035250f5100c040409003000310400b0303001840600404003400b0340c000a10b0307040400c0040a540c00d6418055520440d00715105903d80220902d4070300e0004031090045a40350f1700d00502100b56000f01d89402d0000e0210506c041007030000003202d92200004202016081011060000507404080d00b6159030501681c180b00f440c400611181b10000341950449034000c1c0d842c220340d1100c00050742c2100600d0411188a9102038a0781000051951124081e038901c0c44c9008c4404501c6000401e561182e0200900581004010701c6a13100130390001c103055 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 677727841 1250 677726591 677726593
    0x15151801120e0a05061b0a12020d0908040e04120302040e0a0b0102190609120e13050a02040306090f02031005090d0815090115080915010e04061b120e0d0905060705 72
    0x10000d01c0d0303000b03032500d100b4650495065200b142000f1061103c0b42c25020301040402040d0305201c45084003901c0c588914001120081d40419400303801039242c1c000c0e440190300007034000daa07140c0340d690760006040b04071b40654004500300b0342c0b02000b80c424401c40701110f01d804021001c130340725007554401800900e5411070440c4981c8034000c1c400c5440041c20071500c0d220780c50000700c01c01d00e8940014480d1080140700d0500a0240181c403480d01c0b0402c2c191070f1000058000103560341c070140e00da0000e026581000e088185441c00300d008200c160350107290b105000300c1c2100d41c00140c544e80f03017095038022150b23211b10b030b0051100d604082d130099907401d4004102c0305032203404012000228910030390076404096441d800344091400680c2107001c07290840b108038058514800c00d803282403002601803140800d0003014800050a02a507070b440b07103803202e5600c02001104000b102c0e00425900c20394102c051000d1402c0308030070700004002400842c14540b915040341c40d0b480c0c6000c100031074002c0f00050300e003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 677729091 1250 677727841 677727851
    0x120915051c020d3303022209030e0319031d0f030102071b06080105090c030726060102070b0403150b060d06060201050106300c03141515180112 63
    0x204500380080d060802c0224400100340342d030078000301e08400200c0c0180f13440c1c80030030303851451807100030400200742ca406603214010328400c0d03040060742c800b0820910800e5841d0055480415912950001e8103890481c11a4074152041c1c41070541001203070002000f10340324103100c40d04100a11101c0e14651001021402515054000f013400d9920461003142d0f40403a110104c40e80c0b1f844a80402e015000390b00c0e0043d10f40d81400046180f8074005420740e001403101000013506944503214003840090516080d80b07600382a1034240001c80003c3e55110b0150141040c0454100000d07000d582c01c8036005007038442030030a6210030f00b0003440200d03802c40d00400100301850311204140921002042141d00004256151010050514900401c00c68900c06150800701e00700d101d070b03401443c0c0143e61384800035120385c0880f4180e0013007241440a1074403201101c104181e13800142100000010165800882403030f02480342019031161a42d1202d01500b0a200015a54030500000c0d90290000700c1c0054 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 677730341 1250 677729091 677729137
    0x6170703030e1924080411240a020706090501050a02120a0c0b04081312030e040e101505030115180203040813030f1407080705010e150a080412091505 66
    0x44141c429080940002c00084c40b4414420218200325000c4201d854507105509160395410f00b0180e1048444c5d1051520606800440c564084450054040c0c0080349a540482042c003944030180c2d0720402000c503600600028855000f03108171141c0d140d80d42c0c05000f08540406141c030b0107030040c24864042240807018400050303104c04510303010701d006220f4903448000042600c40440000e401605003c060f00007000d0000f60005100808100c0889000c9008200ca0305800e00c0d04180f0008505154201800c5410304001044410207851042e0024412400951400707416091548640310080c101106512a5003140d075000d99009441038411307030301e0102a10307109107121800360015071b40ba20585010504208120341d01da2450210903014102c000c1c43d201c546a103a060610510381406100800341d6599031b6652001d0300c0382040c00304a1912443d00030f0005000400c2190219031280110105c0d10001c0d01079103001088507845055580b884142150480b050b812541044400e88503e90181d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 677731591 1250 677730341 677730379
    0x705060c07080c0a23130f02130b030601050708130b04060518010915110109020d14060903070818130f0b0a09180b10030b010e01060306170703030e 65
    0x900c0060100030000c4608080792281050180c42109209032101801041165007401074500440c42110741c00f032242000e4404114044000601021700c1c03498224207000d0602a507010b80390041e18582102240380d00c4600124161200307807449030120f1405e01200c1c0000f0240c00040c0709400862100802d4195180b100c01000d40003070300b114011880119008800e2403520f80005440002460481c901e5441c01800c0100f45040f0a50241048084c0e0840300f941c2d0400d4201c02e6419501031700f0f01c800d52025051841e08401d1100f40e88926000380d40100d4415030700041918140e41c0c210242c189031644030030324000718400300c00d010760b08611310820f1480094503500c502d07101030890020104c1e0320b50000f002c100812000b900200c48040c40c2c44040703c0a50800c04100c000c20380d1003002e250141d02c0c0e0b012204900c4c2c546500c01495071140c1e20020594800e0103469a049a0b00307030b10240003464032565000b1071110f40404103480c43d4404902000800d00c40c0b842d400181d500a0541088030701440100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 677732841 1250 677731591 677731597
    0x220e010b030a0b0103021c0b030106171b090f01060f0e030a0606080d0507081204081204080406080f1315061d180f0312220b0603100b030706030509070506 68
    0x200029038804010054190a14003920340c44010174a0210720b400e480c908948071400e5103c800e0b940a0f0380c0c55a16013042e441c25440180500410303420f950b8198147c25000b9600c105940c00301e1040e0030ba900b15070800d8142804c030203000e07000302000c1e01d029a08100b412204c100441155400304806401124071a480511440190307a002c0c81020841500b812411807038540300064610400008004072400b00d161f00013680d03401c1d41d0101c0501825103580c2031861242c01102942407680c01584e09100c104041c0c60020402c4a0154803403c2059a0f411034001c2080390460700030345500060380300f45001401d0703441401400030030080000b5881d91111a035108101c40341200d840b41314480400e0042c0f0f21368a00f0030b01c0202e010100149030118203080440d0312409002e100016004a040205404005905103065441c2e50340685075291600f40c2028a452a0b00340c030380c00d003c0d0003140d8041046150340e005650340c40030098010304103c3c0c5082d0044005000013405030007207002d00c0c003020640d47d94070801 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 677734091 1250 677732841 677732849
    0xa231f03050405010605030d0c150f23010506070c1710050106020d0e0a030c0e07030b03060a020d050615041a0910050702030f030c06131a040b0901110f220e01 70
    0x80000c0c1403030305190103400c441710341d00a540f0940c4000c6071b0100d00d81d48090f038010f045500118003285201000c410314082d02c00e00c036204042a0920b03424140b4980300d40b00c2c0c500081c40649451185990f14030a0010500c212080501410302c0030109000071502d100341c2c100143e007484110755825410200002c00c0311403c1e00040010b800003250011402e0788290300c05804141200c40d20102c524640d561036001c0e99500c20300d041208040700151615000764804c0c81304200140548042d450312a0714000254400007010701920f04d0b100200b1043c1c00c00016a5840c80b540385422032509041400326a50140c0545c41407110702401c2010701003c1d2955480180c03070350440c1d1902d9032501c415204250400320300c1c286415050f4400e100c030703082d00d200001d00350740c0201107907140c0c10340320080d4204192a4408101150a80d410b031905000c1001280c814032403003406028000c022110581a164180c0d22480c0300140c02e40e43e007404054000341d41781681406400640040c500382035541c421550120b2000d80c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 677735341 1250 677734091 677734097
    0x204060311030706021b0409140307080406080a0c0c02040b2121070f030f030f0e1c020a0f021905100e030c0f1807090f090603110a231f 60
    0x1c0d010000381030400500380900081d0000d4020b51200040d10741e10a070f01d070003c45100315280c400b01d00c240035550101601d0210b030b18050301e554200d24104483c1c80d62261140301c00248107400050300712a007a218030f0507400342950702c1640140203a000c01c0050b200754411a640030310040d40002c00f6100000d000c1610311406400741000d03061402d4043c0c1103810400002e410702000700720800c0000c45000e108000241e00d42001f00242040d11011801819240a4858081d01d0301e448115031103000a09003d403914080d5000d0302e96018003104070380316800305030300920701c0c80c1160550b00145007401d5400707106e2030303040003107240203076203600164260101c00c4054010695028040909040c140300c000b003c100203840c6448071200d40d4020a00e40c0c0720307540100640d501030b080400c080d1846500800020801080c010184c00e0301c905581c0000d0441780b001322607a0504c0144080141403c0d5680402c50320360b4985460540c1840c1000041441203031006075110214036041a1241c1c21022400d00d00348003a5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 677736591 1250 677735341 677735363
    0x90819080711031e01140a02130314010902181b0406230d0603230105040804050d020f040507090504061521020f03011403011a0f011b050f0303090607030b012a02040603 74
    0x3d1b00030301d84107901400303800e80315004101c074108400c014022041100d90041414004220090080d0300609802100940c400b1702d03450141c0b4500311640c8854010060166001550b0b410052030f88100c1c440d9100740d502264085407034240c105c0012481c071102096040d5500e1400c0c1c0c482e101281141c1060b04102d8a80402e0903800800c007030741c8008507403048409c0d002004207042c00e44541c0c1c1d280c012407007007501c02c5101c0c1c07441c00115100e250503a4201000600300340a2070910f00d03000780c14042036000d00c0380668500180081c1e010f0314801803410400d01a200c0c4d42060841c40d8114904007090004040416001c00c4015114100c40f0000d40c024018a03040c162200c4890040609440c8a40b00040c1e02c10441d10300d4002554401402c000b820300c0900380110402c00843c2c001e0840790403070324098024000d1707144400c11040084011449020340c54103a490f155214a029022140d200400b540020b50070b911291058171100c18110242c170704070f488008518040d80c0000d094a8554204503050f105507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 677737841 1250 677736591 677736611
    0xe06090d210e1305130b0f01210c12020303040b03160f02060402130e010608010f05070917060f151e01030b0f010c080721090819080711031e01 63
    0x580340303006614020b480d00b48060540c000000d905038070180842c049a50342d8101142d12681e031610b80440b11540a5180318103890314910300d0204450034030802207113112400011071592030075605101c185a00c810140e003d68200f40d4101211f071011002203030117110402000c5145210320010f103209100700b8503064801d42c82400000c0c00301c040c0100482c25903020b403091000581d5098900195002c40a00024021101c0c00300c640c05010598040c60303195203014180701e00002c1e20341009128891301c0d00c588d44691f9844035030104003140c0714401010b982151010410103401c500220343c0140c590031103041d00d0b080100004050121b40d100441c00b4071151410240e4550b01130241100340034040300c18188000d8404006001880290001401c54800140302c104204c40803c01000c0c1e001460f5110f10b10020801c00602112102c2c000c13545240f080864001407006031138a8002080e50007050075041c601d140d03940444003054554801d0b4136000700c1c07800b5a9900801201115003058400c000700300701e124 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 677739091 1250 677737841 677737883
    0x60a0506150c0619020d090809040b0f090115200313150c0201030908040b040e040c0e04080a0509010c0b10180612030f03090b2809120e06090d 63
    0x30600c0c044410020038404000d402c4800f10b4555841808a04208400701c0900300e86402071280542d1364139010320b480c0c140c0b0280000c2c04090300088006a030f040001041c000e08120480d140008016440440000107020511071440c000c0700900135402c0400440008220351200040c41507a003203280c0d80081000c0344103120316290800204500c0c101012403411016008200c0300a1800c0641031549074201c1c01c042085d6281201c005140304125581c40c0d50311010404122401950250b560b036441b25030202d144101c00100d240282c1e0301150300d0b841d154081c9000c3e00e854112055060510008000c8500400c85168103148104c03102d501c40745005c0d05100518841b924030010419025107091024050b00c8030892400c0c0205801d03003050402d86107541021005030061090081240d00c40c1000e028200792450b10740002d00300d02070f01d00e05c21111420b800004860020350b010f000f128120345d24114060060700d1140c603850010f06580d01d4040c409000c41e82207100d06004031041041050003040d0480 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 677740341 1250 677739091 677739109
    0x1605010522090c0e0109031e0f1502042603042313021306031407140409020f0702270606030910090f060606140331110108010b070206030c0a0e03060a0506 68
    0x4d42428909401802c1d034071110381c80d000c0340c181420b9a10002080c0414800c140b030ba4031650b2607024249140203d0b641b51054007941243c4100008102c1100004103c9660300c90364281c0710308c0d05030046040a217000c0c8803a0301c800741c90b100340950000080c0031240a0300e800c0803000141d800c0850243c1e6800304d01500b500f0000c00b0341d0110742010310b401c1c4000c190b80c085a0700a40c022900740f41203020030300810b06010700d510950b44140039261001444011407042070b0082d103126402101c0300100004107540d0103005540b584c0e4060f8844440400142c110b16040c4043d5070848044e50844011442001d40300b403c4070400402030320300040c0017658a04101040c010000900030380d14012b000787c040380c45807030b610307001c064449031513002a003241d0f02141000206407061401e00c561407211190190130700d100d03c14103036210240081e45101c00840c1118028040703803420f40e405040300b85075581300066041e40d5007104461800b0000e2600c525107540d0780c10801e03d405a02540300c00185400d0400070840040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 677741591 1250 677740341 677740367
    0x20c040b06040308190e0301020f1801030e0703141b0607030f090f0f081b060322020603041406060109050f190b0304051c0206100e06010e1306080c031605010522090c 73
    0x2307070040107600c08194243d02501c50005840559003403103c00c0c6001a0090845014400d000b84a143c03c00000e0240c680c0354103050400800654400c20790307a61701780003040d10b504200c1360080350400c030510000c0d00c01da0700440c1289440c84d00d0240036888455055142a040e405100841d020720000c0c00300e103101b4001818050030150304400200792610110b0220302000b0400360382412124124400300071514106007820364000c08a50362071504e441d100003074130303000d40c0d001000b8840c0c40c0c00100694003074000a03096a800030624894140c1003020880d4140305070f44103941c0c42030a18400a405100480914001c0b4410405810f90001070144d40640034021031a000841d440082070290160741540c0a00548120400c161a1035a03290010f903051200d00c20301c0c94000280b008982900111036200340d0a403481401650b109000b8001007542e26005052000c07144491114100b0881d130240005151400c00811318204840702929800c19807400c55100c0401d1548840c3e403c2d0b440c5a225030240724007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 677742841 1250 677741591 677741593
    0x18060c04091406010e2803060f0b01021216140a03020f0f0a020a09050711060c0c0705031218030a080403080d0b120618010f1821020c040b06040308190e03 68
    0x10720f49800020400c0700c244c1c1e2000c2c020008050200c0105075420045c903603811010904c8031046070f803407038120020802e034403d44001d1894215400f5881d8400b003000314020b4544800c0300d0414100f0140781d50800c0c24800c04488400c3e00d10442d0688001c00e01c920405c50340280c0103049810341e545029030074000400e0701228603800940000006944009080b0151026440002402c0d51603286c2a9001c14000050390641c2c0f144908114600c2d03050750060402c00030502c1606c481c075940c0e0f81030581e035907030064002c442c0e03c102380a40403045290191240350110006e04540343c07000652220485a1b00c903800a03180c9138000988910710002038003494146400c10b648074404403040a005a440d11800381003100d003480c00d03411120302490250850205540004410891030f000c83c1941407070100050b0003201d5400e800511201500c400041c94601c81c0895000b400c911251401044001c8c41034404190780064148000302c003060086028040024080c0004007498519110180c0000500c000403407107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 677744091 1250 677742841 677742881
    0x3020102060c030714180303160210050703020a060b0a051003020406170403050a0c260403020310090b010e0c160b06010e041b030b0d051603110904110918060c0409 72
    0x15039010306040c05d00a070a0081036220610303101440c04101543c084550b15101c081902103428040d42840840d061089480c10354005010500342ca190041032000b502603001240c0800224106411110841500802c60090942c60700009034490303444100307500000f5408607040c003102da0071240f41c0c00b8400407100000003a103480c2e0307401042031043c079007500d003004000c10304401049a140c54510320300300d80e0a100c1d03040807a22403070100fa64100e0700c4141d100e4810000b00c0d41c04850305124418045400810340f09440e8200f0140c59051580604214406030042021202c8840801002c0244600c2066100031380d0030320b103000415188143d0100e9101c0e03031800440b11000c069104008603503040c90b040200f02c6d8410000061112614880060402d0260a0f2526000442d03100003034141d17445800c285507c402d085042c400040000c980041243c2000085141c240c6002191580c1c45040c28281c6102601000c845504000c804e641030840e681021409103c0c0c50654000c498554180c00c0c80096 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 677745341 1250 677744091 677744101
    0x206071b0804150e060307020109021311040e09150a020903011409060712020403050d11071e05040504080d06031101170412080c0d180b01210b070c1b03020102060c03 73
    0x18a4890391103010b0a02003080f0701c4940150090307041107000c0300700038492501d03450601c1c40a8080e01d02c0c40310403481034082c0b0b4401c1000c0a83ca200d2643c0231598085414200350401c40001034030b541c0900424407501c50310041c10480c10448280903c034220715070002d40c4612046080c58207603000c81c1c0300c1180c2d010b80502000301c8418001000d90380030506260650b0503101e540001002845550809020342c000c0581c004a0990080c0382840140d28100c11128490303034598581501d4080280300c1c0e406100000340c1009540780941007140c120303000750b0700d080c0307032841c1d01204000b01e90389030f03000b1a2081542d600e0341c0786030740c0c0007801da0030000c0c004500f42c0c0403441c00e5500c2c00f52240d100005241401401f034045244540700c0d8060365034405480c0000c000801022441c4072501b05c0760350701140d491880071b00210319960300c014803c210000b03c60103010070341d40b5541d4101c030a06000307183d281001419140d00300400c0070411030709000c145079030f62441c403103045000081c1801402010385d050a042002484 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 677746591 1250 677745341 677745353
    0x3021f14061e0108070e0307030b220c05010c0c180902030d0f0215040804030c03031d0612160315170c032a01050d0219030e060702120c03190206071b 66
    0x805000003444c02e084c0642d6180016983c54400150b5141c151003562000b0003044a00320205004d42100700c040ca0007440f003400e8031600d0f00700c1064010400c120302a42042254001c0000c0700501d44074040e0165065102c101e003094a10403003052840d030030b031124454010360038180408030001c100341c42c00d0115041664800b80d61000154045100f461000000600b40081e50f070948000d15072148088001a0b030b64140180341001c1c81031203141d040c0c4102c0c14120207107881011280c81030700703c0260108680d60034024200500c3e5140300042899242c0c5072b01700d002c690f101620310213400310f1004904598040c0216626203010707080810300907885002412555400c441c040c40703203a244544084485400100125400d0158400034071515001080c0801807a00351180c1056041e016a4204000100d00030003550300e05041d98402d025810000d80004040240001440c3d02d0652104503450901880540c1c0b028903116003400c1d0042c3c210300144200180e100d02c1d0414604180042103002555a440350313 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 677747841 1250 677746591 677746639
    0x212090a111e090a0b060c0a0303050c040302010f0f020f12180d11060307110a0609030f020607080a090501090803090d1814121005010b0408070611060402010c03021f1406 75
    0x14420303e140000180703248a240c00281d80308202514480e140e40c010211f95903118200f01080707002c6810030002441c400b6069003500c049079016981c2200303444000400780c3c2e4800d03012920340c02314054501c0159440008000070090075510000290352100890041040d400f90303e49104c0c800e1a5091003d808200e205d8903500020008590980c3d0342c0d01e5003038040d901c0c0031402520140600400203507900f07101441d400981083e009807039482c031040b24a04101d807104421580d40000c00e0000000c99800e2409502100181d4030031400015840c0c0203803504030594004039a0312885502001052140641c041000150007002d2074107110180c0c14600f05030b2000b800581010b00518a8440c1c0d0801c0c400b0401505042c03691a40c000c116552712003200d1500d90f402401007080e50f01c103003000020100d200d06002008000300c040640a5900d071640111096550032600354218480c0d9024440000c07544090b00d458011303601d0b000140304001038003001715440000e0946105242015400d40101c01d91080 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 677749091 1250 677747841 677747899
    0x230a0c0e0a05012f1f051911040b070803070306120c0e0406020702060a0e09060307060915030204150c0c090b03100b060c01020a08040212010501050d060903030212090a11 75
    0x4400071408130100100003a2646090101c070100400c14110498040402c1e90341d1500952059025915141e140b20403e640d4240c4071105c0440400441d00350b550081d40c000e81d480002c084c241c61800c0c1d52083c1d900e41f5500a5801601c500030000140842030760503108181c0204000880f000031685680c139003810b90f2022384100340703102c100304001800308a0305504894405600030230030791312100421001007c11900c108154001d100030b10124005250004280c400c0303854079615074150505000d0b050701c810508074007600c1810340901c802305051b6078510041d089124107544a00900c00941081a4495940d44c00200341074600f101c0400309460200c2c80003c200c000b05404944601c5138400300e80103201d5400c008206520224491190a0b40006c00d80e010354002c40701421082034011009089840078802c9035442505807902c24001011034210308482c1b070180c10018101401150010230413031044079645415000350144004001c418040d003150400288d460b00101e89441e40622281526100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 677750341 1250 677749091 677749097
    0x50910231306020c1503190f020c0607110a020607050102310b12070818030307030b040e06131e061b02010f050c040504090501020415080f070203090102150703230a0c0e0a0501 77
    0x800a1f240d01201c08140d21003448203182002820382d1081c400b00290000400030701c442c06254042400c01e0712a89150007140d000d20064012f0300c0d015800c1013a01ea004103801c4800755002d001c4989030716641c100390b4460400301c0400a40400c1e5413940358801c0715194001ca40008020700c030001610032984042c662010840c100282191901c0c040304480c0f600429103080a888000200118164943c12040740d491003550240031291328180c030580c03100000c45d5001090769248c8240341c08030b019981c11f80c440e041d840340300861414068680000351425014a1500c1d842c0e80322145103129824400c201d003140290904000c0d13401e040f1840c461600c118400c49101d191620074a10034403c0a50440300108800e502402460032005005020120100e404200054002000452a5001000b01c0e03860b000140d000d0410b000500c82a80c1328083c1c09404181010340ea0b450f00a141e01109070500f40d80d400d010105121840c00342840740a0303c0400c8501005c106410600410a403140c2441c5c0050f079034242 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 677751591 1250 677750341 677750347
    0x50405030903010614010207050a1406030c0c0105070804020909031e09130212220305030109020315040507020f0f070303080a0f140a0915020901050910231306020c15 73
    0x828a140366000d04032030141e255103001c8001500e000390115402159100b0380036a1001170369003081200c540c07818800c207003880b21400400d1900d40b80100086a102c40e4038502c10b41403140140000b07003101c80031146000880c481e14103200c154038003600c5141c4e100d00290011440d1542e100d440396042851121001220003021501d09001d64411402401d408440d810440d1102c441481c0c002e4ce580058404010300304010484029688201003030444c0d80350152900392959281400b1340009500013000215101c07030300044884155a24019103002c4d8245034010000c2e0076616034154200780382800428030340c1d40300c0f9008100094008510303a500807084a00002e40486130800700001e803c0d00380c50030411040500400c00d201a99074002c1d1084c0d4040c9911200d0300e002051001e00328401e0100081c04500281f08159951030003a030341d9142c9801d02e2507d040c0d803640182000301c00110f03007400a000480080742204a980d40000c41030b0040504e48000c2905254090104a0483c4c09a130080d4040c4000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 677752841 1250 677751591 677751593
    0x50a0803100b0304050d080601110a0c050f010c030503011e050406060201020307080c0a09060806030a020d0b04060509060f0103080901020f060114030f010216150e0d080703241419030c0509090a03120504 89
    0x20304403140c80440d11800d0f1092112f16190094011410303029151084d444514921065481080c0c201c11841c1e25403103035465a4281500c084002911000080003400d4031032001c07d203600c60b4000c3c0d90080c0a01c1e00007580720b040210300034001d440c00a200d50f0304540c06010106104c1d6021000c00126032043c10200016102c0c000032038141040420042d4204c550703445540108841480540c0c030580c002e0341c1c200600c2e02c07803810150300c6a0003995030450040e00b000051000c681d10301d00030214400140111b50040c040402c9450401d04240d210035041607081c030424405007024800c4080c4401e144000310301d00321403111121244d401d9980c0c0540aa440003644501e4803004e58400081e0038480400ca810030304050000400c8040103c40000019040000030b90302c0d103200e4580607542442c44058420414200b18003406103041190805922000b0813030b1f5001c06c5025175540001a6001c3c0c41c925080500706014450b5403032003e01014401d507c101d15140110754012050232205820800101d40358540e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 677754091 1250 677752841 677752847
    0x60d030815060d05100501170906010e0c070507080f0d0806030a08130305070311010f020615060a0314190c0f05090f01050f030a05070f091a16050a0803100b0304050d080601 76
    0x1e5040929810b03413415040c0140d0300101a1541e04170340c400d80c0d80a05030055211088101c2d441611240540c2d401180140810f120703a1280660000010404504101e43c540700c140c80c0a41c198401082600302100e440726000d828409250700d2215800c0500321418540e011940d280c40d40c0c0400b5002c481c003ca00c540749201500296002141c01004840c0029100e08007202c00468848000340403503079019440c0c2101d400415464841d051601c40807185100c1042441825401000300904061303948000b442460841150503010322800c200b4001e0b20704040740c0040c21140303d40503034400c2c40003201d400f2040039480000c80e948548140d684100014078440141d40e03900540030210030400000c07040100c900720079444136108500721b6443c0c203660443d8a90503580c6141d90301411095104a183e1a09049445002071040f80303502c000e5611282100d0700c80600b025800030044079880030000901c0404c590f4400c6400c080c0c60044e00803440c5081607a81e060342c49006a6a000601c803d52001410b00d0380 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 677755341 1250 677754091 677754097
    0x40c05090306010e07080f01050f010f030e0d08090f150106051602060d020d05010902040b0d0b031905070f08070612090f1e0303050c0c07030222020a05040608060d03081506 76
    0xd0190032140b0958480c800c060320104111030900c000f0341c503100044da114443c0707044241280c0d00585082c0303941d44a200110b0700945400c101c2800c0c1503c520084201900c10443e040321004655540f00c071a00704440c01c5424002c544031016410303030080d005900581d8111441c2c1e41110a107003002c50b070700c40d04003905107000450b210300070350302040c003042d080e0240030743c2c0c0c00405109800d20405c206503a2109030800480c005c5000e2156040802e00c04050711003510b40c40300d100c01c00d00804031080c6c503c81c40009111009980011515500000d10800c50311484041c480081e00036000601720290528800400c4241c420440c80c8419864101c01420720803031412014840c1c0e00a140c9800e0090380d0032010752064500a0708400192402000441c81180707202a998000340d41c4019007071381842c0d0b03001c000f100900c42c00c41f600c3c4103140108892420341180700a06407481c1d42c0e1102a00e031441c0c80c0001e014040014460380c00707001d00002c0c0c0800a075221864541c01800c400c50341c4210102b8101150942c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 677756591 1250 677755341 677755357
    0x1b0c12060c0c010908040609060e0a1a0c03070c1203080a14040303020f19021f09020906040b030f0d09030201030c080f01061b1b03121103070f1e0b07090b0c0c040c05 73
    0x461700041c0030030160342c0013091409907035040d1a032080504801041c480002080e214481540c843c4d07083d004028004540101145040e0000710b90410007241c4601c040c0c45c2807648103000c20324060100310109904200103d920400841003005071001c0007000c2e0400c050700820003400c0540c0091031501401214065551621540c4c0e036410b135240001b103001c1c2d40d510700000080e03460500c100d402c000b1a403880c05000c5000f5800740000706961140d82c21310015100d4003588a515015050071103480020400202c0c40e426001c0d03407069580740c81c1d40000340498a485540000b041850800c1204c0c005d01140003604403130321482c2c680c0301a91805800e03155146500001080000b5400b12059080482040030003502e000340396241480c203a8800546030743c9400c00d14009590414840c03d004681d407000f502c0d00d61402440c0400c10041040d1681d0701361a1551821140c0700a0501441402648040008040c0c5000751480749810b41401031143e03203481d40180c0034850340e128140024654403a0060b91094 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 677757841 1250 677756591 677756603
    0x1b0d020a150222030605160509100306031b050f0904050a0f020f0604080105150a030c03030c020102070e041b06020f07050d1e0b190908030606070303060b1b0c12060c0c0109 76
    0x110f80d01c02c4110643d0f1080c80165001d03820000400c11000d80c049444d400c0001944940f440c2024480900045c2e9040c103103c001419980c49c2c00102144403c811200440e1108040f074401501380030130800e420044070104c5009100d0b240400c00041ca00003540d09085400c204103030032103412440040c891104440e250340e0031a401090008090030150040360164031200950010715040c42c061082400c214400900160707003800c02000464054007e40c446580188141c960380384d220035401c0481c1c0700a89085805007001d07502103207151160f40500015100358070240400c031844001c42c658540b01405028464104c0000b000100400e410300511002d0040300310700103101181c10f100403220000c403003d05001c00f000c100c038030303003d42d180c0b04041c4442c0e44064614115100e5200b40b101075004503104a0034507079582030203e01d400383c8001420700c8001d1044000c1d0070700d00044699040c88952620240551060400c8460120300802e98660294500032a0350311a9051500c40b40035020503c005404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 677759091 1250 677757841 677757877
    0x90b0301090c1e140f01050d0b0a0b0c010507181701241511070b0c0a0c1715220201051c0b0a0e1608060102070f0801021b0d020a1502 59
    0x1c89032400070f5611184004a50030019594600714044d003650801d40d0964003455220802c003880d030084001c0c000c402280755000403081159004030360301c0c4010740c12142034000041200075007103200f406110b900c030f44249402504900f58180c50b201002c260b01a092039203200f4840d40003490025442610640941d0f00c0800003900524250b252145881c05119410840c5020710561140504003040a0391042d03001014100c5c0341ca080c0d0741054001645030300701805130154107000305411403d4032000d40818440161101040d00c00309251900c10780b02c02c4803c00e04941006071528404003c1c0e1500d060004104801e2035661004a0300d500c20790106640f03011180540c40a1220703d94880490b070202903c440c11000c0d124190280f0000c01196442c45040da80070b1400c0c555485601c8031600701d001030044407419900d5000f841e0503074003240c000b00e160ba035003c0b41c400c0030001ca2415000c1e00f1803026010b07120031040814000e44031410550042e00b070f2444001c2e4442c00c071786250304070703002e009247c803150322 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 677760341 1250 677759091 677759099
    0xc0d14010905090c06040e0f13080c070e0130031709060a0b0402070819120c02060910090305030f0601050d021b0606010521090708011b0215060109090b0301090c 71
    0x7005150540315000944540d132811400b60070a001281e041e02d00c1c074040c01c03c03981d030760344803840d002407004000c4007080108100700400580142302a103401c06480001e082614108030540250340c405a1152030300488001d041c0c4103202203070700c10014600c15940c0a100341500760a041d9001e154691503500c94080c081c0421030403000115086004e464208018010010081c04010584c0124040640342c0f220402900c0d02200940400c4480d4400310700380000c0300c50200c48160b0848007540000710141e040501003040140d018044100e00c007601410404c86e03034011f40c800608034040100403e80582111000ca550f603070094054810180040388255581ca58102e410006a24402440040e0707202d0003001c26255070084084d1403055a03a05c0d25076116143c40d1094081c4100c0191078100180070b00080031800e04820700881e8800c0411900700080110001c9009150410340c0080c101070035162010b016544c7c0c3d00000307010441c0c00342c24000c5105440a40060b00404000300010b00c030300d01c4040c0000d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 677761591 1250 677760341 677760359
    0x90f0a0309060f03140609190e0a050f070f2d03030903150509030a03090215030a0902130504030503010b03090f160513020c07120c030f0b06091501080c0d1401 70
    0x82a1a025a03d804a180d40340e07a05406481d0300c1220311628501da5800605a400e00d8801a5400002c07000c81002409450072150111412060461460341050a1100504c101001000500400c46000740b08091422007801e0314000240034100e100384078a41c1410607201c0150a40d80805c5600c0c414907101c5070349141c0030341404003620040702d007210900c4a11411002e030b80304852041c041e0101651412800313500c00c40c02170580540c1282e00008038006140034003a0b480142d0701c6078000142c000781c554158010001d4100b20740748003400c07081c04c0c6000c000c0020343c040241c0741100c1c0f0700001c240d1291200228682880d800c08401c0702140302d00b0b00e80101c07a49940c080c0c2c400700d030130644801b038540c0c5500810100b6840f458008000381e0f032010340c0800c440345c2c80002c18214240103401001c3c0d0103032640d50324048110130300403d4810f0382c445002e2011503d0207a08482c0c21008034072062065208200019100701801480e02800d984003040850b0ba04c1e05581140c4070b200c450b486c84035195030b1184481 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 677762841 1250 677761591 677761607
    0x140f07030606050102030309150a090c090c1b0c090c1419120e031606060b0f0d27020906041b11120304030c1704120f0b06010206070905040203090f0a03 67
    0x15100075092000000d40c55002000b128018200c410244c0f2000d4019820f181c841d071006000001196542c0c005613004c0f4034180907600240c00200f9000c29040a404c40003000000c60110811501085d4051140040c3c3e91001110440e5000d80c00071075040c601190a80f1200c284142c3d0f4491840c000401d19191207248240d118851010348a191304040070320900c038104c503c4014400ca8036441040304d040d0011190074850394292190f90049441915a440040184c10541d140004e07072002184c0300180e44841d0040b031542c12204000703c520851720540b00c520390030844001900401030040030074a5526107800c04041c1d401d90103041c03501007501c03c034002c10010080210940ca806074030601c542c02148007040f82e00035901030b519131000041503250380455518035640c03c00041d01c10803000a0980b600100e0703403907460080c40c445c56842100e00340080080e40007007626045400c0802000500d0750008409416680c0c00e80d40107031a542c921004619241806c18010502d102e51030146040550010702 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 677764091 1250 677762841 677762843
    0xc02030a2a120e0114030106090b0d020910180b1201180e0f07050a080a08190e091303120905070b0c03041a1e0a050301060e0d06090b150a051804140f0703 68
    0xf070178900400601d80e10b01e00d0000b03020340302c00190000d404004a10b0450b0160190030701011005241682c5480058031010000314920003051803041d5900e203100e541c0354041c1c000d0814580e900c0ca011481c19031840030701c1e030500032040d4031100c2e10038403c85c207840c0c0e6021500905007841114007111010841c5503840c81c4e41d00c94244101c003042d8021136119030104d9030280c61940180c000741081400c200d032450410604040004001e080082d03180b2940d40c40360018042c1420012100003080107007002031a021034003282c0303501d290506000c00006100040c0c01c008079240507110940703820709290721a003944240c0d4005400204003100003c2c0781d07464200202042c094040038504d034084412106400c1c0d0040b85105000f084c07080c0010400140102c12900c480d1200612144400c08560743e80c00440d0248881035800c0009202084aa41c2d91049078600b001012604848054034200001e1582202080442320703506001010504200c0ca840c2c401c4941240041550b490002014449a659805100c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 677765341 1250 677764091 677764097
    0x3090d06151d0121060516030f2021100816060e0f060d0c11070504060305071403010b0a0303020c0f1c03030c09080a06020c010c02030a2a120e01 64
    0x40012507007000c5082c0740c09000048a110b503960300e004c070045104024a0090303042c6422001c5001e0001d0002d20031240f013131030b05401550918520b20001000c03242d0141ca85125645000c003d02074804c04182c42a43c0362200c0c80150f030b0b6603004000e041150421040500402c9150b03041403208030549000200e003601c2191040701c600c03514160b440b02c5002c0c03a500c1110080b40c622a02d241480c10144180c9103100c401a10039072411114620280450780c07500c51f0702000404c102d042000a0302e05004203401890304640074001c6030f04503122580c80d611030344039100f62020358103202c590070b4a003034026542d90309001342045c8460347e43e402d001c2d40f9404001c410a101d02100b081d49485881e0290304800707108031400d125150404140c0c0c0550003080c4501103281031003041d60001549040400c80c132980c042c0b05030030143e01d82081e50300310b60070750b41c20030320750000d640040c0000e00c005503012070820761304200400800100c0c2221803c61071414400900608160703043e074003c0031629001f20460109640a907 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 677766591 1250 677765341 677765381
    0x60c0a060506010c0c032d03020a0506060103150b070c0b0c0601140d11120a0b010b1308010e12130503010203010306091208060f060a210501082e090503090d06 70
    0x8011542d00c0131042c0c004000549448080c03003c150094005503400b0041d0408031094400c000803004007400741d0000724010380c009803820081001c1444100d400c5802030900b400010030004080320255184e01030102c0c10000801c1200c01d00102860f488024040d2031402c40d40c503400c0f414069220f0400740924035851211610f03149050178520390840d20242c1001251500242c140200b00c5180d07180d41c4444124401c0010f0000032a0310340744030500801ca40d003540d43c0c1d140943c01901840d03078451303400740c0200e1340342c40c000503031650022800400f01c6484501055440502020f00c0d1000e4606420554056201000100c10400664412943c15010740c0326415401185502103882040c101d03005504503645215201c01ca0a0907000707401d80151500340500305018030000505e05214100c51010300c20748074001045659010300600f4403903030180c2c0002500c0c140125186c14a90441000d0000042d62840d014060140910907203210000050014820380001d00381030010340040040d0398107401d085 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 677767841 1250 677766591 677766601
    0xb01090e010b25020109030209060d050105012c13080702120709050703111c0f06050d0b0f061c150b060d0606090501020c01140d090209341d040209060c0a0605 70
    0x201e00c80c40c10f010760507501d1b04006801c0d07509000080c03c000d460b20780c010031405002400104280680e07400b1700504201649600d400300c0034003174018054000001d81031005070a000c8c58032246881d960640390007a0000d039030b448052021501c00d15208200760005e00030041d000c81e10300c03070640260740512020390303003031001500c1845104407901c903407964440d00a041042410700c2c1c0c2e1031604180807801c07802c0c0000880c140d40701c3c04900409240482120200321140402c240d03d0104195a41c0003241030703400318001242c05c1440303421109105400341c0103a440400404d004100383d0800e4580e80400f42080d61201d100226500113441103000e0704002c00c551081c04980340d44002400b019003081651816502000c01c0300345840c941c0030811050000784c42d0140c15015840341800c050003162441148080c160448044581c030000c01c540d00c401146c200200010007960003001d41c1c1c003000c08a01c05600300d040040003d80240b10b0280d4042d0005c8010481a541110204641c000e040c040c24080c4000c1d510 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 677769091 1250 677767841 677767897
    0x15041412030f0a05070e03010f27080a110304091d010c020f070b0706150308030f0a020a0c02100c0c2706050303040e070203130e01031e020102100b01090e010b 70
    0x30482e10351a80005810002d54100c080d5040141c11a8a42c2020042034a04102007800d41e0f0500101c80801e9444100c0e43d006814907850780002c0c441c24402604440c0d6072607545541c64400c02d0003010401c04200c100c2d855840c410701c1141d00420346850100300c1a85003584020000d13030f0101c034004855280c94010401c00b80045052460905404007030540346080440d212801d801006040d40c0d9245e54039100c035906140542c001001c2d41c042c00f9035079120700d4004010040c0d13140007441c44002500610900d404030350001c3c0e41100c45581140d101d03040d201600800c803029448088042d0ad480f0324000002000308040840c0c8400b03201c00f4000b000808a024401410b0340c090348102c40d0158002c10081046c0035202050030741110061043c4c92402c030403400ca0450a184982103a18000c00b00401001000351101c0242c0006818131480300350480284c002030344078418540101d110b2a00c4009882d0725a1040c0000300c05003003036845103811940c480c1081d480ca41c0003880400070b015800c41c08442c0300c1074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 677770341 1250 677769091 677769097
    0x30615170603070e16021c02010e07080c060703030902040906050c2d030c0a0203041502101b090e0a02040503010f1a0901080a080a03021902011b0504050a090b0315041412 75
    0x1070861a041a102c0e142144041c40d00c00302840114007c506004d403090300407000c160300001d07541d40041120b14038407002034202040d43d400300902d5404003890038510b03140c203802d0314500f90301420002481c160030300128015007088d190060801e80381400b00080c9410741c9001d008801042c0c20903002400000012943d001541d90003048ca01c0000d10008481d040c400c0014900014144142c070305041d0340f142c00c1c2c1040c002030310010b800340c1c100340d18101c2414a68411201d03659503200c20800403944000c0c01420031074440c0030f040d0150380c100f00000c504d0403613a0100d034010400580200915400311113500e004081800d11040c46a0300082c0c500d80b40d2801d01c04030781c1610064409009030301c0b440d50fa09010307a8080d5034a4000d140d02440b12024502007500c5804840c0d426400114000030002d00045000398010f01312414001d080c0300a00280d2240003d071070941d0744540380083d540c13440da40002d182071411800c1d0011454070b0000c1000300320030741c4103410980c120442103078000b01244040c0030980c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 677771591 1250 677770341 677770349
    0x1140c0a17040c0f15080c040b03060f12190501060f0501050d201902070602010203010627030f051501060302160b1e090d09050a06020304031203061517060307 70
    0x2468441c24207141581c5100040d81041c46081d0301c441480d95038401005401a90340141e0b006100b0b0383e0800076880c1c0141c90950320280020300c05c3c1c0740c181031030903151007400f010f4a0140103007450f49044682c2e03152202269046650401101d006a0301c20a0500745000d020208484650038410300040f070f03210644000d02a910140c480ea0303341a108a0072400a1044142d1070f0084111010310310300410b40c071402070611100d40c00c0102c003101006007002e454039005074040307021a0710410040288990082d912141c0001d11181105e1f100c1340030100c076003601c1d001d42010707040804048441c010480f000803810840145484a80e01c1a80c1e1080203400700d015145440c0504004540b0703442c00260740302220f43d8808140710710300c05031790f0168400c43c41e00c04003107400d0329143d8001c144840e10550803008601c010710007120311001003401d212000f500d83c051440000d00590401c0c5541e11160f001c0e421103070140003119100008010405401040c01300328203490101c505540000c10168200070030008169 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 677772841 1250 677771591 677771597
    0x306050a0e0c031f03080c012301050d050c030d0207150206040b0408090102031204140c0d080a030509240103060501050f031e030d090f05330406091401140c0a 70
    0x66610948030a001c0c0d40001c0c401805960440d1501e8080b1080c03503128130103903003c1d010f466261039202c02c8090031205200c0d0620b4140c2c166002c050b0b81000d0300c080041c151a005e40e04406000d4a5161640c41c001442200c2a80350083c0b200600e062640040d0400448850401a9282c0702c82c000d4107a80b68201600c0281c09980e10900103000b05504600400201c0018411a1f10303240301030105050300601a03404840a103030b0354114001c06e44040040c034440400072901c0c407104c00b020b60344200d9a803148000e00401c0c5600c0301e00240310004140124070b000008010015407806030026810541da10900044803528900340000c50242003801e074600d2a240c0290040809e800c2c0c0d07103001061030100c103804440d14881003080404030105400b40b070b41054820310150b00d0540e654605070703040c62a04960f0300d035841c0c0481110881005441a40ca0800e509900c00880316112410040701400483e1000b17010200088400500c5000c158004200c034030244001804688441841160a2048050310000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 677774091 1250 677772841 677772869
    0x50f0c09040c170a140105010f051605010e0d03020706050a020c0307390e06120a030f020705180a050105010e010e090a0b030a030f17060a0b03280c0306050a 69
    0x1400e050b4400041500c2500f84040030012866218044503022a00b40c2e903450744422004003203c0615030180c0c003406090030450310b4203290303010042c220f0146040d100011a864600345083c03200c294004400440304000ba10700300c040388074001c1c02070350243c80c046035618680350001d00ca161052007039071410119a03014516100040e02e40401070706400c6404900402c00103084448103009040d0300380400041c41481c40b10034900000410541070043c002d43c000c0b840f19920780003020003c41e00245ca25030505040c11099103002c4100c1c41c00030260465500000100d124070303504003803807c6840c49016001c1c070600142c1e0b00c4400455a211200217598042040c1610746250751421038040c95110000540004d0040c2800300000e2038500c8501060700410019003260f043c1c603a1000082c000380d66045000324190600c44046540740301184111a1b600c034010001c03070a0380c0060f000000404c17948050b860504008007141c88000c0c080201d00c000400d260440004c0c850030800001ea088408240343d01030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 677775341 1250 677774091 677774107
    0x5010e0402070606090507120f0c051204030c0605100512070b180d0602041e0902031320090405071706010806010504021308031204021203070510020d1d06040204050f0c 74
    0x806500030060880f030243c0c603980c0101e80c1e80902d2007018880d0a80342d8072040000303120302d0100100c550340301c60603107074034181109952001d800400f10f42c00f107030080c24402100e0361503040440740e016030403000412150400051019460207940400190b603411a40080380c10f1410040c550f0300c501380c2c410750110003410710001f80315040d401c04549603071b1006400000181401c2e0703074404c1241c0c0207400603030400113801404c40c04400d410350403001415079540114550300780311010701041612904000d00381070b903002201042d4810b61240f4020040041c150030500c1c2000d183c0240c1314182400303200003503105081d600c40303000d00001d07926048801103400340850307900300340c103100103540700380741d040410b03a02044001100c1404200070b05400fa6041800c0e4042d082030b104100d946c0c01030801e0720103207034000e004200102d040820900c5540d0404440180d0390051140e48070041c2c6284615182c0241342c403640120488030216002e440380d40b08540820850396117036600c01c40881c0a82c0d40200c0341100b8081d001c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 677776591 1250 677775341 677775349
    0xb03041103061b0c0c180a180309030206030604110d0905280b060d201f1d0a080f0102030609060301050f0103080715050c0a11010c170c0d020c0f0c040605010e 70
    0xc454850650180d80d401c51785031010807200b2208a40341c14111401c501040f20702c40d1a032056641300f500f180307060f20042545440007001800d00740800b0f440f0340303130020101384c1a41e62544407100d035101001001d070b198004411050300a212a00c020b50b018061600942202980d510310716210917174210b654411140151101a03001c20002c00b20342d00415112861804a84a400c00d101030302100c4d07420003613001030f0109100134074000c64200041202480780398055680c0050818038190240c24400b030b500ba80800c0000c160144c10b43c0503040c50302a200d1084d204100640007184284070588040c2c070b644d11081d0600d400c84c0c0702203491098a8038414014000030310080f0092141c81d008100b07103c51181c0c08404070044500c1a50b42070f010310000240e40172081d40221004408840ba400200a10545100050101103070180e40f01031a9451100250880302c8480503a403840c1042102151242c1c3e2030358000da500c030440340c20140140f26595000780301c0d01d014003d88090700c8040c0c2d901100d54140c48184 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 677777841 1250 677776591 677776597
    0x90102102306151611010801030201091e26150c031306020706141f08030307050903072102011709100c2c0a090212010302010e120102040b03041103061b 67
    0x1a55101c25840e00b03c000380d25600c0e004d0014081c046030110581641803800300f0040492025190601400c1401000540c1c0c000180d40216510201c04d1080c42003141044150a8055088241c5100d040c45025139440703400c07d548014180c1c00380840d21511800c0b184416080c6c1c00b220b403004885410400103100f000200c1000c60300e03078030070480503082501d107550b80b800303841e402e10300302104030041002c010b030b0a0805003542005070240c1c0e00d103443c0c00f03003403ca4054492000420800c140b200001d00036a03181c4040145e82c1c000c14500034410400c2d000c1520503801c0710140f140c20790000b114050084e179494900c1e10603500624114006150202c0701c840107001600e804005182485541c600014520b034211440801602e061000f487d284003080080000810700c40d0412135449105200f400b0004450901407815281c0909003102800c0015000628000c8030442441c281d5001013400184020040084c4d4016403080c05050740c40610301c400c0c19070f11007049408401e280c2240c4c416604c005148001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 677779091 1250 677777841 677777851
    0x13060212090105090616060c09050d020a090b12030d0218060c0304061d0409061410030302070b0304061d030c0d0503040803061905040e24160f090e04080901021023 72
    0xd01b00000520016801651107000350f96036500c402480b04031660040c904400b0380310440d11503a1034005c03500400c08040103405002d4000380d5407030704400c440e034903a0000200d500710002100e130f95110307800022002e0b40040515981030320740003903021000d10b015020340b50420348100085043c01c0c03811038100c1c1c0c0085c641c08100c04603d00801000f1894441d0300407110312034081c0790b011413401c00120b207000310000c00808590f460303240243d00744002903020a01c0000c5034098000380380c598542d410120028202c00381098440078030900e00541901c000b00c042c0903444405030985030f0821a14200fa200c40c801114000c0c1250410030002d405407401283c8808800382686422140310b880301c0100301140d03801c0d010812140d024031101c4a03e1241e1800005c941403030b90b0000d04d00c1d0b040c1603500c030028220510080d024015145038078441c20307104541c068020a40d05e103100006061a040040d102c0d4031080c905e500501440c070040321180c0e1940582c5000b11000743c15411580004051000300d2807015003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 677780341 1250 677779091 677779099
    0x31d01050904060303030c08150d03050315030105040308070806091b0a02010f0e0703020a0815061e0d0c080d18170304050406260706020d050d140106051306021209010509 75
    0x200580840d115481260044c51190f200000e0f12000d00030081c00e1080020800c0985606c480c88820326511008908440300d9450304015807642c0310300e0440030325152000b528940540c03030f08040006040c2e001c5041c03800b0b1022500c0e418410b45440040c0200204102c5981c4090483c6040311001c1074007020040140c1c00c0d1500c0006203000741422003130700f5206440c00b4038000c0d40c4044c0301403003507180180c041030080120b140100b50850b09206462a170503c014081481002008407454151071310700380f45c14044000500c0c4001304401860080318014050040780354070300c2220710405146001e80003180d400190441103407103c40c03401610300900003040030ba0007503a01080c88001801c0c2c8841c001d00004c4c14200d81e580c0014000e204156040200040180c50564060f607801c22600d40c02080300344001c60b0620306169149140c04900001d800300754050949003540000008146500c60050404254081044030246640d1032049a4694540161b4078803100704014441180d80584014401914064 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 677781591 1250 677780341 677780347
    0x4020a0803130e070c20040e07030b040f1a090706110c0d020f03101d1c05090f15070f02010906030e0c06031f03051b09191109060c28031d0105 63
    0x656590b001014106d000000581e130200c040e200d07842c0c14000e24132600010401000188c0c51a101e40741f490b10082c001400141d10380550301c083c0800d102d101d001ea03000903520b1152074200140302c130341d07680642d03c00d050004043d1040faa420507408201c81c60082401003030b640088502d86c081083c11181021120360520801541c502095158000c0d81d452200d201145082c4071881040360342007855400b00503c00260700e01420030800d030010242c030780500341940c141035488541c0c400701d418110303130903d0850886408a01c58080020803442944071a10130398940b401e40d40e54010a80c141c0c1d201c80c11981c1641c02951a8103105d0070701c0000745500c40d101886250421580400d0544c2440d40c0d40c2040d40e00f81c02c00007010014031a104203034542804280c84150082c03604d2450400c0783d060300c000202840307071500f8901410710041c20a40309003070401042199900e44110b02d1907540c00b035a2603200c80103400e807001c035200701c00f07100007042c441901902c4d01031400c0000c810400b52001d210000c0f0381030000c28 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 677782841 1250 677781591 677781593
    0x3060a0e102409060f0f0312030e012003040c09050c04050904060207173109020d09080307110f0a051203040302240a0e0708071512020f0304020a0803130e070c 70
    0xb40810100804a00030005420b03030a10490806030685604021003004401c84204000f4086215000243d01d0510700003076800b8008a03540c0c05002801c0403900c001201080d40108124a20002d50259110b100d29204580da145004029100d0403521b24049c000c0610003046542041ca00550348144560700041c070703008065480c603c0c0c540d5142841c0d820254045888014540b10030900540b161460211901003810b080608000070018000c40681170303004100c0011400845d0803c95402e0340c03001000392079180200c8010303d10701c1c1c034a108000c14032820303501940c007610114a034142d01d600700d000b400744002401480501c80d4400303401113045114a804882504424110a9860b09403514a0900074207104401380c055a030511080c6490f17400038501002256000145042101d40755500c1b1b0603811886441a2144196041c0314070080e400000d00c13404241401009510039803089074040360031502e504201c2e581e23000b03d2031040d800c030341241c0040c003450b544030101651044241c94144518001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 677784091 1250 677782841 677782901
    0x9010c0210080702100506030c060703021614010e040e0a06111902031308150402101202030108010c0206010b0f181f0201090506160c140c03160503060a0e10 69
    0x4941d42000103409407081c00003990341804030751108a00c200c0700f400203050032000070761160400316075140700740400920317402054028000f94111134000020022748544c4c88402c1c50001201c404103a000038440000d003000ca00d450700c240d01542403903000401544405030348001c0107000c110081360a0328428803c0c130a540010707810303103604c240041e8003a6840700e0000146408044568008100e103070400750f80b104440175581415940180c04840b400807680c040328017a503044800305008003a490000001240d44001500b185504002c82d5003143e0550b81d13180c00402443c01080d8a0040211080102040200b05c041040c1c8070840c0c002d29403000080108040a542d5011108182c00750f511101100107218050054540c0042da00000e00000d840300da03801400c940820304018400340c0000c040100781c12040205070b5402ca0050111080c0a00701c1883c0109403009100c1c1c14131038882c510002e20b108010780150440d6035031510041c4070748206102d00f240980103000c0c0625225004501c20490022 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 677785341 1250 677784091 677784109
    0xc18010b0a0c0f15060510080604050c09043b0d12060902071a01090e0a02060d060806070c0c0b04030f140124061b111507050d051b010b090c09010c02 66
    0x3100e840401428031304c2d5000f80c4280c8000790310070381c452914003061007105904074910641c000d00854000405981360b12114016010703c0a046801c94640f441070a5608000244842c0084000c0861f2403401d4824a049050344080a042405500598681c500302805407110443d04962040082011622503090000700d07005040103079a00301d420005038403a08119003000340504244113051018a160411841d542e1004160003801100000355801c52903500394013200c081c100041c1a5101b60400001c010045019550308ae2120011100c00245060003c0c0440d403c907a4007a081107010130440d102c035454048401101d8031301e95200d4440141201e440094880717010f822400024145040507401000d071020383e500c000e214020240e03120b001c03500c40500e5916200049950020040ca80e0f10218200d0007801001840740c40b841110300c1095030808064000500700410b28940c00240004803400d940c80003500d241c020b11000c01240d80351107444020001c003141030400c40b4034903545902180401f5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 677786591 1250 677785341 677785343
    0x302120f1507032003010501050c01060b03010e041209050a092307030e0d090e041214070309240804080f1b071e0812031b030a0c020c18010b0a0c0f 65
    0x320030700100003485415116040c94146100569030030071114003900d50841c80180030b4070781882808211401d400c502500300101030900011115107950395064030408048042d0380465090019250b140001d0f4442c207000f00032680d000700040051850006d611009050940b80d54142da000c1524941022950140041c080c84131f66070300142e040c105003141403c10000b040088100308580e4810007421030010442904581c20196408d0030382d120b110140c54059051003140413a03040030402c1000d054008161704100ca0425240c0b12011310882c0c1d41c0c1e02503c010b645c1c410040790641000c074003c541c1d460064590517910f022118030b4101a2440c1188071180a032214000b6888000c05000f40340390075020b4802010a501500102070908a11360380398194080500c070f043c500031000900b01400d034210410a00da884602039900e00304481c2003006400032540714009441014030100041c28030f04000d0030722582410601c071059013065480400c2d035100c40440000c0008102c85240415002241d450307940d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 677787841 1250 677786591 677786623
    0x30a0309091b120209041b030b0312071505060f190312050f0d090203011401230306071b05030d020a02071a04050604030f0c08030d09020306100f0302120f 68
    0x4189020081e4060303480c110020412a520888080903454201e80c441058907a031980240e21160030030049401130902e402540c900303030880b0000070300c900d030503602c0341c450540154155014900e2144480019110b0310030024844408a0551402c201007175004a801c100700521041d18281c0c110009140403c02d0030b44608030b40d07040d8900700208204021030000f211a1410040d051030b0030786004840d00e010f803c50302e502c800d44035000d9008558080d031050304404500c2c0c030319031040d5865801c180c0c0c02200f035074008a1140c800a01d00c1d01c0e076150014903035224100741e0744c584d10f10b0b1b13404561038840c0071711100c42117070319210510060b8030141280c00074001c8548140c0c010500b080ca0301d00c044c040d0503103810031618405c1c0200b00c144615143c40e01198182c0e0b400c810420092925032808044841051b884840b10340070204000d500d41c0e01701d0b0172104610b0f000710103d800e00e0315103d0010304407070494414030b010600c1a650400041c1440c280d104078038525071064800501d0b1203001c5505005041c404101c003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 677789091 1250 677787841 677787857
    0x12080a0e030c0309010e100801030f06140a0b040c0c0b010b070f050d020c090f37060801050a060603020301230d0503030127141b07051b0405091605010c0201030209030a03 75
    0x10350b0f2109880903401c101310750031f10b0784404485010f01824018040600104024082c0c0c2040c440c041c0c014540c16801c1042411180c60900c681200500100c001e0034810b6003400a0301042501c0b43c5040d008a98100b0f030114507a928002c0c11611591210302e0455010281c0c0315440c0100f0401d020f001c012400d15009800702c4c20540d070411150403001001803034107180f000c0c144125100c400c0400c07000c10140b0481207640310070600c802c0c2c00c0c0b0b4145288110380e1500f441400320301c0075419000907005004030a4203016403500c4403000d40a89c0001d0045250004604410b4446107000c3c2c200100500c9024229101020303e9454890035640f00341c100020f5812510b848548078820b801e150255040f41c00c004202217600030f000305104a0010b480041c07040702588150811443c040201e03142181c0c44000c4a0160355403000c21810980d01c0d01106204500e000005280c91b440496464286000c46040300740c42c0741040019181454804d00690400d5424002049103440c104168020300e0301940351200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 677790341 1250 677789091 677789107
    0xc0303040e01081e0309040218100f031b02150a02090a03080309060c0f030711070909031e021204060513090509010b030d031b11030d11210412080a0e030c03 69
    0x4640851318040824103440f04402d604580000f0040c1c9010031411580035a9031000d0000d03c0100c050041c0b02c423603024405c1540c1301002c54000301c1d0140030709110f45042c0324003d14000303118000d160f00380c0c844000d40c009182c5101c015500142403507104822020060074152514041045024590001c548904001003807203214041004503542c401039002599140c56003500031180c540c00054448400e1181280d810312514006200d42809001024010404074010303080040100c1c07a665107120000110003114030300c17035101040840305140002c2d122890a440c0807000c86465015001359881c00d114103030040f40c21156405414040c8040e0301c00070540481744801c160412209c07001070f0003410b10384144000d181101240d40c081c0300d107031401e00003a81c1112148240c00c61007407001c03500c4c140745040000b1440c1d8031720001404c00c2402d00490010842c9c1807520540e9000e00580b805468040580d45030320b00d8500c40d001c3d40c4c2d4410224000840c0c100d0407108400d00d1500001c42c2d40c4113640001c0b4800e4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 677791591 1250 677790341 677790343
    0x207090501090504020d1202153d1707180903030c030506090a1a03030301031407090c0e0d02031006090b010e0319030818070303020604061406130e0c0303040e0108 72
    0x240900b8080c80c0400c0b0b5410550700142180d40300a400a0002c140c0c5e8208401c04c0b0b00034400c00c00d070080390f03981e10446072404c42000d601310005400f02109424074028090056080020440080d40340c021b040040a41440014520134410040f51000c504c14034070007040500402c00c030450b81144615000c2040a07040ca00581070755120000c4c1010146410200101a03444220482c0c000c042c40b03900041040305c44075070501c000b1148500c41d815100000c000020089144180d404441c0302c003090f03440060b210314214098403480c00f202c0001070031425026503140b0f8240840c0101c40d100030300300c80c010320420b0144010389030700350310104c0e410f40d0790403601c00596040802071684410403006411407080031107200c40143c080003805410014503c000508141105410321a030400020445119540d2840c00070b607140c2044030110f40e4142008610140c1100d400c89841c00390f0300040c2070f80c1c01d0800f40640c0b0380007007000b00b40303620480c800c800e42840307030361400e000603c0509600503480300c1035818240e040b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 677792841 1250 677791591 677791601
    0x9050a0516090513030c1101021501182d0b010917010605150a02100207030c0206030c0304020112060305250b040801050a0b0f0607080d06050a0e091515010309060e060403020709 78
    0x101c90035545018040000307680310303011b1100c00f54031041640d000d08600300100e280200c4d80c00c407402d050540784008204803445500d40d482104000030203201a0315500c0086101c0c4500d40410411f614040865950031900c640026207020306c185031030001540d0300cdc5c8091308941c0b40000300c0710703c5035518a02130186041c10342034202d0180c460801180382c403940980c0203688075140d4003041d88059010907907204152143e40b031141c8245d002400662a0304000c070030124240d100313407402c0b800b1501d84989a4086c0d40180a040d00716074019002e82202d1540750a408a094184802e048200800520100c0c40303050482c040c0001d07103a01800000c0703514003056288101c4a01c81003a904c80c8616130b5800b94142e41e114100c60f405903001e50b00544500c24401500007030001e42d00820b51007509040041440d640030380c903a601c40e021500850741440408007002008000c16600c1c1081c8488480390845594000d402206007540706220000b94800c0d203086080c01c0500540e0f044005810410041040760414094 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 677794091 1250 677792841 677792851
    0x10801050906060a1b081903050a0504080315010e0a06030b090a060807271406011b0308060f0a170604030f0e010e0d02030c0406060e03010f0b0d0609050a05160905 72
    0x756041c10444000f80c01802501035140801210559081000315040d80c01d4680740c0d444800182c035010310b28003000c2c0b00882c01841c3c00c0001c0c50100010b0030003840e130149900503a045400c0c14915241c602d2041c0940d4480601c2c203041c09451482c44410361035404082c030080505039400034503484040d08000245002405040009042000a00c0700c030300049085810ac5413403141c0603580705c6101041e0780e141c941e82e1100900e610b1400c2d440380d0081da143c2d139180d88144000d90703030244681400c0380c032103c52020a20000d4000b41c0b030b4000181c0b180c14215400918108001c0c0003101c6180d552104616441da403205124554101c0c44c107000400d42c0100f00340174071000900b00300c0c1d070303001c02000020b01c190140e80c4524840e00300c490901095407001d12603d0701c040c10160040c8a60f030f03203c2802901d50313031620804901961a120308000894850310400c7c0e19500c000340300202e8504262103902c0070f0302ea0064203891034025a1007110008000700102c4900c0b80352908080d282910b46001601141d2000f0302c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 677795341 1250 677794091 677794099
    0x130c030b0409020a05010e030a050a0302010c030c210c0e0301050406060e071e050f120a1d2406040b1c02010801052b210c0605010506090a030807150f0b01080105 71
    0x90b00d040160b80c0c0b0704282c0b065078006c0c07800c480100442d00c0001d00e80b00980b24040c00e42d002e111400d0042c1a03041d0840c03400d0b40d02d540c8080c0314101d0b00d65000c4858001c4001502d00040e04007206944449c02a048510300c003c0e03501d4018441d118640020b8210b41c42510b085502c50342d00c00c010003000c0ca010804a0b408034103400c1101022a148656410a6414000d0301003004800208200101c07101c8064501070b503030244400c80c0c00d2401c0307110140100361244010001c1c000c1c0c2c40343d00c48032100002d50102a000c1d6071800c40400031076015581c1003007001804065015403185503820207500d0302040100c243c01440d64400b084059400058689041a0000c3c2e024040d0071036007422001040625440a000b0440c1344040d9881c6070401d46e44ca03541581620044066048040e898640e10000c00d440b071600030310f81041241d0ba201d0400541d031080300d8040d500140205001c00201c2c207640c000e4448207005d480d0104505280400a40c102c40784408400407035a83d4002020302542d0002447d070140000703403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 677796591 1250 677795341 677795351
    0x30c03041d18060a0908130611070b1e03060f15121308030c13080d090314010c0f1107080d0c1202060408180a05150712030207020114090609130c030b04 67
    0x10022640b01c0d0310061000c0d0b401c2c5d0f1079000a200b0422800101c80c02c1603850401030400c40d440d9813000340745000c0c01102050302e2049000c045410050b41040b01d001421941c4603200c00010494042d4140c0c0000b0080e50340140f80341000f00090f215400d016090b440d49004040c1e4071488040d150344098800b514480780c104003085810001141c0c6002c498120003107288298817030404020800d0020b0300c0350804081c50080480340088035810100c4442036910806041e480c0090382d001490803070f4420710b603e200140c04a4100c40d031550140180c040740025090665550980701c5241c2440d2450075051070313000604607181841848043c040146006440e840600803504141e151030340103000740054a0606040303043c86025590f25000d0302d01c01481e0103003803100556800324005003d42c20149040d241c3c124608a4103010510130700c211105281c2c16110008202540034100d0015008050901c0c0c00075000c00040c0e41c0740d41d409125800c1c61006240200d110000198020700ba18500800036000c2e90408d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 677797841 1250 677796591 677796631
    0x721020a0f020607021201110c30090a03050d0c110103050f0103170c0106080d02010b030a05101505090a0f0b04110d1808030702011514031e030c03041d 67
    0x500e040c03901c020b4045502e552226001d000140c0c1005044001e880030b5860300722140d01c0030081d1000303003540e503c280c4255404004150304021542c03800001d1036640c0010141840c0c240301120001d0300400d000940414090344d02c0341e8420f8500a0080c1d001c502042d0100d290508010080501d0b0034500c0c003e10f42030009051041400009070300600004141c074680c11444651004142c0c00e58410004003002886140c1c0c0c0c841c0480c1d01e6034600d10040d4010b5080c44590091414005001c2898541c0600101101003141c2d550200520a0001c807880c280c4140c035001500d90749214603103004032011440011170348288140703001140c240d480342a02a40c2000c10304024807000200b9074003803420484001c9110214a40300381800e400c1d000c4001c00b482004801e200b120f80d4154000703041c4800d500c06c0751080d281c552240d403040d10782c81d10481c0c4c0e164ac0007184285204003004003920b003c96440003164208480c5031411b82c115041908031007080350b5411180c0c216044d100181e2900000c0442480d1190a03030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 677799091 1250 677797841 677797853
    0x5100f031203090311011404110f090f04061d1e0106050618030111040b070606050906210a0507091401120c0e1905010b040302030d0e030c1905060721020a 68
    0x141e1025881415035a500c4030003850b0050303c000c110904044020084d56042000c03070340c58613030142c4007620822606c1d564038002c1d00b041411000c80c0c000042c03c00f1169aa80c203d510702c1404020011180d560300c0d0b502000b070903180400380c05080140500642800d07200303040d403a500a114000c48100d0360707041c500104000e4488100311450040380e00010b603942c0c4000c8004c00d014080030313540304404510001d00002c2e40302c9004003034003200b8030031942400f080d07960340100107180c81c0586e41d113070344260030044000c004814003203009901e0008406803074024015854860600d600d5620401000e621140c81c9106c040b15140c00c00d000d486102c461044285d2152a03201d0340601d2030064501c214641000b0541802c6046900350071499842070912203580c4800080010383c0091008a001c2d11440c0c02d0410010b0150050481c400400f800400b51240b01104100c04114005e89501c90810440703408240751b100c41008110780390007105220103141c4451654000700402c0c6507007a0442d00440806c03000203130 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 677800341 1250 677799091 677799113
    0x70b1b0d0906021b1c020303120a050412050910031d0a03020105190e0d05070c0f091a01020604111c140319050708030f0a1113031509080f0309010b090a05100f03 71
    0x20300c00841c400c5c0f551203840803a141d88101c807080904d80c03040f00c04014108a103504103602c5144601e055881040c91000b05550600895410580c4070260444510140344250321424900034010301d0034415000102190307040400006040c1e0050b51150300700000c440c01d01000304d0308552016010490103908202003625550321034041d201b0071600140d25800d000c400e0100341c015005102010403900d6440c280407000341504003000289d10610281c1449030740c0040303040e6100c4c07604048640244007140c0104100b8002ea100400390380001c510820021030060007035130742d4100301c9070002d5a641018003956a40c40000d0304d800010403004000d00000109510306890708500c004500401076203500c1048070180007240c2c102da0700b003a800700307241a40248148501d01124003500505c0d0f0101342c8414007800f0746094034405883e441040250700c0b81842154001d550141035680001000d0300c200f0001860f40200b580c43c655111744030001e002012644036403410013414240b104180c101d240d0b41d40c1d006815 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 677801591 1250 677800341 677800369
    0x13051c0213051503060106020f1c0c12050d0c031a0d031205130f051b120d0e030709090807110405041509050a14150108010e070b1b0d0906021b 63
    0x240c0c0b41c4011601494021079010704444005041d95040c2da15040002d41e65070200000070b9071403103907a8005d0b503200c20030400035140703401668030540e04100782d8071001409011030074030a081000402101000d40e00a00c0758541220007651302151980320035041c0a4203520410201e4882d0308200441d0b0006a00001000c141d03000040002c02c0c56a90040500000c0e03604000241180400940050030000c000c140700344400150702020300b008401c0010310280300e105c1150b50941e84c0c00703802228040c90045501c46c00540c002421507460a84a41c0400180c6c0d0300202c0890300c403030001c240b60081058014102104003403d9070208003918054a42a0f0a41c402202d1060817641c1d490165041c4041401500e41c0c080c0c2042d202071030107000702022a5107503540e91486416480090002c0380b0104107001e00c2e489000448001c0c2a03042c10120918032035804009150400ca010250b04200c9620a0080804030304041d10ba0040e028034080001e0b0034500b0690000c0301450710740344008066079658200380c0302e81d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 677802841 1250 677801591 677801629
    0x20f19150603020307030809090f0106080a110c01020c070e010603050c0316020312040507090c050412030e03030714011a04181502070c150f02030703051e090613051c02 74
    0x21140300518000e2125030006901030254200100c00d000e54540103105400007038504448aa030340c080e9410080350203004207400942000c0c04035090302039507041074071800f039031107841480c0c440d101d901242281e0011140d1031079074105800400407045259920b50040c050b506050007e1f00d002c80011066101c020070301042c0c0e4503656655121a4400c100ba00c100b620210072030b15290819081840d0380e110703103100e0300c1c1c605420b20140c00b00c5240f003401554116180041001c122110036070301540c40c0105581d541e6010303c0148807000c04035100d05202400382e40c480000040020000205003080d20780580440e0059041100340c00558511801545143d40c200b0500e0300c10240c0e800e4004060b02c0303454805001c0982c60f0b4408070360450051039400324841c040d00c0c0c01c1c0c0011110201030b070300c81c0905100603006c500309020010802c4c640401c815810044d80e03a00c2c03403400b40c000300010b440f9000b401e0b031003101c1180020140b01e5410706002c0781d4070901c800455509444c03107943c00142c2da807484a00200e02 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 677804091 1250 677802841 677802863
    0x20d15050a06021f020f160303060305061003020112021821011a0616020604180209040c020a080a0c020d060608060a1d1027030807021c1b0f060204080706020f19 71
    0x165241c40c0d0107441c503095041d207507400c2c1c29007c0c0c2001006041d0f40e000984e0380b40a11408140c02d9880404401c003120f506031100c801c880000303c101002900320207a51650131000341810708039655020700e54004002c21507118003d40009808444c21900b40c1e00c2c4624075a000d0f4211030300b05036106000c3d02c400544681420112400c5440401c40701d009542c80114404001d40c0701883c03108054001c3c18010300192800c12030000f2a5000700c0c0e032a511040003400d0a4000c01c030089074107124826100d45e050020301040e003440420356900c4212200e6a0050109822210521081203214011800c558100ca5540081150451851a10b581c80800300280c1203540c1c1141126520421542151220103050f1406c043d442c20308000d000890700b1100c1e00010700602c040300e0f610744030240300c041d006520b50f90b0350b0216000c1382c400300c0480f00e000b82e0140e40300c1511040200001e8060300041000c0c120721000743c00d04603e45000130b8a001c0204035034011a80110141c40ac0490341d403644102016081010011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 677805341 1250 677804091 677804107
    0x903020607060b150c06060901030c120501020408030304030804030f020f100b030c1503040b0c040f090f0f0e1b010c0803060d150923060702060a0f020d15050a06021f02 74
    0x4010070700580042d4210b4a0444000149841c8134040c0040030004802d66840c3c2e502c1d8010882951802d0000405190441c2000c1c410086e259106c0318585114500052605e03488400d2649550801c1f10210001040c400400c420580d0000c1001d000310003c0c002040804505098643c844000c0940d0362070341c9035120440c0500399020406a4600807001d0100c0c8625140511828801c0e0300484050710a101000c010580b134140700f4013140c0442d40083c2403185000c6c1082d00d00400b41c101050102480c0e45c84961640c50600c0c0da20441903131811290040c40c1d001000051032030090880040c007418408035864110206030800f0031a83c1c02030782105c1903c0508684d251640b9139443d070008400150340b40142d00c1080040c0c010581c0e849c02e80840b41d010200c4034802213241c1e2408100c60000c01600514042038020031903800c14aa500381995016007807808000c2c0490448a04440003200c68000c80010032960401208400180c500c91019040814248038140c1740c10441c040340340343e010f85c0090041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 677806591 1250 677805341 677805353
    0x512160201090819090605160231050402120c1f0504080610060e0d030f0807140d02040e0906160503040503040e09031c050907030b0a090c0303020d020d0c030903020607 74
    0x1070388036079120402c40d495000d400f107142c090b5010014084003292103031601086c4035000700252151a10242c0e905540e0a203a5401d00c020140f00704204225503c0c1641c0d90700c50422500840240b05120580000c0c0301d2800780100907061180103014074031504804d4242c40b41b6100c41101e0312101c2059079005031105103000c02250365225551003d28035010b404280032240301c03c0c0705a0003c031400c80e41d5142c0c640d460841044540100c3c4000200480d01c46698089840c2c001d9070944d50007039141c100f0003d4100103d0040d2042da000e04010054148d00140500c40d03852500c0500b60048889001405030340342c005580d0840080124100d8140a0080000f03001c00c64104200da004d41500300c0c1c8102c50b400c1c00d00301255250040c025403044141d0307040c4884070f91455445036070321415000c4018a51289507454420b08001c0181043c0701d402d4545844001117400c1d141c1d0080110702c00d900600c10090580c5c1d0003406c041030f69210400700710140740d280000c25441460f6200f62501126081c0c1d58a40c0b82c0340c40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 677807841 1250 677806591 677806601
    0x604050d05030412050610060e01050d0f0e070b070c1706041e02031b03060a0c050405010c0f17030711150402010e01020c030f160906081b12070906050f010512160201 73
    0x5040c601d02c0c080002017000004551076004a040352a14400309454050540303c09103480740942c00600140440101e0300140d030040c010400441000140302c140000c4105d007002007940003940384c80340001c1c0040030000300b03000040c020800740c0c060008140b12820541d4560300080d1024010030600300200e40030203100020500ca141d80102110114402c03107110301903014401c0c240701e02c42c1c0a07038000034135808594000c1d0f40d8900d8403503481500d010304010042d224200d030804141c0d030101d010103400001520b0b00c901c1149080000043c6600c0346040d0000402942013540c0e0010316400410503040400c5104200c1a042a03090814242e440c40b0000100d01c2c150b9924412507041c441c5070f8042c03240810120b003101d0b842018044840c0c2e8a0b84400c0310100341c41c864400c0c004560302400720407034004c041045103942550300030624003000803140e002030b242c441613400a8402e15500c0f18200080d2400b540c03210074110302801c1880c03d12588140c8050303a01030090602c1c0712034410300c201751202032003036010f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 677809091 1250 677807841 677807849
    0x303150b07120e04050708041b0506070803010918150b120a12030b19030b06010201020f0f090f1e040905010e010c03320a1a04110c12090604050d050304 67
    0x2081c0c4074005810000045034448440c00c020840001180b10541014010107100380c0d00c07a160452140c45036950204107514002403c200404480c60201e501d41d1000000d180340340c060b003003098072541440c1d03240c0110380d40b031041c03480200320880700303400010040403051344a4064003030b00054400c0f00001080880c20302c200354620600558000070b080159042c2168807800007540c0c100404500d4809000d0160150400d010318010310400400000c1e08800c0340960000c41071001504001e0b00d18107900702034009200100010401013011386050821000c41c0741d00e041d00b2503402292a03409150341d0b50a41c1801d107442e0040351180461018020250040c06e85503852500800101a8440b0002c0003071105250524003903403490482c41500c5440702c2c01181500124000060a40360403110313000801e400c0c0c441003201002d0a43c0760b54990b490b489000100c1c20144141641d59522103545410441210820401c00006000500c0740f6100e903003d5a05846c41626002824030260178914918044e40e44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 677810341 1250 677809091 677809109
    0x2041a330c01020319050c090603091203010f06021005041101050c010902131d210d0905060f0a150b1e040b0d0b0907020703021302030a0b0a17070501050306030a030315 74
    0x8100d07074200d50550007180b144022400c0080c0c40c43d420710301c02e0240d6100f9252440c14407801d0003540305500e401401940c01001000485071605142021860103800036400fa07003d00d401c01c503042098503010720200c0c40030245040c00708081d1034030b81e455040c030049903a525810480003207412020f01a0960001000c03540050003804201200c90f0380001409456031024034080720a1020198054000761044400302001880d03c04110520340c540c040e504080032450300c59859508000100d2414894a40500048401d0b61400d20b03200100350306542d480101c00c02405d51100041150941950540d123150240c010009801c45031010040480d0165401c008490f0b00300107480d0014001c1a4001203000b07905403411442175542c81c0082e40c540d284c600c1301941054058000490541c40d65004641c0310900000000303d80482d04007207400200541c2040207203200d0035201035036884040040d040141424600580b440c502140800d132100a00d4000030f0a141d25490381040781c0f502511070f040138202441c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 677811591 1250 677810341 677810347
    0x2031314061201030506271b0607150605040c170606030c0d0e030307090e011202010507020a030605040f02090109060503120f0c12091903030c12020c030a0602030402041a33 76
    0x801c19030340381e103001d80d40b103017a17890f898031f07981c008080003a01c003003158107603801a0080300b610100c040c95928080c50102e070301c94400c01c10880013070301c0c150900303110031a884c1c00000c80da4103101c203110032111100002010710181055455500c00070700c1059500038030550b00342d034698407400f54603403890203010001054907050540b03070385202c0f6000001e9441000541d450a400d40d5440142401503c4207000f07a8025506250158025502580c001c0415030300c00f400020241d80e5a455007002c6520584080b00d008070f140c1408410740ca00b88d45070a000d04010802008080d01d02000a959078589140c03101006801180180114a482d402d40300c00d8015003083e00c400312904408208164089110b003407040300301078a240c4840090369519410b803907240c1c8401901040f60b4640c42c0d140030a411070302c0c1c2184984101034801c0e48007400907200c642d1055001680320304240c410801a0b0320411501008204c030740c14084080c4c0d6a1200c007a82c280b03265000300020070b0711043c1d14481081d0020070301001c08000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 677812841 1250 677811591 677811593
    0xf12100b090a0c0909091b0303020d11030306010203071b05030a08120c0301050f040f1506030603060509030307140703020a020a150e040603022206090908040303020d0203131406120103 81
    0x15410040c4003003000c031070704141640c600c0605400c0f0382480c050b600000b02c0c0084180b05031080c2da400101c1441c040c0e41100300b044015400c000103200c0c039800450040e00514103200b000d681210030b201c9400803100c0514158505540001d549004a9101030000301c0340028544600712074030100d001509028082d03420606203802c101104d940600310604041c0b46503000a0000543e0300242d906880005152020084840c4200b1010303116502c8014102640c910700da41003441c0c2445000028005902e010880b1840d50400038102c0c1c00007415400319230820804c00c20001d5105800940c0380c1c6064180c01e494540d5400d0892500580b004025001409514041100ca0100e914901d00741041d5a40f0004140980244002c1d1003851000035040400810600f040b0007101c108007003140b800303041c00a42181d03222800d0056a0050b00c003a500804001014000d00d80d06101c2050b0300c140740e0000b185810f0040420b5000ea0800b4440c412214880141399007895541100b158200c038149102036400e541c50b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 677814091 1250 677812841 677812873
    0x106081c031b050712030605090f0601030f05090105011806080c28080309040c030c120c0201020903011b1416020d0c0801020307081017030414040605030d0804121d0f12 74
    0x4c44081603502c9440b15044a40f40c903c00d02031402a91006090b6036100c2d00c5840700d0028400010f000a410b054852110507200340303081c030a8ac1e102d010041300119195146c5081c861503080c441003010300700c0342403c0e024058104000794035251510f0689045913100050b4594002003120102c1c3d110803520f102c1000131f8068800405070540c103804503030030007640701034030815170807901705200d81800b04500e030fa22400401c00d642d00082c4094101c0c0005403912041c0c0e40000d007199116511f0041d00030702c100144010ba03601c4507030341102a4220450510700140c844005941d04d440c03040c002d01c00c04140c1810410020766030603800080812100075900c1b4108100050800304044949070b401403950000002c20007800c5e00c2100180a10740c002e945030a007407000c4140a62841111150019192030000400ba1010804003080e0740780b03030303441c0c0140c3d08052501107a41920540d84900704100c40120180c12040e50307280c144515001c0310718101080c4048040f60281240c1e85068507940503042044d10541c0c9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 677815341 1250 677814091 677814097
    0x603060a0f031203110a020c0f06042105010507090e0114060702180f06150d02130e040f0b070201051e072003091c0803060126040311010c020106081c031b05 69
    0x100c61307103090165002d0320b103008265000b01076000006038086041c0d02403a060050710402c1107507002d07101c20b180589402c0c1c07201d01144d58180b80035545101e14400400d101c03003885099000300c01032078004038091801401c40c00044060048144240e0303140c40c001c82646c0e58004031150554040c00c4031442c1c130070352210510007200880e170348442038803400c000558601d01118002c0c04110885c002a0920003040d07001c1c0002d41007007000d6032680019070b10118130042c4024811307110b0780c0700c1c038018180d0b82442c1c0784c140806140985810f043d61b0620060054000b181420f0008044440c07420724025511120304403a81443c6510b40d07440c2d15095203201148078000706c0180b094060070384954143ca44541944c0250201c8500040c010b9102440401d81e690b01c10b0000760550001020364140d0381100c0400350390400b4043d036081340426904466094200c4081c00741400f004110700003000340c28035265030161540172079141c5090f24800c5055200d4418000e40c0440c50b808003010b45c6002c600d43d06080a05254 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 677816591 1250 677815341 677815373
    0x705120711010b0a0302060f0702120a1103100b010c030309060b0a060e01110a021305100306020307030606080603160315060f030f0309050d0507030201030b0402091e24090603060a0f03 81
    0x750816402d103d540c20542c0803141182d5000d00002c5c5407610759950b500549d0000c00d000c83c0e00060386154121108020040c0c0000d25000d002e5400c1c031f084c4141c040503c0c0408031110603070308500344120040140e03000284001e010750181004900881e8901d4418018940141055840020f030751022070701550181010075107100a172600d450038084180843d50b11403071a000203501c241c0400749002e107800c664220382c1c0c010844d4601c0e13110958581d80d84e00103903041110f0702c000003603482400b04003269002c01d01a8100c10290040c0201d145c42c0c04c034081c0264928003016010f2000200b2101c00c580340303035000b000203103000340006a1031707500e901d000490640c5100701a4000b40c000000800c0303526114400d120450303070280042015903d50380c01034001c1d011031449603900660a12000255840c0e404140e104000480140900c811800701041002c003000000c412880003a00304448031034403183d04951081c8400c80b1050349a07584c0d100082d034414a0303508910388089400c2d8000040200c0c0b00a1030801c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 677817841 1250 677816591 677816593
    0xc020418030908070b16021c15050402090606040302010c110a05060d0905010e032a0a0c08030c0601150219021512070f02031c0207031101021620010801030b0705120711 74
    0x3503178554100000d80503006074501d05148003440b900042c0707400d00e254080500749040100002026840c0c07089603075840c01c0c1d002003098945081208519290300e0340d0341e00c1070040b14014245402c54000030045103c20200030101da042081c000c80559070792404100030320005150b6903880d001e00020390041d156000f82240e956090142c40307010010040182c40c0d80500140c580300d201d041c080d0317120b031401c00c201103419414002d1829403400708401000362000303419594000c41d034412404400703515080050344040c11003d5000c2075600010340c0480c10450b55000100c420000c01a42d00000701e42003036440c01c4101c0c07487d001800036103003003000b50214441c110680b18031801c9040100260303102d10602103440c2e4408071409e03580c0801c20981d8003421481e4047c1c41c00e4000042c820503d107089038131942c02088404c05601e0071000b0442d032030390300030103001c2070740700380042401500000303840c9220600009082e160315000144032140300e0005d0303400b0000b03810050051400d0081028012050190b003480359 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 677819091 1250 677817841 677817853
    0x31c05090301200304120302090a15081b040902071a040c0e100e01031e120201020306100306080a2a09050402091e070f03060504020c030d0b090405030304030c020418030908 76
    0x4800d0302d454820329806110f00c0582c590341e15170741c1d54070000e00240d10761014145e09000080d815150450701001415180901e2261002820400383c0b82c48030007803507140302d0039246200c601102c2d60002601c086032000f0741c026031240340740e02e400b0822080407104140320008190810050050350f0b600c15084804030700510f041c9454401c1c8003030320340685000e2415005440001000044c019070240e41d806a940e0408503400f40c40c669a451300160003c506070b006039004024403800307250a003c0f81c1481e61141c101003110a19080100e07480c0c400c0900040d00a4440c042032000e042120306001704603941c807181d0340002d26200c1c142c1100504082e00c069002c1c060040c0004c00c031101000c0700c103a14414046c0003007150b5503209000c58550031021401010107440d08000246a11a80040c0020740d40c503201441e00d4503a0740c0000c4d4101d80c03031004214840c0003402c01f8000071503800700c101c81c1c00c503406140601042d141c0e070000c503015040a02001c2003079503105071841c0c20b05502c04001420f41d2000001c0e00c4c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 677820341 1250 677819091 677819111
    0x160906060203160201080402041407080f090c0a0e0c0909010f030b0c030906130203030c030703120b0316090b010e060a030e0d110718061a072a05040b031c05090301 72
    0x6620f0041030000012603075500c86540241d806040c115a002c0d100a201041c2241d9442d4000d0405006850100205404109202800020758151640324050303100a00c20b6220071000210154040d2084064200460010440c1007402d102151a002400340109525581d1210542a14003d500c02511081440320225a0456800d02101d0141c030028004161544813400c044904140c0c04200700d92600c020000c5030b1400b07000340050446a4001d0b1074138045042c44070009002d0310107240c0d04074400d0b08001071400c98080f000419405842c62030f540091194168001a1580800c0e6040540c0c022004954543c0041c5e0680119a00004990654507040c02110095910402520300c80c4041d03080001d040c80400700c001e0480e60b1401c0c0740b82000c81c126945a0410385400d0001841152480c00041c00300c09000240220705207000740001245461490401c00c0da101c1c9485004162282c0e840307080800f0310382d83c1000041d480c00c000c18071418070101030240140203540010441800381d420038050701 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 677821591 1250 677820341 677820343
    0x90f06030603021e01030b03011a030f0c03070b220b0a02192001140301030302060702070e070203030106120905250b1c050709120b060103110a0c02211609060602 71
    0x1504883c0c0c0909410070040402c422288250310300c6400c1d5042540c3d9040140303503a40c00340038818a12000105192261441e101414200b0f031052130704041c0365105032405030b40c0da00c0001d001800c0b02c1c22000710303e80f00d40c00c0007919004064200c981402c48d8010700004100524428000d140c800c805400311200c4a403080d580c21902400e1784000b9180c0500d4150603143c01c6580002c01d0000713a0305240a0a81d40140c122074030070740e0400c0e003007600140d000c501001a0a501041850060004841c09003103520f0708220080d524030050150004203c0d103014441070a41c1c46810a01e20070342c1c4601900c03a000400c4604001c0d41100001204808504c013200150415528003240c15558490309540b041c400c1030503c54010301009010081040414500040c20076051548910454400d030340a0f880c41c20210700040990300542c2d203500010200b0003103080300ea50040c8902c050968150b40036482c540c940719401608500307210711103c560140e032180b0b5140c05144240d200c00c4e00c0700b58200700811a1540412 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 677822841 1250 677821591 677821601
    0x4060f0e0307060e0d0f0c08070503060c03011406190e130606050f0304030c1a06040f0537020d02030108010c02010b0d0305030903040f120209010e0702030418140403090f0603 77
    0x1280d05030704504030500055206070f8032051200c2016103654105411690b0f511ba00105040064410004240341400300030b4050080c0380c005e2100710700074645424042941c0e0060722040c0300f018003039182440c1a21640d00d49000381c03581c6090110f9004600410030001806d8100700f054240e2181031800076014201043d44980e40c00e890080c1c0d0381a061901e00c0010314641d500160068007030004c910320400000b048600030360000000c030b1290b02400d0603d201440180c902e03040c0d1401480b41003a04100070940303064600841c1d070180b28014112094a5007642039200361140c901948140000391516011820360020350403600c3c01002042105c82c001c074102d00700c9190019070b541c0246c8020040c40400d1141c0043c50b082001d50303040c2c0f46083e0743d1780044078822503241d110710390300000d420f1800250714241d0107071401032a942410350f200f4501500001d480e03101c1d50086400f9079400c8411810001c626a10016001802d05001c001500f42420043c1160a05100d45508000c000b1004103040f44a8091 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 677824091 1250 677822841 677822867
    0x130506090108120d020c0f01020a05070303200a121d160b0309030307050a031509230f0109021b0f300901050d0f0f0b030c0301020f0706050919060204060f 68
    0xa41404480742240b406035011804c6e120240c170900d2903071034a5000c20310081c0007242141d00e52035540d90340b42c60082c094841a10301040030f01c0312000101c890180d0b131404c40b07d0382d030000d10742000c0d02802c1000030300c018200445040f0500004040c000010300780054168450494501c00078202603840360301c5041480210f5400025800074804500c5d001c0c00780000c0c00900320380b420040b450201d4141140e000c10555030242c003410f5100c0c0d10b410000c500954081e01d0100c0c1e0203450070403914000004074070040040c4141c0c44156400248044615045203070a1403414441c81517407a200100120030b0743c1e83c10016030480c0206118004510b1140d05080c411030800721000035142030002000054a4507044000d402042072b072220350300c00418840744110101c1035415074000a034000c94200707051404e1490134a4034000d0307104001c0405013500d5081921074441e80250301180070703070310005490b080c910820200704403440c03260f601404014858015105030b4000355128000e80d1000e07601200c1134460307a04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 677825341 1250 677824091 677824123
    0x30702012a2307030c1a190506061303021005040537061b030c0506160e0a030506010b031e0702030c0c0f0603060409061104140f0d2001020705130506090108 69
    0x310f03101c0043d0141a400710074600072102ea840b2041c0100400c03101c104201c400300706486204046000030700c064440c098102c20296202802d2070740b11418900781a0303103400040e00c5400203040111201e17119608481c06424081c202c203011421403008402c1501050080c0b103000703180442010000c04041e19490221902503a030030000d0a00b4400c002601100300348240c0821445032480d80114108100440c041c100700304401e14540700159004001c00440f0100c54410000c41c601080403510001e001b905541d04007002c03d80c0e80d1582c0010707009110b0903d011200c17000380942009006900880901070100180d81640c0008220744101300700c0300300c489076a0358002e00a001084503400c2c15402409540c0c8076840016040c00f00355661b0504d0b820030303400b6046580b841c0040c0c9200c0c0c1401050310682c40c40603203c00792906c1040d510002070350f070841d10300071130780a6a00460403183e10800003a001821701800300b0340744141500300388026243c00c5500c0c0e070148506100003d604480000c442440151640c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 677826591 1250 677825341 677825347
    0xa0e040b042d020904050106172d090a0b0f071413030f020f040e0709060f0e06060a09180204090e0703030206070e03070312050c0607180902030702012a23 68
    0x100344020031151a41075900b075160709002d048115151440394a000e006507031119010340500810088107000024040a000454119000ba1000000b40004d8820180c010000895a00d0283c454a000c100b0a0094060071180c030030320521800146c409402203880d995403421005498101c02d800744541605501aa01903503c100041000c0e05085e543c0d441c4010300c50540200c2d440c1c005801d03103002d01607041070354109100400c90b561117880780c04010b10814544a40c020303d05050200c280030700030401806518001204070409124240940152414168000300d5040c2080120000d4001d40605a5801c1c40d2401400c00c10000080240841f503265004102907076441d1412500c00d59000f000c5a05841464000b000040c440c0802d6900c0000b40d41d02c19403960610340c0740741e1a0150103820041803107942c8081041100351160100250780105801581d40d0311400d074101e004000c03811459081e480281849510611703035175002450760101d40d0322090100040198900301d451003540070300341c0d60010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 677827841 1250 677826591 677826641
    0x19050907050f0d0504080405040f090b0c0a050d020f0406030608011503060e0106080a0602071b030b070c0c1211030c040606050412030e030a050601031a1611030c030a0e040b04 77
    0xe00040180b004140c0c9540e0810030088204800d0b240151001c8440407004103083c01207041510038843c0504071000c003408a210740d40c45070016105c1c094450701110301d0015180c41114003d80444401d01e0185400b10750310307590010004403d81080c010400024107290b00026110301c1401404040303510b00048514581c0395030303100b10081904051541d05552500000210402c003070052240b00c50040c507015984988510781040c1c1440000b1491800980c11001800032407101001a5441140307800e001f0990300032400c064460407955408407908202e02c803004010003a0202880940c648141c00310750b00c0c0e2130700c1020881a030b4210300a01001034010b10080100036171a0a51403101406030404208010414001c40d0411850010030f46040d80100e0040040001840007010010f10444180e400b40c00c08040255150110030606820090000d110070341c140703400e01c100d070301c0c1c9034080b030444c1d90718440780501600070030440100520039490a9048081400c1074010100024101c10600c5012024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 677829091 1250 677827841 677827847
    0x1b0307030c0306120b060a09050912090112050403120f06051c140a031808030406050f0901021c260103030e0d06021c1e09031b051908030619050907 65
    0x20406250101510f682c0e000a040b81c845203a0725925002e00c5110f1940d140c10418480b001803158090120103280c2400c0040e92030000c01c1a0540c06640d2040b6aa20340c00800120b451540c405040044140b40030140000c0503042201461103100c0802c09002c821503c40d0b1183c121000d034850039422500385155644507480c81d0940c40902c0744101200f418803c2c0c862a814a400840340045001c940e079040c0040040c0000d401c0440203104090085103440d00b84803006010340038905172080380300e20108207011182c1c02449501405401c0e0005114410305800c0003d114506071901020090a0f16511034099550324080c136040e0b9425468146580303510b442132202d0040f003c4000d03101c07e130b400d11100249540e002201a1311080301c2c400403030f0a1148911700c42d0382d0100d50454240316403070015402d0010340c0244614030020600a0000340070381d181e04100c1d0034001d80014140320103d0781280300f000c004900e03001c1c43c0201c0e01a155041c180003d8042142062618010b10368824070410005107003600c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 677830341 1250 677829091 677829101
    0x109120f02162c06030d0e061b01021b070e280203040606170115230d050609120418020a0903060e06060f06040f09090809061603081b030703 62
    0x30301441101c070002c52111039420000303140d8010781d071552010741c0c1050500c0c1c061400f1070143c0795940c2c889141801c00500007561621a86c000c1e40030701c5080b035004083c5544a1043d9001c00300f40900c00721200c81800040d0f070007944032810110907004448000c00c0641c00014256060303070071450b040311494548444c1c2c00c262160b140d02c105c00c2d078031a003a0000340520303190001c1e40c0668465640440c40c0c40c1041c030f120402c3c0c0381c2640d401d81642c0c5000d1842d100c220083d002c0300304842600359440207602c00c0d10b100041034401400d01540010301100b04008018002600510810300c05c802d40c0c2450340d64801c00e214038410703807040091303000703000b02080c0b9040c00540c010710a1080c03a040442046645c2c2d680c44c82503800d00403120780d5a0b040841007047d60701301800780d0352000d036049840b1407929040003480d00b5407d000d40101915282ea4a500c0402c1040200854030041030041804d0f807541d807111491000c0c01a0030404a0000c2e4000c40800c20b400009100d40d642e01e021001d215045071358819088000704 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 677831591 1250 677830341 677830367
    0xb0402040e0a0308061e0a0f06030c11060402011d0402160c0503010c1d010918051e190b040f05180c01050f041e0906060302130b0a020601031e0c090b12010912 70
    0x381481c403089020f80d4807c001c030002000d5060b08100340600d00b0310f0107130858244180c2c2d0310520580b280304612114003c03580b254010390901740350001940c0300203140a007444140c10290002d10000348076008505114240042c00c1c03050305800c0c1c2c1c090305c400c10315081e54040b05500b00458842803480b00780b40c00010800025407410b141c500d032020340c0e4032100b52911098540d0795802030340e203c05000c9240c40100303000d103080c02c0f09425207c080c100f803201c5000d03429040d00000345560742c0d006044800d68954100500000b0003c10920032030402e0b482c903078514440d9070a100124071500203201011350040d000d0321030b40030311690b400d801d042c608444141403001c401c0c00e00e00007141d10300002c90300303410903c01c14024200c00d64005850707050040080300300f5a103a4001100d41001071103c21000f60380060540d056030b50080c0100c620076003080c03544c2d24005d010790004002602c07106e03000c40c11417020741c000c0c40300b07030400c5a032801040424070045080744c52200f070151140d4055410440c0c503a00483e201d0f1140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 677832841 1250 677831591 677831629
    0xa021b0106081e0c04020a120b0d0302060711100c0207050102072102100309150e0c0604050a060f020a060f020306010f0519110f1c08010f21020109050d0b0402040e0a030806 76
    0x301da14180010101c0e401f0400000200390003500e01d85140e080351041c2a4807800a03140081552503588001c1c1d0354880080c03100081180655100c41000e40c2401208003c1e1f100e014284080c4001d001d000c0e442c0c0d55140101070040c030850000148080c088500a100300c02c4100000312800070680901c0020b41d81c032a052000d00d91123401e03410001b00c070424996250f1611520002d035001200720910b05110000305000e128040c248010300c002e0341d4010707280e000c581b0142094619103520150582c10b00c500c000d8050416440e02007034298625032500154400c1a09a0362074801d0603180740296814061601428841c0242008540d041409121402401034150040f00d400e0004c0081040c9001064042000500701e00c80d01480f07801d4020740454054411114090300403030a20b00c400403d590400c035606d0854840244042c256400b0303511010180001405080b180b60f0302d420300a081c00415a0120701035480d000e03100342b000c40049280b9400c42e9040e0f913100b40c2c0e40c450908002e02445811186040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 677834091 1250 677832841 677832853
    0x2403040821150405010801140f090106031b031509050c0118050415050f060a0f031a060a081807050d030305041e151104030c06050a020709050a021b0106081e 69
    0x10a1850141e00307104a000032001410964160248401e036101a8400c2078180c0c1040781e611014002c08079425030000e59000318685581d14120054003400340360b803000e0039950510001500c1c114440c1200010340e40a80150040c106120000e282103420110f0701921a03001118012410b622032141d05e4a05001c004d0340141603a2100006021a0b20045114010b00707509a810455030a154901004a0504860541c1400f10308180500009480045c210805581e4001c030500d804e0110b10b22512034902604050300c92640003405130012900795142d40b4043e1150100300a048000030b42076061307407009000c0380e4a182030b56406801810004c2d1081b00c1c2088502180300c041050001d0130451203004924104110456140c00000c6502c00e41304407100c900108414004501480d0620044a549207841e40d56003888000c100d04051090304048103480c282011f01030090341d036401400300c00b82202c00207050140101611030880c0d040740b05210841e004100e458000316685001e4036a40041241aa00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 677835341 1250 677834091 677834137
    0x3040c080a0f020d11121e07050a150c240516050d020903120711090c0304051231080c060c0d0807050c0d0918050402030a0803181b24030408 62
    0x1a1018103e1b14200d056446840340310403590203660030742040d4848501400d0542d0500c13010134264510343c0610070000001f40c0641070f5841c407030005400c1c01ca4102107845d00405c01d441c00b804180e5601144526114205008200c09004080000c0e05940c45038480619000140516201942080c4002641030240240e010314004c400707001041010302c610305040d6258411400c002d9044800342c07050380f001c00240700308000907800003100d2071503585003180f15448003403c1d4810540001000018018110556211540e2074184500401903503010800d452403000d451044c0200c2e8025820034441a92180c124039003502c0c01040d001d50005035a02c1c02d14904085000190710b005001c980102c0002c1c10114100314090103406011001c20340c035401404582030640000c0e0781c1c4d10300e2040180c20a407000000c61100d903800040c2c40c061590701d07801e9411204c080b03031101361109081d03104c0c54080c2c4070840107072601001400310600602101c0e10420b00b561900d444000c600d8000401d803441101c002025a8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 677836591 1250 677835341 677835349
    0x251a060901173714010e06100e0606090d11091501020705040c0504121220030d0b06090a09090203060a0c02060115090b030109020a090b032e050604030803040c080a0f020d11 76
    0x44492800755101d80d0805405415450850314440c1a296103a0402001d0000302d8603044403080c02c032150080d41009e40e4880ba030000d103c2d8401d16a13091760041f285c64150080245100030114948400ca62914899440304400c01901c5041c440c4940140c020081c01e001900c2c0c9580514488a01890140d0809807506110380e8800420709083e64401d0315855144080c1e5884075904c90300006020010740e901c024020216900d0084100006500f44c03907010003819038441c0301c10741b0303000b0314010a201032003591910540000c00b454403040c0e00901400c4001003071401c2900814000d5229540240101c0e8030300303240c40c91461200356041c2d082003550180002d01c514908040c5020701000e8034010fa54208030b1601409442d6254450440c0c00e009004005503090000440389241c52128820318a810700705c0440c6011320815001642d1148001c5004070611102e000954400d510900540401075151113005950700709120b0300900c188544100c90005013080000111038a21a61204000403035500c00a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 677837841 1250 677836591 677836693
    0x6090d0c0510050403141c0e031f092307030b0a02070501020d0605030f06041502090303090a15080f090c040b030a0b0c0c150c251a06090117 62
    0x82c004601031041c4030204480e1141b409a01c3c00600c800160700021040284040d00f110b001e01c00c240101c841d981e00c0038410b48000459440740d02d404c3c0c1e41d084811000410f80c548080d15490808042d0818041070222281c1b5500400300040503c4da02d50f03900c0202c0c82e0802040105495024800a00002c80c240007402401d80014400310303855041809041c6007000c51070180005901900510010800400300e6190101120038050303aa070016502092952081c8401070740c000c1e401e03110028102c098451103854036003081e9180382c016160007c510720403500035110500b80d03801c542c200302c08516103a8000078030140068281c03a020f40ca1501d81020f210300c12200a04001000101e0b40240e500034407002c205802c2206594899081c500094005802016202c2605541038000c00c24034410006074210f0040c1d0180110401400308504058411f506403081c1c1d000d000020000304091034120b00e40382e00d241c1e814004045070072045a0181c00840d08818030000c5c0c600102041e100140e11941d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 677839091 1250 677837841 677837869
    0xa120501030b0412020109200a080f071401020d12091401090c09113415020403020a09052e210c1710200c0a0605090c06090d0c05 57
    0x24015840c030302814a0081200e1340120002103902d0011034800040780f420380741c11002c404e440c0507442003980c1d00c046840b0b141e00d030700310014902c208070007003003003080000d416400c0e0380381c0e030750103000756020032005907075a03c00920603c0120b100c40d00d25201403070321907005800c9a40200504045800510340e518215040f8580a0314070105006040c8207424181c040d10b10b030f5501c00c0c0e1500340380145048010011400041010701050550080d0107001200f841d03001011a40000723490302580e030140d910200075400f41c48200d01074450322200060003040307445818414907240950307210308100e001da00c0e0000d60b1421103d04518510410102d060041075404e200c5454514001c090903118500340060180c0407584009880290301010200d0700c2c0b00801d03030b116800c48110b80400c4020b9111016218100c2c40c9500b035088078400b00e0000303601e200001d590b2030b09070301a100030041c0362074501c04192982c15690070703260454400c02c072a0b5284e08062207115103041c042d4941c0045281c603400020084da0b6142a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 677840341 1250 677839091 677839103
    0x7080a0c1401050915090c04090206091009061403010b041707030605070c020111030406050a0f1e0c0209090607020c0105090a0306050f1909170a0e09010e0106030c030e120a12050103 80
    0x2c000d00d810040100c9111100c2d807100c40f890303a2620002d25a940d841d1240111700239034031010020304545904055602ca000018020364010314000c00080c85840c0c3c80c03142600103840d008040601d0100041183d0581c1d48580b44d4030319003420314100a10943e42d04060103200d10400c2c00c0080402c4080c4501c501030800c0f599842c0c08060107000052070395612508030706c21034100700000c00000741c004085407c2034071030b810b0030344105003115016112206e9446600c84900e1000840702c1c141c42d4842403129842d8401c03070302c41c0f030180c64600c00c0135940c01044445d0000b41c1d010441c80c142542c0642c002e40820380009058034200c613140c0da41d40c025104144c8144d0b03000521a414040e080d02d4100c0c2d1001c51030000c0da401c102c0c8003400d440305041a814095040600c0200085020a01d07100340300d481020070f8060481c10032540c3d100c3d1403643c0f844092041c41e00291416820942592080c0211003c13000340100410222011914200c07860b40025142418400000c0114098281a0103800e000714013070300d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 677841591 1250 677840341 677840351
    0x21503010503010605011d0405100e010305150703150b030c2104030e1008040b041104021209010606021207080c0f1c02070509060d0611360603070507080a0c1401 71
    0xa240c00d48206402c004d061249a6078241903647d030091184150038411500418642c032014400e80c8070140941024151020940001c800d2001c000b80e0b40200c0c071a8035007815040c3e902c2131001c03002c581e28001c02c01c6114612444c2000b405240c4006140c01c0400101020b24000c4410000340c03d907140d8102044c1a84804010442850b80104400400da00107031051001c504107a100102600402031008202c041701e000443c0c00d005104104c141c0050380034208560b03589c000581c40c01040c000322a41421982031000200d01c507407000c5110501c54018481160078030b4101d545180c0d454001c2c845005442c887c4000c0080190002c0150500c05407403440714200c0340c0b0458030001d003440400d4000394050071001c1c090143d02e48940003049512900410300050070341c00c1a405401a200f0010740040b4004c1500d1107110340010b241144400e84c4825841d00303864107484090207564082113912a000c00d80a0241320089010a00101100c04c61840d005001441580d40ca00660071300307601003c5645e540b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 677842841 1250 677841591 677841599
    0x11070603050108190503030c1602060408010f150503030d091506060f09060e10121b050903010b04060e040206070302240103200f0d1703010b070c060309051e0a02150301 74
    0x1841301032051000c0c4500c0f00042903a03500e40b0351b503070f104c080c00c0909280c50024820031403030010342400140c3c43e402041c50387d465542c1c04100d0301030305069180d402c0881c0b810b1904840560b00303c0700c0754121400030300510700302400906500c0040000354000c0c0d4190b58417018581c0d50000d14030990010f490640c403120f060404d02e5034014490301c250f41201c5c00348481105034080942e00c0400d001c1004205207002c218446841480c54054907087c603902d44400d000661030300b140740d0064040c04a00806500030400c40c50a03908120a81e4894452100c0480b20440440c002d814008000c0c001d841c02030044540003001910810082e044414808030381c208074000600410213140515a404c403080c012120212407500b00041d0359200656a661188804090141c01c00c0005101d418102078107502a81c0c5940e0f43d4a91014140d02100b821228542212008a080c13406481049003003500140200140d01c501c0d402e100f001d80c910500740c0e00c14850740c0c42100069481d285040c0060031561140c1e600c039490 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 677844091 1250 677842841 677842843
    0x90308010e130b0408090d061b11120904091e03020c1c021003020d1401080f12041206020f040b030a0c020606030c0102100b0d140a020a05010305060d020904020111070603050108 78
    0xb030422000c0304641e280700e201048188090b15009a0800417456803602c1060000302c05540781d2200500701814000d00189610f8484410325003001e8985132000110030558005845120488c100c032030114060100d511281003603442521501d1160084291100010951841815180b5021401030740322a1140806007040d108008048a00104a075140341c03031580040c42800754220810105940031410050218280c1c019010031700d80400054265612000802e46030f00d0001c4034501d143c45591080030341140101c04442c1294040c50180c01107814942e05e69001e94040c1021503000b440502001c0b4139040d1070401180126101180010b41e440c019070f029040c5480108451721982003001000782591700070541040850f2481c0c0001035251071440042c42d03045071000060b11005480c02c8006000b40d0001c0c4550555008907200100513946a00440c1a10f00445195403c280780e0015500181800f40c0c00a1300a4414107002c1c4640c84400070f010b141c06100e80c000800646c440c80100075140c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 677845341 1250 677844091 677844119
    0x9120703060b040605061b07050d140d080609010911040302060423060a020307140a080a1d0d2004060e0c0a080a020a090312050915030a0c020d08070f030209030109030801 75
    0x81a01c1c21301c010340c900b41c0003803082d02552420124500d56010480061041441000098080200524641031450605003412401d001115425128181c0c01d081101e000300700075480b9203c014004d04c800ea0a02c03114002810240c0e220000d004020711011005030f40b401c02a0000d03003034102801082c0200e410480702240e0340206858007400d810042100c2c56580403080301c4500b9000f076200841d401d181c821003450145030070405800345502080004402d680916104110045d404400b030304810803070100030400d201940e00510003400c409107042e8041d90114014504c007002030001918030713a6a03a081091400131981300d01c0045001800205407500300460300d42201440c002182020713a90b0700080e250034842e01000c3d00030729000840403a824841d2044400d502c41c06400003001a03030300c0501d003c003600f054402c10703045403c000111850620002e41030300d10800310756a12005441d8050142d52036500f0b00900002c150302001903007445d4509000703002d4818441e40e2092000d62600e5171010000c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 677846591 1250 677845341 677845361
    0xd1b06051c0b061803030d020a031b0207050117090f06040302031c02120406050c07050d08100e0f1f0f12030f230a0e19030b060105072301020912070306 67
    0x519001d242c109640300c510581e003541d4415000c0803c058160000a40340d4043c0c0da052420150000800500c0281d0540107220007050392820340042d110001d1041c1d03101c041c83c4c003495002800c0407002e01c1c1c2d42400448119000b908882c00e44401300c0d0500900340c10a64101c4054016901c00110303030124107401e8240b001d662141c04000c50078841035031140a034540000c0c1026000e2354940700822581c548000450700c81130343c45411100b03104d12211000e0300100b803c9404091044c84113400280840c5030a4180d4803440c42c00c01e58541a40c0c480c0043e950200050500004040000310042842c4c00f4043c413074805001000d814110107102031800801c0019001049020400e4402d407504c60b190709101702d10f0760365002c01560741d100c14151100b100c451400f040c5a41d0b00800003190300407406409000d15040e02d00899008016a07144030042d200d501c1140c40081c08000000540f040c01c20b0003035401044502d0000c00580742c0024103002070440c00140d00340010540240c0010800c000d010303c141240c003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 677847841 1250 677846591 677846647
    0xe1f1709031309021806070309030506060d241107050303100b4003060c030f0e030409090804050d0317100501080606030a1b0302042303060103020d1b0605 68
    0x800c9900e400c0b880d4200c80e910800c0201500800d8440c0c46032484610795020640192030240c550b6070f141001801070780c42d03120507500d901902d00070440758180300300c00c90784182d004011110000c1610341100118000d810714550516035840d1251002ca034ac440051000c540900000c5880f8200342d55070f5110304040d03a0010001d000e0400c08000103d0300c400039418886010000d03665007413544030441c015071807000510b00503980071705000300030051982d001e240e550350203075410843d01410012060480c0c0b0307041441102e5034014881049407440340c1d00004c0d0b8542c4608401d41c109617841d4040b40b185140f410085000c24044009242104421524141e006002c4880645594030340000030740b4000d0090001c038015040040000e201d01c1c03c40c0c2240c030700d410344a034038103c1c00c3d009010000c6c02500640640d0b404080d600140e51400c0c004034500842e0040700070068002c0380d10f1582000b07145003068104030340c1e2401075100a000202d0420204000384016115240d40da00107403180315210345400303090604 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 677849091 1250 677847841 677847847
    0x10e071509120b04030f031506050a020c01020c060d09020d050f06010515040f03060c0c14070f06111507021218010e03031e0c0f060412030e0712030e1f170903 70
    0x42040050b0f6290019054180503240308801d0200310f010300104810904060400e120004205501800400c11215164207550006e14400f0049172518815158190700440510030002d6062080c0e100c20302e540d20041490030100300903034a8505201c038901050030203401c01d10041009007015051404010049122103291500340307594040c051200e4000505410b40d100d0301e10489034010309500c41c0c8075401c0220300d00c0c10102c6521b0f0a584800c6402459034903440c050000880e103000d007042440c483c06c0d003c06010001c403803040e44030703c43c0c2d0014031910071403180c0d0186020251090000344049002d031440803217000250000900300c0018079001a00a5204129580c4840c44082d60310240f101d014000340e6803030000345042864000e04c0e01603205c880c02a00240000c001c082e0002c0d01302601d2a0303c050004082c9025159140c1015119180d2801d03101000540000e02c1480c08000300700d0000d29603006210040d440d40d40900302e000e40c841c0480c103842c1301d0102c0280e081e08800c2d801a102c0cbd0043d85 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 677850341 1250 677849091 677849093
    0x60f16090305062d0901050108010612020f090901060b190206011403030304030f120f020c0708070605040e100306050a0902040b031b090c04091b11151305010e07150912 74
    0x540e403d001031a104042c2c1c800b41a03000254031034010800c4041c07103894000d00705e042c01c0c03540380d0003032100788100c03802d66180c03000000e50250a01c1c0300018142e0000c040f0007560030310206000c1c000500400180055590f00d0010a011560300094000c40c0c6861164247c0381d0720510000c0c1c40c02c2010b03040900d4034801180042c144d80d800200700c0351310550500d400c4410050904080e150300b506901e0a40506092601c103102c50f5469502402140810300122806140d41c1c600303258681d0458050040019400c12003070103105070307018245810107103144000c1d41329541c81d02c0b0882162070540e441c3c3c128035224000b0406502e0300e130003003c6910408502400385150b44d4039080d40c0c040c101c8030051b8018074040300001c4007032001070f0564000b0f1510190500c9808002c04101c814140f00035101c10116a4482c01c45181007000140ca0b0090301081d11504529215a10010302144e10600304644075900d5802e4101400000d0021000038240310110100c95641200b000c1c000e01c2603904800c00e4414031491f004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 677851591 1250 677850341 677850343
    0xe03031c020703111905070b03040c0303110c0303161118072d0c0302060108010c0e0f03031332060301060c021c050312240103110705060f16090305 65
    0x1806008880d00680c1c56055140646450066010701c0750310740034410540003012419800710f00314034401c20554030056180c0d00c1c004414001030f1006000080161020700003e801003054025080110003100c90035809040001d25580c4941e00c80417909840c0801d00c4100300d108290701105050480d041c64040c105101611410704000308400108003e108480310311131109038100c94402ca0040381c00c4c000414505c0c0103809014100401c0700144200000014400380c184504549201c850b81d80b4a001c40c0401c080284138440350000507030500080003416070600c80000e052000308040851117035042d21115540c460141002501902c0618920b21800d0b2a0341e548205c0741921046d040c240754000042c00071031480f80c2c4420450000c808901401c000307001001000d400305900a01c0758910356500e100c0181705e000c004090600c040b40041610604560094000160224054980b42c2c1421459122149040025210046140050301c140806860803141d00024050700d810403500e028515560f907 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 677852841 1250 677851591 677851627
    0x1021c0509130218010824040b130507111b03070504051005060a02150c041401120f0f0902040f0e061302210c03060a110405150d05160e0303 62
    0x20400000040d080000d50b02c0050340c09060109100454039401060603100702c40c585901c0050110759000c00003440c00c1440701c2092403000410043c00392040380c0308140700140807480c1f00c1315400301b03407600355410035100c0f4400c03640311741c5c2ca503907a048109a45280c158108006507000000c8070020304c000100d2501e000820b40100e91003500e000440380c0e54070203884501c100d40e0304003030317400900004c0d1408040d50004002090400d0002d01603080e468010440e281403095100b1103044205224146409d0343c0988103005200805031800300b208064038803604101c51030311901486590b91840f429056040a100d18070b000303e84010208009102c10001540d00c0200900061078403010900f040115240c510310400006100d044441a40d0720320010280c139007482004441c02441041c00003104070585020703456030303401c016030002c0c64281042c0600400348540f903824034490344100f14184141c0402d100d120300c1060304406000c0b6846043c0001030104000326100351082e4000d01400c1c1d0220403503251 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 677854091 1250 677852841 677852893
    0x316050607031d1509030d020c030408070608011212140a02011a040c020c090a06090203070e042901050a020a0b281515111203090c0604030503160c030803010816050102 74
    0x1021300310b6176032101c41d680b440c41040020a600c074000f140310000a800007028009031040541030300c1000340c80d1401260840001d10585001e80303038180c00400440e16521500081708500d140201515400020760005940a0016100141e544030b040344840c2810050310314041004a80c14802c40c0e2088000968034841810f109101c0d8a0f1345e0041541e80d01c042d48000c1c003d0103d14419501c07031821403c090011406520114011820700710401c4481c0c9000041a181441c56125501419a407c004446c60340090b20841c00b50700c80c03801c87c0800310f9264402944111405210025084001d0b41c00600c0500701c2e0b0104205181014100e10030b01c1600c0c00d41e01c00b51001c02000c190500000740003101c104043d002442c00c0d0780190301c181660803030810015481280a2000c8400c513035815002d028482c07007148030107030040e0014011250091007041940e8007090062441a450b151281c907480741c01c3e03200703900c5a88190b0140d058188400703070300310380800103144c00d0001d404c084031107004000340e00c00e01e004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 677855341 1250 677854091 677854123
    0x604110316030506280e090115091505041404111f0c2907090b04061d03010b060f130e0108100507020f0f1f0c050d0e0316050607031d 59
    0x42d0b466282d858045072006450148441a00e5082c00701841700041406031684502c03039100003c1d2540014000e051440c0c001a162401c41881c004c2c0c4800100b010751188408408049000030b12072390b56005822025028400750714160605107824101e120000400a002c6c0e0300300c0b03090783c50511032008070038144d03141414400810581845c1c0b60054028001030103a031680000e001142d0440c00c141003501c00d50564803088041c0e5200c7c180d00310f59000e1840340c800040c00f44003030186141d0740c0d00049107490700058004168903a40d5400600180c020100c2c4081141012520340035841030000484005c2c400c1307104074005941031504094942209104030f419050b100e4001c101a544208100011071100c00251800c500d450300403241c03190001d03202485404114800a0b0030f222241c41110401e08541d1a40d902d840c25180c103000240c44030145c0c80909000520580c0704029415001c501003500c2003000d40b40750714000c00f02504482e540c0240505000c074030b000d0342a0740d813400552510703a080100 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 677856591 1250 677855341 677855351
    0x31309110301060c17032d3d0e0f130c03140c04060f03170a0807110703170912070b0324060a110d030c0f0806010e18060411031603 58
    0x1080c040310f0188118045008001e0000400480c80240c009507070402010451f0400c0e2280340d140800044038003074418481c8180c00c3c4500c100441200f420103079094045d1811100f000340d8089401075160b10950081416000082c2002401c610481406601c8400300807400035520307007621924010106400002d00840354170300d070364201200070010180c1d030a07001001804465221301900c04070740414481201c10729000c401182d400360091042c2c600116082d59080f40ca90748030300c021141c000814201220a000b00709011020480460350b07030b11440c0d0f00c8600680d54004590502020311001581c07002e1541044009100008591049940050410905048102441c07000560000700e848074250300c903500103500101c064001864034001c2d000103040d1008240c0f00c0b00283c060f00c07008190304000030310400a0061040c0140c401540192042c900003000f0010440420b000c400f00e060355420303608224082104500d8280560400300107040300c0b641c10750420000000300f0070301e500b003010140360700c40d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 677857841 1250 677856591 677856593
    0x819080f070813061e0302182205072a110103020d020c070305012703080109020f04050303131a04030f0809040e03030403030207050115060c060507030b12031309110301060c 76
    0x6030060702e50300301103091404040755a0307003005440800b0900d04008601211468581903600900c00e83c0d01d0700485074103040711082345204020100c3c80105030170400d90340c0401d00c180a80c03018801c0f10f03c106260b4485440034804104d8001c0d01140c5440402c0708903140c80341c0480019140340304c1d624288802c1c20050789580200034410301030b0091000302a114480c4140010034403034150010101804007003401d02e14081600350704c1c945000d24030806030100d04158010006106294000c3c0f9074001204501410141c40d20006429030b0302a420301d540111000200380305404101c1400360100c40b1034240d403860a40745555081d41c120740094042c0142e00007180042c21a220341d003041c40d02d0b40c00401034990721f250628000e00250080c401c10341e2203610300030142e442e00703c0513828401903031525281c5c02c5000311a540e1324000340100800d002d041640322001c003221612852042070b0305400b0f29000e1615000958440100018076a22034011941020714200701410340f4400c9038199181890200d42550403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 677859091 1250 677857841 677857853
    0x1140c100e0316030206060a080613080307030213030807120305091207060204090603200f09190b0627040501120b13020a090b03011409101d15010819080f07 69
    0x302e0014401c070307425020b0500101341d40414010b1007620304a42c203002c00794969417126039551044039410f00c001c802000242c04204d500c0d01a40e8080007130b203405171402c3e00310b550b84c1d1010841588111040b50703022400360b08100140100440c0c1d502d040c9002c11480c9000303100e20342e940d02d00480304036820300c1c002408814001e10340c040320007801c00c608042c0320071680da150101c00d200181107640c0340c0d0b201181c13400d1540e10b440711341901c178000000d1a0b00c5058585a5005204401400b083c0401c1036407002c421405880e5400a0403100c401030101a25a00440e40030b0003074403506400052140e45003000600c800e100343c01d2428003054009007440d429694031440b2040340107601074065071024551000090140d0123821144400800f60000d0040c040901010b1440d02001d45000c00c0640180c03408006001c0540d000300f030060030b0b811102c103003007010b121424105808000ba030b0340320980702801482801400c12400e61a44500800104440d07074175200c0701424000c0d00480101690002509000d00c01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 677860341 1250 677859091 677859097
    0xf06151507051606090639020a03030e01030b030c060f030c0c01020d090c090c090504020904021e070606150c1101050409020c060a0606050711090408120a0b01140c100e03 75
    0x6800400c845142201c9038000110f00c0c0c181c8940400a048544081610380c07285016004131410b803030380b0803034815000002503124401c100703440ca20403c3c84200c420140e50b030403240500441c001e0311600e220100c0400010165a58110024000e07403101031182d0150b1105011612907003011150b0ba92651504044180d2034803481e43c081a40358000304600d40fa66210303074002240b8911640304041000e40d14040c0c003007900d074503081040226111400030084c40c102a00103020305a13008000510309800c10550f5051304941e43c9070211004404501e0108104140c41150081d102c031042004880b04000002801200c4040b0000d001c001c0b02c02d4000e8059000b00262006054074260030f644803c940030905503683c804807030083e0200e007800b00c0082e019004d0804c881d00385030003170201c04e800010403041c03000c81c0300064022200360364100a9900c00c500318811040c010244680003140109100b40010036650340c20900c0c0c041c204042001980c13030f103000a414070082e41d10001c041112240c91007a681540 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 677861591 1250 677860341 677860343
    0x9060303040312020c03060709060c03030b030c0a030f1b030803151f08160e01090302060306130203100f09021c05060a03050f030a02060a0b010203030c13080a030c02030f06151507 79
    0x201100c000640041e004174000b4174944041e011541a0354608200f1140f0080030311444001c00e880414150101e0b100b038118078545c8001138201d650009400000c55060300b5242c2c401e4442d06d21540300d03a0b0411400c1c21001100512a40c1000e0006003162158250b0b4400900000200e130340901d58082070307460302100142c451840311030300100725421a0010701301090480d07690380341c4001d241d5285c000c9401016000e44462044c2e40300b5804500319424492300d64000b60641d81d110007049100f10034a112400154881d0b1134078800030987d03a19014401941720410342100380041d0052286095030640111042e40349024241c2c007203107603191540031030621000c0c0d4001410350f014541517401405000402445a00b1455084901c0c41d61030aa1401c1150340c0400506e0050b00100040f40f803404082000d0500155045000c000003665400910702c0c00944110480104212402e12400d6203024450080d03200003402c0a00250302c1e2a481d9402020001c80032580310305284c0c141200303010a0380b420b6803256 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 677862841 1250 677861591 677861603
    0x2060a08090a060f090b0a061815050303160203060f132409030305060117060a092703020a0309050f0d080c0a0605010f050a1a0d02070201050702130b0901090c050306090603030403 79
    0x2408025a04d0020b4140000182c078000411404900d1120340c030b104450440d0b4030740043c1c50f10711022101150203043c012140c20382654800c0707070205403980d0074001001b2100d4801010b0700d0340803462061600f40a4002c0502e1000d042020801c070b10140400103480102e60f0002d014020106213504c0458465248641520030341e18240d000713820950194000c40c0074003001d80f15030090280075400d018030140d0460b169a003081c0406402c124a81850304070998000c0c00c80600102c0e0069900e511a440043c0b10701a40141e00c840c00b541c040c950081500b01c0945010386110100a40c0c06012668040641100416a41c00019440e0305590b05005004804e40d00250034001541c0d0b0b02d2020755540140d01030380d80300b040c80510005440b1603500c14055456000d10707840d0300780071400c078400d4000d41003060300f68180f04040040d000140e6801407605403203181e1000005000310f0309001e010301d0f4101600424180e500d001180c04102d5000002e4a84c811001c541000c1e05590756404641580141c0d40000c0031 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 677864091 1250 677862841 677862851
    0x70602012306060d09080313020306090c1f09030b0405030a120b3703470705040b0708130f0807051903060e03041403240703200c0c060702060a08090a06 67
    0x20323a040050a403010394000c4088808944a082d50151188100d181c1e05901ca43c200f21030f2030740d0780308565849000742418100328140030b5594480740d0750040308079800c6911360000904021425004031441401c1801c0341c40030820820004003064404000058400300c01100143e98520204202e100c400d070010b058110080d02d41d0383e0700c4d010300075442019410102c01d46160b40c100300d11103c0a82d503049150310a030521481c80724030f102c10b140520081c06400401c84c0070800482e140d582c54004209691003030b10540c2d0b0301c814510071100080040d03000032007503454052003000900740008049058440440d40902880b50784150301c091101664401480c140c10009415010400800a00222441e01920000100b5503404042c2c0741e101c02c4000d038032040a40250380003240c1080c0c910a0b8088140d0600040081005d0007840040900c56801e075018000001c0d004200c04061104010f5500c1c00c2d60b9050400489600040081c018180b24800b0400014009110002c0c104413a100642d041601041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 677865341 1250 677864091 677864101
    0x20c1614040b060a171003120c03020f06010e15040605120705130b0a0e06011205040b0106090f0308030a0c2601030209010e071202031017070602012306060d090803 72
    0x10a0341a40a1118030032031400d1a4120107041903030459500000036511100401c1d41d0750620004904040c0c511041d04006150120020b60340c0180548c40e0821900c44011401d0280740080c40d01110b286102e0894006000420458001204180d04941c486510308125810b0401040003000950721403a031025002d001200000c402280035825140c0c01c0d50401004000c07125108180e4054000051300b21110704010480003001600c02c0b074100702d0525110f0722003000c03c003014042d076070700b80d6040d50490100c000400c41d03613401003078000c002c201840050034083d1a603200c489140c00020170b4008403585584644080350b01c290041820007144810100b8a0002058842481c1109000481c092200d2400115004007072103020362040c9006d030f43c5e40b5640800010300c0c0019420240850464202d0043c010a4402ca20703204420002c0c5030400038244e0b00c0c03600900909440c580781c03181c101c840483c0e102060880ba0030040303642c008404c0e11142c0d51084106010002849a440c0103481998040180302d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 677866591 1250 677865341 677865359
    0x3040606140d0507030b0a290906120a0b15100f0305130503090d0303151403010c0c1205090112020a0509010e0303041202010e0d02061b0114010501050409020c16 71
    0x681500c11000000712107500c00010300403201032002c005060f80c1c0c8020003c00002d540341c1c8505902803c001e802040d0142031491090702040d04204640359240584044a100d04006001030352061040f641c0c038144030307580c54146460703a2034004050b1002940d100020348148215201c411080400340014401204e143d100a181400c41c124800c002401c3c00b020a000103002069810542d4104000d189005c440b00c00704041c0540d40380e4102c0505403108a40c030304003040f415800000300b0001c86c0362154210400201802c41d1205d1803070800740715280040310080f0700d644110300d01840550421550f00c0e035a120058031051400070100d00143d00001e00d001031903a0042c05444084000c0c0c070740180c808482410586c0368025030081c55820a20300c0c02c07045c055841000c10880d81031019100c40d21080b01c54011a0301c3d984450b65041042c183d5940050783c4450900c02c0c4041c2e4114101600915414031000800314821807041c0c000c0c8640104072080c54030000d1004038000301002d50b66045080d5602400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 677867841 1250 677866591 677866601
    0x60e07080a0b0a060b0a05030c0d0e0d020c1302070b16121d0f0105220f0c0324020705061501030213080d030f02031003030f050c12040e07050705060f0615030406 71
    0xf03c2589051800020300f4640445c145c0d1071a5410f525251308680d180340301e0520076000544681c1151392100740d180380b20b01050005541c241c0ca19805811315003040e10503c4400f040d030101c039903812031040007030002080701c1c58400380e00140141001c000c01d45142c4c2049500c50045050032101c1480d0070003420790b4581a41810038000004ac043d0f8008080c412401400ca410886058ac2040340849111181e6402c42c3c0d01800c115101715103103940340044d910340c0d20b8140070941045410b4030401186800140851070081042082c13117005601d054420f907a42c03a12003d01900c80c10701d6025124000d50182e009406454080300c007841007039641e960b2200d2031a035a45128030b048000c03902d400342c041c0c00c8401a0086a2080d072603400c0050a16195941c100c61081c4041d854504000c2d041c005001c0000040c007202c0c1c549200c0d8100181c545041840090500802401d0769007800000c104020004001059495102c00c400203204071903520700c400700b8a030009410b00d508500b807001080000b04251a03002c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 677869091 1250 677867841 677867851
    0xc030d060b0d05060607030f03110408010f02090f0a0b0703032d29010c0f020414010e0103060f0608150a02211503070f150207090203180d05090a03060e07080a0b 71
    0x18800f6860701003e00c6180e01c80c581c0050001141e4254502c21781c0e0285d00290302510309120a81d26099580e01e00c03a0031181031821101441d600042c5070550341c640900030244222040354514a440d2070049011580c0c030404c0e0000f0181611401c0320200300c0749810f00b0100c64120b01c1c10301d03c03a125410410318001c2080c02c05000c00700344000c101003c100290307540492a00e0040e101c140d4082055262000fa508101030300f00d070701a403108002c1d5880900b0121050003003003242d0000b81c0650444c03a02d07034255015550740751001840e180f420026500300180d200f541d00314141e010304c044d884983c0500040c0c80703844030742e60084103071070400b4070310300300d2050b499105100e4072a00740301e01800c07502056140e24407172141039110281242c0c1404001404403200010b0741d140d00448a03c3d07a9a9002c55060380c200b201c60343d40f98880f085190490340c10034000010380b01020310344646001c0d5000c00191a020941c0405031a099540000300e0307540c182009800041d00b0043c0498080c8200d5191080c02500d003120 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 677870341 1250 677869091 677869117
    0x2503080703150e0a0209060c06100503060c090423011d101d0702010216030804021f02071403010e07030803160504060c0201081510080106020c0d02150c030d060b 71
    0x10009038080e00c80d02c2000030810003002e9009a0610340004070a510101030600c1d0042d130741c2007202007031540c0e5120080014201d00c4d8040d02403440c141e90a08503c0b0394603070180307000390440000c1008505102d006c0f140c6407070701110005140700314010000340c01c40c0700740004031a6900c8440041400b070380e00390810140d980c402c00502c4450303407582500c000402e85071003030054070002090040c0209070300103405a401800751000500702010380c4600c01101280040580120702540d0030b000a5084c0548007500300c104407034925031841001e51000396a48098070a5501c0c2d10f140e00c00e10250b940d800e401aa042030f41c01030840d410940c40b0700741004030703038002e42d0b641c8902c0701080c110031140e900840c2035408680c02d81d00c1c0c48040c444660010354004600030094480350440303141e2201955100048034284031400c2c0c8e14500107604140010345001e500202c918450032440320610016a41c924042410712007a0780b0558642c90f0580d00b051443c090901038000b002c2c14042e010480c039503410098200e12500407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 677871591 1250 677870341 677870357
    0xf0506040f0b181807030c2301080f0a11030c0919060203030c0d061214010c180b07050f0d020a020108010e01030209040f140a060b0406050f03100b062503 68
    0x70740904807214207244036040940c034100781c0d001c0781c1c602602950050711246091030030000c10740b6460600c0c0f0309410440d07109024840500c4980c0261000f14070302001182d4580315041c1900018148120003003035148582c0b05c0d2400122411016000b06210791850050242c4130308058001d680b1a80201c070099000340c800d0f580d404800f682582101003101c4c5541c0285156495010014075030307a0284158010060700c07030b84001250409401c40c03404c10350040544c441030361042c8103204d0035180004030000402002e4600341d1050143e030b078403610403a240011642ea8941c020703e002d074101045a803500300c82d400341f00040500c0e039801017020714056200340d8403264145e03204c58081a2084003804080d421080303d0b400640050186054012014007803000741e803412030a0200c480c50040403080441e4040d072606114062404d15004020260400300c0d85940c0b8400400c012940e07c031095a08402100e44910040e94a80c03500c1e02120000001014510010170010809200300c90241c1e074118000340c040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 677872841 1250 677871591 677871611
    0x201051602150a0c0c080a0f031104050a060c05010e1e01050a050106050712020a02150d05130506060108101d07020607030608030f090a0f0305060f150904170d0f050604 74
    0x2290203015205096400c2000b61a80306851009041041300d0750103114501e4010004206401d014200c40303200c654840c40c2e445c9180d840181965452070310780303401e41401d010505c00c96503202e42410030366895140a0311460303201d0403c0c0b80035140341d480b4905540280c200200344d064060010902c6402c10f140284481d4481c02004d4084960074822000041d0052050900107070341000c070342c48804500d204030ba10071742d010380010720074100c0400d00955244000840082c14606801410b9210b49200e0f030480f40282140c9035541c0300d88c0d00502c4a810440c4440c0082d0110201400b448090000c180344484004000c0000c0d43e0f07100001d031889005849407000103050307148a801000c096070504070145080000004045000d03070021142903610850441d0f0105400e03410b8200000258021070042007241000c240003200310700087c05000020144043c0d0201a4507600d02e140c2d0001c5d48400c60110007640e4101d50003940c068010180550340c14030052404029242e0000c60003624121000c00c161000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 677874091 1250 677872841 677872843
    0x702150705060412030f0e060a06050102010608030d15090507120b120d0503190216060501060807140901030603020d050c030d18180b060f04030c05310e0d0201051602 73
    0xa1140300401c1580710100060001e5005500c450b10074090703080100e040a000800b540542d2003203058050345a111004000701105140070364802003000b070000700b020030b003400781d150f44a22900d00200500d80d1161884521b08030f40150074001048005400c2020b814001e10081c40f180d62560744195943c24440000036519000702681030350032406c401007001400c1c101041d03416420081102507008280c030000c5207411400c1c0000d01da1105d03049803400700240300d850718504840040c3c1203081000181c1041001c500d03001711b125000b11001c015200d44510401c0012405030055402c001c0d0890a80403030307602040300000b002111074000f141524001481050100c44242c94000c00d4140004400000c1180002c0d200001820b0741c0541400b154120781c0c80c0c00f2032500d41c440950348850100c001010028458400343e52800350400300c910048209960790380c5a083d890364548003100300e00800d4007410f0b20050ba0f102d46220305094094420008100350081d000b400d08a03040760302c02001138958020148 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 677875341 1250 677874091 677874097
    0xc030403052d1e010f06080303060a0f0b031f1805090f06070f08040c0509010e041407030215130509010801291809100204030804170c090c0d180503070215 68
    0x100702c002400c00b0120071212514501510818106a56842a0b2504c0c102d07114010180508140c000035992410210140054040185d120340b0302ca500705102800003014603002c0703a4000124a6462065400101082001910036844000c40342404924819014100d41101d0701c5961414107070f42844030b18045c40c6481e903400301c0300d000c00207030350320055a8160b01502c1031030f403c2400381c0070b00540141c0b1b80002c071720554070030707000362118152a108000c10010032121141070140780c80003a243c0945164007003001d658014040c3c90480d800445d00341480865100203000400008100c4509540d660303c0490003070241c09042d000282a100c00d02c0c140c12000c220201e101c21000d0440da07212b400034880c20031006005400c0c003406004860b90300c0010b945900107070024601490b152075503140340c0b000b0940c84410600c070382c0641d0b0b0410107880400383d603203590702b85c0e106145029840d6114070644080740141060000058403203610b2003038a040c40000400b0703000702442a81c19050048111844001d140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 677876591 1250 677875341 677875423
    0x30c18041a0f0a0f05100603020c01180b220201200309040c0504050102070b0702090a0b0109090c05030a0c020a030f03050c04091401030605100f03030e0f0409260a09050f060c03040305 81
    0x1b90001c0c0800c40c8512a034010004940070780000116442d100d0340e5500300c04031743c500c162054155070090241c0166005890f0b00700c58080c404401491381c01da40068a841d04001d02050780c00728170f10010003002030074000c0300c50100e402402080740c941c0c00c50f00540103030018010540113216001012510156aa0886212030b800070440c180725500d201c0350030064002c840541c1d0410040180010313080140780a119081c1050b512010384130b240010401c4219104800014115440260020003183e04000d644039400d1903490045529500c168400c1300300e100b40c0d40010040e0307180076141c20300003036200f000700c0c10790303100394810b000c3c0e0345035103514101640d101e011b20099400140403c00002c4e000d0981c14a000401906c041c417060034800003d400c44803560029280c041164546016010b6400d250035007140f40280200c0c24290804c100800030103842c001d02e801030b10030034400c42e41d56841c4400d807107090b05d904007101d959580740c2c5481c684650007521412207802e04c00d17120122446800d0303003407403500c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 677877697 1106 677876591 677876611
    0x8090904060f0506010c030c0f2901140301050103023618010e01020c07090e030f03040c150f170a0b1903030e030c18041a0f0a0f05 58
    0x140e44001c10a45c10000d882d0002c01c006500800c41c070184a4000c100d04d001d05004d0300e4117954200200218803030903101c080da8048101c20800400381a100500340c2004c0014505050601b030350000e000080d0310180791049a0084c401044280341c0940c8000c40741100500842c0c01244100010360704400003103040c4009130001e00003400b44112150703030540210310f0710400201c0180c40d103240b40104c0c6c18441c3c940302d48000f00700c1d04000392600b40324518000c41e96400d05103810f120821080c480d0f080c445210002c1001c180340540c01e019501d0507c0e07106ca40308884c07401c4000700c040000030b0020340c40c0d40d601c1040e01035503101c49010b404000300da4104000343d80d086003000b0380b0680050503164481c5e8400304515240342c541c5036101010655500c140403150300e8a144c0f45c0ea1b07d218281c011031138901c4410400c070b003195001440b5406044200001c10101000c41c03122415244122218169 = true := by decide +kernel

theorem cover : BRFrame.Cov 677697841 677877697 := by
  have h0 := BRFrame.cov_init 677697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 677697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 677697841 ≤ n) (h2 : n < 677877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
