-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3972
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:12:25.105955+00:00
-- url     : https://prove2.me/submissions/07f8e1db-7bf3-436e-a52c-926fe4a6f4b2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 714208633 ≤ n < 714388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 714209883 1250 714208633 714208637
    0x6190e0709050408070303060f0b16020409020306150a050a0e0c0f070c0602152d06030f10140702010203041e0609060207061e020301120605040c030c03140105010e0c19 74
    0x114039a102640002c581c0d042d1030855001c88002211410701da4903002c0c40c0c016043c0301d043c40580c00d02c0e01001c440303180304003101d000c0344841990022003555250f03407048400c00e4010b419102103244c0301310307180380b000140c240c43c2d48140d01a000114281c1002924003094600079481c00e0040d0301c1f07140da00c41050700f00c81c081c1d4010540030003404000400c5007503808000d21b950340040c6401468070300340c000c02c403600600740d014000c80c52401ca40310102100443d0880d0401095413892910754001181c01c280c0300515a0406214031828903841084580c45108580800b183d460880e45900c10100d0907448192406080140c0782013480720189202400107030040e2081c0380014030600a07550303500a07a004400e0644031603590344683c0b03107c00250b1000003281180340b1011072039503043c560b0542000b541c0c1d10000d02469940d2001400300b10010001c50065500080c00ca405503a981c90080307803241d00300c0e2003801d5550030000001142103034005464090844000d0560600d00903c00c210311000c011064082 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 714211133 1250 714209883 714209893
    0xf01050607060f1116110f211203010803090306011202061209150103030806100f020303010b0a26091506010c0b250815060f25060c031a010206190e 65
    0x40c0e01c20400005014442003100c070503c0361101410078200c403003071b4006550f00542c1400102c56a40d6142c14440d01c0d4103c44920041940240c1c0d003045280010340300c034143e903003d0004008078103400e0000152124110880441304540c3e01c418901465071031000d80207400500500541044018024403654000c4084017103840707000445400341491107003070703009070049509541402464140550381d02401401400d000c0815054004020b65902c01445032440e15440860104075161007450308610f24049920f4500041d80b210b00038030600d880c1a40c0343e000510840c0d801d41d406820917000d103840ba60058688003001da030641c80384400d58500801c10601181894548180d4444203400700300c0045407569807181a103040c42445002da464942914415501804030b80364032541c0004841c2d01c1c000030103a86100c6c000f000900e2160279070128006041c5070420703810703403030720380d0300d5400764408811800342c248030324124400698407440b040d19a4400c2d4881060107042d14885504a841c80c0307402d4004840d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 714212383 1250 714211133 714211151
    0xe06040b09180703051608060a03060209010c08041403012409020f0c0a06050708130c12020102010e0a0b060f0402030705030a090c09090f020a090240060c0b0f01050607060f 76
    0x10340400100c4180011075942c105206c0616000c0551558005d440c0c2048449401c001c070000d408014180b100030300700307900084e290005921032008034a100d94892515600c03540c41d134040003132008454101078080c0d86001d0b4083c06030280041ca0894100101c14990400c1c0d0078180b524010390321040582c5182c40e4200411112400c003005507000650089100140500b40b600009202c82e9000c0d001740e45001040502c1d1000c0b40d110500807007202d101c29050700308444140b005074090729600e116810f20740160744451041c000309000a40c0320301e90450314088618179041c00c1100b00d01090300c803100014030501c0001e001200b1980880d41c440d0040c00c042547c0790350f0700104c0c0255076803190100d40024400d4810340840c00c1c280000000f504a6240079810414107441100c00c08420054442c1102c441082e0100600028240300944c100e481002c440855200c41010340081c132003075030480b2004040c0340040d0100414140107030580e14000d02d1070340b1300300f4182c80300d401402200c070544801580c0c3e40050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 714213633 1250 714212383 714212419
    0x180b060a0e090102030a1b020304060318060903020304060f170a380f0a15050703030609020d2316030b1f020a02011205160c050102090d060605030d0e06040b09 70
    0x140c0b054980320000360313032444c0498061007a24200c110542011030b0700d18800078116004410340c1e06840c86840e0001e0940c02d640b03c2c3c0c502a28841102814045c603000004040c10340c007000410540d80a901e44114071311416a080714a54a80d00500c154011200d0100c0c0b50401590040302114940320000403034281d03120749034010841003288c6440c0303500780844250824200080501050070003214100d51107403500392200e514a041c00c8040c01044800030344401018043d0340500080c044007541152203031040300c0c14000901c4514a9100b04582c1140003080e503410a410191048000ca0030146216400d01c4042e0090452000720343c0c0e10184c0107481b0080142c06602c14880e41440303500034060311550340005018401c0700b0b40b504040c9410b02c0104800920900e41c09107200a42d440d0840c0e030540b03641000c5009028501d007540c3c3c000001c4000000788075150f08418295030b0b0840a884580481307980503245034200440e01900814248010002d90011307402504901c0300c050905802c0d41850951 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 714214883 1250 714213633 714213659
    0x308060d050f0d0e090112020f030307080d05182a040608060901230c12060a1502100f0b0109050409030c1b0f12021c05071d1801180b060a 61
    0x100d07003442e038400c410f885105036010149020283c03042d41d1214003541030050b0308008640300032010b17010744411600d03541107403020022900906c0d0444d056541745c008103054400030f4203003030302c0d15028000d400e41070038081c1c04081403207034052000c0100d03140c042d810614a200390001c40c51035150700554a84000503064010b00c80e00b403041031034100020b00b9140070b44820240301100c05101d042e06408808222079070743d003101100d103024010481c1070000ea0318000002e45811143e0408200c003011400116011900002e103043c140207150300a03c100d8103426a500c0171203010042c2c0b070707000903c051400c00090509074130810b400c5019140820f003c01c06034076490703821010822400609201c0303c000b0402410041c804001038002c1c80c0002040c0c03a42e640020b00d0350138204036102d1002e40b080c410398082100802010006040e0240d00001e00d41100354021003680f000c5940c4e2020000080c11a03000030018480e001d52400310f8220003224918903101d01c2200d002c0100f0a0b60041080171010420004000c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 714216133 1250 714214883 714214903
    0xa080f0c030f0c03070605030a0216030c210903080d060f060503041208070933020102121e0f041a0a0f0b0d020a12030207120b010e0f01120308060d05 66
    0x200614052115005040c0740460588002c440ca0308505a110000d58000c22410101c5045d850032a48a4a4600d0714000910911500700e80c2d40004132456420980c004c0d19006003075008030802c480c000c5a803120701440740d900c0462403000074031070300041c0002410080175002405100b680044c0e5992580300b00c503580a00764021501091380482048108103803840d1141801e8180d1070b007042d40d800d140d40080c05561843c00744201007690741e5a000800d000080c90802ea0400c220211074000f01300c00c2c0068001d602c2207902c50306101052001420b451100c1c91056040300d0501d1048880c1e81e111050b010300b001000d403080f03d0740ca85d40310f08514a810030b1500c0c103004509244000a00245c6a5546001c980c07076254041e014100e4850321202603078500001070304442c20010910009803c0703207022420006d00d5040714400ea507254117030f801403002c0712400d14140d03016184160034540b2245403510300391809100e9400c1c00880f0326256130009116030142c90308042c01904995580407155251414015010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 714217383 1250 714216133 714216163
    0x190f0507080906010801060b04090c1209081c0b0906100504030605010e0609091515011107261b040c090509070f03050a0b03031608040e0906060301050a0e0316020a08 73
    0x805210031401e051003414010f20b66400201f00e07003450003d040d02c4138051881500c618030794952503a1000c5000d800c2080745c044468070108207891091800c0e00c184e0f0440100ca6401505814201316200740d40d00c1140300c0903000600800031079551100708580104c071032540c6003c11205000000001706a03002b62406800302080c000840e1520009010030300c01c000745440443c3e03018000862151010111003500269089040582e003904540180d83e202c818101c403051510503c03400241c244036090303591000e62803039015010320b0800c42401c10f542e86014020f032030140c518a00611910326240e03101040c51102420030701126959000003450012044507020003040e2040c0c038800c0c58903818880c1c1fa0740800420ae00b040074803441004261349000d1010003a0380d9a100c0700c42c2d04d092001c040c00795001010500020b840d24070f440c0b00c00130744540c0c1c141d403424060340c00c1c14041001d0718000e00ec0d00c1d210102000096003846d00c401102a00341c603004000380d81001900b4408122120180b06001d0146c0ca55 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 714218633 1250 714217383 714217397
    0x2010c0c1205010b01260601051b0601150e0109092007060504020f1c03140c060709060f090b070b04021201020d020705120306010903120e060a031b090b03190f0507 72
    0xa04100c0d09442c1041c40007070400910f0402c1441035801190b062002d21606c900000b190340d80c000040c0d5a52042c00c6039a40e807900e0340c8041800003100044d915059840d052101c0c1401070300040162240800c620150340441c201c074200344100d02c540c0d031003010240f249140807003076807002030b15a86059018010aa6080384c480d000c02c415070070072034850050f0703e8054032000301605401d51040b81001c40600001d003000351004c509040c14601e141640e80300080340b005c0d144c03e800c0004d006402c1101500c96800031490418800e07500c0f0340030b920388100701d9603680d043c6441c100d49645c0e441c0d07070b940d00244100d03480b0008000d1003075a40d00900c003400e09203070101401039441420381085803030200020300d07001c0d00080c20400c2044a03617100342e64904803584010030747c3c0b202a1420f01903818221701c142c0300d80c0241d0045a91956158160032500400c008202c1c0d04064406809003100d141095020340c80d03401400704040b178007005001e6041405800015030010700c040704074007500c050780d000f9035aa00004410b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 714219883 1250 714218633 714218669
    0x30203071502091806090703090302010b1504170c0105070f240b04060b07020d11150307180605071214040e01081005220201230a09060806030c060d050402010c0c 71
    0x129070502c5403804d44030b281304015480d04000040175600018280d50806444030100b008250007504103100400000304041c4250038000031044858115101d402c81404194000610400d800300e802100c440c0b040c1d460501d0848903031202e0304824500c560171110000c2c0203024042044021403405551000582d0104005401c542040261080c41d0810503480c1c50400c506001a40d0b811034460000e03a226064154000c1000c0c0002c40e051070480c0b00d214401400003c1102142d40304100710340c0410f018890803503060715010202e4036030040c2500201b91110800e17410710070a008d08101485085c540a20602d055151948034541000a0340282169448424480e0103154140501c44e0300c049105892825942e04000701c008840c0344500290510a0f510405520360788060740e030aca8119003a120719940c8444d0480c0043c4072a49500c1484002151030000c1042407802082a5084081c0103004a090004026070f4a0090030003800c22418410000703402000528140648401001e00a0310314450247e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 714221133 1250 714219883 714219889
    0x60c080108070603151202030c090c0c01270f0c12140f15010b0a050904020708030711030f2a0a050303040b010902030c1803011e0e10020414010c03020307150209 71
    0x1a203800550a05092000380a02d17609101c441c0c401b00c43c41015115143d96403030001c80d060451062500ea0043c20742c0c1d0400c82b018090200428140e52807000030024940040005240d8030348403108030101a40108809000ca103084502000c92406007041c0c000c401e036075090441c011600000b00300c0d5003950303062600101010a004c00e118445c44040078100740384200c0ca40c0c460514050150188600c00411406e12a51085095804943c0f002d00219900c6010b420800100c2d00704484103c0003507810720b900750700300001005844070388464030282c0d803c100b01712900c0140c00c5182c1c041c1001c10349080c0c0742c000d01e0420030081441c090307000b54042c560b2410a0304100c2d07503900058000c41c1103d0300400501211400003001c8030720710044a40e88000301c003e0600020f0140c2075507450800c006c016044105441c009642c00f406226403190122802c0120a07030011b401d90155100720015480002e42003440d0754001d0070100100c42c401d00c140c901c3c1001c50fa942031034400d558204813400300e07804211080030303007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 714222383 1250 714221133 714221143
    0x30c0f150518010f0c0c02060f0c0102070309090c030608100b0d0203060f090d08040c030204051509010306020306010e01020c030d081305100605090106030e0c0f04060306050f0f0c03070212090607060c080108 91
    0x502030701305010071804001e014000d4a084071000380107400018074001040600d8054419111030b803402550340c1c4140d07017401000c82c1d49500440c40c0251504141d071103598000e2003008111002a0b02600c0010400c40c1050010409250110341200d4451480da0040e0380078400070780f284108141170a103504200c0c11440c0f9086211a0f00803d200110003440080350f2900400780840303034102c030085031944d10b00010b028000119241c44da0070030b00340c90020082088a4015512404080c0d80c0c50078800e00035801241da80441050054141e00010203090f030040c424200e0030350021003e00212080909030b40c030750385010441c80b0126415540c4003018421890550502401041d0a01c0d082c045142612226a190f080709580c41d0701c01c0120f20050044bd0320f0341c0e0484801983c0007401000580b03096840107181b41c2c421035500610300c80000004007101e03100c1056a0080d040c0d9401096200c1807803400400b56402484c0090380000284407100005030240190b691411444c0d0306c0100302d501d880c504511388 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 714223633 1250 714222383 714222401
    0x9020c0a03080615041e05040513050d1403040b04170c01060311062814071401111e160c240f12050c0f040f031a04030c0f15051801 58
    0x40504440543d41103d80d0801c1c0ca05540d40c42141020103051041c241c1b07001c0754603512064004d8100070070048480002e8805140ca240a001034402405940c2c2e000c48100102000d034141d008814000308012070740c100300f4150310522500d01c1c000028620529180c4a40100140341a0b503910351509000b000010200400a102e0550b1103d06100c41001030344001e480a141c4441d50b544071101c000199031142030400c4a66801c01d012990b00c084a0500055042149404001c1507080c41e4000d01140207020403980c0040701c40580c0d851018030210354200c640d1000034404100030150640c01c005c105030012610052207808141d03d542100c5120f040e0013825105191014070585c00c012000b215042882c0c4c4d82c07000f00340f2030001059900c801e00040300c0c1c0140342d103241381100003140110702c1c42d0000107860156409035500e12400c8144542d0540c07002012100100001c095408480000320203001600c02c03184100502488014079082c0b500c01c0354000c8804101c00e009035541101d004030284910200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 714224883 1250 714223633 714223639
    0x1180515070807082701150e0c04120303230402010e010206090c0409020a0f06050405031002041a030c0702030a050606040e0c0906090c07140c010906080f01030602090a09020c0a030806 81
    0xc900d00a6030141c48100003d0000c2c0c00d014003180028043d803045106030006a43c41c0c0d00c25810032070800c0c1890300902855007400c581d0780c1c05000220f4903146607403005100c1c0c01d07400b480070703c1d050a06561031104d4940e241d0407010b0607210a1142c13189140d510030b21203000c5046002044624260000500013a40c0d01e0036039043d504030105102d07203210003080e00c60140000386c0e0b010402c5500c03480401c0c00c20308503130310018500c0070b00e0401264155002008000b115422401c0310380b09420141c42c00c0c102e21441c45000a1a008244c10103000550710024607032200e00000e40c242400311640100b410011007075811191780d04020204052881d181c800c00811000ca10000c001104580001c110011005884075200e11307003080015502e0740d20714003200c030310651210101c82c1e11640e10030700c00d03138035600d5450050101c1c404900200d5414400c00c07100e48284464007646559900e191511802917105500850b00b00354480d0b000300320445030380010304519100740000c242c00d444034117004111a0340035002e244 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 714226133 1250 714224883 714224923
    0x4603080f06090a0b0112051006180b070321020a030b040c03020f0304021e0d0c030201020c063a06060203030402210307080c011503031107090509070b1605011805 71
    0x80d86459401c04643e11552148001991811942c01603802200390750680850034206010440340d12900c1e40810120b038002d40f02c0029020210a000d04038105900032007c2c001000e000c074801103031003604510782100300600c4c4e108903445450039440681c1d000724203681c08261900ca181400341814481e40700d140140749821410200d00c44403a48643c40091b101a1085a0303020228181e100d011092000c0640003c2540d04900d40758904225030014622059000d8000d84a88400a0421804540032144010210340e12000009404610900031140c90200e20148109441586205201d40e0001d00b078981c001b181c807031600d44100507004c4624084101c09400400016210510004c02e0319243c0d070b030200c6417640740c0e14017203802401402c44540880c59160b20947c00010305400000c220b000c403134403e0a07225030585540300c9109071581070352a54581d6202c01e00802c00c1c21415030203890b441055080d542c0041c000c5441c1c050a4030a2840200340c460318128040e030402208120f01804290055803c403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 714227383 1250 714226133 714226141
    0x305010c09050f1e031516030c0807090302010f020f1e0c04020f0901050a0e04110c0d0e030d0e06070c140a080d170405010219031b030b034603080f 65
    0x1683d1500100c00044c10541c2400441885940a1200300725600070400e42d40c005282c114101d43d4600d48105080c40070078509081420840d00c503200d8103107c3c1807a51160740005107103a00455200d00d1030843c0b0411401034200510400400740107420101283d0040f02c04100c00328800c16003885101961a44074610401c90701d841490503400341d400480007420a0b50722412040710030b503a203103500740c20716a00030f180410790b41c03001d041100035014410324141142d080505a0005441d09550400c2c3c5e564180c2c4008a0000c046100d00c00074443d1080c0070b0000ca0078044150750700c0b10408544e41000300d0000c04000010201d040c0303040e6807401803620b800100428150400d000c0c0403401c805031130040b500581c40006085c05025011204640d041a1194a00322203803100280241428810240414031010b0350104031442030158001e54071004002e0304400c00e0403070b03104070010400b0404000090f1141240c490121261200c10200407406100c59104022440c1c002c040c084010501c0b208080080140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 714228633 1250 714227383 714227389
    0x15040302010503151212300a1d010c020a06060902120109020906090613080d0203040f120321091407030b0f040303060e04030c03090b030c03070c061113081002090102150406090c0305010c09050f 85
    0x1c50340041186400141305400d00c3d80c0d0f809441c1204010b270a030340d07003000c00741142140d001400b40c0d9001e001c0d02c4200300c1a500c800d030708030503032160031010805103044000500102520703500801c12400e008040501c0e11240d00041032054201c903560680d00071004074100840300c0c0600a00a1071481840610b25240c00c22580c5038440405006554039240c0240c2c207401054020b0b40460a801220980c29841741c90316818803000e4a0140402c480128042d07074080940c400c001290001da0794422400002907952403041408000000d00c250308160700c4050000e0701c080c40300036446c019800303030382e1b031032450141e5050203044d81c0c0042e400b208980c04204108070691012600f80e03034118105281141d8110080e05200010700300c0300c21201d07030b406000104400d407944202c40e05400c80e40c8504c10b4900307882c1303900d0340c0104030300801d12220b016800904100303075480031401c000781d80207108080005210882d5180d5840401c00364104071610307035583c05514466508104024028101141d040201030750030808 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 714229883 1250 714228633 714228727
    0x61b02120a1404090f1a0a080703081e0a0207140a031e031101111c05100b030408040f060302090f0406060207050111070e07050915040302010503151212 67
    0x10342020842d4002c40c1aa036150b2101c02c50b0020540d4210034440c1c102d40d136201ca4020401c12121203660001c6901c000305509000c0460401c07a04480058400c245c6140c41d4020301e680001200d00f02021059495508040e2102c050408440642d0050960301d040601203d07501191700b09051090f06101420000201030640701c003c04282040c403015840e0040c903050721203410700085100b0070b5003020b080307160600d030300380103030440700105800c05100000705240b0608540c0c013a82d05404e802000c0c4002d0009065010003160050702c03070740040385420f640d401501401816500703c5400240c00059400e0945400350340903c00d040201c1d4100001b80c600070010396102c5662161a050009100241d040c0b80e4041c000d460041ca0408111301d494940690001c28a80c440809244103c400c1354001030106220010342c0c082c0c980c1078603841d2846e294410ba14601440d0010020f601810804580d030501006010000c0240c0c9103224558840e1211005003600500f00007090145840d06000701d10340f41d50000e8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 714231133 1250 714229883 714229897
    0x60613090f030c0f05250905091b13020408010f0b03010c020c0f030114040507090606080114240d0e0106082a0307320d050c040b03010612061b0212 65
    0x50100329032031246000b84d50024864400b40c1607004103880149070384015480030480e01c101e40341148141341c8441c2880c085420584003482160301000310300f00c100078000080030f0031400040818210140900b0103409907803091b001940c4503511703641540c2425142d80180d000b0070710308030000e0000d0100414025610741c41d2011040c800c1030150b80022a9881c203600015003410034203a00c003605c0c81c290500700d5031900390344a148001450070704005901845400954141c42c800300e4102000d030140001c02040c05000c0b55481d40d4803600c1354001c0c1c03031071885078010050510b18410100300105a54991400c640c5680d001110075088031010710601e00c03450000304000c048608041c20500d0350301c80800d1402c03041e0f400034440e0749500001818845184611114044c020140601e0110b0000040c00010000381d80000c00586c001014070000d450650421901e2000c00340001464554849140920413210364041d2080d82e981e01440c18501c499404002c0981500d0004102d601f92018000205200d505 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 714232383 1250 714231133 714231137
    0xc010506151c0e010e010603050d03230604020f04090e011506090b030c04090c050d0608070302010e12010b0a150207080a030813151b0f0906021f0e03040305060613090f03 75
    0xa10880070910940d12400c03c000c03d040c005c01035028804040c80c000c00a43c0401e40342c5108000c4801c252a100b0700030742c1c101070417084a94030365941d1440c8802c035007503026186903402902840b00a40844030f480280005100c000303404260070007101f211908481c074410340c600394586c07095400c0c02000c0d0411418012940c00d241703450365a989003055040d09001d035801000b010303030900c4140042d880d031103005404450301100c8200400d0750347d103004507910b90380c600c4002e021680700300040000d407074100e40c0c10b030286d0b10760000031034005000c000141c49861550040d4001c004410324640c403485d810000e45000d40341d0a80100961880764401808840d8002e01c40c00440700210040c008214890075910700c00888203030b0901403105212440c06c440c1d186e840031440051501e02e041c0c030503144203281038411284650082c01e0141c109507002d801c071a2164107244841d07500d03121000c22200e42000140004c49c00b8001a0403142042c004001c0e5840c034100441c40347d00d060080e003074042505200468012540741c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 714233633 1250 714232383 714232417
    0x50a080d2a0203190c05030d0b1519120e070b040906060503091c180e06181302040e0703230c0109150f0c140a050613080304020f1f050c01050615 64
    0x4c04030884403101c0c840320080c9035020200b00752403500b0403a00701001c403507402c6500c003140154544140e10980520402d2000c088000000005450b000300c2042401c00103012000c50380c90007218445140590aa00c240c0348002c0c000b4040180031014410b00010346000e150507032950801e01949540c0b2203004168600625000400700e0038170703003e0200b8541410f001140d001c003440d540e551507150f01e501156054003035402130b501c1c100b11003003411401340318260600489031104520340030702004200302c01400e0b880e480340717020200100b90001c0e501c0c1b202c000030030400349407c11341cad000301404c5c40401c02417903042c0009410280140d00d803a503a6082c014032245040d0a4038070444d08201c40b50b0307200c258040d06150311111a4400b02401240c02d4400d18051000c84181c3d4541c1403003140015600c1d04003038100c00e0140049401441d103900f404241601c004d01410a0204a0a00d410380c480072942200c04200009041441c40300c0c28010f0179401241102d06a03030444058030031030a10700c80c28500c1d0b0140b1401d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 714234883 1250 714233633 714233677
    0x9090f070513150e09060306040b04231c1803080f19110105060a051e030c030f10150509010311120f070603060515070807050a080d2a0203 61
    0x3048080d03680c0e42d01ca105803140d07416980c1d40551580c58401d80824006020441020460f0424035041801890b01034020b0005942d581c40740000717103030083c5c030888080d030350701603051200721010b26107424003c507446c00307014100e20005100d0660b45d50100000c007071010603c2c02c218401c0f004e402c0c01c01100e41045500f03907250070300301c04030b00c151040e04c2800c100c0c0e00c0e50007a0000e816600112400c001d20f807650007008a078440b030081010780f0105110307080e4444078040b84a00780c2c0c2500c6e01e40c0c00b6511000303400c0310781c50005040007a081071401a41001c0544c000003001e07109401e40d000e0742c401c0b00c808180a45145041501240e41c50380c05000145c06c4240b080000302007900ea66a61041c0200d404042ea0201402c00b54858ac9600e29441504002424410040761510f030008401d47c0c40b40c0014036151402c5540d40d1010456000030744252071500a0752003200205845100402c01c060760300d40009240c010440b1006000c01400300c030750505100300300751011f02c0d40c0c002040350a60f902d29022504e42e100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 714236133 1250 714234883 714234887
    0xf0507020c120328030e0f0303010501050f251208010e06012a210306080705120304030c090b04060902070b180a02030102180108060d080d0f090f03021c0509090f07 72
    0x12400807509101500e61001c007604000c0c108203007031390508603a024043e4001100400e503603080113020310f00310b68000300f004100c150f01904c000e000607840300400900b8801e4052003580c200f80109804482c034818006080d04016130310450320902c50041c00c1171070b01035041c800160310381c0900070f01450620440900314407801050f1515505858101e50011054185070b1405010b142c0150004801100d00401c0c4808050b01900464050314500001070246910f09010401c2214442c035246200e4002040040085045100100060031264101245112146c0203100454203c0c0c0d210926051051018500041d5405003c68210301e8420450003500c404142ea6424400040701c000c0d850741c0700180c00390004440182c0504a01070903201e152540d0350340310500c45080540c12004040034010010007100c0e94141e4031805a2403400c103070001c0c411049503145044201d4181d41034016a0000c81d443e40d606aa40e40c3c0d003001c1482c1c929040782496007a0000c070340301b8100607084100d00c1074200f00141e1901c2c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 714237383 1250 714236133 714236137
    0x6090f160e040f1a071d0d030e0402030703021903020a0e01090302010c022e111b0a0b03090307020d03211b1d0d030c0507290304110307080c040f0507020c1203 70
    0x1601340341a4005410651800f600d45030b0b002101c0e00c00c524100811500c945405001d4841e501e0301910f9941241e0341490400c002036000408800c240345e42840072410884405441c0c1c0350200c1d5548005944035001d441c003a22841d00c101080b4100144d0110900050364440e0f0510851541680d40c0d51031406070002c0262002030714600800e04c505d001c3c0940c4000d81d0f100c040c4170080200c4a040da12517401c45451846541d004008158000e4001c0d6810803414003171100640e80001503106483c2010016400580450f01c081d5003580040c0002c2c00e03080c051000480d41c02d0596401200c20001841c840d0700c1584103c103581c00f024184070007544144188a103a100c204250b01008042492114651602800100ca81c4c03505650302c2c402c1c0c4070080b03031402d44414803904103007034a9803060060007003910420140e0320007001203601ea4400c04003010962010002a00686405000b03802003480b080244011168600c0b44407601c0ea0404081c030981c0c0e500404c1d8140c0c043c005480442c000201198070500d18 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 714238633 1250 714237383 714237413
    0x1506052d07260f1c02032511063111010302090607060501030c1a030601020a1202030d06061101230402190812041502060609070e011106090f160e040f 66
    0x2801000038000c01d0702e402d0f14000e00c510a40c2c4a4040c4898041d9202c0c1012408101c4145131444481d09083d0710004c1c0116601058039054a401003c02035100540c0341407403c1501c01111419100c5c551281c0314841910200204401c40d0b40d5802d0714100e900c4490a201199459505040d40010900034549401c41212581038101000340603950356460021340110f003510800030074455540620441000702c408403401180305900405440a0580f219880c4410401c0c4200962208001104100c0f000d402008020185a110a01c106003421003540c2520344802c000340d0300b101d4907900c5409101c08c0ca422240c100e60103403846218030100490103988900e07143c20840451140c1c6003041621510f003c01042075940b1407014107107182d2085070503a0340310001c0c1d0300250b2200020002400403882164541c2ca01e40c4140b40202107000c000c0411802c080d07027a02d52006540103005001e03000c442c20003424a803094503a030780d1540035240149031809440050802060007003000744400074456011040540 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 714239883 1250 714238633 714238703
    0x1f051008011e240b19050f270909150105060702010903110d08040b091003050112030e03010b04060e100b0309060c07031e08070305011403070b0306041506052d07 71
    0xf0850b1107404060541c0c20111070001d1000c0c00144500c0a580704006450102502540d00342c10004050b986202046103480f4002e410801110610b1540d6295600c96000d24001e00190004102000f01c4411401050b0403050051108010410050342d016500d48200c0c0d0b040b01c8598120042800040c400803030098000e041d260003c9004964001150002c1c42e020900300c4082d403810341c03100c5065064a82c2489080b40c00768800f600c00f40440d00849006400c035500400011701e40c60305000050485410b5004454107500310344c100054082c404240c20003070040940594110b00e4440c441a965075001030100508010215040d0101806000e21021309402e080c02d824130210b482d140188010b10468007040040e0030100005411000c04003608040000a0f0242450900306000c6004951020f400d0a402c15564081181600030010204001d00010740c0c845039540d000c09a21000141c840d0324401d100c04021041c0640081460101e40d4110752244245d9059103c190381c03d24414000d40458072 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 714241133 1250 714239883 714239951
    0x5090f09100302150a270e040f0206041206142a07061b0e190603020906040b04030302010b183105250801060302060301090902031f051008011e 63
    0x8000006100a40107100c1a80c2c1d40d10301c6c410181e03901d080f10344002c0b128142c171000c02017800c0c0400d00104d501c166000d8001d03024054074140650126480380c1c0306034001e140b140c100343c0c006003c001c4103008144048000082038199401c03c11108240b0b10341303ca540700c55044180f80d0044821040005030780300b80d50040c1003048503107080c1d034541174229525140d280004003801c0003418149000c400e0701d564a045180000c0e01d5a04280701a130007076122410055012400b40000540710100720b00903c0550702c0382d40040740d0741891400b0720140d6500800100590700060301004020035600a0400c20441d0500208034200e60b0540d098400d2165000040e0503401038101c0d40c0c0300c05111848032040e499040c0134401b00d2940c1c3e4216242260740ba404029031001c0e0410040001886540103424141e0005095130345602e80c0c0c400110000c400c412644250136299401c100500700700ca050380e00201742e001c0091101c44480316031076039a01180300390300e0140c55845418042001010000b00705d0140e807009408 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 714242383 1250 714241133 714241159
    0x7030b04051c0203280c140106080c0d17211006020601060203070809060304050c1e1503010806190b10020601090501060e0a1206231605090f09100302 66
    0x20b6142c8941190002091004000e03800c1064800012a0040f020404004005602d12407182ca842041346401d0b401b0801d56000c800c020400340c42c40401c40000c11000003803038900d019010382c02c148a17082101e100340b2081c0c03216008154102e154960586000d4406c40d50b469134001c1107080405c24103404101c081498041000c0c545040240c02c05442c1c1e141c0840ea85030b0780e140c00881e641c1c8030341d15005043c404e0500c14101c80b0706011000d0b541281c42101a10750625003480420004001094106201d0101c5100001642000d400422018803014072040c65036040410340c90340d4000250240609201c5195052605606980300c1c400c10714004240f41400c3c3c00c5110002d5a4000038003603000e0726490b110000a249010b0a02c0154210b009025a80340c1da01d02070100b8581c0c00a40ca00799486030b03c48000c01c418400c80410b01d440d04580345082d07412400d00b50781c200c00794035825003040180141006800e14641d514502450580d4044030804000d40d180685800ea002c440d40c002074103c50700032070f01d13 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 714243633 1250 714242383 714242393
    0x9020703020a080c010c20070911040e09031e07030c0f110910050103050c040302030601170109150c020f01050402061606090c0e061320070809090c090a0911041707030b04 75
    0x1481032034155403048408012081c2002c00c0343c10f42401e107d015402414100040700141c0c018005200c1029000742c20b1560359030f004012200300315010480303030b0800030f81402501403140030ba180c2c0d29001c3c00d005003040b4a60360082c011031800c00c0d003d40745106c8601c441003003080c02e00340e01d43c003c50083c005c0e035400c1c18100710038260342c129800780d0350100c2d080c5070001b400c01c107013071082c0c40480741c00500400312079287c1490030541c0c5a203c0341d00364a9540703a514500205900718204410340400e0900001d500c420010b0082c1040c055081d051056410301c000c2c0405a070300c00d4241c0b4614860091a2281c0c100d882c0341102c000c4c0000b080c010082c01000c00c0000d04c06980d45043c0c2c1c4540e905640001d00ea6141c0307000a011131700402c0b818440100d80788800032140310300304042c1034042c1c0700710161032503e0f844100180100000700c4500f1265a000611108039051040203900204056101880005c0d410b5051901d5401a409890407200c00c19103ca0550541001444003e507000380724100981454100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 714244883 1250 714243633 714243641
    0x2d0a0e010f0f0b0402070203030703360303090509270102040f0306060f08031303060504060f1406120318040b0402090618030105010f050f043b0606060702010909020703020a080c01 79
    0x50581c2c4500e803010703000880c2424000c5841156005001d14540070f00c6540583d0120607413010104a4190131040381001001194908035100d02d17044d440300040d18519000304800050340050f8000c89042c018800c0c0c090b28140c010080404421049155044040c00c0f07900a004581c08181e524003561030001c14045103512003401d0300c08185100055039110186103039207220300001140c2035002c05100f0404200542d2200c1d421030b01c2003d02181894070f1107100003c2c0c0d000e4801c8106182064420b000007442d000525541c0b10906c20055424403d11600c406051950a44024043c944030f1a0404a07580c0700d904072200c0220003450b5540f01c030700342c90294942c60310f00c1c00d07218000c3d032070600085a141104c0d40c00804a800050602d10b800031503c09001c00b9110115003a036103040204003000e043d404c00519080c105e42c0c2c01c101000c81d180c80c00000d600c1d003603000d80128040d0008014060140c0d0380140d5110903903c00e100050b80d904601d01d012440c1500d005009410118003090b518410f41d81900 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 714246133 1250 714244883 714244901
    0xb01110c0f1c061d0d0504060507020a24020606190e040212011409010c020309060319060323010f06080606060a0203040b030c1c062106060302040c030507082d0a0e010f 74
    0x4015585012519a01640c40f07117444101004240140002c00007540314034010851280301600c2e00110356904c0e11403400420718460400c0400c072a0342d011310b040541c10049103a100208031420724082404203030000e950701c882c0c041c80610f50030031000181035484034910409004000c5000f00201c1c4510003035882d403141e0960b0f60142c25401e1500484076641700000b50303650170000401c654619200c2401d540b08441c0d103442c00c40702264032450000081800040c2100d1104080c4000e000410384102825085070102d450840820345440000e02919000086581d440700054510a9451014503010f034a98010790b4031000b07100030000200503042090801800d10781c00309120b0300c0d4040d16400404070950300c880c028540740c0381004900069698000d4503002c0003a00889000030559100c0d0041000d8030340c11280d02002c00d07110003d04c2495a4001000e41d48940c18842c0b40025001d000184000307901018003c0340904043c4011819201445d44150207649100008009500030030305980c1c040d0440007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 714247383 1250 714246133 714246161
    0x604090b01021009150903030906060b030601090506030c1e0c1609050a0b15130315050f0105010f020307020105131203020703050c03010e0a1707140f010b01110c0f1c06 74
    0x5030f80d10502000d034001d404900d035124540517000c13217001c40000d0041c07510b000103038201a1180896400f00b421442060081c0013000d5501e0b9881c030709100094100d071280d0b8000d5006607020010480c04140703440981d100480382500c001070040d5002e91000060007040440e8155000d0100c51920000b41610480100d58032b020060009980c0c3c1d4100f40f00301e0f0b002100c1c450300700c8000c0d1060f0172000c0c01c1c50000c0002d0036a5202c0d200034692261a8140709111041d02194070958800900c03915400300908a40144000d1a01510009940400031345038001c01030000d040c0712000c102c2040c405540031019010b0415a0044181c104140c18000d548010310703c000d4415000b00350300340c0c0c0703182010301949010380d0700e21004007900105030b510258030040c000348030b00804005200d07150000f8008101d1552030414007008050b82c05038070380d4140c00c442500316054107112054480503e060400300d02d01c88005001c50b100d19066891001180e080a0714010914802394440041003c1110607488007a044102e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 714248633 1250 714247383 714247393
    0x307060c0b1302031903050c010e010e0c040b0303040303030f020d050423010b150c0c03060112060b011812050a02151308162310030b011701030b010b0c0a020604090b0102 75
    0x182692182c264031042019426402100c50a010004244141e5131007a109190451405841e100150700b1a4407040000002d40d46a1165a5a003142000050080b1804442c100f0403841d07188006a40c030b01c2140702c001d052507120500305144074055416541c0b00d450541c0103011914107440c04100f00c00e072040031100340002001c15028040d0052140c0c4c126840060680e6494140d084a407104c160010034100800303110b1030a0502454400f84125802040191043d42d07000e00309190043c181c07401d2001c95410000b00b21400001400e0b10401d4130211860340740091604659800e20341e08004054201070341000e80c040c000d10a80c024580101000850b50490211860701c43c1212074641e00807200741c003540c00c00f4000500c42e5902000140d81c4206840c3e0700c0b221145940c2000c078840e4030000e0701c107401003659051440981d58001204400006807040c03022000e6045a951410441d018014481c44d1240410141c0300000c04001f04550540c004242c540c075a81d442d152070024090a8103001d0060040c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 714249883 1250 714248633 714248641
    0x2060f071b0f0506090a03020406030804170303060f12100504200405090c0931030311030601140c210a090602030705062419050a05010f090915050307060c0b 69
    0x181141039410b40c0c20449000031290716010800105402881c20141e0140c050f0500100503a224415500158801c0c10460f450394035101c0070100300d0340f04035a1130150760801c20400100b562903401000c1152803c4802400b0018131139110351034000707401c3d100c0050a02c1d0100780011b0001c035107608840002001000504410804140001e56606981d000140d03400841e0340b000b2803034a544140e6005180c0500c1c001c0500400384980389920111001d11a06250081900f0501d5410b000d403e1803801c9001046203142040e0b00000c0c401550801c00200c02440880e14015620040c4580d407002a40c111000250000e221021090350703016000e10b001194080d00d000814500200c26140643c0d044409400d1070390701c840c0103221240741b11046507031030551481501050740d5410320314000f04114401858081342014244241424203403c01810300180d10502a005944503201800b42c602c080d202013a81d44003050310f8503408406400c503542c14050302001140e4603a1081c074141d211401a0010035082e15 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 714251133 1250 714249883 714249923
    0x9090b010203181c02060f070303050a060312081008030d021b06041a04021804080307080f010b1e312903190c020c01020c0a06051903020702060f07 65
    0x85080703190b48010f4060900004a03207030280711a81d450114240d032281000e220f500161300ca5000a02540003403401048640078554036200c1d45910401000f820800c050440e1204920300810709003000811914000095082c0c540c05808001420315070200c1e42c903202c0ca02d081d0701c0a500240050b8290b50f51600b06500084ea0003e1654050f030340102181c2d8600800040034a0310f1640140203903003140c80c030910860302c030300400081c900c1940141e60700c2e82c607030400400c001c1c00700d00e024140041a050410051101940b810b007102c00005481c111601c3c2d00010141d241064003170300e820f094088959210741e64842c180315110000e40d025502140b9421502e0381c070051400414005030005180c80348d2180c0c05802c440000540e0044007007401c5503070580071003281e00141c0752061201ca0058002040c15415075070100010125020201d03480750645041400041c124001c40030004206200c000210720b4050095046880c00c6802424583d87d403100b000c9034941c581d0165104840c00f10300e40d981c1c03401d004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 714252383 1250 714251133 714251137
    0x90c01080a1503080d090506010f1e030201020c0415080303160f020708100507120603080a141204030311191814030a170c16030201140307020c0d14010c09090b010203 73
    0xb102c00003034201c1c00d5890b5590b0750b4009006081910b07548501c01c0012a8080043d54001c24076417644440c01c0d4100b82c241d0388000c00110b021004203403440030600040c2c0e0003040300c29480000b5107001540c04111f414158441410307078000e08283c0030001c00d00012001240d111006008141c03100100850000b00c100c0c1d65040310b1203a40040d0f080312400d980300c0186900116000a5549030007051900103079165403c6400652044502c0103001864001d03450f0480e032480d941080b14100181043c056120215405400400040400d030703a0301408445240d1072400d4441542c03041160080c0380c0b200c0d50f000f46c400d0b03070360354250030344031403800d5001590061400c3c084c907100d08041e0151941214555808800300110f03424080180428050404403500070005a450600d004880040252660002519100e11225150070036282001040381d01c540008002c1c1881ca01512a00315000d11400d01106011101040382032950800c0900911180d0004540060719074440040064801c1d40c001a41d0324 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 714253633 1250 714252383 714252401
    0x60a05010f020601091e02031801051b03160c0803091005010e1e060310141501050324010314041110020715050705030d020301081005060d0807121205090c01080a 71
    0x182e00c0f92005001000e50f079000300e9691595501c800b01c142c40d00748040710580c0c004580794416000c16021103054404240156034000070f07070010491050744040c0c8030601c0d07440b000b001e01705201c811090540d501d074400e2176104070350b64100784240e8890420f90403560311811604c3c000300704542400300128108814602c2c05028060800c0034644440c1c114010002c8107500401c2070340d240c052268880d0149809004d210824030408031303541c0c44c5140082c0815001180080042e0410409000300303c83c0c4004030290120040215a9084281414800480c080c0c5441c41c541c0611200c034500780420003100310074006880008445110012000010480c2d450703010380314145440408040d01030030310f03028100520031b00e4042c1e82520301c1c00241e4800302080e42d2084c0d000c444558407051100002000a1003815007181040399a4510124251210740d02c0740510b8038068205140d0301ca102e0203140c066480300320b20352141503050145141155000d910b0f01c00c04460180031403100f0002910441c110f00c103054103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 714254883 1250 714253633 714253637
    0x5060f010f1410080a14190e070501170c07020604090c08063307080a0908070f03030e041d010c08160302040e010611031b10060506070203150a090c08010203060a05010f 74
    0x10b0f04501803c111500c403030103444035811035543c00550f200080000515441010303006000041d041c200040130b41114021904905e40e900403441c284041d0f0b900c0240c02c115080900381c81c640c240c07200c0ca50844580b1403101c000f903100d2800280042c16103015004858414800e07168600180c2d540c0d0107004011081c0031142c2c520f0000d40500d1000f84040c201400040404880050f080ca0f103141e4480e2100d500140c440000301c0d14800041050085c2000b085c8040c0c071144450b0400c4a1640d5005010301c200e10198511032511500c0b0f0007201440c10000f0b80b0a4171440e0020b000800420101410303813101900c800280002500410421a000e80201c40480f60411450200d42e8a80b8108403080220627401507024001000b00c21015000c13200380e649005480c3c00506099610032081d4003c40d8440e42c401c9001d01001c4c001c58000d079402240003903c0c03a0782c2410703009450f518078418030010814040001c0105030680c0000c01d09000543c0618405d10066544071629174031000192010107940a003040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 714256133 1250 714254883 714254899
    0x40c0302041b14030703061805010302090711120a11191b120609031e08011d010315051b2a030f250f030e01080a0c020d0c050a05060f010f14 62
    0x1c83e408400d801554130a00614002912546500d1015000c1140c0000100090b0310f0340f006005610300400d5160300980a410700d420300000080b125619401720079040d00000c0000300c2c2c846c034150700410081040000f41420f5510202485c8034450350b1035035040040c0e600e018000d514581010a4a8020094810f1006a50544543e1b90350701c0c4080e1654150890422500100034800060316002403103030b12907541c494980d00d40c1000840101d625210454a150300c828500410100380c00c1218580021501800850740303680e031088004056241599901c086880054001c100421600680c48039070b10f0743e101c498013243c401d00c480c3d5030b0b40103c03040800421000c005489660013400049203810030100307540803512180d174469548507140003105070080f8120540d001e45940e4424102a07220502a108004071020070344000c0d610442140ca81c014072402d08051414000104901000d09078003e0484242e071624a0082c0e58140b0280306402d50041c0064010502e0081645190000f140150081c0f0b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 714257383 1250 714256133 714256157
    0x50a03060203060a030f0c030506060108191a0604060e1309021f03090501020a03020306010f0306061d0310060b0903070b0306090402040f0f05010305010506100e03031917040c0302041b 81
    0xd00070350015114940c4803010810000c0006d00b071941c1114a2409481b0f01c8840380d1840c1401317814070030001e0241341002103e02c10868000c041004020241080038030020300e031040741c050f05a18a2a20b000161f000740003280c00910300d680074403119400b40098803e0f040e101d1401c403c00046c0c50304043c000754094201095140b02c1040041c0d40d001801c858074000c103507500c0c0764803000d08a0380080d0603030000980000800c4807558122144501400042c50100640c901d050070007440c10540b401e4591403640f070451100c0c001d503010462a0014030204104000440d03544c500d08002e58480031503070340607018401000030044044815a40702d0708014040382c0701680c5542c00c0000402d1001402038009a0310052580086854071426018510403000001c81d418002e00308060901501540000c1006080d041080c0e0b450110036a011101c1c0380c1d1030ba041c00c070300c9402d0039118004000076105151032124100030078440c910400b542182e001b45c038104010b00c0b0351205080151046400030300890000c00c000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 714258633 1250 714257383 714257393
    0x6031509030d020f07210305070816050a02160806010f0503060114010e2142150d030906030c0f0f1d130603020f0414040f02042706050709050a03 64
    0x60215040c5640180c3c54108540c1c0d0f40030034901b52143d440841307a10040e494501c103416124007a0891100d0404820300e20700600403c06181c1090740b191704011000c640e20380f00038020400030703080305c0100004d081003549a19800d81c1e43c800c03d20803c0340c003064010000429003000305400b8103a40c1d0440d65107031072429440c0156920701046051580003469104031407003018404160703d210401d86005030160990b420781d0480e03180d054400c1948441c00e0740040c00d01e45004078110034142c608040c02e062007640e0b600c0900305543c2030411841d402c9000301360410308050b0700c0b80707090096030065117003000319038140c89007251020024010680030400c0e0381101c14100340a5406880d0f261400500e56004451001c08540d00c142200029601951034100910171450000404000c01600b174030100003006038940b0680704505d020304003400c000304c0c0d100c11a0a6442d02d4000c04502d500119280d03011140e411104001080c01341c02c140d48680c546170205040c18030402c0100120f03100105000201421501c0d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 714259883 1250 714258633 714258637
    0x21c050408041208030604061a090d1e050616021902060903070b040f030c050301051608090a0b040f060b040b03070512031611010801081501090e150f06031509030d02 73
    0x4159a00340040c440011540c0b0003c3c09600068401d0b490592a4240740061000350b5203160000d00c40c0d02d500011034008441c00c4000d807004818115012141c00201d0b00300300c002070101c400d5896004440100c03400500c040022014042d03403003101408041d4124520882c2c4031015516800580c0c5000911000580307004000341c014620002d0039a241e030b507500d1117681d1460344030f580840308100065104005100c043e403840001484203900a10030b524013034440d41d148000c0c030b02c0600c3c00e020aa5010800c0041c0400408484039840030b1070007c917040a04000c420001e107000308560503414101c0340302c0141001c0c0181620040043c0083c408107061030204801002d12220b001810300c41403100401c04542940c84004140c0200800c249580d1641c000410740071050b085088123910a4180c03e0118030f506c140d540c1110b84035900040c0c00c074200410785080901c580701078075180f08a00144001208140126406401e04900719110b80c500310700541241d05048641880c1ca81041c42041c01046039500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 714261133 1250 714259883 714259891
    0x50d050310181805160902070b0f18010203041b050d030c06050717040b0906010e0903090d02010e0405040311011a0603190e07061e0e1f0e0409140d03021c05 69
    0x6020410f540366286070052240841010341e500d602030000342107030101c40402000a001034010544c9084402d8507201c0004001502841108040a0000b81d41c6905482c4c042610140e060003590f590910b0b042614501c0741c4100300c0031000c03024404c0083c19103840303200324009a6041d15694040c00b000d0f101d0b00c0c01404002c0840c41848104031031080000351004620340710350700c0f424801b2400c0c144140c00307918082c01608904608985542809400c1c0000030a80d0400401200c2501d428181c0784012502d410a480c42181c01c6414101404105038010550034503e24840008011a061080d40d40707003c80001804503402680c1000403a01c044105040820300300000040840e008143c510324034a480a180c0c01100002c8804c59051803214902c0b007501a6840907191411a550210000402d00c400200e1401c00844c5a8240444501e000e03042030710b94020000d0040010850b02e040a1780c0240e56140d4055290040c1c0c800403001e0b501078402e860105424203442e07a0709402c3d40c2803007402000080c1c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 714262383 1250 714261133 714261179
    0x5070812161119180b030604032709060608060f1507032f0307030e09040201171e09100e2b020c060a0905040b10082206090c03050d050310 61
    0xfa54207010280c84502c03000040400e03501c000d915940100d02e01084460140e0310a10941100d814040482e1748040440c0002d00c410f91012140802d891340711401602c941d1006600c24108000040e1054006074510f105080646001d00d070b1410400401c08103000d044e103801c4080708280903180c04684544180b83e04c1d401c03c00b46804495030210300340b0350728034035420822903103910000e9000101030f400003241011140a98502000d81015400a85100442c8009903100b001d1000000c5d2440c0005403600c5142c82160b00c0010981406a049612400303600e4030450442d081641000e102e0f603000880d080c111818000520050360034041104039488581551070031407050742002d010945d1081d0040c003c550031600d036500d0036841c1c801804203942200e801144a2490182000e00c91504600110f0780400525620700c7c5940c94514050780780101d50901030300717280c6000009020000118407240c262805072088621409020804688601c412144a081b50306040c608002c02885419103d034030401c0c0c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 714263633 1250 714262383 714262399
    0x1a10090209011b0f03140a2001090b041b06110d2001140109060501110627030c060f10030f0209060103110d151d040215040b0304050708121611 63
    0x82c070020030350f10043c0d84042d80c000a82001020030035402c4070100240b8118401d445007000c2a03920040d03c05644490036448081402d200b13045904029400000c4c00713035201d0005282800c00b400c0c4107504c3c6a1030000050350815034000030500c18021214202440c0c1d0000080010300f60b83c60040b030b40a40202034002410340321007130400b01a2001e00a6180c2030380c035195540c075150f24102d12041500c0b425072086051146a10517103d1076034010032030a0340000340000d822420502c842101d590010002c0344804107000200301c00d1000040495490b000d08101070800480d6159610640000d040c544001400000000300100c018105245002d5100301c050500081c460720054944225a1048a001c4c07943c1756200680503444c1e02c0c01107890301030324541c0840fa0301842c44c1000400e40810250020b44111404440c0301e5001049100704e034068496420440d03183d040c01d191050f9242030700e01901d0703401e00038511006e544000c110180c2d1040c803039101e00841c0600c4151204d81c10940c440326099001805 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 714264883 1250 714263633 714263657
    0x507082a0106080c0f18010b030a1b0f0c170c100501150818070b04090c12110909060f27010e100905070e1e040f09082b0906091a1009020901 62
    0x6c04c0040c58001c2c81c484824550ba89494100901158402031560f5004600d000c0d00110681e4000207103e6031080a0501d400030031480c2c140004030303e541e40050289500000b0701d08a190801154108038003510300c0703090049980710300c2104100c061074520380700002c40f49000104444c900c010602452500350b0103444180d86c5410042d6030780d9126402004e14151140c0d00c010390b40e64050314806011005201c2007242411504440300944180c0e141d00b0303c110b40d544c0120ba000c0c0c0d0ac010001030f10f0700d00101091000e030710318980c0101503140700611041020443c800000c0b2215412100c91164024a0560107420709001d00b04004240c0038040c0b0007000304e905000401c41d12800300c480640080b00c000004082d00b02e00402c0b068032080340d00d10704581d0030410700c50000780c01e4405943d40d280e00300003280368441d11445401c03030900170844454010303824418040c041c0901c50340b01c21602c0780541640480544003096490701005c083d0b0385000084000c6104200b0481c00e0382c064041e200c81407503c030060b000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 714266133 1250 714264883 714264919
    0x9120d060e070f2006070c03090e0a0905060f09060c07110d032115030809031f02070b1f0501110a060204031104060807030b010311010507082a0106080c0f 68
    0xc11206400030603440155a0480c0780c2042c0e0900c50601640494141040d203254501c0d1142d45c06803170b00b003e00c02c1040400c401c050090a4100c050070f10641a08054a0441811005041f0a0209a889008440106021031111039055214910790002062036031501c01032084c0310741c04040156408410350300c103c5601c3d0346990051040d64000d039100080900203a150006090110070621495407a0905a21803116503c00f1441100d8000340c407d600c2c4c500130310200b42000000c01d0309400804c00501d880e008003143e03501504d490b80c081c6c101d80d202903079804c0943d5140d001c070384c000c0c3c52040301c00c3c03208200940c400c070303440c07a08400201b0a540304135201e559101c050344c01079001203800010140202c1e40134289031044034000c242140040021030301e1f41c1c81c2caa00c013500600001e0103000c0e0015034915203034080c40072105000c2d88148020341d101c0c50501c2101c9070620003500100900c09222000d140d07003005005840a41c2c0d9400003a00a9048003030410607100d444606882c3c0200028072441c403400c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 714267383 1250 714266133 714266159
    0x6040222020d0e011a0d060504061401120317011419050303070f20060706020906071703070e040506130b1810180c050a1805060c071d09120d06 63
    0x40c003402e020800003c0f403107825080d40e0510907410011186480d5001c2140d844841e5000b81c1e82e00810300094903166400e100f00a013490000c1003d048082000014070f40c82d040400c0c1c002a40695910442003a0800140c0c620110a205a4000e100d50101c8200e251500000080d45542c041d0134043d16290799030086400d542207a202940c0e1013250b0542d4006120380841c2d54004056080900309a40030303207500003a0b56019152016000700d5011441c3c40c0c036a21044101c1d080181c000f014050347e0214041200d0459008880070f01c0010040240c1e42440e080c035014050042d400100300f030141c0c01000426800602d0074103c81980308040c3d0343c0702d40b6064910380545004103140d01801050174100102040c1c19007000c5410404603141000ba8400e155210b4144c644450f11031a02e440e0450080c070191089603469002603a00c030b0800034140e400d01e0070009101003110300040c2c001c000e040708652018a4043c040300c21160301d400c01031865540100c1a0002c00d540c0703008403c000351090701e83c0c00c2c500c050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 714268633 1250 714267383 714267397
    0x3010603021303020a0902130b0a05071424010303110120070204110f0c07060e0f120f0106080c030d0e0319032307021c170327010c18080604022202 65
    0xd41e400a6a880743c41c000d1108e060140a107640104d14102000200401d05e1240ac1c0018143e01c03184900c580031200140300d4040e13903c800102001410741052011b50240c1c0c0d0a110480100e041500e201903c028180a00c100442c1c80010b02c00d40300c078100840103103c0c0d00000040340d00030303510900e92481c420300c2409454182c0005c40450b40300d1000c20308071480c01d482c5401c5002440118034242e40c1e00c1d43c3d03140c41c2000d1182c095a5252090345000055403a0803085460b03d03071603500305a00807504440010741c4a00c3d503c022021908485081e000c15506050001c201c10f805400c040c08074400c0031298150380c2c072524442c2c5000c0c0c0c0408804070200356051010300300f03942c12290001e0601c041d07107400c1c440c1c207061000802a410344120165910b00c064070390850a003050580120004041e100401c0c3e90b211b80164120f81880b00b61088035549009015000b40c2e034000c21400c0464402c03500803101035406580758036005151075119034007044020000c0460b0b00c032001800440104403070f5054000f510203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 714269883 1250 714268633 714268649
    0x93902061602070e0a14010501050304211e0e030c01050405030601140109120501050406110903060402040c03020d06060e0a060c03050f090303090d0b070e091006030515042d06050603010603021303020a 88
    0x600c132000005901c07000c410b170300c23150411109206100c0452400d406140780100c0402990800c40480541175891aa0565032910000e10104583c03c0c1c5507001085401290701c110b050302d034000307000e900548184c01640100c40c0c259001c030005110b00d05a00400030301141d014107004141c1e03941e1b1000206107905c1d800048031240d444a082c0300070080c2c1390150f201c10b6034600c0d03070381424202800e001c00d950700340042019100b903441c4d8481c2d01c0894001c0c1e045903000e225084050000a403a144090581403101400e43e0088411050000d42e140c07103012002c040f01e0349596501c0c03500310700f5801060303a0b42240f5540c6034540802c000000c2166200d51902910724451100749081e03103410500a00540d140384890740c05402c1c450304112041c4036012740030003515807904001a00391200d50b441910b410220703482c0fa400500c0c00401c0d4a0340c465801e0104030611040505003000c00c0c0c0d842801c01030f50560b02c01d40d40c0003003082c801846120300a4015001c003030745890b054012280d4a0700021010940c0b5070107030310 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 714271133 1250 714269883 714269891
    0xd1d09090a290106500c2104030b150a06200109020310091b0e0103120507170706020d051009060503070803090f0604093902061602070e0a 61
    0x19181c0780b00c003040d4010034003400d0101ca0035a04d42101030070341150314082a20108480f00c001c0c004010296401e01c0300c1150108070321181c070024066070b8181d220400c81d100c1403280014680c114028012072144500b140e056841c10a490365886010f800c10280c40c00b44036107960700407883c1a072a1840c03048000d103016580c0082d21a039011040424026101e03000c886641007183ea0130268400103542c006031400031000144485841c200180380000e17405011200141100c0001005450030340030b60305036401540f0b8040514400007040d40c0d540300b2010002d10144040c020400181d400e5805400510b006820152034071003203002d110200d503070458080c00c0c600d080380000e0210403070034800c803000303080e06400030034030307035040184d615034a0040e85500c41c8100045100e141c0b1030380304c00b0256401400b58100034088190703922411001000d40c1c0c0d091117030026000e40b41100c0140c0e000040c00e605042307600540b50503203912610183c5480180319050940c0b10704000010f540761020070046c49240b42240000f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 714272383 1250 714271133 714271193
    0x70b04180207021c151a1516020a030b061503040c15051b0105070810030c090f140106120b040614040e0f1501030c09060803030a020711100e030d1d09090a 68
    0x141296452800d490380f103007080607046c03d0750b19441c3d900101c0c200c10010b0a900c6580e000e002c524030510b100b8009401c40c00349540001044036650381540640b5084070310100f4604100e41c064203038001143c000d010081c50f103e0030007140400c2143c13248002824503109107409100425001020066138a8101607952642045031303043e80300c2d00c4103421003082d410745245e441c0b85454100c801c20a0740143d40a0903511048083d070900c0e0b542c00b15000b000d0740100740c1c495680d20b400207072039040d03540c003940d2100b0b0520300d20150710b00d400c3c030460f001c0d200c0c800b61034014408440b0901008000c0d002c00c481484c800d1201c3c0310314800c000c00403031a0b460000e0310400c581c0d604514240c0c3c100313201d0b40d20110005080600c02d000c0c9001c0030060340c3d8000e002d40c03c0103071511100e0411820350000301c010a80c2003502084410340141e40819035603065801941228000c004945003116101d000c0c80c45549011800268501d007803030304074404e64100350100115507240302c00361240d0080a2000c2d407102d59202d4060f00c01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 714273633 1250 714272383 714272423
    0x2091305070918031b0605090d0e0411030103030e01030f0e07170607080c130b040906090b2d030a021e100f02030a03230406060602070b04180207021c 66
    0x2110140001180901880f80e66205002d80d452510200409003e248802000c038201581d80c0c0140176a041a410311241c240550040c1c0c551050145000014014400242c101e04150180390b1541031031201803491a86103403011240582c2304000c2d581007585800f941d148802e401e000300184454840060440306203004001081c584502c9402030081d000070f4100101940c10a22956000100000e190351303c1503000415140342449820111041d10702007070100350088a40d01140070f82e55510010891907000104000c07418504c80c810486050140d4100b541011045000e501606005011a000410141e001481806484000803041600310313140f04407500d8406d19040000030181822900440c040800075241d00c12200e041003490b07180c0f0400d400f1818000400d810303954000042d01e440703003007614112000c0c054a2084a0042c42045004101445000c04507001c452000350100143d46840d4099400b94120a00680e440784c500100c03840c1401070800c4845c6881c3c4a2130410508414440d50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 714274883 1250 714273633 714273643
    0x1e09030709090f0b04230115090911060a0e060f03150a080604080a050d1805070f0803042105150a0c1b0204051008100f05090607050d0903020a02091305 67
    0x70910307441c10b042e010307400f003411426801c40a6070406082142d07541c56041580f58642e414010001c0902d030013800b43d805102c194070003a03002100d1291302550580d22080407055440d051409422050424640151480c0c0b400040c1148001402c0c800802d5075810002042c9810181240861907800010442030070070b55482c03180400b4080b0750145241d03040c0308c0841d82d11040240018400d0500140c90082c06000d10256a80741180716011310031815039280c03c1c124103c01a03001c0b0b80e00d1049107804503071200903225440130750b444103004504282c074102003143c050001001684110711207490b8800422400e020514103403c9504102d050703420003816075000c075518840500100034042d04501d074485819641c0c048869011103001c500c0c0c0c0c840741c407500302c080d0866000361a01c0c460101c40d200b040c44160440d452404081c0300402c1540d543c001060b8542c442120408009007003000444000b400c40d078001101c01c1e0081c4100d81181c0c1ca10750124103010301c242c4001d4840b10310226518100715003004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 714276133 1250 714274883 714274889
    0x604050c0a080114130509010b01030f0204051c06150608100905130228060215060a0302090103020118090606030609200913021608041d0106020703171e090307 70
    0x2400074075055008000402850060040301c00500a0f18059081d43c0c0d19180c0103055110900000c02140c1060780d1524020034a052036075000c2803c00e41c194940007094400d6800311038010b003141540301d054a001420240c0c8820045403210395903081d0001256078424a040545001d48640304141801508003004002e10b5001c11402400c000030801065000c00740d018015905841000c401480618194988075011508003420810034a000861a0f40050340da01a00816004070010343c50704010b101c20502e890002039001b600c40710040005510860002d0583d84242400380110b9440d03c0c0b992080d00c125030320440009455009c00c2c800c0e181c43c6e10130883e0304d52414401c58044014590641c440d40211440d5520035a81010801c80c40c2096404803002420015040c405041151504580940082c00b6041035110881ca07207843d40f07410344d0825070580b409a00200841850355035041c200e414184041c0c010210f080c0083c0c0c2240c0101c841d060b171590301d05114161505010014545005505d038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 714277383 1250 714276133 714276151
    0x1810180c0902040305071502010f1b030e0c030a020d03091e060f020f0709200d021216050304200607120e03010207020a090f060506120403120c17070e0303070803060405 74
    0x21040000410005242d0121086072032051791259901f1001c1e80180b0050540e0001c01d0304200041c0b1a00303441d481a000002141d403402c111058045800a5170340c40c0c004030b441d406501c4858650003501d89000315582d80c0384607180641c105078680948140940c16013480c0c01d248415110140042c0390407881c4586003506ca0320040000070000a1501c0c1d40d0b29103445101c100355640d09174032002e902d4841c0400c9a441c07200a400365185910b150340c01c0294401f1001c0b05e498004040416201c50250840070150405c55445604544070b58886802031030011140c0841c0ca0f0102904003616101c4c50064501c1034090070301d0020000d09028007420141d840b5030524400e9204100500c0166103805142003a521180400210090003c0c00c03000100303032a1308002e07440503000c501002c070310200c2d03c2d89502c40c034826941d04089600c0380c81003e00780c9011004003404200f4019044040c030014006065201c034081c900b240341c00601c000441e045034401c88007901c1c0c20800004000d1541014010139401000103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 714278633 1250 714277383 714277387
    0x5071205070f0f03060b04170c0405010305150a1d010219140703120b0402030412031802130506040b0907180b0c1e010902041107291810180c0902 64
    0x601c0010b00300000041e20805000070420340c404207034865441203010340f0500803125503440c1c8680704a500304d6031205141c0c9442c4078945d10800c01c1d09103801640e0480398031100030701440b4520402141001c178024038600d070b00b03551043d5007100d8014005814040c88541c0d4001a038840c91504942540684100030030284040024583d41c001c42660490f17005c0c88d01031500c21002002210940c02404412201c1a8071600120501061150140b1281e00d464904d403070801540c401c003071004460340101c000195009045000880e41010660003040d40201d0007000022540610800100840320030f0b2458400510100c02008400341594003200140042c084154105040a805169601f8504440c4040140d01c50b038141d043c00425085401c3c3d51398010020301940000c40c8869125070054078080e520300e440d03100b5050095488881050142514800b96001c5658182505080c4032843c0003021443c410521420282d0300300341704d2190804004000401d0107900c84c242160b401c103031504098411441 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 714279883 1250 714278633 714278641
    0x31611040608100207020f030f0c0a08061003060b0301020c101a0d080a111e01020712030e0d0e0d150506041b052710030b12070f05060d0e0f0105071205 67
    0x140916410001d21005a900d170594404507450300ca50004858243c0304000d1010301c20600810074441141040d03400410707456486038500e6450400707554009802102420600124203144c010311160710010300054981145601c4c03c41c40c1000e42d404803620329555402c10300e03144000da05403142c1c00804844c0c0d40c06a910503210803401b841440c82c04802e0101e0300188045119081c0220301071a000e001000d060a01c240c0b048601070351062030102e80e030005003041554103038041c2c81502d9195103140000e0501610380b15080d6a0041801481c0b6032240140c07108000144214080d4061030351381d00000b151905190047c401910a0f1080342e4011040e08241c0c0c0ca03040b0752102c1950302c42544c80c20800e546815030750807000c900d2440000b03503810148032202d40000d185c144d0002c0c3c0c40722605a9010160072051070140340c40b291a409a5010031481c160304201134075005000c0e10284078201000213014508903801803500d481c561844603140d44460421401030303082540c0150100c601c4134240810310b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 714281133 1250 714279883 714279899
    0xf0c1b030307150e0705060d020a091215111e19020109200a0902030906040b010e011a1804061d0601050f0a120e0f160803190c050a050316110406 64
    0x42e00f5460594080da16056424031a0003005020000e0202a121300d54071400d010520010b544808580400310b940a0f80000d60006141c403c015000c0d00030a03202d0120307012840d0800074080011201e041000d040c081d0322010b401c91000120300a5803085641c1da0b40c006400011450595102c60314256494841e540c404200e00e40404003105034105da10141c006607040028402c03540d19004550100d102008100006000042441c0242d0040b842080943c2c0d03191400c0059420901031011400d081c081100c0c0c8403511030025241108042e1500d6804400010104d400c8541903405810000700d101c00440c207041c00d0700070b1030b038002c2d0003803030310503d44141400c100f07101307100d00a900d4080185000c50900d02c045294094400e0689120a13202a2602e5507482c40d5039049100400b210701840590000b00c0030400021a1055840b225455944e02c0c00c8003c103542c0b00020706000d4802d400341031500c3c00000c500780010600388900c413448080d86461802e24400c6066110380890107140762003c1486445 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 714282383 1250 714281133 714281153
    0x131a1209032a10090305030105090609090c131e0522020f011101020d15150c11090619060f0306050102011401090f0605060309010632010c06020f0c1b030307 69
    0x2601c403400c441c0310360150706a100e03c1c0089070012488042d01c0c001c1d0b8007041590010065040b182c0441d120300440d02c840040005540d07050b100d807100c5521282168000c0e00702090301034200e986003803000506880201c0002d02d80030300c3d01044070000d640c540c04c02003140c5450392021194650300205030404e01c41a404102c00c0030850055505000300c2500f0350703800b8842501240c6044100c00c0081c41410850340e50640c9041c100d010352003809003034900905003a88a110b56985003a0890b6600342c2110301c003014801121006804150400a440c00440002103a66040740080195a03214250040c031290004c085404541106046905042000e2596030070303824860b054515840f00003440c00403008010f4014400765000035045071005c002c0050100066020f0002c5840c035080c04a5a400c10b580c803c280341c080c1c4415407000000400f24090303d540301c0d201c0f19002507c81c41c001894500700740700b020303d250020815106958081245d144008401404460f4030010641c003d50402c0c8040d5039203401c038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 714283633 1250 714282383 714282427
    0x31009020924061b030a0c0201020709090809060904110a052a0a0b1503070807212f060d0506030723090405031207050a18060f05131a120903 62
    0x41d00c2c0801d0040e8a1030412a820841224113811130765200d510b0500640b072120004003da002d07000d0783c0d000107000e034880c0c0030f10200c1e954400c484500c0c2c0320901301000b005420088203d0703009584c80c4d00c3c40c480c2c078851130020300c051102500c40b83d46031007900c0d01c22502d0840451420040e0004000d075002d07a4400011100e91860340010644000d0355021a410900c0c03079040792499041c800c0d107000081d4280040384680942c2d1815940710500d1450b2500300014150f5124010070000000004410000070383c64400350340007404400c4c0383d000480c580011429004080d4450000b03075144203101c6140750070402c22008081d40030f000302400101842c89207100d0203842000c0c4c085c0608030006020890107100312510503042072142c0c44907041c80312004220381c0100f031540010032213640102d4800c03036a290070320088803066640c105855010b2401100e0f40e030421000301c5800d5000c5007020070351650400038920100080c000042e00d07600380080c1c003003141070040c11681180e00304001680710794190401e0b00c451 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 714284883 1250 714283633 714283639
    0x207150207030201200a030b0303030103050d051e070b061f081b0f03010906060f0516060f0e120a02010c090e040206090102121603030b100207140f031009020924 71
    0x4070030071410240d0240c030b540050041307070340301904100308a07910110141c03102c0d50080d0340c10400c2043e1030043c10b07075a200c01e020242440c2c2c000940310b03065510030f100505200e050b41561121283d2a5440a246a04484401c4403110122400c004240c06d0000c030f80d040703003000e109014030380f002ca203503016000c0180609529254860300440070070f03d00c0d060045036007408070010816502e60f51003a10400030b0070b030f50103001c0000e0b440318420748005120340c2c1941d110600522031071420703000c0da540d800700528180050001c15134035044443e81102c0c00380300b640d4080050301d04103551107040311002401c58048507012014843e0081060181403803c5458a074460745c103030750390341d0740b00b0340500140d14180983c01c080d901d009001808001103241048012501440394400740308000141041101e4a4a0f0030b0b0701c0c00c0140d2049070308005030308003803841208180002d449451142c50303203030200342091500e0319021a03250b11503907110114100850a654000e02c0c0c03070a0505d00700f04c1e19041b001c88030130070801071b48 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 714286133 1250 714284883 714284887
    0x5010b070209060d24020403141c05040e0109150b19090f0b03011401030b030d020c030c040203070e0405180a0317010e060306040825050a031706030a0818040903200102071502 77
    0x180101750b604440c003940d041499850548a01c8020310766404500c00440255200c0d91465405540564144c400f596410a81c050503682410841c00040031030390204c00490803101c100080902e0307494010212200a07801c0d051720250120005400307090750b42d0000e103c11400c03003401c1213044450429241580c2042d1824000202c3d0071004070050140f01c000d0303d0341402505080c1901703540014032106a00010f6044d201d101c128441040220300044894002080507141184024946a480690300c03944210004c200011030f01c0c02140b4040d0901e00407000302e4140d00292020140180142d4010440f600028540c2d10b01840401c0d100c2d01d010b0300003440294041901000c04800303a102113110312503001044000e25150401503074485048034160b01180e008641b84c10301044c076000c818031034600a4000e081003d829502d240305a03110002850010842c80d003a49220b546601803280701324040d40d5043d4450b00300c0d0440788548510b00d003a8407110780c41042420f000a0120100031440c0c0e0454000507 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 714287383 1250 714286133 714286193
    0xf050f0316170f0c1615050306010806030f1c090b090f0d0c0509040b06010810150c06020d0f020309071202010c020103090204020d1409070602071d07020f0105010b070209060d 77
    0x7500c40c020b07032140100f5a5000710f00016401000100044140d5105420711201c564822420015204140080002078401c00005100794043d000d61a001b500240454074886208007c560408820b51180075101c0e604041e100c0580da40801b0000c00740185c03614083c03800c442000094440031801101501440403c0c0651090089078580400104405170aa02191038685840c0d100007030b0840d460340c0490002030211b03120211603405041a100081411044105000f00640340c000301c042040310229020021079072080107600a904a09010303480c0541ca0b42000b000c1141401021b4118240c80d000c512400c0700940c0e03000d211020041c2d020f00340050582070720300100b030181c0715144d61216540d0902c0d400003d01c1030205040c0d8445e9003000e0030388040c20340b1048101c0c0c03a056544129101c00300100c011007552003c0d144103503041030301c900483c1c0801108501850035a0300981c0683c0c949440843c000c001d42c241241c03640c5e440801203c020041c4042c80e610a42210355080e100000b88440c00c1e0350b2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 714288633 1250 714287383 714287423
    0x3040f0e0606040f0807061d0a2607140f0907051c0605091009060f06020a12030e12040608010b0406023714010c0203090d060b0a0e040f050f0316 64
    0x84000c4d000c40d0005020160300c40c150030780e807414130707204036000505a05038403107503800c070703124195511600140405405440c0c806845820100c1842118408914051140c51b8000c1044140001c00b0350b4036107401155451404c110082000411140c090203a0310b0403c0381c0594407001b20b600c41d05e03909502c164110400c1d01140002c0c20b42d50407003a00241c44206203c4403a07a6103000004886150005020940e142e180c4200d500701144a007d015901c03090700840014807000742030a02001900e000540c2280d0221400e190491035038840c903449400113800d1000c0c83d0b200100354007403c65400c51a10300340c0f5001d002555040303151058a03e0b45c024101007606800c074492080c0d0090501d2160000c0007096051801240c0b0501c40750107490740c6000702960f42240040f0070340300c82d00350003400804c2c40b40c1c2d0740d11100003038800081466032244464101091107010248800d0049029800032086102c41d403814a1610b04481401403255000b480b5040322145a881c88050a580c03011702030500e076070010b200e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 714289883 1250 714288633 714288637
    0x1030c1e0507060e010f0507091202040513020409030503010911090d020f01020a17090102070e0105011b051212090d030501030213020a050d0614011b020108010509090f250803040f0e0606 82
    0x518036810240444c2c02c00505400c58011040344e98410400e940722840e081ea4018054419800c0c50048021240050b1901e9840340c0e0344100300310380b000a4512103600080880c1c0031440124082134001c40140007000552244802018240a00034039010b100c03400a02c214440482c0280318440d481000030241c0d20a008202010707500c00c6039128401d60090086081b81c001299060061046400000e00000000303115030480310180c44128002e152607041032103000100806440500c9110300c8004c588601c2030007000ba122603050300e0b0400d4200b22074040c2c108480c2202d2201010304040060025949017810740465041c282e40040e603c04c0f041e0310649850003180c000b1502c051501078006aa58044140e062158200342d07649100400141c02681040c0d40d0020041d001440c0f410050000e800d0100340c003030704001103004560040480380809460114440e41d5080481d9140c9100b100090b40301c0c0d41030014208040195086c68102100c0c2d4003c098280704d2000c0c42e00c02400420119103038581 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 714291133 1250 714289883 714289897
    0x11203050705010515100215070c080f0d060303030b0303130e060d0203060f06090f130305090f13141003051f0b030f03130509131101120f0506030c01030c1e05 70
    0x100900503403801d185d0000040104402e00790080b2064106031401a1010030403001c460600d0319045166260000d08a51402244000700d0301d4440c20030480e00d034407092801406001d80c20f0b04e000329406055140080c02d554140c14103c0c002c0e4020311a40794022071a05070302050f140e60003202c40d01640d90400040410204580c040d4041c001e1a041c4071310101d002d40d141d4410b000680d8040041c2d00c0c0d01d46a81602501110405032405125050300c0c0040e02c10001014000d2008180b4403000030050000307070004240e4018403801315900c0b0340041c001d06002080396800b04001c0d060b8003513285552102070300c0b40015400442c581384500a07000c00c030341280c1d100c260040030180464100d80310118103075031359510141c0c44082c0398140c01e0300040c05103445c142c3e10f44140f20011760300c10f0721340240daa40e04044001c0c103403141c1440070005d903000d4a01c0c8107102e11031180c8826000480d86042c50b400341824400c501c10000d040504004a000b092500090300620b103440c0c00b006000180540b100c112001c2c0a156 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 714292383 1250 714291133 714291143
    0xb03040201230d0b090627060402040b040b070203010e010515060705030c0601080a0b1006050f0a020c130212060303040b030115030f0c090e0f010602252412050f0112030507 76
    0x1c2001c442c40d5000758881c4c1d0f44c0310025240c002c85916000208814a214052400014858038002d01c01d034803680c000a9400600161026080a4444c40040002c6d00281c100c410700e01000b040c46404d528090042e021103d020b54000c00903811308030041c5401054402a40340940c0001a0350420003004204460341c143e150019074400c0c0d6103401449807207112006054590540f690301003190b02040c41550350495082361101840d180102c5123600281d00510701d0039041d030151402c400e0443d2550400c0912841c602d0b100181d0f10074060001c2c0020340001b80049010380e1050009003c2803040104507815030300c05050040254400300c1080300641003c41a0100c0c2c02e00707181043d41429000321007141035410130401c0d100c0e25600c40d881083d004600344a4080141c0c40150b82c01e1542c114500360346450a42d035060b4003040c9840703490b12040a10403040b030241c8107018a240100542e031114146003003024980c0188040d040056910103400342c1030082c50070301903021030308074100341c040d20860f941d0366400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 714293633 1250 714292383 714292387
    0x1090b0f03030a02062a0306010c020f10050901032406032f0301141c08030601020a080c241306020d020d0f060801050c07030903060e030912070801150b0304020123 72
    0x103c00000d4840724251070000141c0c440003102ca504480410710703920590720400f03130281165161801190f00d8400700780c0a9030401c01c642c121400d65100c41e490640091100d455184d41c0d908100001001c80724507130075111715841c2c407000d00c0301203892500303807101102d280346004a20510040c0c80c9023200d24440191002c1e0103110204881503100c20700146040354002c003501d070301000714441800030308d0415071030711603801106280baa400654001d002e180c01900620403542c2e42d02c170983c2c511000da40100e192890a5100350400c2901fa907042159405101110204071070505010503150010440711800411540c1c0200d42100d010072071b0313415100d020500090074000c10522100b0b050040c0090b001d01030043d42410001801815080c0449401039410303a602400c4515540b1a4401031407420750310826804200800d40682d40ca600e03480c02010003110140010728603003c0f510703007100c0100007240c6007006501020406181c0c14170540350320540a00f03100301c030b180603007905011501070f85102c40381034040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 714294883 1250 714293633 714293647
    0x3020c0f0715051227030d0e0606041e1a06031503060106032c010b09040b010e01080607090b03071e0903020f121c031506080403081b0301090b0f0303 66
    0x41c07910482d070b00d00c51000d0302ca9072800012200c2d4810008002c0d006521003000c100c0070091a0028001d44000042d002440c0000b00001425a0300c08070885449603221840100b10740010b01c1419005401107404121404c8082290080000c458050029441d51a042c8250707a80c064140039880400c002c00a6a892519404401405102d4034203180244180f8001003502c80c001d115074080d24030303a18160040400c404090203a21300d0030001003500d9540311080f810b0f031074558040c054010741c455030941d0321a6041c942c11060b4210168809a1180e0012061003085500259200b00366861421030640d00d548051040d640d4007200d0b801c8000c8690504407258840c0e50003480102924800c0303651a8204c0320000800400d00140147c000041d04516000c10300012040000d04080702c0609001c2220b4070841c1c010f07910201903034088008140004100402c2590180c109035200c0400c0090300310005052105a6842c001401094811075a038500c0710701c07130366446481a1102c2002411295113001e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 714296133 1250 714294883 714294913
    0x10b03070306080105072d020618010f1805100b01050f090d050a08190203041d10090501030c0312020609060a0506060702030708010204061803050c0409030c12021506010c0f021003020c 81
    0x1074440000000411520021100c01c683c7c0f44017007207103040c158001c1c003158407401c610403160315449010703020039980c0c1c9a920044142c0f5000d00c00314400741d04220055008a4103299040c515510103000e1282e18084c20b0035a10303a004810b985c0306004414805850f418801d002c52685076040e40b01078042d124101c2c0c820200183e490003801c0c00c1c00303c0c8501505031310002000b42c2ea0781c0104d005020340028240701c0c02c007115154074680c40e800041c034241306900d107070b544810400f00c90081c0c0050304c05551094040c414407858a008203801111440141218a46511407035101d0101806212040c0c3c0c980011030140c0d034616043d80da0081d00141507907030882c0c1e2018614002c0d0302a03c14000818110052403000c2d503c030102103c2101c1e00200641260072210003003000912442c4c2c400c03024000f010b40c1300800302c0e003a04240b034841d459a8006181010710b02c0084d2051080080090b41080310850301c042c001801a03503080030f0b1030b60503a40d1032101c0954007002d0b400b03406281d8103a800342c400e103d42000016 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 714297383 1250 714296133 714296147
    0x91a04110415030803040f0c150e040b10052a12041502031201060302030604020706090f03021b06370206070e241c0e0304030b0c0909010b0307030608010507 69
    0x40046500700220340c00b1820601101286100291100c0c00038000a00481c1a82c4400c8400912035002d400b055510f81802c1d1200f40310462000c40040c11400c4080c40a05043c8030700111014100c80003c05840805e100401500c035600070210760015280d44440c09910400003085061000010b030f0f0464551000e03004866001441003036085042c080802c6481400402199a0382040900254040c3e0803d0800d9000c0d60000e049190815030800c0450085002486070404052103110841020301480c20000d16054200d2580c3e002e20140340d040c1c1c18646c3c0c86804481c00244910940c0441c5c881007103030341c00782501c001514440d88446000d00640703c0d80c0490514820750580e20780114589019050100d40c07009548900280c0d0720590385080c0f00c410400c060403120000070002000720300a81c420718180c44203585041010b61001c5030034020007048031015940810341103030240c101180c00c400a1b4070f100044c40b650148640000104501034883e030495805002e00d54024002410f007040d0080040e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 714298633 1250 714297383 714297413
    0x705091302042c1006060509090429150901150c03020102040504020301030c030b0c0c03040911130e01060e0612010e07140310030b250f030e1e120309060406091a04 72
    0x150081911444018004c1c1c402c4106a4116076125402d180c03900092100d00d60000d003065580c01d002495140018a0082c290020411884a400558200f0042d01c0101d2100007040621401c0b2420052220086128110300c000406150a6250b100c4508050b030080c41303140c21003608240000008800d101040040c81c040b07a2050394040b03441d5607500d40000d428002c4180651a41e00100401c100c41c41c0c20f038000701c500501d00c081441c90141c1031941c054680c6e45951018050054080040003810f03000440f03c54000011b40c0c0c1a868001c03280102000d0600c14041d050344a81b203c000700300b003580715010000045407180f446907030f681000000c0c4d0380d41c0394140c801155503006580000b02600b12911520907500c4040d003c266000148001c02d542e90061113800320200b56031044810400001003180039003010a4011a106000310701c0764442c2400300012032506038807010824410980f2000584580c00f58103d43d00181c130900c03514003100c09807024421102c1c444c002e40184414001140380001030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 714299883 1250 714298633 714298721
    0x605040501031a06011809050c04120303050a0c0507210908070602010e10020403050606131e150501050406091502011508030a180b0702330d0509070509130204 70
    0x4594900d001114000480425800c0c81c46c1c80303500c100700340803c130f802168001c0d0000c0c0d92a42040d4454a000c074200403910400e030006601d980501507004a64411226050310074a0b1040c6044050741300c640600e080c02004606041e50f50020319101c0340b207445060084c11507401569a0580e580f000240a809030054082d41801090001401911644201c404403030307100015111582e10b500c1040300014110103407011070703901d80d60100305085000e42001880d44981384001042100d020341e862401d11607400507414010104401d1060a0b04400c800044461055540c0036400329038000300d014208010500f0100c500001d0082107240000c8050010300e249070b030b6500341e45900c42808040c03000491060b060040700c02c014242c05400c10044880c0d2000785501040d0f00304104407400103052110813189880000b020450b006c4111403405840d4000c013821008001c030909085c00200340d6580601080d01c0c0b2000c0107200c80071504e590b0040d69005241125500128540c0031410190b100c0c50008503031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 714301133 1250 714299883 714299933
    0xe01061119030c0b071818141e04050a0c0608090f150c09010c14070315091707150606020601090c111513060203070507030807030506030a02090703060504050103 71
    0x203000c5024038401c500940681d110a007048081d100c00303224010141950b81081101c2c40706580003149400b00000614a548021460464604100003240d020228002c2c0c0494090f090010012040745030030302d0540c2e01020b204181c2c9503450445c0ca043c55007800240303280045000018000e0304810468410700b12601038952071040020015103032140c00c024002413150781400301e900703440341c500509007103001810404640f80a41d115103c4514102720121500c0d84208014000c01c06d0100360002c400c42155004e03c1042c00d66510103845141044c1f05164054000c1910020311501e0480b4420320400a00b08102c1070741c0ba9100292186c800b4090510002c2c10b00d145c0600b014461412003c0011001019210310700c040309400d400020f015060181c010080305140b408620302d031000718056049911660346d10300c080c0c50080c1c80c4020040c8003000f814501003c000c4141c4000c144070701100d9040b280030200b40c2ea1410154010702240d08010740081c07401001004000c903a4072001144203104000032 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 714302383 1250 714301133 714301153
    0x402040b030610060f02010b03070e2a0a08060f13050624030f06030f03031e010b0307120b03010213060c0204060b03090304150c0206161b1a0904060e010611 69
    0x507510401070f242c911040f48080c1c0100302980c480c044580c40300c0071510021980e5551340d00000c1c0750080e1078108042c0c5031089800d201032294071901807448442c01c0103441902e5480030481c11524022008a0014041000b000440315561a40300c3d06480c40c001b00461402d5001d4442d92009043c00c80b10a0700810315030500c44061203004038058486004c41c15628036503036914420101a642c040d001507058807a26420040b00c4109002661044010780d40e00f00e10031140e4038018403c070a042c1c2c4844043c00c0204103200d1b403640e1080c1002c2c2c240754140404138007411000301290083c460141b404590340d0510038085482030740040124000c43c001c807028003002d5102c0414940600c8107454005147e4410081045403510304000c660104010b800c00380f0040380c284d00402c0e0f1503807110040c1e401c900111141e01e410404c0c0344044d0f020151480c04008140d6090842d060b6030b01a4040c01d00c1160480450101900e40da1900700c50302608401001050b29603403020040c14a044201c2c0b0740140b0302401c41d001c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 714303633 1250 714302383 714302389
    0x5130306060305061614070f0c030609051b0607200a0302040518010e0c030a0b130510050a0f060308040918081810170118020d060609050a0501091427040b0402040b 72
    0x4030700c10145c0c4004040c031f040e0990b0364001c0000340b060390032213603444500c0001000c500c49100d030104040c01400a0015411040c1d04503640201d14588180b06002c20300020010501c0140070701c0c40720514801c08980100076400243c00b41c0b42541c00258010b062904001e000c80c000100c6100c20706061009100b03101f0500440d0781c5440d0800311150700340e0301100516020903144100307540c000d8104103880038031001a4035010708216149408000c07013a100d0b424880858030701d104800208081c0f46d0104401e90840c1d40c2d044251246110f580310040c2c035498003000d90160359260110031a481144580c0d00d5440300c0700303490075600741000227101c1c0042082201c0030b24010020b200c41c074807007400e00c81d856070b00b808001c50404884980303103910682d007444001c2a201d4203110740000f4256a1f00c1d000c804914050070001000b80c070307821440c100050b5400c100a21440f48980d000d10310700880e07001c0988040356446003d00c18580383d40712800d0002c2d405000510040c5040c441c0201d0007071360700f4031060403000e00b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 714304883 1250 714303633 714303647
    0x5031215041a2e0c0311150114060a20120706091a010308271e0306090f060103080703050c0d0806090a0603020d0b1f08011506020d0f051303060603050616 68
    0x55051030100e00d00c200e0f43e4035803003081c0c50300415109051001c0340e007864200462800c04450107074030000c00007900522801100d1450b00108c20812103a45180051003075000f0005001d00100c1000043e1007141200799510900c8080d41103070480d159943c8460003428000d01030284000c003550784500120441000010241c91541601c1e08056458544940c900c2c0d80c0070b40840f4885145104d0f8280481c01e107031603071046c5140c1c9074041e0800114094081d4001007608242e00501000c001d58000714462fa2550b02c0403421b05d04507a007100c0d4464440406040c1a2a6881080b031341d541e443c00340f00401c80c10540c00100f100c0c00341d030099805990b01c1e6210046041101d0140c00007035804110002140c2c0015031031103545a00080740313000c8038034044010f10340c0031201c21030303403c803d00994598020741040702000d43d05034002d01e86480201101210310f0400b8003448110303c80681002070014402a4903030100065000540e8024010800a6900e050058175154155140386003a0010b103a00c5c034107a485040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 714306133 1250 714304883 714304939
    0x40605010f0c20040504050109030e040204140609196210023601200a11030c09061309031103181002060405031215041a 53
    0x4034040c88001644800002e02c10700340c410092800140d8030b050f542e45590207200c1c0114464400400c0e81c1d0f80502d4042c0c1002d421125040c000c40c4103100c100204035048862100760b0a058910b10354070141c6c03c02040d601c401391400703203468640c0e2510010786c44081c4140000d80c041c1d4001c0750407484412000031104e2080500c03401d51902c1d04051440c2c0310945410080c81503000f489a0070305017065400c581c2c1c0c20020420481e80450703a01048500c422403100e054a190039040c52001d102d15980300c0001642960b00340d400030b040081c0301640c03558102c00980c01100e41640c04085a801c1006481d186142140700b28000c0d019014520980702d841c10418185809000c0080c4005110300c00d000100d40144600d01e803d030204102e407582c0065481091000340502e028407151329241c2d0b100030060200881d502807038501158004010080411000b00a813180604940c00d00d400396141d166260307040c01140c03149198404e2803e074a183d0080302c1c0c68046400a8800e031a00078541c180020003940004600c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 714307383 1250 714306133 714306137
    0x206130e09030a050d05270313140a0e090f0f060105131803231b070e160f030e0303131104270c0308120105150307020c10020309031b040605010f 64
    0x1110003000041141c2100f035104041c500c680e07d81500c0124640086605009900242e400001c4c1041e00d1020400d0b980000d040081f0005400000c94400b0601141c10383c410088450540804034406030401d218400b10b4486036000c4071103104001682c1a00c44100703214640c4500944035400045600d50301416007141d03011310b020b4000004548003500c09698a02d02c40c4c1c60036000ea0703113074500e502000c405400307490840640e00c58051601c0e40210701e0b202442c0c1180460700c000d1001c02c4900c00882010105140d26480d0040000c9146c100c2903019000075000a4007500000c010440440481c55803130f2071060081c840191080966401c2c0411103100600d80700c402c0c0c0805425640304a103050701044081d21400080d003400c0d589444041e4160810351041e0b2700f04121600400c158500501d4020082034000201461410004406580c607a0000612800f0303200b010400c40c4828000d00c140d46072010007406451245e00350900740001f4400c81d0300c00c0341c4524a45003000c502d0f9485502c0f042d00015182d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 714308633 1250 714307383 714307387
    0x1401030e1e1606050309070803040302030a15020909070509010801380d1803090b03010509040b06030a1709120a0503041a19120c1707030f02070206130e09030a05 71
    0x32441c1e0340d50044202041000602c40c90502c0445035038010390510040c0400d9841c16241d0400c2464981426955070180e8800d80c41408140090395022408009042d4842080d06072811008000c1029024040e07210350301c0810702c4200701030150448014440104240e8615605a0302c80811001859801d21461100e0070400440325491400711074200941800ba0403003030a0008203442d02d001c1c1c652020041350450100959542055041800840903001c814032560541d8140000300744200001480500032041b08404560b490314180102e01c1c40c180c01c090700d610000c843c031354080d1081d4000c000090145892103030443c440d00000c64081350795079004010710b25080c58107c40d012552240c0c105030f118600708002c0b5510701000d19507000000482603c8400407800100f80204c100c884400801c405c0c44450a01d01d400f00d5051180c1c0769000741c4a00300002c8143c0d0200001c4020700039801c1c004d40003040040ca1000d0058002901e81c02c9a80ca180b05032265640d11609079241c0c040e44500790081201 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 714309883 1250 714308633 714308653
    0xb0415091d06130506160804030309290114090f04030c0512130e131a0703020d090803092526240604020408120a0c080406091401030e 59
    0x2598100100003103040c0d200701401212032821a080010507200300000544000c0328004001003401901c0d800082c07106942d400340c0e10f2035406080000010002001c06036218600020400044181c1009402c041020280c8040c2605c0f01c5001a0080c003914082030381d0249884824a0141c8070217110b208081482d41c416226541d05880009047d41d044510380100c87c17200c2035034402540076020041000d4041707106a071602120541c950401340050341c440d12041045000b0400c000c007101d1840c102100c9411544d43c803420118000c1c090b10760442c594500700300140085c0079000d00a903029200d400c00b0782c0e140d0f076030780c21001141c2c06201c5008090607894850070402001300e624602d14603200c0000c202d210300340e075a55550070102003d1040c01d102030800c640b4040c207100c4d040b0440e403020090300c085107464200261195500007007200c00c44006000a880c0b2005032045000e0703e50304d83e024500b02e4645031140d00c040c0c207022040c0105188404403130015400da43c41b901801200341e41a00c081c03c4050b035 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 714311133 1250 714309883 714309899
    0x201020a022e0503040c211401150605040e01060c1716080a02010f06050108071205060a0b0c033f090f0d020a1b0605121302030d0f030b0415 62
    0x4401442c9407a41c000c084442000c525560340200c607401662000e5407880c19242641c040f9204d40c004203800f00c07180080c003105480d0003076014805900701d1b50100d010031042d200f1501402c41203030702050151486400003031315600000900240d81000d0000503070b581e01c84e00308030b86540c0c4000000d400054004840452030f001d8800400070440925036010b40d04d84161504107044e880300d03807080010307036441504070320b03400991003031300301404c4240b0b814442820020302c0104034a00fa0f44031030203842d0303807070010071019a98200c01c44000e0606282040c0c580740d0003036015440b034000407661901c4010184c1203036540828240b514042507050480729110241e482c1c45542d89900042c110340d040d100f1400c1e046900d20342048010042d000542c0102403070102441e08451040400da11448202d80300c0f14103100b40344e004030a80d000f00126000d00d07988c944c0d917031a64010403c0603c0000c1e403d4021100680f103460b60200c0c00041040c10303620240244408081800102d9403003640c80d1a11200018062290b01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 714312383 1250 714311133 714311149
    0xa140a170c1215161e08040203011406031b0f0307030c03031202030705040e0601050904060b1b0a110f01051c15140d110406051504050907170606031003150b01030e0a0201020a02 78
    0x109900c0c0004a00846201a1210f82c0c550307540100840c601104100840c41d09000b4030344207411001c13407104bc0b410b10001080e80d4000407075000314181007100d408103a070340303034414400320844000742110380031a0f5a06010005684d980015000158005070071540c4c1041e40c002c1f64020446a950185002e16001440080702006840181003050030400440f0941e214054040502400c0480595410261402c80707100b03c08402c0082d0320342c0250788040301041441c1540b074501201038401859081084004843c9441180848189203441c22202c140410f03859101b5008440c009c00b441800b1030300e0742554144002c00484050b0701c03241310b002e201e00241d807100307400b00040000b51020500c2ca44900c005040724404200700b034804003000c01c04000c640380c840032458010300981060301c0c0e00a413030b89002001d244001d000b00e0289600002041e82803140400c038138015a001507803a0120420302040001808107480001c0c002804c02d1440e904004002c60f107600c0081d0b05800800d640b16039a42809266 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 714313633 1250 714312383 714312421
    0x50f10030206071727190b030703060506030412021b030607030b010513080a0614040803040602070f021f020f07150309050c0301050709180b0a140a170c1215 69
    0x544003240e0002241000344c09003c1442d00b220700200e1a40d903010700c00300e000341407082c0d40303200c0d4602d102c60740b40c0a00c0c00d815620a581c40d403486113540b5034540c04240c0c0070300f40c55030246802250010070001442619102c200500b0280d60940d5404645402180c04009000401e9503160700480c0100e000e01d07000784d0004007250b8041c10001e080440541c40d900c1c0078100f070b5012008a0300702e002c2c40310070040320b071050341c0340d00f111002c40001a040c1512440c620b800300a1004009030703400140c540601a03203031603000a155000300000d024044001c016500320410744820000351082905401c9161004110002503640100d880d28403000b10080031005020558416146030040e40c840507041e803000e0050b144141300d5500c6918046151003011100180b141c40d10500052900c1e541d501d5075a075451040d8211000351419000c41d40700d180000710816065030004c8440030038214250040d000c08510708250900480300c4911081d4490310352034a41100800000c1038520074000200f444155500e84811 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 714314883 1250 714313633 714313643
    0x3040507030209070c1104060807061202090a090f0b010309350f0c1603120c081207120b06211b0d0516020d020619150e0703050f1003020607 62
    0x5241c0d039401142d01030000782e5107100018044d03504082884070306019030080810556081140a1801d80c4042d01c80c00030b80500401c00c844112000740419098054503c81080104582d840b265202c1640008002c01c00c042405d607810f1402219003580648146215150016032a0030720707c0415011136500307924030751741d00c20350200c400f075940014586101800b5440c40d6641e04075550244c2204251404809000201c0003d1528009000090111503500200340d03990800c00550b0b080c603c1d084215000d11050f01da28000c20b034003001521a8049801851001503100030090304442d001400000d1140448140359003100e600140d02150101d40101e030311512074103910502d200b4a000000950384060082d43c0b0381511001400014a00b00d81000d60460282c0000c101a22013403c0194441500402d0700c0500c01c0b4101414507901100d070811070880c4500d000c0b082500f522500d007a00b004c00140d8486002a1600d070015104040745c0c070810740500c1c1004d10310890341e49154208040d5034031503c0100c070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 714316133 1250 714314883 714314893
    0x80411040c120504050703020a15050406030b0a210209061512060607050a030815101b05010204080106030305183c090412020f01021602010e28170a17030405 69
    0x164002e2074440c3c0c60249104201408050f803441c010403100d02070382e400c00c48040c0000c580010406401400710303000c9071510305000c02d120ba000703400901c10301d6642e84585942c0704501d0300c440160f005102041c40c010301c02c80b40303540300d41c9440b014003000300c2d00000b414040507400c205003690302c0324900c001640170400030440d0340362075080e0707aa10f401c003180b80e841200815600c0c03050240d0b4034981205401c1406040e85c010b402d40c2c00740c0500420302e00c11345990a0401006800d0101844029011140a01074900081c80b00607568680201142c1c08040450080400190b40d440c6516001d0000111500c403c5c0a001842000800e06480c40001180740746102d11580c606014a458016100e44034a00a005000381440380c0c2c2000707401d2800412605006034030403c4095072060940181c2c088031038080c0b0703084145240407404904103040030f1201c500c100b5146070f1441c3c030b050011804542034400b40c6851034071400b40c48072020354415101d4401481d0b000c88400b5400e140c10741d00061a0301030b00920442e6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 714317383 1250 714316133 714316157
    0x4030803090a020d080c060f06010806040b01141909090903020705210a080405040b0d0302120706140f2a07140c0907080907050909030901141e04060e01080411040c 72
    0x2c4c1300c07044a94801c65a40ca004110b031100c00c503050281540c8002c038510004a2458080f000802c6031400800c058441c41d13031010124000c0c1d02c07501404618484aa01042c2ea0360203403640c1311b031000c600040c048005041e010011a01404600a000e41c15074140c000340b945a0800040200f00c003516070002800015641d68880080340806c0300140c1d81d070052000541c0c490074401400192400c1410303182c05009000d841f1000a0f0340014071b20040074000168585130051850704002410300100c00e14403400d1454240a002e11260481f00e000300d94034003544036201c4401501d46100182c50501500c015804e00a81c000b1541045080d40200000025588540c901100040c0402d8090b50a28002003081040104424082088802500007100d0b080310740e251540445035030b4800c05c242241040500c4c41004080c54028045d190380d0010040219060340d43c01c2e90300741054105205000004001c3c030340100265000b03d108a001c1c54010140c444280a100c0c18000901130944408041007141d0303000c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 714318633 1250 714317383 714317389
    0x60c0216090605040609050f0f0618010305060106020c010f2304030206070c231e03031303030f0f080609150f040c080108120901120504031b061b050f04030803090a02 73
    0x4007410855100084250401c018002100e1054114988080ca41010b0100381220542c41e95842070800003102541d65842c404150349140000d00c141c054542c00c4008010060040385a9069400036802c441c8103c00510044404041260301400840c88001c4804d1000c8071103000e0740744042d610080e0070b151541d00d5000c03c416502c00d0b03030241c0d00105000c1051200310b00c08074144101c000030450051030485650001400340081110703244410445400030215601c1c18016980501010008080055a0380c20003404000325039840c9800134140445030701d030300c81c02010905d00900002c0c1001d8015994021070b25869006001c03001d6020104008484095480f4094000501c0069851410551510100c94946904441e118013010014880e00f0083c6e640021401a090514240070030345460b06d08060b180c001520300d5600001c0c40c0b5406040c240007050300407101c0c01d09800d202c500103c0c4174000403034240c0510b0b8401e04481004000410104103004003943c1c00c0b1b10b41c0030984500c80503075400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 714319883 1250 714318633 714318673
    0x1808041a16050303070201050a0209060d02070c08070b18030102031308090301090c1e05030f03030c16050a0f021009030201050a0c0809040c020d091409180a12020102030a180c03060c02 81
    0x2c0360198400000c00085541c28061a900580e802005504101d00100010700c46d02522202d040c0f02035000c604041440101582003000b00000c2081d030f015a500e5550030600d582c0b2942100030b0310414000046c00c075080520032a0720603607901070700100f152540d648036400c83d4042d0b04001d40c15900c0e41d4041c03010400c2400214020110a0040c0e5041c1102054040b1101d03000e41c01a1311076002084110704074140802181e034071400200d41140e0300d0404c0000c60b0050240018060203500c9804400402c0007100b215518005000b00c1d24500c0d89074038403100b00e0b55030383c1901009000500a008002401c1e0003960244040ca102d00d4845091034100000708044803c0c1c03652840060f484a07400100140d085420300010304604014a1145183c16010a00e1000080c2c01d401040c030302c0c101c00380c0348a201400840002540410205000300046800a002c3d400a5901642d45440c0142d1081900c0c1d4500c0003000040e800403124240c5407864403840300401c02c02c04650b00b503014000019100d1134035095 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 714321133 1250 714319883 714319927
    0x3040b060409381005061c02070b071403041a0705070501090c09060b04060f0516080319060b0a020616110f0d0e040b01020a2a0b07061808041a 63
    0x21222181c02d20030894501801164414070901d000c02e84280245003449100c804143d1704140e40c0ca0390b41c0c42a420103006503008103550610001c4c4081400d170100148580418010b60495071230211500300103544040c00c0c48103481c0200402600aa8401220081c030001944040c50b42000750805050b81c03200d5007510034100301116214011031041c8504125446420301a004020220341494101500138040f01030384030540c400c0c890007140008422884070205c1c081d07180e03c0f9840e1500c0e41003a40506514003244104215070905010340899510b0001e400d076030745901544d004140d0303915030801d82c011040c500052201041001030150440010800c144511001c82400510001c0680e8000030503002810170a54401c509207100000c1581c7c0c000b4006036500d40003102015194120703000314102c9001507103081c52078001d115000030000071010140141d10b009200038810041d009200c81444c070121440206000d00c2030000b4855020028010b06108002c603541501c0d01c5101c0c616518a81d4180c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 714322383 1250 714321133 714321173
    0x12020a0909050c0a0c0f0f0c0803091002030c030403020906030f01061d070804122f250f0b030702030f310b0421021206160e030303040b060409 63
    0x105041281e403806214040c0e1200d9425151420044d0b2607074000d1030710b03222000280036032281d840ca15083c800c44403021025a41d2100a550079180c1e22140e040d00c1340c220090f00d902c911000c03c00c00011034004012100c030400d60070003a41c40c0c41e05583c00c01101c0c40700544016090301c12006021900c0700c00744119000341c800500340044100840041040c0180020044800c024090091000289800010424049860400d01148802805481905c03d2158101200a84407540e075400201c40803034030b041c910a40009041005128a400e00c0d4200440e1180320781c1c460700c10f031b02000200c601c100030b0f5410865600c1a0307880d00110414011340b40d00309a200140b020340b40801407503100c20100e0070741420502910180e0a00d482c001148240f0f000e90702c00c103a80503080114034440b15072205404100a64000c00101c0c030318842082c2d1a507240d4088440140e01411000d007005207a00401118816250090003036207556181c5d565140d1840015101d10b400980b02e00300440090711425028518003424 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 714323633 1250 714322383 714322397
    0x409030203040905070c1704050603010e04050309031506011715010c1707080d0b040509150a0e07090507110a0807030309031b0f020906060c0c0d02031510240f080712020a 75
    0x1a080041c04000500c551687c1d9441c10007042055803503400540f1304403104070040e41d011341e0b160b00b0b0160440c414580f5140e0315001d940b03041a21400c2d4500c0a0340200000c2e61281c400c0b101485828105000c29610002980c2011104140c10f40c40f502c1c107000390510950300a10a00314001071520f10750841c2c10100d91410b804250840c3d91050ba00c034105014100f22028170003401c1c02c008080d01c54554002c4589034030403480019000d08600d80002144520341d1048594459a6a80403c014481a600c0300c0000d06450410b40c0702010014854002da60010f010901d00009076809038010152a0030840c2481741028003204003a44a0180104190150b04020150300c01c920401441c554000c0049108560500c41007610307000c0011548400b9005680140140446000091400e0400300070400e042e25100e0810501d02d4000402d642158200181004603050a1900039290008034680c900015514400201c41314821402d06410541c2404e2450b010340d046800402039910403039001001c00c8035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 714324883 1250 714323633 714323657
    0x14010521120c010c0c031b0c15050d0c3f0c0c06050a1e020d02041518050d080d0f110a050405090a0207080f03070e0d060b010e01020714040903020304090507 69
    0x1c00c2c001c05a050a0905d041303a5103000ca590043d024800390030441c820180c01d003804108210303d501c2584050700c81e0500d0380c250740d15002d000510550101042c4101c6a050840c3d6011840c011049c4914840044000740f030f0556899407642040034488403040320310750310302682100710081352003031a01425580d542ca6104d01180d0070402c1c203a65002d040b44086515041c5401400d20b03c0d0480310028055484001d65039500e01d482d0038010340a01d800444a003c07031001b04080c52600424021440481c004440c0c4007113039604208041d04a619001400c2e80004020b440e810395880d6011403d602500704000a02e049280d00b40d03d27082c3c0000780500e010440c0080d0a01030b51410128880c0c0c42000d2100c150700d06100d80d03a81345d00720301900d01c000c00700b51008030200d0b10130f900403a41d060240001030b0215242891038100708014203054542603001c07030390541c1407400d42c0d48041407040c02d0302c0f5002c0518a44011180030700c00140030200c419011400f047c4004200d01d0140c4c000c041c040d4846556010071041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 714326133 1250 714324883 714324907
    0x905090c0d0c051b07180b01050c1009021f1d240a030b190b0a02100905010504060c0e280308120a060506070507090f0e01020a20011401052112 63
    0x208a128921a640607580410120316480d20181b203c81d04039601080d80c41803000107807040e000f0400001c5240c044e5035110600c034030580d8450f40e0018003c031340b10fa404c807100d40718044c010700c0b02d6070070b03580002d600c2400744060a05000c80324024460161a0741001e042c02c0c1c80e4645c602d072104000380b0403003000158031801d5036410b00405110b96011100013270b0512107c610424180d8091213185105000440d03207a03100b900070710004403005c29403402441031103028500240205411078045a0240c540103e80900310320402d2554204034024103450800c4005181000c0720240d06050740540203400203010000840800103012822480700d51100706e81030881640d03040c2c031510b4101038010708042c0220000700394005040021a5079440d800164100b020051001800381e070b00c0f42900b5907000060021402d0b52250311030014402d07200342502d4035640565541d0a0b152540d0004908032903080041c0840e04d4103000c400340303401c0304854016030881010031013400c0c01d04003000c11a0840c80800c00e103c0c0e100d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 714327383 1250 714326133 714326167
    0x3060607080705060402010f0201060509011a09030607230327030d09050c0f010503090a060e031306020c01090504020405030d141b060403111f150306050109060f080d0905090c0d0c05 80
    0x3002e240001c1c421203007004045502e0371014400d0702201c4906450380c1484006c2e0301d048a07490074000d004d6864a140801c0003510050b9a200141d800e410304c1d0004a00c12906101030b41d0007184c00305170b03221074580c00c0f0f0040c01098220700c02e1403a02d40010442d0360b22241843c80707000388140c4190b0241c205a00700b042040864008840a14180a400c104214100340041042c485450744040300096085505c0d418520f54054000346c0c03c400080340304045003154000440204018007640c650300020384031800d210581c051032080c540c2640c4081a2070820701d002d41c035410048400c006005040c150303c4001a01a241401c040b0b00cbc44e82c005106210502d9800030303608903203503020b50042c042551200301984582c11811800b0340401e5540300340484500c00c4080740350040d40c100c2d00a00507540c4030a40c0000604207441398a03407030700b115040001e52010208100008450740c1d15107022081c034010510100081c01820010300710810080003840441c40e00c64100180d40030340c0e0f1300703445007030f070200015881c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 714328633 1250 714327383 714327407
    0x3130e010f120308090705180415060605090607060b060403080a09080c01022a0d05010209100e0a210606090501030212010207240603061a040b0619050306060708070506040201 77
    0x34401220501140514021010b040b0754145800344240d034480304100c0c1445582c1e00542e45c025907a0918541030301e801d204c000d000d203024100208182c0c0200e00031504451040c07003004045403040c00080c03030340d24000c00a401102c3c081e00c00440d514800100062059115400c122200d01c00400c032840e45507445200540600762400040ca130050320328001030b640d00812a80c074102d809007000304559184500c0e1043c3e8007808007500405031242035182042c081d410032545140602d100b070000c07821442c41606003c2040c035019010004035800c0008001442d858181804100d40d410b2400c8030001c1c3c07141c8644c1d4001e0910340c0d4000b4036941148100701044c1540c003c0c00086a0045c00f040020031b11144526107407142c001d00082135107002c1514035010340595400649103070b140007540900702e08041078a01400f0803c0b18200034000c803103810803c580c090f41c008100381440074055180220f000320002c5030498070007005241003008070317a030703a48040e449030710304683d95008902400110b50300001a0916 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 714329883 1250 714328633 714328649
    0xc030408010516140a1205060f090f0412052803020708040810061409060108092a0310050903030c0c070f23060a02100f1b02151608060103150803130e01 67
    0x60650304500040ca01c3c669201d449002a03a00c9010690036640d5010727413501030030080c15040f43d91801400c0c4d04041c4c1c404680c141c07148481c120354140b81c0d6100d001281d0000d0051449614401c16061800303803044246180d1009240d42044040041392a440180004140d541c00900000e081800c0210641e0035551260448949592541901e0340d2248400e40e4491002c0c03901c2000c940d50842e0700703803512100d1007c0c0032032500c21420802014096000310082940c05400302e540a5290306c100d0001c5520440d0390410b241c00500200316411544001001106503c10480d090141c81d80c928003101803040e40f2a02c900c60b81009a8286404d2018683e108004110746032414a215464060b49510156519007403035030b0340710028584034800c0d600031085404001000c9a43d401812000307940c43c1c12100d2a0740c3d16a1241e00000c054002203030301c003500703110b1658883c0c40c0c94585800540c003034482240ca050354049806800315a001d000c0001d05220210002100210f51600c0c5601808550603000070306 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 714331133 1250 714329883 714329887
    0x40f0f0608071b11060d091709030607260117010e0c091f0b1605100605031902040f0509030d0f0e06043804150b0d0303020c03040801051614 62
    0x402a40100110300c035408801510b040001ca030303180244c0384030001d0b11595404600402c115500303c034681e201c0c00e9030702d101d4262201150109044440d40380542040c5940c140c1c840b40028114910a1000722201001e1014820450641c41d6121000799402d070028400700d00b4440c2500c0e01100c09000d81c0c0b8442c04400040e150104100010941948000300352200c003800300a104002020a0003e140003044041c0140d5190140900d9600d0b80755407900703080e9228807135090700b0901c1503290301c11002100e00050007405449100f12841c4020044208207a0344540e494003161064400c0e0300900703106850260255680b54041341028048400044000e01041d00e0442e0007014107070700044050b082908020560405042507501184034444002a100030b070501c00134008401c035210901a0049200d841c64041220503e01301e03801302d80007c03e0322540300c1e420086c0c01001ca4000c1d8000d09003c03d0040c01c0d00d141c10746031950309095401c1980c060382c6128803508070b13045155000c0c040d40d2040b0801d990242c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 714332383 1250 714331133 714331141
    0x12080a0e1903060b01121a010917031219090b0405060c0a1b02041d0624060a0f0e0406060c060e070f09020f04051e101e030509010908040f0f0608 64
    0x1c0150501804001d04440e03640318540740d10380c080c0c81c007a1408030221009005904038083c2400c860305188100d10702146805034003040302010925000c0b0008003100046062a000d880407280307141c0c002e888451410002566801e6060990181c203120074000d110030700f0541081c3c030305607103072540003400460541024894203100030f80c8005004e40c19946109a100c418059000050003080c2e1540c008006808030030005100c81c40215206e0b1003240011001e82400700460400981c45000702c40c0f19502500401c282e40c1c0e02030081228600310300e92071074100120013001020070704584041d08980042600420f089040141500034591180740c12005012400d02c2c05030001201909402040c5441c0e4010418502c4865104281d038010500141001c40e060906d1120242081d508031900e4000e907501c1d40601107560090404034010007000c0305640c4a00c40720300040300201400b0746601a20b5407260401c0c0701151001001c0d002904030300704103402e00782c03619040340c924070402d5000c001030016441c100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 714333633 1250 714332383 714332419
    0x200c150c03150114090603180d020304050607020d030e1c020f0a080a08030a09120503090c0d0237060807090e10150e030d030e1009150209030712080a0e 67
    0x10b0004044282021100d401140d40070810038003840c00ea036600200c0c007104010b00d000c841d104072254980400d058a1a8a0b51104100c4e1244194000d40350054020000500103080400c8005030311070280c6052405510150000b03600039030080205640c8482503da81402d624040f035100036075440440380c0700907492521b40340c552030320041103025004c005c0110000d00820300e26000034080070340c04809529211389914000c0c0040c3c0003501c90076400c2c8980503040711541814503801c080d194004000b0740015802c01000c58500b031860425105811080740e00851040a640040f0003404650310381c00707002c0c40c09030001000300c1340d0744d400b645003010804140003485400d0031282c0151034407498100d010803078501040d10303544814418107400d4420a1034500079980e1660000202d0170301801624411040050700400b41c0361034500c00f62a9034118807040003240d055600409940c81c0c00303419110311030740d69211340e20010504d1710142c0701e0900c0012a16502d1740e210304405203680084036050940e410002c80 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 714334883 1250 714333633 714333661
    0x10911030613050705070507081c1106150301090206040801020d14040b0412031b1e03060e150406031203060503060c16110432060f13200c150c03 64
    0x1060072043d42c0d8004504958803e8040b100495002011559120340d05e444080c4e6500700b60750a26104001c0441c0ba5190920413002903908141520081c201611010701901100700c45142e80c0d9850f42d6240364940040e1a220007610061612000058481b045040c190041d18811280ca4221003042003c001c001101640100d40203500301611401031508403c06a0081c0500b09414001400000c0d512080c036a0041c485849003084084500d403d800c6144158151003940c001c800b411800c400000310500d00303105070b190078280020030100300c1d10b5503510b40c010070601c004001c10029807110814407141c00c082000329042190300680030304d81030f0000c8801c222540010401000755605008404090b0384682150170f20042541c041d0b8101965001d101d1448201491707950181c40300c403000130b042403030100c04500385000302405448c00d13000300803030000040810740200703520426410000c51641c902000135180300c400040003464140d08200040d00d070f080c8010049280090100708002c1041b051101e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 714336133 1250 714334883 714334909
    0x31f0f0f08280f0f02090f0601022a1201020d1503120c030905010302030603070302121f050408040312110a061e0621060b1c0b0c03010501050414010e040c02060109110306 75
    0x1400350804800e00d40480500f01d81134000e0f41c04405882484102ea04003500280617034826003c4030140710fa041c0089441900400252014040030390105071181000c0d1104109060b03240700043ca41221003901d101280c1444040e40343d1038154400510800070348410900325101c01d07007420036903144035540003069512a40101410540c0200114002d81c81c108801005546d00402007006a200364180d2a0385000021803050101c0350340c011510301d40000d100d081e002e41d0b0400221072415085459500300c4401c040140ba08102c503a00352080b02000a1100d0b103285c5114100c003059000d6001d816040034041d4049607080c140c9403c40400089400459010780112a8420038904d1000c60401400400f081f00c081500400300e400b05981544160042040082c401c2400c82190740300c8162504580c0000d000da24003042c0c0030001440904082080c074055200145010700340000d4400110341a20740e080c05000c0035074031000052188010f14010052000b002052940c29894600001b81c21102980c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 714337383 1250 714336133 714336143
    0xe04090b10050a2405070f12122a08040203030d0504210e130c14120603120703020d0e0f1012050a0209011d0a0b07080307020709050705031f0f0f0828 66
    0x421038100300c490f01500a101c0c0c0c124000329032404000074041c101d481d030550049e450915050320440407210803466140d41300110686403040c00d10706001030702c40c080007400a036454070041c419010348020358003443d845a4800c1c454045440021100224912038016244c4103200020080481036150520003406523043c00b800800d0010342c00e042628042400f51034200b10b258001942002680381e0209680102d070240c003141e040b003102ea2650340b120b0280c0940100103800a41c2d500c4180c6105000302400280c009020503603110003080000c143c185140080000b0920b00740c000c0c084480c181c498258001c251050a5240400c1000000c1c075000e50b9680032200740b0600702981c241512032007003e01c06410814046a0765145a0610102c2a00101c44501c01441500c1001c9178441c854040c0902490a0303442c3c40c1d0540e02d03034840b00c128450078520100420401c540d0700040d104c85600b280d90084c04109600541d00341000111810960210440740c0d002007052405403420480003070101d1020381203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 714338633 1250 714337383 714337387
    0xf1902031902040f0f021305030f030a03020708131403010605040e2508070b07060c022b02250816060507031107050303190e1e010e04090b10050a2405 66
    0x502c0090018050b410b103001503035103004400d99040903103a0040c2030800180c03902c1114640e450003016640c50440015988681083c000c1c4091035001e5005011168400c103812808e0550808800070151001d60101d1130a44041013074007090b060a12904001d480292000e12841d80401e480707a543e807400544140c0c04051400000980d07a011206000c058408032050b21003843d914200800300380c1283d5015240540381482d4180641d00004000c2c066004c9584e044070340f001842c16038034030080300784c10030700a600a00e44140081c2e200818007050207900144051400c5082294443c80e0600c0c8402d240305204002034140b0159801c24255010113038140b6184080c840803022040c02d240326540b00d180c02d4400030580340c2c040d1000501c00107800c006035441103a0540c40b501041107100d070f030b83c0365646507406e100711420f540d502c00d140848203c0700141000c80c07020102c0c2d96680e0590001c03030740d903082c403030390507405000914014142c00000c001e6880d00000e030f40358120544000418000c0140180140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 714339883 1250 714338633 714338683
    0x30114060405090411150a0e1203120723160227010801060608070e0f2b060e07170c0123030720030a0c02060304230f190203 55
    0x140c0c9007200e029040241c09102c0300d0410780303082c0340507406001010f4494100104031400d030884200580310382c01040c0e51440c0700c48246409000754081790580f182464041003280d1480092070110303081c011106a52228122103108115002c078903259030502c02c09900800c40710103030b80e080321464030311640c0469298a0062808070045000f5000da043c202140707482400000701248103505c20411648261507030b0300e884c1d0700c44000301d80010350003900e240c0c0a15840309100071070500c0300080c0c14130f121503140910010b0100b01078032250f007080c50040350303e1600c030035044061020a000c10b80c020594007071044407940350303494999100c41018520300d04005000180c100d010040c40b40d03221200c1c083c000426503d00b00100003c028415001011151041a400c90303070398088000f0031908006103940c0c82400d044015406c000f550752000d04281d60a51107041c0e0795404403001e0b184243c0f1085210001c24440101e211258141400290300101500424500c5009078601040d03200c55000044903014110390 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 714341133 1250 714339883 714339889
    0xb040e0604090c241b0b070201060f08070f1d01030816060f09030305060102070f1a0d1b03050c0403020904020607230c01020c030d0906050a030b0411220308030114 72
    0x40300602a01440c50007400150b90b0414200d05000407000c00681d80d88450200016540001005c904c840140c0c00c04078110003003081034032100e420072203500c00807901903a29031881c80f1521480c1c20400c03898110b01410800f04013070f00d510400500c000c90f001c0f000902000c0524801000c144006000030000196035040c090a01c13000541080d8000d5041080808040c4030000a00901c1c404034080b034030344000304656600005a1004551185a050104030705103000003155041d03030b100442d2401e100707000c3d5500414141c09141c41350b40c5144c203001181340c181c6000400381d075800303020001c0102e0b0420003880903031503107411285d104c0e80580d1150b564003098540804448044c0b000c02c0c18074060302e030304040300b007101050005c90070380300340d0031100404a00703c02c16444808240500c004a17881031030400400d80600d014144049090500103070107507a01c0e001c0f4098540d01d1512403403c03e00060f40c2c6251100000c03d18180003050010324460600b1030780d561019210600036000b84a141a0007825180c1e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 714342383 1250 714341133 714341141
    0xe0105060d1518060f0c0c11060901030b092802031e130b0114101e0f0912050d0306080f21040914070e1912030c061b02160b040e0604 59
    0x100360b038510284841003400c11000800b03005d201c0d042058140b5456104080c4105080b0880d15003105143c24120000c40422080f07900a481c01030503d9110580980680c0d03e48540078481d103450545005070312010820780411200320034034020014410302c00d01070503552940c130343c00b180140380d41d10202e02c5c4c0300d80c2d10b448120340d140000140550000070012480403490340b0380c2c4020f84030907200700c0d06078070500030142c41c0c07142010008101c5c548191480942e9501c0742d481d09034903008034117000307541035118503400b5020550080150758a5102801000390a94148107c0d0001d200807405010b03d0510024110b85a08030030301944244184403002c0c2c08408030804c201c0d001003c0356201000038001d415403020481d10100d0701e034004501d600643c0c1003d400c00d00341100e01d010101d10b0300d240703c5003400c44c071403c40c5903c07400c00e404103c1c540341d10b20001109845003d40010300d41188090007050000300901e02600e0b01d0250100b03103c0d80345c1c00c0001590905c1174a007035070308009000c00140e5030480818024 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 714343633 1250 714342383 714342401
    0x20d0506070801081f0507030b0d060c0f020304030f1b05090c180109050303031f17010e0705040e030304171204050114010f140d110306130c050604050a050105090f03010e030a030e0105060d15 84
    0x10844d017041e004100850303940210460cc15948803415601c6004c001070762030b03001310701c0080d2031107260360303402d500103058401500611040320b0a40300c040c54079100899044c1c4c00445004050341e02c00940120107d5990005c13162464003460500b0f1000d00b480d0209403240000303400070345030298102d6102c80303601056000101904112240604806003084120f0103801071850307804a40c022480086128102800b881c00d566980200440c5592110798500d9820204015014003c82081c00a042c20380120840c00d4000c900510020800320509074040c5107000041e4000054030306000001c0003000302250542070f460204490740c40d0345035601d0400e201c0d0364049a00c1190305002d8001000448140000c48111081c02400148451901c44052201a1066004803540a03c103071804202c1588100028074946901600384c0302d01141320030100782583e404c10002d034007541000c10910051035140c881c80c00608200d1009114900b401070116010410382c006c080c0c1035031481042d105996115412461305 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 714344883 1250 714343633 714343639
    0x601140409112d030a0f0305070c03080d0903111c0c0507050603041a0a0903081902134109100b0307030b1203090a0e060d020d0506070801081f0507030b 67
    0xc0805a81e25001110308800f650081043c0305891011414001020503601c0da000d41c56141100c0b242e00e0984a90b00300003001c640410303846602000240700032019100010402c18040742c446242e1030701030010038008254003890f50060500025800c06035810002e41c91940c20881e040002ca414082d0620600d9040b182d00148000180000c0054000004804481c01c42c000611900c500000c641951f07070310039010700059500c0740441c400c1c440b070300c1c407500e0318070010000145030001a2103415510a102d0340004541e44e005000900fa100c00340c950000c81452400800541c8010304e40c60f00503032180e42c80355074010401d54000402d01c180c40382100001c3c1880e00981a1286005040100038103080c803e22401007440c402c080c500b92100000b0768001035001040c1800c50307030420010029400c4010007490f03200c4482d90282d8051f03183e444a000142e40201c001d4070399440d0041020b880d007041030344903071420751101340b40005840d240205068598000b03032000c90b4548524030114054102e69841d664 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 714346133 1250 714344883 714344899
    0x204080102070c2417220b06130e12030705120a0504030e090f07031a060a0e0f10020d0e040603170a080c041512020d181103060114040911 61
    0x83c80740b40ca00709001c80e043c50019003051840440703894840031602d600300010078100c80e010149640c800355100d83c084504a4240e1b00c2100c2c401401c0300c0803103803201c195a42c600000502050742048065020081d07416441840381e40000128144e4403400751b9941c2d1742511020001c5441c1501c0b45003145c0d085080c6442080407801c0100b003043c01403105550880c04600c00d80108407941c14481203043c421007607400480461b03620703151309070041c1803910140000c03402e81d03009144180d0b0b15007002d01010100f41e40c0d51103904106105003c5240501800701c0d205030003050b240704246070f0000c0c14140b072800a01d0401d52180322280442e02030700058100410320502c8510b5503e40b005441d020f080001265600d84c5102d48600c1c14041017440b0300e010700141c04450400000400d801602d4903005c0c00c100d0f0708010300d0320403d401030700100c034016403080b4070107020180007006001111a6490411000b10702914543d40342c000101399404c0102c008500071516158881c0610404980315004014094445a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 714347383 1250 714346133 714346147
    0x90313080d0e090c090904020d02030708010c080105031203040f110406061214040c05060717040603050117030913050c13080d0908010b24160606030b01090903210204080102 76
    0x203494100100d00d02000402009820400b843d0190070705014185400f195031030a07810006116000c040240141d0704180340503440c80050300d080013030800810f040c000010380300100000c018084038061f4006446a0b02042400131282090340c06c40e41c120740c0c050000b02100400380742807905c00d014241401da006152150010380d49030010403810030410840d10402c00d900d44411441240c05060305c4c00340201080c89014091404d11030b0041c042c0134042c1e401c9901c014225092070074240c0c0a6080340c40000d45036401000140300401d0350030280c0c40801c024604111031680440e030302c1c01a500313418003030300e8580c8046180290154100e0f0204054520030040058480c1516981d403d02030b500400014000c01c00020510b4042c41034008d814002003984566060602281c00a28034802a80058041c10041d1418040c420840101824810710300411302505e1800c01d00c0001d00d050740000004c0b4207060910b0006580300c541c408800170349410042c0417060702006240240034941012010750310011f801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 714348633 1250 714347383 714347399
    0x30405281707090230040c0303031107140106030c08060c030a0c031407090e011401020a06050402061207020a051b10030f022106030d020307150b1807030905010c0203030709030b090313 81
    0x34998000551750130550401e5178140c02812110111009000c8074500c00041c800a4880e070400d42242410070402c03802c184154807400d0400303140040ea042242e549080810800100c1c8052400802901005d8419031404c004404d05502c401000030140598480c450b0031100d01940c40300e403002c2d44d20b42a00a40d03242606000c2c002d00481d00501800344000b000024902c07000101d6200350001c10781c003800a03500340e40e0b43e0102901d8042c008030390104007070001c1e40074205a0014148599210b900802e4000d45504000d41000c440207031084036001c0d0304091201070f45910080c0b2248902a240000b0b0b09484602d06100900a001012000308a4981d6014013802c440352403601440701101a240701d021804001d036681d100d0481c00a02042500e8218595901c0350303800aa440c96020745100d805c407007a00002c000c09541201c17881c01281d51074081d241800b509120700c0c1d416160744c3c0011841c40c100010b020b44000725030b00c00208450456400168000ca00740160f40240c1e0602e02030901240c1c4400305 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 714349883 1250 714348633 714348667
    0x70f0f032c06060f120c040b0d14030a0305090c0114030a0e0316020301060f0f0b0d0b060703032903061314011d060f040b04060903021e0304052817070902 68
    0x1218403a4880700300c1500a40780041c001100051080006c11100c403249043c4805807002c481c4096204643d10700130000300303000c800c0442c04100c0c1d0002441d034401c00ca4401030200c40e409895a05654061003c070041c60345c00126003900c40a086601b1900d907a1045450000f03040500440701003800007050407807200b80c0b00000000d1141c800c500034020b01d61189581106900107219121050a6001080000c10003c60080c002461403403404900310610740c0101e02d441d440558100c00007030742c0742251103080d0040302d0744681c0d03910480c00c0e1020150a04d0000b95441a0241034508040105032040c1c0030852528050151898404028000390040741c500d040c41a0b803d1141e80c0103401800c0010b102d05003400415445a540805944c1d00c07911251560002042a450110194402c241d000304044101081161545900d9401107650340d04043c2881654250509500034803690450404542055480d840c01515000d90038240c9114507117454600d0311255602001d1020710001f00001181c0800f11 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 714351133 1250 714349883 714349891
    0x90c020d05030f01050108060d0804060203070b01091b050a020a02031203040512041802090f03011503060e070605030a0f060e0702030c01060f080c10021e0c09070f0f032c06 76
    0x25200c03100880d24003914684003c80309040030f03260450050085600480f072190304128007900444070ba18480d5641080d5a000790060740143e400465880c041060070001540034000c8a04240105400c500407450602e4400c070703d074003d010340403400f020902e108100d0445001d03001411154a01020030701022a640700313072002c0d60a402910285070703414100d40102c40c00c03200046505901c88c010344407000d00135000a090709034010360b400d9a284256409019080404200613410a034003859440d1403401c5460300c1d4900e18842c2c00c0403208000311500441900d0344246144c0e0003243c070995105003003000f020290050044402410107001800303900201410b0300d00287c0e0000c01101d5210540d64455607460310814116501005441c2d50a0811201d43e0f459100c1d0b500440e007007440002c015601803104812500c07031550054004980c0c038a410464503411a4881c00c2205a8812010008003610301000541041c140c9480c240169014003400340c1d161101002c44c0a06d0980014002544829040c0d13 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 714352383 1250 714351133 714351137
    0x803010512010204030b0c070606180e07140307062616080f011401050706290f180c070f0f1101030b09061e1512070f05040b270a090c 59
    0x101c21100300007814401c03a41070329080a034682c9282d40380205244903a200c40012550306843c3c1100140e05444080c014613106408600818100c1c0c0455149141c40030f1580700d0481303946503000102c03140d00e000c101281642c0c0945010794a2819240c0c0c06045625103ca801d80e01040c40c604018412520341d64510201f09070b5501e600d00c1d92503541480404a900b8000c04501c2890009840d4440d030241005108252040304007040403624801002440320b01c480908101444c001e0708011180740c42d001100600e10300f00c8600c40c0203103a030100d810700010006c02c070100c940310002d4910103110000a0100407560700560500c885007141c940303456030080c040ca5050100c1d04081840200749460b40e0741c2c40c429640035290f0040c404030030f107008440046500001c0e0f0403010499091114102101c000c051000502124403001d0502003030040c012120076010703034200300c42844107214103014441102d400b9006001038404024900e0741d94155682c3d00001d050b401f41d5040317000510941a50020b0f2500340d40e0b6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 714353633 1250 714352383 714352399
    0x212041d1303020d0c110a08030306101107050d0c03080d020d060b0c0d0810080f060f1b0f070206040b28030e0606121204030c050f06091305180a08030105 68
    0x41000c00d030348000c001c00c01409070b0024080e0607811031242c440550414010040581a48000001300d040542d0382c0e00400d8041d0000810001d090402d014440184c641500d400c04280450800d62500d4078028021180b045004069032428400e00c483c0b810060f641101005a031042104004070007588080f0141c07101d03d08060000441d990000c0c156035483c00040013421f40e130035801c081102d03240f00003050707540c02c10b200800110701e226040003d80c1aa030f030200018425400c01d0040200c02c21801081040d90503500400c202000b0010b4003528600003035091800e032070f0855440040c049016a80040070304100204554001035240d40b40c0c0081c14880c80d030543c1300c2d540c2503282182542c508104d00402c0d40e10201c0802d0450404030860f050f1b04505105451003841e8014814000c0c1d4019401641c1c620b035585024811841d051403442041841210518a80351340d9001007a104404440003480b01581c0d10000303a42008040301c140c001c801110180d0303401c0b140a01d00071a040e04213018442c0210a1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 714354883 1250 714353633 714353641
    0x1e0b1005040f0912180b0c03031e04020a170c100f1229042a0e1903030e010c050709020c120f0715290108130c0501050a0212041d 57
    0x920300c00c0505840e000840002c0603004950705413650a0034080014082101e840c001a840780780c00087c18101014078061940c1c0d0610714a034955020f06440c4d0300401549103000c0c40016980c2d403154208446001da41041d0f190445c0040c503041c00700c1820241e80040303006a22002039680605020702c03d503c591121140614030501080489609220140d0201c030001140404001222b09942180d07100910105440b00c9041e030498407034140c04807880c1c6045180740b0409c10b19400c402c400e0302c1f980c4141c50380000040615100c59566070341d440040c042c0468114015600d0344140c80c407080c0c0701e411408440d07880c0d55854082c8c2c0294440d05034030085002d0840401c41103100c00c003c50b00c064480740c0c405824a0590345039211854801c0002c42c0d8083e96074035441074084010301e0b04000804201040c0345542d40720000150507054001c04440b042c10460784144005040c80d8107841c140d540a1a0054944103001426460b14521034800100c0300301c04640004d581c2c1007500c00c480460f4101d1003003555134072 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 714356133 1250 714354883 714354911
    0x405091510020f1b040209032b0c150e150f0709060507021810031a040b0a021903050615030c04141f18120f0209180a1e0b100504 57
    0x2504094982e55007100d1104c0c003040d00301e0b810020f521a0010001441c02c081800007a10300740d40721000c2c2951b201d03c011420840c1c3d50041c14000c004041e03090911040440c1c0c2e4480000041100d038980d40c26a036218402c00b042000c1090b007141e0b0101407000c8007075040c4500c210000c04011030321080051061000071400a20402c02c0d00d0700d2680c090b0985902c002e56810507002d40c82c00401c1484c1c03010391080000301195048c90300004c00014641c444010342064104200402c01c0148115a41c4d4010003000a14848407554504d01e4292131500003480e4070748000144090080928180a4900100a21866404000050007100c18200b81014207100280510003404480d044051203007a1003004004450f006003400b42040000140015103141c50340001900324034802016a6200000162001142840c00400e034200a4240080070b410b2440c01d000395030340300d01c4100100540b0340040c003e120004421030909900b0380c06071008209240c030700c8501500342c0c0644240c500c194101040410581 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 714357383 1250 714356133 714356143
    0x24050f06130614090901140a0207050712081209030f0708090f100207030605100f080303090115050a0b0721180b131509091e0608070b0301060c0602040509151002 71
    0x2084110a070b105010b40f00c04109203403500030596000c554841d4007004c01400b410003454810140c1d01401a2a8000c90405926018654018101308540b0006581c08694038030103603081180e00c0000106103645141d2100d0641c0540d03482c07584034090100320700c001c21501d800501000c8000303460341c040e00342d0400d0030019110382886030301c3d000d42c02c10542400481d101d60001507224849541d442c103150390b00c4445503a15032141d4403003c06030300080180804110280510700d1000482c40e07410a5030784c10000000c00c98519440380403030b152400501d00041060040114000f0035801d4103130100510016005496207444e45400301c1d034107017481c002040000300842603e80c400c009402408000d420104000710b11b14000c071449080c00313030b0508c000a21031a14020369a120408059401070001d00782e401c1c07802e48103940c04c0f4030707196005000c1c20301090300460140c0341100d2603031924603100780e030700c0c20108000d100d0303a04200e80251100d02088090032a951401c1c4110a042c0c600001c41c07030a510040380c4035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 714358633 1250 714357383 714357389
    0x90112030c050d0909050c03061c0311100c082401050a0e0d0501060501090803030f070804020112050a0b03070b040b0f03070c1505070e010318080f0d0608060106020c03070e0424050f061306 83
    0xc1460880b010740c2b032a00350b41c03c00d00b1840c460f08005030b200c1e54181d00f6928080b205090340480d240c03105400303003204d54400c03001ca403c540340100046000f4500b11246c045501c0d00b022907410007902003010310703203a88100110444c1c00c50103050301140080301d04086000c0c001500800d4080b480120300003a06850000c00c0f40d11030400c5000311071054075005c40031118107801410a03030402909080030481390030385200321805240c1c02c10002407042c0d2400207150914006a000114114041c841003100f0b0040c101118904001107804503625615008241c0361b443e183d4070003074840100c4444940303e01c4466403215005485c00d840c0d4004e0b0441000044003903c1da86000c000d48840300b0011800003030080c40181c0518459800d640303003880d007500c04113411150141c0c000c00265000754010044150140b0644c04803200540c041c1000c581000c102110010000e0b00c01000d0f2074440019618441200c07199010014040805000e84d061050002e1003000040c2ea0b11841381400b018110301901c0a84120411 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 714359883 1250 714358633 714358639
    0xf010e0610050402070c09020c0d09060509031203090109140309090a11070f020102010b12060f06010c030917010b0603070203120105031c080c070b090a120e090112030c050d0909050c0306 82
    0x15402c00c4144000b94001250071120709982503c0420b010709607001521210b03004a0003448c41c0b100107800205024915403040080c88410000b061054802080700c080801c5091240b994030748070003210500404810703101030710952095020551300c050110003080c0b0147c0c02c640d841000c2c3c6a07221011b04942400a403040f169004002403000694011981e4450758014000080c1c12440c02c00414101104d6004400403900030301c04110059401c00d4056410100c00c0c41c2c002c214013215a0081c0c40713070101340290070070000000c600d10310b9030400b5000744144440140820342c1341d00302184042d40d82c1d040b42001c10000401e00700041010300f40004c41810041844131280001c015000050712501000340040c1c86194040050101043c5220440750080702400010040c042e10781c205035030518001c2d2001000c10002c02039503452a13451428683c191500c0d42854164000645402e81da4203640000c002d001d4000c2c11303043c0040d1500800490226054800d050202c0d80c4c440c03c02205901c003c4550941c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 714361133 1250 714359883 714359911
    0x3030103121e030e07030b1008190f140f0d0f021029120a0c081009050604080a02030c060901020409140f011205070b030108160501020a0f0204020a030216050f010e06 73
    0x81c04520940004d80f14250800a403891103490b5216007086540444103441d501c0c502141c01c0000d90070801803520074014803583d95046c1e050382d55900d07000704041c1c1c0c8041e0002140761034a040641041c800c107280d0400c4082110403000c80580040c0642511002d020003500900c5209880c004d558003030584081d0341d01c06201480400d601030b80d2000c03900020901c0e08881d803001c00b240718040401c245403050b802014002d0400e450b241d80d191a01604a83e0110340509100c401000103d00007a400e400c281c0c0700b11051340314203804c079007286180070f80607450a841c0708010600c510002c065000300259040120107004140c80c91544100000003a500700c82e03800145d50040110b4421250209800b520602c259010b00e6592200400580c0013a0009150713504034080b83c56811882c0745400004140a00152041500075203a2001074110244d003c1d024940000315030401034841d030704558141c01940a4001280c1c00e50612560701c000c003088003240d940c44c140070180061000250a4840c0141d9000a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 714362383 1250 714361133 714361187
    0x609060703151e031e121d0301091113150e0601020c10020106091409061803160b100f050a1203020709021215041a0118080f0303010312 60
    0x70000d14105004007000002002c0120703590303c0c5a030383e0504036409240c1d0003240d28210b007403a90b0b034400c01e03041c100d07908200401c10400080340e07403200114103045801e041c09009002c0700b06144405061030059499440e00f6151020040700f00268074909000359030012821890003040310854480840100030f9130f525210400018041c4040d03664414010b1042e40c8420a128020070340340d1603000d00c0740c00581d441382014000c0c1441e910811216035031a000420460515071141a281e2102800341929142c40600040c0c2002d42002250400c0742c0411990324285440e05004045605c160362034280d08002504c00549503064a07806000d5490041080d600d6514000c1c032052074607002c010440941c02010700000e00750596102800300000769400c141d60311b01e02162005109200080d030300c0e02c96440c00e00b103040ca500702c00f00c1792003400c0f0f42800c000c8050000c9206604950311103520040b964812940100d017044008006181242e104c0d46c444208110850400c0c0e802c6078000c016118170001c000201 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 714363633 1250 714362383 714362387
    0xc080c06121e090d1d0603011203090803270405040b060108190227100504050d050a0b01060c120801030f022b0606050a0905060609040509070b0a021e06090607 70
    0x190031041c807a1100700b28508901c94940c208404581c0f44545400550301c040b02c040d000102c3c0030149640410194500280b580003409070700060203112403206543c04071030101401045144017809132542140d80f10a4051031516003c2c40101310030307d207031454800c940810b003440d01920313001c1e40e80800d2024503503a40c0d4004545280d4001c05a410240350390300c00c03500c4d586440c4000e0a4480300358010406c1c00c501191996100340d40a900c240c040c2d803495514421250b40001501c00303031501141c4208045000d420217611300310710031901800c0151174000004000ba00004420f0415100e0301022141c48070051003502c0a200910000d000701e02510b00440052030401454282e416103c10340c44014219407200700650b001c1030700704a4046588039414009803800180c00c074020040820188172501e0302401080c0c0a00500f0f0360342d40200d4641d800300380b14240510030840905040d403840750711194140c00003503403509150b04050240883c02410b4000d888013098440c8118480303002071104e41c0b03ca40003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 714364883 1250 714363633 714363667
    0x302040b03100c031a0102060405151905010b030a0e0304060804030f0c050609060106021006080a080c03090d030509100806010503150f03030a030608193305130c080c06 74
    0x1085901d4003074044101c0c40820944540c1c8840b54107941c0010701403030822490306031415183c04ca0307819584100704001c0000e1001440b501d824802c840c2e01c40b803680b9886010100b002c01203162005040c1001c0c0003051502d1307118055840b8810502003441414180f003415901c1307110754020800064510000500801d0081c0c011840e844c1035898840c4e841c445546500f0709010f8240c2d80f2003400c3c1c01c1000100461541000f00e4000364192217410000d1502c1d04c20b404e41e581102d190020030142c0d0101c2d4000e103c10080c010703a104000081c01040c680351440c50010001c0d400902c6c264031403a07107003248160051040c07400d14440d5074180c48a61031600c6400c10b0f24080c0314440200d60780114100c100a801c0e46050003c2d10700e05c1200d813400f0030500c0c00d00555a0419001c40d28240010010609030300100348066000b50303030f030480011088070100c1c0c0e400e02800c0754101d000305080345074209028003180e0520350004403002030050424008413500d07403c20544a61180d43c0c5654401014407544030310482c030740c072 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 714366133 1250 714364883 714364901
    0x306121b0e090f120a09030320070f080d0309020d0605041b0b0d050615160311010921090501090b0d0f09050102210c03040b071107140f090c04030204 66
    0x9045880306503152022000d0040455000610f070300150504012401d0400022a24810246003242031072204036004112614130b00c0301504000740159221400700c143d00459905020704000d441c4195164099801c4119a51040841510a5500040f200c41c0b02c1c0c0300308a501980100b4101c0e101c4501c4d103c0320040e0030040c0055440c400e00b4550760300840b4152000000602010b9034954941c841e80c141c2c40d045400042c03140d40216416007540c048206100c08035030f00c00d540204604c1030790000c4d040480e11660400d81036421507180001c0c24080c8440d41c01700c00d0b110307548000307031101540071045c0031940750900c0d02c165400308581120034001d81c0394103000b13403040942005002440c0c0c0180c204260585207450000d883c00d941c00904c0100e1039000c04280241c3c400300a1406201e420304010300003661100600207060b1030051808151824072600d141c49140042c041254161921100e0308000701440d24070302e5105010591410030700d4184070030594850310300074401500341807441d02440082d002c189 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 714367383 1250 714366133 714366173
    0x6032703021501090c09080105060a05190305060c0d11090102060a18020d0c1502060f041511211005030307060207020103150b0a02011a06030601030e0c04020c010b03060601030612 79
    0x1803048503148642ca5282c1c000d28502c2004191007400c80001b91030081581c218006c5641090100500c1e0f8451100781c1c0c04545040d1010300001d1080551240e41c81c0c010382008090740200d0042c400580a4400a80340f0f580783c17003800308044054440403211398407d180c045800350704084005502006160f02500020400e00728441d581c6810744d0000e02c50b189036060440b00c415080000380202010038000150400325030009103810b0070031080d0043e6450006100034280f000d2041ca0354107001c0503030010000c02041e4910075071120116280c2d145d070a194000504020b10611000407403024061043e43d040b00c1000d0702039071a16105844000113584084003da05050f00c80034603145006094000c9401130003059051901c45007903241c000e0070b64200349540a048000030070000c1c0b880d0344e44002c40c2d41001003405c00081040f12143c00606100340d803000345501500c003060008601038107400c4400700c0d07807048054402c81c1d0340c1c1900540c00c0720010f00400e8503495204440d000000c11403417036040540712403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 714368633 1250 714367383 714367393
    0xb0f0429150f03010312020111030109090f02040c0c020102060a0506131a090108030c060105040b09150a180207021224100803070804030615030506060f01050705100e06010603270302 80
    0x51015070241d0042c4003100602d4070000040052011000e44200d44900c94030007445070b5000074021074014001030050110a03030780d56184508100402c98102c040342d078007030001d0100e540f403400c01608041810030140d02500801c800201092458820180300d00e20051513481c50040b180e450318018004411340c90711400c5210389001103941c6c0d4110701d500828050009641d2150f80c50740c001d0030400181d1015000e02d0a1641c074000702d58900e4042075001c02d08503844250185107078003b81003d0520303841089941d560560f09943c001c000c0d001440c10a000381d842e81800c00e5403007400d6681e08840f05079104006030401c010101080e50048a07900a1a01c01c2c808201c1c07038603a01800c1c150ba001d000c080fa40d0010008040003000024000d0710303c12034400030701d10b41051071038583c1c0e03031504030080216104410100d1900100ea02401c10750716000d0300720080f10107240044403100014441d003450940a4402c2000008801c2d1281c011a6054000102602d40e41112208104428409181d01720194064 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 714369883 1250 714368633 714368659
    0xc3114030102090d141005090a080c030909040303021806030105060d09050a12080412030213050121050a02030f1303020d0e011202120105040506060c060114060c100b0f0429 76
    0x641c03a0480c144e18010000c401c4c0d0000c2a4850902d80028107130094001030404d810020810340c0800c0d1180c03095040b054190303654000017003082c00c0d8492441d00a03801440e80080c44213040e4564003130f1481101802c0b05880030712b8141c2c20412140824480d0030b5104604001c90008030603960400800c03e4410011a0002c003c26540c464909056201150010346242c081206110301d220441c5140001402e04500d0035442010040208105004813030622190800b201d8201002504a05030204160030130071032800d000c180315001e94002c0d100c19402c0c0c0000400b255201c40340301c0c292101260b25070000c2c941032802030029a16022400b4015060202d420200340285000d0f0000b0004004243d030107040f19810941000101e50024020f14040d407000c0c80b0b040741070007001800cbc0c1d040d01c8042c914000c020031050001503140c8903440190310f45004000115030500c0c1c0c03940228450744411140b0052505070039041c80111016500d1030700f481c80094400c8803040c058046c1c01c061548000d0a10250b043d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 714371133 1250 714369883 714369889
    0x70302101706040f0e10021309050c19020f340e0a050408070b0408090301060602120a080c041509030b01120b040605090a0813061b03200c04050c311403010209 70
    0x806d001c040b422940001c0c00510b2001c043d41c0b500d0141404c5a410800b40c1003030152540c4501807051100c010039071100b20202c1d0350b4001c03c9940c80c40d01162007113440c2103000301045d50003843c031410032680740f8022003580010704015201940a403841a00014031075034511080002600c805001034492110030082100401c0e103101d42903103d10300980c007259480401c0c0061608682180e4400406c40d000100030505144800049680a849505d031424a5032100f0024000070301c40c550008020300c986c90000c0340030582100100080b24051690107140341e1b601e9503410714040040600802d444000c2000a00007105a84940d4200c0a03120031900e01e1185a84c40f142c0c2680304040c001a58081920f00308001603000c43c3c0038034240070540741503d401440d030b58054140b125100707440c145110920300d202d804c0d000400092620b520010b10030b008505042e5203180c01c03030b441282c035104401d01140b01c403054181d014406503140281e24080002203843e102d52803004404042081b98107540800803440a0390b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 714372383 1250 714371133 714371143
    0x13110907030204170601150e040b03100621050c0103050712051504110702090a20040b0d060b070c150c15051503070f05010e011e02070302101706040f0e 67
    0x8452501c00603900d5041560040510999800d860410307032140c40103200540c42d00c0c41e410202d5089083c003000c030142c81e00002e00a007100720409605807117040e403010000c510039080b401c200c5000030045410700440311f01c00d030303d010840600a00250304c920280b0b4850b521035849283c0c003180d43d1a00e600c081420740a50707011f40310291080b0a185070f019140303484c01e1400e84508041020f895506515142c1143c0c0490701d0700c28000c00952210340c0d1b40d51f121125018002810f00e110441d80311040d61151190b4540116820080c060400c4614244c00071800240340000c9540b60340d04194041c045034038080c184140601c1c0b040c0c509081090788041c090000e5100c42c2c9100d49402c03580c5000c1010300e8131401859140d130488065510943c0b12940800c07490b0142449002681d9082c81c244d075904502d80e0042ea0700303d1000c600348940e10520614841d0340d030b03404030719181901c1c821a1207030003807000c01c0d00482c0d140b00040128445d0108210104065140660100d070080e840407102041c000d591740c80d190300346 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 714373633 1250 714372383 714372391
    0xd0203071812020f0d0804050306090129090a050a06080307050a02040b0f090f07180e090f010c17090703061e0f050411061b01050c07030305010b030f131109 69
    0x45400440544071a505080700c940192440b038101c4000c0c4251600004c242602c0202810301030080b503140c441c184106034040320058080a021074405082c0106101e00030700003040080c0b040c4500c45484001c2000507404481c148400070021607058481c0140c178001080040c0190310000e1740c071180003d020000303101800c8074900a402420441440340144025140d04040d01e07441041040c0c500c480b9513944450040d0030002400ca41c2240d55601841500e45000202110610101404002034500035005100303210390b002a094030f4400c00e02c14615800c0e10f098404c650042214807024204c3c2001c242e4100741c0c1300280c0801c940e00d1680e02e80700d8408591240070948000451101c0d03e0310040c078940031b1341e016619031080403c014501a03d681b41c0000080440e00d1007807038009445880d5420080c3e940c1e41e65021800204001c3c1086440721071344c1e5002c1a4200c002c030782000b000103611070001d0242c038880c5103802944241035441c4500305040c00700c1c1005c02ca4620423000c1206506845a6942d070f489 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 714374883 1250 714373633 714373637
    0x12011508060423010f0f0e0c0403080a030204030b0a020301081015060c0c0b030c190c0222021e301303090b0309061b0a12021602040e06060f0a0602030418020d020307 73
    0x80d01301048054079069076004101105100801c1c07021025841c4111270860350001c0d02181c40f402c404908a000e44103d03031015041c00007d0041c85030f400141d074002c40c122141002240d0340680401080002d84800120301000881c17003100401895014070026501c903442402040c2c0d59940314240001b89400603030b16030f0741015000c00d500414849000d6220b0468000b4246070703094588690003c0c0901c0011144c0540031890b200c400e0540f40c81c25010346094010450451401c04444c800c4441c4071381040d040b405803002e200742444003074134503480d88154091140680315015914800a20b1780080e58240c11410000041400100c0d400e03560f021354020029030010340302c541031000813a96560304161083c9900b95080000c11400c81e081000d08000d05e601e4030300541c0302e810703000902c0048007110101079040b0341403882081c1c0103000422000d10420040350b10781200a00c61042c4054015a8000c500250340104001d02402583d030f20504014201b0540161900c9141c2404200342d800030b80f01100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 714376133 1250 714374883 714374909
    0x51219050127170901030b030d0e0321091203070206070606030b06040e0d0f0504080f0619050f150d0c120203060106050901020c1201061a1201150806042301 69
    0x10710102c2c0325080201d0500d260200340c800d1080d0340711020040e12510340b58161440008100c4140d034002d03048003040d400010107440d4000014903015110340f41d0000642c3c441c0c0150b2000c03480344050000c50302043c00c00d051f640c60a0281c2d1509200c44101e241150990520003409072400682d0344000500d1224454400416070364030703510b01180400d03400760110303110b98209132041d10360b0200000c078003100d21018038080441000c005015a04e0348141d801c0b007042ea000d84c1001d400441400180c59010f00000b4940c00545546c400100c000c8520a850040d10207042d0004030b00c0318030b1490b140c210780c4140203000c02082c44c0641d5440b030b85413004c0d0303010350862420802d228095103020302c0a0b038010700c00790510034500704190000039110005000040e2054041c11030300303001030001350310940103000d001001d49006484804c00f100036400c0329920084041203100045003007000b08003000d00f406c1054503140c920391107a0040101400300001c103134a5045460607000d070301608210a2074000d0a050540d55 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 714377383 1250 714376133 714376151
    0x40c05062d120403030902010c06020a030e160303050a0f1218061406030c0d05030c01060602010204080d17190209030703030305060a0512060103030c080d090303021b0a03090512190501 81
    0x40403003034400c103929450092000c0b1190004044000341d0080d85440d0000360710000c1d01c01654444060000035040510100d400760344141c169001c0341d682d05d1214121000d54000d03503440c0291282c0e034000240040c07003e1040a600c0c0c0d02411000d07074410942d04012001848a1a101c400c0f03a444043c01c0d060a01c01410300410b1100f5442800c5510030001081651450700c04003080e62003140ba03802e2402400723003a40c40340c1032000510030703140700310345100090203003039980c62000380031350018001c0004034010000007882c56070092403881d90038052105012a556180b841180300402c0311000a02108d408010b45030642e942030082d080614880e8034005824103203c024000c401c019604024040c2008a00d1040c44d2a00003422604407581032502e00840281c629186505000c0d52698084407410220200c04258140d000380c0b8014010505541705552054000e036543c4070880c8000d00801c0070101c050140342000b038291061200c0d82000c54000035a40301d240c2045060f84501036800381d54409050b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 714378633 1250 714377383 714377437
    0x1e210721020f011805010e0102100f05010e010f060e040f0603060e010c09080a080f030604140c031e0c180a12150c0206040b07080702010b0d050307050111180108040c0506 75
    0x10b00c0c00000a180c05204100402c1d00828411141d00036181030019084003071039039030b2007004440500700c82c4250030310081543c042410041c050a004d1241d070b4824100010580303003500601481203961aa980c80400d58002007803100801012403402d1416403030f481d000c00030940901805030001715020000407c5041c00000900d4180d40d600403a03056040041101c0104281e002540e0402032481c480f1a665200d06002400130085265420301049021082003070050b42d1002440c4140d28035080602c4241d0004000201020201c900e0b110340320023400f000e00821501e12018000c101c02420310780960380c0b40c10805111410800c01181e65210b103007008400d5500c580070700126507000780000c001e0350800d559841d5440130002c06020401042e5000110503134400d4000d85a14000903241c00105810303030400546a9212440550b260f608003400c11304500c40060403202c05c0501c982c440c92401c1e1080004407251040035000b650380b040c4111011415940b000028540e0103503400c01c2c604c83d100f0049035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 714379883 1250 714378633 714378649
    0x3241a0109080c0f010503060f1c0302010c020c0915040e070b0a030b040902010801061209170a080609040302030f0c03130b12090102070201090513090b090c1e21072102 74
    0x1050b0301d0b68002c0c1e49034900d0b60321515408501c041003401c140d900c9a0714000890004114450b41135071000e0110f82d80d0300382e192010f82c4200745500a90080c8070003e0484400d0f40d5034000001099000407010f8000342d1a40c0859012000b100001040840c0c40c01079000c0145c038028164000113801c010000d204106203070544184503080d11706480c00d02025109800103000903405225031824804030304400c4007136013565881548a2903002541d081d50031000d8aa000381074020003c10400701344004040b890320b00d00202400e105641c55402103182004c42c108ae4083c9400c80490300b40544001d104030844124141140d1015040d00ca19054179820700725100204032101400d80703202a4170410140000d40d03407001000742550003c0c0e0b0071003102101040e586009105012014142c20b01c04018808440d4010031980c589030022540e49658a010082d0b03114400440420a60300002110181c459400050180400507034402c050b280259920b181e1980d0840040142c100c0003840f2708100350841c5040300b8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 714381133 1250 714379883 714379889
    0x3090209090d0f030608031e270406080f060402040f2d0606050a0801090903120c030509010e011112090c0a0308040602060a0612062004091401090209060403241a0109 73
    0xc0c2c2480041d15151b405a06e034821483d10113012021142d00014007403080c0101d8401501088035110b0034494a20301d03100c003443e504c1040c0c0c480c608200e40000c40810000d81c0620040011028200c2903c95900304001001c1c1150940c81300d548454006605401c10701c090405501500d031001401c0c035174410690111500381d00901c0901c0010f0200700c001c1c0e940841c8072419955103c2d80024202d680b0f00b000c0d10411191b0300c120240a0800c0020b02c030303082c2e040d000103005000c11002444150f004800480c283c40f80800822007540d02882a441584182082d41e50000d80315015600c400b16580003044c102d0b265900152100e000000b41002229810800168000c04161701000003c0c2003251100741100d800802404003600c4007000e41d00350103003100305290345500b8034100740c0c2d540d514040c00c0041c0c01d620b44a082d004610000025606190b0700860713804050042c00b00c0d02d0182103507a40da4201d408001000442d0710b003003e00c020410000e10441482d210f0f185684100046100001040c3c0a4550 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 714382383 1250 714381133 714381137
    0x1f030204180e0d110102040b0d0e0c0405071706060c0f0a0516030c06111204090b090c030f0115020703020301020d05090c0a0605040b090105070203030706020924040501080703090209090d0f 83
    0xc0051807950800700d40581d0f00c02d46071a04620504242c0d031024064020b60300840a02000011005000c200e168440c0e8840c0400070700341c843c08078440c000c02c002c8800c04c54240d400304004400c14003189840c1c02c91264000b00080a0324281744c581c098151505154280744c825584c40745034024280041041100c0e003e038045070141c60300070b0442c1e8414849806502c1254140640172090810500051040c01d500c84410b0143c503480703983c0d850860020700341003540c0130b006d1041a00458076203c491000c0724841e100301064040681d00e400c1c081f8010b020040848005c6009240c008001a80c00380011305144504c2c650201d01c500307000040320b0070401c103400500d1085841c04010032141d40c004054408031011501c10b65180c008800040e5294461810f0007507050000142c00c2082021942c09020202c4065907042d80e03041d1000b4860184c05101c0b01240440c060a00c000c02840d881100340940c031411501c2c01081050440d80401d000050035504c0c1e06250f0080302168084980c06018859204054 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 714383633 1250 714382383 714382391
    0xc030c08030f040b0f0910120c08130f080d0c0503040c08031206130b09090a060b031204030f031b0f170f190e0d03020705190302031005061f03020418 66
    0x2d01c00902c0b142c480e0384210903079400f01045a6011311300141c1510111000a4110200c2d4100c10000920181c8208040e084161074502c0c0c4030525841100d109108580e2840c1f100302c181e0003516070f038400c444030007401c40d200e200c10002000080300074040c41e4031b61740d807649032243c4030300f02858610721705416500170004a074001d0002003030790601420015001081075520b145000015001d91000e02001f980c001e0b0400300100600a08820018450365210b01404007003100b031800d44205a00d036012440c11000f03201c0d051000b800401c0010018031440b500c46d09111a02c2d03c1d0200707e80000d4603190034180c904410101d102014400b140518510807205a80710303500d8242100b541d4440c2e40122100034029641645111035101e000d503024985000f0003c200040c5000b2514009690314224000c9070302440310f031051807140c408040b1034003060fa41d000780a44044544180305800a010040007580d1180c1c3e841c00107854002c03034021485000f40c50f6036015a444c2d08201c040040380e600c032545089002d00d8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 714384883 1250 714383633 714383647
    0x12030402150f2710020f0d030509060414010b041109151c0218091618030818150a050d050f0f040210140d0e06070809120915070c030c0803 61
    0x1d80011520042c040400c5a44903c0c640d161a030b81200c0b03003103006500002030f004200380e650340002d404000302c4042d604039102c038100800c0480544d0750580d0741d03800030b5021001040c0001c0381c0d0700b0b6210f84100400000500101c0c03510005060340c3c0c114042141c54040002c48614078105401c0e004040814500c80c03628115026504010b031000071982e448103a030b404102c07400003002c8003a9034016800001d0007045513042a03041c01c80c4a00280c081c44011030030b40015200c1c2c4540080035141183e822450071401d000c0034103a1050142495484a9844030040d0384103504604901c01814549015030384040e02d0315000d001040c01c6034805404079144015000400808000c00d4440c16031180e410b279080500c035181408248c1d1002c501001c01501c034540480c44c10390005140d40303c0c0b070f811104141111081d0720340034801e0343c900c0015035010005410541c0120152141e84c0000c000c0320b0320290403241c4442083d0700125103a084500110745002c8940e03010400e000c110f40c3c8910141510781c0c080e40c40c01030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 714386133 1250 714384883 714384907
    0x15040f031206080309060c030409060e160903050d26251409060a140409090b0705130509060319120f050c0604031d0409150c030903140f0c1203040215 66
    0x11701e0500a100c0c09000504044000301841070360300406540c10140320058403040344150040c1d0854602d540c0391070707250072510528415000e070340407641c014000c0e100c01c004ea024111200c0740c0128814040006a544441d000f0340b10281d060710030303d0003c0d030742e00342c00c12100a40c456102138254504208210348104000b00d88a85040700d9643c80b040300c40540e00d80540100769080c1c01d01d540f6450742a1001300c1c001825000d02c0e0001c0c14110721030724a90480d03030b07a222000d0700d07140038a01b0800304003c000c507014441ca00703200e03c0494000100030200d640a00640a0500710300061307040c11580303039500309401e01d2684d030000011503059550782030031403d00b4240c1c000702c0e60b00c3c8001413000e0208032251802c10401c40d240c2c2d400401010018006020300105c60800c03002d801c18100d01004074a18184a0418462003480b8895100c0d40c565504a01801c51030407a8030160400340a02101e0102003214840d83c00007000840112100c4445003a220316041c010480f543e5152580002092010070805801e40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 714387383 1250 714386133 714386137
    0xc050d03060b0f0304031403160e0402030c1b03040b0d02090411030105031011130308070219050d0204050a020c060106020d080a1e02130317120912030402060a0215040f0312060803 79
    0x204005183c684076a601c1c2002c41c0c0c4804030f0100d400b0b500f10000305100341302c1ca4520803108858455211034403903415010900c0220320044a502c160b1200c1801071621440c801c2c848004030030f43d000103d0b03040585650a0f0313000ca51000b900c4121076540001d01348001c0c20a40519a90b030320105402c18191744c034200103e5140c0d05082d4920300309640e9524030b00300c07550180c0300340c641d1101d010241000721a100e1808840f00d03440414113a20550001d02c484100382d440803585400e45001901c0424000c0310f543c207000c06003001401e502c85041d001d000400360b254081061034002c200a80c004d201b5402c0b41d0310080d00b141c0c1d000c0c0000c40101d05006580104100d100020315040ca1500001650740350555a80b41c501c00460300700804079082c035218100b01c1503000000d00382e0b130b8484c40c2c070b03a260b143c5400390000e503070b00b0b24009032030b040c40d5083c00020007500d048030203050307200c0c81c0f40191187e144122074548000402224102c5801d5002c29a001c24107038405056400c60017207040812910382070103e081e580c0c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 714388489 1106 714387383 714387397
    0x11030f07030e21070515090601031e03020d11030c07081c0e030c0f0612131509020a0302240309030702010f091a030a1b0c050d03060b 59
    0x1940e0007103003056450314060403d48410500080000c03036034010540680307a0f070040c2d00f00000b12200031b191862113070803400f019016640c10b502e070804404074080311004c09030040c0351780034001a40000b80f02d5940365441c14000c07030707800400d01042c1ca11f10512092408602074510000b581181c002850500926102040840542d6180085524100760a5059456030014600007100d0030110401100038101400003480c000324841c00500c1ca00c010359624007540c100110b14018822083d941c2110b5403464071081c000ca00c001d400103908580740d400040d100c0d030406800d807920140c0c100d0307520fa2550920f00d850351301e07460010031054480d0861202640412040c41c0805006407185004200707550351401000209408400010b07031070b40004150f01c10203690340350072420300002800c00368000c00c0e842e55000c00301ca11070702d00305052002c100c044005043c01c02209100f6200c000c0d0689000d = true := by decide +kernel

theorem cover : BRFrame.Cov 714208633 714388489 := by
  have h0 := BRFrame.cov_init 714208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 714208633 ≤ n) (h2 : n < 714388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
