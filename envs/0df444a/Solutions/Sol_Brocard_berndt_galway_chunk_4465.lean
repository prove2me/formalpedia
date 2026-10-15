-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4465
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:42:28.671083+00:00
-- url     : https://prove2.me/submissions/ca3ad7dc-c18a-41dc-9877-59799b9c4c37

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 802877697 ≤ n < 803057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 802878947 1250 802877697 802877729
    0x2040f06151d030f15060d150501090c050a0c030f05130905060406080d02070312090b03070314060f0f060306040b0405040b0108010e01091a040c0b2a0727090507 71
    0x1c03011040115001807084d0013460603041100800030380700f4010b400b1808176100d5035490400148101141c3d00c0043d040c000560140c00035900164051070507030f400d200b0200a640040c850843e4680a41807162002c10f4000c030740c0da00030034041c00341c00700001d045152091400841451122002c02a0f0380300c3c0300300c25280e80901c01d103440d11740641d801400446000300455050a03600030b41ea01120b02c00039000c100b07040810310b0a20b225144040140880c00d100a81ea030500389002402401c12080c14210843c42e0800710315586410f8545031000c0e00010300d07102003d2a48030400001d684040c04060b40181d031207404400a450754001e040c852401452082c40541c9003480305070035502544400c4110340d14095298000807007401c9010008291129280e040daa43ca140c070f110901d04541010b40340da6404900e500340c1c0100700042001c3c48804100480020954a050035940c2c105c034050066214011000b001070101183c00d80035040c145040045059966a111641003a001d81c12000741394103d100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 802880197 1250 802878947 802878977
    0x20a110712030c120e0d0b070e01021f11090a03060e06100308030708040807021e100203250c0e0708040201031107050a02010e130e0c210a02040f0615 66
    0x1003100014000e090107034201c410030742d400509041440000a108200d03104141904070f02c00c004416902402410941260b0024140341d409041c049900e03000160001c0c10303c407815440401c9600d6001c0b180e00b4a080ca92860701001030261400f001400f000503814040c00800b45e550140c5400118010900060303080725840e020350401c107004002004811400302c040002070402c1b01203a9000b0042d00d8070400949462174010000e115140c1c005e94410034241c5600340c1f8982c41400a20442d008440f85803421900b00303c142e84038051f9242c484018903e01180f0199000b903030000d25080d51054044100e0340d61140441004144141d070040c0000d00741e00c08110440d60588100c040c03c4c042c5521040c1000d0301c5544a90340c4102a050080c1001011407010400d40c854000c1d0704020b00004101b0b102179001c11084903660500c80c0d00b1603103d1084103014074a00720b980c0000310b1280c852500603001ea200c41c6d40902c8007074400d01d8082c1c42000d03078511002944540011200742c0c0d0f005696129105444414 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 802881447 1250 802880197 802880203
    0x130309060c031403040f0f050d0f020d0801050d1407091e020415200d030b030c0d0506040b19060b0702010306090b100c0c03020604030b04050607030c0e060c0c04020a11 74
    0x180103001804150003518021075004500080f80103000050180d485d80d0700c2c5424090807100110040040c0c00e011000c90030007501264001c4411095918500326804058003240d90b000c031000d080000c10541c8006001c82e05001c500d404142e4014480000084456020305262070015440000c48642c1c4000e60307060b1182018020303210030b64601c019820b15040607802c10140744500711943c140020500101020401d460310003030741b481240151100b000c0260006000340142d00d02981c440d018680d030219482c5860300000b403c1640000c01444203590b1070b5100700048201a0032400b050292940130b8800080500842000e002d42c070740e9881d22168188000b4066603120b0b0420f8980d0381c2000108800d588804002501d48811361a100401c841c46d81000000803815400103500400c0c005004014440c1603000a401180308070b0888465a4030100120126400c411034100002d15071040420140752060140410701188002e403403001c042600024100c1c0d00201603100425950140201626401c3c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 802882697 1250 802881447 802881449
    0x1406090d260901080f07090b04120203060f0103050a172a061806070f0903020402030c042607171905160b131208130b1c1b03050a0b0603130309 63
    0xe10704080c10440c42200103020000024108200c03c0741c52000610034500c42c050040060010943da107994945411014511007201c270300990082c0f040342d0200e4518000103801d18102d90b0000064030324086a5601c201d41d01e00c82c3c0c20a511510024400b02001c445c000181030250380b50003c0d1807218411a00c0c22605280c0010405042c40b00d810030003003400031011400300d5006116141c5805c1d10280313448269a407800b2a000613400038408030030070501c40c40c580014801e8442ca02c646403414201d40c00a04510603407a180c03c07080e600415010032007100c52a000d0720f1141443d20030380d440d0498684040b150035025035825900d0f0b078070240140321014156420940035001018490340b41030100f09405400900520420f1203801425a01206201401043e500c403482040103000450340c0d1380102d440b19400113580108240d1018107861394a511324071600d00d458140c00c01d00b1140e0020400281c00820004007410006a110480a002c0340d56010055114801206001c0d0060f211030500070100001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 802883947 1250 802882697 802882763
    0xd05060111010b1e150409020c070b07030504091a0405151912121116050a0b1903050406020408070e0a050a060612020a0216090b01020d0201151406090d 67
    0xd00f0303065101944502d1091103015000c44490754140d2800f50124003525070800c2108144140800e0100d00c514498008000031030406048510300c40d201c3c0344c5907083d40719840b001404140100420040c02e05141c2140b401440c04002101402c0d80b410046410f6420865292014001d407401076402403401c1011910105c601c5803403586000d0600004240300a11050050150a000102648050b02c00c410000124540a0a41e600900c030347d040e1a00c608100c0c050144a240050004900b03a41401c0aa42460b800305601140d400c1e1b00c89070543c01060040c01c2503514940030440844c415104001100007000f51002c0310035a45000c0d14260100c40c40a0070b00300d10a410883c3c200090f680c002052407018655800041c0c0d100001c5c0c1041e468007400306101c885840080800040b840ca10f644841c1510340c003a000d91300003c0801c00102d003220300000181c414406060760500414080203103540800c00054403551a04065200003100101603000c01c032280d09081c4e500302c40215a865610118000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 802885197 1250 802883947 802883951
    0xf0106140a29070506040b16080c0a03060803030c130b0316050a09030b010b1b010c1d04020d02070605010f0905160507061503080c1203060a09050601050f0d0506011101 74
    0x55000415511091007003a1106507010350b4403451003120240c84015400c101d5003159103002500e0400e4641008440a589400c41c15002416064a021031200541c81640e105441588c80d0201d0140c2031308000d00520806954100c0407031955001c000841c00b454941d0215900c0d216201c0030282c0069481d00f00c84000d00003401448550881414003201020b11410b0070340c1c80d80c80f03d40c42296911841e62015203541c48802c00021060b20f040c0050100f0400d81004058410740721404600343d9512025603400920f54106c40e03400982070b9041d07a030301a000140098981641042000141e821416023950302c1c42e543d0300100f12200450201100410307070080d06102510f0807006a001c0b03e00e52280002c1030020010785002001182c0d803083c25a5203205200071070443d100e06115050b03411450345002548111481c0d0100c414105065a2080c50b0007080301e88030030700301244080a002c0240400d414040207015410100001d038001c0c01140800c0c0c500080c10740750240004001c02c03580010024503074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 802886447 1250 802885197 802885229
    0x611120f04032d0602040306051806040305030c130807050a0f03031d0d020301050f09061b0f0a02010b12030d050c1204020f030c030f061605121b0d0204080f0106 71
    0x151480c06960440350081d020140c215180110746a03081038007440d071012004203910f104104403040c0d020308241c90182804004076a200300601ca9107001c0242a4103090348040000380001e0300c00c0e40103560000b1941074850a03c1074100302669548003d8005004c0754200900030f2203142040f4458500078005844500c0c6114516140900002101c108000706550f0100100760729840381c1c0005034400c1d5014000b0411440e211010640ea11001c0d64060158060000070424442c0d00e0342c0e444c0440d00346200c1a600d04011010b002c4415444001540195500c45148080968410215010907072201026544c2e407040c0c0f400d2841140c4004000c230031039181c00e000c445044d5400341d5100764016419034041202e581440d0000340b4140740e003101c482d450302c500c1215808100b0302158081c082d040c0005c2d203045031103d00f80203503660b00610210b030f00864100c0e800605003012280c50f2020303001c20000c010340f0300003542d40c01000341e910039000a44a9482a60100c40307030703030092041c18000c10704120a00020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 802887697 1250 802886447 802886467
    0xc0a0e01060f020118032f0d0809070905070507050d030612030302130b13030b0105180c0a0e0607061d010603110402070305041805010810050c07140313061112 70
    0x21410301501041100c6181c007014424000d520488880c2c1140000415000103843e00070050340e41246e10354041c180800400032807041303030340c1c130407040c1140d4102403c0c859681c4031044400308802000c82c64544500f240016540115200b024080c1d2402e0303071029622072050408038a801c04804c0303030208043c40d045003048819010454404500e074117190159444003d010049100e40e804d4000320610300c00000c1060b407281c22111b0180440e031003a11041c0150382c1c0c3d42c00b0022040200206941900040400100e42c0107031000101804081414090301100b0040c022603071503040040c0490b1007a99420540c0350800701c6c1c100c03400342d5000410003440440e00b0365945092400300810f4550042ea0040740c40d204060099054030040c164410381000c00e1118042c3c1800900020b02c69108140030352a200504a05030303001d1144114515120039181100703e681e510310500301c41e60100100d000500000ba48002c41f09a12001484a036550b006590032407000b0300e050250342607030810704e180104224041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 802888947 1250 802887697 802887719
    0x2041a18040c031203090b010e09070b040503100203040f05030c0d120903120c050906221d011a04050306090f010b06161101030e1507020105060a030f02130b210c0a 72
    0xe580d0302258005440c580304c1400d4000d44000c0030b00525814002e000419403c0d13004003660320a480b40c0c400c41c2c0c10503541d10744040c4140b24034003466402d9004a00010040c000540085801a01c150781800f0805402e441d0142140c00c4015800b1a41d0021403486500701e504c1505840700052030030042040c0103070f0303980242607451f03070007000d1420b80e44410310740401c14092010340709035410141c25155034081031040343c05001652890042003054418021031440303c440f505000c0d084204400300c00c17507420840386c6803148003551000c40e6100802c0001041036182404040d0240703403c00010010412004d20850a50f0300d03503100107024903810f1140c901c2e5105c8180a201519410200c035810140d40000124003901104c280e05042c0e02c55441b007003d0402911001c184200d649500070003880d1030b407404112811030644809801440845045400b52510000c503080c0240c1200001403900e80f9000810709103170301c8180d8010380c1850410080d5103090113001c400c9025200b144c170481036500741035981070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 802890197 1250 802888947 802888949
    0x501121404060b06091801080105090102090109090911060706150602011e320405151302010509010207050a080f06060909210403172d0306010c0f02041a18040c 70
    0x20303e4807030300b40c10394680740c0108895003008054050262802d4682c42e41c07244c0b440a200d030340ba4a42c60103000403039208041c400d61340c2c7c00d032050703550b004118070b443c0760100500710080003510180b4030b10200c2a180e5039900010402c55220720000f041c0209207880300150403403181c0c0a5400d59041140b107181090400c40b145882c1d810116001403822012802e54282c04030802c0008a51444030041c01c2d00842000b0791a0300c0f0318441d0f000c50f03070407080040445403a45016078206582405030100e1000540c00b8502070420001c0c10b104444082d5603481c0000c2c000d01417079021132481c1e00030883c40c03404094140308440c6c0c807120654504055003081c0882e039940d9140300035501d90708242c80285051000b0b40804a400442d0800345000904000c04445a8140c0c020b40b00380907980401d981403411600760206800c3c1c03000d03450f103040e401d6581e040b0043d903418800d00b0b02191803500c00c130b01100c010f030380301c1c030030560f9100c125401442d003203003d1410300805080640d299401100c2c0c1d4002c2100040f02c40722050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 802891447 1250 802890197 802890203
    0x40e0709021303060509030723060403051b1c020c04090c0302060a02190602040e13052a060f030f0f0907120f02030a06092a120203120706060501121404 67
    0x107030b032100314041004801400d0b0304010305441c103040c14400c00740d10001c0541481d40c00f48403803116443c0040b280d50350405c4058144240f44d04407030b001601090260b0051300c030000340d540a00b44009046d0310b969051041404030240407600b031400c101c02e1940c0c1046a1000818261000c00c44c0e20710300d0301c40e041d507403c1e1031000030300c07031080001c0c42000e480c800d00c00c80a011549404040511140b45407031006500140a8009144250300c002030080c032003000c40f003114039082030107040490f510502c1e62041c10301c040c1900c0c40c180d880103208045603d5a8001b4190f0401240e010350f100c0c00c050019024241016186286203040d08040c84a0301c14082030110459000c0b403240700c0d5210a61408c607590508504004c0d6050107502146001d0080580140c0310380c61091248184055400282c007410210f00040e404c4510403400f03084c00606092a006d1060500060840d100017018540b00a52a401440c013103444076150b6000308030558201040c10310601c0301309402c3c440452141511403404100400107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 802892697 1250 802891447 802891451
    0x403020d0309051e031902130504170d0509100603080a0c060605060c1f0e0a061a0a03150c0f140919060203041a0703080103170f1314040e0709 63
    0x2000800d40600050401480c019010002e0403070340c120748210100c000b0045502a0080404607580400207202d001c6600c7d0340104070b41903404015a07880c2c01031400400448804040410f031103840303c0307124050100c4514103000828586400809907040c0148240040ca4040c10244280700160f0000c0a4659050151800c0840000c130340c1050000b50400b548582d030400d4001903412a030b980302141c469010f6240d480c002e0b0a00103040d54010444040303010340105034000d18402c500240c3c0c140c004000070a42c40341c091400c050080c001800380841e0f980101d5802d51783d4001200c00345114014600e03401300b40d0400c16507502400d103000d00700e0b0b12030640360542c100c80011000c3e110b0359994851400480294102d040403a114400696294094004c0c800080201000034150100d5001145c80300d0354141d039941496460b558500300c216030003082d01d801d1603500344081200c8189050140c82c004c0490145990a03d01c0d0103801c1c00d8080f58a00e2075401641003980741c1c85080400554141200d03056080 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 802893947 1250 802892697 802892719
    0x80a0c0303121e020403050123181507030b01170c030403110316081314031002090303070b0405010603140d17090322031106030108120703030219021f060506040302 72
    0x81c2e8024848903282d89086160521490351110b80c1d540a401620b118000821500c01c24000c54002000c50188200141c0f40040c00102c2c000404901c1852100c525021500710101d1511843d82d046000c03290030001954810280313074650b0307104411602c2d0800400310620241482e044c51030319444000c001605000c403290070080d8001040080f554401c040302c42100e00070003145400f0010750720481d40303e0780702c079851100400c0e44100c4103089a020100140201940c080c4e1518580294100c04a119490b0106010715400b0562001da00382c800c0344903c0c000210207081d89071900d400900d85494014680c040c0a0702c036a619000b800781d0072940c100c00b42030591341e03442c844107519504c110150352449501208841010401c82282d01c001d880c85a0181b041c40102c1a05004080c042485403951a51201007405c000303061040c01450070f0350103072801626202d034940d510740b450720704a540000181d02c029040d0703040c1680b0010004141031445402d20440e071411001584502031400041c0c411504111 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 802895197 1250 802893947 802893977
    0xd050c040b120303100611010b031b06130f091a0907030b060426190b01090507090504020f030a110405010e060f0c0d09030302011b08040602091305090a0309080a0c0303 74
    0x100c0d070070360039185000700c9a130303071522002160f41d501c000c0c07290710041010002201a441410b010310103410401600a100c504040c2c5548031000d080c1c05119504940c040010350140d0304010031a101401c0501c0318041080e02e0034540c20308580086a03242441c50200c032031003003d03903607400e045500131071249408140464000001803040c856a4400078125104c03000f48603150540c007401032800f1050740f0942d1460b001c012180c1028803407081340100803a85400060150141c44d900c01c0303800c04c4c0b0515107220b031181c030307200032504a900c1099019030a52011040003000c00e814010b0803000800d840c19141094902030010b003440c1c40040c1090311a81000c0351a00510502d501554403405513a0101c0d502000304010250125009000c190011b5007030070345900c2c00041404502460580079511581c0641e5940c40704002504a0400244e002c41f443c1500980c40c0b049001c1c10780100000400b410021074240303005400b048803a40006504d0f01300000c21000b05221086000c2180d405003068010382060714 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 802896447 1250 802895197 802895209
    0xb0609040c12021801032403080d06080307060b030c0111120f07300201021c0c02150c0406110a0f03051c0504050a0c1706180c031002030a05060d050c040b 68
    0xe10384402d440c404607040e94038807851a41c071306000350207817010481c84021326a800f600c21451011f48030b00200c20b000410001c1c07280d000030580105103a00000380d03079448800d0346007036a12944007610155291003d031100d80c5403c0c400404419002d092204e0b1140c9103c9509844030360441d00f0700440c0502003107801011035000d044400c441e034440060314082c0310b401c40324031030561000d403102d00340b2400d6104e44941600510072100104046200d02c20386044044802c8003910b01982a0401c41c000c00c0000023207081031005050252840345000c54446040c260300800300300013840c80201c0c90340b1241405001c500c02d504410003a036091b240084c0d865242c0b101c101f9a030508000c404912600e00010401030200c045904292036200381c03819200c09507644203806103c0b088440c1040321340c10550210b811083c4103201c04030384400041c10744490784090340000c0c3c03c1900076000790303407690303000401c0042908181c0716040e8094422124403071204c086448145e0303980c0711011318900450b681c0e00b01e482e156860b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 802897697 1250 802896447 802896467
    0x3090a090f09020d06090302010506030d080402040c050712022113030818030703080a03050f0106020d11120d05011503090807031119110a060207120b18030f13090b0609040c 76
    0x13405001c0c003081c16190241c020b0180c135000750015407820010813074510380414445a0708000340d0b00d10040c1c0d1129001c10004000c0710307601c001808410802080002d03480d0602041d28001c64015020300c2c014820a4019440d2401480700b201c14200003489141009041030f03805c0e2500880f540b81c50b2455460421640701003444101e50500c00e000000013003004402c0100450019960240002d480c3c00100900c114400c1c000c88015800c81c40044040d1441410b0126040ea60341c402c0311081c0c00d00c5205e0001319445003000c5690940c541700180180c0c0706c003c07582003410f602481d081100c01c84507150360b5520b00030f1040c001c081016514194200010400400e149150391041c020b440c860079241c441c05030303904000c80703602825810714000360207030011501500701c0e102c03101000208292582d882d0148540141148034101070190b000c00c0c3c00d10104083c0111121f103034800c80e500c810b210000b0080031506c1d40700305009402c040c06a401798a401c0c3c140c94246109035400305c1c0e041d030740203001d4a0800d04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 802898947 1250 802897697 802897699
    0x1081009240e010801060b0301050a05012613110a2612030c09090a0e0607030b04020c0a030e01090e100302010e2d191d04021207090903030501050303090a090f0902 72
    0x126520118034488440b4146040b100c0c0200200304080c0c2d80c0782c1c8801c1c2400248990707940070740e031504100455405031302003d5440542a94661003003110498810700c1c0c81c0d0545440244d000d100c0313242806c0150000191000f10821505041c0746840c100d402c50504038944600980c60000b5051440d11400402c600e04012480c3d4840715101d2410356001c0b9090b8100500061007071040c40b02081d450061445000c05980c102070240c901540c0e40c9005901512030210700d2a0015400c0041000682d03040c8400d5500a11030782d5a51039901c0c0d000001040c6a0791a086034140314034400600403d10b84600801046950a007007100c0c1d0303400d007400040c0e4204036005250b032800d03011049a030601c2003092402082ea003030483d442d464052062701c1100c00c00c22140508280c4c410411041c600e0b07800f520419580c8284000e00d10a40714140300e0420303040136046d5020700c03081611140031508140e090f00409000d05800e800940c00c0c45180000950886c00501c50300c4030440c0d450b000300004811540111040380d070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 802900197 1250 802898947 802899011
    0x7110304090c02100612030f05090609090a05010504142206110c0a05120403030804020904020604120f11010e06031f050d11030705060306130e10051e0601081009 71
    0x4010103504c0700414240d40c10401e01c0d022010802c2e40f04090010510354040e5501841041d00240582d45940451030307469001c802400890840e039911403d03107108107040306c40410702e545444240300585070b154840d800084459010010b035224541703180380c681c000103a0b10450b000f005040c804000c00c80c21007106014400000c90440c200000a02141c00510400c11136043c200366460740e800d18003480c040100042c0c9010040b6000d850018482d58000740000e00181c0380c01c0d0380f4003000384603e140c0b003800c48061070741d003001d10144065034030300c203c1200081c2480c10b0000c2400001840911000300024402044030303050945801c00e400840001d000003904000c25094203041104204400c001c1d03952291242e03050200361400c1c5481074074080d00d000782091601400d46c9041e0350161486050304100c900c14900a41d061990601409018194295200c0d80001000b103821811420041c1407078103004101c81480002c281c41c0401342c003100ea09110004040c0d40d0000c0110304000c2c5060f030011014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 802901447 1250 802900197 802900211
    0x2001031b200619050a0b0604080a0303050603070518090a0501060b1308030c060106050a0c171209070e07032004060215130203031206040915020307020d0c0b0711030409 74
    0xa60456495141d101070441e482030310111540c40c0a66881c0101d803030360036100011a052456204a40000360003441d403100100d4595146e401003900d5030003075440301a10741c1c4200c0c0210181074240c807a00c0c0d0044016000380c040c1768140301c003282104841e584214100c10f00d04c000101082014002c50100d60303407001c024060035544282c02c4610b60031614010b9100c07050800002102080001120700034141000901801d0386080c4003070f9401e411448010050011002c040c01c0010000701c201c0d11b03410807096000d0749a00040007400896140245199410340c00f82d0424072000001010050f441600d40c43c01083d0b18140607007a40090f2000d15483c41140000314000c030f583d50300414024218075012080d02d8845e0b40e11400120314034150784000c0e4141d0010405a82d200050701e10207039000c40301520114040080d40d4076880d98140a1a81706401c035400300c1405803641d414444001a2181c2c0c2c600100c5c2015a5215440443d00c0600b54405011a50740c42c0f0792800c00600a81d402000c030000208054 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 802902697 1250 802901447 802901501
    0x80d120e390901061b060f052d06040f06090509010b120a15020a030204080a05070f0b090a121e06050402010201050c070302060a1104080d110705010c200103 69
    0x444000c01d12481da40c407141d241a6610816180241803084028a481e030380703901e0100281d03442d01d68a907500c1001c0c03000c441c150000c80c505d401200c144040140f0001000c0c27510003402c0e01c0b041c43c0d44c460450740c901c130340307409405020300000302c00e4018000300c0300000c500e031407400014024985a403011101d03609003810001034240643c030501d110001a03817000c20301880028031549800b110742e401062000c84200c0050103400031780c041c0555130a00d090051405858150035840c0c08180001241ca59000303260a02c04101791422080c028003a07078481604050484001a0040c0c01c14011040c413a070030040c03614107111115403500070300403415001c1c518072000781c01c164002c1c11045030168095820074012408001048d0112614a42c05902030095a100d014400c005016039000e0001c09020a00010802d114188011045801152a201000501c01109909019503503102c603040c003850b010f5280108120309c05802051031850350241441032943d005034024904030300e1810200302e4a400070390395 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 802903947 1250 802902697 802902733
    0x30309180b1e1809160e15010311070b0c04080706080105010f0c1a1e0f01030c380a1106091e0c1206070801090204080d120e 55
    0x40d5400000c0018628001050340c00a03615004206900801203400010032050740020004003650001c0c144200c0c20740040d00240e038624199418103464010700141c040c429221a0004010315481d40300c54010300d00740c8049540f000184100030b05040d00c0da0746c550303d244021030480d0441a0300a449c0161403c0400749908207800c54042d083c2503101e4410301140b0303c2d001d0300f2054101c42c03059503540c00c2d46554110840d01d81492400444004034407a040340445040300c0a203a2288080d200003075803030354051180700e07069079014080d00454052140140085000302c00c0c001e055034040030b014080e4002c4080d00c007007060b880154440300401480020019007a80034014818150141d440011400f807400c0d0b0103071240402d03141003007160310080101c02e403ca03502010f41c003c90280303002d80d060b109007440400d804201c07000401c0340540060042150860300f2179200b074050111141d0840c10306042c8045240e0700c3c105141000148103d44c4400620140590000c6001a070b118060b0f07000c0c410062640b102c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 802905197 1250 802903947 802903949
    0x20d0c020708070b1e0c01050103030315060912171201090614040216110609040e060603010e060132130c0311070507052b1b050111030901200106030309 67
    0x8014011114001030300940060801c040d5564520310518000c0c440c2c00e01ca1928010301041d10f080601440b04410940c402e1180900a40c002e85010032208180b0f41c101031183d0881d00088140710540d001800368000340c1042c103002543c00010790f0391008540c0031840050040280914040e51500e0021400c8440c9812010448002e84014030401c071129041005a02500282e5440082860703548000300c1d030f0100c1345204065001d40990320b0030303500d2804201501da609460b0700456000b04240080c9060034480e0120740701c21180580825414070419080f000c00c0100030b0b041000034511040c1685900042e0381c15a410000d0042e00200070703450352103029005100300c01010030f20b000c45440002220b8002c50386034030b5001d0080c0104d20300303110400180d901e4401e07400403034112916028034840c1d0343c40aa1500d1900030106034604104103c03424a0b0b04186400043c10081103ca2840380c900001054480220090900489064503070401c01d24284081d6500c41075582030180000900d50041034481c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 802906447 1250 802905197 802905221
    0x3060c0903010f060b070f03360801090308040807020411032802030c0a0305041703090a1514152e1215061209020619270b1309020d 58
    0x2106008001c00c00601311401840360207580c1804200340740000e80c800c284041030600c641820a500280031082c0c1940d031303510050648031414102d444800820f40c030f542d00d9006042c681c000744001d2890b0346d0014851000508010102003010a08608654840d0848500000d02d56401501d9282000e038040400b8496046901a800d4850320404130007168001c40740301e4540c0c0301e0840d1901c0c1000c1c00403001040010b20995180c3d1f2409000950001c207131004600684024009142840140c01d125901211199060301c1c0540f800c21001d0108458030500d03544007451f03580c1910249000e03001b240c0d030707002d00d400e010380001c00d03814140c4802920b0054003000d0100305d41c1e64240c11100441f4500c1201d42c03200213030f00d006000110400c00c0074440d88464100a80790000410a0755080c1d01103021904040c051020002c16103081103421035000306030040004085465081008607000f00c25041d08642c003a950058200003003004851241130540002403001140c1159030340481d240d804003d240ba000c0c01c07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 802907697 1250 802906447 802906451
    0x40f020d0c1d1002010204090f09050d0206192703020f011802060f03060d1403210f0f07211a030601030b0c071406040605010513090c09050c0903060c090301 69
    0x1000da14400c0041c0046481d201c980480b00c10741c500c0801643e80d0b002040c6404640d001c0001044c0b105150103113513224500068080f8003546a45031581c180189641d481301152310200400100c1701d22060a100d2038400b41000080d8520858045c001003a001c0c1c031840800021019040105940000c1c103d0241481d40020441041203440c040f0050b40d0000c2d01a500ca401032050042da05903010080d42c000000034113400c0b0541c80d60b03550600c2a4030720718440400740c20201e1004511041003840d88418a60b074020308150b803821501c403120801c400b42c003078081480e04100203804c10f4003e10070802c0f42100305130840b01c040c40d44a020350181c0405512a8841d05040c40b90300e03028200018128141d941c4000c0c0072820b692003801085981c2c00103c816941454044660865501c00740171080c0154095000032440d5810203003030041c40050448401c40da03c0c90041d070640410343c048409400e54840c1c0360049050703211410451814010103c0c81c9902d40107050900900004620040c00d907500c00f42d0007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 802908947 1250 802907697 802907711
    0x221031e0c0d0e1509060d050901060510030c08010506040506221701050115020c03060a0902011707020d0207050a0f030f06090813090b2e110d02070501020c10050901081005040f020d 80
    0x813100b010f014006141c3d03001001848007070b1540140350022a40b00414000008100b82c2c0c3d000043d0002841e00072240c042036584084916250b88910110f014010948805180c00e1420010401510961a0700030741040900310310b812090403808150010b0001822614101140d520304600a20003881000e400c4603080c0c950164490021031442d5807a50020003038800c03942c13404a400081c10502a04134100052183c0050381395051498080c010250740c0d004007101510840c001c1d15107000364200c13038800d00c8498010003c584e401e00c00706007907075840000455080c1c0c0c18904200034144080d8000c0100d2004950741232191400105d101c100c0e04000014010b0070412412310019441940406040034480504804c0301948410003401481c4035150121441602d55111810041681718200060300404000c10040da410042c00c480501d0450f190500300401e0080940144944050035040c4042007002403205070841561500518010b40184003c0d071100317514400070f5005011441c07031039140000d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 802910197 1250 802908947 802908979
    0xc0109080a02060301300807060e060402060f0f0f3105090a1d011b1206241e051b0c0904060506040b19030221031e0c0d0e 54
    0x5200c05003a40c024241c6851a4206110408005181400b004c80a04d80503911480322240c0d82c0c140806c1401802e255480d140170340341140640300c0101a0803200c0d4480c0e000c0c0400740c1d9985048032004100c240c42c082d91044054030308400d6019100008841c094081640d0b00111100b11200e0b41d52a05082440409a001c28051190144c079002d0f0320b80140b00a0002840c5001c9a40401e0302d101441c2031001c02102c0e9855491b0a403002d048040c9140803456446042d0507403c001103554010a5042c244480307030900d004a070720b400580d0f035a1204031000e1000000040d001c1d120103980414080341d12681403d50203c0a040c640c48051703d0701b60200c0d02a038000314110046103100e6070310030080c58500316841c2c50704c0e000050100942010b602642e0781d01c10740300b685c1d1028202038060518170b80781a45180b840c01080104495580c5a540000318075503070040701c0c500401103c9000d4001540c1040c07142e244d07801d64a940c050486040180c2c42401c402c4510950041d4008254142c01c0303c0c4e4480c0346074810 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 802911447 1250 802910197 802910203
    0x27060212040b090928060602060604230c040314060f10120b0403030209030706020f0111091c052d011a0604171207081b060f010504021305030f0c010908 67
    0x101c600002014140010034140c84c1c00080c2c5a0000301303801d0340d080d181c502484446601210703070200455855482c2000c211040e014000c0c51780c4001d044404102c0c03500800481c452004481360850800c0c83c02000051070358200a0558003d140c00c14449400a180d0b250702680c1e504090b00d19145c0301507910005800c07a542682803109031207001c401d400d010505580c42d0000400054002c406040c1c0a1006441c80e807000c200c442c00038007155005007192070102c0c02103800c50780700e0b108240e4424001c125401785901c4e04400d503000c0451004601181011a0419909003600500601c41c1c81c0d40000541d0508ac000b5402c5111000001e4000c1103c200b0b4644242c009000552541e40c02c00700620007002100403000c0e195010034a00ea090380d2801a4610720212140e02200e81129558070104215000ca2401c110007042448540c00506e07207428602e45002524205100f428070035500000c024810a142c540442e0041130041d08442140c114030340e000303840e03084e0b8441d0b440c0000c0e050b02001407220800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 802912697 1250 802911447 802911449
    0x13050306010b0d200d0606200a02060307050708030f06011121070203030f0a03050f01140a0315140f01180b0d060b0102072d05030f0d050a2706021204 66
    0x549865442d207070843c0e0b09880502544241c079009404110b264422400380c4c540180100e8805040003d509403c000303010f4104000700052048604084800c4110283c0016503400c05c56012289251255901401100c0c1482a8040142160790120610401c01c03d1041d0041c0148000d0704c03011010540710618968a03007107001610b43c084007480030700c200303488850b00a080050002d000d503490981c03180000b41003503218510003000240d5460401612a6220164502420407035041c086c0310b07080803002a0b403211190201400c0600700107c40308049540360701a081c0d204541c1040c100d0703442c2580c40741640050034407074420341900407440e52a000c01e55109038426458002c00c0303c50b0784d602702c1e15050b004103001e200c5181548a01341e0f0204c0d62000e1440c400c0c4d103102e168003104c00300d45005c800c03100305100660700c91402540107885c95809010f002c07912803046103551030055100c483c2803c08462400f210b0340041000a81040050802c140c81c412940540b01c09400f10f6000b585036003100c4403d0710903 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 802913947 1250 802912697 802912709
    0x30c18060b030f0a0b01120e03030105120f120a0c1e020301050a1404081b030f0715020c031803160603090b0603070e07031e050a0b090604060f0306090501021e1305030601 75
    0x420f070002400f0b000c0c0c0782d110b4500d000061403c0c00030b40c144020284110b801811030280185c0c004401000286045943c102d10360000c140a00400d09000c245c041e601c24140c0e04955103610301042218415108680f401d91080d00a590b00da00c030f00684170019050031141105900035424070002442c25001707070041102009840400703401580e126215135243d40c201c44149402d045121401c07000c0301c10104040e015003100c00403c16501c81c600d15250424034006514400528018492130200340c401005540140001c1d02d000c042050903140041c0c1412000f181d050200300104102058181c0d03d9071281059500c01d80b560941d907102c1a040641d03408542c030406122941a200107075895100c0d400c0301d1040c03500c10b805800301c0f2010714445420345804403a002043c0b9a580c00310b03512880c02840c403680040c010794007003025030304018503800c004c51140005001340fa140d407060001c01609504072440e071000300a1800b1001040e00c200c51442e0f0040c99208000c40909902040d50310300452351034100c0324 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 802915197 1250 802913947 802913971
    0xc011814010b060412030305041506030c1409010b090910031209140303070c03021003062c0703110301060e0307050402030406050405071403101a1005030108120903030a18030c18060b03 81
    0x110b1b540d045000d040300400031070f0041c40600d100082440700e03010340030146102c1d545411b00d582c103040c40f03c22181c29500c006441034041c500100003034000304044500340e400540b554201c50707880c04860710548040f940000d091110030f14829400765071020f190020343c1c020015000d6030103000400c15507603018040c000340401c3ca820000300014540450f9900703a80e5110706020640030359580c400e000f20441b40d4180e60b10840020b140c0103003010319200326540700801d41801c0229040460b1042c4050005000303d40a100b603c13990410550380c00c0040e04001c141c010403e56803803809140134000f400c02590101e40c0c1c0d1080c04001f0503c040201800c451030761000d0700500c1d41c202142c4420002e0840341c40d104001503058240c034213003030315441000c810f0b45100b034032190b58951400e83d4461030700c03041d00000d01600710248500e90450350088110740000300d540c6007001a0440c080806150207259a000600b82034003c2c1e40000c00410f841006450f5104900d010001540d44e01441d0505100845424210030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 802916447 1250 802915197 802915229
    0xc03090515190504030507030f0825031508070815043305131209080715030b03340e04020d05030d020a0c14030f03010303050c011814010b0604 63
    0x3603081d038035544a401c0603078502440d000315548804039031040d10282e001420005020050680042e00450214443d2516141514041104001540d03c1c8115400346014162091440ea0b12075040707901042030402c045101b099036424401d0762010f142c822100300e07004007104046000000f5408a11031034110000351002c00c0860900034000d610303018a4040a006c1c0801c070f1082540da0300c107243c0302c2c40614420701c1080e010341c01c1c040d141480c211004020010030007070030b0042090125060b0201d0382d01415446c40e0841d07014069010b02200e421164240c840e054000d00041e545e4032000c54501042a1903c800e0300304031044090459541c000e200311222100003207801030902c1c0c0c0541a80303c3c040d1083d2810032103001720303c1c010b0fa0b128055141c00542c40074051000c0c0b150003a01e8032268805c0750b00451828544507188140f600052101805224001c18001411070082d000301034900d13040d0030300701000707080313450100010043c1d080341480701c1d0718140c110900c906245003201c0681d65200c40c086846 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 802917697 1250 802916447 802916473
    0x611090307500a0e131401060b04051c0b1f091a060d2009040b100206180f0a0807060c03110409020a20030403140a0b0106110a1b06030c030905 63
    0x2c40b20010016820111901e00001c00200c81200180501080e6040003084a07050408010074542051000c003203914000c0100300074003075130084500b02c410a0382d080d407041d00103d16510041b840988045c02008a00c4100070036071000840083d054070031004056050341d103617190320b411199100b41b0501c08000000d072070102460320002070058030802e0711020880c1980e42544c01c3c0356505281c0200800300012403c8001c030300c0d050142c075150440c16a40000c03000608a002503844501400040e04161410791507490081c080c0002814020180c1c00c17188500010b240c244a181c0c0f04103015140e0034035203143c0b4012079200c1d020b007880c45510803d038107060508001010740298005800c00041c8065640d180031801310720441602c0c4240789001440d196413841c145110300740b0b42301b840044242c1041d0024000a102c2c4203100307054407814900b0780d09591240607968900700790000003078031000100303003a00040c1100503c0d0780c0548170356075024404a002c4c004240c06503801c03540d00070300c550462561031b441 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 802918947 1250 802917697 802917839
    0x60a05071409040e15070e04050f01031106160305030402010f080610030e070f15020106080706051c020f0c0f0706170103060c03020f0d0b0a120f0611090307 69
    0x9100d000400014075018100c1c0054a0134180c0d401101d4405e0422007005200c680000358182403401c05d45090080345002c80d2080da944c401400014685045407820b8441a121340080e90040240d80568005c00041400c010b08036400c00c072801ca0000d03d81000801c0d403248600040c5000302c40c068000803a18140300816006013800c4603440542d4411a1000030345003100d400d00d40d0080c202d0a0160a120440400013420f5404039040880d056105286c2000342560110881e40d00e160061152050865020107040281c440c0405c2c801401d4004981009032041c08101c07035001c804400c084560072a075590003500c030400e8080e0030354036544a03500100003003440398103d0307200752400d450014940451a0242d1a56070440081020301c2d0b40c5c1c0d0308007503006040c001d0320040a0480d180d43c400400e6001c2d0340b101d050011303509004102546030b41c03d800c110010b41041d41c1301d5010080c00d0b81c207a03680700e081540c400c003240d05041c010403001c00680003607a820030f04030b2607101030f584142a440c0304d140c10b00124 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 802920197 1250 802918947 802918957
    0x112050c011d1804051506130c05070804060e040c0f141818180c130e0a0c090b0f1002031210080a0602030105010e010e3f0c03060a050714 61
    0x60010494129605190350f0005520581c50424151865508050418619010030030700346041c0b8602620500950b1740c2d4070354646a190700c08000200b0030100190307089505005000000300311540c04100410f80c0c580000c0c2086250b4000d9400300b00011145208486941d00f01c1c0ca0000442ca031451203200160140008100c018401450070701c458035050085540b10b0410070400140010030800d0000703c046035050501c04001c820000c140d0251000d0000318020b054241030501c844d90f4505a0112020a2000d1080c080d085840e0a03030441c1c2d50500000076003001c0b2070441c4100d0404a2000d441d103050b1f0440e440c11001d642c011410041003070f0441c6034081018012100b000046080003c40400801942c00280d110b4200903841354507010024146280d0385000d68140180300c00041c407070b502e0304080c18540c0503d641e1800341c1c0900b1980255202541d110f28202c1c01600c6885a00070104d0010b1034116044043d41100d40c5035458a15410455000f60303401400500030000c1001c030040804050300d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 802921447 1250 802920197 802920227
    0x1509010302060d0b061c05220302060c0315030a03020c0112020735030a0204031e022206050a03050a03020706110a24150303090611120d0615080f0112050c01 69
    0x107468440080c11b1103c00022044a04a00945581c10441c0d400c12040141341071901904142003e011030b03a502035100c0707000910030031001001000140b241c0c4666041485030420180c1910031184080c10002c0d25001d845a0050204001c80d03819640481c1500c08c03202e41c56005441c04060150420004501c0340c404041f07042020740b480c441d03001c00420382e8021401240c3d000e500580d910302c0d6241c020454003c801c4034409031408203a05e480540c8a468000580141c041507180400384140c51410041841341c1040d50443d501d418044200030001940c440d050307020340c0840304601d070359040032a40030584c01c403080b03195080003088030001003d00118807040c1306034500310034030001c458110702e0031a006d5420001c011290300c8010414075800001c444050512440d0200c980e2003104d010641d21000e8070381c00c56800000207011312a4640ca980401c0c054000720044007071038020108028171846065901010b1070890500015541c1c02c0c1240d903800b1103502c400a402d032100c105005403101c0860208207 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 802922697 1250 802921447 802921459
    0x114030a021221070606090b1e1c0f17030702031905040504051306110f040302220204030803090115060804020105090112060f060e0f03190f06050a02031509010302060d0b 75
    0x2c020140c625103243d0485000c1d251466464100a0800720103640031070344030220383d528002041d4607a445603610100b051800013a500d0340c0310340c0180810001701100c00202c40380700001c8290410000b034140c4072030345940500806c202400404450519510041e9028000742e4020050300d0440c1d100a00c0920302c102c41e030300b00541001d5580f40810300b640c004590096585802d540002c0030401c1c54031a845041c81403e43d55810043d01c010b0b010354a105600002e07100d521015114410b07900043c1800d100e140e00614150b45a581e64035000245820a880d0484554201240308081c2d009d484860005c4070790303540d21600c103910f4540055030342d41d01901845041006002000c003610141d801050014261455003043c01c911307211005220039409000c10748078940c0c0b16020310b60f030703540000e01c450101c0c0d91580c1d11210b0b18840c5403505ca0401c0c3d00300e008000c82d0034441000940046a4040e600c206190110751100880070800c1150f036190900001398060340c01c2c481401c40d00c02540c03140c5841e050141030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 802923947 1250 802922697 802922713
    0x90105062209021b0d020a112407030203030702061f0e06060705070f080709020c0a0803180a03020a1101030c02060f0c070602030f0a0b101736060114030a0212 70
    0x140b03100b6a801101c4072510a414000722100e03070703101002614810381952010700a00c242c1a0b6036440000c196190352171044203080c800148003402d111488188210070001c85a90700542c1c030b8040d49981084940c03001600504001496041c0503940414107558410b034001e80703090400300c1f52280448050800c0d50000400e011200008400308004005803410030a0902201e00d0009030901e00001743c0c100d82c90880c01440560004800014111045507004050b079860340c0e075100d2101310030044540c8941084c411500700d0720506401003081c098842c003071905000c14201d04401901640c040220000040e40114000760314407203090801d54102c0c070000186898140142c40c0d0703009070303003051340c1c0d010b5107d54603814494400080d1103480c511301400c2d01c02ca00501c3d80c449001c1c0c070940f161001c44110124800000b8a5110001c245015403035810709810890030240b1013030b50510208a203421103a104203000030411449032440d440e02158000e004040a8001341e00388001850302d5600c214281c0f2070016 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 802925197 1250 802923947 802923959
    0xd0b070323090a0b13020d1419060c08070e0f0d0302071802030a0608011e150504020408010b030c031c0c05010908030c0a030f0203010b03070503281a0901050622 71
    0x5102d001e007088200805450996041c030586071840945000d00c8014006415801030711940160718407a5040007000010400c0102c0d040c0c2007084441c13806070f112a103403804900304245036100300480b03080d40d5512041561000c10503a07010401e942c2940d400400c541e816041854009540d800c2a482441510340180c0d441c2c000a84540200da02642440d030084104820b4640750700c1154010207022000b40003030a41280410a444000301002d250f164803011138441009001c1c480c24010540039004558960380c40800c00d0003080901c260341e119008480c840921171900280300f038199103480900458200440b442581c000c6131400d000c83e040d5407103915060101e00c50b00053461080301c0203101035039035141120b0001c0440d00300c500a5950f1a1060005004409214007900e512807040d041c2182d9035241c0390800310310385030a100e071695071301000e00080560034203607001070101c51688945a030305001351100b00700c507496003401002c2e00301d00c0c01d00050490003892058504038400e03800c148101c0d562108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 802926447 1250 802925197 802925261
    0x9060412021f090317090904121139090114010c08070309050a0e0708070503040206070209480322210201020a0807030c170a1a0d0b0703 60
    0x2000403000f04928050410510010440c10380200e00f068800e6803034000c042000a00c6900042d10181403013107180c114003130450141042606411a42e0203c0f6110308104170134004580265003805150880303030141030440c00c40242c41940500c4007c00400306a82000d04001034000002c810a04000b400080d1401040042c0000c0c5440780c06035580000040c100420b0000b026082c2d80240d00e1800c1140030802c0c40f662200030a60070900c0c61400617a01c0e101c5000050441c0907508019500c04100c10910400c110200103030b00c4100801c42091400c022408410b26040010320105210141d4880c80804600341103001990320288070f4484005103608a65040d000c3c441d010780403240301100380318507041220a007041707039030142c2e030751000303500c0d140031108028901d01c03000d0800310030300d5102c40c40d186903a40140741c1d00d000076040c1c410300301c207525020302510050950803800d1604280071080740c1c0c9103410310791031a0110b50381010103813072951a4502e00310020003813a1200c2210581c02c0d101c01e04580010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 802927697 1250 802926447 802926499
    0x603020406080d03201818070801060306050301140f18060c0a021905190c09180c05180c0702030c0a03060c11010e07030b0a0e0d0f02070b0906041202 66
    0x560300800050b502c840000e0201c8a19a0700840c007103400c0304004902c5c45c030748001c60b0000c40401c3c901705810301a100100d02c1000700801c10012511402c0200113405900040b114103d401c50b0740c00744500ca644400b41401c030b0340780603803050407084900c0005d00702110f8541130319080f81c3c9080b017021001e00310812190a090054690b0200f0120001d241c1440e15810002c0c01c2442a40c5654031a00700e840769150b45d6140c0c61104414100c94040d1100414003c003110020010000d61b041409400c2000e407801d00c81e005030b40c0084506484203140443c03242030000010012201c1e818070020340c2e8503841e03c1c640507a000100100e80c1441816002401511010340182c010f6125034004540110051806050760211000b03500c90391b850601c4c1c0c100c1000c4006400e10441c2e402c44204038058076407030401c03409010f041d41c850b0700b503110744022001c4507613101300c0c07200e0000815030907500e59584401d840d044d01c0c4100210b5070390000080c00181b00745020f0074060100b00c0c0c802820903200e40710b505a00c0305040a2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 802928947 1250 802927697 802927709
    0x1e030f0a170f060d060504030309050321240105031003150609050912030c1c0603081209010507020601180b041a040b030a0515220c15030515040c030603020406 70
    0x4600e02100304a400d40842500b0000070402d000b010b282080100304e0040e202c0c800904880d0f142c00c0810709050003684154252600241030701e079108079803106940016084848200910390800c00111003400b00410204110020261000e981904400448550304041d00400d185181d400000000980e00c545040038541c0c1c900011682c1480d0030b140c0c00454100a2600303071140c115500745000118110200d03640807031205582d94035a200c280c80c2c0ca424009911241400341c0c900203022007401001c5020f080b691520f0380d80c007402c5950702010170707081c2c031002d0318a400903034031282c010303c816044c0f00c0b0794407010040340c90f00040c1410180002419100010300a602c3e10901c2d1800d01c440381010b000304081040190010b02502100765515540c41c034102c0c6000003664120408030300e02d200040c40041c40300e1002c0013030224403400d50804030701c10440c511030780c0b6040e5a0161b92002545c081e008180c0714220100d07906148603001c00900010f00800d240100c00c042e40c4d10760201c01a511031143e0030203452 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 802930197 1250 802928947 802928957
    0x90b13170a03120c12020d0b041503120507032601061101060b04090515101214011212050d0e01060e06041419060312020a050615031e030f0a 62
    0x1140491220040c00c0d065095115504915169800300c1c0c0c00040b0708526044240002034440001d22088032105c460075040001c4d2400022808143c1080c1d800c0700e07034805003c40b0100060018000e00c0c0e500c840491000511a0a2101006100d2400b80f805000100d02038141600c1c640b001403441a44901402216004504400018405150301040c641c1140c540398008201007401c0492451181c02688a50800c0b25160030000c1da15a000400708064800b01401e40da0781003030500030203081c1030068459982114034106002d6565039440782c0320344c1220710064070a4070040954a694580a14907070080c8140001008a071074a818148031b111002c1d400840001011800c0444408041e64060041840746041003650103500e42c15500b07151b000101c81c1c5420302004025400d1801503d21988068004d91503070300d00000f000d402245c80280b4a116805032aa250b4420800311040203000038030302c2d01980503408146680c0a201c20080c0c0a4400c1030031641030400280c03074104154012602c1c040021 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 802931447 1250 802930197 802930199
    0x6031202100e100f0b060f0307030b040207151d06010602070f0b030108071215090b0604180b071206080604030306060212190f1701150e030f07030f03090b13 69
    0x3a410301c26460300e501c821105002000244014960f1a40744031120840503545045080c901d281030743c8030140708500070388002c1e10780003aa20980400d820072250b84000c2424075581211a10f858422940c800343d200c0700440c502c40500445100400c03820b190052008108103541901c41c1d01045110f00070f080702d60082200c83d00302040308a002003280e0203054942c00c180010312841001080050a8030070700320403450802c0450804d009205142c58107108a10b00d451521000d110314001c00c0b601c65581542d06206210b0b2004050004441050780507103a5074008011640700f40c4117203000307002219a0040032078115140c6148504100f0292011008665105401c000440d01440b1411650310240710450a01d500e11250071b110554810381c180c10098054283d00c040d600501401c0040808460b8005181da155040034140e40190380400d00440c254000303100c280c5c40e000403000c104089a1018200052542c0d846901e404d036050421014800b04c1d01c00440c0411041005d002c0814011640403016 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 802932697 1250 802931447 802931483
    0x50106021603020f06090102030d020f030402010e010e030c01080a0908030901090c06080c09150f310f0b160b070c020f0d05031206060f040803040f0e0f180a060603 72
    0x10000300078802041c5000d80c08101603034500825010b45078096030a241d4590101004038158400c0d0029240e2581c40070540c10203407591440030f184550b1003070721a07035042c00e03002c401903901d1071010460b2549937100608600346944210166030301301e01841c07030109120b441540d45d104260800c88010a42d41e54840040050008218420303004040e03905090f495810884501400c612440f010b0500803035100d401d200545041c0700407140e0051091a11584071405c46184000400d20300418010000411012299102c420841081140c801028074803c0b2071030003600203055003103003040d20860301c40040c130710307010034011080b0714480e403d81e5449a202034070030720400640d18503994500f40200072245084001078000000c55042268501002c440c5503541d82c0050064490200c25190400010400086101000010300300350740c5041140140c41780c540f40c00c020300840494280d10310f0918040451500320a1070116903144004000741c03025184140c807003000340c41380d550080310000110b100749924 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 802933947 1250 802932697 802932703
    0x5060a0c150203040804090b0d020d08120711030919120f1b0302010e09041103190b090c0a060c08271305070801090b0609030708010c080709030305030a09110a080105010602 76
    0x11403440c0740c0045040d8246500c400505010324000c55655650342c07100d0404640d110780654010f950b0080c0208c1c1c00942911f0420f0903a04051094242c4840e0000812443d0707020f5426075480d9900d102c029800c11651204004510070361400034200c60401c000081555215442e4240c0c28600803007403140074410728544040c01840d1041d030206a0041d000d07042c00141c1e80100e0710020300300115102c084546072400c00030100411903003410b034544207000070620522881c00b102c07030b1f8480c010040c3ca402a541c100c0302688a00051141652210f0303110802c0c0078107800380c0b240d184a00c0c081c1c07102c1401c0040d840102a05c1030f1860703102071aa201e004240a94510380700b0440b465102d58204107100e5410000c01c080c140c48018001c1c5944a80c49400801b0181c89003030030742d01845001021036400b6656545524020101002c1440000b009000001d00c0070340601c003070004403581503407603d296070744440d0030800030042070b0b20072900100c402c481c14003542c0e140c2c08080f0241480000003e1a540b62620181ca = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 802935197 1250 802933947 802933973
    0x9090c090312080106020c150c07060e01020d08040f0602030709120c0509090a030903081605030d0c09050603010602152d07021915111948060605060a0c 67
    0xc103c41c000052000550101d1165490703101174450080d21a490004000e00c1c1c00780c18400300c0e161003940b000041d56607000c030080c00403007802c0c1c086e140f6031f0b00780007400c4a107030303804582c040c01640c2c0000f41000029819401194000f089190881d085912501079601601540c00709803601c03888000c040c4994641001111f4000b242c40008011040c51540d010f0f0695043d444060900080410800b10343c0300494a0514419402010b49503650040b51070031000709040122200080c0410030003042605002d411a8142d070040e40081441103001801003034451000bc017000041032015820303814103000b4a10280e124142d440300d04d0300525000034001c3c1b900d4403141c0d80403c81070b2a00744540102d541c904040c021080307210b5022803213400740d081803891441403c00060307244002488020403541e01201002d0f291404500403040c40d00d01d40141903200c60000d034401b0071010300c900e00d00d00c0c0304200b9010025075403192001080306540d8100162081d04000d02400124a003203a0388030401441e4902c00b5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 802936447 1250 802935197 802935233
    0x40f05150c040503010c08060904021e060412110105122d07080f1005061e090603092107030e010e0a030203010f02041e0b04030221060103061b11120a09090c0903 71
    0x165023482c00c600002c40c0c04801400c0680140350384c4131103039004440044104c85107070002c3c2045944a54842c2c07040040c0141c08401d0320703034003415094500075601c610101c4580ca0100e5000c1d8040341c4802c035091491925160760364104044402605105688100341c8078841d4009848403815441c1c000046140064018240001e8481c4030f83c0c00d0001d41e9030391060740e1007020b01121456503405924070a80d0b592003100e4041f50b02506c00b108200c0c00352000151a42c0005107440d621034036440d0b030032500340280a80e540080101e4812000032035103501c10b50201d0142c41000741a07080d0f20b942c0b0b4000c2400c5500c41400300c1d2040f600041c05100300940c1c1c80c5e0051194a030282403504c03003480e050802c505802031f800001e1185550388030900c403903000c058003200c1030340c9040d00755021540c0d41d00c2c2c10401800d0b07030280c2d8074601c0b12100c1081506d6000b5584021101d9014014002c0202c29a10b082d240c3d5100464050034842000b0000c1381650481c400c5c40200b0b01503455004210b070442c00c0c00305182503401909 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 802937697 1250 802936447 802936457
    0x10b2511010e01090b03070f054609030f06090605070503060f0603011211060409150608070c020d020f030a0b04050106240e010c0f02060a080a060503070e040f05150c040503010c 78
    0x410102107090700706d80d0301c40114540302c4002880301c2400c440030b11440d0025200c4d56810015080023201000541202c0784c9a40d42042030042d81e003181c4d20300c40c5940c40c038640c04500300103c01c1021405001c54111001e10030b40001401403801d541e076104450742030300d4501c001500802040410b00300149a410181c1044a1543c2151b14082c01c44607402200c0c1e00040c007840c0307506100d080d241c48800c240c4001e0607011106011840016074207041921035840343c40300003544200420a4a8002d41003a59515006094908184c1440e000c4c440c1684666103030740d4151043c000140080390b28003e1040c0618410000881c407c0d02c1c00c2101c6800000d01c43d0800c09200404200c1c184650300416100e4885c078081c248050150071904003240c0d000c003400c0300650440800180914420b0340505007500c1500101000c0004039166428940e44401c1c0740107003801a4110000701d80880c7d0484040154184120203d0f924040e070801c1d13001c4e0901c81a510045c0785207000c0703024841c901c0c00303009005c08002c1e90701d09 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 802938947 1250 802937697 802937699
    0x30602031f0f03050c0409060b0d12140c1005100909240e06070305040c0b03040b07090f05010509040b0604150504031401022104021503150310020909010b2511010e0109 74
    0x21309500d600410b018075100310350303a864034070400407141c21940400708000c0503020501030605101c0c1400860300d9904000500c5c0c40c0c1482d141403120fa05840319246014000c0c610304440c411031000911000d41940d5000d0b000342c0300050200384600840441a104d14003402d40c000d40040c03042500016907044c00550350406e4030703100c041c40c00028020b80c0200d0a14010600d921542081d891006c841c1c1c10581e0180310000c2000140040310700b80b5070040050b81c2c0c40904031f650780c04100002d680140030322400140e00b007000034020b20745604030b21268103004009620f829035416a9000c1101c0010400011490101f410028000c01c11420000e01d40d0b0480207500e0001d202051410414400345440203240881d00410705540b00c3d15241080740c00c2c804c0c074880d520b0400c602c1007094901160300300703482413040480c82d40001d0054000d58004401c09088100947d080c9242c14605402c103941007159000514030076072000700c50500050580340100c00050403001c2c0d03d400188203080c83c4e6003880c184201c90300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 802940197 1250 802938947 802938953
    0x70c09021206060a052203110a0f142205040510021c0f020d0609150614030610021018021e0306042d050616080c07110a030602031f0f03 60
    0x9603100c2d808039100f070b55410722140103072403a0049a10f080d0100041040e12100501c241044a081c0c80c01040b5144190580808101c0555000d000c0c000000762081810007205280c4048000c1c488401800703140d4240314940c5c030460725518048031480550b01c1740140320038030000b400321120644a0090551806a0040000014580300c1c801260a2a62480b11004990b115410745419a0b1000c0040c040c2c50344d1101c940c4060310f40b5140d5004500c102420010b5200e00480c001d82d1214100e46140b4250355400d0b0030800c544060b80600c0d4154014a4000481412184221184800d076955110081101801030020000340c20314005015050701600518940d0700146040e070059024100301c059000300080418028424040306151420f803611840070014081101442040319900181212840c004c04403403600d0140c0e01450900700c108541008070728902c1d0925001e460107002e40502c80d550b992124220703030045172904603651a80a0039088440c11130800f41c01001d601954010140c1592 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 802941447 1250 802940197 802940227
    0x1218050a0b33011206052d011803061109030a050f0c1503040213180309050411031608040c1805060a05121905010f0e160e22030210060605070c0902 65
    0x2c10141c184408001940342d010780680041001c0d04001c0c2c00d40183c10b030340a652450400219012180c0c1c1d0403080c005c8411540304241d48500410380c0f540da803d00c2c600d035440305001030001c80c41c940400c034001c0001010b2a1010410400c446120780c0c001c140002440c032140c1e0078034142c0c0c86d40d13a01c80c00e10350928942005148095a0308640c04a403502e90000d902560f01c4003c00c01c640d0108004004400210207140d000641041142d6003500d01b4000459446425191403108980303000c0c4212007807014100880c440d105641d0310900c00c5c2070030b00703d02d500d5007420720103042007440c0d0040d61a2580c0030017140d81441891800146419541448001e06506106499010f4400314080d50640142c1001c01c0c0b140c01d4106426482452500308511006119400c3c1c4800c0c01303a04400c9a4484180000f8000341c810390101d00c9058010302801c1c00341021412040d8401d54003200343d00314440e010794102041160300c640f4004129680b180365445500c0e01e000d691750030b503d0313008400f81d13481800440d49601200d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 802942697 1250 802941447 802941541
    0x60d0230011e030308150a140405010902040b0403080a0c05100506130507090512010f050c070209090d05030a0c0e180703110f03041106040e190e0d1218050a0b 70
    0x608150403d581d41b280c02c490520303050a03400742d011104440c000fa48181220281e20074034001c2c0c406000b26a03c440e10b1205038401c5200309801c844040000b04013041d101b00161160502c036160080b0308d0b4010751a41860004981da446007450b03542e500740807007403400403404100507003e900306104a00d00f4440282505840e8820b141c06603c06540c1c3c6580c2800c00e50060910f5224014204042d00788040140c3c40c642000400b280503d0340580800c010200010f5902c40001c50342e41e5007451941c46500f072078081d1200c560440f09006413072040b0502940c0344800100380c00a04c0041c0c05441c540340800901b900c00c544580c419041e42000040c400a510200301c82e40280c0000007008143c82c1540401c00620960b40048c010901403030a000d103c10495040c1125461a20820720040b1a41152140c03a605022082c0c0085003092503450410a11504211003c01d0118051601507405803112401c1c0050541c0440340d0320162010807410004020070303016250b207568245030640702c0750482c2c040e9841c12 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 802943947 1250 802942697 802942703
    0x1005153c030a0501020d0c080601090b070825050a1b050904020925020c1f0c0b0a0f0c26040506010605030406020d0903020f0106091109060d0230011e03 67
    0x24140540605440401c40701182c01da20a000310750342d00300302c90319200030204a085100000c01c0b1001040c0250310481c0468151480c1d05001c0c0d15088007556035804651103042e00560303011480082605c9402c0501030708070107c0c0a20040c08034002140740c50400b10403552261700030b0040078801880161219000317140e205030705450060345600c813241020142c90111100d07200441c0d40c02107028242d90b02003900d0180d4841620b080640b86e204141c221100ca00d4011368030001143c107003003140403c0035103c0c05038014501c09000541c41d00003c2c0c00301e054800c0c3d010410301140e03264500045a211000c0c1c01003425549086601d17450a0941e10380ba04c4075418403d0508024022001c1028090036604031802d010650780200030103500e600e03010b034841c3c140000301c2016500e071030800110441680240e2280c40c020b054080d02c4c12980c20300304101500140f0080103050f50901c14846200940074224101682e01c0200e10842560b0305441c48180c801600503500c2d009201012500381075034446000d003501d82c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 802945197 1250 802943947 802944049
    0x3021612030309050f01150f09110a030b040f060906050a080c0a0b03040302071d0723040501030f060504241202100507020321220f050108040203100515 67
    0x521824424909117003546043d50035460b040400300240800566001100d071606044080c0540d11000316080b03802000070150303403140c01c2005507032051003540460800b00c8018000221010400a8417040ba00c81e42c201c00101039540c03505002a01d01609030074000e10a00005004010010780800d081b40c426110340108124080086070802d402480308030051f000c800d844c0b1810952540b00c002d488841a00c0c458007040034592183c4030f02a8290711a40207180c102800b07460a0b24250045000700460f03410800410b41e50b4401103150f50380c90050b10131110070440c902030100c054039501129204958814030001403d2131041005807228408070303c4e240c980e0300b401512005640082401e2140030401000e0741446c2c0f000201010a8039006840341c00c00380348003119044802c8000f107180c2d0465010300c0310141079402c0c080025620038568282d0080c030140c01d40d015045080c0c1490b003511415200514200a911940f8506040c0301207009050004d20180c030080d941c980e4580102400140140b0350551 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 802946447 1250 802945197 802945211
    0x6050105240d0c0c0b0903040501030e01020304020d02130f05010e04050106120308012321011b080f180303090304030b24041104170105100509070525061107030216120303 75
    0x14044e6401c00b25981c0c01441c15100d42c5000c110740e6859a02c64040c150210745001c02034104200c051081d01d00c215405440c1c4100082039400f0082071600c024102c00d00c4a42310003010a414002c5d01915000789641c038004500d80c1031030300c2c1060941e811500300041e0301c201c01890328042036006025a04542c55000a280d41103002c0c0341d84603040c110504c082e5000307000319004441031940c6982030496203289a000304030b1018460711400c00200f00200e140d00103600000803550307410b08007440340c1d08409100c00c3e11403c0401501d610b07046400845400003290804142002404090704e235480e80f112120100009200e50307070340e24000304070560500c81c0c0102d94602c519626240c01500300c0d4007621000300b801d802e004e4080035582c043c103402c4035015540d01903c140061035041880a10703000f01e603562100e90038150b4030040d20300d1340030300030888014003894640c4402c041403280c4a080c5005050243c100e035100c1c0503040192404418850400c00070307080d008d041000d0342d08816003c50081d40341c81c0100d115 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 802947697 1250 802946447 802946471
    0x60904051f090b2707120201050309071203050a030f15120302070306050c09030c040c0206040803101a0a1e3f05010807120209070305090f01060306050105240d 70
    0x28207107603100814005000050007204e440120030b6841311100c056050811018080c15141c84150301e224407540815008101c10041d8010009150301841034402c072420b00d13645049001c110100c4140c107401080c030005851035603d51500600020000203001404030b9040c080801819030140c0c45005481c0300501f107594201842400890001c64211318140414105001c2c4000c250b40450445482072003000d41020071810319000b44c04000d00740d600600a26611034580c3d102a5000178514240c3d01c6030400003041072a80c401e95903412580801200c0c4d01d881d07068101800100a4101c5094500c00d09170359500c0f681d6000c404506000d0940c034801942102501c1e2420200c50000c0e40301c5015603002103894400038260f48428121050750045072285982c50030642012011894043d410200003000203a002d8040e41041c2d8205e5200003c6405840c80c0c2c0d050103084620035001102c1d610707120001001540340c003c500c1c0c034500c1000207079042d0b40d0b500601e0944081c4030b20031000c03c81d9500d8298100c41 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 802948947 1250 802947697 802947701
    0x40f0219030b0d031407141e0106080303040b0903042403181104020a03021201090f230a150e0703050a050702030c0303160203040f090603061d0c01080603160914060904051f 76
    0x220590012864618440d41c9800c0350726095250500b06d0746103441180c02d000e41234140501001c9035100c81c040d42c82c580341c589440301c8200004061241d1440304101c00940c040700034415041c0c12524000c48441c0d1a603644005046e174010b145540d0258103000a10310100e45001c04010072520100ca0050342c510010006030043d000d80a240c201e48050345000007a6108260003914007200526420040c01115042d005801d1010341c4080d5801c07802040050080609039204010f40441c0f1158044080e07a00c1007001c82d1603400f2148100040e45030000c0c400c10601c140111900f2900600255042c505212541562400014600140c2c00760300f003604e4a8450080c006c540282861080d07a03000140c8075010030010301883d01c01200e100f071503c0d5124403522120380071285110380031009440940c0c81c2c0c1004448041010300500e80c54094800a518000c071b01d400309000a0202c82000302d03a400842c401e2407000c05005004502680340c9200700300c00241e009c1010840380121811003082d2940741c940b8180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 802950197 1250 802948947 802948957
    0xc1812070b030f070f020d1d04050a0b03060c030c22080f030a02060a09020604180f0f0902040e0d080f0c040803070c0509130302031c0b040f0219030b0d0314 69
    0x10540240c030004546440d101005521403000c8041e81240750302d5103642100c82181440d800710043c2c204050000c0d5151140040341d840c0780041c220344080c06c16132400182180c0d001c0d2442d20030303a07540c5c0488860724141070107a80d601c100001c40242c15031910802640041c840d802034030030030302e490b4000c4801d0242082580005021354000301c602c41420742c031b0016a00d50010b0019405131140700001101a2124002c8144155019101504241c0b804510000c007451001401c48100c2e1510b65080142a84d4400c900690407030400101b44007a060041c4000c03684411700034180c0b07130450b02050007410303004449280c101ca41150010340e16a1803101d8494640200e411181150000080c00c0060040d0f5105c05415104215200c03075140e1520303540d01c00089100440280503803c144038020700e08c0d68a60217980c03022000304020411140c100d0010b003c1b1103440030640a140d03404511040c54500d80f07904c2030300c0c0c00720606007009107503201d200103400b0001481c4010f0401c00c00c07800495100840d041030794 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 802951447 1250 802950197 802950229
    0x14040902030f06090a020111071a0319050a0209130b0609060304031101090c05010906050c2a120601080114190203060f060a090302152110031208010e010e0c18 70
    0x14140c1c10481e80294803000174000a030700248400c0041c604186000c2030b0b00b01201e0600b800c0224002c10032801c04402d0301b00030b01081c00e90700744d00e45d4041c07012518020345200f188210001680c0e14054010460001d61942c0025113041c54103c00072029102c50046600180d01103a4154803542c03640b808644000514600c0c0e0865402d00e0a2402009640b1b135615043c1d40c1d007600e6410040d51500e4003140c40c5d028500e0007813030590050b0411000b00703051000000b124450555485149110000403601d0103c130045219600e603c07101c010001c4407002e220f42d010500c1c807a4807258240c1803402103a045541d4201441c81c015a0000c081101555809040302604101a01d20f0b42c50304408840549030382440e1009901683c0e4074400700c940da4102c2000c0f60b503403550820a050901c3c0c40300300c0908981c42d00a02d4200502d0840c1000f102103100800d980302820001d42d91001d180d814154182e0b000c01069001c0416183c11a051020290080e016a00005001403200715165124400218803403506d1503a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 802952697 1250 802951447 802951453
    0x30c0e06182707080906040312062115060815060d0f15060b0f120c070b1801060501090f0608100b190e03031801270e070e0a14040902030f 61
    0x1854107031a500720410103103565519401240e483c01410360304c0c140100c0784003410b41c01c07000c0010006402107030002d85003600141e00040c0d880d190400c4021400d2994500010344068a0081c000c1042414060341e0054a089061100514000d40d003a0f4a00c501080c1480a080c003100084040e107540509001d42500000d01454005203406e0100741c20491442c00d11925061a0011411380e900f0700c2140d5a010700546940c3c640f0441c8040035214030005000300606c810300300890804500301c00c0246000e200b4120020503003001401c501400c4034150741c0414148140755000b003000d038561a1181d0111215810441d00c0b035a104051000e0070000ca40041851640100e034491010f0480d0380e004050140d181ca4803070800d41c8090801d80d030b034000c0b8240800c1680088030445110751080d00403413646180b4184100003d000340c4244a5460016080200307801543e008004800ba4130048220440505403000ca1150342000d101b12880c9150450f50713401280c581c034581c811510100310f4425010689015 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 802953947 1250 802952697 802952719
    0x1e09180d031b0c0201120905120d060e100f060503060121020a021203060a0501050702130501150f030e0705090c0408100209040e031201090f0e1506090106030c0e0618 73
    0x40d000b400c28403508051440007811500c0c0150094030700c42a0290161248485181e10b83d1081d0702808030fa40d02120240550003010340380c004000060200300500807004203a0314100150000f10f04001000480e0f140d04c1d02070b08001852078154014243c6140786852030340c9546400041e1280324808207554154110320160314110401a40903240c41031040c0c0c01d4a0000030354445030100b0740070540307203180d00c5040c4c14010000d41d8090401055003603c0a00805804001071000c00c007140d2003644004078401100c1111039402c0d03405110300b1041c1030a0b09082150600380154550f4800b401c0c001d0300d003c3c0685a01040b07035030200c18146c500800103d011a54040300c5040c065004c2c3d0040d1078043d0040f030a00007540c0c03075107401000341d6410f403c0f00881007141ea842c0c000d000c8007910784503140c5421031342d8540300312507054000c3c84256078141106030140c45500f06001070000950050384034208051401245036a0a0b51108040341c1103502110b40c1c1d61100c0703444080801c64083c2c0c0d020b150780030358000c1c9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 802955197 1250 802953947 802953973
    0x2090703090309062c0315090d1e021b1302130509100e0a0c14040603020a02060604150b073e030312040321020301080307020405061e0918 61
    0x1003845028801d0790f0f140402681c8900940300f03610242505045142c0205003014050486540e803020818004c0840e680c03c20450f000740c1c4824402c0d00c0500d1a40c100b00f02103081c65800014142c510108840c041081d5003001c54001d4542000101d603a00443c000d40d0502c8180e83c40d40d4082c03651440c1607800319a1042d05d5442501e4000007445031078000e11030f400000f09107180d46026a01110b00e6041e1209450b680c0700200c2c3c004246180c0c0703003414071904014240441c3d02202c00b40001e031843c1e8a006a07204500f440284c60010b008011300e00c258107054101c0e2000c0c1c0e01903000c1c001c40d07441e10203070341d02d0341da20340b50400305508540c400d854451080d4800822144652a8020080310205502c00c112040030051644a114420b5110f514402d4480860006072045581c101a0b01c400c0240702c0c41c800100708910166442a80036020507800844c203402545050300c1015003154044030f00c0c0071055014880440001d103840b680510424030300000425207201c07810085410100e21081d81c2d0000741e020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 802956447 1250 802955197 802955201
    0x1b090509130302120a0c0606090b041514010c02010324210809270708010611010e06011203090801230108030310091d0304091a060a0c0b1302090703 65
    0x11281921410048001c10400300c081e9905001d241e0305a409024282d1100605850382c0d402401601c00b0040c01340e80c07240110300c3c05e00c2624082c100c1c81c0d00105002030024104030640d6800b020030305003a180707074030100318440082d00c00f540003220038205444030320003c0c00140d008110790300070282026440c0c01071b030307500c1c420301d51449040d01e01e1200303446c1c940c0303807800c1d0721009480d09000c000b8454001000b4050042c504441c0d0345821924034074201340481d04095146215500941765030010401c240010300c541504403517070f10003110b103800080100d416101c1181c1d40e90603040c8507107003544042802550925110703902c01070180c5008002440580701c501e032a41d4080c0d40c0c11400a40c0e41c0c1840d000031459000100c100c80c02941319020154040d400d00c54540001d05000303410303055902c2c080c1401c0c0714410060019000504003954000781c8080700310b450580075003100081501c25402000100c0a0541004411403120381100c0c4100a0345e440d40c3e0352a12490f08040040c1d8407200d200c080206159142e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 802957697 1250 802956447 802956449
    0x90203060a0b0712030510120311060114010c060b0a08030c061f061d040f060602100c03150e0402040b06120a0c09050d200607030903060b010207031e05011b09 70
    0x296028040c05070b494000545500030080014105416181e088840300d00c43e03005503410446441100700390700d6462180d1207a40080ca10100c0110301c1e4080c50441c442010b0101a00500003420030f200301c1887c000000700303111130341b103001014903940b04840641a00c9580800e00501402c1e0704880e40c1d40c0307420030074079540c00c070442d500101c05c01c100102450f444005400002220041c1d00d6155a0b40c50300c589134034031910700c0e154260b0010f03510550448420800c4c09000003c0100303401812100b04401c0e07440d030564403c140e00070305060070020000b900e0003c4420210440d03070340b004540080e80780d5200040c00b034072059803581d5004c00082400c850b8001d0100549001d24030940f020440c0301c0040e481925504442d01c034881e803144100f00c4000100301e00f603500b110101c03211001811402007900c001307003494220380c000358005080a01c0901c10041284280400a04240010700146140d9901c801011078000504540304a540c0c6114007080000d4008040006000b16a2a545141548001c1030110a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 802958947 1250 802957697 802957699
    0x4170601030c0501050909180f1c09080d1407030e040204030809010806450f0105012604111c080d0c050f030c0a0c0b0c0304031103030717060d080409020306 69
    0x380080000f410342c040c0045038480c100184c604103031a41c8501079041c1c10440c030300c0640c00c2d40c0207032425000180020710100e0701c040d0704002d40e50300c03c02000d10020010f24141d0000209980603640c40c905098100320449154208042241d668508520382120245030781d003040c680250000c00c02108020394280a0048014283e0355001c1541c2c8a908100400200c4403600d00494140c2000e0000046c8065400c41c01501203c0d0552804821310804845d02000b25200c3c843d17070f140140148240d40c1d10210220b810220140704099076010001841d100020240c40246a2051403e1100711a21001400b1400c100191000d505003989030a00a01642c049450700300c0d00e500c0c000b02c0d039100501840584101041d82c3c9503103130442d940d005003480301d944401041e50901a1031a00030700000c0c0151103c510450350300881075100e040510300a84001c110054080c020740090003001400c0d4cd00c200d1165070012400306010f4151242c1c000304024a030403030001303040103400140220701e080306a0005c50007118 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 802960197 1250 802958947 802958963
    0xc0d0f06050a0c0e030d0e09070c1a0405010b0306070e060a11060a0f0c02031e0d0b1f02060609060105090d060e16031103010506090f1b072907020a170417060103 71
    0x154420030180c44404215628020482559250f0780700c0c01c1888c6280d038040014102502d01507000e8992290902402d01c10302c110081d060108010000c00307001c1c003d00344401ba0000c11550078540381c054100c002c3c016445000c1d0f01d01195402c990b6118058080780003800794190b03465418104d0412024101104e0030424841c00c240e85520020300c00011070721828000c09208903034142c980702400546e40300860184580c1e8960f020040b035641d411643c08aa6541d1008017222140c1a920203400d1a9000b40700500c10044c180810181c0d903005030842c0c4c0c501c0401c03030b0f894009c03400070b18103180201084035290801e40b15203211703898802e0002c10002d040d03a01031002d050851000030209826554100c85050b00304904a01041c14640c50301c2455401242c480008074014841a006528075001201c0568007000080300c0d49140e00902c449201020706200303825421031400c600041e5030360a44d0103006000d03001d500711200c03100c0400020b5502428100742028040e03945c004007295506003e01054034800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 802961447 1250 802960197 802960217
    0x12080603070b040e04050c041401032013020c16081e0d020d0c060209040c0305190902150706060806010305060f131a060d14011a01110c0d0f06050a0c 66
    0x3250008240c001c44882580c5249071504004403e0300b0000b000c1d000702c90510a003c4501c13410ba9136405041101201c036003504e5019803441c10030820240e0740000386220036003950358911280d211943c40c4210f01d6a220300141e62110002040783c54601310b58000ca00701104150080755850002c41e0350340300411440300ea1100d8120419009440d4a4500704400159200f006200941d074054071121416038060700c40181040003090118054a4800b01e0100019595000f00145680c081c0c01c14803500842d24400c02106e0016800304d09800054800300c2100358011828100b00000c50700100003900400382610301c9540e6901d00541d490318151501c1103183c178110001908802c2c2010700b40040745e0001180240322446203c84541094081c01c25600501503c990b280403444a0700380c4013003c0c50850000814080387e03109804090345449201d810051041d01c00150a0b90024040c43c0c2554101e8000b1305002691404150280b0303902c100501c02e03030812080141168030b85d03100300e6078070f142a19108640 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 802962697 1250 802961447 802961449
    0x2090f0a0509040b060a0b0313020a06050304050a03050f0906120a06050316050d08220603060503160b0307031d060106021b1e120a0f05070902070b0c07050a0f120806 73
    0x8095001c0c080d00074000d5000180440c1e040c01c01150070020103080c2d140c40589505140c0c030154000c4892035000080504040c08600b070841511300240406d250050039810560748039911181519000f504100020403500d00210b042402c4443c6271000401090b511405c0e40c01c04030700302e00c080f0f400803400c600d01100058141001300d200081034a40d0820b204083d410082004590040c80505958561040c44500d03031140b05d04a0500710b407442c81c070900011074a004001416100a5040070f40240c12601141e55402c41c000340010a450030304600c40e0302e0760f403042c400310001d1100c002069240010141c000305028000308403e41611810703400e450b51241e803c40c40d4054226105092030704038003458410b108280c60049003c000c0c000041800c0c00c946200030040c3d15000280703206070351541e28820740c001000760800001c4001d007400c1c601036050810640759100e06243c018403000c0807001c00034507001000380600c0360003065980204100750300d182d20b0808802e510600328914003c02c04400100c0c0503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 802963947 1250 802962697 802962709
    0x20c0f120f011e06290d0e0a060e0c0a0501200703230303040308040602033409300314120108010506040504050706140c1e0712050303010504021b0f0102090f 69
    0xa1791202c0e652400300b502e0f000340924148500b03c510307a2140700c090284242e0502e0500038880c481011200504540c500c03400c04038211140d1184004003a8840b180218490f203e444180d812107100b405c0130110b020f803144588000705440c1c10070107518080c8142c084104050b01c0900c603101c2c1c0a8140c04040d0b600d005900300e90302d20080d10081c0108000c2d800040004045800039540b104101c220400700c0002100c0c001d40448490b0100245807040341d856225696000071001c00900001080d07176070b0010702892081182d0090b0080b900603410703003409102418015401d40701c40c1f00a200c0074958401002c0c61310005000c0038050100c8650800b8081203c030700d0240103007802960044043d00609180a0058400300407400d0405056030091140c1c0e445040140616800851040e41091000004200e581d0900280b50050111b07004001000070120340000241c905503403041d100181c4c0c5100920701d412050780030706040d0101e413041018100c4031250640142c01c8410081da0240300e04e100d03c0c410014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 802965197 1250 802963947 802963949
    0x10203180a1128090c030b030105060603011715090c04061d0606130b070503030403180806010b0a03291e241201080f0d0c03020c0f120f011e06 63
    0x20242c486a1469680c90841c40001881c41d2114824148030002410100c4a010540c0014425651741a0320090541c142c000d8050b015400c90003001185070240015006001c180a07821a041104454492804042142020080840650410030b00d800d0001c2a41c61082100060242e401e0040016103105070f00c040c2c199008203d209685c0b280e40b40b80034417460341c1000900e04001c1e90083c0c000a10380c00c4402c0101000b50140000e540d90b032619017400340c042c03071002d205640581001c410402c45140701050480c15034001e48046983c036019408114040d1800019258144584460090003614000d0f4944200c8100703580c8900f901d43c05035070b40d003010904038a038650170150000030301d040d00300104201a240b511a100150511000c0064410380c07802c00d82062403150700c40c00085c0d40548040007010275180d0703940390041078000355640003500d688104070350300d0043c81d001e9101c00c4260784500010b030111444204980d09807400d0810b0b03070b01819203001141b000c5007660f202c0b203003600504e0080038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 802966447 1250 802965197 802965203
    0x1c0204150e0a090c0b0714011a101805060406030504050105060303090105120402061317010f05070923041b11031326011407030b04060f06050901090b0c010203180a 72
    0x81c03416940c84203032101502c00c8680c11a840000c2e11000300700d040c0100302034551540280951500c0d5902500800d0845011007003482812241d69100c00d00755440b110011600305545c43c01d034109850f0b03c40c540c3c0d100880c41d0400d41c0e000001040c00309a003645a4002803156000b10001d110079101d001c1415200c2c419527803003900099041000901c0d41031800880b44d0000d00c00752015150000c00c800c92102c00318150403044220100c4840010380f030800f401038003042e18907c00c040200e428041c40141c00d10109200d02e41e02c1c104041c80ca090260300c401c0607084c16110182080c042c100d0b2010440704d40c4060186082b012039026032031148902c20001c207840c49860250000f5030344a04101d65400c00d205080c40c0c448038a0302c00181c4c00c0d9402c1c800e00408540d0012880440100d0030004000b4007038941d42c049540c00381385410010801104100300ca441200c00900384240e6800350f180c0100c07040000d07034000394040c00000072001d00c0389205500440c810580c5e4100300b4500d070ba40709006034503103850314405 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 802967697 1250 802966447 802966469
    0x16050303040b1c06032105040605041401031b08091b092802070507061b02090606090402070804080a1b35010f05010f0503010c020a0b090307021c020415 67
    0xe0040d00007110081116141d0070006540b48082c030f00c150001c0c1c41c41030300101c82c00046402120b01031a4000301d44400d101039030070841c3c00c09040c10001042d40c000c0384940c40c03480d0780c0c04240d0703a4542d000382c1c41034020003141e2408488000c0c0c04440900180000d581c08a440c0c03203210040704003c5802c001d50f110685c0e009000c81c165440303660190300c0d102d2040d03540382c15000c00051000c0f101549031000f81304c0c06102e0700c09000440d14100000d0564040b0320081e10784510036030210001659010080d5071700c40f200b01d07806a15000c1480101e0002d0084980013072600100280105400700001940844141b103450700300140718000c00c602c1912245031183c0c0c00980e200700985800c068001100360080842030742c03042810490103100c81e0079100304152140c1c04503550801405070055021034840545025002401120305055009640c0c041c1c045018201c5107007200881e104810074003c0300e031440d400070134204072403070b4165800c1004003111600704d10031445c0440f008000c1c1da02030841030860f04d43c8061 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 802968947 1250 802967697 802967699
    0x130f0603021e1c1b08072112031a150408101b1b020603161d03030901140d0509031908150907090e090c040f0504050c060f04050a090507021605030304 66
    0x145007080248182d048031002c45680f805045004051042d800901c080381c0284882071506c04200c7c5005174500c25041003c00a81e85100441e603152007030b00da080e0842c90300180e0400d1070340c00300c41000c1d03c841c0340036803140d1028802148003007090081c00990b10113009503400c00300240d034804c0c02c5034200d00d15250100700440303001c00414003a40806100c00c080b1106c40c4241d10b810381c000346040d402200e0005400500c500c08a445990150102980210340c0024504440031040040e03624003a01c00040d042000840040911200000580348047e0342980140014100a00444e481381c003d04495003110441c1c0707892110240c400c5082d00d00400d044108042a80541c0041c4107050400514440500c0321030400010f0b1041c40040c3c05204c0c500c090041c01e1500e0b4990108000e4a03000071404000350f09010a101c080b81011030402c803489811110103a650003140400b034a1805954010307684a940c0920001c0d25500715044548901c0580d8240d0b0b011880b01c0f6000300054455000700c903099441400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 802970197 1250 802968947 802968979
    0x29131a0c1603020a1502190b0901200f0904020d020406020c01020d1430010905060a060309110d14071203080f04030c03031a0d11010816020c0609130f0603021e 70
    0x203a08800301005c0e00c1501d03d103003600910704c0e00b41e42c40c4c2d450840d000d4003043d041000740c02d0284241c6480744110741460184441d062030103030301402703146103030003c4c42400203000895a58650440f94411204030095455503030382c201c0a91a56450140d0901500603034845119a510504030f10f460711380741081f45400e02030811403159200c440541207040c08400d43c3c08401c203900c41d414003103000300708240000c9210b281c85018411416021344c422030600d4203246114001562031103008041d04016920030049599909000d900c0c50f82000744610a4003c060012403154104086200031038004c4c0c44503442921040726502100c3c00844024000410741c210680c0040d200340c116031404140414160007040c241000614402031030701080b98050b46038114900030356003128050f40c0c4261400800340c446450351802946800c02950b0880c418040055146403950310b4021041c00e0489509040000c1c01041c00c0c494010700c50fa010991054203640c3c042881c2c041810032161801901510100340c40c41503203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 802971447 1250 802970197 802970219
    0x1306090609060f05040b030a1d030a020a0f02030a0213020a031109180a02211815011502031b060601020c03070518062707030629131a0c1603020a 64
    0xa60748404c110b000c020005420254802035401803415540004402c00300b080a00e40005110b4081c0c0e0807600b061015403125a000308000541a4011441c54030342c80d00e5100080c02e00000060081d405400880f01104000e010342c007400c4000c949440030488103501c04415542c0d40180e40707001ea808411541e00c4040102001880c0340c1164540c28050705180b150a00040034940c51100f90820311071580070000311040c64020000c000c1500c00180071015500340d1220701200050143c6020100010304130f102c4244200103c40188045210018100c58003000b281d0300c500302603a07524014442e11007165400d150102d035500c11114000c003200800c01e002407000c0040d86004020b81d0f8010342e4001d40c4005940760000d030f001c21200001c504d004500d0701401c0501180c00c03940110b404080410485045840041c0d81c03169141542c08545071548008402c101c070100203600030070020041c42524642c2c0d0302c03082c00502a4500c25a080d0350780782d003400318007452000c682d2001a40c860701c18801008903039010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 802972697 1250 802971447 802971467
    0x11090a03060c0c0804061112071e1103011a090f01180b030a0f06050402091605120903190503060406080309030703060b012a11010e0114090a05030601080102130609060906 75
    0x40c0c141403078a03082d80e0325164860342080e806500422807461a5541e004414020403d007060b480234030608100a640f24008200410103400c00e040c080000c10364140b000c4804040c54401c03005009001c0030b00c1c0700b05a074013030380b101c1081280114103080c081940c641d14bd07441581a550b4014201030a01041e210b280003409601e003501e41c1600401c1c44101c0805d0416851901460080c82d0118103410700d8410f02408110060100d000c0c0d001c0382d400c06501070791003400c480903540d2448000c020341d2200326905045114451a81180010030310b105013105401601035482800220f40420043d503481c100e4640342c2c0300310a10b01d649078001762001e10001c3d82e40e62018140200600d02180101200d01c840640c1550004881e00064501441e0500300103801c1080b0958007800e1a00d40045020360f00080c1c05154920100c08880c035001c1440e24145d121013800c0401800001d0841c1c175039580d41c02d01d00b4001c1d44410722200400200900104945000e4988401103c4465440100d0b031454a10201c0741c090107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 802973947 1250 802972697 802972721
    0x7020a02150c030d0203072a03030c0516141b0f131d0102130f051305060415032103090302030a0804060209091905070206060f1201020c06070f0311090a0306 69
    0x144010081850300300061300441802e1030300140c0e2400d0200780a0008400060102a4901d40d1003441d0751180300c0c1c0c22004807030303541030502087d503101c1d20105443d0741c020b4030010440c0c011380090f09818040010001c4000c20103070815074100024000c80c40d07100b00700c285a81074000701e0040d0f01d146c0b241868400ca4007440703030000e40001c146074582c200580c55000523401e45110381d00414150101f00c00000d00304020701038400040441494000412241d03020346441a0081d541c4100040c100c0e01e5030f420949944144d10303440b40010340c59180c0b88058503009035104c082c0555820040c9682c9000b0301c07038081200d0305a0011030420706940b40440c1d1024009000311801a000e10400c080d0380c5a0748a0b041c05444011400182d2840c204012001c4a1300140381c4803c40d0710020070f00c40c440d01c2c0e6140103650140291210080c50074249015400391051000c2c220580c812030381000090b691080a0401c107038015a030503c015029014481501d0043d1240179a0062a0007020000207029502285141c45 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 802975197 1250 802973947 802973989
    0xb06190c0c0f08072105010c0c1520090112151a04030b010b03071e050d0c0305241503070e0a06080103080d09140706021e010501150507020a120f060c02010507020a02 73
    0x2980c1da507001e095800801003072300841c048440400c10400c0002010700c4580d40450104412080d4010340301d8450b4074203440e080040c2c000240300c00183d11071103600c0e0401003400c406103c440d100e08801001d1303290b5841a100158a5910210300d0111180115012a604141d2000c090390802d050340500d5030019210f2400d0220380e209981303c0c06001d14044201604030349036107440e500c1045030542520000f801c0c034000c1614282c20003a001c0101144442642c84c0d0013880304501ca0404c021403138003107a83c2170f400740d00100801040307a42a0700c00d884681070341080c2c8002c01c1d12585c4003c04c2c0d0f4804820300001304081810700c000d14040117140c2c401000180079078505482041d0405e019170400b0a1501708a00513085512410402400d440c0d401c4416402d0200800866240402d001ca580c0c07413160058007004400524002035507612403944020700304201820f2600789841c54035005c0700352085811201c060610680b141203d0043c400d2a200780c1d900d8004c0c1184021130303420403000c0c101034074481000d04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 802976447 1250 802975197 802975259
    0x20c04090804060315080f0601060f1e050c100501090b01030b09070512040602160f140d0c20100e090a0b06090d060f0e030c011b120b06190c0c0f0807 66
    0x2410021036844900c400d015008c2d550424200502e031400c078801c0f103c02e1018003106003c0600b600a00ea20011005251880d1228004000c10b4104081d4450b0f0f550311a007803000104c1c01c500698803c41000741d003600d040001403035032810700405c42401c0b04e44202041050055100001e90142c0c141e6100740300725801803400c402c030400c409000c9a0400e050304c0380008040c3d0401040420f61281c1b107603500b220024810034840c00b1b002400740c003c144000305030303080c0c004210410000e48640f0407900f040041500005200c2c092006083c100304040041c071034040c600204458680c503201c2c0f24032101000e440681340621510901c5209820402c0846040c4e503202c49604510f02503200b1045508103001c0030355903850082030314070b00750ad021481145108008500c40041e2603009040d00d01340405082001c20402040c174005030b440c0c0101d00b002c059442281c06c0c01527825a21141c01d15426100c3c44003254869101d40b0302c00c2000c08580a0740b040b0354030a000a001c80d12038800040d000d00c0070502414400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 802977697 1250 802976447 802976459
    0xd031e06120204060519050105070c030212030a140a0f1805060f04080606041b2709020703031a03031b0a2a0e090a0210110703080a020c04090804060315 67
    0xc6155a1003909500d0100281c0c104500c2c1900500d4020304044604088691100000b5040007031548a02810f002d40041c0080400001400380801140c0050070801c203a016000100d07141e03445242c030080040c114010040496411000761000e9043d143d44100e5118000c110644601644440c200303070240c8000d0b4002000c0c0e0300c280081000100084d803868132240f40582d420301c1e1070009051180304504001e8003030080d090910b040c13510700d031192a007a03000d0000f080380d0300d21059403982611400e090f501c1004c110822286c0051030b5891003990f04100400c8003c1c00030040b501c00b034074860340c0b5030402c001c0d08100b50002c0c2c4844682051000c20385d2a8031803150b803040e12031200350035540818441c00c10200204112951120003d0103880341c0d4a0701d615121000544614000c1c5000340329038001d182d80241a403194140c6492101c0301c00440e62115101e0400c40010740040c446d01005128107160040c450905000b11000164007490b440d00781410008280d01074501d0102003040f07907610301000200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 802978947 1250 802977697 802977701
    0xc1c0210050c090a08010e0c040504021207030605160314010501110f0304090b0102070803041a1303060207060504050f1207170c030406030f0f111c02090406030b0105030d09080d031e 80
    0x82c8500c0c2c0c072038554a10f0b02505120080c8065030003961180d14014514507000004039400314080022240050155070b148001500c80b0390f00003840c0e01318072410030044100000c1d544494082e103e00c1e040d640200c40861800c42c01e648201c000e40021180e0040100724650140303503490403100700c0c40240e5400d20b800e41c1e0341c3d0b85560040c1e8855480c0310744a00c001d1800b5601488940c0140980402a503c3c2c00e0600207101c41e042c1d1300518110f0b07088000500342c100382c2c141081e4a070166511940a641e501001c1c123051000d010162015036480c0030710613000b6545100003900b6104610043d11440c02c0581c151030302c1d1402c003510f4201c0c2410407020054864448024030061014000d5034900285440d51542d11000700c591845902d04a185841406c8000c82c3d0b030307a020707610510304402c1c00b04540b034401c1b0021406402403020301c68100341007000c0070041140d50803129040e95015401c03214244240c0108541201e910303c201811600070359642800c0360301c6600030070350b00b09210f0b200d00b20340c004488003602 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 802980197 1250 802978947 802978951
    0x605040e1c0e1c140d02120a03021309020702152b15180b030d090504020309100e0a1a0f0106111903030614122a04090f050d050c1c021005 61
    0x5034030240d8440000402c13003400038031682501c402c40200303d1080b803a039000e551442e5100504e041030b10b012501a5041d8480e8040318030300300c913040040510340d6032903141501a40114108910441441c203602c8084100482641c06800e042440042e409a8406a003891a50b002000d510120744880c0c0c1c000c13078035000070300f00b1000705955030040c0d8504e2404142e42e0110ba0340703080440d100c4d420200300301d05250790008918040c0c5100b16001603a03615103030031803441c00c100c0700c1d000003007030b0f081450b5020302180c013198035030b000c0340a00001e1900d141c82104021b02076030b045030100c0c1000c5041c2d0040c00700303034800c160b00c400000c04001103900c00c29108610151000004d00c040740007984424051007186d41c000c000700382448050f84d191000d800d025000381d072a6800404d0b2080d410845000c2d0391740f00e106012009004890151007044940c07050300700810a4103200030159030501c0303082c0300d00c056584210112005800d0782005403000b0700c032500e40c031107642621540000c11031044c0da200907880801ca03ca118 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 802981447 1250 802980197 802980229
    0x2060405011d040e0d122c010209040f0b0a090b060706021308010e07030c060e09070807022404020906010c050a0f060e100903020c040608060a0b0111061501030605040e1c0e 76
    0x140c0203450740c400038000a090b036181001c40c0e00381461f168996400594a046d501e42402c11a80c2024104000a009014142c20140d115081045070b07200b020050303002407407118064a8111a0756200d10340c0200b90361003003500a4000c14100010804901c031079001c0d1103154080c1c02420845961441018251252900e0514003034110034400c10030003108000180081c4150b04000c5410700300e0900249120342c2c0102800c0c00d02620740000b8100e140b091180d0304607841d030100ea03a5452074604000c0c075a1100229801c90240300c541020a043c1e40c0219850856158880010711030320125a4594021401c111030480d030440d150340340300d02820300c04d00c0015401d840c3c0c910005103581e01814020300d800380c4a030030701d8015407a002c8240a400c00115000f40d020707523448800320b006c04a4600480e62604880103c807024002d80040c00202c2000c03040e03103a49818260fa0030701100b619502004102d440b1011500041c0d07102030b603070408901340b0780003003100d075402c501300002d106051078049917040002400c04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 802982697 1250 802981447 802981453
    0x8090a0b09040501050117061207081218030604051209030c043e2b0204030510050702010b010c110103090501020c2a09283602060405011d040e 63
    0x6090302d0a01e44980c1d40101006d10f040740508210380c0d1030303005005001c0c10301c0e4003070305083e08061200d039000c00001d40142074410032101c1258141c4620f10b6a504028070b42e40d1060305403145030815150015045002d02e400001038042c1c640c16030041007450388089403041e0140250303031040046541c1c5200c1e42005110540c5510101c074682001410b980f81000e0f42540811815130581c0c1000b0928815111040745060b00d034020104119842801c0040c004200704515000260101c204400480c3c01140c030800300e2401c1c405500c86013400c0c0d013a5120886c0050008140400841c00310306510071208030390406040003e182c41440d260242079034081e01400d4201c0d071161004071084032040c1a0000d000d10891081e8085801203c0086c035158009801c0b0095250343ca41d0100d5058035180300d104c201041060b003001035692810131000c0c0c00c5c5510708640041600c483c40d02d51055840440c100702e05038020155440d142c103000041d04c40c03c2282074040800c0c400e881d00419030741c842c1d12403040e0401e0943d0003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 802983947 1250 802982697 802982707
    0xa1d03030a0306090e160b18041802120a2f130219051306051b01090f03090b0a090603050709080a0b0a1112070c15050f06090c1303020d08090a0b 64
    0x203400d41e140b40240702050303440300c2c071040080c004070094001501d11041031159540680c001880c8c1840c44200318552041c42c05614602c201c009144900c0111710a4641a4090101450041c0c9449420b1000b61480301c040002c1d0b0542c40d00c4403014040c00841001d003501c001c8200d00480d0240704056164580907038001204294684a1811414080954a000e900c0c0031200d0f1002562060365105940078004041a4a521540304a070610344141900008004203c580d003060707450402c4590050300801c407142000b080035007403241100e401c50000d0300e440411030318084045000b040020078402c100700c1046c5020500800a002c3c0040f014040c17400c40b01e09081c0180b0304802c88001074000c034000e138401c014844a121441117000d40c0620981054442c00c2c08506208204204c1c4e103000c003480b01d00d00350170015030310500714000d4000c0e41d00361004111541c607440301c42c12038821b010340200d48141c014420001440e00b6106414107600c00c05c0c080b0b04051845001ca0080d0291341c00c82a0f003c80c2c04a4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 802985197 1250 802983947 802983959
    0x15030903020c040207020a0e270703020901050f03060f1f0305150603070e07180506030f07020114011211061e04060215060d060203040f080c01021b070602030a1d03030a0306 76
    0x310182c039808850840c0b030440320368001400041c1903c030b040b20062956001a94841c11003040500c00500c83c28151030030f2081258554403400c450008912400f603090020885040003002d50303484c5000603000702820b4480d0001d0103c07102c40107180b00040016100c203001031170082840407009511030f000800c0c04141003002c00881700002070030341e8000d50200c18100958101c0361895508100a41080b0fa0080ca915001d440100e40a400c21a0001000014005100c11502210744501000c0e402000780f0408041a54449482840b40d007100034070740c18001c030100304403c452100c11840205030505d440c0070f03154192501d441001c3e00d804001d901041c1003010720740612000801d4606071607041580d241020004000441e8040d01500c2903031f01000113410054204405d41e08280c001c0c904944074100300700c0050103544031030b00403a07061054040d00780400b200003400c402514941c1c0c000d9414100254001c46182440580c1c490360020700d201c2c2c040c40e0391000d00c000d0409034910741c0e010803c542406 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 802986447 1250 802985197 802985203
    0x7050a05300307020703200a06051206190504020a1115040212010e0303010b0d0b0a081f0513170409090b07032405060c07090f090c060203031308090103061503090302 73
    0x10001c45040030030070410075590124a42082e2a4004510044411915091101d10800c001c1c159008080060003142d940e80003400f030b00c0f10f0510003072614410398030300003031100c4082c1c1b46592041444920741c0c00c1c0b15604d4941c0203015489618030f400d500100c000000359180c002080354111403035201506101c29400d011081d410850300c180000c0c807030703064134400d210f55074403051250401e00c6001090703c3c410b07d040c0d03802c0b07044203d47c0244000041a100e000c0d0b02d0702e840525603498241d010803000c0003004c4200b809020b03c110a00b1404914003000340e00c0d80c136442ca14800181111510820010948500a00c541c001060081400c0e031a6441c00f82d60250484805549090151149808103480c04c00c0714082ca01c103880b0241c49480c0c450109400035450040325402201269003401e2200400e08010f030f1090315524010030518507110794801c030a030788902c8150742d01ca80b21046043c8030303400310710003d0042c420034006240c0011520b59a0f805071440c044c030b0916800c0083d48490f041e0f03003416810 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 802987697 1250 802986447 802986523
    0x2130f08010e060f041106040e0a060906080f03040e0705090a030623130201111c0327030f0509030a0f1a09010507050702150919150206150607050a05 66
    0x90300081c0001c1c00c00d184031000c000740c01400100501c0e4406020041e1f07480e4002500c0c001c1c074014118034024284030041d440a40320901800380700b10b160500006802c00700280b02c00303900c81c240d0b0155281c03505041704040802c40082601042c04001c003c50b40d8207441d20510340006501490000034505e00041300319140b01d003072404075192007420105000f44061042400c0c241c2030b909080100c551100010340d6401d20408009000b4100030306030b100b5043c00c0d0960415001120401c030b070619904466628400848050034019002030541c0c3c0310902124007400040c095020000c0c00c03200d10011640da4240c050003d030000701c50313041c80104021050b402c02c2c90301c5600080c14100a011504d40704200910a00458501a00c0b0301c81c60b1136100d02c003541110848480d107002038205542d882070444120b0b0010040c0c0b00b03814078007884d9003c207040584049100d50098422025200040c1011070800009401101e01521980202c400040004d00200070500d80001c11050ba04082c250040d000d02c0e9134141 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 802988947 1250 802987697 802987721
    0x10020a060c031e0903030b0604081f020703021207030201090b0103082101140f040603020a08030403020901060e090a1a100801140102013e03040f1e200402130f0801 72
    0x1890140f02c0b44400740c064401d03e0000300c003800654104030f820100c1c080c001c82080d0681010001502103000000440d180f90030611034600c6500081000c0b1003801240b207414406001038000d803280740c42070400c10300100b0849010b44000304071480300b80c58511540300700386d01c1196880c0001030b0301f0300c0380d5041000413444540407501c1c0446030361511810003000c1c1480e01c186c5100f032241034001c203c0c6603110342c4184c000d1a0003a0031000201d450750b003100d669034014081a8814800807000107806071150042d40c031003ca015000000c01d0716440100400740c2521700010003120003264542090b0780300c0843c28003c410030b903940c04265500d012005952501d10718612811641081c1c2c2000c0c2ca500204031141000f80380200b614800b081003944285112101e070070300010740360b00000380010300000b010703007440c90307802140c240049000c02c480d1070400c4100000010080c034003d1003034000b90344855140140321a4054005440c04580403034a0313000d511a45c00050009641171820b00198809109061705820 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 802990197 1250 802988947 802988951
    0x71703060a150f2708010b0f0907021207060615031d071d0a14010306021201050d050d270602030d0501090209060f0a121a12120714010b10020a060c03 66
    0x1034800c00201481c09800c0b1040074444890094801e451000601084040322402d0020400380c90340174603400781044036000741c814681c50303071111260311b072159000303004000a400900d108502e16400c00010b422010341914070035694200000e420031409042c603582100b40e64002180035521000c141341d41443e040c608420f502c803020920104449407405010220700c1401e840e420f07540c001c0100080c1c45070b1b00d10343d48d1904100d40000308110003a0050b0030454200c00e824100340e0388410a05c2880c009882e00600300d58491010217070f1f80c80c0500211041000070180304104400c1c04104040040740c0703030f4446c41c01a0b00004064100f0455445080d01401c1c01c000305514000c503940015034140910012820032420004080000c90302802d403090075407640000a100140401c032114048040980742140140000d0000e261035074030202b600c440c5600c01540260601c62252142c40d1117203400d910003501d40d942c1e0342c1c44c90a103584200d181c52100503540d00034100120035290010958031050301c080c0501d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 802991447 1250 802990197 802990229
    0x308090f121c0216060b041e0903020a2301050a0b0603061002010e06010b030402030c0d05031c1d0d0f050301080c010302072a090b03030304080403060b06071703060a 73
    0x1080031440440707603012488040d403240701c800861545000c18a0340b40089520000d03c04800c0440b00c00c0c241c3c02c46000b4113040000704010002d200545103038603200116440450300c4805541c141e98009001240284110f0391301070803d50f6103076100740d55085070300071a107200400740c29038580c24003600e070b4010605042480211205000715030030340800745c001031045e003031022548141c81c400d40c4011404c0b86294125065540c1d510750042d0f09a1040e10164000d0003080c4200c8000c3c00e2080d20703000b1550303004c0000d41c6482c8180c500c46114014081c041c00c090760b143d60041095810250403500241e00b460042c2602a50851014080780d1002c0f551a040c000c003031004001880022486201106081c00c01591303d00e26403a080c46001c12400c514800500d10300c40404005902d0142c08003035411500c020412a007240c2c0400d581c90000f01d50040c01c61108000c141f001500503004410081009000281084400c0d503680105003010108400c3c52200401004807620301003580000038031044020f10030345 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 802992697 1250 802991447 802991473
    0x30d0503010512070f031e12031b02030915030a090b0a1508070e0a11091903030806150304330525050d0c3b010302040f09090204020d1404030809 64
    0xc8405d502c070151030148a001d00f810700b94080030500018540c45800300044c804055005001010101002c0b03660191404004c9040c5000000712444080000c0c40341000c85004190308030380b03034001084014002d403241903110001e502d500c400c80c01203480d0407012901807010440302a0655042c0c0c4401e8581d4400e02013040b00703845001046801c5642440045500f034030540045256100f0000c40c59080246244a40000741400c0480c500384d0780302e0b9540c00f03d540c40300c0041001c100720032000340d02ea02d08200041000107216070000d16156000c603e6200c592042540c149041031800e25859484035280d01c00c108508410170000e07200f202d040c4000c00b41888000780002d00074024502c4034482c082d6500280b192090207881c03d00d01c1c942031601a0007041c104030301c1c2c07102c10300c074154044104540e100003d00c1c0d00c0d40c004c0c000e9400ba218010342000c5030610700550300c1c0203002a51001d0380c03c650700300140803403550b442c02100c9100d00c00103084d94490034646001405004028640c0700e460300440600044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 802993947 1250 802992697 802992719
    0x2041706190903030605120d17010b090f0a05182203050906070203070f08010e161203051e03010e0405060f0405060105011d0303040801061e0e0a0c0509030d050301051207 75
    0x1c045000980010680c0642c034040e0014190354118951102885402c5008030b100091700d03046102c2c2c2d6560340d4851f0f503140034040e51200e2003800303540a0100c041c80000318509044420f095804001031501c1d151a503a400070541e07160000850b080650b0381c0e103080000100c3c004484640d41d0860f10704c403031148402624024010700501c01d02500c0303103500150100c03c0d9902080b5400180002c016141805540c407262607009003030b4005095058080d843d51411150030720101e010440d0690400100c044030141d80417206580b100056500504140d804504203024900165018144081e45e0b00c00300e04103410114030b01030004040d04420000e031010400041d1000c214181180c03000c0c00c0880c07402e84003401d0740905414083c2da494261102250001e24034034150407205c101d0b800c2424019440078182c02d0400350980500904810305068800b165080305154481005801c06d4a0b0050400c644100001c0c01d10140880c1e01d000504080014009031038661701104094081d2002812a28600003090207 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 802995197 1250 802993947 802993981
    0xf0608060108130203100f0506040f0e07050105031b041d0c0328020403050a06060e01050102390316030501060906030f1106160b010f0b0715090201030f0e0102041706 73
    0x6465a03d00095004549042002040c510101441400800e000e138000000504045803070510403801d1403003200e800c0c0705c1c80c424448480b00d080050715200342018015100780c0d0000d01100a17901c8a400e080e0b40010704030001d0800b84c515042022418880e4104085050300068801c0c0140e07002001441121441104c48240701000d440108020148800b08200240135590002d06180510351a80b0108140c55100788142e405450380480c10ba42c0b070b10012690f41c1f0b038200b100580c4400130440c1a518040c50303481d019000400100142c4000700e4007011904260099040300411144031b1810300811030280104070241c0b40414017000300a00d10f86078225104100f140242c000305140d2003480d040d49940e01120350401c0c040400c04146501d600c0d120039011001d01c02d44100340d103000b101207502c40da08030485603003a03002281c81d4030f030982d00c140000082c0076800c000c82c10f1650719071106031800150702a5240000b02900010b8445103400303401c081d0001044d12402d07a540052041144007142040010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 802996447 1250 802995197 802995211
    0xf0c09060e1302040608031c200a0c05120c010509010b100c0821130c1401050a1b02090114090a02040518040f0219031a090c010f050d0f05010f0608060108 68
    0x407121a0340c1c00420010100c0740c205150a0100240c4408d505a10b1402c9143e0044c03104030400c115803100a040c5e1050340140180300802204000584883c3d1040c07404040341406081a6040c1c182541c0c211a144c3d8031a2a03582d000c0d9440d001002030726442840355229081d01070300c2c1000340e098004002040b0110508004080c00300120303004192038001d800082c080c41c00040c13001c40328241603079004025035448078200e4052101e0080821031001940c42c107031550b141a11a9030802005030310554400380b50050030240c0380807560001c80540d030748080d1107009045020a845240c8aa20f00f8001018801007500099034010041042540ca855040303080341a1040fa541056032034601d0702c0c50303845450300c101075404004c0f40c10751034025081984035811a40b0a01800545c0c3e59021000300d43d401d021200004240c0014426010301c0d4050540f01d03000b4460340c81d00c507240024800120341156a500d590f4044990384178010300516005560a00280045080c03c9000d031400500090407064028850 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 802997697 1250 802996447 802996471
    0xf09021806090c0a1817060a0b1c0809130b030d260910090534050420180102070503070e07120f0207060b1c08070206070317040f0c09060e 61
    0xda22101c2c440c0301600c1402c0c419a080010741541c5403460554010304d050031007200c7c015207001c41d414600c1c2d4403c034006a50b0180690202400030180d0100391a640c5a042c0c4402d2410000d031038071a0b0358520890111498844001131300c01c0044249441e0020240032903040c04080610085511000e42641c0c4940b0300d07520011000b0740c2c4a8407a9030030140d0b040017101d9058100014101041004500000d54054041200540301c0494091942c2c0620a1704440382e01000c00c4030a0142d4181500321600300412900a103610000d408902e41c203079404610701074011058007a141304a50790501c007c2d4010041140140131903414512080d00400010700428103109011540003002d54058002c5480110b0ba41400c640340c0146042c0440548a4a406940f140580c29040c441809503200d043d41d6030b9400000c29820130401c1c1d8280001548004815803e0108598401840c42c4d80c604100b031080c0d00c200303010030002e00e99141c000f882440e0350f0040004507040c800144103440c02c462032a64048089000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 802998947 1250 802997697 802997707
    0xc02060a0c020f030a090315110702090405012004053a020f040f14010504020a02030403060513080a020f120909070e120601060315091b080c0405040f09021806090c 72
    0x682c0f8012800561900c1400080382c000c2449422101d1441240d02410101101600ca17410f40c0c001c590790703038010400882042c84081c0c05420301e10041588030344684000141038290030901d0101111400a007000b0100016051040e0300b4184d0f011200f00050ec031014480c14000c05400004c0f0708a03004280c0b41106d40c0702c05c1c100350760310300030992440400604104003400c4c1a0740410301900c01c140050300c3e1007900100004860030b00d8400c6410300350f1590b026605041c01c569070741d0058a000381000700714405c00d1150401147c4d503840280400d4485030010701c0d0035006201e89508200c800c40c01100032440500c003103903980e110140f009500252385e240000c0911603900000380c040715159240388251150b0000854000d0301680301c0b0400e40c0c2c18007500c004480c0d4542c0200203940e5050400884180c0140c0c10700110760003450000e411000010240b81003c2e00d80b00400c0c00c541c084601d05085586038801036056041c9100740c07a81c03400425404e511149498400700300043e0000e4807c0740c1507000020 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 803000197 1250 802998947 802998971
    0x90b010c15110703050903061e1501020c120c0310020c0309012a2303030103150c1b060c110f0d1d090c0c16060c0206090f090a09060c030c02060a 64
    0x7100b060710842074000240c99034540d0600501582002040501034400c1c00e000c40d070350f00380c400e01b0700d80e50880d200e541521554880600c1ca20030b031602002c85066214015440c1a42d030340e0002100d10b46440480181803100f2490105481c022420f40704108080c410491818803520100495480003000c1c2840404d12080c1100c10024202228550300d040d000400c039070ac10010540103400c4105108500007185141d48080262a8402807100521000c0120b060803c40d41c07040c0c02007207550403141007d002c022902d0148446000c0d01d039100b04c4d661030f980c1030301e111401d0704035090311034400d40007004001c007812502119079540010006902804080e10084500b60004091000643c00c080c124000070b050517042c46100d0b0308100c2c1c1c4009940940814098665400703202201101c90b540d4600d20320303014540901c00e19600c4001d40c0794000440d201c5a002507103e10746024000c0c136115000103a03113103076414508125810080fa0204240c105550f0f801b529034006001384e00011030180019a2900c802 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 803001447 1250 803000197 803000201
    0x5061f26041a0c1201031e0f060c02101a0d080f04031406071106010e07020a140604030f110a1704120b04030306080a0b0a020c0f0f070609090b010c15 66
    0x401840503048000104070402141030303514403000900300081c07011902c070840340d4420b5006480c61140076807101001000891800a00e045130340540c440301f4040e4260507203032890341c200403078001d5811903140c0e00440d411607130400024170103c07a401010010007191808140b1442c1c010404075204408061180007801166802c5500102854101da9611640d0307142c601852020b12517000268001d10000440b107600030310041e00fa21a03101c0251456a085c00555a84030300c1c040c14480442c800d07400403030006601144001d105030340c2e2a008103414a0585001802c40c1d2100e6048010058924182505207070001480700b9181e40c010082c00441000400c10151801158405c03810201502c80d80414010202055070042d4003d6806008683e00c4000c42903139494541402070001e511030380014007404441c2e0252880341403140c25220304403c0b4032411803500b11520900c0b41c858000c0c0d13a0030042c0f40d4000820600410000348180200d0300000c0019000d0700d10154068200340003070001c0320b105445a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 803002697 1250 803001447 803001497
    0x30306011e020f010615090e0f04081b010507111c0518010c080a03090209090c060405150c060106021e0c090703150f0915090219030e0a0c0e040605061f 67
    0x40f0020855555900c090410004010b0060000325100800108030000b94590007445a2441841482d071900c541d550880c1c0b680c030405100c01201c1c0d0260103c4442038081c00303036a000301c180f40d0b219155a80604810390030401040c1d92110755840305105085030396000341c1902c42e10200070442c01080c1c003034000140c6680302e0202c401400d0600000c4c2e034010302a0943d018900c018001e079078044540d03440d22595a81c8280e0b0303610325503100303e05000800281c94840440010165074400d03180c10039480020042c50074000380c103c1c40c0540c11401ca09151001c240c407490700c5012005c030041418204603008100302440180c446020181c44400500d91005010b503d0f90080008015011700c0795034a08800f4014a252076034620061780b6440002031440c1c96009541c420703000780214048100e1035003010740081012120ac980e0078055281803101182c145c1e0300c4100207150003011569036241c91314120040b100020700701807040c00003030b80200380c616a110501d140403c140c100f1810104204440010312411 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 803003947 1250 803002697 803002723
    0x103031b060e070f06090b0f0d0b18041b06090317040b0409020c01230712060b0a02031306090807151e0507030e060f09130603120c05060702030306011e02 68
    0x10040c0c050303142080042c03580c0071070340c13040c00c2c013000786855110440340540184665079040b1010312000680c40d9102c802086400d407454000200c403c80000841d0308009001032000710008040d0800040c454001d1420384e82303040b488060000c440c00e2034005888500b05000244c4021141e0003440504203841c4100c502904d80b811403242c81d07558440c810740c0030f548180c0003001c00b94240a42c805041035401c00c0c041108071a049150000c2e0745845080b04c1580321025205001070301d60800080d01030400c0010001116954061036a550901c9003500550301c40d64011360400a480e28200711850740030424400752502846100c0f007031078182c002124541180d8040313030006061200c07a0a80550460010401c0074800d48030f610540a03103008000b00340c000d1840f540c6141078204410740071880e1441245122884c1a80b0004a03d6140d07240c01642480070104040441c0c002d00c85034061000c100441b80e84500d603840210f18518190000804082041c2d400068550b8117945e03d400482c000e100541081032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 803005197 1250 803003947 803003951
    0x8130b0c070f0b011403061005040209040621020109080d1e12060605270a050d08070c1d090703080a0806011e021e01050c070305030c070c030602040e01050d0b0103031b06 75
    0x200e607042c0500d80f150203104010911400800d900410b080c0807480910899600f9051400c5d0b51a0406010182d440001403582c855a110008a4005507001c1003200c0500c05c5507080400600d0b6100140842c0d41c150020105503000d81e2001115540c0b003000c19215104060300d00340524921102501e2000040c0990580d03e800d202c00403964550110180090410762118030403030104900c400c80301c0900d460b00d00c54100305000000d0015003090008401e460303105800c1c251a1103043e403a81c07407039001e0036000303110710b2244240e254250050f0480015086641c1201405880d441d55460000b50303c40ca480c864203010600700040d80030ba01079100c0b49080e440d001b40801e030342c0014440c000d4680303000008808140104074911346001c48140700301841044468545480c007015604c080ea080c2d0401040f042524004200b080000703030741d42d60000000c41c401c02c005078581f4100141c41010a405030440781c020401c542e03004001c0fa2040c20458112605800e015107424046001ca0441c401a610003a217194 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 803006447 1250 803005197 803005223
    0x103090f050109030e040506010f0818240714121b0c0319080106030b011b170f0d050705091807050d0e0703050706051201181508010504030f08130b0c07 67
    0x50300036002d03203d00345c8106c1e002c101954075003006441c2d410b51421107800042c1c50344001981c3c12251400c03819203100c1c1d0001c807804074101e100400801fa000203000f01c00043c4d00c0317042c408825008555844c1751172550840c07a041c210040000e0030618401800b48a980d040c10000b48540b084a1044400f02d1000e08140c0b0f0fa40d10741c0746c00c3c5025803441903a85000141e0701d400009407151003031040660100d416940d00d0201051544141c003075500e0b000055941329094078002089628160040c140c0d841102c200e40d855130003210b141021035400a2454090120400413450740c1d64440005080c032000c882c543d40116101c415045403180201c542514030a0310304007145001ca0000107a840c200c80c0706d40e0803200f165456041c200c80303038000d008001500e4034004005004503000e202e010100410242c3e000110f14402e503413110410449a485001c00343d56070006c2c0010f060340301040d0807031a606810800030030f0800300080c04245c10b4800000e0022101031000c551070a06141c126a945900040e841c5004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 803007697 1250 803006447 803006453
    0xa09020d05070e0a0501230d0504030c210503010504020a0201060e0a06180c200f0a03091805010f05010e04110301030b091507050d0b01230a030b0607020f0103090f050109 75
    0xc10041e2002c2c2c0116040d88162036091812080c00b506407101139540c1c0911402031203200390101c08000c1c000c910181d00380452002034103240325488c070950090340c42c1604485541040c064a00c0314000c0084038039241e811410015412504413411a402941d005a03075280d040300c200d00501d031f80e40013801c0c00500c440a1000d85002c2d42c100005075007506840402d8035680b030407840200c0710000d00100106034006103c8541400c4100c8500400b070a200540d140d816255600c0c03400d144004a0407404185081c0e020300c0402086080720608800c010020055941402140051940030344500c60401003054915421921240c021f0658110500348054413540c5038034068100310001c54100344107100350000d2003400000c0300c070514051942070b180d040c81d01c00d00304000340142081d510700764107006040c140141c000000c02c0c4422240032500c40046e8903041c8910300103068072420928180726100034410f00c1c0141e5100599403054007003d0070001100304492600c002040380d80b90b0050500c2d40f80070228414 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 803008947 1250 803007697 803007701
    0x100e0f0603010e0d0207230a0e0c0c0109030503040308130302120a0516080c0111030f010b07210804110a0b0d18200306060d08030f0c0c0d020a0b0603010504200a09020d 74
    0x20358204101c4c2120790030004980302003502d41c0b1a90188c0c040d021036410046840c0c0c1203499070308120040211840e00c0c62018034a03081d101d81000440c0012000010130060540c448001c40e0040140c420f0425261201d4030700035620803001800c9242da200004001034103900400484040c00c1242e902594a451141400c5000f900242451000c0b9400c0c000c48006654001701100e102d44100d13108080c4030b0342030403203200040d000b5800072a02400c552311081e9017500340307032000c00d1a80307000e81c1c40128519280c0343c009070903405425294050440400300344114100001500c0001ca002c40300092610100041e1130480389919002525000d00d41101c508000040700407a0f403600804d80c100c1e03002d5141c00003400807510041c0c0d005401c4500500100d00d0a0246e840302c1034000c0a0081a01d060961500007542800c580302e030100096070200c521b910030016410702c401d85c0940110000c01a61910340c88940040030514a19022030310135480d95040c56892100150140026036021500d505100c001100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 803010197 1250 803008947 803008949
    0x111603110f0607140f0409110903280609020406050a0f0f080c0a0506090102010b090c0a031802061e0729090a021507020105090324100e0f0603010e0d0207 68
    0x11a80c040c20100007212000001ca07107020748081e0b9101c0714651241482121369802c04000718a04407010040040c40224a020f0400360300d02c48a4215550101c400030140303801c203a900c50b804103004040c2c0344403d802600305000c000e03030340195011400b114244001401052144c201560001c2403060100e040040210100103913040e03260000401a01c03402696918003480178000ea02406404051040f0704011002e000d4011040c0000700b6480c410760001010720404565000e031a500110315400c1c903030341c9030180810b0000304101424221151f5004544e03144a0484081e0038078451101c1c84c0c2030700606800300c170440d0382c104210301981060380420351700501400d2841212003202c00085000f200e004101e4900d61036000300800c40c4d41440400f5000c194000110903414040c0c28440d461081d2010b000100091140140b40d4238172025240d07079811600000b4210043c0c500c198071090106a0442100c56000b410220020000303035074100020340501074a46081c012800340070a002d12980c1c00041d10341c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 803011447 1250 803010197 803010227
    0xb07020a1407050d06020f0d05190605220b01020a05030a03050105090601080f07030507021011070b0705040308030c03130203011416020f0606090406060e04030f1b0b0a111603 77
    0x1e01c6000c0304640640c1e81d03808a000d4203921201070140e0b0300c0040d015900410103650a40031030340c1481c59070040b52003143c6007214003240100c04205a0300745c1c1007091103050083c00302291302090540c3c4031409035030402948200c10b41016600c01c0d02180ca85e000700440700d641030380101201d0b41c074848058000c016100a00c20940100040300118056600840300ca9204030052007186886980c0c01c04100d001c2e00025000d101940900d80c02141d1a2030917000d1340742d100362415074603540c039415071030302d01d02501009182004100c000c3c041400052561000c403900000d030903101d1070701c0e41c907a90500f00580c915600020340c15880c00c1000c000d04083c03c0140740c400c031101c0c0d10700b030801080201d080c2d807104031122104003207400c288002015468641c50860f08a4015500021103d4844c401000c0400d426242503001c1105d84511070040c81e48003440b0081400100c1000408607070994900d2036440303000c1c20500c406038076107400a176131000c07420a451200c0c405851400004909007001340020010404030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 803012697 1250 803011447 803011463
    0x51c0908071502031621090e131103070806162a02030c0901090b0901061b031409040501030c08190309060804110303040603021b0102071164050d0f0b07020a 69
    0x1515025018034200c0007112308080ea100501c1c0d9485480ba2543c0841300e808032001c0c00645100b00b003580b401c102410140070024010021410418004400820300b10300c82c078100410f11050300c07020005100301c64112040d410721650040ca00d07100017401c21982050154100765800c000040d8844a41c0010381e1002d015109121181d803180c0007200d41300301e00842010100700e00d86140001030300c0b5209100b80304105048885c1041401e10004007030340c4082e4000d40f0700c2a80d01c4030602c408a814085440b01c0c001003c201e540c00c0e240c2d5039025090140c18861801442142400142400396455001c41060402016207958544800c0d014000350445045c1010f440f010304107a0700c1a180c1403003140c0c865a00482c0028100900400708141d582811140300d1700c102e001240c0d08000c5210081e02002010401e0100660301307800413418030041441d60850101c0f40c03014103883d0701c2c000000c0800003520f005440c0364150001d14280240041c0c2ca074a8001c0440c20ba0000300960301e51b02003610b4010314450300a0f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 803013947 1250 803012697 803012753
    0x603070f0f0f08010b130b0c0c010f081b0c160e010f09022d1c0914010903120c0201020408070f1a070b06040b0f030109051c09080715020316 62
    0x42220700c010100309180203d081a00180840140d1201604400002880d20407940c0c1d04c0d00e00c172030200d4000c90640b050503401880421403560700007509000d00c02c42da14242c4803901d07041072100000d0005803107e101001c0c00061039607280c0b106103c1403807180845034a64071010340da1840012205000d11441c03008408044000c200b4030750a008507841c503e01d405000081100a651030f1400080504038100098030421003031061401c0c40d4680d0b07040d00300d90980014110098100b03211459070951468059034581144100000e030450102120040d51040010304c860746401705038024800c981008100c0e02c1180c3c0c00086a40562039204e090f9800c45581003d030750040306c0a241940280340000388481d100e0400280e06084c280d201c0b03d403d0500030901c001c50751164020900b12042c800b01610140c01c104a85c0c038200b010002c0001c100140c0e8035010707001600d001c10705d68840c1d51070f008a0301000080b00703001424620170801e030395880d420418241d01c3d01c162803a043c1c034041403001480810500e0101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 803015197 1250 803013947 803013977
    0x31107050f010b0415141804151a1c0203031e13080703020a1802270f0a05011409060408120418150306052823090a14010b0603070f 58
    0x245c0c1c88800750819000d800311b08000500c1d001541d0600c080741c12949001c1881038860641d031010303000754002c0084112071607910b0b034a00e05940742640f404500208007505a041070300c4982c1d00c20480888800c0c0d100c0c1c120307128800281036110344075410340900760b00400000c0f4481c13031034010a8aa00c0f0305129668443d907a403003080d1100300c0e612000e9840ba18035102048400681c3d00f00600340c0807044801454401541c1d02c0c12200d841c408100111007000c6200c06040d41050342c144d9035543e0088030080a8031340b4000000b404104001425a102280401c0c04a2140c9815040e500030300201002c1d030390000001b4145800942003071180218800c1c00529002d0801c3d140d10852220f800d9995680d14142d0035510340c1c8001d0500540700850ba0589200805210140a02c0003202c0d41095071010030b03241e01d62826004030b50390b44450002410700000a00101c1c540003e02d2040c1d0540c811001d448101e050240140101440308211313421003400400c01c8481544441c00991884131a03e48403a2805083c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 803016447 1250 803015197 803015201
    0x206060a0b030c0319060f140103051b0901031103070c052104050d0201110d03051005030c060901110709140414060f040816020a0306050a14040f0f03031107050f010b04 74
    0x48074418240308100301050300503011600540e4041c1840520366000542c03810314408680c1264010011103e9100081c82881e8160340b01251000c0d007464140804c0c1815100b101000074950143c041c03040000894504990103600524841204843e810b030f204d280c0900d000d02962106c2808941d140641c07000030000410850411140e0001c0062150825082406100811080403401d90500c0345a040c00215400200b0821401d813009540100e454103003004840703100711140e001513103c1c0d04000c0c42c01e070321521030f04290350321200241b0700b84407141c150440c0310741044059000510100d0401c6d001500a44900300d09074010782c803c003030034071078600c503120060f843c1c0e2815100800c401c16203034003007404600034002904842e20641101c80c813004480d400102c0045856100301d658580712002c00c0451800c9100f03403408a112405580c400307142135511207211403071a92004204004549004083c14803136400116001007140d840c03659807600d401d01d660b0f9450b460b01124240d60800414000310b05141c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 803017697 1250 803016447 803016449
    0x304080405010c02211605010903020117070306030f06050402150307080622060e04021905060a050c0a0b04060f0b0f060a11330601030606051c0603120905010206060a 73
    0x9681030419040500450f8400c0040f80c2c203aa011220007210203205840c280704a440f480e4000c000e00d088001c0100d0704401032002e9110b00d040c00105c00003000542d81145403070002a59980d00c2400790340c3c4403001a8000c10458002502e415440d840d00ba0420106a01c41400740e8022200300350100500809041c0c20302c800ca44050026142c1030129906003010381c40490a1001011408200811301c00640700f00c5038540d1145860f526014280419820714082600310060240d103800000c504000120f00310744600713030340d01041080005142c5200d4405104141c603840e400307207101079542454284100074004649803400716601d028441e13000b07481c00c00d5410f00b070304001074281c41c14074081d801c082d125841105600b01d110b0146a031602918a8030030480c01a00c00340d00d40004891b915550003e040000c01045a4145031424800b8403905812030151481a080148050003201070841c1c0200600b81c2c551004011511594001141940014481090742c1c02a42120300650f14030042013400021 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 803018947 1250 803017697 803017703
    0x1002091005090102120c07030b0105030a08031f081002030711060601020606040e01061a040e0703060f0b1b0111030121020603042a030c090c05181c14010e0d02030304 73
    0xe009104140e580640007074685500140161841c03403078030040003440f0b64001e000401d041d4200110074010403a902d1103040c0901829402040c0c50401c942d200d81080c1b00c041c1c4640c0e080d0030100626030b40080056040e00203800400c0130b4682281412a4101c06500301f619010003245800f0f41e00110a24002104d51080c44142c0c020500b90b11548103001c000c058100118650b552500c1020030301e5880c1c00c501c00c129000b15074426640320b02c0c010950342c070200d02178618020181000002c204400c012050202903840d40d100703565940003181148030001c03004441ea9091755091843d803000040d001400ba5049078201800440c94450103071403410545540b800c004d50282c01840490040f514000c40902c0b8155000040392a690000c141410704a0340f41c0c1c030032514007420031f209010110307682c01400d91411076410003a080c03040c00100340c64a80b502c074140c1e034007452180c081070250301c15800003200074070b800080c0e0341d1411014210700c501826000302e07240a28442c42400d41038480c80041140d00c501e070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 803020197 1250 803018947 803018959
    0xb0d050919060f1d030a0e09130308060414150301320603010b0a03050109050c01030c0203191806120507020c0d0b2a070201021501050307090f0e0f0609100209 70
    0x85250703140c2c401042103100c0080c0c640c0d5a000e040f03a0b9030141224803400c2c14804401036845141604004120f900b442080718040c500c41d0080c021415454504140646d50505003008107580f2900814000c2040d2540c0303016102d540d10502c81d10144a0207000703104441076000344200201c1c107e040c0042d4400d51a00c55000c00b4261043c0001094054006d8101d240180085524040700c03001030001c000d150401e40701c59540e21050410041d080001c03012191081c20300340821094804065100d000b42034508605900e2410b1104042c1d00ca21034040180140c500e070f003c02a03445440051259036120305100129280601140f11540001400c40a176800108a60041d00c583c1d6034a010300070002c1c00440b1b1100c245544c0501020198074091501b0704c0101100f5111486400028070f0181d0070103081d4000426940140481d40b0040307584800d4615141001c518904107460301e00080824906c0241103018a911b00d44d10b1320008030320303030b0302071442481140c035005d4440320184128801c0e4500107074021 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 803021447 1250 803020197 803020243
    0x905061b04091d060f0a05161e03060f0b0c1203062b050d11010c03090203030d1808070f141b091f09060611030c0a26040b0d0509 57
    0xc40d50b034001c0200e0b00d502491003c0703501440c0c1d10291078084140d80c03d005641c850780c20000c5950152080d594800c00315050020085c2240c98003410100d210441061342e02c0041d440400050702a80042000300315414150108542c7c030003192100707803ca0b0748106854001d13000b05903002c1031380c242600d00401c00140401501103450a00c80302406122034009000240ba4640001190091255110080b92a02c0345068940643c80c0c86084440c4c80710524145490b00c54901c001d80c60000654046c0741c008400003440168580100c20001802400203089800004482c810801c2203c0f10707480d010700c40c2d0040503d410281500710745842d145040c1050001d03800850030f00928050300c034283c2081c5109010007241ca000c040000040001e07030003816070551540750802c003030740e03020b15900e48004088024508140035035a80503207821aa040c0038124154848604d142e50301d114500601c6005541c010696945d40d0f00703002c0145410808915400c1d515010001d50043c401103601020f03c026148100b000f4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 803022697 1250 803021447 803021459
    0x2703020606011107050a260f0d090509070c03030b0d0f230d0f0f11010938040204150b07050a05010c05090117100b070506040c1a04060804080f04090905061b04 70
    0x1008040041c4461f0140000d41100f0200081c0200300403490f8080180182c60203480000e00042c031641d01013070207210480c5c02c001c0c025920800b60140113134503150105581c1c10100c00164401400b0070b0243ca20284214014108400e136000350140f0801d0f0946554890407502c40d25464010496080000c2560032007507104191251075054010700719070501784003040d020001d10b0300f16408007600b100c120900e520038600c90303002c0007074000d1000c0c1c46442d45520800e06501d5241c4076a800340c4000d015541b10141d4244120604407a0400303051407898050f2246070f18100f0b81c1d07a078440c4a00984955103844811074aa520034812106048810b031070340c00300d180032003500510780b40300241600389246200701c011400805510088c10207034080e01c0182070030305050a2440d2121001c1c0e01c4040785032078114802c200c503a41202a2070480c2c803241003a4209a585041082d071603c620402440384800000c0d0110364011642d01410102c2c4c001d90071260181d480540039207101092107540c200d00d40c0248810811 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 803023947 1250 803022697 803022719
    0x40623040c1b0501062114060c2a15040b09063102060307030204090e06012702040b03010e090c010f350c09091003020f042703020606011107050a 64
    0x2900c14000043c1700c0750755641500d03000314401c184000e403440480f059410701a4202d9540d12204645024060504240400461500c98000004214501a080e15600001901034106040440309c00d07121101d0101160051401b000c840c12101c80b030b5903e02144140d800010303101d11070700380d81190304000ea03400d14000707140450820407584d1052070a002c0000584400d0041c41c0100c3c00c989003d6200c50034a1440c40030780d94640d041d040c50b5030240c001004400d15405113503c00c2c1000740035528404d01c85841c031170084c1c40755030000d0510003030000c000141807104036020b0748aa1160741c103030307240681042c0045410041610503840018002c000c54110300010080c14040a1481d0558070094091442e200406044c1107031040390400000c1000301660814940951b8000c000da211070071464156800540f003101030b004254040c99540d0850104d00703841c40c50f00700c540c4c025a5040480c00c0b0440c5402544c40340c0443d103090008115800d549581800000c2c01c42c241c45001b8402d030261410001c060301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 803025197 1250 803023947 803023997
    0x503010e06030a050106090e0c01140919080604030f0809030324240304020117070503041b0302030f070f061805091e181e0309120c040623040c 63
    0x19043c01540301c1030000400902ca218024444490007061a0720b03405038160400346400c044506019140400640e007800c01d5007226502c800486040c1e0030208080f4541c450030166401c0100c207840342d00c080c4000e2580111030f04e00007802a940341405581d03440c0c1d100340c9a0000351440c0c440200003425000c0c0c6140e07143d01c00c0c01c4101c40640002200d06880c019012640d14104400c00035400020500080d540c0c000f641c903811003050b03207041c031030384c103020741e00601500c002030014005260140314034510a0340860413070000d580080481710121140030005454085610555030185901311000030681c3c02134010b940352003180111104980d140c14103001500c5402841d00d80c1d83d540c51500b030340300c080300301740e8650290403120301000c02c51441e1880c0c0e03841c014a154004495210f61202802d492000000b151000f10040d102040c0518940d4201d624041440f8003460313201e8104203010850b180c0800f1011050303419150804407002c540c01c1800110344504210b24000340303013800c0c03a00840814550100c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 803026447 1250 803025197 803025199
    0x21e030f04090f140103030f080603160603020d050f0105061b030d0908030a0606080f061c05240c0f03010317070221010506011701170109060525030c0503010e06 71
    0x203140c90115801038100c0e60082c1c00035114643da0310008402d0b075445201315208580d4110b8480e49950442e10040d050a07203004202042180d02400a6160784040c0114030045040305e032040750164590381c3c05806500010342c2c004049181100149070070f41603a5240c1d04a4101518041c5055001c1c60700501c00d40008901d0352251008000300d952245143c4103040d401800f8024031a26810719101110555965500413000c100a50041c4800c81e01414112a00310900b11203404003508100550901003c10340400b510300d00882407401c4051f50b9021608015103040b044403000360b0789200d0701102500683e00d20b12441c460600c01400020468005400001101c00445052006a500144103449d0198001c0c50072003c07450002c00c01c0c0310074090950007500900b02060102004107852150800500c190180c0b4036030303900182c140800030362280394800c1d007207001400f04d0300d8038050203c182c0032802449034404143c00c40442c007c910a00c40d40712041c00e9030340d41902d9640b90075000b801c0c00d60080e081c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 803027697 1250 803026447 803026453
    0x30b0f040c170a060e0906060105031603090b070807032301090506010c0501020c01090210031b2a111008010e1506040b0a020c01030516020c060a03021e0d051501021e 73
    0xa1110035002c50524070500d940400883c801c0c2c286080d00c00c417681c0151003015664030000511030540c0c1c011081d80d41c03204034001900100300c1e09900480150100c01c80240810746020240001964440760b41c80c41040c5585061004049882410800040c0782101120304c503c42401405884403680203181c1000d0140340104043d400750f244c190899200030000803c60f03644080c914110706081c3e40390305001c40782c1e060030001c0340740002c00b084001850100c2e800401c1281d14040080710810205401824052119000901924078102c40596114040a4490094107046002081c411f2000c14182e440020f0320760381c15104e60191540f000109110750350b000300140004541e40d06c20750080c11110744503a0050050024640c0090100c46028140308040c0d0074205860b51000c1d000154134070131403420b80300c8503520140441c003107000780202d010310014000350903406295100d0580203080302c0111100e0410081d210421160408440f10140742e026030003010111228500c01c0a440001d10850025 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 803028947 1250 803027697 803027717
    0xc11030f190515150d06110c030d050a020705190f08070602092b0209060f060307020d0f0804030806220627050c030f0903070204061212030b0f040c 65
    0x40d241c00c0000c00d100001c45594204403010a00c1010490354a5010101043e51458244281150300c11a80700550902402c28041c14004002e030640c01121138081e01c1541c191140300b61002a0f0b120340c08960440c5c1c070741d81404003040b103a40042c4225181d00354030000400b080f40a400019040d569244130540380545404284004165940010304000b80f00c0d1100680c0c46c10150204003455108134000f80d10780d44800d0317185215a02c0040d0000c1c81e10f404903821900c0e40c0e00c003400540c1a2103400d000d260081c401000784a08142c0000ea09002200136483c1c504580d480240d08640c0c4050465026000481400109805040428a030881a000c141a0300c00b5000c0307440c0000103076070403940200c03154411903406958500d20034100010980070f8900500c0301e41003c7d80380488500001c0e0507040d0410701c850206203051420001c560b806035018006000441ea140c1d001c03040210703c6602034480400c80c421140c003180c481e05c90203112440080030040b100e00c0704018040105200f448aa0603c110101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 803030197 1250 803028947 803028973
    0x181112150d060903110601180b0f100e01021902090408030a0e01050f101d0a0e030c100605040b03010c0206011e090501151806140d18061415010c1103 66
    0x41a262481c040c11021450f00800c1c0350007454a4544d03810f04090740c002c0b070014030480811580c510541c1068201c04207941c00740f10000b800e00300084141075072103480352001d800b600360464030160107600240c0036200141d07185141061101003041009500c0100c003800a40001c5c00da4029607007103500d5220008a80d2140e1200c0c1c0e08449094820140b400c652170f041020350349034042e003107018003003001400400010480c0d8003040c03160b001e0a45200180c6401c80344510346410025640e101084104650110038541056001090a402400d0007603003002d80000c0541414010182c460509a0013095107038a03003500e0300c0800e0360550b44c89400e45041c000001d182945801070b0380c040c040f003d61b000000c05c4030307040251000c0b540c4038040c60511640b00c0704000042e0044000b10801804020066891248103000c0c0300a015904c5102d441800448422051003827a46c4140c80c40f40104600508680f0380da0152134603140c49802b0325000401c80c490110001e2000c0403000c1801300081c08880314404248 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 803031447 1250 803030197 803030209
    0x1e0c18060b030f0406290411070f0b070e121b04200301090c080402011b0317070c030905030102040b071b0801020c0f070603050f070c0309051918111215 67
    0x3030b8841005030043c0c030511051004521404222882d02c0c1c00b1020800641ea5407000d00d007160000d20746c03007180e4561951240040328412104503551099004e60454080e02d40328004079819119100040d820407040f25681c01c00e0301c000c03001c50380198018000720410313860303d01c07160f08c83c40c0c1d030b80e50065100d01c20071003000c0200c0241c0f0104402440d002c4c0d140d60420000b8000c648849503400b04015400c818040980d0f0401c01c68405500d0040880d101290075080a136403040d02c030350380e12152044402c01c000f202c2d9841198420070502c240c1e5540c51031941e449c02c141c241d0003a0701801c2c3d501c04040040e400002d0800740300f030b02080542d86442040750f548220003400ca811039242144a034100c103800710074600c820301001c8040d01182c00c003084a400c0110005000000081070f44c0f0611402031090401d242c0105803400050030002d01c81022440203085070a1045401c1c40f8032010503a072840402c0c00c065a50140e040d803086003200351810072043c0c1c45480740c4c40714040c0041d642400359884003070040c0c0b200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 803032697 1250 803031447 803031451
    0x1a060d09031b12050d1401150e0910050d0317010f030b010906080a0201030b0f1e04060902390709090b0603010c020a0213180f1e0c18060b03 62
    0x24280050382900505002d400c0d411410801e40d80e0a0002034800000340540800400812040c6030854403901001c0030304005003400400841c0c0d045e041000002c4050021001080a441503a039424032502103d05014901109481d5024401c420400912650070540400a042c600900c1c0001e255025224002e600903030a0300001d590100a0006105020755520070134010002c850007003103800d01c0c00d0502610f07640000380090401d030f00c501c141030280d92030300c1c08654100002040c00368045e1581c111080d20b00600c8160328061418a200001c44c80701510a0f110080c580c8446145c1c0c00840f4203030428800310012414110014080a043c0003400811880001d0320901600148050040c10301c00c091400040a00d4800da04000060481d180d01040d002c50701c2e80c1c15141001c45807010b03010880640031000d100440c1458000f07240017030060144515200354010240c2c4118580d40040d0001e0042d00c03010007800c0158603540030402550000c0c3c00c80c10f042d80d402d00003d9159250302000a159000f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 803033947 1250 803032697 803032717
    0x1090e011403010e0a0b01031b0b030a050406050c040f0b07061e091e034e050112260d0f0c1103040f05040509100e0d080c03010609091a06 61
    0x311908401582004d100b06583c0e248144005c01e008011661541d10020301404000c002007280b8a00100100b010000c01000e0701041845075180e181226940004040403070b0140c030b2950815000c9002c00100c1400c075800d0721120288600b46508255101d01035600c01d481c111404c40d03540d10f00900d0b10040e41c0100c500c1d0203115601041e82041c0d03003071064185610b940c05258441d1580041c10000e138018141001c1c2e0f19004108e0001d4004140c0000c030511100b600c000d90032442088020441c03800505000d00c84803200904000c1641c0751080c81c8265807014400601c01101402c0d20a840c0101c01700a0208120b011001490b0903500c024400c00e54010100e001c00c000c3c1c94030501070b0340f1030308400c81d442c40f0070142c0001d504103844c0038000280c82219100f0a4040c82c3d07101c0104103052030901840f00c1012140409020714190340c103880d82e07220101d02038000007600603000320b0115071403641141c1c100c850581d2465049418140b41b14000e20f0701c6010220800d5080c1c0c4084916107510f009000c3c8001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 803035197 1250 803033947 803033969
    0x22107020a050c0105251a090d0810030803060108040609211706011407020d0206040b120a0b01080403120b09070914060708040311030a0f051b191401090e01 69
    0x240b4074115280c0062600460705200050080640c0701030502c400b2084045030248180f500c0c8001e052003420002400d003c20b040602d488200020702800003510390b00c0882507035441c40c4544e107040c49212074020700c1c080103013024002c0001c0b45841d80701d144041c0d007160207010001103145c03943c2c0d2010000c449071104106086102d10010f13100503000440d9011020084843e1000c502d00480002e001048012003540e0f400c0c0b000c42e0007025500c482c014120403039405098203980b9501c58542e52810740040d10203050307a00c0c1c1c1c0e800180c40c442c8a40141d844908040e1142d0603507456555058071500254044403081d46d03038490200403991790303621086000303000d10740340c4446080c01c1104030300031550220540e901035241001139500168410080b10b00322038003c100a403a02c04050300082c1840311401001d04461080b42d2101d0910502003481140603920b15440790203000f0801c00c1c04001c08102a412500d5104443e0800c02c544203060280c0810205160580901e038841c006c0c010002e6080c5c00c4605020 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 803036447 1250 803035197 803035213
    0x30a0f17010923131a090c131508010209240315060706090b0f06100905190e0411090f0402010c02130e011505210a080a0306090f0f2004030602210702 66
    0x950812481030030342000101c06170354580b08010f2650341281040d1140076410007030207a0150011a440a00420703010307404201007d99481001d4042c4d0044000b16118000c2c505000e5000c4d81c94019a491145105210314107542d5803421203690b040d0304c25241d90300a04100080340014080c0d00c50348038043e03c5898041070394140480059494100100341d140510455507003241c80b00c2d04111a00f0444104582090154489012130502c58520340d0055420150410a0000304000601a00c24101041e6980015130361202686034450350291400ba000c50980203450025007801c1106020001c0c1000c2d02103000038440036020b08540c01e40721560404400003105126034900310388160387c0c1010981440c8908005841d000d51603e154400c01820008000340841039140260040300043c221640d00b000046c0f00c0c00c0440c0c01402001c5100c03103c0324230b03044401212200c4564100a03406403981c0c0d08e820309007150b441c0002540076560140d21500d2204451089100710035080c0e10a190f03070f078080c180f44 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 803037697 1250 803036447 803036453
    0x807080d060f05011d030102070c080709050c120a0e0a02030607030905060a060b090105030a060f0e16021c03020903010902060d1409010203240d0f0302030a0f1701092313 75
    0x101c4158110b00c6580780a050104650307a03201080580030103c040ba207200c008503501c0082d00900c80e0075801420203240001c00160a14040f82d69411034003800424003141e40d40701c2408d0400d105001402c040203402c2300c08144032200d69131001901452400c08c4554203001c03900000e14095046402200180d1502800420010207000068100b2282d0790240851414800154900d01030120785904101c400f00000d06042c2c1d00da003003500200f000784180c1812503280e00c94520403107800c50302048100c941c00f0189060303a00c005000c0403005400c1d98200207501900008802a44c0a101d1440e899900e5000c4c1c00c0c090303582e400060100e07614800380081d694042c45104284000018800102070b441441000130102400403041e101c48040e41c2a00f0851810384005004103014480284c000030b0840d102c1c01c02c241d0000004c182c8803c00e900c0c0c0305505080c0280c21140e0300080c1ea64134026107000401004483c3c2c9a403c43c0118100151182c06409201c40b401280c4800031220041c240c03c042c40d141080c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 803038947 1250 803037697 803037701
    0x50702060c0a0309051b0307170628020301230d03090b0c07051906020c03190602030403030e100c0e03211b0f06041707020603061302090d140f01090c140109030807080d 74
    0x12301d090200303120b4410002000c230f17890f070364000c0a10718040e2022180c40350b0000c0c082f5203091014080081151207503191141100da04028440f4000ba112035514100603a1400200024602c0c3c0c0c10f039035120f04d190400d10802104c1e001028018100d100d50031020401d40d83e03950107134100501c050140c2c1106e51422400a10300f410341c0d205540250030000390144544407414540b8841d54102c04056540d45070b82c0782c110002e0022080c185100e010780c2c1400001d00c10190450604031101c0d9541000e0140000c0c00c154541802940310f03506050082c58140c548031a4401a1141594802c8510140c1281007000d43c281032400100d002c0c10342000c401c100411600a82480d441000d81d01c0c0d4a040c159284d011503901c3c400581050310a109081001300f10440e02e404440300c155000c1c10424524860349021140304649408500c0c10340507605400c0d0402c181403044050041c0c00003c13075a8a40d10f00b0b10902d6403404002441810400341001c0807003c01e0320000240b42c201d1044180d141d641c140d42c400001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 803040197 1250 803038947 803038949
    0x6071b05041802090a0e030a0e01020a020405010e06031e0325020901061e02030a202a091302010816020304050303070309090c090b04140109051021050702060c0a0309051b0307 77
    0x500e05d454130b40c5401078401e0001c00e44a81d002c4908002c03015401e5100142d2074550b242d88000d511505101c00031800c1c00850000ca0f00071042039046031080028202500b91010702c1c101d020200b94400d2103500c1c2c1d90380c001d26070100c200e603000e0100103118030306401180842009800c8100801d03035030190880841c280340040386514480d4405182002c40b400e170018100c01920801c2100326a49400d2160700d0f140030b00c42d88000f0381a51042c185070324a49807010080162451905d84280c2c005000102600391b5800c0c9054040e90595400c3c4480c2e4901c40d011412407400d1a1041c2144002d10011030161000c100802c0d813140680c4500b84698038001018040d500c80c1100a0b003000b5070580108441803030442541c00340da81c01784d01001d100c03030000c004039042d04072584410382c091035090007880b00f5500403038282d20403006908141c041414603c00c2c401520020303a03907280140e000c8400174a107000500f0203006003550030700d0003045100f440c2d21014601001c0480158074480c0703480703080c0c41618040241d20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 803041447 1250 803040197 803040211
    0x12010504020108180613050c03100c020c0603062b0b090a0c1d0703110d020403080d050606040807030b07050d020a0207050f10020c040917180a09060506071b0504180209 74
    0x1300c03000c44901d000a80340c0700c004d040c0302d03105a21000075004003d8280100d00030074601400701d9004000e000c030710130007030000c405011000d405000b5078040a810104112845000050a104025010302d4410b45044000c466800b200e80d200051880c00945a01240d50140c0c040000408003a5010700f003141000e4510752150511410500703484c09040303051111030354080c446040014444406440c000a248102a5a55034480c40003401100300140500a000c00e8114032004204175599a42031040c0380c0310b540184d80459100c001c080001442281c81c040e840f00452800c81d003404030304c0d01290b007a60040c814440250b0401a41445541071074040d03501049400c54a840c11200b8502010f5100c0c041300780c1a5005a488071945c50504c0f400081007030310141c0b030340e1318665105200c00e4100da01491450300d043c420034ac152800121800c3c24000c04080e070708020480d5190141540d80c42c1810100c40d0b518290b00fa40c40c5800295030385e1588a400801c0b842a10281c814080e5481080321181006002d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 803042697 1250 803041447 803041471
    0x215030c0c100b0f0904030e12101b02150601050424230d05150d050709150e06010f030e01020c0c0405160c03050f0d0f06080d030e1009020f12010504020108 69
    0x154000e913540c01010b41c0803520a850b500d1032074a40e804d00f207a26982d0f044445800c5040d40c250354071800000907902c9042c5e404140b08015014504034000841200402c0760b20050340100208000e1000c650400c1e9008141410074601c0c0968455009036802403980c2c00c51085080e1003c42c1d41c1c0e06400640380840000100b006490314804160386503140e00694035a0612640c0e55000907440c44c0d1000590250b1090080c2103d03484445071400580d680715038000d0170341e118103008071102280440e614a40035200c2c54a5800340940d60000116091191401c1d140101030b10b07103110b002d0007042880241496184c49000d09001250042403100b5584094018590a41d44a100c0d50001d039000318107620f0030b54946000c075590903801c88a0440c0c1c1c004e070b407031155031170789400039140b4400b549500100461f615103090755001c402ca1182030f82103a4030b010701e00c40755800c881600074410442368400c507c071902c020704000b5110750a101240c081102d08040380d500b43c1d90390083c0029036810074000b40d8012320200305 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 803043947 1250 803042697 803042711
    0x100c060509010524030c180603280b060f10022416050306030a12030504110d030f0e0303070b0405030a0e1f030522051c050f090d0215030c0c10 63
    0x5180050801001c004a5244282200302138954003070010b4903640c4c0d0010141005601c4010000403902801d8032064440d21442170000f04810155801b40902044546503020848460300c640450172402040107900440490310140710f59247e00c120540c081e107541c01090010000b10f085030f894060701c081000c00b2501c00d000c00c1403031900101c0300840c0c0c1e011807a02d00d442c0e86850000c24500350301c0040061803005c3c0c51b0304c48020154540d104602c00e5015919412001c0b4820040c000200c886680c06000110041c103880c19150162201401e804c0002d03003100e00d81000c548610340032140030345040359180c000080680341c03298061100006403004503440925140e8280a060305c0c4018040c071481416141c800054203810a40030106120601c400092100c5000d031070095110302c0e64104d82c03a0047d82c080b4060301010301c9030065810403000400c4880c030b0f14035401d00304010103c1c80e0704100d0340520040342c0286005c0207a005180580701c00000c65031619030010443e0304100000d42100b01c10761074200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 803045197 1250 803043947 803043961
    0xe0402090a1205070e042108131103070b0408070503010e0c060a081e04050c1815280e04030311070f0f151a0414070807120b100c0605090105 62
    0x3800c104680503001011540409494001e050040e01d85c803802950a00000b0402400524900d0030206011031000350100c0030424404e071030145d4251000c0c12200b4034070b40058005241a0010800400010116407019903144512480e546c030507081005140c000b804100300508007402500d645895074030150084920302804542940184110035080020650110700584030400c006061004865005c080502d45820301d85e80c1c519034112114000d4403903000c400801c0114094103401804000400c3c1400c80c400c0040011103400f00c1c0101c074459035411030f50540d043d2058540c10040400d00040b501600e800e0034050304842112503c0008040c04005190000d541d425481d00d201e41d00c441d0168024040f8100201c010001030003844c042031400301b106508040ba20321880c404031084800f8072003042032a10001c020700341a00c0120100d010480801d00d034be4080e00404d071030a0b4118000080300782c1c800c0c00099611141482610203e02032008280900404d8050a070f4003142d400c000340190b08000c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 803046447 1250 803045197 803045209
    0x151e0405010c0b0c0c03040303090501020d081012051219080a0608061b0912010617030f030c0f0d06060509090702010b03100f060504021201090b1f051b1c0e040209 72
    0x540102401090000915135401c14401d980b095600d4104594641d038507480e0280c2402094000c00740548903039000c00e00c40a10545103184a16150060411154541072000e420b11030351550440b82030080c0220300446141c2d00e8050294400410100036881780d80d50400f6200d040080c1080d034905003040010700c41c50000050294120300ea010311000c840c50110124841405001b001562007481c3e6001c0c0310b01342c1415046581580c12000403804081e10441d407481d030340e101d2503030591345203d02400041c43c8541d07a100030f4001e85500c0403a06241610030038000e01100d51540010000c5034000c01c50054038106170612a5000c8020300082081c16501c000181d03807007070181c00d000f50b42ca88503420034901c3e5401e0780112000f0900500155112101003000c0000d0b00000d00843c42c2c80740c5400c03080a240d18008920f0440050700105251075050b030702008540c1d81d070183d08170f182c005948ac001041c03070100c00c0109140000540300f01c0790421003101c400400602001e00054030032801800504025a580c1c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 803047697 1250 803046447 803046467
    0x180c060f0c20040e0106090b10080a0504031e0201062105061303020304090f06090f020a080f2d0702010b0f101812050313090504030e040c0e151e040501 67
    0x40c001c2480e180702d2038001c00c41c690703101c41941160800030030003d861015040401035030311a020a204104071081400181c020f92071442c3d00044519010440306030303603503003c0c2d60000d0082c03508002003401c51307803000107080e80e03144c022006070341d2298200f095401c1d0b044140242040480c8140000401e0b440e01e581c2d40358054600c04145040c9185070742003500070030884006041090b424490b0514191001008004500c01e0248060521000514650052007100c4171583d1944a5403a1600d91b40600743c4081c0c0000e250b031800e188000d034400d500bd46c803100715a8404881c04500c3d0198a44081c000b402d44d0540c0ea0f0840c0038044502840c4095a51546c0e4a4640f03810b40c07501c030100c081540c034442e46c001c14550180c11840094120001440000720041c0344810bc165080c000136030f074401e0410100d600485014000407941c0041c07001e189099004654018410310b864040d90340a42c0000d801d0085074010b024800000244001c13003102401150394203103500f01c0940e414940307043d001a01c15020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 803048947 1250 803047697 803047703
    0x411040b0f1201090605101a0403080406120e0a0b01091401030206030601110309120708060906010e070302070602220906050d12080405070b0304320a24180c060f0c 72
    0x5480003002c1c45040c03d520030600140c00080c1884141000d03014422001c0103070140d140030040c54a0900e01044119044404a0742d00428051600303140610480320b8640c42c100390000c1c540c030307401902d240c80c43c200148604140103954003c07140d45000850303000c50b689d03a80c482030b220049000400c09030344c4680649500c00307000c2c20311100800c000c40c8a281541309020565030301c01480c1e40100038085000841e8410303204400d04031034440c0c5a1801d032503a00c0409104c3c00f2010080d460019445911070f2b0080c0410900c00c440240c1406400048070303100c0c0c0c480300c0400031420b401003030400c0001d606000e4600200010782c1d041e4500c1e003154441e422070184c0d5000920602c003c0c2ea004c0f608000b41040340300010000001a603403241000e107442007910213100420240e000c0c40749081030a4403002407107229481400c2c001007040e01117585da207002c0c0164418034010b218038492442c0041210f58041d15503200010f400e0300f6082c80117032812041d18640b0b50003100030001010400c0308020381041701c0040701a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 803050197 1250 803048947 803048959
    0xe060f220507090506160b1e0103150f1d0d0f0c081612020a0515010b03041b0f030c080106060314181908030a060501080c0a0509030c04060e0411040b0f 67
    0xc0c0b0b00074190344030045584260b401c0803000411880500043c181284220b115245030000d6840b00c0c81c00c1c840c6041c800604600002141004100003540d203012140c00101c003100c0402c0e564a0302014400300d40481c60880445804c0902c9100d41803801e01205c10ba154036400c04075120b00040300010010480040c004241c408c0025043c0f0402c01060881420780e81e100501c484d52101142d0300130344643c0c0a1104503814450300d070130524183c0140d0b10442c1a07030303a960b000324150341d2540c44044086901440c051083c2e1110440030990051550f14240039601a85c2c82c40220f500e80082c5070708580c05540f05c2801c2520300340da2040c0c20404810304c2074001104141c0c40640f100031080440c20300d41e0150006000c5074880b1082401c0242000186114442180c0204426548c85c80151484001191414601c3c00300304400c443d010b0140c3c0107065500e05c0501154121450304000c9800c803440c0e82c004056004501e4104800c01c803001860700c404840c150340c240304080d00040801c1101107509420b52041c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 803051447 1250 803050197 803050201
    0xc0e18030a02190c09020a09030c0503150a0b0112060f05031b060a050c0c060d050f0a0608101508060c04032612040f021504140f0907180806010e060f2205 68
    0x4035204c810180900b03e0050308540d00d8010240c003401c190b04501c000c9446444c07640c2d0026441c40c010911071810035000c03030490030940e586900080204401c415043c10b000038500801001da001e0b100f603901401c1444030401000d42003004141c07400368802800844c90f05050a2000d66450b00c00545401000383c0c20101d40342c2c160303d1609070500e1818100c00b0740003d00801c401c2c241001c3c60304a5400b0740103660f0502041c0d03d89001210035030b02d0740d0050700e2055116a107404c851508980c0906d54840c5016402e0101544565200e4108802900c0180c0c0c4120b000c6005d01c01c1c03060b02962812070032404849000103440110b65200c0a000d03e420050103140484006000c3c011001001e941066005220075403200c202e440e88404ca80050103007003008102c200c00d0981c1805d10600c000350309030004013072848503a68184201c6005681050b01204111f1f00c540025940070304004860203041c20240484003450203009000e4007068856a480c41a60424034040c01030140f950406003985807008081025 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 803052697 1250 803051447 803051453
    0x60d11061c020904141b0c010b03030d051021122106080f07120f0c030f0c0e10060807080c0405031b092d130c0e18030a0219 55
    0x1502401944022103024070280314140101a8024541024100c80c1003103481c01a20320b60001305030032514828000a4010343c00326000281003e4101e9000c02d00020070b90342e8405001c6411030b00306100049046443e602400015054160f640d0041c0465142030f0f02c3e20360b07240d510410100e44e00080a8014000b002182211340e100d031002c2c1008005050301d42150342d0000380d6a600801540c441c0380c1e03043c0280c4407500d01d04072010844104441c0915451a91020942c44084250442c440c1c100c504940414000000429540c007030070001e801101080b007000d14102c141640483e005003144c18403000c01c1000d00005400c101c40b941c100d002441c1048050f603400c6002040c5100d01e803c25a414030a80f1640c91207580c0d0031844101c414020f0342c07a01c0a5846402900742200380c03c17002240c000c11152109066015000702c0b0652200c0011100f40d110071b1140c54502400d9100d4001d4420342d40e00c4410440c00034415110118070054400c0214540901c0040094941c050b41c0407004c2d03081c81c007034080414 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 803053947 1250 803052697 803052709
    0xe070e06031218032a090702011505060d090c060504030507060c0f060506010e0a0803270315040609020a030b041a0c190c0203030c03030133080a0e06150315060d11 72
    0x24120043c0d030012417800e070080c42d441c4110041d0010910940080c0006441c19106000349054210340400c0e002d125030504040240035000509030180c6550366020400c0490000807080300181a00c3d2a515a11421401c0035414400f86400c8001071159043c40200003805240e64600c1c1745d174200c2c80004d981d40301c00700102c1d407a4a440c1d803007581c490f140c0e85004c00c940c100440240f1311036030303007502480c207c010032140303095800072201c0b80c164540c229005011444490801080e44207205040006290f06035500245540ca400d42046c2d80e0350445404100030800e2028400c46180381c50384004041b80340449505c0c1881c46002034246482004800c5508040d0085100342221903004007601d46410168141c26030765003092003081140101c07052050000ba4802411400d50202400d1540e51031903004c800703032501e04d000740c045140e00b9074a10514103070913000c0c00218001d030440310800c850785c0f00900c00c051825500300d4138000441c51040901c05196101030441070a503901001c0070100441400000794 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 803055197 1250 803053947 803053963
    0x305030a09050d0f090f1401030c090b0d0b0108072d1b1101031503150203061f0207050102070506250f15060614070305030a05190e070e0603121803 65
    0x1407841450f00c030b280402e401c803044a5040c5004d0359194a81030399809040c000800714400d010301070b502e10302d40c01a154800e4012038044907250031320a0015aa407900003c01c0d038405080c40c9400356881d00c40202540c0e120030599000519443e2140d100c0c130014002c2c45000d9485c81d16071450324000c41e0f19440c0c0c0c034080c0c803041002c68040781099082c4070040c10810b96130004504803a0000c1d24082c500804c10f04090300f4841a20340080074039205080c20009000250320260445078801c00090300e01002504042c45c101d900e440560140ca4900e02e04400680780490540019110f60001e101303030031103102d00a24281114000d0301a1040c1640b15080c0807244900645c80501a19207042d203c01046185401840454050340e40386106100010a010700900500c9070080005a00b0004a0314039a1590405508030903503c0444007007040ca841300c00101c90410400800d1a0010074013044000502c09900743e00c0342d020f401602d40d0001a8006c03c85a01c80c46070006c0080030000c0c01c0006544003001469 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 803056447 1250 803055197 803055203
    0x3100f110a111005010317091924081603020f04030804120302100504231c091802090a0302130f090609150b10050c031201060305010626040305030a09 66
    0x1d5807074003003000040c941100102005018400c1c0076a42040d4160b5108140c100e9410460030318249142146050540d4031174002d45134072110045040800020b4144040d0090500300b20b0103055000c8000006c80d29941d84801409018441e0104408210141c1c8407090003c06480c1c0103070340d080317500003410360f0307000b950005003859801243c0822811502046403141c03500a40896005941c00d4140005440c02110003c0400503000c2d00071690b070440c6800d42c015030f21518180c1d450492003000790b6402c9000a5442000038214110401c24480305010140c600d40d4128000d500e0510004046001c80085100003406610a12401410030020764840901c0b194680c805110b034000740d05001015081c01c4400744d402d68400013001082240743d100d06012802d0103030040d109200880c0064481c1c0c1c2005494554901041000c801e1016040c03000701c0c040c001da43ca00003500e504100f0000e096a200d1052280c0321041d00907040c860100c40800f00b540198149000c99481c0c0c0c1c2c0903074000160440320001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 803057553 1106 803056447 803056481
    0x90604051210050f150d0515060d0c0902030a1a130f0f090c08061311091e043c11181009061403100f 45
    0x810000700042060300c5000e0603a030082d0007511411034005215402c450104091140c0c0340224a407100410744040c41550380300d5840c1c0d41d0760380c242440d940d2240021000944956100c03c211810281e104d140a07412664820514002c2d40080e42e808454030308001c0944e00340ca61410705194914002400c3c0010b0f80304c100825001444481419001f81d901c440707503100040d0560080d0400c40d4850429078801ca0b240600042c1003090150030090b09001616882010480080c14a0050041104d1421135901c6000303a000c080c2c6110100311071000c1e2007004201c00d01800410fa410340b404841c0c032030340c40c80c18445001f2135805040e010408903001d0080d034803c0401e04486101e0380607003002e00035044042d10400c180c02404411102c0c0f613601a280c0c28180401c0c02d0b01c0c06403100404a42c1c40c0c40c5125424000069110009101e9003103000380c0d14411545081c003250400c0401070300f1a040 = true := by decide +kernel

theorem cover : BRFrame.Cov 802877697 803057553 := by
  have h0 := BRFrame.cov_init 802877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 802877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 802877697 ≤ n) (h2 : n < 803057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
