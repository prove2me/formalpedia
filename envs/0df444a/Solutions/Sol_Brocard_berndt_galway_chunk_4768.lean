-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4768
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:40:01.679989+00:00
-- url     : https://prove2.me/submissions/c913b579-fdd8-4c8d-b785-c2ffcd105048

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 857374100 ≤ n < 857553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 857375350 1250 857374100 857374181
    0xc09030201111c180b070b0a0e2a180108011d060c04050603070e09150307090207020303040501030c020a0609151107051f0b12030c1e12030c040810 65
    0x100c0403154012101e000e05404c80d03031201040042d40e00030f600c1e400790012a40c00220215071104410003006140b100511030045008009030140521086000c0c018692441209c0300e941030130540180382100c0e03038504aa4488091030180c074283d4640e52003910070300802d84101e044220412013013230760710f00c1100400c4091050b203050301c0040c2440d091034140612508000c00100c01d020300809003003d00d54440301c40c94030459947c0640072915401c04c0515082601d158480c00f500c900602c05000182d0700401990f065030020f1900194044115408030710708051044080d10603894524008180000c2541d8100c01d14500e81c01070004080d41890782a081c07040f504080c1298000d4000300c544186c07071803d564049026007101051038141b500002c0d0282200700301880c850360000440400d040004d00601482c070050228808071254640d0700340d501d43c03207502e11084880c00000b001a81040200c82070350090300d0b41104444030320841e518542c1c000c01c0002e46140310b0640c2c02c5800b091101e0311119141010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 857376600 1250 857375350 857375383
    0x3140601060801241710060905240304030507020d12020d0c0203030d0507030b030f03070506011202030a0b0a090b010806040c15050a05031305011e05090118021908010c0903020111 79
    0x1408440c0c9035610701d62800640200b00b04840e031441216141c0d48484501944e812050506e0543c58118084c1040166510a9001d0481c110306026101c1722144085400f86a5903071103541c130383d207510301120648100c6000943c05001d44403820148408a0304480b101403258013215205901118142d45504410f040207500d075100b0480c120040c2d107150007071038111980e0704011034005900300001e0b0400507004c003c20440ea0005c5080002e00204011903401040240380290004841e90046521003044d00340280030110300d038010071016803555010400d4541c2104010b8103558480b10080e8881509550607100c00c0402d80f400f10340c2c1504008100b00e40c0e902902c1d441d142c10024001912543c000800031400c260443d503000c03020500a00407490071035040c0c07440200f8101492000402c450010b480041140e15281501d00718126a4904051180d012581d000340e0400c0100c0d0744520442d20b40000896508040000c100f41c0d410240f0789060300e03c02d8969140401c00603101d81d5803030052a41d104c454 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 857377850 1250 857376600 857376629
    0x70b0a140f040f1a0a090c0e0c0a08040309031a01030b070f021009020a050909070608090309090c0f21160e0a05271f0b0717130503060103140601060801 67
    0xd4120a88141c900e48500800b1444004e20b034250391002d642280c01c11401915404408108484080c80074003400b904c0310108024103140182e28414041e20f00c0c140248407404010074141400303501d101000b198840c1020a10340c903c0b030103040d50110b00381b2048519011802c08201114058400039100401e107500400c03900700c508500c0c1014040038070003640c2040410501160503211590411300c2034980c00001c0107880e01d40100284100e1000300290080c2d042400040004ea941d5800c0680102290385110f46944075105a40f0f001c1c440e1181416201c080400c00303100581c61010b490703124596a4030b001949152501c0309544d030540200000754410151034044c44185011840c442e0b00304030303000151443c1c9030514182d441c0c040040d21800c01c1e06660b01442ba1580381390300f0420000d040c1140089080150303554840c459058030746810403102c04041103010003d581c41000310700511000b01100c0703072542d680c200300d410841105100d075094001c450022561034066140c3c51b040302e2040300c24842 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 857379100 1250 857377850 857377853
    0x4170d030e0604111c1401020702030c1507062c0a0303180b040b0c1201271103060907120f14010e01030c03060b010e0a3f03051608070b0a140f04 64
    0x15138002d26440e040d04002c9001d40b05d804904401800c2508543c81000180e0300d240500400d843e010181c60400d101e905031229102002c0084c1e810f480303040b42d03c028081024050078030007103031241914110091000d5410610f9035400c0700040c10380300a5000b6101002210790303144004042e000a0540030b03000e41080e501090004080161482d408044d882d560381c200b10410400c002110820791041d10031b99941c07002c0390411802e9100c00d011500c181c07001003020800d1072020705a103020060003d0b1183e012040000c461500841902c1c159017400c64040050346031442540e802800b5940030781d02c030102d83c18000314000c3c1d680e0310035034161394010003894030980c030f5592003c1c041d012030700040b8100404202611401e8450076040d030040d10346c5c845008041450b48003000b00c01540d601c9111210450301c0c00d0004131865150800340301e142c261070495a0381d1202000e2081c9184a09001003041000207665030902c442444034601800c0455010301c20100145000900984140e8440c0c0c40c0703202c2d0001080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 857380350 1250 857379100 857379109
    0x5072d0201050c070317120c03220f08030a061410082a0703030209041514060a050415030623030705040f1b020d1101090c050108090304170d030e060411 67
    0x501d03074403c102c404403910303a91102c080003040d480742011800c02040c81c1c2c03038802407201c6141c0c0c49041440b0850561814503100c03078621030b541d0030003810f015800c0300d00d90038402107120070250250001e9800350b03242070400c1008020141e0b44503003140010080790400311407426071141c0d01001019a01e46032991104090300310b00851156041070501041403602e91401ca0600c09011203500035240141c440e040c81051006950106030280d20041342502c003400f0f044001032030005501d82c15142d0f01d484041003c815540781c40744d42c0191600580c3c0380340360b602a5038140c120b0003e40b105030280c24400c80c000c110480031600300f02d032002d40c16040280301307011505042d442105142c28415010030a010000880328010302d80c0040c1c030f030051304a54554500550004031a180c510b80040080000014544a00c00320410900405e03040203803940216480803010130551f0f025009011050350343d4840504c400b9503c03038201c00b0341e10200303040003200680701d80302040c0f5500c2290842e6082c0d1010b10a5002c02 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 857381600 1250 857380350 857380357
    0x21203090703120c05010c0203090a09050603060c09010513090c02160b030106052505060609010f1811070b13020a06050301060c140f2a1c151b05072d020105 69
    0xf14100200b2850003400b0881c24051890008050380155a617138208600740003031180c45821030700c0004e05000500415480001e00150f10202c0c190549031201c100000403038481c401c4401441ea0181030400c049400180c07940401c0c6803052a40850b82d1545604142d03420000d02e40c4103007101c004090004111036800351004140a808400e0a620744003d541201c10a030394403002d0698003a4003040c10001a800e04819180c05081d01c030000101c618035107501506517203c4429a45a2035454000010240314900d00b034079035160740000d8480103407500c8060140c090520020991142100c11000190b2600034401ca9051303440c00d40c2e915100b650191603a4600810f5543d0360b01c00c62145255520f10b1240c1801000500e103001c0c4e80310754002c1c28481c074244401d184d48055030f10501c09802e114280c410305030300300c40040303a200a242401640c100384c41e000904040142d0702d25003900b2281e5190141e403200090000500c01c1c001d180002d50140b400d0408020f80750500310b06a203541d011800550b0248026 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 857382850 1250 857381600 857381633
    0xf0f06082b1d040c030203090c120a030302070c031707031d0928020a0906090815041407090f02030708070201060302030d321c0b060714011803020d021203090703 71
    0x600091010030041002c0f5000c113031300b0300c0020307501100b400f0f04032106200c00b1061031003c5611500290500680b180c403149443c2c0010300b1725a001580004204035003a441c2c00a6402ca0b8014030700904100842e101c95000c040308400041441c0080348510790442224484858003910000f41c5030348514011001401c0768001c1030340c2c2c410841444845203880d0004000c4c0d030010740d8400130b560340307000d8002e42000c01c40d4002c41c03495001007042d410300c2002a6100e640c800e4002c800d440c00c426030503410504040c41038001c84003d609003e800c520880071034008500902c245d48c1c9412069480751000ca00301c5441e404025850340001042000c200d01c12141441c40c02c103802942c1c03044c41d0305106d45003142440361104507042ea80120f4415a0301e0b003020f11110905410314000d1080300d1507000040c00c2442030030070081c910188140c02004a50096215100081751540101045205401c019540b6521302d0410030040c8074500ea00c4a402c624a415207020b04010801024135038256a0781068842103140d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 857384100 1250 857382850 857382887
    0x1103010b09090705010e090108100507050706021809010b12070e040b0901031a011a0a050d0b030610090e01020c031611060d0501030303060509011d0402040f0f06082b 73
    0x100c0140603600c0c1110741e801002040300410000745454000f4094115078100c05104822060040009038804201072142d00351442c80003405a076480b000f0744031030085c0000501035603c0030400e03801c10050f00c0300d41e084001d4100d500c8056aa07803901c0b82071261040d0b100c030100c031000250205084a010f0070304c10b243e03604010300204030001040c3c0130400f6101c091b030068076200c00002c9421003050505210324090710381d01c400d800c3e0180211700842c4085c80358403403c000700304002400160300c0280341d00c80e04019200800703076500c1d41080d4070315180e184011300441d01040e00d400120340c503001c814030845c0c1c0f100c45100f000c1c50600c1c105408003014000c54080070b41b00b80d20903c5003842e40f039a1b09401040404007030380d400a083d50450500808446040d0009030040d000c41e4010b200462481100350116401a500500c840c0e540b44046000f90000780005001103080420003201e0b1007603a08540c007500c81d081c080b07230780001a2441c1d084845030751000140c26024210303030302517803030744143d4079844400c1c0d5a0b00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 857385350 1250 857384100 857384111
    0xa0204080f0309100201020c1c03090b0a0506010e03060714090f090103030206100501080121061512020f04020a0c23060c12070212030106050c010603081912110304110301 75
    0x20100d0381098103540803000c0d207810001d4000c16615092009007144201e910085081c203180500d030b1681e42160440500071800b180d4241c2840da4031a0b004022030135840f4007201080d0409502d1f07240949400e6a001f07010402a10510400b42000110540b141409a450700203410005111145d10744c491581c103500f246524545000541750411154001c612a900410035403074a0b0b44100b108100d160021030404c1802001044160f0014149a07000307801015114103c440e5403070100018034404042e2650b01400f036800140c40e56411006c140014001d8510b268880031100800c022441606a1b50010640c00c0801a000c1059162a5601880801842202020800300144c03403c0c03070450b5006a16080012000d09403501c8a2035680c120701d10340001c141031300b081410070b022400140620020400d01081d0002041000d4214100442e0051100c0342e9070014840b0141e1410880800030b404240400f410300d4004000340325172207283c24280350580c2182c85a59840e0a5504c031181d03100e81c590b4032103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 857386600 1250 857385350 857385359
    0x1311060a1205040c1809030504090c0c050a0309050a0b1614031309021b030a0215060d0812090c030a050703030e06210f01060f0c12110303010b0d150305030904050a0204 74
    0x910078a03000d41d01a041a00e113051510080e20001d05404100314002c60070089120006a00072003a2030a80361081000700b608400f0043c11154a0381442d8041c1c101d1154583c80d006054204a503d404e441003035600c0b001e000d484114232522031048411480e10368041c5016440070508005404502c413490809413443d003100041400a03440c0c441d0015401303180c0c0042c1c002c1d03102c3c04c3c03046881030060480f4091801c040c980100691120809502c20400c5006040003504941e01c0300c1c00003207003c0c0c1c001e20007515928518200403141c00101c0750110248140000000e071842e002604d0384040760302c80c0081804609681c0c00703c0b10f0a210055554000d00c0070711072500c08414100441103076084504541d01d261410090f0002800c4040e40800d0600c1402e414440c80d5680c01003002071429007200ca103c1c02c15080710320403200740905080032001804044004a0881164402804101c640c00780034081c8a041680104000391544001449036008100e0b00d003c504154000c1540401341003801424566103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 857387850 1250 857386600 857386637
    0x200f070c09051e090322050301020f0702043b01020f030712050601180e0c090d0f0302070506160308090c0402160204061a0a081803120601081311060a 66
    0x641012401d191500b0400c99900e441001c0c840038010392410b0801c150400f261515245d00c5030b0000f510b0307500780904080c2080107040c80600020903016000b1542e885100da01e003446900603d070308074880c1d41031400107601d280031414070002c4424546a8481d00c0c9940a040050700e0b03481000c090103554090103c0c0a01e064580c000e5441121242c0310300207616261901141190402003240341800008050001740042c040c9103074054030b041c01031030007081d124085845400c4c09001483d1f076020130f42c00d00340c604110300c18180024061003a0215242a40c540c0c08201c0c590088020042c02e000740780c450107010038401c00107240c0241401c07056039911116000414240e0703105071b81d03061568203049010003c50038648030f0b400003403136915443c1c804108902e188062038421719652070200f001d0580820804882148002a02c1000001300c1e6500d2286d04031451150004031082400308050100080740342645241c6004816442014040c4003034a54081020030b030048140702c420804070703a0817405020031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 857389100 1250 857387850 857387873
    0xa050a0905180402190e130302030f210907030b040206160c0602030a02161404091b080714010e030c09100503060903090a0501090803030c030c071b05010e04200f07 72
    0x5448a40c0c2d161403826006105400e010680f0381c11034818480d004201d14103500000c50b80101326000a004103c4507800c0032465800351640a4803103040c0020016041c1440b600303901d003800703480c01103901e4540ea81c0444540324001444060040c04c9404001801450204c1c010b0042c0810002d0006003023055032070303103004074030b0503002003025a00000c0c90301481070301004014585501482d61914841c106801e407441c0840d5061021700864407103012004101028032801c650b0803080313144003c06941c40e5500c5a032075516114004543c40011649041035100c0c8528601007a0054000c0c0000b810200a004031010000c04409051007012000300e000d640074400f885c050040c050017107841e08030400030042071080c5a0f220038144552540b00308161726020003501da000c4000700203140c50359102c409a040d1403041e408001c000312800400d2243e5101d02440d6481618000e17690440080840030501003182c08800d039a03d11882d41100c2d8002c118015402081880c403818095401c087c440d42d80d10001c00b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 857390350 1250 857389100 857389129
    0x100e13060b0c0f010b12151503030d020406140a0516020307092f03010312052203060c030c1112030a0f0c080906130b01261009030e040b060a050a0905 66
    0x30400202d01814140174010206a03a1045428080e400c5200211581d1101d1429055032441e80c00ea001552a40f04030808001180000d400d480d9942c21407041d10303000350306c98080d03500410411031080c81d101040c01c0c2079070200c590700d864140c5030625450380d4070700d82c0d94030280c00c0741d2601c01e1200c0826090400d00803c420604030010055540c50002d550115200b10b8440440b03807060140010004503a00101c0e101292190b400d10307035520445d600c03406010311002a941076036803490400000801899911585400000340da0402403c1e0110200300c60740c80e201d10031040707194003c2c80b4507800112034400843e0410340c41140090200385a11150007683c44845110f40817079411000c0019409050001f90386c40102c0700f0404000850b980e80301942c0d09818010a0100c1c42e000d101000400c000400300e00c8480d60307071003c0f500c000108503000005003107242d10480000e51800c41100341c1c1c4c281800782c1c400721030008060038103000041d8400c4a02c0e0b04203540e0701c01000582400022140c40d0002160345a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 857391600 1250 857390350 857390353
    0x1b1b09020702040605030a0215130b1b010b120304051306120606080f0f0615060c0a0507090c02070e010623120f061206010e0601090b040b0414100e13060b0c 69
    0x401e518010001180c1c0d80d40d00190094000c0c1555500603956100030304000d29003040c50076121018041d0803136207592141c10a145030803002400040c0000c182248500c41041c0700002c4c41040da54030305000101c49052400d0407168005e00040c0002d02e441c03541d808802d00d8091000031401d595080344108a904200207070340c3c0e10b56510041c050f1354030510080c0e044401d450020b000400303402d100e5035550380004080442045480803402da403a03444a00702c600720150303c2c08450480100d820460b4642da2541f03d1a000c243c603043e8030500035800820120f0440b1201800410b4580ca4014291105810343ca124040030f4120780e4003011441520000d0314400c9421803070840d0903d030881c0110034000d8003904842c0302d41030400d03900309000344c0002c2d01ca054400600c066141074070f0701c0005845281f000d40221503c0140440e000c64003c15400c003a204540e418030342c40411842c5003082c00058649242030b20006413000c96203040500305006424406218a4070000710a81d48040b0001c840c0c20030081c03100607 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 857392850 1250 857391600 857391607
    0x923040614090a0b040602030406060905071215051305070c050a030806152b181b0621110d0501080109200102030d050907030b0c040603050106030c1b1b0902 69
    0x6210500380351580b00074080300070a240c402c95103d00a441c030340108003d00c4a0f0f00000000c080149642190000706031446041c0858142100003811000d40b141500c416249071080141480031008080d000312036015004680300c2040d00790b800060704008181a060202000120001035010001114007d01039070301d911031070510000b04101c20341300c0d11050503000001d02100165a907809a0300088a44242600e002118080200c4024120882e206600447e0f552030714018031448150441181105846030b089580d2210b506807100c0b11f4a2441c0001c2c00c800c0d10307075a04103010b103501800c4d091405006940c14000a14040c6043d50000d800c0340725542d455a080340200600c01180b940f1039a01042c0501d460700c520f0000075681c0c043c148145c0485071710f51000c128044001c1c00880080d6030400604440e51404003180d00440d4001d20400001038613100c00043c1c403601c24411030340038518036561016540a031402d0003480c40138500c1e0669429108001000d000c80c401ca54002c011304401401584 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 857394100 1250 857392850 857392871
    0x8010609080601060f030c02070b0f1809220312020307110c10052a0706030e1005040f020906061201080c040b0a140904210e040b01030b0a09230406 65
    0x104180981c440040d6034054001031000c6904a62070843d0040e05290001c0d40020f002c0c000ca181c8540d07075109010100c000645401c1c11f8510200800e40d10701483c0e101ba861041c3c00c0280310b01740c1b004498000d403031501004101c0365098891000003000b0300a01d4107100702544c981a0100702d0740207540410125610700c4411254100600bc2021045411604140320050a01d0081c0c1617202c1c0c0b0178a0fa1303c04070381d8010400380c526900801103800d011501100c03003564903030744041c00402c8410988810303032148650403884103015000d030510917075001503008100034080e42030042002010303000552001042c80613290101214482ca8000e01c4004010300120b507240701480211403a84416502844402809114100251000d1065500d013a00d0311800c0fa0303210700f82404196401101d142c6886910000708041d107074400d0013076101c14400c0780c08001504480c4015012501e6036495185c210113090340401900170340340c0c4a441020051140503105007010a20b030310301c61100b11021a00c40d0f564003c04003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 857395350 1250 857394100 857394107
    0x9052509030b0903070312050702122719050f011e0305100609060e091302090709030219180507120608030c010e03090303071707020a0e0f0603011e15050d03080106 72
    0x243c0200d000c8000e18503088613a10020b21890f00b002e041150207842c3c1c00030071131040c420400f2080680310326004c0307074881c64143c00322a070194903042d0014266070400c56400315480c10800141030060143d0202d0701c654034050501462810f0301c414241403103131070050280740e80c044560000d00c49040c1d81e4002040d2610f64502030a4440caa0002000c10040640500c080764008a46802900003280c0c2130039103039078003500340400c1480000003c1d000421841401909a0400b11460959100301c80a1462226042d015415150b641c4104071070406a2801c184089800e0340c840c1d0b41002562410381503c41001110800b0740b0410380c000002a44000f4554400c05401c1c41410180041c00002d5840d1200c004000383d9a0300400a000d80070705100001402080c0f120f20803144c1c419400b4000401c6a03a4070392420781180c2d0100c2e01c52a040710700800003a242d00d17062041410102c1c1c245040d6040e4143c1c40c509800902e20140240b080743c031022004038080d07851049240c0154030998640c2025810614000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 857396600 1250 857395350 857395373
    0x60b12010902270310020403030f09081902130902060a0905150c0a0b071205010b0316080610051e1227211e190203090a0905250903 58
    0x1024542c0305002c9101c101102206143c540c40c901900141250f50703c0d40000e00307000d180b1030a201c0180c40001e00100b0160400e0307925030056030a03151042d90658400318281c403030103204081411807403448290340042c54441c40d004449440d107100012007140550100e9110741c01480c8160104000410402c43c910f0002107050100310318460ba6803c0002120040c3e070b603600c02c074200030984016080007492681c07184507107002c8508070000503c43c95030b5072400050760340c0c01a18401c0c4c4180c05401c1212480d070080740ca043c003401c03014000c01e03503041c10300c44d0454039a00606006403500c03400180000c60f80c0e07030769805003a042e82d80c2031301c0607082d0400000081d03494160b0447c0e8202d1011152030340000c61004102d81d072038040c01543d004000180c030020746c5c805101c0e078881e045442d2210480c000304040b610300038000035225501d0030f0000060494090380c0d2802810200c69000900340800c0c0402507490300a030350808400c0f110b004a60b000841e036944400d00c44010307040020103411041060000c0003460 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 857397850 1250 857396600 857396609
    0x70203101a04140402010c1e1109180d0302030a1508030a110a0c12031209150e03090a0b070c050a0306090209060603010e0402040506012303010e0a0b10080a090204060b1201 76
    0x822840741c0d00f4190700308241c0010800390600810700b0b150018060300a0840a4100e14400203040c01e15085c50103015a60000b04100d004032022000500c8601820080c00000700c0c1c400e00610249036245800c130060741c030040141e824241c032040b8203482011400e08100c05842c4203005151184070702d0b0380040401220314640c0445600c0f2002040c0440c81c1c6007140d03800e4526245d441d4290418505054582e8005c0100041016203080940001e00a154150140c0c0181e40f00080c4030070a04460407a581307014803034a00d503008a664008000901e4180300038064507214110003001156500e000030600e41c0d4035841510401e0315011044114a23214954684c452003c6410070308650503c9075070401210001c0000b802036986002140c051380c002e208040d801c400c2d10402940c0c180e24606604103e400c20b00c24860085410000b058080c2100d0003020300110000e041c1c1003080740c0309101159640c00140810f1256a60361000b4400358072680944406031864407801d42d66040c2c4000d503484440d00c161b21 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 857399100 1250 857397850 857397859
    0xf170d0608160b12100320100201020c0c090910020f040303120c0c03030b0316170606040e0606090a020409020a05040501180e150402281e1e0203070203101a 69
    0x5000400200040e5015044c810304046115651520b0007a85404503800c040c0000c0040600300c0000955540201d201d00030a85c1c0f82e2140d406a02000d0f800c0c4c0c0107103099401c8580201c0341c080032506142c210103074064480c1c4115180d244811054a003264007600c2003000010000038240281074001c0c60980c01c6807008002003050f41000c02e401071104600080c01820162030b803c0402c07031950204101040e203441c406000c4002c40d41c030070340041040d44000c41c050581c02000006800303880d0510420a201c1e01c090050200365070360400b000501c4034000e05102c2c40603130920003c2280d0a0358806071001120a132500da568508090000d0103008900340203040c0300300000c030140b182c0c1031006401c07a00a070b000c00c1c400c1315070a8031000140281c01001d00c4004160030701e4604e40c1a08411009400c4900307026203403483c03180c12801c01c0d2210132010381042404078280c50000070103040d402801c0c0300c0710302a900c1940d04010881d17002034200101c103049281065103072844d50740c000e03404018400e2001400ca5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 857400350 1250 857399100 857399143
    0x1903020c091008150a02190509040e1504080f070606081501140f060904090b040b041b06080708100308130806010923060301060506120a140408070f170d0608 69
    0x103c140e0f0b40c81295145a501d03119501c80030540416694050300c15080c407900381c0d0307001c480182c10001c0003a0403101800748039504041420198600104141010030b40c007001d0704040d40e8403a00c48156607401130b850030302d103c84100066404a8541c0c85020043c1110002802e5442d1080c1c010042d043c0041c0c100841580d8403001da41c5803595a41e1030220b00400607900141c0703810115000800906015501605e2802e0805c200010040c0810f0380e180b00340d00c40c40c0194007810b003030040075030300030398600482001c143c0e00404203c0240c0030ba8103495002c4880c44013411010f803245d4880d881e9400444c0d28601003505081c0500c0344407014006280034098640c010032010000c400c1c020040740b800001205045102c1e03001c2074a60300c0c29000300c0d000d0100600301d00d550f0700c0d5052602c0d0550200712194094a49031009044001a00308080c60141d90083c00041c1800780c0703a101c10442c5105400112410400d000119170008904000740000680000c0c001400c40d250210160400070070130f0301c8160507080e01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 857401600 1250 857400350 857400359
    0x130219030507081504062102040606051608070204090f0f03030506010e0f1e0901080a050c060414040c1e0309140a230c03120c011811010f021903020c0910 68
    0x80f2206900482c0c18a041c2c4104201c030000c0380c001e1520b500b02945900c182a90f80c1c2caa9054400d007038619900c00c0c1c0c3d04003c03072580c4e0b400485160107042ca50400d60920b4425050110f4018005408c01a00040000580e02c10741d6554600d40c901a00c3c04131101103258800800741074041c030402e0780c86082802c1c05040400361400161501000c9225248100f000b5190556030302d40b8850404601c4202414040311961140706d196620274649208070344501c00d41c220420349040500917a030440340358071243c4091100d01000c010181c01740214410400c5880c000c4070720021002c1040c1d188914103502c0004502d590307030500a10526000444208561015101d01d0024ac41507800290708210b412070310301c241c8003088803e410440f02446c8070b90700d0300c00e1036100d84402c2c3d110001464601344420082062940c0c852840c034902441050203880002e010300c0030161940507200c03261a280d002d1040c0c8990ba0042c0750024090200314900ba001039214100544442c104244183c0c0c010019826104455141 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 857402850 1250 857401600 857401607
    0x8042906040c09050904082a0d030c05160b090c030a110603060111030d0221041212020409060906080634200c09010b07020d020d030e130219030507 65
    0x10300300d140120b603210644400c4a10508400f005060020480040ea007031900340000650007881000441c40c002e02c03905404202d401140300c01902c040000341818851441040c0e0042a00307041690a0020402c62419080845c0345030745181032041e600d044090902c0001d43c0d292071846450b940c000d074000c024550201d4030401b0300414800d07007282c0503981c0340e5805004803002c0030100b00c8501c1a10020030b00b4240181c6079000761920301003058155141c0840c2c400703003c2c02d40409940c007800d900ca490700d47c1030b07c44c0d208003001090000c00301400b42c90582d0b00c104000848030690300004030142d4481050003c0e075803c0c001d0036001030001c0c00c1008820191054134441501920500d410600094150601640110764005c05540d4100d8100e00ca4cc0c90740c0000d41d207800204002c1846545c2200003c1281c0c1e41c0070040c0d40e902a0041c0c1044c400701503642c2400301d01140380d1415401c1c0a804100c801c1d85550b40300346600000002040940c0720114000408064a00f02078503000745401d000c02c10550592 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 857404100 1250 857402850 857402933
    0x60f030807020303070b0a0b04150e071d0a030809150406090b0d060b0703020102030f07090810020315210d0c08090d02010c122d0813030e060304030804 67
    0x30021042596103115200007842c500c9400c50041000d450301d41007101d0113125900c09a411441910705100242c02c1103600300c0580110302942032889002d9010038011792083c1008103550328054070902d00040c04400254041d900741d8000c0350a24800285001035092102d0307100c3c0d10f511456555410305042ca100a807c00c80e140c0180090b11002240ca074200034510b810440c01842003c1001d903071030180d801d0080c080d5004981000708840c407500030441035442450100210340080e07001e401c11140310b00c1e00c6406588040d00c28440d00386d136601d10048503a10000409045036102c04000c18070010580542d003050030915190b4248170701c5030503034000f04000780200c03010a0b00441d40d502d01c000e07043c401611090404800034014006200b400000c45810983c551008445510000103120141120706803100842090b03c0005036010f001c01d91440481c4500065a40300742815000550381401280c1107030400c4034181d000850f980b060000703200c10034103e101a2445031002c2d601c850072101e0a130708440c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 857405350 1250 857404100 857404103
    0x60301050d05030405040501170c0f0114090102010b09090d1202271909051e04020303040e060a24140909010e0601140712080618040b0a09120f02010e01060f03 70
    0xd070407100442044020f000f181c0240c50b000300104140d58547d1200c43c506601c508490850744120296951985410a8191000d5030305958425803030a20750800d0704583c102803100c40c117640d03d500c055466a503620304158403d04855005088010280d2b5009110351085903404120503c1044030790f02803000712400c8451503814605244005100d02c01043d01001240340e8000c1d0a5111140807520050541140c1d02588840c40e0b10b507814000f9010045912100b610001d41c194410001081034103c4440096030119000f002c01c000d40b0b507980c02c041e4465102602030101c14140b80200740481e500f10b980c07034450141c8210801d0a0242c28000b0900c0c0040601440110303072520000615140e1040703150b0302c210360811b0201030300c810940c075006c00f0141ca0304c044500403420300400150a8207200000340b0000307518110f43d2406490b0740e250000f0b521000703444600c40365110009100402c914803003201000071140c0d180d510810422100900311418007981200c4c5034103280040100015000314102501e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 857406600 1250 857405350 857405359
    0x120c050105031909030f090515071106070f05010c0914220f020a1107050d0b070f020a0b04051f0219140d050906190c080403120f18020a0f0506030105 66
    0x2902c400c5101c0d000c40091122103040f45040100c4035081581c4410714109140c00da880340c1180355183c0040080b4840c0c2c03800c030b00d040346106000c64404181e1144202900c01e4000c0c004501c2e050140c6c07640301c0b045003421b8040c3c0c1d044e074403034680c1d403240c0c3c7d88407e06c000106013a0358030303202e941c2c1c5040001c4e800c001c8481b610b60000c01251650020705181d0341c001c600400c2040011996a41a800003504041e4003072607060b600c0c00342c040000780c582040140c1d944110380c01003048000d81d4501070151040e100c9400010118820035003130700c000845009c40c070b40c007076405500286990700d10203026807040c1410040c000907031070061000e41d414a6910b0b8000960182c542003070000081029001c0050703018024842c0301e290b09003804d00a080c0000300340c560140d4800d014614542e0f80380c81d0040151400c080583e00007076a0140018080380c895001c030181d502c56a1800f203003510710234001200340c403180a50b03510581092620402185000c882c00b000804d024580e00ba80d561412000034803a010511500e4000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 857407850 1250 857406600 857406607
    0x1110715090b19110c010f0f06080d050315040603081815250c0e1b070c060e0d0c0e22050d050a0c08030f04020a06030506150c010b0301020304050102090a120c050105 73
    0x300d2a054004c0440e454583e012940c480f814040c0340c030302034180d01d00190552442e01c200a0540c246074001c0600f962742e070324000e00c4807a10500701141d040c0d02c010100c903010001c0d4004580d0701d50f11030007220000c501641c070f120344484c100e443d403680701d90041c1c4030148036201d820700502010344c41000f902c0d50445007801c003000842450a0516082e13900540090418103d4030000c50032141c5280903d01a0700454020104040c1c5020b0394103491251400141482003040010419113104409070f007117054020b03040054043c00c5a45400b900364080e0041411032041d40c0400c10407030b600b110449425149100c0d554202c00c02500d4094840d4603049440040005c001201d400460142d01d10707481d49507010101950742d151038010480425420f4070124441c080082c400180280f0a01902d8002c282c020036503151005500c4500f0341c40d500420f0049025522060000c026907000e1001d58480c3e40588000340c0d480408004000c401d08031608170600f112030301803812011600b8000c40200369603007130821075074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 857409100 1250 857407850 857407891
    0x16020f0715032919050306090604050c0a0308040b0348090d060506031203070e0f090c12070e0a030c031b030c06081005090c070c0807150c06020c01110715090b 70
    0x90304d85411960700342c810b4805000008000180c0c1c603104600500c01d84103210040000c000d0008050b11025056040038801800050b48800056412007040c540142e94010424200c55070000c2e10140c580f85110603c0054a0010b100342c00c501c210f013000158245440c40c0840000d81e814800000580802da56038000307841520100f000c1d440d10b0f0000000e0f9a00d925051000070422004c54414034040d5030000b10300c0090781440d100b518010609080c0c40d6080805c0c2e01c2c0c00305400342c0b0081c0740700104000c0203040d40080e01c136040d105c03001d907000300c045420481c210304100031441485425641120869402000440c00c0600094142e80303841c034090485883d02100000e80350002e805c9681c1c040044000d201001c1e003400b00408441d48140403410341a982d582a5549990032482030035214525481200807041c031450f5100c0040d88219001820b01d80c4901e5407500310f0300c00d004240825500021101c00f4014007203920700d0028480d10007807049005994440d48180700140020a100600d80380144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 857410350 1250 857409100 857409139
    0x150e3603070b130c030804061e09030b07140d0f05101a0a050408070b090111301201060801060207080307083f07120e0616020f07150329 60
    0x42a19030072082101c4c08613200e003806801340d4018400c000c08221090034210400b25002c03202401c0f80e20035110407900303d15545a869000400401c01c03004c00036208840c03641e842011004e440941c01e907003000100504c032581500c0c06c4400140c000030001a0100b000c00003030311400d40700b05940b1003200c4000e459405060041c3c0e1180100d4000702010700450360081082103035080a0300111101740c3c2c4417100141c00800300c603140c00302030003840c0080541040c08200c803840e004090280d80d8030b0b000314030300d0b28a02100147c14001c2c2a0030007030005200d04010050644e040015038040c014034805145010325990350740400c0d100e00c0400b0328401640c4009041402011420001c00f00c2c03040100000c0c444540c038450744103410071600b03e8081803c2e00c0155001c09035620a4088001010004109a0300c4130400c25034035090100a041c214428450030f10000903003400407100038100040c082e6030710800c0040150540d80c40c0e04240c8443c080d14030021b090f01c003501c80390200c1c0000940e071240d14440540b0340d00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 857411600 1250 857410350 857410381
    0x5270607060204031505060904020d0321090f0201170f0f04080702040906051b070804050402030c0403020d0b04050706030c02030a0e01111b19050310150e3603070b 72
    0x5050320703201080000520030005e285407071640c04c201c4204042d036102c2d410008001e00a941c065004060007058800182c01041e40034508000e980d941c800084154207070100362040600708031032042400c1030308400c6507044071000c070f013048070302c0700c40d1506107407030042d81d144483c00405508c0c0050641000c50107014480040f0741946402400c14400c0000508001028090a449c06c04440d0310454651050015007026501c00d04c0e80085164901032600f810440a50400ba09450188508000000c0113035200c94010200302c2c49001030405928280c02c0c00c504107000f036030010050500703008504540c05c1d408021215075181c1c50400e035002c1d24118004940041c0060141c4900303104128000001517501c2e0b00e10704440740121000f80418003101141d520f07603011449005e4040c0d0042030002c1500d10190400340d800c10484504884c0c80d030740c900041010000989001020f036298020803180c201031021424060203840e400d50407501d0103d03c2e500d40d207201e03104029060071601b40c0460b9402c0c1022420 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 857412850 1250 857411600 857411603
    0x1f0c02060d020a0e04021c051509090f06061c150f0e101104080d0c0623060306090606060301061409090c130801091e03050d0f0b0a0605270607 63
    0x201d48803111864060020362081c0800404074445808509945c82d15008440007003000540d40c3e030708800c074200c0c00005803502901c4680840444858441a600d42c1c0d040141709203a650002c004007504c646e126414400090b01150082e4450100300800d0002c004940740b01c5a4000d20344c84031540d000c45113a00404100b0b41300041d050402c101192019000100500c828000344010400e801e51000100010f118512445030203030000104041d4480c017400d04a0101402503201044900900690b10702043c074401e49409206109030030710000303040030062076900c0b1003544000d1600c1d0400b500080d001d400144290800c01000540a2600303501352820750705d1154010f49440e1050070b01c8586001550001860000301083c04100018032400501074000d030706800124869202071000d003003481950307200c40e043d0305100f0208001806003045104262416031400700008442c0405801c000c440520b9034031034410003100b80250910140c03681440c10038040c000c8041021008404081000c50049000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 857414100 1250 857412850 857412859
    0x92b150f0f0510090501030c060828050130080c010605030f0607020127020f010c12180803040b030a09062d0b041a0d050c040f0209040605010e1f0c02 66
    0x5060441407864010341c0c02007040aa2200000d41c0f035060107030841e0800d1001a2504182543c1000716034010540a5044000d21101300800c1e80030300a5801c0c00c044540c100384405641d2401040030b142c050b40248800c40d41700c448004040f002480c040c3c0e12a80242c1c0241500c6030006651140d00c0c0c00354040c00043c00d018007a105580002600c1036181d403011070b4141d000d1b50801c0040714502100450391001d960310b050288403001c155400303000100c01c0103156503040c4140425080042500d1000201030141641c1e902c0090b10305202e552400c480c1c0e07507030110403654810321052282a40718000d80350303c01001480090700c03d8107410403034094602c415100e2050488221104890340a51040c0b07100125030710310501100f0342c01000e0004954642000d080c044ca10b42c00360b880c09181c401102c5510701c1c010b00403200032940c4800000d048511030061300902550000342c00000d03041070301030382e0000c11f42400c043c4007800c0290040340070301a510100031a59164550500307040c501608850204e181c0141 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 857415350 1250 857414100 857414111
    0x30a05010504060c050304031e02240405011104061407021c080a020f070b0702010810080616020118020f060c1203040f050c0a06230c010c0302092b150f 67
    0x1821802440150b40940d2a2420701003561069801141124016a0b1507928071003400303802d92600c3c21341d03d4840035500c11400303a85c50b50103402c0840b1034081d241d2411044062900e08240c64843d0850f03940b01518030344005c0c203204c20801d1076002103512410384032100b03a29580d08a180f00081002c808280a030800c0c0340007010702810b00120801410441c9280e8088400000c07094114036920786051050076172442d0b0412422006512648a45801c00301010b1401b4400d170300da02801e400c040302203135440359805840705003404296090040c981c3c0050380284e0300c1e20325510354020651034010029194061480000c0350045400300300f00c4903d1007030a5100d80341e00c9007094030b840ea00e03900601c00180d65521402006071414906240c458080b02c510751601580323071588040740011041d99101c12400010b090011840784030007805400050041c0780e4005a8400180c0d0805c140c8035940c110005c0d06500201d01c503240d81c0d45582d60424180c3d00000000c06038600001e031080502610103c41440a0401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 857416600 1250 857415350 857415353
    0x70507080703060212101202040b06070c06120c0528090e0406090b06031b0f0f03030313060606211a061215011107050f03250510030209030a150b030a 66
    0xc1d8044e01c029245951201c48a0301c6c0e80380c41c2c0c0c101034114003030450b040b100c43c0810001071602e540640450b00d006001d05040034059200c000c2c500e0140e5100802207114111040c580f400c1600c11000b006055007040d5003041316210180054000300021200e009d03503a009041c1d892401048490004c1a0551811584e45064600440a04028041203130031a010720045104c504c0d0108088081018074024076000344450b0040040714103e40040b145c0059a070f1950f039100d17071814001148900180500c100b0311441e1807078841c044035503a0b40701e503041181c507aa610002205500c7c4440c094855690040b800d1549507520641c1d4101a40354144d00010000d003031000c0300d1042124501c5810090035816024080c40010b50340289590400d54042d0890781041c0500d190210500b803102d6000380440d80c080103542e100d05440f42c0441c030180f00300c0041c8030b8200a81d1034904118008042c071840d00f517040c108800d0129594048030100102540c183d80002d2800302c5c040c3c1e001001a540041c2150603a110700e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 857417850 1250 857416600 857416613
    0x30603020102070909050a1b090c080411040e060a050a020d0c020c0316120b36010e0a02090a020306040e2e05010510050f0c060f0609070f080a02070507080703 70
    0x49110480c05805641c100040ca04150b20a00034800d0b08200a81040045540c41d04060000070400c0101507500300c04c085101e100f64800c109040c2c0135511500100d0900d170500700d240c03001c100403007845282020300c10390402c040403d001c1c0c0c20500d0802c000c51030740c40700000d0002900450740e0382c85c051031428168140693f40080e000340441030035400e0701c1a13601281c0c9008030900785400340f001c4800c4e2801d0072100007400a410070341e0191140740102070126400c13034a040d0710001c0418001d1030030660100d41280403000e124a160003414100100014031441d0b002c0344020100a0100603c01d5011000441c56155508060b40d04241c40c8151500611780a000540c81007002d00c543c02000c980e02428070700100306105180c141c4400520102254000f09411602640507440c45285200c05201c040c41065040007214042c0e400c40f01071307080303d190a078140215084010000000c00c07240300c049800703c68004d01e9068024100080140e51000715041c10f525100d0203500c518800d100d03841000091008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 857419100 1250 857417850 857417861
    0x303241e09040807170415021b0d140d0c140303060108040b180d0320180906060f0f04060e04051003060c090503070b0c16060e0f13050f0910090c03080f120703 70
    0x10321820303000d0400303040400300e03981d1405a127030344d60003088400e919400d403920180b03100000d4421507614540b280340c0d00704181000e4100c500000843c034040008820030001c040e00064070141d030380c029400d44c5000b200081400e0720203080a8030810002e07011400480100c1d056150103c004001c8503151100c02900900a0944a24a80d142d9810f06808031946051070129a480e030054504459a0409071007005100d00c000b0b03241c191b01002c1001800c049032408409040a0f00b0451842512903190080181c00d46111848041c03159103030404020001c10441d500c04203507504a2400a41d1381141c0405503041c3d02e46401090b8035100750100020765410a600031f00c1c2c401c0c0c024003540d00c40c410030384501c1404c0d0f255010350b0020407a4442110302c1400c1400394007854000007000740c04078041400b040012030300c05840e00d1a00e18400c80030010800c20402403c1040141c040c4208445c20381a00c03580341003140ac0c04018100c640000780480210807603019202d2030004c9440c208864180020302400510 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 857420350 1250 857419100 857419109
    0x20906120f07020706081f120c09050a141302061c051f030201230f16030807110309130b0418112403060d050303241e090408071704 58
    0x4207104006515644045202c1d0100d0701d494994401c25199455a81070301a1550010f20040318592400283c032590510414486801030951480b0241400d40d81ca0503588020f041501d280d090580b110050281c1420b0a40e01038180220f5407404141880000c000b40f08145c01e20b004420309102c01000007110f5401070b8092459040d154440c1406080d241424017054407020b804a131a038004e50b10240c1520700c0c6250021100c006251511300074622040c201c1c0c000312a84002800b00090b29001c042e0805a42500b02c01c1d035042c061004901d00070081e91320710400311094058540040d2540304d840c1203400003400510700500900404080801c0207140031101d2400380c501c0e01460341100c5080c100f400c210038050035800b01000c203201c09000003504541c005440c02e604520303041d28100125034180055800b801e4181c2c0342c5401d81d201c01402007400c1e0a820201845100e0741021030f803011070809460b907042c150036985200c255032a800c00780070a01034140060082c0072aa0b00d021000000e000041041e84c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 857421600 1250 857420350 857420371
    0xb04020d02120603010b010206041509050604031e021b19030209090a050d0c0c05041e05010e10140f101202030a090b07050a020a0221030c1608060f07030f02090612 72
    0x55840000309170a0351080d0040324090307008036010038082082500014101c607400c0101140031610b80e610300313240c900c0448042d00090380031030b44100050340e00300e0105010354091009249204000c0081c0c80c1940c641d41a880c89907289030011186682410305000c0259001040c03038281d0b1030f08641440d20703590146400c594a005031040514090b02440700d011005800207940701c1e10360305110a000c01003051003881c942140c410354403c0f107820914010207000c0c1c2140d482804407400c112400c8450702d0500d8012190003024588955031030780310301e4003a5410740c100300c80c40302c980c000b08075050716100c0c81c022001c145980000204246001150003450304144211003105c0030307a86049040f0303614000d0100300ba00681000a101c405850882d0304a43c404101080681c2003040500c0c0d0315296501a04414100c0d0f0000010780140c4940c2e0b2800400502d0004044c00b003614000b04140b102c41c0c0e00070030113824155160294044800113905070707112508050542603441c13070a0203107055211812118501407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 857422850 1250 857421600 857421637
    0x10e1e0a0609060816050d0311160801200f030601033809060f1201020d02120117160902030405071203120b040c02070b09030f1e060901020405150d0b04020d02 70
    0x304140060083c00791785a420840001e181008200003803180441d00540805c140600b0a00c0b5181082c411502c1c6081c54900b00c440e0985001260760170340c1c1480781c5000c00c22050507030b00364901d484082254062040c2c04102a6207940d4500160010400a200014000c12513400c02ca00810903080b08070348105415080048600600d0030407803800030031280c241d003080000e856501c0341c0c10300a800101d4504c0040015051508511012040341c1140300031000c499035450040049900443d40c500400b43c10340081c01d03400b044007c0900d1340b482c20303210300d03295543e0000020f414003005118810107042c140c517038000e84174054107006240b511200980d407906c52400401d8441450a03210b0200210340603005005020300e400b080640da500700c11a9240c050180100380c101d00241131104250038248400d015100203000c032601031505000403c0340d00540c2c8100824012540c9241000c02105140718180d5607030540300c55100b01900c00340c1032140d0014008030b00e4000c0021283c01500401d103100c660340d400d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 857424100 1250 857422850 857422859
    0x140604030e0613090c022a0906091509070207051504060807090305061b0706022a06090703120507051f0c14030c07050703050f010f060501080906010e1e0a060906 71
    0x100c1d40705014100c2455000940c0c1007006043d25040179150a00ca030040e94030390000c030f21100000d0790890304180c82802c01d6602e861444c0c90103007001504107e0589014071203180480361048003c03030001c5003d100f816900001048103100f0001d5401030600601300091401c001c911700f000641050189001103080780300011442403040b80d503541260b4000d030041c00640c41d211030240300e032a06440344003d600000c01450011600900040c8880c42601c8981c60b46040e41d2040d01080d0158001e100179190004000c1c0030070540700144c10f0f001e0b650495001c81750314415400545140c814003200500c3d5005000844d03c0c1c6e00340d4500d4201c518036040c4010710403d49410400c03505402418100c480099081c000300d0781d48108580513060581c410303c1154040d41d100d4031180d140640700e40ca140b45a130f4459042c07041070305441c00703058002c0900b030a0840701400c0a440311512808140115824219050005034120b046d111480c40c0416107040007a030141010321a0720007500d00c0d400345140c41824807a0005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 857425350 1250 857424100 857424109
    0x3120207090e0307030917011127120d0e01030e1902010f031112040609020d050304050a140102100b190b090306161e020c040203190f0204210f140604030e 68
    0xf40e905174540c2e04e007030040342440024521144801c0244000b90750b1008a5807400c01120020a01c00200003c0f07002002d00a0741010f0030382d1605a882801118060084400e84500242c4401140e0045c10f100c0c11036528070004234002d0a2000300403da610030100910703038404440c05210300440c000c0e80e441a001c0030590041d41030341d4035a680c111014104100c3c0980c2052403c5d81d880c7c1281c4034070b1012481c484c4070303000103624070030190050b00c05400004c1c003013000e403902d100164002c02e29081188684a01e039030001c0d49400c10040000754070327a1149618030056440240e03111606490740301807040030341c458541e1120358006061a44c005d00c0f45002107000d04842010385403901400d56030b00b07032240031244e48800d005244501000254854103900c00c00b240e039503001462041240c0b522034003d50703d46401440c1602c400c0011691101c0c410803081c41041000c2e808801c4001e80d000c280400313411b85280055903400800320140c03074414030700800b43c9000c002244042c0964000d90315080314189200420 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 857426600 1250 857425350 857425357
    0x31b030a0e010606050f07060b0a030803040b071b0f0f11220f0501032316090e010b0a030308011202030c0307060507030207080d0905011d3307080d02070c03120207090e03 75
    0x510601c21b040c001e103c00150303aa04110380c402009804011066920b9960003005d03003083e0340c00c603000800003040001d4903510066500d01780245040301303240c039011610780f11007818207840c01610703405010312804180b1201b40c203d0315194601810b01650001030100310510a220001c40d030261030304000c1c00c8a00e0480742d01681d810380707400c07800501d10070403044c00318260300f1002c89107560706025089040b106a07504c64200002082d15060100300500d07550801e50840c2c000030b8071a0700c03404242c0c10500109901206a506440724090b40081c420400d00003c1e283c14084004554580301d080d0020440c00c2d0700c4800340a03010700ca902220000781c0c4841c402502c41c0c445201c3d81c0300250b0000000c128a44c4501040e06030100c0381c8009800d42c000718404204101c0542440c0060f4240c50542d00e901c4000320070101895034071081d046070801c4440d80c6c41071128419000244c6100d40c0101d001020b004c482000c100046600645c0b4802805600e000a52101100e200e00543c0c1890300800020580020049 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 857427850 1250 857426600 857426617
    0x9020c0d0e060f0715020408010902130504032003070501060f21150506060412050729310f0e0f130b2208070c050604120602031b030a0e01060605 64
    0x89040803000c0200d401c984c1c011040a440c00e541601d00507400c1c0380d041c80200082e08075540085090161070060160008008a40d1a80c00c0c2c074200812020030fa100c0c91b0040b041e4080c00c003030b0151005000750f103491402000070180c803a51900a002841081041c0108220362060021409020010b00c12410610301c01c0b03005009179441902c8020640410340c84603510010041c0003078245616005021311703c1c84020002c0b1400e600448003440582c1c030190110742d022440c44c40f881c8c40c640c00e5901c40702180c0580d010702445d034251591a5807010500c250204c0d13070400d01c20040d500117075031003040c601c01502d103100740ca040c9284000031a504040b90a219072050007001c407440c41407007165480d101c0c0c00c2401082c0801d441d1550300c9131002071142c1c5540710b1101e030007100102e4480219083c002070303405039a400a4840e62082108020b2072004203010400c41c1c0c0c02480050701d9540d40d2884030361414488442a59110000003081500c114070741c080c801c010000c6008010f02038691038159000d1140302c45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 857429100 1250 857427850 857427859
    0x102040e0a0b0112050403120f05060d15020d24080c0f06131502010b03100501050109060c060b03010504060f050f15060a0c080a0302030f0f0f04200a09020c0d0e 71
    0x41c20310303411900124980107061604000e040100d0806004848003503030120700013800b015440d405104140541d180b4402e004008001c9820030400107204181441d9004102040c80744480000220950644200310b1800e00280311981c0c8800d600b020a040e100d8601d04469002c2c0c101140d100000507184081403805010760f1000d42d00101001a16040b5040d58250714540319004500345d070035405201d28034a403580011414500b402e080600380310010169180a41c0b4007001000180c1c0d02409034021a42142800c8514460509100015221036003910b034066003048140700800c042070744860190703408d0140410081d11020144464003805540046010690828108552500200401c0502076508203405126183d58403032290703400c00000200400d03400310801403007030400d0101c99807007444407401005614107000c0d6004014400390000d03201700782d404080800a115410400300c00c0b500203204000b001e070f030741da1403002070b50003294440003a00400c90a0500c90b40182e200500c0040000c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 857430350 1250 857429100 857429129
    0x1110714060306040f09060b0f190608040516031a0115081f23030606030f03071203060e100f060507020102191a0109020a1d061902070f1403010c02010204 68
    0x20440180c0000c0e0400d6132007a0340b91495281d281592045800c814422100451404100c03010000b41c14a4442e125000e24159007010611524080038103065800c1402c0520441e20b40d42062840c0031954180300c2850702c10220003000703200040362100c1101c440c5603c400131580c0c031003d0369440b80c070108050201042484000c2000c00820040d041e000e151090030500d04c032642c8910000c0301c0d0b512003888442e906400e80cbc4400f05400d09110701740c1d000405a0081c143d00c40d1f0090303455964403840f00c0162030044282d061600c118031036000040200b511b09514060740c00c1017100a10b80030310a00c14200c0340300e4448000036a16000b48143d45107640c0503000f50030700e035080030b202e42c4000b02e07000e500b15060051888903a00080005900c1e5010702404000180c880ca0081c801034040c05220000307a89002c010120f80886981e40c0049404115011003980704140400740e0691820300940c002001c030003403051300070a200480d6544000a050120f00900c003080280100707900301d1141d80541001d840008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 857431600 1250 857430350 857430389
    0x3060c041202090619060c140331030803072001110f0d0f0c051305010203030c0d0f0603140109030915050708280302071506050a120f0b15011107 64
    0x101038542c0410051700c0b1098054144440440011090300b202d030104078000c490b20f051183c1c114440302540e00c814011882c0400d410f43c50590440c200c41401000448642c1c40210b80c000100d8185c010350b8801041605c1c0c0c2002400030b8040d4081180d42003400e86c4039003840a0b08241406003a664007400d5011a00d004020401803145911505d60099090b845107034030242c8242d94468642c0d00e0303051341d40c4d058448a000300035030b1000025921090455009009004190032020704854103803000c50000038512010014400c041c3c40d456001502480300c1201c0b608001d507040d048541028802e81e5191741d00c40c0c0711000e00c405d5140e0031440d0400120144010b0002818081c010408c442070088171917a4800000484850440172100c203400090f004101d68080003400004c04001c002a084240030150400300440d000741103501c5000320408059844a090045400c1014611134002c0354400711460100000c1d8000884041410b000030120340c040c40a10101003042d800b55052202e090701c061441 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 857432850 1250 857431600 857431609
    0x2030712090b0a0906020c071d010609080606041805010504200103050411270a09060c02011a190e0103050304050f09040f03030504210306081b0f06030a140408040503060c041202 78
    0x31380c41c00b01c17610fa60811003640d03200001c0201c40000d2507042054045442d900368000480b61040e0310100502440c3e41080c4541c10340460203540c000c01c01d80d80083c501500740e49005e07404000501c01340082d483e1005000500541001c0002c002a1084290b890301d002680110304940089a024003058249900118035141800040240002c09000d1020341075008001401c000d070f09580c25040d0541e101501d00811800b4050300c955815140001c01c410010b522595803640034030a41d151083c2e00658491845810421020700680f03114074181c0c4c6c1668603450300030364a50150184070b04c6401c9880505c8128500307041258411a403166080a283c0288d030b0301a80a44805007080301d800c4a404203a4600b440c100b2090165629644c2c0c0c04a012407074070030094103001103a452100c2c4d00c210203062240940f520020a4614407003a00c00699170352b101480180203108162040030b5a4081034207100a010204002e0010795001310280c1d80f184d15001c04940311403280e4451a0a82d41c411060400586031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 857434100 1250 857432850 857432861
    0x80d0c140309030d0507060609230907151112090d140c060703020c040e0c010903080f16030819021c0506011101022113170a020a05060a02030712090b0a 67
    0x9040007182c1c10a480d000010b4100980103006000058003c03800100348441d40c041c290052040840402400b5000d0207802c1c2c542200011702c44c500b103c2c0002148429078104030141c000c040c42d4180c0d1010a0300c8003c0241040d480300500040c0f485611500b5a10030845001c4030b0301900300a0204601c40e02e1991f5180303015180c03185000303c500940e01c0c007106584980d070003016128401d078054524070921000b000b04803440c44103002d02507402040784400f02c0c0d80007140714041d0b035002802680c0383d940400300703d401c5103e01c001c211126008030300b0b04010190021686401410200c51800c1c445c0d5200f00408201e0084005494140082d0b0542c00001d072403070350006403c4101890030100911603511794600b079034811884036039000d02c04e9400c3c2e014894107482e071903008584032610081c0b1460544880300c403202009500740c082400001c114030813a00030170404c080d00d58000141c400c0b92500026002c025001107515201282412a51400300e00b00d5200ea1600c0c540c0c010303c0b14540c0d4941c035910500606 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 857435350 1250 857434100 857434133
    0x1205043917011d1c090503012a0804030516020a051c0b16020307020d03180b0c011103060f010809071e14040b030d120f0501081b010c0b0402060f0403080d15080d0c 72
    0x191702c0c000821140c9003801b84060800c3d4080f5a0340704800c981c20b42c990490313107102070074040200745c0d418080020390020444040020001384009891b54070b000007001010300da40802d5101d030113012450301c4403030100700070820640903100344012540c40111000710a59916031030001608200a68801494003c0d485407105010303142c4002d18039044c07240f40c3c5040c1b5070764006035041000441d084081d90001d0003503a2220a050400320b086040040228100a4680d21150b040c880c3c0400010149501044070200401da0759a100c03400a10500c17010802c2d070034502940841a50240940e6406d06050103010102800a40142040400c40034102d0344c1c5211140c1c12402c6980341d048030306080f011400b03a523001e8100a0090000c00c01e1012000d5608454603402034140403050900902040010004590042c1c040e03c100d50365620b000107a0101c2c1c80b940d0070060809001044900c0c110340e02e6800000392040303403644001c000b6110915207a1f035140440503d00004d0752001d0080005516410515801 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 857436600 1250 857435350 857435357
    0xe0a050c2407080c250807030803012907080d0c141909080d080115080f0c0903010f0606320a050d09080f0a1205043917011d1c 56
    0x40300c0205164180300d010007803440500078010410507041c1030951400000c6c06c0c1440207055151541c0d5406203d8041440b07024011171049440030b140b0303409190444044103c040c2c10366507400301c2d4a0800181d070840014041c440349071402714882107002c0c410321480c43c40c071400441d04010031321400401d512000c0038824104201140e00149880007007003200310140c0ea5445143d0701c1d6041501e031000504c0807000c48000c10100906100201800c2540d5640000f0217880f400c1c2d03144140b00200e0301420780180b00c1345885160031000540164024510b10103074440034015141880c03032a81d0303010a103000a014031852101000840300341402000100785110000d0780200d210341c01515080e080783c0081c1881903840d02c0002e412a04941cac0204c142403202c0e0342040810079414075480e610100d0b0a106144104902d0342841d52194916200c100e58411100031813a050007600c802d0442c80c95500079512106640c01d00d00c3d840d40000030418007001d006401c070021300075030f616003502d14400b100ca0002c607000d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 857437850 1250 857436600 857436607
    0x20a0308040f0905100302010c12092403110405010c0201360305060603060903090f1207140108010b1204080304020103020909090709231f2111060304020f0105090f040e0a050c240708 80
    0x1e801076070a6850b1080040b05880c1c849995510000d002da80c901e59421607003070000c03c4188800c0c1e0700300039612005a0286410a9a9450010301a08002d4505500054060013100985403040310060015c180e034071a0003541c200d40c07114018107540301020340da6202c0f1030304240000c02903410001004159140010480c5500001100005052200e16000002201d0004c1c549030229600024941c2c0107000c00240c0c6840d205040c2001d07040b484018100403d0000004003003401d580c0300380c0654420f9140204621041e050266400340e40301d54500c100c601c45406d21212283c45407600c0380702c0b43e05a10444001d03c0ca680c50403140030051800503501035000b40c030b501000c02d118054480c00789180e1941082da130000c4e00340d801c1ca40d10000e01c09403c1c42c0700e458100100001601c07100c1f903c0c82011021f00303041d0b8595128100080f0b642d00e111305090f4210340f420244805507000010f8980e01d2900481c1501d185811400c240001e412030810f40892100c0300d0066200700040040003080c0c0d0b94080c00c0200d08 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 857439100 1250 857437850 857437859
    0x1404020706050a0609050606070302060708070908010c0f020d170112050a05030a0c1e1a040c09021206120c03120307201c0518010c020a0308040f0905100302010c1209 73
    0x1211025075a101043c1e0707603440c06016070b000901c91150400d104503485414601c00703a4000f5991540105010100130359000820314040c0100107070005003099100030300c012000300390020b04c3c007a0010b01c928014401c0f01c0340e40843d103000c0c2132013480a24626812985682c02d01d0034900c012502880c04451038800d411003500031440c10300240404901581d2204415959420007840301c1d240c5107d0411000400464240000d032912a11122154450305162043e5035500f020740c0d208074190302c019521800040c5810380040e0044400e0b104800031280c400419949403103a5503070b89540600300360542d10890704100c2000c0c0701d0000c0d550008140c5400d03001e0041c40c4a2202e0315001c18405a500c0350301040000f0316004040e0000d07060b640561501c142014070344458035000d040c0e40e591f144d042c486c8443d07114056407901c40d4a48061a004001640e449582c3d06480c40303010000c1c4541490340d4600300c00301e81c2000b4075400304001c4a4050356a0000c040b2251079004400750703040e1090041c449600d50002c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 857440350 1250 857439100 857439113
    0x11205070f120f08091915020d08131b090b0a1d0705030c1e03152b051e0705190807140d060903020f0712051005220c14010c0b0114040207 61
    0x11441b2031300d102c0101c540ca04d00381880341c009062070034000554020501c4c24059a6200e0502548a490000c1c031044220160811038140001e0201d42c1790410281c2c0340210708076840707030080240810140c9990021070740d1190b40c0742c1818200c000224840c840580803a034a2481600075541251842c84030a203820144003101394441020204004828030100c02c00052010030250200540000d840610003400d05034005800d00c0f01011512a0600108151005000c002c1015002920600309000c1514518080d01c507903804552040038810200e03c0c040003059044100b51200304c41c80c18009244d403c1c00d1400c0c04684000d2074684036003016030200010041010750080501e00f501940161401710b02103804141041216001281d04036110142c0100098000612040341851000d0024454652209200003100444007208500c00c00a00070024407010f80480012116201d05407001c40c0f044000640d8004d80400c03001e010400244010405110711200c0c5200c00580100010703d0100c0950711407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 857441600 1250 857440350 857440369
    0x70509120a0f12110c01030c0c05030c15010b07081206010e180402040614151b1b27040303091103030d092010030f14011205070f120f0809 61
    0x559820100c240c030721060000c001e00e0303181e40004518296004e52142c4650544e907020680c9540d041650303a0803451a000c0c030032010320000e17591200c1900e0791a0000713007a49a0380c1809406103121400a00000586000c4000880784203561041e1414209540644d00881111005100b5810b04c50612029961507444030b40140c0402114a10a01203040c24018042154403d0b04850b00c0780c035514905c980c09587d5085544180041081606e42c1d905e90008003a800684480c112074282c451502913000440d0030500c4601c100400b944c680707840c0480b5008900051900c000035500c0700c0004e0020401080c80707178010b2030540340502c0c400d060304031110000c2869a070020b0701d600340c025500d1849070108040300207000b00b410032500030a00424451000218842c205007101801c1c1036a03121049110a1030342c1000040d1584038225850707645c0d5510303100d444030002950459142c0600329000c0360107844408103406464000c4002d00c140e8880303548100d0803920300038040c0d54444040c011054160381d900c400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 857442850 1250 857441600 857441603
    0x10326040312021b03190c260c01050405090c0a0c140c0411070317041e140d020f07120305091306060f0201140a110903011104080f070e070509120a 65
    0x1480b910b0340c0d94220082c00c1280e510000c80c0c01e84030700900b4031401d5400190080c10b8041c144400c10124185140c8141070350000d034004c0c1c031288c0c00941300d0391003c052154495a010706020964400c500d010004488510650052075400303041d90000c5580030761000007a00b81c2040f10b092000008400ba118402540ca41314200e40d411380c4100300319600f6043c680a14403168018149e4582010195540600400c1100c0a0500e800030035000103024003000c1460091103010340111113007800c4181c1441e881090b040d0188980d41e10440805159075480081e0008003107100c54042c105030b900701601c2c02c01c4030b0501502901004020b00040d49250395020b00e500020781c0c6030f100040c24519100300a0a290b055800c01c2055903d4a035143d04948400ca5a8590002e403480c4c001130040e102c036420000038041d030401c070350301986400380030000100440000c1055504d50f50440b0b032035a44082e80150354008500034000c2d880200c00c0800d0629004201400d000340000b0004400e4500c90081c0c2403800c10380030780 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 857444100 1250 857442850 857442863
    0x17060307090c0c23070902030915090717010510150c02090613060f05180c040501050d060b1b010509030c030d0513140106180504200303090a0b0c120901080103260403 73
    0x21134a5400d070108840c0d00208075190040d821807800c440c1c0c41e0303141d18480c51140d404c0808440003440c5900140900006809031007070803210420b648016a00a000c1110008061000108040b0341d0440100401d01002c04540c0ca2104a010b1a4240320070b00300003418498012645540713420405840d4010750019052818070444040e01d8070080001030280b0b03404086060306540c00340228031003213030101c80649100b0b0a110303a9407801200345000501041c0c1c007100984501007110607002d000440c1120085d8407500c000d010503121000c5603600c901c103480c114141ca900801017100128090741143d03602151012481c44040340c281c50344244007140ca102100540d40d00c40302441000d140b003500e04014130000404000a14003690b5081c5009017040b43c55807129031458488402c2d9808200325a243d000143c0f0041c02d80b40d40744003045403500081031420440c002d00d850400d00010a10642d03095500503580d500840e4650344400454400808450b41c014140b8840081d041201100501c0110b20544 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 857445350 1250 857444100 857444153
    0x40c020f060a020a0212090a0905012301031a01180f080610090c050a030e0f0d020304030b0604020f2d070c0302011107060f030b030316050105010617060307090c0c 72
    0x8511074280300c8001c00810109106000056000343d0000b000c082a146036000c181d1786082c2440014070052099100c61209030a10002168440b003d00780600342c29000280c80360015031010054040d2050a4180180d0007551030544450b5031080b85e651005140c0564102491034444a2615080c0c004d03030880c02c403031b50115007800100341c10041000c00501500d501008049240b0307d008020340b180d410740404050b01c0307104040798000709215070400880c084040300e040308500c80d0069100e41141c803090340c4210000d070005809017400c0c02180c101201910000c2e142020011189a0f88400c0e0b0f2609801d040d21072101a60380c0101d040240079180c0540440003a5a186100050201c80842c203a074409810800f802c002d4541c001d8041038010711103040208400e00e10710f0109203507008400c18140c042030094101d83c00d110065005034182e601c107076240e20071040540d0500040b40400d50700c40d50160700440f81004035900c0c0303a1000c1c40030500b908d04508034600a07182c9001c00031070340019842800105 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 857446600 1250 857445350 857445373
    0xc0705011b0206040902031e040506011503110304020613090c18090b03062403030d0507020f03030c07080a140d0c091706060d08090904050303150d05210405040c02 72
    0x1d105294800e40c0c514080d5003030000c65000c280640110300c5003881c07145e004400326600c440500343c81541e960b0180e00000b07840c0340a0400036900d0900388580c040b03050030500c0030340f8900c0c400d0150030451203a0501b0fa510303544403036080c484240c0c806911851803400b48940800e0300400c5018800a00319940d4030011280310170300e076160b00c00310b03180e00c01c0c0e1030303140f034100e1035662610302003055540282c0c0f0b0010031401a00400002954407072135031b0f4480d4140400501402d1005555010600806a503800c44106841e00980643d0303030312003600e10b02034043c0188013134000521b2490040103240710318501545a1840040610321b81e070082840c002041e9140c1502224a40d17201103007600400700300a5484d09142c01c4400f0603142c65000c1c000f00d00450310b01c1c00c00424808000b0403201e032000c0c041c24908081c506800d210351240c100b556144e801034100e07000706c0e0162400710801003910790010f01814440e10401d800740826444501c0c0c504900400740030000302940c1d070b0702c01c2c40f200c099950007606505602 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 857447850 1250 857446600 857446607
    0x504050c0d12121b111621171b060c04230f18010806060a0b03010905090724020c0604080a0209041a0103060615022a0a0302060c070501 60
    0x348003641d00078101e441c005404110507a602003220384003030800c8500d9040510180016142c1100b03440380514040320030a40055100300d21004c1d281c4507005945141c001e042d034108115190744201013810001c041d0300101c40c521004101e10f114465000f50944501c6140c40945a0b000161400640500f1420611381942c0a010159101500d0500e592610b41000c0001200b00305150701c9103181d034141d150400349511410382c2050300c02001410102e00c0040c614180495440134001e54255000d10f0700815418200400d2050664280da5505819a800c2c1801c0200500005000705041e124802d000200300c00f0310801410184610007584181c4c0d403c10340c3c043d150081410310b050080324100401c00800c200444d82c0c029107641210205110740310360401d100c18840c0c1d401403003121540c000c00042041081d900c484111211002d1100d039401c50600240c1c1c50780f0101500460303e02801000050f1002e00d0780d140d004505004201c061256140d0300440c40c0b50700004060541c95101d42424006580c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 857449100 1250 857447850 857447863
    0x1030b10030f0c0315200a0e030604111912060903170406020a0e0a0326040b19031802030601051c0b0f01050f031c052a070303080a0204081c050f0a03050405 69
    0x40944148003159600704c100c13405500c1c0180b24030211b24003017140e850042c8106014804400010101c030442e0429040c20643c580391a207800f40329070514011034442d0388417030380d5420440710882450101e400300d40d21103101612082c282103041000740070b0b1117070241942203101c0d0f0249015000050b16050002c41c0580708410818030680b040c0f00d880030410000c1d0002c00d0083c60000f0102120301c0e00d203a82c101032030b640d0181d90010401c0c20320103d84500b8050202400d14030740515903409005c0d441c0704083c02103c144560380c0194041d0401c00051101d81004000a440002212030380c407841130590700d803150500019100201c520000c2001000185408054803030282000c5001d04180c42e102c40342c0f1525001940c2101c0207020003c04c501200c4141c0f036042d600c1291185800d5011400030b10419900c6d01c1090104402103140440810300c081e000b842a1400d459408000b00026130207241d001000844451611007040800c110424103061f6070303c041d10b2a060a900d0101d16400d040c03909070304225 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 857450350 1250 857449100 857449133
    0xc0c0a030c2609040e0c0a03050313090207030e190b070605040219060c060b1c060b03101802041d1c0215040309180e0105130c0e0105030601030b10030f0c03 69
    0x5040301824045800030001c540c0c1c191000c0714001018545010202e0400401b441c405610080f0000c00006214020006204400c00c0211000c041c589a102c09412401000d4018000610309042d03607010703060101103254003083c42c00c01500310710b0b5220b2054040d036001101c04c440064441c1f00b48821402d0010058003035002e001030b00008a414604010420480040068486074075a540d908903900c480341115032031100d01c6c04c0580b89802d0380c14940040c0040144483c040c0c46039581300c0304502961700c01c900070517000b03010302c1c01031100300c0d02000060600d402d03e18243e903640c41c1034401ca410003042410001d440c002407460700500d18100190030040c085440081c01c000200c100400a9400300a9605860b280005844018031900031440200155100c2181d05e41c60542800081900c184403100340e00e2090042001c199224910580c10700d03003e00c0380b543c141e4800c030018400034407202d40d210340c094500820041016507a40b41e09030b8072404503909842e0003440e40d40610900110394a014070b4036 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 857451600 1250 857450350 857450393
    0x5041a0307050f03040c0503160e070c0503300a230402061608160309090b0a03110103090201050c01050705030105010e0f0d080307022407021606080408030c0c0a030c 73
    0x146400031010300a8890403d00d42c42d96840000090100048400b20401500010b0200e6001c1000325070300c484e500f01c680c00b810541903088030014007043d100d0483c0c003207420351041c00b8500784046404200c200061807411510020310211100a071076102d03224032841010590408a840002d40c0050524600c3d011041c0c000b0382e540d18108009a181d1070101c80e507190780f80c1440700301c0c1b1400d820a0350881c010380b000e05401203420312005041c164041c07090f40030350b41d40c003c0421482e9400410044446e50342c0c40001d080303040303004009140358000c0c1d100c0e4075800d0041c1002d07403415484101c00b600b11242100c05001140c03000c8010b00c025684983ca0b42401c07542562400340000099000070070100321440001d0185800000160310b0078400d00806401e000581181801034800c01c0460201d45021610b46005104810545074040f45217607155003114115203420201c1d071039a480703815059000034060080306a04101100c10010104201c0303405500954505c2d0242d0325510704503030303802607641907880c44 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 857452850 1250 857451600 857451607
    0x4030c031b0509040b06010935010612050a0c05010306050d0b090c1804021f12020d060513050a060509060f010c14010c12050a060e0a0911060a05041a 66
    0x6200940540a5035041062901c00000121401906503115001980c000e4810b20a00041045541c9158021082601c0e010b09141e1034090071030303041850f5604814001c40807001141d0f03014200600282c070860403c000300c1c8450321260800402c0403141c1044a10754040324035902400241c0c50001d000c1e000c24070f01400140d28010010f420390700003010185c8241c007007501040345440100114915840c01400701030b04502c40586030201d002c801c40c1c081c2d000e001c8902948040b244c4c0c0c448850b448050700d440d4003902007048201c0000039049848903240c4543e540c0400308003641c4401d410b50b83c1201ca0500412145800c1620200703a4040d0341c003150103030200d20180300c4942d652000e84100c1400038605500d0310001401d00764281c8417a1100f040c0e80c0c0d440d0100504038140d020a2072140c40c5144007092080e929014211000c4505900c03907460050302950100e458840c417500202c1110303018202c076491070b400010020724964054610f04001ca04001000c0120301d0ba02e5089500c2c044140d00b03802d05 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 857454100 1250 857452850 857452853
    0x210c0301030f24060f03020f040b01170910050a05061905060a0f031104030605040515060904030e1f03050126060c0f2701091e27052401050403 63
    0x41800141401884100c05101a0f90901010002d002c0d488000510511025903074440781070072611180801ea000b440c24440a030b6403402e19014007524064181c0d86c003800d010700d1036180100107202601e218068014101d524102030400c4c0181800781c4a0504006001d0620600700403610340c861007100c0c0d19440c0100100641e80e148000d56003500d52a0501b024031100c01d4008500a080d266008000d0350f101003004014840c80745e00c424419449002280c003402070004214240e814202e5045511400820002d40060711496841410103c0a020342c00c07101d84443c02150f101d01c040c80f155000a54602c01040085d904c0c01076044c05690251b00c40c060882c5084020f61250401012443c21010000b1300740b46070444c038000c46400c02c8040040140095401d048840c01e898103004c0c4078001200014041180c002000309401390100144204201c545080285075548003204018010451040c180810100e85030040511800b2185031816164540300081c41e00802c0401c012810007009200500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 857455350 1250 857454100 857454113
    0x17070203090a0501020c031b210106092a050a05070b0702062703160c150306050406050a0b0a120b0316031a09120702040f061205010b042c0a08210c030103 68
    0x101c4030911700884103941d40b030542c003055081c584104127090100d08000c200c50110010342c0048151080490103014900d854805003648006000c4030150b0400f0304c080490540d0300a1004049400725400d202c0e08020355a2a803200d414812904100940c1040e0700700052260481c040c1884020308080d8880c880000d50b104a6907401603006802c413000088d82288248051041d80b44000c2c10740300c681400200c400c8000901070f103110f10400e1b002c0c5042c4031b8080f80924080c18500d040d9680079080358100f0300c8030070b0102d62410300b030401244110380d038545103540c6c1e803001e0007a484030707150b296822206c0724510301d4070000b40c00c0540713450382c2100038010a000100301d011402140d000015610703c1e45490352400040c0c002d056150321590303658030309980003400074003503d455402180504001c03c0ba48500c03005001c281c6078941c9140902d0b201c144840300a0070395100048402003004400c48000005c4d599842d40d642d03103c02501e458411034811854010b0400d00011684100c014400d0342c1194956654807 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 857456600 1250 857455350 857455363
    0x130c0c0308190617070b12040b0406090c08030702011103120609070207080d0f020f070506090607060e031210090903120f150611010e0102071a0717070203090a0501020c03 75
    0x80c00c1086600120300200c80c60903600700d05181116041112690760740b9015000a41d40032a40300d14003e0220029895600b01c09440201e40d506012a009aa407941c40007400c030801030080702d186544002e10781c0454101500740018102d440003c40da158520700000d01415000b03646030b40142d0081004500010360b06054580081041c0c807440003e171640241031f403c101482e0007034a0140710303c041d080305982d4000c00d9034805010399000d0380c1c00850110320300d6803038000c00e01a42d0780194080084107947d0030320f800245078141c040c0c60001341e4150400c42403070442c0e001c0808030207030303030106028003080100320348004000380f13000c086c1007210034203542d000b8100320a007055400909684842942900c40203822817074250320141c5200dc001c54490794050043c0a919032003000c190b00c1e2410791a1108014400c454210340c0000c3c1500300481d41420501006500404030004c10103018030f056483c0c51140d0460b80208841e0f00031f10344401c89a000c0c09400a11a88402d045512601410344540ca000c15030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 857457850 1250 857456600 857456603
    0x10e240702031e0a1509030e0f0609040504152405040f0207020904030f11070506090616080f3f093a050f12070e0901080c130c0c 57
    0x22280c4486150000a0801c0003440f03840360440c030f640ea41d6100481001c42c00c2e4070184c1c412481c20903000c00f85108201190401100200414180c2070b2550052070180064500490300510240c68080c038003010078103444095034104c0c1d100c4110290041c6d40ca040e40100b40240c45283c000e02c946070054060003451201d40d01c5100d01441c0d44a92000b10805641c0441d4209034016104c07103018103140c42c0090000e50003000d5000002c5440c2030340300311004041000743c11168010101070420041c0d808114130b9911050700c54144280781c4012a000a52050103408401043e51456842d83c82d5800f901050300400c00465491003113100d0001d10510680340120031110141c4003c4d5940e581d00c00345145001d00c030042900c240198000c0310114103500e05e004d0000c00100015103071070080aa4025181c2c1c0c001c8290000d0f11902c00e10400700079400c240403c0d90301c8a46481d1440000c444103000c00c1d11a4030a800206164001551104590404030070000c0544441c00c4100120440c0c0384004081e011ba0300300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 857459100 1250 857457850 857457919
    0x30d05090c0411071509080307050a0305071b02012f10060510080408070f050609010902180408030403140d0c0f11061014010302271203090102060115110111030105010e 74
    0x840003510317036a40104401c0360301c0141e5a43d42c2c1000342c4090400d8021410301da000a09000000c0e692902c80d2110b9091103000e507a0581e032700090baa0040d10071409140d8208d01c840060380c604405040076080d52001c80c500b07a4003070701701da100c0e0011010699184c6c1d0003550040d001a10060400c1c1d6000007500d40c000d4021060310303103c2502c0c0c50100540b640c00000605075100318020300c480d146042d880081030600c00c8550990780f6000c15a0000b1102c011a0080c1125000f400001c02281c0141010306400d405151680d151201c0c8a0b809002c4502800e90b00300014204d609010041303030021091070004050b8001403e9034649039400c030380d49080500a000c20004101d18100b90380c0d0003a010341c7ca0110440e400d0f690220010086c030000c070740c080d103540b6220700e800110301941000084100e40b6800e506078007030401c8c1da00b080c00d4201c00387d40c0b21a5160801c00d402020400c6500284118243d02d0541019140d5951610000502814883c544103105d41d05600f000c5680c01ca9856070000301d0308072030b071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 857460350 1250 857459100 857459123
    0x51005090402280501030e1207120219050c0a0806090c040c0e060412020406240f091d0703050a181b0b030a020405240723030d05090c041107 62
    0x804070761010400c400c0640c0c90b0010f0040c1c1c80800040c291040c0c01d844080e0380400c1034208031a6072a80d40e0300c80404041c0521020444d48000c280420b00754014114180115540105a105140d5488885400580e560741121a03a01c140d0719082a80340001e0640100030a03207824020810780d12511482d0304c130782c855039561004402c0700b0f000701d11082141c10000c082d1a00c981c1d0b52400c20040e100b444404074495458100003103034061035001204032003440d0030380e6801601c0f0342c8041610321546c0c10741c080c0d05100d0740400014a681d2040070742c01e8084c00c1203455100b00d00b403000307000d025188060480042c15040444915101d078000e06c1094070780d9001020300400e1164528510079882164001c0805004000100242e000e1369030010011124261400e0035100d88191011500d95030444410383d009408000c0d02d00414206200e01a10032107070b003820320909a084168514507808500352010040e1904204044000d05000c040722a00e41a01d0070700180304800b4080c00540704a10008100040c442e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 857461600 1250 857460350 857460353
    0x61207060c0204050c1810031d01062d0e0613180b101206091e081206040902130f0b090a1d0d140a030905011d0d230711040f060e0a0510050904 63
    0x2d800881ea98142c101c15444124603118469000e800207000e414071031007103083c0d075050b070107403031040640590780920001023303e0130890301125200f0060301059229a00c0b130020302800c00144103102c0b42051440c03503a0704002c00d03850f1010f000c1c1e07801042c1880c0444403203801c20019507a5040118016840300700041c415515190204421003035a500c0c2d84011504c0030744804020f038030801081c81803c1140c482da01c1b07980d080108015103000c400000d401111540200c00710b440c042d0031654440381100300c0440c5c0420901c002c5910200c0440b4525802c6481d01100c2c00c401c1c19548030f0100325030b200009044410072554016200e0102401c1c0b80c200346200180b115000c1d40710382e014982480e4424024002880b004150b613420341b14602d1101418010901d03410b100341d009102540d00d00175540702410022440d817880d60b2554002071303420368a984031042d0440c007a503121300c104040c01000c907900081072414480100180c0310010240e400e070f0703441c24051041c812841d204060488008840c95016035590703 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 857462850 1250 857461600 857461607
    0xc030504032310060503100c0314070e180105030604230a08070c050105030709090218120706030b0d11040b06040503061e0901061a03061207060c0204050c1810 70
    0x129400a01810000740c400d0b06080000540201c4080070b110460f440b480c050760f50f01c0201c951601c40c4a0317141e44075500400c0a260b40c0d400400940c100c0d8280028040095190140301b0306c01285d4030400116629071940c09881c049070000c2c522888c8454a0a541d0304120109039102c201602c00783c998a0642202450b20f8081e602240e500707080d0300d09540326101d0500d0070603510313081584e080320286000c8201081c29480349081e03a1046030b40703641c2c40038884e14000b6018020750254480c500c0c0765100d00700c42c00c03540d140ca000c0c03041e030700303000300010000d10b86000030090448440c2d012a921805540c03a091010402c1c1c05961400c80e00d00702c60002e140501e13500081e002c0c1c4180d030302071034160150000f00070502c1c4400d403903120b400310f9030459461541c1e03039510a6401c860060107201c3e41c400134212691400118407028503801100689424800d50b8128490342ca0101c0983c080c60008144003007030011820140502a0070900d44041c00d800c00c004104950000c040c590304a6006001d00700719040b88912 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 857464100 1250 857462850 857462857
    0xf04030c0815131a15040e0f070f0b070b09010b0909060a0e03040614130b04030b0907060e0f040e0c060408150c0705060f100f150e0a0b09010c0305 65
    0xa205441086855507070503600e03103464405030398141c6102d4070b9000844001141c00d4141009034072044e000314600940707800325010360f00a45a5040703443c2d402201d60b059200c910417807240034601c03401420b0340d1a600485c1403a003040c94100380c407040c441480400c002d01c15102600c10032940110704804c01d5440340c8086004204401106510401103c11300885580216070305000b21012482405a0000c02010303070b51b07922507031041c003001070120300720040e25060020180c003043c107074024180d007460342e500d204140603045600f00340d0b04400c0710828030032502810030244c0c00500f4241000703a0030410102c000780000d002043e007180916110400000024001c0c0b03c207854400c0018001078070355441d02d040300e40c0d030039112008081624000c4081102d41403280203440245503c40020980e96484804100307945001520a41c69080b4040001c1401c0c4694a051006424042038040584048640080c161010320030003d0040c034100c03106100602c004421140c52010a0038004106009031400b01e03100d11 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 857465350 1250 857464100 857464103
    0x6070602161401230a0216050a3e01080604090c030506060301060602060c030714070b040614073b040509010204030b06010908071503020f0c0610060318080f0403 71
    0x41d110260307003045542c0c0464040c1c2c030207000081191400d58022080e0750010042c65203034140000c00010380031081030300104406085080038001204a5555041c60403910000498240c00c010310316181c1074940000c9a1a0162000714822500c003200301105655040a4800b504000116000030038940341c03500a00c90b860340c809070300503003107a0700e00340140c441000f500c100c1e00c01c2d4280200010b90a200082c524007450804a1031440d42c1c66043c001d9803c5030b85101240413040050001002040b118014140315a00505010a110022103a0403030b49000007014001408091202e02141001c0340c503000034a024885092030403a20003c01018404140040d41a0311a04141c104800860190081e00499100e003a03004c446880c1e810066400c0c070000e010b00840c036489220100070890f003c410240d144020380c200149030074400400c02000f9446081020b4040d80b055050041103140d400503d40106000e2070b0403c800c1c41c440316a4000317030724a48009481c031300c0d0200d0750b10007025808044a0085 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 857466600 1250 857465350 857465377
    0x7020c1e0618060d0903090914150301060312020d080606030f0f090309030a051b060415050d1104140f03030406090b070c0b0c0d080105030105070c06020a2f0f1b06070602 75
    0x3140c1100c41c1002410313001a041b0b0029400403800103151b591405071540081d2080c0f100300c8075980342e0000c00b1040c4491051260b040d07480e540c3c00030114065030903030440e084481e4050280c9241c1c84901411240020b015980210b00400810800d503000041241c0c00c2400c602c0000307138540302c00c00e580346580982402c166140c025008908c08000c0300080a10f450084204000f1003852442d0800c030060145100c0c0c2c0420400303948140d402188203000809004119820000c2c1d6031a83c880044c0ca81e42294002d100305081e204810303201ca20702040300a844c810102c0066160608100c4000d00041c140d00c18070134103010204001c8100a81d00351160f0291080010481c0c81d03000c020b0f2550340c0d805e110302c5d1220108207180008a0542010b000700762054100d91200c000b082515500d24009610400346e000401100c24503402d038802042e0564041e0080400d515008403428007281400c001000c2c400703041d1039010761801da80705817080350744210040080395143c1d100d00d805e007007070390180c49402000c5400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 857467850 1250 857466600 857466607
    0x60a08101401080703021c03030906060f03051504030504060c0c0305060406050f09010b060711010c02030d031e051b1308060705031518010b25050607020c1e061806 72
    0x108595444030309852000403041c805640e803100a96220103150201030f4120800c001d0744601035001c0e90284100034868900020a10700b15200d0705d0890742680c00c8103483c1402641d0400c248070040001d00c1642101c8464102c140c1403d587c043d0035441035104250a200c1044282014410440c0d50000116009400ea030194070b0a8a04000140b00444040c2000226007010130f6200c0301c148121401050003804080c549a801e859040075004190f0b065810003070b00480c101d0040c1c505000c002103031415a00c01140340700312001065844115110ba04640a107804200114200c0109030064003019002c1c0065480e20f8144030001c01c450aa001640303944580702c1405603060307100c4015480765082001c40703ca000c00c0c22081007410b007607181400140045450041c002c10340100001d1001980000084c99804400c108080b100c1c001c006007910b00c4d8110f60208100d01c0d4040c0300350310440030100c8000640380c0744c405000e81503030300c10f21a544c040c100200da0540d600b8240392204000100091801d48c9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 857469100 1250 857467850 857467873
    0x1802031e2d06030d090609090f0609090f020307060c0f14011803080103210806041e0903120608010207030f0f0215040b0615030603030412050a12080109060b041409060a08 75
    0x4000142d82e124024440e1045403010b041c4aa4402001e4440f555680e005480c0b4110049000d880481c220700c034015a1800c2c00206454988190080140701d41d000c14002c0038507004040c140795540e80311105010b120740108001030210868110215031151400f800d00841550139801441904092004103882e020301c0304c241a04260303002c1c12a4482d11031245c3da2202a202122400d40f1800100003144050f030120f03966245c00d0300100b0410441003100521901c0070862841036031210383d420340c01300303440e00c4121804078001c1c0124009000c0d580025450482c0a950046c00c04182e0303400036040122103420113961034400c3c4600d60140740000c03400c001c54100790404290030701d800e5956501c1101e11907030051003c0761a02c03d41e88102c0c0c00401860405213040d400358000c030f111354004c9525004105003c0c001814099004407190702d07642e40d041c81d640c1030680080840c2d9103904540c121890510003008080010030345c2d07140c00141a50004026240c107000310303100d200d1a4006603041c0c01400410704 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 857470350 1250 857469100 857469181
    0x602030108150105220902030f0709020a3f06030b07051917011422061802040e01140609030f101406090a05101502071802031e 56
    0x1140c0ca400e1102d01012640d907102080b88502e8441003000c2d107000d45500400b0034013815030068030301600140646100782605041a400c1c0b80560f0845024140e020455404241e8070a282e08095911882c10b94072141e050801c6548070440c10705075142000080c00e1090340624076402a0004542c026441d60752400d222101911a400c00c20702c1030340905050140d8070125104824101007500e168120200b10790a040c0e841e034207410107400c40c540100c201110062001c0e400c0c402c28003075000c06c0d10001186420b081110450030b40610341c50448a0041c03006028036400700301900e0454009510310f2041d014180003040703e500981001ca60305010305c50084186280124581c110900014410410f41300c001151400369103003134410750f03000340c080b80000e150301d201ca0b8000e542007062000110102a5203602d0446184c107418035200050304000c601f080101c0072a181041c0288103043c0a608520300285945224841540c1d06101040c2540224900c183c08081d9012030740f40c00c20650307058040003032121 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 857471600 1250 857470350 857470363
    0xf03060423010b0f07080c0703051e0d03021e0d140c130b0c0a050a0302161a1c0e07030b160206090a0b040606051804051614090c070602030108 63
    0x4500490404003486841940c0c0c00d070504200c01c00203a41501642000750b60340d001c1d002106540403407401000110041480d403000340c58480190001071648504601c0d0a50802440600c507003001000d19494065115000c02d0b0500c901c0300620300180c41c0c1c1c0808806d10500d89088003006400c3d40006250300031070100b0b80044c000311180511541e9140c98109190980e4490300c4410800740340c502d0400e02c50003032040d0003080c103007d00787c088420845494403a50304000e40b260044015034402640b040f20a60342019800c01841c02d0203004103882007203100c1001d28030605150040003c503130360300c40341d905c0e4466000010810391102260780b503036100d20708804615810703990859104821005600928400200c0a103da40030b000a00075882483c1d4402c1c25480000e4012680c2c42e403110004105611207010003046409203203100012410203082071410b000840c01d08058189009505200c0407141070301001e8441c10544540540c1c1c1d440750000840c500420b08002d091034000400005c1505001614 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 857472850 1250 857471600 857471611
    0x607140105060424052101050f011404050103030c111503010f030201022a2106070f180605040b1e0f0703110102040e0c0c030c10050a0b01020609061b0f0f03 69
    0x4c01c030402c00108940d00580c0310756030a0b0b000401c851810320031401c14007110000c1d0f041c03048059001c18050306211f03096a00444a803d8407a205000401c0001e081c0c2c4224550004195020092541141c9000b40001e4007000003400d4281104800445034031410121869907106120042d26945c6803400111102294401039005100d2500c0381400394030441000020070010381e03a210598250b81007070121400801d80f6410000d03003c4811104a10800e001d040d2080c0c540780d41e881000300308640c021300760300a20020031102d00d40449c2c2c1071204541240c2202c0136180c0e4160240d0300c40791444202079010b001c4c00901d0441030360224680e8a41540d61014000c0c1038030980301c24568911010141d4200c2c002c5200f221001845103012401c120f410340300611504200d9410b41e490140400c0a4926004021400701c4115565104003c5940081d11640510340c1091015004a051007a98203541e8a0301170501d034041c0c0806031060b4810490801206c504403001c0004a45410000d40c40c00c5c801e4004460 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 857474100 1250 857472850 857472859
    0x60b0a0605130603090314041511010509060c0f09030f0a021f020307061119120b030109031205070c05060a230103021e04020d06030c150509091302060714010506 71
    0x304500c0d0058065403158440d080c110a00180b41010071800380c80b078a01e00780c09200085100000030580c5d000100007406501d0045410310303111000045c071101c080d040040e0717140d1520050100d001c4012071566001071544014944803122201c44010611a080354683d052041c00441c7c120500c021444041c000c1c002c54208100342521302074601c294008040c80c00051b041006581c0019030140d101407014580c0f02140b03400c1004049900081e0004642d201010441c91107855800035074034011107030f5040d8254002e000495190b44c010345020003071b08076a4006910380c00040c801501c2000c04100c507980040494042d81410410b04000b81003461584c1108002c80700201804040d00c00142d049982c00b40403c800f4140764985001240c496007521039100b60200055030084516000c0e01010b50b025841070200c0b0743c500586010000071900c0b803030050210510858003265a5149030a5021140007519040b040b140d1001404a205400d03001300408801a2018540c210544c00303e40300c2c3d0303416039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 857475350 1250 857474100 857474119
    0x1b05100c020604030918090b07110d051c201902060112080f0a02010e0f031305040b0105041e030219060314060303030705090d060c0509031504081806090a03060b 71
    0x5404a071030b0807044402401185d5184000c218411101c0c3d10500c0300042d43c01c0000e100c0c1d5455403a2628050161103040c001201d03149203240b450014000903804419031b007803152411100c3c100c40883c1300424109400c80350f982c0c9011080007000804441c0ca260046070b00c02c0d541d0304000f04141c4800020303444500051003080004a00044540d840640342500419a070b070038000d88007004039a0390300100155046540b1180001c500d80700c20003035000c034084503070051500d0350b003c0c96440382d60b910b003544400c0c4554142629000c19981240485099846010281c0a2861010f1010300c100002d17034070080d00800c0b030b038049120030001c41d040d0009541061754140700c1381d0228041c180d01a00240c07002503060b0400c0cc042480300d800f80340101041000a0449400480140c890004550941e40403a01141d00002c00700720b6460306102050400108581044ca1404d0503228a0654011000d0000c03e040c103d0030404582d40e505401c2d2048024010201035496440c1e02e4007601400d2200c80c654040c03040d26 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 857476600 1250 857475350 857475371
    0x60e030307020a1b180218030d0e03010c021207060b0102030c0303010e010302131e0e0705030a0c080105240105090103021b010f0506041107020411071502030702070909050604121b0510 81
    0x2941c004c01c64510580401c900846042128000d60121803880130b00e442074000348015032002c2c40405007401d415100c51004a5a0342c0c245800e46a400c056001150081807003810120100c1050313070303203094011100040c7c010b07104c40181d2541c80354440f9100c02c1d01c000b0000013116016090fa0a040c0c92003540c03542101c41e901c0c08002c0c25240c00040304180600400c0c20300c404690103501100320403126100311034181f0781e01c101090420102a0046e144221100710134000300c2024058603401090113040d030400d4240360712059036207070030201100707040100006030303000c0981c801c0e015220282495070304600c05510f05d41600f4004c0c100040205800341c140790009426140511036200180e01c401380d81847c140140c0e080000410340b404008036104814440708000c20041641050036a00441c3c0059581c103054001070b00c5c00b203455007c40d00407402c14140c140020000310f4560707007150707002c0010307540600b180d04280c40720442d10541e81c41c0ca0070300140c002c003444400612500444035142c02080210201d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 857477850 1250 857476600 857476643
    0xb0409051005190c0e0a050306040c0b0f19050c010e0c01140304020a0b070503040e0c030402060a031508010e0304090b04091e0602250201080a0504110d060e030307020a 74
    0x506002920a40119020700c0401080341c102650015400001d90140343c48503140c8821540f2481d108400500141050101360404107a20009050100c001340703024900383e81c07040c01d52040c9016100340c001020500102e481003801c01c1c1d8038580070b2000c201011600710040200300750805030002030785609100e2022a4240046a10811440180c4d01c0140b4281c031286000c01030307440508100c2e004015002c00082c075020280103040c02d984035030040c60380c40c0d00d000c841c070130f0100d80034001011400e0200103200043c2e80c5c03001101d00c080d01c58100494103295010030911007408591010000d5401c0410201c0c054201000510a031104064208136143d40102400222445104020601014604d01070306036551500d01e606910b01c185000362030f00d043c24802041d541d8003442c0520181c005a40d4200c1190303003109405034400318207401040035241c592504007842e00741c7c40d40107000e980080c1c21075040c0a80c0790004106031080d00112540d03400c08690003561010f602c1c1058a40744d0903041c0d01c0100740034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 857479100 1250 857477850 857477861
    0x9031b18090606011d150c16050f0f0d020d0311210922150608011d0610090801060b1911030708250b06030d17040b090f030313060b04 59
    0x200201001d554200054404400da070868010390310900003d00f405644400200e140510201d00481c3c45030f5010403414a041230180c0d121081c0d2104002c2480b0325142c07201400020380301150816a00265600840c551080e5940d000e0b40000c2e010382d0a1007803603001201c201c22695918111858040281210b0030f00500d41008480800810040300c109403400d07030002404e0110a68a040f842c01070b0414500c100c43c00f840390004094a2814100441e60300f00182d1401444045110702e0507030060482c40402500007051103100d01141c042081d006d500c2910b800000c0c1c40080d008100e046e8403014440103d4019441110000c00240c4610034824860200341d04100140c000a5040a100d540c0d0800260404081001281c4002186c4100d40d9644a00064141d028041000c1141088814035040007128020f88051046243e4850303c251903425500e03038840d41100c0064240d07151001e0301800e088200020107010b01c400700134004008078048140c8207207403051004010090881003400150b60 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 857480350 1250 857479100 857479111
    0x1701050f030a060905030c0316110a06170a0e150604060803090607060b0102120a0509010e041b0309020f0a030b0106020c010824040e0d0203070606092f09031b18 71
    0x10066840c20703000031240d40218002c0da100b241524140343c01401c41c1232a54100b650701588145620303581d10180306802e5400142c10307a081d2480101c00d4100304000c1d2100d0107038080e00000742e413500b00068a0b510b9941c1304190151000d07040d1a03040134806c04c01204440c0554266214501d030560000d0280c200004954180101503c21420170328162138031001800c40301e0800d81980141100400c41002c13460080800800c030fa16040c0d00c86801170001011841004120f41c0030782e10700114407011a00040344c1c8082e4400350319012034100c1040c408210401d204200140e0840d14401000c81049900711100f0b05035000c81c2d0031070381d1f044c80e14001180c054005030740c00c1d40303c40855180a2840c603030512441d5001132000e04046811210507078224a000340202044e0010303040810040c0410007180110f8009001c0000f0502112801c442a41c0802140100d081e084100866800c2841544841558600c490060680c0c4803401982807400e040c64412240e2441f0702c401140c00440401d9101840b4040d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 857481600 1250 857480350 857480353
    0x405010902120c0d0b03030f0a0201051f2304020f091c0201080609070e0d260f03060d1a0a021e03040b06100302130b040f081c03180203030a1701050f03 67
    0x50b203c074010121298003203c2149000390315245880f1a03510104003d00347d000c1040303081d80da01c10300791100074212a80901030486000307643d9158103844c6c0d070100c0789009480e4001c0c3c12141d40050442254900c00c8941062a00140003080410303403c1102d41c060301101106903800d50061040c5004102c0074038580300000d0115400c0004070780c142c14140c00280d03205007142071004c044119480001c6018400b20b03412a04030440f04480981030703174485c80203205084480c0d800e03414140c84c5c00d50311000e4080180210700400c5101d07100e8040c4801e114086201034040c03e0303a0889410860220400303544007a5a000740140305e550700d040b0112901e4101ca10454100c4078460198550608201c02d09015030203450415400f8845d203042a40c1e20140c1c0002000e50000c41545c8601e040441200d0303003481c3c5d100300000c1d00304e2a489080c035918100d005003052050324000540c03d00038840d00c441000718040c00b0790140300101d068450340b0b40080c0358040c2c2d600301e0703020300c142caa0b6105c1c04c2180000d5000742845d0113 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 857482850 1250 857481600 857481637
    0x90a0b012303100c030c0f0203041401020a0f0303050108060f04080d0f0f020c06010e090a03090b091c4709010b1c120e090121080d06050405010902 65
    0x1071103161602681000107803040c0c02080781d000000030300c0e050070011449071056507100f0500c061900342c410383c100e0064a0900c1b0040040d40744010f904c0340070324450b00303c9075105c010300c100180e8803d02a0010140d804408580c00d10407038200100204001d0103868801d100d02c101140500b10b451000500c00c540c85128241b4080c0d450501c44080c0c0f18441d00410101c1d180d1440781e00720701440c00600007403801c000007031105600d4545941d42885014240e5149900f0402c582404264000e6a40341a913541c0c1d00c00c40ea80c0c0c142c010100751202e041d0301200109030655070b601020002c650010b460070054a0341310301c02c2401c5100c50703090360781c144d4042001c0d10040c00c060b4049500401422aa01224440c00060300402401c00b00c0e1740b0b0242007000c2409040380700c10040401034140c0e00480d41302114a010071031011414041280b005041c080d00c0006c081c0305880c07010011109010203480c9912030122500c074110102030001070311a40c010079200b141448001b2605c00c41034400e40f540c0d001c409290058 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 857484100 1250 857482850 857482859
    0x3011a010c050703171215030a12171510030b093d03030f030c1b050f0d03050a110c0c042004080a0201110604020306040303020307020c15040e090a0b01 67
    0x7601400c050084845001e251800404102880c0c01003035505200b4a80660b61070500440000802000706451150030000319030300b10984001a01c01c0300250702c06521102d8181003c4180c605030381030007840002c24185010400e4010010144a84801c800e07210500105007080c02a01135601c8000b9164001e1041b4000980d140c2c04628100c2e01c54610b59180c01d1586032558030200707000c00355081c2d180c62595103001081010340c06800041094090f20b1308212202c65214028584064600090344102c00e1001ca0814890280700b85c065802000084516500e20018064041c10040781c420603141c2c64007a4124000b00c080003140c0c10244072030003810038031b0285400c1100408032090402007072220a50078803501d444402c02803018000403801802501002d20004203100d8402c581940b00f0f80004040c08016200002d6940d00f0503411300300543c9903610210120b01d400c040703804166000d0140c03e400340342100f0000041065406400b400c50040d6110750680b9543c440e03811000b064250036100402 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 857485350 1250 857484100 857484107
    0x9090609132a0305011b050c03030402131d0d110a030e04150e04050a1707030807140d11030f0703110307050c010204120809040510080307020d061b02031803011a01 72
    0x1036000d82c0100c10800d00030000c1a104110301d41c10445182c0e554507080000440602000404040a442c200e840c114180303646540781d0002a1000b401031460340070060300f01035960000c100510519010182c0340320400001541e44034100c034100d01007410301d00d030410b14420208100e0310b0680c05880e030000c030200b8542800000c103034024801a08802e550004540300c03482000e9140984d0084004002c0354809080030042405039208141d405a4100704400000c0e810040729544009503062000324003510340c062110034480d41c404094400d00d0710200040319103908000d58007900d984030242e01c080d96440340640481d007501201040401c4280000382c14a0302c00c40041045c480b00500150074150384d040c1c520803c1d5080ca00403640303040d01023800f02d510304103882260745c802c4241385200c0c2142d10303000500c1d80324883e4940c003a0007a40582d00140c18400c042e04082c1025040c0c0035140192103041030300944a0b0030482c2840e000040d6580b40000a142c1405000d6510798130500e1648030703484000054 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 857486600 1250 857485350 857485373
    0x41a031806070f0c050a06020a02070905010b04060e0f19060504090b040606080f0405160e160306060f03090f020d0f0b07020d14030712150f1e0b070213020c030909060913 75
    0x5c9809106810740800020540c0c009041040619002000c40b01e0030402c0c80b41c2503840c16084000f00403018070040140340e81c80f40759981080703c151440c071541105000071640151240240c0d4003400b590550004a841d4004020700c122694070b20100034150303224040000742c4d078440c850040002d086401180741400b00b11040c0d0f400a00c03690485142d541d40c0307000d00c610840681e010750040c9401008005105a903040d8044804c02945010000d0504000b00644520002c140042c01c0694400940013080a08210441310580003841e400007050f180c60403c01c11003580100310341c02d101103808202c140c0c2c00007e240209090946a0302d5619421000c034003202c0d00010302d032004000300720151030b42c075840c0c5200301002000300038003203490315085c2107a4143e644015070081034041110042c915441d0303c491600c0069078034281c0c0c8555510ba0b180000b80d0444000760510880030720005000c0041440080201800082035582c1655030395440104214024100c80d10020300c0d41d0501104005480070416 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 857487850 1250 857486600 857486603
    0x204030f0206160507120b01151d060702130606090509010b1204030512040f02031b0d1104090b15040c050a0f11190f0605060306010303020a0f030302041a031806070f0c 74
    0x1600000c42d1130b00d98501c5d02242d070307100841e610080e03080c000c180110b16481d40d0242a500c2108224556074110003000c0360302c01142c45048202403000d5414982d1050f0451321801c4d001001000203941c41d100c2807000b00302600c41c0700c01041803940c0010f01e034100943c405040741c001d007640504181e0702c0c000100c1e8140e001071088040020030400701c020a4442000c2c0e5004d14042c3d40024007407a5540b052620b0140d4019103c8159040f40040684594500103100d40d5182c1c40800360071811a1304020402510300c1c04401030402e21242304011070701546441d0a10700d040111014000e900d140d81c400e581610411110100251110021015890141d01a080809402c5045032205544001d0b40041c0c5854074004582000303607021003c06000c1c03540a902d4001004401503e0b09514503900a0b6035006000f800034260000360540c0c009141c0654103580003012000c445403c00c85002100c078109600480d00b0a030f0083c012440d20034030410024004d2300c01d10540d01d4138034040d2412641030b03500b44c0c11000b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 857489100 1250 857487850 857487877
    0x403020901080c0f060421050f1e120403020a27020d0c09140121180809031006060801170a050f03070b1e040303110918010603060501030204030f0206 66
    0x40180c444601450007050002d000d81008003401c81000440f0070300030016482080c042c031040c0244820311107405010f1140c40040780142140b031418034103013201109515401c3c020f03808210b0b00806500d0800b08403108840590b036010010902c036040c2d03401680000382d001115010148280e9541a15006680001e28440728002c4a100490010fa0340300380c0d1401310564507446004202134020084101908030170b0b031501059004500004c00400d080741c04e01c5054030006030f013400c584aa5602c103011040258442c207c010b509420041c1e03080d030000500c1e90191242c21180500d800744c0d07103c0d000960f0419a180700326030740380c042b0300c042586400708000414000c3c00011000100100407411119083c00007840e21000329090040205500501020302c00c0350076044003d02d445031842d2039900941c035044c001480c0b00362040440346401603a5002d90400c90511400c0900a64120024100c41d80c9a409000d425110740044044e405a484020a4141c0d806811b00c01890b000c00644070410f08000d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 857490350 1250 857489100 857489107
    0x30a0c1a01030305090f0a0503100c200c01080c09011d0a0801140a15060c080a17040f05061b0d110f0412170f07110a1d061c020604030f0305 62
    0x1900000800c20ba104402242c00003516051505100c818440c00c5402121700403103071860070000c21703201c03120000d00391140c554980c20380520034011101c00300c041a44051204040d00e40410560b96842d08043c1c650102e40310600090325030742030740120b07002002c060b95201070039810039410803141c1426995580e8411003011000c160407200f40320384041018040350b6141c990900c0c50707104084030b05c2840e40d920750610000040c4a01600800420b051991146d0300c1651480308200403a40b4244030350803a00302504101c10f000900855460002549000b030040c0c9580741ca0b02d80038070701501c201c5c2030400c0328900e05226503141485e41d6030240c0500f9108580907482e01800c60710442031640950040d060716580d140e842001e12081c0d419070001c0180010115141a22949500c5a54020b00e00010030b940c50803040406a5115002c00704001e000411441d0340841c1d0340d40b0300006581007100c41a018000b40356685c01459505010ba905281c0c010b0940e91078181140c407030341842d8403c444240c0074020b041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 857491600 1250 857490350 857490383
    0xd0c0c0914060406050301060605040b0d11030117070e011d0c0910020d022a10030b040f06081209090c03100b18131e0c030b09160f030608030a0c 64
    0x90255151015049840d001d051828004000490300c1c15041903029a1600c0c0d814400190404221810340d200c000d83c3c1900d404490132024003500d21020249907003803001c0000541c010000c2d0740b600104801000b50784400d51202044c0310110b1007403050120b0040641c1c49012100140224a034100c0000207181d4604000341010484a090600f03208005902100c0007210f4958180801241c2d0310f03a041004801e0b800d031584445906a001a0a910641b00803480480f018065800042d2074880a0001d20141c10407484500061101e0700c5102814010076940d80c0b03080301c80c181140d000c814021319119954403040c0e49040950402481240740700c001c40710114500140f400a811422108100c80e1580728071140bd000d101c1180c2d040b841e6110382000c04265806000b4080301c40c1c0e50015030000942440698421000f4022010400d60000015014021207403256054802003540584603441401030041084084170000c2c421204c098005110b030401c01449443d2000340c1c1401910b1404629605 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 857492850 1250 857491600 857491619
    0x5090105070618020a0f150e010e090c03090c12030f0c120403150c1b03120f021204140307030207231002210c030405060a17070507020103050f0106020d0c0c 69
    0x10444551254108101c1500710702c1c0104140d0082c0c4241c0c1e011080c030a00d450035142d00071f48044101400e000303c80740c0c03601c010391049001c0d1016480c0100112418209030700610541d52003607840c3d00c060701035a10294032a00380744000e1380b581d002d142c0085182c550302d02011000760700000c045001718003035a00071240b40035030607000c0e00103540a054030802c900340156203102260100b04904c01400b48007801010007894801d070710b11081c1d4043c2030140d80c51006a100c08010a00c1c0b2039110000352000c0b441e04190040900f00600c55445510b8920f440c0103000b60496076030084c2800140183d00000d0148200c001c0b42d90110040c003090441460416800000600e50041d01e002e81001640050384d02c2520070b800e000b004640341c11080e109841c04c814003800545030320503802407038010b00c1c0000d0084003180c403038003080106a001035036902243c100300d04000c00c164071104060b800a81010045228802d00e85600e50407161950020403000a413484c080e1a542c0e2500016a4007a03040b040010b000c01c803 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 857494100 1250 857492850 857492861
    0x40207020307180c0f0309020d030807120f020702270c07050330010509060d2003070b03040c06180608040f05010e01091401090c0e0901060b34080a050901050706 71
    0x200c041010400e50500035008051141105e4160101800c0c0315141d405a200c44200c51085905807901c00159940c000059620040c000387d0b00244520348594940c0a680d55406071007080d10860b03041c880140641d14840a0440d000000502d806507480441c2c0c0304001e94004102c0380344100309032404d01ca0803c0409610140d6100024150505500f5943e0310b23591400300305000d08004c07102c00e081818030001041d10034002e4000100307030814289846101100341001d8101009000741220801c1e81c4620801d40d0179041503e085079181495400868618000d0701d4800020101443c012002880c280703040701c031008050419280d5941c40009075001c01da003802284140181e02c000441c07000300354541280c400350000c070715a16a924001c0c0e800001090020110100c5403180e0343d000381ea4640714060b074014901da5214417030b818000a42c908010140030510031000000c0100c120061a15440d44a0050400100101401400c10400c00742d58054400343c101c04806242590420f041d540c0c03500700300c45 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 857495350 1250 857494100 857494139
    0x6050a060809060601140d1808210901050108030901120902040e281a060a150905010e040e060c1e0304050a0501050c0408070303050306060f0a211505040207020307 72
    0x3410142008500b99081000039004a03003840d02c140444401c0c036072200710b8014912a070400b0340d100c0c0000d000520440c0301a208036a00442d5490359182c1c01c081d0004007401148110b8840b000312800107603102c5040c41068102c13040f600c091898106220011140094520305410100340c0e0f8501368001341e21a4030500a10f83c400380002c040201d0459070b40544610383d0100d41040080d103010702e034002201101001c0044103905100e40054540b440042c4150400b90840b40c2c142080a22117070420381d01404102c11030714207072501040100b00d2000d000560f491207152906a5103d0b10200c3c0c88040c1c0100104200ca0306840700906151075850700c3c04031a80b080c0c80680d4150300045074001403103801e1003101d801c030014012140c40c0626040309241c940307490348006010301001000040c003948032801110b8001c500500401e81c5d0360078021014110b001c50300c080c0d1803902140c1d0841d44a90075144642102980505c03040b15207949408100400381d40449422601401119800550950005104180e0305d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 857496600 1250 857495350 857495357
    0xd020d060e10170106030f021201090f11100906050703120b0307120c060801030b010614070f1b0602032a070e27060c03190b090112350a0306050a06 65
    0x1480c0280203c4946510840f40880f41d01d0700904100003802c803003030b070104564107449400345944c603041c01da40104001800507041085010040301040341800d40c650380e8200880c1c003543c2c41003048504032200c2c0d0503400f5500220b1810464200884c0c0900700e4444840010701003ca00d03034151101003400c1004540c0002542404408010308021070141140050540d034038044456614589508010b400103206020500034140c0000309010006000c032241c03d60000046e600809041c03070003011075549484041107038040c904001c2515840801154003a800e030004146810401610f800481d202c03815181c80716200d84280080e059003d200140e00c102c202e0100e10440c1a80c0c0c1508070b01040c140e12089074250800c03401c00800c84124415a07070090304c074240a205054415507594001c0c003402c106242d03c030212000005100f4000707a0400d10091149407030703050b00581c0d0000600000069403550350b828041c2c00c0316160750070360b580c091700d078225191501246003a42c2b40c01040c0240e40681001001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 857497850 1250 857496600 857496631
    0x303020304111c17070c061404051c03031a0a15020c13020a0f020c100e0103021b010b03011119050f0409150626010605030907030618260d020d060e 65
    0x14413a010985607004e100c00701030613180c95560380c2c0b4440c0c821310600a0f00140401c44181c5030840701740c0000da0b0064100905550700c1c3c044245c84800c10031085185c1100064100041100c084500ba070354014015405480035140e1030078184421010b0309045540011032103443d40c9c20302140e80f030320079020101501c0e140044e591625080c00500c40405c0c1c0244030150340c00510b107590355845103144000c0c0c6580902c1c0406401908600490103485601c074501030320b0b1140c0c004451304400641c84000030701750890003002880812400c0341c4e624000c40600c00720b44024040c0d01c4035098024002007030380100324110b00d46000e481d01c400c0030031038100c000000e611440604040c01101d42040031072580c61406003004044135a2806042c03907283e814041d440800001001241d082e81d800c10024006e158019400e01800d01d002d0000c036440a80114150340039081a844960b03070102c1540180c2300c404181100b40e140501c00d4509401a61012000354007469403002d00051030400810602c0c060804c1d003944180c0f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 857499100 1250 857497850 857497853
    0x11212030911041a090f090c0306010305030d020f0f0a1707090e0606160b010e0103020a0f0803160309320603040308360303060a060e030304090e01020702270a05130303020304111c 79
    0x2234528035510540c0650301450040c8041070000090300d041002d40140580d45400003543c80a0303501458600d000154000705080c8c0401d40c0184094181d038103442c000c04800c1d42c9036041142c009046120702c0840e00145808540c95041040042c6184000b4507200c407216034151b9540d840301e5000364020000e0300c03e114014011880c00114150007000b012045000341c500b840030380c5881e40300c0c450343e00a031b403000401d0440416010f07022420050503100400001400310800883c280d01507034003580840d11010500205d586004002d40f030241da0142d442400581c4c41744c0e0180d0164001c9081c80c1c00c0300e00c4040c1c54514068040084900341c0c0000d00c003660b01c074107080e01440307045070850b0820014440c011006807170036200001914100c982a060228203450725046c41c0d402440b41d00c9002e900205485159a070903840c0c1c00c0491780e0080c1d2040d0543c0b06a5601403100d046034020707690301c00d61039144d40500300440d100ea0060358020380200c4410710400107140c0004e440c1c1445001400e0300d12100d081100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 857500350 1250 857499100 857499103
    0x90106150c02060405221a090f0402130e01060906170a0b0c07050a060b0102100e0c061b010609062c0403032304050d11011a01051c05011212030911041a090f09 70
    0x5014800d512594480c7d1441c1038000b60311400c000702640c064400841c009004d554490501c8d9944c204402000c10602560740346c1d040c00717022103000d00304403242031140010383d410038136110344401844d48000d000591301e541e4840e1030409001d8000c0640d201e0500a250204100b804041c10640c45108000313080c59541001a00b45400c405014400ca490078500c41e0958802240d01898000115183c1c1c0da030750000c01104c0424040082c05070420361802d42c0115a056290303000d40155448007881d0042e600030f014048085444100710510b0038040303039000c140000c0c000e400100c60f0141440d050702d0800c0030014100c0301010111420340d00703640581850301c0102d8015001d100c0c80c044100c000c1c05090a580d0b51003050710b20f001d041310b0400000041400c18403903078030301181101101941c180880d503034841d284091881074102c1074409595102440c4460ba009102c0c410942d603210124002160007942044010001c0e40b0b005204001c0d001c1c10b0f10b40075518103a0003482100b500802200500302202400e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 857501600 1250 857500350 857500361
    0x2b021612080a050c16062a12050c0a0b0f2508060d1209050405010801090c050d050102040807030f0501050705040e0a0c031b080f0f04171e0409020c06090106150c0206040522 76
    0x9418000f840f2100111034200c048060303100323400c9803401c03034850310b20380c021150351145141000d174a014032800300d803c2040c000d030120b0095002502071540d5417140b00040701e4100102c94040d00d01013034940e41c003034401d00900800340e1051000307220104134003068039203032003035031303441001a001030110103090160b803416104280c09000000c00803c8002ca40d40e4a03e0130702203490042600c02c2d040500070b08200309007501106c0182150f40192099255a0324105c80000143d0a00700c40b607508090005480510074000c1d541120441c114101c82130301c403103031031000a1a82805650802d40c844480b00b46840840f0703040d074030f00507040d62015407628024800044056010f050380f4a40c038260030512000c103280344484400c203507120288682d20103140c03070509a0045107000480004401003000980c0c1241031f40a4400d420740101654140e60395001543e08a0b48140103200624001000549916215015002109101030050b40ca49501d540000329070030040500003007100c40000e80007000080d1030091 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 857502850 1250 857501600 857501627
    0x15020d0c0315050a050d060906020408030d0f1a011107030605070e0a0b09060915160b07030c09062331060f0c0b04052b021612080a050c1606 62
    0x70b07079a814248000103001015500c0b41504c28922840b000051101c0d0f907010b50742c201d0b40107808542d00ca580701d060949039001540d140700c4442c0380030380e691500b03109801546114201206030038094800d4500641780c0c00b405140036046481001400320006031075100c0c19005a12903240c0d0b80c100714914042006520858011101080c81400040d070662a51001d40f50002c00458801011507400724200780300d4019030344c508007114050640c0030240001d0140c128007801d1244d5060007030160321501903c0c2e00b501e030f100d40c20018050341400410010155041652001031170307400742c0b0f05024480064080c1504503c0d240805a0144103407009018400544004101c2801c3c003c20482200e407000c0d040d218071b5200a8400c4985800160400000784404803823500c0c2d07032844102c5442c07400d9102e00605041c01159025100305d000e0501c0205540d4180c0b002c1342d070100b1001c2070b000c03200ea403080520340000d031034082402403c2c412203c6062050205114080c002214081880c0ca802d00040074004280036 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 857504100 1250 857502850 857502881
    0x5070807211a040305190905010806030a0f031220090108280c0c080a321602180a0e0705060306060a03050c0f0c100e011103040f15020d0c03 62
    0x14181c00103100c0c0c00a001c0d010311400c4407441140d42e641015a428850f4000c03040c3c0c01c03400c583c003090416820054110560f503003a40c4580050755040241355803414190005444c6010000120700004e101d40c074803008417409083c0214414140f40308201980701c4081d010501a1400302e43c07620156440750110360b00c40001c40480c81d84280c820554150300e250454041039a03600c500c50840f02a020712281001c10350300005895440c2c3d10000b00a285103810120381a004040c01086900d000e201d0680b018410007000095240c14022410360716644842d000c100d070854410345503410320100c003199a502c1020140004506c4000e0141e84504050f05a08118456a401c0c0300b4009551030780420343c0d810010904000900d5241d40300e11600500402d07428003502c0c00c0c0042d02412017140811101c150324410b600510406e81e0203202c0b07500740e861144801130320761410300020700030808c007840c2d40c0710b01ca0086410f00d1102c0b03405103565059034005007a1410460b15640700c012819818071410180141090 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 857505350 1250 857504100 857504159
    0x20d0207140309151e030a0e0f070617063c01021c03050907090c050901030e073204020d090209090607080a021c240905010b030103061805070807 64
    0x19040040d11326062004c10800b04540d40c103c00580d02100d1016107184400b5102e151a03400d1038050aa814040c0b48940558012120a120002a01d034180c0310103131540ca072405244444501c15100027002c10f80d0100105001144030082141c0403101f10416101d10700c0c5184901000c045007040e5101c0c464115440000c01882c100006203c1c442d03850701c070745008119501c40e0340610385401c1d61078015090803451310303000c0e0306080d8200c001001000700a0b207041c0440c030030a03841e40d501c85182d4428190000004900c05481230800c1944072810b420b1440e5040300c07800c5c59000b2a080703800801040f40a642c1d241501d0b025481c1c415911035104442000074807030303494044001000d082c030191002240e5a0082040c091034103144020b0304080c011100b00300a5665004105000c40041942122007109100b9000c5490081c078001d55050320200300072503103540d01e16a2000018580f003065410300c0c28142a112000480c14068400141034650003480b40d5800c0c03d120350114220410024124080d40c07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 857506600 1250 857505350 857505367
    0x1e0405030705011b021503100f1a130308040f1a0309120a3b0108011a07020f041406120109050601170304050603090303070e0a0308070609060f020d02071403 69
    0x240d00c50941d4028603113182401043c04150150414100c8001c2d440348001e84e03810b42800d02a0050f52061104012640704c0a594541d401010f51486c0964100c5c060800303110603281100b8401000007000d01e020801e02c880d503988941e400d030740082e0012015040010010000302d01c43e414151803600194030140d00d1070070036192060b40e6a00000c245402032401240709041c96000c0d5500c2a0500e508a213403140309151a890003844904902e42a09118450130038a0000d52182172b1043c1a10112000c04000116145802410b0f40010108036442140c000031480c05450ba8014403c2c0380c05982c001500c24205481000000c024001d1a81c400742c1c904050800801e100042050468040045c3c1d5070b40010105500c038110300c1a9040320381c112000000b44000c94030000029849a940b907520f003030503420a00200f00d1030007503a02c005071100d0360900c200e0340418031503170000c01444d104020002e603c0d40942016801c3c3c5c0c10201e07a00240c00c2c0c0c041034140c00c1c410040703100d03040e140612016500d0314021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 857507850 1250 857506600 857506603
    0x2030105090703051005032410031e231506010318110a05060c060a05060d1203050603100c0309050c0406080303010b0a0e031501031101110705010c0501090f081e040503 74
    0x1400c20082580b1900410036045448003114041d20014023510b01d640300800c041c01542c04613400154444400c3c00001c2c524085010180b42a00c1c0c0c40035201003d0b820345139a1402d00680e0050070741d0f48088400807440c1201d5401400703d51070718410041e0171012406a1003001070503004001c01d042c1410050421611440d5019070f0f2040e65021480713240509119000c21a03c4140f600540e40046002036018651140020307003034403903082c4201c2407150341e4a510034070403402c0c101603000749042032140414400f40d00940096500c1040a0212100e401070300010105846c00c100080c4080b1341c0d04c585800921509100002030305030265800e100492410382075550720310051003010f0346c10101050b410403451183e00a075040240040480b48483c02900000c01d03217003030130311048030070b5031100c0b10046440d40602e0b000885c1c00c48117809001d5031481e000055460b401c1c2e010040f02c0365541c07001500c0015400403c6002c440d4040d9011517120070805a005240c500c9035660740001c4c81c01807208120380c1d0380 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 857509100 1250 857507850 857507869
    0x11190501050708090303070f0302070f060204030c080c03060f0406090b0c0a180b04030803060612090d080601030c0207051c060f0b01020606060421020609060a1205100317030403020a1b03020a0902030105 89
    0xaa508e84600b52040d0144200c000780a9900010000e60300524a10148030042c1c020300305480c080c00340c0382c0541356103500d0540c0c1c0c0c29640c00ca46406810100008a500e101d2021440c1c0c4140140e90101e5035044580d202e6040c0c06003100ca1503513604000ca40c40840d55401050441c007c485035182080850900301c40c60002d0140e84401001c1c504004001f9465481c1c00055901d10a5035042aa015050440c8403e8851900310314078800141c1c0d050000340f403503120b8040c001207a009074000d0803d40d4181b0040c4407600400784d081d0907580036040340c8240002c5491281200c031b441555400206101d560000a0a050010740042e120700301c184414030203a0314201c100540c8010000c82e0394000c0400e0b20108440b405001c1c0c48560050700480e100700d20b190403414140810322407170130401c06c6a440c0d03058440c0c24400c502016180c4404260310f945641032000003150000e009004a503111580d07a50b6200202d001c5100c0c042d1400145c0303c0400860a041402e0006416074640650440d810304000c9100b182 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 857510350 1250 857509100 857509111
    0x10e060d021309051e0c10022e0507030506012c030d080f09240a1506210e030406032003090d110601030827040e03090f06070201020d050a11190501050708090303 71
    0x1008110b0440340107008126400300020391100020789c4174111415100009051180c0b0040703a07040400050401d446841102d21500e4161660a03007822031101a60203081d0f80c0f40e0000314100150440160340d9420000440c452090f5550060207181c9800d4a03c01003c02070410703400c0368401c487c00f500308180d071764548804841d4100c010003244d580326000d03c007070501c0881542207074440c40008240315510072855206250b50500e0044c1540d001604d42045030808003010034260014031040c4015031080c1c0148402c0302065065011604901c40c0c05070860740182e80207009540860b80340440d40da088010100c040b82110301a02c1650b1650700e6401b01c5220354540da42c91103a000e104510503428082900400031000f0b08200300c2a0340c14055695260b1207554114802ca8440c42031400702e190140495180d5a4181e001d0000071500640c16902070300004610003e10103107100c4988150300030403030841480b0800c400c0011104a6040c45406c5030030207420300d001c200780c0804006203410000b04030798020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 857511600 1250 857510350 857510359
    0x30e03070f30022b02180f0906100501050702150408070305060c1804110714070602120c070504151701140c070515090f1006081e06010e060d021309051e0c 68
    0xf542d03843c0e134003103138031541c000254818081c08031050071188040041d84079820f0403c0c003030702a88074040200d03607445040701d039040c0c01c0c42140000d100c1c9500c100041c052452002e01074680078203000c003180c4a2500305400c90100760380254010000c6c0601005001d411401032442545480d60410034680d604044140c0a4000c5072150300b00740c1c40d0210034084a001541242c13480014410302c09800d034441e81c8030710030704006100740c00085c403081440e0030440b10f00038034040041000350315110a00c4003600345e8010044854100000001714206c0c62901b03207403203c60302e10002980d503120081c6680c44840c080d00d104070303011060042c0b00c00101d0000e165002000c807402240490b81c1d480c24050300c1c002c00e02d03c041e542d50141002c0d5400a1016401c00c106882004050304c1d08901e0b00070111270b4040d4200d83d1100e0340d5200c000104110122442c060b5002000130b014150025016004500e100070390b1038410030714a564044030320905c0014440700d844182180508007074100840c070040e546010b00c0d0301f005e204 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 857512850 1250 857511600 857511649
    0x1050d031d120d0809070b040e0103060b030102090d0c08071a18030c0a06022d1b010201021306080601090b0313060e0c0306101a0f0403030e03070f3002 67
    0x282d598000c624240c6a40101119000d5041c079400400040781581c241140d0300c102403000c076901d40070100b51003e031068580c08002c603030311307545581c0c020388428084260555800c004079403154584920310340940d402401480b404915128600780f400030654052030002582c224443d100385106001c4800030031503c65614641c00c18400020f041c0f08464040c5603100391032103c0001c000f034000c02c1400e03e010328042c140c89003c000008003940c1883c07030624030501e0307000b420b04a1403402c01c103004851404c00610006087c50003034402c1054200d82900101d003c03460103003c0021660703100401e0300141c00c0b070710b42d0a402d5041c58181d19554081428000344004d8680c29001c07040c00c1d0800c18210300501c01011a000b6007481148000c0d51030b490302030310000c0b0f002d4291052030340116404482000f40d09580080c60240345071011a1410f16195a099140c06240c40008524186409000107011854400d0800807594880b0310f82600021801aa1201c03140c040030002d42d5842444003210142c00c0c41e41d42c807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 857514100 1250 857512850 857512907
    0x405010f02040f0e06040b0117040f120806040c02070b0f090d1e0b090151150e030607081305070608040b092b050421060501050d03 58
    0xd4500d2400c8554024030201c0c0c0011800c0900342c0c001c08651501c048010f0584900c018002610f01c0ca21025000c2455040c031400605100000d2a030711034004c8083d00f8002c0c569559401e19410110030041c0003407590800d001142c034280c400c00120811500007001d0b401e107040d50031000b9029440000c25000000b28004495840e01c1218518941e40468140340c4481c1e14262500111801401618808915000105044014821400d81c902d0480c0b1101ca14054641a80406086145800444a0050b0320304074094540941c13500d6401742d071505000c103941090b9003240c613248443c180500704290061a99010744012456a070000c00c6450112010b41d20385441601c00e01c42e41500904600c141040002c54951000b4442d002d42e104140802c1581c4030020b04030b907100f02180084c0500c04d0300d598035030700100014084c88506000d0b410000e0500780c2e180c1400300994040f842401c0e20041420007071040080920681e070240108482d0103031180c4584d10b000780014444281d8903641030b4040d20b40b40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 857515350 1250 857514100 857514103
    0x80c0106080a06241a03070309080c0f0606180604051803070f030e0904030503070e011e0e150406080103060213120f050d051e1608070f0506010603230405 68
    0x1000340090310221060074105103485801060040222212900c0541c014022403504c0d0a44404490342080a450014031901c02d54415900241800b070a040d625802c0703800281e03055000d001600e01080250001020040d54070f42030403002015548510034a03e9150340368692212019001101500e0001c0c0e07590301d46605600c001481d00346107940b8440070400340208540101e0b00503105100e90b0302c822520840f007003405040d5809407002000304405100142e220341c03040d14410011141450320480d80b481c104048030385140e449158200281074030300c200076207003403400c4419140c1d035040d12403e01d06031074207070b000b84085e1045c00000d258940006543c5400310005011402070002104004104000c92030401c0211500d078100b1507450048010880301c0324010720950b11780c0c81004c480408040d00186d85500c840c0e200c0140e6590b100f544000180110700f080c4094036865115039180319807014141019458a00e05a00000400d030810240349600124001c26903410310301c0f0b0645107529191442d190f0f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 857516600 1250 857515350 857515361
    0x1b050304030605010b1312020904030c060906050c1206060a02060105090406020c1902040c0c020303090418050607050a121503030f020c090a15090b06120907090504060b151303080c01 80
    0x2802d00d03800c000021841d00c4440c80105144095031299094141c0c2d26940c41c2c10351411004040d501c400814000341c0402d01030360b81071380c0c55407203120300144450030340e5104d80883d03509480f0306003004004142500682910001c040c4c028100b1507280c0d08102020304000d58a80050103031501428004c4003003001c0000c641c040c0c410302d11082c0c1c283c0f070000c485600100f180c0307010384801360710440c20100910045409028400303d6560040d000d0741c503181ca20070502010b005004203102c2c10940f005800c4004c90801e1100c180501e0f0b550340c80f47d941c0c8280c224000c10001445030006640c82c5007807052194494405000c0041300e6160528040c449880300003603003441c103190000c41c1c200d00352600f00b0444a413654004011444840d105001c100d80742c5c0c20351012076640540243d000b5800704203843d240307291080c3c000d500034070701c4040303440c205d444241210666800ba141202c81507240d500700600c84c0741041721a242050024681070410a03040700801b2507a98501c8060030030180040c20254429003034010b03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 857517850 1250 857516600 857516603
    0x702030d1b05060103110f040912030c02030408060c071a0705180406090c08070f020d05040b1615050a06150e0d061508030403050f0f0d0302250807050d020d1b05030403 74
    0xd0f40c542d5a1749003062114072079150440e9128291041001065103010300c01c0340901381e082035002c0d00e208407a620641c010208140504250b03c0140f00001d50f8413020007811780b04021050885843da820b5160110200c0440c250f01c080101074181000480765100341a2101c2d4100369040003010b80300040850020307c0786402a00c0900d040640c20300c4a580c01001550144907540c1d0b614801074007c1c0d9017261512070b42849840006d0342000104001001c250140041031005004802070b0301136030b99950030200764100344607402912203080110001c000d118840050500300305085400341541c40040501a072a070394a4440c0d000d541d00d80302482990751054441c6583c0d040d9000c899607c51012545d6034000e03120072034091140000c200040500458150400034000c0c0041014107075a031404d401941100750140b0902c030380c1c4644c5251240340806000040c41c0140360702561040e007070501c1d600b003022446050095501c18200000070a600c18800c2c4143e000d1811110312241091a02c24154400d5a10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 857519100 1250 857517850 857517853
    0x2060403060905101505121c08091b0d0605091614041b08040803041119030b060109060504051009031a012105060c090402190906140702030d1b05 64
    0x240403040008503805010000d0150b8100c400d80c0500d04080e034151410300407042440c02c482042040703142414010303d291071912005030f410404009139070505040004044c40c0005195209000511030103100d0081150380700310188142001000c0814034186c5180c800804882d034401c00070b0040d0005000700102d10f05c981c0308000905644890354004111507084c02c1e8422441c01352612a60541c2c44481041080161280102e41e522a151046942c0008206807010181c0101d44000765a901012601e0701400d100011441400c1d410300348003101c002021507041c401360030b000784182ca80140c1a54211102110640c1c0c8082940030203d403500c070968801001ca0800e40320300c640010400c54558140e50300e00c2805d8540f0502c3c03105410262001d4980134103983c020b0808a1403104141c0010224a00003400162904100103400251402056294000030700601024050141c4c0b104200610951071980c080c02c000090300000c0e210f01e084800b110074482206040303143c0480c100e000e140350980100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 857520350 1250 857519100 857519107
    0x140a110f0a1b0b0315041d0a0b0138130b03010b030108010b030303011d070e1f0201050106140d090c0314011b031415060906040611060c070201050a18030206 69
    0x50305001c01d100071410001124024403001c40c000f158642928807070014107030a0300c4420102400c0c48000c0103030924181000800c6000c0c4501405c1c2007003445803291041010710500d41c9000d03c0d03080f1401410803d07090b0510040702c00010344604041312190b951141448070b9036070a02d89031440e00301d607655107c0181c0150200c000980c4c0702a000145040743c45110080c09800311003404c040d100d102c24080e41500481c031420b0307032075942e803841034031503211880b400c000394074001d060002261484442c400f080401105582c0000f0355a080c025179005080c00d0a003030b2103501c02c210540b4101d000340c106000c41159103c080c03205210100703444100a603004400e0411356a00325030414003826080b08104800501d06078030401651084c4551210340c1c48814180e03000b5111240c00b00040d034140e400540d8410303420701194095507500c100400051609499001030a07407540c1c040c904010700185a0145c1120030300041d0050b0340c001003110321f030302c03154500780d8054440340800f10420030060700040d4002c0d0012 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 857521600 1250 857520350 857520353
    0x6031e070503160e070e04180b1503010b100c0c090905101406090a0510050312040602010509030403030207060f2604062d2d0501060f140a110f0a 64
    0x100e4003805032401903041d0740b14804100c0342143c518000c1d2103081044061a400196518400c0070124401c020050011421810b07040d6a40304600000d02c1c15101520400244455181a200e2004030400268001e00c8480641c2000807a4610044404000d00520040000400844d420210040c0020520030410300b80d9908102c0e95841c030318030010458a20b000710400542c7c03d42c0090a106142c020310244050ba01c42d10a0400b52801400101c9200b00511000c9065901440000601050340c190951100d240003802420755001401148194200300002d01c0031a901240c10b0007640c84905049207404030103002241e20024070480070030741060420408a0f5180300400c0503000d00d029000901800e05200d03c4200b000d005280208010340b1203240010015a107500401042e010811807261003402195209108145104204902e103603244014080d290700b04030698a014101e180c42d60518603400000500340c8180c080c840180001e20300407078914030041143c60723040c926900603601d805009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 857522850 1250 857521600 857521603
    0x1801050c070e040506010b0310090b1206150a05090c07030c021c0309030308012711120c0c0712030c061104270509010e060a23010303081504090308040b06031e 70
    0xe031802c4a281c000c5d43c000084030703182001924050782748441000c01841c54595020010015241c0c110341000c813201041100c49014060688680310076143c1c8170101118004000c0140c0050b00010300c108122000d00001d4501c4205036008550f1609104500c6c407582c1c00012045110f0130f0030907a01400400c0c111042541c01115281124030079200e10000d641c8985141440350a00148800102c1030314443d407141c030515410080040c080211110b10b000c00351285500000000c9132000d4a0000c000b80092940e0300400c81c06000308012841049000380d01e60700281848038440740980041e8413034101920084c1d07110101c034000e010907210100c40784190010813414541280e50030240320301c0c1c4400510911410f020351810702a41030302030071099551640e030710014054050484c4032000032105c0f880035084608441307406907019031520f009a1030a034290707124014050444038003440c1070640c04800203403c0b029941e0051782c01907814500d9900c00380840d00e490bc1c1139180d8100c44000010791504480c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 857524100 1250 857522850 857522879
    0x2181e060a1d01080622020906180a08010504240b04020c060406140601050f0d0b0a0602070305071a0307111f0603051e07170724080f09031801050c07 66
    0x10030b0900586480b658006480c0c00c0c3c0c0443e04c3c1c64001003164164801450b8100035142c90a200c228010f00340288400814695000b461068203441d00c51400c00d007040c0f5040207200b00601107100280200e2409590301031700da1402c0e02a0b0700082d07500c82c448484848045d00483c126070800342045440d0700e007240307401e60b80d010142c90a8803014070f05000107155898030010300d441180181c54292a00144d44c4600425030b01c05103d0350b00c80c40d070b510f0b004076590783d40c6110900184500e030700402c001c9041d4200316081220700d034011041000d543d1184000d09415070203030395200d074032802c000501c007070300c42e01c0310742400203000190407103007100580310b0382c240e045600000030b80e80600c0c1107800b451082043c1c0303806c0002d40303429030010341c2c0a440108490f95001c05a200d043c0004002d1b940c1c8596a03030381ca4014881ca00040816144c8050b0242203260740c40440c5a40c01105562850b0050500820094580c4100c400e0107030341203504040e0b4042a40104111a1140001d90880d05000d68480340c5010700c05 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 857525350 1250 857524100 857524127
    0x50c130203010302100c0809190b0a051c0b421b0f0601050f0111150a05060d2a0e0f010e09030c0d050327010e0c010302181e060a 57
    0xc42d105c480300148074002c2007850a90001c2000d00e400d00d1542004020308445d500d04403643e9100101050700280c100c007070515484542c889540b180d0780c1d44100400d07010407402c001034003441d20140303224540da5664042e00110251040011141c401e10f5100e0001080d24400b100700030340741440300c0d658415203008084184810702012900c851070482551a60107002480c0450f41c8000c005020618055032002e50015050403d0200c0d0744100540908200104200b400b84040c4842005614030903805044e60010041b03c541c070055189560345484141c0800115100780c41640c45400704002180c0103030003800600c8012601c40c5881c0a182080d900c090003085180403405020a1042d20000142c486002e00d0602920b1a0b003448041200d19420003000048600e0750150b040310007100d131350405e91100034120000302d04400380103041880d210142c0200ba04142c030400c1055a811448845000d815000f2204012140c0c031a5003040d2070204000101d503030100c00044c28a5005400c89c00c40810340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 857526600 1250 857525350 857525359
    0xc070602011a0d3306050102070e07080a0b0112061413020c030d05040501020d1b0f021b010507050f0616031505060d0b01090807080d08010e01061407050c130203010302 74
    0x12001c441035403901c07042d08214a904002654840000981009560b10300248403500c6941000000d0b04c0805081031513aa0a14201d551031009204650303060124a014014605400c036103814581001041500000c00b022020390740e41d070040d1100c0c1c0c4100a03401340401c0f0340320280401c0f0307200d4201e03500342e00f51080d505108558141c20802524854001e5481c05424400a50304003049040268007602c03000f00202c031555820400f4881c2980307a0b114444280070817001030610007000210140050b2041c0001005552000044018810b008000441101428a0819100d24940c5040e92519520f035014600c180640820801d02c0c110088425035241a07554051007c516102118004a4114000c46410003030800950011405036002059200c8045c500171520540c2e4902907810840590001c12854001c01602c808066101c840300d40502203040d69a041c42d490040007900c6035001c1e1001c2d0304c5000000c1102c1040c00b100b403050099003e0050450b9900188039900300c5c00075407003404100c3c0308 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 857527850 1250 857526600 857526611
    0x6080c0c120408100b0d020f06070809090c03091b0f04090804050a032a030803070f0c020901030501052e03120203070503132102030a0201110a0204020f030a05060d1502030712020c07060201 83
    0x5c6140001c2401c3c4034070340180c06070f80b554072001e0900c070469100e55829100e0368420032504000c1c0d190b00c0c000d41d114100e44240c054403400d20317810302401e00b1701d0034000c4658480300d040c500400c1d0390b50105040004000f00c500190000c2d803450320224901880d44200d030b00c080b00550000c144944031095422045d6450700c02002c202c40c400300c1c803078102d100380400707070151500b4000100b2580c014030800d0b5002c001ea06190824a0300d950019141180981044481d83d441c3d07800d01100400d1698640da60321020800c0700708280700290100703030301a4107101c01f07481c47d03d21030f104881590007070044482d01a040020f5a58940d80c0c03c004504910b030034880c00c89000c000c41700d245181d8160100103104a5130080151020003041d4004640c442d842d019005040e001b40b02e145001660365200030325021010404c66034482c9081e40c0c00d031003140d5004200500480d40c0e00607480c005081812038041c80c2003881d000580380c1d25240811180101c140c260201c13001c0c400200c4001c90300c40000d80d08101c0720594000c0c0300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 857529100 1250 857527850 857527871
    0xc03120c080301090507050919090f02040b09060702061c05040302100c080601210f060e0f0601170a390f0912060b0a030321050106080c0c12040810 65
    0x4046120010140c1001c1e818401801620740076007280e60001d42510308942010003082c00507000d40c05040004078246c1a1100070800e00d60759000703c94002a40b40b6046080a01e0054000301034803c04c140039201300c10000e2420304544e544004e03070301e6003100e1100f000e41c00401c03031014500401c001d40d0250050312511520ad12107485174003072100900c0c01941c0d9800e0544076003005440840c49615600122400081c910000b50214402d9101502c8501d501141d01031800c01d14200380d800c00f030701001a80c100c50003045a666045409200d5441c01015101b5441c2e4510620364000c014101c0003c0241d050312413803504034000002d100311241180e9910400c1900700c04002d45175214105d0904000c10640380c020051502c0c0d01001c001ca42c0e02030030300490308001d26070018100701076940044001c925601120000d0704041c0300f01030804130409000704035550500401600b0440000d201100c08200010210180c1600748012155844040d85054a41d52038200c1701d82c403000d0080e030320b5030301d540f80000800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 857530350 1250 857529100 857529107
    0x309100516081b0315150a08160915030e0c010e0108060f010c0501111b010209012c1809150f010b1b03040308120c0a0e0418050a0c0312 60
    0x5019000084032045071079026802542c0440004103800314001c081642d0001c1070349401c0086200303616103140200c0f000212010042c10b500c4c0303158154058101400007000164100300d50039081004d00845207800407001030100c90410080d00005001c1985446070b02c042505a0003221070510840281c80010410400441c0c0842801807550300040404002c2901c6003000d00c03001405400601d8409041030712900c0391801e58182c04400e4230002030008001b18030040d49008560705282c020001d51400f0080000242041c405200081140c00f2501200189945628440720030040191000e580380940031001d100351801102d2040d5540510b6241c4044259101c58007403080703400405030350706642040748101050b048040216855a1141d43c4005484000c1020740001d41c89005940d03071700d451018000c0150200600381d1003507030406202ca40c00d03081d000071040b40506070507100010250485190110400310401c0040d0280c01161006400d0060025a040689000714001e600e003030007212089 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 857531600 1250 857530350 857530361
    0x7050f0f0f09040f2d0b180717102112020a02130b01090b181e030d0504060c150605040908210103120f090b0c030a0908010506013002070503030910 65
    0x1900007140105c806080440140080e64032a85c21207000150720907000042841004003102d680440c0c0034400803c000b095122600800c00803031480a8800d60030101e1000d4403440003801150382d904e040c100740252841e504c0500100c0e890308001181186a00380f84040d4444080c1c4205078040c4081c032003007092030784050080300100007040c0e40302c0403128a840e513000c01c2e07604140c4004c1001945101045015a6048184000c4140c035a01c0b4155844695041628004641f107050003404010302041200603042540790304002e800490f1120365102107a4a1001414a40c000a510a1400d00b044e0b00b44524400603025000c21910f201c0750b00300d03000c60340c018003800901c130003040d51503c0c001600708113100311810880b0046508145107040c1d1070300d80424841c1c000c030502803100d42c4042580042aa8040f40791001800c42000802041c10300b0300009050b016021444040c90f052040295090507200b01400036607620310300d00715211107017464003540f29441030310002e003a0312407000c4411084242e072184 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 857532850 1250 857531600 857531621
    0xb040e030901050a030510120b0f242724030f0a1e0602030a09020f0f01080a1e05043c230a050601080d0e0907050f0f0f09040f 56
    0x50f0390500d0115242100078000080c80c03200010b41c2420005003100b04c156240030b1452140310008443d181218003581407450007440c40800218a031644400400480ca003019000802e460011404c0c0034100300025010041c3e5145c3e5240c0e0595040102150144d001d2000c0300306a214040007400c100350806a82d03000000128007540c0104400d20001101d03500f044c840070b0070b510069040001c80d51544400ca8000301c58283c1c0d407680307500660f0304500d042c100001600760111084110301840e03400080408600810400401e40c0d07441c031225400c00032200455600003011001d01441c9494900030f140002c0c038200e01640b084900301c000d4003040004901c3c03001900c0380350300d20542c0c1220b9103030107900510101031a5452040215030031100c10013444060304c180c0c0a9030007041254541002580b8090540220f0030412440d4141c00c40c0541e00c43c0c0540e90460450701d01191212680c0f03000064500c5807042003000e141000601000c0301480c0070190150007412242046070044d0700d90200241d5100000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 857534100 1250 857532850 857532857
    0x1b061009090528050a0b06040609050f04020f06070b0c07020109080d1d0a03081812010b011d01032c0c150d0f2c01060602031603030903210b040e030901 67
    0x5411501c48507082030340c3c1c03241411a02e04001c0c80d8064460604103902d05800343d40b000d40c1401000043e0815009000040c03000701001c108500d442c08130343d83c0c2100050002841504416002d81080d9200d106441c08503820403c41c01190410807201c4074160b0203903104901040c482c000001c3c0745d01c0007043c101040d030384903102e00016080c50003000e2410400f217a20710b580320f40c00c08408004181104094000000c485034030420f051500806c00c01c080800078143c0c1140da04094084070b950741d20400ca103800b010301c840c1d00f0032845500070040c1c0281c034034100300086501269124a400c01c10045440c80712175481c500b40c40384490070078140007074011540018010050100006280180f15a00610b60004801000100c45145010010500d00a00c540601299602c0e480a1114100380300e0b200041406000662500000c54030b0b840a42090040140c01e1550f94070207031091501850b4a01c0c4800c1401e03040260038200c080c1400010100c024005004d10314120860b040d2120010803039000200585 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 857535350 1250 857534100 857534113
    0x303041101081311040908040801020d060e0105061c090b04210201050717101a0406090f0e1b09030d0c03030c09051f020a02030f0c09070810090c051b0610090905 71
    0x440b080302030704c507002c1d20b1900b09a071050080c01160008028001500c030074800540d0303846c1401080410b40310300350080300e440b4982000401050750b0b40c1b8220703043da107600c007e030114082d4414914002400300e020b002e402e0424480401c0308010f070b50f11804800c0b6545100c0c410100c0c546070360803801c8403000c0300c0320345c01324842030102901d5030303059052a07902101e5550104952922403001d02c00740b01c1c011550540e60100454113000c40e54018100e10302605800740c118ac180c0e0301c4c4c86030000016074040d00d510881883c1d06900b14018080404441600c400581100d000c084600320040c0004841070050b00041e00d028800c08030720b8419048042100c0c0018020a9003c0710002c1c0d01d05085c48944900b02544500b001000068071700707001c84541000c2c180c0103841d040c0c4180e010300452910007031002c000c00c010700003000300c0e9041801c0e566054804c4903a002441e003040d08403e0300c042c89900312454400d0001940c002904a0000302107208401700038002500c156600c621200703845080400400941040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 857536600 1250 857535350 857535353
    0x1e0a0c021e100206011a03130f1e08040f0602010c021509150a0c080f07090e040812040506100b0c071e1d060109060c0201020615060d0e03030411010813 67
    0x1000c81d0000c0141c0401c01512600c40c01c80040c00102c0c2e000120000368014000400107411038009810914110004003840c40c903000780740100e41e00b004440101010f101d0b0407500188175002490402c040c0011420001c0c1c52a18105405203030003e00c110030910904840209800b031060240c40c10102507a0020185000c03500c007014803652000340744010522950601e01e40c0000b0485da110b005c0e0840903800162282c102000909038000140f0048405040e907083c0040180d106d056603040741d01e02d28040802c1c0c0c46902d8050241d01c2601c000820f2032421138140400e000c40441d07402c0c0100f802c03076801d11040b82e0f074590248040c00f620800718503540088004101303400c020706520302d925110a082905a64a825010b0450400c0200d03035a48540d14104015155800101c1c0101500490400d6010903d00c0d42c0000e68402c002401501000f0b00c100c1c201a40d40c44074000d8a6128209520078014248202c5500b030342d13504101d50035200018100002c1010354020003000d07025000f05450964009003d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 857537850 1250 857536600 857536609
    0x181f0e010e03010b150d050a0b01091208040e090f1b0a05060c1009050a0605010e0f0c090a0314010b0913050d2105100501081008030d0b0402040509040302031e0a0c02 73
    0x440760495019500c07000301008581e01c484050303030160462146141c56540f41c0c404001220702c001d042c038031400d280294003000c0c0da81040100e0700f2039026002c2c83c16001c9261520500c00e00444e40190b04456005007400114200455003a448035100d0044682c0d1131424082e010100390710a03070311a007100f041d18051106081c00f90040070343c4801c0e5411501001641c452210441da980c2805a580f80c000700144010042c00b130103610700500c4100d080c095641840c51110301c1c0c0010281400100090000310180c5607162001814021a041602d50407404129040c3d03a0180800e42c5031280301e4942e040001e070280140040b981d80b00340d00000145180030007000c1c103559005041c496905071541c005072542d01c0b100c19000300c40c401c0010103441492246444000f41802790041e01001c1600c1e0160340502c03440c9400420ba940b824805d250200f1461020300218000380f003103401484d00052190104414560004000c1c90741005480b135000708500e4031a50404240940700c034039400511414020000b5240 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 857539100 1250 857537850 857537867
    0x90a0b100e0f1513020903060103060902100e0f12010b150d2f090315040609031707081501090e0405010c0e010f09060507140a030c0201030f0603110d03090803181f0e01 74
    0x100004c01450718181c800002d223018002d86c011a90729440f61200d00441c00d00840b0400c000000341071040303003240a4400103419182420a00c1c1c024079040c00643d068410075001032210001c00340803640c554140354070141fa00d922894200903d00d04059058003900900361100c0c181c03540d04440174103040400d2090309240d03406a40748560520071002d180d2074a0150f030315040c1c0100d10503a030005000c1c1041c030b03024140c81c102800142402120004104040e070b0480c2c0c106500c00c4a07005c140341411244070068409421542110340003131111400c100400c0701c15030102040190b141c5900c501071000303c00460f0103d8003801000300060040f1400c00c1914040c002034160648a541c0240820f000790300018034113204828250001840c503280030042d9601446800c404040005003803080700e085468030012240392468040c00b94441d0007559052510401d2600040d1102030113480d500d02140b00a1210f00d1801d42d005031041d082ca64450010000c24505601400540d85602e0131141c3c180005490761782 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 857540350 1250 857539100 857539129
    0x40c0521282a0b070302120304020120100903053a0f090f1b1a09090612070e070f1e050c250603110c0c09090a0b100e0f15 54
    0x40000c1c036140c008061644002018143c007500c52a180c004609000b49002c6001c9250844902d040040c04090f0341c0c411100d01e048035111202101d4100000c44e0f840c900007104020070082490081032108155000d8001c00200041e407069030084110080101909009085c5000704a00d46160400700c103d46a005040b01c0b0100c1c3e540010f0318105521072100081010b10210351703029240029103010400c1c4101d0a01410214400b002d940721010703540d40b008d100342c140c000d02c6804a440041d0060b82c2d0030f201c000020030101c040c1c1d5030340d40d65080764000000081c2d48420101740988031504045104030048414203041c950304080150f000c0d1025219544800b5103e080c90260810b451803200d01d040c803158655642000501400d4030b084401811101d001d21480030040c0c5c20841400d8440000131915200c0800300e60b0700c3c185440e84814645031448402c0700a01626060040080030425001d501080f1481c00c10040721541e904046001c40342c03821528242188062004031000b42840740b2800c0c03950 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 857541600 1250 857540350 857540393
    0x1140f040e0627070e19150b07051e06010303081807060c1103011e060816050118181d010c0f05030601032a0e031603020108040c052128 60
    0x2070343e441c9031140c02c20800707400559100c0d402c001404005d004101c1d00150170400d14800b0000c244101044100c8800329100300700380c80c03402080070350611606114171030305484003400032100c44820055803038440c0e0702407000380c0204600f000000c032034442c0440100c0d85009404060b1100d44d0070a44181c800303c0f442002615030f060410905a4283c400348501c5901101c200d40144588005010101c1651001e80080020b9000710742d205081d000d26000742c20580da42400d0521080a580e420304a1454076a8400b4507a2041c840700c0394004c90680e845204015003184003402902d0403040c0590a0701c1c041d10410307002403465015041c80900c1400a0343c0c100b0310526002c00c5145103907030030824400b40503566644480102c0102c480807074014143da854188150041e2141e0072161240e1408043c440c40082d05104003000000d00b0018508a94000303003c00811002c020505055402c2490044008d80c100a22480c0c2d4000002503100b07100395120250740d641d100407800d01341d41d00142c0108509000c2140c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 857542850 1250 857541600 857541661
    0xf0409020310090e070819020306221505040c050616030c031e031b090f0e070311030106080601120b0a031709031c020114010609170f01020301140f040e06 68
    0x201e0744038054840c5001c1c0e10001400e40f1790900c40c5440c18192401c401485018104000c00016200800c65039401040b21424019030701d42c12850040c0341d0b4131100d00800032807846040c24089181c42c0d02c914081c0c1d0145100000b001c0e280c40c2484002e12800c4e84072036000114000c3c510000b032042440e07a6800b0301c2813400c84d800281c94420110042d0944040c2400300341c50b400048904bc1020451071102e00452230000d4086d8a00410300300304890601900340100100c600040040d4042c0d044000c01407100082c40350340350b0303603030200502e2200c050340e0341800030788852588014415240544c9c03c1368100184890001031469331109402140010301d4043e0100912464159681c1880120000c4160381d800c5401c00980c1007009084a41503000c07960604400001440115445814070094410728640342403000c2e00c00c09034902d081c00441c0c5004071076000000210301494034031007005244009a41501301e2921000401040c3c80480f04940749a522840010340c0b403207105802c800c4500741d84ea0340040e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 857544100 1250 857542850 857542859
    0x131e1109010f051e060a0f170a0506090702073803100e0f01060f08060415060509130216020d0c03151a010e0a050613090911040c050f0409020310 64
    0x949200c00d9026100d0048110020003107401c0501c058603034000702d101c00d01044040100010042e009903419a41005505844521828000d2035040103a1820403892403043c503080ca4540040c00c41160079900508000005c11406400050058180c0b501885031091070143e107000d03e190442c880700403492031121038021301c01d02c038103d0700203500440440346041c2c0b13810708001e0b00b00403002c0040d04d1442d5413200180104010303940a04c00040c01446031038110b10350b440e01d0001401030910b94020046982d508400041c01e9508103000341103a68040c0c801e0344a4900504000c000c9001d0141400e50010306210110010724201244a103100d201e0031181920750340341e4030398110100306890300c0c158440da9a01440300952015000045034002440e00380001e59511010621311019440b03200d00070f46000c920211310888082251001d40303407107002000101c505080002d810030fa20380d01c05010700d00e0300c65849001071150b0f046410043d009407549240901c0d251800b4001d42c0002e1180000c85100c030b02c04107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 857545350 1250 857544100 857544109
    0x90c02070b0c0f0601172a0315041403040605040b090a0e0c120a11180a05100e270c09011b0305070b070207061704061104060c0308131e11 61
    0xc2401e035007000f00780c910071421040e4505441a00180f502e1840546d40390801180020340701d00d49806201c0c0d03a4000942d40000b999501c4072519107540c5030003180005104418049201c502c514003841801601c46065048640c90b44558010400000c404000512081e80c000c001004040c4028000520141c0e84140302c040121301943c1c039400686001688030300e5160660b0400342c011098003010420329011032619051403107030034410742403a2a070002e207582c9540c07100d88442c010503000c0d242c1e41200c111414001c01103091684d40d20722803510101d44040350000c50268040418420300080000c0e103882d15510760340d4101105080c1006200000704662312a01e000d6200c1c5548243c540303d4594000e0710700340511460080c541411940403580802155900868540305e03220154171404070340e211030410030003400009400c960160740008000840c680e100c0c010464142c0240d480720420384034548011006541c140f00540040280c1c0c24000b101001d1690f2151403520403480301c0507140342d060104 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 857546600 1250 857545350 857545357
    0x40e0a020a03080c1b0604031511030a0905060a06030b0112170a1e110606040f020405061803070807060e010f0e0a14010f0216030b041a0901090c170601090c02070b 72
    0x46900010101d0741d200e0042041012007a06401c5d8810483d40740b1400012031028060341c44080d050030319240c400c030107450305075200d159088546403c55036a8074102000c900500b541d00c038100d555120f400000b507a0352146228480540c1c0d032000041050346d207082c80c51054040101c0c429207212340110304040ca800d09000c020305255030300d0f8a07190142d48130036110004005441c4a4601844400722101e000c481c0080342142d4071403001c0390000b03085c01c0520a960028056500305680001f000151960444a840241501d501c001c070100d8120343d441d1040161203000034802c03100458048941003407158001c0748405162a468030340f081d5180114030000c1e017100443e03030000c24a50044042c0e1142075a01011498101c13280b8002041c18100224130056410500d10002e00b108004038082000c0000c80020b900004120031819251420300506260082503401c070111036581e1720b11400984c54024090b40070301403081c1c0024001c04e80c42c2400c408064002e1240f91000c41c00795541c086441d0b21110040e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 857547850 1250 857546600 857546603
    0x1701030b0c121608070816120920040605150f030601033207021501051e0d140601090921090803041d060108040503040626160f05090a05040e0a020a03 66
    0x4039500303e0045640513212400141c000801c2042000030005a44e610f90110b41180b03040c0e1400390489014481000000c00c00c0100c014440f2098200e54565040e25860045284200301c40400000e80e4030b90402808010050910911240c00d11210003503107080009143e0107203041c1408a440000070448040c0a6040d0706110341c6e19036a011020740020710005001d41c050034030b0006081d40c00800580c00b1085030140710745403040840c428480c01207030b540701c115411090f01400c00401d8101c20f05e4114210380707034803c1c034424901c0b4000001070303e2001409074042560b0040c5400441040d08800200e5404034030781014140601d0410002d5145010001130008007258281d44407045111603d80500000242c01c8a041190b403009010104201008490490341a400c200100900041c04034450825040c1040186c4580f074042141c0b01000c44610700120855035a00c40d28590240815507140c0600801e6540000c045035050181e0306040d4000c2071004800001c0342d030b03c14000e6002420841c107d400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 857549100 1250 857547850 857547871
    0xb060a0b0a210c09181d061503030702090708060d020901080a021e21010608070f03140a150b040212040602040302150415030507030e07080c101701030b0c12 69
    0x48016241c001100b03007003180c0350b89405010001d481d0340b004003005001e016801015101a0714040140ca043d4050a1004e084010314045110300211058031000200c1d012040700054606030225460003004846995038024610800c6807034214085600500080c400d81c2c100d0a8540c1c110017582d560403515000702030345030040c400c10301541b0520003001c240e03000c01040d03812060340780011982c1e0705030b45041e2032145616078601001e1030303d4541c1c054100c90f880350629024880d40825180c040c45000b1707090307074084c205201c810030003c0c803280da80300c801c400003410200b40e1920b9240450aaa000030b18682002000903042c4200f180341084041410f45045800e2680007a04008504100e580018008079a074022030030039151485c1e648403102c807084c14400301030f81d920004036241c3c060303031110b45440d003464201e901d069201e801050f41c43c64102c004600c28101205801012403160310000c4202550344181c00c1c0c2c0303900e0b503074401e44441d0000d048280e4108042c01509061100e80050728420740300c2e0708 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 857550350 1250 857549100 857549117
    0xa020c040e01050118110703030e0322032f04020904020c1204051c1104050a110a0914060702030312040305040b0d02030703050f160c0c05130b030705010509010c0b060a0b0a 76
    0x301c507101845d0320701c2c0300080c031241400e25460300c44400c00c040d1044190582400b0450305880c2c3d8565007940710303003294030800000a805801141c045002c0103029280710f807000c01616100c0080354060a043c008800c0126048000b0401c00b50605401401030700001605c09414421960f450b10305001c80b4982094891030081001c106034501000c1c250614005070840000011710b80c5c680006a20462040d1b5008649840120b0b02075a0180d0043d0321944c0f40e16030050715912030400003486000d03107101e40650307070b211902149000d00d4035000304d0348032681c014003c0d498031415055522101d0350080094090000c140301c0082c400947c10024504416050780040c1d41c0c4c5402100039017111000713080412205010420008486060301740c041444485040008207032403079180400349038200c0d401c601e80208803031883c60300031704468021207103084c0102c0903158041d880d00011a018054500700780d0000d9404000c040100786081d000680102c0090514140707aa2198401070055100d9140400054030b0f52 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 857551600 1250 857550350 857550359
    0x80402031f112b0b0d0314090a0305010f05010905090c19050a0b0d0e0102070314030a0e0d030605011d0904080a020c0301060612140f0610020115060f020d030e120a020c040e010501 79
    0x8480268400840543c108001c0c41d9000c0407901c10700910f440101404a42860103404c980300d00203450901c4401030500c000360740c6034030740350340680160002031200504210001c5000041030180070f1180c842000140000c000040411481100403600c440c0142a1070ba004141c1b038a40e885054080c0c4100c8125540d1a40e0900131102107a52034a100c00c0c1592042c442000080e5201100000111000c0e0001d07450352a440c100304020f101d040004965441445802c0301107d80641048048401c01d8a0703503071096580c0b4449102003401c01600503402041840042c00007030000001c0c21950b0708038411902056034000210342141c44503000440410520007660303040c1b51003400786043c02c0c14820703000041402d103070341c0108403c41d0207402684240188030a50240603c00d40c401c10005100680c108402541c5500190aa4140032001001805080c003005009402402400300841c0100d00410850780002c00c004041d410040f040760841c00b4a60840e88665a02e0040b4100295000300010301940350 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 857552850 1250 857551600 857551657
    0x30a02060a1509091407061805010305010b030c0a0c1205070c05060712080604090b0c0901030b01110a020d150c030c1107030c03020405070309080d06090b01080402031f11 75
    0x1000708681d0360400000c018064490789040d0201c0b4141c80000c500e050951420010000c00903900c0c0c04144682c0c0c2e0009040d030345c401105003101090110300d03442603840308011025190240515000b0314010004034078200032000c01800d100340c0700e1401242c008040e130b5070185007402200084002036008074410b8140905410f40c00300030102211303c0c51810f04250785284c201c1c01c42d0382d03009003030040c00400220140c035035400c04400b480c2d000c1244200c501c1c1034519180d0a03089987c1c2140040d00c2d00388402c1440d4000c200d444a0b9403140c000070b00007000242d082009090b1902030464121785961440101501680038000050b1aa07031030100342034421120041c540351200f030b0410b080350711068041010802d41007100098a8050f1b802003170a0341c9015054000d001c510b07200034018200050342d07000b07803400c0f58840001d5800c0000d042c402e40580c0300044403402e01c2954080d40c5900442c4001c07000803081c152240314001c41038400306490201e540702e104940c1118200503440031500d95003140c0c40ba070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 857553956 1106 857552850 857552863
    0x4050d050106140d1a0c0d02070b060f030d052a030c07030b100e01180b1e1305070905060706020f0f0d1a0306062709030a02 55
    0x20289000341c000c0c0300e070f4894840070501c5079018449500e840113030070080c3c03a082100c880c0d41401c0300050b00c00d09440034000110200303040044280c080c003e4000341280d01e0007450344440710718201040c8481208d8041d580340c400d400101120044d150003009440e81c1d030510741c10480d981c080c5038400404c0e4100c025000d1407148000714000325580c80005452007944c1c402d0708030a203661170351003050052100c14012118061030500050141ca444540b07a00c46480c651100070440d20b41110108910000c26041005501c0f040528001c81c0d0804001c0103c03807021401003040180b4041c20002c0c003004842c02142d106000000321217050140a0301035410a070400c05c445907035402400300190f25503101d0441d030310340c1508082514007052003031425502d0136400034000d8159999100100031500001045a140b229480100d8040981c990781c04a27111700c85000085a56622000e0080d19110 = true := by decide +kernel

theorem cover : BRFrame.Cov 857374100 857553956 := by
  have h0 := BRFrame.cov_init 857374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 857374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 857374100 ≤ n) (h2 : n < 857553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
