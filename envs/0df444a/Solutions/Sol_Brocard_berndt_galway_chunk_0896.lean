-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0896
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:33:27.100979+00:00
-- url     : https://prove2.me/submissions/35d455b9-1541-4735-a965-bfd4f9a7eb41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 160971223 ≤ n < 161151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 160972473 1250 160971223 160971233
    0x18030c1703070609080c2b030b010309050d081005040e0d030e0a0b04050d11030a0e0603090118060605041b27150908070801060509041b030b0406020d0f020702060304 73
    0x311515112090324078242031030360340000321480d8200c207541d08180415a942100d50400c0315000441c070810703a890029070b4604682a510085c100118101074a88148140f0b0340d020b6086004130341d80c040f0546102c1d0041c100014941001116030b041400024200040c0c02d085c0307481340c0220049a200a000600c03185007054020f00388804550455104030749144001c83c400318942c03406640300f400900300403218848003d1403000015055800c50b001013008402c60394220b40325212075401603400c941c072541c07441000c0b8010400809080300c11001e0f48590820491640c0c051403d40300212010000150550f9074901441d907010b0340c0131701268543d00a20142510a40c00380b101c1004100c5081085449000490800920501104c046100b80c482071020b400d0070300081000c3c0c11103200070081a440c110018803451000b40024020140d2014400218641681d10f10040c68100704080c8450a09140002c02075104100d81606107140c80500a074001c01c50086403032494005166074110745036a220 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 160973723 1250 160972473 160972499
    0x150207051f0507020c0618040506010e190512070e0c0304060b10110d0807090b031e070903060b01020d09090e070306230603010507200f06040f0318030c 67
    0x10548a51154803904205900040700c0030036403003a11100401d8500b40a0f40181c074008000b8a941e05c40c40003400381c512000783c1c41d03002401d0580112408282c5450b0440166051070207007020b90303040a90114401d4021103d9448441200c0701070318a42544100c8a0015803200c0090150320740f02d22221003c40c000141c020091a003140c01808000389450507038001901c2e038041d078022380000c5405082c80f80466001070000000f03241103070411203110b00e408178000b00034171a180141c1e17480d11f4010001c2075542810312440705002250342c14000c4142041c01000d040030300b05c7c0c031040b10581e051100075183c0e540b012030a81e400803030356117590000b6410a00341102a056241c8010f5491040e0340000010483c1c90141880070041b503080142c0000140707001d40013201008100324001d078101020300c4001c80d8001032280140c01945031300c42101001c1c03190f0500f0061803049d004801e20990301407105100403451523411203482500c03156400a00d80605e08000d26143c4070141c99922112802c0100341c1a40031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 160974973 1250 160973723 160973737
    0x913030801031730070e090105060a020109020406030b16052b1401060f0306050405010b090f010909060305030406110c0a05011409060f09030d14030402040b01030b06030405010519091502 82
    0x2c2e0b29003130030062403d80074146084c261144900c074201801d408102c041038030b4141c002c0000d00d0540d4405101c803020648040061241d680a07103400180d5501c010710039840724400341d600034403d01006503241480000c2c00720aa64401e0607424098810355002d019000300c0d2150f403e0f500ea521208030303466a14110b8601c0e000000020152207001e1854441107801d201400781031103803910a0100c03900341005085810b1504014001c9280200520610003d04103440d01c40c0b00495507034000411000c0100c0300240035601c0300d09407038209000403040082c044082c2013a01c40070fa5642104e41c4015a91680da004400080da8100c50951014086035200b0700d100c10720500c0e0907045904c0e060b03020011400d81e501440c403409100301d01083d03865080ca428840085e10602501d0840c1da00c00c50880500558400948000c2c4580e546d00b0740d03185140d009400607806054000d00b540c0e100c4c5440c2c04c28a02921080b035800c064495102c1c2101042d24035840368030085504001d41c0c4010007140d18901c40250300500d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 160976223 1250 160974973 160975013
    0x124060309140d030c03111303150e070608010518040f12030e07180b0a06170402030c0a0612052a070c0504050c0408190b04110a180605091303080103 66
    0x1000d600d02628007040100c10100c3d241d540060681424070009007114912150405000420006044404042c05014050700e401180300480c5030082031254009003101c10b0b592605000300c1c0c900081c0c440d000152541214403d58034042103000b88003521000d03e404960007800700d80c0c185c20800201d0402c0007500c1c950f030482d040c0002c00e2648519007034507001c0f09a000741000b0168040009500406000c0c0f0707650f280e01030b14896021070600902611304803170400140c0740710041100282c19950708004941c600c070700103014001c000c1d0301c5201c028803541c40c0c0c3c0140c0d03440504102c0851030340c0c401108500306001e070303072140000c82c4684414208260350125070180d81a01c260329000c9000d989600c1118065103841c25090b6480d40f40011842c1001c081c404071003030781420b801c940c4000c22214034645521603030060030315011154503c00203000383d075540c12101d60400217010125181c116940000c0584204581142c80d554518040c1c03119070029000c028009405080108001484c0c2e5000349d00b00c80c105 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 160977473 1250 160976223 160976243
    0x306030a02040614120114060d030e090109050708090a080a110a06050f090601141522090605030114090d0c0201110d08010609050f0a050f03011119020124060309 71
    0x540c00003402d072105070700154005452041100190b11703103104005a42d404da000280410261181c1da880500e40003444103001d568421424000c00d4450005250341c40030007803644880356143d1580d04c0081c1800ca600c44080741d100804100c2d146130016007414060340c0403120071b02d0b1580405c1c4c100c50b0004042082038162013814025000503030540100b40c428107040c1c500c2122071605090084c07800c0c0381079101e450201031500704042c464440022400070141d80043c855a650302074004160ba000705408410740304480b021000c0341310001c3c0c0e0418021104110000e0242030002d00c070343d0440400540b808031481d806403515541d030340d028450100c1c0c4240141401d80601c0c903601c2c0381c6811b040941500c00b000407090001031095580001c40907020300410b4510800d1003c4c4400402d00c42d2805001d200e00c1181030303010b440356039902504241c51200e060704140391038000c0c00307040101482540c203a04015500b0178200840712080c0c030030503001e46502e1003041c0041c1454490260024042050300b0f0340d0b84005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 160978723 1250 160977473 160977493
    0x41101170c07230606010804020a030b0718060905180408070203030406050901170105010c150605130b09090102030c190309120c0c050901050303120a020705191b030f0305030603 78
    0x80400018814580440c00c1d540d50000c0c0c0c502180507500d5005409000340c9600349424658000080095015000382030407c502e4072603000084101c103842d440280002e040c0001c00031490b030f02114401c0c10f007140f0f01100d074125807140c10603200c1300402e02810750495406a1004080d40d040d0b4001c540040c01031424914041c0c164001c2800c6a0243c2c0042c2c0c04150001510f00b01540c2c0b040848041000d440043d80d51235040c800000d002802c00790b0702804044042000081c904030316030000c1c00510000342047c0c00c04981c4803e080151800d50b200611400c3e08600143c504d41c010b008582c42040001d0b081440e0050a81d140702ca440ba41c035201c0c0d4101640d44026000103005043e04441c400d410b620b841c4807000c1640780c091100c2202c0d41165025040d10001000b040d140002a2110403a40928a0015540b02405c140c000e001d800d001600d40d1164084200300056040e80e2900101c0c001d0903410800b2015844510412466200060078260014190004079101d4004ae41c0c11100082c140c80f80000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 160979973 1250 160978723 160978757
    0xc0909110d051b030408210408090609032b080c040f030210031e09060e01060501050313050a050304120b09060702030702042301091a030105090a06051b04060206060a0b0c06041101 79
    0x4481c110760a4800081c131981f82d88003c1c0d4032120000b2030346219040c0d86083d0340c0b0415140910080316001e03490200b842030031030f501030001581030385103a000003900c0f82c1c015006a8161108aa00380042400b400c046181000050211000d4500a100a141d000c1c40d41d4288100750424411400c1056668150750898140038080c48409102c400804181c0d1480c3c1d0600004995038140080f0181c0e160030400c0100380d800000340c80d4010000c10400c04414503c2c00c1481c00c10721b00c0007005001c0c3c0800030703000c95035034060400c50040a0103800c03404000d40d43c50700803e5581c5800c0d500c400146e0700500c1904010b10309500400c0700141407502d4202d07603540040000300428000c0c1c110403051900d51552000c461003034100d40100c29804c600a2040e810100c0f51561500340e081405010f05484100240c04180c00040c180c4000403a04441c90b51181d60380c8009481e50340030b4030031510424941100254040100003a101e210301d0301c10240046465070b40e0303000c4008101e80c80301414440d58003082c0b12146 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 160981223 1250 160979973 160979977
    0x20a0602040806060103060b03090c010815040204080303100e070909020f0c06090a03030f11040e280501030506010e0103120e011202040305010209041d0304090e0109080304060c0909110d051b 84
    0x403a01e0001001c3e5400d10400140640d0a5a0405008502c05100300115511f002560100c091030038200307200203840e40090017030049402c503140e40c0c2041c0000307400110760340004003d610a102010403510304a8440b1801410607109940301000145900ca041c8180c4003940d0040583c501c450503410300e00050010701c0b501b0500100d031000015000100c00384140b54040c05083c940e2584820308000300ba018030034040c81d40c01180105e1124950380c000180f601030310289142100740902d00012461215038080c04040c003800d010490381c2d4014600006040c1d8411030110741680e501104e0791085400792002281d01481a440443c100a4141801e58003080144000d10186000340005660380c00f80e10180002d07610354644d00c0e8080140344003034032500d101c040141c130107440c1e00080c0400c6010429407c2809481985005005207000105000401c142ca03803124000314420740300c182c0740d103070345035514401c1341e00c45400c1c04250001081400707401c604580c08554060843c55041004030f54504035010b5507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 160982473 1250 160981223 160981229
    0x906041208130b0901051b0102120c031603060513180803090102180a05011e03320a09020328080403060b0306010b130b090d12020c100309050c010f020a060204 70
    0x2607100000c030542e07003410005105019001ca400310034a40400000000e20302e109131000308032141e80407001e03120400c5d0290100c41d030810684840a8060600d544401d0703041c2d1007a60a40e81014031064100b414034001e0040200f11040106072204002d03004607914040c10315860705101c01036249032100001038028010b980100c4d8038000050b203924082c5a032644840c0103008442c400c41c0e242504010581c4c0c446e0f82c030740341b204042c0d24807824046a2041900902000308002c0754184400ca8035084c0c41032007011042ca103032020b40c9100d1058943c102a1012100d132a64042d4064016804060b141410100c2900e001d81d6403211259030080182c6032000d080d005500111000c07034683c0900c048a180401c2242d01409404100900e84580c2032805214038403a8450010741240124030004075584a40c4050b0b09a078001c060400c0c8081d464200a446181d4085914800e1622944070803d80b8824803a01c030300d49500800604403411107100540e00c1da080e10101000310710450107940c0c002683c41c0050001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 160983723 1250 160982473 160982483
    0xb0a08010e07060e030d0f2109020901090b130e0304051302030403110d0c03030b040e1b030714060412020402190903021507030807030c1107230d0b010b09060412 71
    0x422411003107503604103900380c2d0003c010012003c0c41c0700d04594010914200c050710b40d0410f2072102451600648d42c100c0115404d0819448200101020642a4202140c0c040c42201c0740449680c0b10040c0d4030803075449030040c54010036800d00d17001180000350b118490150807030049a007043cad070f00c000040103d484002d05801158000c0140810140c11000080310007066001502404400d8800285840c001c01000747c2010b8803002c81605d5038507076912507005000e04109a94a0304c4000326401c2d01d610800f00701074064030640130001402d010302046504e2411001341486c0c80c00c0d1910032540388481246c11b00780d074070645c03c01102c0302c0550030408545c035007110354965140d018514010006031620002660042a001300007281c002940300c0318050f4402c54038140080c41480d000d070100c0303500204542d138440318440c840002c241c0c202c05818000003500303006205e542621000d070510400407102c0c030000f046501c0107001441a03083d800040c0c10321a00c09001141000ea44030320403d101d0403118416a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 160984973 1250 160983723 160983731
    0x21e0402130504061203050a081e01120308090303091b0f0a03121d0108041e080d15050609090f0a11130503060a0b0f100504030501020c0f100506060409020309010b0a0801 75
    0x702e00345801640000c2c003090203004001005c603180a007292051040e500100500c01c40042c100900e0190706644454030425100821344e1130b507019603028546160190080352401000403140300d400005c4a120b606041c025014840741e203008a5035400c55a140b142d03114001c00b030071210540b280e09400c401540190200d81c4502548000076114000100740c0580141c50000025400c0e40c00602c281c1e0807551003481c0f402520003c40051100300e052071001003845500080624140d501a0031002030407080d414003c05240e40c0c2c60420055118011401da0803103000c00c0018032400440341502d078131103410003020680454070042d481c266071014a070b114425000301000c0c01a410f040110311307848104030b4010402007800400007a030303c4a1701603102d840780b071900ea1a111031a20840a075401144e002c4025505c2d4405209015140c01191000c0303603852141c54014990f0340080d01441d0700820b0068011807410f8184101c44020b544000d00c401c015640303500f0010712039121450030000415507a00001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 160986223 1250 160984973 160984979
    0x112110060608070302040302010507080705100f0c090f0f090b1903050a1a0609040b22060506180f010504020a170708101208090d030c0c060203030402040609060e04021e040213 77
    0x600191800703041c943c00c16205020620042c0d03000b004940505030442021034440040749842c07864010220740a480341c07401d107003814003a044244c011810201c01d980703900125984030384c64111913a0151098417411030300c0ca40200035443c01c50b8015001e080028102d000b0006440e640224040a154400c5429a009803180010300c041d02487c0343e0400c0655840a4003800c08030000382200c02c0180c400341c4502d0401001c9219a03807168405892081d40c00d81604012001c1d0074102c4c0144030468080d4014030070120040074130710358941d5181c42003100386014462340e402c280600000350001940d610a1292186c4100c2c0c045282c450528890310a581e035030211490880311013020f4550542c0003c0071180f00c02e03242c2000400c1c01047d24840001511111159005810116a0441810740107040d14028450100358140d002c07000b18800c0d030080e14140300190b81d07001a18201c451900c5640141d411401c0420b00501d4107a2148080d11008020708484905c00030020f01260b12407444c2d009540d041c0d040070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 160987473 1250 160986223 160986227
    0x60609040203120a05070b071b1202070f0906080f0102030f1303050d0615021b0d030503061f0807081e07050d09081909050f06090111030d0617010e01091121100606 72
    0x554072623142d04c0c0404441002c6502c8540d5030324103410003447e12000c003008440300b91080090000600304400300200c0a07586840401c0180002c1c000c4281c04c1c0600d00008071701e00414000c40307001d0407688903451200c0c0d50721f0129198460011408508000e070800241b0158080350250502800115800d10214260804060300d81802c2c1d000183d1140e03615401c00106a444100d40011940c1608201b9500d0352403200050055025200000080d5040c5881e06503280e440040c49102e0003294495031003d846942c0c070003450a0745a4404500319540b40300040c1d410348140042c00000042e02c00102c0d1a00a0743d0b0f504116401c0312107101940e60341e031110040e030300c0c3c0d1054041c402882e0680300342d0310740100500413038024030454040300d05000c0303142c6a2801d040800c0084075055440c0a000300401034440d240200c844c4060520001b00d9030810f04058140b84042c455201c0c81c9901c0f40c10000030601c1c0200303000c003040030100420412401d00e0712018000c2000d1001000c040c440c1100040e05034180000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 160988723 1250 160987473 160987493
    0x7081f05070c0321022107140f0306150d05070e010e0121021c09050601030213050613110c070e040b0108060c1602120102070c080717060609040203120a0507 69
    0x1102081080103804203003c01d821a00750900d04503a029010140750300344902c84c1c0644241150f120880304401801556412540c200320f004000640d40c40840002c907942e214041c0c001c50b030440345210001c00100360070740362203145a601d043e00801014100100c0c1d05880045400071181800800d10030311840030b8540e03001c041e03c280c030701003420301041c0015400e0300e41801481c0310804190540d40000c0400860b04010309008001c0c158410074460103055150031502d440003803204030301840d203015032828000140e00865215270320180a0300310307100500030080050310085105075030800f4200440b1070369180a00000c4081c1000342d12003442401d03e490b1805911205900144117900303d4014400e0050144007181c81c4064120756030040c045a0b40001000f10a0030b0841d0003541d03100184a4041152503115202150342035000ea9800c5542c1c2ca0602c00702809200303404020340c200d140020305d107152005499403c01c3c00035003160f003111054412503000b0760200d8180c102042c2c0128240d0100049145 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 160989973 1250 160988723 160988731
    0x20d0c0602010e010c0207150507050f0709050703020705150c0906040306091502090907050a090e070e2409061c0905060f0604090b010501050a30061211060c07081f05 73
    0xc20940d8040b42009469550500541040503d10001ca1441c41e104c5d0007514240e5801809440c410513440c0303182c80d912241071190ec00414140400588034602a10130380715500c2d0490050080500c0c050244e81400310003c240459041c1b082c0944a1941c44000181000c3d500c40d06001601e10194244140400e805400343c41c007590040141c2c104603101c4001c1d054010315a800c0076600d801b0700d030109a40308216900825080c030403400030882e0496220040c4000004156003040c106442c031001c90850107800d9045000c0018200b0040c0b1250030301e9401048451034260b480080d20480300c4000041d00c0074600c0c04e517526030141c41440310f900ea82d41d102580000c000c481c2084003c2c000d940c3c0c1c00011905219440c18800d0128015072813074061480300307110000c20142401c4c061321500982200944104480d202186400f0000c0bc0d84111030903030358421508a07603044144401c003020840306031b02040329201507019204000512a40400c03c00140c00c5469641a00042051381c00c9012100010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 160991223 1250 160989973 160990001
    0x40e0c040b0405060d020d0c0c0b1e15010c120c02120a0b1504020c0610060906050913020a0504181a0319080a03091401140603030f0a03020313020d0c060201 69
    0x300041c019010031a8116034056854079151080f41c05a1002401142c4811354124105110242e03003580c01180c02245034411b03500c1103050f0300c41642850444d00d110388000c015a082030081042e401c2200c42c2401100c0d41403402c0107001d4200e40e83c1c0c11040c83c441011001241d81c042d11002180f03000440e0031103002c415030003011144030039211012900000380041c151080c940c0e4102c3c4480d110354045841d10b4000d5001c841550414844a100c2c21035030707119000026504441c081412446581201e00a6a0003002c2c00c8007488807010f003800950280d00c040c0c003403210400001070b01c0d540950342d084100700c3c100000030350920700d802031000031008001d91130b00c2034026a244580c484841540c4d07104540d048501281c85804200040e0700804d05400040c0416000786109461010305404c0700d25040421280fa0f0310b103031207850505650f8004e4900303440e4100f00501c5190146403007640076543c061100c0b4110040144507030085a01c0f821003200559101842d210240241034090250076a04589a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 160992473 1250 160991223 160991227
    0x1e12030c062d0412030905011b260115210203060411040b1c15080604050c0a0b0f0703090f23010203041202132403050f06250c0512040e0c 61
    0x240c40e1180500c10000d00c0107080104001529041c20b20986c0b004581b1a4414001c0010320310091194075444002c0d8941400640860921015086040b143e140140324683c1520310903400e02c010217070b100d040540300d8030403c190a5806216101c201aa01c0f0215251540c0169a82071480521064803101e050201280d1010070080003440a22000c45440d808080040d0703e0342d50003400a00d028100b0304098030440c0714100e50200d500d880c04a06140a644504100d4600c800c0d0b00c0d0038013401c40d40c14824240c001409000c1d0b03403c86684d11008141551007458281c0c80c51703895002a01c600701068001e14404070120340444103c0109003500031403080240000c604191628004011041401c04000d004904101940402c01d0868019603000110403844c400d42c02c011004244904010b0310003078800f0b00c28951b003a200c4071404242603002c0d036403086135264412500018411003a425440320400c00c0244004240803038800c2c0000b011049041d01c40039500c500d06035921010010250140c0800082 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 160993723 1250 160992473 160992541
    0x30e04020406050d0504060603020a080102040608010e0f040311070306110301030204140105030618030405062803020c06060105090319050f160b07380f151e12030c06 73
    0x403c00341c60311341981d0100814182da492400e100546040e81c0005e4001422410200e0001010340141040e1801035442c02000d0f1f907100c0c0c42540680003a14407148070401c0314045008030b4494070110345104410812145015560340c1e50000711843c08602403d10b0740080018001c601d024080c01c80c060001c07011985031541404006a114000541400c40f00d001d0101e003014031510a00c250740091900800716502c030303040503154809290004804588206521b20302d181d03030a0003882601c02d04040d6a0050a40743c0c1c40000540d11503120307116442d818400c0600e4003d030340480d1203647c442c0c01d01c2540604480142640e030f1303900e092003842403549a0b09029600f8425101c0721019103807007981054000f0350014500c2d50400f0748840d06180c0c0846550600c280e1019042a0312403039028440c2c1640141a50791000000c1c030a410a81c110300d94407007030814200711000a14802e58102c120f00801c030b00d444140c8281014915407000300c0c0c2d84401e0f00310004000201050b445002d0300c0c642c4000707440c000055 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 160994973 1250 160993723 160993727
    0x91d07170f15220605010201060f0b0708090a0e0a0b0406060207180218090a1a09070507060b010201110711031605030d181502160b0903100b040e030a0c030e04020406 73
    0x280142104140303040c0c0307050b0350b1440c0e8480d40c281c0d000c000c00003002c0454100c2c944402c07014001d00d0080c180590f090040006100c10400c12110440b0048243c0c00d0420015a171010380c10b40c400503200380e100b80288404508441c8502c081c0c0d001c0c8501c0e110000c2d080c4495010f00042d0750845d8402d1066402001c010010003200346040702620220400042e43d030300ca00d02c0c43c200380c4c1c10640c2070b031504840500e0030406036242d40e5004000d24652004100c03000c2078000100215540115150b000056052008a000030810703003006804110500020480d081d1603e0103080320740003082c05403105004500c514085040501c48200d50310651542d00d00d059048c44007280d40d8000010802d803c07c44040c014618050300d04807200007070b040900d04074030f442c00194030080da50600c0441541680c203404000103200000041160325441c000390107000c009003550b031500b005194401405402940350f9044070680c51007400209071310040340e1140310b00c03803620307050040900c4010100d9500982c410032091180503 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 160996223 1250 160994973 160995001
    0x603010f030209060409060903020d02070b09010f0f0228060e07050303090907031e020c010c03091509060b0916091502060f041109040b060f0a03170a091d0717 70
    0x794059940380804d446071001302c0c00034041c0d00c038042c061074501420801010782c041401c5080b10003a0342110411520748046940750f02c181034074a80410a00700410400030b0141110305190f180900550301d0004402c0b0404070700d841010148101d0301d00c0b10b4240320400901e8403031080074261480c01000c6650528000ca907403445900c1d6007901c00d10700b590002c0c0519102e41c0140b4080c27440705481c0c0340c011101c3d00d0346801940080c0f09040641d4240807901c03460700e1007485280205900615601d03456225400004010700450b82d099402a44070b102d10000c0c2d48030003058074094035000c134490040116403200100385850f1f40d0000d0600381c5014410304181d235030018540e6005000c0c050b42c01c41648803440c003003031001c21010a050f00408280208810b00c224045a14403802d415101c1103c8001d0840c100000920140030041840800190312a0b1462128020340402c0d80c0a0825811045c3c4424806000c1c030940c199401601600c9002c000c0b400d644038101422010b80329468200c1418aa4000a400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 160997473 1250 160996223 160996229
    0x503090606060f0c10090213050f0601030c02030f180a0803132102030f0c0907020307081b0102090d050705040c0306030b040b19090609050f06010b0313030203090a06050d06050603010f 81
    0x1007a02003851840b071446042283c1320202c003103080b5007080d03609541d51405443e00c2c05061b8418010000740002e90301190290b07601c6001c100e00d070204940d403600010341c02009141240c208510003440400102d92994008201c151551449c0440d5506079808101200c0340300e0300700b0080c0341c01c140b210580c1800c11b01c04e541c0942e01802da05002c141d10300c1d140481040070b4810065810321070708608804d800000300d0600505282035603401d425a807410b001380d03a64440d9403c020f02c0034404011038892090181420740c5480e462000151601000c0800205a400b008000362040d802c44030040049240c02d1045c3d105106190400340318072850f5803280ca800500007132000c1c1c002081340e40094101c01c0b00190034801440c1082c010021405c0e203052820080858800803565485000100308400d0230015070383d41200c0303161031050319680c0d41000d16810002030203011400d500c021f200c3c4203500e54803040c4950107030850303a0301d07640c0351110185000166150340d8852801000c4c1000140b080429000144043d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 160998723 1250 160997473 160997479
    0xe090c030a0f020114040b0c0706091d0604060e0717010603090c0303030203060a0b04080703020915030a14070b030403030c0e040b060405010c021203040b041502010509070e251e0503090606 83
    0x6641540016175075000c0455a50494400002d40452034411030806407916551000854001d680c60f59015550120340d40140c85000c2c0e04054200522128000c1c2c0e03550001c030250003c60000d2340e42013040740c051415603005010900100210311600302160000d4010030b5640360500050304540c03210b40404000c1c1c0005420541c0010003d040b50300c9800d8000c004040c41d2100d1a0358030f59980c45c05407150a68003089120700d40c54030102c2c20b401b407840c1000480a000402408841e102599200da0030540100c00c0c500314021040002501c18083c000741d44254000e440205145120030002400c1e00c0040b8000c038481e500d480b040f941c007a2500410340342503400030f0030700d0740d03440406e80000781700c1c401042c0c0c01d4140e0340300000f4042942e50304400a0812521b02d5094400390140703e1324264240c0350b0031501150540c5c407a074010442c0b2103800003480d81068081140100c0c40d41c03403056856118401e9410031003c1006e0940c40401d117404060f0303c1c6070031381d03c500c3e02c64110304002c00c1c1f168541e10041d2000344 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 160999973 1250 160998723 160998743
    0x405041b08030d060902040b0912070b0f1e0a02061611030f0a0e0108010e04060914012d02070503030c071a040b0703050c091f0e0411040e090c030a 65
    0x410401125180d64056280900115010390303264585aa2644000400c11803d070404900241949650003aa01035403104000c2d03604041a0400b48900903174031194090f003610030703c01d00007102e0f018100100106035030b010002d03030740c6c060503032074848200518100d2500c890fa041010001c1240e02041854004190000300c00c2d0040c4074141c01c980d5001d188000b46460301000903056a200719540041c562262540c6074400750522034001500e8501c0c0900c039003005800c08000180c002126940b254402500c542c403081c0c00d121400404508440c1c2461034021440101c51070506800006204005103184002040d450300100d0340e5541c3d22400068184000582c0c041140420001c0f05060000e40c0f0030b50718007154903443c2a003805480d243c002e40d1100f0220f40340c0710100d2103595112044402e48078000d060700c5000310b680c06c3c041c0c4252001d500c603801002410703040340c003140ea154061440151a8242d000b601e03075051100048445c680038118001e44c0c0e21050240506450120740012810382000c0400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 161001223 1250 160999973 160999981
    0x8041b1d0a06180e0d0f0c030e06120f09011a06041e03060c1d0a0b070206160c29030105030a020d05070b04061d0a0602070b0c011b030b101404050405 66
    0x400034002070780081001141c3c240403080c2e0000c103940403a2131008900102c41c00300c0c0c680035090324003400040790b1a001a1141554001090043c400501c44c0c03032002d004240303441f49800c0124514001502c20950221030072082c0000100240107060690302e422040d0201011010000340c00d0780f03d02d1080241c00c0185001120882c0f100103504001190084000d201942442034001c140c140003d072141e01d00341c00d845012101c1d046c0071410700195070215007812f142c45401d808018041d080f8800607010100e00358480c000190600c40c040000b800c841c1040118120000c102c464440040014401d02d2041880100243c0d540050503070755058054685070400c181341d040c05402e000b07040e04403415140c00024006030046d800300702906500c00048580314070412610401c04030702014840c0c44010303400420244240b40764800100107400350315000040342c005551512065a0320a118030004c0f82d42d80316400001c0c00c00d81881c6403100d1892130300c02002840c003031461845004d80d0264900940c0e0f074200103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 161002473 1250 161001223 161001241
    0x4091b27050d05030306090c03010f0b09041e05010f1703071103030c1c0e012c010c06050103061a030f030703031d0a0b040203010e010e0303130303060506040608041b1d 74
    0x40406000003070407903407940b02c00741401c40e41e07544242c840c2402000c0d21400140c2047c440c005036410f907041c204c0c103015018901005a0700da81c000414080e8401d585014180082d50015181002d09000c0c0324007141c3e41d807400c0b6141040c40c03e15070103140f00c1d046082c9901620074011044501c0c0c1584130380b030046e120010801080c6113014400640c480c0340f29022410601c4c0414203807601d01d0142544c0e80500921000300112240c010042e001031b40304551031484c07102c580f846201000208410301d0800025210380d141c01c4103a0341c0031b0340b055610a0707841034298080006080d030b00450300c40c2030b4020541c885240c03403402d40e00e1280e91009020103076121a400c02000d1102008007010000307100b21841101c590515183e9581c0c00ea8049109601e0016040324600c010b0080260b200c1214001d181190b0380c02d0040303210000000c0045007010f81d03c84000c205a0b0b14080580090007040d5101c0105240c64603094035034440e42c0c29001c03415200d0020402111340050820341d544401c2c0111211583c030b80d03080c2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 161003723 1250 161002473 161002547
    0x80109050c240d060f171504080c030f0405040b04020c0303070e010e06040e06040f0606020c01110f0105011e0b030c030109020702041b022404051c0e06070804091b 72
    0x800e4030a424002400f09240c5240d411803000c0e83c3c22400801050342d624130350590452401c28800c40781c1d40140f0008140036440c1196560f2050143c0203103440d0001c90700c81941103900c819240420300001103401d202a0030680b0408100c014140c03070071442d10660b10349080d62400010144030401c01c14003034000c0701d64821110801250009490307551150f80760a4215080403088135994044c40c5080050085520f81d030085208850306900038125500a113401110b4280040741490000d100c9c0391001c0c2e20924013403003118001c0041000d0034403211490103c00625440b543d01220b00c21801740240701c0c0b610100001c8074110b4180d8080140e88489070302c041009480104004c00480c04070442649050340c000c503132070b0508031240650b5003105030110312098120105840242151b800b40356000070982c5515034001d019261403c2420100c0316030340004080f81d11200080b1541c0348041410480320070745014039168802100d06552600c02244001408000c40c00d042e80c0311400c0da0040401e0400305091 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 161004973 1250 161003723 161003779
    0x3020403050318040c090308091e03030a020606010807080126160e0106110a0c0512030c0a1b1706070f0e0d06051608011a0904060b070c03030801080109050c 69
    0x401c0d81d480d00810001d1509030080020094084d80c21300000750107040c418001c810035654428071160400e402d600c180140b1005000c44c50b161410760159044880d43c00304040c02c24600d0b29802000d40d0720341000010030905019004406100c50640140002c55000070100d00c0c140700e102240e4040d5418070b69407464404000c08030400414060004078050055610141c143c1e46c0503207608005440091040350f8a148400d005840c0440b5441c0a02952510400d10504041000c0459060056100c0320754140a402002143c000260000c0c61400d003003030007804001030028203d084244914100e01940311400103142501308003040c001d0041d968018496000300100180c42c0c0c820221440c40c08038014902900d009100d545442407440b0003620800301d40341600c40090009403002103480f0002c0a64001030002a8429194800442c0c0c0022010140c034a640c0030700c0040c00b0300c0e072031070401a0200c01d06800c04000781c0d05000740c04002c03e40000c5c141018800c2541e002c84001c400100c840782002d8a81 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 161006223 1250 161004973 161004983
    0x70309080f0a0e1c030203090402030a02040b040902090103050f04120c02040e100603060f05040305071704030b0718050103050121080909010609030b07031404110a0302060c0a2a1503020403 83
    0x1040d29015198001484002c1c83c0b001c0d03802c0f40012014481c01c44641009110041c0164002c1200c02c21030b0420381c001d5134000aa104001d81402d49404142143c2d4200740c108454280d80890030090030360341402019001013100344150210304041c1c841040d5108242e0401c405c3c444488041000c540710b0780c0c00202c40c24a04410399004500343c0700e120000d484030b44001e55a0038100020b400040b240c42c410a800f81d54141c482502d0001541c1d103403001e4600c00c10365007860f038809200c00004100800c00c034900c22101030380d800c0c8010b1031041c041d42e503152640e08800d04040c40c24005008901d11040069415200f80d42c41c00da0b009198a0016014462007214540045d0b804000040c4107070071000b400c0680b84036400c0d4500c944c2d80c0c00b0048003103818110402006c13000781000b10340811011620340c030282a01510079515a80c40b600401c41e1b40d800790311185110b0344141014028089800071082c40401c1e200c500803d0005500d000340c01180c0140607182510041c240500c94242c065411a801151302c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 161007473 1250 161006223 161006227
    0x30402150313200a051206070f051603030b011101050601050f090a21050d030510030f0f050601060e0406080f03030601050307170a050412020a02031218040f0c0e0117070309080f 78
    0x40144010440320801001d0080d15113440100f0070f0310b0020362542c001d2140354018034081d5584902100e00000c00c18080b03050050400503050090390102c0c3c0c4440c154043d0320045002e9620100042001918103500d00c0240d01d01406e000d416a13120003112000c0354541402030b100c1d07505000107408481c5c2a44001541c0c045910b4200f902142018034a10701405201512043c220001090f02956802c80d22000c0f4203110781e81c04c1c4006100e03032200f128168054810b01c1151a4950303102c070301c0c1030000c0e000303c0041280759007440c00c0707803078140a000040e008001c05003150340181180391795a130001902590602c40e000c00068100c40c4610382c0014450800c00400e480c0e41400c2d11000c005000940b000c0d954080801405003d150001400707100e916400340040213507840300341140456030094481002072145280d029283c1c0d541c1c0c0c1c00741c250719152045001880b012000c00141109140701d8405040c844410f188440207051030700f40c4c80c5e100c030603410049010303549440d0644192041c0394101400c9100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 161008723 1250 161007473 161007503
    0x50f0c010903020c030a0b01030b040305040308131a0406090e0406290a050108130b071b050f060f040f11041b0509090603030c0a14070302030706050a080705030402150313 75
    0x20541000404074025000d46060308050f030141501c0d94031660300501511101c0c401040040c0c1c1280e0305681c00350291404500340342c2c4035038910361258400c00301e0b110030b800034510502030b40740b800304048003c080c0c3c01e101e50b00e0b252500710050b000350294401c1030840d405100001e02401159000f42c880704c1200d82c5040140034004600200c0011201d100718015142c2c00804105540505803203409090120002080000ea558a00b003901c0b10052a51041064070501c800c4143ca03041c90703003079465208101034444581c0100d4501e1a00d1070080065400f40510001d00020504001c03c5524094110500c1c400035a4020085009059141c04501f5035200041308500d0040d0310501801d40000111071f1421203072900d500700340d80c074058007040d054683c000d00c0002002505004011102100c038070207482d4003035941e80000342001481c0e440f08000c0b4100040003032031540d005101c25032080300350901754251304007070300031a10b00c401c083c641c030400d81c00000118140198050006510580c020310000c02144 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 161009973 1250 161008723 161008747
    0x30607120213080f100b030c010806040905010b040608030d0510060e011808070e06091003080a0309050109080408010501031b060e040c030b0d12030e0a11191701061521050601050f 79
    0x61701c02030240410f00d00300280c0014640030509a80c00c0905075a4003541d0340718001003000074200504101d882e0341d80c480ca03428594443e4020342c002042e4071006507884a0f29420200162400280081241a8846010300140d60405400304040f0710a2804546440d500c580c000e0140c01c4c1350b0014803041c854450b0004e0400d0b01e004d4040e1103503c05490700c5c1600e880d500f44409003e220317400b004203500403c0c0018100c1c90b12036404a90351500400012030910610303121410141e025401c0f48540765191001401440b2490b0b1601e81d910400301038210002e480c1580061082480c0008244940d44540300140c41c107100f600031011600c0700800c001803000703d529048030751001d40d11499000c603080608146c00c80c1404200c030344680e84c11042e80510a4444400c00a4541d4080c03e11040d800c03c0071401309088030a400c3d452000b510300000058100e0400c1c40c00f07050032644a00403c100440c01c031100084005940400c01104e4446c0ba0114958442e400103075458042c000085503505400f04480000038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 161011223 1250 161009973 161009983
    0x30d11070e040f0b0115030b0409020102100e071211040501080f120a030e01050709050a0807050a051302160c030b280c03020903010f0b131b0503090c0402120402030705030607120213080f 82
    0xf4106d030310108114400c480600c0251000440c000e40940c011350414540b901c44c5810044400e040b0f00240c035403140d241c64440d0003403074402c075043d01c0800c40343d6640002820584986405019008000c2030b4600e66140c1060340e6a1111a1b582c1d0014004105442014020307004600c180750b0b02c2c0024080c61800000081c104016032044500c1113010400c00500302c40e0101d6000d040d01c01c06000b4001c0785081200380f0510200812070050400da0030004000b55555254400c0210303441081e41480e42031960800183c40c080c007810041c004a00702011035650440d01864101c0710f0000b903400301345612400c0c0160000d0084007003c0350103500f002d071899007100c0300ba030040110140031070fa240000344140744d49100b119500d607805242c03004524900c0b10541d000f60007866110044104035000c001280d0040b80590304080c00d1103a0b445409800c0c003003140341c2801a032024000075001000d0720304d4013120041012000c1d11085450a034005040300742d200c4a58071a4020380302c0c50048070440d15541c0c0e140c554070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 161012473 1250 161011223 161011259
    0x100f03140c210105180d0e0d080a090306060b032e0e0c0408060c03010503070b030a060b0f0a030e150a0b030c03010903051b0703033009080306030d11070e040f0b01 72
    0x95444d02002a8503c42d10f13a980554031800ca10090284185842007030b20030b96403e14029504c05a1000800b00081c041e10040c00d031946681d80342640540b070351502c1c07410750b0b80c05e07048001c1c021010300400c010003403041030b00800c1040481124240f4018402c010010071450740120740c540f00840c00b0002846812001031088070344603821143c0681c1c41084141030fa010a000c1c29074140c12a150800c1181d4060001d10380007401101c0003d0060307a80c9001c110941d10450002d03400180c003090025220344c06108900781d0141d0680a00700440502040414400005119048281c1d030780f0951011510100150b401941c40038000b0400c030303c0c071818094000c0c2c00c05c080d071144c4110000c2c0480074961011403140c045a5047d100d007010f03600c0c400e541d061007a808502d0305003080e03040d1b41c424041802a0140048840c01224050f60b0303403c106051500b0322100c0722a41c1d091140c000116191442c00080c0c5808582401811007103e440c2c62425010010088201900c1c07a040c140002c50345580403140d154103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 161013723 1250 161012473 161012539
    0x1210c030c120b060d020304080f0307020a030e04141602030f181906050307140708120f060a080303010b0c0a05070602010e07050a080d0f02010209030a031205100f03140c 75
    0x4070141c00d104003a070315807055031138002c0820701102203441c51030b4000d150080e00c2910114103052100010101a8100315040c900580c40070546c842410b0300880380005079001590300307002203580c120003564180005071052003503500410f050006e00d8400d206030f8000e04034450000d03581d000300004441880201152441c481e080302c1181d42100e000054843d001c4a41c80d8403024110754075000700380d0301c25400824030068180100000b000240e219401407500e46050500d400c124148245d082152031001814180a9a0080c43c140b02400c2c001041d00d04686803400b02c0c40c0c1e43d2a1110f03403142042d4485100070319034820000c0120301c058040d01f1248034045c1c04801c42e61043e983e1340130800510994468040c10783c2201012150303086c45070281c000703090614000035140400c100003081c60001592016000224400e0303a09000080394096150840c000140400442d0b08100082c3c1480c0450321004100803210703903290380200c10503c44183c6814000744180b044ca2121070034445c00c4030604c001104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 161014973 1250 161013723 161013737
    0x1c060b0306010506031b181002061806060d1e0f050609010b010e01050a0e011709010c1b0201090b07030903050604030323072010050703020418110901210c030c 70
    0x3d0701c1c105241541d03c258220f002207030400c000c0400703080c8503a1000300e040c2d03440c2044d030b4556440ca44586d103110890a5180e401001c00349002d02c64100c85e8480d1003504245a0080400e118a0b41c0d101c901c1d40202c26040382035071804a41c154045802c030344003030070010040d560030702441d42070010202d0003910460b92900280001001c031801150424100082d55000c0b607010310a070360180e0705c0707004141c10b00001030500700c00c3d4003501004200d0512040301d283c0c185a444100c0b0302d039241c0e40000c0b02d07644034020b1408405030400300d82c006031130500310740103500b45008041440c41c10b140c40349010300004d64004040d00d0040c145414000c010700104c48441e029095030411030541003076080305142c071031220355031801415140074010300d0606042100c80c40c4c803807041c1c000c0c041c400105403140310b00403003c5880c016a11450700180c03801d41d003021803010022528160803150350141c19012200d100b03c0919001e04820b110201310402c400f201042141d00d2460b106041030115010b0348060719400494607114 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 161016223 1250 161014973 161014979
    0x23070905130b1518210d0e0a0605130b04030b060405010b130306020d0213140907020304030c090f0e16030b150109090207050a0b04080703121b0e1c060b030601 70
    0x602034400029540b0b411200100c00e001200b031004001c1c0c444001d04c1402000300754580c00010b1807040408400035000455070900b0040f00c0c90800a18051098600300020000c0220002500c22981481010244a000905510031441c2d6400301ca01070880034040c6038603261a82040401d41400310f41050082e03180c1800400c09151080503104a1178120b540e1103070903802e6a44d02c06c080e4010031180c1401640a00400009250648034000580007003000f00c81501280801c0120461000d031142c41550010001400403820348461001512a1088082411400702c440d040082c40d02031200c0c0180c1c05100305511030042e0300d181d010100c0c0d000d01c29200040e00d8000d200c4001000402c442400714103004030810200701e00d0340140020500907426910808459210034010002c100c8003160b80c0c080001e8028201078020780107091100d9114400c10103d05400c81d40e40daa805d600c00664140010f801c080501e0760340d19143e41e909580603080c42c0248404a14103413000d846848015480307409480004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 161017473 1250 161016223 161016259
    0x503071202120408032d040e0a1a0306040605100e0408030601020708010c020c091305030f040330080604060305010216031205040c0501051c0612140703020906010323070905 76
    0x150f01030351003940245262104003010001901c0750003800d40300554140c289401080d9454014100034404158440711903c5c0c0b00b103030754048403400d00201c4609581b00542d0071054500080881d40702e0b034032002c00111074076103062190710081070760300000580314510208410000c101010314040c1d01e0070b8003250280c5480b0b180070b03803d03141107400e1600103038007d40045081d0b00d84100c5180d0490401d1704402c4004202e52115800d41e80941011b10080000140030004c01ca11070b000c8c0d4560f0b04000c011814068404009140300107514101c2c142044401d001156495459034006c01c01035078400002c46d52140d00b5100b0b42d00c000405002600420603138400c01c11a1900ca01880d8442c907840342c60071004c3c6040900544072500002850469134500f42c110714031142a03881144058900c12040d04080006c07407070941d0b05c990203001c012000380c0124038104010f0325207441c1a5040b02c0c2c00d00340403680c1c0610010381440348200c50a004480d20b000070a100c0a290014054010b4500603600000c103002804c505c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 161018723 1250 161017473 161017477
    0x201050f0412050a0504030c0e01060f140a0f051207021c05070b01050103180c03060204030c05030c010905010305091011091807050304020409060221060a1d0f13050307120212 77
    0x8064034440d0307920ba4403005540f180004040b0080182011400d0075200c1d00c0380102c19030240c001100c0140c034200140440781d00143c40042c0f01c03440b0f1506d507040385182180344c1c00318000c90b070b200000d01c02d0303200e40d1003801c60164083d980c0340c00080c00e01e0b43d414504810002d5a074100c0044013001c010244208925983c1302e40101e0b00b0f1340b900075000f54030716468900118010111000c0e400010402104070a00054101010300015030243e61701603144d42c29070401c51183c0d0760b00d40c030082c82948000c1d2a00410f0741c001b00d042007120400d090001d0f140d592030031220300703180c113028079842c0c3c1514000d4924040c681007000740038800415900c0400b448441040016880380076900311001c514240001401880e0640100c4070b59403007580c025080c880c480c0c03501d1000707036100200351000c444010308201d03403400d041c1451001401520509040d01540482402c010303800503004441080b11140040c0c60074000d1701c2181c1c6d0440d800400c6070350325070307160400c14004040b110070500140104030410f26480000d0702 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 161019973 1250 161018723 161018731
    0xb0a0903080a1a190b0c071a1606050a0b0a0602031b010c0804151e0516020102030601050d0207051504080c0c0301050712020d0f0c05090a05090708040b0a0b0d030f0201050f 76
    0x901014140208020401c55a060300480516815020804905c40f22604041c041c1546050010034681b420b000c191a014912054025800a000c0c00b15220015480108880494100c1c0000036181c5a8800c0400940310400501d6005450380c034002070541c0e0b0010091810364000782028051005210310507082e61000100200010014004a008504141400e10081c01c9036a40019103452008000302142c640d11012004690f80740304104101c05102c2d076880c2003101a20085180d07240c54400179000e4020141420b140c1540410002c007000420000c0381ea100ea1401145109482c1900d03041c007040d80881c00002441c01030411a10f07943c1014060305010700d000da2109072000c450302d04440000c0d0070146034108643d8690f180810000031910841c11205081d5031a9903480d80a2030900c542446035900090184107d0005c004690b0341c1b0108181c0c00c150700500580d40c94452001c40005418445a04c030f034000c3c540c1204808242e00300c880c0000c2c8280c00d4000b032115a50b20411b084003e04119 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 161021223 1250 161019973 161020001
    0x408032214330f091507170906070219020a0e0903090a1a0403080306010c020406080d0311090a1a040b0a08010311010e01020a0209060301180507170d0203070305070f0b0a0903080a 79
    0x200481d220300101c403903c65000540c1400c98403889101d030808a02900151024800f0503440c043c800000c4101c0c801d5181d000000b4001400c140c10080b10007542c49158200d040001c42140c0488011036a80e6207034080144280300d0b0342c0105041400d00b01751290f0000c00840d129001d61b100004100071449180080c0a411101300c500305032440c0c803141a0b03580000c0031641007090740007a9a00680d22441a07001819984000708030391000110301908450f03071500ca13950740c84010700c5060807030358070808064191039007506280e1110003e0480d1000034003494006070501900490290000d9038801151030480f4040c01c000d0048404c50300041d90183e0b04541118010b8004011082c0541010801c45801c180d02400000340801e40d011907000801c02e040c0203c60369045668200010f0a65105d8038030400703e030350040c1100248010010390340744a40000142030044c08160344090266948071000d21903008003c104072440e04802d610700408207e4012000b140110001c141910310b0f03842050708481000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 161022473 1250 161021223 161021323
    0x1706250c0201110d0c0201020f071406070f051b0102100204180b1f05071a0f01090504110a06031407140d050a2406020c01080408032214 60
    0x1124115590080414160b0500c0500c0241600c0310f0000c100300b0507090450781e0f80c4a008021807000a08055481e010141180d1000f03405109141c40a00728291080c2e0441724180d54010034900700361240980b402c040c10501580c070800494031002948010081800d03400d581c50440e441c880340d0b003213000303e000b548080000d000e9074131002045c9a00146030000700400039080c0b1007071700303110a070350b23041c43e071420000035002003000d004104e0011561075055483c9503c1d4045445c0a800e081c80c200780511420030a03588480104c2d040c042c1c0341d40009034400000c0e102d124140d45900000d4007604103000002d084200100000311003c0c41400c004400000c0185501d00e00090b00800c40c02800025245030344850740c441074400410055640c0c0074404410700701491825103040c402074144903603070f1075442c1800b04440400002450450880798065040244a01c0c49003ca415414000e1900f074402000e40c0007400b840801000f002902c050701d001d1a249904480e2141074000f40b02c090703c005030900070152 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 161023723 1250 161022473 161022541
    0x60804150c0903080f2205031f02092e08091e070509180f0d08070c060e070e01150201020f0d0504080d0f1509051302040e0f0303011706 60
    0x21503000240032114a01d02a441da98983d02c9120003917003c404842c03500400020810310444030200415840c142030906480042e180001080d00e64004031381c00d503689100840304060340710031503040d03174460440684520300c01d034071680340c541c0e814088850b070000480e04042094010b51284001611072880d0328050300d504a001c0803221030300d03841a10101c0d00c070301801001080e9501d031001c00ba442803110740c801129030441d1032809801d06510303010000782a002901c1c8203041c2a00801c500e50002521b280c00d0f0800b035a1420400003e0542e11103810741030040c40700c0010144c4200c1ea0381e0b0305a40340c141e43c3c2180c012507900260300301e2184d418440d1000b10f062240c014003200690007507070301a0040c0d0381680b0f4026141c1d000d40885104009404d5103503035943d01c5400140100c1200000b4107142e21081015007030003121140c030900030a60003481140c403150f0a06008400b40006544403c1c2c280c00c0b203407030396101c8480e150804601c0e10400001d01c82c3ca03001400021008559446005e002c800410000036 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 161024973 1250 161023723 161023763
    0x90607020d0e01090e0907150c0804050f0604090504051e0705010e0d05010e07030602190e06030406050a02090402070305030a11030c0a030e0a02060c03070203070b09211203010e01030309060804 85
    0x40c181000d0b906110405400107141070790700441038401d2950f0806000101d08008440c68a5000144008200000207007100c1c005088501200d050701d90448200b00303c03e400800094240c03040e80c001c6052181400d060004200d00000d0a00d146400f60001c540300d0843d04401c1039990980f489584d0000d00d0240d82003800e800c03c8103040d20028015400400d08070003070701f501d80ca0042d9039441110707181c2d80050900b4150780003070951030300c80e6240c0c5800e412503060386001a200d400043c202410349036540d030118000c0f01d15581125402c407800390055465500078240986203810881d201c0c0481400c0103814480d05114804030380c0b007081034106070307403d01010000440060a0036500e00d91503100f005080c40150390340002400c0310210400c000c1d942c9aa292042c5424031200b84e110155142d8180200c2c001e0b5550b451480748042c83c1c2c201c03a90300c441ca480107458908241d8032501c1101010010000c102c0842d0300c00700d01d05032402a19803106840d030ba00800c031010441103c029080d00c0e02d10302c5038500c8007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 161026223 1250 161024973 161024987
    0x12020306061c0605040513200a05120f191104050402210a05030d05070e03010606090614040e1003170c0703030e0607062d090807021507060c02060f090607020d 70
    0x1502c00107002403216101c40200b4100d0744180e03006040d1303025001c0072904000c0b1851050020307266042403001c42503002c401040c400411030042e1880341480c05230911005204001e040c9100710604116803076401550410f40d502100c041d0140d900089292401c9124180344c002d0324059a409130a101700c0c100130204000005040150304000350152621200c080f030310030006800e01c4140c0c40360005407810500c4026000034501e40300140280d0400340100912500041903804641690525842c5090181c0310710215220355040701c250701c44d00d6001c2c080007075070704104901034900c41c1c840480d00282c0c82000040a0045211440890b409041c0c10300010348508162442e1110203040507081902c96034400040c0c5082c84800300200c0f5a01e448800c1e0440c4800f03107811030280325078040210031b4851302c52410718031410708040e0003820410740044a00c40801c0032201c007150401820000352a000c071000391960b105407040c983c1c030030075000841d1510b58041905400b402c56500282465900840b098461f8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 161027473 1250 161026223 161026267
    0x210050705030c030f1308060601020d050c07050418030305010803130510110102030406151d1f03020a0b0a180506070f030e0303074202070503070f060902011202030606 74
    0x140820320426071400701c208041d000b20341704d081400d51600303032052010b811065903501072181030780803005005c0c42c2e9070045048030310321146107030943d5105840035483d480c01a490784199045868138010301a0260385c03c00c1d40098902c42e0b44d0a000c20390f1703602103403945c1e8040d203041c8510a0340301d0300040203c0c4c03420001080d441049818000301200c80c407034284d82282c004071000d0395010340f6010440007000034610034001500200301d9441e5150304043d80b003188900020060543c9510550200030594007991760500111360042a0307080b4140c80c0c451008144e0084203140020805184600c0f00048035503d03400306403a40039051078140310154031342c034140220160381503040c00001c010000c2c054030240000d103840e501880704800352450701300090080c03040184580d0184400300c00c07610018045248200091a02c802c0f016803145c10704c0c1003403801c511580c0e100801e40300d10b0303494034001c00c43c503900101d030070a000343c8460310801c1f0801d00f400241c0c0f108403502544010f04100d02204005d49802203410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 161028723 1250 161027473 161027483
    0xb0c0106030b130b09070605070206130e01170c0a05010f050307030b280b18090417070605071b0b0a09030302040e040809030d020f060f0406020c1c0311040302100507 73
    0x1a481e41da4440c0709a441043d1108900c3c822002209400e01c45030f15140d80e000900800185080c03490140c0040031401a240000c0c070035800090b580020303011036426040505403e683e2003030303256900e0810380365850050107030f204540603800c02140300e4a40181814100c90043e11414000d441e0702404890507400208074000380b50356080a0b4180d038840c0300b2a0820103004035102e0b51808031001d00711501a5032a84403400c1c49100300840f01542e0742c2c2c2840d494004070180c992035410380f42d84c0f6005130301440b04920741204800121780c00303061041a0700818000e40268803100c0c070644d120506074041c002c8103c0b000d800f1030a03c0001c00c1c8404065440014000d00a2900508158660551071075101007aa0261a681c1001c035042800b0f240a01140749116507900040c01d850710000b0046448001c01000e20121a0240001805001054040720b0700d00342d20310300b074964551218940441100b035012042c00003918010500104e10125400c44065036002402d041d285200c8950403182680000b008980d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 161029973 1250 161028723 161028731
    0x1090905030d0f0b040b0402070c090504050f1b010807050702010903081e120901050f040f0206031503010e070f1d1609050d05030d0506060406051204050715091e0f0b0c01 75
    0x1c1210704501c103405010305180f0f40407854880000801c4103680122042a04c260710400a01d800035801284d444100d4212100115042d5140d05003103040422108030301040d4007400b5560103a203504a0024003da0000b42c840508136100c2c04800c40d098000d013000240403c0c0c4802e01030000c00c5e01d80002d0064090310850701104401281c60f4080d158008501d4000d0401d40e01d4284441c40c0340038003503540e010040c51a24a410301c0c280c1c17241101465000400380c02068000041548060709030061021441e01500a003d41c083c030f40d503400e0340c5c3d00362842403260005000b03501049e10000714804c242e064020700d05182c6551200c2612403a070f0840086100c1c2031014800000a4075160f60380d10700c0b00d00d07000307001841c2c0b02da418183c2c10080e03d0b8010842c0f44100700400043c40039640000c01d030b805004464040080c80d0f41c1d18540140b400c8490380042200703416520401000c60340c40701250080d544840e4081c0c040a80c0c07050090007142550050f1407881e0f824442c02e1019900640c00b03420520552b00003c6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 161031223 1250 161029973 161029987
    0xd0e2808070f0810050603030a1404091404060c050a0203040501030b0a150807080a09031b06060503060a021b0c102d030905010c0e01050d110705240a090b0109090503 73
    0x151410360719a1080810b0804903000704541c0000703021508000b048500180103914001c000a500c91180d442c42c182800003e4080c83e1140c00140e0681e40038010043c0204034010211103120810802183c0481c0d180e42004e070f55021982c8100190b410b5021550011418641441700540c0941030b11121030f60001c7c441d40002880d203090b04070721540c28149840d04112800c001c41c005040030340048c8901c00c03c41c180500c0b80002540008013032001c107041d1082c400f281ca401d00c2c100c8050a001d501032a8136120315401c1c03003070ad46172a82c0100000102d480e100d82150010f54100c0784c840b040300130403544c08221000d91a58240c0540c582001415076a110380f002e0701c26080143c2025400c1c4000c04000075980c02c4a803040160910403424042c0036820a460700c0d14401c0c00081c06486402d2103084210340f0f518182042c0c10805040c1c03145990b01000f6919000c1005003a4400b40c100140761222400c3c07060017085070788115200b1500403581214000105a08218500d400b0703141c3d400d81101c5a01c000c00c404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 161032473 1250 161031223 161031239
    0xb0901120204140a090c06020a0f030f020109060f02040501170108060106050a14070606030b010501030504151e06030812011a0304080a0c0f1109010602030c0705041d0303010f080d0e28 81
    0x148982c1180b140094920080e00700406c241c000d0f03070010002e56015140704400705420f014a10186680342c50440d64001841d0012400342c40114030080c8014140041c82c2001d282b45d4000d40143e5400baa42c40014101c4a410701d03002140a100701c4119420184c0180580341c4584014a010807160810707084c4081194018940350b81f15000136524507980d0802401044012290b20380145001d01e402d21090800780c0340c0041310b0208602c20313034040b955402c400b100320101c003803600c0201085820030820070703590f42045c3c40c559001e026444c00d81400388002080c00d00750307180501d09a140c980310290031550b9030366032504641d2088d61003906218409120000203000d1794106180a4820403413074100484100c24880c15040c10703041101950403d00541e441c0100c0001c03020201c9608480118a0300844801044020402c02140c521390100200200e60040d0042c241c00480e20b018080b9034884090144c219110000e64401c0c0780d010b10b50042c04210242a05c40354000814644040e5110996130207003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 161033723 1250 161032473 161032511
    0x2010509060418060b030c03160e10031a0103091709010e0a060f021c020d05090d06060803040315020307050711030c03030c100605041a060a020325020f01030b0901120204 75
    0x100000305070f58244034024881c11401000c00410340710480d00c3c00c50400c100e01a085000080c10081c4d030a40c0c800100c1e245034030541108104003000303020420400d140201c028040c1810002c01900314860301e0b61940c86501c6071040071460b03500081d003043c081008801c5c942440d48140c00141c108105001408803944c0c690700c540005001503220880c210040000117410142f8008406454500000380d003140141c012032b4020800109141550707599004074001090351a21f804041c000c00e251100104650f00004001d00a880c014846d103441103079020503c10523072000300d80900001344240403903030004003000304100040c0ca008066a1102c42a900420b1554003c0c50b0fa0003403980c041a00c00403c0482e501c24076000d000c05480520043d00b001c243d1081e40041c04600310b00030b81000444418980c0b0034426254088030308281541c0ea4241e1600f202c40c0f80c003166800b42c1c0708855110b8605041e40c00392007603c22105001e450180309030720784182101d13170b2103141c201603801c6030301e915018000552801c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 161034973 1250 161033723 161033729
    0x904020a09030213050606090d06020c010207140613051f0209130218030a050303070e0111120307120c0e040b0a05040203040803040b010b030103051203040c05060c01060311151204020105090604 85
    0x5215070010307246004002c04440c48851800d01545014180240b644880c0222089a00300b81e1351203840080c1d42c03424100a01c5042401103142d44017040c104100603c150000c00160381d074404a800d9503c489564484c00d00e82d201005249500000301d002d400048851092410000c3c518014140310f2050042840050b1300c003085401558005400701c010448514020082c3c4000d50080014003103540d90340d0781e20310000e00220b09000002c88590010b030f129080045c501162081a01c01100360b10f02900e105820a840c0340001c82d051120703000c0003240c14410400d850341241d88401c0034400c008140301c010840d9040c4990050f13107004020815440318002903001d580b2900340c1503a07900d005d007400514a4410381080c6020f007003c000400201d10700244986246903201c0800346d6a45680c9030802c800f50700780e400190065000301d801d024419040d40300030112406017140030101c8189904021560000000b645080c0000f0b22807425800201c1e54020707406407040c141a403510044a0005a090700158 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 161036223 1250 161034973 161034977
    0x90405070305060310021204020f041b0302030103030206060f030c1917030310170601180216060e1e0d03051f0f080706020312180a0b07120e160312050904020a 70
    0x20240103c0f403c040058800540c1d11050460801400310000304014078050806440b030400c0300b40100d075030b80c0c8550104100c05464981c1d0f401c0c8541140018019400902c01980980260400502e103420845020000720340f005001d0042e003204e48003000b00c0034a4101c41c80c0c60780c0b007000b800840c0042c45288c5d803481c2c941080000b16101e146c081c0e0240000c8890344c100301070303454403e03100042c012400281c403815501010590491114800381c100001c0c0900d201a42d4038603058074420060000551080da800d04551065800740c1d6441c0b01d48500c039140e2051300320402c1e40a80b07500c0f0b00152280e44480e81184440e08550140008900d020f0745030099030704000c8002854007002c200c07540c0c1c1048008010301c0e00f80003941c1001c140d5000c01c1c0100d400107000020402039508501c08091b0180580001168072414007002421b04d010300070041e810040b92100458600b1403440307408000025020604002b4440b45561541541d0302d020107020211039038418031a0500080308941d4031030010f095462126 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 161037473 1250 161036223 161036231
    0xa05030406180503030c061306021908010e0f40080a11071a09121203090c0901050d030f17010602151302010905120304090912090b0a02030307140904050703 69
    0x50903030b0300c4038a006940054071981c030030072520400000105030315a02c0070910500c000c2c0c204a07402c2c01c3c0042e1046192a510444c2c04511076205070f500b01080b94107031041da040c2c0d00040c4d40c480785c01d04d13aa00002c0e1403040e5a25401120014018681000c100c203156981c074460803450700700342681d0b1030002500c0e401c603401000840c1e102546980558400361040c510002451103130b2403c0983d845a46a9405041015200160b20582500c0392800e2540303611a400441d40c0782200d0440c070394140d40042e42e1025080c082e43e110400185030403017040303068440041143d4a0086240e1702991240c1200305103400340500400b0720140c0341002c8801c2c0340208156005031620030760100050306078400040080c99030400480200003d80d1b400101c0c00c0540c0d4040c0d079441c20400c0d524250038a1809998003e406c2103090a25540030098a51200032070200c45445004a198448420411718040d1300e043c0e070300581c410300020780500d1040d2088140c0c5c04909070900e10301600c8001240c01c2d11000c664010100e512 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 161038723 1250 161037473 161037497
    0x3060b181003061a091008010e13141b010e060a140d150e0403020c01030612030c150207050c1302070213090609080d14070e0102030714010b0409050a060507030203060904030503090a05030406 84
    0x1030211b42407113503e00e05a041c540c1411084104400082e001c1440314603070ba40c030001000400b000158a03c2d15200484150703c5600200c24030000107900341d00e0001c2c50700d5480c15002c1c18424151410b000094071000c1100881034003c0360a50007008409080e181c4410503408a00300b0340f404507003c0c1c0b41c94140d85da06440e05007000307450000e41c10651810186801001c0000618400327018a020358140341103100c851240c102015125030b44440040c01074400980e07041000000600d10030130800036205100104a81c1d41144104e00402501030b4001070303d00c502c00b090a090f5030000110b07510881c00041e10790099164010700d60060410800400d83d00e0202c0700701402400e29907a4010f60f1840d00302055080302e00000e450b4040c14800810491602c8003490403271200b9007013889441400741041000174070a0600750395640c003d05c002e40c0d10f00c3c5803001081000b0310900840b031050070081e18948040c1ca0320343e030443d4140d00c007d10341c0c142800f03440c8243e000104107100801c014001a510740d601080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 161039973 1250 161038723 161038729
    0x70507091e0b09040b0103060b011106010605070611040803070f0f0c0902040503011b120b2202041e0f120218011e050405060d032001110a03060b181003061a09 70
    0x900b12203a54428184002004000362910440505495000c0700c04180c1c41034080c0181c90002d914800324801d40218400441c54070390102c040c20025010316420320591400c600c030743c0c242d84154018000c103034000308548400f1861011340300c030b000d0b40b141e64204842c1c0345039180c1c151303c1e00041c2c00035110385800190800080c5002d016000090842502030303a0503501035000901003019112603100c5490322a0699540c603600c00d44140d008950b83c5043e40010700c048d1103a80000e500034040e282101c517916005440c184002990702040c0e4500c04500c104160800e00f51481915400c001203901ca07103a00c000121000c021039a0718000c200051300c0c0c1d801e20941003841404008550001801145081c1c00c003c641c0e600c2e01c440c140015010700b4140c0c2c84501c8200e0090b4400c9140162a110b9030078048181d0316031a0200003801800c505540c10005c09031200d8807001c0134442c61001c034101004c06102c00a151a252848890610784c6060025200c0d640d0b0a0300030f03c500b0105c241040c016004504012130341 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 161041223 1250 161039973 161039981
    0x41401150611010e0a03080a02070c03060902090906100e040606170f010507050901090b03090c0d03120b0d030c060e010b0a0906080114090613030311040305010e070f0b090105070507091e 82
    0x10b05820300134090300340070302c011980c0c0f5500d031070014080180709000714400c0421507040300c0b510341d0000040300016450342403c2001d405003841c101d014070100b00015550f0343e0003003170040c0240f060003a2034035814604810041e1000000d001910426500e500024421030201c0703501c5070340249440130703210000301213840e2030031288014401c0782844410407900c0e030541e1384840603e040d42d10200049489807184040e580c540b0703004117680c035084444035a00700c041c07681100c603182868580d074100b80305400d4102c09000c0c00030078088000300401c804101c201c00082c080e030800c1a22030107000000881800c600c000035945c8c0c003254004507500c0d94405003031001080a005190030901c046000e58010700701200c40b85c2d44c030003004045076940060001070008045c4a5000340c00d5141841340d002d43c50350b0f16418503038001e0000d00380c1c002c081e215070000040c2e20030081020704100d80f262103a41c0d052401c281c006480950080a04607140c2c001c8070340100310786a0501ca2030b80e0412400784640700d0300e4441c0440300c0841d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 161042473 1250 161041223 161041247
    0x4091a01021b03071211270a0908030a1802090c0c100603230304050d080405030607080405100b0102150a020a1404050a031502070c170111210414011506 67
    0x5980501201c42c6038400103030120407039000041c810005032140c100b035807458802d09111a405510050221070807141407004018100e440c0c1c800c01c0c0b0303980720b024106003101e1803164002c01c0300c1810300004441e450280e205400b00b8a0f032010035410308046a0000d81303032000842c3c0346801404042600100100100141d01008049900821a0505540f21201d071140b080c069a031094500c2024920000e509105aa00404010744440c18010340313840c16003503075006070041e0760080c82244000fa88151103151079500464215015000965121151401800008600606511516020600007003001c481c003442916130a80c01030f01c81142420007000f08881c0070b25842d2aa00500c81072201d03a54804480d42101c1d80100310707007000c04070349051101078040c566000d828078644c500005140342421504080109080d00204000b03042e1110b5034009024141c001c080140781e031119004085403928096402078010703941c0c18100c1c13030001c0100b425688019000102580b0300d04041203210b402241201003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 161043723 1250 161042473 161042503
    0x14070f050d0b2a0405040507020307030c060b030a050a060506030c0303270a09090302060910090c05130e06040f020108070c080a03110c0307031701090203010e01180204091a0102 78
    0x964942000940288101d03078025103103032404404129101c007070a103c04046941c920a201641d8140888071545030864400c070b40c02181800001103420784084100d40c0c20710f03810307154610241c01a07212400240b0382c6140305505482150205e402140c02004040c1100e4450070b00455580382101c107050400030040e05417402544288a901000c032082060340352170700e48280d1001e0302c04030f81c5800290000c05075444100d0017480d200402040c50790210340c0520413120202220008500100200f0888604c41009070103400c120b507003409545003c4030006170344200040042002c040c00e10b1807904014041c3da0403030307a801702c00701c004003107507046811b072503200341e450802c0301d0200c0c46a01e030f408661059a4004040640ea00d4481102030507010995105001842c101c0f0f803925001d10b409040d001105201c00404007182000082600c51402100d050303c40346030745403096928000074580da881030300c482c40e1a8190248030105181c00288a41c0b124400d1518500070710b5111400068100400c030104102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 161044973 1250 161043723 161043749
    0x304180e120c03070b0406110d02070c0b0301051005031302040e0f060702030f04121b09140117030f0304030507020616061401050a1403010608010c051e040302010c02061b06041407 79
    0x82c50b032004010f0301c40203074206061350041c0c2c0d10344c03618500034190b030480da2240840100f504c01806006501034801c0520030300d80009410745840c40c41742030380024031500c0e41c0814243d112040d100d1096001e590400c810001980f1000c80540c00201034441c2020400c1c2c01307900a000240309001b0800c101034111466001541c90000100074160f2140314900600e4160120003640a007084030000d0354100b40c1d0305104040440e251180240405041c001003081c51107800d810000c6414185050f044406c403a60100035440c20311000d00e011400e4000404c00e03814040c051081f80b0161710340d81d0040c000501d2040064460041a04c0c25000300c40c4602160090840c5c0c00c0011b00030f40c2c440590f00f109950002b0443c03108904031100080c050140341e00001d85950a00c1c20500030f041d009000760071080c00844c040605d0740c400d829880000d00503840064001045040407001506200008102400003a0300101c0c00400440a00340f4229081da03085918403007030a040281844140440400b805404800709 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 161046223 1250 161044973 161044987
    0x80105090606070807050a081e12010e090703060f2903060a0f0207060f0b010e030a0309090216020306070206071d031002090d021206010501080115051b0304180e12 72
    0x40d580c4100100520701403580080c020040c40855402c0e82d03912944042154520306491510541da90044041102e62135440d140080c55801c060381a10240d11481206042982c60207160200103140500714424a010300c003004008918140140c690081a0700c4020408044400f000c0c24082000c0c80340d00035a15110b1846401560086082c81d002342800a0103c0c90307102d61311000e4000e2043d20002080e0718900104c1149018032a0000c80c00280c00342c0b520740c070102030002415100c84501c580100011003a5034140a60a6554003a022040c01407005912490340c41c2d0100e85400d1080c2c1d41c0f0310241e8407607800c0003007560340705c014480c4640100f40012a03490b030507004aa56007002103c40e0300c865401042c00c100648031681030080c010f400804078541c009001481540741c0501f0700074240099403120001c102c0d0f8041c00b900840c1100381750b480501d0542010300c1d880e50440071460680060004000010340380040390100f40d01e940c03502000089034107042078264600200090b00300f91105041c800b107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 161047473 1250 161046223 161046229
    0x304050a02010c29010e0a1b0f021e010b0916120209120106120308090c01080129030108010c091a12100b18010e0d050c06180901060203090a06080105 66
    0x21058680c1d0a00340110040001d280540880b458400c401601e415000210060b101e4150042c5040340c400200707443c55900d504c1301c900141c0d031801401848403c0c00300b0020100303e20074031800c40c080a40d4810f450080c0c2c004501315180d4105440d80444680d128284400c0d640f806600c415048900c0e404001c08c0108668805050340c410b00303003a01d02a9a01140b100120348913400d0420140041e04001c109881e1074490300d82c00d0510700c54041c1e0001d42c0c3e840005c0c003030b404002044404620161900b00e05d0b81e1800e051700d40000202484c407042822100c00300c001801c035042c0914041d101040c00400d100001c000000d020100350740c4032000c012405016104000d440781c0860301248103501054005035140340d81c41c290b81070658050085014006082e500c503501d00d501110386820240d07a05003008800c2420401140390300d810281040d000321020070000e14140c0010305040703407a4284103012008400001e048100309900441c050307000064140c10924090065602403d043c1c10014080e50402001c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 161048723 1250 161047473 161047483
    0x206010609090f0209040e06041502070206030604090609050f010614030a0b270d0507030e040b0a1404060e04140d0f0912030306030b190c140702061e121b030405 71
    0x90142c1180c0d107040307605007101182c0445070f0703658001e4410300000e401090711a070340f100c0844055510100003081c0c841c200c020741c021034800d617400812150840c3c445008200041204650850701310740da034210080010414002c1c420b038881c01a00008002d442d050304201580c05942502c1d1203604412040d000003045052047c2d08500110a40c0d030454600700065054a00d000c0018031152140c00c04901d01203602c0300080c07110764800c0c2e555207014480c1006200c1907500540b1200e601900c001420b0002946d03042199221060050000c604144e50780d0b0003403d60042a6000e40e41c44540c501c0c100c0000c8003c00032a40202e0051803c40d021700840f0b03000504150040c05112141c1c50400c500400741882500a140a5600b0616a0704035003041c2e8101554a982070084403006d0742060354001c0c02900508002e0880302e102028a4545203560b800c0140a40c85181c2266044100e864082d101030004406020752042c0c0e03221114050901da011f114030f0344041c9100c001d00030800c10400000030703004a0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 161049973 1250 161048723 161048729
    0xa0c030605151909060f0311010f05191e020609070b07051c081611070504050a0e0706020607020f0607050d09050124090e0106030803040f0302030c03030a1b0206010609 74
    0x40c00145036141c81c000c2c0b08922001c4070b0a075500030b19040c0c5003080405500111001c13103401c04410031040b42d856502c4011041d091101a00c07060340d11800600755401101c003045407420394074009142040040c41600202d201401480000314503003039594803031104407403070048605180001c001602c0e02d1258640d94900c03502929980c000040303400c40c10080100400d40c8241c811504c1040070079039000008194a00c101c0c2d40442c00c1c240804580c0e007070f07801021000e040c44143c00103031049078100404e00016240107024030041560712030805000e101d0a10041003d040d03c3e501400c240e0404100c000d260883c00001020035400c031500307016010303070082c00720b6000c1418001c0101b5920a00e051aa00401d408003c00c2c4c8202c0c000400500003502d807001c01c20680f07481100c200720f56071500324000c1c221481790000800c0240c042010030f000c91107405032140d80034483d20440340381040405609046810523569840f54580b02c0d0030b140307a84250450b20032524400c07440140015850418010102c0300244 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 161051223 1250 161049973 161049983
    0xa020c0d05030415050c010212060f2407080c0d030209010908060c180105070c0f0504110c070605090604091e0c0e0f190302090103080a080c040b0909071218020307080a0c03 76
    0x9414a8031321400352099440c0220020000c40d1614160398030782c0c00f20b40e411a600351190501e403250503410b1500d80060003e10500054041c003004241044448a89c0056400d5070201c8052020019116040052502c858441c1d50f0241e1201074040c0050151070050300014902c1d001002046442021003056603549290340490f408107400d02001070300c4510602c0c0000d41071008821001c1550414164020205c0d40151001c00040e000300d00e603014603020744101034440782c100c40c400704103041c0f0400c007078030403200d00400507031800d603465903142c0890704400c0058048031044902d0803101340c680e1040706003030045d504001d408001d07c940083d84001d0300700c00440c42501c18031000050141444105005185e003d0201011940c50b400c00410136004109003000040200f0009005440d0b007009481c101c0c2d8030007402e6400e1004650400030480b100821784400c2040300e00b503c3e09a26040c0c09110519001a8421030008034540149405c00300d00b0b03084685140d001e0800e04000582410651040326040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 161052473 1250 161051223 161051249
    0x10215060d14060405011a191503020418060f0f14010c050c040f0e0c0a030c060c0302010f050408070302120306010504140a05032a01020a0b0f13060606050a020c0d050304 75
    0x1407504540b4035104080c01c681c14800c080c1080100141540078002d540a003035001c07441680700d0000c000b15825500c21410600c071a00a00300040070825100c610280e09a050150a043d00d445045402c100c810104c0b000b0141c6610042100300c0e0035203168800340500b030304008105400c01c0907286d04440800400c42c10002c0b0103084c4014000c0600000c00101c40080050007140c01031030b542d6029080c001840c03012800f55001c84041e9103440d40c1120212648400107a80171458504103a8030307140303240419010755403200a4581d101c82d447c41050302c00d43c270444009032501181d0034020f1400880382c002c07545080042051203682d030f0300312066500725070242c040c020030100d41801144200b00c1f1603102070303094462110301003000310004000707a420208141c8582c00d0740084100481c1d0301d8a007628050602c0d02d030785000c10340b003003074010080394003030220a01c158000c090303541e9107402c44802d540158002071002c180e420800343e050040301c0089908031500440e410240e151281c60744158401d003454041c0d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 161053723 1250 161052473 161052499
    0x20106141201090803010801141510080705301b0d09020f090a052406031618080f0d11120715140103110405070f140705160801050601021506 62
    0x1c02d4000102055002c8041922940d46201003406040c0144070288070681c10000161620b582c0c80340911b04100080000324110802e100907204d10402610403030421104001d1418251204280080c40e81c04182da007804950b034003480c410300300401504185041d0b03581010403403150814000e556035180c0c5440c001031000c245100190b806101460219008100007041109018481c0e00c07851003a000200c00742c078a40400340e0740344902e0000c40c03221940410140042449044129003924080241d42400d051041ea80e035503603001c441d40b6071300640c0d40b42e1102c00d241c070100406011601b02c0520600381204038080090358a81c45800350800c0c80030010001c10f00406006185103041c0c01038803082000c100c604080d611081b0900ea090000b5100e40c0713000e01080c042c60a1034810103102e00d140c4c1d901d698543c0c0c40d0742412a40c1090349012074240980a0000c600403c200340511040346042c9140c4c41d40c0365240c06422130946100030400c80c19034001c00b00084030100a44401caa1002d01240c140901c108 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 161054973 1250 161053723 161053759
    0x606090301021225050712050318010504060f0e0d020718020909040501020c0601050d03050d09020102100f0203090c012d02030706090b090c1f050f0d05041b0602010614 74
    0x83c89295008090b6010600c820100b0240746015203200c071413002401c10071114819610303441040c00040c0100902c5811911041c880d0025642100e0b804500009086041c0d07005801e403501518280c40450362a0b1315a91402c00502c20003107860070210140400c01000c0c032001c0e40f40d040394410100c04000940d815414146264100d440c64000201402e4646c00d26040c51070003500310420000c0144100790000c9050b2810524840d07105500d980c6e41171402d100b01d80701b10081c0044940882c103511510494000354615402010301c0720346500c000503140e10f00544603078680701c0000d2100d4184035031071108e031090000c840c6200c06440009a80c02c890162074140407499407054510151030b0a15140e850000c010400300b5040c00f410800d000c8402c80d01d00301017003041407440400b50030b0100c269408501d148034060009810b00c68002c20807103042c501116424000e644c402c4904a0703c0e018000310f80d035091070050041001030501071008104250425690711b050340521000300d88501005010048005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 161056223 1250 161054973 161054977
    0x50f01090e09030705012d0605060306040b030a0204021611120604141606110d030e07151209060506030d1107140d0501060303030b1e0d03050a0504030c0806010603050609040209060609030102 84
    0x81e5012000b000b07150305003400c55258101144d01c81f043d08400071002c511040803400f800c001d40303030001d1166182d501e0b0305003004001c0c914400815014080e0240c02405665288098000780042c52000850340e48285040c2c49850100e5000300e100d20b00f1038800c0d4000302070004056500541c0804007481e040312002013640380134000c40060b000a9101ca0004c16800d510111180781030344d4070001c480c1c1d01040e481041d02a500c007400c81800c2075004041c00c011114840c119440702c03034281d0030506c0b031061041c0300c600c0540c0c02e95041918443d44550611a8900b070410500802241d58a001100304405662150726250284520502440018107121682c0d5808000304405a0300100030086184e4900c0c014002c0c0c50701d0401e680c45a00001c00385100408082081c05007001c000300110001c04c015641a2031517082800300c1410801c040c032000c0006480b907100d85000c0c0c42e03c04011b10b0152315095008003a140001c00c5640204a514244001606c40700300c46904080201c03980e0b52148030100c0864024 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 161057473 1250 161056223 161056237
    0xb0c0708030103080a20060406110d0204080312090607120c12020a0207031119030b100b0a120c1b02010f030f020412020f04021309090f0f050d09050f01090e0903 71
    0x300340001c0000100141d880050400001d81d07140c00261444c00b1517000403110003007a0310881c40c0c010500150010f0610340c0105402c812601001e420050590144012608070750000d980560000904049070f0b40d0701440d89500180715001007102e440c00c07803c0245a088e803030b40c0848071140c4902e024061039008140c500440001074004544842459200940d1800d0030306c402d0306c1c003280b50346119001e410700c903242c41c1141c86120a00c0d0041440c580d5120358440000341a00d0301c6400491000c00d1088565004140401d0b40e42d44200b030b1204600e410030110751001900c80184028045884c0c4d03162000c0e048010f03003980900b003201341c140b00100705801410000c0105440d03a440041c0120784035a03040703801c00b402d900965000031088426010311040707100d034614042e0a81810304003000360640c95040715541c6403081d280e1b0344891040c1d9441c40c00c001ca21440c01c540d1504204950001280d1201c46070000304070440f2000e0001c0d140343e0028001c540c0501400d80401c40c040c001a0407924108102c1e128 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 161058723 1250 161057473 161057483
    0x60a06030c0521040b24061b030f070b0601050a1e031d030d0e0303070915210c0e0307030c0603020f07050d020304030201080a0204081902130e010c0f03020310030b0c07 74
    0x501c2541c4025000c80c81c1003243c089621080d1400894021100382480040f44401e9113803030803400d646c040070800c0c2a00034410503010310041500000e06041d007440908909440302d0512034861007a403520070b0b14181d0003042903040090910101e4400c980c8070070306c7c00640990092514500305503803000c030042c003480e503280e6900c0209101081d645640c0040102142e802c0400200301307040e242d048550f12480280ca0850005891032000d11681e0009104255080401d0078112104140c450b142d44041003100001701078950346400101c8160b400c1442031405031000c402038401c4904540d1120100b2003607000d200105580416069030602400045524040e08402201d11383c0140321002541caa2040c08100c1c0056604400304480300d1060003a0350981d01ca1001030f01c1201c5d8004a0040401498802070741c0c0841e1450513400128980c5c4912656030500360000b2030208210a00035044000f45051841054030401c20002c2440006030700d40280c2c0c0d80301c445503616440c0c000541c08680280c1c1000380c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 161059973 1250 161058723 161058757
    0x40b041109090f070906180203090f01090f020a0501020d1409060d140a0b18060d0201050706051003050d02120315031f1418340b0405041103060a06030c05 68
    0x1500c0c2c00041c03062804208000702c601058840d43c2c81c20585103940724003141c10320191421244007a044d009140d022140100b141c070460761208445003503807280c3d07000b0b603a021405039943c025801c0410710140900420f00003001c58003149580140150f40300304e01c801040d070000c0b40d00030701c81d0390348011100b075044010400e00c5040c1c0daa017901d0b403881c0701c144d441c000c09520744040c240c15424045803858440410b50341c50240c5554a500380509031094100803410003c0401284001400d0b0344140380c0a21485102008110304528040349881756040400c01954002d40094046146407000c40382d01c06881c9810044a080d4800402c0ca04078449043c88600c401d280040012561140e2180358080d0190301d240c1807a0312030001c244014203485100c4c0e40f49420044e81c3c801c02452550000346202c9404c00a1010043c0145a200c5110240c2d000001c5001d000030b001c104500e8140a182d00c0c040c01903801c41e14604140001501194651240d0814103840791030083c0e1250252050b1002c0307040b0303400303911 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 161061223 1250 161059973 161059981
    0xe07150503090105060f03190501090c140901060513171c021b0109150e0109050402030106030f14091908120748140109082808040b041109 61
    0x14020760811500511998640700000c1c099141000d5800c22103840075000d002c28100340c0d005c40345c80403d070402c265000c0d9203030403c0fa400105560f2100c0010204c0c80701482481c2000c4d000c200c3c10390030681c0417504000007031003801030008101e8040b408031a409500c44841800481c41c07542072030400580c421030b003600c85034020221a008914856000e401d10340e8202203c0800f40196034030140e5020748421406600000e562890281820010500050420b91511542c800000e03003039a10982061000a44400d0089007441d0340307000300c2151428201500e00d103484c04040c000e0f90b4034401c0c0d2400340c40b03c0b10328900308244500380c8115542410511341c0e02c08103291112001d0203900c41100c054030340f07280880031200070b400000d000d182c940d452142886488241003100240308403c4410694a880021001d01403e10091091000d454440e0000c7c54881c11f1064007a07844642803640d032442181f091002c040440c0d40060090b0344517620001010316030b2264140224100340c6600800d4101368140140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 161062473 1250 161061223 161061227
    0x250903050f0a02010f02070e0106050307111b1005071a06010c20120a030f0509030c0a0311091e040213020c01050f04020a090b060904020c0c06040b03040b0601080411040e0715 77
    0x440e00040c002c0c1c81c2e0300345c40b508200b0106c1e034030265841281304156615005000c941c0c4200000c5820120703078601180b0030303141c6441003070405240d0f800b00300700015800e012001c0c6003007903c202840c5000d28100142800720644850b04a104070552800d08014110000381c03107a030103032020f100d096410404944014801008800581c21030301101445402e8072089100c8007100001c100c0030300790b4180c0d149040e01e003460806a0782038008007030a07075040c003503c000021103031070b0303c00810300544c080e604030003840c030f5210706001c40c000014201181c204216040e206440180c9104607401c175070f040e524900020180b52401000380107180343e50300c0a5092170b060121481c078400080d40070764002c44003124201c0d030b11002d410442d81482d582a030003500900c41c0e441d481c5451750140150148c02000d41e040c082e00c000004990b80c1c0325402c4400110800b000b400103205251040c20f620a8085c240440c0a040903129007141402e43c50505220302e850305c1c2c03040d4040790203200c8600149452200460400c00c0c070301d40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 161063723 1250 161062473 161062483
    0x1404080307140901020309090c0c01020708031008030403030807081e07120506010306230607080c070f150e061b010e010c030b0906060901081b03040303020406030e06250903050f 78
    0x5201d001400c0c101100752414044400c035041c200b016002540390011000a001c801c0310010b01c0e40c201c0010921242034503400031300080046510450615075203190601da03014010700513130000082940180b20903c0000c0e00709480c542c00040f40d0411404036580d100d081c401010600c58212100e406110501c180c042c2c2103c2241c6028070317600c0040c130031603a50000440031110107200d1140040140d407502545c01606400103280c69402400880c40e000a545810300aa40858030080460380070010401c010083c842a0902405000d03004d001150b0341a1401003000805042ca00d12a0b40c6c00140c0b400042c1030080481030aa02001c000e03c01c00c120091400e008041e8030340b0b030101081c00c0400c00d00c41480d0100b100381c820440104407506142811004440703c40700200392440407250901c450341203049490165100701d1207617801683d52410004003d05840c981c8054004c01d500000501c0070300300b040c55500001c08400e54004d0303d5200b0824007101c04400c0340e480540300d8000e8640c83d802ca15004a6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 161064973 1250 161063723 161063731
    0x5040302030607030e121c090302060103050609010608070603020322060605041d0604030e030a142b0c080a0306180204090b0a060c0807140d211a060d14040803 70
    0x259050343d075550500b03805403444400400b045422440c0300000c0c03d081140605140d29030300c10910b250580c1c0c0382d0580c084900001d0f040d40560b103e0801001000070810081d07074452440c4000340109460942c2030303aa506014059901419004400103100800ca0400c8204909201107501c03000c14403404c0ca24000d181d075004280c02203007055845414031002541030300c40000000c00506c907a503140d0300c3c1154085c517012400307135150145647c07280100755034030704400c0b2610180010301101d40364280c0304003d075104c49042c4900d04100c25404d40040d81c2296200d0f09580e0031400c00d56903480f003504210011301c840d42000e800b403200f485051002d1915940904180d42e0400405c021540702c903001c104000b0000d214140004440c88030f41c1c8002400c0d84007400103140705003d414007080b0320068041c00e003008031520800086d030b6001e00200a60807407042070200d51482c0c4041100100411000070005032803d0b40c0c5005d580b0002d06801030740701c15400041000c131359071840c81150405182c02966a402071b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 161066223 1250 161064973 161064979
    0x60607050a031106060109030209010302090606070803041a0f06030619020408070909120203070b0a18020d08030403030b0906030a020111070e01030507060207050a0f03320c030f060f0f09190305040302 88
    0x9400640c59500a0051402340c0750020203070307182c40e0710316030800c00303901002000c035504803d00707024032000120050043c0d03005504c2600303200e00090490004880c880d20081600030380100c2c0c0710030300c8031075280401c0f00c58020213141c1120110f102020903202c0a0301ca6a4040e25a920814100003000951070340050644c5100303283c41680354003400012640c038013030450098003504c910004150314006542c440c0c080242402c00c0310800c071006400084015a05500c15665007200108110400d540351050301c1181200b1281c0c0c559a0074050b010030760b56042c0c800001d040c884008117150381404100640300003814000d841446541c2c5070b107405c90321640b00b07110782c0e4003512421001052030b01e08a41240305a0341028100380c041d510396200d00d81116006101e0341800000d030860350421701e10b4240c0f0603a103180c207800101800e54200040c54589050a80c00301119004030b400d0040301d5200190b51034100b46042640143d5442e0459058241144da8078142e01609481e2080300825421101a00440e0300803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 161067473 1250 161066223 161066233
    0x10c02060a0221070c020301050103030807030b091009090816030c0212150c1809010605090f04020c120a1803050a14010c090b1c02041805010b12010e060607050a0311 73
    0x201c01c140c1c021051000e040c125100e03001c2281e00c07101c00d103035a440313655031400e0203880c82d040c2c010a08440003170f00140c001a00120400440a4044c062000701032010383ea410021724000d6a921032100c0c0900464064a40302c20344401840120b0301074401d0403800c203490109580d00c0303140c060070311805120200e00880182503041458800800d03a0110f000b10a03040d419696584010403070140d018100c00310080d2800032004249482d00c1c00c9280c040c1c40c0584030280e0314182c200410941c1c000340c00c582c88c4110b0041294403080c40c40860201e0300407285a01d5a5112040548207075580354080c640201c01682d401c1000041c0000003401d900c5c0c1d58018003001d0a05180b10054070700b60340a40c00c2c0e60000c1010040104100745001c0c0c01003920300040010750146a00c0c00c4003102c10380c0e2160380003010402c844000b64074244141d200c0d00b401403030151000c52030031a0281180c58809414410a107020301e10a000610f0b030f4662400300c0d600103034048141c540c000030301e282c080c00f140d0401548400d14800c07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 161068723 1250 161067473 161067481
    0x8060a051f031203240501020c150d150810050f180c090a0f020403060b0a0902040e04110d0f06050403020c0108390f0d0c17060418050d02010c0206 65
    0x284030304503020665802001e034407142907031105452910500000d10401d90f58120342072110035514102030f9200d40081a00c01c07a40d10f0100020f00d03007184041d20703030310407210440b01940000254007282c0c0c4035a8401d90200d0301c1424030688a801d400315902c051344501528101045044080c0c0c041403003400c174480c140102c0e468250701650b2500390303074040c0f80d4543d010102d40c1d805c1e458007520140d0300041504000c078551141603040000c6c0d8000d0740c011100603490b032220035558a842c002d00c8006c0d112000c0b08500385803515141c28103400c030140000d09840452240e040003500c030318003152440354019505504104c1d103842c0c501f005060440b0103070014041c40089844c5917100703c0c2b4160081c810040003c4000b030180c2207100c0c103080c42d014184403034040c42d800681a0300b0100090111030f4035051010b82c80b01103c4400300241c41d072110361070041008540840c000c0f04822441c1c0b40e084001651700081010800f88002c415041c07000d03002d4464410004a4000c05d54150016a40c40c0400e03401e40b40c031526 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 161069973 1250 161068723 161068741
    0x801050705090409060b150a110f06060d030e0301020f090f030706020d050a1808161710050712050a060f0e0c16020a090501080106171603030509010e04050108060a05 73
    0x54240c4040000400c1009070081c0d901d02a0031450115010b010000380c80d084420000c0e0480c0211400180a0000407079480c04158020a81e848500440c4020b0208155242000e68858074010041c6c3c2c4129100320004003030504c950640421188003500071951450101429403480c3c0088140c10312034182031005019606000c181441102e00a030001e003050f04c82400244d80e41e800460b29102004480c030350f18070080d5aa0389a850041031081d0184c480c0382074003030550345071410582180002c0010b00302842030201e00010802504569040000780c1501e0f07440d800c540340c803404e8000c2c03840c840c00c040501c09034014540c80070048070043c50080c444503a0b1102810381c2054100c81488080308180103041c68010198040000280b00400301951140c5400c1014102c032405c4e0000c0c48541e6482c2403d01110341e00021034080c541c6100000e1026070107000b2440c15207500707030200030204072002c1030005480c0d014070b0001000c1313030700200140010341c0c4591015a940740c0880301c000745541407401145a0300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 161071223 1250 161069973 161069981
    0xa0f0f0e06010317090904080d05100b072301022803110702091806070503041205030103020603160201020f0c0f010501050d20210105060a05010302042702072a0801 72
    0x903054054401603185807540c282009600a8001c41c045041291400c550b40d401041ca1080b8450f203221070701c501c0e1341184201183c1c801400300080c442c03039140a00c501c0665209480d0701550200715902d00500965446001881c010300f000da2540c00030480d6241e08800f80e0f803411201070484450902d80c10810811400d55000d00303440701d86003904024010142c02e00c40d0f6080d910084031154440440e071448040c52134503d0484440c1b0006c0c02c040240b00c00c001016100c0030032800d040c54990f05550641c0c00180040c40b014200e00b200107516481c1160860003074045d00d4a00340b50204c0c00341c0f545010b0310055180e80d10500c100070315503c2e10001080034688140035400c12600b0441035000025025080c03c0040c25050415910a4982c42c03c050303c9442d4803900e00110306080004161818194180000c25103075801c2a41032500520007808802c5000455240c44040c0c0f098042c0d00740b548503813590003485030a1000d8080d607a485c0c20199504d0f02d000701481401e611210007106c49130385400075402c075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 161072473 1250 161071223 161071241
    0x190e040b1510030f140103030804060b0604030803060f150412050f03031003200d060204050103050f0408160206070609050d11010b030a02040506041b020705030c0418080a0207030602030a0f0f 84
    0x319000c00c02819020384260f011010a00e07044900141c103c62160170207100d04826801100060341107010002001061300410251340410380f80d01e4105030071079803442c0d264040100107a0107030b0313854061801070740e0303981d280a0031850000b5000e40e0340b240ca41940a075240b8005d88256914401e80c0602c03006d21200000300c80c8280040e1618502050135503998403061b81c2e50756103400907005015045a241e5503213040c05088030384a800016904c40c42e21002405a580040c40503000004100801001c00c0356501150450003085003240350005091000800314022414094151407808104104000e4000382c0d41d5402030f8640c58450320048446010380c26507051510498054100240c07010050409030003860304241c004202040b811900412900c400131882c0506005a00c40c1000700070a00b401d100c0d0006542064030103110f41f1a180090341c0041e610f064000700180c0c40007036148506842406100003941e440715095540741440c201c1040901550422076002600c1c0c1b2031041001d034114804c02844c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 161073723 1250 161072473 161072479
    0xc090f05060313050f1c030c0810090c020a05060a0c0905030a0c060305070903080c0c04060501030605031209030c12010b031005090d0f0201021e0301140904020d11190e040b15 77
    0x1d1503a03900d07040981012450021a010b110b0324641c2e2400805c01d0025100d001c0c0400f102020022032000024169014000400144400700d010700403120300c2160104107950f82c3c080d01240c21121404100c0c40c017001c3e1200a4094000c1001b40058144107411141406074283d4070808001d4850b81099190120008002c20885043c0c0c0100700c0b09004c1d0b0480b0780e00014a04211034820364a40302c0850300d034402020304030150440c4180c407506140074854403018003c04c1c03030204089410311010a40d80c040c85501c451001e0004140984c00350350070823080c060b00d1070140044d0100780f0030b0785005010303000b001c2c4054400c0c0101c108644030307490544a483d200706032110050084800320401600d00015420403081155004c21485d11150090000ca0050301104130166075250301d0001380000e03818010100314810b184bd407050001594400c141c2c050381c1ea070441407007000314086000040d44040c041600110340c00309100b0000300c80c1041d09065208502401c800c40f056500c440007903500d45602046554 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 161074973 1250 161073723 161073727
    0x606260303041b05090106180614040e0406090c08061b070c03030c1a1504051005091902090312091207030b0112170f040317040501080609040501020d0f0c090f0506 72
    0x41100c65400140c022065401a890f42c1e44840c081020030109801c00300c0825000301c509426008001182d00c01800b480c6841800c4003c0d0451805280c8101e106e04200020142c0108003030269a510220901da4030075800140180c1ea80012a210001200c1d190980042d00c071150007440541c0044442c0190302190742c01d03808d0309546e02510b240036426015500309041031306448410000e030a19a0050382035502d550030310000c050800c0305071180241803c2c10000c00341820401c507101c10209641060f4005c10b07004410410030740490083c0521903040da071502c146d00a50803d050b8131001800703000009c1d1070001c0c51a1443c0041655480984001040e0104840041000b10240400500c020744500c0c004001842c2034240b21540b9048488180b0300399000103001c01c2040905120070b0059001401c85504040c544400600700690007040103010b40c001c1c400040c1001801e60443d0010030b03550ba41045000851502080181400030311440804c84240011404001d0440d4400849000515680c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 161076223 1250 161074973 161074981
    0x80702090403050d09110406080c0307090e100c05070c050612060603181c02071e0b07150e070e090a0209060f0409021c02010311040806150a0f030606260303 69
    0x6101100034000c2c1c003000b10a01200c1036007220342c09524001c40c019500002400403c604200c201c81c00c5030310141039540300c228588650b0310003144140884038030f028000b4000b40807903007290425103003d515901152034403100c07174201c0d500704000e04209800741d00902051920340e0180100c074800d844800552616802c0015690314140c4021a4001410048965026269034000785001c0701402562440030382a2401c10807141c0c1003007554020b21080145402a10b611300c20380c00c00036514065001ea03020000340f400240030107801c004403070a12840c02004886a0b03035500710346500203401000025102071011540300c6000190509030690010041901a04c8900c100031403114580e40142c0c00c26140e01c140e10240e51006000400d01410030000c0120190602c0018115034203070702c6204031802c0502007406941800105564804034544142004000080c0094580c0409a1007041e50400e540b00100411034960020022980c8030460000110b646d81e4078141d0519085c0c041c0b1503a0380c800d00c001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 161077473 1250 161076223 161076229
    0x7030e04051506040e01030204050708060d030c11130e0607092d35150103030806010903150207350d020c0601060c021f080610030615090f0602060103080702 69
    0xa00c0e006081d40ca682d01d0311210403400328496800030761088810b0b00b00540104194181401866800321480c40c01510074030300440021040e8140c5100642082404c0d80c2600030440f0704080c1d0700380c03403900034041004001041c2c80007024000c0d4030301c40000780c018180840d4803d40100e03040380640704c2d602c11018600c0c3c00a07018048442c451a841918035650140009034076401048501409050402075005151f002183c03c0c2201c1114090b8800b6034004000c84a000c20030314640ea05581d031618083c40e031500c034440100c50404581d00090100207180714001002c44480c1e008113581031003510869211b00d00521a840d54401021444808002840c0c0740c1e8003035000a0024004540c0b61100182090030b210011450711009030800c5d00880d4100601d50103515201d5000c80c0c901800103069682075142d504000c203840e002900160140706071003080d011040c0240c00a030054060241d0f00e2f03c1c0c91030780303040c003c040c03010a10404041440b0b44802080c400d10103c1c1c841d06a07a005110103213020b600e6424 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 161078723 1250 161077473 161077481
    0xf030d021e070606050a0e1e090a02120609191101050715090302060708090a0f15060302121507090e0c090604080109060f0c02010603030210091406010e1b07030e04 72
    0x7058060100325090500100216000c1d1880c18040c490004407182040103005990400741c100e54201c017464420043d001104590200308600303003034004403a5465699155281c2041840b009502c40307081a0031800c1c1210000300c0310303c500702c40011192400c174116400817440101850242c030304402c4c040182100c1d40180c0080110340d1283c04815a001110a035110403101c8a030004c90040e0403070001c1c80212544030316410b420035041000b5208001c1c450b074071201503082108008210306d0380407850040543d580e900801c029a00a02010000034046c420907860319034000a4840001c591000b280c04035218441180c2039465800c60201d035074640c008920600e810101080e0380c0884200004124010280294a06541300d032102042c0c2c8001e054001095850768148101160714184013000030030b42c0000d003000ae40031015400295003c81e420505040d004542c890702042c4104000020030501580b034551051000d005240b00701a03481d90150182e100750030000d0300044203072a0550051070140d00c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 161079973 1250 161078723 161078737
    0x100e0105040e04031710050310060803070201030b0103020d090308060907020703051203060409080a020c0a080105070f1404270605040908271003020a02190c0b1c050a0501030201030b030f030d02 85
    0xc258218650104175000e4050049891150105110b80c1c10400c3e401e0820881e20254603251041c02000e080007801950307401007240c081d040684034115509581d01035811181100c0402c40c041c007040c281030501811003142550030b14047c14882001402c0710f4400700f03956081d00d90040140a030440d6030051518a07410150505070301c90b07600c0030144001008100203140710300150700680124050141040740c1044181c3c45408103905044c00c111b038450b801682c10090f10498103101c0001441c3c00b000c41101e02441d0401607064400002488624015910000e00c0342ca040d01c0038000152904d090200741c454503c001481004107003c02c0401c1244040d940c0d6012140c1c41c84910030405681c00110088a504176210110f50300141d0212030b540c1c140304408051001031080f4440d40c445075500d98503228144201c110305e840104120014400e0641c502c08108401c080921440c10700c4425400100002c0c481203020929001d102c00c842e0602164407612110030602450400040304140c5e0003a5005007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 161081223 1250 161079973 161079977
    0x3011703090301020315120105010308091207030218010f0f030b04020d03030f0c0504081b06070201030e03070609030e040f1407050307020f030705010603061d0703060c05070b0f06100e0105040e0403 87
    0x1c400001142c409101031807050814808640000d2840d105019903000080561070380c43c5d0611700140080b48180c2c080b14480207003521842003003d1459a418240f04107500001d5103c02a6102c1090080c01a42158180c6188203040c00c00b503a618508030000a06e248401415503182c540080e01615090309280031540c042d050100d03003e5108010030044a41c180f40e40c10105901040a015580007044918594004c901e040c148011900000420500940500904058843c071b4098030119041c020340b20465440326090040134110300d0080c246400d4800424051450518454080c0703829007c6c0301b822004c0c1c003803031141e2902c40150859041e072006040109610078401031128038602000202070450049000055883c110703d004019240a0140e200b2401d03460782c41c14014150108802d421290710010000792018010002d485500480e007001d000c2d009100700300070b00e070482d10130310910840f003c8031020035503075000388292805000b1800d264001501444144070614841d03170281c2d0400e01034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 161082473 1250 161081223 161081227
    0xc0303050a02070605100305060601090609050609010203120a0b01260f1510020a0c050f06040b1315030b04150b04030b060d060915050903040303081f03080c0705010e0a0b03011703 79
    0xa80b070340800e45e0011b88440c103214020000400174060103002c0560004024030f814001c103860710200400d4040300c1e0080d10310031500024190240da00800854a12402114190303065240207081c0c64001c12314a000c03030740461003001c804e080708404180505811030f101910f00003551100c000d203074400d05000341300301c80e40c04a0045030190343d51081a110396080c0305a00034850b01c01d191034402c0c0b003a4910f85c0000d00844000c0b6080c0b81940d5810103030703000d540805160750349480c1c0c4d0701200e4a0a40059000c551032034904040b420701c0d1640f5400280c406581580d0500c960810480d150800b10902d10541080090900040c400a00d0124010b600030308000d01800c05250781d41c4505041328031240044510580300302c40004110507d00641d54400d00320030103941440e1458401030620b0900411102080c0006d11141c18100383c121030482c040c607000300b4115150081d80740300d40c1c5d1b1184030380242e502060080001c00a180303005031750b2a09035104040c600d400c0d6403910144060f174070141507180300c0601003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 161083723 1250 161082473 161082487
    0x2190c021207080a020a0509040812040503130f060f08061e0a0b0a0503090712021e0319030203040807050301051501050703200601060806010816141b010b19060c0303050a02 76
    0x410030802e006040303658081d1140d200c0343e20402400c1d01e1254000d0340203078150b03c1004040703040fa00603600c01d200b01801c80320480d5110719006003148918682200340c0d1202c8240400c81c0d00780c0c4500003065841d107440b0607034800b24040d001d60396400e00f00d1300d03d6480800300c400d007015035183c035545044400b40a48000c07245501d4400030040c6130800b480003c0050b00101c2008106c000030402840100304146248080140540116040c0e9001e140242120342180412081d903460130130002c218000701101c640006250751900032b48a602170710414403a480b52003004106880e041c070072180a0301c030300c0002e43c034045000341c015200c075001030700103600b40704076465100d50404103d00c522101c1e001107006005150704010b0702500d2240c010309401d04100301c0104000340c004c01241003e0748803401d0305107003030b000011428084e050b218183c1d40ca03052501400700240510740540010742c00074401c4580030068403000002160030b4110384034a100040503800c00d079000c40c0c06648050f8000d40e920901603e0208 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 161084973 1250 161083723 161083759
    0x201052413020f0904140405060c1c0c17060418060e0f16031a04030c02040e0f0f1b0105031311010302270f0111030f090414042402190c02 61
    0x1104040e10342c4480061380d00310078075040c400c000480300d54001c0c21140341800d4490a5507600010003815050400081c54000d0f01003c0c41c420600031040b02c800d2041001410004102076103035510b100549030002c010401c2454980030390817001c14080000d40c0800550784820010b80014000c2c42c1c500d0152024140400b1002d00c08001003016407500309032400d00c3d501d0080c42400a0b802d609540052000074440001d42c482c41c01140702d030301102c0105090558040160402e400507140c40744510400182c4a446540030032180402110052942184c0d00d0040055a651000700c07022110349a00d81c0955001401aa052206070700301032500505240c0c01034050100040700c0c1003461148154107100404900d4822188213410328286000c041200074800030075074901a56030507000000c800b09950700e030364440340e018046d043c15580d000f030090701301801e01c80005c0c107034001c4440c80b01098401e205030b58155402110342103900c0314440300202886510450300c0021000040380c1c0009641a010f01c0c200c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 161086223 1250 161084973 161084977
    0xa2109080705161809020310050a09050c030304050d230a0305070b060102011b030b0607020901032111060609040305071403040501030e01060b070219090c120b01020105241302 77
    0x2600c40c10a256945001e0305080b0303d003441120340c2210626041c0d2080c40200a07211083c0c0c0408184100031640300f10a10004c1d0410b0070403040c1034203d84c44e001c100904403a6642004048602510982d001c08a90406050326440b5601a01c0c0d041101d8000040c005440d080c1a42c82d09007200c42c0000c1410300d140030351801c081c043d80c0c042e8000b0300041020000c0c00700d04c007103035508403000740002c0103e4581343c43d1581603030300170700210720030315503144004219500c0710002c503905154010104405907840f480c2c980302d41c1d40c0e11118206414017290a0b190b03405e0151540d08420043c0800401895a82408002c1c4552009000710100304003402080c0008900c203420618680100001c0c544850a100005003140c2c00310005030b86580c1415000c101c0c1040100032181041d0301518815411010002e808006c0151a0f00003000c01d49460011039180e80d009000755076080e1412410b2100c01003160049003a10f400343c40c4d102803241d0502c1440e480002c0214608103000c4050886640700410900c040200d03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 161087473 1250 161086223 161086241
    0x114101d130b06061e09040e0c010206010603021b19060b01050a1b0f0204020307080103050c0a0302060d11090d0303050403081302030d031a040c080f011512020a050403021f09050a08030a21 83
    0x54201089442c180c0c506801196905400c0e10009c007800711200d00000d5403490103100d44000c0c5540002d41c030940f100145031040240c0340700360480e141501c900c5003007402068590f8003a6080c40c42c0c240a0081507101d201204c3d4910103239074501107034044603402103020f0808024101c1d04000324a6840006071118006144501c0c03d5444414981d0301d1401c2060801c8082c07642d45110312144507007400141c0e90a03054400c0c0030580f80000603414004030702d40c1e680e44a04090564003c041d40b149508140d0305400c4144224441c3d81e0300ba0780307901c521a83c040303c0700010380c00a40c1038000f1107500111500c60790040c1001c0042ea0380306a0442046c1c40801c044807104001c000c0060804020004504481c980050041c00700b4490b08487d601c601c0340040258540102030254103030000390b0748000911481c2070718007454004010504095000c001c1d000340780d0502c11040d0102d03010300800102490484d5a000403640c07030401440c81c01100c0c0c2400c8030100c40c0003640507484021482d120b94080e100b4805e1a0311 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 161088723 1250 161087473 161087527
    0x110406090f02030f010e01080a150b030303090a1103160509070c060617060f070c02090907270b030d020d030c031e02040806101212020114101d130b0606 67
    0x3990503c40708000104205806c2603100e440d4860041224110015024203140d400007a0040000f24105481000c0d20400244652612022080c840d510002107141c492280c807404552190b100c42030181900ea00c8449000619042044010001803c1c201d0301c00d5800700c00c0b441e050800400a56410044a9854005406050b141d501c1c0151000c001c0000c00d4201c10503001c54406803038000002065488507100007809415628042088100b0801042d03028202c00a500301000c0c503140750100764201c000320403201850402c00000f4080c14041255440f0510a0707010306500b0104271020303405001410340740010190b40b900c511107102d03201045608015a401c0b400343e601d5140181441c0350280191180d00c009460000400240403502d25026815901c04446800b004281a05138010308e91a5451000c00c000e910802c58180c50540411040d00c3ea003c41c903660020321140d45806160040b07452548404082141e4800724200000c9143d02440080400d032503c010b29102d0308520b1901d002401e8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 161089973 1250 161088723 161088727
    0xa0f12051b0318040510120c150e0f180703050619030c260c0931021207030b22020303040b07150e0d030c0318030206060a08060106020a110406090f02 66
    0x104080c050b00042c3d0880401c035400e22550070300c034040340c1a84200d48541041040c0b9480c5400c00c000c607003680100184503561004003034141075480500a0070818008600c00c40303000d103240400303241058559070b261004000c1d1520982d1110405d400510010300596070059440803c20440c2d64000d041801951043d1188000145802d150500041d801080c040c601c030030f003038486072881200003002c0110f40401c43c0c822074551580c000755030f110481c1d4030a68080200b8080e040070203440404024030040e100799602030348082048a80d0b511011140001400042600040341240401501c0401096410300039610b80451580c0000e14560007075000c180d012202081404c00d0200f183c880f40da90b03401145e4140b200c21020000e080d241d84080d11480240b691310710011072400d01c40e078400d8032180c103140d0020001702d1482c00d02039560101100c02c18441c2c03030001008502c0a0010a0b2a812610075400402d854440b60341d42030344c3c1d482c0340c3d00d01c960010350b5090b0025207040d1074040c0c1101e001c40440010703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 161091223 1250 161089973 161089987
    0x5190b1f031415031b0a03080409090506010503060606040911090904050708060c1303020910050402030c0403051006060e060d0f050109020406020c0a032003030d09140f0a0f12051b03 80
    0x101d8411070041c0b481038802810101510952004510724400c005c0a841061a507541a030004090003169007014001130000b14006c2543c4d10745504c580121801202101c03907982c2c0e030314201551403100b180c115400800030f02c0100400003143c0c000152440641c01e0b0941864010400700312810320440301903600da80001c0b010410308500f40121a0080040c5080c0351030558107140144150702c0b41e201c020f0140d0800000074819180c442a00d002800c1c00030015941c0c0d01f061b9140100369002400160381600070480c0d1002c80c00198407594049031040e84400c1d00d0008041b00700402d5400c414840710009484039050454284944038060280952010050300c50b42844402450304110081b0a4020071618030300f0700200f410954203000c400480b10080a0804e441c5e0042030850040701e007005049824691004100030355070345a80c0210780c500d400c40e242c81f09071501d410b640d40940355002c2c150181059240000c250422039000c07807440503003441031406942026902c13001034070460304205900042025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 161092473 1250 161091223 161091251
    0x1020c06060907080103051b030a052a0a030b01050402090d050d09060e190506130b30010b0a0302070305041e06120b09010b07020102010e030409061805190b1f03 71
    0x143c01030a00e1424490702d40c1165500307599164a01096003841c1c8440c064260290b404100044005078002c1c00c0c0d42c40c51344036258003d4010343c28406401080c0390320b00303140c000b0f080412043c4210703a046892903e81b80d180078207000c025401003008a401081c45189440820000c004454030b414495442601c0d0f28540400284608200c5140c18454031808511050048191241c88240e86084904940d12070701c9510641e4999940da01020001d04040341d10111020010b1021402146070085000350f60100700203682581c40134051900d00d95424004090030300d10036409044510f210782001894207480301e20518041000c5039808071000710070007080c091035038400124100c000700c4100510200e400200007ca40900501565401400c04165001568800d411054180c640e0340d060341d0303640d070711010f00348080c001c98000d410100319140c10230400600d01b807060f14803c008a1041d5045454200f22244c0a0a0581c04550344080400354402924400c0344d04110010202e13100020910001d1241c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 161093723 1250 161092473 161092489
    0x901030c0e0c09060a030b01111b0a0501020f0304090507090f030f060c080112030804061103010b0a020c033d0e0f1e0309010503040303020c06010303111b061b0c0301020c0606 77
    0x800407094509000d2083c80f0384800302600e5072803d650034082020340640d80100c4507000d46600c107010030700c5007403901483c00b003802000303540c6907905880441d10750340c40c0c000690752002000c40420807544200400c10402d0940d45c00030381c1014881c90000041d6980d034089000d04071441e0800c0d04c1041030f595154080150703d00c40e03c1481a91414881d402c0e40c50078280424a1a036900c0207028858050002020810140d01443e00051000051526540c4464020149070040c0001002500c01c1914201d11441d00003003100ca2040a603103a000345400d8804640320039960240c511550303031894074584c88912164015040b05107403d900a18024840e00b151328a46400d80d429017008020441680c44031180c0842210403030b002c02e08003d50380742c4507840c02314000e1080359076071406402800000f00030103a00c00b01c108143c2c000901214240c0010f0040091000144141268807050400502c0c0d081060040d8540755516000c0542d1719443c900030209099034010700c0a00e590303070444010001140f40501c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 161094973 1250 161093723 161093731
    0x30c1e052d0a080d03090203030d020304051c0804150c0309051c030f050609220507031211010b0a150507050a0609020418080906091512010e01080307021302090409020901030c0e 78
    0x9002c0082c1450301c460244c40c1c0c140382c214041010340794100c210130340d141001107851866000c0c0b011582e0740b80c242000b584640010030f01070392003a441c1d01d9a01105200f03c240a001e6500141031580000c818014034000301051040101459203407840c83c40810340a008840b03c4602c10f103800300c001c10271500010b04440c0341c20300c81182079180809100164070745002031a40302c0070340000554910041040410910105000103100c2c0c4100b610100810400c48401620b044041e202c024015600e44902e6081c1e411462041d50400350840080003c0c08224442c03000e24030160820f82e16102041e11250b052040803c0159220b540b1000a0002c40c24580300c1d403c41580340d40082003180c0d4482c0c0d2081030074890505030a11550001c25002042e07515503415484240b004112160384031614060581c150509116444589101c10700000d030b10000813044544041d40103001840c41e1080401820080d0407000c0e82c95006661106120700684030404000c2c0698001d40b008012549030a45041074158010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 161096223 1250 161094973 161094979
    0x10e06060418020304020a03080406020709150e130c0b0a0503100506030c070b0615180102010e0607020705040504050c0301020c070905070203181c082a0601030c1e052d 74
    0x1081000c4803031648104030810321502c01603503940f241d0001594010310383c0c001500c8150006000151550002541e03400c841010788240035840c440a104c1c520041e103449060000d040c0300c2d00060707120070903c0036186a2441007085c160260744415201050f504440c07448808118000140107000720101c3c003100c01080122281491880d2140c442030180c01419401080b040700180890b410359150485406280b000b00b101c2c40e105e10000142082e18201d48030340c076000d0f501c1d10300c0d0341010810100e2074502c50029600204407440c5003809100040000900c1642d080c040c01c1048580740c0c0e0280005c12200b00054000c01c40c0390f0070410050121000602518159030081040104150180440a503041000c59101024241710b10b449081c0940454005010f643c0c0098500300c440d6031400d0901c402c0002c03142c0031007414031581c00903507142d20a001c05003007400c41403010405d14440b5400250061160b108040070b0755038030030118000200c800600e0049001020446100c61500d10920302000303011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 161097473 1250 161096223 161096227
    0x20150307200f1e0c030d050d0f15060f0320070c0e0919080d060320180606070507030804030507030b0a0207021003050a060308190e1017070e04020a0305010e0606 71
    0xc000c540d950380f19900c040380c560f40741c9000c074800c003840c14480c038450440c020f8151490b8522415006100d43d01580e018000f0758a0b200e103890300180c85104d00c014081101c0c00340f500e440d0400b00c00780e9880708100c004e881015200c4141900d9120f044030401d04a50800c55003079151545440c1100700803041c1d80000340640b24840401c000400006200004181000c00070b1172222214106080035119004059804509240c1c00004205480140c503040d8103800d1420a2521460030800c1020306014480e9610600c0402c0800d80e1792400030024008903105204543c0c1c556039903921000990082d5100ba10541c11100c010001d100b902c0310600c0d840502d80c1011850140d2560000318881d004104510805964000203840d0351250b0707012030b01440d040300740691034590341c07212400324078014187c0c0c2002550761101d1005c0340c28010b0b0b001c1d098940d261640c8010f001c40104205807004010216000c0150070520700c201074680d0b200074500e4490b00d650105003507040030b4100d0688500030740a14061441 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 161098723 1250 161097473 161097493
    0x60f070f0e010c020a090c08010f08010605092d0a05060a14030616030608010603050309120304060c1709060a0201051e0903040e0a0209042a0305042015030720 70
    0x1010110740a428400d0921040440e801c2c00450059034941d0001c3e0451450072401880382604090041d040307940304c0d04140000c80e00d50000b1820380d581c41c8510b42d000000f64012804002e04200c10305801e0a01541c181c040054200800e40200015580982c01d556510140841400c04c40300d034402416889012904100c0a100829603c007001800e0122400064403c0310145200341c01031002000a10000c2c8a2640c47c3d0401c1501c1c0c0c0e00c181c004030710511100440100d0410080140c401712001070b20b6046003581192600400e9031420802809924020805a015562a1009003c40c1155680000f0f09481d01242d000301940407106801400041d0004001806e60b0008c00c40b400ea41041010003101e84031a0b241c00080d0189150150b841810302e1040707174410750020106188001000c01941030020300f40c005908440c810303207001e4030740307002d100303502a036101001a0f4044001e07001d440380e11100c58810080110782c109031803080c0003640c0c110f012200d07607170460711994a9034001c00c044c0c00c46144e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 161099973 1250 161098723 161098727
    0xa0824090106030507030b040c020f1501050a0b0c030408011422020306150409020a15080a09020a050d030e090c0c010608060c030703110706050c0a12020a080c0f04050301060305060f070f 82
    0x10144160340406455100051703480780f09401c1840d110802800a000c01416190b010791510f038480b00c024064441c0c24154405c45400805a60480f14060b020048890a0890981d80c3e50310110b1150502c1c4010480003441134024891f1107481c0c5088400010107081c01c0c2c10540751060003038030f8004ca48622007414070250b86c002c01d8254010381400122252000c07902c2c08100645036070740020790b0085000d6030000e0a03039200031524140ca10b5607600e002503a070307800110703038215500d03880003135080112404244000e052650881d2140c0d800381c00c4c8001c1d2182c5207400101d02c06001c4501440792000803071040d0303000f81c007406081c015110034400303031807503180c01020211280030041c071480030180c41c5c01060200c0340716601240c1040e03411000038040c0380350854108444c0d900511510303000030700020074109900464800c0c0d40040c111643d81c040c003074542c0c404031500740d04602600d0031440010080040c84e603a0922840c0700840c41000908a189011040082c0c2140020140c03400d00401c5c2540f600c05076 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 161101223 1250 161099973 161099989
    0x10e0a06180518070f020d080a09060b190f0902160b040c0305030c0708120712030b0f1e030d09050d15090c0305060906061f140705030a0824 62
    0x1410501e44031550080c400034614075001581e02103600120290001145491200851849001c55413500a4105880341040307a4499031140000d0000d007403c800700e800e2000e250004401d00c2d020307010200d00942414002250241c2c03c8200b0b0302c54840c1c0310001c0102c9103007903242d10003c009100c021410108841c0740c0144000450030014400d400304400034003000452000b8001440c1c0001c08c0300d40794810034000350795800490240c402c0170311a209680100088020480b4130342a40301c20040070b5050141303419805410f4040070280d000c81d01c2e1840c00c00d07030740301c20001c41100007400311075101840d004170600d8148141c00100604000c8402414080768071844c0d1998040c6500004c40360005d06c0f90f440c2d0500030706926100034201c00e08400000700b0700200040481c011002c07a0113070350194070340500704210310091540009049145407a000700840c024500c01c4144001141010b142800d60f0395041d00b56803244030300ca00490120014000f100360032140844400082209110400707855000180d000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 161102473 1250 161101223 161101229
    0x1b03030106050d0f02070605010b12010f05060d0e01060312020a06052427100303020d02010902090105150405030f030408060106050f070f08160b070e0102061e100b0d1a010e0a 77
    0x490f1300c4150714000d130310455040391456078004804100658548120003a1503000740d42c02400d10300a80c6c000300b91601104014030072507000070612850440c1c0e605102c2d02a201865a8032005d550382c00000000c42c1c03410041306011030803680940440a09450614102e400141c42800300380101070030050014601e418199a0039070454199104001148461001d0314542022342504038100c02800b040035000001d0780c0c15030b8880d40075541d121039080b104078200d07001910701a602c01070040c01009039007000d18550700c0e5491903040311803070a034586020a04c4c0c40b20f00003d100040d440003800f08140c1006005060241c0580d1800b2807a01101100c1200b0724020217501420700031a2605807030420440c0c03000c4860800460b0071895004401e03080120f8400e004490040116948651743e08641d88085003d510400f620601c0e8a139803500a01b249031202c0c030041ca40d0303521400c2c0c002c01160600c4403e01404000b440d010021500000c43d032864220031426410541c10721617000c0c0442c1d0f00359258030f800015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 161103723 1250 161102473 161102497
    0xf12031b090e010605031b1305120d080103021908120c070b040627080a0b070909020c0a0816020d110f04020304030815040b04060e010918020603070305040303090b07051b0303010605 80
    0x140d4888108211500341f4800c164030720850300090307102c0768501c0d01a941089503000c0303a002480a2248020684903a020180b000004401138010710042c645520090b171080140107003414003580710030550f032901102c680c1143d0940d401003042440d8007800c00c081c0c00500014603c040c1001d00c4c2000140048404c2c024030310907c14191031740d03507030401300c51180b1008004100407110312410070f08040c07921039000c0c4e074110300103180514003050742c940718000c840440000c10003d001c1680240c4401d000780d0041859080543c05030f10112003d84d85074608841810301601404440c0c500305010000210740b5051500e0003180107000b084046a08025032640c8242509a9000744014001c0001d0050a40e003007980d502a14210020a10300c584a108605035400c01404010324421000080b4645c084508003d505c0081000041d0f00c3c240700750020b43c0c10910a0074040742d00710b400d503180c111108040307400c180000d00100b40030f00010305101c03491041d080310002442c40c55041c8a801403080c8140000340364 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 161104973 1250 161103723 161103727
    0x3030504050c13020c0c15270a0b042409030605150306010f0e0603030f072409064503020a050d02030406020d050f0403020d0f12031b090e010605 64
    0x4240070040c0400c1032114002031500300e5022442140100a40000c0b00b651788520030929610604e00b40f00100b00b54000316445502d007400d0034524000c114000500458244406a00701e006007030321440d414401401c046c01d0b4441e150750401011588892556000c050100d00d2152402d008542201d00b00003a40e030001401301d003a54400600c441c01d4400380c1221b07609845054000240001080b04c00425584011001d038030a40f150010560b80c3d004a0080c100c58520812640e0001203a003591100502140200e041103410f1602202c000c0762007841c0291085511014081940640500f500d50350741c05a401564002200e4010001c0c0d0b4090225210300768072066a1020616000300010784845030300204a980d440244070b17000307440c1d41262003640c025100e504540040f40c2d00440c10380350b50380250f00e485820140f56400b0041c1c900d48074202038800c2440ba920140100c0d480c0304061a0445080d1008124a201c01003000e04031240701003000c040240b070f100c040c048080b0002c80581113607101d2820a07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 161106223 1250 161104973 161104981
    0x31211120c07050616091a12062101060608010504090f0215090303030a0c020c06070308060112110c060f0603010213150203040f06020a06050f0105061b030405130603050c01020a020d030305 83
    0x9a814441c0b444058168803450040052011440100f0016914a6a02d81080659800307000e0043c0002e598590f131b21a1044c0804680078204c0f070151680132000525002d103078950b000c1c2c810b440080c00c01c40982c01c0d9440d00424403400b5008003542c0d0050905480c10081508161601400c442011400a21640000310000e00b880506410303240001002000e49550b4148406c41100600541d21600c01601411549aa05152800581d5907507505615000342c0c65650700011510142c0c03900403004110760343c10741c0600c007070880701c0503100c4821030780020700c90340c20451b4030207240000040c41a4801ea004000380092080c1912104048801020641d09214603a800a9081d400b5540000c02d150618038400110a82c1c0018907a20743c0d8050070003003089440e4806550350328074003401019013185040090048820700320801030143c220b400c00b0f40741000e0b2620b0002c1d9151141360460700e0403230f45459080c82072007028440c1414203c0c09000502a464081d0301182c182d000803080642411790350740c002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 161107473 1250 161106223 161106241
    0xa02041109060f0c0105130b010306050907090908090a150c03030209060c030a021005130c0303050702010314181009020a030b18010203010b1215030304090c0905130903121112 77
    0xe00c801001c0288416210002c845900a00f07821210a0700ca540d07080c8030100e00205603500c0c0d049a4540c1141000c001a07085464100151201400700324091090030000242e036142d5102e690080c1c1e118111301c550b2907403000704100300c42c06640c101c550104118580c0f03030710803504808400700c456458100543c4a0400c200061018003c0203070202c098040007403418881039005ca0a010355407074117031041002d6203943c09030240c5d41100c084000c0609a03141d1040c0301103402140600003080c4145404100310042102810160707a0940f00755100030a840b01c9074944e61810710251407a942c500a04000c80c0b0020340025411341c2061001410b200c0301c10000c130f0508104603e070320b0f00229401c0001d540e80d5940c1c2160750190b510041e5240380b0b41000c41e012846130701300035140121341c0c1340040045040030b0801da8900000c01c1c50101103400e01660b402c0014180d121002505070301c01c0b01d0f60b400610101d5900340a00b00980109041c2c003884c2c90207924002d0b4403105005e45245c501626980c4001c1e5540c2241 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 161108723 1250 161107473 161107477
    0x115060f0e0f0303040801090b07080408120613060e060f12120306061303080307170402090609090a0c0e181203040609030c05010906240b0313020a120309091a01020a020411 76
    0x82c0398050000040120726104150010111107100307941050480d5203103101107592010a840c010311420081001242d00c0085a0503035400010040801000952180040b8115182035220300301c001c10351002c0000c90700c0e211200710300180c01500d0488260709036442e800e4440c1b071949030b60843c003280400441c9040d1904025110080791480610410342d840e030500b100e45400480d45c440007c0c0100394220807800448151a010b20b5020309010342c942c451000300012081c004203440e000307120b8000f10304042510f2b444a000204039200305c074503060904030700b1501c0100c030403081c941095002e0740b80d5511401034a400c40b0381c042c0e0030840000b04060302c0d00e01211299903200c03010700250b082091080c144841907000840c6280e103506104d070b03000400b51020741c014059114420414106000046206409281070304050348010400130700e00392100b003020424020707403a090f00000d112030001c0c4606c4c8400e10600f84885059405070007003984040000703544205814000340641c1e1030307141c00303141083c0c2041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 161109973 1250 161108723 161108749
    0x281a040c050d0b010807090e0c090a0e0d0903060b0307150c050a0c140111120d0f140705030a0f090804060c03020f0f01090213090f1707061d0115060f0e 67
    0x4650b0182a420020001142800381d0b5105010f4941c0c00a00405203101da400c40b00013410251000350207203401c000c14280c008000e16001501c9103081040c4c41e200340809064840c860b21482d2585040d41013074011101c240040c00c0c002e43c8400d6007409280071007180703292401d14514100303090841d589489130620300c40c0d0800030446602190f0108441030415511840381000f070f42d401ca030910941c00c050780d582203900743e4601c440c101001103100d8049990405030109806040210f540341031186411301d08d4000b1104080002c4002c01400441c441c14081c1300c080100c0d0040a0000e50507984602e201446284520b90503c03d840c020f03503040500900c29000380d003003d4419241c1c08511584098040c2050352030480c400c40034a02048152500f0f8492441925000000f5041c00341140d80c542c0701d10815048000e00c9101c09010000018426002e450900380f159018800403001815400d802d60341a2041c0108460b10340d00e0900040f80d101d01010341e000480d140900008003090041880c10403040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 161111223 1250 161109973 161109979
    0xc06030415090b0421050a0c050c0904060b010809010b090a020a021009030e0a0603050903030a02091203041d0a0c020606040216210908120f0a091205281a040c05 71
    0x64146040c404458225132040b0300403014030100280c03601c0581406031002240b0800304070180000301626104d109082e029030302c1903003142d4114164000080c952041110201c07110754550102007020b50b03224038176a41103c8008004d114050b1120300041941c90014000005141d0109801c14164802c0221040058150720100142003032070800401c24540b00030b9990251749040b20000c2da007403182c415184030309209406182103441d0490140084d40c00807403039a0344802e151400003503a03d0140300400081c0303401d807134590741d00d0300c1d40c41c1089205100601c080b5400b8134110492840035004a8000c1c0d01400c108d400590f81c0480c103014805402869001401481001c6234100d05c150a603541410b09010b80c0c1c89480500ea0746c0c12030196a50009011030040e010140840d00401d00040003070140c00441d0b00780441c2c103035101e00300c2c800c15900110064841d03a12122116420803101d180c004103210440000c0c2c24540e11648031f074210381240d0201d089130703114602d002900748650300d02201c0241c0002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 161112473 1250 161111223 161111231
    0x10b0319021c060e0f0f21070303020403050708010f1404020105120402042028141e07080702010e010e1e06120906070215040309030b090a080a0906030f0504050c06030415 75
    0x4041c01e42d1885c242040b0890f510840b051300070281c50002d0303c1511049801402c1602021031141e992003034100c00802c50a01d0380a202c01300008406000141c081c2c1420300000a400c042c0c81e40c0e075010345052101484e00540d8400600002d40d03808421180e0044107800c0141e00ca031502e10101e8001c2122042402042d1003144201c80d400c807174a40140f0103c3d0004c4d00304e00c286408d408820a00004d084d020b000443c1000d00301c9030003440200041c220794035070300b4840c590347e4040303d1140d8202da20980302190148030000c1c01800715a080051070403000001e191104400c5017001c0403c800080d440954904c464400301c004009075900700854141109184501030981085005035690392010f4070b500c0c0150150507a0000c100b507000c5c0c1c010384a580c1581c1c8581d00c81303285880381051118050071400860142c10f000318081503c000c020815030a02d81d1b10103079981d1400c1402030071510104406140c690a00b818800032400000758070100c1c2c201181c1c141e40e81c0c1c40e585030816103810080c2281d0040e50030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 161113723 1250 161112473 161112491
    0x72709020702040b040b0901050904110307030308010501111f09060e0312010305120702030a020105030703151806080a2613090c08070c1208070c0b041103010b0319021c06 75
    0x2054000d411800d1007079809118009500082005441103e0902604807070078000402c40c502d0000b4032a41c1040c0514007006100c08030b503000c6810502907400c20b03800314607908010840c9503407258680d64444a902c0c0504900c81c0c44900c11054540314640420259071122500000d02c0026488449001591000c603940ea6a0310640050154003d1106642500941c0d21245403680c24008650646900802030010104141e005442c5604050038650400d942c4210700d4060700840720988024089804040200c5144900310500f42e950780d411030741c51500200d032001c002444080e00344400316440701c0402ea928421040c010f049014414446040b1420860002000a040d41c4041c0282c0c02d55030312180113969040c025560000f00060082c0400c0d8580d89419600d48a441196080302c10f6147c2401c0000311601c031148081002c0d201916242803400f0442d220345800d20078684040300550180030402c90420407040e1004450001070301074091045c00703100c02c2c5900000090780b030394082000c04c0034480c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 161114973 1250 161113723 161113739
    0x70e190303050c161404060e040803011e12150c020109020906041109060703180f0506071407120506090f0c060d0b010507060603051c030b060703050f122a120727 71
    0x105d102c080900492601c0400b06100d800600d00a10898120141c01d182d40d01e0010000b5101100c4040302c0c000810700d40d000700304190030240303501c03a01f07000f4000407002ca20002504030449010103940e1066a00d0a201200161500d41c81b69501007002c4a00040440c1800c007114034610a145601e0360000e0006907000406400004101000d00704000081c203954440c030200b2020f00c039902401382e0000f000c2c0504800202ea402c180c84004c00040191000b440d034403201448102c0b080700045030150400c0040040d0301108106829000756450020820b00441d9808a040d0f88264040c1488042d15084504e036207034011802c651030140d008408001e1b1941e07130b0421a88031480c00400d420881100002d2516242c4a4050300461090040c0803d240028980d13081c0e9079a48a103014000302d500500181080c40080007031188640041660740100c0060070040051034103e5203450581117009004540040c0d211581301c0c0d078091620b0078155070503441a505a800d44801c00c0002d0031201c3c1140c40403030303100b0b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 161116223 1250 161114973 161114999
    0xe0114070605100303031104051302070201030e06150f1c0b040606030f0c09050601031a06070203280203120f120411030a120e010507111005070803010e070e190303050c16 75
    0xb4044c0c2d40030807d40109038a6002107109500c01c0d0740d405085007a580350003006590040c02c00e40e105040000c1c140001003106801c106044a00103503481540700028514141810f085c080b82000f200d284034003402c0c201c46d5420007200644042c02500030030002808000150740490003964100442d0a4180f00c146060100f000c0103004031801c9038203000115103a5406805030108801905022400d4021400c0c00c2c800d2075009a602030383d05202c0c01c04044030808441d02e03000380c00507400350030381c00004040c01898a4a4107641c00100c0c480c4040004003890380800f41a030304946030010940b90542c0f202d0411400c508410480d05906002d14440a02004171800d9920081405a1540e10641164600660b841d005082001d00010084000240d0300c2c5801d901041c3ca0510f1414840d0a00d5400e4a032500b458000b42c00456044284000f0b00507119040fa083c80394070a012100c10a43e840c0042707440000e1030052000a0620001054041d1505001e011141c8040b20507160300401d541c1d030341c92404110f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 161117473 1250 161116223 161116229
    0x607080c0708031f083405060324010503040c030204051305030309101506140f1603050403060f0203040503070b040203030918060a050301050106022e06092004060e011407060510 78
    0x2d000302040040c04ca00d010400f0b4254000e801024038031a80401c6c600b030098400e440799250700000160000c10315569100140d402101e508800f84502c450912180104110030403180e814000b0034410000012010004002a60703810781340812070381c80b0140b04680600e2911402842804040100241000c00082d840c048a0b0018030078403149100003001c44d6200f5150140344c0c00613800380011004440048000c0124502140d601468822840c0e1411810b050300344c0101c00080e0300090410a0200900036040c00c3d03010b80b01c0451550a2554a1aa492250301d01c02418501e0100c0010103666080c02512a01c81004d410440e00100c1e956818203101c00440c1d8191040560940102d418201441070074162600303500200b01004048000756080b140114002d032440248102403000585240150b600401118030040303150058108550043e00046002c1c0400302c038280000c0101641c0816403814445081c28000780400002d001000310788100c0502416242c00c7c58180209901e04821000071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 161118723 1250 161117473 161117521
    0x70c0302010b040c0e1305160305060f03120406080702060c0d090c05040e030403060509030a05120907030c030809010f0201090b0a0b0604090e030301031a150105030c0c070609080d0e030607080c070803 88
    0x18000c2810b000b01c01f00d80f42640c0394007000e03440a41a8451500a07400b03940c0000c001403805041031302c4200040d241c22502c0781c9200c078905010408114858000c00d10030b821402c00c0c00039281da407070520302e02074190240c030201003c0580c6940d03080044c8a80d030200d15016100152003840811441d45c1d03010380c1c0303902c11f02c0200d03031041ca400d0004002c40408000d492110586036500c51070b100e641100c2c0d114040c00905200054058680004002030300300000703034000d5115203d010385501031200050f00804c2c045011406590501d0481000600200030303095103c449000001154007010021861901603074100309100303450580c180c00340d100000041c60490307106850039489650507020000c10844142c0d81ca0b6011618803000c009ca03980210042d6134040d03404c60505080c241c82000345842c12000d58000740118203641d8051110308802d00880d0300c010054141000758000e00c0700407170340d00c00e8000c14840c00c009082c00800c04807a0b81034200d580d89504000040d4607401d14014541600b2014030345000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 161119973 1250 161118723 161118739
    0x8010204150206060f0904140a0308070e010e030a03030e07080a050a0506070504081002370e1207050d060603020604060503011d07050714030910090302030f06010e070c0302010b040c0e 81
    0x303002440000c03018071809015100d1000c180c45001440b02175480680112212203442c23284103842c1c9800c0045505243c020b42da01500390034440d134058000091002d0107410441c0e020440005504d0025144540c0343d8145400910a901c82c039060b4286061038112208034000c0d016590706115001400107941c034081c505940464648141c161618444c903c40d41010360000e8442409684e000d03806803074400030310710a1000c2004060410b0784400d08506614001740c1d00445650381c0e607030b80860300e0042640140c0c0c041c54101454482140e640c0d05500c191803003000c00c44078041c1000f06540103007000f5a03007e00711684494840b600540550024011940c820b000045181c00021413202d4550040d05035480d6149020459200c440d8514402c01c89405288000c009414440e110218585003c59145d0f60301003d560861040605004541944400940c09140117110f015141556a81c1180341824000c0c19520303280b40580c09011800341070350f48140f0b03001d441e1400319088020030400c400d007110041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 161121223 1250 161119973 161120009
    0x203040305010f180809060904020c030d1d15040510050103030f020606040c05030f07110304060c02121c08090109061a03010b040603050c0d0f06020301090c17040b2d0108010204 78
    0x120413200b107080e803114001030480d9003002103044c04004201c42c0101501c076918003180b14006c28241c1e407000014000c1a4000100e1098404551144903850909200380b408203221480e4040d43d5610a0440455828000b401040400c0000c01406c0c6032044060014013943d0b0b501d0401814824050f604c280240c0034443c009862450240301c0d1000c00d8030b00b92074250458448d52083d8503a000700800300303018012503800008800204001801c001e160360f40d01c1c1c0c11040b809205002280c02480343c0c3d12100c0c0d00c801d01249292541078a858280c006a24140b8103a03a200d1a882d0302404d800c01001c0c116500e0203a89000c1080080d040b49141c0c00140c00074002c000059042c0400c40c0c0e0207100c06846900450162109440d020245030081030190b04c01e000351a4443d01d842e012a4801e034010691070b0342c1c800d00030309110707082081da00e0403c0c800340764030b0603500e0582c40b000c64240c00100395130030a480e6404c140034a0807800b030ba12010345118201ca1400e568480d52010700030350080c052049048080d075941 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 161122473 1250 161121223 161121251
    0x708030903060703020a020307020411041e0320011806080f010e040c15090503060906010e090a0302060402131b020a0501050a020405030304090e01020c0307030302040e13080703180b0a020304030501 87
    0xd925410024008140690380c2036401c0303000f03400c040103d4085000800442015a413503009054404440a400544e190700c3d08221045010310b5400c1c0084441164008001040740c544640c810100c0e0005e801c1d118200c0c3d24012034010102c2e2000c00e6a0000c1c0380c20100c4d1955002c074810740300d03034070704880a038583e42c0300c0c21504c0325003108072401000c403901c40000380071088040400300494811410850706030b41c2c41d40e0002e42813040891f0707950300ea540034000410007052103402042c1c1181000c8080e1901b0282c030f450094850f1401000a030041462102c1c8040d40001544030100000c89003103010301c0d482540000035107501c0158000d0306d2641c205808640703002218421101182d10090041d85000e01d804400c02c06090f800e0f032548410f550a1001040c10718084c001441014032035580140c1d138a0829201101c50140a80402d2440010551074000580031108613030b03030385415041c04814001d4469606078105495004075140f40008149504519000405001900d2049000340055602180f070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 161123723 1250 161122473 161122477
    0x30801090b09060d05120a021605150d090c2301030b01080105030a02010806040e0d20070b0706020702030c061605070e04020918030408012903061504270f0302070803 73
    0x40710751181c1401c02094091605654030803401d4400d00c1640e21041d4a0402850190003400240313016800071540b9031003030481402da403409000111450b4502545010322034501c0e0003045900906159188002c0081c040e054240704000d1140421400000440c0c0c2031840a14400c818400d0201742000e00310b18296004515160503180060014a094007403070f00116914000070300003940241c1c0e1085040907140051000700400c8105844140c000c0581d0040c08200c0e80d004c00303451255802c820341c140007440b903100440700125080382c00580c0f600c60038000a4285680c607140c0d950320600010300680c2100380c8015415a41d07008030240d03100c465845079190122501124000c0d0700201c201c0009801816040a490703414105c24126410a91100070301821510036044180c0d0410860300c1d449403900d0100e4101409082c15030143c03c50b800c01d148141021100c440d44d15108981f9410220840c1d41c60481040258001d161002400c1e84c081c10440d410051800c0103900602031400042107950000003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 161124973 1250 161123723 161123741
    0x609081b090c0a030b06220b0a0509010804110a090b132016060501080c1e1e01030207020301110315010203030f0601120605030d110f0c0d20180403080109 68
    0x304000841d52101e1008034940e1100c606001413583e034500e1200c00e9101c1c80041c1c9885c050701182c0603102c003862146140fa03640c0b03541c0300b08100841044542c002c940d0000c10f03258112020b003041006a280d9251030551110200f0000f80c0081d1050700004502085410040c4054419610003440034900900b4106440a05c1e00c00081800300007802a40c0d548450024401c3c51400e500941000c2c0140c0e44203415a0400c1c0e1003010158080d0741c1584141c80d00013064501c034105901c1174500070b198000800d541c6140c5500c6030445448000110700c16900039011545050b600800030803c0480140d12654150021340300c2d484502002c9040852a500000c1103030b008070100141019299070312801103480071101010854103540b40c0d03100051540f01041590b90142050f248d05a131803030318007481481e01141066440c46607001103401e08103a1550341c4031a4105420013500f0240041c8481802005048074180c190080d58003020380e00c1101418480c1400b45100b80e4030424282da90311680015950400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 161126223 1250 161124973 161124979
    0xf010f0906050a1203030b030f030d1401060e010804080c01020408011a04050c030a05040206040306020a12050f10050136170a020f040f09020907030207022803080a020a06060609081b 80
    0x80030521069141e040c1e5103229034802d11b004240d040c5600040380c00c4c0622a44a200c45600200d40500006401e0203400c0c8483c105641d024102d6240400041101c00044003240c148401303440414244200707501101c10301c9451100a41d925580e42070030398020a0781c0744582c4410940021014103514050240c0c0e40130301c80c90b44000e415503c0d1403204c00c004044c040c01c204e1707000e4801c101c000700141c01d90010f8013400045448041c0241b280c50140010f40c0e50007041404043c09150400102d41d1803180443d060350f40c03c0c43e01c04c40810880030101c40302c01015549034518115420f107421000880c200b000181c03804908008681609000401d50714840110020760010030040700d16554101680086610007205e1400301d240200c0f500030071800d003000d581400000381c0001d41e01007981800d081c8610580c01d403186400708908014040d40c5070b0102c5010017003d0b03500004104d0082c0b40b08000d5100060340045017042295903440001e05518207901c03420709103000309209015031146034100e01941c01006 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 161127473 1250 161126223 161126239
    0x190b13020325170a0c1e03020c0a110916020706050901050405150304120311180f040c05130e0103050c0402131a040608090f1002090411070501050601022802010c0804050303030f010f090605 83
    0xa07a03810360359101c0c6d00d90030f482019030a0105440314841003000808150013a126103850811840c184401094000c185d4400390107410154485198001801000c40b80749141c05900c0709900c60040300c8503c00c582c485580514409284040300990030010741c0502d05c07850a002c1c21000001041e0241c0f008440d02e004889410b11110b038122007032031040c12080d1070080c0400480ea04090004044800411080300064000b08905002c0310300400f4140c0a8081c000346012190b1555440303da5031060380c030b030442c002c940105a6038461080c084085000c0c00c55241a007104000007140745100307030801c0c423302c1c2c000b03146040801d1000e04082500340052088da4080c0404042c84680f85010358059000c46030026035aa0407400190b80c42000350400301d11440003c070346403e00100080ca040b041d042120705610000c42e51001035049851740c1d1603225420b0074240d182d1203950400075154011903000312f801d400004100034582082e400080e040c0d5290304800c081c07058a8a191a080341c040e13000d07682d00500c03c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 161128723 1250 161127473 161127497
    0xc080711120d020408031614191118150f1f0f0e04090614070906051804181203060b03060102030d15120506190b13020325170a0c 57
    0x880300404100000030b40c09403800c0e6440a0755403455100300f10aa403042d41c1c5814400401c40e03250040182d2200c20802002c1d4200c070b50309062104102c0740d500800d03010000c10200c41c5070b122150001c04e02d42c0c155068445500d4918446030b106a81c12010520650b82e40c482d410640c508410707900707002c03405031240d408044416201074501002c0b0680100030700074000040505940c9034010b94903c40d11440c00402d03910180407440c1c5900304d01070320300d20030300039200828032100d5840b400391484034443e00d880120165002000c580200710704012900150903241c450014000d01c8410303400c40042c155800c100c06071382c072840340307403107000075240d16006030003c20030081d641c500381d082081405200b28003100c803103a07588400400104100c904a8107a04103000b041032071507140e031a4441030942c8e800244400c0703402c040002d24001c001e04c10400300940c08800b03d141020740d00070f411140c0c00c113109809150082128003510713691051200281d03c401010001c2c5401449004108114640e9183c080e05004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 161129973 1250 161128723 161128753
    0x150a14040c0909030c0210180b04080c01120b040903030e0c010c0b070c140321010b030403050403030503040318030501050907091103040f022d09071106240a03060c080711 75
    0x1643d090268101301a420004c80503076101354000e042494143c0f034246d00100c09407589042000a540010351914080c4002c00001001160748610140709186c00240e0030740081d0842c00034814400da1a4125140042003c20944c059101440d1849200c0c05c48002603001001107554134900c4000400040718180481e01c1180103c213020b840c14811084071091000c192452482c641080280300303011801490292410014541d4660141c009100001d01c0c525081e18054010f104502c0f00900b00b200001c00503007407600c607005014440c08640685103889039641440c42c060320082e0b44541ba64091550300040c038840ca4402d001d03020442c403038540d040d9501d603283c10300d00d13142814081c1e80109011525030b0503c1c0780030000a48502101c500080380341e1004040c041e421b80010884010b01400c0d0340040f07a0b050300010740740d6004006042000c0440032600307100c86041e4240d10801e030084141c2c0404000c00911b80c102c00c40f0503804daa5610880e690b4100704603441c141412904070660808000c6592540c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 161131223 1250 161129973 161129981
    0x4111801080921090405010608010602210c0604060b0f0f090c0a03140c04140f011e03021903060e0c07080307050c0109141507050c1203090f150a14040c09 68
    0x81c05054843c0144641620010400d20401e581d5080d400000ea101c5180381620449026110720b10304140598103281001c2d43d2a40b01e030f503501d044883c4247e041d01e4682c102804550380341502e87e007a61002e013454071700030001e001c5450146110f0202c91a0781046810b001403c42140c1c1c0004008581c1a1540c11041819030700c6441c0003c101038132900c11850308159802c000b809003600c05201c40c0c0d00c0d841c05034030b041030f45041c0074018400e1190246d000e4841c3e038401c142d4403e0b02e0341c8000070401c010b00305a040d0000d205a10544120031414a041204603030154424800c81c0d00701c01454040c3d540b040301c00e00c1d40d4402e074007004110b414244085100c00740300c0e0023f4900740d00b400b00005101d4010341c4451440c031714054824001513000f000d480b04080c40300b1100d99002035241c2010b504113a4108059030301d44010b41c0c1d01020b920000b10010703405030002c00003c581c1381c0c514402d542800c01d6000d1b00b100b104c80304580181c82c440c2041250a041036a070401c00348580d4220044c9480303035041c11411400741c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 161132473 1250 161131223 161131231
    0x6040623030708090d020307021003050a0608060a02040e090a0317090309040f061d0601020717070314030306031c05070201050714010e030c0c0f031b120102040906050411180108 78
    0x35910019000051110000158000c410a44400195181c00220301e4a0b0009482c0721034119003040c0025001030b2100c42e84d44034040414100032883e070781c62001c290001c102c3d40d84002c1072845013200b44010441698010406c1d104000c000300c0300c1d40d541444203541d5014419000300010301114101c0c800c0c1e1600e60b4500d40040808040d2480c04107284001001c0c2c4da402d0044039030141e602c110401050a4180d04001e41c1c110103240d80c5124504280040e480f02d64a1059038103100031030003416003010080c40709802965006a16500e00d02e0029065a66038100b25945c1d80644a001003903550180440500080c0c03298541d621441e0481d1540111016000300004513640100e06090910100081c004d0040e1001c6000085450f02da106401901d0300380614003a5000702520110b4421584010030800303121240d10102044200c454800b264400c80c0f00f020402a81d4404100855030341c6e42604020225542142c042c0802c0b882840b000c1140d10541c0c2c0f142c0c81080280c031101c10254010002c075a80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 161133723 1250 161132473 161132507
    0x501020111121f0602010606030c030510090b010c1b05040c0507050a081e070b04030206100807090507020f030a030504030806040501060e010e13060e0118200c0a061d06090606060406 80
    0xc3d42da50080790000034021904103102503515803034203005469041c840c01002010a10782400141804095030380202201d0003900751468880001d50b42d030380d0082c20317005551503010311035511545110464100c0d0911300c0c0115442103041080c0c01181038030600a8803c075070b82000280c08600c101c2d548030690b44c3e10003400107829111414446205034940409803420500a5122856910b05490020300340803006000c4e145180032100144400400001d0f60341c00d640c115503001070982c80b155000d070f01d0001803071a1a1094400010800d04103030b41038108a0042d0f11a4480b8015601c8040030801a500c00740079640004010700d14100bc15841207909940c000000341138031506501c42c000082c103480041d0001d624120004004001d200c10f507240544401c0002442007106217090001e810200005600300a004038000c00d00c20780002d020f0090803641c1754084810002400a032404080a10281a0000c05401490000f403070311680401c400784a200020035880c42c1500300a000e07a00382e15450b5502c15 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 161134973 1250 161133723 161133751
    0x30604050322030f03051b030309031c1119030b090c07020103090f02030f0322080309150906030109140901060609171c020a020a0b070b06040b04090b0103060b0a050102011112 77
    0xb01248040103112801390081d601c007a82c4804a02c00111401c1c0509943c0501364410810421030b258040305503083c0001d01d6136034190700d00c40441d204c005000710003521741c00150002500150005a1108450070700358075201800102181030030800d800324100c6400000704020815100150b110f1b901501c1168800d510100740511140c0209103000808039502050394800120049030350b5030103221148003c1c070800000c2020381440d42e0140c50740503801d417150003903440380e003100c0a40d01214143d4540300006482980c903583d40d21342c00d90181920110312104040942e011488015060042205640d13080d01c548102a103000e0400140300500440741405000300480c010032241407411440003c202d0342c1c02014840454010001e1846640d8410070303211400304070140000303910010071640440201c5e0006080c51003080400c0c007074900c80400806887c00000007204009480d40001c80c0300c08180c3d8800c450720b07200c0e8010385c220380200b1011001e1501c1031060390002d03000740d000c10380d12412281c032102d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 161136223 1250 161134973 161134979
    0x206070221061b04080703082802060105010905061303021017040b041112060a020319050717011e0510090807060509031006150c142406030604050322 66
    0x1001d440049103012181e03400480c00e00c0300b5500100811100c0140b141c840700d180614003450382d85c4da032000e071100601d0000c01081c0d140039181c4404d001145140303114442600e05042800007515100c1c24007580e40424031650f80400d0500340302040d202c1c107072a50003c402001e03007142c08200c0b41c05401c2078007008000c1c5208402c1c0c40e805d42039020314040c0f8421182180241040c2c54009851900308040c1c60160040900030402600002111500505648401641ca44601c100d41084000c402003000c42c0c41d0402c81480803203075001102a9000758a84503005c3da0340d0303d900c08a04080301108020211401c1d01e00c0c20b108600d083c080c80d44404200307080c90b400035503495103103d00f4071807a50310400114101207046455410240142046a08040c104201c100c1c20411140d1403900c501c04040d0070046413009903000c201d07210103825085400700048440aa100807180301e40d5038061003013880070f00c1490001c1080b45c01c0000f140c6001b2940180550705010030520649480d03005c1c4800c2110101100d5000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 161137473 1250 161136223 161136259
    0x6090402160c0b030c030403080403141b0c040209030307060f0b0a0b0a020f19030c020a0905131a01030b010501210606051213021f0e04151701090305030402060702 72
    0x144030403107041021100c190450304100a03081d5440d441142c1018042040100c80c5154900703c0e94080d41c0760400780c8030350f2914242160003421040b0500081d110010b49006800c40c98221509400141c00888044000800900040c0c0c06410791590b0194010302040c00003c40c81c2c0c000403522584140000b41a803440d02c0065160300c516440300303c000c82c0010340d07106007070b5040c00200c001e00714000050084031440501d0844ca407012402c06010010b032600d0010440d591803d8160040081c41002d020754100003d0a4018115808040303d6038080520751101040030b0030308180c1201c0c2c02010307a002c0f60f0f1803e401924070b28010148101c1405000850200f6a60103114910240240760f66094440035262009280c404016010441a030007101e100c0005035552402d03010911f2a0440301070500b90044026204c1c1410100850341c003600308071109216030075046a85040b50000300000841e0720f0603201e55030888042c02d0001e8006501003000030054280301c00200f2001d072002c0c180300c2c21030401d03882d2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 161138723 1250 161137473 161137477
    0x1e06151f05070b13050718020910020d270608070c06090b0a050108150718090612031403011206110d020d0e070501030b091f03021f03051308090103050606090402 71
    0xc03900c0801c10200314102408060a03059074490940444210888841d8070364913901c408500c174008450541d0041a03c0e554180d80660350201e50141005000320312018001e911007040607405400500301d0304250040d5085100300c0400c00300740c0c0c00b020040e81c0c20500d04850300d2000822520502100c9503400000450500c22055000c1c000c000714041d506100b1600c00c01d40c3c80681c03000c02a0f42c0301c80c0c12140170a110b800e03807d40103000c82c1028008820640d00242c0c501400303520161a19103000d000180c43d54423000c80e6208248296112102025032036014171550200303004014294400b5180b03000014000e0b40007200e015400180d007410940a1150b40702640c0c02032542e0000c1c103484038025440c040e402c100c01304c06002e003400e0510030504004c0100310107003c0144035010a00d00c800c06d540560f160302c115a800b844d005010014a40e954508a8032203032440340c4620700007440c01c6d00144103855540340d814081039100310b40d04c1c6807119440046000d814090310702540720700e00304000f80c410360303503840 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 161139973 1250 161138723 161138779
    0x9080903030a030b01031104080c0904140f150610020607050f28020d091d060409050f030307020714220e03040f030b130b1605040e070503091e0615 65
    0xf0b00070400060090006040e22880b0014043d401c2e0140002e1020850100f00341c06007000035248010300c4e51352814030610a1210300d0746c0c04011700503000032032100d01c0301083c01c82c000200c4504454450720750300d0900c1460590041800d00581004000c40c0d010ba1144005007204d07111002802d0610400c0c5003041191002c4e8550320680d501140b40c0503908a030180440d040d801d40b2401c1003889945001c0c140d8840c20481401c4259440c03824000454507a5154010350445030000120384442c1103595142da80c0fa401510184050b119a410002d201c0c03058554040c80b4800103800f8001d801c03481c00359038080c8070100e07408951580d21101106402070040028000601c00c0c0c04415807028914200039100e143c0140414036002e140301c070404049000c1440554121900644092002409000c21a400e02442d000580441c0540f0184034010744d210300a1070007045044180c42d2240111074015907400ca000314148003540041c00011018062207030110420400907100044203d81109107009881d2502 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 161141223 1250 161139973 161139977
    0x5010b1908061008070b0702010c05030d0b1f0215070302120f0601030c03150b0a0c0b0406091101020604020d1103010b0303031006170907030605060f1c170a090909080903030a 77
    0x100c01005035410411031240c1200c15008880011400c160440d07071104040d0040170040318000514004691140d001e1142142d00442900c0c3c8441c00914507001822400d031401c3d219102d0956401c06080d100c505c0d031403080d0f405400801620071090303031b21400404010040c10034184d007488500d91550112080d944100f1000b0041042441c1c00340000d03048400380c2200d40708061619089510205c078101d20700c005e64840f144815100d40310301c0421100e1001806005181164080c188010060170750001082c461040c49039000c42c20780315004980d5801c00700d901a40c400c83c5181d4082c04240140c0741c01001c40d034041c0002c540f51081c038000c203107580d000780c40000c2c0c0c07004a2402002810741c84103845230642046010700d0410708080010302d681c0c420301c5c08041d18095840c0e010402960740e07a040681e81103405040c0c025401c82d40c121350901824081c506540d4100e080c410b4402c04403840c0f00325081c4680c282c81d550204c50400180d00001c2481d0340b000c80b01144200540c509a540c1000645a541856 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 161142473 1250 161141223 161141269
    0x4020705070e0c13050904020d1e1e03020316020f120c03101103072a030507020108010906180e01060911130509010302060315011202040605070611070b1305010b 71
    0x1208032411611002400f6400201e402c0c480c0403042403a50705108201c460894600300e2585480c00000c0f800385d492900200007240031726200c02282611440d00b20060701680701d505640c502d003402c0611185c4011801401a0810000d05041d603540c58440885a8009094102d064030404089114141809100c2425074003080da00f5086203401c10503c1401104101c00b40034aa81e015042180c0e800054100c000703114601c2c040701c60a500c2201c1c0032a107070f090351000440d003c01038100500558013441d006d0340048c80080006c5654025030203100211940071111010310511060940c000342003084000d801d40d52200300c000350305502c42c050243c1040600058a03920742502c208002109136513840b1a0142000f08010005641c2d500d0130303a40d01c000c01111707440d49064900700413101c0c0c0e40300d03150700e801071403000c60302041041d407090260444074031607101003240e010b8100034915980208100181400303101c00c000341001c10001c0009034014499400450700c0044800050ba0221500441072408100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 161143723 1250 161142473 161142479
    0x61403071418090a0605041a2b0f0f050105100605091210060e060310060510030b0d0b0709060f02030403080403030e01051c0902090a0c020a02010f0e040e06061f020303041106090402070507 83
    0x144a452800000c0240460820048e03a0205007006c41583c209548010380d150000308612607164030001156000c04405110980343ca081070055080c001c050b2020761808000071120344a41c0152800d0310015151103040c000c0c2c410801140600202c107034043c5020b032611240b00d500b42406000b025244e8441c80e0020351070003e0030b1518024011040881c110705199040240da21341200514602006140c04544545403401082450800c040c00401180c0d60308100400d50782d21460320300a441c225034503821610319086040f40d80c0e0003603020141170160204800c00000740a404900d003080d0060402c2410207904d510380c150340281c0002c1005081d80c031a141541146403081c0c80651204143c0720802c0030f00305c5000000c3d5a29071041d0002d040c0620001d55031036440c000d82c0a098080b000500500141203484070b20780d200c8400f52003590140020040710110340b1000e01c0141100e03c6954000c6046503aaa29030004065440101c079400803030400111141d920b0b140004c0c01158000e200074181c0c545 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 161144973 1250 161143723 161143729
    0x501080307030e0901060e09062719090503120417040605070c0603021c0b030c03030c0c03120304030c110a0b040b0309061018051f0f061403071418090a0605 69
    0x2840400151040013841d0042c442e058101000c18240a400e5480001650342c45001c0780480b4400d030442c0e1003040404401a2074a0440c812403481400400f1074984098a180e5443e416112000e0008110b40c100788440e03034100d5240a51241d0182c059800799601020603406034005a01980140000580010710700040c844c41c0100301c8020b00303c92030118076241c09080c109080d40d041c0c600c0408201d803620400401ca541c104085c10744d070000141940d98598006c50110340d01c2042016090207809540d990801303803008034042e81d224581545500d041060983d031070b2602903142c07240099004180303890205007801503401a0001d000b04d0880f240d43c03402c2c9954118034160380109190703052001800103204049004201409600c0c0000b000304450b00c2c3c000c1100260105040500301c0c801040d440001c019032680c2840302100e01c00e4991065008a0030104034252100b26a504c1c00701d00a500c0404030f61113040c0050141110ba45040001d084040000501210f0244d0f54518400d45951040c0030510f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 161146223 1250 161144973 161144987
    0x81003020d05150106091a160210050913050f0c070f0503030403050703110109020f06130308030c0a3c05070c08070f0501030204030b06040203182a0108040b061002030c01050108030703 81
    0x11950741402c0848600c1c200d40e41d01140e400c0401341906540202303292111406075400000040c0e402001000207003d661001807040d001520101e210312450f541d0080a03500d40c1c440c50b402000e0308568030400e9600d41d0600c03545680645000c59010420410f2080411010710245000d14402d6550958455031418002c21281501a25000c1645818100c4005960b10342643d55050804e4800c2034442c000b68840001c125120f030f0014080070301c00000c02500e852020300030243c0c505a80c80f55000c0e2030304003001007a2280399841c0d42e10703038503004119000790050b030209540c410003e5140c030314545201540ca0303c01150203640300510710b50151a041c002c0420744203a02010b09020701e030442c145803860b00c1d000c504800182403240220740c0040480c840e04002900810191003c400f142c518800003498284500480384565080701290200c841d0150720640d03032140034940180101c56192110780411020b10b5032042107500f5444104030000c4e01542c20f02450703000784a100040c588406403400d000d0444 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 161147473 1250 161146223 161146229
    0xb010501170115030e030403050d030e03040609030f140118060606020307050a060e070f0f140603130201030e10090c05091602100c03060e0a02090a08060603070303081003020d051501 80
    0x100c4504094600500c42009200c1e046600203e50b045403015909019401081c4010040841d0300000501009005002031034a0401c0e01c031360b82c100401443c01902c1e68481c05071b8002c50000070143d06080011900902400550038020000704c54180031080310942164200c0041c800c0c489030412490003070140e2031007204002c041070b00156191204542d0386580301c61081d84020586640c9002c4800e19000030040400906480d10b0240000ea80700d040d031300120006489603103400c421007000342d951403c00b102900e01940140d604814480c800703600640103032000c1406903040d0312034000629410b44050081c1e0001d10300410580070700302e040c4006d200d00c1d141c005001901c24440340c07a03a1081c09030b00281410352801c410344c000a803d030500c0800c0303019000719400a15018919024007807050b1450f4010f101c503c104584502500da0340d808602e481c5c0100700e8200d80d00d034011a6040003c01e006103100d56200c400c5003041658540c0f25030001d03161803201201510654442160006028650341206000d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 161148723 1250 161147473 161147477
    0x40e04061e0c0c140a02030d050408010524102d0e090f0105090c0c03072003070f1202150703020607020f0105060a1502010f0c030e070f0506041217030906040b010501 73
    0x107802c62140000c0d02081c40e0040040c10014000782d0750071254024048892402e40c000c09032203612104d143d00a0041e08940100d03d41d651034100822003c80e0a651034007089a0f02c0f8a40240203541e007020031052080000d10442400030414441d0010400b244066480b14000741842500c080f02c050014010f0208043c44d50142e5856001d010306540350071565411110111540c0003c0c3d0366801c50a44580140c503003940b081e12012a03060200301f110220f040500b11100e0710310360007034034a40805980b05110710030442400c045540a02000045910041e54140064070b52844210584d81c03100c3c09030300111003a070041c1c008005001c00349906110441103104000000d0004c3d0030031000017041c1200c00d00c21040308682d801d0b4000d5103035000b03402c12560890143c1e030400c502c3c455900040d015051040941d00c0f540101d40f00441d01d40076081d60303841500d070080d09050606003080050803528115a505030f0754424290315460540503000000c501c95131900d00682640d0505181404081c00107801041c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 161149973 1250 161148723 161148731
    0x905030705060304080309071e1a121f05061309061706071b06020a0e0a050105120f041110030621050606130f2d0506010c080d02040e04061e 62
    0x452503950700c0c19aa0081e42105c1400c0d541e4a8001180f407504003140d01900c0580d01c682c001d0307801024000b0650003101c803140c001c1c04890059904640c003170301c502c00e9180e0704226140041102070303024409904401000c035041e40302041d12040000c030241c00800800c034070100740d035030180880344003802620001c0101010f400341c138800c7c400700c5e039880700c40c0200703004204804c0c07411500d000318030b4010306455240c001e8411565407113502401070140c0c0d04c10b0311550050040e0440082e042d4810002c07640c1344803550700710703c0c80354444141306201080003800c262010401d600092059503130302c0359006268102034500203007a900e010483e0445d06102d00c4a40d000d2200c00c181200401c00114200e81d00032411211030011440300354421006201d0300d0782d44180319141a5010b00024000c2c0201c40601c11b5041c0346500d200039030b84200058920403250a1300090030f5000a4002559990280441480040c005414181c0b80c0700c030800d42d55000c0b141982d03010748643e0303088106207451040c04044040220144 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 161151079 1106 161149973 161149979
    0x70b040b070b010b0a0f03180b0702030c010b040b0901050d0224040315090f02100c32010b21070f09020703020616080115050d1b09050307 61
    0x99900410300004140461900117981100c121559050807152074280100c005e0008040c020406905000c4140700040700740d003409105406640c020340e01c41b41c0092030b035070950310a010b109008518102007000300f51901000c00341903410031b840d52001c0405c2480850014940315864900e52070340405c1c1e000721802e401004104582c000d903070f04040501c05170504401c9403580b660003003021059010240c014204500b20880403095070429100603103154450314440307040e0f485440c410b0383d10780030b0b4140e40c6548103991f40c2400200d00000c0101c01d903200c000c82c021610310003a07040d1440014441140710541002404054200e00c58551100303591181003001a420240d4100e02501030f030310001e0769040e466200e42e11502203550756072100340d1a20004100b8001040c0034082084010801440625420f0043c031900c1c035101002c0341e000070420000100300002540090784250441c1d2410 = true := by decide +kernel

theorem cover : BRFrame.Cov 160971223 161151079 := by
  have h0 := BRFrame.cov_init 160971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 160971223 ≤ n) (h2 : n < 161151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
