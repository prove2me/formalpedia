-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0083
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:44:40.218507+00:00
-- url     : https://prove2.me/submissions/dfc82148-15d0-43e3-b57c-2a64f8dc2886

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 14748208 ≤ n < 14928064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 14749458 1250 14748208 14748229
    0x601050f0a03090b0a0c0f030b010504060e0102030c151603060312030209061e1206100905010f05130b07140610140a0305030a11010506030a0c05270a020405090c090f 73
    0x20b02d0001450440fa4031400d01c80c0200381d50700080b203a580c00e807449560b90301c8642c0b6004100c00e400c040c02924048800200284150707c182e5041008064984c07010760710074000c460fa40d00c0743d4011210b001590f08080355047d8800d40b502c00403800350f180031005403070281c0074440480390403501035056184c80d418250081e501018481d503000710204214000e0300c01e0312070403003c0d0011800444d51500d603001d040c40d0301d40a010700000d01c20030300c0903800551254403a5050b41624000e10b0511507201b031040c4262080e02031f4003006800691202d00100341c4511301d001a0200c0c0d8016500c0310f40c681540d07035285844a400b030761b210900200806c0240028101c2c04283c041c0c42c0d6014140d409160303565120103040d504480b002d079002904545000301d1005090041300c2d04002c04901030300d10002e06594022460855210709070040d4490f080701c07400180342480c03542003100c00b00c4840040d031820780f80a8000354014001c8620a542c00380c081000e070825181501e0800002505440001c1481c504001840c5403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 14750708 1250 14749458 14749477
    0xd09081b040b0d030903120504030206090111011112040b0109060b030c0708040306020409050609090309010c0f020301060305060115090609060504120213020d090203010b060910050a02070806010b0408010c03050601050f 96
    0x201e4102ea02150344031040300405541c06a038070b48a8143c00c62400d8981001510107031001c0140c184018005640c42c041281c120b4a03090811864010fa154840360140c10100758000d2003074400300d08910103402070450030744564411500c40140d81c0c2c985150104680e02da010303070880c0306028400910701c810404010112140178032066401d2980d6030741d540c4140d074440d400030610340d5156814090b203418803600c502c2d0090f8110b00554100035040300000d041c15107100000e044508000068415900c003903106102440c2c000c0169003d41d80c4841100b2003050702d0102c01c03800a00510000103400344039082c050709403030003555146d1900e03161012146006000c40c5007031f80e115540c001c80f014003045510050620714401d01c1c01048805160040601311091041100d01501003084403540700d035034520445c214003815041c5280c07518018401245000200e4119211900c6510004551070f420b002c050070480340020b00900541c510828100c4c251842541ca15012441c2400038120807a04030b00500707060603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 14751958 1250 14750708 14750711
    0x10617030403031b12030605011b1104020d0902090103030306030210050a020c09090102130603060f05090402060702040203180102030106031406180c0a12060b0a0f08010608010e04140a03020f0d09081b04 89
    0x29029151505691400714600006c82d560b0801040b1039600640c079039156695503000c0386021280c0c0d0300e0703001a02401301e41c5c1d94840c540c000b6840da8881816030001032095006090034200750f860789070180083c1044d01080c3d02c1901025104a50144547d044407003c000590142600305007540910003003880103094501c00b55028403c00c8a07004014000100422013a0f034045486441d001600700c2d05912038002c00c1c01005824100005a00d50300e04036150781b5419100160b51b681c460140c0031018400041d100b050794000000001c4040d490341050890407a00d0541646640304d20b03082040152540c07440322070344441840058103400a40010341466202c45c10f000c5010f04107846940c048801580203a01ea070040842c100501e02e42c00f9029081034603903400c0028003541401d001038405c440510540d0429111840002c080201640c00920704104c413400f26200c0300c0342850040d498441038200c4d117480384105003d484060344074083c400c00f00e805090140500c80390461004001d041c0b118030890300903 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 14753208 1250 14751958 14752007
    0x40e04030c0501020711090a02040f1715010e04020a0b07021003050901060f0303110609030301180f110703030b0411030106120b030c061222080a050d27020301061703040303 76
    0x2c80038001041201c0c81582985c01d454404410041800f0025040d600000d205000c14802040c1801410066484588400f000101d0507010300f4030344800f50202d0003031074508400002c0d400c1141800d95000d41e00c200d0b6441411034903540e84518a005010002e980940c2442040c200c00c1c0c06640010b070050064000031449130386940309013401c4901580200d0000749180421031a40000b0b104041e0811041310140d480d40d454880e408000545001c041c925295454010b20117840c41da0b4041c41c81d8a0900c40640d07150945810041e00421111081e140590b0504900b019050105004c0324165080342d00c5080103940340d071554400404010f034900c1d0b010b00c80c5a240c00480c0c0e6425024021242c0c8080541c0e001e4030b0200c07070700000c801811f0302c03a015061001043c0da0000e0012070a0f2160b4031b2071031525a86464588054034003404142c0f0131921106c8800141103401005c2421076140c481c0254002d10220f580d81d0000070003101500c07400c0790b19400030300041c000284164102c0c2141ca03145c00e04030300310 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 14754458 1250 14753208 14753213
    0x70609050601120204050a0c020a1b030c0608011503060302090c0c10090803060102100b010516050c09010306060f0e0c030402040b030f0d0306030309060c02031513080d0501060206010f0b040e04030c 87
    0x103001d001e0b000710f44007408207510402107151502a0300c4e03101001407014000119081006540c40c001048014003c20328100050301605124042800a54018451990b41d540d5004060680318003030040d082d0300c41c04104003107c3e00d40280070340700840f07502400c200301d940d5805c038940302c85400461022035180500d144a8184032041d00403511118001e243c4c403652030a010001a16090044000c10845030900031012a1aa000f03025211680c00c000204501d500f0340e0f2038900d0a1102c21519164001d010360004401c1c04540d500c03030b0003074810b01c6003d1000b00c0e07190300ea42004140100c0d829001c0301070420001d401070415821a0021590140403541c50707070404105c4a041205412400e00082d0f43d0b2102002816407013124030000b000503050095031800150040381d11207102032290800303d0540c0e0b0100e0701d4a1003807146910004d800403485500c5140305002e15028001c28461500140700b420700210380c25080f40c3c6c09404594900d10242e2a003490810f00d4820a040100250248a44002810003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 14755708 1250 14754458 14754463
    0xc090302130f0b03190b04020109090e0705040e01060b040306020c0a08040608090607090506180307080a06050108060609090307120504030206040b030a06060806100305040c050409050609010c1d0607060905 90
    0x40e01e4104980c003007691200c00c2c05000071911040351582c426804103505a910040c84e4210030000c030b40042c21400c0740c0d659400141c40c085042e03888040ca0034580382c04803222680105403d82954802ca0f02031019120b00c048075800e9400030b0281d400030040c10001000003071616401029981d035a40c0685000840381d442d1526541c10a0b03002e800401d034001c0412892010a01031182c1c446028100100480c0c2050080b510074001c002801400003258080344030b440e5010004800201580b004941d1801d0702468440f000d00130a118104c4c1901c01d00c0c002c50014600180401e1041c2c7e048002141000010f88920100080e0703003040ea004c0c828100000300150b140d0a0082c0094408000020b5923800c0c1101c400089400329403141c0104080301c402e1102030398652031354903985030603454046110f440d04e003400b11400d185580b0a90340a0b04d050800741c10014041166441200c80d074008010140700101e0a480f03051040c414103200074003007441c4264910f0a400a021074500407900044c1e8450150307600361 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 14756958 1250 14755708 14755729
    0x10813050f030304060c08040c0504020903010b040608010c0801050a0e0403050d1b0905010206090a0c121e0c05011d0d080307031b021b01170a020307050708031e060907120c090302 79
    0x8102d420000c00c1100707000c058020040d0070a5a441d0501d014a45030b21180c00307400340c50207014420350700002e60000581d000d410844941030014000c0168654400e80780b4003c02d0011816000b10760080000103a0f45400d0545500311180c0e00d0481e078060796159022a40d0354008800300391400c1d500c4101d0550060600d40c19003142c1043e4843c40d007500c1c1000c0c000392400000400d10341c000d0b40310062100005001c3c1c402001160040c0024011007080c92918042c0c2c0075480041b50880882c0c01500420700607400c0e40702c03007110300030f886001241c4044240384141d01c0c0d42a0b11181c1240000f0301c400c0015003000011948540f40d441c0001d100004640403141c2c00d84401c4808005900c8800c2d03a504500c2803410102c0d06006c2400c003952408c48a031240003201030b00910000c441640400000c0c2c03c140208100e410181e0b01c50003031981d03440c04507005040249800710000f524648100051420b00785250441e0140a0540701d5507500c842203240e800c0a0a41c0c403000ca030422501c40310010058503080c4210 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 14758208 1250 14756958 14756983
    0x1c0507050a050313150207030201050c0109060203130209010515072306040f05070503030a09050d1e0506010806011d0f0606090607060506090a090309090f0207080c030c011b0e01081305 81
    0x79503948150b18282c4c41050005c0e000101118000c041d01e034440c540000c4e0f02000c51390b0a0170070944542c12034903141d006102d004809000d881c000010484a440d0a81e0079070016403003200d03038199590f00c890a000c00010307641145031740c9420810506000c1403a14548070000301c90142d0a10240da01000c1d043e0030300006171000c07110242c001070a1420003000748242000b5000c10781c000d509080442d640249030161a00c07915000c1c1851491450510403130b428401402403041c080403031030002d0b40c5043c40d580e0000b4411100b143c010030300041a07005c101c1603e00c0c000c0e82c091000d41c01640307403510451164540130b0f10f05548020100402845074a0f00300190864502906e0700140724903044013800040540103040c035062624084170400080e41001c10042500e00f2488006510151180900c0080c41915000b91442b50041980c1100040000041004041150090101c00480400025500c6a500414000c01c409500c004070b1940b0495405a115010700c000410102e801d8a61609208203840710 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 14759458 1250 14758208 14758213
    0x30303090c05091009050912131a0f07110d0b0c041706010f06120b040216050c0109080d030f0f020d050103021c0308010509070309060501060905040b06030402031c0507050a05 77
    0x90080c012060345a0000700400c2d1201c004070316004a0f101130341c07034050054040e142d0341d910100d1500041000014500b1032100415a5501d40481c00312464940d18841e0b05828000280f007010302402401c01d0740c2d2500300903070710a420540b00c3c0e5200c11003030088590068000f540341c20100d0106000d500200d000d801c500403041d40c2c560070284606030300400030b0243c60044c0c0c00800100701504004206404545861030415452440441050041c088076000c4590050022a40124510032040035800203482241190440303420310005450201041c814849075411583c070f404803990080d0000203284011100002d913140381d60941c0310490704803c000141c0036503118018800c605206c034440c3c01c01c0409261142c65100203560080411105006440c0142e800c400410b4100d4040e40214070f0305540000140030642c0c480400030280036061045612480c24407096032800c1c00c1c060122405190081c025009680c4071450460f0b000600c05408002c0090030089080030503002d11031410502e01c654003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 14760708 1250 14759458 14759471
    0x1050106081006051903050603120310150219030e01050f030406090c1d041704030503030f0603010b0609090a090309030b010605030403020114060d12030f060b0403020316030314070602070606030303 87
    0xe0340c6501c40c0c480d00f01c40b003400004c020086850360080c62001400ea89403134081220b95030400070905002441031029034048012040c042c84c54228911001501c0044040f00d803003144a1004aa45d13450071142060004101884100800d05ca03890040300d020042c10594075240aa011098407544100e609480807a0340e0301300d0b4000c1000040d813210090500000361100e001100c00b403802c1000000d03100802c0e10303070348030b1000210140741d9054500640d000802d40b502c900d842d070543c0d200385c80b013280d001d8802c0d441d140e089071702071800806440300c41c0805814040d403552549814001003145400c294280032141d00000300240c030f10b1481e030f4040e040540d0703250348a040c00c5c034019007510318412102544901030b00411032103840d084030700c424542c0c00c40f101d0606000c10720340c10b800409125028044503401c2c5480454051b850400400c04c50f40300380c0444103d01711582e4900720f1014240401000619008031301ea041907544001f900c03045018000051070041c10355101012038406520032008070f511840e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 14761958 1250 14760708 14760721
    0x80a0c0201060b1c0c0f120209010e040906020a020f03040614091201020a0c03080a050606070206030a1401062a030f0f02070e040b01031b0501020607030c030b030a0b040b010609050a090b030c030105010608 90
    0x210030040301c003410046d148410f01100907003d0301160070407011441d8007141002031a80321741d079a40441d00f0090020071200f00c3c1410650046d40c460032120004d849400c501ea0064500041140e007200e070580c2d18080414202c45040300c0d02e50107021503645c8405074840c0302011010078401404002010388509454000394540508441e00042011701c61501e050100a116210b8004954035650704850350381d6a076888140c44802171010b03080c0c003c40c402d0030b8400802e1094000c030030503000303001d0704036015408110210f103820703140c107640c0d40100040c014100701210940607103440e284d00d107082c0c016684240d480d5146046022801c0b40c00742e5040360458010400d00628803100401c3c03000906004e8000c40c20070300040d40d1010060031035000c0541e039000c4680440d20170752044034481c2d4024107482c005a10380c184550702660544094455407190000020420b008030150021030302c0103807008a0b52031404000301c000f0042c41a00b6501400b41c81c1c401c45a82d9400c0c03042d14040c00090310360325420309118 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 14763208 1250 14761958 14761961
    0xc01050f0702070501020a02010f0c150507020111030c091219030f031d060103110a03240b0603040f02010c080d020c07030302010c05040602030d181a16030903080a0c0201060b1c 78
    0x1078910780541d0048401482140d0b4041441840c554080c24425900c1074000740484ad0103254803406061012000405403332034070705400241c00744207258020320800d0582c000001d23080c8401d035500e00e0005400c0003440b40c5801c0001200307805002d19825601105045007a40320f0740a9050012000a5201c40710301080b86c0e014480d175045002c01041c0d80800302d06100006507240010300020b081d00c0c4000c1b000b4810360ba40d01d9440c2028640c403400000c0c0d03a40d50007101c1c003100d01000c6481e0b241ca504241d1242c0b803505002040d01e05c56500304010308465840c680064810402035281a00c50000411146a107000a40010440b05544200801e00c56285080090031600180d8620302003280421003040900e6000081d03a02c1414048400075404008160010405a4604000707140e00500b01070000c840003460117031171180c4da0400d440b415110440c04104c04850000c0c400601107501c0300046031006241e0390110000451600002808548074903050b01307a604170084c1c40c5407008580400b07900145c281e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 14764458 1250 14763208 14763211
    0x30403020913080703030e01020c070b070c05011103030f0a090209070e010e0105040803090405061306060c0308060f06070f030e0a0f03050f0f0606011b08040603020403061a031c140c01050f 83
    0x150b03049001024065643e0106034860b0803c003504050f02d48858852084007075041703d0b04800550304540c3c134a039403400900d0b02c50f000014240c9118402480018040d40102144052002c4440255241d0760301c141f04034803406409010200e03004e40c0c0c0d07100d81c00140c50311070009010703100070340311443c4001e110400180317030382c2400310700e40d04029007071200f08003400d00002030383c0607882d00700d038007040555500011036000756406040c2d1406609082c40000d03a9a0045503840341c60b03000fa034842142d9500d41d0140a41d0381100d954490300300030708118200105003030584800c8981d20900d4528108600d1400203051600d058020b010900400d1201300108842040020019250712000d03000c815003003024280c032900c000b4045414490020800303516000c0120b03282d150b0380d50182207244c5842d05c81d11f0081c000c1d08940411a045880d000b0b550300c2d500342911940658000c01402070400d8900c800040110552030040030045c014804108000d550711800605523595011000096510380361505000c090130 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 14765708 1250 14764458 14764471
    0x5030609010c05030a1d0102120105090703090c0603050402010509040c080106111b010521010b030709060302070b0c090609030a0506090706170c0315030a030905100516060b040e0303090304030209 86
    0x2601040b06600c0c0c0e0004152644800030780000500e2400b030092010f40d0244014240c6541d5100196214002800c600594140c5400341c902c000c0da50b66898040d011a412900040c05800846008001142c86034000c00d40c031070700c10b1601c00d007081c2c07000011a013a11340c0c008034000440c803c40018451039520501c4070030300641100041c02d42d00d40c3c1da81130030076030888040583c1c10800700143c40f00d030301030101c00b65680a201d05401e2040540e13582200394025001941d440b00004c22001000403064868020f403121150082a10912038481745010000c2d0b40c840e20800350000d0080c010103105071740a100004d2210300031000352003203180c225000360400c805500308030248800342100030755510070056501d0f0b00917907580184d0ba80391102b040031407141301f1188055074940b148803800d00416a20071065021101c040e80c1d0090580710040040c0d956000e05446654100b01d90b46089000c5030040d001610340178400380000605400401010b8115441100c0384400c50380005000c204505000901360390040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 14766958 1250 14765708 14765711
    0x30602090604030f0b0f1b0904050c0c0a05010603030e01080f07080615220504020307080705070201021006080c010201050a020a1d0a03050a0b0f250503041a070c030909020f040611070b03010f0503060901 89
    0x4c1f19100c401601d0f010301d1000e20b0146640c0c1c1c0c0002d804400da4401c5400c0d10925008841c0849840d00c1c0c6070b400382446000841c0040d0303c420100402d94082e0000034020030100e4205a240e6981c410704640707000700100b5150340104c42004a022030f01e018002031003000c03000100440007444003c80d00100c4000d9500a60140c0e10410400442c10743c050026074100c1c401c1d1604565401550004038039001142e0b01191185141c05400500524006010001c400083c0c000344041d40d1051400030490040d00d02c0c0d0408185c50703141c11080205c10b02c00b205603601c0020058500503450307844061520100a008640045421003488404880103a41c2540202d502e204010b21540b801007034105018003442143c207100010001c1020403030030b0720f090255042d091001d2407451925030030040405101c10f000342c0100310740740400b0078821881c0c001c54826140c0c50709540d1070107141c4a000c4481c801450640d113090f001d9154003040c2c40c907102c0011402841516080c40e142404c042c2010f081042c0a407284445a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 14768208 1250 14766958 14766991
    0x5090705060306011202040f09090b06010306080705060703020304080304090504050708062205031c02220b040312051204031d060313140304080303161b030207030602090604030f0b0f 80
    0x80e90780c8001c0360760080c802e00e413001132002d07001202c8003e17000b95040b06105503100c080200f07072802c01e80e201009080c09010500e58603180c030310040d41241c515024039042500011020301c6942451002000154402c1c03040300d04d080d0361a028142960895041004002d464a06201c1400020443c1c2d00103072203200b0190466082c4500c0400c0147e00004041e150460302134003203401c1c04003d00c00d0b07035a5400c51002d0090350041d80c02e0440029030002140e045031180e540900c01802c0e403541c0340c150682d002d030380000d8941f50450311084032002680c08080d007086808c102c1c841412041f01c070384a016a100303480d55980028071200400100021032640c13401110180708001c0800d80341612038201a17003109011440c0b0704003050050039807140c3d400101c0248000000e0003492110745040e442601020765a0425614822907001c01c0c2e55841e01010b00181c0c0039200c10700202398158000c101c02d81c001005685092b41d00c1d582c203800c90350100c42c00c2c0c070907410700020010724500b6400140d90000d042c10440800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 14769458 1250 14768208 14768219
    0x60905030d0801090b060c0a060b1c030801090b030102091504050a140102031b030c0a110405010e0606120603160603020309060601020c030a061a091003050106080102070201080604050403020c060a05090103050907 93
    0x2e98a05100701980181c8601c000c4126480302c42c00c407441d4510400c1968000c0f1a5400c000002c0e0140d0a076050203030800f201e81d1300d02c101700900e113095010b40c103640c3ca81069180500c807001902d440980c4940c9075500f0402c0801c03039603c2c50909024808841e150035165450001081040b400d16408441503510b21203968545a030301204442076032500c00a0151341c8042c0402aa103075000d2100d07266031074468041d200e028002005200e40c0c22000842c0c060205a884c0c0740c924907000c0050b038046411030030501c5024200030904009580c00103026040b80e1441c0d1240d10f25200c0c080d01c5030300200c04207900106104900d00b042c09582d034011004c0c0010b012984001020a035507003031f007280c058203265460806504486d4004148654224001c0980040d81400003590016a51900c012150f82d0f01c1c0010000d1701c900180203480d0004d40585514145035202c0007800041e00d4020011070443c020365129804a0b51800003520048040ea82c800da00d44c812880007604a6402a05a10b019441820100030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 14770708 1250 14769458 14769467
    0x8040212070807030627080d0f0507090807120503040302010c05010213060e0f030601061e021c05090310050f040204050601030e0d03020a14070807081605010603080304020103050f06090105150f03010e01060905030d 94
    0x6d805034001c076140d540d2034042c1541070040c658020b0740007034a8104010301811590001e600016240c101c01034440312a95a031441240c40e06408000301240c009200410240d070155010a564038010000580b0342000f410b1032040c240066002640403030381850341d003001c42c01c0031300d90018044005e90040c50f10354189003026100c4100781180c415400c400011110080f4402d00000c0e803a54001c0f80c032016203840361301000d4a20703049800c0f440d0092061030314040c0320045500a0700c0c003c42c0303414001d61498845809000140c4002400f40341030588820212100c03180412640d851000c20340e80058031040003100c0203110107c0740c2d0108140c406c01707112400c00304440104035100b155014603410b075510421a5203814490004802a00c154a088800004c0c050400011031246100340e0701080641d8900c03c42e0000718900340e6403260002c20b04030051009040801c2a003144186450341d090800c07007002c1c4410001c1c0e10982040e0200c81c4c01100401407207820000340d40c05060100c000d094400c0c1c0c40d882c000e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 14771958 1250 14770708 14770781
    0x1061404091a1008010608030a030c0813060207022b020a05060c0615030a08040605180103020301030809040e0c1207050405180a0b0408040905090d020601080c01050406080402120708070306 83
    0x1980121031004141c4203c103000007000180b440c10001e0103c550307114811074594000003103200c0407a050500c000c007c18400c007040b61140440040c00020618142c03100002034206842c01c0f030700582600c0780c14440200203180303401a00700c00080e00703404892a205009403030f012540320f98041c200603c201e03425000c000c601a68012000e445030b540030701c0b034600003030305d84052500080c00c1120009004112241e01c90028019480341481c0205034220030001101284005d200140c003104082c4040c0e0b205213025046004490314a10443c1e40400e040b20004446001d90038540e02144c0c4505000c0101e4101783c041d1980c8989500d030300c07810521066101d66141ca40c1001c4c0200380e0800500010100080b01040c2c0c3c0c0035040b441820081032030f210341142da031400c3c0880304001510a49000081c20100050f00050440040c1d44080c1000d01d800b10a64007001c0c040e0040341d01c0716405040e00c14424040002100501520009211562460912404642d0901a02c0380c549e140c0d003803810580e400003804c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 14773208 1250 14771958 14771993
    0x9031005070c020607020609090103080304060e0a1101080a0608070603090b1614070606080307110f0d0507090f020910020d09060905030601030210020a0605040b1e0103050c040908040b07050106140409 88
    0x35942e2a1103100081e22072107a0410b84e03500100d49c60000c018840780001440c0306c1e03480f8200802200302d40c49005942d550003504001c201d44012004000a940700d0a69280c10a000440100701961070320300b02410103529400040000b80d58030119400d1094282005800c4824070031609407108170b81030000d000c5a9525a1008031040005221003042000d07071200b4020701915040d41e4440d00c10f4981f845607030f0b108000031407050580f416007051908e440c0b25055007081c5e03c80c00401c0f03458071b00410b0301c001c2e152141c10032104035424080d0100d25111240c482c440010958040e0041600c0201d014040803001c0d00104104010b2420a12280e1800903205064940403560350303007504e1409504034030340360300d0010040c01d1500341024002044806481c0c14010b50710002421940540000c4c0d1201c800380901c40507013240e0000f031400000c2d04090307000c000700314003900300760349082c1e182c010076a0503a0003a401214269914682081005a41044100036100480d8140190b440f0740e2500785960340343c544603 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 14774458 1250 14773208 14773219
    0x706050a0203040b0301061706060909040212010b0a030b09010606020604030e010507020f130c0305090a020108041106070b01060203030702010609110703030f0b0a0b0309010c030c0f0e0d06050a0209031005070c02 93
    0x65005240c020000e036401003134140d401660b00d60b1900c100911040301100d895580007951400b00307540349440c8041d28098400940907035a42d0b510ba03020800f00b4000051500c03260b5695081e42c02c0c603501c400d010131025500400c0b01030194244035150b90300311020395118604541200c4207000000b07900c6030784469805004d00e011501e80340d0500000361000ca00700646030340b0050b1815241750b028019003041c0740c0000a600c0c200308070754550220f2070b2520209500280040c240c40c0004000500880c4901c40b0680c024141c1030600010350344080b0b00003020303000b4801582c4044204110700794240590f07409416005410300c602103903408039841c02e0041b9400103041c5a06c0b1000495290301c154004840118010301d4510b0040ea60b50100ca1544c0c001d07945117003c6e50034082c041c62010700900903001c5421059035084000c0b04440c2c0121400500e090707201d9071200d01c0210000100740b07140120360081031000801a42c84200504151520076410f8000740e4542c01c00c41001aa103811000380d030099034060b41d9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 14775708 1250 14774458 14774467
    0x3060a0213050402030a0f0605091b0708040e09060901060b070206070b060d05101a09040c050d08090303030a050906060307030309050f01050d0c080106140c030313050a0b07020d02010606030203010503070605 91
    0x240724600340481c0c0c0007a5042071011081101a03d07082d0814007a0904111041192a44440030302241c00400c03100c0c0c405d81d0031642101601608150000d10700a8020b000300340c1820307210f814508961130141c80c000803660110045c04001c40080c8200c000400660480724908019540480c40314080d10801612103603001000a109450300040790320021340c084151840f0300804488003009007031408214042019980c00441d41d41040002c0e9130003a0b41142d01e0b82d440c1e61038001084101d6940f1001112203681c280701e40161038804201940c018a26108041943d00d0f040074101c3c80d00000030a120712990240e2400c0021030341104015040d1001074503019480c074103c00050314648154070520105070b2415040d0300c007055000e50300c64160740d615a600900d03910704407002c0360030b40140441901c0c02d41040000c202c8168410f20ba01c0340c02c0b40b207002035a0580026407909490440e00300d64000150700030240d2010031541c20711848000d000c03e42001c6040d54100400b082e5515081d000310010f002c0e0019 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 14776958 1250 14775708 14775727
    0x30e09150d061d010204140420030a05070806010f09030605060a08030301030c05100212120402040b03060f010302090a0207030c080c0f03040f150801030807030e0a170105040209090a0203060a02 85
    0x54181420040151240455055614109009002032010843c64a1200303150482e10b01040c0221002c8038030514070303443d201e10034804101c0106210a14158003024101112680125890146119504e0450001142d1904034406401c0303020041506040001400501118030b40000a5030240d81e000b810003d8a65034010200b03041030000c0e042562103102c0440008200100403101500f65042034814640a024402060740e480b000003a003612191414002d440c1d513400c180c0300d03040d4000c0c0000e2010074440000404a800c1110071703148001c400c9401001401541171070804943c0240040504500d00462a10000d241d5400490001c0040000180101c3c03d50001c22010440800b00c03030a41b40d5880d40d8504600c1000114400c0b1910f4048100c00103c40034000c2d1261f6040b290080b984516204c010783c0e044540c1071710b000580d94406201c01d4080303207404400803021012800c00c8000140303424507004101110300010400605c80c1d0080d848600140c401013110b0b45c12808100025886ea4100c0703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 14778208 1250 14776958 14776981
    0xc040513060f060909061a060405031b06070f03030e0705011b0b04050f010606110601080d2f06010602070e010e0709050913050105040c0302190b03010b07170f04080706020a030e09 79
    0x4d82c000860b05003840d0304281401110f07403000c0e801e20703420402100102100418002e0900503846290341c10b8205082c80c0705900c2544400c620381c0390303004142c240b034407945130b6078081c82e42d4414030144c0009a690322640001c1c0030801940000c3c0c002403c0203c0c064600464000d01550380010042c03200c2d500c00c0105d0200542045603050700c040b102e00901c101a10f078440280001014540740c0c12500c500300c00050500c1020400c101803007915914060703410050b0f16140c84007002070400000d01050031044015080b002e1000e036000c1c0600340c1c094040c061825075148000181038000800034020b94061205c0c59030010f003c0c200f1680f0503194000345079100d1200c0600041140406082c0d07500f880308200402c02c4801c091400e89108440d084000b6045d00b10b00c585000040c0950042c001d0100f0041c0481c50700c0340c001c0c15100313100e48070401685030a83c0d0419801d8010764184441c2003000705060103005000e10400b400340c00a440181200655034030000c00008000b1501e03070051869402248608807803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 14779458 1250 14778208 14778221
    0xd0c120e03070909290c04140d0209041101030b040608251706070809030901020d0e0d0c09060302040b10020303010303030209121504060c11060415020c0f030403050c040513060f 78
    0x54041002400c2035810303d002d080301d200d56081000503481c8110340401385050f10190246c518801c0c40f0b800c003400c0094541c04070100fa80684d0b40801408004001642c91440d800e1090b40b0030402201709440d440c0024040c2c5005a003802d100d2030900d0703c02d2000c0c0c1c0e80046c0e00d08540d0070f980c0041812032201810f001440209070486226100640c0c000c4100640c0022061b001d0500c035034a40030300b42c1e20601e060f40c0340c3c00349181207401a006045981d140a215600041704004000e003800790b90700e4a03a880e082c0e03400c55a40142d14a07522040100254079161150101c07031401620301c104844803006009490b84070501008090503408100703107c881e1916952035401e40491012a04c0740c9240190007000f42d001201d0031241c95040414811405208620100070f40c49650020011034940d5503e0b200084051070882d90403580c24021f1081000f010042041103001c40d4008c0d590f00c40c15410203a08007006d880310b840c055405c0c0002d0103803e800200080c1d00d034580001002401074404401d00001c0c121 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 14780708 1250 14779458 14779469
    0x6090d020405160e061e0d060510030507021608060a05040219120210020102040e07080901020702090906040b09010b0105041703070b040b01060206070206010b0712020a06020307031a040605090f0405010603150204080d0c120e0307 100
    0x30b480c43c400ac04a0b015030005001d5115502190140d2042c60403c100740303105405002040c0d040900480c2c0960700681103190480d02c02001145801011182c88a2446040d44214104c0d80400d04410560600590748003000c40075100a40c549814451103640010016011004120803400042e070300b0030782941540c640341d9004121608605250448566a04090743e00b44c0708400c903d000703d082284144681d0301c1082c41a12403500f45450302c40f0b01442090b15200111007030104102490000c2d5114445500c514400c0da0455159418103000038941200103101905651080006100701c4c0100d41c1503400103039000000c0d800607002c280c001c90030500c1e881c1d4020007403400032050040c241d8142d0005009031208940411401d0645003c110540780b0310b129190b0819481000325410401c00300070698018000e0f000401c440d5900c1c0d41e01001500e40c8004021159800f0a051000c140c051003104550300e130f2403a00d125940c003103454810841001d80709000500911084a003c01d480c10300100000b0039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 14781958 1250 14780708 14780719
    0x11120c030a080406020d0309120c020105040305030a0c0b090312040f0201051909050102011109090403030203040f0b0403030219030902010e130e01020c070305070b04030b0606090d020405160e061e0d0605 89
    0x22618102c4881d0f001405504058042c105142071024444d204010400ea001082441790000e03540c81a5040129000d081e410441c00b0030010000c0f410820081070409460341c1c80100c03400d25070a1071034000c0c0300a0454000c03500700700300c02e07a00c0c0c0c0450031a5941080d008500000c124640d480140c440388100c84040e03c01c86034540d08895408e420425640445500f03800038000300c40c001c140d41c00c90707100d841052503108001101007008203200360302131540142f00c1e01550b89180b101e500c41e26070040c01180e045001940019129841e603031400402c1d002e1b07081c00c2c01d09018007585903002071701c00f100c814461400707050841c65078200309500b0f81103010840345003002155101030403101a40c0b81e01081c00156803d10407140001a00480cbc041209c003240d821040c138454940b5000200f080c07a80c403c241490b407000c4078140400150340c4502c280c1313005690041c500b03614080d803808c01078407003050000f00d28403030103007800702805101d00000251000020b802c80c0c03581e10036500030540020209078000d0707074000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 14783208 1250 14781958 14781973
    0x518070501210c110f151609050a03060f06140904020f0a1703090420030c07060b061204060c080903180a0b040f03030e0915040f0b13020406090b0711120c03 69
    0x195003019504400d0002d43c0c041c5d03205101a01145942c8026000455984250076400035049400c8000840305208480c03900c5000c181d075400c0094040c060b00e400a41c1c4060ba14840049144054480c06000f4243c40145548880c0004002144982d005201038043c5000a00165295035600c22070030160600c000c0c000e91861035914500e603290088100b190140307140490f0864007007001c0d1a0f111000d80601e882914543d2000d14042007504807110441d401c94907222003100b2541c0700381c0a003140e0400001858414582400c0c4031055030b40b41001c8500707000706d0f0340602c0040400441256900b0030b1203440b20740000360440205071595000e03480018051004180482e04c19207045403481240d01a03500d03900800d80780801c02100107030903107100e14194040b24801043e402c25402c207234003d0704131010005a0112010100b800c002c5e401d00d20b034481d01e50000d401c0c480d0a412644100103000c003074502d00d0500019076600200ba4111001040c401d00e44170130400751444c0d04010300c0104520280a48001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 14784458 1250 14783208 14783231
    0xb0d15060c0614040b0103030c030c1502071a040302031b030c07090203040302060702070e04060509011506050d0e01060506071b090207030c0201080105010206040f0b09070b0705070306051807050121 87
    0x503401960710484500381800c0da40001030040c441a2405540c1001024119900c3c580d4291220707039240d8011030030f11611036031907030115010758010a50406a100e0160307076140e00c0c0c5002040c5145a114030030412201d0400e21000c80c5e400016070b4422440d43d10b9410074060860202c9184d40580f00e20b20030680310760300c2c010400701e070580c002d180140d01c40c2e000c41c1d02980b036084040c0d8607880c03a030184c0030049d1594000140850b03215081a90805048030002030751502a014120840301d242c1c1042001c50700028180c0107a05117841203401203403110000300405800c086c00035102e0703c02c00801600c0300241c90340007088140d0003101c0e0801409014401c6641d001507140180090881306800c0c2e011416041c00090316500104040340f05503400300c45c10b50031151560f5203001c07803c00603014205500c80c2c40d00100f11f002c1c6078001002224003801c01041d6080c610b01d403c1040d100d0040600d01e034064070001c0322807a0074000610700162082400d11511136850303a03009070021450882c03001c85c6a0f041c80c1e0b84054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 14785708 1250 14784458 14784467
    0x6020408100b03070303020c04090c05090907060f020f070504020706060f0306090b0708010b0703181e1a19210603060b01020105010506030c0a030b06090301050903041e0f0b0d1506 79
    0x8041c0005005001142105040603140c60181c0f0000d00540c018035180c20503440d19901440016100303074441c3c000c183e2610302099031201c0031140c0c94000d9110403014005180c0040740807907420003038802072650b101c00070480307a1100054401c0310f001d55000b01c0c01104001c540d8001074080c00020740f44005855403030078134030301514242c8011781c1d01d80d031418017183d81c0500c6642818142c0d0700c8807504a01c0c001040d40d0883d0810b48205a078440d06004200200c0c9602c506180e240c10550f903580842c215609200d400914031902002005184c0c800f00100101030305c41c2d41c0922484c1d449820a40c00d604101511148102c1681c0359401100c0d290440120400055a100ba40d0404080e4001c001d10303038861091003054402500c40340c4a1007014015049240d00c01e80046c0703408440507088604000054021900b0348006441c1c4900c00d81001c03e09000c00c084100e00c3c541400b0542c007800084614151884006000c00d01031080f42140c001040ca0300154181c00c8026800082c5810710000c0d03540344401403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 14786958 1250 14785708 14785723
    0x608130b07120c0c02090606070f060609020a020708060601020607080411030102030705071b061b080409021602120c06040902030903070210080115031e0903170f07090b19030e0a06020408 82
    0x1203903280f50655841c1c43d02d200321030900c000c3d80d01409013a890b482d401c082088940020000b01c0710781d11042c0b54500021a41c1c0a035038014070500c800981c4681140d075001e0304003406a000110305612000401189a1307001503070741c0d040501410000c00c143c656041c4000010700c4030003100c0d0158000001d01144981c814014035400340101310025070201100d13501440b02d002d0344122400200c171400b4882c08038100d02c03000c0c50351600c24041c076407805035178441000c00d0741c00c0049030700488240740c8000410750400083c1601010504c1c0050900710525000050b141d0185000d440190399003c00010f0140b07404008480040350002c1c00602c800d60340f550010700c9800c0902035a42ca4101c540c00c0301000034001e010300038040010a00b10044a15210103e000814003883d068007000301d035400c0031401500d06281180203d0f20038400540c20300c0d002c00c0241c001c580c1c952041c50708160030232070841404095103010007a11200d1030f000c218000c0c1c28580030b281554654018017410300c0010b002480000004100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 14788208 1250 14786958 14786987
    0x60c0a080703030e06060306220b040b0f01050604030f06090c03020619030b0301062d03020904260304081204050709020a050405030f03040302060a0503070306030b0406090308060306010503070608130b07 89
    0x500c410782c241c800c40e503110171040d12440d405074001c002240f051000e403410f11500d41006000340940354080d07202c0308400c3c18207840030f60302c1c03458980a100c0c001d80f148600398090842035036014542840e6945170313440d071240d61030090b003219075400850b020403115a188000035500104215180e840f03000100010110301b0500202081c038000390f0712680e06042c020102120310f00550103c0c43d15580003903c40c003100c040c1411a0041404001100681e02c40101074007890040d043c200c1030304603803501c554884409002403031401800f4001c21001414240442d2054000003508950350f403100d10f0303c2072804100d07030001d20701c40f8000700d00408140d520001810441d14114110380d0400c007a40100c9881e48034034080071350404010014050058091002107400240603c2c0c00a061556034032101208442a10115102c64a484040702459401400c45800c00d50440190440e54942400640d94a0940c881c1c0e10602c03104100141e8081050411030340c20b80d0700124031070207d2400c00c10042515a05007000f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 14789458 1250 14788208 14788211
    0x60c010c090e06030304120c0819060c05070803060f010c051c030605060705071707050a060f03050601140a0c030e060301080616030e0607031e1506030e0303040f02010c02060c0a08070303 82
    0x80060b50352041c1c60040c02c000c0c0c0514135150030120320305c046c0d00300210291780762200b40c0c10002e0107000800101d02e40c1d8000d510f00c204140d0103883c0000a03500800302e04c004000083c402d040c049017848007107035008031045559884c4162103c0050380d4945d801c107006401ca00584e61850b11040c000e9504502d00c043c04ea0b420404940c035801041024001c40c8e9000c0c040d07621104083c0080e01d080881c41c2594411481112281607070b40b030001d044510035401031000911002142e40010b0b1f05802002d400c51400d00340702c00c2103003540491010601400b0320ba60b0821041e100f810080c98029030003200c0e411000b9015682e69038541d0401c650301d1205417452210a0200b041481c00c052003845903c1070b1401641c05050151561078049029042c0c54102050741c00010030500013400542c41040f10780303e440c42c4038881e41440d103074000d400c9803a91280c0d50050b800400030880015031050f840d070383d502da090802040034205400814010f0007000032032043d510503600c40c01c0900410300c0c0503040451003691b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 14790708 1250 14789458 14789477
    0xf06010303030b120105130303020304020a08030a02070e0708060d02040c0302040905010b04080f0d02030405090613021b070603061206050c0705060403030504110607020315071103040e010302030c03010b060f090f060c010c 97
    0x24445c200c40040340c3c1008407048071140a00001d02c131760019a08640003c00c52840b4680310300800e8115408205c0040c0540e00001082140c0040d1761640caa0281c0c1a05052005280c000b0100b69041e1035180b0082c804d0b980d0790340c03a080c0207001e50b0548000c1c00c07414404000c0d660712002c680d000e40d1b0150244000d10300c600e21549211090001d110f099840c51540554200361501d002e0145074580035241940c03010184423401e801050310701c041c0c103038903102d00c0d8101d500050b001200c60924940d601b100c0b041504000052002c10201003000360980da001100007080e5413003902d8500e40c0d001789180200b0740c3c0074220a11003410707410b8100a0041d0700507422624a61700d07031402c200c154415000001c0d010b40200c2c041004c02a2250501c5510050604000041d10036001d50703c3d003140c0c03098201240c1c0c0200c100042c015800d0801800c2c1040c542a0020000410544000781f80c40c01518a01040c1038000200d1540703944802400307002ca4140038240035144c41310180058083d148200c44100003e00c00744 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 14791958 1250 14790708 14790739
    0x70f0c050415030609020a090f020919050d1103010f0c05030103060b04051003030e010e030f0a15090503040509130516030b0f06061602061303030504080d050c03031501020f06010303030b 82
    0x708100501284060b180100341c81c540d034640280c030f00084140d07485030034501e00282c03071142d0b4040d001c40d0007100c80300141d480c400c407400c11140104c20329504202150340384040c4025295160b1094540c6c2d04060b81200300100200043e0141207c02d808041c21400c11178090f00c00c40d04180075505903489084c0074402052101c081c442145d0b812100041c404182034001c1010900442d04020003034410314002030402c0200c80401e107421039101c403285031035000c000385005000e03521214554400946905001120300c544410b0365030f0046018681c4039201030000300703500214003800b1901030f43d405815103a000300701c2440152541554441918614000307400584021048494540b00343c1c401402181021030f9402c1004202c5010503049802a03030400034504412030703100343c2400452280e5140d41c1c4ea503060210250400812005c07020500c603040c0442c0060580100c240e0781e2040c601c1c42c402125515020041749800440c2c885032030907004003000032040c1541a004460001019941d08000c03683c0c1c030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 14793208 1250 14791958 14791961
    0xc0e180303061509010210090b0106030b0312041a0d0501060305070306051f0e060405120606011119080f0714010c0306270506060f030a05070305060904030503040b0912070f0c0504 79
    0x3142c4855100f02c07002019840006801c01800d64020184103c400d61a1040c14210884000910a96146200c003004100240e814011a0340e8258180d019001104492f13010034010f000d140540c030048c900705490401c00031848025100b04c80b00d540750038005560b507094050018035080d108100007074200040400e080c00d007010000140c0c0c0003821201066802001c2c1120786541c0c54145c2c6501030b00070800081c250344d6410a02c90007414581c083c083c98104100098a420442000007c05800c5010000504000d08501d83c088503000b054059a44281085420343c504c90120700a040110200200c00040030551220b0342008694504101e038a44800c070700640104020700d05010003060031405421141c1c80d800c1990060405088203041c540c3c0e0014949040d0021600142d201d551101080549a41070240740d401c80e030107492245603402e040d20020f0031417000070005000d244000c4003003081100704110072a0020085a441d9403500920b02d4800e006020110066402400c1c20101140301d140a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 14794458 1250 14793208 14793211
    0x3050703150834080304080601060e0a090b040b040c0201052707050103090204020d020301060f03180b070e1807050913020a020319090b0315030f0d0e19030c0e180303 73
    0x242c100403d0703280c4100c2050340180c03500300b50312410b122a4001c44505080f0a003d100042c05501e00619252070401c031303e82e850204140d2280c01086041d4000b203803151503005880d030585401c9080072030f1030314819011030064041c1d960342a4002d0b24003405451b01036819484a0700035002e078a0a19807040d001e07900e0f0340400c1030a08103540e164201801c1042103600a611150710107101400c09400c08001c00c4100040340c000341d200340d011942a1800ea5100782e03041c400d808090350a501c2d080d401d180c1a8036204030055006042c0740034090b0700702d0f09218a41d24a41c4030054030b019490140030604c0c0c8907100401c1030b04a051050b02400c03070000520502c80e220300955810720701c41d030300550902c29100c002da000001c480340d4850920509440105e1130882c3c0e60000e41c4580381c055090101d4030319940030b05140a107110061807158004900e6682000e80c04081c2001f60a011217480010900080c18548403840f143c3c0001e10141c444000054840c801c422110700c00c1c02128880c4050080d0246200d0710b0b48070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 14795708 1250 14794458 14794469
    0x3110d0e01030c02160e01080d0c051903030e01060303050d0b01020f0a080a0c0c080105011701020306010c02061b01020c06040c080d0c020d0804050915040b18010308091f0305070315 80
    0xc80c90600154803075400345400106a01c100d07540300490800344000d0810035003012011414100052090308030800c11040c1402d120310344003421404580b180c5072644a0b003031032025084202111001814030075040083c40030924130080189990782d2601803c20ba0010480f00c06482c100807064041d58000b00301c8144500c01e0401070302101c595503a45492030752100c4417000c103000c48070b085080803c1340c000c107510150448800024a650400d20159903d4242598503101c6038010400c016580c0d030b01c42d100229081d81521402d03101d6042c6103584003a10f107140070145541d0b1001c640886038a07400030300103010b41d000d80910120641c84100464946650112803004200e03544502030060030100001550380d40140000f5040a45a8000070302807031040e101800c200f003100b141841d1610327207846154420401200c42110b0000c080d600d4080d00c8a051002914240c000700341c50f0013903198004115861803009201d00010b65180f80d026002741001d9600000007850640f112a84034105000e0304182e88 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 14796958 1250 14795708 14795717
    0x80706030b030c1002030712020606030c040c0e0108040809030a0807021503070c0f060f0c0f030e0105010530060403050409050108030906070204020a030615021f02040b16060b09100303110d 83
    0xaa280103200d04110b520840d40304600c420015007000c2441503002300c084512a50162100c0e00744101018942001c403c44a4411031400020b000c20540248941e039046101b070070b1950856640c2d0800c20700070b024042c00141c041c0200b440010030030180d42c0003003400910868440221862042200c0e1082c041103c0800200365042d2080b00401c1c2c0051489409078403c0002240030740146602900344d884491300000450280484c080d43d15405014000040716900020003c540c0341400240c6801c40001e00d85150140302c2800ca035189854200005a2509060440d40300b42010314004215500c01d1141640c40b52400001182e0650b0100c110b51441e94028015400c1201da07808000003540001040c00030700d030b230f1068000f40302a808181414030b0350060700a0302c00c44c01035101260b0340f054412007034402c0b54410001885203104240540e40b00001ca000c2e000391010162030b106000707014114880c7c1d404070112040001c4d920711412140141c9100383d8800c103001e80034000456031000103e100c0400705 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 14798208 1250 14796958 14796973
    0xf030906071b0b0d0501090506100801050f060c06011202030d03051003140a0506010611010609060503060403111501030602040501030606020307031416140d0f020a0503190903060f06080706030b03 86
    0x341e803082d6030040520381e0751660729100369100c4074014154440200c01460381d8880b070040145600510030300d80d0150017078450b84019135942400900c41101405100c1c801c1a59226412894482d082590101c44841d012a0400c0d612220032102481c40380c0d0040b8070900c0740c601001e415902c64000e50b80510700e40f074031a841710750465031400c1e100c60309501c6081041c411809804007250b0308002d00b900030040c5483c0c850303038000107110090030b44076180c001410581c01c0c0201041f00d41c40010b00c0c1c580c8645c0515001114030890a215410450602242c05c03d1800350030021060100c00d40c010400c0314400d88003082010344d640301c1641c503401540e0014010030020f01180c0102c1d0860802441400680350149644680560700d00d80382e841c42e590b010245500400c3c601440b150446504511984140010b1144410aa42c0c0c80d660307200c0c880c0003101c600311903100011414040c0310702001031035200ca824030101d450801148001c008a124485081c03080013400038030075009102d00e2044910103006001351 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 14799458 1250 14798208 14798213
    0xc0114040b0318031222030207030b060406050a0311130605060702040c020309040908030a0b0105030f1501020114040f030306050a0f05010e0f120303011d0705030109050403091e05030f03090607 85
    0x754000400360301c1d40490b00c20403800540e0052005004098007a454031001d0700301000e102d0020f00318010001004030100002c00c000c25000181d401c1101ea0207909514603680e1240481c0c0a0070702c1d07034070050300f02640400200812411162100e400c54003502d21070042c00c0c01c90590705c107030340152180e01d4120b0f800700700c072070090308082d01701f0805010350f401224603041d40c1e031000c070b01110348601040d25050b01c08800d0000000060003040100e9109182c030908500302208120940000a03114080c40500891000c2059000790400c0140500b4041003204500d000d08040518000314941100020700d00200400c00340707000004403081d40e4031a0b4030b02da41581007400540e902080707441e08a610a1101031100200d5a40e80520640303044074070051034884d40341000304000175100024004907125440e0410034081d1b4450f0542c1d0440b02c14584c04121501c2d1814150f82c80d0360320381c10884c512881080d00070801d5100350303401012142e06404451985034410810f688a0040c64a100e03400f0b02c00b080210701 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 14800708 1250 14799458 14799479
    0x403090e0601090b0307090602160b09010516021017090601030b07030c030e070306021201060302031308071103100203100f08030a080702030408010c021b120a1401110315030c011404 80
    0x1c0c00700d01070518006003a03c401d28400150021290040041c2e201d1a080c04080d81c180400c03091168445a15240340d4141007160a1a016400115041241c08100b00d00c54220f800d03060760106802500903109070310000d81c014818488405121008444900410b030b41d0a000103425040340c1c0c1042c8040d1154460003412800b80c060180c0d1082059116014a4201c18060040f00c000358030440c40141e50744104001c401718114140c0c4080306040c030500800c030119640303890b2980d0040d0302a4030140d40c0ca24514003440d020040143c51034242c400d000386805d80200c03a40c004d502034620b031003e404100c7c0c3c0d1545054030302c040c10300415407203810a000003000240200582c94100c40140162801c00b030311100502d0031200910076400050340b10b0340103242c907000016020364540c03005484940c10744980000061b135484141c01d0041c04500b5240085100900c203511004c1c1b0042100f400540e242001e2444460050101038618030038040c580b8111032644c0907210b05000101c50f984290b090610b001d41101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 14801958 1250 14800708 14800711
    0x518040308180f011508120a05070303020708210105030609070302031c170a050403120903020c0108060402040f080709110a021506010c080309010c080117070b031504110d140403090e 80
    0x80041c803400d60440351641080c040c5c1c2c031105110540c800e0b20603140c4903840d403030b21915180b0051040b0b030401086600582c8441140d0007140c0600300542e40d10000d04c7d154200d441500d005803440440c09c010400100e00491030a070484008808030b0b0801e4444c101c04645a42031840001d615a00600b00c2021002005020352070f07400050411905000c6264141c0540031720840d40c161002e0ba071141000704164210710464080d540010701042984000d54004e565500c0741c40c00d40d8144000c080002d03086948a0b011100a0080c20039050350040c5d031258981e41e902d140f806904006400c4c11a01d01e611032102c0d083c0e955801c3e0580c0104207900d400385100900f00c030080d040d00d0421846080401c04a000c80005602130b0040704000664105900002030404206800000400405101c204c403c04000546201541c48a0054543d81d407100f110f898046420220b0064106041131070548064a811000e0901c0c071949503000e000813504044003000c10101200d000340803612016040c003040c685403001c036 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 14803208 1250 14801958 14802001
    0x603070504110403080403050f0607020c010c030315080d09060305010506090f0603070c020405040305180f06180102010b0409050d02120c0604060e1006030c05010905030102031b07020102120d060518040308 90
    0x503d4680c49843d194103940c06504243c0e440d80c0328080140c00180300308001076010755a480504100d07020080000c0c16a540c0b40d101800300341e00c98012800c9842401006801805500100d030340f40404c1040c0548903031110f01c100b80209281c1400094681490b00449040d0340d4001c2003082c5116034181002003e40020b0258420009607540320401600c60744540b5018074002d40b0781035114005048015071907801700300c005001c5c6000240c030100e5520740030159120200c40502900f502c02d95070300100d0040400720b095507030042c00c11404d02c0a0010104040d02482c03071315400e680d802c502d0260305003018441c020048165a2000000038041046070703100b1801c0e04410030031707290b0840b22100c114007a50100e07002541e01c9403c6040c100300c2c941c0c01c007072011b00a2909400940c11807800f0314640f40c41c000300d40c07041443c0308400111441168800d01038901c1e0000c04421160300d402013210076800a1006000d400c4c01080b034403502002078450004114800c580c15541c2000a54400398411505003040ca6039 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 14804458 1250 14803208 14803241
    0x614091005220b12060402070b0402041d030708040609060503070212030a060e0411010806040902030a020405090f03040b0405010807030902030c010309080405100816030207030804140307170d060602060603070504 93
    0x3405100006071030b0721000309010100d4548540b524100140c0071030010380401e10481c8100b114000185818502d254400c2d01103a0004840300703580d220400312403040e010744070140800240c200c2000002c801030b00c140c5200d5514000c1d00794803500d0544841c80291540005039010703180701489031038800011a8001444c140205540f0354818aa942d40303c01602c0c205d400020354140000a541d0181c2c226030b100300221818868502c040d004a134550300081000780c040e13515080050f0094108006000c900d0700140100d0356180c0d07544145010941082c010140090305040214a07018803078018000040d07001000b80c0000000c2c0c1c4015001000c108a00b12488030050000080c1665100350b000c080b019692610041403500c01800b00c3c0502082e5084030a040c810321008020a50004c00f41e0392056010714211000c0003030741c000c0c0307195020380300000f17003030350101c0d03500000700d0744100040c04020065460a00c425500c68509a840d04c00458503550164003503481046a4501a0009100c400700001c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 14805708 1250 14804458 14804497
    0xc062a07051c03020a021513140c0907020a050c0102030901050a0e0d02060c0102070204060b0c03030105090702010f0f09030e0103060608070c0303060302030a050c090c040b0403020f01020309030114010614091005 93
    0x1800d4480700b220190940802da010891040c07480e0180499243c8180000f030181c2c0500e0318420789032100c0d04680026048201182d02c00c0c5015100700101484000c0040c40110716203007840001b55141ca0840003103426006030000011170b940000191611180142c403603c2c1041710a1404a44403420341109a034050110003010015858410003040b410b0a01c0001680c7c03440b0328010300c420388200c0e03031041008401c1000030a10129000c419031741500c2c07080302c43d000305403030b1440e049000d00003808c05004841d1500001101caa0030a40c0720400c0e05100703407034800700c08244030010b50031500c961181d4001704080d10006101c0c1031040140b00400c0b8402d05000030680d403070781c010030f00c1e001c0140004ca5155200001d241e40a10305032903402d07802550b800710f080c6003e0030000c4804507400340d4030000b409964551066501e9070f000340305945100c90050700070002d000d01c003030504612000070710a01c0c0218203520055500c45032003404a076100c480144c08094207801c2c0810440706c0e42c4c420300f00c00c121010000d9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 14806958 1250 14805708 14805733
    0x20906010c020d060f0c0203070c0506070302100e070f0902030603060411030f0a11091305071208040e0f0a0b010201060302030a1101140a0201020901090f061b110303040b0c062a0705 80
    0x80000e0203043c01382034000390704d40264502d02c0440745404a101c0a6500900c113075000241c07040d050300c09440c0c050b2052511030170a4581603180c030f8034001040c030010b810941603800c6914001400f4048a8212140e0941c590b83c94450100302e2005940d0150076401c00000100440d0404004094050303000e8111070250001d08003103420801e004c1c20803980765680880003042d078507044070040d0700201c0902040b03c105e03074603907a040d5a402c0381e40305d032145460042c401c51082c0081041030398010400402400079625041c68803612800c4100c4005241c1e41c6485080c2103e544144212015603501034004c012101c440d4642025800c81c2c442c000b810801c41300d510406e8000d402d40a40750f248001d4002507102d40c582000500b413400a81c2080140c8012500208040c40c2e000341c5071888140c6005659090081d1340c1005c40c103d28000c4000c9800d48800030300080c004082000508141e044c01b41603072020388442404400f01c1459411807413900e00c15a240c040001b0201c0001c1c551144100100d170480503105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 14808208 1250 14806958 14806969
    0x305010b1206120d0e09070801060504170a0804080109020108010902030c0706090f081603110d12050a0b09010f0303080901020403050a030809101505040e0c010906032003010e04051204030807020906010c02 90
    0x481e0303400f000500b209120001741c18518011504044a410048010340c1840c80080c1203003d64401c00c040380660b0000710182413424010300312040c0d004584c040e925510b81811501070a032040040340040d00081c000902d902c0c0070710a8034081c21641590030318080c3c182c4c542c4030142c0140c00c003c2d100404c4c0041c1f55030004038144014803580707200e48065500c80c0700c01d05001e041c600078003841c01c10940218004241e5580c3c000000103c807151580d000030319031602800400184402c0924581040cd0007001251a84c003143e442c1c030440744a90707100d161541e0b601c83e50364240c0c0214480185203611003001d0100003406005902d0703106007088102c1c1e004194010811003aa01107040828400d000b41006018500f81070003008504041c2e41c00a14910b40c613000000c0c840c4110307100c0c5200301035440f00e084444404007248244c400090343c03606034036940c6400030b40c000d0301d50a8400302c0c0d40c0c0c424110004902480c860541d4200d80e04030381ea9604080c555000d11000c0c04c0010b2086040080340210440182e446 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 14809458 1250 14808208 14808223
    0x3120405010603020112110423031501180908030402100c0507030c0302130c09271b09062105100b1204050708010e060105060d020405031b030c010305010b120612 71
    0x6100100303102d0324600003d0103018051020090060800c0e0002185001240031503040311034a12465501750481da1a030162000400c40c12039060041352003e540c00400d21000a040e02c02041080c40008031f01c800744011210100c070000c007529401c1c000503000d441d0406c8519072001107402c141d1000b22042c0e45583c00c146040e0412205038920050070b10035420450643e00d400b40007030303c04000e80c124100f006044038903140700c3e802c9001a0221180012030030741d1040410181203a0007881440c4002d90000c0310002c40c1544040002c1000c000090030611500192052340300d6502e0804105115024150103484010283c00110b03202d008002546286035000301811007031882a0306d511f040500e030050a2241a034400d5501d40c0c10051101f401c1c0c00c002c00e200d41124400c41d1a00c0d0f1700c0c0010f802100c042d006603400183c1c18084d0710b07406003c074000c2403041b070208401103040e0380702c0d810300c4401502102c00a0060806803003081c05070883c2426018074042e00314000401e2205080c8090910a00d030189 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 14810708 1250 14809458 14809463
    0xf060b0f03011d06030c0f010210020a09030b06040504080d0203090102040b0a020309040e0d051c18050601080f1902060a0903050601060309021206010501020d18050307121b081905031204 82
    0x180040100460404032403003c409500f0003c003502182040d000007075450410100350340c4101d03111099441c0700e80c004c000e140c0c10542e020a06640b40c005070312000d000f81e503044c40150b807003106d40350020300399280610030980310342c1d4448401401c0242d40c19a8030700035000240080d10640d400c000c041042030700321001c1d0a0708416a80116564803404003030100781c40103900520883d82c40603c00305e2030315401c03a06a071f40d4000c4110a4940c82613034a148113001c4c1440d240515091004407091409108002c90101d060750004c0080b21102c080c0c8540d103641e0380421040c11140217407000003400042c43d0603801070103040554a400c00c1280d4403a15103604001081c0d20180100b81c2d82c601c18811402c051960001c1180700c1e0f80a410190b02d448000707500d0f9900541c04004004000800c4405508881c1010018010140c100ca0559450b142d03200041c1201e004240d500c800c986c2c0d140801040d200d51080d013920f85100c0940380503026404544403880603281c08a815000070f005115880b1000480240700d0360 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 14811958 1250 14810708 14810737
    0xa0311070e0f190b09010b0d060b03070e030f0c011e03140106020105061002150c070c03080706020304020a0801200c07090504050d0e0603010308030c0a03020d0e100b031f0f060b 78
    0x2d10143d0300a00158448155600f07500303040c05440d0503569030f400141119800c02a150b40d03588001e10400041445402004454401009000106500c0001480a10015011202c0003d20301180d43d5444808240041c0000c0b01d0b5145a840a0010303408042c00c81d07030318100416107c210b014468041d0000b6044080103031f45d02c008005180c178003a5000c19070342c0d003103001070000c8030312400c945011042c00030318180c0125130000c1c81a04000e100c1032540d0040d50030420190b1528114504407000e5072003a2400c3c2c0c459030a40307c0c0419990010312a1a40c0700e40d031950751003064440c81040d820b0315003000c04440703001d00880c2d200003102032407400352922407403003200074004000e4050000f0300b0b0402102446270207800140014000160003104580e000020785441949482607400304070040c0c810854144050740c104aa40c3d03c0d001c100259a2089003441c6409002030001d04041c155940c1502201103150411103c03424441a49a07106100f990007082010404542310815001141d01059404881a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 14813208 1250 14811958 14811961
    0xf030d0f140406020c04050606070206030c030411040c12050402010201020d110903010507030c0c0807020303090d061e05060f09040519050d081501090302010305060d0c080a0c05030a050a0311070e0f 87
    0x201d07404846503141c1c91504030310038102810503d0080d80c0c1d080c5902614011942c62002c5021036840d0025034150682c000d010740d81d43c1c5404900326072140c1042d03130102c440714680122a0124a098010003050450310f554030002192450542d401074840580305a041d55400c100316404075505015500c1c03100840c0400540c0c914204042c1405c5800041000b001c1620f8005801c0780c03e075000038038101282d0040b041548440c400e0000a045101c1c5e52030641d40500411001e408210941e04060201074400c0c0d26402c101550044d0382c41640c45c100c51281e07000890ba0300b841a01d2a00355040d43e046402542110380d0788401d80c068280400641006440e140c0c02448105910340d441901242e02030b414401d110411060700340041c01c0e040e0345000003414913803503d0000340395482d040c44003800550480c2e0100c01040c1c4e02e803009504c1e21103040f0180c8445011433400304a901380084d402c3c403490342c000c00038800041a034408845007803007903841d42d40c240203004001445d00c00c0300c070206015200e420001c1145 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 14814458 1250 14813208 14813237
    0x1903061e0302090a020405090402060a030204081912080106230c0f1e070302090601030504030e04051006090803030f0a050402010207120b010603180b07031104050618040b060f070305090f030d 84
    0x902004004140301c600410047c031154440e000c0740e982065040e1030346500e412441b1f00c283c01038001d0b500042e8261040b500102c200826681020080c01d0062511002c21000070101b1100715409024800c0070078840c031042920272051008408502402040b15410a0341c0d10303a8050a01e504025221125840300690509503a071071040072203004400c0d401440058559800700d14082c10062040b81070642d40c8001605140c00b402e1040c4490000030f008008a1a04440d0007108034814010500000c07041e0b00c0210f0b03441c0000003101d00403190041e4400d529901c46070500050480100220b045000f003000010f509802d40703a442d4041841002960003941c1400402800c1b0361001d001c0300030a40c0354002c3c03034020035880303610980c2141244c5400314807903408901040407485554841d94101e0703400141801700380d4039030320b0000c1003640440302400920100020041c15006d90086c1c680c1d00c00e010003503100043e028900502d0000380107008100d15030554000282000003200c0d034240460310810540b0720 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 14815708 1250 14814458 14814469
    0x51b0109030e09090c06030a180c0306050c0c0303130309031203060911031311040605030706020f06060405090709020d0f060305060901110a092306030702100b0f061903061e0302 78
    0x600c001640c44603c0c500e4001c0071190b40e4041d810350240a0b0303800001003004400c07981c00094500402c1e2039031a139003a01501c1c100c0100c03030303241c402524040d180c60046000c0012040071184601c12150041d03043d40c80743d9031000c000c801203c004800384001454000002070358550b11192190903618001122460000501d09440d010150001112030800400030390600a503510408580c0282c9210001d82ca80c3c408200241100d402c60b5925110341000000c1c159800a4905250090002600c0040d00c8410034841a1070042d180145260841c4805000d480c0403a809080428850300e404a06054004000310885040b9081603c580d0003202c10855086400d018008101c80252072003403400c21040c3d0001c00079100c2d4002c2c0700c0000c28074184100c0c650760320b00700303661514001801199607003002c14019640d0050000400f4983d414501584410b1924000812080001401d00c0e031074468000d00e03041c8107110154104007030507070351038010500070109a0400890381200d296040c078107085004004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 14816958 1250 14815708 14815727
    0x2506060501020106030206120402040e010614040e06040b01030b070e0607030e12070b031f031209050306010e0f04031419050d0b040e07050904050a080307020a0b071e050a051b010903 80
    0x10705681c1080b504000503241c040484400410710301c070403c415150340c80004c000c0e0010701c0382c401d641d600b86400031644c41d0311740308150100d400c211790800951541428003920f03000200c070050310701e031a8080104003042c0c0415480d0740c864054501300b0540c84000c000600f40380c2200400350000380003080c242080c0d0418065401203041d28400400105241c801d042c1c17241d2000403e110700340091649000e480c44185608a800707182d003e60410103041c0c900400034105512482a94482d219250000030408107880481e4052084400a41201c0c1e07542e807411340b01d215600b10011001e69080208103040d01501402c0e0769500070941d50560344e40d419a46000c140d442588801e0320552410844180640c800180c090032101c00f50b40001846d903d906000e8207240041401601d4003200104000040780d021600310030b41c0e8411b10555826445017903080318071030f90f4410186998501c04030040da0711402a80170340030702207462030800d00d8070b424500115280902810300f02c1c3da5a4440c1018030400d41c100741c2a0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 14818208 1250 14816958 14816969
    0x905090f09100b0301020702040204141801030f11010c050d0903030201060f061209030203090612060103050112020d021e04020c100c020114040305070c050a0303080601020105070e0117090102250606 87
    0x1401070400421058940b4000842070201c80c0c0d8461009116840a40550f44010b0300144210745072b95840705510081019400c20302e20800449407925803414000654605982d0800c401c4002c0400b02e0f50790641c03109042c9040e605105d84001500c1c006941086004418070403030b9a40070b0308901c1c0d03140103800d40b007158005070300b0380c0c042c400140a16a80040c80c100c10f0040c01c50046000c1960b800c0607811132240c0152190412000620002c00040c4800c119010b0310080c1e80421643e82d84100b80000f580002900a40c40390300c41c88400050310f449145040c0c00703204850100040d02020001904170381c041e100003600c94010591070349003040d4501c035400c55500d55000a04c104410840350a070074100c021310003014490080386038400c0c440408408006403101401c0b01801c0d540b01c0c200903003002000c03110280150700300700010300f06500c034030403040f012030043c0c683d0280c6042d005420043c40c0070081c4503000070343d400e1000304e141c21200c24012407481010099100b018910303041800564407182c012 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 14819458 1250 14818208 14818231
    0x50307031806050a050d110301120b070219140c0402030a0e1501060503010303110304030215030f071103160312050106110d020f03090904060902040509060a0f061a03070c0b07090509 80
    0xb0090180c008040303c080b41198509140d5070345a0007454002402d00304910480c91070040000308031a030300b1651310714009008009803c9140c2d103e4000f240d81e00c0004082c003000c58a00900b40001030007030140460b001c46031a0035104c3e0030700b004001c14100d800072112402c0241d202e0030500c01c103c106024800c18424100ca015241e90b040c03400c007609510062000034104550311201224030324062043d2405194000d01e10f03210f852038250003401d00d0308156685c40a0000301c4020610030342c007071801c180003c042200a9418480441c03141a005140010140c040c05955001c84003481031030310805018182e50f0b128a140300c2c1808000790b01d05500c808042c810342d84034240b0072034090b0313001041e107150310400c1310450300e02e41e110300c0c1c003d000d054030001c02900030f810003040c03080040010407690b10628410400700986101c64041e42c040d28000c0c801c0030070047c10f00c124514401c030300000450340440c203400e0034001080a6540c012590034111440c100080070038106100502d03085100729001840d0340803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 14820708 1250 14819458 14819507
    0xa05241806011803060203010e01090207050a11031006090606030c05030403020c150708071208100e06091b070c06020111070b06220f05090d020105010806070e0f06040305030703 78
    0x11800040040605411440365100003030501c0c2c1c4250003941a91810303802508025035a4034086019400070301070400c2400480c400451111001d10a880c101b503001070003003004906903241c104050090414560301401428030709490080940a48002032142c400b000540500d044401002c84010050305030801000f04284001320f580001c481400000031509004120945040c03940d8601c100c1000070708420300030900c80103002468444421040f6203803a4105940d03540c03006a00401a07a028041c000c0041802044c400d0928451444d0b01017480940c601c0ca0b40d2017010034031403035000300b841112045000b41042c003280c0d60a0044103a10440084018203081203555110314a02c001401c46010301d01aa40300d003c214003150500e80d6101d01c42c4410486a10012070300005443c04486460f075a1290001e100c00e0540b05220b501e0403640c1079009030074207899540341124103c0b46015200e6008032007600c03542c1d1581d5200010001507100d5030003150b8403e02443d0182140b425031555000401c001c44 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 14821958 1250 14820708 14820781
    0x21c1503150e0309090408030402042d0b06040503010207050a03030605180106050a02011e140c030403020d140706020a03020d050a0605030c010302070312060308040e0a0b010203040b0a05070b0a05 86
    0x4588038442007004902003201400c00030128558090403421950190300e29050006100303180300194080e034000e0b50244140c8c03040c02400c803030000607a040300821804044040e2000b006650107a040340300d0003403049141503550b200123400d82e0000401a900c070340180c003a44017015018460701d001040151190750007c40155480b0008180512645040c40f20009000c840c030ba03c01c1d40300341503448090741108004050405a0001090750f041c01510200d110300118004013110001d0324070441d856402050802c0c0055411a94626010b40903294184280301c2400004c00da4009003003400c10f00d07a401608c5040f46040e00040e50005803e420020740360240c10b0100c0d03140412080c0c8901402e00f00985d480350329140480d0190291005501c0c0c03545410404400c00c003400e0b0007003085410303810001703000781c98a2051030304417010307502e803036000d0307801040704110980b1070101404078001c6a081c903600742174032501e1320074030068122103040555541e641001500c20030301400d0219000710003a548e03a000301b0315 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 14823208 1250 14821958 14821973
    0x5040c03030311120103050609010b04090c03060b01050c060106020114060f010804020105090a080105010308030405120a09150c05010212060a090e03040302060327060604050a09020d0b0a0609021c1503 88
    0x280400340405455028424040c0c4886080321808440c90301c0b90300643d071b90307810495110030003510079501550170500d00355614a8103025a852184e0049203c2500506c4e565a00c0010a510f80009043c0b240a0060b0321052406003d030a009044da038001142c404104805480060001000544034808400c40381d40b03942d030f1024240350f2160b42820a55a108105400103082101a60241c50315600b0030001000300b0030180c002d0340c0245e10800c12110100304c1a20b002e081030081d00322050009915520404c024078049440601d0501541401d030b03070400280d2a140c0c2664000112000c160404006000150070180c0214005192410040101170741c100101a1284228400a4400c1e04003101242d00610712940040317400141130001c400e00400284290345545049504da0304c190305c0c0c80c0000e0045c0b01301c0d001e00d21200713600500788804640d89503a40040001c1c00380c0031524050350340001081c1c80413144001d00402481d52140d0b101440303500d4802c01690380c2090b650031741403020442080003c0d1340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 14824458 1250 14823208 14823233
    0x50f060301081005100b0703020703050709020702030303042018070e0307080c0618030307030c06150e01030f0f02120f1b0108070f0302090a03060b04151401050c0a050607090e09010504 81
    0x10f8000850f132500c9400604208410540100854407400610207040580014119046a12030015078502d41d42d1800008101c0c09200d4000e5003640040000070002851000c4d8902550040c0c0d203c110b140d2a1840440c04001480c5014100d00081e8414441c0745500b0a81144501c0e5040307005104440c10301105644500024901c10300644010075a00324403400c40d1585c280100c009802c4a0300c590450a005184486820050f070b440c52801c41440f0040b40780498030000c0e01d404040c020f4050b443c40c1e031107404010401000361340480c801c014000050340c60000740301c47c03a0300e03000084c240c22040c10000307400d043c10b43c1000c004854174000c40f07aa160740c00c150003d0b8000c1c014203024000454400c0709070064800e9001e01743d844580400c0c08400c220807503210140080d402d640c1004916244000140c80c217540d40240c2100c0d403420320b400d5000e58400c0005180ba091f9031010398246035a16996185007410680b412000f0403170b500401d2145140000030360354020030507002880f89080540342c00c140ca003803 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 14825708 1250 14824458 14824483
    0x20105190509030d05041701060f050d150608030405040b0d0f0807030908030d1b0302030702060a0f090605010801020c010b0114161e050c04050a060e06041802120304050f06030108 79
    0x441204a944550050040e520b0400000e0b00b512a000c0030284004e005521a001e0300c1121040c0381c2c540c030866001445568203640310510140d1500341454100b0044a5000900301d5105180710000c1d805400740340100e50081091600030743e2200e040800300010360302c0b0407035500d000705100000c0c0408500c90003144810307960480080d65503229079090894014410b80c00601007841f0010f03032000301c0c00c0141c1c401079070340d00418109031000b1b0f42c0704011016884180c40c814016070001001c600351001c0e03548040216070341d40000181340d4840c0c1e81c1c0c01c01a210700f43c0c00000e143e5400f09444020110038000c41c0c443c1d18007480c0c240300e07a03419100941d68500660440405085034020f4540802c5500038109031102503440d4004602d8035946040742c3d42d02c5002d804940a00e0510010455038201400350205070f48400078040901d42e03480d8280402000381205801c0c004c0d151261940242c2c440300b0140118105040c080d582d03850401090141d0002d080c1207140c000c1c03804000403c00c507000030070184c0b80d206 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 14826958 1250 14825708 14825737
    0x1b0607030506040e1515100f020c010906020c120106050d051608121c06030b16090f0b0412060615050c060f01120602030402190b1b03030402030c060a12020d0b01020105060904020105 80
    0x21106d8607604504a6200c1e195a0040c06c0c050020030b40580001c418130b10708409a0131141d071501e40030011205004d2a21400f800350317006040030b44a61600140203e000b00d00b0500005866641d4000541c142d12207120a403400c0d002041002410010f8544d024083d001c154000d103c6503c40c11082581407050718146d1807148140445240400380c0d60300402d0040d07803c00d0040f102820004002424000c101c143c000115498041c00507080c00560655002ca6100071105428141780c0340180716091101c4800b01d031132650f01c0e640072400a0130590322050100320780c0d81e159100d09410315101d180c48070240c02c060141d24014010403070140341140442042d603101c1d00152f102e403160b1010480b01c81d4210360301d0346000074800e00828a01e0f0200f01403e24181e070180c034145e80107108050350b902d82c48207440180d00f41d0401a0020800d0a210300104003400c0c0c10f140140340c50080200c03000480e04207080c2005840e455004020440d80e09000e00da420250450b100380460600b603001078907d104052081c007200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 14828208 1250 14826958 14826961
    0x30703140c0a030e01170105030706050f1308010902010f020f0601170f060a1a0409080d05040305040b030406060603050601080f040213021608040509010f1208030c1b0607030506040e15 81
    0x909640c030540344800d09280445040024a140203450245030310125400216040e01071081000740340c00c100d048400240141580702d0038901c2c11910366005c84403282c4410700400c8400300d2050100656002456040000911401c0c18070004000c81e19041080c0219803105a0300345200d0740214055044852011300d03010a52460b22080b810b01078076400003523050052070308020700005c0a030007140129414001c0c0c00d880740d154500304000c641c00000c01030000d04090001000e1030070303d58040b9800078001d0070f12a0416070b43d10504030741395108550441e441503c904d0100540b5030140960b42e0020400d0031300280c1c2d071428445060701c102c0001d002a109111840d544100ad800a40c100c0e1585014a01c0d4074102322001d0600205551003881483d000300e810100028100e010108248192446200340c00b040403100c0d1550035041c0c0028220900c000c0c01080013400c018124604000e6141010001e42120314141030081c00710752000f4520380c011401d00501c2081315030085a0f10805c4665141c0c441e249 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 14829458 1250 14828208 14828237
    0x711010f03061502010b040b03030a0e090606040f03030507170a050901030903050906130503190203030a030c210504060e03030105061c02040306020310080708030901050306040902031507090521030703 88
    0x40c000340d91206103180b0f8507108a09240781d06400c444000901510140302d5820900c080c15524411200007500284c2c110034404071920b44142c0c1107800c00c9005207014202030321001d58000d0840280d0081780400d8001a04000b00044480500f22007484000e100c1c0c10500d0030348000d0301c10704c1003200e0030f41095500c5600d54201400b4500b82d8030155000f0b08a207442c0c11080e408621802e40c076005851107445203092400040301041420850319602030042e40c10048401800d50240958032498800d003e10034076080c51081180201429803801d0440203c3e660030b060a20008440d906500d00015810030001842103440303102c201c4a80710b000c0c280f02025122030418600090140c2d4200520700da000200780031440c855405507005880c082d506442c00545e0754118241e5a1042c80034040c0800c2086c0002011450700d9407007002200d0018040e030707200c11484940300452010445000010581040d0107100a0620b6450300d01c401c0090503039600610083c520302caa0707034011418001c00700051620300505 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 14830708 1250 14829458 14829461
    0xb0904030c140109140c01020c03010e0a030810050301050403050306040f0903091a0d05090c0a060f090e0703021b010204080706020a0507030605060a081609111201060503070c1505010501080c0711010f03 89
    0x9174120f113298003100d40200d601a222035401c0d07612801407240307503c0c0c11964030707040c490b005008481071b006210141c2c00f0365042d0b03205040100f125a24000098000a00d500c083c015244124429601c0d03941d00e24090303003008121800c1e0b00030300307041d00c0c54144507500090304000b00c40143c54820445107103d00840500704d03114030a01030101021800c00c0e052150305540081c0c001c1c1c003448201c9a0304003158854404a0f0504a07502000f40002c503005001c004004100e42c5035074111903d031070050f280812040914502c6001c1c039078424101d07907001408201d00c40c0180044009000d0b01c3c8080d1895042c262212580ca48142c04050b001a07a42e0004c60059a07039105210f0082040400341c1c1c0140d00d07029114591002203120354131945080082004107040d0304002c44607500d0b0b42da172035440d00c0c0c2d007841011940740e04000d10345014001c2d0741014001185401000c85a030154480f0041559810880010003c13140030b0081c0d5a2204140421000520320000d0444442420710702041c5c600702c1418200c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 14831958 1250 14830708 14830721
    0x10903200304051203030402030d14040306020f040b1303060c0311030c03060319050105090705011e140906040e06030f0105160320040806060f010e01020a06050604090b100602010b0904030c1401 85
    0x99014498000c1d0481808000c070140d44194021010f4420b01f02d400c4400781c070100020bc03601203000404100910000303d881d400303840341041c3c00c07800c0303400c00307844009400c0345905c0010324414512620000b001086000d018031004c16599240611040400102c1010240409403025601c004080000707800c580f0b0403c80c03c2196690341100402085060406074002c00c000e48146055001e40d038408200b0b9400f554003509001d201701240011501820700807100000c89019400c0c00c0c04080201c1e0340c1d00d5032080c0240000c1d2131903da0f01d08460502e042010301d81145503001455a9041108001c3e80300c115035416091000c1504000c07601c40000040b5140a02c1c0340500b10901c05008a004642008000b0314144540c406644980c6603000140040d40d4604490342d006006030301001120f80000c003203411041c2c11903405080070908021581d00e201c0400e000301c0308000b180340308480c1042580d034240540c40f50403106884249145c01c06880c000c000000c0b1402c0070f040703071032a280383c9282c100d025403088 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 14833208 1250 14831958 14831969
    0x4090f050105010b120109060b030105010809010b130c030e0706051210080105070809011401051003020a050705010e0a1a010e04030309020d06050a1a040501180b01020f0102040b030711010903200304 87
    0x8000c1503031a42c402c4e620541103c41e600101180d441c0010514000900c554811344401c103416a013075030720344401100c01e48001004010907548540f11803886460b1011b454024008503403002c1095a4681c2005048580c182d203440c100d540103060800520b41c00030201e6403060301c01d1140c5100b5030b540400183c4c0d41040c2d175100d40c1440d0b2030501004406640081460300030711803403009000085025000407010f050a0041540c080b182848080d031960096005001510305410100d0410429498ac2402c4420783c20501d0b4058003d200f542c400c1048030390040b44903c80311064910340b5410300e0345030024204000c000505040d40c58424001795911a401040c0c2a03601100c20f0106140414082c40070b820135140b546c0c080400251440000d2401c1d0107180c0c141e1301c004040c2c02c1e54500c0c804105014140019806040d809585601d00c000f050a000420240c40d00340c0f0f141b0340e2410941310003021030510170040c81c0706915100d035090000350711a004142c01401d02d040b142a1560b01001c00782035101d143c2c8035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 14834458 1250 14833208 14833211
    0xe0c09060f2409090a020307121d0f030310060804050a1b030f05100e010c08040f020d0c0308031611100b060409060608010e06030c0a15030204090e03070215130504090f0501 76
    0x91910721468a00420300c00109681c010b00548504c045d8001b40d01082e41c0002c0404e1114060080c10041035001805203200c10b0000b80807001d954811504140c0c1200c422034807a0400010059858103020100340280985e14056115240c2611040d860b4090054028060858811070a0940a0f61544c0c080911f400c0010a0850945449d02d690f40c0c251800c1044036007420071801c6900141c0c18801c0031406e10781501c5038000d40e90750b03603200c2c210070001100c203d034420141c1700c0032001714801c021440060340c0300300415543d0313050585000c00d4800c0d9092682c030400c0b025000058504030041485410b400b030050020030303c060040d00007041d40c05681c021801051038a4400940c007075101c46854121400040c80742e02c1511840141038540f04400074050700a0052041000100c94020300404205000c0c5401420191601161703415919100c01d1891640d101048030000d500e000320075200c40e50441015246050f10586a440070b40c4a42d00c22980308035590510030007400705d20b80380140c529a03c42d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 14835708 1250 14834458 14834509
    0xa030b090903070501050108070b09040f060b031602010b06030103080f0912010c23040f06051b031801080f040b0a02070f02030d0305040b010812040b0702010201020c0114010602010e0c09060f 84
    0x1a40c42e80d90304400801d0701d8960070700d8000036840303101048400a49405a10541c544503c407000d000180c43e04025074485641d60f806d0004200c540040514029201459541e40c0c800700d0b00c0000b420340d501c06400301c1c0304950420041001030100c10884003003207200720056403a41a040005607104100e900001600e500389682100d0143d4400c0040c11100116031952010b00141c400c00012401140142500000b85c05014000d5a0141c4060844800c0000c1d20042104142ca40700e17086820100c01c1e043c50300e600c041a26400c0da0000100d0382e110b0000e500c4940f6a103029110340000303003000b0381482c000903400143d8800f402020222140310940140841c0c03a81c044103500100140310844055035101e50b080c0c0081000034000c10244420495005507070704040c00c06180c80004d520440c0c0881c15503508020b803030400c00c4203001d0010b000801c08085103896152480103400d40741903079400c0c481500088140100d42ea02c01d45106e4101b0740540d00010f6000c5483c02041c40381708152a5a079200aa014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 14836958 1250 14835708 14835721
    0x50711060a0f0629071b1410030207020d02010806010e030708060f0c04060c080306060405040507030605030f0a02031c02010905030f03150a0e1306060b04030501090c0e13080a030b09 80
    0x40000da80d880036200100030003683c0304d044000c94016032800180080e00b01c40c03401400480040603000722402510f070703554030070541c007401000b15200d40e002c51a031031606820350416141002c01c40240322080e090652604066900164016030f411800a050203982030203e0340991160340112095000501121400e40d01c0d2807800350b603030300c04840030a20816040d00040300c2c2d8540c00280c40444030700b80c5030800006015038a04a003608010146034100e641803200140507912400b642c5d004d00003030f031000070306907007004241420306600303610240145c0e0020785241b0044c0c60001d1031940d03940d804c610700c00c008003070181b0807405003c408101920030309c4082503540c08010120019805051404510031803045200300707000143e200ca21611400f4001c0100207044030b2000b10800003114032401d00000c0b0b95489900b800e0345a000f5401c2a1400c0c2c0d900d9050508202c80ba110080141054601c1e80905240806640c5034038115030b0700c001c4c4041c00c0270901c1b0340c00c1400f941043c5600e01d0000d00741101d81c600803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 14838208 1250 14836958 14836961
    0xc031201090e030406020a0602030a150e0604050a0b0a050103090602091009170a080a0302070302160801021206030304030506040213180305031603110306011809020d020403020a060e01050d050711060a 88
    0xa014060380c1c18942081503050340c00020403a03040b2641a00604440b000c0c0d52a00d2001303420085c076080e042c80d19088401d4204210100000250102e040941c50500301401400126003000740002e100d203103401e00c40c55055840c02000c0b000c80d0f10901e004a541411894424082e00401d070403143c000080540350750300c664004200005803401010700140c10014440950380e141c450708806017620000b00240640d85100ea0021b0561501070700481c3ca48450f82c2c000300c04c00d405260b1100500d0395001c2140380402442441d01e94100008600440c18582943c562a1301c410340030388024801c80032892155000c40302c03500120f0891341656041d03440c500207814054400d0b8011101606039041c051000144103001344a00d04036031000850b4141541e84160055401e140000e80c0307200b509404003400a00c80500d030001b0300c800744007004090b845a1543c03042c0028090781d40c0141082c443c00c16200042071343d124094940c108500c02003c2020380f1031a2090710103024031004419140141c40400c41c806c1c400c1d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 14839458 1250 14838208 14838211
    0x20d020a110604030801140102030903070608090106050402040506190c0609030206270a030509060c0609012f030703020304060204080d031b02011802040e120a0309030f090302060909040303020c0312 87
    0x703880701c0910105000c1c40e680c88210480c2c005010610a0b001440700780d03240030481c1c0c08440113004036403030b2081000010349400b055503c402c00043d23605040145043d401c2c01650010320007603a003075041500b4030740010001d00820114100b540360301103040210f14455158100308580041c1d00308814906401c000b500c0744070842d4900807140c82d080075440803c00b048018549803401c200588030003070107981c0c2141c140e440300664a51048042c4110a2541e0003401540c0c0280722010002441d4080300035100500c1c1c02a074070318680c00414500b8140e103050940100c80d4000c500d40307001682d981c0c517440c1c030000901650300f00b030b4038078480c03c0552004e0390b8040d0700441c01180202a41c1d206800d900034102d00fa0f0303c84422000800d90307809000b43c01170074207412820700768507800300b0348005d1904610340318103070b80042030700c0310000b6200e40c500001c2c9900038400003240c00c000e24280b4002810b54020507458401e01800c103000d40e4481d000074040c188242d040c0c0b441e00803545c2c1625583d14a14080c01d100038070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 14840708 1250 14839458 14839477
    0x30c020714090703050405030903030c01060311040e070909050304030b0103031205010f1d06030a050604080a14040509060d17040906030611030f06060a02010b090f0f09010b030c060a0210020d02 85
    0x3589602140e02003441c0c0c020480200c0040401034181c1d60344000303c0191a028004588a00c02440645070940d001d2000c0c141c0194030300000540b4034558140095191492070342e07103014030701d0a20904880c60000c80e0f14400e0721a07905001c0350081d81c47c68040e03e140300715440070b44100a004000b10404d54454080c210344c240c2d2100902c04d690325500c62a01c0c200261003a40c05401d04100d000503c101d800005035070000005083e01c0c040b8a807a00e4140c00e01408a508460021002030302c4500260821800107102841081c0d403400c0900744804918580c4001e03003a1441130124000303440411003020342003010658900c2005440d150758014580140030b40e804101c810341d052102c80c446030345604099038824245a451015251510418401c030381d4013108108046548403401c449440e03e4124805000300840c650324015894071214031b031101600500014040d03410716482aa50b80d41c005040000c00c20100c0d40f02c0d90b501440c00080e45081081e110000d411400820301c4442c040065018044d200c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 14841958 1250 14840708 14840713
    0xd0b030c01020705010905012109030503011502060f010303141b07050307080c09040204200a0e10030903020601030602130503010905010e011401060512040f0f0605010302030d05090901090506011b03030c02 90
    0x212080c01a40c44000c5030160390f0014011250803c459840383d10309000c0e0310319404080404110440406050300d000715029000b150b000801000b1020100a01d0741c9410460301c090016400c2140c15103a40503810311014081000c5440c003000d42d040e110303007111a074190b80c0340001809150030040c10b44441d0ba0f8800c90348640901100003901440c08100c65000c1c0030000c00360b03400c580c0c6503801c01c00100848441301801d50044644687c2d4115408000c1660742e07407c1c0c032060780242e0b40c3e8080100381c1511644050800d030400c448100087c1d00026106c1c1540e503c400003503200c140040c0581c2d0312078425401035606608000a4006000c010f500031440b92460000a025516160491042c1e5200030700c501c20000c0e0040080350f0358202d10b40711940e0468031401890380c1014035519126503181152505596113542c42c001002145800c001142500c500f41c1009824040e002000410752001407048001882c2c960300014080c2c0e106408150002e0107071407a000c03000c200c5040c02170091120385110005032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 14843208 1250 14841958 14841973
    0x210213030b0106030e03120a0b0303071a06060909060d0201030e16090c080603070303030b060712030e0f06060607060207020d080a02070e070302040b04030305132103020c0f010c0b0405030f0d0b03 86
    0x1188240103416800e85170300c0046107005003d19550b040094000d180700a1541d450584406541d0140001e11405000d000c452700740c44401c14400300224400340c006445000100442425a10384080c07195010b40300b100c1c1e08183c00150f00060340070b001c0415513a00c150140c02e0482c0580358510191400b40e510301c3d0300800c040e14650300152170740e076070646419616610400c02000020301c02c8d002544100d001410590074000156500c0c1c1050403001d207003002081e00c1c2c0c2c01d10b0303e175401c1c10008114038a58020040615003409030126006100e55100030340203c0d0002030580964485a0200280030350080c001503035168109802512400140241740304541201c0220700000c3c440e0094038141d6050581d41460b00e44bc5640c2502c6581c032016482c1810702c442070002070801c00ba0455019001c9074581c640e0f450000509d80241441e0300c0030600da1040603031402180959a120101071011607009071111a9600c81c0e040c0245907014140009c046540c0000701e403080303020140c11000d0114800c0d4100c130b102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 14844458 1250 14843208 14843219
    0x6060402040e04021203040810021c0524040209060406020109020a060801030b010902030702010b0d03030c090801050c1b0a060e0a06050708040506160302040911040302030705060f0a210213030b01 86
    0x50744141e1069400c0b60703002c4408580985003103c1810350008031001201e1070155101d004509041007081c106208642c04142d01c1c2c44100700500c4201e07681c9660000300424a07100c4280300150b40d515030742c56420425038540050b1903c582c0c3c101d40e81c0c02c200411258541e561020000d020705140e00080b40202d24800c4000744190051031458180e0380e002e800200d55a007000d40c81c800a4000812501c119900c503410412183c645152442401c1d01aa5022030700b800d1541020f409103100e40c1c04400240c0c503020070040c5003941501900d44d0340c0108881d0411300003500300c889103090340c00d16014142c24904400c481000f1000202c034031140340310b200e043c842030f80d848000b038941e10412500607181d9081540003c0040311001c80e80007201c00325040041c2400e842e02a18030455690701454084040001402d1081d807a00300040401040304564061030140180b2040906028000b00441401111034440201c115400800d0310a43d550100031903c601940031403200802c5184000c0c0c40a111a03000800da = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 14845708 1250 14844458 14844461
    0xa05132007030207030303020f070b070e030601080c01020709020705070806010b030103110108090a060504020103180501020403061109010507060e1002070515090d230408070303050c010b030114070c060b04020c010c02060604 98
    0x900b82c058000d01604c031700e15202a006035002c0c44035041840c1c4200b12a4000914034030059007d200c41d40d0b00d0100181005040c14030380401a040710940380d0003086501c209a03030001d00c2900ba2841008090307100c403405c3ca001c501c2c09000b604111824010140041000f64140d00654100d81c0039001091140c1d0f007010041d140210240c40c00c1174aa00200d010401051594100c15041481031400081d42804030b000d80c0303001040b040d0201c45c1c2c1d9400240402c280300c210300078200ea007003042008a00d81a900c1c00060821310a54074010685c903160240d1560201c028403048040d550340e00d40c25982c4408030700e407181d00c5a288038a0902e401102001140400800040180805025894247c4004001304096040301e00c1ca440e240b500900c20040801c19032020b01c8003200851090311115180d581d80b50b001c609548000d014a07006e80c1c98450044030741020500016080b28050501341450030080c1071800c00b508100c21080c3e081400001c40c84401c040542c00072092039056401c1c2c0e1843e413076030b108010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 14846958 1250 14845708 14845717
    0x90c0411041205120408160509160c0c05040203010b09041a011b050a0203030d0905190b070806042003070e010801030506040209130507150806090f0a0b0a051320 71
    0x10015106010074840201040c014441407801101103680003002c902101001e0782c017940080800d500f24032528124610061403260140a040b1101d00d12454170011070413280c51003c082d4400c1041000d007803000d008500342c0000c090400500103569a42c4c40b45602c900c3c50740b04280d00c0340a1881d0124800b900c031030414000350041016510704185499400c00352505c0110324006880500510220784c0c01650104000c190400040c4400300f00e072a0302e0308241e41040c403900a80300a101c244000e0b500003500c04c1c400c5507031042c80390a001d165921035a010400412174007500088082d0f103490243c80c903609200c0a50302c03c03401982e52569002504004442c214000c3c8802032250b4030003000300d0014a400c1c844560300c2404140c584042c862103403201e41c503000c1c0c0e07540082080032035400c0c1c00403502c0c3d02501c041d60192054400c0c045070705050b00d1140b039280000b4680707200c0f940d84680c001d00303540d12074103240c0040000901041c4400e80280030b100080c0030466041010380c544031a526400b2844000742d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 14848208 1250 14846958 14846981
    0xf03020a02070501030f0f0f06150f141e03100f0801060503070308030a0b1908150f0601030b03071502030903190b0103110409060603030e09090304122405010e090c04 73
    0x10202e4918000c01913029028030a196040c95882d40340480524202d44911000038400d8800862050728000b00140d20a80c3c442a2204101c0f4030444a5060b0760010b211210400c10580882d5680034902c03642003803041e51140a09035134a00005000000c20813640b0305013501c400010580400d50f0301d122942c00c0b224030b4411290980c000840070800314500c00042d540c058181c0c45d000c80e42140d0400001d10700503811030300e58000e0002510034090140104801815000394114070720741420410f10001c00e804d40144103074100340d290811903040d510180004030007012018240421080d2130400a03482e0740002030000e01903c16854a136565242c1c031059914003d400825600341c1c1d9086440b401450703a5240840f03500716482c3c00342000001d850780316000046000f542d480884944100800069110207002e2038440e500500050141c19040703908400400c1d48091007880040320b0445405c20b0201b0240c0304100c05140c1000001c40c1c6a801c02c010384260960030a4a005480f0321040008560201545 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 14849458 1250 14848208 14848213
    0x120115091e0f060c03080606120114010c080d060305010509061b0a02030418050f100305070501050703030b030f1609020301030305120603010902030106030302012301081b0607140c010f03020a02 85
    0x1080710440341c19140e01c121290020700345001c1d4030b400844094407110b5121500180e035141c100028941c1c080c002c143c2002c2c04554091500c04141108401103606000d010b1140640710085110360307000f2401c01c44000c2e03000c5091516000003c40c544010007a0f071005031040e508001c0000d0203010080341c2c6520510303001c010303041d10f0b20f142d5070780035241c0d04451030707042c103511040001090107000d940100c4c841d00d2001d00045803910304000700704a82c1b00d028194035001302c850402813000403400b0a144054600a181158840d200380c1000c030017270600ca11005400d0302920b05445900d6601048e08110b0040307842e46407602544d20350807481284000d00c40500044c2c018440c8620284098100e140c02000080c0049400386441d000642140c0c855801140940e540e030070390100e103c10a000b074a0702c170b8104906a212a40c0340080e41900ea28040395509605140180c1c003003400d95502d0242c074906904004d0f484102820442896a5406407503941d5010500980c1400b03e050b109008403016900907602 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 14850708 1250 14849458 14849477
    0xb0403110106050303041d060a0e04050d1205070f08071b050c04050c0c0303041101110318040501060f050702040b0423070201052d28050103110909060c0c0709050c120115 75
    0x88003030b40088003810f482d50006403c0000110f802b8402c1d84107000398095400303812802503180d00a80701e0016a445030500d10300300001c00c605d01b90040031104058400d07041c0f4030500c0d51180001c40d5450110384106e1041c050401c02d0f00d081c01000a9154a00041980c080000340c40d0310141a5860040e2603008246030300410000e00098082002d0078520716040c10002d152401c0c813102141160440030030300a0444124800074010319103170056500500890402c1e034080306c03072440014000d20079814003070702840c0c5802026a19440300c0e40050558203000c1207c0f0301c90a84440d411003600380c1900d02000542c2088045101c50020080d00d11042034000051000030f5500c103106080c0d11001420903621003011030030101d040140094a24480828081c0041c0560444c0b80c09194242e0385c804880c040c00c80e0500700507424400003011f9400c010003441d82a00c4e5940041910300e406280d0300140c081a003013030300b40301606921030050102c100b020000004940c0c0c840241802c010301c6498803500280220a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 14851958 1250 14850708 14850749
    0x6050a110412050a0b0a020306040507210e28030810050906010f02100e0a0201080109050903030c0d0f150311040b060a0e0a030f03020c03150702120a0201090b040311010605030304 79
    0x401040b210b44074030b0a40e94095040e0b100c82081d100b00b00c0b0340c140f8540d000420085503182c584030302c41e0b0003c00c0742400a10340f168600703018015071018010500d0a5a00d20030305081000821540c551a10100948091140100c84518081e0b403040021004690948080742200c0132018414082c2c45010b000c0d60015a01c20b401120340340015024401580036101041220f0344050040c054102d4a1000508884202c1c0c4001881800705a2010940038641400d0040c40d400103c02c4a4001080c504590349812280c00c070300c07000f000003080340400e8520f040074017410302d2400c0c4101000c4031f00441000d4105001c41d0144820b0340d0134400c042d83d002c0c00801024613032131f014040e985004030300a4603003002c0c65260360700d145140c00300510a80c00740c1c0c4a6a9510361601d410030016040308502865840c4500340140040e545811103200c110703032101c0100c0d444141c240700354000d494203030b00f101220b24182018140034100c00704103100c560403542091804070b1a42800000c80381200c4a042140101142c0c18 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 14853208 1250 14851958 14851979
    0xc0c01030203041a010308040609060521040203030c060a0b04050702150105130e0105011217070c03020d1401050f01080d020d0e0904080c0a120305010509040b040b091608030706050a1104 82
    0xc3c800c03211220114403059061180d0040b050185100b162030640e9a400c0c90300107803020300d05a0041d810480b08008040003070880c58203a800301c80c045000e04915460b5440028150302840b201038000303215500401c5401d0071250084482c13802c1c103603401c20568075010412a19038088915808404404800420441c20200c00002c1c049082200c000f80200000142c0750a440b02030740060244040c0003118002c0c0100c0c085280f10001c10285c210b4038211349a5149170082800c0d2102901c1a0324681d6642c003844188407100c600ca0381220002c02061030082e003030b8800701d9030070700800300710b0700c141035078104803600026050341035800c0ca855510301c40c50010300b040303040c0c0c200520032109400d06000c1d81003100010021064110f208840b524004c80080c0801012200164452440b84030202c082c0800f080140003d16081768000d80c0e074002a54480700968500390345410814030a2038510000117600d003020001d00500c3e441401c0c28400d5407502c02d010801e0301d207111a95101c1c400200710401151511 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 14854458 1250 14853208 14853211
    0x7110102011107150b01030501030f060b01140307020d020705040501060e090a0b04060806150319060c020703020a18050f09030a0518030312090c03010c021c140706091202030c0c01030203 82
    0x140300200308414a02000c0d452900006030403122511a400280000d500310f01500710f0741402864204083d600d180c94001d140000010090140755441c2c20030843c0340d04c01e02603511600300003041230341d4034201030000a56032050080c030a4014011a07502143d24134141c09110b04036100d903a40c0911400100e070030440b0055003d13110548084d07440c0024241500c03103000e218000d203003000c00f911a5103416100320001000c40c3c1d030107520030742041084005c000d0004d14000c1c54a90801c0c0f00041c103902e132110507841d00e10a81c0000e54007049089001510549032810141c4480301000c040c4495100d00da104152101c060341c400b080c0340c1051190f902d14a01c00c0c0041c1091010f00100010b500080c540401c0c15a88102c6901d140c4c54540f408001a0f05030401100c3d521581c07d4000700620300d580807001352a41002ca960302c1ca42031100d40c00560a41c840c001000b211300046100a0341c820840c90b000c0d004111b50303a000c4a02071000c103400040c030360003c4151600100300030003400d040e111440045009620 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 14855708 1250 14854458 14854493
    0x5090a0b06100c06140907080f030f160b0903040510050403050a030c15050709210f0b0603030c010e01050405060708040c0303050a12020309010905120403032001020f030405030901030606080c07 85
    0x805118000b00b21680505176018014a2244026061810895003482c11741d4104c04c0090380100c641c004c070403000008444200c0041030080740c840382c0752000b944d41403084180144c00101c1c040d0078016000300100090040b144200c81540001d403050400795030600a0b8800903003141c11098802005c24015015224424420561a842503644260780e50490300b0656400c1c1c00203501c1d807014401e03c01c0340d0a15001e4000b900c641d05203811410f50f182441d0300d129140083c24480908085500c0381c0b402c10035a500b10701d03036000030f1115581a285c200d00074001140c054540d4030a18000c42c4401740540360850059403c04800c180507070460301c0070794040e03101403100c030100300c1316514406804241d48040d42c0035920840c00442c84000c1410451701e40820541c000d030300c0c400200420400a5045850002c540c4d062130b0314880324a200b07e113650b00a0047d11840035460354004104410400040f00608880c1d0098070200091178a400303046514040443c0c80b8041c0b540108072030000300360803004030032404c80b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 14856958 1250 14855708 14855717
    0xf0402040b060d060302090a020f0d090201020102041203020a0c0e100308070305040518071101020a091e05091e01090501060e0909010b03030a0201020703030509030711100212070c050405090a0b0610 87
    0x107400d0301c0440d4480d0b000ca600c10038115a100300502c01c5141c1201001c1e0002007003401982440c0510b41185464130a9003c18003c50b5a580015411a4000c1d01038034003d20f1804000c1a03440c4003030401039103031440080c040310030300811030010600201003020140240c00b0051014503050644d980c0003c83d5204000030740c03c2c414103020004580d5141c040c1a445050018060440c40c10005809440400fa940407481c20764018002507501139404440c9008545100d511541c0741c89000b209400e074440d564109541101d111401c110045808503810b200c0f00c0310309a1740244581e07071070310600210340007070044100250a10310300300d000e4030b8400107668112103000d000140020010000030300d035a202400c440c000d070f50003081400c14150140300c4c150340b200290f0f0107180f42c00c01c1341e03442d00078580e40030752054811000050840c48503442041664050300c9003081556490601d41030a480010240c03203213520481c24800068a4503002080b5010803690210300c40c1007940b2200308200c5045c0c92410303d8010072 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 14858208 1250 14856958 14856971
    0x118090b01031104180201080c070320011d010c02100209040b0a090b03010c02010b090a1d07030f02090a0216060b01030e01051603060b0c070311010c080d06060206011202090f040204 80
    0x89940c020503000354450940540c02c1c0c0d076202c05120903542d95819031140c8540e101d072405c0160b6000079009030710540320b00c0c040b40c2c0c1d03144a14007924240b5403081100c49180c01094002c80740041580895820b200304c10042840c541341c21105426150f5000c5440016002324200074074121003900513114041e0300401c0481e001d10010086a401c4540b81e00101c102070b103949a689207402c080c440c0d240c6000b4a480248401080c0c040450803600000d0702d0a040c1035a5070481440d5941d520212190403a030050607520810b50b0b9080181c00c02192610130ba01c1040c0c02800f0a00540e483e00c222040c1c9240d000400c40110616162100140020b09c0014141031b191182c108082c2c3c3e0038840d8038131030070503e56028950201024000d08648598103c0e000c040400c000c0c683c08200c00250b0381044a0b48040171203039006404004a40021200300000c100c54408a03513402202055000b100c00e43d04d066089401d00e0380e03203400d1600c08401d64880070750415588004941b0051070030281d01d5000780007520104030b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 14859458 1250 14858208 14858213
    0x20105090d0302060615041406030601051608070b0f011211060c0106030308150105040602060a0e010603020d050a0b07140405040509120c03031006031505010c0515070302040f0b04080303011809 85
    0x1901da40002200140c1200041000910781200014810b00740b041c00d0900706800d2510810030904810006481008044000f0348260702c540c00310b40d14a002084d042814010310b10f0109125000101d044915402040c0000e46011050201504a498000d1654100b00140d220480c0c581d2030030081d540c000340100090381103402c0c2409140000c0d44aaa16000645070a84150000c000080c0301c0c00d04000342080104001e07640010020782080714103000007100e18800d400580145882c1d400207420042c006009014060040f5043e5030030380c040d40c0c00f01550740d1180c1080301c040200541248450030103000a1115003480d0344040e42c85503004003200c0000140004001d07194004040340800380d84004200894040700810000c002c0074541030510001e0a006040080244503019490400c00119000028454100a0820000c1e61254080424104500e0080c0070350f006018082d0542c240000001d6581a0b40048904640581001d982140d00300f45c480c2c1e10034101a107040040c2500c50b00d40703501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 14860708 1250 14859458 14859469
    0x106090606110106050603060d02011107120803060f0102060c030c07060b0d1112060705120406091b0f0815011e0b0d02070c0b03040c1403010e070905040201080127050402010509 78
    0x181445031201c1080e840d4242c40142518050b80105001c1c800c240240a01d60300d1300490301c0d00c12035090a024540e000040c03161482c0110b40c1d4041000c5044000d071590a00c0440c200850180505807803a11405104000682c4c0e22032056411048009080000800d030450340d00280002c284181e0000c01e00845810000328121401101529201002c148045151600250500c5807540e600080c00039481c1001014000340120080c00301d061100744d0000b82001450b074070160720198081c24022020b441601800701e000a81e0042c04810402e9000c0841c1c507020004200c6079150501c507241801782e0905180b024070414821040d0301e40d20305840041078001c4444007130700b0020300441006071915494100022604800d52001010507402c00c01d200108521070701200a80724014614408403410101003401803641d582030140c0c50082c9035011aa012032074000d00d0060b4003d80e600049030340c031034a14130341d403209400310ba08104611006202c101c0340c01d6005140d116005040290074542004003042 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 14861958 1250 14860708 14860721
    0x3050f0601050a0f0f1203171503060109060e130201020a12020f0106050d0206070204110d02041202030106090b06030f07120608030c0d020309030c040222030503030106030b04090c0b0c010609 84
    0x892038100e10010302041c2006182c02c0000c011140304900300e145091410000c4404a00805448580580903070050600030b0a0b05000842c2c103101250f404c0c80d02510782e400481e00c07030610910900500e00005641c0d0198021241902e41030000d551a81d1603103010320b105070003a56000c03030550150202c005e020802c02068440e0340b00b8950040c009146520410034215201178004600c18407a480e01100527072120303001c3d6010164180c1d0300040d034520511442025004000c1e504154a00001e408580740c0c2000d210a84458800c1d0020300050380c135096568148e03034444202c0b41d0030180510018090f80700d40c03644140c0288140c1019032071400090240d00541e9030f43c1d080313041c05500c0081d00f80325940042026820442d080d2000c0c505100410002175261004240a14855900030461820001c0c00c0b891034060700c2d5948029038005030740c82c903259840390002d20500d40030915041c89403ca03410180910b01c10290300c04151079040c0e0400d044504140c21441440d01150350341c00002c10000698829078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 14863208 1250 14861958 14861983
    0x180f020a050309010606021b10020c040203070c02010201050a060e0f0a060b070b040b0f070801150e0301060807080d030203010b070204020304051009051b01180b1e0a0503010e01051002070e09070305 87
    0x79590707280090006080d60359a038494011584914101d956000a03044560041d040449036204610504002213180032a40d284c07040d4050b10001c14003082c0c82e0030002010100f80300303070020300055540c0d150729422103106107d50100600300c4c00000d413041c14400c80c103a601409842e0000f07099070300c800c9c3c10b40180c0c01c000002c40d0f003c482c100602c0f05003d1440c0d0040d90000321100901c2c441d2400f4800200500018480c544015069802500c0841c1c000c01107500a0700001d4000c0003042c0e501d80090350b40340024840c850f201e00541580e1204584a4001c03a4142d03900d10825038600300fa03d9092100a600040007074405028060520300f00311024000c0d05100d80c05031004102c0100007044100090400307a0045040c0218800703503040c04150700c04010102c035a9140f149854400441e51440d4003403c0e1075400c010104000f810b0380165403c080918182c0300c0700102510940e0700c071001c0c80b60b6643c0c1030403e9005070f17028420802c1009003000002e03520141003016100c0312542d03030f6140c0380340c0304190400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 14864458 1250 14863208 14863217
    0x402060a1b0f0209010909050d030b031f0204060e09010b120403050706050a0b040506010215012606010f060e04020903060a05070905121c0309030c030c02010215010b070309050102030c07180f020a 86
    0x10079440e00c41002400b409800501f080192a280e032420b541d2011040000f09144c1c48940c1c0c2c3c50995002e016900d103100703140c00001442c90000104c10006e40c00343c0a01c0303001c12403000c90110340f801c21201240c10b0703074120300e50725160840a60b4501c1e83c02000420071801c2000c20002580010900d000b04c9015041113440458140895003c02003901d41c0200143c2c11944044000c00c200c0d0001c060043c115100340072041e100c04803044501c40d11009004e21030626214400001a03c0d80d240c01d071040c01c440c030355650a0340010042040209030710130600c10a9141d40020003103074200c142d9034003003900103480e03041600b000303544c2d03001241c3c05042c581c080000c0354000c0c0b4a40b1201d41c02000d0b0341b80034200c50340f40c20080c1c01f00e107990190080c514500702804200c0911103c0c02164000c2044140032150007070100c1d265a941c04440c00103902014040700082c001f11400249940008103440042c1002d101502c94141000300b4006d0a034842c05035420b44a03100c2c400400c06070058070041c0748038001d903600e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 14865708 1250 14864458 14864483
    0x806191b05070c05030c0d060207020604050303070b040b0105060301030803010b0a0908160501080f0f0c0717040e09100c050405040f060306060902031b09030712050a0c17150105090402060a1b 84
    0x1030007043c00d8401d80c031460081e00103190000303103941e6000901c4000d43e44040011707122440d5001042d000d0049811403030701844005030342130034010304025031803080f80304500307450440ea00e5600b4400140800c0c4401032001009000601c511012413001d040f52410078038080100613641d0720b00301e00e81200b40791148210715556900f4400c0303591000003035501c5042c58040c0c2d0050f0030909820796000d1002003401040100c0481c4c10010084440c0010900c1c2904480c0585c41c0c68540082481c1444181d6400d2198032884215100025650240b1301702c400298807554145032500003800094941c8107900c0d41d0311590f454010002036901e11030580a0001c2050040c1c41e0311b000f80703010b615010f58408125002d0350900011009550000301d41040d030300000444003400504c0c0c50110301e4406100c100a12a0500c0340000c204940c8002060001100d941c0403030700c244070500080102d460082c0a91a0400f10a20004001d402c202005014542c0c030b5241520f08000503600b201244105d80e6021920088500c8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 14866958 1250 14865708 14865713
    0x1407020309012c210c06040f030f051006030506070306060e09040b09030714010c020106082e110a0305040203010c030207031407020105040f060c120302040b0d05040809060a0e0306100806191b0507 86
    0x2040c44a6445c2c1656007d2400b4105900710040c041903210081c0b004038010702d02400c000e014411088040c690080c10300460340c4038505240c544208031540d00001c1e107448030005c0d43c0f43c8112030740c03806002c0250101c1c0050302d85407650007640c0c40c000d00d001c5061104102d2480050041c1984504484082c2c000140e44148494000d00313460700d0b98041c118907880320407181394200c1e445c40182c007002c2002c904d01c4821049414954042d00d66960f5018442c9004a03d415001e40c26070031051203036100f10004c00c546081244194228000c0c031001400240b150303006100741ea03460f88010f100d241d005050039400e040c1e88078024a0030203200c0d042880028a02c02c0b084c410403120381050005186182419810142044801c1007180110b40441d207401303440d03101140501c4010021208482d402a1419960395040710010307000841a071b10305401307442244000303100c0e200003103885019280d03142c0c05800551102e400903106180110482e10010740d41d107034080c041c000c00b00651041480709480341c035200c95036030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 14868208 1250 14866958 14866963
    0x421050607020d02061909061404020a051905060c010e06090f10140f06010903021003091b080a24050411010809060708180102090a091407020309012c21 67
    0x500601e0030743d4440038150b0040e580202d00ca41e0310020b080140d03900c0b41200001c46020f003c0140014009a04e03001c0d4140c80c0d00400f042082c4294000e68810081c1030743c51040c4003c45140d00d1351800501c0c52208103002034684a002001e002c00480700100d020b013072040c801800c04205070b5a108aa0b80898040d0071038001c144041032024a002008022200100d128181200001088100d450911000040c40c82e0700a404800c083d5801030100010002201d03c05401010700541c143d85944068500d102c899481c0404c0b5003e40351110081d00c1c100c19150b45801e07c2c03490b144085450351071012908102c0d01c80a1180ca0320a40c011144110000c0c2c040001521455000e803c0703002c550010420804400c0e001407409401100d082c1c43c01c0c000b141c06e59580380c0280600e40155910004010700054461445e0700000003184203019100b11603111200c9c01da94034820499002c0c0130419140c81e411840158110016001c0202540c00c50000416000202140940c0c0652400030301d920141e4030340040304 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 14869458 1250 14868208 14868211
    0x30405060c0a0c0201031d0f06010503070909020303070209040c0305030309011407030209010c020906010201060e0a020c1207031704020406090f0507030615050403080d060807060207080d0801030b0a050c04210506 93
    0x42815561400b142c4a0005100120092019040c5900d4600040360401790f4010035045c2882c5d0420784240490100d04252102020300c189803184c880e1002c0820142c0c43c0b0711800306a9503009004500d00b08142c0e080c00044080140241d900b0303501d12030000b001c90003c0c03009620a4040a0001a260081d51003250f42800041d21369402c051040c4451b5090740d801c031b9042101580c0440340c0f0b000c07568400f40100e0160945030412514002400c0c144902c01d8401d4018100301801c0e202078400c40c0c0608064210240940c590180000f07130307401902c007c05210000525041070000e80045030403030301c560040741a41c0d141c802440e8565683e40400000907814030900000e4403005000e2001c051181600412501440c00064800d0000040b4001c240520f035111100410040d000e58032480e940d8079029403148158483e1240030300403401c4c070f103003d01e216460040c1a04da00c00409260743d150002c0a00007842c0041485503060780400000c25a89602c14000541210300843d0a81d80740991400c2d82c00c1420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 14870708 1250 14869458 14869471
    0x50304151b02030303040303110c03040609150816051c0c0c110901051302031e07020a0b0108030a09030602090109050402040f090f060e04030c110907050703080f01150c02060f0f03040506 82
    0x4070344a242006a034084201c1e50131030b4144c6801300744d24685d0029000d044c400d60000d8000e600c0f00080025049401c480d090046a51552403545c00b14410081546d803040101e802da620842c408444061803402940540301c0e45101680d01018144104480c1084a180050b1000440c5401d42d4030b10402c281ea2450405c14013080c1e84030320711540f4080c040313a5500004810f40842680200c00106e041c10510035594401610030700e010002e040c082070103500d4000c2950180c0d80da040700400440e11a10010880c0c1c11080d456403200032141c91034540000a40042c46070398104911074100203440d54450020303102500540c1c0030103c8592400000d042100c100d03801d00c107011820100b0411461481d176810303035800f58042c140940c012015141c250040c02d50341702110303400015070303090240c116170007800340109500c40e888903082600e94850541c1040d80c01d1141c40c604118070035000e0b01d070600c1842401e001c68806480700d41050003500700c920030340d0000e03142c1440d13114003c402c00c0709000003001090342102 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 14871958 1250 14870708 14870747
    0x501050f0315010504020f071e02010206070203190c03180801020315030703121103070c060807030b09090a121704060207020a0e10030209070c0203060406060602010c090b1803030705030415 83
    0x100102d10825a45051042d144a0303907000c650b0f40310003d0b001e0102c6044940c0600304904800d01008180000c0f2461f40c001da005202d0100000c440c00d0001085440a0b0344080e81c0c0c01020715400f100b1540d0150310401102005000740501058030b21110120010700307128000984c0724500504d03480340324203098036458400d40c840002003001c9540d8138802141c1001c01d140880c54140d581080500e1807240b2100141100c9021400141c03ca5003c0500e5016150780d54041c003400d081c4e241000894501a5862a0f1a40025081e000003c3c11901c0410f4008400d042540400302d01e049a075410b140c0c110f506985451f000140c540c1140b4202c0c1001e805442485402441801c21030002c0482600e280070080c020070034080404c541e40c2c02108a907003429801801c941c45480e192500d00c01800c0d441c824140590f09044400c2d41080c01003c403102600c4002d00098141807516800031003a101c0c0301606a01400704000307031001304200340010720180041c1e0341c89050740d020004006200c0b02000d8510708804 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 14873208 1250 14871958 14871973
    0xb06101715270109020708120108030301030204050a0207020306070f02072c011502120906070605040f02100f1202030a110415021006150507060605040204090e0708010b030a0b0414010501090501050f03 88
    0x603200309100b14151444d0800040c1c0794501e40ca4140c2c2030f80308059640665450044c000520f8030070000086040c0c1e4825030b0244201c1c1c540d044407005a02410500a42c15045840002c80c210b11810f02c01c1a0121b40d4811202d016070f965510700e511103198405c641003000403460306a0005038210311036004140e240c410005c1040d04840094031045103040d0086800000035240540f0743c0d500c0c060740c0340a034000801304890f00b030500d0b0420180034041d02c101e00561000e032007010340d140125800440e00041d901c402040000000203c8020b6100416106034241e68100383d641480012018001502c00e9050b100d04000c038080e00070b0b19100c18204491000c60a102d800d0000b44104054003203480030301d04043da152800c618004020702200c0d000b00303070424400304002032041940e400050759010010150b500281d118040c0c5826103401070401501036102010690010340e400b01d210703900900070b000510104003154190b90945070280e1106280d140c0796401844245000a00c40300010411002000c0c0ca = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 14874458 1250 14873208 14873269
    0x30e0a08070303050304050a1a01090f090302030d020d0f0203150a0e010303120c03021905090f1806090705120a0609050603060402180c091201021806070b06101715 72
    0x101e0300e06001c000e040080100201d0304122041024901c102d034081d500110485404120403400c4400f4414910780c0e44c28483c6040c90012988101c40c0243e4142d03000d140b80c194107465110103584100c012150342c2d0783d0f45050007801000b51015501580c5c80e207202e2814102030034104401c9500680016000200341801040000e07000202450920300e00b80000c1080c0f0440c1d03e06800138010640c0080101358003c6034000000d6000c4001e10304ca8004a6001b11448020340a000d251007584120a030302d000e22002181c12031400700c0e41144c1c402080d1818500d0503c5101c026450490240e0780b034110a91a0b40040c0441011406000d90090095005080f00e107011b4000403444240819000840c20022020850002048044401584014001000881c4000b6419000b540860420100024043c460203043d1402c0300407100d41c5a00301440011546a207400c125085090002003410f11450001101c183c442c1042d105201d00354a541c1c0c803050b04541002c0c03224807003401140c2d034070151540750302421 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 14875708 1250 14874458 14874463
    0x1080c0c0304030b041103011b020106140303030604020f040f0303050717030717100f080a120801050102100b01030f14160203030709030f02060c01020304080c0d05070b070f0e04060b07030e0a08 85
    0x103c80d007040e8010002c0d01c1d1400d2000103660b030404100e805508243e42001e0345880d444c0654400c8056500030016590b441401c1c20030001380e01220359060700108042825440c0c01e4010380801580c100e8054903044c2d85043e4440b1204003540700b2070104a01040c20b0b001d100c50116944110000c24400300e2461030421002003450308100b820318400c080c008081901d980584280002400ca44030b2810b04841d20381e081e00fa62030105940c00c5034100d00c45001301e0401485442094100d0b10117030000c2c2100c0098485500162034035046c5141090341c0c0e42402075491015000760b085c1e20701100d880c03d801e404d04401131003540f580ba10182065500030018001826400b8200c1c1c0202c81e0403d8400d2480e5140e0310005880340b0038240b05034001e6001005000030b100c040b070014102500e916048800b950b02c1c0715410358060040305409014541000d0000d0051030080c11400000a50351411032035812041c0e00003000c40744e1503001103a0464010403c10101500801c28a04c1c0c07640845400790818a000ca1040e07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 14876958 1250 14875708 14875717
    0x207031202031c1d070b0d05090109030203030c0304050319030b0910030309140301090503070303050f0708040302030a120207150204080c0103020f0702010f110102040602010c2c2103030f0601080c0c03 88
    0x2034103d03640b100850b4400030852160100100d052082d1080c2a41e00c24048280350001d00040300038500e0400414201c110510034040703656455000307941103590795040340c402500000d2040d0341602040120410300107203503480f65001c415540300000c0c2035141c8014020308800040146d03420100c20103091001c80c0d0410501c100701c4240d5100501c2031080340b00828058220031900504510020600c0410180c050704003501c04c0d11a076141030490340e00d801089501c0c01d03040c5c4000e409038004026040307071075210780301840e20303a21442c0b80546404180d607108141d40e4041580210165400300c1e061002003c24402c824110303e00b4a4103500f01501011701410520614a00a050146649003000064081d0142104541c2c0d810000c644442d600d1074007074060b0401482c203100240700d80804405800c00642c0c1400d0700c01c1d00303400000440e08040c0074800304000000340f80c0b9400000318640311301c00c4030410003580302d41203101d650307045c070704005001400a0401600c640c9600c0024003071800748540010948 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 14878208 1250 14876958 14877007
    0x1501060e0a090e070308040308070209060108010e040807030e060a0210060501050c1207030c02060708090102010b04091a060118060302040504050112020102061501050d0c111005070f0507020406090c020703120203 93
    0x3e03210030407003042031408900350f000405241010800105020b050000761840c0f80c0242e99807400d65890790011280084240583c074406080003022a0109019602620140340b180c14401401512003001900702e4009011050060b0305c00a101c804207052409154014079083c2016410041110364441d1102140008034a55000108219090510030414039150340e03009014a9600c900c241401a9543e0221010a002d0b600f0302020703002608003489103505c0c060b0450f90070b4100f0204003d00c010700b124080d1202d410045002c074010006c03c030070a031190007000c0c0c0e5100140c0d207503d00014070042e250145d1000740c06141801141c000360b40c002c1683c0e0b600005400c0524190420940103a0f85805120000002c00b4900550a05100d4011941589a60307405040b560300455074a903a1041c0c0d8021104600041c1c4c90030400c1c190781d40500d0260011600c020804100c41c1d84588074481101c080704030590050380040c0e0b0030414000030813000c00501440344040d600d0551008000a001c1a80c0c0040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 14879458 1250 14878208 14878211
    0xc01091505120a18080c060c0406090e0711060a09170910120905032704060305030d0e03070209040605070f05070b0612010e160603060e0105090103030e0d0b04051501060e0a09 77
    0x4143c09601e40c422000001c1d0b035484641d45500350300b4010110303000341900d02e500d481088041a11800aa015241147d42c80e0341c80d02c030080c0c03c28140f1580c00001034480d0043c804a20140b0100c10001d101e81d80c803171030311501c000078404850304101d1204440002480c0a00c0800c21441d0125140c2e00030072070002c001c84c01e01c2111540054001c2c0d000b03040c100000b8041d070001142840700c02c070240c411034180500440b007405440c601e6408120451c2d02c0d521004056520070800c00440d00395980004003020340e5001600e00b03010281d0089070142d10704480071a44a6500d408002a00341c0003105442000c04519119040c00e00a5031045440413002e010988101120b5140d0645510709400c04405e201000e01a90f401d2514021010b08000c3c841c022640800d08100f80400c0101c094140681200c00040a41009034a9500c09640c000e1a21107141c0e013100110000d00040350403408650700442c410001810704d14001540700c2102c002c180c0000080181100e06c4081d07960302c52000c072003960071001e170 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 14880708 1250 14879458 14879461
    0xf060307090f09020d05010602032d0702041b110d0207050108040c1205010c0813020109180207080403030215060405090c090a1506110d0503161d040e0c0109150512 72
    0x3019030304064241d01107000d101c0448030100c1c0340f41d01d07600544a103001110007400140d072100400d0ba128041d4180e012441b2240001c4224100c08510003048000c2c02d00c0700709407900140340c012600b940e010070144260510704990440a031603110003070b406603401200213015451038000000392201c0d05031181c14100f000355000300d01800010b010007001090075100d100c00c40c25061601c0c9001c1c199260f11580480d1096000461401032a488003c1041e8140d4550105d2414075902c0c40032800b64403240903510354288103d01c0000c82c036100404c00366000350010304c8035000405404442d154018083d078040c9042ca000d01c2808030700000d045a801c1c20454203071685984140703c0400520340e168281001c1202d10703000155694000312500f0006400d002031380c0c1c003000d007100290786600c0144c540c1c8040c040026040024a481203200c09a40582e280c0805140c0721039500241c1510301c80080203c1d0340e0070a440c09020303982c100d031404000309244000150000e010010180c480d018880c1000321080032a0b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 14881958 1250 14880708 14880721
    0x6030709020a020d08060916110f03070305040f090b0a0b1b030d20070b1b0d020f0306040e0a020f0f04020d0e0601030507080c0d0311030705060a0203060307090b0f0603 74
    0x49440988a450001c640750468507100a40d203132a00c6100d440030a0000010580b103040019075103120750170b2084104554101000211170b0b5010030100e09000f80182801888030050030f200134007049000c0da4619448900b40104d00070106c085030f1100000e10310b0403180d508903413100d0b65030b01c1c1210600784801d41c4440c6038004924026241610080660000244503c00148641d1200074003100300e00503a26402402c1c000d0940d58030615030068450103010000801c0030f140c00005e000d0301c4611030707071560401d0142590401642c2001d140c00000140120401c89a80fc107480f880f03294280d080010a40ea00840c0c001c11041c250a083d15401446018121040703034485070119040641c03034000070130145041203030640c0c0311002070104480a0064040000c5c8500000a40b405000401080d5420400c51641c05031191108514101d4041c00107001d20b41c0842c40600240744109501040541e407440c0040400d4105140e03600048401803030204011044d0312a440c0e03154100d03209880b903503502c0d1150f2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 14883208 1250 14881958 14881963
    0x180a0b06010201020909250c0c140d060203091c020d0905040213170109030e030307110108100b030709030c050103061809050c090405010b09011203052208010204120b01050307060801030b0603 84
    0x5d00100c0d03005440b00061007107881c0046d0743c07100b40c030044001c00c05010000038412912001e001001030902c80071440d00b40f110341c0001100100851006042c18100005507807501d003a0303082100c0c071849507000ba46030000082c0c64010344003007030800387c03002d0842c203000e1001c0a00041078070700640d4061a030105401102c0d05a824500011b405500340c04800300c405620b489000c0c1c0042101200041c400d0540610a41800001d841040d035020601c000302004000c011180128000c042c12081d140b6500c0000d801c070410001580600c0039a80c41c0301255041d8201070910b1044d035844141003500c0c000081024001c00d101020140081003c041503002950405901c1d14050600f291f0b8401007103024041089070540c0007820544060310403003070a83e40d8041c62251008070306409008244100071296204000c4504c81000c0c90001c0b140c42070301510303420303518220f81103500000401030412441d04103124400c10410f0040000302d008102c03450401c0c00040040302d06110080001c50b51001098040d80c2c113 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 14884458 1250 14883208 14883217
    0x305010b03250210020c0105010807140a09110f04030f03080601050a0e010c2306150a0b0a03020d091709010306081c0f05040e070c140c0102060c090a030b0a060e180a0b0601020102 79
    0x1300425500d030858048800d008160a101c1d400040c030491800007596041c041084042c584020202004039103011030b0440908145180108420402c109203a51001c10307034040e002950040c0f0203407040703000390b180140c4800700250403903051000521101c107000350710895024162000386024034000c00b031031805445e0082c0c0070000802c240c0000000d401100e800042081c4501c1180031140f504103064001d014900c1414011a12440c400300009440f29010b60010600070205e41c900141000003529034a44101c500001d0b02c0b044030000032218100c1d030341406450040c18019014291043c8888900c442c10302e40c20240109002001132100c960b180190140d0f00106803070400d80325036240010000f0420700c03007000100d5041080c0e0520309030300200001c0e4101ca25106030000c0c00340d41c50b80c0440d0000d80c0c21507480140e210880078404800103003883c115900030005404003191041c10024013000a0400130140400340660400c0354001ca900007881c6075034160002641a03440d116480101c0c0a0b124 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 14885708 1250 14884458 14884483
    0x30102030a150b090102030403060b1f05040503010f02090319080c010f0f0609020306100305060402040503071403010e0609031c060503190201020c030d1421070305070305010b032502 80
    0x408030420840803607542110410926110306049030a03100e40c841c107114022062070500503441403105000041e07942e84142d01c0407200500242c80e0f070401d0006400504002c4c202100011030215080003d0300b003d0050070f02c03121081009500701495003021958650718104030101d41449030128005200041040b501c107400024024404800001040c201809000e400c01d2240c6140c5140010301a00d00d20960b40208401000c4031140502c00b4812009842c01074600317035125908000008141d03608000e140000c2c00803a250049034104501010f00b1580c43c00102c0c3d00c190030035030400c20b80810101c1142d00e00760885c0710031811804842d004034003d00c040d0304103603058410341182d03085080c1c00302c104e1441c06200742d08440d24a001c0701c007416203800101c10a0030204d244648001c01c04c01300311000d8240300480740c0205841c42c0b9010005507a800c01079842c0d102083e03030380007401000d55250040c0c6000d001015002455401c14128424840c5910b889203200078000805c2d0040c140d10900c0207024050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 14886958 1250 14885708 14885711
    0x309020603090c18010308091203090604030b01090e071a0d15060503041401060501050f1b01020a05280e01081e09030d0608060106050f030403090308040e0708070201050f06040e0307020301 83
    0x18001050b26503480b000c0c003026100f006800302d03012200b0880041981070f00c0d4049490703805c1007100d4080c0300c51030240d41400300c01400140080e0341c8a48941c40604015400340d482600503514003088201103903100b200802d0740fa041a8028400e44081a821204602000a0250380c5441d00c04822006001c424a520040b0030340d08000144558404040c5d405a40100761043c500e459280300c0038200c03042c034071405010540901004121001020203480f108a841890320b07032406501c0d03941400c90740303d01403482c080744000c01c060015000011568030f800d203480410100e00042d20b01c018004409a0090504000c510000525460341100c075280b150000740e20382081a06000b0103181d180e03000140f020900603d8450000340c9404d00103011070403103525031145860a034420100e681164001003050f401c1c00304014000001440540051006180c00c2c0c075219624104100000c0803100c000e890300e000c6a0420b001e200502186203a500d8019004560003d0314240c959201401c41c01110406503165 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 14888208 1250 14886958 14886961
    0x8010b060f071703010f0509100e0112020103020d1103041a0402130207060e0f060a0b09010b09010810080607020102040e09011a040b030a02090406060501090602070602060412120e0a05100612060209010309020603 93
    0x11070030f0110010649000f2203402314030b60b6500c071155413040e03001d1145a14440c1c60b6401003120600f41d00d000c080f0640180340151622425051100940b5850810907907012400403c10040c4940c1600074008c50103403c58441a03402c0540000d0b40e11018110b111419560000d12901040032580c80001c594026105940140054001030740e00e443c0d00b00d481218160400c1034612803450a1071203241a00c5081d483d171801c184c201001120380e10402010140380d9900c0340c40108114000b00710591040401d90300151b5035a0400c04400e00b00a806410801580e0520007804c44440c4c2da100030007880b00080d60000780c0e04400e80c3c002442c25006210294024171200c092009111507a0001c4050350750a0301d880c204250790724412170342c42031036205603401600a0400303e8001b5000c40513407003031440d4526021034101c0c80216101c00f05c0310305800d81c0455501c9280c1420410500307001d140000925084100092841d1101004070034145450090005e0703400203801c0ac00768040e9000340e2110707802420003a240e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 14889458 1250 14888208 14888219
    0x110109050606040f0606090902070302010e19230a020d06060504110301050a0608010305030a1b0206280f0203120a2a0809030a0e0405040c0b0a090f08010b060f07170301 74
    0x141c0d1000e40c0d110380610b041280082880b10540101001c4801c1035460307900032454210503400039040b00608400b107540f1100700c80d650050801907082c8541c000b90301340c102010035240442c0031010744c1c1c80c084890320f42c1c1031101900c00c00c040388507080c030b94040c0c07560183c100f514502100280890b82040398050310348140f09000070041710240d4183d49050b01c80c2c1104d04e44400003078468140900c001415680100140043d4600c100440c10b04c22007450140c4402d0b201907400180b6942000140203001d02d048003400c1e104150209000e40001d100d400c0611040d00c034014002d4880c403130400b1b1840c5d0b0719144d5002c104070114075442040d856007003020287d1203030048401149a05d980d0001c000001c0c0038200495003a00010040300c6141d8030b00d49411200a1030001800007910340144240e0b0100e1a0407800100040200c008000d070800503610014441e05064025804010641040005a140010340380854407000c1c11905001e00d00c608250301c0d8000780c85d1800007001e018440014036100071000055 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 14890708 1250 14889458 14889463
    0x6080703050c030a0803062b060209030c040615050a1b030306060207060504060503060906030a06090b07020f03040e040605060d05120301050f040203040507090513060203180601080703030212090111010905 90
    0x140c91086040e1001c0310409010159140038070000a00003000400c0803e0a80c900034600307c90f4402c1042003460501150704081518100148081c0c03801c030303000101d0049500c3c040c02086000f86040b5407c1145600f0a85500d450060414409051040c0002c515142034003030480400c00c2c05602e20716030040c209610740100600764622952025114104000c20302e50f005000340c4c0c0503158259070f614115500e000400c05c1c03020f0050000341c1c02d0300410f0b038284d01090312400f4940d1b2070390188170369005500b85444006c0c606400c88215800d02d400c240700a010800c200ba0003640c10580144010a0300d4031400b0000f1000f00380d40000070054482c0601d480c1d02c10b07510001a5040390011075540d140200700300c0600c0141e110071280140b0f203400c200340501030a480340d40043e0304400741e041c40a00400480e940d1004991041da070740f844054071071300500460b0004002c41c50250074034030b003d018120300d11740e0040c1d41d62403801c0100201346008185030041c0d9100f111411026000e00d0000d01c101621400c1c03694 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 14891958 1250 14890708 14890723
    0xf20090103050c030118020a17042003070e04080a020f060a050906010e04030c060c09050d08030613090305040e091504030e040b01030e030d02031b12070e030106030201090b130305010608 82
    0x5010030b0030322001400961202040d01e049039250380f0314562800481444100030742c0100111170070300c0f6401c511903001c13155141c1c181340300d40d1040d500e41c99000418809480721007064800244a54012082400500405804550400d620160103600c6100384d150503070414803010800c4880344180c5003003004d154a980c000a000c2c0a5660507145141d80f04c2041c0801c0050231540517021606082c810000248113a03c0340380c3c03460b80303403410b030442d25185e40000d101b046104c0760980b2091408024003000d4940300c150f181601403417500800c10003ca647d000341c50740c0206d00c82c144201d0300f6040050500311050000400d04200c0500b4104503281600d0f024082d105090907c43c040c916110b000f0205500900c112541442180001d504105151002c0e40183d44003c1007401141407032600f0a5054290074080e00c1c4a40d06035502a803207141051004001ca4004013105200344e052000401c0540d8000301d02100742e6894151a5654110040b40c0350005502584000c0c43d0398600107000804035804182c86 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 14893208 1250 14891958 14891977
    0x303041a010602150c0304060b0303040803041707030c03021002070b1201080606030a03021e0106080109050a030810030f031b0203060106020d0f1806050309120403050109060605031903030f20 84
    0x8060b40c07a000220b136140c0e8a40c01300c501d0090080c0100300b0910a200196500600c1541d0104407100e0490119040d50407a03405004294400b003014010140055406080f400611004040d22451520b4000d0121018400a4007800c0c1c44d080b603250031482032020f240a0b01003240c900360307582411140908010350921841466002d1040410401c1c84d0114000784c2d510f4259009111720401d01301a00c00030440003581081070744d40c0b00d4000070300c29001e00849034410b0041c0c000d004a00301d14240034058900080400910f0040c14070180300080307404400d1404540c062901802c3e07182c900000c03003409000000c020b9031600c0707007600004805500040031025403c080d0380e00300701402d40082c141c64500d181c091141224049003024410b040c03007040690750040c040c500300c444038103125291b0446580a6041520280d44440b082c0090111500a800003081c05400518010761546440400d100720004018201600e90030310038080000b68200061507040d103206201c075500ca000c0c00007129800512070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 14894458 1250 14893208 14893253
    0x40b0d06080c031b0a080a08190804030210050604090f050604060c030b0102030415020a02060c0105010906060c02010815010909020a030209090c04050d11060d110d061401050904110c030304 83
    0x1040301400401e030000c202c180a0004d00030fa584c0720140564001e03444038855000003020100182611040007482501c0d40201101d03580c426513188082007502141e19000d041c8015a41030200080c0c2c009602540403910b640000360039128580081c001d40310710a4050144d424140c8038030140080070422502542c4609000c01011250384800d070103881c801003403039015800a010402289540000b4409442070a2050720349011080e80041d83d0758000a041c00c01c141e558a00502c402c140780c2c4182c0010700030a0410211030460b69000801ea5100200b41c5d61003280d0401c082110399024404e808080e080b03080c415500d50859010080003034110300101132051070b601000c1290b01c020340e8203d03000c1c0c442c007030722a01b890010b40c2c442c1d8007060032003012213130403000400103040a10b156105a50312585100c500b41d50ba0103641001005480c410b0f000301140800b40041c1d107103160b0b0440120b5403405001e64001ca00104014601d0207907004103884010503010000c2000201700e01030b4072250804035148103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 14895708 1250 14894458 14894471
    0x9100e1003050c07111f09090506030601120305090a15020a020301050c0313030503040809090703060302120d050a030c03020c0304060207031505040b01050103090212070f090e030c030307140708040b0d 88
    0x60403000d8842c2034803103810490081040710042020700341517042d07409020700440441109099110710038a14106820f0005e041d6403400d0007072400038015103812150450060101d94101a40d90740f540d950309a00805000c80010055000d455417001070340246201104001d08005001d0003039128007210308202d1003035203004001034020f201d20098a024444200b8040326050030b80c0c0c1c0c2a1016400a80140c5180c901808145071030381e1420103d91241d100e9079000303d0111b2851061001402c10880d101c00d4a810122211b90700aa114059507081d0000386070201e0702c1e02800c0c0e03041d8000e104e9590f4075800c9000009000c200c0c1c0b40c00081c0030302241c0c8140c0c40110a0785134165207030122101030750000e100803100d03001008598031170740201c03c9550006140b1903c2100c043d0040e40781200c0f550100c6218841140c041081c082d0310711400112140070310142d45454801c40d002078880c480101404140400300c19500c0c031006001003070314016980548520b54541d1100f55200d410b40001c80e5000b1038909211 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 14896958 1250 14895708 14895739
    0x5010203070f1e0c0507090e0c150909061009030213020a0f05040b07031d10020109140309030703020d0609150b0f04060b07020405150406140a0602060603030703050f09100e 76
    0x1000c0000000059026038160358101d0204c03010070040e0015200e40c4240700020403814190b100300c3c1c8120b82c260000b40808801d100501c0300582c80543c13480c3c0288820b0050301466120b4244a036071003a400c4607003400f441e24200c41524141c00304d4001a4000e200402040e00314001c0e40e0090600b00440d403600807407084440e00031170301031042d0300500d450002c00380031480000e405101031030034010101c1002c50038049001e021592a02c0850718090050703449820407028030032503c024000c0c010030030014514080c07030f1502007603a90f0103910009005103081407655081c8042a401050741ca5440040003484188200540001c0c00300100c201d0302c030709000300e071040452415200340c800f241d10130078545040251580820004220003403049541c06681494418680e681c4e03c02c0c140a0410001e11002c000b44060501034151341c1e0b60480320035076011000f44501c1c0d03a800401c0d18001c070340c1841c080c0c0d950204540d80d030011b030080484083d0031655000070f8040781604002d8681c2114400d0b200300c0348015200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 14898208 1250 14896958 14896967
    0x3041b0305070308030604060911030a0b010504081203091903181d130f020405010621060b0f0304030c060501060509190e130212061510030507080a021b060405010203070f 75
    0x521008100382d10a031800c0002883d200090b5511401c000d0000aa65039034840900644900c4240c542c3c880c4000000c00030400843d00c546803602c582840d0190809091000c1076644082c504408244000c02000240703000744104041d903036540c990345d03106454850900c0d025200311203018000c130082006010115068504246454203035022240c3d03100340e070b1a0040d0301c0910007101d05043c2c80c0203003070030b80c0c4038056103446c0600d82c02401a0fa864818900e2000003441c0706c61860301030241c3e103d00304117003006942c001009441e00c1081c1594103da0342e440c3c0c0c2c5802d43e034444055034024140c6051000000b042600304016025005040d03403100c602d045803000f040c1c0c18a0160040200c1740d84048081041d003d811032810034480e00c090100e0303076410b603580140791034002e04443c141c540e450039403020140c0d410b248410303040796980c0d800c050180c0d080c0600c000c1e000d03460090032941540d03030105885002e0070020300d40d0000c01c061001075440340c1c02d107420454081c0d8000c481d0540420000d9600108481c80fa = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 14899458 1250 14898208 14898263
    0x201050618040201182603070b010b0a0504080a0602030a0e03030402030d050a03020c070906031b030c03031b06020712020c0a0302010c0f0302010b03070906030302070e010b030a0c09080f01020304 86
    0x5140c1801d00c0c00101480141d400040c02c242d04010303100001c001260800c44403032001e00300c5c031170000760b910043e51584844450354000d130042c1900280316801c0020031400f00103055618030030405885244801c011140c900440d80511004e2007282e9511042c04210b90040d800340c0c003105014460042070020742d556a100c2a10003d4055020348021b0108503c103502034511345180745005850101d4225a42d17142807407070740001101c180c0e1480b040042012500065032440d07903103000ba030030361460760b12201000042840044c0512031078240504801c4c040d4100726410540c0240e00315111022400e0402001c00840322450261041040d84811440c0c101044412250305a580103a000f00c55640d0010113031a400d4120159901d8020044080e0b80c24810a0060004c40301e001170aa86103040007403501c034050b8803024480d80c003903005004600c1200d00b1130380c1c4001000c1012901550300352044815950503404004540201400b01e803101c501034005502841c003880001c540017a01010b4842e0201700c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 14900708 1250 14899458 14899471
    0xc0702060d0f0b03011d070501020619020c01020906030708100f300203010e0307061b09090e0a060606030f0b040204080604120224090105070207051c05030403150615020105 76
    0xc01d100350104522150451026810300c00c0e03001c900308203900042401d43d00200c0500c00482601100d010408104201c0140100024401044c25040140d250a0004110100801031a400180c0c00600c0380c0c3c00d404881c0070080c0a44880d5482c60202c0c402026400c05903078011000d40c1c1244000f81854582d005041a500b21044200c4090342c400d881610000d095158410580500c0c640b85001d0780d800e201c1c200c202105d90024503501e10f581d15000382100d071a8940401031160030780e801e0110641c0301f0711000a5800203040000d02c2070107090303034510f0702c4c080001c000d080341c2c10302038080380b11a45a04008240003492200f0700c4000030b124104001e80c003e40c00745004560007200080c0108070f44c0014a0f40714101030060b42c0383c107662070410b0002c11410510b25048480290140503480c1001d20854bd071000151001c1d10510707080600080300107204d1603540c604401000074440c01c1c424180101e800442d4400300b03038020006403621000c00340030180f1a4500c24090641c5144800d8018090a8440e10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 14901958 1250 14900708 14900719
    0xe090f070909020a080109030503060102060703051003020603091606110706030e030f030c0c0102030103120e03010c0909020a021005130203150705190302190e0a06020c090c030a09020a03080a02060c0702 89
    0x9081c4442076005198800050303900c04602c00700015210028428144220b000e50b5070640d0302c1ca404000039103494000303410101014544000c1081244c074480c41355082c4c07a0304031039465907a100d10403420301d480616420b0706484a42d0a0700000c800343c210b0402c0c00d003036810106841620750b40351025400c845401d54020a1500b08000d00da040f00c10120045500460782d250f8a41040940c02d0003500b2030300240c20465490511050400c40c1640180c2c601e40075a02c220002d0010000d4008010300168461240d80311280c0c000c5850807581f4024481742030b000780103417000c200030f10341705005070007411407000182d009000380b00300042c5010500781700314407400b199101c9500d003031420845824001090002071080503400d00404c920884404012800c000f8140c1e114542c1410110070400240c0959102c20195800355212070341c07685503140500d5103c2503c401c50307620307556100c1c0c0c1c0e540940b81da00d030f00950040b07510401004024a0501030290386019600312001c60741c0340300c002d8600d88120703507010f176001c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 14903208 1250 14901958 14901973
    0x406081209040603080a03060911090112050606190206010302040e010209030703030f021501030b04120503090a03030e010b0a030f14030405150702030c04050a02180d0b0f0403180b040e090f 83
    0x2031085000030000c42402510002d081903603600c0d1701c1c0454104440000020f9150b80c01046518040d00031199008404100185410f60340c60010b00b4400552000ca02e1907a02c0d01e000800076655201900d25051460f07040014003040b0480003500c4580034002244250703c0c5c282900300307840f414030035152090b0b806802080782da07040d80c406503103040e504016841180300b0140001074548004000500851061080020714105491b00c42a034210450040d02000004d10410404920000d0406002070701410001024002599014007601e59201a1a009048c4003400801c0140701482111514003c90382d4014180901c521a91240310354850b456000d24606140140e03240d143e0006c0201510090445507542c0d04a070228003911001c0360311001580e8003242c005811240e0000b00100d50408868041c0c000d442030b42c0d40300c03509001400c103101030b10b0544000b604141c01944c4503028100d0b1842c103600c2c05603980c080052298024016030160002c05408a601c03540000344206030250050083c0c0100c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 14904458 1250 14903208 14903233
    0x120f070906050d062102030c0907020303060409060608190507080606030304060f030e010626062703040305060a051b09130209010c0204020c0102040e130816020d060f0b01020c040608 80
    0xb01c3d00f18a2080d81c040703589000000e00180158075014801c10403a1881c0401036290040509203100584650300404000c010403254645c08003c8a0b8002c00444000a0040f41c034103100d001402d0310741247d0094800d980080c1c1d040003039981c0318180c103481417085907092a11390002540703c0f042036501c01d425074801c0c08203000041c0102400e420740382c41ca00e00054161010a221401d58216900807861505017021f0303224502d054400324011500041c0080440d810101d018141082900124044110030440e000c408004107008075002160414200c1c0c0c0709080503031400340180310540c0c0020040704000019555011000d00383c44000301c00416804a99141031080310182d8003040146041181e80c104000c0103903030314406041713801c28060006848908182e040000c42c04080c01080c0196500c2c061480002e24410880355228502540490494510710100c0c0c1100c804810052055051084c14400c03000960b0000f004802c00740d00f01c8845500e0310f1305020464080d8001c2c220f0f140c00011140c2079 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 14905708 1250 14904458 14904467
    0x2403030e0904080d150303020d051303060b0f0d0804081504030e0d020a05061201030506090f0a1119030501020304020310110409091b2301050918040f0b0a02120f070906 74
    0x2070260042e4081480d00c1d02e42d071326400c125070071045c1c0302d6203108000406000307040d4104806049444503050a62a10070700c45076a101d00703629840014007450302e85d486100790745c403a03c1d00300314115005450080c0c40405031501484940103401243c00d984581c2002524019000045070b000b540c2507140d46020708200001d0000c2841c2085081c3e8110104500000f940d841d4200100350200782c1d56000c950790b50540ca0100d00300400545155035a0340140c8007070b80c1c060008074952520a83c00000c41c100e68030410081030078200a9044218100c4040c01c00006210041d00154412803085083e00c00e9280100c1020b011100c00c0f146960103a002841b00f401261120350212000174003da6406000004107100d0b00d0b410000c9400120030656500b03507041590940e00c0d09a450404242042428a4400c3c00841c50541d0383d092150500035020000c241440300c0100750440e01901324a0110441c58003070301c40c00103544910103c44c84000501c00240d00c0e2400c1c64070203401210203654000340245841c40844 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 14906958 1250 14905708 14905711
    0x5090103051302061603030f0905030301050910050301020307050c010e060f0118060803070f0c060806030a031d1e0f0a0311040b1314041a0405060105060c01020d0e012403030e09 78
    0x100061030990300c2d0790159440c44040c000c0e00f10169a40c1070002c0f40d40ca001000c2d20020300c3c100660a040c1030128001070008015203040d59010340d8588003966031034054140100d03142d030140390194400006d018649500c0001440307401d0740d1800a000c0300b00340d910459513401085614128400502e40103210281101c40d0780044c49810310310104d030300d40d110306455096900a400441d03104c800c54440804010a50881400a010700e00784110903144c180c3c08680ca800d01c4030801010005200180b007288404000006600d410140c00402c02d107510031710500035451181c105500c1030728a845031112a1074289201d1040e642d0003070190850700400e100b0b10000d0540c0032105548100001c0014041065620403000b11100d9039442d2070300b9091a08000d4046200148000305110b03000041001044001983c141140c0054a04d541c0d9071b5594501d5500a01034000b000c0c0d800360a05520385c505100541040f082e540781c1001642d040b00e000c1e1443c105c41c1c20715101c000d0100b100f80076201c00516104e08400e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 14908208 1250 14906958 14906971
    0xa031404050603190606020307030f08070c080304032d09050904061805030301050f060306060306010c0305040801060803030906090d14070602130312030506100903020f04090b0f0a0c020703030509010305 89
    0xa814152180700168082d04110340b1001c0780f4410030788900700480b41c0c0c040c032001401c80303001562170043e558030300030702d13440c260586001840103203404200c6a5100d09070420341c494000340100e0f101d003010b280c000c007508001c1e21160a4022440d4040c2e0000c0701c1000f51300000c5002d51140b180070b07481c000500c01c0141008005072045030751040b2114070042c10404210030148208046d40c1e9941c142400c0007500c4600a03100750007003038140700f080f5860f10380780c1c1120340240c002d0030114100b410501e0115114441da400043d042e500340840010042800805180194010020396010f960b130164455521140b01040500243d55401020304001041d0300420b800750054001600d0010750003c0d4907823010b84c03644210703401c1e1005186906145c0e854800d0302e401890884042c2c0a020255600a006500b1804083d1191484503a07103600c0340e440794009a0400e510007c100e08900e0400e07454824410221040361000d41403440101c0c03154408070f142c4081d070f64180c41d06c07410030581000440042c400103000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 14909458 1250 14908208 14908247
    0x50307110f15090c04060602070810060509180709150503070b031003031b0618050105100506040b09030309040e010b030d0c12031e110306010e03190303090c090e0303040c170a03 78
    0x140c05132611079000e60390191200e50000e010f0030b0701d854580c91408040d0941781801a1420b0b0040c0595a03030380100c075401c030b11040740f00c9000c182225200c5040030156446145504d00e401c54003000c2c0074040e01000102d6104900f5200b0590303a0707202c04020b5100444000c0001941c2c4a0700b400003034081d81004040d50b24000800c000f00d0295950941202e80040d09849400c420115140c108182400340c981d0080c250050000102d103000c0200d0600d0007580145010f5072804100112180c604206465120000420074464010b51000450080501c0b80a1700c0c0240208018507070380500034402c0d01c42e0181e000e01c0c02100300d40e2114007100203151007420380703500303804e1421000c804e0000d600951080882095615a07282403200000d002000c4c050250b0b8001e8002c00340b8410b080003034103160052039406003400b1413100f5003454000075040c0c035500207001d024580ba80c4801d501d030b000801356104a200341401032680d0740318446048013050000e1050101d1340f20702c0384240004d210b1940403540e22002100e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 14910708 1250 14909458 14909473
    0x2030c0702011803120305040605090d020703021507080d02030402030d020f07140a0e09100506040606050304120507050a0c060f0e09160504090c08060a09020304031b0215030106050307110f1509 85
    0x41703940c20444400e0705100041d03214000e100c00e0040b580705080e004920754000740880e482054010352209001d22019218540b0500300d042c0c8118010215039107198403840d0130359240d4440800314000c0d0001e0714240e02a12509800f01e0f41d4600000e10060903036444001440345501c0e11000012281c03201c0c88058000e0345200c800910034007400c6030700380564450006040b4400014152404460006160301d2040742055010880d6030b8011045070703001900311101d02e00c1d43c07050740c2090b2046c0c0703d0418024214456140c01c2c02c00d004941c151803041c1d4245a5888608440c490b4045400c602c41010903640200d41c800426000030340030221000f070004506215041542e5010f80e001102d103821420f9000c15003100401c001c07441d015100c1c00150401860450940c14203450007001040700784100703000145449100c03000d642d103440e003442d507031555041e440e5074035031311020010b05a4000391141c0340401c41c000442c14040700003240342101d0b90a00d03001070030484602c0d22200090180540615428025000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 14911958 1250 14910708 14910713
    0xe01110c0c0906060405010f050310030503070b0a110909071101290901050a06050f210412030e010509060c0708040807060503060a0e01050d03120b0a091a010302030c0702011803 78
    0x2029250800d540c00181100900071400d0084042c0300512061255204110900041c0e803c100d50307105c0f205162a1281d2255254000412144499040544584004601e090800880568880c8154501041030281007080003040030540a19212603a00005400000e489244210b00d00a140311348000045407162610442d00d078141e500305840140c800700c42d122034446080c002c154500606058490442c181d00d0070000030064043d10745882440c1000007608903924450400700b1200d208005113240d5107041906e440705030b0076a8809450040307401d011001e900c001061023414410480d0300c015000c0c558694070110301d02c0d4010785085512690030310000c01d08035030410602014200c00c0c0c41d0103a0341e003000e00030481c0002259100405415040005009944030000185a4154035045c0801d0141010f0900d0001d000805004ca410940d1078200064242c00b5803c04045418010310640c03828402c0d80c0110143d20044400304a030010801404005502c030320382e46003541445652826081d034596 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 14913208 1250 14911958 14911991
    0x60f130308030105041103090c0f060705010e03040608090a030e01050307030608010213050102010b032821020606010e01021504020603060301020f03090d02100e102d021803060403080a0e01 83
    0x80d00107407809200030005000a0600c0d124440e8034000400e012815881c11184143d90780b500004990f00894440e100403059032580c00c00e030341280794450000d02400c0700b10000300f9900d421034030440d00050001d04c04a250624017107084020582c01d903461041e800c91a00064940741d0000c1c0070720040540d10280011030f10020b2028104005600603561b202c145400002403d55a1140003030b03210b0b80100741c18400c2e0240d0300086894000300d03c442014124442d0410f20f0500c1c102e4111415034400c0304100d6042d05501090366403091100340c130741036400d40354140120b07690300718071030b46540d02c4649101190240c5414400346601c100d00074009450415042d804641030340054401091660003c100e1a080c242c051008010130320008a041040b6000d0158455568000d418a111070707580c2e0311081c1003280181008a40c0e4543c041c0850303d6181521001c0700f0083d40f0102c80d551102850f0041c581541c83c4c00700b40e0324041c9030035559000c00ca8603543c65140c0100324060031804290350702d044007030215501 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 14914458 1250 14913208 14913247
    0x20a030f112b050c07030f03030f0c020109051515040504050f0102070c03060609090b0105040c030603060e070501021203010509190b03100603120c02060f090f0d080307020f0a02030a02060f 83
    0x1022403480504102d180781940d101c2c41c412240090040601a41d25202d500090500c1201d802c2450228000c140307040581c001d24044d1610520107003021120720304185c054102c1841c0512036012545c00700140c1c0c040340d80110701601d4165a0540b101d00c0810549030640006070011f01a406580c4480e82e0007080c64226032040100300c480c00103401c004c00030300542e40701380801481300e080d003070021a000e42e0b15864165030500640e48680d540f0105080030502c07980c0508081c6900000070420107021441182d564841c40c441c0a00620481095100981070742007138038101c032409045000700d501c41844a1448456001034214815654a28101240d504102101e40d8152a00c4002005404c0d4181100507581190319070040c000c0c0b0510307000058a030b4100311b4000d48403807070455440d03421001c0026619607020000c00e1b8400c2d40c14031a031342405101d400071400f40c01039030215082c2e5030000e100c2d15100c881555000e5819041404024003508195000f011100d4900c40c0c603600d4228100385c0c0c82496600c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 14915708 1250 14914458 14914483
    0x3040614190806130603051903030912020105150d050604030c02030a0803070e130509070e060a05030106031b0f060905090a060902030403090306110403080405060d020f031305010c0807020a030f11 86
    0x2d008003030000c0c600b048103e6a00002419105100d80b40c15a01c942d9a104504902c86080040800c0f20f0401d042c8a40d2100404650240303182000022012000340a0301054a20100000003c003c5024601c0c20b500c2c08032203aa03000c005402c1a9035607840a0f075845040c41c200340c0c0c01d40560900c0700c00003000b0900952040181ba2108000c5441c0e42d801d21469034850001e4480e0f00340341005000b1081d200061003002c0f40da4943c41003007d0355400300800c0c0c1d0030741d1582c0250380540c2003110200422180e01d0032030042818000440c040343d80d480441c00c000c3e0050b4401c90000c00d00c2400c0c18840c80c00c185500e40d6002210b0000480c019546282090499204503010341c00034907001014010803a29010340c01c0205040c00342c45003880c1c1580c886003400d204501c181c601c07940340000c0781c20130001e054040e00e40255250901d6600c92521390020000740b020001d0071251075190031100c0c241d181c080c490703681c0203c1e4194018a00d50141c0d0760240c030603d003400c0300031060014401a181e0b4402040000d0700301c0c2036 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 14916958 1250 14915708 14915717
    0x1803210207020d080f07050313080706092103031503060b040b0307030c12050a0c080309030106090c05041707030206040e010f0602010504150b031c03020406030e0106050f0904080702090408090909010b01020304061419 95
    0x2860800d102d420800b003900310f101004480c040400505141c06084022280c1007507492a43c0031407463f084d801400c034181d02400d003101749800001440040e902070518240e05a606100c00c40d06081010703201d1005010050000840500500c00e0301c2c013161201d01c0403032207541151301061003510380001e001031a61151801c1e910008910300316041c280a0b034402405280c0003401040c101400141c600c0c01030340620200394515031000c441c0504d04110001c001c5d82c02802c0190340360b4a0300e004110f1100e00f4000c81600028001c00003032214070510441c4d110300c3d00051070f005048007202141010342098184194540f00c0c1000c91060342e08101480101c00c040e9840042c1d94034a042409801c4e10510890180581d1400400304820340300c00c0f2030341891040848070780c0b2482d9114604443c25001c0c43c0310103508003007850100003c101c1003100030700313580504413003000059036480c00081c01e0713507014104c01d07005800c00d0100b003003018000d41d184940c050140403018140b20310760054040c42002c6d0003881d00001d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 14918208 1250 14916958 14916997
    0xf0e040f0503030c180a081209010201140c03070f050901050d0e01020c010c0f0f0806030601090c1407030c0b01080613110a1710050f090d0f031803210207020d080f070503 75
    0xc040c3c0a200518099060300c031a1b40451910301c550380c41d18105225808000350000e160b6405030b200b0f50103003141680480202d019810507a40c90707103282e04100e0703400300030032002a01420f000b40a4400d8580300101691818605182c142801001d0210340c0b104030f41c1903400b40243d2040321b400380918464500c0c1c5544030604031000d5030b401092034051180740da003404010b0080c03000948011904c14152181c00c04045149481d4a0007100c201620803981403103240c01040400170198400445510b25014004150b03d036626036180b503465010a50300100d6000e0402c070302c3c03400162002e655175854036004201e40140f640d07801501113035005c00c00118100350006003044400d00380600c152030700b003200086074a610341b402540c02566006241c82e840d09101040600388055442070b04442003181c0b60200c50075a54080d4500908502040e411818a00c070b002401c90008940910903103060540003000ca2244d0398107529038900c0780d48003800303000041500f00b180001141c0d007000180841028040d920182 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 14919458 1250 14918208 14918227
    0xb0a05060108060a140405101e05180c16020a050a0605030103060f090201021203060a05060403030305070210020a0906050705070b03160318020904110d0203070f0f09060f0e040f0503030c 82
    0x81c002c000d046520501d0041e40034000c9a80003c0d40d030b40069029600003c03140c94a4140305c485040c0c41d0300601c010007030094040b8610010a810303000303c03401600e0400c5c00034204d1f4504450441d046814280380d036000d002e08032041c003020000230130050000e8600740b88a621040440c815031455084035002c16400001041001740c2442911440c0541a43c02c012032740c000d42c0000d49540e03907041241c02264012010407440da840030513903801498014071950351035580749400341c09064211102c01c00744c020103007000c0007014140215001c07900b0f15030307032140518248035003540d0070b0700080016516803040042c0401c030460010015130007080900c00e04007c10018040c01810b0f90701d448081d0510302400700a41005031100a40150065071014a94515840d0174002c030303d040c410000041d40c54441e130440060380d0810654400141d07448040c0c010702968884110b482514000d2054030307004038402e0710421480014246150300a48035603004105594182c0f18246075800c155034240d82001e0000c2c410b0394 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 14920708 1250 14919458 14919467
    0x60207080109050c060c010609050103030309050105100501121508030403030504030203070605120103060519090c0f0b0f071e050a050705181302040e0c0310090b07020601030809060d090b0a050601 86
    0x1811044024080036030741d80d60f10b94488003050621030281c0400b08030012a06020b4000d000036209903c0100b01075a03490a005010b002a081d0559940d4a820082405030045550030403d9500c1a1119141c3c644514000401800005401c6a01006012011038501000d0005000840c066070ba11521982140101418158950b00c1003092000810520100c60351126070141165001000000c05540d6004030310315014107a003100342914908a040810032250072001c90941d400b001007811031a890380035074481c81c40761100324100d1030703401c0c4581ca0001c0d0700300e030040e59600b1001c92603840c01007003079550a00e0100070060413a05038124010520160802c01c966a00650b00200c102c1c5003400c103003130f40074502d5a5180c400f90003035888140b004040354080201d58840000a000c9030000d04188525400500400500725007124144021685451000074181d0680c0e820800f482d1420045030208100d0382d108602c0030003955240c00f841000305002e0022a4400c44104201041c5450442e00050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 14921958 1250 14920708 14920723
    0xd09060203030108060a020706060312200a020117090f0a08040e06090112030c020307170a06061409070c02011205070210050c1303020f0402070804080a05060c030f040f030309080d060602 82
    0x319030040c4010481c0e0600001c8058015910100c016a666658144003016040c6500090481c5000a03015841345901c8011651200c41c484122003141c0701d210456500d0b001442c8020340003c103a403079032000714440001c42c20741110740c010813540700030100e1440d2401d04a04090980e2480400300e000c104140b601500b1a80c010b2085510b81c42d690b0400c42c1d041d08105801a000c0c04002c0803241c1e9600b192400c12050024100e0f10080d01001b0034a0b203481a40c850300344000f150004e040c07480005210002e543e91260703108006204016a688201040710390001c201c40c26030400000c0c01c185900314103244101800784c642e903030150400310310724565007081d9240034042c1800910308003e60781150742514400c01c2a240d0450365043c4400d114000100607024208001c4c0c441000020b0002d101e44000a03030a484a2081040d01c43d11307601c8045203041030004469074490010040001000504400d08400880d0302c44e06001404482c6501c8410301900309030134100701a0382e10341c01480040e80400c50300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 14923208 1250 14921958 14921969
    0x507080c0417070b04080106030203070f03081b2407020c030601030305030a020d0603050f03040e010e010f03080307020f0d0e0112050903040e04020d0605070203090a050603040b1f0e01080d09 84
    0x4111600305800002440e104500c40e980440d12908001d12000d001405864010481c13010720503196a11004007038001d00750391008074441e1161000c0000c0d074880500701001141c0c1c010118905040161101d034610742089861148140a040440c40040520026003c50038108c030940c1c1c4094504440040d2a01491a0103d842a8442c000400002c0d40c000102c85c0d001810000250303c440882d6901009041c05800003042c070300a07182ca00c000310000201a03c11101c1f101c082c0300d160390340c030700c240c0c0f4002000f0301406841001c41d60041c00071540e024004c40c1c211403144112201c1001c3d03900b80c00d080a0b0b0400703880f00001e00405046c0410b681c8100100700302501c40404010504294511956a10840c8980c1c401260b0344c4d00090306540c0c1d000020083c5541111040c0100e1801d02c03002512640498403941c4943c41d600300c003103400c2c00c2040070740744150f500105520760b50321002c045091300c84c141c51811141190001c000308210301c0a4004134000d000140c002e00e22902e203064064002c1400e504031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 14924458 1250 14923208 14923217
    0x10908090406060e10030e01090209130506010605070c06051809100501030605011b022106090601090c050a2c03030c060402120a0b130606091d0d03051303080c09090c030a0507 77
    0x2c0c401c02d6175416a5907000ca00b0181400200250940da24038007601c600e181c0603501c22401c0341040803543d5540d042442c464480d50984285a0325800c050b102c1e40504100500100f812100a206050180004040c84c04400e40208217900181002410782c000807100044c511002e076004000a503014098036000e00f2007400c0c164100320851f549031482c03101c0200003900c24007070310103000039200171407014890882c1c0d003000341d603228a00746400070340c0e9079803c2c841c1001c22464900c10b00724081c850401c0e00e01c03601140e40c0b00d1096007084011864030343c9080040b0500c004100f0703c2441c0981e0100014801c0c841c0e100c000c1c1c0424a414010400c1a0403202c4140c482508001c0e201d00c00144102601a03000780000d001620003c01c5003016802880e954010f8071982d46064000503e0310701c011646410310030004101c0d00440c3d01002c1c2101a502c094440750301545e807003844000081d0107504002d5005044c10842c070305004803c0000f51040c031007542c2081180720000309100ea001d00900070300342c4c480c460b07040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 14925708 1250 14924458 14924477
    0x150f020309130515040c08010305160302010816020c060a020706090e0112080d11070b01170109080a030f020c07090204170604050a03030903050d0e0303092505010c05030c01090809040606 82
    0x1c01c0750041d9001c2e01100007595000001e18511161500f00000c00f00504100100c800030306001e84407030000c3c04190703158442c601d21112003e01c05000d01080e41d40c181c0d98910b183c1c480011090020205100ea10154040c5c43c24092180e219580503141d03103515035006004452500002810001190700030350982075084c001403002541d00610962000d5220500c00d07523901890142e80002c0000e066410303050b8600203180402d01c00b0030003101c0d050f90203800c00d813040359844801c214222012100007d00c007000038031101244c140030ba84a01c62030450a400545440040f044460a280b0350780c01c01c540740f0b80d0210782403049141d6540c50f5038078400c80030001c01c500e04240c0c0301c1c1c9a58012889006080640300c03641202050300c114261002c8402d19001400b00c0200c0807007240e100e400441b041c0905200d100304071610140c0f0440a80e60948060921088150902c001102d04281c0c1d808207903035610003004001540038092040303074a0385014150721510f4002420810081c2c80081d031244003003007a01c45 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 14926958 1250 14925708 14925727
    0x120031e030108030405090c30060904020102070303080c0706090b0906090304030809061605060a05070f02011404080a0c200a0e0f0f0a064217040606050406150f0203 73
    0x8880503103008841c07e0340940e030f07090309811141c8290410360409161040d004214464040300c004007003424410409960366604c4140040700800701c5000c0c0c0168459402040404c0c01125502e400c912021400307440c1000b11703240d68013074a0440308100c1d08400c0078010840c030f040c4107110075a00240b0540282d807400d455a102e0032814064141d102e44603034000181000e013540300e240c109060700d5009064681d00d02d8175500710030003404100d60307590104800c9a4400707209481032144001c000b800004028407030315507031200041c035004805100144410074664001150030740c409641081829500b900c0380c0d03c041014070102c180c0707980c410140d400d02901031055080314003040c103501a80c0c0044407242e0b07a6400b0401d9024003c80d42c08a000020003201a4482046540c401c120740000c2d11501a0742640c004003222001c1005400103000508401c100c032851803180c000140c000d4000d03003002c01c440da100c80000d0119030241d40442040c01080d050424095000300058080c0b1000307001071030501c0d2071403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 14928064 1106 14926958 14926963
    0x3050904050601050c0318060702060310060e04020f03130606051306230d0206070809100905011d010f030902010c0c1e080102030c0a05090120031e030108 68
    0x3070000703051540076104a5034010210002140781071085014503d90f02602032060341e0080c2d0400802000d0b0792100c01850241503040720320003007140741400c00351400001041c80c42c00f80d4010b00c00c1c1c1044030300d81c02c280d9600c0b120060a000300f0554515002004103070640000b03030f00024240c0041c2003c200361b0b12450036141801c4502803141403c0d88040700e030400e4000e0340b9a100f41400036200040c2001001f910107244503510710f1b81009038401c000740d0501c03001400040061240a0100515a03110082940350030507d018083c03464410000200207001b8051040245521882e5040c21644074145104000390410744c0002625201c44120b017204c91800030a0401c86012400030a2024041c42281c0c0142c82c4c0e420802d00c0d00401c05000d490b160048500c240c188030150540304114010340c81c40c0160003000d80041c42c0c0c0c07500101a483c201d441e2081c0c0380d0104e904180b0040c403490000 = true := by decide +kernel

theorem cover : BRFrame.Cov 14748208 14928064 := by
  have h0 := BRFrame.cov_init 14748208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 14748208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 14748208 ≤ n) (h2 : n < 14928064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
