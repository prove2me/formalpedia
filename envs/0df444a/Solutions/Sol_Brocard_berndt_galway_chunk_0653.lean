-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0653
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:56:56.510316+00:00
-- url     : https://prove2.me/submissions/f206030f-50c7-4c81-96aa-d7027f09a1ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 117266187 ≤ n < 117446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 117267437 1250 117266187 117266189
    0x4060b0301090f12030e030a0c0804080d030b0117040b010605090f0916120612020418080301030606030c060305040b0f09010605060c0f010c0f120f06090513060e1605100504 76
    0x2030198a031104000a00c6428001008294440c105800b46200400002c505494011003002102c3e042000b400d08014000c0700019000341c0720341e1080d030515035264186030034100b060321018082074403121000c07919a4000c4041c0028202002e03151203505013911146080541401210140507002907408260360302d411490f40030380c00080c80700322185001c00503c1d0b56034094905850104500e2040840351079180d000301e1059a0000a028200d141d9540812000c0e040e00405525044005030b000700104250340300850103180520f1b004241c01d491460540d5040d802076018000705441c1c64280400030707460454050300b080c1140d8590035907480c1c12203103d00401c40307070f0320059104500040c82c000c000341c0409d05440104115008001c103040020064030341c4a01c80c002503000400c2c2c4092107160310915130000b200b84020490016044e03885a0001c0c00b210300583e00b580740e030070410342180d08001140c0200454044110302031304013810700107507900004030107010b200d11400121446007109446842554 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 117268687 1250 117267437 117267439
    0xe06191e050603040c03030e01020c030a02090601050f03090f160e0402040b060405030703110301181a09030d0603030c0b0a110f0c150f010e01050607020105040e1312050a1b05030405010804060b 85
    0x1c1e90307900f0305185c20b040651280c407007200841c01182400f1201d6001103070150f4032500c081d01800b584003e07542001017141c0d004104605014091040c2000d9007440d0001d14410034030300b00182110a03900c070350140381c280004100109025a8003061024180d44d84006030480d9055502003203501c41000080e9244c015900716540601ca250000000c1c00402c00480303a8415040d80200403620b4000440d0780514483c030009003800c0802080051a518005c040641c4034070a503098a041c0a004042001510220743c4240d00280c543c030300780c0043c4800100c609400640300700f0b081115442d002f00c0b0103400e01075031102000da8400420101c0109209000115480007848000c01480ca4034901d6860068401c0c000c02a0b1407541100100f91403c0040c101c03101c03182c05865850409140442d11021200010324a01d1a40d100d01d518400094451744200484489501c4643e25040c1c1505c00900500c074002d80407a00d0506c080f480e4001c0b400100c215410b4078400e1804111a9840d42440e0001c0c0442d0036000d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 117269937 1250 117268687 117268699
    0x11090a0605090c070c0f050102030f0c0c040510090c030b010818100903090305060c0301050d081b0f01021806040f0e0606271c021f170c03010e06191e05 67
    0x4400c000004c0a44134030400b8003034603098850010041a07180c50041902681c01044030b000c40d2024040541584a41e00c002c96541803002004503041da501528050085280c0d07050a01005000303010700f4450020501d41000740b602030800080c0205000342c009000c0700038a042021b03103400c5c140440301550a06035000e005c0c0e02c080c0c0c6001007800340d040c802584c680c0101c4011495031040b00d411a81241c8000b443c845070441c650316041c0701d0340d214051380da0010243d12100641090140803e1020082c0c0c2c3d000143c0714402d07400c199907003074049103e96204074000c0006110052041d84680256078100c00c41741c81542c2d4400c00f00c0d415100c0c0b400c80c951803201d048002c0e401120303000311808462800b42c1d955188502090664a9040b010707040080d131050b070192403100001801c040b60401e001040c904440c0310715954100c07152030715007a07a140c001400f002005001520720145016000780b41543d0340952403034080260404c3d110540030744008040c0302d03901004e1000410041c0b1000c0c04000b018 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 117271187 1250 117269937 117269941
    0x8030c030702100219030818010e0609010b0d030c0620040305032d3f0402040513020a0905060f060c0a020f0609030312130501050702160f0311090a060509 68
    0x1040365603030000c0000b00d1186001100708110b15101051200d10041c40568200c81e8443c0d598080d901c25074014131640024500310188203e10b113007401034035450810700001d840c0908100c0001030a481d0381044c2c56005090000880e00002d41c4400106d5046411060002d03403114403400110300540400034815100e400400c01001b40074020000f0701205140000b6503180d44007400c01c144944c2c5030505008a00350b014001c41c4044840c0442c0e000000e840030554504580c0801403100c0c1c0805103540e4107080400540c204400c5003454441c1c19040209108440700c0c03e211a40010324480079405500c2c51240c8a00203e000c90701c807048000000c40009145c581c94540500c1450b40d0380091040c264411808400401d0036410514225000c440010b0061490141d40c11810f002204014144052030b001107007581d40424000c0c410030b070103003e032540605009003040506001040c80340d001510350300b040d60000c20000721001545c0310321003001d8880d244107075034258000005046681c4111342142c00041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 117272437 1250 117271187 117271207
    0x603060d0c03030504180b0a050d03030608030d02070c05030304030b190e1c120603021507050304090911090108030c030301030209180d2a020901050f0d06020d0606110c0d0b09070803 80
    0x800b41c0203517581c686200410205810f81b5000ba5080d1f50b1074a40c004e4417046c424441800c01060003000c1e54000d04003c100550790b007105c549150701401c0c403050300f564045100d004001f0240c14000c018441100114141815070321403c0351400c0c0640040102c002541c0030440070400740d04440001c072034a01c16180c10b00c0d003222800549500c0c502541c400500e0185d1080c0c0403042c0303485640d06882c4c0140a83c0e141c2140c1010300030312640102016a01884107120004004a81d8041c002d4068800c103a00890114074005114078040c0c10b80004c0b00e642c005003c2940b87c0040082171fa0704683c0c0488902201e5250602001c4070213504440c5c0b82c6a5008081402803139680101e008440884007410b205079100c0c406450004594030040004d61150b1508010445860b2040042e08613080003881001000c5190795804201c2e400480b81c44140390312000c08100c110782208502481000103801b526029850400103203200c148128000d055000c42000300301c11080810180b000340070385000f102d80e60f0050304 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 117273687 1250 117272437 117272447
    0x120309060a050610120c120504050703030f021209040c051b0616020a0506040b0709270f05221110020a1103030a0807030f1e0c0e03060c07020603060d0c0303 69
    0x1d54030119a42002d01284081c14900d410f1003089542d41e454514800240b849240a0b00c081c02ca50010000e12030304214498400f0701c22180036030b201c1c034020011646586005440140701100303000a41d00310750f0300421455428000c482882108690014200501f002c0030f031414040c0d04034035405000b600350465048040001c2c4107029480d00c0d0700c25841c048401c1802c80c0c0d581001c5a0080c2590030010210b000210304100c55a041009800c1810170341da1140318030300c0d0000e0007040b1100200c2c00c0c145244c1c00301c801449070078540902e0440c1480305141c40a0b0845602c1045141c031901464019811404e2100c007141c001180f80e030091a015102c2280403000b03503203121341c810594040c41191600708241c9000000c4603070070f918580b030f903414954404409500410840355560100d58485400c110000780003000c5c3d4107039030702010f0001000c2c29440d1000f003d10403000c000a000750702070b6040c09200a07544003a1895968100d6445541c2c0c0e82e848003151644844c2540200348840c400004401c02d6000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 117274937 1250 117273687 117273691
    0xf0207080a0c0c051f1112070b040c05150909040314040b04090506120c0907020c0607060e0607020a050c06090d0204050c03071b0c0515120106030f06080304080c040e12030906 77
    0x41002e003611036180c0003084041081c1940b5140f408616181a000740da0240041c0a80c0d40c1024051f0b40300305100d825051600c0d07000c072070b04580980c0d100040004010b01100f06a0180009036020b881380304002403a40e0f2640704800869114581c003000040c205841100c580d81006400101c0e203844d5540e0340041070761600680074070b01170301c0e041200040701400c00035030400072000084000c000314020007091102140c03010385204214040d00e01244100d880701c80060521a00c190740010b10828003006890602c04040d06241c00c641004c9640710100704000b0305000514012507049682d001c48100140714102c64210094009003444204126610180043d611030189034507480d8808808450300100c110031890000c19030321090000740301900700198501240c82c20483e01d945000707020030712600310003401d82c00f960010f41c480009103986800c9000389801040a00015801d00b4108120381e0f458090b0782d03d0320b0340115074425010f4000d400c204854804090170304060380d03403030600441264a074402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 117276187 1250 117274937 117274943
    0x405011d07090b030102130b030415140a0c020604030f0e041e05010806070c05060408030a0207020d05160f180507030b060c0102040302040501231e0a06080f09010e0a03030f0207080a0c 81
    0x240c0108000f0702e0070107008075000580381683c581303912404c08810019540024006071041182100c014024124034824841000d41c1c482802d02c580c035003010004155406920464115041401404002500000c807a0959410307400c25590307600f410300c040750050801c0c00d00703964420140505a01e06601c0c650282c0e05a41c14101964581e0790b56090503180f80e200d130790004004e9071285c0001000b29004801a640000b00c20a0152030070040b5000208459420b1384183d8458010f09069000d50700d00c18160002064031055403101c2e60b14118120020714410b2841e0b10070b0380d442384000717012188245c1c841940e1440041405458542041c00c0328000e40150008034040ca01e403000104c2d1008206101200801c2141c610810340c46140b0f080c0b0000e40a50603049180710511444401f490307803902c03044e501808070b80c0e49200c500d02c0c0400d240342e000800517010303e02c60b9141c40d807085103800d00030441c040a07035003500300450030b40b030400d0340c99009120b001b0000d405d0481c003048603445154840d07010482140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 117277437 1250 117276187 117276191
    0x503150604060918020d06031b06020d0f0806060702090c03010608060d0803071b0203060c0a0806190323010f020405042004051e030109060c02070905060a0306050405011d0709 77
    0x1004010310200e489503026034404203148070000c02c1060301c00c04074403078001505103000d418415421601415222240c204442c000403580310580010501581c50005112510050180030020303a4098890001c0442d500b08020305240040d4076501c0d00d004544c0c507a039000d003c80c0c0c042d142481c100d40c8550001e0260350005001540414001d291031855003c966410104891840d200c800d4240c4055032140301140f8854880d09210015907420300c1105c1c400e0f009111065a03c0021440c01402c2e83c8004040c40d03c501040d03800c02465240c00101d0b241038940c89880d41035407078910744c0703402403c0240760071001c81036007000c1880c002910740b80c001c0c00840780203481c00c0c0a20404e03c0d40d2000c8a40c0b59a203040c46100e000d100400c420310300340ca8030720440803039060b0703100008070400040f078207413505102c050721144d4954a5103d030346503040100c3c100030808010100820304201d000543c6010480c030014013035a4956000c581401400e503c100d424101c10108610001d03050f4064544480041c401c0d00b16241c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 117278687 1250 117277437 117277471
    0x10f020706050f0d0b0d050c1005040b04140102030c0703200102060f150a0b03010905041a010303090e0606190f02160f0b070c0305030d02070605010902070201080402090403110d0503 80
    0x2400000c005007581c0590715901e0030700240300390322040c80c0c000903070b0b15410580390381014507562107000c172030b1000c0c5001da00035200645ca24018004680045ea400c2c10410004000800c8401c2c2084180d50960312842c0080001c4031110004170718600948ac4614568040c0300c06c0082084070b241d400f141c192501d83c081c1803200541d10016038940f80700300c031941d0f2800c4401e000200c3d1007000401882100700700400100c40c0075116003401040c4c0d00260000c100c041d030344800f4030041c024201c110504c1544056030882c035a42c1540c0e03006080003000d125400071440e034080072a1156079280140d41451820080f281c40725400814000c0c21701850007195400341c041c40000d000884100314000701600c024000218040e454040441c8455002800c1510f14800900300800098010310041803500c00034407000d40c4840701401c10400b00c1300103a03c50b80c03455204004590042c0d0700007d200e03500a070115258103140d0b856080a8501c0c0c03036905102c0181d409402414981c85411802031401481031912200c00f20f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 117279937 1250 117278687 117278717
    0x10b0d060614030f0c1b06180a02030304090216080a0507022b02010e040f020f040306060f141212031303090504050f2e0603061404092f0907090501 65
    0x1000d184010600b1001c4208000340350f11081e000242c0d000605150001d1a020110b40f407009201d003505500112034002d601444103013101d500e41280d40c0c00d60344001d00300760211a800640d90b80300703038490203500300e80104106440c07002500c01c01484ea41c00a24441c0e031118020b80c0100a070388802c0f4200d00c580d2140c5800b0522032060344508a0802081c03400741d04094140e001541c0c4e5030700d45100c040e80207844400480001140d800a804181e00d80d2855136195415894a5010f030380e0541c01c1071541251000d42001003000c0c210400c4040c0c8401d8030640400108000d8007402e08145441c41c44000300000103004141e04591a2800b1860203a50380c2c01070b0686880800095440503108040d000882d040402c03078604c0588011402d01c00c0030650708032182911213801d1401c503226071080d408070740d07a00c0c410800c2002e16003408003441340c05c4400300b1651250356540c1070350180e11240d8403083e0055120445170b002070740c4450050b208005140003424a42102c6c0148080b01501941c2d0000e11240c1d40c407190 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 117281187 1250 117279937 117279947
    0x90102060a0e21070c170f010510060305090c03070e06040b0a0e0a111e0901140c06010303030c1701091d0706120b150d0501060207050102070807150314010b0d0606 72
    0x4040042c0010300243d606100121540c0070140b850180303404004c02222001132407401d102c500811060341900807032a061800c0f5400c0520000500149034105000c03c4030122155000384141c0741c15080c005415140c203c0381515061090300344941611840e140411386100300940d072313441040111810b120030117003082404180c4807244240300302581d000003c03e804c40d140b90850316007031140c12809420708061071403034030300345134050460341da07001c0c000a4903101542d101880320480d42e660316a051601c0701d802c6040e079850b50148405010199101d40055840b40318603c00c40e807500c0e03907103031503031031940c442074001d0081040c070301106100f8009000c81e01c0c25150220f114011900e1548808942030545031090380a0082005841d43c800d00c0f25450b82004070070070b8060309140c2002e100000b0598100240a440c1c001d41b60800e9041d5801160704000741d15000500c00d064800040d03486e641014000015405000300e42d590705840850300002041003880f11018008081c88004184880c035a10001622 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 117282437 1250 117281187 117281201
    0x30e01060801060f03060222030b0901050601030603020904030c06020415020303010f050d0c0303030e07030602070b06010207060905100c0512030c0c01060504020301031109070207030615240203040e15040908090102060a 96
    0x604100110003000445c0050340502450403107500301c22a05080704400c42c00b50008c5400450f9020015020300080700d1003481000e91210080c01c0402c445411500000c443c0c02d0300610060800c40404548420022960152801011101c0700306080715400c04010b500e0740c00c00d0090342e6040a640b1070008180ca0070080c0d0614254101011811103400c0d82c404178050010100d102105204150700080000d07000e20040030000e010358200d98040c140f003800281032043c0c9512003010401846002d00003660740c000d014410802d581407008900005113020350502500d082900146400401040094120310f00100b11000c00c84008102d20350301d60041104078042808040e00451410000001c2c034200207405d160007003c94012035003610755a0740c804d0241e909068070103040f21701250040003200a0103d41d10050f0268031080b8140002000307009643e40620b00c2554009030381c86000c141d068105032900307215420098018001c00c0d2a504141c4100d0b0700c00c00f0b0150041c40340c0400580c203240d66214400c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 117283687 1250 117282437 117282449
    0xe0703110a0b161407030c05180907060e01020f06090601181802040f020c0601091a060903121e030108010603140604050a060509190620031303140904020a030e0106080106 75
    0x150820030076030f9005906001d0440e04075003100c010f80c00c3e503200c20070401c280c0740194070038042c1201d4a403c01090110040d030b6048a125280c17241000d02a82c0400441c10b0380c140d0b007841c601015000460720040785000d02d042c120500038000c0c001408034180c008505641a142200c4011001620034400c080031030b0030040c5c45109682500605c00e00600d025000800b89681001c001b500b80b076001c9466a05100003a400740008070760b01c0c036a10380702c8001845a0703038a02c0c0080741c0041c10701c484600401d403114007101007c0c03020400015902d4500d448100840352030f51800c01140d46940c2c580d440a4000c1013540020340d0f20500b40000c0a14905000640030310859102c0c02504a6061569030039015200141126606000b045685118000c5a2074480e4449000d07001c0403640fc568406480468038000030500c007a82000c004210b214900f881d6039107400307a07240c40c000c0198013a51034104158000c2e1000d950380302d400011040f0805602d5000200141c40c0c00b07008200056484441030708071103281c0706403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 117284937 1250 117283687 117283709
    0xb01060f0f0c03080601171801060b07030806191a0a0215070e091005030102070c0f0602010513171e070204060b13061101020d0e0f070509190513060e0703110a 70
    0x8000042d00c40c40d1305a0700310006041c02a1914410340d01d910241e6000c80ea4240302c0108000300d074401400901844000b000525406494148142c400502e2102e0042845004400440b0320b070840e5014190400010000544d120b24608203c4503070440720382c0001c02c008010300c0341d0440c40c031200c10880d070803d001d02816260300c90514018418001c5024006183d0311078109003460010711a1402c0c0006c1c00010300c101c401c1425141094800418040c49030030510441e8582010000400121007400003d25006024601071030303580070344140361744900390000212008401c01c40107005001000b5182d11442210144013082c1c4400e10b4003003a01400c41c09808949080500300400c03030003540310200002080c00054680784010880406490741c0088a002d9544400c00c0c502010406002401c00340100b291919606e0800d04248407044404a25290400d40e80c0d0005c9210103001c810705030215944003200b40281440444c4644e00c0709a90302c410b03100caa480020300384042ca051501002624421451 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 117286187 1250 117284937 117284957
    0x22506050a0c030e0a060203070c0b2a1c05180f0f060702040b060a0203130902070302100c1704050318010c0506040f0f170301090c030c09060e01030f02070b01060f0f 73
    0x890b0ba0780340c040c5040c0d040c040740d0b40c807110043d21a001c03a003001d0700c1350390019582d603a400c2c07500900c0b824055000c920383c44014071881c6203924040405441c0c0e40700b1091903060034076040e11300c541407c00341c1c6d031040f244038240d804503680141c1050140c83c00c0408000005d0381c0074051401d00c60084d07401e00d402580061000135403556850710002800340c0310700180000400c291401c0100b001540410040005640003040a5149050720b00240c0094041001c06504144150350043c0d40c40110001102c0001e031a0303030300c141c5420321814040c06081c0d10710016030364608007401c1058980c1d01040180e050040c0c20030b05c000e90765005240402907154000014145aa500d85800580e8090f0040441c0d40c4402e074890340001c90758082001c5482000e03412556a69450840a141109c8542481c0428981042200324240da000034450301200d1407810316010f003101400040f40100540350f06041c480e40b01081010611034800300e8107041e07030015180c1000042168200391400700d0000c880c040090b1a507a8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 117287437 1250 117286187 117286207
    0x6060a05040e03070209040b0f070908030406200a061a0301060515030702030903060a0510060806090f10150503040209060418030e010302090603010e0609060a060f0e060702040c02250605 82
    0x11040a6052180b025642004c0030790340003540c0c00030b050301c05907840164081402901c24101c40103a8102c0401c0c104400c502d480e040201d5204d0095200e040d050020b8490312042d600b94500d08469000340140c1501c420019502d80070008101202400c10303502c90011100c4800d040c14852441922802401449448103108800f01150300c000c0c0700c0f4085000a1161038426201000750718050402c18802007270b03074034143c15019168030781c60303110b442005641d6007070001c25101c203041c080d00901425400805a5284540389012004a83c072859120501c085d2541a0b1a1701001031402035108481c0e54400f034980384200400c0d2003490b070220008042d86401300000a029103103c4458450606000d424800c12000040d12508241d10212403c0c4058040091526201e10701c1d0341d0000080740c00980c07150030100c0042405060035250028013a2507034000e100c039620042030f510b02c0c070303401001800b050029140081d20746001090301d40140041001c41c4000c210501c2003541034491903502ca9080009a40e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 117288687 1250 117287437 117287441
    0x8030d020904020c16080609010c080c390f010b01050906031b03040609150c020606040e0307020a151107060e01051c0f0501060f0908191b12030f0206060a0504 70
    0x20101c01e900030340c01c208000703502009001015011030315554010015291a10f9113090000c000e0501d203250b4548902c040c44190410480c90708400c882c800261504258282000c0801419108035104516581165090720402a0301c210524509090701c0500720b4800380142031b0740310300c56607901003001070000f42641d08120303000c1d5500c4900d440900c04003041d94004901a540309450555616032555101020311510307030301d9008204d503261402c201102d0785e544025100c0c24040d0030a44a29180c01c1c0c004038042040041d280080d400505400c4055510100040c0d01e0354051484c5010900070710035001c00510204150046070002d880c0c54400420002c0110b6450780118040350180802c024103100308403042c03040c000d105515010004403035041c1301001e05490201c0c00000208071003030740f00b80005900421132444801d042042c1d000655014074280640003420880ba01005240b02c0001801c00e081c5052403040718065100d101110b10b55640c01c0741c0f208812500c0c01d40021140008101c58100f41e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 117289937 1250 117288687 117288697
    0x1020609060412051c0204090e0c012001110d050a270308070c1e150e070306020702041e06140402181002250f0509010f15020703020d03230408030d02 66
    0xc0c0c40c2103450015500180d10303005c8003680d1103030a020380c0843e05002c12132480c4540030183e541c81c00100161095000024141d66a24007620802d4000013581103010307909400802a254007060115210040904400010801244d0700d003c030324241849108406207000032104444007500c22014a03021030344090703842d0000a06494104403144100380c001c02e600c00303000c18030450100000240054241040708800e0000d0801200c030501c0d2203040c4016200002d4481d0890364890b1001da00c0d1091800054010181e000383e00070001504c0a040101d0b40c0d8035480305003600d903d000c0302510310103114140412030052a608a840813441600740c0018030b016005469031002e6031044400c04001d2001d500c0611106c0c03c100714164036001424480d08494804840150100f41ca00103d65032400e08000404030692060b001c00c54905070002d5000da100f4069880515005001000d0002d9140b030000e10010410039141d21007210301d07104046440121084a0888103c0c50085041240c0414003400941c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 117291187 1250 117289937 117289973
    0xf01090608132102010507030506091003020108060d17040305210706090507090606050405010e0315070804140307030903050d0f0e060d14010905090f03090312180d20010206090604 79
    0x3c0750b001c00703907518400c490301c25036003500703a0001c035041c14200405800c0d51005032180d07104420b00d03c02c0007803c4100007035070340c1105d40910b0031021036142c0da40030580b200f01d015000780800001411880503121000b0042084a101c0c0040783c80040303445d03102c200004c404900503502c04400300450700c0810483d03081548400c0c010b4090342d1400e039403540040c017220110751281002ca500400c0410841da08401410401102500500000c0c0d00c2c200460507454002452441032040c1d0b000850203000f180880b007500c011030303402200c0d521030072030074060b0010009100481d070324400c100242e03100354440c01c41083c01d5401c40d12001024102c00c400c000c4907411661000c0380199403448101000c2d518044428028010840c000034542041d90ba0070b42400241020481c041c0d00400000384a501c0001e043e604030404040e8654640d2070054160a00b00b10822140e5448229144c0b03200a1103005c105518200360f80c18072046511545030016622500122100e042c607400620004000c2040034061006c1110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 117292437 1250 117291187 117291203
    0x60507030e0a0309091406130e03040f1d0c18220524030303040803010b0a0c020409240b01020303180c0d03110607111009031101060b090f0109060813 66
    0x68480107549804906401a0001a10030300c042241c00402c0c03154006040f4440c035030210f540b600b000840c4030030602100312031105544412001d014801401680c0251158860419495581d0b5012251070044803840c4084190356001081c5488200c00485400c80003012103014100e940c8410010008410402034030141481003402180c1c900503c41e040c8205c00d001003201e600b01950074460040c0b05141d24880c0654010010300011601c03d405a80c1128400d00c56a640c0710768ac0300c400c80b6020941c400c025002414040b80c0000c110410a0703410300407101a1900c0c0004060101030350580e852403503e20701580080011480e41120482c1d420015905034040303410f1b890a2030301245051250850641c006010011203404920040c4101904280700740741c16142c81c800070b8180d0f41ca8600b10900c1d80101c96403144d50500f014022501c0b6080d0054600c000c0210a668407074081c0e041e070000007018415030889096444940c0640c200310155a82d580c2e55141c0340d41c1d2484036543d041c1c0400000c0d84d20316 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 117293687 1250 117292437 117292451
    0xb0132030d11100e030310050607050a060504051615030506031b04090c05060c060a0507050301060801120c0306050a0e120a050708030408040e0c0c100b0f01120e0106060f021c0c06050703 82
    0x5001d0700961381e044007202c0c0250303521315041c0c040c82c4040b519900b04c07510800003080300002050300040c07182ca030741d03030000720000700b42c2c956103000c3e481c1824440100500018054000621100495800031180c810740c40c14040d50707461808041d25800110600b94200c0c1c2804510f0b502814640c0c04104101d2158001000d840e88440c00a80d00d500602100317400c5502c01c404000c201c2d40140203058101d55282030940c159414480040c0c100d0505005000c00c80340b400c1c01c03d50611035000d0b040001160018800c1209040206135007000c2c20354100d0191071441094100d03102c0405844c1180c181ca00c20340e41391824000396958060842d070020340203a400761014880810001d5030314000c0c80c09050401c401c9960f0300e00804074142400c503140c0c00740700e030740b45040206a420b445003001182e00b050f0910300181042c2030504420010940d6044200300356107011408604aa0048505c20707090501380c00b02e80f1082c01300461015026200b500000005a107158100c1c0000c0468100e15003101e02420082070352 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 117294937 1250 117293687 117293713
    0x20702120604021e06070210031b02010507090f03120f02030c0303100e010b070210050306010c05190203011103100b0702060c06040b0a11070b0f090106030b0132030d11 74
    0x144101200540380780c2180e0300344011807900307103001c070550700c550300202070590755040000d506400740000c041d0040003162007015000d4882c0d40f05000040d1121000443d00308040030081c001c0004503400c8000c5100342c0000f20303103030b880c0c500f80804490744408480a2030804003400c0f84c580d1511651841580b00038403208400440a001840c440d102c0c0700d1a00100350715240102103504c1c81a8400710407030000701f2196000d40c440c040d0040b070b0311b5210300300107540e80c0f540c03401200c4154000c10040c220340114000840000c400314030300b14146e0b000714028001d15101c0c100c1412548401ea81b001e0280d803104e1400c10400200f0806401800e0000b020f05040c105280da1190801d038040300c04a41001a00c81000341d003145600c10386880b107142e106000d040400c207507035040d2104009004080c41400c0840015030a41003500070b030f40034680c0900004481c1d6981c44d03000741c0344481e0555400b41083c041c00c807119281e0500901d0203c124008004002d5100982d00079603241c080c0b02201480c80c020404800c2035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 117296187 1250 117294937 117294949
    0xf01140c010b0310090201050909070504050a080606040c03180f0312020a0e0114090a060e0a051c060506033d18021905150a0c0b0c04060807080408030a0c03020702 72
    0x280e604040008180041020209070510401d400c8200c88145810403203000f503680034081d82c00100080d0380c8495640c4418506803882c1c0202d611043d40202070385004940070030702060700c0f0300a502c01d54050182d20010f034019010707220608a500c0707500341392074010700c0800e000c3c8500480c02804ad061800c030500304c5005000c143da01600c103c00100c1d90b00f22001c003d07541c0c8800080343c0e04029208c21400c0501210015560031034602c1030f1020401d0104400c61250b407007140b51001018014209240710b9a0580b9490042089010030b9403400d2070100005c01c0c83c1004144092000340c1d68141c04250f5800b040c95540941d890400c0004901800b00121014401c0e40300d41011119403110f0007050080510401c1404400f0740c1582c46e41421803c001c1081c2c0e00c1c5c1c038451010656441050b0352700c883c0725000c2140c001c03881c0c02003c0d10964143d0700b17018000b02003000400a641c00c69907003814581d1071080960300d140d0107540050250f501040011141c606641c80f00300c1e03c4015107405480c0c40c50903000204 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 117297437 1250 117296187 117296197
    0x711010f0c08070f0b0601030504111311042907121b05060f010911040506070f030c0602071a09030c0a020118050901030803150910050108040609021905030609010b03030403020f0114 80
    0x5400c0c0030303c2c204c0000c0c001040d04150707000c0000d00e03041c405482e0540d1000d030702c6200c0b08a5140140e40001108041000340d8001c1c1164014601c10240c13101d40c1c0f4007801c5469203510300550303005117001000040c400803e100301c9100765001880c107036068003280386c201c3d5400700c01c00c0300440025043d00300c500018400c1c000d040c0182c540700840c44955040100103012078028030240c0d40001030402c01041291108030075030721b125400c040d120900e4034690405486214003240002c103d071f40300107488000c12000c000c4154134600848103201d01541c84c0b501880c1ea070310a450343e2403402c5d40031150510040d845640300c5110b54a02078544c51301940d0b91000f05003100703001c0e00102c82d1180003004015440080c0803000c00a8802100c01034000e0412081b0384d4a0301c8140e004140c108044e25000406100b05500103090f03103a409840c1c03021641040c00581844461406018070030301a09010500101c01401003103000308000b40a54a428656800c028090340c03086200360602401d9812211900025030181c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 117298687 1250 117297437 117297443
    0x7050409090b0a050c040303140304050307080d0204030c0905070203072a0602010f05070201050105010f12020f0f070302060108060c0909040203010b0306040c060e0108190f110a0f03060b0711010f0c0807 89
    0x5000307803d25201040030b8600c01402c12003699400d00c01000800e40c04618400408441c0500d1a502c2c0c6460400030f045120b0f4103400fa007880700002e41c1d4160542d045d401041164050308a03003418584460f80c0030140e40050700e401e00164000e126460101d207107004090721985e8081c95900d000d07001c6401d00300d100e82d9140d001d040540d540d0b1036180410032860240681c4004244000c2040790705000001e04031078030707400c5a031042000142145000304c01c298111682d0301580c1c04129203480b000f00065141e80d0040c07508400500841000181d110340010f58240103000074040743e0b003004105070a110351450001e1041c0e0741507482d040c050840780c80070701a160042d07006d95030b600003041c00c1c24030181c40301d01a0013210b810000518104001d135070811214410001010300086121100511000f001c1c0410300654000410006540b00b00c10360011044511004035840034406a569070184140c5406145c05c0582a0000303602e0081203580302d03000115003880340b4284440482640e031500c1310940c200103422 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 117299937 1250 117298687 117298703
    0x30f05040f060503090a120309020f04090803070f092102010f03140a0209040902060403061401060c1523100918020307050603041a011806050607052503081201090b011103030c030705040909 83
    0x10b1003035007404021a15034070300c0cd55090207103000558814446100051141d0100403540304902c0600307104100180041613103200011000e480d03201c0c81d00d01e81d0108041280072a255503011100e06009026650000b008900001d80380d680d13600092010354811003000d0703405607594623100c0040e61100301600c05940103090009240c200100071400420341038104c5000d000303c1100c40c400280420500c003413500b131480004640400c0160b214007445088032004550207004130104890030321001ca001c1c0884d18070040a2005003103011b100c0c00301051403403010303402d03030010380c1c0a000c0c6060031401540c01138030464850721020000d58811104460a07048803c011421740010317401c1400f00d01485014040480d206440d0590940da040d41d00d1300050300d0001c204070701410310903400c40c0a603928402150011042a6901e0758403a141940c90424015001c540d803074102641c81c9035115591141c0040380c094011850740c1ca6411020f0826040101142c040102c03c020104403440607009500005202e400300c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 117301187 1250 117299937 117299951
    0x506150901020a0c170708060f1306090213050405010b040c1209080f030108030408060c250201050d1d01050108060f0103080906160f0302071a070602070809040e0703030f05040f060503090a1203 85
    0x101c9820a00c155100d202582c8c0403200b449450f040c1c440115801c0b180f06444260359091605d8403402030324640c0006980310f4800f00382450041c00c160071a5200303034481c1008001d148603141c1040110b41010080c0400030342c00c040c04403880c0c1056400700e8a00d5005501440c00d10395400d120071102d50098120780010340003c1400c0140c40020444190460351242034a814100341c0d080620103100000040001803030503c19400559026400315043c505031030f242030084055159652065004845001c0243d40c030b004c0000031031000105200740505100000318104d81d203113854014854020701d050a500070b90402c1500c61680c214903000504500c0750480243d00d00590901909018841d40710041e100702144013a022209410116145a0317400381005071103c0c01410103040b6402045a40c0e900a40b4040384d0440318400020004116440380e621580640b102420465040c001c1c1d10421043e004c0292040c01503d00400181d80d021b290322040b1500094252a5a0303410100c0205141c0401e5545507 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 117302437 1250 117301187 117301229
    0xa06060603050613021b010204270504020906010522090603030e011d13110c0307051c08180a06050408030108010605010504030c06200f030912010506150901020a0c 72
    0x10100181903a00301000240b602c500481c2240010542e0012601e40c00685201124a4038584c580101070900003152190f4448035008810034144005c00c00c41c00c00c21420024002142c09402d10880d40582210003c7c1c0307800c8019103094010300d00d8101031201c030701d51014040e80c1d0022410000c10740d40c500071410f1407850401809010403103444904200400300c0200790071400705200c010400c01560303542120404c00e1a504024000c1000303503800000001407444035036100101a103011030040d002e031403002d0000c071421510008200c4ca100c0201c0e0801700003607200c0502030b1a05952030358040940c0c15000944d506c140c00ca44080b42c003210009400b10060010400900c00d000281c002828201c1c9464150707200c000f0404103e100d8041003008400070340304d24002003214119041030700b01c03c690844030445805900d0740c0200308401d009140600c4520300801d014001c0c10b0083c00007070561480701081c04a440b03220f9019403002030562081d010b03400c0014100ca180b00c07004202e070300440c45620380511 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 117303687 1250 117302437 117302441
    0xf03030b1201050403020c181506030a02040b03010f030201030c1b02040c030207050d1d0307031502031005060c0a11010504050607021014040f050a090c0f110c1507030810140f040e0f0a06 82
    0x12542014001008d420444210008004031294500c07c0751480d443e0365a0381c3c2e030309001e0f100c7e64001620f007903c007100000d11410f40407060f0060324030076203003442051010f05003216102c502080d03040a4a5010201201508007a8404400c200381480e01518000d4203441e900d207030400c00120039000070705440841150142d001e400b10170b03180c407c0300a0552585103884115030014044c090300d100950000101e2001c4080021010080401500458541030308c0500183c4901c102d81d41580d6820030400580c1a5612800403903082e920006c0481d0708200040c3c0a110040c900d40c3c4400302031125440c442e95090071428007070001800b00d00242500c0a0800382408034032885544040c24145c140703807800c0451900200d078031030180164034041e1100841c4c000210702d4940018507068004c440c070403020f48040240c07001818494000c0e01d40003083c1c0c84010b00b10f090a0710300d109400502c07448980703090341c5103046c07280c5400080004001140076001005481d0038490408a481c0e01030b802134a16030200f21941c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 117304937 1250 117303687 117303709
    0xc030f050606060406050703030509070e0106020f1002070c03060c03060b1911010c020c010f09050a0303031d1614120f0f160614070305130902130803070f03030b1201050403020c 78
    0x9503400d90400c0d29165001d001c2e8094240008c00b41521080014201d90040220900800c440c4440411a594495001e5180e20103400703008030301c0c000c4100020151165008840400c5d60260300c58a1552031619000c0c000c003145242c00c410140c45840008200304c1d900050310781c442c6110842100300804070409420300c0e03010703010302c480c503414207407004040342d000f05081c0c038600020300f011b0740c00c0140481c086442c03e0140c0c0000303911507040d1402000781940340d0300541c6410080d04190040100c0400070941c1c45080002c4152450b05212080c04030301c1c0544580015031a0160150885102c2c00c43c00505110344007000c1c01c2d8540c031040b240300282508001c00b441110100141e0764040e4140000200745130744800301010640800205402050301c2941110001101046400b030841c0d101c1407010040e40c0031a03060b80728078504400c00302e10808080203c0fa40d290303200b02c004100b06401da500b50f010f007a003450b85580c8130b0040c0b000600b1601d006c0c020248200e100e680500b001080780d004000a010320 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 117306187 1250 117304937 117304939
    0x80c013c0f1211031b1608131d0703020c03090301021603170f060402071106030f10150503061c0503030f0109050109020f181309080301050406140307150201090c030f050606 76
    0x4180d11180d00003c44403c4903088400800b0103654031070812942e050394403030b0580c1402c0c00d20b42c007401c0905006908020b0490140c1c690742c4240003c1d60350740c1c940300c0c80030360f40703080c4c8100c81c266808508924004da00805042c5d070700006032030401104000103804c98000300100d62044605c1200c0500b010381c00003280d00c0e98900c0003001c1000d801d100303c942c0410b0500400880c001e940c0010740c0c0d4140400c2c040807140c038040081005035a45800c00b64200070544c2600e100d44401d148400c04100c245010808407d00d00d05a95028210f54482c01008403822441c40f296045c400000c41480101d1400d0000b18403c030500b551601c0c3d2945002c03da0411134405902041209205004501c901110001264031912420024040301c100704400202c82913510701e0b07101c0f200f5161881c02001c001400002e035040b500105d83c200102c0360303141052400c0020f03401d103181c2c0c50f0b00008000d010076440c010304400300f400584000921f0844a58609a0070100da40090f2514503034032040d0000c10074208071031948440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 117307437 1250 117306187 117306191
    0x9010e030d020711191a0913020706050705030910180210020609060106020109080a0e0111010501060e0906030c030a0305070f240b040903020c0d020f03100213080c013c0f12 76
    0xc581141c20100c480e05000740081d901800010039041b441c040c0640750412030003060148108010030981c4000e5019100448802e0309260000f80c19034064416a0700c2800680007405902c02496040e00090000342003840b030b1000e81041030000750b03c1d0b010040c8400e00740c0e50010724050603c00c81c554a80b4605030f00c000116810009a180020032078404d50f91040030509041d4082492200140c4a04e030003120505003035841d1000019206a0200d14546121016606112151116420715031941d08031114135401d80e03c000c03001000030780b0035401401075038080c0c503e01034100205e5507000d0340340c8039100084e066002c21075002a440e6035507206114001c442100d0030042044c0300da030065260355a900c800d03071141aa0010300d1055441e00e041d50f40c14000c0c0102661042c150321a0140000d4010105400480c80005404540200001824524403105855a40d4541480905080700280c1b12507428100080703210400f407003036800040000c42140d107882d0490ba00c81c10510041010342004000c4003214 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 117308687 1250 117307437 117307459
    0x7030203040311030403081801020f0f0106090c030e0d0c02060c0a0f1203050f070e010201020903120d200d0c031d1507171503010b0a03030503060a050402030f060909010e030d020711 80
    0x440c50008c49099a1241403070306210b040317030300050f0b080150081c1c82c090036000f40860601c0200c01988080d003550780c802d01c20401b640d403514046089400b04403054a055020320012035025018000181e503040c402030100345131111000e000d44c100f0640d514110b0301000e9031031103241003241c00000000f0405041c941006140703400124120403010103000700042c4074100c458000300d039100307404a5540880c00b404407030380c10941d05072560b000d0b03002c00c03262201c041c80d200e907640c1c48603028841e0541c0c41c00502199810b1120620030100117004803104d24092590f520085e5000c0000742071002e00342d00b840ba019041e01500b89000d010342020041c40c29003001075603070440c011140040c07001c0e9000030070b0b80003080f03180c2c0010011900421760032100c1340e881403801100008040d13100c0000c2d07218000aa0302419410303074990511040c1d00041c0d590940080942c00001d000d4200185000d51001c0400004655a5400c0150608540c44491030303d20481c1c001071460180448209034004410007074601143c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 117309937 1250 117308687 117308693
    0x6010e04030f0f2003090a050103180b071704080a0e040516110312090a03030c0306270f0f020a080609010806040227190e0705010504090902010903060507030203040311030403 77
    0x2d400048446010310082c000d00c1d4690a21485210107040c565110f440d0040d500190019500d0300040c81c1c03540b24001102012906520900404028042801d07100030368002554600c100e001c1c00608910401c00141000c641d80c03100b100842c1d01071030083e1080355a4001c04c4c20005c003100c043c0c5540a01450a14052144200644180a4030113116280a824a80b0b881c0c11190071403052464036001d03005820148602e01c0b0020450405040c429181084920b0b040301056065940da0302c00c48203890301d41d40700c3d02c411071030290000c2c41c54051140b0004a11a0a654146c203c03030142c51460343c071540c041507025005401c0001660400c100300c2e490846580f512803210b9845000401c001d0040c0106003090312200c2020a0004000302c92081c491414a0203001100710980000401c1c200e140c00c040d61b027103081601068a206a44060b5241450181040480000307840c8680040b4100509404000045850b910406000d070145540159403820503040c014480301000641c0d01d11501f00300000c00c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 117311187 1250 117309937 117309947
    0x3081815010e0a05040b060d08070f0302010605090106031b0804050c090709140913020f031c0503061f0207060e060c0a06050105090615180a0b1308060c0a02070b070c050604150206010e0403 83
    0x84483c08440364071801190b480d00030207500034842b000f45101c0c9043c841c54101a0103400440c2600c10075104411580c0e62100110252000440c0450762141a0f0210500303ca01c04c10b161540319000f001200c44d0350305010007080d04440200c40707900003d02190301c06c0c0100c40f0700c1554a000040200c1310302c0da090400d2503007040308904c104002403140601c2c1580f600d06403002c0c8141a0011303901c0508242d01c0a02c030001520f83d51007100c2e040d108440b1864a2146140300401096440c1364030340c018a419400c01b0f800f0350345801c0807074a21754401b00620842c442403404100310301030184981004592949030000344800c1c04070182c2640c0c03241520b01d2981704044541019640d02090044490400b80c0c40301010070700046aa41101409441c000307550744283d2202030780c810444400350100e6450365103900c801589030080b0400000144c0141c13034100180800c02c0d0280022900400001d0f00c00c640c3c400026080c4d030b01503442000301d04000a00096030b190140f19250040001c555034030ba0070b00c0d0542e00180 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 117312437 1250 117311187 117311191
    0x602070b090105220302060a0f1701030f02010e010302040b0c0109060b12031c02070f0302010915050c1b07080601060c0302070503010605130e0106090e01060f050a0e0403081815010e0a05040b 84
    0x9031055082c848039440301c544c0580001180c000c0c00b40c40c0c0d00c1007000070081803501a0f8042c540420180c0124083c40541100300d98100c80d00115101a40030703a41d8011941d5240740a0b00a04164003440046044403140740100410100a000020490090301d40710041d070305c28140c0640300b040303003040001c4500c030040700329034007520341031241d44071040e16039424002405407410160178504804141420507405500c0004901d0042d6441e42080030b249590606550301141c011b1400700c02403004000601c5c8492802500500d514151910f0a8980d038000303162100c02d03801b83c0000f903001c00404081c140c04ac404500030740307801c1d0000d10505050001044212002e103d086241c9503803940310301c0e030300345c801c1d88040042c0000e00300c180083e0080002d4a400707030085000d880c02c0030481070000035080c54844103d104036001100c03000c20300c1c3e03500d48094554500041480d21622800380c544003055400f4440c2d44148c54130b101d000b044550503e18581c00c03ea034001d000d402440d143c58140008981050a525 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 117313687 1250 117312437 117312457
    0x20a0b0a14070309081507120b0609010c1a1611070b030112020103091a0108160503120a090b0f070c0b0a020a06020c070911030105010813030f0c0c0503160602070b090105 75
    0x42e41d03807036040c9021070700101554003241030b82c02082001d14a10890440143c0254820b6941c40251092040d0000482e070305000f40d9603104c801084600081c1d400785170400ca440e4000c82e10b0740352245858040003a085400c4442e0301c001c4480a079088070240c0c0080826208100180042c0032003810a6081829440706008450922000b8400601103a211340c1085240c651321400d50b0400c030504100c0e00010030303000e00500410b8095803042c40c4880a21004407800c50b403000340202503014101c101c01c1544c8d07000250303c80801c070719000d010800341c212038002d104450307400c02d0996951101c0e0510341c2c0c0c810030b03070b030058205000c04120000c0c040c2c1c3e0000e80b4010380d0307030406001a610701c4501030780741c44d03c04194415229141024507254114007204095412100c0a803104011f50782c0d0500ca5a01c14078202000901040100085051040c811185034200d248034603840c1c3c2c1d141e910f82c40083d20f40f440c02e06821460100d655002d000c0554180100c2c0e0040104107038990914280c0c200192503400390300102 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 117314937 1250 117313687 117313727
    0xe0103030318120e12031215030d080a05060a0b040308030702060f0c0306120f07080307211418060c0a05010e031611030a0c0605040e06011b120c060c0c020a0b0a 71
    0xc0041e50341c44117031400000740282103d545501b10908107004101c21a070205841c41d00502003440d60070041184203085560742c1d141d80c40ba60310405020000c040151965401170246034000c514003450702c004201960091502c00d488e4684100c0003490010018042c803044111401071003850020340050301d070080d0007140da02018075010b0030810324003401d9149002952103101000510a0404001041103502908003c070f918110011901c4c40c40382c503900c0180000303207002d03002d50341006c01d80b0140a07a108030f0341408040000301c10010300782d90081101850f40e0740200f841d00003002400d05c13400070041c0c0c030580550304007498420f41403000c1d0001e140241403a161044200349a81e000d11055032800e600c0f4808001a944905005280780c101c0d015540190b81090041001507014461402c1d04000403015178900c0781c034543d26200d520310055880803e01c0000200700d0002903c602038000082019516110b40f895903004100d600c800503801031541d02d40800028408551000700421040c41107081 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 117316187 1250 117314937 117314957
    0x9060f0e16170c0408060c0c0d0c0c091a040b01020616030c03091b03051509120f1303060c090b090609040b030a06090809010801090b180c040e010e010303031812 71
    0x4241c802c10910400c100001c2c80b070400308a61544a440500103840d074480c200e0340e69135100c49594001d0f200f961080d040d41d611004c030407403d03c0e1181c20b00d90211881f910854000a44d108030302c1050f141c0c0c01c0d480724143c502c011511a6142054824a41f11800c01d10003445c840c1408842e11882d00c1c44450031004064403210a000524001e42203000c00307076403142114520f4030030b040403440110344030b010031507183c0a18036220425800c0b40d00c0142c0610b0702000904081c031400021084181c2c0700d140c0204102c5000d1003400c80940a000c4e280c00118054000443c1c1d00480c010003c0440c2065001300034049402e0008006a486820503200d8418081c2d5000890f282c500c000039140c54100000106150f040c0542c540400106001402e81c1d10320a8a8504959803220010402c1e0b541d03a0046036004004100c05c20301190304024050b400c1118100390904d4103440304001001100c0c240c005004901c101e07401003040590503c0360002000030b590041c40f04407515661001d283c0c103040c10364010031030381c048 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 117317437 1250 117316187 117316231
    0x20f01030902010c0855210e030a03150603140112050f030a0f0e0a05011706060d0c0207380d0b09070e010905030f03090904080409050c0409060f0e 65
    0x120504a070801c00010348103280000c0010201c1c411b03aa80c481104c941481e4a0b000c42000080d9161094840c1e200621182208003a82006c80d900303055040c0e10340300180d52055040c170040901815564020540366051451401006626807283c402c00d486e054444028110034284c89041d2a1000016200c49070765003401850014a0240301311907001c000396001d005a04103800b4031003c469138403442d142982d4402003128040c443e101d890701154480700d105c0c180b0308480c038040b42d00c207030020010b600784190090304600f26280f000c1e140300964482c3d40103110460010b043c1103043d44c20345403200b400b202e4140c00b64070418074041c2221103080c004501c0d2880c00302d90f83c02103401d04034042c00d180d4052820070030042220048141c1203001c100c10b07010108550034003081480c4203c0c1c880700158139100940c410700c6940b1400600070f0ba0304400500001c101c6c41154091303140035101e8603401903111400d21090408559850380009810007000008000890851840d01e50100c0290341101003a10484 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 117318687 1250 117317437 117317467
    0x1051011030405060f0705010606020a210c051009051b15030901090819030f090c17070312030e0d05090a090207020f090a0f0b01030b0a03080a0c05060a0207020f01030902010c08 78
    0xf40041e5409500403a211041c12070b4400600301c0076010b0070083c001e80d035079501c09986407035000d900541522401c44070885202400b20170090103c900b807500c41540c2c0c1594403000d0400d25220300440300c0c00d032070742c5480d002e200080000c04c07114400e4404400c0d07910850ba0000300f0120600b0301e03041d5101c40101c002045480b0a41c4140c1506030003a04040c1e0703440e1694146140c40e8400c50205020900c2d140e61002c411203148150280c0c10344c456030491080e81030a042244002c0c05140540e124402d4200c04400105500001043c0419944000c90707940100ca5005003030203022410b841c10410180f0180b500395689007062802c40d994410010382d1200140042120940001400c0750440810401d20183c8511940320030040e400d01c1000b084100e50f01d00044080da0340c54012a6405108200244041a0f200004003c150b1607400c3c1102402043c0d40c900b81010021640301281c10343c040b030403600794280000c034000702c200c1c06d00c1c0810403613826600180c8003038444070020b00207107008140800300b0140c03e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 117319937 1250 117318687 117318689
    0x17060d080d050411040c0804031d0d1509030e03060c0403170c01021803070b0705061503160906030b010e09100507030204050a080c040f0b09040803090a020a14010f08010510110304 79
    0xe1001d11051409052102c542d140c6032004c140034138580506240468807501c03030540079039816a114030704881e00102c03021a0750360000c011030340128044600000514144541268000a1400401e541100c2c0c20042c0c01403460740007940c00382c1c010a04100c2002c1c3e044044801ba2640000c80441d00385101054007001d014014800c04d4640c40098841c202c095140c40001017800101e0031501d00359110341c00384403035004000c4020583c0c0c4c00040865551011000110405003019013102c5480300100d408501c590041c1d44042580c85c3e0361441230051100e80c030203c81c050000081500c5040c2003801c0c0080c3d9400d4440aa8401d841e40c5038080360a02c3d10a40480e00105401001c2d078101076142d900b02c50321002a24aa2840f0702c0c5003407150f03d042d5185028a184850004060a0480da940e450b00752090384000c00b40308244c06004501e900595a0000e0030010b062403142901440c1c0c8000005082000c094030444180302c005401040740d0f54825020049008623403808404010602603060300d5030080e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 117321187 1250 117319937 117319957
    0xc060c140403050f0c0301060609030605040f0f0b09060a0b010c030f0c0c080f010e0106050102190309050406030f0203010e0a02150a030603080a0302091f02030301090e0a0c080303150117060d08 85
    0x2000600100740301c400107904041c100c0400c1174441c000741c2c00e0105801c039041d80c070550021548002c8100045001d5600c100c8c0d000740142d1841400441c0c13585c42d90303e50410864210345210302c2c1c00030301c55022010041e198ec000440582007080c100c0d01c500180143c589010000d080001c0600b050045600c00c5409800300340d406400c085105d5122003134141c9806900f1040f010b25841c1c8228001da070101409039104541041c0c0107030041414070420b03600b0448000200790140003140b00300051035240c03441242c00550050803144039800d82d0744105821344400310300c00c0b081944414403020150f5600800000c41103c2064104c1d500c29818000703401078800e0703620141020b04042007001003290990014801c01100311121843c02000d010700203030188000a48a0050344240014007666109034071501c00c0c45007900484400365030742da81e1f040c9e00100981188455801c040240190824132681c03601d041a001d00308409620050608442000c2c001001c051040c4400300c079800900030078804072010300203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 117322437 1250 117321187 117321227
    0xb1e010e090a0b0c0c0c06030105061b120703020d080705030f0105040c020a080c0105040b130c0e0406090206070309050f12060609040201171305100e0a02040f023007030204060c060c 80
    0x240000c4c519969800034544006180500c00151240c1d2a1510032070f81603070b200501031801c041e0b20b22000c840740c0c0d010003482d004a10802c41c0498444d1810350141c500300e88aa80100643c11200ad401803050701c000e081201440814000e102007203921400d23043c1590400c2e9400a40c00200700412494131070014405040b030140061901c0d6a058190061841180648156a115215a0000700f1940387c0c41c6405019400c1e8440180030504070742400c20b402900440c0702054140940d00022255480184214085010030104000b103040c420320f100c080410407541d5541c03000d850a4441d4490341d005050300c0c45000550000b50440e03010304211080040481402511403904a10084402030056401d44451050b20640d220006150050314920240c40001e800b41700030503400d000192841b402c010080907000d200c0c2000342940503a4603c0b035000f500c642c4d806000c16080c01301800303042c0540700c4c0041600400060100c3d82e0040700d1501c45550103e80021522041842220400d580c03101c4060010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 117323687 1250 117322437 117322441
    0x906030b01030506010b0f070b06030a061e0b0a05010905040906200418020a09060c051f09150b060a0809070f0b19020706120c03110703020a0b1e010e090a0b 69
    0x2980c459140c1aa403084049902c1030341c0b030306950541800fa464980c201c001c0704010304400204030190464000070042d044034140c60055507804c0aa80c1842e8101103c0081113060502c115040d0041400d2400140d600030080e40c10700000a09503903146c0161400ba03900c03880c42d00c0800c07038598801c2d0100306504940c0c2c21040000c032404e02e000ea002d07100b111422041008c1154101d1154030807201c8040d09525600b00f0385180102c01e803454500e021082c1d802c1d000320359000311610401100f20402d44002c0000050a400314500740051900002050891602e060043e003c01d4942e00101ea400711001c2c20191840d55444500742d01d0710195400c180c0c052103038110b001603480000340141040c2e05031210005a4a400380f6400c83c0d403174400c1c0c425030000070700d0000304549090443d030298503103580600d8042029804020304c1c100a901c00344040f00164801d6a030350302030200c1e580d002c5821180d0700c00491607500c080000700d505610107001300c92242c1d00c90b0001c00c5400780300308007400c2d905a001000b402c840c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 117324937 1250 117323687 117323693
    0x14091e0c0d0c06020d0e03030304030806131401080708010504081e040b1602090609040b041e0204050c0d050f0c03010308160f1505060a1d070314090604030207090207120c0606090603 80
    0x10609100c0d0202604c105841440114050141c1c0c0c2101b010180003141180c1d07a03501d04031031001d0042c00c01741d04400101582685038019020702901c0d002d0700714040b038465150078078041c6080f269a0052000d81d25110a000000b110041112031010038142d00001c44040001a4440343c0301d15030111941c8180010181c280ba05500e5100c1c411a00888002ca07003a030300d0b4802d101071420120340050035141c1800000700010800c520200c01c0707080031080008190941d03804101154002d03982c1c5010014003040300002c0c1c1c0c449016040d0f001e00d00354140142418000ca980000d0f00042c0001005071402103150960f03a680222038a4000d600181a80c0445441d030070f001c42e41c01541d0381d0101c00e0350305100000d400c908041c030030613048a0402d241c030660003010703403002e0007524005000c00040540b03403000d8510078000003400600401c00040941001c2c100f44ca03010b1314000c80c07640300410242c018481500450390405002512040500b40a01c40c400146003400c000c2429411503100503181160200074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 117326187 1250 117324937 117324953
    0x30c10030c14070305030f040c320a030507060e01051315030c05090a06030203130204020a0f0314010311121c02030c0601051e06070f0203150a14091e0c0d 68
    0x6441c49549890328401008540359200b072103038034005408100f0410225400000c252540c59005000e0302403102d03180d8132154111031743e8107030008102a6035003482c6400581d841c410a000c0203100100c0e6582e800c5c0703107540da03807035120f111510409081c8041000623555a90007001282d0701d030110460f10b100491f884002d078482840e030050b10f0400081c50803280007030182c007501c01c450702408000d21201d1084c3c40c16800314065800180503483c500c02510003400140c907280060302c001c06094540103421045120000d08031446a00c044c0c090400201c0100040381686440ac040550b041d034041400b0720129500610744012403105080707202142c0c40030000c3c25404000780440001e0002501d003141d0ba51020011104944c02a074070aa04c1036000c000329510b0000000d056044c1315410800c4260b682d1b400007030400c4e40d9160382d840c6d0004c584013002030f0b511452091a024803c2914007644c00d0410410310b6955024401c0c90004001c0b41400c0c1ca464104104244900080018142d402d02c400519144103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 117327437 1250 117326187 117326201
    0x1b07030c0602150906131a0c091318060504080702030a0b100b09060301170708030f0301091d061f051914010203030903090f0a03021915110a11030c1003 67
    0x1402483c2e00f684400740c0c0d0b48050350040302400300401e92501d8986010464007518041101e041d10300d021484001c1d81c040e181e10303125400d40f100031500d803c114018402195420950f13900d00707510702103541100b4541421604075940d044003002030640d03180d00d486c0204d07201d409030207549442010160b01c1000f5100980ca072242c0a0310303007103000306659000d4005d542e0141c018802d81c4030b0070a000611500444c10701044026403040304441c000703960f078543c1e035007598040c468520704810b0000041c0705011450080e50402541e60340c0c070702000d041950016442e901c0180600d0304083c1d203140c00c40800084d4046107800740c50028103900803031003502c00d580e102600b21701c519000742e50301042203000d41d070020054034450300204001c0c515007481c4104000b643c0c22145d002660261042c2c40100240e15040a00705040d008105200492814001000c2c044249552460104074501001d9407680360086011042d05502003903410b001d144035400203003410403120410380c2081c0c0c1e0142031582c0355031681240c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 117328687 1250 117327437 117327449
    0x210b0901091e0506010b0c0114010b0703030623130e03040806040209070305040b13030212030109142a0c0106081c14120f0603160b0a02060609010302151b07030c 71
    0x40e280910b01c07110078820a04480010705660000c100400000700d094008050344540302c130001505a42d0402c20507070000c000e800252043c400810403500300741e0140b040708003401c1031a0f01c440f040c0b00e01501d600401403221084900501c2c850201d400c6000170340e00000c05404950050740d41301c0340c803089069074540f41200d0a912403042440441d40681c080e10416000b19001a0600e5243d079032090404042644036001b11f0440c8113600c0348001c00030603000514040c0100d15004585682403451603002c40b00f01500d494504018000040d034040700200000c4032a40410380d50a4495810080710760062a442d80858014069480c00c01c00082c9041c0c030300740184802e0389400313094080a5501c0600c03801400c0100000005000224031104900b450042d40719030001c0445c0c41d0801002d00f016440280d40d07000d60100140400c222819680600c0314940c809001d0300c00d03900700e40c50364002038242111001c1c0500c090320b000421ba01c4501d0782030f4071a10502101d50444900f076a59180181c0744444a00c500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 117329937 1250 117328687 117328703
    0x9040e10022a06040311031303141b1c020a0b0706020702090c040602030d0504061d060a11090d121206030b15090709030314040f0915051009210b090109 67
    0xa80b42600400440e403040c0c8000052540c1c2c2ea5aa40a4078108440b00d8002850701c8184804801c280d081c6c2c000c080514419401c5094840300849241e01d4410240803001c000030010500040350384075513110144810700488010400c1841c1e00220f1003418554000854444d4002401024004150010403081e0700c252030310320382585e0b071070303410440c50103103000b881c00580080000c411080703969041160020b00420001a0328542010410444400d0302140c80303054201e03000304004440f240c0301e095841c1035001002450044410b00080e104202040c2c014400081d03c0000c0d4000c40c45500c0d42c241c0c5c440e032a041017210726241c1c10202c0c1d0741141128100c089000179005504282440318005019450984a000710385003075a90a54046050441d600c1c0005e20074080040c7c03454075a60100004c1c41075100c0000c3c03410b1065003407210b12940d60416402001061041d44003168400758080032a5120a0f0306110411268900741c054028610050303e000300501c1030000f4901c065201c0c200c101e11078a02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 117331187 1250 117329937 117329977
    0x10f03090503030f220305041a12040605060109080c03030910020c03060709050f010e0d060b01030b040f09060c050301030c180b040e010e01050a05010803040512010b03030a0f1205040b070509040e1002 88
    0x30081d000070817260010000350b800e20003004209551401c0340c06854003400050300301894881c0c100d0040300c1c00c48090b07494070740b85d40902006503007048010000c0c000e40c40140c28000c40882c0825076901c15030201c07600030301840810909083c800c0c0700c0815400c2c0c0c0201907800700e0501103001031400d0010f02440744150036200c00c0704850b43c0252000103540c100500702140401c003d46501c0018503400c01043e05040d140d81e442c1c01c180c0d5a40c0704500150003601c600088241840c00c00800f103400c28803010003031250800041c4003003546214480211007800308510711800031113400078042c10324403a00b5a08142019003800301c2d481e06400920380c012520008201c0d503500d400c840019030724288155802900100014400b41c184106220342021014002040090301480403034903551001c0d0b03d0000007110103c034161219070204405601c81d042c41c0702400241000e403140d001e8004058500824044000f42e9141e1340c0c0c489807c00702c91041d58074203079100742c005014118042e5004681c0c1c0300c183d52025030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 117332437 1250 117331187 117331231
    0x6020f0f031207031503050118061b050f070c030b01030f0510060609090b0a031a0610140a0309050a060e01150603020f0f0906040801150911090d02010f03090503030f 73
    0x41e030b00600c0300c038034140c070041e115090150001d06801c4100030185081000100200c1c409020300d130600c81542c0b140e4114240c0506000048a0241032507131514030310700e8003a00089a100702a02d0b466000090b81c02d50314030f5107280072003016540760f00c0108030000010000040c042c0d41c840640100b0b010b42c080e00d40000c000b10110741200e1086c0150ba000ca41a44024000d071111a8010460014040c0420903910b40b42d80303480d1000c00402c250b804411052130308000c41030800c0e0403440204107150820321420801c22034583c1c0140220040c00c001c241c0d0f2001a08280001042002c401c00c0d08200f04100c5590350740c2c42c25020b400b6210000385942c4c81031800040c0103200344200c070001c1b450944280d042203220200b040381c5038000000f107984030005210129103254207218561240161032440d8401d80d04e4881e82d107007a28803880346d90300984000e00c1103540c2c0380c480c01581d81d112035091a2108910602501c15030041c40030711000340c0148800700800004851034481c85000d400c81c00101c4030f400240e02 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 117333687 1250 117332437 117332443
    0x804060605091006050309010b0402070501020c010b012303040c03080a02070302030c220e0a02060a1d060702100c050111120105031c02100504050c040e0d11030a0c030e03011506020f0f 81
    0x3d101c1d410104905101000200e21580145030010003d5001082100d2001e00041c10b136000801c06603010707540020300c900a0b150034413079612041c40030b00749030000607a407103642c194000b8900101d810319500000010100106d1001100c06075500056035902c0341080349000350780c0c02c06800228000e10030030295001b24500841e0802204241c0305100b0302202d00e00c028800905030307186034449144100704500c0c1c010b0f80c07003c01508a1403caa6a28040b009541c46508644401660740a01400c4100402405600ca203107100d404d054a90030400212140c5203800d41c01401007803020b02c850702000c80c0b9004c0400140076110304a8904070102c4002d600c0c140c1c4081440340c0020600800340e0701c0060b00c00d8200404d84c000992003401502a9210b40c4984800700e81601c801c0d110221003074024600f840380c0c42d6040f0f80c0050036003400c0d10085040003800e0b0744c05400f034840340b200501071015000b128040c80d54250403104240341465180c41c08907650700782c0a59941c0c1d4485c440780282c065502500ca10100c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 117334937 1250 117333687 117333691
    0x601080c0f060c0a080a08070f0807050f0715021303060605090c0405090c04050303210a110901030f0e0a2102030306030c2101050108030a03061205030406030e1c080406060509 77
    0x300070180284228003003040c207078841c07a0f0004241c041d8100e400040380d00240a07000d6039080f40c0710702043d45880240100400d158600c40818000440148100f0030307406003ea95070084010b04980d900d0b21141485100e9240420444a401c1e000154021089045c10510411607100342d0090240c16140e1007001010742c012983c1782e900d00000e0008116600d407036400241c01c000c2c080400d603d815151804030341181c0c4000c400800c1d841008042010302c20013800880c1c0c0c45032064800300251210a00348100714882c0c0340b100390425464042d003584031040e0394440c0401400e21400c41d0915140c1d8509a8002480441e23907407000021032015190160010003100d206440003005030508001120402003d44684610084518618008601c4810091280e940a41080c600840e101d010380c1d0401002c2e80c03116004068089421102000021030002c00c0e9410b680c540e090204480110720364141c41c102c01154040b071070b11541c160040f10b035a00807810901980c003d03d0140019904d940501401c06c42c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 117336187 1250 117334937 117334939
    0x1c02040f09140a02030415140402090108030a12020306011b1103060c03011802280e1003060e01141518010806120d0e01110a0c05191206020a0c0804060e030601080c 72
    0x641c00000d01c0f040203a40116402481401c4d5200c000640103040c000700d90304104c20315403082c60f410a2106618010f81c42a004000c00001035140c160380d0714004085181d410a5440c07010b8000c1b01243d5143e02880700451203819445910000d00c2d06414035603054044c00c50307854002e026490125001983c80011207050b02c0130090014824a4100e0036100254466003007254400e404480c5410540d080c1c5c8080403044540d076440c02c0c3c80b1600030341023103c0304400d40d500400707062802008000c0044021140342c1180c42c3c0300380c0484851600310110b080324452764090601800002200b0034400c0c810020240c6036031080c4c0ea120502ea881d402401541040e0320f403d50100d5004071889030440703200d40c89007103440c181890000c41c03180380062440d2800580440c00c41c0d031081c0303668092045040600301c2d1210170001801c000041c0c1d01e00701307801ca5030460b4828054142500064402a518050008a03490a500c2003485545541d9104005c160300e401140f502c0c03190081100004140000148410134110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 117337437 1250 117336187 117336221
    0x15060305071404063506091009110409050706031104060c0f020a0b0d0903031404170f04030c060c03120c020c0f03070512010509060106080f0106141c02040f09 70
    0xc2040207401824082c191200d9100791281004181c1d0080400e500c180341c5843d68148604135841c0e403020a01c0c2e601140f6605030380d0310003402c00c42034601c002a80181d02c0d0300c060000603c030b141d034148280f114004007012500a41840c01e0718041200000e41c00301101c0c0c060b40d08012201e110040007520784070f80d208520000c1d060202c80d4002c558585103614082c0d10003400d6500311070741c601e0169500e400401048110541da5100d10080c980c1500500c040d446c071114405400f45010f5594030501918420701186a1a000c2904809400341404580181da00f000b540e881c0250b980000410f03409542c1303000c0f00010200340e00298020403a0240052820880d0003a00c840041c0e40306115070f500041074002d525102d010000640d5807181da110740283e0031808004181c500e082110356140c000103078007290420000e6010043c080140043d00c0d81541c1c0076140950b0600740150968416014801c440c84413400140386500e881d80007940140112041c0c6078803e82007550300e01c0b8410803a0a1280401d034505 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 117338687 1250 117337437 117337439
    0x130c0e0c070308090a021201021914040303200304090525090902030c040302040510031103030708030a020703090509090609010e0f1b010c050628020c0a110a211506030507 75
    0x81c0101da401d98080e00c004c00302c4a03241a21340008110300700040b070000441c2d46c002003800c024241c44104480100302d038104a4160000d00400d07102a1040303101c081c0812028807010410038004180300d02c28003c14008894856895403d0300f030041c90103407800c18203910b180c82c0501d680c0a10110b442c100c8031864444003401480d040d40d020203540028049071869404010100050307444e8840c050141d00003a070294060b6041d4a4408a280740c1c8003007861081d401072000200040c46a001c83e90300070307070341b010168842071286030a45c0c1c1407030b042d000540d00009000402500184c009045442038201c08002d00091000031b00250b200c1c031402d101e0a002d42c0004a000311010003854004074160300c10300d80500800500d0311a82c1c14100181c1f11207240401e440c02242d0001c195500c0b42fa900404202e08500e8103107114003940e601c042001c03004120343c458039a03c4006a0b14845940000c0c03003e40400490309440c0742038400c107801500c000711800801c0d106004440340e80d0784100d00a80394024000c140700c0f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 117339937 1250 117338687 117338693
    0x60604091103070305010e06090106030b161803050a0b0708090d0809030c011503030e09010609030f0203011b0e09090106030b07140f041401080906040b1f080105130c0e0c07 76
    0x2814140c0001e03a0384026000d00707100542c030100f11500c015400342c0c0000135600000c840e0700b414000040c0c0002242da0502d10705101080d020404550040301c0500b800013082d5003c80161180403480e0450301ca0560003850020901c10040b400c11552480361124241f41c2e6100c075420360f404441600c6e0648207601040c0710301c5619004a0245401541810032a030608a4907031043d425201791a090100c03140c60401704104144d00318410100441040341c843c4c003598146071004284c02d400b40302c050891034412071a281551803c1d0f00014201c42c0d070b40c1d1904202c0c1000d900141030320030003a0405010b001c0ca00002040030a06201d810709507a03200808420544035500226111440030b038010100c40000c0010859409180000780000c1200300840c4c1c0c02240c00800140140000034031041072500007404200004241400b500d61180d01c0520a40080030100d01520304000583c01c1020b076036286c407003400b00c5501220700d0380c1021846640703000702c1c898444000c0540241b0070342d42c20070508000c0c8421800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 117341187 1250 117339937 117339941
    0x40c03050417090111010c0f09090c080f04020103020702130b010e03010203010b0a0804050304080109030f03060806070801060f0e090a1406061c1d030318060a020703021906020f0c0303150d020102060604 89
    0xb0f005140484811400708505170844000800b0b03400420b80002180c6c01e669002194040204401c200808c268400d1b05005440504000c0014651655880000e000c42e80a83d040c3c4c1c0d5010b802504170b6103d80f641840c054004c100c2550002c1c003107034100200107081c2c1303414002c0b28140c1d4042d41c056400d0008a10003a22450805031040b01c03603000074400452200c60901c6400c405d98065942c499040046c064007a00700d501d00d03001241d640d04031004101045802c201c0b2503044030014a0600d4403042003607004c450000c1c5402800e80c1c070600303840921801c0c20240d044a081190064080d08441d16441d0411141d84256102c03880d6418804818440304115544034810f0504011840344055030354140c1c4a0540c0d000712005181028090314444245008201b1305500070301541c01145801d41c2a10041d50f241003a48400c169031100400d000b0400a09030103403009050b01c42c4407140c0350050700003100d84a41080741c001c418071615240398007551030449000b00b100c4da01070f000740c2100c2e00c0b00302c24400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 117342437 1250 117341187 117341197
    0x22704200d06081209040506040209181807240c03081302180f04030e122a06030412180e0a05091518240c0307111605040c03050417 58
    0x111241d0351440000c08440c1400064040c84d02039044954401400b400c1104035400504403900132881400129002e84481080018085400c44521b4a9907640b03085410102e0300c0400e201618040c108001070b4884040300b06061100c5040407040e07101c0180e0104947c140d80088001d000110a000170403403a03030104002ca4035090001c0c101039000c000b0104051b84002c016245484805440c00030441072542c0541080d0481740304130348402c2040e49070b824207540c40a0040303510701001c20901c0e858904000d50b10211144400280010307803a454241021000d4281081c1c140d004620202985505046196201c40650301a42d08900301901d078950502700400d00148400000d1046040c10580c84042200062050b002c0300805032070340c96422401810500c1e4071490b0820b0803002030444400c800b6840701c0710b900002c4400f140da120f546a5800b180c0403c00d84603200c000d4060019a01591015036021100352001602c003030180c114110001c800301d40048502074903c1e00302c0d00300210540f00101c0108 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 117343687 1250 117342437 117342457
    0x10c0905010f23040e06090105030601090b1201060f05120316030c02130630050303071b14030a030b09040f0b0c0d05011205190f032102270420 63
    0x7402c414200500e000784002083e0003424290300c0814100092070400c5521580084240c0300b4021952501e00407a50343e04040c001c4403800b54450301100320036200c01c103551000a80d400001d09c4202d0b900c0314007001d0700000c0c2c0134150207180d0000681046003000400c0715048585117100c03403604240c540b41155800315018080380d1080720718000c2031070101c603130003500041c000721a00802d4640d08440e50000340b002051040021100503152070b800303d00c012054a030b22080508041075580d045042002800a030540020400040c01c2100b00f40c01000002030415850340b07440070042030498104014600104550050001c1c200125000c0098800c0c00310913000121846814180b0b03200c002c181d410380d14260046519821806040401e022007003128001c440c49903041002d2006603615005103020fa540350240511000c020b81520a0440c001c242c0c00c40e0750900401c54880002060300090809002407141c81c0c0d910558203000c4500d000c0c4903200d15040e4410b4800c514800004270300d00140c04c000000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 117344937 1250 117343687 117343697
    0x30806060307120f0501050f01032009030c150a0e040605030d030e010b2106070e0a032d03020f0105090303070f0311040b1306021009080a110c0406061709010c0905010f 74
    0x1070312021100d405060551340c410340e40400d45604000034014051300c008103050415040c80514a4043e0701e007855002c00e140c1070410160740d03440b194046480e00c0110b500f000e4014052610070210080341001600c4e10310300795603032404281c070040108000d9031428080c241e896040181006001c600030340c40402400150f00001c41d21008100000360a90954810301c0040c20000210034150311091100c0c0785c0c0540d0b075052052125003540d000c1a00c020450000800b49441035a0040100c1c81da0f884070111441e161181c05054855440e009442c0d485101e4844665820440410240030004c001d8a2080c0c00a07a24036204e020303081030807000b5004d030300300114501d60b0402011514800c004002c040c104445207410402910f0600001c0c5050030f001020700a080c41c003104c807000a0304102c22184408981c0ca08000c2441e00038508a0034080740b1001140d001d417800100003507054000324010b512180c4440c03040841e50f07030940c0c2c071420f070b038203d0f00307140002414034200b4006580150b42040b400c4200b8a04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 117346187 1250 117344937 117344957
    0x12050306030106090507170a06080604080708070c030c03050615010e1c0219060f020105090a02010c02031915060603020705060f1e090304050f04020a090902160f210c030806060307 79
    0x83d04e00f20703071090328004002116071240101d440412040c0641110f070100041004915020307402d522070034041d000a009580004a45050187e040160b8400d5504009042d10072941c900d004500c0d182148401c40d101c0c01400002110b03009a0766042d840e100701030b1100c0621110b0f05003000b00100781003181040785019682c4040240c0c0300c0240505800310503401807a5442d041100103064008000144011a030510081101c1c0f0400441e1b41f030503250f42070a140d02c00b1038a6100003800c00d808448002c0209045030085030520014215400803c421981c0c20000d20703490f03000803000d034401c0d000050400e5210300b0104442c546804400c59000080d03040382003134a03055113400c1c40d43e542c0546046515030f2000c1000e000c545417803170380618070043c221800c510b00307040d44001600d21091803042d4842c00da404110302a4480e09007000ca5000340e488105079006101900d801c40a410104401c040b4103044e00e0030001605d4041c1c464031b0700154068403807290b242d071503400f00500c50b071000704154200141610 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 117347437 1250 117346187 117346199
    0x30604020103051906171603150903050c0102130603050106170f0403031d0706350a0b120304090b01080118020307170a0915021e0c0106150c1401060312050306030106 73
    0x170442e4080c01d003001d040d500140100901c40d203401c40540c888080c0780c0040380f042000031540c5125000c1220300c3e82d804240074009003001d403580d020ba68013050540d4000a50017698003909035003807050750581c0d10204103d9072541000c80300c202d076081c50072001341400f02c08a11085010500d440c1c0c8180b09141c0401d42940500d03e503084100e041c920018582e005c513005000711a084019985280104032006416643c402000780e00c40355480102c103000020707a40440c61165650b0401c1180381006401108102c100750040c40e40c9074002c1c4030b504005440c0c001240650341c8541c0000303048034125410120300f20105250040254000342c4032009200b180d144019041c110329420321300c220140c5400182d102070a08242c0c40e002d04001075008030b588100418140303100c140d49400c8504051030400d0381c0300d1140c01152401400c0342e800c848802c50315424407402456025880740030940c42002c4030952031034100c0a850076500340b400018518001c24164400f450701c02c2000e9a84504020300201318560b03201 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 117348687 1250 117347437 117347441
    0x60a0c081e03010311040b061605010b091e06030a05030a050a12050f09010507020a120f090306020c01020307140f0d0b180103030e04271704030804090504030e030105060306040201030519 82
    0x2214603542810701000420074070001c05018400000c0a650030b1005410352030009020b88100c2500600c0d0425010303504c0c041c020300b5440070404a50180c841881414060880240c804420308405841030321a0001152401c021a0500d02142d0250041d8145405480d040c0c80581110040104101d1418911700850406000f000c1c0101c1c580e00300c002440c102030000307a0944a00034041019035001007402c90005440c440200070300810303403421271542d0803100e108941d03000813a80094036250002c02c1ca150901d1041d4002d41c0900740f243c449070b0851030302e130b44a45503e000c1c8030711700d4a030688148402da1040e0600d4102000c407220092649040c0380c121103040d000b1601c03e0308140c000506181c200d07082c5007010f208030301b098610584140012410300071400e008035040b0100a1a01c0300070401c1115000c03042007510043c640c40307200c0507202c0b07442e0480e10700141400c617801d600003942466441c00d0350506102d080c0c0151400381c0076140c02c0e035442c1c005501800c0080e14644c0843d003031041c201d002620074 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 117349937 1250 117348687 117348727
    0x30e030f0304030906030e0a030c0213181101180e040b0a061512061208040b090d05030a2607080612070801020706020d0b0a05030a0b0402010c0b13020a08010b060a0c08 74
    0x10313880e0a2040d80c2014001001c542401007a44440d501c07140383e00303011a8000410340c3c00036604890303100d420704650071440041c0200d45001415008254852400c001c4035102c01c440340300c800c1e82d0b80c01c3c40e441c00342d010b0283c51b0704e2441000880e000d0103000c103001c155034416042e400454a10301140b01595020403041131060015580c0020303414108000c60040389000340c20003081100c189180c00215500c44e291680b080e4850242d401c1000030f0b4a021030707100e12000c403c08075080703800d03241c40e856078000280080d000400781c500080707045000032070445042504035000311a6175581620598452051011043c023030b42202080b0300c1031950000d01c2079801d00062031014030884000d601d0b801c404858006852083d100786104c0e4403c02c0d01404240c0b800075091528030f0b08180c0c1500d4a072603030300060300c04200c1a80080d00451461007085004101210310f002158420303200f11500f1a1b841c94440d080791000f40e40581c0c01282041249189449945003000b6680100426494520301131601100b28041d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 117351187 1250 117349937 117349943
    0xf09010306091401050601120e01180b09010c0216030311100f02040807080d0f05071e0807020117010e06010e012006180d0207030303110903010e0c0f0f060406030e030f0304 76
    0x200e01c00d4000300300f1003410210f0300610840007032200b1b04008002038440040624148182d540c0e92418100da04d00941007900a0700401c3c0100c0d032510300e1420701c9010060211441802582440c0051110620008000701c8505198499892803421a0340450b0024858041184c8910a01016603441401c5200345c5401c0300b00c0803401607a9516120000b810710540e40e0000425130054000211110303048111420760002502d03159542d12a10b1070189020416034560000c00c2d908140c056041200d0740d00103100030344c001d80f115003a03180061400030100c8002d0050444464204002c1495540a030414a80403001410900301401440104c02007050201d920b100c00c0e9800801801030307410b1500307460f0340c0a4203500c026240c80804c03140f01071b41d901030302c1c8002400c040e5150441c1565110300404d032648581e008009020103e002d601096854031041029485826200000c01e65441c1100e89550480b10240010b0f0400d4541141600102020525803810b03000030000301308002c0e0490011845144 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 117352437 1250 117351187 117351191
    0x311010f061a090310020318070806041703090a1e0f0b070f020d0e190e090607090902040e0a180b16080a050f060f030c040c0509130b01080a05060f09010306 69
    0x1107085080d8440c02c92200e42045011400c02c080b0005860101e0900c0704961440c40c00f507620303101c0d1071a1000410022541039044c0c09105000302d4040310209050b80282e0052840d040480c454005c0d0040c00e1000b40c8085105038400c2011200007043d040d05011a0609048440500d00503a110030400d00c40d90b071011144018280700b0003c83d20b0304492454080c042030320007884200803807030021b8105001c1503070242c070495120040002028941d640070001d08039400040d17100303040c0402c1d140c3d40c61038103445480114064a0b40803420102600c207540489500c01c003002070680322011250b000348a000c402c440110110009003001c40c0da240c01441c00b4042d030301e5802d0107602c144900240100b002038920f10007035040505120000402c0c4440c16080001201d4038060710154200091410341d42c800c40c190042d0810207440307041604407005e02120201aa0041c0300d00410f1a208011100708201300340c041580e07030340460042c51460388816070251000e410106244040d40013304040000da02c1102c2e580e0b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 117353687 1250 117352437 117352439
    0x19120803160e090f040c05120d12020a0905062101030b0f0a0b15030a061509050a0b16080c01020c01060b19170106050a090b0d020714030319090311010f06 68
    0x11503030095205101c080d89081140400c2d11000201202c001420100104401d0008a02480a009400c00060600603c0c1e07a044422041c0da19442d440d2400848003c1101e03510002d2017401c840c000c0f03070b0b040100c0d030b40d0301d4222740c0c241000c11106800005800e10344400c14442e1a19135440403060340d0186025042ca402107207040082e415452000070b2850580c03504003512441240c66040c01410134141c500140790300da07030b02c40301100010b088990240c0054440c030601031400700c1d041280001600d00c107031503c2c50407980301e4400502c20700c41d486107c0d05440503070300b10001180040024262a0700d80a0001d4a020f041e820203900351810350304240ca102c040001e00d0303d8081c1c05280742845010716824688203100c0d40c2e40100086000501c40d42e003d000e000500c1c6040c5510603854040944009030392552205804940007009410041c011039960504000c1d14803000740c00015240b00e42c15000781441aa94030240140c060050080301320184500640c641890f25000c0c040c041c01e00304207240c001901 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 117354937 1250 117353687 117353701
    0xf011410050d12020124050a080a0b0604020a05070c03080405010801080a0c03170d051312052d0702040513060506040603020607080702010c050a060903020d1d19120803 74
    0xa01005480540d5904958900304000e89820360040240c0c0d03001001c01c0302c88401884180e0241c1240540c11340946030341613201d0a00c0d94412178520942c0c90603a03050300020740354074800c0d6654011a00240c000c294000014a8600c0c0070f40090010303000300d00e081c0742005050356480a41520603042200c00c684042000d02455900605040c014103009004052000311a211440308600c28000031300000700c600011101c2010410482c0c03030000c40000d0804c654a09071907918070514418804580c15030b0805801d01d403c900c18410f4852444000300ac1002da2845116000d00384025403a41820008003404081c1c090b907500d00c2218450081c18108114a030072500d0300710200ca038020320443c440d619050060015032255070a840c09140d00c0300489544200c1385c0016682d01920f000c00800034400c248607001004031940010296501c25000c403001c0c980505815941c480c0580d500000e01045003101000c980b400d601c903440309006040e034210925460711124140c60240240659402800006220300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 117356187 1250 117354937 117354971
    0x4020f130507080c07081c0b030307060f1503032a140f0708011107110604090219080f0402010503070507060f0e0f06090a0b041511161e052d0f01 64
    0x841301810074024600b0b00030790354000c01809485807210032011900d880c074500560300d42c89030359400c2c4000c041340e4a441007842d01601030b103074a401b40c035841818004ca10f95210380104000b000d0740c0d81502d500496120869046000a0142500c041d852500007040740204003041a230218400b45030f00030b04420082d20b000245045816800200c0c160b150403800c81c01c003c03443d030030b942001c3e50060b0781c1003120201e0000640180542c0d000340d04101d200141001284410410443c41071000d40c4888583e82e890401a801d00318003220040c1c04603400b000080c2c040361052006000303052150a002a074001ca800c02e403c21542c05239000c03142944104070b10241200c082110396481400304000307201c800c0040e5904582c950024000a09007114035241516400c641d410012182030411400f46c2c5805c22403828070415030021750141e560309442d1002101640c004490f0f203c0c5c45030031600a00a120310b201500782c41095a0980c9045161809807150030740205014441080c0c10120011034010b00b04184181 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 117357437 1250 117356187 117356191
    0x3140a08060316060e0409020a090614010809010b06040302060d18230f0a060c021009081830070302030a06050108070e01030c090f0f0203090601080f030a02031204020f13050708 78
    0x43c102060f000c01c2110f81c420080909140103031070114109441d84085112400d494021440b0f041c00d03d600429200800d0b18907004040c0300741c2c0d81c540203031100b2a001d400c840034911030b1307074018604000c24009400c106000303180c1d5a4014000242d0308080d40d90b00000b110304d8180466000082801c0c2101304035403070b003c04120020400281c0280c85030400c00315038490b003031100200701544070302e03003e40031314002c1c03110640c071070f030582418012030400d45800980f592080722090030002d200c0d18044aa403d000004021007064840d0300181c00360000d14a0442203080351504020f480348100200058806111641d00716210328408034842d4100301080c0c0c103122403034002c150886659001007011034a02d03941031040303600410001410014803034007840030b0009a61010200e80c000028170400e100f0006040341210305104c2a180105180c0c000c1c41d03141d2244401c2d180043e030052200d02495900d06a00a4000b03200410101508400d2400f1410010450710022202039851040010b403a0700141500d03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 117358687 1250 117357437 117357463
    0x31e030c080a0e0c1309120203090414090d0c020303040503030c1005010e04021f0909020307111605010e04050c0c01090f05070824060d05120405040b040515090403140a080603 77
    0x40f082945818055503141d40f400d19080c4209200c002e94018025142d000314000354001c168040d80c600d445d03101a5480d8050414680583d1404101136000c0d003542c07003024022075018010300b1000801da40304840c041c4010302c0c166414041040700044a0303030100024101c011b690005014a0f089015140d411607905a01444a04909800700001070782c0300440b103103488103a14903140c0c0091a0317000c100c4400181d5040303884c600c2c0c800030a0013002500403050f492440f01c010202c0709170701d0610b060520302c03540f5841a40d0104080e5003240c101c0380340c10b41106030b11100d02c201e00c609200f260407580e030075501010400e070340808030b007101001448070034810310700600035160003405ca00e47c418070a503000b1202c075445885d1f031280784808903100303a6600351014100d681290885e01000100c09a040341c1e0303400380c4141d9120b2850103550215070305060090a20841c01550b04c1c641481d55030f41440b0051000400450403c40340a0b0f0f4102c008001e00301825003030a890383c0710904d92528806042c54140465100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 117359937 1250 117358687 117358691
    0x1b0901080a02011704050a050d050702030f0106050a050f01050903030403060204080f03090f040504050118050d02011505060a2304030503040608010801090f170c03030c1305120309040504031e030c080a 88
    0x7003400b43c0d0b0031100c0340034071440004548110342e480b801c04501700085100010414010031440c0f186e81940130700036044c40c1d40202d0585030802c8200c43c5c064201c03a501d1040325004400c6240c208000d150180e891040c00f00c06040191801031000d00103401c40c1d21540048640d698040340600c500a410040f2031001c154010045181180da400081c4503180b803c039400b44941e844000140c00c001d07003034201442420244080004040e96031820684540340e40070683c0040d07103005507000c4041402800c000803120050b011500d45980c1500131200c050503200007084510b00031002142c20010303400204011401000556291820150028404003041e807207034610368101a1450046032061a00e00e400c80d600c124114525003c0c50550302981c021800036010a020200421000c681014020000140750f0320084000300d4860080002103540780c00c0104143c0d00170b005030b0045003829400281c005002e42020803c40042d61508021041100d04501c0040d4969918540302034000e82c4480c1c20103900c0c841 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 117361187 1250 117359937 117359953
    0x8010e071202130209100e0102010f060e040b041a1e1005060d052e0905010b0c0303010317160302010c020c120d03050a020c0601080609060703090308130309081b090108 74
    0x19907a038140e00804040d100300010b1550a4000c2210340c1110729000c0060520406050343c240d01910000c45022154055405d0054545c4403001a00c100f005440781800300e40b0300b60b180c0f511898243c072002031040300d103600807633800d417200500c0c9070312248a00c0042034144504000d14444448820b000b60510341c1c4000c0d03d003c21701007540c4544c2507580c00c140007000002e0035500d841083c0c6001032409842c0b40d00301d119281c591110040c0d00821000d5800040c0c0503c2166650b0b01c80d51900e01c1240101d003241e41091005000080005150710320b070a4985008038140442c00070008804002d101e800c03001350303640d41c0000b108c1a8041c049851180411100c80410071a000101901c0d40c1c505164801011740d10310000310f484409038152040c0c0036198040301e00d1503844440b104d0755480242c2d9a0541c912411000910aa11030300640551690598529181e074a441c400f0780c10100b45510210240028040081401c540410a02c0b00982200d4401c5102d0342c0b185042c040e641c201078010400319084200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 117362437 1250 117361187 117361199
    0x2041103010f091a190312050d0518030a080a110a030614011e03090f0c1d011e0e070507023c1c020112020304051b010804020a0506030601052208010e07 67
    0x115032690130000d881a1640e20456028030790740d035070290002001d1a86412411000d41c0d40b141c06050302880d0300c1000c005a4941010041074121078414401030f91340300700b0078654850302c100d845039000118200c1c042000f5030b202280c48000c0c0c00011481001039036039134003000000c2103840c4456400c0300a080402d66603000c2c01c0c3e001100325030099600c0902d9280d850320010400f48041e5196007070340101000035500d803500101d896071841d178800c0b2141503203800c0002c00c200300144207081e580a01d0440400100740b408140312201c031030080906003803010501c81c41c0c003da1602040a5150b2045039071304d24507030b007450901000b040c00e4001d10003d90503c0341030750103040d1100c00120641c48580c804015060440e840121044900a420001018004000c1c0003c001d0001030712946422600310300740366a030000e001118078001c02c9801035840b40c116001004241443c0d8025604105c044c07410901d012824114860750712003400040140001e8007004120401c0300380b103800a071886a0f00500490b6107406 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 117363687 1250 117362437 117362471
    0x90b09060d030818030405040e0106080706051303110f031903020d09180b040b030a0b0a0b1516050102090315011a0304051e0717101406030a1106040302041103010f09 73
    0x5101000c084500d446505141134104107840051600034070500028080705000c40c043c002612400e0314510401d00c010030494001e02c15100c0d2068030550800d155851901ca0981c0c29603400c85443c2c011070808071480700e946041c049041ca60740360740755903111407510707141c000d207000f80d40b010b54410814040000d0010700340c2c607108403050711115140801c0d4840414005001003461070001549481045544410042d441d20420b10405807240100501445c40007444805005032050788058281080b0944591408100c400e135900e028900040c14568404c020030329089000c0c1d00b440b440400580104a24441c003041c55160a031070302c610600f5400c00d95510b50340c888442091603183c101003840a219a0401c00c07061000b000074a40c45022800008215034030b508030704400100c8541031841a051130350403503c2043c064440a00104045d41c101d44502c100e82120040c4550700c00030130840000940d413940902c820040710744c1c441664035490001481c07110a02035001042c8107042c1200b0400000001c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 117364937 1250 117363687 117363691
    0x20609120306030f0d090603180f060e1002040b0403020406050d030e010c14070b0a1d0603060d08070c03050d110106150503070215010902030106020c0301110f07080d0501090b09060d0308 82
    0x1400381e4a07038803214006030400300004500d6540f0b202d07807440e1354402c0c2d0b4401c04d40c00031985ca98800f04803000e001d110402180c403801d00c02a00c40015102c07401c0000341c0c00e5001d1303400400440240c800d402e510034242c005907030165105810598000c5428825850684035007002800d04440850307c1c0c000654000d444290882096418411070b940a201402003c82c089150001040c0550f000c1c40c2c0c07100c0c02d580c4250000d4080c00b0014034003142542083c111280c00100c6441c0040045046a80318410170492180380380048981c48014089000095261054400514407403000b4083d000340f0414001c0c0034940011203034409030304000d81000104a02c800c203400e070310032914243e90740c1c0c0d40e255010380c03421142000e24a090602da100000ba503085039800f0b141651526400d5500700b0043c40101030a0300e14082d690104448100100b09884c14028024044244142c5010f41441034088480c000c60f1403d03485429000e403101c1d440714040c40c1040840b60f0200d012100036030000d00a0310024100c2c000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 117366187 1250 117364937 117364963
    0xf050a05040204050a0302240310032901031202010906020c0604030201050705040f090903110303040507031502040b0f07030e03030706090b0609043c0804091419020d0605100302090907020609 84
    0x80050810441c400c07861030901c1c2201100c020541d4ad040c04040d0300300c8409144800d41d04113020304905501c4480714035003e508080141d9070412980d0039501c41c1ca01d001c0389940600c00350b6680e404c0c07810028107540040e255a1a031035020f03011528260070064291440201200d04122041205008094404480005070f59408800060150007890203aa99084c1104202e249101c00700c01c00c030400000140b0310040d20300c280c080b500680c1605011100368091409105120fa105024100d00401010007030031005000307181c862580d00c000c0e0701190070b5922203c1c0540300b0584640b0300c82d091003003410040c0c0c2c00900c16076230354a103443d00762100d100f4041590fa26400e5516404188800490030701841d100050209003140300e641d80902e008a0250f200e44612a0400e081c401051540000700703150358030401d283c0311036401744003990b04450000d500181c0321a8200390359600101e41e43d01c0d401c000714125074094130b0040c0ea40d002c0804001110350010501421944070400308070204030082201070300452 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 117367437 1250 117366187 117366199
    0x15020609070315021b011b0e01052b05040309062307080d09021509010201050903040509160306030812060f03010b060a030917070506160c0803040b0403030b0a0f050a05040204050a0302 81
    0x80c43d6151002c0c2c8140b0303002c15100fa003421010180301c0c5040d40050b002811107001200542c030081e5050b20740c403000308000b0703005c03903024442d1f15450107403c034450f51899100204150200307101c49468088801c00d0f50140c0000b441500d06014586d04005111050946045821a00b9000c85a40300d042d20414100420380c650120b1400d030320001daa0481100e480d40100422003a041c0616080d4040c4c0103858824010341c2002e0103d29400004000c035425a54084c00d0712110b940c841c1000b0f40e02048000d8441c04040d502e881c00030120300b450015004080566917858194280081088200b02034030718042d11a9140c107500031821b948000031110201760328200402c110740390b414455280d20121070020b0f414000020700350304104000c0b551034422061048940b10a80c00c46d0811107080c0b9a602c001058544100003080104400b11710b8254842d11914000c00e1601200c001f240c0d050410307134408840401e50030300a0009188c4103040741c5c0604bc080c0c4003181041e1030040003c5028113030f8031010740264 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 117368687 1250 117367437 117367463
    0x507060c15020f0c0109050c04062102060c0f01020301080106032a150c050102040f050111030313061a04140a0c030209010203090f0d0210050915070f0308060102011e0204150206090703 81
    0x510860300f03862121300060000c000f190b2103420300303a491b007890030403151107a40b5054020440c8042c0d01c05000d001d0201c014601caa84c00e090342402429030280c1c905020610031f1004511900000340005c501030100a070002c10b03500c0c0b451500d20078008025014900c1202018400240070304101060300403550480024400700c07c41c0001546c1d0b900d00d07000064207a5000207408544801e1203007000044034000c1e039421740480849040940c41e4001070702c015440e07504000d100d9021900c0da41000000c0c4070322030b00480005482c400000e00310f6640641901000000c00104100000d0500c5001c00101c02414150300e000d440000003074992181400d42c40c850384003600d800c5659218208421025980a08900800303c0f0840300030b415600164030980c46100c118404040f0700c0c003c10141e4a8032a4131104e407660202c01079405840f05040205114115981c1d02c1200f0440c241103030310810220356001c4016619820103541d070310b84d00c41c001c84100c2903620100600c2112000090740b20112600726440340e14203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 117369937 1250 117368687 117368707
    0x10c030804020a0815010e0c070b07030c03020f1605121303020d060608011103010305070f0b0301030b0901110a050702090a0608060115090513061401020604110d020f090406090507060c1502 83
    0x1103203c90300030a01e148502c41c0c050a2580d8695000c605039003400a03a060180c1d030b1002078100341d1003060001444012007001041884d4000d0700247e15040550802605080d044002200141c000c01d0000c0340e608250b80c0900306010307003445001010f80441020614240e5012074100c0c422105102c02030150400c000c0342000d100741d03580404050301c10140240081d03409644240c07a245c00c28002a00c1034000c10310300050f020250a94442107601caa0261815a0702c3c64072001e026240007000d040e015502d81e130b41a06041e02190041c01c4031103164450700d81350300e0140107000000100402180d8007910301310f4180801400020742c581110002080b4121035000808200c840414680c410b542240d8015880203104445030401d1043e00c40c4c070481c800e071800c0540c0049a0f02c960541303000e88515101c075800720f0541014080082110300103000c0d035032491062400300c0e003160801c031030954925a94510f50b0301082010700c01903004100314980001100f507240c4580d00c0c42d91881343e214000390343c009580606c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 117371187 1250 117369937 117369949
    0x3011802120718060c03080105010f0e0d0305210603061f08010e1f1404140723090115021203060d0210030e0f030c03040510031103090c15030402010c03080402 70
    0x2640201942941c40c00d1020000e0300b000000a506100114420004500300d4800e40380ca040280e0035544100d1185d103460010341c0c0d850303544800c034002c2001e405850340365521000f950303d00c464465540c2c01e50b1380b000001d940c070800c410082c5542e0803103403203000d0002a0350002030160304080f10741c407079000300e55409900300b06240c1c00c0d9100420031350800303100c05803200f0040f4031410342103100d8030116009004400c04030125440c405420310329209020100b4081503e649868400040030b81c111125147c840c2c0c0405c01d035a004240d484c214007404403c0c2d40300c1d414251000f0b801001c80010034121900c9d003001c06074a5180304001c040031900003100042240e50340080210001c1d402404019400e41d44100048c0600303072003007110b1110322402071070310444080002141d1074804050042c50405040c181000308502e50320503200304160f00e4030400398200300c050303000b940a103842030014101030301000140035030112100c0840000d000d043c0104000f5036082042c40400300d07410715215505969900c00901 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 117372437 1250 117371187 117371197
    0x60b010306050a09020304110904051518100e0d080f010b09041404080c012409051f06021b03070f0902160b13020315040f15020405100512071403011802 67
    0x43e0201000308002240d1030280c2c000d41c007450240c0044544011b06500b07014024a007642c008010b50300510501c1d0020500c01c5440ba000b9001052019011030f0305a483d5103441e500e41004841c50703a130f500d58024000e40c1000040e45008850404822030300d0014614209510144540e20a9210000d626840d03a41d84d503200035500c01c0b050b04545100d0425041c181e80b40c0e001081000c0a0b503180241c60384204036038115a009003220740c1b1500d004c607030030084008045e000180c0340e00b080c00006460885810120036807140a41220341c010440c1391800e4010b02c0c807520f4210311080c020303040038805101c0c24180700b2200058503a072134009692603080040d81507112042403c06030811440300e0622210680f01c80900e40c58a008030101c68401e4990b010303074040070200b990300800022043d98140002109455580e4840c0700c064001410640e444d000300c0c0c540e40e00100c1c1d40001803070000303003181000a43c1070340c01d41118041c503041c0c01c203004440e8154024401030044502000801c3c41d80c00f01d48e11160101d031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 117373687 1250 117372437 117372439
    0x5040902040f05040b090c0919080f0604150b01020c06070813062003040509040f0f080c03130806190f09020d080909072105060a050603090c01110f0a060b01030605 72
    0x19510756030741045055019541c01543d2055042c0602115646421580780b030180c00c08400c800d240c0782c01d080401454008440c41ca8121080300d2000146002c8180888103900882901419503450603150005940150114241d0214502404d185550341e001400291400040d0b4072140e4403100d50030f0500582c06800d50740d10495808a4000c1001036001d4600d82c1900710007101e001500d20b00c0741c85071351640a94060680c005100400040106110503002245c043c0180c80c42d440c10440b41c2c48610303c40c0e21102041c0025440000e1440c0c01c500015880001080e9540c05403289080c903842048943d95400c162182280d1900302c544c016401980c0206e00603540184943c120107524900b5460913081906403a200311405000141d549000d80f401c21011420f2004020000d03804e00607150041001500c905d0b0002c088040110766600c0350700c019070044210a0041094544140c001406101503400509664010481c0103034a60300026030000401c2d4080408a4500c4400700101d000717050941c409 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 117374937 1250 117373687 117373691
    0xd050d091e050f1b040b040e0303070e0306010e090303040201030c0306050418020306010f0b070f0501020d020309030d05070f0507030509040b0d0f0318030809100309080a031d060403081303050409 86
    0x10514070140c0d40305400300a1195080d14011039807080e00c2925000504c099980c00c52002c1c07604600c40c9803070b900c181460000104009000300c60b020055182d9001141e40801040c1c205042d00c03030394a410400a801084621517040403403614017a020f0301d83c000500020305042e00d548054540500a401420150401520410080c5030400a5074004080b01e00160300034090701d0000f01310840c2c110351070b01c25900180c0c6414509001c42d5503801d01c50b021804c00395010f543c00e20030b84204007000d0004500500540000359241c02003003058038111040a001c117401c1c0607461280d00c0b050354101040e11200742d00340c1805516401c0200c0410050582c2c510039640c0054040b0400e02007003481c140b0080c071903019a45a02c0700100b621415100d05105000c050889541031050148920b00010044a00b1040d8500490200c1440d074541807160844403140c00400d40346c200c2c00c86140c0c08000c5140400c1c2c800c0d0001d00040c14140c60203006000c010b800a419580c64602d1241414021070032140140902c41c81 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 117376187 1250 117374937 117374963
    0x1a030613021201140c0c0c0301022106030714010c0c24020d05090d080903010b33030c090d140f010b010e010c03020d1b0f0807030f0c03020d050d09 65
    0x800c05800d64100400c920619803050403010b40396051140c80b10061580111004070b458604141d0802c0e00940e4161000344155480068991820f001408000e01e1100505c940c1c0d4050202000d031814000b41114040ea01c2403c080042120204070f000010320300f07081c401c84100440c1000d4a41c1d03c4203070000c0601800d92048003084074100d00304141e41c1c090319401da844210015034111605d110ba03c000d00e0340400c03c420b1070800320b04036600400d101100140005400706694000c640308260140c010340703c000034403403428030185008110604811224550510794030f403c26040c0c503030740100c0d4840c902903200c1c003030042c0c104809030590080704c0d01c056048500d0540c011a5150281c0b020708a82d500058400440c04110750050010003030b4264140c02611500c01883d400701d940840ea1124904441111022900801e0110000c0900280102c032501e546440078100542003000161295040000348000d100201c1d5001c40c480d61402e401d0325041c1d9864040c106540060210882c001c0e00c1d484060300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 117377437 1250 117376187 117376201
    0xa030504061b120b0d020616020a0e0c030105060310081f0f06030317070905060f0406030b06032401021c080a060e04020901140303070209070c02010e060c1209031002030103080409050105060f04091a0306 89
    0xc500508a03100310340320ac0c030782a151008072406080542d15071800150900052081d0301d080e9010315030044c1130302c4641944544d01c041c92443c002010342c0001c3e2070400803071303420709110b00c901a00380c51840501c0d0a1101e6071039650014189003454040160000c0340c1004980f2036031080107103400420004003200d8883c0752402d0f24100f10b5120b0321501011a241642110b2942014429a44030300e400540190316098410403000200c6500e82000d4118050710211100c0b120901418100c62400c565803c1c2240c60000a080125200740d0040000c1c140080c04020050b503e860b0654195180302c4818100304400d031020034514040c159000b54030407090320401c040e07117901c10181c140160007640c032490707849134000c1841200d01c20980061159002015080d0000c0b4511000b4462254090112804c1c070b803800710b00340220781083c1c10460f44018001000c00051407240140d40c050072013150f003149400010000359907248541e2060714a266100d08843c0189030900010212031903026060f10a42d2401c03407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 117378687 1250 117377437 117377467
    0x180f120106170d03180303020702041b05040918050a14030706060308030402030c1005090f01050412060b090703020c06190b120d0212070c0b1c020a030504061b120b0d0206 75
    0x4507007040511840c0503c40305580700340503120140e905501c403c441c404480e1011000303503000103010f81c0c10940310400080c0387e10071101262200c41c082d40d1080c0c0c44906110002d0140d42c01c10846194408510040e50041030010500c1d04807158032200b402c0c0407009529501e402d50081590140c6902e10b40a0000280080c4a00561003140300701d003900c10910000003001504c0d0003040c10040014414003c1041c3c0b401d0001d80140e07003800504210b0300f041e075201059801d0303c80801048850380d8940303503280f009042c0b100c41c2907001002e900701581010000740c030702960b902000340020141c007180242c22051440d160303c000c03101d43d005030811041d68601047d050382c60060075101c50043c030a0a03200511000e02d0700560b0340c52603014485108503441c00b50058041c2e080794601c01d0008038402110600a012803004200c010050b8a01017800d2400c1d0900104407001c041480c64000c0c00305404d010307010343c41409c6924510546070001801c1d41c1e0940441c50201c15030030000c0d00108002000e0895800d09 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 117379937 1250 117378687 117378719
    0x409200708090f030102120c0c030c0a05010b0414040f060507090801021219020403080409021b030c0a021c0b0f0c0d0618112104030216060f0206070302180f120106 72
    0x10f5540010261541c0305240c202d120b4186014080c0c02001c0108041c030894600030040d00c0f026000700ca0520310700451360741c1010b50004d01192160b40d1200e0003134190615005542e91030f03c0c8159070185e03e1809442d4100000600e800040000b0340d00c00c0001d04003400b074030004000e00010340003151111211000c0c012040000d80300d050b0300009180d04400b20000b203000b1135043d41d9010903443d0a191a100c0030034080e420090303060360400700d629070361007003075000300090101f000c5440001d1940700802d00600040480a200c6c0c10018548428400c0101c0e80390101c50f034002c250b416160403141e40d2a0902e1900340204850000d020307041100004000149400d0310b0303800308031460104071018803d84030a81c42d1041e03041c91641c00011811103120692000400e590281c001d00540e040c0095500032166901c0003034008030042101028112181c07981001801d61249660074110714100015000000070303d941140c00d80b00d16100d0501c0c072100d45403081001365603140c0714020b001494440303001d0b800360000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 117381187 1250 117379937 117379939
    0x5030a02100e1005040215071203060e150904110415080c040608210c0105161106011a0703020f0f03270a06031109090906070f02070b040920070809 65
    0x40c4140c207072030030001441070100590b00040140060020402281d02901000300166405040e5024074450700e035010000b40034141c0b20b0003105c04c070746404c22406800c8036080c0c1c12280700e146003d0108880c10340f605801d188541c90440f48a034041d902e502c0d041e00d8070703d040c06030f141d041810841a08031071100100e458007070b62000000e483c1440550b0040c0401c4401a00c0381d003140e588584080840045a48103000010343d807a03200b0740c60304070038000040c01d4032000e942d1403001048014001000b2640701c0128261208040090b240b20351405580041090854801480a0000154050806000f0444400d040b0952002ea64207010340440f4a501c0350044800b8010800d4080c0300d21a004903046240b510300b0354010030f0a62100d007080320403002050182264400403c0400541007140d5514820b948160f0405008094038a03040000502144040c0a0001554419901030062019501c251810359040010003d50b0b0f843c0300782c5604078045504200821301400140c2d45d014441103d000f02a0f20300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 117382437 1250 117381187 117381193
    0x90605010924031e0c0602060105090c03150909100e01060501020c01090608070e1c0507060e030c130207020315010305030306040c090806070e010915030e060f07020a0308040c1205030a02 82
    0x1102926840b401a82e108191011250b40754090000a000310100113110311040b0500e00b030300401d40c0d0b50580e80f0f03030302d90498409a0f01580041180d4502001c2281e40102e541200c94114203242501e461100321050a4034881d1024a0004104500401070b00c2003480d20303420213100c207030b45146400740200740d0b9005150040c000c2040d80344007035011780030000032075603031b980d402070306039101401220b102074000c02c9107601c2420080728000644004136a00c14150140000d0000f481ca0480084c080c4101c101c03160740240c012404e0a5a150345107021602d1043c00007030090703901d00040c80020300300480042000e892035008000442441400005144154429101000174002d030f954242c4111005105800299022200007110140309900014604034181000d09080d62200400900e030040c52074140002070740c508001c0c00d100e600308032081d0440e01c0f003a882d20b050b0802c1d800007920381d16000ea0107401d0001e030401007000c01c01600c0c940001003009000352034000003145002922507102d1510100188 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 117383687 1250 117382437 117382451
    0x31806090c0e06130c140324010e06040308090d0f030f021506100c0609061a0a05100c08180603040b09010c0206150409060209040507020a0c0e010501051b100906050109 74
    0x14903689400c5005502c004e04080b00405801964000750820581d41002c00c40003060a80d903c018007400b46026107415400e4210703603040d0b224040100a418001c042c100000e9070258021500c072031040300c0c10707a500420a5944d03800920085011440d114500800b5107100300410014141c0c098080e01c0e42659560135125100b01200c0020454042911169400f444600c112001c0d14014944002e00c1e5120307a00214820042d03403180c1080710001d41d203840e2441d0403000c959501d40380c201d1003100940740480c3e44d00100401d01d50002d002c1420220000c0c40c00030001245c001c56020381c4c240b2051548000c089554074501841c1a800c00c4d241a14031110700d600741646882254004111184500b20b10b07109000c16400034010000075003c0800c0a0758427a034208240400c5407914026a0310902554008004a119034940104615403036845202c2c1000070170014040e91303a00c6011604c11303410313080400d0305045d400482141040020140d000e801c031328000e020020400b954000720304075405048200494 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 117384937 1250 117383687 117383699
    0x70c0806010e010806160e0301060905100911030c130312031a0f0108160909050f0f07050f1c060803071a09010618021602190e100303120903031806090c 67
    0x1d00d10a000e111403e41004002541c20300e60f0101b0030702d00305c803140b5080d10000e0781c1a000c207003180c1050304013586040d15801045028505400c1c08801401e41100c2008280c0b40403460742214003014041d0f10044c04005040c7d21407886a40c640c4000d182c0021028156a034906e5003c1c000700210780340226075030342d101012022841c10185010000704180c50b05141956000f50401c2086401a00901880b001c6080880c0c1c640040c4aa94800d40c0d4400842c2d2940c10036000700724080380c0003040e90b010040c041203040e40003c0030100350ba50303c6210003002405c203407034160501c002c1c0c11160085401e5100104400e0244a0030b2040000582d90000c6030b001551590344030f4a003130300e1450162019800802400f02d1800c2030b25030043c140c20f50300c2d5288103070480782030340082d005e0002c240c0441560201d909003442201403d903021a081102a00451840d030f15564001d0f0107200c20794845590b80e55251102d200307041c040d81040180d118000d018140d50074851622030020b000490003a1280d0841e5031000c624 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 117386187 1250 117384937 117384959
    0x109050108070902040312080c0d061205060f09071205030403141b01080112020105090402070204050708072601090e010e010213030c0509040c05100c121d0d080f0a02010e03070c080601 81
    0x6803600039207c00d000d4000020259070024029240034090300b0100b090142510171881100050910300c4801c07040e070350450034200e1070030002411802c49840d03100140404214009a11012100c081410302d0100300e50741040383c1580078075030001e01071511040a003600c00c40040f519924115000c022030010210b00f4004446401090180d02c0150b03444850300000741d03004801400251000810243c68008c0b00d5001c1019900c040e10503002040c141c0f420710032400e400542d0001c1c5030f14013240010300422054040c80c0c1c1000d0601ca8000030720341d5142c039000400c400390844c1c0021810540251342d11151440e00e141008910321003a83c0003140550041200d280109859001c0c90b000792640c0c07207036400c5c00200f0450071003044160003406540348040d0009990151a01d091030020f80320b001d00071401c4002d0f01d568000c15030034070748160322103105800090792000c10380e1401d030703101503030706894800040303060b4010001801800c40c51b1001041d4001002807090810003030310b4241c0140d84c805d0b40e80f8100500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 117387437 1250 117386187 117386189
    0xc1903050d0f050a140c0a060b01111f0e0f010504080405040c0e1f0207031b0513140f0603010e03040e0403110708100506012a05010e15011203020307020306010905010807090204 78
    0x188040000d850910310034101420300317010b0190707001e14004281d0903080c905124240d0482c1d4040d03c3d40c0a9080c1503030004400403448442202802880611081510740c0d184414001550340c0d98405001402480030000c4c440003c40700002001242440e0038205140c2e0002d00c40c0b148207074140142c00200600c200b1901c1e03405c26018019180b48100c000260b88004114182c48046208124002001c03c2c583d5444005014021144401160801c01805503030250250242e2056041a00d103e070259210149a40d100240d0b034003d80c4561a910700180c09003910240d02c0819110105d00031034521100d2961394080c62191301c900b25003015915100752a60050b00c0740c3d20741e035001203e2009541038035401c01d5902520525200b60801c5d8207412420f071410fa04c82074100d802c000e0310544020807109100380baa03c00c001b07a00522588c50301a103803010b001014000d10350b0300441010042c003018000c1096400380b542c001e058803120343c0c4450903c4c0080001b4826500ca5110b4280c00080c01140c074400c4030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 117388687 1250 117387437 117387467
    0xb060604030b1602031201060302030106090b040305060423030a050d05010801050601020303190f050c0d06060827010204090e0a120e060f090d05071829010f020c1903050d 75
    0x12542d07540d19086030b1002003075006802e0543c00200710700a03c1109148219020b08615100140c80794100200148110070769000318400f600700708814004528001051580a5444080075600d02410004251820045001e2034403a02c030106111146d290482c002e0068010990b8042106070398480c166401e8034429254540503810410202d03901050800300ca5043d080000742c042a10324207500202e003299021500b10100c54808207184a9580943c082c80004040b145000c40c000d0604041d407283c1c0d55a000d001c2d03440703030400156501540300d088d0141d03402031482120401c00344941d8041aa1180104481119038440700765510302d0490068200458060000e003031181840388107041c1d020161f102140f1198070894440541001807001c0240384040c1c00c90300801446041c0c031fa05001c00390f030106e030b030807a07071040514a064429424401c0004a83d0100746844001903400f07000c260305010f13408078200c1c1c0115100300e00006160622182000312441081103a64001d03000508580074102c040c83c613 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 117389937 1250 117388687 117388703
    0x90b150d0b090102070b071205090601060504140d02100504032102060402091503120406030b01140a050f070f0c1401050c060103021203160606170d020a02060d060e040309030b06060403 81
    0x110208852075441d9910903052000103151510356229020080000c580c05000180d04d04521415030a950041a030400c041d200104487e5040c80800b800798029400307011048003100c1d03641c443e140e440d118030482a0380c0240803003103401742082c4001c1455110780000c2d60000c581c20005e2080303101810001208820703035405048562540d40c00c000c15042c01400b1200c0b41004501c10203020350b000e0242040c40081c400c0140d5503903150840240944102d0041181030102140c2441949450b000403505a4000e03403030459900c0010103681c0c01240644039003d8802990b8100303603020006e85525079030075500071288680c514622000115014840c81001d40c000d600240010001402d02010031903640d81e0600a490502030521002d15200142d0b08056607007984401c0c04000000d101c80000e941d100b40c100c06031480c5600144040c0d500e4822000c001d004900002d040512040283e00c028060170303001d000c4040701c2c18070307050080500040307010a8588050710800300f0558a04081181c0850360b005d509 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 117391187 1250 117389937 117389959
    0x1030803040609060b0603090a0b10050607020d23010c020c04060b1905040810090c06020d050a11240a140915190203040b011805150f031f090b15 64
    0x94002420943c102110315588a89110100d642c070040a58429804400140801e2080b030400c10414000501282c03031100e05408180300c9074807500f08440985070140d036603100740081842d1808280780c1d55041d2180d001021002003950340410740000d0407225030341c0e00316980e44210a041008440d028070a264603140100842205039a410b500962212400d0404904041c0d585c482c0070301b0060f8082c003010246603203036a501304001c40005034001030400c0b8401440082c8111402410610403c90368000348441c9041c640c003900004c2000e0070f86407003104844085210003480307400f0031020580f01c0654103800c0032501100f810510005a100d15003400082243d40040f840000c26a0405400c0b0601164849072204200400380000c5018520a07010390281c1d6240201040302242d2a50910014504100c28442c440600301040c00c0c4002044401410880c0c03c0070009250a003a0404c1c0b00800038004800100b40c0700980c092070040b03000d90342503100d07555055000080f074000c0302c5d60680e1041c2c800707076 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 117392437 1250 117391187 117391193
    0x105060a11071503020403060612050c0603100503030a052a030a050c100501080c0102240105150d0507030515010507080406050a0504030501020301030b160503040203060c03060301021215010905090103080304 91
    0x19919150001d62400e40e841151600f10071031007160310900443c0443e0300090100200030031845644000c101d59028000210219540c142e1200c540b448050b1041201101207800c0e10b0074441d07a032004043c010300b201c2c1c0c1c40700003650203407036a00501000d20103a0110b40d0326940d20b144403c02880d10f8108d00025500d00400d0007815216a0004800c0000c1c034400d82b45800d039101024403403a4081c1c0b03900d00040200700502e8000a1601038040c0901010140c03980488000041c981e91144c19200d0454007547c203904181c40502041c080d01d40b02c0110f0b0f6040c2814040c006030141d01940c02110030300048a07801040000540719445407100040041c2002c000c10000180b00b40007500105645141442c039140d0360703807aa54203a82003a0010b4818408400c00e000319000f20320002a06c00ca22030510f24154907242c0c000a8907510020426140e003600003000482036502035040710a00a00800360000909001894036100b2140800b02404100303035141c003180b14902944254102ca0348031016900e180d840796 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 117393687 1250 117392437 117392447
    0xb04031d2d03010f0204150f080103060f090206071104050c04050904060b0307150f09061704110f0a0f08060a020408121c0f050a1a030709020f0d060807030c0e0105060a 74
    0x8584100551001d019540c2030246641d40f0000f00f00151b103660030015032000650488040d4070a00160400c080b0407607421201d114116900311500152600031a44071070b01901c40c8400027036103c1c0c07002802d88100840600d00304803e54082d0340170001aa9450503a0401e84102c0c040c80740e008119100140000351950000b8000c1c907005030680740925598282e110440b01e0b00e500031030129080d0307620180c3d0941d00000000c000d01140ca42000300e0300200005590414025001900707052149512520f02d864a2100b90341e4020050910008541d42d900010704140281c090710b081c50207104046800178a0a000b96001c1c2c845001c0909009500f91800c9900361380080f04c1801c8110013100700c0c004c40c5416100b4030807807041c1c241010801b46020303002c0408031100e807040740040d09002e5402c14030603140000c0384001d0716400c0310b00503a00c0c914060130340000d00540003a80700e02030030700d107001ca00c82d400800c01c02d0841c2e00c144000443c503900c0c0c0d0b0204081620034050550040c41c24403042407158426 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 117394937 1250 117393687 117393739
    0xc05070b06100c1412030c12070c0c03060c0e0a09020703020105161e0c080f0c060601091401051c0e1507020c010c121701090605030d0206060d06021b010501030b04031d 74
    0x40c212107445c07102c000806035582044807490003443c03010500d44891400150b0190f4441194030b448410070740c0b00e507903034100c0009600000d011165140054032080d80541c42014a03c03900503c6e01c90320035510305c510720103580944000c5005500700b1020407200381c015001c20341652456168100c2407003010003060703c0e14107a0350202c420403074010605808528000e000307088006d03814904503650140020b54521f003940107098075040009410040056650599000843c41d0003440c045603500790b236404441c90960b005054660485c507000144201000005103034544000c43c3c4040c0c0703503a0340d4151080c0c0e243c40e560208a8007048680320a04006404129405000030150401d081161100180e0300c80080c0240c000d10348107580c1f00824012450704002128031411144000c1100c0d24100000c51440c9101c0302004141d140c000c0b640c09621001002c001e0040706444c0c00030070043d81e59003040c0d0304a000c1954142c0124014110040d0b1540d0345a800d892000005048070400080b0f4411607800118a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 117396187 1250 117394937 117394973
    0x70602091c030806090f040c15020c03070f140a0b030105010e04021605060f09070f1712030c03060a090c08060d02040f0c0e030106090203061f050d0c05070b06100c 72
    0x90301c2103119460050099081158026640c01401c0d02e05a810300101543c00344c21034405e5030620041100044600310031030140d541c425000c00030707070600e990207070b240025001d07001c0ea050148240100d82e0655a1000300304980c103100d0302c07c02007450942800b014085a0140c404a11010001800b0340d5020b09006906460082c0c40107183c6031890048043c110800d210850305500301400703108009043d100100e8002000340c0281043d90301d0030803000460500c030301c01d00000e002c18005070044802c1c2400204143e46940350741036641d2030003c50034051030348104e0703402e84140c1c603101c404141260236208011000c3c0e41601d0356209234950204202d80340700e600208076401500d40210510310706980c0a01551145a0746403022410b019604050946489400011607a8814000c220580d56100b503000f880780c0b0580748000500c405058101d403607204900301c00c180c05050021140078107078070800078405540514121f0304d498840740c040051440c1030048840c005203240e1250004190841030b00b0100100e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 117397437 1250 117396187 117396199
    0xc090603031801120212060a0905100905221407060c020f09040f0507080d121406060c0106090204060c0203010e06042a0909060527030304080d02120a0b030c04020f07060209 76
    0x2108440c13203c1070364042c1d2520f68003500d4150a1101c0c50801056040141010080c144880e140000640454010394810702e541d1580300d40218008110f8000c54411b4802ea003604034011101b00e0810102c04002c007465484a44506000015100d12030843e180c14542d0041010382e5107a003072000c11281240140068035502184c80c05400042c01c104107000060100101401c3c669405000c091b103084010020011114102111024050003854400b9408901115026102c0f52184081c0780100030a4106100300da100240c04a5103a400c10541140240300302c00a100d0040341140d1141c0740c03c0700b541c00a0a4010075013400000441d601f10860790180001c0c0304041e01ca941e82a07280c10307614218403d40e543da5540c1c007841503180340202031041000b010384c030000134407218550980d0751384001000039003c28004101c20306040026011102c900c400007184091320308055154400412131500054400d104803840e9080c941414000c1d40c081281001c006414030342c81d84c89034400381d80440d4905c3e42c001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 117398687 1250 117397437 117397457
    0x70603020a031d0c010e010905030a03030c05071a1005030d0e01050d0f020301090f050108031903180203010c090501021e070302040b030f0a0602070c060809060a0e01180506090c090603031801 84
    0x21401409003c46154102c0082414403003580000d000a182c0c6252541000401a07040c000343e2400958904000c2e4180380004160090400840d4540100701005103040c001001c0c031585040b40310380b107034012540c0030f40c9400b00599500c1015952004640740d1400300301707402c850070001c2d80500b004d85880640b2040c080340740b41d0320020301c1041f607101742c2004c01c0480c8e8a140d0202207001d103118090140c00210300651a00c1070015032440c410100500d100105070f245c1840e0480740d0604251900d0140d03000d4000d00194012280141888815006550040c8100810fa03855101d038070940080150410000d0008a070641c0c0034040070340082c59049402d84680c000c0020080410841449840e01031440141c54492910300302c0007141b40c5500c000308000f0a402445038181c000300d920742d0440320810000418142c400401e602500419007850980c04024504030240640450300600c50443c801c1913800400262080003d850b0702643c2d4960154000d2100700181c88006e000c5502803035050500158003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 117399937 1250 117398687 117398711
    0x301031514240d0b01230a0b1c090b0f0a0b010f050c12041205210f030402040f05012c090d0c03020c0a090b040c08220c0b030a0903020f070503070603020a03 69
    0x244603100f1003110b040c0440d60041100e0030070b103060164650800c4244698a0801000003801040d8900495810510000c0c1d140f103184003925000030980003846051050b0320842c2401340c40001e088804031f003c40448800541d06042c1c1d4402c09018510584920402482c9100200c0d1280c104152804040c801c0007049403000c0882e0000c7d00040030441280e405101113860802c0c2003031001502100c81d80000b4098082000300c0304203584220000710b0000d83c481e6141c1c00050b015103082c035460345d03066160000100b0b846240c0c50b061030b0142003113101e50791102c11510301180443d0003180c10204507080b01c07101c03100c100c0c80380c02003a0040c6c0c040c0c03045601000b141400030b54099030651201e4141c4d80d46076250031243c00d140c0903030b003800d1009080030311903460f01e00c0c03100c00074648080e81110420310074504002008038100304400905004a00c954a031320b8402c0400b0f006081824081d005486844110405400c00080f410705442c03020307001d0256940352007425406504404614014152112044180323 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 117401187 1250 117399937 117399949
    0x901090906230412050309070b03060d060c12060b0316050702060d0c050a090e060307060e06070503070c080c030703080d0903031b03050a050108010908122703030103151424 76
    0xd41d150200c0c0c0b20107401c2602e0102c00c192401494203003404000d00c20031200d1038000c2100000c41d0920420903641f80d450000080c131506198500911b210b00d041c4640c401154844410002424140400c0118989510301d072161130000300c1d9100e09030503541e503428000c2480f6030040c1000a10152049040551410743d40068494407009440000e50200c0c099010f141c0c820a44001070080c0c0320060000d00305000840d494500a00501040c0202c400340100251251011110565005401d0b01d40703074800c1d40b0784a011403d00f849060307024400c5540300e0780c56140c08a031000441f075002207050310b082299604a00500030702c0f00290240f55031a008144503580b5441c3c40d41d4480c94565000541d450800c85283c1140c8042c4c21610450385030801e088006100b440440d400c081010207407100d560ba03880343c0c401190482541d14010b04c03020340840c14a0090000166042c0d0344210541300400004000d41c408032401503140c0c1c804490380001241d21152040262540030802c826100410400303000460310f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 117402437 1250 117401187 117401231
    0x40b01140a1d0406080d0c050304152007080318041e05040209070305010f050d080c0f030721090e1008120d0e030f040e2503060914060901090906 64
    0x20500070340030544562400500500b003410102c6003003000c5400c02e800c00e03a655a410340340c8001e1154440d010014002c040098500901d0f1030410342d000d4240060005000000c03c1c480540740e11104000c68480c20008980401941c5d502d2009604001c5c5c203d0340c500541c2a0100f11a821503602d00c108075015000308074646074542640004102410240305100090308000c140380c040514040c0180554640f00340400c08407001258260f0382c1c01c016040c070303600f18852603500005520515010600c06180070000e443c80780d011740c642c4910000d03000c1221080f075010441c1a0002840505e0510a0300025958a0f8210759141f06111450f03840300c07040391500040349522404818040754030305c10041d40f801120035070310415000d507041c84080c0d40104024040d602852200a58550000b0b005503000c0008140010140e0b40c1081f0003607860f0300140c000d101d076008030f2a101d8100ba0b0076000014220030345602881c8050541100c0341c2c42c01c3c80181c014100140121640381c0c80354203013144141560342d490 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 117403687 1250 117402437 117402457
    0x1504080418090b160806060c03190801060207081b150d050403091401260601020a050604030305040c150f0f02070b070503030105031e07140114180f0301140402040b0114 74
    0x1114030560804004141008080306144d40200f00f45480f400c0d8084445070308a001a1036064a0740c2d207200f00381c1e0440c041c2076821103503102c0141c443c503000d65000b00b030f1504070759454082c1c03450161600640d07034a500b040f03215101c40c010880070989080c144540300f1100d114013540a2070400198078051029158260b50580006400f50414090a525501d00000d0b449003403c29820300100035820380c032020700341032280e08c6244c042c2c8009103a41e4020711203400c9056010041c2d44c00c5281c145400350013801e05603020340701c1104070040031840c0041c10005440b80e02c12612a507030f064404a0044030210f190158080850091110020b0607801c010080c00b00d01d441480656201e40c103000600d440d14070401000508185c1c0800c60003140c000200748002a200b0441080c4a402e1701c400068a0a2101000c0181c1515000031aa0303108507059a500410b40360440e2202c1021151101701400e0b0f4041d00c05456214403500042401403802e80d004000ca0441818501801605426a50b006030441080c40b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 117404937 1250 117403687 117403691
    0x4091202070501090b04050306010b07050a020a060f0210141303050d06140315012301050412150b030c011d040905121309060b0d0e010b03100b130207051504080418 72
    0x2e00196130005000d001524180b11000e05240c03138480040d43d41c07841031141800c88180003078184203201003803021610031a0080e245c10111a030f620380051041010300b81810041c05140031080c01c5401c00c2c09040802c40043c410308205844008950842440034041203090290070800150105103038041c41d002060003c24055100d8450340071b01d401c02e10349040c00100c04102000601c00902034540410102341c24000100c415034900780103035950700c11500034208030082d2484010400040b00002b0b43c8010320130030309103c01c116980c01d0540c0d07042984e894601180244010419113145600c1d6580f801d2802080403804410a03210b05040bc440c2906141c0081c0c2d001600341e20f54013801d14560010003070300d0010441d00b841c0500c004c020340202801601425240c41540c034201e5425001402260401002e4070b01e100d10408900c0010b0180300501b42c001c2d0810552103054801600c29100d00d26001806801c2d0b241d1038040340f1603586802002101c0b2400c040c00040381c10b004841c2d07a41c00c98440d100d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 117406187 1250 117404937 117404939
    0x601120605030f15010803040f18020c1518010903020d051e04150206010b04060509010503070c1505010f0b0309060a0902030a0b0a02040e0c07150510090207080409051305060c03060409120207 84
    0x40c044c62004140c000916590042008100c9480c241a54104031256000301054103244c054204c03000c4d20600c9011403c130f202d04004800700000f902000c0e80110f1404046046040502c411203080c1c4000c0d01c03025000da000b0001d04101207000c0c41c02004208444140c0020740102c050752407107241c215401940c0c8118030042d0104205804112041c0500300011040381481e28024004009200b545a028100030020001ca40c1c01c0b03020305c07482c4240c264441030400050b0000c03206030300100001d101d0034610b00020000014252000f00c101ca00405100014041950701c03210404041c0000320812038051083c1d01900b40030420308910980103d80d01c600c0540c0c0d6034981b14168111800c0505140480b90303003000080006080b00c541d040d01d0314842c14001c42c3c02d640e0141090080c078941d500ca44a1180002007100c1000418002002a216103050810035034440200480c24040f203c1c10040070340c2c0c4500040307038085030000090359004030010f001260041c031036075034841d00907072042d080c1025074000d4038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 117407437 1250 117406187 117406213
    0x80a020306061504050d080d0e0d080606070c230d030207030308010f060f0807180306051608010b1c0207140c3f01020904050403180b03040b0601120605030f 69
    0xc1d9003020040b83d41d060342c08a15660704225115034401d491080c494510004200714454081d654000030031041004503800f4482940c1d182e010f401c210b000001c07201000070b9098582807054a04030ba4002c0d002c0c42c01d10703003082a04050b42c400d0b010903c4881290a007032510701d5840706054040140309a002c3c010b081d18519020b0900103060300f044d0459002e1807800c1c01001d80c0031040d00c40c0842c032850240243d0b11525000d540301c0f00302d01c050480c15113122902005002c00d680205001d00029842d000055403e0f14046929400038042c810701141d0402c02c5115074080e010313101800480400c001031802d0280e649901c40720a041e852000240c10025103c0d01c140381081150b290703094011401c3c1c502410910300520001c1c010b01c0440000002031640c007100500950503110398030f00162040000741024107000e0081009202c0f0091010015071000c2888040d10040d24000d0380d0249940c042c43d02c5030001954080401140010511340c0c0b10300000f600da40c10841000440b110f1006802c02c2c440d20700b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 117408687 1250 117407437 117407443
    0xe0a0b070c0f060203030606030a090c0f080114090f071701020f041205060a0b0f22020a0306080607020f0c010806040b090411040b010c020307060e2413090504032102040f080a0203 79
    0x140c0540c0564105208000042e141ea0003168ad01444076140020980182c0c9031680d0740488581003902d00c054042800b1440700d030158400e0031540001c103824031040d520396580702d85e204c2ea0b101501449420494081010003a141c0002284580300000907003030041080303003084a03402c02d51105003120201f0b58542c5c01e01c9000e01180b9001604240248500020b503c00710304280d42012410303000d502e10398207050710341c40110741046140c60300d40001d5580b60000c0d04010090300c0680036003500c45c000d21020504e40b0340001136504050b0410000f900d4203500361801551640720080c00f540e042502c3ea0200a0a50340b084205441941726035916000040000305000c111106a001c03541807050045040c0050394000444c1c030101c1e02d06142c806849800c21020410880c60072080106240700070031144e4203803201c2000b401c0c0501c3c0c40c140724404169a0f114880c1659020758002d004901106c00c00c0b41d240f443e480301011184502c20b00546060350791203441c503a07040e05520221242e00402c803040c0840c9814 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 117409937 1250 117408687 117408689
    0x10516031b1e0306170604051c021c03021902100b0a08060f041a070c051002070812060105160f020901080a021c02030a0606061e0914010e0a0b070c0f 66
    0x40d206001085a5a80c0644500440050034800a451a4420306898400d4009001510300900000500c105d66041907655a4090f14211103500400e071b500ca600c000706030040e400b1076407254020100058144259042c00081d0800103042540800c4091400c5800c0803c1c40f60800180d8000c162410014840d030048424108496201d920356a80810070400000758141c1c01020114054036103850b14a0705491070700c030b0b08250f000668800c00400a07880e40124a04030f005000f9000d5452809103031583c10200e209241c00100100b00a2081c800c28820620189901070410b040282c0340100b06048415002803149040354482c4110a408085040c0402286e0051018100034000c1036641c0c1d000401d5880c961204080000100c0401000e55030200708124203560000c10030005540c45210051480d40c1c1071a50010043d1081d6800070203078840e0441204445400c8101c0e42c405104000441d144000602c0795035009654003000f2908116990040c07500900c1807500300c000311300e01010f03c0014141 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 117411187 1250 117409937 117409961
    0xa02090f1c050f16050411280306060c1a090a0209150310090503090108130c0b07110f150a0302040b03070305010303021c0206011404021201140406120c03030503100801051603 77
    0xd44c820f1861100080ca10034184c43c0c044402054540380300940941070300035800d42c0c02c042d4040780780c0c9a1402d45092000c1302c10000703a650502540380c039040c0596805480001c01468145601c030316000c064480074100d41c00c01d40c40e205031552200300e600051188501603540401c400803c1000c0502440c0420503490309200440d0144905041512860740303074007a5116660601690700001540500b03041c5411100e107074802e00d2009180d032265041071442d00620000c03540a062085100f2a5191580030344141c0e800c000c4c0560031038881c84006d44200c0d001612a0018103400340f1022401404d0200514481ea90599000546602d541802403810f643c0c014811103610414220b60032181d80850501e040d1445d10360100c1c00c844649002c14004c1c418100c04411406012002141800380c218420042950443e010701c034503a29000e03035001c1d030f200920b40200080740c030440c200700182c051400303103500c207a200104014440d45d83d1030103402d407031048600e000c2001c4039003600e0600300e8051140e03241c0b03040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 117412437 1250 117411187 117411193
    0x100c091706060307140102031b03040509150907140c01091a070809060a0209272401091e080d0c03020610150c0203070b04030c210b0a02090f1c050f 65
    0x10002c000c41d03210b03100c034081e4541c0b80c452418541c08590003081140d400d01a8600b0038000941008903594072500b190042920800c00c00f030100d64056101281e80114520084c00000f180e02c0b0700d202660413441103400c803210700f04248004000b0341428460b102d03440b40603581d616010040441000d4528030020400c8050041c2d10091002006000600070385c0855040c00040e500c040301e0000131044059880c0d204603549460394800040a2404c1026000341d40b0807003c4040380c00c41c292591120443c8031487d500003280b58404010300d4181041026010800d562801c0306981c8440500341032045c0c00b50808081204440617104050381001555448105071160724165418612140c8440d2940c62024080001007400502590740501c040070081031a00441c0b5540c554924102d030018031139101e0640810000422403080e0000d40c442d0a4145034403400010f4141e480500e168000d4003c00300d101d4200300d855070540f001d51609a00700300505c0c58010201c01400070343c41d02070700e000c030489007901860f0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 117413687 1250 117412437 117412441
    0x306140702030406081905090c01030c021207151b020a05060f0708280e0c0102160e061203090301020403081c06060206060111010e1912020d0818100c091706 69
    0x19408000e5400b44c1e00079250110090b1902028500c40d00b01070741c800726546140c042482010700300041c1442074950282c0b010300045040104c10390320756090360b0f00400d0720a003c110180028480d02845014014022000a80c0781c0c003205820418161881c2c080000d0f03800715136828203008040000540c440e516405208851610440080c400f1314040d010541100f00c01442c0340d10760b542c2c44401c0e910000100010828912000140c643d030314910003845000d80118009402940b203007240850a0700c540800541490b21004180100600f2007900c05403240000c0c0a802e80c0d983d000c3c0005c000541c05078120a440c2c0c0105130641c0201d0420756460b040a43c03918504221682c2c020076903a40c07040f424208100801030301d038541409030515140c94038131406241c002005840b004c04409003100c3c05030120071020004100300707a0740c80c051100351101181c000700000d200c503040b88001281184814003a110490724840c0045c040ea2102100c65001c911107290500141051480c41c0130302d6582d0704010030b194 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 117414937 1250 117413687 117413701
    0x2041a0313030c110d0303060515041a07080c010e0c2d0105090307051207060305070f0c02060702040f05130506070c02150a110a0606031a010302010509040504110a03080301030614 79
    0x820407115004003800002c480d10070600031000c0e14202c8940c005000200d403602d051070300400404450084921444004100054451891003540c0646418036001400c284c003011465880b9040100101c0b8030207420490b251a190342030003000000f20131000103100d4050481c0030408004011141d580740746130350b18003024901345103807418050000300b801c0c000d688240410103c3c2c18440607401c4950440f011000c0c01d4284900014400c00f2140e840d5420800c540f01c0f540d04554000f0a0342d06600083c1e500c81c030364805454224014004035100800004a4018564607001a500700329030b07074080d81e41d4252029081c00014451194080104d00c3e01d008026640c0d4001909041d01c81c6944804443c0440c0ca110080c1c02121035180801c86001217401907030162501002502c0c0f01d00003104d45000c000302c0f00039140b243d1190503040e60740c1616107a0501182c5c81c1440010a402003003500c181030020b00b640402e45903411b01c00080c1d8003806600d07070ba035070541c1004003c1d282403481e041a50400c4c8001c0110b6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 117416187 1250 117414937 117414961
    0xb040f120203101a040e060405120a0804122619020c15040f0c172503080a0e092a0a0804140a12050702040b010c0804090b040e01060902041a03 63
    0x30303204140f04001354001004116044c1400c14010030741e0000d140520526007040700144041c80341c2e20550032992080f542070610000d50080c60100390102d003152000c90700051000803060150403176840c01c10400c0d044c010340d84544980480300351010342c1c001c0c010302051503c1e0212106084452031030030740c03405108060003941c40c0152444025594860000700b8104800203101c2c1d040c02da0004a0729000a440304411465280041008135682c440c81c080316441e1150303998200c054900d407a03071442807113186071204002644000055410805c40380b02c3c40110395103a4040902900c0031020304003c0c180c00c0c003034481c010030323100d283c1c2c07a0455000d006d6030b5030b09540000002d070301c1a4400d80a01500305505412443c007044000c00400c028590b0490719412075210f4054640a40222028016140700360010b407005245100003804031001044284401010f079001441201c134003800c001070068002c5429402c440841e08005441a0002402c0008048103070b19a0440f03941c80c3c1c0d2843c51824010b5401c01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 117417437 1250 117416187 117416203
    0x2802030a0b191a0a02010905010908040e101a0a020f0601060e0102150630101406040b03060408090a0302090103060509010b0a0f0e2d01060305150d0f0512040b040f120203 75
    0x800f2400604419114401e400108999074000c000388212626441c0004881c1c000340a8021600f55100c0020070700305803414003008880e130b2300303a20740b2102c01d03540300f028071582c041380311a01544034460711054512010841140203041c0c0d5030350340f550f0034000000203007019001c007080d2010200c2041404196540c0e290341c2d100005462049c0d8012015890800f0760740e801c030744480c02442c090481021000c00260300004100016909603001a913034010401080b500e0550100d60903510040000c0c0008a01c0030050001c1035004001d050348550b00e600142e07100c0402d820441c1c5083e1214107219841409008a010454040f2400100701d4142103030700403020f180e0300c01e41281c94080400f00f00c0012054480301c60300941c1c0800a60940041d07603502020140c04e100302c500080c41c1c600055048a064a10003070707174590082034080b01c6550382d200c03c1ca90301c04000c0107403884c1c0200c0d2609000069140020300007804415005030700c480c50f1108544800d1125031240341c0840806499500503179001ca4421 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 117418687 1250 117417437 117417479
    0xd1101020c0301022a1204080106050103060e090d2f010e070905130b190e010e06070f051b07080610030501050f010e01061b14100501120503032802030a0b19 69
    0x405c0041c0604a03d883e299144101c0003105100150105030600190803030b4040d5030081e00c05108850352200e420b40780034021504141607070000f0b40c0e01d0244511842e2a581c14512002c0c501c880b030507031050902201c01c01d003074001007142c0d0340e2400c40b014002c05112100080000361010440d5152102180400c5209902c00402c04020390b000200c5641d48494040c511103030b4660704201c26000e91002c103000381003241d104e030b8040c424640014103d0b4800d0110b07010a0fa1503584260602c0d11000a0380706140e1804586505401071040100c2c160f141081a035228080e203a00d207120301844c40c00d04500b103440290070417025000b86801070003035030419034a1a04407815460030440b55012880102024410224024140c1c002d40c840c490b181103002030b440c00d103a02d1030603081100da66070b2043c0d010004100ca00040442d0401d20004040e80003e02490140503020300c4552070307042204628808a9100300e03070240744680c0d0354280f00594180362441c05611203209031140b000b00e007040d5015000b60340c22035000b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 117419937 1250 117418687 117418747
    0x9030a170c0a050d02070b1501111b0402090105041520010524010c020904080301060908030711040b031203010f0f15080103230f060708130305040b180d1101020c030102 74
    0x18111954542d41215100c6e0b42211a0328510708003010100c9080201e1a003581c0020000315002480041c041807003a210070442038014076400e521801d00c0065000040707044d050000038003001960b00c5840032410340b00402c0c0d544807150f050700e00d100d610440540d481c03110501d80c5081c040050350b0030b0361102d81e55602c03500e035003403020103644000481e000c0f440404000e420418010074441084080c0d00603505844040d19031020841d20b88074082d940f8000d03a4000b505000d072094180c0d4684c01c0030303840400d2000001e01600c2c0401c0ca541444080daa200b03910503140302200303000c10000100c403010240040d2040e585641444488584000c185003018000a01640b0940d59002b81528041c58100410354191007591002002004c056880303000c200e440c0008581103a002488100006220f01c6200b0344c5502c0c0c040c101030600003000e40070342100750b290807200c151514100d4030360399101d103824031a44142841a144041a0002414a0781164a80c0c1c0640e00610000e0321548010b801c1c3c01144900300340d1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 117421187 1250 117419937 117419947
    0x3040501081003081b0c01030b0609100905060403110f0f1f09080a0305031e0606120601020a0c03061e0e031606020909090610080d090509070306050909030a170c0a05 73
    0x41c0c50107120705680700a160401c0002c464030341610a04801c3c10400d17280040e1645041d81c040150166580160b089074410790412200120707181c07001d01c2000b02e09091601507165a00c61000c103c02c0c2d84580c100303488042604c00c140c0130074a0b0092000203002c400b626070500241144010509040074050380c00540c07a060641c0f80004d620900e80d0381f0007400c101040300e04103540d6040181c0070394825542102c404410b250100242c40440c3c0005003e510701800a92800418101d4100c0f00760014010782e046001d0032078220b01007901c220b200005180605e90000d850fa070354040030000300c600340d0440601c1c0380c2042d461020400000c0242c616500c08001007a0080401d0310b4584020320039484030591000c1e4040611010b08000105207101e003002e07602c00314040703850349541c941c0d42806c1d054400000d00f400c8420301041c2808d903030b803d03000b1880d820302080160720f0703100041d0040d5003203501d00c0d050b500101d0382d10140c80e80250001800c100c0c406100d01107040c03001c0c02207030510400082100748100022 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 117422437 1250 117421187 117421201
    0xa060e010b0924040f0e01060b03041a09011107030305150306010f090f0b06070501050402130203150d020d0609050f0d05040b090409030504080706050a0f020102130513060b0c01020910110304050108 87
    0x103400003c40d030004104000d004581010360000b071030202e444101c0340d8a07041c03011880c60a031900700c0b4040c9400c000c0c0da44640f6107101d04822000d030020711091095491389440f121002d0854041c049552003920041440d1409944600d9095440110f00348254409401004100070440411003610300c04c3c400401c0e8155042c2c2140090030712008880d401c04000110034081c41819441503029501c2198040841000a1554070507070100f03540030100a80c2c511000035452500c0c818407010184050440b82c140031050311a4421078801c00002e6079a0741100080c2d54680318140083c5905188a042c00b80c1018201600d500086c003641100b036000301da40e40008010303d4017032000c0e41d0090000740100c07150141c075030030000c29030f0b00501226070100310281c416011950060080c3c03121104501c200b5942e0910f060b08010403040074a210400d210758502d8045240d84801b801000306882030f8001513030700c001c1c807024440c490700140500d904001e03c0c030300d07101c28180011045408540091910032255203801c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 117423687 1250 117422437 117422491
    0x9010501050d1404080a020606090c0d151707030b01060203040e15060f0a020a030f03061d04030e0409030207050f030f060c0d022503030605040e0d031802030601080a060e010b09 78
    0xc200e149000340c019040204005c01030000341a8002a5070903181562070361030a01c070312382006541c14040c40c1400d00c03950f04448860344c401c10b1008060034514038801e03079440852048040280401c1e01641200100b40188440d0243e16801040740d84010350ac3c09203449406044440080c0103106983c0044120b10059030f00c0401390b03110540240d502c1c60340c0e1002e203030000c1c0d650f100c0000e0407804940c1d81c40401e0710180c043d10414084801290102038856030481c04490b034071400030411030600071100b00c0303540642c542c1d1007502d8465210790024171485062404000101ca88411103e05c81c0d070080e144040e81c540d000c111590024401140d40391039101d0191081c0190040d43c01c0391404061700300c420440c05188200000940340240c50400005031a1014441502c500001c0300e03034140d0002c030342d810342c83c0d21036441040b491400000300b40401826500090902d0020303881000a136000158080900050703201d41002281c1d0540200000c0c4090b20206240003c01001000456600078000c10071a2001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 117424937 1250 117423687 117423701
    0xa0605060a1d070e03071202090604060f120c080a020109210501020a05040519030305042603032503050906010303050a031e0c03110f070206160f061d0c09010501050d 73
    0xb9a1080a010184281c1542c41180880c3c802d000100c00c0c0c003c600703460070041034800039035110860440380c2090303070340070301c0312281001d042190029901c06e4001201c2e06c58000201c0904050310729a1100301c020b0070700f841d2201c0180c000c9011604400d03400c40043c0e030880a81c5044038007203000100807104180244501040703070080030301594000150ac22146504c007004105440c0308a902c1c5486116035444e182101c002d600004021900420007400f4031034000c803084502004210142110b41415080181103400075144a440005405404d4240c106040900c0c00040707201d1804001038500b04a290380d40315010310000d0305003c0005106102e05220380c0010700140070382e8800c018070315556201c2030000d0a1052071a00003914100942401e0214082100d0034007000000c0c0714181442c1d1707003c100f50381c1c0c00590003103a6022400b0b418800920000e40c0740c0b401c1030141c1000107040c501050992180300c0c0c00032940d0340c0ca401c400030300c0e40c0079510000c0d000d041d01c50078a040c0751504409004d0400920071 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 117426187 1250 117424937 117424949
    0x91d090703050d08062107030b0a0e0109060605040c0c050c220c09030308010b120c16020d050307110f010f082d0603120a08010303030c0c1e11090106020a0605060a 72
    0x3039a2640c111a603003041c04c0740d01400050703401c02c00301e10300e0440c1d80c6141104030403a072600350440d4000b0408103041c0110240c01642440d400521000001c00c03590840d035070044d0855a01e9200c400400c0305140a1145001e46c002c5404d00131032400c00381e0340e00c548501240e40c0082c464205d030000c401c810390103500c1103800314455140c100b01003010500058070b419424481103000803440030003c51440d9103076043d1691004007611308803007903c03401c070140c10f2070308a44101300001c02e00c0c80041001d42d964481c084881800341e80610f87d501c40700d003002d00e10091200d0510b4040c4005495032070050368003400030b42d1150110b16001035207031204aa551610190f944011f4030300e2074850b1070301e621451506e00c1d1070702600007103007101c00300741c001d03400141e540c0142010380011a54000040010038000e0700918444215442e0110315541150750f6041121400c0c81040c50004c8040100400c220720350302c52081100c80bc40d00030302c0540c900f0100070b690b00c0100c04028a1640c131340d00450855210000d020340a840 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 117427437 1250 117426187 117426193
    0x20702060c010b030c03030a120905030702060a0906120209010f0c031404140f0405040302120f0f0f030a1d0d1404030b071715150a0203090a0303180501091d09070305 73
    0x801e507201400b0b040d40a198500c80e010303607504100145400400c481d4412407a4440036040c65030b412a501c010600c003001642d06010130449180107999010040c509080e203078444600711410b0610051502c501101e0016040d44100480601a0b0300191040414401882d11940e102030ba482c1c121685c80180c00107540c1801d02280c08507400030100d048485100080c2c80d4132043e151140d00708400e580040c0c0e800341c0036070402640001c1c094140780080c0203203454501103078507062001c3c100c0b400e10b503c200711400d120030380401440844002409545522015042021907014000c02071139220808500202e080c803001c00341c68440c82c00d030f10741543c0c011600186400700e5803034660300c042d01c100c0400011160092408001810347d05d10303640342c00b02040c40581b005803009201442c180d40340d80144c000c40c0c25840103000b180b085a9034426900301552003951100c03401c800103e002c440c0b1040b00d4010328103011034100e0900c1003090361419072207003c85c007c810024a484805806003881071b641c10280c5140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 117428687 1250 117427437 117427447
    0xc051603050301050315011203230d050f0c120105061308060a020304030905030607050405010c1103010504050a02040f0c142104060516050c030313030219050a060507030519090602070206 82
    0x160801d000d0341c101d45050742610642031500c0d0380e03440d048809000d600c030703e5989081c2032400701c2e104e10b48688101e29a80351000302072517290b2151101e60401d0380c000c0103168481082054111441a030b05811120341c0714000d080070421054440c80c0d081c14002c40d03004000c08504d468a080c4000052402010440c0c10b80d8170600384078000380301940c41120240c1c00b1a04c00600000c2508000504500c01d00042e61124102130800004585903001000c0c150394401c1f4002c1c00306500d40e82841100c6c00383d4400c0f03005001028440c070500040d6503840c0e0140d4070951070440811909c0f80c00c0700510040c001b07480595941d844444101c00008074850081803d02c10b0010b041004008803a03211500400c200d171112210661031840c221018419801865600e400900100b003500c4c84d4100d1424545d4400d0058a0408109261000c0c444d02442801e480c15840001030009101c8e03d803290541018981c581404941341c9242610100d002070000d01008566030803100040c048258141c031184c80d4000c007895079030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 117429937 1250 117428687 117428693
    0xb0408070503010b0f0d0809040603120f0806010203160f080d0510170615090414010222120f0320030307050d050f06010e060c0109050a0302062502100c0516 69
    0x40d0080e00034070380030f5860300019000d9858020200e11149a0013001e00c0400c007840d40d188503050b0081071550340c0140d121100480096442c0d50302d40c51200b070310790b24914440c609017401082031002403e0641990801c000380034810030010128642030343c00440000c2030305050b2034103404500ca00785072072000b01c0c80d010500204482d0b5044502c11102d4000000c400e0401010b6459190281620010507440d5140d00ca440e69081000b0150741c498001d0703850b4203040c4000d0701e641d400d80e4009d800c080c40003500320b07603612050310920038490017510002460320103261a5945d4a0700a41d60004080d052101c5408000500c40e4400c41c0403616402180a50fa16400c0132500500b1035003150000000550501c4000303220804c56a0840f0300c540307816520005801c03d040140503042e80700c000c41442c1035484164010200b101084041c04052081d80100007916000c020032503506401c41c4004413080d01400ca5031001c17640002c2011404805c40c0000845142e44a000d403014840c0b4a803240102d08250540c00c14 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 117431187 1250 117429937 117429943
    0xa050708010e07090204080304140607020307031118010302030c0402030c04080d080f0702030c0d180b120f130809041a09090703050708010c090e04030504051809120304080a030e070b0408 82
    0x70703400c682111803840d00c5160340b0301079011b0f6015000440d84148010032009400d000111200403010b00024503190064001c80d0514450760401d803141c01c3c110003004180c0c00d22858840d0b10f19840c000183e429411680040d032100841c080d290701c6a03030044040f07405030003600300312401042182c00316134040c90759480190481c40300703c81101d03d44001e580000c50480c0007104440e00d8581a901800314051200019110300704c442c1400340340301c0407555001c07501c21807040003803905100c035030021200c0d1300d80140700d1800c884006202d40614441000c1c203070006640e03070043e1428a002141c021903ca80a07403030526501c40c4910302c45600402c0c0034203019603080c010030780d00180c03401503081d203030540d4450034094245c03403950a00000003261b807e01080718444100c40580c1282c07082c50014909551040000c118000b0112150700c86034800c1c080c0320101c1d0081040d4010010001241402c516250700c038040c0d280a90700758141130644540c04508520014003c0340060400c2440303481d100d42e00c551100307503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 117432437 1250 117431187 117431201
    0x18060108060405090a232b051215040f06030809010f11070902030a0f0e0304060e01021f0c0c020913060b09010302101404030503210a0b09070c02030a05070801 70
    0x101058002010690318140b501907680b180c40100001c01d41440a0341d00c074005140380c2c40020400904022030780065032018001d4240b2814010030343e20b0907850380ca0720910b034003034200c149000313000301088030754590441c442d101c5d07a100d0005038402c0c0c02c40440303501090141a1041040d4500c82c40d1940100c208401180900300244007a41c2d1100080c551680c00e44407005055802038403548488002c100820898000b5a80000b601c1404076080280c030f800c110903110400441c0d05a40c101207424130850364031440d91906103100348010001c1c4a0140c0c0244560035040d1106100240c444500c00c0c60386c0e0103401641001603010307140e4820352030151140b810100c0410400c54000d070074240100c02615142e0080760684c0e40042840721041c0010900b03594640411454950511041c0000008210148054040400d0043d0000712441c0341044820b40c0f840300030011034140307180612050003502c42c81040c0d0392081ca0b0341003d00209140f030000a02d81519202d0040180c814080c01140c4400c040d040b000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 117433687 1250 117432437 117432439
    0x5060a09060320031303111209030d0e0105030a09021804150f020f12070c08040b070309050907091701110705010b030601050102030a0f03050601050f0a03050118090213090206091806 80
    0x7280c503e80c03907a5002d8081600118003c5410f001285801a00012000a56100c2d08010307416101c0c1a41040c2002c0642104002c0164080f40c5080365040501c05e0480c014510301c1c05405d0a038501001812600001c4d011608030740d680c018507001c548032030003034007121424107281d50740030326083c5000c0e00507003007042a06000500b03255110311581e500d402511480c0b06800455420318880c40c80b846070562000301100100503860000710040b83c24500140054924070417507070b6072400941009014141540d00c101d015100c80c00401c2045984120080151101151026007091280d595140909031080801401100019100b030400405500c02c42a8030030503000c2c0c620310b07030380c91005984a0241a0400011502000ca507000041c402d23880700b17074840c805041080c10464131032030800003900b0000b8405c02183c1d45100602160220003080448940340b08820b0005034407540c0400e50b003c428454101d426501d9862070011556020183c0d808610081e0101180060040400c4200001510b540e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 117434937 1250 117433687 117433691
    0x1401051003020a05042112030203090615090a0507090503071e0501090b030a020309030712022401060c032f07030b010603020f0405011d0907020a03170906010e1005060a090603 77
    0x2008540e4001e00999883d00902c2c1c4030113003481d20305181031070060103607040141800d215a00090008a181e1001c014181e80c582c1c00584a00e885e001c078034a8000060614030f070036201c1d00c004007059134410031025400030f9441c80c0481c403a200d40320251070713070a400c2c1c210a40c940100c500101b504500c82d01c1802c41b40c010454407a8005135240c005454080040c010808070050400000c2e0b0000901d400454101003414200e81c9403074019161540b0b10b062102420300142c00030700d100035100c1a0100710542241003209034888551400c5006000504100801028040341c060f6040041c10364202070203030043c64071514203c1c2082089041d880c1c03502800700311204403080c030010030043e1081c400e4a2110526007841407601c3e00300001503d61b88402c103001a0340c0c403a00b1266006549441c10600d000342411380003050020704624002c0c107041c00d0710b14a41040c801901c01c1084080700010300504482e50358440003003035140d80105000c51a05500044e8000200242d10f20306544c1c001131980445001d43e0781 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 117436187 1250 117434937 117434959
    0x160e03100e0a03390c120803090f070602031801110604050601080f07050102030a030218120f0120030106110304080d02060708130b1504020d06140f0607050a0b07030f140105 76
    0x1080c0c280a0010203c040130715286000c0d00c04aa550800f940c01413401903041d055569950301c2907041004081c030f8111542c400c04001e0204285041009180b5480b01c03070003522106080c01c43c002d580b806518200000f4009500e84205103074000c041d49a40342c0890019142289018108280e0300c03542071041c800f5911802007030180045010501340e0039158143d014600e000b18a003000c402940014240c840800000c9509072641d54510303001301d40704102e44014040d00001800441c0c21903821104610b9001100080301c2c680712010000c40e41594003d00340004040300035104203145005070f401100451003444003a00c2e006400007201031242c403c5036a8488941c1d0340540004004000d441c1c0148045100804609400e4800c991f402028502420060404070100c4c1c4240039504154000c141d400180b01541c0c0e00b0342864007100e0095801514a1841c1100e41d0b030f14035549004640014024402d8040482d04440c40b0b80c1040f050600d01c03980501c1a900f4482c0d2900c103040c1c0a20a85110b0189848 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 117437437 1250 117436187 117436217
    0x50909030a020c1e1003060905090a03090902090a0302060a020304080307030507020a0f08031803011e060e060603161103070209010617010806010605040e0c090604080a06050c03160e03100e0a03 85
    0x400d026650f1150308913001840c1044d002d20608415070700390403040c142c503440302150108580c843c0360712882e0003500130460782585081c0946541e81907040120024010031005c1407a071a50344015040300e0741035a14030350b5158400c50881c1107000e1504040c00c180000128607050590100c050000c03a0f00840c0c3c0e500f02280d6031000c1182c03000c0c55104520b000e8006110940d851a8540120844244041c001041070302c90301545d400070b1504201c2084030590f0f1550140941c2424140d855031004050300d580789181400031103c500c0443c2124030704100b005081d441c40550303174284252540c0a5011346840c03110f58444030050304400e074030040c0c0d640345d80d20b04000080c40c6400065050480e0196110107140c10f060642c00c501c1220020281e42105104100f08481074949100401c010305402c00909000c100b18034084064420280c40282c403840c09005101025521600c0c1052040e280d050000345110314902090401d1507501100403140c3c0380c403881340b8180c9404580d07500028842da59040c08010a28 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 117438687 1250 117437437 117437449
    0xb0a050103020d030f110706020f010e07060e090a1404060c0318260f1317011a040c0e09010807060e030f0a080f0f0301080102040311011e030b040204050909030a020c 73
    0x44800b940c4070b14a100a00d000c44d01848052104194070b1900814580303500324441c2c90a0300e143d0090303006034424104002e041d8405e10070b02e848205280094550a46413001c02011840729662051140c5000c80108003444500d50143c410030b10f14450150b824549030401100414580f000b03000400d0502d42400c165403e480050a00d80e85d01001d0449821280d00211001280750280500c0d489400c0244907059058500030b4551950010540001e4509002d00503401161a050b01d07030040e0304045107000c4105101c424086c41503c10340e8006058400713040110340c150f0000d40800e402c104807000100f50a0780c04034102d8280ca00340c0d100c00e42807840c803c00345582ca1074076403072145032904007810010010312504020092160200602c0d420003009030361205280e4402e0344000c2c00381c0e50000d01042000401e00402d0340612003400d12008401000c2d0440d20200c200380d03500000c066035160b0a120741d94031a07041c4c070003074030002d0300d01c030458680b211245903284c1c00341c5030040c0548928812034100340f400c0e03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 117439937 1250 117438687 117438689
    0x70c021503060a0b0a1101150f12080307080a061701141018090f020916020d031406150f0a03150801020a090e061813020a08060c04180204030c0e040b0a0501 69
    0x10f812520024680a080207050308079494030010483ca4080d006040e00d400d004149145101e0400c0d01d080b5460a080e6240c250020785c064080d0655000307201001c94041030070b90b6889929414000880c2c0d544002401c020841500007449c1c2d0741c201c28074040307020f505611240e0840c0c8418075024064890b44c4280064500c80e12824010705400341d00d1000e441da80d0f4004280151140384031820041c1750394009031b0030110444080140d4a4889083c607001341c0e0410015403042c0c1e1a06040100840d0341a0303420640c0d0005180318090b11040c6c0c0b2a80c203002000c01200d00600c0c074407401d9600c40d0035220004002c0c02020f240b44a03082201e0401080f8004184200d13503600601d03031a0a14410b1601c03071804240c510090445501052020700b820002c81110300503480343d101c0c0840008031056034410002d411896070001c00030b607840f40301080040d03407461084a00340c840b040c1e90b500400600c0c3d1246030191140e508010019120840d00003000d041c050042c5009030f1040000803c60356541c80e001c4200d880c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 117441187 1250 117439937 117439939
    0x20d0c03030f0902090a0f05060618060d06170a17030408030f15041a03070b0408071802040e04060e0d030e06150a030519020a0801051003030c0213050103030f2a030503100e070c02150306 82
    0x540c0034000e0113440d1160040dc195605c0740008110150b03101801c150030f10b032500415000341c0000c61054200034210512900c100b808070407840c118240382d12001d0032800014500e15009000c200894103421b039507154203110840040c400d000c928000e503001c800140001c118280244601741e4041050302407003054605960815008016580c034000034200265010710b6001300d210360810011078000c900a030190711560051002151026034403140340c2c6040e000780c86400c10540f500ba1071f011010f001280340c54001c182e020103187c801f080c110004030310200e03980c001855403003501141640e01144a00082d04075000304c8012140c00c0c0d45401090a803001252204901c002a18060000a01451040389240d00142031440b01ca02445418070031208280c00c1600403984031000e002046034400b6841840c00080526284440f80c202a1450600350221000f001e01c100800000c0c41c01403404090001000b44e000c40000600f0a00c0c0003515000c042c5409a00602e03610150700394540c1c55a0450307004042c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 117442437 1250 117441187 117441217
    0x10308120601090f03050601030c05010c05060606220306060510021b010f1403042d0201120b1c0318061403190e01061e0501020d0c03030f0902090a0f050606 69
    0xc080d205540c92003004007500d06212000f10003050000b18004010040c43c03098009214a5045061900301e8020540c003140c1008044010100000d6002c510940c0005007a01c5258540030301581207900600c440044481400000b100007090155607000801210420754504070340da448018106d84070041d82162440944140c0c8003900254860707004041154aa8900845180080070352540950300c242d40544601110100030b952801c450a00d0b4411100803240c07400110f20b440d80042d02840c10f071101900201c1d80c4034150760041d00c0c2c2d450310310303404e07622018002c00c90150751070003401000c900025000c482724080700116181e80510480f285000068502e00d043da51440f00319201c402042e035074640d043c3d84400d1410510b00d824007414002d89203100b6071a080b21030460b60500c0b142043d520442c1150300c1480da240d4029041094143ca50382c1625020980d00c05d1003027800094401c0c160025005401c8408215510b05035901c60601098001802d101075142e24042150f6406a10140b01e0190 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 117443687 1250 117442437 117442447
    0x70b060118060c02010e10080708010501091503051806010e070206060402040f0522020d0209180705070f0f0510020702040b0306010b0d090c05060301060e0909011406040506032b020d08010308 84
    0x2501440072210f040d403051400100c0d0f07250030404035880d104004184000310f0b411409000e41c0a4001403607901500c401c0ca0f120041601d401c0344500106c1615003e10285503464020480c050200040210f01da82241c0445119507510035044d000c2c0c1d1409c4a000c030040c0111001300c3e20320328180c02150116500307060500f111506113010040d01c850030a0740001030744001c00c50030705280114000382c04c000304200d800507111180701c4240008101488512000140c45504205500d600301d010398884580084100d180c8025610300440d01d107104410160161188070b4054040d40c8039500200f03461031099400344203c4c40030a042c1a0b40d84000e0043c00325010083c0040c02c085a07032907102e04002c034010507185400c81e6880e404980b50350302c20782141d070005981c2c0d2007581d241c1c01c00000040c1c103c0f01800c020041040b185840c1901401c01070200ca21807900c8001081c09903408019030200851004c0c10745000f140c001f502c030f0541c14010503440002d4000d10515940190085c1c000c0c0703040784d8010041501d04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 117444937 1250 117443687 117443699
    0xa0608060a0216021806011808190309090618060e100306230f060111070f05060702060f03150f150d050a091406040501061502030d0f021c02070b060118 67
    0x41c3d08100c0c00c1c010b42022030718034400907940b40f011240d1003400204500080e41080d0000510103960b082031100c502828030020069a00000748070313142c01d94030a40241042e505460100c88201080c0d001400c045c2c18148081401507001c90203403044c2041c4c150800c4400d5440036800d0500408a038242180e081e66602000450f0392074101c01110140d03a28680c24020060702007480304142a910034008048500400015503000002c05004602c000001c155151034600d0000c03d0300101d0040500405c008118141152514400d55005034481131409890303251260403401031a01c1854401d2140f6195003541800742000c2c1002e5010651a500d03a030720301074034010464041c3c000036200030940c503610740701c460103d255074140010305900d04002d4050760500341403040c20f59803960002440055004c00c20501035800004032101ca00008202040180080540000078001d15540c40035004d408031340965600016030042011034840c1420b0200c5480d4003004507a43d2a0304c90802c02a42c0c0034039824410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 117446043 1106 117444937 117444941
    0x3031806040c1716060c05010c0f09030303020c070b0703020d090602070b03160e09010801020a030e0102090607081305030d08041110020319050c01020711090a0608060a 74
    0x5041948501e00040d880d4070034801c1c1d01e030081c0459031104100f4070050700c0e080440682492143e98070003014042c0400c006044072654a40020090010700403405c1101c07040065649840302f500319a415070007076004440003e514460328000244500b0588001c107a0701d03200e0f03070180c18002c41c1d620b0080c04d550340365000b80c030940d00507903014401c1010110580e81c4c440142036203140400c01084040e2140d1420050700d40e004240740303001054008054000b0641e086159904101202c1c20004c081d00f04c0c001c03140c006070b1100003080f0070004030f42c407800038004407410100794440181d560b0300002d00c0e00c00b80d4169600400c240f10108000d210010303030410508407040c0d480c41000c0180d018025140d1050700c0005040900c0c1d000c14104041c0700d013040d2054002e040008555408407410071600401101805a201d85485800030b6610f40c42d500035a0f04565091f0010035164036040c2807100 = true := by decide +kernel

theorem cover : BRFrame.Cov 117266187 117446043 := by
  have h0 := BRFrame.cov_init 117266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 117266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 117266187 ≤ n) (h2 : n < 117446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
