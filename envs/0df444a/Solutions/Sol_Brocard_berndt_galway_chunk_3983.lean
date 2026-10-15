-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3983
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:14:29.558935+00:00
-- url     : https://prove2.me/submissions/f7864a4e-0909-4914-b779-2d2baa98231f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 716187050 ≤ n < 716366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 716188300 1250 716187050 716187077
    0x10510120f0b060d150e04050601170c0a03030507120e06042603041205070e1501050a110a0302060a18050c0d0c09060e1602010504050604030f05040803031608011e06 73
    0xd0b000c41109140c0102c1c3c0414800b00040301a0408000e10300100b221441e041c3e220003841c0c244000c101c8014290768020401000302060b000c50ba00031114084c010341e54840c03c8a00051004409648150300142000c500f03041403280d0345940340f0b0100c0042c1408450111240003003201400f441c4166070880b400c804600201c842100ca1420364000680281c03a5101e0312524000500040d102013543c503071040315030104040d222500c100d0302400c0f1000c94600c1c01c5050000461b000d5100e1448a820080768099030b4985990800010002ca4403940107828140f40901c600710841d00e94003401c9540d54808a0a030010400c08202145107150a0322020f080c24900d0600c0488914980c0c4001211468200001400010803070418042c8021030382410207d0107142c8200c0c03d0b00c2c2c05480140140e0424004900024080c48106075010b109060050409603103c2446d030858000700e4040040c0c041c04002d1108040e40090340602511800c071140000307500c40d40c10b03910040d01da8010b260038800381100228 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 716189550 1250 716188300 716188331
    0x9020d14060d0f0821010e04170f0403020f0604080a0302010c020f010606120203070207080d02071d0721061206090c05010212040b28022a130209040207060203010e010e01051012 78
    0x20300d906017182607101c650352590148440d1904031816580a0026515440f00000c000704440d6800d021344450342c18a400d503000c022440d0204e440440d4842001c03c400a00c20400744160510580250000216030342240406401c20180c103140201d980d24282083c800940c010b1000d10078281480e83c0140c030b90f03a4512080c1c0c540009900501c3c0b00d84152800012010303800511003080e2a01405e82003c2514904081524940242d81c1d510215011001a40804e06240420070310b9000c280b10110b44243d840c8040002d0003000d0105842054590300702605200f0520800d00040400f8802002602c0c462038005009028901442c07241100000d4104000406800140c03412007014440380d5407030985c004040c0d42d440c6404521468a1104106111180c0c8101403070f103e021000b4010030400c01c80c1c001550001d41c09000c03925485a820700001011940b1440030b14060681e501a204295041206241d4030142c1644964031440400195007089039002101c5003440c14551030120300009005002c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 716190800 1250 716189550 716189587
    0x60c0403080c10050f161404210b0c040305150606030403200303070306090e0d02031b03160b061e101b05010f02040906090b0303121009020d14060d0f08 67
    0x43c1c0540e4100018801c02c01da12030340f501d000d49145844000c0e400c400e0740080d110b030360703940700013644080081c0802c00c1806d01403050790a4031240c84444090a040d10342d40c00c1d0302708200303a6803204584000304042c02080400c00c001c58914000d81213020091a001c400031382c1500c0000d00003800c0100041040c072900043c16046c0501b0b5116105494480c50800e0380100100024443c90308480d04182e42e0107140c84001c540303400140803980c003462406990784902d0b041440071242103c2c0b144010400040d0b4042500302c013003c00c40c811510a5901e003040020040c4c06003140c003108070000d0840c507611302c3c20b41c1d9002c2d8140c101c6545080204a40ea03200400340084030b190140a082c650820340c903445154005c0d1300400594400385400c1100c941c4440800d4201c0e000d1412003a0540c0c401c0020051400c000d504040d801400320644e1030380b0b00d0b1030b00803070400ea0b0450300c2140d02c4140c0303400c0d88001035481103c2150740680150b40380000005240c0ba1610401c0040c00c0243c00e80f04001048810042e80300c040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 716192050 1250 716190800 716190823
    0xe04110d050f060718060807020607050309190c0806010b032211180604110c1203060402070812010f090b090f090102091e03061e0f06040605090a090311060c0403080c 73
    0x9a480c1ca213800140940307135000c0080311441e03a1159440c049600d5000380c10701070203031409500038601c0380d0b01c156041c1e89650014060034101d22602440c0c50200600100d20100d05104050740d000140c54408458500441a00f00c55280c0750b040c01040141a50481070f50a00103403640b01c0c1b80e9907052410041501001003848a400c010a041809200003031151001d0042d0000d590030402d403c50008195198058802125030179001490b45881d50313901480916001000104010b00d841c02554070354510740e00c004107001d22984d07010010051081c840400400070314000005000c0320101c10700040c00f403040248a0508410307d180424944082541501c07c60389015011801d1000d00405605901d000c007554184030f8850717980042c0e0300f50702c01804106010010401500c01e91540040411038040041c812a041595908006415070320304181900620146400081c160010b05000f8540041303030030b00d42074543c4a80c00b801400e401d880b044808603a0014100b640304c0040c2c80302c40d070506001145 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 716193300 1250 716192050 716192053
    0x5190e04020a1d0f10110f060907170c0607140c280911030103030c1119050f0a0b0a05070f06090b07110a051f0e01060e100e04110d050f 60
    0x12848200c1c0d82154950040f01c0c14207441405079040380080000e10310160a100ea0000c07003842083e00d0071307401000000604268002641c440e181440851840c103401154681d4640d40070380710800480303e0b10030024009119031360140202d01c00c4000402c0d1648141100100059819030303485e291404140f03c14105888020f01c2c444ca9154200e8201c3c002e540c16060b00c02c0e41802c04400001c010803039100c1ca0030f002c3c444160050450703103180c4050322a00711008050361144000011a0701c541d944043c4c0d00001400c80941c50885410581440801c00b100e1a1540c01220760303100502000860714142c51300c03842c03145041c5036a00aa0314000f41c0e090f44080c4000c22980c209800c0390100040041c6141c81400340b0764a02c50200c01840085507920604c03034000e41340c1d030041403000544071420752031985640307102e420125114807942c26850864206900040c1004002c6050013400391022000307200810300c00d80d2200b000c1c101502c440d24101c40701801140702c0c41c2800e00d0030040140c11700008100c0d24030f040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 716194550 1250 716193300 716193307
    0x20303030628150314040b01141f052721010204080a080903060609100501030203070e130e0c04060b03190b1009050f0414070c0201022d01050901020a05190e0402 71
    0x2100795800d540386080110119041548024036900d6002c1303171034800ea41010441150340d1810070140500b5000c000c200b600f1000e40304040d1040321044001094851095a0b010750303c40d0050321080c04603c01a215030205202802c009403941c1d582c000480100720318024104114a540f03d4881c024400e0f07900260ba140960f01d40c4a0a0003618405041075000981c10740385203541e01030810a1001003103a5505080301d8249007807260354403c0c1c1c042e55000f1450308005800b070800100145c09201c20030500301e0f800c2d44039002c0812401003803010a502d80001c0d02c0501100b410400f48224500000b0320139580d009801c1c001d08801c800c00e81003100d20f440d002e80200640200d01900814244003030081d54061401080a040304d414280720b01c03401c4480c5528080d5041d1609842203d2100c0b844d4000d074110b01c00d102d4007042c6840401c07a0724039004000103800000c492080180d5095600c0200380c9407999205220b680007190700031048171801200d00758080d4020203411030580d044986400282c2c2c001c1e2012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 716195800 1250 716194550 716194559
    0x10021e2112092d01060f0905090c1009050114090a03080a08090a0c0608070903050f0c011d010e060d06031221060b0d0e01020712020a020108090a020303030628 70
    0x1000189940161191841400e0359a03039001c5540ea12040380c8014114403d0100b010500e2501041041c80c000140012800700e03642e118080001c00c05400c04500d8585e40c00911044400030400390007a91800d0398404034a440440c00030341048011310401e41400b01c25202400034240c490704480000c0d41c001d0074014425268280b40f0265008001007001140700c2201192098900091520500d076109000401e0241000b45c100c070827200c0900600c1c24050082c10110009500340903079030344078054600030300c100a202c000050080381040722110032440c3c01c0f5007070b0600f03903840034848402d00816a21141d0750088080400000c0000d6840640075400160721088010b500010f10580c3d020600400c01c820301002d030801040301e0303440c07140104950041040445045207034109081d40b140306000181055010340314800036000c41201940146c201030310071400c641e0020344554009017000c00138641c000f5940d000c20351302d10014010b00d1003071264420f5402c16407a002968003101a010f500007840c150354 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 716197050 1250 716195800 716195863
    0x10092003160e040c1139010e0307080606030d1d0f01020a060c03231005040f20030406230604051503011b030c05090109090b030115030308090c10021e 66
    0x840450003190240c80c000c2108004000001e0303691890707540c0c0b89034490703c4960348511000c1070341b01c120f414080602103900c01c0355814003074900180300601c046c00c07103031900c20300305402c03e40f800308414244100f00c410840902100c201c100c4660704140c03203044000c01c1003801030f46442c002503001841e003800c200090f5a4503500d03400a07000c0d042c400c3c1096414848103020164180011515005444000501040300c0d01e001c4d0054610403002d500000344a01d0340380500200354034004100410200d000042c4810840d15110300500201805c80101c040b0411094a01501c1c0d0040d15440c4030300c1e101d80202d0840d00910701c5031440300000900070090000d005000140304100c40c804103000c6468944400e00301401003044900c4060140e40c1ea80b03203141440c40410042403a81c0341150950369a401144210742030660302c401441c001e44402c24249001000da600d8101030508060060b4010042400710301e800080304500d0045100c1041008152800d030103180413840340224102c0104080d590001441 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 716198300 1250 716197050 716197067
    0x16061e021203040503120610080703050c220f12050304060f1403190b0102240a0609050711071a0301030b06040e06010b0903010e06010501021203100e10092003160e040c 74
    0x1ba2500e403488582d80c200c10001e030644030b207500700041080440020090b6120fa4403203980702c80b628101c1400c24803440203172008921500c0564510a11030003080c04200d94468410000b400c4032441501034484a46c1c0d00e07610b0b805203206010034407506070f03050380031140142c11101c1a004054100d40c0c0f24940200e800c032a0000700407141c07485501e40011401d41d9440404c060849d0421520303000c1240130154248000346900806107180c141d034a25004c1a41c2c000c0740143c1b4000d4919541c0d8140d003030851300c080f5050076150391010301074545c1d558080800c8040b01040c0c9044036003018800c4610b030b49150201d40542420140d49100b4020040085803c40b05040071b850140c605400800400811901d0f099883c0402c0c001c0501583c42111800044604071005590212074460b00029196413030362180c11000d010703100003000c601c12800501600300c041c1b1540540340000054036041502c100102c542074030000e8074a09101d07041c07080403110940200001b01030100c000c0c004020030188840028507012 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 716199550 1250 716198300 716198317
    0xc2404150302071e02090610050f040914010621050c130f1e08060606070812041113200a090803040909050d0807020309190302060c07060216061e021203040503 70
    0x68800d01c00613202111440e85140c804d42c0608030021607110361040001d500786d13680c0f40c1820420204404207403107041c1c03409400144410040851030740030b4003207900301a24058005404000d18181d5201c60459025000000100840800501c1d620340391007404072882071020b6030741d90803804d2000041c1301da200e11071602255405045140300405c00300340e04038000c12074030500c40140e224402040140c680b240041148910808015107014400780780e460005104413800e60f844103292903008501d003003130880d660342ca1024007c01c01c2840a550490305041103028502d51000c07401003003004006010f40200e0740544080e0080ba500c07a951030500d6406045461000c503418041d07441582c0c000360148407a680a072041760082c6040c6410501400300c81c00c041010007010040c441c80000268a88100070084c0c683d41c03c015100141c103103140a85000c91140e08d8249000c0400307010407959511031b404100b25040031101c42025065843d04901e0701201c000e503404202c800105000803c08000010240f50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 716200800 1250 716199550 716199563
    0xb1c03091502030c030405190e070302030420011d010201110423010509010c0b04020d021806040b0f0120010204051c0b0a0204180203130b07020a0209090c240415030207 74
    0x1c107510300c0100c1c1c0300d000d48a1503c00030f901c240000d0003140361224503070007080b06900300c40307107040d98420b0b10b140c0031001030302c414003c40d500100340010b07c070705031181d080c074070020f8022143c2440da200e0000b82000240241030003465602030303091085a10070740181051400c04010760384c445848001d900c5840795204881e1244105803202520194021130940c2d100c01016141c65100c03402c1501c0d40005501c00074001c0f68040e0304003003400c00503691580400602c15030010403184c5803814205000880d103010810718030035461010920b216aa00001d2120802c11200ea0300c140c108280f40b1590180c0100d400c130541c4503881c46407001c445003816220b904103d0180440c40505d44801480604912940c0544072000002c1650900103050300d800440c0c20000301c24a140d0503c680e51281203200307205964a00050300101d543c0350542c0751000016400414213005031010b4201000040d9420b51100205610b21002009202e02866030300180c0d4010003c4290502858103440b4004009500c10402116003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 716202050 1250 716200800 716200829
    0xf0a021c1a030319170108060621031614072102031501150f030204120f050312250e0d02040c02120c0d030c1806110c1203070b010b0f04090b1c0309 65
    0x302002c0170011412500c0706c0d07000d01034580301c490900a86417480842d841c20a005072070814071141e810001481c2c80c81c2881c1400251107100e16124000c0c1b450801d21407426404131009000c1c040910b02c0d6045920020101c03070100a10f5440420306015500d061010046803160001403401100c42143d800184260b8410090025848098040f409107002d07045101c49514032b51400107400101d0310315800c2c06003088a040040d6032000182002d01100c659804040f201d515440072a488072480406070103d0400328030881580000c2400040c2d8402c02074032443c1c4840807020340d24000c2c488040c041c422110000e50740c1c55541c1d03640c0d5441c03800c4012035001038908101000910f228203100c6441c0103034a088503c0031860001c080352039403180740540a1500840f0301160141c3d40c0c5581c0b02c0d11800c6803001442d01c4503c1e9040844501c981640030750501c210070440036040f034641ca402c80b400e54200031000641d0070901d00c0418813001e00350112000d0102003420503018503801c952050100c13400180c04504 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 716203300 1250 716202050 716202077
    0xc020607020304080a0314070605160f02010c12020918010305010903020607090501170c1306021c030207150e0109020909012a050a110a06020a05030f0a021c1a030319 73
    0x940384a07902c100b45094024100c5c09000902c200c1c00304410f03a400350b032182c2c1407000c00e4848100715907007602d08507201c10031508002d040c44c1d003207076900404180303600003006050900074010380070024007034460160301d45c00207141a1943d20303840036045040c050780d040410756840746850f90003000e05e03401c10380252140c0c20004005502c194214410394006949100440701c008450301041c40c03020380510a0400d007440008015100d42000308014900342d40100300f0100e0004041c6e0149681d069884205401081010040b42c269002030700c0362000703030200058510a1600d100c1c010310300c4900c000e5114242d5414044042415048820500600341504000c0c65001240a01c034100501e0003001250081c403d803034055000c2c0e44078001c012460003c1c1ca40b90701342e42d5500c000705d1340450301d580f02240c6d0200501041c5051194225407014a0b20011840c02e0011812210304604455161241c1a02e4088401401151001e502100384000e421241c41b4001000780020b51000300d0a0880081c4044203001b6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 716204550 1250 716203300 716203303
    0x603010510050702120f10050f1308070c03121e020606130e120a03090506130507030605070203130b0306030c03030f04120206040f03150b031f0b0a030f060c02060702 73
    0x9040340c00040c000240703050014401d4840d504111001d991001c016010341c03031802014404802c2c03444021000d0096a03884012175401c8820180101c0b0039410940c1c20000c0807800d4984a445454010b00c004d911000e0724504501c020700c15800050034501d4681c101080701e80c01100c0380390100a5610416264822841704a81c2d8450495007194040d40c50609180c01000076801030100760420819100043e400c1500000a5800f00711f8001c006030340ca207400d00a102090103955042801004900401000c030780300c090b5105041d0101a080680d00c01c0854082030080044a00e120540042d5080c12603075030101040d00d0b0421105103000c0d014040c0f511406240110888188000c820300950801e41400503041c05005070b80703002c0343c0040c2d0400010440f1501072031607000070351045026040680d20391030350b1420394440f006050301a40c484440350704c4d0444040040203845024104c00159004040c00140030540300e603001420311105107210605020064000c0203526416800b03c48a544404404a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 716205800 1250 716204550 716204557
    0x103060608090a080306060702090c0a0207050d0309060f12050411030f01111c0e0f0705180403020d030b0f100203070606050109050a0905072d09231207081f0b06 71
    0x402e65000480c00100003040c4402541d0000b101600040c00e08505601040c1404029114044180c00108e8000c3d440307541008018040d24007922003501c0c91040795406041d0420900841090140c0100203200051294081d024165030f002d60074041810b150421f16a0211036441c103e009009036440300c62100c00500406000c110400c240c03903c0e04902c0000c0b080611840c1d40030301c240a8840714900315810081210003d6905090060400e4900e400200901c1c910798040703410075000c4000811001ca40c0200f0101d0490445040100c0e070258143c001030306c1c07001c507800c196501ca8a0540b410481550001c054080d2510545007013080c19181c1c1c0040d104881107200d803651047c0c0c0c1c5181405032031540d40205030405140e050004018011080b00c7c0044900c0382d640c000320b6180450300c0001d49074885603c00003400d001d0001018400030045141d0000550081e41c1d0013941007c001c0300110700c04114101c01060504246c07a0b030003041e010007420751111010300f11940e600305801c0038200c0c80c024084 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 716207050 1250 716205800 716205811
    0x603060605091504080a081b0106061d0427150b0a18020d0204030602190c1101030e0307140c130b0604260d0207061805150306121b0103060608 63
    0x5040c2808610400c01044014a43c2e5450079508148000250940d003008000319540c07003040c0c2e44c0d843c0c403070f0503d01c94040d20a4052000c3c0e5a810181c0070020142c00c002c400381441070b407400ca112480c0c10580898003a0040864071a48203a00702c4106203084402525684450b1281172050080030a081110003503c5a0810300c640c00142100100100810b850702c4441050800001504229a4070911412608183c0c01a20001d800141c0000000c45109001440e1980b0341000907018069860f1a0300100080c0981c0381490740d030b040340c0c4100784003c1090b20445644982c0e21001441c08108103511030340d05c40071403070190b210b03401c00d01361801c040d0040c90b05003030303014140c50309192600856035659506062032003194058204800aa0030301400740c0343d8425110340040c0705c803d02e040001001c0242c80300c80302c110071104034800c0c4501d50b1000b40d003482640250715940e80342d031113040c005a80c3d075280d000318620601c1203104c4050384004c2c01c0d080000d0058262010040d550383c0360019687d92a08682 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 716208300 1250 716207050 716207057
    0x80a0f20180d05030d020c1c09060314070903061a060d0603020306091f110706020a17010b0c030409090203010e030c011b08152407060506040615080a0207330606030606 74
    0x40e074820750442d0f03021f800c143d54180121a042d000941154244041d0142090001901c0e01d000740002c540500960101081046842071a480c2000004020010501004045585032851042408124403000e010729070000c0c803141d41c034201c680c00d4000504031448224024001c00700018254240800d203040d2a00f12420601c1c3e11416018211009002e0b20038900c000c01c6040c001c51001c50b0140c400f41c000062580c0300c50400c6101d0035100000004140c1c4004074000c010000b80380301c13850101c2a14202c40703880780d01140c8440c1d5440064050b20840e40d4075161880046441028260150000202521803e180030745030304c0782c0c4000301c0e9000f400700c40c002d6034218501ca0304401d90038845100c02001220061800020313050600d051810780c07200c4011b0781e145440f1414003110f803420388141d00044c6101760101c440391928100180444400030101c441182c0e001c00c0007c240304804491120b400c600300c506083e0040c1e0b11343e55450210154120110861034000046111402407007188140d8003c2c2d02c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 716209550 1250 716208300 716208307
    0x5090a08070803100b0d0509010f020301081005060d06140103121706100212042d030b04031d0a0e0126120a0903060507021f02070201080a0f20180d0503 67
    0x841d00355032944068078111084c500e0401c005a0a5031020243c882c166101402040301c0c20011415400e4642e030a0751078440b14030400041100e031400281103405000048008211f50f40c0700400110f0b80c905100c1d010b0301c15404d003a1004403061400d001c09058038401c4916414a0108180c00c41f100d060303481d0308224185624020491524000a000750707188505e10455100302510401d01d10a500b0941c0950039030300400c80c0710381d131440702c0010500c3e544050040c1c075110300b45192209030f50001c001d40058140106000140421188a072114855801c080d14422155598081d5104515801d00c41d03d409201000c4c5910080c05d11681c00c910b0503c581380c01004444140c05003001c46904c034211440900440201c0040060080d001c0c5030301c40c26841c0c014011640c41000d54801e200412504010a617104000440040c2c3e002141c158200a800c3c00020300210103640410090041c500030044822060700d181a003c2c00300002000c0310110031070f1020060040c0e02c1407200c00440350400628a41060 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 716210800 1250 716209550 716209553
    0x804090203090c040c02010b010e01020319050c0a12050712050c0c131401120b01080a03090e0a09050a2015120a02041505041d0106020c0d06020d0212090105090a0807 73
    0x3500a150440d884100303581d030040109000500701e40c007103401000942d4542103000c02e2907030010f04154080d07800b07001441c42d1020080e1712890822001406c10f040c0440401c0508001c0801c10a000302c05900c118042d1087c00f1407840941240c00400040344c024100f01d1a00d84410303c82e000b079801c10a001002818001c00320030402110b010302039550010203941d80f40d948a105144041980241500101041a00b40d5802c1c8881a250160020101540513126140000b94810100d0044810710b420310009602da03081000098041490064014481d00c0041d50a00c402d1150120103c00072142022000c20303003400348450380040021856920409008001528003010b085503070000e0544001482c0c140c580d080e0310306d80b41b070f400e000b200007031404181030100c0700c681601c1090144186201c20f115600d07140d0020340c3d801103051301d03d020b4104145c43d0400c1280135010f8829540c1c3d910010b54646010498030400038030122640d0400d0340c20600840c0011074080344d000344040d0000760151509005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 716212050 1250 716210800 716210819
    0xd031e0315090b0d02150904090606030b010603050402090a05060a0b0318160b0a0c0c0806040f110108040c050d02040e010501290408120c0709021204200a05011409031905190804 78
    0xc0341c01406c0001010410113440f540c4070312945050a1060728002561400c50034043d1000d64141c00c50418546410140b001594900010691019a001000ca8956148000f103403446501d90300c14091804040144544d031040140480b8200c0016811140741c0d0010000c030b9071402d18030b4814014089070400c0861341540c4030321488484180030300441c3d000c0d03039038846100740f404e1800c680548003245000e69540410000010111001070f0910300400a4181500d03003100b024058840d03944a0300c0d07190005011034440d5008200420074100080220350f03900da0710755801c5006110740d000714000203072031480c44000041c05e56043c0d0390b00000900140680d420680007541c4511981c0c015032140f035200058841c0d1a00092101e014900b036000e040d41403502d441c4581c43c880c0341d54011107041d542041021030301e50411510480c0c03c00d103010036600d6540c8210036207510a0301c038100d4240c000d4012000d10700308403a4120800b54801d03003c8507010b0041042c40450018911801050341600300720410281d0b64 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 716213300 1250 716212050 716212069
    0x5061f1d04090c060201060e0f01033207061e081909020d060905030406120b09061e030109050607141c0908041d06040f0204060503060d031e0315090b0d02 68
    0x401070300c0020101519122041882c100f5444007005039111402401316001c003500582d0000c2045c2c800c05080d50440c0c1c1e803580090100c003190000c42c5102150100d100380e240100d5403102d460002580c0c0031036140e5100500c2d0014005500000e80e01c0e10403440b421900c15101c080c4124010041c8000328060211002c019241c1102c0a9030f100c0601584000800c4107031086401e0640f0440056998500d0018007600c140c00c804c121024003494480880b200b0748542c0381041e40074608640814004602074000c00d104000c031441c0341d4256107404c01c00310800c0300028880e8040c0d01c0b01e0300c503024140400c502c0d0642e14401e01a40324803e0340c040c5500900c0c86442d80042e022140f1841c022070600c3d407289002c07225040c8107a80c40a000240c0818042103051a12030b80c550440038110a51509040c5040600148405090703e4000c1c44040c800f0800e06116840c2000444610070f1aa0702a40c1420801000b4082d2001003d10050704140c001800b07080a2143c00d270119030150558000c500c041d02040303030701c60 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 716214550 1250 716213300 716213357
    0x604050c190f02120f0a030c050f070305030105040509070f15170c0711060c121e03130303230a020a020114070306080f01051e040c03050a0605061f 65
    0x10074440005240080650a40350440c00e60b24585480101c440c020b203454900d5101010358401000100c01104e820022220308003028180802c8456908a0445e20391291407a075510048021541d0010164880c00035412107000311003e100d144c0743c0320b040b40c1d00d480051207a584002078000c010030512040421052010840f420700c06080c0148580440b0140011101481c10500000d000e80400c0210102110348500540302e9500701420040b900e40da540300300301000050940480c85810300030301210500c052104e04070496485e414900c603c0c003005a2405802c4010900b00000141020030b14519280585410803c041503919003000b860020350242409104554860200b5440380340b46c050558000c510903a000554076240c0251039080003034000300305200382d04090600019120703102d451101800225203141c8140c459241c145010305196100814600402a6400502c0030b282c5c02103110324415101c9060030440c421000034a079040c8412301000c600c0740c00302000390b50903101a854829 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 716215800 1250 716214550 716214571
    0x1f0c030f060b2704140f13030f110304091b141204060f0902040e0c03010c080108060109020f041e050901050103141609030b0c0a0f0816080c040b0c0f1b010206060405 73
    0x1a14100b000c2005e6a40f1081641402044141403001614600c44020b41c8401c3c450580356101c4140d9400074040606505840300300150140300640c0d07103400703208540041020280070817061071b040060302048291030041da8040360585915029401d80c50040b55000c0700480c040138860740d9650340340002401c4540d10180e03415512121280141c969101d64405405040020155941a642011f094403d418a8881046502001040a0000000c420b41520410321025031a089050280c03d203a00440e401100005c264a444541b9a011181001d0540d20196000142c0d1b80e02c3d200150305451500280032008540180081c40300041188640d02c061120b2600112065980d1070700c11078010140e45030320762203900084010207244c00c240c01400c541503508000c196031400104150ba407900c86281201800762460025200709400c0c402c8501074424010b82c2c1c0d4883c402032111540e10f02c080c502114062250469404580005002c0680400300c164000d080a035902020700003e041c028000013141c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 716217050 1250 716215800 716215867
    0x30309060e070e13110f0409081209011b080708100503030c0606040b04050c0403320f1002040b0412050102282604060b01021f0c030f060b 61
    0x20114003402090303007581c5005100283c01c040e81c6000803071000e402c0d62460854141c00400003040081c0c2d0051114084401d603514590080101d07020301a1140300030440d0748001164a010b004694403203004007410002000303c0c02c40e002c2d1104040d01c000c044040410240d200003084140704075074a9500c200000300704510645c0e60f0b004203286400071482261150041003c20020307040901c0b8074001c0f044111014041424420040880c52040c1d005c0688100c640b60810a60003030b802d60155a841002c08409c0d041c900748502d6242c81e801c0c1000e0741003031801000d04102c440d031428000c0c1d40583d41c15100c030514051905405c900e94600604080346c0ca55000d21800459081c030034595007a0300483c0214000306544150020508540407039180e030311400d0000b00d450070f46e00c4000c5c511350084e0301c40c80000e280d03582c401c0140d01d01840591108280c28008022a08405e0a50851405545e054030240030003c1c080007850207a84440c0035048407030a040c0b04041d8103126a14081e402e41c0d21182c81c7c1d20a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 716218300 1250 716217050 716217053
    0x30c1e030f020d06031b0e0402010f02010e0607092c06010c1b06030e0708010504051b1f091503063c0902031801020a0c0308360c012a030309 62
    0x80c0e0300600043d4007010f40c0d4204c10018011283d55201001d6840400d01d1159402c010043c440701002074000f0341040172103040f00741054000d6200f10342204280b000c5401d04c0c501900c4c002c1512110b80103404600c0554040c00d4580380000303d07100c4034103001130303061000c41ea514801110443c0c4a1001035032444120304075149c070b0301c181503d5040900310b640d60200d401e240c002e03840c5241419582c4508196850402040045600451000c002c103501c07500290312000c1140008000305c00e00785144020103a603006409c8c0c100e0700300ca25141101d40e910b407400b0214050000036030031982c0c54400c00b80b0b032500130355009403491102100b0390030081d120f1111000c02000d1491510031280544c0254860903800410701905c80d02c1ba00c40756801c021848003d520b0030350f0140d0000d080d100030301001000e014040c804101050003215000440507949600340702000750000d90800c45100000d0014082c1c00b950110320486e500c5a528500200d850004000c0303203440c00201c0305401e24482c1016420180d440400782d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 716219550 1250 716218300 716218331
    0x120301090209040e12040b07020609090a050403030c0c03091205010e10020409060b090f090601021f020706050606030709061d10020c032a0607061b090f06030c1e03 72
    0x14040c1214020040e21102494140001c4440040c0b003402244e014505c50400601c00c041220309079000700007001d807595841d101260440c0902c940b96079000c0094000c1140070040b0350b104601c182c0c0255001e10420111120030f0310800da10540280029044e0791050040000180245400a10800000603540f02c00c40e070050400fa506560040380a400040c02c000007040c500506010304441c4590a141034007800002d10880d1711254520b0041041d440000e03c1a0f00078008074070760b40a460103200998005513241c8009501070b084c1116003d140c040446c865080a4054a1090101c0c0c0c070f8440d09641044000d451410001c40310103903a0502e42081b298680703581c40c50591a4000360010000324116404240c10558104a0180380c40310404c3c0030740c9000c0c0b015201a10100098503041d0f81d5030790504048014288920081000c03284420420b90300c150712010b440c0c126481c0b40081d051044e11001d048060341c0c07501a0f0540011141c00155400404079001d003903045040d1b040003d9803001164820 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 716220800 1250 716219550 716219557
    0x7021c0512071218140f03010c050706050109090203030322080415020d0f0203090607050c0a1e090e0c1507050a030f02010606030b131104030c0b07170a14090312 71
    0x203004400080b407a1010001083d43c1d50400041c0ca0070500b04901c49080e0300240b0410310301c5083c180c1c217825a10300c24180c8441c040036043c0d001c003070001e00c00c10a00c03c00107403080e84034220840d01149840000904c085440c4035284104d5401805180b440c0c50308034282d8200d4681c080ca0302d00000b000b07401d820000e500c80005000820300c0a8244c00802c422180280c01c055983c3c2d000c00902c152820400316190340401120080c1400320342c519191801801d00300c0c0b5141d0300301e00d01c0d038200c2c4070a4400310b4940c81022010040248400c0314801c3c0c1c40c1c50750081015240b52120000e156031040e069012546401124603200907021401c95080680c99100d42e0b1805118103001c1d4080394020450403501c44d03084c00b62101404250806101480009000c501242406142502e016664120004075000c001045a00075a0403c0180186035296440e09a20307510521302150400c10b1041054558620305054544404035500ca541c40c4882108102c00298400703090141d245c02902c1c00d0058088003800075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 716222050 1250 716220800 716220823
    0x4081504061a0a0e0c0f0c07050f0a1211011b030f0315030b04120302161b05010305010311010806060c070621060e13050106030b1303031d0307021c05 66
    0x8125a4189410003104452409003240922926010b0802c0b4685840041e68101c42c00c0460401043c4d5035019008070a006001c02c03040e00030400130300c0341c0e043e101c005460000c0d50380c01c4030005124180c003000c114000b6501e10035900440d18844100e070105482403940060208103040c900001d45071548a1003200102000880c00710b44d0031015a203005505200300c00d510003a40742e24000309030664859964503140180700424078401c0440750070000303219405845940305d00d01c0c0890108c24080c40d200c413442da6840b01c96560440ca12100181e81d6110f400360034101c03031300171a44100c1e203d0740d40011074100d81c00404054010740100880514414200044401020140d47d805800002100c0d0108160f0390074221000703403400d00ca405d004110010078a03a030400801c0150080b503500514186014105c0c0754006441121004204a804441d80c07000c020f01c3c900c80d580401030010040c0c3d03441901c8400a04400b0550300030f2110200506200c207840c0d00100c120310720201c45c0041342c1d070350524203142e6055 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 716223300 1250 716222050 716222083
    0xc072706031b090606020c04020d0e0f06070809070f060e01200f01060803033606040803010e0601020703050d1b060f02091f0206130201031401080c0a12050c040509030408 75
    0x40852455081040e1030b4040c00210005005091609900a40d0b07030a019000920481c4e00040480c8910700507030262031400740580c140c4000c0381d03095500b40e0f155502201c507a00403513045e20000c0c81e981804507042c0d040e40c0d1045110708850341003001c1190380200f8484694180000010114000c071140a03030600c407100207400401e0785041d0201c1c4207003900d2459015108640c0300f40300f4041c0051802c6000c0805a03001100120f26010544552140074203c0e814200349005a500703000c01c1c48482001141662a0700e426400c00307032145801207941c0c81c03692002501a40152025120035846591160651740c00100c1c0d00c4140c0c2c1d050384941048960b0714030455400c40d4001000c030b0740d03800c0010007043c2410540d81c5020510b000c00f40d01075120b220003000065817902850358181168081e5001d541d074210341c1010292030307603140c211990341c44500300181071040d865441d0005000200c0c416135850140e001002d009512580d00500010300380c0581030359800e000c14400820741d0b0100300407180d0000210031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 716224550 1250 716223300 716223323
    0x70618140d030b0d0602130b0304120f0f020703140a02030708010209030c0604080a0b07111c0206090106060207150c12050703080c090f0f011206290c07270603 70
    0x14042403425406110020a05050404180d000c1e039400c1004544250410400b60703507030b20f40d404041219070094200281c00123000c0180400e0118690100400310041e071030300e13410b94604a0041d070f5140100c02540d0016401000203200080328090f10b812030b40490b0b403c552891031150b00185c00d046240c1c001d04500da60101c1c078078202e0703d0104200e9000301da090b0340241c03429040c0a00386441c0d08807a40003802150364200440c11551042c41301c0701c500f005030b0050320281040620047e080e2910548480010712032640810010307641841002c048410580081a48034900707005103130300c102482050014491940c04040210f1001c001c0e04001039510394925580b101c1610300a0429940548440b44001c001d020b6614151500031100044000c02c84092041614000c012142e50410641124407641404400140c5a0445a0040710740d50000c0f038120100c0ca08040a031080d025202c413400300c0da40809010072083c22030000d04242d980070300c05450080c07604407032060241c0b416507104460900302c82 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 716225800 1250 716224550 716224583
    0xb031e06090105160c080309030403020402040b090f03010c0c0b060a151205070203130e0a0e030a02010911180117030403211b0b0703150909030c1a011802070618 71
    0xc0c403925a0000d40d101c10002c888104e000001c181050302c03c3c0003001604000041030400d00c040064400969000300150340e01c580320000b80085400c89a040c5025101381c1e00003080d5860103019034022141c0e03036641c1c000c0f450041c0e00d6034a03100d880604100e80100244001081700844e20702410030f11a00d90326040020301a05898400b207500003405082150800c0c0424088048a010741c101114a00c8035010304036100c100b5100300400008140a14a10002508451068041d08034182e5107001b4a9205030420030f42d4144420840003146038842c41c4107400040c8161700d1b12619203148a0320200850b0308154490313031000ba401804946851011480000104c041680150402000c000380306e2648100c00da25501c50014000240c07104050544550f000041c0d190b22005400c002e1810b040140041a024140900104010b010641e915030020b13600c0001984a444080e0403500064120182580e048100328000c0d04803142c105e41c400d86071981310300c203582011105802c031400340c0b20109145506 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 716227050 1250 716225800 716225803
    0x1e04090207080a0f020a120302030a0b0d030e0102150105091810060e162f0f01062310050904051305160e010f0b07080d0e1902090609010b0703030b031e0609 69
    0x444c001e1100719400550030300b00081c60644000705e6143c0c82d080141e107985a91040c040070744000e20300781c0d0b04170007007024140515520100b02c0381c443c9001c2c1c0a03140284182100800807910900032150409406000306140c0610325008a4040200a0560b5207010050300c13000141c40d80b0303074003103041c0d29500403d019a136002c008101400caa040d06007000003281d52100c5802002000d11141299182c0450058451401380924a003820084008110700d0f070301ea10700507001c1201039400d01c50409100c02c2405030f5040c10f07180300810341d03107a480311820641c00004000190900a04204000c150403040c1c40005004211080f20008684080c2e040c6a05200c03129100080503489200681104c0a04010030f1710040111224260441c3c2d90070342c3c1e40c441e074400700c4c0507041c0d40000140c10701c640c620009444a190807008482842100e8044440e150481040314014083c00341d540e40b50170030011800028040e50000f580a50040c0a440d1020888000d88400c019140f042d146c45400441c00c00410850 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 716228300 1250 716227050 716227067
    0xd02030a0f120f080f040f11040905100501050604081507050409090f110a060f0503041b080303011e050a0618090c030c110a030203073c051c051e04090207080a 70
    0x301450103480300e1600302c1e52a03450000103840509204851f500031403c1c8400d14141c26803140001c0c0041c80604c0891800795a02c2c000c0340345d0f5001ca00d1a080c00860b00e890400221000c807070264004007941020410740c10040c000180c005402e006007003200050204980c02020361090050b8a081d0784210141050903050300500c4095108980204045c049a508103001000602e048d180880e1240d4451404c2d4100065101c60681c6140c115440001e10000000c02181620788092682004e01c3c4059881f00c5c11100501885034001078005040c000544184050400f540b004030b03188079826580c00906040354104401d05c40004d80303920041d058243c021800700d000912440090440c4202601d00a480b4001d810005040000c0d5120b000c3c0d05064001d415404c1c8202002074000c401520740c1014001d0b10381c9441214140600450005c1c600c84d20307250022383c1c0c2c0041e01c8403841d118cc94808094400d1462943c030702400c1c014013011920044a1001c0c0820f10700c00c001c00380e640d40c50a0f002605c01f91 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 716229550 1250 716228300 716228327
    0x110307150f0320071a0f181203010807170a1505060409020a32150a09090507050301090e0c0a140102030d05040b25050909070309140a06050105011d0d02030a0f12 71
    0x14a040240f02e83c1e980b06d02d1038240e00c10040301c840400326a6840585003482015004135907949004400882d240c0804100300c401c0b40c0c40a000c560300145501c18113a1200a04000034101d003881091000183d501074000d1544900010300000381c071b00311640010340345030041c0c00206071800748c03103842e1602c0c0a2400c0c0050510443c54005031f8040f050030009070082100d000041c0303030381001141241149000b060001e01802c042141401300d8684140002d140707800901c18100ca9900301003452892800c040f80c80c100c2e048000c1e1031005401d04003041488400c0311401281d04620040041000440d20361180501552040003c145513081c407021400603540200c64441e5135842548a13071050941101c11291804011381d480441c0c0d0707440b94020350090100d444c02500d1110a9610308502d01004101d400009200d146c042007145d80381c1004640441d850708481119502e0102c80c0d4202e480c01e003c0113059180300504560b0848283d5030f030012081c3c03010f4400c03508070b035640c40300c54101a048205110b814 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 716230800 1250 716229550 716229593
    0x30609060912121b092d090702151b0f0706060603050702030307110c090c0a0306060e030c0409051608030a03061d01030213060b03090703110307150f032007 69
    0x2000c106410b07801140141c945011000f0b4890800c2139910101c09440b140b804c0240034095001388181d040b1400400340c561621071100c034a001d8007851810781c1e00300d800740c002c0d0f0f401408804400e4000640f9100081d108200604004011141d0000514000c04030480d545898070f0300d40d003492030804155003144d0008010f00d410302c01000b03011540001901d40c40401c61510003c0400c40424060a0042400c503403500008101c080000d0307030300c4010050050405980c5d0801425548804c1100c5282d00c000d540f62389604141140c002d140341035080014614004c0c0103480b0007a1420071300300c102035036641c040b4400340c1011801e03151194040c400e0400a1100c40da905500840350038610084001c1408000d20801e40d80b0301a80c241e0610350300100107000703045182e594070300740a11110303540e9a8900c42102c0c1e400a56030710249604000c50501c045403c0000408009900700070180c1d0505400c1d01c8003403c1650f16040342080c11040b40442d0206d603031200c0c0090b81d6020606100c1260380c13490940d036414 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 716232050 1250 716230800 716230807
    0x15080f0607020d050307090e0c21010b040b0c03040f080607081012120203130308030118091106160c0303091d04020a090f09020402030405030a030507020a0506070c020f030609060912 80
    0x254003c202c042c0806800d1402030381c1c9607a102800d982e4049143c0020f40504007075401c01c403000c00703900700030b20303941d142d984003154003040d034446034401100c0034011480c00c00b074140300401c240d1040c000506846046042602e0410762078121844102d0101d5002c0d82c01a840301090080e002d4009c440a42c00051051110000d182030a079020f1405c51b00391070060128076041f0700d546840b44288195881400b01181842c0034596a041802c0d10360000e0041d0901c1810600000c0c02e00c41451160000003507000c1c07450318203408503404001035a08030310a081819880f42414800240c004056013020314400d031102e95507581089460004403241c081c480c1c0d00c0380c001809110140ea6001004011a20b0b0030501084120b1102140c801a001c2400004d41041c0080203004c10003c2c00f0006d449a6035055600f04200d0ba141da03401c980e1078402ca0005002c0d90081070104102d81d101c1c0807a40c5481d40003501c0a42c100c05404042407030f0080440c0c03881c802e030300880c05009030131030107000480a8810f4090501d08 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 716233300 1250 716232050 716232061
    0x204090f022806082502010c0e0111060109050a020f04091415090f04050705130b0f06091c03030b13020a020d0e0a06031d0a0b0403020709050f0a090302010f15080f06 73
    0x1038502c403a02a000c280502c140000704000c0d1500044114001c01c100402c3c4401ca0032400607010300450018040403d045401001103540701c1d0403101145021500180b82c0d0b45d00e4030f0181001040090040080c541d020050610302034441d6008000604101c100052400c0342441a110302c00c50281881c20000360641990604c0d40d0356005040d0044d010b40305662582d00c951038103c1c90a09207510141e0030048225400604110710340c426403040a042e602d0180c4080d0360760410403103100b80f07000650300c90f10a02d220178403440300c91032a00d800b0b48a8200000c09070b80c50340001d82144440c0c0032041c2202c1e0005100c102043d03041c850340c4050f8100e400d02540000300c060005000c0a00c0d801103c00b0107545941180d410480400749601002d0031a080c0d50901d105402c0c80203040d5401c44090340584a40702c00041c4404e40303841140d1107644400e100c03550740e07181e403985800504a000000c0d0210340d01c0d06200704440c0b6541c441d8092070746015503403c040b140341c000c0c09c50a00702d0f11107000b0401d0300b20104201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 716234550 1250 716233300 716233369
    0x7020a0302011d1f02060108010c051c0e06240f030606010315030206030c04081b0d0f11040e01020306010320090409150c05030106030b030316031202070204090f02 72
    0x400d8a909003403054984460340401d00fa05540761400c1540211107100352035540c1c0c214120403141c821240e0a48030703030b40c1c0c8445040e0700340d442e0b80d00094001003040182c45007010111500c1c08400c0100c030703c0440c1c1c070320702c0d2028907150003c01d441d0845049510368400c9a903a8400705c5103000d1110940c0c14004812071038000a80711480101041d0515485840f070142d2103040801c00009541d0082090383c80c2c2c2000c2d824480c4a801030b000e03c614074483c080603914103201c0700c00d208880b41d5008043c00028401661010540c0d1038500d0111080e03039038019140f10350f640d90300401c066004610001a100d203014030006040d00c14048100420034500c00e43e503452140601d0494006034401d07100800c1181092031f040c4400c414441004078410303e040c241c901c403190700900450480f04560b400780501400881090344a1058101e11030181710310010440c006401440300d813400014643c0c005042500980206064950b0344008492500d08580381c0021882d080018210040800e01c4404003000d0102084 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 716235800 1250 716234550 716234569
    0x117040c030311103e0f0f0c06161e1b021f08101a070b100902160209070e03120702030a0f03030b281a190f140702 51
    0x6000c01c4448101e01e00300003401c0011041c1c0f403600e40030030030034000011704481a090144075441c0d1010318412a030f84422140782d852010702125010f6091900b0340407891000f855200088070041280113002c1708900e582c0034400180310f58820b0500d8142c0c080c0000d0010012a259032142e024600045c000f000c140e03a2280c01203c040e01c018030382080c001d950b80001088801c00c10b05088000e00c003d02c00300149540328030024050740b084501d1b0010030341c41d0100c41d403182e94040c40c1c1e2003031181d0500c61500400d5080104a03044940128108180c1d501e92001c40700b607070f1001810722608614110480c0171070901c0058264080300d58031f403003180c620a160001c0d440d0b440c80e00c2d4590389844042449020740d0360500480c070440b0f92041c2c11046061040c6005000751a00718201442043c0710b260450407540001e0b400ca04503003e07845e900c440d050038a05e0444414501c0480b60b08441020300c11014016400031524078620300603101d8000702c40d21000d005060655004d0031280381c0405100c8100142c6408480 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 716237050 1250 716235800 716235803
    0x6160c0f02040209030d05130602032506140c07030e04150605071707121b051e0f061503070603061a07020609030106180c020703020901030209072105060117040c03 72
    0x44580311921400000e019018582216038140a460a01e040d2250420300800c043c050f0561164625686c504040e030301d074014007500d006070407418801807941c48609070718a040c2c1c6100b5035001460501d03002036294a504202c1d618200c3d1040040e0000915070050554210440c00701c8007884207083c600300074003001441e842024203028020480c070041201c04040000d001000c031010030b4946525082488211000019510118041d0b68002100d80708248400c416150088020850030010840b81000c1b42210815060207000c3c0880310f07590f1010902030280103e00c0c008003141d008007154200b50408115600c65028103103000b400300304458070058140320b50460f440c0460388a04040c0080384a5100341700d0010303071551a00f5004600528034025008454081c034004005108104400f40c0e580e418a0102940c0704803117000400c0107107010038565500405510740040c103410b01c01d6501c850185190090194151510304001d1196070100d00c8010440c040880429103040a45510004404a010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 716238300 1250 716237050 716237063
    0x903320724090507050109090506090624030a0c020f03030405070b16051509012904020f090d03020616090308090111010b03030d02120a0203010b0a03021602090f040506160c 76
    0x1d0101c5a01e804540c0041c41c2041e440303042c80703600c695107000c0b03071164014010107000c034902c0100800d5041003841024803c0401511824407134403840c0400c50317400411040d401008070b445d100d05466184520145010f1b20b0724443c0854a80d402d030f800030741050108900c2d02c1d52540180104008203a0010b02801100d21064800c0c0c1e84001041e5070010910413001c010384180319440024030386501e0b005802d84110340c698003c000c900a001070042503547c00b000880c82c401402000c130301c10b034940f960007089002607250f99a03203803000400100c1d05003112544198050b0f0071040c02c0004400720b1070040c0c03500490324035100c1304440c1556140940d030b0140d55803003410403c800b580c90707101000942c40140809002404c5903100c2e40d0042c0200060b40c45201724030b100380d04080100b40000390500a803816100000100c40c2012032401049000f074000b404461034080c40b04160f8409a10b4000642c0e000e02c2609210042d0303407400341002c92510301c01400d2070000b0703134045807922403c0d60700841d5203098551022 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 716239550 1250 716238300 716238323
    0xd0206040609030201110403050a030e060f1c0b120709050705160b090a06150612020f0a08100509040609030201150509060f011202120712180602160609033207 70
    0x3e00300c1c0140148100e007050440300050210034010005100320f412442582c1d0701142d2045041031110900403051034220648040c05411514540f041e07811030125140c240025840000b14001240040c5c5982d4191158100000601c00f4004500481e6030110305410014a07001200244609032030710100701800120201c8081120200d05102c46420342d904134006200c10030300003d0b6000f5401040c4903407000328200d03207040c4201c1a504d000361007220280688072810f04c018002e081e110b0741d0004100b006c4603104510081900d54907104814017030350092500244600d030a103000b03070860f60803205450004045400420181d42d5104c40da582c800001d032403d110306000500161607407820300320420001d034004154140c02070f5100510901c195040e030b44445600d120050008219042107a214540d01d400f40782c10740100e80180c004040c00000702c2e01d108101c240e10341b80e00f0115140281c086000600349480c111080c04030803c42c0e80740c1c00c0c800b84a02d080320002c0700303074001e14802c802000307284c6111030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 716240800 1250 716239550 716239553
    0x210801031e050c100503090f0c13050601020a12020a0201030506010c0c15020a06091a160219170c0706080108010e07150203070c0e091203010503031b0f0d120b030d0206040609 77
    0x80c4289540b0901c09410700304d0368286a2405040d640084035820810b21504041e480c0046000940100800300501703810950490f040400c8050100180303200e056101c1e80782c1d1080003445602051842e190150702601e00184148001416108043c00c41410441e1361396070403011940c4003105070111041d41c01d00c4101c0b0f10f03410000740d00780b5048c0c0c1d1001c2d1800d460800038a051004510004104403001d001e600c2150b40d92004503c1200d40c0304401d2401a8410a2085100344c168010b52005c40e000b0044050501e915007019402c9a02085507100550080001041070b0f41c0c010442d85d0142c94244024880c600d1450340550303031201c8500c61301d40c80000415501c01d0550003801160040c0b40c010305d600074032644550030010701e018141c1c0d41c0c6034503110b4404074680d00e440c0030042d00e050f030b940100a1403030300b8410041c9070803035400d264410169029180640184080070085644010110b484c0c41e0800b203050341d00c5c10300f02c40128000d68081d8100c004012041036010941a07403050348000300040040c1d46 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 716242050 1250 716240800 716240803
    0x2060a110c12010501030203060c28050f0c1006080f0a02060306040b06071a0705040e01050f01031b020a30050313060c0806030d09031527210801031e05 67
    0x10001581103101107030301c0000c070241900141e058a000f074045446546075500d50041da482081a800110204191150803c03904800e03a0f002f07101880c603103582401d800340c14900c92580081c0c004212a0b01068a0010210603030060744020400c4c100545091003c00043c1c54681d100d81000078411303d000000507600d07582c2d6605c0390b4480300c0050156502c03039202c0d02c1d240d5603013075601c0b04071403401ca20440024040392080c000c88056030810010b20a6a03440c0c0414021b0142c0101c1b52070f0b05042d11035095200c50488020011070091641c1c0c02071420488a0410514003180c00e04102154490f803904404144440f2404110b140b541c0e24285a50b42d445120342421003541d804000e110a0600c010382d0401c541c003280160054408034259109621440803c0d00c42100b5440000d02a0034201c21400f04403010303030f022041d0201140c0403010300000482d030803820705000401c100c42c40f40c440491505101051480c0d428501410309103084154116240c605404040051600c000c941a0b6844070401c08c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 716243300 1250 716242050 716242063
    0xc0a3f0b1809031905130b04050102120c070303030b040207060f0614041b2109110a0b070b07080705070605010b03011502030a05070618060c0c120e0d0605130f0501060e070305010302060a11 83
    0x5221411460494561f268080380368000e106480c01840b5105410310400e0590040301c40323400c00b03000103080841c82d6a405a0141c401202007e40c015420b10522000c80c80c1e5000380c80e20310b5a40e250009000c0d00340300604080002c50203a29000320300c0e002e0315100b05030082c5111889581d00c0d04104001180d00704072440103500034103060130242e0400340f00100300316800c90355008205085410b16601516000051602e0140080246c4a0380749440410501402a51882d810140c2c40c600b083c5802440d86803a0b05562080c1d20411900100000401c0030001010500703a89003c688055840e00300f0f103403401031030f5014820b4017401c00c80d559100c4004001412a1080e0103981c8840c06010a48101601402200d08038005813050301d40c03984107400d5240324090f1826840c000926440c042600c030b4440000401004021031135260f011110040498100c10390548a144100008281d40342040b14080c4500741c00703440c9506050038030b4018401641c031724050354059030392441c10030f22000b010706c0094940728 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 716244550 1250 716243300 716243317
    0x30702370609060f120903091a03011806080714060417061e060307140609040203010312030b150d020724140c0a3f0b1809031905 57
    0x440c000984003103665220010412100d5586461000668030141500c48203410940c0c0e00c0010300d0f02801c0119201035502402806020b4580802c003182c03a0389565a83c007460540d4070001400101c010080991603000703809804125000c24886146003820f0951390b84101c9c0103c140040c8800704458840d00e5040c2610002c1981c0700303000c00c0c82e443c0041c01945400064815090145003851216480e0311130301901d9025210150040c000103241c4045000392042d5070708043d80c00902002000d010f544c540c0050340c084c2d4080e80b0b0104c0460800e040c050103d5880c105014082c1090b0304207901d000c01c0035019211103001014000d0380e0390015151050000301140d21749c0b50200c1000903a0000f4030307120b501040c8080000d032120b540e15110750700110001d00a41c3c0e140000100c0301c8044081070300300803001e01c580c1042c0101c0690841c041e04640d4005010782d4012440c9107540b0460b5a2451808000f1310500512180320384c40903040548541383c0340c1c4505217010003200307080d107103141c2003d00c11030440d180f10 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 716245800 1250 716244550 716244619
    0x30a0f1101020a082203021b0102031917100e0c0c0a1a010f060206060a06180e0103061e05060d02061e04080a060e0706050a0804060f02031501140903030702 69
    0x81402003009000a10b083e100c1d206003464030a0745c15810b1818038102980325401d5002040e601840e00302c0100541e00c51175490741140002d10440c103080c5004000c841c629103490307e030b00d281003100409810700304800419000c0000c10002042000c0c2e600b02018a4100b00c8206003282c0d01d8418078011442e00d440350000400c119040340c55424082801070410303060b250b5044000350f10940d034200c04c070f90302c10058640ca64400380c2c407c0104075044c0500400000d50064100144240350f03030755560446648264400c3d251252070b10705c906030000480c5592441d00c0ca1402c4101701906140c404954030f000f10140003409180001402500400d4618584056031070026403140c1d42e075101c81030302d03455950100007201e990781440d02c10384a4020200c1d01e401910625a04e003402c0a801080807030f8801005481900e40c03d994501d400201841c0e400254800d081182a054851481a000500c0024001c65550034510309000714116940d010041766606a0100c603000708601550b001c00f500b1840a8004d00c080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 716247050 1250 716245800 716245807
    0xc1415130306051e18010b0103270201110709020a0207050a140405150d050109050c030a020d081c06031407060f1b150504050607030b150f0309010902131a0d05030a0f110102 76
    0x1482c1d0f205c0020880e081088009010185010700103400b82d40072902c400410700701c000c3c402c3c01c04a2407090100381c0c413030052504040c01d5003c8900c05050000700e0b0009003203039030001000302c9465010480c08000b0241501c4141c5c07407a00d08030740c074503c1d81541c2c100700340309940f1840422410442e410820042200c01461007420303145518180d80285802d002c00c81c0c2d140202c2e400349000e4503001c501c000303c030707a00070300420406c4a21b6500c0390300c2580708250b00300f04044840c0294540b210759210703080c041c61090041c1c800300300d03078403900360b24215413580031604100b0f21a10400b509a03000003a02d042e14881002c04840940510344400f0481d40c04244071130311481c081c100014084001803041c0030740b045803010402c03121150180100d40b45d41d0920649618810030034492080d8021004540c040341800000a0002da02d40c0064840102040600c402c0e40c0c0303c03014049240c0000803020402d207001c071210200c1c11400d0b41c0e41e40c0c0b0785c080c9101039402d019800503103c0c0254051015071a80d941c80c01d000315036 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 716248300 1250 716247050 716247061
    0x30108030d1406012709090b0f10061b080d230901060e04030c1a071101111303082506150b03061e010c0c1415130306051e 54
    0x603260030051140c0e00c407905261841c9650002c40c21803601804041c1c0d10105084454811010b407009440e1065803c101c3c0e0f074400180d44a0244610101184908140300245c20f04444c901c11000b400751200b081202c45500400084d908020b5190174000d00e030114480c0705006007840d207800e01070110040012410940c9a0724654451445c0c080c0e181002440782450f0340f01d407022a401c0705c074203000f0b40500880310400711340030a000b40c42810100d880707803210980c04881d6202c0c07000c0a090554042c07000c11486460440d0140003801201642280008800d013017240d10600c616000c0110700c409048020001000c046410042e8460b0074200440d070701c680c03464195071034244014030003001c1c3d50310f006144242c040703099140a0b044a0143c600140103007440030100040140c08580000c4140c1440424494031002642901c5a0001810700b820501d01004002c1e0901c07044c00c3d0440c07540f041d128420001b20b407212100646410590390000c0340010b45980f892800d41c1a035141200d21950030441c10100300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 716249550 1250 716248300 716248303
    0x3080d060503010c02070e0c0913360507030204110f041d070518090a0e0d11010615020706080603160b0a12150b0319020a1e170604050403090308030108 67
    0x41103541c02d400030811340001c0b840c01ca850b0760090080c4d51219180002041c5003510300c001400320040b000b40719201d040c1c07096400c4411100c8810b000700b8408803041c051540c0022440c0d038040d45190a07119000b04621643e111902ca0101c2d000081c45075a440d45000a0401a07000b91155003600300f026940e600e071900355408042e8002d00f41090782c4083c45000401540c07140d415540e41c402d4400c0000c3c191050f000c1080107880008100d003140540e18240445001010454040c0c601ca042d190b500328008080a007a095a4043d00400040110007403d260010b40c00202d080889500e40760002c420788481c00001d080408000c034041007409a100003140300411600141070b01100758840d02807459001c4101c02c04d1f501464001c0d20311034a40d4804000d20020303203000f140d2260440c3c032105120001c0703016840498000c1d01c1d0780400211103c03115103440941400d035000c03154032410a200c0813008002043c0106500821a500035500c0f103020408160040c042103020b9981300e0328203030f12581c46002c0c45 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 716250800 1250 716249550 716249561
    0x1809021f0512090a140a15020909070e010c021e1203040b0906071e0305042409090902030114010b0405090f040f020d05160e0702240106180f060f0e01080f07080a0603080d 75
    0x80d50447c900401000c0c0c001c03528403c9605090003d0411f16440d6a806030540e076071900290300c41e0510800d60320400041e5070700701000e20082c03002c1d80440703499040c0390180720204c011810f0443c0254000c120a00c1140c1243e0103541190300106d42050340e803001450074440c291a07401030085a2440e1001c0c4400301030700500584252802d4403070742e0b030007202c04103014041200051250320129211900500c41c048881e00407202c3d2900240011626500351501040c901800343e1113848044000310703043c00b1502d000d04941d5001034203040c50003c1d906007a00c035030510046400c80240b198545460388410400c003802850074202d90003100c41e00c8070b0342d1120283d1517020f04581040060080c003181050b460b4450408000309102c0070500c0200da070070844190340400780c501201817000c03070b10000090b0494512842d50042c24203599207402c031000209020b005003c1241c0b00505101c103100070041c10000215210341e004d6003504e8544115181c5400d00b0009008540000e00000c00016000140c1700458114 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 716252050 1250 716250800 716250803
    0x91309030503160206040c1a0f0f250308130201200705010e0d03020303150f0a080a06050114060306091504020c010b120a0503030a020307091809021f0512090a140a 72
    0x81c519103410503082217840700400c4030001d000c0c1b42d000ba82413185071034400300798003001e40315810079213130190103a4685240d4011500003031001d080007410011078518249080c1101c00e5141c0c01481151a41e5400b8050b214000d042d00360929014812400350387c4507200c0c03102134801c99100c1c031445119001840342c80c2c2900c1d0003001d005c203460380e1000c2c1940c20180c1c10660711a070958061402c507190840304159448031620400d5021260020800503659010055802411500c000303260321a59890b0420540f90141d0020411009940302c1ca0380705e80b1070300100c2c2d40c170200441e8030003690395408544803200010207041640240c40072030500e4015005511091a8403001c07215050324003551140383c0d54480c040c940040503074006002080040015801450f00040c1b00d0506030b035403944869401d40c800c0c42c403102055a0719168643d080540c140700742088841034000302181d0340080100d43c0585140315400540801c1d00760714000950000e01842030b0211213030b002085801c0c5602180c50304d07a03640142e660 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 716253300 1250 716252050 716252071
    0x1020c191505010311211510030812040b130c03030f0918020a020c0f0604050d11040507120b0f2d04050f0f070906020712150e0d030e030405090c091309030503 70
    0x100d0300c0060161900c04c90401c1041b00042c4100d240c50802090410005465200d081c6102c15000c400103001e4400340c1014803210034100745600c1d250030044401c0c0c134045c041e010245449401c11011a40a07226407041c1c03501800d0042401500c0f2004403207000d1075a000010050192888802e1071900f074008205400042d4212844144d60104102c040c0f80b241c000d03641d00c184204420086414980d400c151a203008040040c0401d18210101e000e541e000c881c0d8100082c0388043c02c01700c40c1800e1050308071848095032035011480110340070507038440701440c207400ca10511001400c604030307101c80c2c00403007014054018051130800220401003104140d07040030303800341c840000820752407150050604517041d5600503c001031078024000c004042000341a01d40541807800c2c0440050b0700e01501c459200d150000300305034602480010200d4800c1042c41307030542c00c108020455540da000e0701d00d40180445d404e5a56820400c0000788101b480d0500e00a0090705212540c2c0506030400082d5101e43c80188 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 716254550 1250 716253300 716253319
    0x110f0a03030c1d060304140a050a121b05100506040213030b070e01140412031403100305060c040e0105060906091201060f090507080708101a130801020c191505010311 73
    0x10344208216185201141c12010500019010540304e0700031a00308907401060781c010100a27201c440c00c2a00c0761005450203009101078244e03d507800b0012035400300030240707108142c400c560380b10ba40302e8071100300c0d907840030b40c98802161003a138482d41100e00d04a6103e00c0d5664655407850000d40d5200b0444203407010455030f618208465005143d0000c06144009546d490241401c1111420902c000740680400044c1c100d140245161a4007c6001c1c440c600c5824000600c1d41ca800c070b103001401420404184400c0c0020030441e2507615905054a0302196500c0d182d903190400f00b0454012601b0250b030000100c403104200721819030060703040e1000b80c00400c02c0161507500700010b80d20306903400c07000204071100190030f15120340b20064000f035108a80a14156036440c6514140d050a00303001e8032500e000400c8409241400040700c01000c00710000c0d0f041850f880a801c1d21081511240021510300d44070010411002c0a50b0440c42000324200300706550f141d080001c08407040d0044a030007051040c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 716255800 1250 716254550 716254577
    0x70e1912150c030c09120c0905090606031b01022a040207120f02010216060c0309020307080705120c01080412050708120106020d17130c090e1f0615110f0a03030c 71
    0x2400760880013640d980314900142d10b0031440c10300d01000740c0c4050311685010300300810616010701a06001d5030710707440248024184001054200103408618a1210141074405440d503600820031112440c082c1c0700d510356820140c4843e2554502c1991007a9102c2e00c0007031080101725103010311061f086002e0340d80000d21a907109090303080340301e2000107405000c0e5104c4410005102c0d0b40051000140c18540070400310002ea002c85d02c0e26205410504190f000742e4410301050a02c64a000303c0328078007600409070f03a415900043c3c580c1c100500050000440300f440244800c0c0102d08a60003981e004054656958803042c0c918940384080c0901d00044c014260b0f808502481010b4a00c1c1880d2111404119900e90302c00000040d900d03040200d6240940c03c2c00002c2d4240ea52181c42032034004003019054014810050f4004890008074009038607180ca01c00f400800ca110002005c0d2204500300701c1000d02400700842e02d04480c21400c0f000b10722881b10404109a80f40d0041142c00c00301e078a6002c50301084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 716257050 1250 716255800 716255807
    0x10207030c031407080f091212030106030b06130603090f0f030305011401110606120a1506030317010806070e040612030e1e030316060b03070e01050a060305070e1912150c 75
    0x481e4006172010030b00703106060000803254018028054024400c0b01c14000107060303103003000e5480c018241c66841c003000421001e0b4044c095a4819482180e0b503501d002e0f0015071207028080c1c42d000381c1040590768030000003080000703d0f0410050b5080000d44000301c04910b03009020780800d008440561011085516041d4083c801b03081c42c1c054031038060142a690402482807081c0f0700d821074102881500c4200012801840c1c8000c0d150041d4000400c4840c110304000d00100302c2103c0c00e001721207040c80100300d007020203d1402d421010610305403002402c1d040c0018003170b18190b002001c0c048030751005d0b0820990085611010510195440d440401143d41d4444440d2400c407a90341d0150420842c520510400344062607220f446400002104100308004c285803c01c1ca420442c030344021400180424070307141d07503114004c0c042d40c98180501e24240c000100202c0e110b9219600800d031003606607104038401511480a0b00e642100414445202d040050740d200545003000482490721140e0b80d0980d20 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 716258300 1250 716257050 716257057
    0x60b18040206070b070e04020a0504092f0f19211503140a1b03060e010507050715060b211f05100e0a030305070b09010603031e020708010207030c0314 66
    0x20000c01003403c0540b2901c1d50161a20020049410400400d45015407680c035840075058180303140e03481c2a2945d081c00c02e941c04448400e07003001c4081460b0004107075149200402c10364121079003c076180e00c45035003544488080c003e4036000c41c2d283c200d890176030f10180d50040da410a011006a03c0d03d032110f00343c580c1c56049503200410205c6404681d00c050000c41d41e0b00903048400d60460f07013191840c0416846480c804401c125003a04201815035040051204034001e02103062000402000305082c1410082e28030b20443c6001040150080d80b5511044416132041d0010903400b5031003030345ca4008100e05003200710389404c078412030b02e001004540646041c103144020315907420300c00c1e2007a038284000c0102000001140d0010041d403490071626949405000e000150b100b92a01038039042680b410340c0071000000e203c264980e241000030000b1a600c42d4084407214400d0610340c0740b00b009200102d09142031034020011540c000107110080680c803170b0350125240c4c000c6c0d540c45030031981401400020710 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 716259550 1250 716258300 716258303
    0x4050a1715012117070b0907150203040905190e010b040e030316050c070f12140c0f150705012a0507170a09080d0201140109060506040e10030f060b1804 67
    0x50452401400441c04034120901409004403484e401c000d4451003105602c401c01c103c038014090070510000c184200141d0002d4880702800304040b440f00f040c0291703280a54403e0550190f1a0300c041606401800c9010000300c0748040e091000c03200d201079481c06403640340c600c0c50040e0729100c940d542051003c000d036405403440740c5580300001c51003141120306401c48030310002ca40c002c450002513414a4400f000c401072940c3c03613940b19588141d00308071159441410301d020b683c1d00100079400c0c00346e4854206201c012401c0780c49800c410b00b0f1084030485c034042c201c40185291701e000054440003241e080001000e113200f020750328001f206c613030086815000e060f600500000f4500f03190000009410301400e10314111785801202c4a940741d0765280707006142194100545d56270b80400b1400102c00112030701504070321109000091500003c9940e0744a20300c13480406908990120782d11070002583d40c40115004030780340c5284051814000000c00c48081d640d841400307014955448640e65455807441207 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 716260800 1250 716259550 716259569
    0x70b0f060f01080a0b151b2802010c24050105030c0a050a1202030a080a05070510060612020d020d0608160602070e0c0a022a09010b0403020603011a04050a171501 71
    0x507158402000d005d00503d007075561780004101c404d004402c1181c0040c10708a42d6024580b441a20282400390400c03071078025013582c81c15509092400300158009a5510944c28a00b14207102160700700342c000700300e051111030500c080070a05003403002c003590803481c141d82c02281901d000c0c015050400510380303050711455800c041e40070010002c448a14512003600360028060390701d044003943d20b2440b10303400800c0c5200480d4010400342c0078090308011004002240b46001c01400d804d1404c041d007040f88204075030101030740018014000b69890303016140c5500780e244042c00615255148107803208582840b4002070514180002007481c80003444008507038031010300d5003c5440c0d87c10280f005502c42c801e00410b501ca00350a1680c0e10703490914040a500040f0307843d100b845100c504004402206a00c502ca88020a00061000d070f074400301101c1c1141d9810b07001c0070104516071501303190360003540e208583c00140c040001841c41c0c3d0b000001c080342400036058410341c0800081c0c00d00e4101c5c00380900301c110f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 716262050 1250 716260800 716260817
    0x509071e03050c01080405010b030312071d1e0f0319050f0607080c0d0b0904031e0c051e071d18031e090102030f040311010311120601030902010c08070b0f060f01 71
    0x10f6500030307018690041c0c000d1002184800d10b400100385150301403a580c10400c54a803080082c1c9603800740d15620409072003900700b05121981c1c0000b54400341d08020f62503c0074140b828044141e0f03a0301c201085845000740a0302e2800000b8060107021004040c0292a14020742c11400c10035100840e40c81c1c032441d505d40303800f8020381390b501e0303040c0f540d401144c00e82c5600e80d83d0740d0780b41d2810341e50512014030452295171211b06410315914400c5514490350308400a000c202c42050000540c0424401c10042540b00c0740c54080148003242441c2c110150320001c00e0708441c5404001000c24503181d288a041c82140d0007c3c0d4002d001c14140d0b0b81d02c542c052050201190058501352000c403200104950041481240c1c204a030070b002050320742d17206500803219044202c0043c2540c1d40c05000340080602000062414007011001c0101406801040d141c1055503685545085a0084c0300d01450307140c210b004c540d20344456180c0f42d445140242c400c95884e94240000075036500c1c00383d4001001d0300042c7d603070052 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 716263300 1250 716262050 716262073
    0x50f090a080708040905090f240c030406060f0e060307050109061b14070920130b0c0a080c0609060c16060209120109051b0d020d240509071e0305 64
    0x20315402c40041112100380411002518440034002e260081e81104054480c6541454066180c5855840504d09858004c20f01c0c01c200c000460056511124640116550780e407245850301c000e103001d0300a02c1c02269103100104602421280326442820180d0403160781548034001950480102d21071000002e0a44480d11905141c0d440b00207a003d102e105005002015081c5481c01c0c944ca94101d01c20945c2d131070200c85424560181e50000d080401e4459900d050303070b058186251b88002e401900005e01000503c150944020001c15514540004066807107030b07030000407035468401c04e40d491300c014851f04010440700543d0100f107a04050b032540345030541c1541c0360360310406904000c1a45034025414002e441e401c40d028019010620701c19000307000710301680c42c1903045070946580d44902400e210038801c80141c80e195482e80d80c041d0040700518120700e4a0003156507040710094441c1109003800140070303069030001042c0c800c0e00c8103200400e41c00c5581a0085c034154000f8800685540e001340720028 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 716264550 1250 716263300 716263313
    0x290403120b090702030d050121031b050706080603060928210503011d01060905010c0219091e020906041703040b070302030310080f101508060118050f090a 68
    0x8a28040860010400107003803800181208401c951003005a04001405075181c5040c0c80340303501602d802303500e102a40c1101c1c506440b01d900403607802010310005c060446410b16010710b082c01c80c59440700031600d0042c0c80740340c01032601505640b8540070b4816440855030311078003c00e402c880001c0717405d05a02c541146c0c400e00d4141003e107000a566400c14421030340121016600304070651080754135919030380d52600ea050144840741420415440781e58000500c081984201403004480c024601b080010401c0d00006052410240b0200d0300c080756610b00094201c00da80110004540c0c9070910785000030308030f1032102a8851680e840340d0160341003005004102060321018035505d50007049900300707903e44006100e0303544082000d402590000c001c20840d104060650006030041d10301401054140c0c401c0d19a450101c003061030300d0552110840c40f206d6003c00f00070402440c0b6401120515652140b15040003002d030200340c0581410040000c1c48a00400070190203120f01d280204034440281d201d85 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 716265800 1250 716264550 716264567
    0xa0f02130207050f01020c0f060115230309150714030105130e0303090714060c030a03111908041e0209130f08041e0e100902030907050a080604290403 66
    0x40303164950034824500402c404101001d648111080010380d5103070300503900e525094640308c8451255020344010301010004240f034561403480ca040c10440b003501401c0d100761407620302e403010900000c00300812002050000714103c059424010740d940e1078842000c1161100705802d040c00c3c100f141000104524100200890f04080d00b0150009400d503151101d181164001da400c840907501001d400d0000b07159900725520482401c07070b0030515142c0e4070b42d0000c0e101d004680d054010b0565503114100146c801e90308540c0607a80303250510341800c26030400035158145c1030720203840d00c10003060401e142030342c01100d00345071640052800e44d650b500c510f161010800011401c45c0c4280c403402081300010402c0000e84041c01c00c8a070700520241c0380c24a019140f4200347d000301c0642070410180140d10042d071621300c05481a40c40c0c0546da0786e4801003198604001030713002c590000c2d60f061001858400104201c0d001d1481001c40e4070002042000300c10541e08003446a00141d4400800f080001c3e01401a4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 716267050 1250 716265800 716265829
    0x81308180303031e061815010c230f03031b0a02151303020c030c06091917010204050a06090308030105090711010501080d171e2e0501030b030a0f02 65
    0x2106520341820010a045810a603140c83e10414481011450078584011181e80b005d02900c800d50200507200e1407840d202e00107044090343c504616000341d2980d10521049546075003107900108a650200c8010101240e044100c1d480b90084103007048081c03e0110407a40544601c420321400c10710401c01c0e41c03003180d011782d0782542503203c0c25040c65401024174082030b01c99465400c3c654000700d15410040e042c01105581c0310311a030040044103596945030020358015110aa444030341e0300115031803204c50500550050401c0c0c0c1310b9501c54016903001500240141c80d82600c0500e44a07030380b884180e5080086000c000e162803c244010300c420b0805000d882d0707008042e0700c0d0580d5811150b440381402c440080c6c114242d540c21400c1040c0100d5042808400d000d140c00e40c0300d42852404400d01c1c40f10044125100e143c104840c0302103401009100111003102d805900ca00c84005404140c0c119610404e01c1154003090600244600030700e0049250b4040c41d4000821000a41c419030030400781e00808081c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 716268300 1250 716267050 716267077
    0x122208030714160f0e060117010b0307051e04052b17040302060d0507030b060705190206280e04090818061b07050906030307030210151203020607080106081308 70
    0x241c80303c000d0b800041c0c0c4001c000359030105162600344145545124001020b06041c02605101014410b0340c0c800001d044501920110b91292966202220703980700e000f802136103048445030101c0e0365110030070050040312021540705640c210116110b14a400150081d28104100c1da6a05008948440003155010041d01041803500d0b032a580010325a81200e015000c5842da26010030a9094140c4580e80d108a0129202814050307a035417242c1d9a4185100ea52107440d20401c02d030400c40d112002a24851200350514202c07840070010461242d024201c0301e440061070300c500710b4442e818288503202415800000d400d203007100100700d1007000880d10601a42103c0100020090305a01c1c42c004400e030380c0408043c02e810391a081c1000690b8902804261103600f040100b034000030740000c0d103151451404600816040740c00c07468070a042d03441f80d101c0300080c0818010f6500309035000c503603030b880781c0215103c0c40ca4590722800111500101105c0c40e603003a1280300081030100300c4000c050720340ea401201 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 716269550 1250 716268300 716268313
    0x70c0303060f1503060603180219030c1211010c1a06010210151404060803030609100803130e0907062127050d110c040e010b03122208030714 62
    0x8080c0714030115542c3c00289030b403221156807071101d903244c00b4510007068203250a110f518039491000b844804c2120f4000d12074140c810384803458031040702600000356084401c5201d43d0303030b4402d064000400c4141d02164994400c10014010358051821080840d030000a03420300000a030016000c09480500018158811280500d0503140c1d140100c41004101d0b0f03100c62503680c0b4150b60300c442a00d2403480c00e032003542007003420f01503142c0010580c0e500003012681c5800c19100c084e0107048480498002014601000407021010045601550704030390545c0108200d40d038642032450707210341d800c0c060140090f602c4140e008508080e03041d0b00a030b5030b92203140042c091140314504500841c1c00c0c840c2100440c0c44d41c85030002c5c400306200311f421408803070406070040101c1004250300c1c0c032000c4076554401e40c1d44210740c0041c49000d6200f80003014001d812a142d0a140388034180c055040101c40c403417840640507444141000d002c1d450300480318458002c505283c103966034001c00241200801109204d540d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 716270800 1250 716269550 716269559
    0x5090a090f06022d070b0606040b07051b060c0d030b030c04020304050106080607020604050309011b0503071b120309050409081207080603070902030c0901110102040914060306071403070c030306 85
    0x4008407060611542d8010b07607a20f240c3d500b42d40c01c8801d1001c4078a4240e01102540c0301c11007000121008030340c1c0100c1002d110340e140c80000d0000d0149810100102c540450300c0d1081090005144408562420b14002d441c00c500e010041288150044c0c43e20030b42241c400010014040d81040c03104220050507035645010000107e03003240c00817030301540c45a45901080190078024071040b44c0010941c03001c3c10301894141ca402d5528400c0c80000d40c10001011041280701c08000b0b1000800c81e440010740765500300c54106603600502e00c5040350010700c1349400010f50003c03031a0b000d8581560540314105200e2510003003200501752210180c0f181c4d40204150200c0c450031403000b511440c10780d00d80407501d0421905042c506091908652611403040040c00f040f2003181c410366401c4a02440c0c10460158984a054060301031544a544070505202c00c2c8030013040c0e0840502e2043d403040d01100c07500d942da0790b0111031921010001804d0000104041a4071610900030140484e00030f08010920390f989 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 716272050 1250 716270800 716270813
    0x20f12060a1d1504022802210c0105160f05091f080a24030212070911090f03010908030408130305100209132705100527030f030105090a09 61
    0x10355214032500b0704500308000c00b59800c00008805018290380850404074244280566400c61440c104600a0060f42ca224018802c2011020715a0010b150080e0030b4508895404660040450301040d9420b1500007217880d04181c600e050100031550740c21503111f0400d01c082d6907543c0224401c070b030850440e6146002d4203502d81c0c00680181c0076552a0700e6a46484806d500c100e50a41c5554000c007d000c9084041c4503540b5000242a240c0407224424802000c441862400d000780d0b101010081c1040310070100309a52501070201d494003a582030108610f1142050f00305c43c817501000300424407c0c404600411544406842035800940e80400925143e4542c0d0749411114204401401c0d0002880d08480c10003c504030400340c0d105070140010a152841544e2050203500441c007486400459801405401c00c03074a2500b4240000030801410306e410140c41054198241c00c0c40103034030040d620805440002200c0304400700020150a517401c103000c01540a1010708041352141e22a03080030041001e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 716273300 1250 716272050 716272079
    0x80f0c1504120f2003070b0f01050f0105090402130e01061b150b01140f040614090f220e070807060801080c01120902030303100f05060f030408130321080a020f12060a 73
    0x850000e54035122140340c21f0f044048002c00302c5940081d81c0004109981b140d241803c02d1010900f0320603242c4080e48042002400750712200360107483d40040000d0302002d44841141071703038241d68504c0c41e9095415a040c0140701414001003018006403070b010716030012540b001d102d4800c1490800704d106840c8480c03030b81d10740007040008034203200010f0402000e03400c848903003c5c1c0103600001e03a04009105002503010024081502d000c5e135a05414400310310f40320703108060790318842d02040001c10441c1092903550002400781031268840c044022030454000c0c080349040320301000c0181a040028801181e40e55404602c40450380d403210184c0c00140c0c0d00b400130b14407540684400c1d60b002d505d08502c80603004421f034403a07400355104114400704014400212948540c000d442166100c044e86001e141401c416440642403146a0707080e4124007410303a070030740c4180c4030079924010310342ca540301030303800b24410002640c908000070015104030f8100b915403030b68031480007800560703502d66034010f0540146 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 716274550 1250 716273300 716273357
    0x100e0403050319090f2a0f0e060301060807060c0602071203050402310203100f03080a08150603070c141b01020106120308060607080403080f0c1504120f 67
    0x1e4002c0108001c2e10411100340f2011085103400307112035820ba4542c0390f00702c00320722805000b905100082a5030307100941c0c02034640b00204071405050075651002c164544807980079055610040c000403441c986414041c10058503800ca01508032140b42c2041176030062038131102165415000d007c540b0103e8000380da4403010326050344002c90240303042d20400440d031281810300d03220700d180d42049a6111b02401e4008440010902e001a503a4031483c1301c501c40c6419950018901180c800c0c804402c20280c240940448030140e01d56030701c2600c4680340540c0c8019282c000c00d41150050000650b070302d2045107844680350017080325071100e4444a0001c0c0c24280c0071800c101411100c40e021000b0340d607091041000900e2003c02e11a50f4207841d907001450500090400e40c807600000c6050001c0c0010135044900450b070240b400e031b6440004009042d003c1c4c0103003003400424019807498120344007420192502c903591240740d000c100c4901c00f00540c3c1100b088044c543c200b0881d0340003281c4c40780b81c080c10100b104 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 716275800 1250 716274550 716274557
    0x26040c06020606150d020708120a09020109080705030d0e060d0507020c0a23010e131509050a0207030e1e0303040308180a060e0d03120f1a0f0604030605100e0403 71
    0x80c204040a0725254003d0402c5006031401042c5107a40b01e01c400549084902d141400760390398a850a100e5070074042e02084420051524051022a02c1d02d5804004c11034401c3c0c845a030180c7d0354100503038842e000f40c4256038040d0030141148024507c02c40170a1400f00d03000b4805414490ba072042d11003100c108a4505000d070f400721a03400054079055484100800495070500f686503541c410314001c980c1032907110b905104442285160076543c2e04040314040c85120810400c00c080e07201c2300a5503006520400b46224a44808a1034803550303402103503c0d080d007684170022181e26a1040c0420b84624130100115900000071107030040ea002d2004100460081c00d403180c5a1814001012154280322032151003002078040421110781c000c0703e01c40202d0f01c101c400d101e2422181c00c0035103425440103803030b010162800c4048940e01413164401c101c803464046d4004601c00b00702040c0428801201c003959841901804204001881900704960203c2c210007104009699101b20102130703241528200c011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 716277050 1250 716275800 716275823
    0xc28060c05280e030a020f091038040509130204020d020c0606120f0613061b320d05061203070308070e01080103020d2003160504050c040e072604 64
    0xb0590144031406034032800c9010304042101503002070500c0c6020640c160080d0450070000b240014501c0150005001100c0031400107035252410b441e40100010501a0300da100c000d004000c41c0c0385105a8003940c00140240c8200d803030f01e4203140d020704d40031002280e03c00d40070404460590100c0c00034000c4401e078040100b4680c20900100104004c02c1c10021686ea0b11110708280c40310340c0003843c0c6811503400e803090201840706050410140a40084807007858a0900781c2e148055400400d0388200c04055004402440824500700c04e03071400340d500072000380c00030b004510403403015038026501b103200202403450725009001c0305030554001d0402500841c0c010307810070810399040044018405402d2800710130960469000942c01a8050030180540607050304c4001104420071600000010040499103050448000182080d1103805440e0007a424840404c003c82d01042c251016911055882032181e80c0740d8000f2209038180302e1035020700071074100e50460034201015800b0300071401401c003a0322 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 716278300 1250 716277050 716277127
    0x914100209090c0c07060804060f15050103050702010c052a0a0804030203060108010621050a0b010f090c0c050c0906060d020c060a111602090603120408030c28060c05 73
    0x250b1280241442040141045021003081c0049055410f0351840c7c2000b809a4489040c410014400c49805e5030242e07250003c1c00113030380e0079224140202d0320241c1e0b06014503900d66004900741d621086125004c03400a00144c00004400c50042c3c0b40c8002c81c1905030b101640310041c651403c2c4031101d0035280000001010702c25410103005840c058000f400c000e01c000780c54807442440c118000001d1002164000203014204030301400300006580c0c1010098020b0358541074510b2800d1800d1040052003840c0c9620300600c14003402281d801560040082e00e00040c0e524103000001c2e000900040d8041010401081440814806001c03896255402401d251a05001c07074811101d680944413007141c0b0a2029080e0036200c20800326180d941030711003070150713290840800c2c035250070301c2c07190400c17281e01180214580000001420b44030200008076001403116621186085c5441c1240c954100c110071007a00105081b50410003101a6a141c00380c900308603002c14001c2500482945001c251030070640340d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 716279550 1250 716278300 716278309
    0x6010315031412030a022a0706050d022a010f0c080105040c03060b0304030302040f06090b07060e010b210615180903070f0503030702060a0501050609090402120d11060901110d0914100209 82
    0x448002001d210345c0d812041c62070100355184409d224000070420005036151032400d15070107a030440348100c4140300760a405802c3c5004c000e6500400e0904035840e01d075890b14203004078021115886c00036103a00b0116400d100901001d800750b40b03044814152114400100c01110301c00a41c40f880c0240e8005032100d05200d40c81e4800e5501c2e074025410844868414044c1c00c401d0011607107503d41c001740020340982030201e001d01401140d101d143c1e10454801e940b000000003084041c0a00071200240c41e5140d980c06800e103880402c94113500e0300650602d132400c541c1001e0590094200000c541140d043c04015500c59038200361181e403c4506030000f100784211940c040055070740010701e0110038486581482e01144140c014a20014400d032640e00100d001d54070b0f0840880c144024503001c0e07462148006d80007a00c8210040102d0849120b1200029000300c1c0603c01c04450042d09258603291801d1500144090702c040c54058a58010302c0000100b0320004001c2c1c0c01017205071075001f5894401c0c650410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 716280800 1250 716279550 716279587
    0x902042702091503250804061a062d3001080d080403030b030a120e0f010203251a10060f08060d051f150902071101180305030f0d0506010315031412030a02 68
    0x641b180f001084224030740d40e100251054800b44c041440b0305010000e1200e80c040242f88440e000384840000c0c5140040100e030741c0007e5030b09040ba0307141c00d401040d1099126030324091243d21059082415210040380c441c2104075002406840c3c0810b07690700d074200090400014150450352084000000507400b6007024441500c0001141c6500714000700d43d0000c3e45a102d40310f026210260b2698100700c00302e050358500100c1513044040840c000301c405018091024043c3c2d00ca4941448100e0001820703072180003030b042902c0322540e0b144455240c45087c0000401c0e000d0080760030303000f001022402100c0c0304010203a550809240451006141c185500082c5456001306080e140108030718408500c0100302444400c40a20780a180005171011058a5071040e400003041d60000085000e42c5084403405801181c400f020208403545234140158210f80700391700c400750440d850340300c100b004c10b180306600c150070101e010541c3c415025400548a079948216145a04c2d26404965100e0115070100308 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 716282050 1250 716280800 716280821
    0x1020409050f09060f1b13080a1b12060207080702040509072120011407060207120c050a0201080411040213030b0a050c0d02030c04090204270209150325080406 70
    0x90901418841d03070151140b08021b20400c95500106000203942414400311400040030140c001060358507200d1058450aa40d08203580c0c49019401c44480c1c054000543d008450200f0950304280c42540d844c0340c06900b2400080c1c3d0310b99014000c60300581c40724080c041c800d01c50440901013440c00e12480040d407890855001c10f45001c0b0004680c000b5043c002c2024400324481300c0c010007030940b100102c49102481d0007004080f60003081c41070400000741c0140076058440d003048891162014811a6000e81c0d40c48041c25980c086c0140e10055409030301c81d00c2d0024003c000b0140c0240003100460140d03400301da020306c00d002d6a10820000e100480356016000b42c40d0407001d108504119805004c140140100d141c007499001010541c6034101208071001414400000d44d11140d90b010b820322075550a051200c41541020b4155100100c28400c40d807018400030301c1c0142010340b41031303442c400f5000101a0050002a0105949170300006030b02c0074031030030040da91643c542c6002c1c80c0000c00d403843d420b80c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 716283300 1250 716282050 716282053
    0x2030c03091516030f091e03020d140a030506031e0c12030f1e160b15040903050a0c0c0504050906070f1d010507230102091e0a090e030c01020409050f09 67
    0x240079511940d003041c01c90307041ca00d04d40840c3e0350710300300703680c000400c00303030400401030420000c034202c000c4030116658080601a4090f01d1171155034000c250b50441c002c01022040782c0301003220101a40c040e5000a03081030001d02203500540a000d4090a60400403086407a42d50000c40c460519151018128044451400195080000d403a4100c41c080c00382d140e81d00c090074001c2c298613000c0c1181c8e1040e1000301c031007010051112240790824500d18501a074100340d800da4600104403042c01c00c1c5c040c03403c4c0c80d98150b03611803800550354402c54254203040000c8070240394080d00050705569178011140603690020182c0300c0c900300000f01800c0c0d502c13065110410704c610070a00d0b09103990416581d019052082c02e04a5560901e444d0001070300000d20a000c2c208450543c4040c110b1105502400c8a03103010750301c82400002c81441208600500880f080d40804098000e0114209035084001d24014404c100c0c2d08007038132850907a0990b0090742103c5036190b41c89003041100c04040303810300d801804100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 716284550 1250 716283300 716283343
    0x50f0f0c0a08150c0a020a0605040f020a170703062f0327030d051302040e06090d2c030c031009031d06031501021e0a0510050c07121202030c0309 64
    0x544202c03681c04000d0402c131102601013010402c1034000c0c0800d803016a481001048a454a031812020080740400242d00941018070007041041c40e244a020170422900002c1c8803003440d50360761802420310b0503128032100c0f2049030240e141c120341c050f4142c00100080b280303948070315020095980c000401a035a54071030119106507500c500c1c001c0122035a0f4031241e031000c01c1236030700d0080e0150780c2d01c086400250441c1c034103d040054410003042c4103008102038010f82c1c80ca2480700b50100c4504810550303442c40c3c0c1c078800002e040181c3c4042900020128041c059032007115009001a00300f0303da001c540807400e0385514600c010140e1103d9120a5001079100300c01c4007000c0c41000c5803441c003005252285002030400c3c4c0312540d038000c00c0a151010a41403003400807481c401c0003e900c514241508564911400c00d000d00d102c445805624459100b01c40054241042500d0351200762030a0800c020512440b0702440d041420180001c6114080301c12202d0390741d08290010178075066210035155413890003603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 716285800 1250 716284550 716284573
    0x21e030402060a0c0303020f0c010c03050135070504050103080406030513030e06070c030c06271202060a14040e07020c0907021905010209100824011b050f0f0c0a08 72
    0x284183d442c403101c149080f04001d0b0386450207800a10811448803403210001c1b6041d0094001500300e60680d0f001c5590611059a80340c15121042c81e4601d005240300c0031032103110201031826040383c0320404600080b920556a64408034003101c1081c0c1090341e1001002605000070383e050700a0f960040885030050041940b0340e2401481c0b07884100b90984039100000b10101805003152042c009550080c082006541ea0745030054600b80c401400c007510800100050080350306040c01004c12105032600300c40c041d82e103903801c00c8110741c04050b0403014001d00c54440e00c01c44101401400140c14185000f032250704059038064940050310084501c00c8036650200241103138003048040c0d207a811000b800c4403400291401d079000e401089541e5070823141a2800e400601d50081c5504c1c0502c802855455020101c00d0480140320070060840b8041002508040c1d034442c0d4822042c0b0312130f40940d081d40c2d40040c0842c13005080c089800405061030780103d07000f441c41c2ca0201c0c040c4000b07000e400c0082000c1d00f4075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 716287050 1250 716285800 716285809
    0x10b040605040312031e0e01150b09060c030d05041113051009020f09132307080c03042f1207051e040b0a0f03120914090a0b060d021e030402 62
    0x1da01005103000708030140c04c02d406000781c02c400240c040102d082071189031400281c4c0024005205802515800e0150710720328000145040707003e9400b10908c492030600e140050110f5580001c026600501c800c200410241890344102e600461150f048001c081e83c0003020011f16084900c0803107902031400d000c4c0b02e585a0880303d040c2c00c90b084d824015031a600c558801603458011114420f80100c2e02e0f1000c00e400130381c50391020b8069158ec082111464142010940003c10102c0709000801e04c00004540030200b844081c41e889403090307a1007008400044a501440086c0c0074048510300d050340e40c030796050310341016042200c3c481c0400038881d442c6040c00158a1129815480c214070648102660907600c0310703008110000d402400e294400307650b03540d41d030744414030610041e20850300d0501c0a900c07079842044084c080301e2000607100107103808001041070400c00600041511560349500e04541d44030b500107409044045540140c5548018000b86500f125480320b2558000c410400c000041c4d44 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 716288300 1250 716287050 716287057
    0x10b040209100c0c0801020a020c0301050a0b010207121e030806011103130e0a020705060c070303110403031713020907021509010b0306180f1605040c0f0909020a0521070206010b040605 81
    0x2c6032900004032002c07400d0200640007160882c82d401c0d400061000c00d001c1d00000d8401c500c0c0c0003640204490750b203c0c0c2e603172000c555607017015500503001820b0400000c8201400070100038001c480e01c2c8076503400300261803011842c0380e408401091226082040d1580c1042d40848a0301089020718505102c040c881003256445020342400b0088450101c0c0c0c02040a50644070129446001c4070300c60b0500300303006c244a8110020803000642805405920b1440440c182c40441e503242d11071450404240b0104405440300900040c0941c0e4050207a0b8003503070700c2210040c0112082d8010f000a0141403d080600100007032420080707030704164683c5415100041d1161340300c0c002461311000790f000305c0c0e0028141420010401c070140304407a888003000c0c0302914040103c660440f401c0100310b125000c191407240c800d09103140415903904082050b80166001000d0b08041460000d05d085044010544a17036070392700351502415010000c0104403a01008500c2c050a1400c511908092820714014080e21 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 716289550 1250 716288300 716288329
    0x204050f19020c160806091903080705030c160c0914040c0302060f070c03030923030703020f0604090906021e1e0a200105090705121c210509010b040209 67
    0x142d00140d00031070340506021402d68003080c480c08000a503999a10310b960707064140c4280842c0d0044d004045014903280e9001484283d00d40c803451241e54904105640c103800040c180e00001804000012071030f409810550507980c4284655030f01141003031801800c44001c49482c407503c01c2e0500c140004100000981c0080f698111100c3d03507108124440709d0618050641c009080d082e070300d400442095005010318041e59544038a482511400030240011000106d0b03640d0b8164001c940c0600160800480c0031402d07000140810740b0f8569540d80c5541150310b0b4060540d6825070105040b5a1480007031407c0324810139000629040c01daa0f41b100c08640d02c007036401c0d08141180082e80c010482e001c2c0c142c0701500e80010103526441c2c101c20400314060401140c07009614051008045103516050002c0c0054100c0319006080d5403d041c800c080a101030505603605100703946800702e041a040c03842200c1e030350340444c2c4e0114003030030251882d6082d200c2c980c078041d108600610040b801c03510b40e00d0244002c038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 716290800 1250 716289550 716289601
    0x1030c0206132102010e1506180901020417030403120201020316030b13020304030f02012a030e010222030b0f040201050319090803130c0e011203050c0c18040204050f 73
    0x5100c43d00d03121407464860f89941c40c4400300b09108078001e94040d805101d0080f40b50046c1c80708603451031444c8010f2602120ba0350b6103c440502c603582e040e240001400e512094800005140a0716400c0450380c40c1580d81612082c0c0c0c0c400501842080300c4d0304c411106e03022003030009508500b0038407942d130061000360143c2c10130959100e00e003004c595604040060501d01c554000c541c0c9090500700100310110035111480590b0030854465205003040084425900f0080302c4000400c0b10100b04034041c00700540003204543d000d11200044c4000c0c230051200d00c0d000c040e080041d903895803903e080702031001054920041d017144100300250741c1200840b68400c40b00045011502d4100312490010940310a0103000e02c600401041949031310410203400c0d0301c0c000d0b180d5161081d551052420f0000c2d09000b09016034045080312030000380600040e00e40000c9441c252443c800062002c5403e080310744400c901079840c001c05020035414188110b0741c0013500c00010710200d00d040c5024ec0b90805825626004a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 716292050 1250 716290800 716290831
    0x70507050a0306020414090403090603020d060e011e0e0708270d082a0d02091206070c0c060c0302070b0307090506070503070309080d080f070504030203150f0601030c0206 75
    0x40100500145018000062840211036100d081ca20000e4020340181502c08080d080212a145000b00d8801c0c410b55040c0c1d16481c04505005044020f03400c80030310304624a4a03500085035207401040800c0c080c12126640c58290640140c4000c0003d049034081d501001c4c1040034841c219500c881c43d540d000c804901c100301460b0341d060b07031601810001d4556440a003d000481001e5a0f81310b60400c1c0110651000f4080c0075024440300d4000081001c00101c080f40100a07652160810381c0140c0803150700181714024040444031018100700040382d80e6400122103810356001c000080c0212400b0342503d141410017070301030f5a000b950303508013405503503640341010001a01d41c42c815891340f0081c050143c0b50315100c5600d49850741e0780341c1042c80700f1400708030301c02004a0784400008007c0c29075070280d5100081503c40c2046811a2400500118200541000003101680b020403108040180340c0102060a203410800094000c0c3d000e0141070400d070404500079600b5a00107000350b082044410076004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 716293300 1250 716292050 716292053
    0x207050114040b030a1b05090109090f020f030a09150b0d1704050310061508100b0307120509030a110c10030509070317040f0b1e030a0f0e0f1905030f07 67
    0x7070a000710392200840280c00030810042c243c560f0007842c84942e0000b1a815074140304032040e5001c0c080c021140c0e00091218100700a43c2c4a6030308110b2406110300d03c014684261520342d801d0541c811170f0408903040c0c907000e2500030000da02140309101844807070100651a032100000b0745070440b41001411a5100e010306044080a001c1114000c0030001c0071a00d0b243c984048c0c41d0090255803003a02c404a8510b08100c40c0c460184180503c601611040088081c4c2010181a26030700068448000c10040c60007a0700314008501c1900d000d04d0101004603140c41400b41d008003000b9200031106415040303a008505c45807541310701800391020905010601d6500c40b10f1062500d000c0382d201418400010782c3c00d84d400c800c0140100191070096110440e107a0701c0b403004445501c110071014000c82c40d03940d0460140b40101001e10340280e041c0c0f001046901030010f07030006407200c0030211f01340c50300146409007114104014400106d885000a5603643c80c40ea01c805807a40a000c0d0000c41c1d020001482e9030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 716294550 1250 716293300 716293337
    0xa09240c02121603020a080303060d080c0a020a0927032001140f07121107020d0614010f05010e0f0d060b190602010516021c031104091a010e1002070501 67
    0x10905411022200b070f0302c0e006060031040d11610710007a030180100b883c004c00c4107400881140d00c1904041c02c41e002c160440d59840c0107036844900e80c0c1c9228040e1101c030400694030a107d040051035615000300d40e56558030324180c002400003a5900c00108407031681e100090f0040004040e0010307806801c4510381074110324601601160040f54a1420301604001c00064040300017405140b0542c0c824995a501a040c0c40c00c07100d080840030341c400c1c1d0602010740140f8000002c5c510542c4034070004a4031315800c58a8112019003a0015010742d0102d18041c002035905c113401200700700e02201c80d00c01058440021900d900080003018140c04c0d164581100309459100e078014084100b44800b40c503884d0754540084c001d200a441f0481c0c410800340e45054030601c002403801d54684400703010019079034500c0041d00140603c0c01c146200c03407000d000001c0c8203100e0348107030013140c0420064026a01500030004001c8980c00c1d1100303200703500511860b032615500003944020394100782040b09031010400c2450 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 716295800 1250 716294550 716294569
    0x7052b060b0d05123f040c211b0605030604112701021203040203151f031a01090204080a150216230d051c0912050a09240c02 55
    0x20780700344500c001641084c0b0500c0300600240e1407102e01803414441418449001c4100720125038140c01d00500013548017a02c4081843d00305114280001c04195500707400240c819128003111780c580c5080c44002c09000d00c0181401c0e5280e25090b01c4c170803d5041c83c00240a601015000600032a0785007003c440d240000d20885d40c0c0d5000310b01c0f6400e00c01074100d101c40c032403c106d8a06680140200039a44203518010403d890090f54020094428107000d5854400920700c014013a0500880009040c6603403d1034403419070144d070241d049222980d01f02c449003203821006a210b0304c4590b1042008100c500004580ea802055120103000310120300d50700140b0103030142019250846040c040c1c0c00d402c00c01c0700207a5130f07450320011b03001c91a80070a03548200d4440140070303c09400300700b0030000310003424480702401030641100b200c000350284041c3c84010526100035850703800b1402c0000d0100000d5000310a0344010400f0065400d2207138284d20400341d662a030036400c0b80500c030b440a00c0f00110340e0b0f4130400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 716297050 1250 716295800 716295803
    0xc0a0204090b04060e120732010c02070e040f021002161205100b060a0315080111090a090207051002090607060c0206070f08130212160807052b060b0d 66
    0x41c0006a030a0422030356520042d18102d0350140b50440d5184104408558810981c1c0c41d0f000040c142600b1307890710440e01002c55075a18911490700d507010880446480707000c0070041e00c0400051030079180c0780040c0c508a02e54224910040308072041000203441c40b20581c04003507043c0e4884a540b0b03070781d40045c0e252905c00f00030104605110360001c01e81c10000b4020300741c8a03000382c003200c0c406811031441e00300301e030b04440791960010420860101d040b4040e4110600c142035107a10401811390743c14640d07085071041c1c26004c3e080c0f480060001981d24040a110010308001c2c0c1c03085150a4903961500e07500d8400020b4181210380105101d81a99107002c1951310312a04180c05006403a44840e00075100d22007280d15801107000940c509604038419180540704410080c0752a0071b1000b5a02000b4104a80440985e85031050b07928070700420f9507061403c0024941c2100a00ca101e04110820480300c4840c024442c82e5480c00340381410020405050068150f000342d00012402040d41c0400e6141024050 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 716298300 1250 716297050 716297059
    0x804080d05090a060804020f100e090c09010e01110a03030c05040b0a0201050406050a02210a2a022406010f05092709070f0614071e21050f0c0a02 64
    0x14000c0d094201008040c000c40884400382a81d8031900143c88003481568041d410038030108090f550b608264000c1101081e06041c601c10790454100081d1503200704403665144420081021052940c100300c1d000c60741142400d01c486500c1c8013118480d603c840012000d01010784491f0b070b40741414042d00440c0e010b4100840d91998680b00c1c0c0c500a8040c15090760122002403134800011501d103014800c1d02d81c3c00310072120b0309260480d1140340d005640d80140415030380c0d1341e840d401100340d030040c4560956420741c1e1025100c1c0002d021a0060f040030060310b45402d030344060480402403c0c1d120590b95034072410909140f094001e0510048801c1d0113004095900100f07142e40410f400181011040c0a198035005213003503d90b60300d145c95071528500d12a0b000408960030b070030f00045024000c1644094488091941400d28030713160082240110400380580b5a100200d40c02400880301003d141681c64528206902d803011000a00034418518481c80341c0e840403541c402008801d00040c440660000c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 716299550 1250 716298300 716298313
    0x9020102060a27080a020c0f010210233417040f12030e01060b09030706080a0b06030f0708070c2406030b16022e090218070f0e090c03060409080408 65
    0x280a00413a403220410201512482d6021602441c060600230180041a070103810b09124018402000c0c040788100844a1001c0f410900d5810b007103410b000c0e10645104c02d000b01c092840007100d10303055030607104080855401c0800d005042d030700081c000c4a1340c402428030000d1381e076503400c0c0f200085c006a01e000b0010203554a0f03030b0502d2981a0040790b142c3c40c40b03000800080d0303501c5100c40220b02ca01e04d5440e400d5081000e0802245000e02c007150b50042c202000495120310380700c009842d070f510880303013001c080c02007909014030742d80e0001000d60300c4a2a030401c40004001903c0740403c216681c14443e0740300d090700050002c0f00030720b078000d40c00075a031280011209003840380980340305a486450701001807040802041800140349851401e034a0395a810281c00b24091036500041d1800080507a004100c00748424600005a800c6500c0390380a5501d04080c0c405880004100e4424110114820045002805269050041144d42040e011940003c4461161500582038000e0750300c800c0043c0140b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 716300800 1250 716299550 716299553
    0x1090203160f050603061003110c15070306140312030603150f0402011b11010c02150a0207030c0527090c030a0302060108121602010e0f0d14010c0309020102060a27 72
    0x201101c42a902d002440c00d0038103885a080c04545d000c2100c10a92014502407c458080e009500c2000c064440c02180c0d8901141b81042601d80041c60319004030401c0710800300440340d5031501c500f90140000506441040c80c49500183d551084d01e0704541c40c9450003c003041250394204203012689891411200c001e1030030b401c64503803107907081301c7c01d078089403441d030800039000030b0404840c0c1915485141403440a880c0c0004544564111b08102d0300003062480d8858034151a401410181c03245038000c1a0503411854156291a0070b40d018601403d02d48504907108040140da00380c198501c04100b060550794180b1a0740340c49014054140c141c060301c80e240701459400305450341624051004c0380e50641d05061030002c0c034801e91a085601c8030400b405500198862602008010304c020f2180260308451000100204008402110010604192074640d800c00303000b0490300b81c01c94101089020a00d400103503d0781c5000746070a101d80d548001044488040e49107000300d1190400004151820704e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 716302050 1250 716300800 716300833
    0x302031c180516050105070b0106080405071a0d0e0120090d060e06160c020d0f020103090615091407091e030f03110c03010b0303190e0301090c0303120c0c110301090203 74
    0x30300d561200d150a8440b00451340c2c0d40128200c2e2500c03a8885000f907050307844c010f011903400d040908112918010000000f421441c045413402e105040340c000c03599149400524501202d0042000304200c0e41444407040090240400c128131030309136600340a17618010b440c0050002c110051000707121500e01688042991400504c003445000d04091b003840a040c43c0d00c064450005032240254000b2022005a0020705240092803400384181804200010541d0381d00050352141c1d82c3c01084c4c01180700d010031040c81c2ca0b00405030b01500606a10b44141000a00246004200c2c0618101d9559000c5118040070081c403405004541001c0044140d031498907004103503880346100c01c2094868119682040d10f03043c81000c000c0a00140210301c3d102140c44441d10448640b004c540c28014a16a003040540b0f0a0149180840c440c01e00c04405900b18075000e801e0002200b0b5161086143c4400022300f1074001c800c0980894221034001d14102038031000038003402c20244002d4260082441044c1d80c00c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 716303300 1250 716302050 716302063
    0xd050d02280e240a0e130c02010516032a090e01080d0e1807030e03120f0a05010608220c09020703030b030f12030c13052206120302031c1805 62
    0x8607a480810582c2c00c2111001d07004000643d45502da081100c1c40c0901d006000c407007029031000d0001411001c480c4d1a03081121070603821403002d070351150200701d0405240450300c04065110704040243e10001d144005401200c020b02c000000c0c410346807100341c24020040500184030380c01c0103942547e140c1b034410707445940c0c01d030444010070b6a412124500e481c10454002d2010307102141c1c015980c0da2000200c01404088800c5040c0380001c1110080c91708072100010b121b80c144009075075690030000e940b40c003210016400341040140d84024891107800d540c00c3d80103000c1c095050074000407401d0400c40e0b00740e20180e12100c00381e03100251100405416810900700f100003101a9075107480c2d2031548641b0303901100702108505000701300040c19844514090032840407000c80c20012903071184003040c020020301020b103840d05969081031641c1b200303c2c0683c0c40500889400151850556a0003941d079018540f49202d013045005100d1002c0161a0300401248098101e411801000380c10040e071203a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 716304550 1250 716303300 716303327
    0x1206032a010e0f0d030e04062111240703022805010b0102010203060609061312051510120b0910111c0b011b0f0f03120506030d050d0228 60
    0x100704003201002c6152002d40400d0203007024200302c88240507a0f808890341d0b642c0006003a8804d549403404074060400003d850481c00a840c010490300281c2e092101804140076031162280c4040e08503064917110101840340700b008100049600c40300d1a01c1d0030b0741492404544804420f03110300302da07011010400003245a041c01100204040d104542c012400d0388411070381241c124004200034591410110f000b4018411200f03401d40d1a1512a52a250046500c003c161541e42c0200d0190031140001680c150b0032522104c5160701c407515291344500e40c110000c202034a0300c911440000c08440007400000c0031000e03400400c0058103605485030510760800086070b0030403011a000c442c003e00c0c031407142c500000c0b030507103903070b40e2500813241d101192669441c1704441c110203c1010400254800d6144483c1314480d4842500d000da1081e14601120402031030507200760f11004110038511b801c0f0084450070810382601694400a100c4003010000d4224041191103240710440600940d110900c00380f040d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 716305800 1250 716304550 716304557
    0x1514240a031406030a050616030603020306010b03041506141002031e0408010609022701053006031f0b010201060302090f04060b0904050c0f0f04090609050c01020f031206032a01 78
    0x5450300d0f0141641c40201c040005c01c1d60f80010b0106100406640c100c41c034800062501207049a22a404682040d100780c3c40301d06000030100600c8208215100200880e034080c3e0010400c035481d140380d0840c40080100c045009070700c84201445014820310889041d41c26920264810501d8000c000300250b11510030009a94a02140400c520001c1e008444000451030a01000c0b058181040c50542150221090500c40100400c0c0c01000c42c500103060300f4524070b40e06900445e00740011038a500001003d20348070380c10500040c5a044003080d003414103c0c0d0050302c001800340a0f81d0060340145202d41003e5031008800d02000014610046941d1007948a1b102c184000e0210701f0511081c1e4405540050203500040f00e03a21a50a04000754060280c1c010502040403040b14080307811186000d60503522103031990500e07030a2000400c550300c000e00083c4014400700d40c50007802da4a034094081c04106054001003c038901c2d036420440c00d42a0030800908000d01c0c207002034451a500c400b1200503011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 716307050 1250 716305800 716305841
    0x1020a09090f150e06061c0b0103180515150d06090501150f061103040b04030f0b0709050a140402040b0a1205011a0403030f0c0c0b0d1514240a03 64
    0x1032119018114642c3e2000034040065403c050300066086002442607800400510258156200d82c2c6030070800d643c0300f80750002d0034910400005041d12084284410301951201038580002e03400a61421680c03000007110300c1c0394554180305925000e0003200c6c598041207041c0d40340c0c103220480d8010064140310301d00800032446040c403c0d01500a280c440c0c0110101c0a80d02000003e00801c5030000b002207600c03d59280ca40c070341048125540054009507079000b00c02e40d1100070011700ca001c03240c106c5442c5c140580b030300e454480003941c410500c0c0260140d28141c1e441481d91916141c066601401406081544485c0c0d07071500141982c400040540005003080000100098903404034048100c41d01641740c907040c1161800d030b51386204000080d080240006108001c00c00300b07010300c0080d081171503016a558812a0801044c1c801007580191240a0b0300002c00150091411903412000191003903011076a0241c0b8401c40d000c02c03c0090310343d4000000720803181c0342c1c1c1544140344820300700c0c002480c07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 716308300 1250 716307050 716307071
    0x3020d0f0e03090907030f060609170705151620030d051602280f17060c070b040302030d020c0c09010e1302151b0606041803090302190801020a0909 65
    0x40d1141d0305404a8150010406489681421110964044614180803c4888540031044200ea204e80d2100300000d032032990500524502100a5401064800041070b0312400c180002d000c26003032032841040a180000c413400204c02e00329544440c5038005034a80366030341c40b20201c1800b25070320a0318244039000c0c202015010f40c0c018020fa030480e03012242c056588a4903a8203101a010300030b007101c0d60f0485540d240890395400e9160307030005080da03840031a94043ca013440e40031100c401417040820710b400c510100000d1400050580e00300d5600041c201070103403075a00302a8210f208010318a0740407800016480e02c00e0100040c1c0900442c0146d0748400c0e00d80c0d03509a400700941090360303160f02c40100d580d0580058a03254402110852082504c545002c90210a400d0407802c00c0000703005075007285003040300700e180520415200c0400404500c50210f4695801004d0b02141d02000f03100301201c000310340c840384408403540702030000b0100842d540e030b506803009440303589940306600000e41400031415 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 716309550 1250 716308300 716308331
    0x1050319110a17010303050f180904030c030f0c0807080a09180621260f1602150a080403110a0812240303070201110309061306110303070509090603100c03020d 70
    0x2c0c1206d40658416050400220b00e00d50158405102c1c140d603504092103c40d8550759802405005500c6611a0020008280380242c10100745005650920608101c0d16001c9a207110407078400551044a0036580d81c0800c1003a50841020340040c0008080d10b48040d118000d541c0c444401d50b1128050211801c42c1c1c1c401358502407150000c02003070305c2181d40c400710310340c2e0400c680804036103451700b043ca04140e03000348aa01079030014003031400c1c050510783d1480c096003800038518400d4041c80c800079160000e10700001e400701c031014100604101044820300d8014000348580c544040d4415159030b50340344101e40101949200f55030b81e510740082c1c18140322658180c01544a41c1c040040e000e5820200243c00644400600510f032039010b020401208e0880c0d03446c50700a02070088410b46070750b0b0440c11310900401c0404401c1d481031032a4401c209104081e03402a054038590320040f641c0e002031355510404242024243c0c03030108141814070907101725007501038010b0401004030903c1080540030321040e80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 716310800 1250 716309550 716309597
    0x5010807060906050c0f10091506060f0c1e080a0807031a0105210903041502010c02030d0e03070f080306010e04060e040b040f1a010302040b0904050c01050319110a 72
    0x1001003800e102c010040207000d60064110301d0b01c8202600c8841c80441d403141d052841c00f031403590100b80d48004040802189101b40b500d003110201040120714105400075000d10b60380c04402e005d014070b00c8141c00800204154141155a032040813920410052130000c845802143c2540042144100081c002611911806121580e00d007441c2107403c003148010b6036142d015807942c10558400900c0a00a410201641c9004018100c011030341da514100f01080074221103401c0c4800c42e41400e54220845500005644184046c0c0d440041c0400840700168038621803100700911925541d402941403000c0c56002d148250000c1e01c1310044841c02c01e04003c2101c8240c010f4003c0541c08502080201e02104500e5610238403600c85410002010349030545080300090310709a824051074014021401c0500441c0341c00314058540341c96906240d9a159180c0c00100f050b14100300d800300004042001c081d041030030601418004010102c444d40e441e02c240c1c0e00c4041e510000c070344104107220010b480e2400c4c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 716312050 1250 716310800 716310809
    0x201030921020a061805300c0c09010b07210504031203150506040e04110307050d060b0f060708090d03052205030d0513060509040b040507080615040f05090603010e011e05010807 78
    0x940000744514226690039201a107106403c1e011400c0c9407c10078020600815186040c00d008004040c0c80100308415550b050300468070151051104000142008803a0030306100303410404629030b9a0b40c80304644a004a5002030308020030500386400c080e4044d0300c003071101043c04504481041d00c030400d22406110790b20074452215092070015000c103070020000c04080c48014203440c1025075070000030340040750701032082d62050303079034040b161244c0742c84545226405810303038445090900c2525034540e640030b110003480c044e580c2000b400b410144548226071100c5c0485d69024010100910280c1120070b20340115070013482400d042c250020700074001d54100c200d00c4d46076006130900f010402c071029089404095081074403481d501081e56070301d004c2d06104d0b22082e60768140500d043d03800c02000c80042c800c0b4218a0104110a20400c00c3d507000030019070350251030501103500d0302c0c004030340180600214030090354030b4090031034400106009001c0d02c0c640c0070704060002d41d8841e404583c40310351a101c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 716313300 1250 716312050 716312053
    0x5040e0a020d0204060b0301061205010806100b0c0a0c080f0111030c0702191d071d03100207030c050102030124030209030613020102011e0b100903020306040201030921020a061805 79
    0x1814001441d00001040b403552010708080740c40c590b80c03401088590000e81003040411201c0102d003002d54400d101d094014800e100c0100f07968180518000d01042407801110090310000845140090040041e4007250b40d021911900d5131395a48401c1e500d9080c1124088400e500b04104001d00c0e00c40e68050368064518122040d282661650030454040043c52540c8420f400d219000110403454580070320079100c01c11001641840c2048008081341d4196505100d5000151210307072982c1c5002582490111500c540140d4402160900b5601181000310042c00f0358000800881e103408541c05006840303090001100703204c1d000314419000e0340500c5001d07031741641c410800904c10b000c1c030011842100380107000000e002008050840310408590007201411520703038422810f541003005950110b07080c02e1601008080c215400603443c2c0201400290405407a0040761041c050540c46d030340250034400074907074100c0b0000d4501030f440e1a03900c4000d6410700c0c1f030413081c0c2d6140724203203504402c1c0d80e03070000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 716314550 1250 716313300 716313313
    0x2130e010311120a050111070209090a0b0109021b011104080c01140306010e0f030607090311030d02120f090603011202040f0b0607030f1e2007050102120a02100507170105040e 77
    0x8240b003c040b180c010b40160074070a44450f6000310340203104098207120300824295a802076070040c07200f0300801a044003100d0307000340d00941c00b1039203540419054400090b0301507030b00d8000c00102d9482568600404506518110070094501031180090045500032015180078465900064582113500001100c00d120100300241056106d5a060100250000c107006103402403c0c001c40e00e044012503001b0045a10b4a00500510001c0910f8842410084009000700301180600035114403130800b000140c102d001c500c4495640e020004d031055000064030f480e4503913a41c1c0f080c180246254160590080303140c0703460380f076400803240a00c0b240440d005c3c180c81c0c6845000e5908603410103078040100c00300409000254000c01c0824201c40c18000c0d19a00d05800c44205040b951040c030902700c9099440d40b141d40100b240b40d8020501c401c0041040204645411424000342e00f410080c648a1003040c0c9080108840b05820124111192100741e40c0003030140e0300e40301031204581c041c09402c0304913070260 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 716315800 1250 716314550 716314583
    0x50304021c0302010603150e010b0405090a06051504140130080d060b030c0408010f0b0a0e130803011215090c170f060c091e0f010305070513060302130e0103 69
    0xc00d9031a14080c4a4400010071781ea9035200e104035121000d410040e0030761200b0b11030b0b00707074071090190300c0910008231400c00050030615025a900d0400880003019507031604001850b2644071400c0c84090030015000340015005240c80095549090013480c50b0001c1040c14404035416403546010303c41141d80010b85495910340354242030340c1085840b83c241701d440d0000442c3c0e861202014501a03a41c1c040b81e1a2118108580d2a013969a44440307490494900340024802c1c0d40c8030040c07881101e40501e40300d002ba4458100c40200e0b41410080a17004803000000080d1041c5c14034440181d650040a4101c248074481100302c0c265002c1d644080e01c6840f04c044140614585044184000024a0110b074000c4604801c41070070004101d4124800d09008603001501e41080542d051404481c11003440811955100048441240f0b440d1181010303500d800250940340034804403900c0070070300c60405003602d6031101c000700a98082c0d0384540786052204000168409070450490580c2e038400c032062502d0504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 716317050 1250 716315800 716315839
    0x302012a0504032d0309051003090503030a02031314070f0e161812060903090f06120504020406030f0c03021f050f0705070308030f220308130507050316090c05030402 73
    0x36604110600c002e41d400800c15441c05204d0642810302c02c1e26006051498041040003000c503150b4071002341400e02c164a000030304040300301c03070b840361080790010389030749031240c0081540f00d886c0c07002880980517412a048034000001d21a088a8002d01e2100119880300400c18651809076071580c41c00800182c1c150200d4012118104200d0300c2da01820701c1240c2da00c0c1013010075840004244c0c0c060380d85103000c60505500c25800c502403d926401307600001d24100c801054280e801c0040c540032942d410100d021940c407070704100d006607008007800d01940c8807402c2c030349180c7c0c0592004070b104d2066200300d200d0504d25410311803050000f50325094181100d0580700f038200d038000c000886441c0a607400c0400020300c0180a54055500c1c150100301c10710340110f04008000e603038215000054108084540020352056840d5408001d84480080080c41c52800302c0c94580030ba002030707030300d4080c0300300840e00b0b504c0031300c00e40040702d020b080c2c1030001c0c0017204000c0d80c46100c1a540650000302d03000380307807000e03289 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 716318300 1250 716317050 716317073
    0x309120309030d1e050c10230a0f1a0d08070602041d011703040b04050621010b0a120509060402090910060b09030f012901020304080a0302012a050403 66
    0x2690040e00d01d01420100003c0c00c124400d80c0450105294081c03c44000000031185981c40e10345051245c03910000c2003640341d550b0700075115403201c2603c80308019182a000d05030f0201d11803207000c60321150f080c428000300161503c3c18011a04034909041205007200310544491500805801003150080645680c4010350024109580c0309408010009200450b200d544443c0340c4054000c013a1303541841d980803003146001c0d0490300340e6481840103101c4030107100125001ca8100700c07505e69881030340e00f0411002c040d00d000c4070000d0203046000000d19044030001041070040e180d071007040d90307890300342c200040390025117010300c103130b4421800940107007030907a40c4c95000001101120310407801d0350403050075500207800403d81090003084050149c01c08020100014441200a1064056280205407085c0d0701c46508800e00000c0018080c840c1d009008940141078407609444103a405030030064082e01131600c00c0c107900401c81082c1c0010350542c001002c1d50000e00e9032401c4c41c16244d03860b50b07007000b81c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 716319550 1250 716318300 716318329
    0xb0616020f0a08010917040e0105010528030c1b0503030103032a0503130801140c0f0906280f1209060b0306090d030b0103090c0b030408130311090c0c0309 68
    0x71040c03020036050b81d840c1410607008000c4940081042500c51401d1100e104d00680c0481c6810310912041c8126a102e011050650b5400c2ca400e03500e40008650040304018001280c007101e0a8440d000c11620740c5c140c100d100d0250042d2610040d50103505601c3e648070301c4118026000b9081840184002441008410030041241002d5020319200d40c03c000600304060504542d10303400010003c64000f050350b0450014007000e40200008404444d102091450003000802070107400502c003080000c3c1c81c0155101e054000c0c15094032403408800e443c141c0400f01a00d2942104810f80190010f0b10445003e0702808040e0743c0c425640d95114480406000c0141c0201c443d203407100c0303880a094400300415032088054000600d04d4000c1e00201408035080c0281c443d04250424440c000404d101412030380c200c40080c4215940d03582d40303083c0340540740222088040d0188084100106000b03413000003840c0c440e4201c458002603201c00014014a01c504244040c042d013040c031501c080ea10301140401980c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 716320800 1250 716319550 716319559
    0x90703110907110601080318010f0c0f0204020c030c100b06040f0303080415090b16110a03120608070b0712020a0f02041d010c020304090e070602060c0d0906061401020d030b061602 79
    0xc2e003d108524213061007600700c0302a60340302081442c0311030034503081e401c0308943c00c0c00d141c215401195002000421142c5018240084030046102151219030480301d200c1c08140941e5250920100101c0d240d40c10a14250034090420f4800191441c0030002c40d01254029a00070300c11529607982580d144800070401d54110395450942c0307000c0d01d000d01403400741900c54240c920f440d2800242c190654070b0711862400400c8100b81000307281003400a50728040c03c2c1c0600380700018a105040d41c1d0054045900190300c40c0c011100c0c0040c240b03c0300d070050003290f03100d03001c1200441c0c00c00d00100e0703403140b513124090207100a030100240907041c0f5500c030038411401e4220450b95005541d881c10f080d90310360404e90006a2001908018001080c410640381103034800103400b600b80740c044001c1d0307120030140240b04014000150340c038401c6895030140e00d03c142e100c2c2e000d0012554a054155600010200c1c0030b0142c01000d1003508803510a10405c5d240c0e504c001d00940c1805840f00d400c030040c0743c0d183c90407600b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 716322050 1250 716320800 716320817
    0x703090b06060a021f0e0105101d091905010605030d0f090b0c070612020909010b03150319080331031704053c0601150f09030314070b1e090703110907 66
    0x214900f801010b00c03454809c0b400e1520340345083c07440c0000b07008039501e0400031550381042c400d200b02d0109541986000ca07196561807144030703081050040500758805540b602c105484207000c20b8004245454100c0c044d2101c0c4143c599400c030901d818400d0007030fa4011504030369402e10040d405110484010700b140800181003140c2c1c1008100c1000082c4c0184c0000d540c0071040082c00d0040e10901018440180c3c00790102040d03c41c3c0c1606507003001e041c003c140c40703400f10028201c0140c100740b1200014038508031428042040f85002c42c0307400780c00c0c011340008000c454206503107a031940c03205004681c02402030800c0140e134410080d0b8892a0f0400c2c03080c8010700da0720712856480d004000d80440034450042c10041d49800100301124440c28054414040d1403903920756500e4204113258101e81c0c040c02d051006a20a5074040c50034441d80c40001c01205200b01400300865042001c0c04025165802c2c5c0d03441525002e408035a2001d46100090241016604000c55402d12450b000d8100c181c43c28103051 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 716323300 1250 716322050 716322071
    0x81207150203091e010c120906090803040f06050f0624040506041d13020922020d050303070807051e0903010908040303020a12030b0d060902180703090b06060a021f 72
    0x40c0d030701c152994483d5920840c1c03c00215140002c242c820080520000c008070400c000010785068544580c0c101d020303940d0039051041c45034903004a011180d020241a90380d01c0d092614422504503880261440b43c6014009035400c8080c03074505005200040042c90b02c420540750501c9040d58400d005404241d00b4000010180c8440018101404a020111010320a6020059003100004160440c0c0c445458038440140c1ca55450907900701d9960f0080411040d600b64000544030b801b400000d41108090a4000a02101001540c002c0b003030b640d0303003422076101d4000444031070140310030020842c0f201100d0400c0740c0304103000600035280e01900101d21003070141c0300c01c43c254000340e00c242c0160b00044983c03400c10424131101c021291990808000b00c65018011820086100300010070580d601c00d480c5041d94ac0311100e02c1141e03040c000c5884240c1c901124010082d00580d00c04031000140480030504501d40401a25102043c4d5030003450307800c1c11000b0640f0319088801d410003403d0b40d521030000c0c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 716324550 1250 716323300 716323343
    0x3030414060c010b0a0f091a0604051201140c0c0d030b010e060a0c120c21090302060901020a061b0306080105040203061513050a02030f0105010f121e0f0b01030b0a081207 75
    0x4004013001e0b146c003481c0303514241050342500d1040728906503d9000c0385000b0030540d03866050710b05a0344190f07010414400002d005600502428400b8081c0203120070070001c0c02141c00001300640b5030442c003510041803003010f094043d92940c0070400d000ca043c1d880c100b001810518060658020a450003100b040942d4649100011490700c050b00041d4854011200340a503000c213101e0300c03ca4442e0300c2c0c6241d00c4014401400141e15000080c07040000140d10310260f8801c210705d0b41100c1d003003070080102d056010048424910448141000301c0d0400c040003c84080612580f4400e54000e0302400c070701d640754000d8071600ca0509071510760049540e80001070f82481c038881c8520075a140c03880117980b03091804041c0840305050f4480340c100f1907020000401e4a5212100c405140f080d02c0000c5210b070700e0f054a00003c54001d80ca01c820f041d1401c0046111940c0c0758005d00950407080e2000c0000d16081c4080c001c0c118031074020403046074464440307030304410003881c01030400d68050280204a44403c45040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 716325800 1250 716324550 716324569
    0x40f020309101a061b0c03161e092a0e1c23060105090c040620010b0d05161a0f0313021e031507021203060f04060602070e0603030414060c010b 63
    0x80c940320405d940c20381002c180400c880b0f200300d0400c900070007113031032a941c6001001c1c02900400d2020541c20998102c511683c450210150012150a10202c40040c3d0102504600700c80d1024000307802c9a10400241c0c0124441d02c030380311001c1e015400c0c1000d800182c111840c801d444c12104283c0c40085035141580c80103a40c2c03071000d08000030345419450201044041c050151504078030100c06c0000300302294102c258003a04440c4c1d161181e04c016156847c0340c2c0184455044e094102000140140400c0008558410042c290b107200700142a21406d64030100707442e545030804500000c0045404484100d000341d688403000543c192002d00711580400d21407840c140701c180b00c089060f8035900300e6203014000c08031030070700701a8802410304e070002000350f031800a0101c0700b802d2980040800c850f500d41918001d400c3d10042e10902c070309599100025a1088540b18000e03101e10110086403462401004550403141080310300d6107401c01020820880c2d80c0a003041101c190346c5d4030040001c0da120800304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 716327050 1250 716325800 716325817
    0x209040b1902090609130b031204030507120201020d05031005042d050c04140d080c071a071214090301090507090e0303040c15020f07080c040f020309101a06 69
    0x1000c18207220200c9949515072071554494140140188091901d4501c1a41c16900c03044445502480c4c1d0a06030000030014140007907014055982c540410344108001481201e1180007162801c507640d00000810005828000380103822100e402e00d8a607104001440e0060780303d001c144c071500c3e03807007002408517485511440340c80e02070084040c003058011007076890924495002031009180c000300d0300e0170703510a50160880c0b4104034030440045895404085074004d43c010070b126600d003498480d00756620110f00c030302c0c03000b01d454441c2201e80a0810040d07a03000d0707600110044440a07048000e03110040b0310341d02c080240805024000780c80d9400d000b0310031281e00a9014010f194104071f00001a10040703103594041d030344101b040c0070000e0000c4c03501c042141c0c41c40c2e0014811160072601282888400008c0c85140e118808011925541c0800c500d00740f440100c2e001c000001102c210202a400125001c0020b5007040070481c0b200c00f5640c11640b101c0405000b089201000100003c001741c100410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 716328300 1250 716327050 716327063
    0x1e0609060c0c0f0b09070b030f090d1404030b07050c100c020d180902160206040e0f010906081905030d230112020a120303140f0403090b03060109051507020904 70
    0x41506100192089800080a80c9000410b078011502c40724100052408014504031925000491550080c07002d14080c0c107441454540d607013026482c13882061000d5402903280e004070711180074024003d074080030145032034600c0d460030949103807502054106d0081c454000e00804000100040c1024054540d8201d1004ac002404c2c0140600c0203103010b00030740c00c030b209001e942080b282480400324401d10803641120000b59541400440c100c90800f1802002500000003080c0810803440e00a4090700c45c0801c00c40c031214507a611580c80d000e5032210320804106401481705a031000741c1613055101010f0041c0e0480b850301c01805002d0045a04610341c03602d01a41d000c00701200c1011450300d0f180102011100340c80c20094580000d2002411403003042d00c5024600400003c25000341c0007115480d2115000c010300345001d00c14003c401d4030880d012000607031305141c041095913901003541c2c0241c10680d607001620382040284010000600c1081c1c81305d0b0380074002c1a006a54030780c030040c0b285100e0b00c2c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 716329550 1250 716328300 716328311
    0x51e0103060f170601090b03100203040611070b0106030b15070b040215040b090915150a03060b0a0801030605070c0308070c061b0201060305070b0708120a18030201020307090618121e06 81
    0x48440e404c010060300400145401c0102004017950001100004030710003080040e602d45a0b0320b02070340103081e5140c0b101100f050100e134490611620382c2d1014102d1303c50752002e02480d040d0408000f40028a136808200280c0240502d00104150507540c65200d031000d0304864480131034400c08400c6401c55800b810801d48009500c1400303062045401d50040a0700d18103918032000072000462003c100200d52a4030500460700c28030151081e006400141804050b450341c2d00070f2903100524040302400305541042c14000401c190620800e640b20325140c05a80d02c12503900c03040d070100c0e0720030116103098502c9074580038801c83c0c04030181c1034054000341c90313000000e990346903241107801d12440e0ba014604035032041c050040400e88110489140d0002c40b040f0780402c1e5170b8800d105004000210040e030709440c00c0c03039a013000c02da01540214020344c11030320759401c09a900c1004480d0a40824070155418100714000c00c03500301c4c07880340100c5a07844ac00c00c90341c0801c0e0700001c000030170480381410740301c80b6103a0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 716330800 1250 716329550 716329589
    0x306010c1515050a05030318220b0f090f0c0a050f0c0c030705010804080f030406020d05130615030c090c051908040b0a0c1b080f0a050d1401051e0103060f 68
    0x42c2800100000d644000140b841c110009481e8000c00e00c09071103442c00044010302caa0340c1d0512030400c13001c240000000b001c0d100c3c1e1180004010136050a400341d0300e00c080c9003107589400a040c078071850000841544599803030344580082e0b001101200140241400f070799040c400d03030704060001200761034010082c00300e401c41098503005940d0702c0981400300020500012a034204100c0e00640e005008983d6661260310f8600001e00c0b500c0c21942010741750509221411040708111030555002c1d1006100c20301800b452248444a640b00090804e144480100400005500314203c04070144c1441420b015400c120340005015000800c4d000610340020041000340c141082c6400014000c070411451040c0130004e480c2c012200451484042221200d204103c3e9241c211008814007a0681d41c8400c00c90070301800c180c1110503603c40303050415000102150346048514100da5004107000102c605c005450807603145c10100c910304043d00c2c0c102c00b145009403406e00d14020028903400360404001b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 716332050 1250 716330800 716330831
    0x151703070b0f040804030b150a03060b0f01020102040518130b040311010c0201020403022b32012d140103030809010c0e09061011010f020a1e0903080306010c15 70
    0x1c0030b0710751640d070110a0101042e056802e8034103480d4130402a69060b221203520000c03103882d19441540c010401c2801004200440e040343c170b0180300603685a050207451078016804c0c1c0c010790140c43e03004048140703000d811207010000180c121102842154000c4419249d034019a4400c98091300810081d00b10102c2c40c460074410300032120654030003103080c14199400a60080b0310809107222007502c0305040c12159a140100300b038429406a4090f0807021000440c2c03900380740c00001d540c91002034002c50161600f041c000c011000c084004c0d0003031091172032504c2030f00502125842403280f07031359603045c0b100991405104902842c082d4450320020f142c100d440e0350a5416200013401004a04060809561101c8078000e821101c00ca904d098174200103c02240c1e4101d408104031999820f1041c405070080c8264001e1111031695a184190b2481d007010307240c1d10b00365040c240740000300608800c0020810036000340d81c001405140c144402d0b4080d8445444c0500b12000b0310a40542e5204800c412044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 716333300 1250 716332050 716332073
    0x1302040602120f0406050a030b0904061d01050c040e0912040e0a050a0e0a06020309341e030f150c0e0f01020f060c16120201050108010f090807030315170307 69
    0x105442e00354581903821002002c28001c034851541405008200c03000440d0103034015282c4904050301071103192a050800d038015000e103c601084a10101d90007a03803010040c020329100318007a0500300d1400e8908510707608204d00040190886020b0000d85006002c00741004100030450f500a034203160a10207449802c6503009030034036068610708180900c0d040700201e100d09549801540040e00c0341c3e1a08103090900c02114100000310162a040c4070020340c01c041c03003000825507034035002050380c0c4444004a0900021205600c954182042040000d0408144440d03040c81190340c903c503c010580000d0594001d1040300e00420b40c1281c0300781450806406603140040244003c2104040401086d5100c0301e024080c00c00050b80090740011200c0c990bd50380c007443d540241050141500410024001c250a010b011120b500701244038000080303a0251000c9190032030250f919010007503030b041e0005d154402140e005911140170008640300000c070702c510a0300b40000910780e5200d0304d2a0071000c030321 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 716334550 1250 716333300 716333323
    0x10c0c09020d0c0f0f180503070320012a15061202151c090503130b0304060506030a0201050a050318070f0303080105090f180f030d060618081018021302040602 70
    0x40d40f81c0440304e406500202d580c0c1c0c80802410000340a221403a05201c0059241e0070090301441307588400400c0082d403d0568500c8410584540e02400300c81004495240c7c0b031800e418031403039401403c3d4a120040f0000b0381070042c85107203055000011104a00305075500340e4403060244444c0703039602c0e003541040d6903405440142194418038100415480f2210560701d40384200340c0c2030740d03070030003c0c10008100200e914941c8580c001311042581d4108840e6603600460b1f04981c81d50030000410b00905000680941071a4161122400c11004c990221016040101156450203016003500d00b150700500400d4082e20038503880c04042d6065003406400c01c48103038801c600070340d44c0b40204041d401c9000781032501308024211403054900c101400301e180142a07414540680000116200340c42c0d4903030300c0b00d0b040707038100d407919041c041802d200d0128a50003031242c0d81007500030400040030800c2650020a100c0c5080c3c0d009520701a02d60086411024211909058541c0c000b40030f2007096010040c441d00e44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 716335800 1250 716334550 716334557
    0xb150a0e07171009020a03091506031419030c050c0a030803070314060f060f0d15050a06020c01080f060a08151e070914060d021810032702010c0c09020d0c 68
    0x1410300204200f1090704910030715004a60114090162074800d40040740583d42184800e040c0e9600d181d14140200000e101c100c3d4420039485841d09001400716040e14410900e41600e0030354915520261180042010100d4443c0503801c0018201d542c0d0040d040003550081101c7c40d00d0340b410301005012641c0b21590440c80c02c5218007001071541c1d59401d99600c404043d20b202e900c0355501c5180450b58000c00b90054410f0b0304003100d41c10034141d107a022200321351085504841c01030fa5190180c0c1c4500c0b00c3e1900300d00080720680001c504c000406501da4010202410000080d030b529440641007600603001c1d090400821400d211014444804051800700800c10050860074800f8019141403c2407065803940210020444010741d0f0346025100c2022000c24159662582c1c4015041c140c402280003e21a02d00104890328070384c8a84188180815007040c2050400c0305441002c080e841100401c82c1000080391203100003801c520580c0d001440072900142e200c0b08105000c4c81035900001c144c5040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 716337050 1250 716335800 716335847
    0x110c010507350a08090c0103020403020315060f0418050601050312031b1603030b0307080c060904090f06090b04110f1302130f06050c070b160b150a0e07 67
    0x440c400c0c80560700e0032001801d0b039555031a05404040c9819036951030000c10000003040d01c203250303a00f01ca110340c800c1030400140e44075051041e0043d000c078003482c04080d4065001218003011551541d00d1160001c90040c000b40d040d079220800181070310724400c400e2028020b40082482005020869540500f1084024115849032248604542d00008005840342c47c100003111800e0010713074007101c60000d00d00d072812a181c1d41d182805005046100c400d94001c0c840c9070400110300c1004070b0f1000220000501c0e5134070b442415810000030f02000d02050310718018401c00c0c40d0015045116684009101b9441c880151425080004147c443c45003654003880c0582482c1000b07507518007020107407841000c0f006031030b1540c5044480c0c0840403a040002500c2c1039503404595290004007a003046120001161003064881c01f8102240c01a50300c81603803030640e0601040012000504643d02205100d20380801406010004240000c254040241086c0310401d000540341d10280001d890004c0b4000c1417071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 716338300 1250 716337050 716337053
    0x9140109060e070c080c070f08101104180f020d140c1c020304111018060504030c09021c060e04140c0d12020a1401050a06050a0609050607030c050607110c010507 71
    0x400c11001000300080003000300da910204003032081a03030b120414903800c9440107501e80000407524074050050b01d8151041d8034030140402d5a030f0180d100780081c10702403182082e191204020350f21102c01100c0440c0c41cec88007422100c1d200c40784042c103600340a6482c00b00b60858448030384100c110001c2e012222144c03003042090703100081103d0880c3c40040d84030006075269928100300c03000d001d1410f84540d0209042d181c41c00c0b02035101101c100c2444101c100140c0300d80d65070300b064409101d1440010701c803100c800403c001034440c6502500c80700a90b41d403070b1807213089e038890100308071505034200c801401c05030414002803000e80580b5448c00c10500c0001d2000b550b02100040d090900200020440d48403041c502000600c02d001030007003c0e41c0000740d0081ca80b05907149601078002103e80c0c0000500d80740d4009141d15106003098111807040c3c4510100034101003d1107401d500c840d0096090086295a07a400035070b042068912440e0b4655810000b02c01940b1038a040c0320f141011103040110900c410300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 716339550 1250 716338300 716338319
    0x1206080115030c062c06090904030c0b01090b0901030204020a20161d0a05060f1002100c0207180b03120403060b030709020405030c0405130b090f070515040b03090f03040914010906 79
    0x2000003079003100000e00c100450000405074440c687c0d2281d0098030000a00c0101074010424040c041e20030980041c0503038031045040d00b207807004e0035103990154040c2d0041000d81800d80c01004071200525000684001d0010300a04040d503003205d10700241d001d0104030b814cc41851846034094007050f619507a801400d0211039030302400140407000b44a076100040381c0140d0b9100e2005681000140a4120380c001d0102c0194030790b451818807000540c10514440c03001480414014251103405405031040340e01605034600810415450a40504c5800c0c0811084c00c0c0b040d019000541c4926070200b101c0c0d06140074181481d60681c0b0101c0d0b110f005010038400d90b40c000c03854010504040e1000902542c820741400500ca40603031000d0075070203000c0705020303400202081c800e12680b0840100c4121540c0d40050018041c0d041c020201001c0d0241720030311000e107100c0001d41d0003100c070204803a80d000b20307169280d0850340140e119501556170307901d04004420031150224010700f25030304100f201d40d00d40321414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 716340800 1250 716339550 716339597
    0x1a030f06040b0102010e060106030f0b120a03110114040f1104150605180d1115090a17031306020607090902070f020f01110304091406060702010c031206080115030c06 73
    0x5600c03990700c403019480c141c4d04c00d50190582c552142e0883d112560f4940000d03000304581158229814200a80e1a0f00c6081000c1540c0824114100908d071000c4252001c039600c019520003170400e55240d146000074040ca80c00058081e50260f0b1003410050304914286c0030760344025070716030300440c10400900c4036404c41d940044221803807420b0141d6100303400c0030203901500e14414131591109090080c0b40603c01c2e0940c035143d4120003030f07a02d100b0075954034000201c41e00075421144da0044442105119482ca13401030000e000040070122414078860300c0607180061400d8111800503030040082240705540480c50b44003c11b903c18045141003c15122140202061800031f03000f2020384000c03003110b91140b00d00d982500004000d07a0749031516907880314060035401504041510320706001c139103d8a015401c6801165058544024103c1103940c141c60102c070036000340e40380035a6480c0014400074203014031188034241c4400c07a01c0c414154030304114441d110303070048030411805400346580400c414845 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 716342050 1250 716340800 716340811
    0x111c0209013e1204030c03020f09040f171204030201050a1d1506010207051503060301050f24270405160b1c0b1c060e0607020c150c01151a030f 63
    0x100703242d02e51182c1c2070519000d10f444908441d00c4002400009010481e544c820036244210303541a00360f805c243c108140000e082d6400741c44902510350540000d0b06210f0420288030000581c1402c00f81800880401244100c9007980980d4440e010004a0581440b82c0920309103100e8100252000d0400815980c0d5540a441d02e81000300c3e80204040303a0003017240000a043c000c06a07008460300074000d1320360780c03c10ba50090207507003007002280d0000c0c3c0b01d04c0c54030710588059003412001d0002c603030041c09405401e0000c0783c000811017044084900303400d40c9004101440500c55001d0b05003440c0080c0741034401f240c1d200000c80616020300100c00c00c4030491705045400741030340d11034941141c0801c0c0200070a0700003076404141c240003110004916001e1103100c500610781004224007401086031114000c40c1e201c0e0058200104035900340c40c0c00e02c0c4540a0054000881d424088448078072400c607803041c2150048042070f64810020889002404220400e5803e087c0e410340c02d01b441c0b5a41c815101420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 716343300 1250 716342050 716342147
    0xd050a0e0d18050909030a0207050f010f0c11090a0c08150a050d05120403150b010207150c0c12050c1003060e0615190503190209090103020103111c020901 68
    0x1202c6091010341d9280500401484000b95041492a01e50b032a0300c12101070303000d80102500090f5a00e004444451074860684070031001000c0a031049a580400d19001c540c00c90030014411400c2d01c0d01c0000314801c5141c0d0400040f4411140c0c009070064038001d041c80001c00300e1284005040e118011404129241620184030350f40341451312b1800c24660010420030444041000024408a800b000c4682d40440208004041c0050700490301e07000c050091a43c0742c0c41c41454810481e100c1d03a400b15496018443c12030a0710744458411200c1e03100c010041e901c40d03101001b0b955441c90145506031007600a42410400365213008070392854124010401441050a10ba0141929441000b2143c1d0100141c0e030b54a654040d205003d000c0b60001e4610b00c5800c50420700010800c0720901c210382c0c50304030081c2003800ca6841c6074011000341040300915466a5030078031140d4148501c4014118030000c0b40800581c0303030840440010300300100b41e40320306422003904032145001828a42602d803185101d40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 716344550 1250 716343300 716343317
    0x111806040315090c03080304050606040c110601211e0303050f1e0c071e03110a050c06030702070f0303030b1f231908091002030f0a150e0106050d050a0e0d 68
    0x142042e201001750310103007011500008000401c900030a910b40300b00c0b8100c0d0304001c141030561003280c0112074503111900d1907001c940180b081c0c00c1d03920319101d4402046030741000c1e0012166900a0200907004400401c610b040002400b0076405000d002c2c0e012001c2d891102c030510740002c002c0d100103d00c0000005c9410841c010440b40041b64003101c00c0c01b900482c60100d001c40f18203a204e00340c10b94500980c005681103008400100c004604800300580041c02028620202e000b00a000d50001d801c01055100b10a00001d00b000c0405500000b140240c800143e0201c2100030700000d0b107410550403440304610140080303590303044940d4a0b9640d420405000180307201c40b00030b4460344504610942c00402250391583c03015400082c161058100e6420b507590403030b0b0601c200081e4081a41c50304547c804110000381f50304181d5110aa864021034860920207582e001e55804d03c2c1d900b07130002c070006080018451101c002c180102600440c90920070440c3c45a80310740ca40e02d0780c405406103400c205012 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 716345800 1250 716344550 716344553
    0x180b0f130c023301050102010e03040504050907030615140a03080307050319020c010e0f01050403020d21060e0402031905070b092b0210030605010801060309140111180604031509 78
    0x20880b1400480050700c001d41405080d060080301c0420b0b052880061840f078800210b041d5106000b41c0740400d4240300154217050800301007002501e40141000094855002c0010105401d40280728045810302c0d02684c1c11410702e04000d1485071030403051401614502420000180d0440859900c10402e1526075120345807115409206405105424441030010410110150044d0b12031101d040440084403900c0702006141426107000b1100074000d41c00409200000900400d501566400c540418051201021481354112641500182912414201000300b1403c0400c541c0301c031021002c411241a05003030351526a502c209004034098103002090a603c40c0d16001010491481c2c091800c0088168000805640ac108520283e00c036420744401402054020301c640c1c820341d0307010707924440700c5c1c0c2c20300340c056025054000089440e40b40198012455810030b1041841010180712603035950010003000341c1e40b030854001164400d030420801000052114114900c04512180700072078000820b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 716347050 1250 716345800 716345803
    0x3140a020306040320010c0806040609090203150601110616112d101113150903030503040807120e010909140103020f0a120609060f020403150b19180b0f130c02 70
    0xd51020425030915031f4031100c06070030260310340c454002642e080002540c3d032558001922032240001e50181c200744407440d4001d2074400840e0b800b04060400300c105614000c134191600d08101c649903280303d0681c11840403594496072070310141c90750400070108840a0342c906281c1c00c059600b06600c020318070f43c0303038000384000b480030122410011608100400d00d10107044026402a074844050038612203022440c01c9018460700f01c0865140c0d1000134050a6035000c1d50039601c060000e8032940024407211000500c60548109000001d68841003d400c0c06000506018540c0e00036184a41c20045054802040700c194181141d8040317418038504071100e404580e0905c040e80005540320391f070b003c2050900525401480c0d03007074411842048030800102c0c204089010380c3c04001e041e1b00c0100c84660010840350001c139004031004084c0340e255141000844c1c0c18200d00d42c440c24005a6540800004440d035200301182c1c100161415805041c8483c0020060000162030200c81680c4000c800e0b40c2520 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 716348300 1250 716347050 716347097
    0x60a020309010c110613050a05120307030c020105041a07030807020601080c0d140f241e060a15030c08090f0304060507050c10030e1c1209060b180103140a0203060403 73
    0x2009411941d0365920601b058200e8851030113030754010200660002018141000d04840c03100702080590705200140e80d04480e8407175102c030141e04102c8280f01c0410380044001d001a1790000ca040440e81d100d2107441c0c0035144010003400c1e001903400081c0100450300002c40e00d280b40e940129180d540e04040d900d400507482d190074072803129034031507042403032030010300061071000340c528540303001d043c07680c1da6060701070180e43c201c5000c040c2e24409a0a006c090750030800d600e030030540c0104000707615074031084c6c110440140039801c440000e455469030000585c0148103540c2090804002c1e081038425040c60a03680d11030707807080004000c030000d50a0180b0038140003480f042d000080c00044000c0c0305400c02000350000e10424142405061440706103c146102143d14140050311140070b040c1258004c43c00524400c00c0640340702d03895003c0b4141f141d4948078a114a1080c2d0b440d003907182d504505250130180008031003074600c0d6000842000c0541e40000340c840d8800c0c0d040c0ba00c41981d600304580c0018814 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 716349550 1250 716348300 716348333
    0x151e03280c020c0a0e152115010f03030e01030203060d0b090303070e0a030503030f04031101140a050a0c091502010b18011d04110d1109091c0e3303090606030c060a020309010c 77
    0x300c070105001507107d03002c140d104100c4044800301802d030340c0f208105844840140700040104a00d0f209489065029030041c59201d01d00400750080c00e803c1f0f1310f035035110810458000e00642c10020070014101e41026049421a8003681d001c2d20541c1181d032229a203200c054410030b0320200d510002801c041c0701e8119400071b0700040f4001e000300300c000d0b80140540c00060b605c4031966810140042d801c1c3d140b0344100c0784001445c0d0765903428589840ca160700b40842d001d804d00219500e4140c0e5a580f9110308092098001c886e2a01150170740c50314152007000b2204040300310144401005000c00f10b55a0a090341a00b0012103900e400c00d480391600100d0f600071010615008001e00081116080010980d0b881414801440415903038829804031021403840c038180d58480700007221009858a01c80c920b01c0107070041c0000540445220620b0002030300121101000b6900603010000e850509011ba550f50f10350075100c1e2820030010400281d224003c4418490400203646d2000381400001c804802840 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 716350800 1250 716349550 716349589
    0x151305040f08041701360804090614040c0801060f2601060201020705060609092a030f03130f050d062d0b151e03280c020c0a0e15 57
    0x303540c1e40140f041001160f01d4540c8440d481d09120b0000014400c00c41d80d2041030080081c81c01c1101b14904c41008034000d2003d480064003400003280c0400306114000c080e22001049681501003003081100380e07120803114030704000c82100100250790b00300c003110803080c2590501075031002c0c2015891100d0b0780b442a00280c820320303040000421a40650042c65603030302800070b4500d5995240103100c030111023601d150b803242c0e000c2041101c01c814683c500c103503a100380d014800980240b407400289080c011f500e4044070743d0400102440d04c4004484c07040014802041d124001034680000100792140408000c0d05040e298464522070400309510041181c20b84550142e800b600100010300500d0207105841c0075401c00c0b103030711001c0c02881c0241c079082c0c900d540740b000c41c00000350015403464101416026000408040340c5100b1441000c15541210104000192810700444001d14101d840507525028030502e10082c46828401c40f0429803003e4103030000da08400c400720104603100005001602d19 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 716352050 1250 716350800 716350807
    0x160c05070b03041103060f1303090f0303090e01090501120201030c030b1e1507171b06010e0714090a090b0105040902190e0315040f020d1209060206151305040f08 71
    0x9100d03010296000f64050042000b41d2180401030641e40c2c582900c541800300c43c039100203805c0041c85402142000e10034070745010301c0e03592128180384810070f64004401041c1c1910042c84000c003080000c500620410005025551414010103070748420114040d04140d02ca6540e030840c0c600a40115840380000f0b0202c500d0340703904081307408010400e50092489211045032010508003c41c081c0d40040390440c00c1c140317481c41c2101e80801d15500446401c0580c065043c0c04007407600c4140400c41c0207141c90488440307035142141e002400c5203c0d0b501c21000c10b03101400450b036a0349070a0200e10a03a0041c260000b03034041c0c83d40060795903015aa11120307010303000040c03468410802c100845200c60094a550729446513240801d5118440240300c43c0c100d030175090000380865800e030900d1500d2400582840daa082c100d1700ca6091100400300c00101048001d0303020403245a04004070341c0d118155081400c903440b1a84001039180002c8015110b03540d0319038020500748100601031200705a0301c031113036694 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 716353300 1250 716352050 716352059
    0x613030b0f010314010221130c0801020d06091b140d0606030e101e15030f05150106091a03180d1e0504050f012001020a020a1104090b160c0507 63
    0x1d2510090004458100448195034620b4005000799064012a80201d04003110681c410850f00800102040d50b0358201040d03030b602040d1002c2e003410180486800160b030310503000982405484c42d6030b0000d00d0030340c030b0142032a1180e51541c0c0382601040e1149401180d40c2680a02d8041d24002e001c0c20903006840d140c800100300350954094076100310584242c446081d02250044104c40003038424403003c07150f0301803003e860021030b03001d0f211642c10303a500d40000ca03450740c0f0781c441d544180039000c0300c0301da001840b405400001c0c40045401002c007460300c40c4c1d03041c0c10200c5003070f1480c0044a0a0288803400310210711a0358504041610490003007040340c601c4144100c00820710400242c0100c1c00f80158020321a00503c500110344c1918800751082401d0789010b80111000b401e422071185015441503004011088203000800c4080c1e01640184402003444c00c103c40300004030900b81d44541d15145c0400d0008400320301c0c10303174482c114121090865400c5101502e6600000b2401412402000e10124 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 716354550 1250 716353300 716353321
    0x10501080f011512080d09080a090e0a051b090a0b22170703020f041d07230a05010c1a01080d031811090604150902040806160e0613030b 60
    0x900c1e5081040090110202d10b0f49186000689070054400d80300c140342c0b800000c01c03008001800e940300e1502d000100402d254a0b4a0001e420200d04000018491502004090b0302c120105420501d0010304005504101d029006030520307510108140450101ea040c56036601c142004000705482c2d0b40d010303075400e006880c9140344100c00912414041e03a68401140031702003c03001c002001e11a10060003007078110780070480100254616290b10988920628920304000d21800f118491414020f107000c0e030804502c141c00031803642890180304216500419140e6034441d5134801c40e5403c3c2070040c5103c4140c03c2400600408007007065a250a500c00014002400907040d4180080e664003041074015803140705256408200d009040c0503507054035101103191180c1d00d10b0300f10000500000306085ca070032612644c850168840c10302543d0200381040100b4080c07109030b61103030401c02910748805c11044040c10480c01c0c0a562806424045403410300c01e60030310286002303141c01102000d440c0c0307040f11090 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 716355800 1250 716354550 716354563
    0x906020f0a110609060408072f01020106150801170304080a080c12040303020307030e03160306050105090a020306060a05180406080616031104230909160b0915030601020f01050108 79
    0x1000488081812181e41c2e400f2030a1070180200c07602900c016207842d12a0030300741d040030006172a41c2c100d844000c9d991103180c0c441d0041c00484401c0705c0c44c100c2a503000190231170f10b00754004619500c2d080301500710507601c6456103041d11165803035044074074429015985540034075040062144158001c045c1440707008809071100d00d42400c102e96011703074030141c0841280075074400200560f00900466002a006c2c480720305146401a084482c4401e8402e003003008124594002d890341d5503220300602c40c0342032039a0700a41c0708011300803e501e14104000442e1852060201d05020401e010804034030755844e0402c100b40116005209210b0320b0380b1645800c1c0c0702e43e8107650083e500030349184543c0c0418040d0223000c081d002042c0c5224101072401c0781d03c00008244452281541c032075038039a4000c50317540b40304490103404100010300d1001680d14455444050ba5001100c005009220700111035980e90002011891401100c0703460307480c0c910041c0e00e40001201d006108d94289000810f02da040029030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 716357050 1250 716355800 716355817
    0xf0627060302060a08090601050307060f081e070306031b05010221040e041a061e100c0b0c22050607290403120f0504020f19090c020d110d021f0906020f 67
    0x142d030108d9986200b01580c481c885d205400114100d00012107a2038001c100b829403110400001030845a110502c040d003020081341c0100100340c2e120700c00c1c0184280c14045508601c03400801084082c20500040d654018a240c0002c8a041140c03080460038802002e4030001e2107040703401c080500b894035040060000c01e0303000d80e0b401c9481c580090440e00d4004525800c90081c68483c0d43c450301054103121348405101c0c0c0c050280010b00000c00c0000306400002403040550448491300e50a50015003080300310091804c07011200482002c3c880359440004441041e54043d0355211450941c03c104079060340700d012012090212681040181a049694070121081207070302007005020044c8144101c540540b4065048602c41803103d94131308203551404142002251207003941340d6190300075015a803414480000680040756071046140d00301c034059000045005c09025400d0255900941c3c5041380404002c00b000e031800700074ac0c030ba400d070b83c40b911003d50000000c1d56145040b05103060f0507440780c5039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 716358300 1250 716357050 716357053
    0x105090f04031e231303082d0408012324190501030b0402070c121b0303170601031a0d02013608070302011e0210090b04060f0627060302060a0809 64
    0x1401200c100c003010841e50f14100001107280c5181c03d6480f00000364101150385000019401100000482c480000840ba50023000000e969141045401400c1d141c02d01582258031107031550340900307002ca140840750310001c3c0d0f551031901c550700401c819214810050140750030803031914190f0700c0f600c030484412083d90000e88050040000030b0013030000306c0c401c10402600060141600340031103617818418150301030141404500f200030740304640401030900c2d131049002c203060030b102040b44100d8860711980300d07000b42401c01c04514000c2c0d5130031010f08040c080307620500d0042d6800c003c5a0050b01400c001c885146440c9091900d20f0f584100745001040c0d4507070f4910268440040c140000007a130b002540e60603915140d465001c0c80b10b1808000540b0102025402845103e0002100b14814070354000e0080d0714508460606040000c205e54990754442426801d00a00340044100888180940c9540e500308005400f220304c0070760028622030300000e50040d000504540001d5000c40341c14089c0c4280d50 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 716359550 1250 716358300 716358347
    0x308041a040b090d0e0604121115070605090303040308041b0b0a0e03011a0f060a05070b1e13120f020102070507152601140d0606061101140105090f04031e 68
    0x113070954040d615090903030350103442004140302000003e008100e080b0301c9400d200c003448070300d02c00003866219440c04070304062030080303002010700500c0c1c094241c120403041c2c003030740c82c5d800c1c81c0e100200a410014006000807001e01c0c8140503440b010f46000000b4002092490344401e4401c200900d8800d08141081c40b941c20f040c0810078248182154008120f8000e01c40510741110109100700b6420102001781404428440040451424241e09218402c0107090050300748403601290002c1c04d016141d40100000c86d0550310008000c0071010030f1856140c1480480c004000508a01a01c51a40020854080c1030b000180399420619a0306003030005807245880c0a102005441c4007040419034602a2246480104000d12000b880c003070542d00c0142960304141c00c540c9450003503485c20762004000034280c00203248070a0085c400c5c04041c080308803034858136525060000c1e075250006881c021124030544045400c1601030024220002d1450f443c0c11059015104003510500340286074019070030025 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 716360800 1250 716359550 716359573
    0xc01170115080c130605030703180f0201050906090d0507080c030610050405061f0804060513050c04020c01060f120203070e0c0315040204120803060418050a0308041a040b09 76
    0x142809050700d1481080c40708240041d102240c0198028220507900c000800c54540e0f8240101c41d0080544499280d04d540d030300713201100804948030044440d00c000a10b28181c00061500c0c201c40500701c2d02480e040ba1242400d03400100f007807250001140d48010000e085800301703d808218502124095025190250001ba0905445010450320903090006c8180d05000500d0280d00c2075421410190015100140141151484044448401020629180c100310811101d801440d500c24251445018200316940c0c03056035850780912100c0c4035580205440010300d000754807a0b00204102540849296a07170500d280c007080700300c0310a9000b4091100c000c00c0d60404003510f540600c07070b82c0790014510740d1003111406024040f2a28180d12640821000035181c1b40d00218081281c01007042d02c1d074900302182044215001160244a544070498142002c11004a40900146d401d400c1c442ca0580d1240703000780d1601d07003050110181000000a000500010090540c46918800100e5a011001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 716362050 1250 716360800 716360837
    0x10e06011a0307031812020303190608031c0b0a060906020c062106010c0b07202d100f0f0e0604050304150e0d0501091205070c0b03090f010e0c01 64
    0x1101814001d090040000c50ba02d644680d1120841100c09480000396001e03542e500740729070090284100060b400441407000710341043d1040e084495840b0010002d03e4a8009081e881f401075119111070484608086800c000c099040551400350003440d1500e4982c40c2c0a010380380a038540184c0b001031060390440c21440c02d2000480b50101c21141d100746140264055400e1503400007444681007080100e8480001600304000500030010341d00c0380007140f1519403800420441c8480d9802e83e5600070300c070005521208101c401071070404ca0010882010882103118901043c1d859800145807170b060b015050f0a42c984d00240311001100030901010a91894141e40d0b90000d940243c511b800070003003080320800c42d00c00c500c1035262074100098280c0246001401c1595400380c140c401d0703511500d144041004604074403c00026500307142e0304002c180c0d00d902180521038042d11241c0076000021406000d42088040140c2c3d00c680c000707202081c2d00440d880d40390051402c449011880e80d500c0c60410510 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 716363300 1250 716362050 716362079
    0x806042003060105150c010603060c2c0108180304080105060117060a0e1003021903060c020d0504060c031e0e0f010309030c08030417030a060609060509031009060b0a08010e0601 78
    0x500401035642440208200501d80c44019041c0d08020042e1b1224032400f8000c1c04c00a5006501c0003501820b80b070070240050364030700f254a0802408004400000742040015003000d40c0070b182c020680d6640f05220407510110b1a2444810708c03001c5000070340300005400c4144111000c1e07a40800800f040304c20291460f409481342d03903101105000c1406103040d40c41d412a4070409510402944a0362a000320340c502b191343c00c2088031380d03014040900501541d4040d41100c00120700c028403610002e140000d01d40d00681c001c060401404090110505110712400c2c180c8051843d80c103c11124034410150158003203200c080d01503101f000c920340403503010b40300b203c1249405844010150680b5519200250700042044540340101c035028036822000e44042e610070030004400180030740c10b0800107091001d895201804010007004a00b05a1300e002c01c10161900000b5800305696035949400c8000d403443c103400341c0d0403450b115400280980150011500041e00c001030314400c1e602c44040412070704 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 716364550 1250 716363300 716363363
    0x1011041a0408011a0d061113090207061401060903030f020703080d020d11040b0d05061201060b0a080a0522060f1b0e030a1703070309230607020a050601140613080604 73
    0x68101718420040741058121800e11014002c0681c904014891300b01600c0003603401150b941c55000c94003c041001b1803003005410000310899000700e616040000b0461601c80c04020f00304280d000480d40300034020030242c00a19403201c0d0782c41e20ac1d00c0c5084060000e4126280b0001080c1c1003c41c03103403245501c9022a03003560700e200c0316a4a80420043c0f000041c20014042c3d5070040009000e050100c0c1c028414003020309001075089980d1100d88030014403140703025000b090f0711171030310080c4040c01c00004194141c511102c00a02c000a0040c02d012005040302e80243c0445418010210142e2440c0e0145054014040d102d4040000c80081815074a1601050003450121040c0402c1024111100910b600007010f15000c10119a1a910040710075008030243c80d400c44800b115015141d0103000712680820b841c4024800107245454003075440006120f03000c048903030340054400b2038486104458648841405141c0743c42c1d0350340d82159540c1c504070b4068070314202c400c4040d04401c001c03529010080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 716365800 1250 716364550 716364559
    0x2122503110d0e03070b09030a080901060b03010329070203040f0e0c03040f0c030602040906030b0903030708071d0315090c0904050307031d130b10050702031011041a0408011a 77
    0x50340814040d030040807090f0b0340800d644018031000c0001100c40031910311a510f0440959160b40100d00b000e801e0550146c0242550390616800b40400c441c048180c0741141c0d0005c3c807040310140380d0401c0f03500240c00302c00180c20500701c8004002c180b5800200030300c101e420314504441c15a5a4403640340440c4020389941c0451001007000c01c001c59824160390324200e0084040c003180f41d40e00c0d07465000f260700076400240d00c43c1c1c84a01c10400d11007a1520715030300080d200003440c03441c541900001c1859200900070014402e17000010300c03c400304803d420903c440040c0490703181808070407481d40925001c4600740c4003441214401c03c3c89042c10242e060040d64072800440c00c00c801e9a60940b5109003140309031050701e4101c00280c00b035a80e2000301d040d0080b01c990300003803010085414001c072400c0860801045c0117080140c0740c016100061907070040140f00c0030000f9943c0c1d0002454490f403103240d114400300810112246c2440392004020011100094000c000b044904404111014110280c15501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 716366906 1106 716365800 716365807
    0x60b040906150f0e010315050a03051f060812281707080105151e030c0a09140a090e0a12020c030c0f0d0f060212250311 53
    0x41c07040b10f01d4004a4000001e4001c0c15580304400c07110f04143c1d13611a00c0c5081d0f221030081c4030103814001d14503441141c0c1e07410441d0340c8108070240d40e0003080c00030070700c140c08066034442c1804540004002d010003811441c60f25980303801c01100981020200440c940c00c2e10341d00845003828850315204c161011802c21b011401c0314100a001600b40101c81005001d03554500c00800e5074100078240c440d0386c1e103036048900382e543c9280640001c0c654001005000c00e124240d0007400119806a07230b41c1c00307015a51406c0007030200310800100c0d08108111800c0c1b240e4901504250844920141140c10b52102560b070402401011134404006800810440c2c20a05e020b1080581c0f2030421030f40b10022508000000b000c8590300e05000b0980a99040030104000030398041c0c42082440304c10b0a5158501403e03801410300050306030854050050751440503850291103000044650302c18003604 = true := by decide +kernel

theorem cover : BRFrame.Cov 716187050 716366906 := by
  have h0 := BRFrame.cov_init 716187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 716187050 ≤ n) (h2 : n < 716366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
