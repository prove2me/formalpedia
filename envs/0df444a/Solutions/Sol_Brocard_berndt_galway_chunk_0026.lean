-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0026
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:25:36.707664+00:00
-- url     : https://prove2.me/submissions/c22e662a-8339-4c6e-99a9-48110fd0511a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 4496410 ≤ n < 4676266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 4497660 1250 4496410 4496441
    0x405040b150d060f05060315010302130911040e0d02070807120b0c0c01020d060302040501140a05040b0112180b0603070e01090f0906020a03050a05071107090504030e0a08070302030c0105030910 85
    0x50442c049a054861540c0910030b0f60b40020f107a0038035200305490108030810807004408001c00601c010380718884418503556a03c60085204d400920305070309075014841c5401d03046480c0c00e0120355014000909070254412540985001e1500c421000380c88950600401c0003100100b039138440094080c0d41e420340d01c80c415200c0941000054a02a42645e20048071003030100d0b2200400d100354030340b42c40703028010092980100030a08428020a04100051040303506c210390303442c82116103034000c03841007020124140d0108113030213120044544c050f201190680b6010011000603480382000240e2205540181c0c2c00b0507100d03840c0403c60000740150030503044020342c540319984002000c0340041c1c1524206a10003080515150140c00c0403110000c200c42d0400182001d20344205d203010684e101070304d1002c3c60100380340d555810181d540901030081a50840c100074400240c1c0803005c00e815065030710803401d5a0007002503200442d030900040e540c0e648a90000b001c500840025540560195a09200d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 4498910 1250 4497660 4497679
    0xe060a080604050703030305070f0e0f06040f06030509070503030412140a0c03050d080a0506010507060e03071e0606050612060906030a06060b09040501080a050303040227010b07020405060405040b15 87
    0x100c0038184081524100d070760354002d00080c4201500f501a2960284451604104911844000508510b0ae50198501a4101c682980817648600044070040c041c0441d5100119903030703041c002c000301811222440705010760440030481b86008000c079812071b00c2c4021499030802c20358881029000e08110002010f2180c038401d07a001036000c52207000150300a5010305134103660803001503c2030000500500032289800b00708515a0f8000d020303180042d03081075001500d60a05200c0c1e070314600c68031402416100c0c900a280c203400001d020810176440c419042806959901d03000e01c011402850805025100c180000404c0b6050000d1026440328000b000c403100061a03071120000c490841d002807401070000241d4400742e0505004072401010000014620340e1882d4948075100d0001800080c85852078044140700c04d0512011007160040d50500d0300c2440d603540c07001425560180c1c100300d0049003070030700060301481c140c85814412030b00017003000e1290391510341c034102e2220110f154641c04901070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 4500160 1250 4498910 4498919
    0x60318010903050c15060102070b13080307050f07080606010905040902130504030e030c12030a0302030712020a02071d040b060609040e0316020f09070909021804020a03060513060308040e060a 84
    0x24025074441c24025207031a9035452070704503424101504202200c4801580d181408540c0c0d030b0000d14401210101d094040d12040e404c40c588450f0300141d0b021b06002e10000c00c003082880b001007454501001d40340f0448416917500c0c0d5130a9140d003000c60345035021401640040200d41080d030001c426042c40105110300c603840c40e014080403241c1c240d5068001850b8a070085030035003420886620b920720115491162212908c0070103035030b440f45140d91410581c000c00803c0da1103001d040760340c412000109041d520f5100c0c40b03c0007035640c2c1d024401d21403004940c1c1c1002c800f207101017160781d0050340c214441d209030b0b5a03400c05000d084d6124402e40ba8026a03a8810b00b0709102d800d1000d1705030110040085100748089004106100d403074020f05074860390f04041409005900080348904a0b00383e54000b43c0c035410900305286c010500d035040c0680107400060b0603c82c0070b50541c400c90a4071000c64051950850441021080b180c0a000c02004031004004c10f0001449140c04c190740140e008118029482d03d9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 4501410 1250 4500160 4500163
    0x40b0405040303051807080c130603020306010e09160501020c1005090406170d0203030903030a1a06040b03070305100b070206070c0504020a020303180118020f0103090605100501090504050103020d02060318 90
    0x22a002e400003507881051007404824a00040126480240180181800c00c103459450b411010303592842080d00a04e64031079049950010401541c000f015140150380d20201c41c18034160841e01100203002d003281c441240d4128011140070307500d060380140074071410380c4140090034801900c208203101040c4121405076460f4040c10000d4440011311102c0c14000315034851600440b40d800406541003482004007100d4004240daa006c000f1902c0401c0c840d090300610440d03580b001c2c040e690000350025000c2052001c580041d03000d800143c1d800c2100b5075075440d1780d041140701406580715002040000202500e494000b81403c0c074020340d0000421a9240002002c070f0b0b1202e050580944c0002c400c12240308682c00070242807481680081c080d0841c1c0c03009621410041e00402032149451a40c0e0345400e9101c3e6200c45d0b800b0b40c1c400070401040c14001c00c15000b0896501c0b565000511040010900b4205406014101da0b401390010305600003550810030180c1000340008a15840407100341c916400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 4502660 1250 4501410 4501421
    0x60f0917010e01050109050f04020d0c0e0a020304050c090402090703020c030904020a0c03020709020405060a081305010f0501050f0307080303010e1305060106121805061501090e0115020d1407020609040b04 90
    0x2204400001c0300300b5859915429910305a01076a5058680b10400c03410040c10101ca41d4802e60460780000420850300c0c0040c13402c800d40c0c1006480c042d401c400c128504209500850166003d0022105200f4046080001058049400940041b071030004114843d0107500544081d40b1b031503080e242000c1106001c1f41c12604804603140008540203d072070241501806001c01824410000b94605810040031070718511030801881c00300f08901000500c00e8100909041100da4010028042e01078250500b201a20082c003403d80b10703c841001c0306003e454002400340490324500091811071b0710b001540c00404100030118002d00303440c0340901c000598140002e5000e0050754a40410000f45160007004549010010445099058102ca4007045001641681c0120204540e440104466004a80d480c080d94000b40c0a10018400031030200490324901c080392150303500700c584020fa81729040710b1801c0300c1d204800040000b04418400344c18824020b02500c14064008520804403402150881e00e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 4503910 1250 4502660 4502699
    0x70c080705061f030f02010e040f150302090108010213030b06010c080706060612020702010203030a0906020c1b03060c0901090308070206041505030601030e0303090d08130503040308180d0c060f09 86
    0x1c00c407008000000a1285400303c070750440340d03404900d40d4250f560302c07885e000c890b200103414005404490a81640d03242c04c140c031900d003482070030b002410020003243c18000c102c0c0402c030b05c40d62511001040e034581c140300f91011200040074640785203241d500c038814080b101503e058104100d07034100c400490071140040400302e2107208009107540c5000402410340b01d0114090a095004024010160381e00000b5241c000002c02c000081ca18051724021000b03104410482d021401020440050004c6502d1001700010381a01600d1040d5948101c03028280b04000d000b0b030208014034001c0c0702103101040600a02440504010301d810b86408882d10282940181c90700090000001c0103c20b59040c011541c024030450015421402c2008401d0746405a00b1140710411407200002440000644107904a40e600324054a9840d905c90500030785961000c214204140c04141610270681040120010541d410168603162581800d0013110701b01280d404450400101030004100480d04c00340800d00310 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 4505160 1250 4503910 4503913
    0x4050403050d050903041508060d05070602010b0301050a020304050a2406090504030e090405060c0a0201020d05010b2805030609040201030b030609061b030105030a060b010c05030a080103060605030109020d0209070c080705 97
    0x48540220341c2d001c1c1c0740010914011034000740410400c2c1810391620090800807410280c813036030342d0f401c0410145032a20a016101d8483c1c200002a02501076001c4503800c9001d5000b0b00c819914094003200360310041d50000e150f41c2c050105040854200c40c0091880c400e94034904144120300ca401e5826103a00e074101055069450051000305604544200c44009051b0380c008110700e0207441c2d081e1a184020099202681c0c0000e500301c94074802e50440b40d1030314020342d08010710350b11003085001507000080d01081d102480000d00c54451412102da06500b501640d80c10b15595a0405201210340040c2c4120305058903120260101c2d502840900d20412078072004200a00d000c00300d20340105440381201c01800f50401c014006501d000c039000560a80000011403844442c00c01210301100303181002c0c140c0c0c0800724104003040d602c04003850403a401002d091021584030360416080390048040294400c2c4040d8940c0c0042c02c01140e010b6004505060070101d845d16a01c804203d035000d4541294030707 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 4506410 1250 4505160 4505167
    0x402030a08030c040f080c090a0506030c040207060b01080709080303061c050d080417090f120715030203010305100204050303070303050a020c01020a020105060907020f061b090d06020d0b06030c0f0c0307020405040305 95
    0x14040c0c0018000910186c4010581680654042044090094100a10240c4a400007500c944007040340e0348a02d20007910441d640c6400d41040ca0003403010030301c030390300044502e0007240500344180101c034251030368140918910740307a80080010807049040141070140c11220010003080e030074840c03c0328a074403039143c500f07061905282020f007407070814890010002050040f845641c40c1c1020b10007900b0800d640d0084040140030f00f55240c59440e80c007212004090002e040511a416009141242e02c694200c1d0024034201040d4810390103640180c5406034814808580840d110b030b04030710f03082003041000514000c60030400310309a0340400c00074030150303441e40103010481c00d10940c1d842d44102d17144003030203501c96900850f50300c7e004054044401c004505030711b844122803c1003210360100006058503898881481e2507000b0b500301501d009601854240450803e00703010044922401d071003044d0901c1c0082004181c02b00d500409508120b81c4400c0c00f00d2001612240300c0c1b0350165020b51151500c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 4507660 1250 4506410 4506419
    0x10b130c08060109082109060a020703050c0411030a0b010306050604060e011205061507110a030b040506090609120a0203070c0e190c020309040b01021603030f030b0105040f0902030402030a08030c04 87
    0x71a8014003240d040145160301000740d0344021640c00c6500313402e01041400751200c05e03407040c000d0065101d441d50007c0000741c142c0c00c158001650a040384d100c3c1068030020f20b0000204021074403030b12640400e101e0308000041042c411a4049c20140c0b605050002d80382d62148046503a980003500500042800c00100240541c0c01c58542d40c1c2c000b04440003846145041404120404071444001c0b40422002c0365060801501e84140c00000307a004e0b100010352566820b142e41e0b003076000c2d80c060ba050f01440c07000c10320480000c03600300d2241c4c10060003005400c184000d401c0050f0702103d6075000314082800010700290705085410f000340107041c8041c41c035080c45000304030000b40d841150304103d8030f40307100c45d98a80c2c2c020082d00d120341e0045400003100d4101000503810266442c00da4403441c0d45c544004000c254000a018811101c01c0c2e5081100c0126840151558402e5001d00740c45000443c008011140c010b40041d64401d20240588034481d080c0d80c2c40ca6615002a9000d251407840840e0920 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 4508910 1250 4507660 4507667
    0xf060907081204120b0c040801110d050711060408030601180e040204140f2d04060903030c0c020609040222030807020103050c030105010806090705041a03060a050613060e03010b130c 80
    0x102c0303954150391454a042c0c80c00c1c41483c121660000003c0002030601c000484c1001c0c2d00c401e175402000340800900c801032070103d500e07449611002000c01c07000c3c034202c08201581e04c1840c0d1880451031000c02420162200c2c0c5540701c05410080156041156840c121281d0b0383c40c2c455418000c1040e41c4111190303061903c104020303100c1c00c11290f4540407034402040690b405000c05281c00c17140015030a94100f209424509120b0f10705440060b90038081e40030711007000310b15840750325030760300983e0104030704280c03502c0481e9404183d607c080e41c480c00500030f071300ca01e14081d0b0040c410f5051310340045046141041c00c41c0030003c07140e8025100301201107800700c03c0d941c02d4014a0340c0b00e211811224a1581410700203064060b002d0115801509484001640d982c01502214007401c00c000140d66044128031604e20158000c8035000d0040000304800149420a40d0540e1280c44000130407880d11814072500f110181d4071580d80c1350b030664a0f0f542d0200c0030b8840c1c1140485170702d4481404180403110480c0507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 4510160 1250 4508910 4508923
    0x5090f010626031c0c0509090c070b0a050606040501030e011d0708070603021e0a0c02030714041802030c0603100510030509010c0f0504050111070906080106030c06030c020a02010e01020f06090708 86
    0x1c1c0407038004004000030003500c100d841803480c118a00002d1700b205c02d018201d50b180100280c20350400c80c1e030f03400d00ca00001a0360107840c015100d0b002c42a01580c42005810640d0010389032107400403010310080c09198000c1d002440c04c000b10703000004046100080e6444651707155103201500b038021280a000410044c40898043e00060409518004025051824108a041a040d2512008104c000c0170038800d1a40c107068680081c212008241c441d8a01d0b803154120308100303445980740001031030007590910110c054060300100641081d201030350a00c850744c0d100034500450300070010004074031541d4007409d600800280e9980000c543c0f500440280c21207010500311024068140c0d80000381c0f503406001c031019503c0a2030301c11410a00c2c0c0076002d02c1e01c00207420104080c0d062400c00f16554005502c44011a4060f02e0040d00c0c02e913131940c0a40842e075602501d0801030f00085403000241d401448082648201803046444100200c02d100342048802d8136240015000a1401c00801004202d103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 4511410 1250 4510160 4510229
    0x12010b091f020703020d02030f010509010501090605090f0604090c03050d02010506040e01090c0501050a0509030102040311030c10090e04080909190b012606010201021306030c02060708010305030a0305090f0106 92
    0x64200104032107030040d541c0c44207440f000740b14443d65041101103490030b102030343e04025884001e100700d04000e00b01c076001c0c1030240690360f0010303d08a4009075510b404d0a40c1c0d401402c65054448943c0c5170081404040d0040f0801035035100040000000001c4003008035406400c0d0513400000c0c81d040c22410041581c0c20410404400e0303061031042d4010981036907090b0202c3d0000d0814036583d201c0c020040c0da190040075284c1e541544089000414044041140c0403404404c5003620001c490366400c001070b001c0142c6c02c4c0400070340304150901021900c1e50803150410701036070046060a03504000600da000c0d04031601c514545031350300030f42d0030300d5828014050760365000d08000b000c281000c00709900c00c174103100c600442d401c000700100d50964000e41c11034a4000701d008009035415142d00002d80030304081400c100040c89a4000110594490349295050360362140243d458403002d048228060305018003a0041c502404840c00b9988009200d140700410021fa07025001c41d07483e101d040e621140d0480e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 4512660 1250 4511410 4511449
    0x170103030507031b11010e0111010c0c020a0e010b0a051c0507111506030309130e030a02030a02060108030f09090a060b04080d14090f010c03050d06170c01020706050313030512010b09 80
    0x30316400140f10170040e091010080c40e11039940d041c200012280e207200400b0942d40d40d480c220201d01455031100f0004d11140c000e0f50040342c1165152000c41003071400744540c2541903018401501c0041c4203400400807000960104c4011010005400040322420354201c8041501c038001610718a07020711180d072020a01e1441c0458500c0c0802c0807036140e200d0095418440c0c01c2c1d0100a85a001072a07028010807041041203a032101e040d00c202070750340c0e405517400703002600c1910000180b81c040001201c485103440e85816040079002418003206080240c10703400015201e01004c20003c6601c805080204140801002030000c4610050031003844040c0a854506c0d0400402110741c503106280c0b03e46103002e18213440c0901c40ca040407225070080300e0302083c4003828041d001580400030504140030124050964107107030400e50059039508401d10505c40460410310000741491a50b0350101c0c0c84600034100f03145440110162070084d10401d03005a04809800f140707052041c14003015009500f5210070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 4513910 1250 4512660 4512707
    0x4031401050c1e040b03040501020306011701050a050409030509100e12070b0304020607080d090b0a06050d03020a03110c041d060601110307020405190507020105010e0c04030305040e0717010303050703 88
    0x40c0440142c0c8121201490344140c204243c00d03a0101c05030444d40103001c4802010784034200b524105020303520942d00c0b140041e00c000c100d0284a068880702904a403002403040169610744400d01c00030342000702c420f505212040c88840c6039921008880740000b100c40da5200030719400c2c0307410007103d650074540ca18545c3d80410f40a020750010f01003166080f84d011104984c460a0038500420140700d000903155045084c840080200212910428050030380124280051500c0301c1c10301800c0d21303840f000a401139125032031605c0401d001c1c440310900d0b511207400f91041c2240c180040703001e1764040f4120300242540110384004900c814060075801c110240f8110365042c442c00411a034034020410064841d9513214003262280070403040d800c40400080301c0a11181c03504601c0640201024810307a1509001e440c00078688440f05000c44083d00d0b410788605040c14207181e0040064000100700c179092000f140440354080c071180ea0514000d43c070075503e055556890345402450300743c00d400c08071600b40d0402c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 4515160 1250 4513910 4513921
    0x90b0108060d06060308070609060507080603030a0c02030c030f06040b1003050709050703060e1303030b0105130303030902030c030601031b050103060605040905040c050a06111203090d080a09050d050403140105 92
    0x8080c1508107108a480329825a11402c190f40240040e40c4024400c0c00001948402c0041640100380100d01a41082206541e0304a040d20040300c101c9403030381e168104000030121a805070300340c908041d0018046405480030040420307c0c0010b000001445540035104000c104030407040c40c00c0d48404c80500c9442d58900d5540d640e80e4031100d50246224294543c00042c03040b61007648104010407020301c050541d401d01900302e803542454080d0035400039003030503000c0910b54080d44c111500f0340c02000c106140207185440031402090380c0f0404136854051000440741d1644d003084070744e010394040d5015002c920000d1142200b0140540e00031340c10300d03042c17101c10040a9000b00c1a182280c05035400441c0940c4c0303030324200001d03001c6504019403200740009c2c0840d05a502c05807001d04133040e002190200581d06041c0d5040b0b0104482181a80c0e02c0300381c3d81c01c0300758800c0f07100c160003c000200100342401540e4031207080008480010002590120701041030281c4180082403200c1500001c02031414403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 4516410 1250 4515160 4515167
    0x80705010806060a1407030c1a01050105030606070201030603050307050606090f09031b010207050703060507090906050a060f1403011d010b0319051803040902131d01050103090303061d0709090b01 86
    0x4103018801c00f0302154100e28140200000d0f0a40f011140010b55504001d14000e00036245130241640c2e2410810740c031080180800d00114142c92058540505640d40c01c1c0400c070703199214850403810181c449800000140f0200301420009101c2c0000c0c22712458030406102d40340340000c0504c02961422010f000c1400d00100840e07400004a0440c0942c09240c80701c3c0b240648141c441c0206a1f02c0354040000c14002c0c1903228034091041c590742d40d1600303075a864503641956214040d10384d00c0b6008040c10403125000d40500007001d9158141419990204092042140c0003603001018150030b1103445504201c920189501503c2d0703041c455411400e0400000e1000c40384400e01105640c0d0350404144e0700c41d1314440c80449010300303800b16130740d0313036143c500b444040d40002080c0340441e04640e80c040f038010409580e40c600d29622140d2241543c0c41c081c011400741c000d000056040c50b9640001244402140c0c4040d21032400c00300a403146030034070400003010384e11143e0241101900d010441d0780543e1340b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 4517660 1250 4516410 4516427
    0x60306040b07031808160b061212030604061205030a020114070f0c11030a03020c030c04181502070210030504030e031603030e0307090501060809011401030b0c0c010f0606050d0608070501 82
    0x429240005040d0420140d0714540c005500000d4003c920100304001110b50780300c071880c4400e00c01c81002c121903c2369010f100c210b2402482e030344000c3c0c1102043c0c0000400c40c0d4050356010b0301c010f101040e070542e54000031800001c5d4274015500d54100049442038160240222507005080202c00e421602d0120001041c000c25485c02e0801c20800310000e4040c02411031620048080003819204000e40901c2d0180d921001c95000d24024065540d0510040c07a0612802c481034074882108800784c0d0319036079651500c09980f26400005942400404090b031130710307600d09203030340c902d07850028640c1881c0c100546103c1c0c07550000c0d032099200304030346203040490100741c00c00c8945c58100403101c3c0031400000303400c2c030508e40c0151400c00e00e84400020319641c0903030160b0080c9002c0000b00030b10101c42541502c404004d01020b850381007128007003a0640c907580d00400a6000341c1000180c048810252102602c0c060381c030917000074802203090280554148141d00c01080002c005103691860540007801c600e8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 4518910 1250 4517660 4517671
    0x3090b070302010902120a05070f030201170c0c01090b0a050609010b09040b030a0602030a050115050c0318030a06050a02091206060d0b0606070c0303050a030c020105090a080a020a020901030b01030b060306040b 92
    0x6402040300001c0600035086500e8903903005280b044800341030343c907490741d800d21840c1c00e4901b88541800001d88180e10058a403d40f50103946880d43d0741c072a008040000301000d401035104400c02c01000d25100000c0c0b007410390031446155502241e05145900700192207001d011503104405640040182059590844007114420359020828420200000c0c0c201a40d00030b010702000e000008201050f12180e002d181601d5203454041500182e8003400c0b5030501400e042c5038116030007041007406110124080c0c0c410240001c003103072500d00c110741c0c440d42507400a803a041000c94020514141c0c500d0555210b034842e038214001070035545041c1d0001a03d02e00203034405004640102d01086060f05c850741107e15264101100408a6940789030040095020a120500003450b200c00352a9181c4180038450007589442c5c02041403200d65155620103500c210014800e512685441800586450360010b0003580242c04411076036156050240911000130b20082c401c0d00400204000113008140301078100c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 4520160 1250 4518910 4518929
    0x51603030b0604030b010e010302040e0a0302060103110a03060c030e0705010320070303060510050702100503010e070e0109080d020609010e01050403090612060905010905151909020717040f06090b04030309 90
    0x1428101c0c0407801c980315a40000e8044c8181200108084503501c820504980c4250b4042009201e0007044030340f42c441400c0000c005820810042000c1188541d00621039100200f030146982d42d46d03920507044469907604003010075140d40c0c111108202c1481000000d04081c2014014400c403142e400801301c0c6143d140c500712040114800c01458480e03071242c0c02170f21001d00b07901000b080700c940c0908a90450078003280300782c1003d44218074444c03090083e40c0c100c408020090300c6640303441d07006072142c0b201d1040060422056000000d6150b00c100026541c0070a150054010343c107010f0101c40c02d6071603007000703524503a05010600001991100c605004c5510510300307445103481c50452507000d0101c1d1f9205801042c10b0a001181c17041e42544140d0190460725940c08800115000b4485000a40d00b060854004140020009408907030020b00085208001510381660407241008040d0825000440200e071120018004039800204500c040d04103071150070300b4035181d6640281003015a000e00c0700c1c04c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 4521410 1250 4520160 4520171
    0x29030907030206040806090105011d0c16080313050c09040305120924010e060a0312050f07050601080a031409090103020607050a020301060b18090c070605220506010303030b0105160303 81
    0x40800510002025503801030515540c0e035590907005545071410f403886800f951a000c00020345440c01c031828401200000c079202015a5007400d800c6050300844642070240480c54169400500010025441340782031001039405170400d8140707185441c8503010703a075004004d0715081c80f0100b6002000c2d0b5026804c01560045607954641629007800101134040f01110802c83e083d024075010220b40c0340c1618148a03521620755141020003c0d01c00d05444041e0825040000e18403d1502c500001c0260072801c044c810314002c070f141c1d1406e10b884400d90099100750040e6401400b0950310483d5010a43c2603500c00c03d052081036000200e00b0f102c1880f0085c0710380d40000d82d0008202c4140b1104c0006900100204803465840450990960200b03002e8200700480c0100d182d11440e20f074030083c4c001c41c2c0c00501d55052070015510140140006001c144413140e24110800c44e41048484001c0114402e1020303116035455880e026003075808802580d03051007024008011031400280c040c0c00c802c0e81524001c07130b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 4522660 1250 4521410 4521421
    0x90a0e0c0c07030b070e0d0308010e070512040c050108060102030408150406060305010510060e01020d09051203190201150f03020d0b0403030209030a060902090709050d08030403030204150201090302072903 90
    0x100c0d20954084078010301450780008280040c0e00b40d030510401070340d20b031280b040c0348201c1088200300700898024042031001005010081d0000441c903840036250822501d0250011110921032004403011140800101e40500455078401e1440d038024200b80005c0d42014140106c2580381c20b01c2040030003d4242c40400181072102070f8100200440d04039008000c14204000f121003c085140600004101d940300c40c900c4ca5480050380080d58051035641a20080c01c103420040c1c0905c3c05500e02641d03200602c54902e2940b441060005402c3c0e280d00001240100c5000004c480c207029401804111003601c5d00b0001b40c0c0f620401d019420f0742c070005c51b0644d0703540c62400b98028010b48107003c1d0180b06140b070300010807081e640207408584c021a0383c02034961f22031004031a5414603024898100648109003400100b050000d1a04148203040c09070038103840c0c50400d100801a26046801070f91030311303400d83c01e060f01440904064503034807407071020545185903a916100704d007508015204100000048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 4523910 1250 4522660 4522681
    0x30602030c2107020d08160e030a0803010b07060b030705010903060525020a0c080106061e020106050310050a050a0b01050f07060902030d0206180102040602190f0204051614090a0e 79
    0x205054019038034003003408901c0980010590080f2500c101610071078051134481c50140c1d140500c160200d03508003600356000d0030116103880c003a0010b1501031064158100c0024204405140a003451043c1c4a4940c0110b09000040d520f125441500039005a5410700599074800d00240540c1e402000c0400d0f1912040b541151104d45d11010418270303506140c2105089074085400c44482e80103141ca000000c0c1c503031020300d00300c807094498080820400f41c09105a4115602500d0250039580000102079030345002181c204041d484009845c03903500d500b000340d15606071003281e4000000400c02c201c50942a40043d1861084004e041d101e90004107008003008110740146031013590107010344209240c9000c000c0c1d0b840c001030b280a2580780360280c80540c03001c8140b085e05c3c12107115a0051840c0c0444400d060140580c0060640d0485080101e010250b152400307441d00036149040030607040514280001e07e071401401d200c042c9008100a00b0b9403c2c5d45000c507074000e403504a107040203e6114000c482 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 4525160 1250 4523910 4523917
    0x7050d06090204090c050c0a0308100e090c10030b01020a081b0109060203070206060108040812040804050301150f0b1e0903010e0d02030c0c0a051e15070c03050c01030204030c030602030c 82
    0x48228102640818065440d4000d042100c0291405104034490250103644500414600001640c00340301d4540c04648141c00705a0000c95800542001c2902d64541c41c3d51030358120b5600032294405282640c040c184000c0c2108800310501d820440e5090220000f074541400e004081c000f07040c0803800544100c0301e81a01340c030b4011401e000300000c028610b400d001940003102d000340940142d500040c1c095006583d02d83c4503540c80014903141008401102c000c00501031b00603141001c040c0404500c1d034038244035200000180c00501e4590514168507907070740000541011075101000d0101d1040201403d0040c094041d40211642e1104540c83c003281c0102442c0d400844140b10304601400c509070080000e00d4a03102e0306d01500c45c0720091320203201444005200d001d801c000b98440d17009414848081001c0b000308010541d207200c1c81c41c1d91400781580c000c40420b54044002c030600f001000380130010f0350141c4900b030a055082c1440d42c3c446112885032884041c2c40f0540000000780c0c2821680110f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 4526410 1250 4525160 4525177
    0x10e0301090b040c050f010512040807020a06050c100209030d0c0f0204020324040501030b0601030207060618021b0f120a02010605060d0504030813120e01020a12020606010206010f030b01030201080705 88
    0x308054801c1e810040310075002540e0039100f804444001003141d091910f20704558003c10303100d90b4070f868100c00390b40e014404000d2054030703e04828132203600141c0e61401900003d050a5482d00d8035107801a0300e003800c044010681c03a0701c0c18810031035a921520080703032050240e42c060512040340f25850030302000e6040c0400d0b000390700520000800000c02d05d4901c0b6038466520b001c0781c50300004210000d0104a610a00000e0262480c0d10001000f561203500100280b905c03641004c5204c513620380c0c0d0011004d0b0f401b21510b07400703500860422982c081c1ca2103441c20084d00d24000344044124201c1c215254030000280300c4000400144007003225000350002002424041d003000c2e40e400059440703000031b00cbd0584045001508102c041200901006440100940c0100768461290b80d00c1d801901d0305900600b4550540c004c0030152000310b81482d1080c11000d4068021300040e2810400083c1040c105030800d589840e0900000e0010510203240c25066a9081c02d210020351103021090f038060145005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 4527660 1250 4526410 4526413
    0x1050a05060f0f0406081002071e0503030a020c0307021008090c0301050c030a02070c0f0305030a1409010e0f040905120c060f01060504060503070302070501020d060915030803060409020d0506010303020114010905070e0906010e03 100
    0x3a584100c7ea91580141200e40c00340101c80010429070208102181c04010083d00701c1d8010310100303c114440c0c0d4000c2c00040d0b00801103038605030050340130400d8840940304903800305807501c04001c0464814040000041821002000580b8041c24154030f94040501035032003103076010480104104c0c11070f1200d00038007040c0d4980c1400342c1e0340346420350342c0707070b128190b40d1000980c240b10001500d1403d400340c803244c003416140e1488040341070090003081409071100390b92160f103840c80200868070038040c00c1e84041e07407018070700d03a5600482401450040007030969804001d040c03004200150b07101d8141c0b030a480c00c0740b0b07100c2d5036a12003820031006805600e802800551001484641060007075211504881340031900b030144024951000882e2255444080d01940b01000080c0c801e00d015403000c1c5589200030101c01d11800151a0507141c03c10981007180580c0d5290748640503c0c0002200c940141080c201c18490b91900300340041045070541d442170f00811351580425040e80c01031503140c055090250 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 4528910 1250 4527660 4527673
    0xc09030a1502040e040b1e01080d0f02010f06030c090e0309010c08090102070302060a1d0402090f0103020d09060216030201060504020708040603051008032101050f15070602070804090e01050a05060f0f040608 91
    0xb0103208000d030031381da00942184d20f01c188030071300c1507085011f0f8100c1d09940c020340703040044103c00b47e40780c0300450110011035585a100d4a94824144110406540504044604d43d414215040b08403050000044031981c4180090030b100e80c0d0058014111a510190a5480d40d50a0005034070788111500020b50100e0040790070703840d444e480081e0a406001000d80c690a400c500070602c0100d205485440d500102c90326060b00495005e134000b072910300086030b0f0010b0201050b840c2c12040781c0210080d040c1d486244000d9000307155090080c1c0c0c01620007101c003140703400082c2e074908845104520500051545030030008007014500030b000c20040c88240700ba41e44e00c8036440740d0403845201002440080070298400483c09080064084428120150a0b0102c2d0281003842d981160420300040312000d8007040351b440000c1c07410000c1c0005040d42d650201c1c0510886079014203441c0014109211031785040100852a0f44e40301030f141840e9000d480214481400d1404500070f0903a0350001c1281d8410039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 4530160 1250 4528910 4528913
    0x304031b02030604081207080c16030e030304060e0907020d08061c02030d0807030606020f060f180106080606130504020f0402090102010207020603040507060905030303041709010504090c080109050c09030a1502040e04 95
    0x17100401200040002e902d0b029038a425058441c0311064a804013102410f2120130500010f880380d02c26250b0285c1003805801d442480040e00d0f543c0141c0003480010034039940300301c9070308064040c680c00101da8000f90601e0010088014414035000b01070502c40c143d034a581700f210420040041440940180c01e9403180001c0c1c041c007420201054540c0000a85400c0d030028001d840850303034011718101d02014041c03a171141c410840c901e40010709030105050200703900b87c01c2035409120b1a4020411000541224540f00c0d040142c4003c02c2e603031030031086003014100f0005a980c00906000913004070b030010b84541c5940d00403030080c040d69600a40215001091009202000881200300c0303205070f540c27585003603c07501855100d010030b481c02000e01d11529105001d000d11000900107000041c03406906055a44803a0801d80d8800c11002011030002d00c0180081714081c00352550080c401c07904e04c0d00e0051170001107540e4445010b00a04845141c0c103000701d0510341034046600030000d0b81702000c802e0070a07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 4531410 1250 4530160 4530173
    0x20d1b06051003020a0b090603040f060b030d02070e070f02030a03051017031b030c03070b090a0204020d0e06060103060501020c04020906040e04030518010804020108060904060f1503050c090c0304031b02030604 92
    0xc0c2d00003640300300c5e0b000d01d0005407200200119580d2650151085080da19a1398400d20f555074400f400310f9120b80c540d5480c5a85403410840410749981583c01003a805103008400c090510019003e0300402c040b9401030920301c1c0d000002c517903000c0080d03c1c00085e590b50740761083c007000100303400c24120140c0e4003100c0a00c00f072000020304900714000e01030400d40c140c1420520b50b20701c00d90002c0105904184460380c045100340564607800307442c038400d4880e030300b807680e0001301260301c0301448460b501e0b40c4031006d5144010401800b68010402c0c00c1c20004241000000303982c030207140b6a103e00c12500040c801c5240d44800099074018040420091510f0a003440c001e401508802821403c550111400031b01642c460140c25001d190181c40300e0340103481d244144104c9005c01041950069112811080740d16000d00c10f841c0d0320600341860550351070643c60618180b44108001c1445a814082400406090003084a802c294103080c8a0018814010750890700c00100d64041d5042c041c501c100b0050020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 4532660 1250 4531410 4531441
    0x8030403030207050a0509190207150903030b0a0b0415120c0f02060a0203130807051905060907050402070b0105040e120a030204090605030102070c052106040c05030f060106020d1b0605 81
    0x881c1d001ea03140280c86800380884005d00b4403e581d44004d0000101c0c5006070082c580028000d80c52501600e000c00c5a20f07000040442112700045141c5d550030b40009055161045c42601441104d0300e41c5c0311468201c0b203180c203004a003e8024683c00c00e201484040d401145a03070701e1402000402d002d400000400505035010000c480c4026000d01c0001840c800003a20890f4030a03480354202003d1042542c403601c174541c00040084805205000310000d44510b00f90010405031f11403030041107107282500c6540e00f80015540207034052801880103000046520081d141034038000c0d034000800304481400c017840c11142c0c40c501d51010324005080c0c810b06038160000c0c41034031000d5009008130b55540d0145401c03071250f403202600c203500514040c450f038a051960900400304500440200c65151540c1c0c50920300255000c0300d40e000b068108000c503007001c0c0711007220581a1030180020358503003800a51603034402000c1e803003000030944d115440b4010038070300c88004075003080303082240c9d00d0004914901d104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 4533910 1250 4532660 4532663
    0x6010e090103060501260a030c030e0d05100c030b03060f0405070b0a020105071803021806040b100206010305010b0306010f0b0304050709050705030603070504050c0f0903010e030c1f060303080c0c120408030403 92
    0x601420007400400d80700f86c41c0c40e20025141004142045180e00d003100c2c5103084007012020403d80c600e621515036101700c03400e8500c60140003e0b000d99880b21100c1011566050443e50505052040001159501242059028954000136000c0ea900c03071403e5400e26640303801c03036808c0c0740c000300d290400182d05510151003a0302c0c5850360110b000380b00300c01003000c1c070b52840001c2d03000380055601c02c82001162500381c1c0224003d080071804c6000000050170754a1201c1c581c40c01a4003140c01002884009d004101b10404107901503e8954180f00b0b0228900d0164003610ba06c501d000000302e01084001c2252134024103a000d0100014100342c10001d01030390054a82d18441d11640c43c0225036803030306128140c0100311503505149010003c81a000315074001560036540b42d562040310344103008060005003c070800100103086a0550941d1428014110402c4080711520385181400040e80101e419508050083c038099280c1d001d0300610303481d052280b80d00341114000410000782540c0004064070036603 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 4535160 1250 4533910 4533929
    0x8040e0106020a0c062316050105010b040e0408030405121204050606040614010f02070807090209180601080c0c010207060c051e09060703180801020f0405090105091501030506010e090103060501 85
    0x69030390700d01c226621030391180007034506401201c00b0051903000c1c614400d8003c0b450300304001403506103805d0990b00e4212040300468064140d96506c2000000c0c42118094100c03060031a08250402128085501c2c0007880140705131400004982070003000c011410000d071078000039139552140920041c2e20b0106c15642203a1034400c070707000305e141403409008803c00e8074071040002055901c41001183c0d02d41d01c0003094030640c0664a40410f4a01c3d0034040351300a054062800741c1d490440300184031249d14600c502c0700c0c0304500e40d818081d90340c4e4850b0000c0e80180d2081d90183c0c81d41c815910450091081d080300904c003914000c0c5000811b500507001d0080660b1015000c618200744180c205110320410124030341c4640104801000039004040101d8203c40d110544039006445081c402e08a0340601d0f068418282d010030100502c0c41c00405440c00b4100580c0c038034005041040001c2c1e105001e22031498145a25400040e0060744220880318078000700a2012826584d04d05003440140310130b000d8603145 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 4536410 1250 4535160 4535189
    0x706030c030c02060a0c1134030305040504050612010203070903020f030703020f06030901060305070906330e1203040e0405010f0b010801090504080904021b060f060d0204090c050603040804 83
    0x12400380c42005101c80b000d030042d101c01d0b03480c1d03811607004080410b00603040c407500c1c189220440d40108212420300c188605000807100341c41c005d0329542c010304410704141c03002614080c0002503006003541c3c02c941040d0b401294588401000403900c0d6605c0540090310762000c01041020f42c2d0050544040364001e0310b025850740f0f20101411740758182804040d4002c03184040248450401c24001c5912125010002a103035407250794103414143d16500c001d000c0740d02c9510500510385d05005011094031280c801304101c0882c2001b070119058203012101c144211f00f041c001c12074841c6044a12000362034002d503a0380e241c0b14014140260019501960958a4a92161f1011a440c811045401e00585401c50541e11349000c050150170010802c0307079205003d120142842c0c40b10b0001e8080c98900911031291440302c0c680c80c40c075000000b0f11980d03071505094140803081e103444030340c01440c0340c041e200401d41c2d10305420031814203529980002e8000034000200300c04d026201014100340ca8102074440d11 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 4537660 1250 4536410 4536431
    0x1020412030206060f120703080306040f05010609031e1502071b0902120108070806060d03030608060c0306040e0d090b0a0306080a0b01051005040303020607031d0d050a020c0901080a0204020903030d0e070603 91
    0xa21b443c000d90440040d0380960000e001058016000c0e5a101d4801800411902c0b5003000800076910207a0047c1c02060b00e4000030300400c014002c0070a418105104003030602c00c043d4440001204159009900080e40000c1d00030510404242c0b2004000b1403500d4102d00c56a66160380c0020f511034a25001256010000451259004290582281d402d4002001d140d241c0c0c008003c064081884100c2c00c0c540d80311030000b40341a00380420b502c45d40423405026100e02e800000c0c0800d1710512580030859420034400d4107041e641200c210010b84807920003607900c0312900c1000350002c1019411800c094807600c50000c0401822100f031a05031181030b0380e00340c0d40130318188042d11540220b00008026801203000130b0904e82c07281d4440c08140700c00f0020b110248403810304090030241c6000c0340c08002400042c80303c00c040d804208001d43c1c0718083d250351800d90714151031a6251200510000e1140d40c000550065554040043d80c0302c2c0616954100404c1000100141d03488a0a20860380480d040404543d07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 4538910 1250 4537660 4537669
    0x406020708030906121e0a0605010807050a080106080703090b09010207030905030303070f03112502031c050304080f0c07060203040806060406030b0414030d0c05091c120f0201020412030206060f 85
    0x900f401005880c3c00d0404503051071644445000610400c01400070b0392000605200812a00d4055440c03842e00041c1c1600f480c000400d500b0004062000f4003008100c00544643e000c00e41904442c290320f4400c480ea1207032a07084000d0b094842001e043c1c0b02190091000245041d402405210f100351100305600da0307203000385626400205c4040d00410b420a19400c0002c3c02604010340040d010080a40f40024003415404000c140000c10325450302c800001f80c08500f801c010218911981c4d00455050b01e8400c070b002015480010801840030601150b801c0080c40b4503001e03229104c20401c00d03601c03242c0e15154025a243c2003489400d000d441810302080b15800d1902c40c80c0152030b040494010a0b07562501d030341c44580107101000350107100800c81c1003010380080c030503003407041c1103a96895a100700303c2d0200720325048000e080580c00c034003118444c00014620705942c0601d964904140803440140750b016402401260300c030301c55800140d079200080590101380349210300811204820089004000d20 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 4540160 1250 4538910 4538917
    0x9060103050c0a0804020102010609060b07020109080c0a0306020c03091002030d06060305010501120b0307030210050706050109050c030f1803070f0302010e06011a0706020f0706090203070801050f042301060b040602070803 97
    0xc02c4070310200007899003540310f00c004640c80390040c000800c0e26030303070384e012007040b43e000b6482003184100114100c000c6607031100d444401095250001c1c03800b0460200050012802403100800351540018104d041e10418800e80703c50a00040150085640c00a0069129231246031700d14800c0b0318100300826418040d100f0b0354180e13079040e075654034501c25801007a801003001d43d82040c1c0c544681e201c0040103a4400b2943c40c031100ca55507400c0d8a4250518010701134680c10781240c0e000d0fa041800700483d00e401c030401d41c1d5000000040b90040b9413503007810140e03905002c502104050200046030b0042c00640c0c107201c929644664005c0045403914050785441da1001c2c01000c0e0781c5a20001c071035000c01007034000381c90001d0203007000602d0300040350300514590b4440181254020388541104055203401d00c03140004144110080c00b0602c0d2000f41609205030080c4001e080d04090100c2e042e0103980c6152410710901c80e00d0082040c251603882e8100b0b145c00c0751040d41c0040c4203540c400702d980300010096 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 4541410 1250 4540160 4540171
    0x8010209012d120207060609021902070806040f02060403050304060206040b010504050403020705150405030703260f0301030b07140d050907050109050310050705070c0f0501020d0e03030a0c0524060906010305 91
    0xb2202420403210450b02140654080400c4503000e02601c001700e191440f03480000e11201c00016603a09140c192040031a00c80e44c0650159001305800f000442004203405600c05e0f8028040c11080a03c1c0c4000790f0b40c1e000b05d8002400301d1101180c08903c081e0002090340c011030243c400002241e0343c13a010002503d108440060058101050401c840d080c100508101442c10f103548904058803440070a1030320362280e0042c0c41500100e0000e002d6016210084c1c000c11840303103251490840b40c01d00c0100c06100c10300c0001c00c40300d000400503410b54490345214022101c6c40511550f107074590604017000e00029140c0d1015070044400016080d030203402c0340e030300b2070760054058011000081700700c8000380310081c14641400020091000004c80c4419000e02811403408144543e07800c01d40024606068442d841050003540340411390296000015907103504160315002400306540c0c0340050404080714080006c00c43c040c1d0719840625800c0c2070242c03084e07900782c881c000c26980e000011029984203480 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 4542660 1250 4541410 4541477
    0x90504020a0b210a0e01110904050a06060504060f0909050f040b09030c150406090c030c0303170103020a05040506040917040603140c0301030f140a060203010905150a050103090614010801020901 85
    0x1d0080c80e45040622203940442c030307000005205a1002ca010342516144207502c041c0400c00034400c648c520b0607204181e00242080401c01c142401d2110141541c0700d41e0140c4002d0003104001c07031080604ca03500d10f0303002c0c1035200300a0000e030401d1503284040b2034003070740d085450b400100000399081c18004203072180e01d0300420082ca0072181e218640c080d00000074205540031916854140c000c200180c12440080d84200900080f00b844c50070300801010140ca10a0001d010103001040540e0791203404009441084500280725180c00c0001001884040c00007070241503542940d0b01c4e0001590060300445189840c18400e55071546401c000442045070090100c02c82800180301048590b184018514070809080c0c8409030743c1480d4034505030144004031240c0340c00000502c03d1086500075550800c0c8419400d80c0340c00b503110002406280726002c0c907410941c2d03034212841803198640120f240743c44c50010318986541c407841428041d60100f14000e02088281440c0c0380ca00519244181c03042d0301000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 4543910 1250 4542660 4542697
    0x90305030a020d1107030206100602010b030a1205130b0d0605030a02060d021c020c03030103030e09040506070e010201020f2205010521040204090506070c0311010c02030d0b060403080301090504020a0b 88
    0x44100080d0464680050b11950707400ca54181054084002d03c0b170305000340c0080842d0301d0109603034100d000031038016100b1039041400078491074400190f101c00d003d900014100000c480c50104031058024010100389054818200194914150b0010825480c2c00d8405000e04c54580301810365560340400002c0d0412010084004090f035154080c040500b070f070a940c429a0780050711300fa000c0c0c1e0040300ba2800c03181c00001c01001016040045811070180a89248145103090349a0715101c800060814092169001c100d0040d60f1003035046851f00c241c044907240c0c5807400e640c0f21058603240b2284042c0c9402c091903000c9000d40c01441a40c1f0807044143e03686480c01d0500802e2240c4c1308016200b01e8016440740059000030f10244140c9200e101c440d560040400e11030304006001800b4103c0e80c2149900d8480c4003440a0303404400c5a06503a0b402801003107041066000c684030344210340c409001508044004110004203400aa01a500850b40b80c0c0c14a80c03900c200c1c104912403010b440c041c188450 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 4545160 1250 4543910 4543921
    0x60103020609030a020604060302040e07031a040f11070c081b030a1101090504090b09010c050a0504050d020a050306040503030702011a0a0e070306090e0c0102010f0b01020703020d0f1b08010e0109030503 89
    0x201c0c018203100d44043e0035252a40d07211380c085400d9801036040b00001c60f4020030305000c5030b440303001e02c6640460b02c1d2134217109141e03200303080b4007000840c888814001c0f92514440b08844103560414507100e0707050707000e9a1340c4071054201210161100d014891142c007480000042d0384003400c2c2e080c102000000d02074600145143e4a500d5108482c1d0764403410700466404c00070350795540d442000e00381c81c05841c0c540e4062512400f1542182c0200b03280c0790034000700f442a5605560300100396401d45034160380d0201c00004a00000b03980c2170b4107901850b49407142c0e600700010040d0120103540150810f030000d00001c1203040b5040801c0301c02800319a00110b155004010040720b0700e0310320b50071580340d0400041c11915007a040d029515030703050364111684201041d00007540d0912415801e810303074803802c021030408100004d4549911744400b920540c000e4040c3c0701404280020603281d503a100c3c0410280741051828030440c5505031160340702c903528009506814140c18060b41e024190b0684d111880e581d0382 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 4546410 1250 4545160 4545169
    0x30b090c0a080403170109060501080703090308010902070f0b041a0f010303050a030b01050c0a05010501050a050a0311101103040305010501031401140106050307030f060f0302040501080f03090103050c2205090907060206010302 99
    0x400650400010b203084401601112617000c3c080e0000c81c0c0040381d0241482c0c00035114500240030b0000f014030349940f54000c00e62044985045d14040c01000d031744ca1055040031100030b091800b003e006414150180010466001d04c550700007041c04030030000f00d80d10050f411446030710900c80a80407510400203820000d11a40c015100140305052243c2011842c0506628003040110f080396581e65501c0148240e103045050000181b10841d1511101821940c422044040000c60180208541415116940d01a0441c4000388402c1e40c1140d485e5075507401c110f80a40000e01c02502c100754059100c0c81022010b00440201aa080701250041e900c0c0240c101c440d0350005260074101135a9240001d10070300c6078040d000c010179060320381a131500d0a40c010002250b0b0306910100c1e1960001040840c0100c000c8180c1e42203560900300003640b84d130340f140c1200e002e115001b442402c0e052415480c10001c445070520b41c040e01c0059a100415075240442c0a603211414020000903900c030380c1c01040146403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 4547660 1250 4546410 4546427
    0x60408060610260703060504090302120a02030909090304030b010509040b070e0105040506070c050a060c03020d031a0406080a03030e0601140909010207050609100b0109050907030b03010605030f0d030b090c0a 91
    0x618640140030900009510030000c2605080f0303031060102c9002c1c03008095060180300040c0008817801c00c80000741e5a800395556101c2601140500000b0402086850003030041c1c518031030340545038148524100800d00d4533a8458081100c050700c144001160509140382460300c501d6001c1d05841c10b586460030700766204030b02e41c202d00b030402200700400700300b645800d0b0207080000d01c0790070b46180e40c600309802c0040c90140782d000001046940105400404c5d8001950032403079403242800036039624205500342088002c18607241d0490b08010001072405800680d80c9007850083d03404100480ea6890007a8584000703202e598140c1c01000407a00d41843c1208003c0c3d040580c0c2800180f81918565629042c0082103880c942190445481c03d00845910702a260980e0f000740307807106a09041c02c0002c5c0c0a07a801500c00c1080550354005030103552801d40c42003010b014014100c8508640c561010350b0340321401c0200c40002410514040070905003c01c4d041c0c0211006d42c01d2906000749640304032030406 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 4548910 1250 4547660 4547689
    0xa0812060d050d0c1103030306090c160602070305030a1a0306013003080108160609090207030e090c040504061a0307030504020d0c0305061602030c07050618030114090c0604080606 79
    0x3003801c00020300c2040061101e18864680941203103050500510403900113075036034002d410400400225542e24110a5446030385442c0d003076107814010500c0c1e480030030341d144001d1610b8400900e1500381a00b00000e148501c0145200f80150450744404183c124840721010b0742642c4481700601004922502038000150403100482d030112029100025524080e80d069000c80c1400c00180584082403000c60481d840c1c0300c0e1403035039841c6400710003800d840c0148140b01c1c2091780421003004040c800d41100e4003510000385140c6050a00008425a035845441040d103d00c1c40e0040004075450b01c400d000540070042c1c403041d800c0da40c50001c00e0b4003070800204126071125183d40700100081c100409100598050302c0100081d2904400100310b07802e8959602c3c0540d807003406000c034112f00010310002030f5002601c10a4803000c0c514503a007083c1e209080074540c99400c00c08411428440307480102e04c01c0c08140b0440f1900c414400c14406a48100c0c050340c01141c00c520005901424101003041851 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 4550160 1250 4548910 4548919
    0x30209060f0d090c051008010306090305070203240105041401050d0309030b01060302090906061612050d020a05030907171515040203040f0204060801060f050d0501020f041d090a081206 81
    0x1a01e0401041a800400c5401c1e44940e10183d8406000c0f1000c00c0c03034050170054400c1040542014000b40c41000c0502c402054a51610f00700d03002c00d44a01c050300c0c540d60707003d0102c0e5908000e064244c4148a16498825842c903881000004c0324038150241d20080e0310b12010030041079082605210010080b0704083d4180f1209040000c0010145980d6500901c166a40144c031140c3c03440401140010250040748180d0040c4182c049880c8124490380c201c1b980154055148104108195a0b42c00b688451403900740c40824001d0405800c000214481c4440005646c119a221402c840383c0c10720003a1100241d0f400008a2036076143c0200c01c2a400c400f24405210258440d040041c003a684110b82c11180da507076001114085081502a100c007030b098000090003154284a03100c035400301d1911603148503800040d004014050298103c81404040042055455840311440400302140000a07803081c1001c0c0c0015042e0400403444c440103541c056105e602c0e1a590b03032890620000f0150405601 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 4551410 1250 4550160 4550167
    0x6050403110a0308120405010f02071e030e0405011509080102030906060d0f0503031303031503030503060d0c05030111030f09030a0906050d0b031f06080a02090a050702070b030405031207020109020a030303020906 93
    0x31410b00780140ca004117801d11441d041d89418500f0a09407010300900e0b5441038014440513001480a401d07600a0803003102c060020002e0307900707040780c40c82464042240c00034078000003c038124220384071442169485840703c95001d559290703032500b00d10044920031001d40012000c2030306440d00f1700380c880c4001d000e80e1381070b030402d0095191603042d40e02c183c4070900d0611852001c1780806805010710005407070042280108a131658501416030b110042410303104190a0307d00324204188203034501c1c060a0050f000708910f550585848805600030748a1902003071030342e0001340305800300004444c46003400f0f5580e60403c80c51f0000640f4140c100c0010f01805544a00c4002d0250310f01f081609446400030700e268040070344641c102000c40b0801d03002490340380c100c3d80b500d10144e1541613080780c101c074071428000b03440d64401604a0420240da000304509034000410700050040010140c40658101c5482140030b44407404160708072054114029007014040b81c0404c0403a020791702600d110203016015628 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 4552660 1250 4551410 4551413
    0x5070606060504060306080d02060610090905040501020403050f030301060c0206070c0b03090105040312060812090604080601120516030317040503040504020c0f0d0e090a0506040b090f0612030406050403110a03 92
    0x40d40c0c400c1e0000c1d000203402050800101758540100c41c014050301001e0f000d40690881d00a459540040c0302e1805807440043c10b800052103885004014003a4210820041c280361800e14080e50251109803002e2144403000c003500140441268100d0303426840f41c400c5884a9402d00c0015003103c9001c1d52242415140010140b151200444c07044408400009241c505454041c103600382c0c05503900001d5140105c1805101e0f00000d0b000c10041c0180c4009480d04c000c0c80003c2d4291155800c14a0703203025410000810f90340c00c5011684851080301550f00c0391000103502c0840804503c0054006100c0074295581c0c0e070100f00e4800d4100b8000d0058915083c2c9078000308069078040281d01d2440c2d880507e58002843c42802842c12480140c07600301d4070031441400094080030003510f20043c080c0e032003021401c0c075030340c503408401c0180001c0d1810006140c03500068010720002c50741d007402507805003003896104002201303d40645140d611500d0a1504503200c0210126412106507000810f6080100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 4553910 1250 4552660 4552673
    0x409090609020402070303090b0a020301180f02040302030706050403060509060c04030f03030b0306010807030303050901050f1605070b010608040203010506091605070501060f12120f0903060c02010209090f0a0b090609070e010507 100
    0x807661b00a440c00f0512600910f808041468002e09070700c4c2e100d205100500000200508008080d070748900e0111320400604071280c02441070350b02c029494840c05200241540d088406001213a000c1c40e800c02566981c07600c8151030760001c030303014904000104403c2c0300145064552079001e43c080e1074002a040186e0010138605407003a04649259803142c0001c004050703140c040e46a010a0940080c407450428480d06549034201900400c110501c040d041811544200c003500c443c640c00048001d01da5070b655501400070401514243c0c025400d20000550724140030520034050007240ca40303405520a2000c044481d034100d000125440d540301d00c80000d09420100040300a44900801440701501528110314a1050200184203010358540d100710300755085070950045a070001e00104d901d00036180201d00900c2094020f5511080704c909000d08000350381c070b1071449071800300420014116050204001a02c08403611544074140d10001102e203413080309050350420042c10510308041c2590784c0c11 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 4555160 1250 4553910 4553917
    0xc0a050106090f02070b01030305031306020d02130902030f0a150306050103050d0f020d020303060103110405030607020c0301050601031a0415030803040503280503041103070503070b070c0e010b0409090609020402 93
    0x1a901a034540d081030100150901c5104045018040114030f0f00300641e071199042d03041440041c040c410048006100c00c0300d00c1100d03507225a4480d00841d600c0c0080b515840094000c0444860299010500841c4114042c4200c0340103240813007600f1403d603210b03540c2c0006401d0000700d4107201407240c100000003c855005940c044c52003100900108054204001c0c1b0007101500e240c0215846403000012050700401121b42160302031a01081c0a200204904a00d21460340519018468242000501d55000c5030b1001c40000c21802880b8070f4032007000450603035802c0d400c1c1500002520f81c44480c945800c4e806040200072058490060710380d691900c441e00c2e0021201550305070000100c504d8440c6500c040d403030300c0c9000803130904000080703d40b00074018040100001c200d4031b102845a56580d4040180c0401888018200d441280c0c540d09e0114242e04080c00440b08a03000c03540c08901d001c031340455203051318440d00566051620b41220350000e4000740354107031152680e070621180543c4660004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 4556410 1250 4555160 4555163
    0xf070305030105130209011d010207050d050a0203070605031005061605010c1e0c080304080c07170f0609030412120306030602070b01060f02010504021c020105040909030e090109090b04020103020d020c0a 89
    0xa15499601d001c00f80186a550700916030340c01c52040010001b542e8210050841c1968402c401c2c48146450358010f034501f001940020b43d100c0e1080c1c0b120420030400040600c0358500c03c1d0f066030880390740c0c0c0000340c03039602081d182c20026022003d400d02440c1010740152624070746a61071400d643e02c150716000d0850b0920011a00001e60600d4103450b20403000e0786840c0c0c404014503014000d03040946450905000c00f50004200b5400040c988201040c10404034000d8900115150305050201041c160b03100898181880b150040038001203d080b000300581d001c55414080004140c4107039550240b0b04205172840d0300c00e255036001c01001041962000c1c00202d03100f034402c180c265041c0f00003d09510700d00c007004411607040508003c0180c03646844415401700800c1d000494141e00d10050368140a290010071a40c1d10302809041413541c04803104105003000d954000041e6200c01c848410f171184104084c0c203042000c000b040040d40310780e004003600d070380300c4000604000f80e101402d405c08018550 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 4557660 1250 4556410 4556417
    0x5070c0f060221040b0306010c02040b10030b030c09090604020d0812070c020901050319140c0d05011505120304030803070309060f0911010302040f0506030402040e0d0201150b120a050703020f0703 86
    0xc0326243d21512003520141d02c01e544551300341803821000d66030500c001040241000120030203e011034980e50442c90300f1443c0203010003201e1200c500000c000305158201039120344101d0714055224100028894082c070182300242000366680e80038002c0340b1010040c1100c40080400186076050b4903243c08500074071031075a0340303007171800b103401001540007041c0c11452003604840d00444140440b4460001201c0e48200307100110b02003003044c5800d00b01055625034125940e440c8c0f1404000042d80101c5007404000743e4110090b4844c030078841000510703000205280c0c0100018804128880c000d90381c841c0a500d40404e41410940c0d4600642e45d1060400440607240c50740c1c441044030b2b8401c0c40d041c2400a01c4d04506140c0f91100201040169109450080100001090a54486401c1407402d440f5510488011040ba610028000c205025a081c004507880c60301140120344d140031075248490303100d405900382d01c40e00306d000001c1202038088001e043c3d00700124000034007042c0250410901945 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 4558910 1250 4557660 4557673
    0x50a0803060a0b03090a02040906060f09020c1002040503030a1209020a03050607120506011d0a0f0e090d020d051b070f060504050a0f0503030703120216060c030e010905060705070c0f0602 82
    0xb8000701c02d281c0e8000241d105424002c00c448544002102c0b41090380480e00401c00382c04500b043e800074001500300b01400d0844000c0030400d14080d800400c00c2d01001d43c1103420721242030b110201240075902842c0c0d1301d07410400c12081c81d244074035013510302880c280f070000071003401da9400280c100c540c590040b696600712408000129410040c145414070040c02c080c402c92a2030000280b102c3c03030209800c0404600400211010303110300d00d00501030610100300412040d222890f5001c0300703030300b207660380034600c0384400142c1c80c84c2c4003040b1181c0c004e44a032905802c2070030307917614156003807d05010b030701c2ca03841010030015040a1460f1505e004000c69190386980340e08090601001c1d455907000074102441103101003140d5100001210300294143c0340104080504040c08400b030b209461600c415009980e800f801031010951100440c0c020741d071020480000e8a0b4620760990f9250040036046070004000a00b1184c0500d00070100c081c484d10340e005949071200050442900913401403001a804034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 4560160 1250 4558910 4558921
    0x8071403030f0f0f060f0409060e060907031e08040504020a03020702030d050d0612050706050903070810020904050609040c030303180209010815060604150302130b0703170a0905060a0b0d050a0803 86
    0x4a40c0f600181802c928545914041780841c15000c03141c12000d000300d80e6602070300305000055000c2035010311610151790060138280d100c540d0710070b1706000560300c580f01c8125100d00b0660b0300700250f56066102c3c0420303080c6032400e001c0000075000b00301c01d03c00707140e000c00c01c80b00169810710800b6601c0380f040e140c10b41c683c004e9123030074011070380030f50004405203c1246203100401c000295071001c0f9801442c2c010740e41c100303100111b81402c42c203500100c1c09114015800030038034502c3d0050140d4076000d89041180e40e444e201008ac94030b20640f4040c0240c010102306002091080c0c002c6030706010f50384c450340545095680880e182513026401280f050700070714103400304181140701d6550402812110541864104690052001c400350500d40905a0000e01d0a08400800c03c4010050141d0407e0648900150074050920a002c0d000e207411009040001615070170144240c2c054181c0010040c0415a603846810009280030043c0c03aa04c440740501c40400500c04008400440b1b10403410030b612410b02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 4561410 1250 4560160 4560181
    0x30c0809061c06050307050102060406020a0309080d020a02010f0207030e1002070506071103010c020105100e090709020316030b040e03040303080c0c03031006030507050304030f05070201141b151308071403030f 92
    0x3138000038400c3d044500c0412041c1c0e40041d09607000340e0400401a500d181003001a001084200d50041c01000f0203d40300d8180701555024181a4000c0e8009101c41d2800b0244001244202c503c000e020801c1c141c0070b00050b050294101c14180d17184e00480c1c580d1915400040d03040d41103041c0480307050940c00d201510605083c0900c4005078600d00081c01541096a51404003c0071409084101204140000e4505c4010024500203114101085549052582c0307000c0303106050382c5208010a003012480c4e411810a44942404919200301450806082da50216160030700501102000d41c0c0901c078103003141009200450061020503000400a0b10785040902503c00041020051040500410011a030040790104072030850f854090ba03102d0701407005072800169960f407d81131000c0480e802c03200514580083c2c002c044104120798140d103480034100740482040300c0207a200c60741e0011075000035001b040174244407031042401503a81280d030b01e40310f13196070411610b40314103c0f085420301c40b0f00180f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 4562660 1250 4561410 4561421
    0x1050a0207020307050307061e02010207020d060227090a0e01020706020d0204051504030206040e0405010e070602160902070507120312020304030903021503060a0b0a021e0606010201050702060112030c0809061c 92
    0x17415000b41c0364680c41e00b50080c0411001d0030380001080d141c403a4442c0c1140c0300303504a0f482168010044450444541800c074000d420200c1310308800c2620f000c2a01041c2001401d451440000030031403c459a10200208090b003800c0d0740050b03156400380115000031762a4000751010200381d10005895078500010482202c80c8120043c0088100b00801d20140c0c803101e08540036140c030340e0080c1032207032140e14010340100851040d00095000b92480480c2284e404509482c020940309094038525440d40700c51300c22817040301402040c9600c640003c0003004100d8421340c01c0c1f0b6000382401c01c3d034800c0b082c03079a5041e80d000b224110300044039038906204500d0890300030340403106907041290440c0b501c1000300c2d2140c0094040c0c00130030100850280302c1c0034070030041d0007100d404000c00c49040740c50f102d40320b039a140f0007a02c249003d035080100085110b44001039440c100e07198841c036400001c1c03007620169003544000500790f074100c0c402c02420106848010051840643c25094080c442c003400c440750007110b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 4563910 1250 4562660 4562669
    0xf1a010506030408040308090f0d05010606020f030909010504090212030a030b0301110a0512040212030a0503040204050f0405070b0a1701060203070203010c020105060303040303050d090c0305030703020601060c0308040b0a0e01050a0207020307 106
    0x10030300501010600300005d0300c058a40c8800ca066a904c2c21100144048903a003580c1540701c0002e2024108010064002c101281d41caa001c0310b681c0101446516240c0c041c140240390009440c42c0100654a0b0a8101c1d5000034005081004040fa80798000c034150790015a414001c00d80f00c040c04411400d013486030402d1710039000300150404070403440c020840d201e03414940f01c20f2401c2d00042000d40d5210700c480c004044842c802c0740c1d44c0744035407080907000344c200315400d80c0b00c0c41c903260000f00304603d40718000344510340c400f000c0d10206080180103c180d030004e40e0200200300c0e002216180f00b0070b034888014042d00f0590002d580301d241910406003510320741c013804411a4140303014024a6100002078606480d49420900d8031000a00039400c000c184860b800350000e008c01c0000428801d02100074800c90f40203a003542d4180c0e80b00d03441590b07405961f90b002000200540002804100810140c5812616080307000c40e170041031010107800d544040e12102c1c02c0c1680042e0144c02c40c42e007000a88000c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 4565160 1250 4563910 4563919
    0x6010b040b030c03100801020412060f0b03030a0f020102070605010f0311010215070e01020f01020703030203010f0b03041205090111010509030901020d02010608100c1407150f0203040f08090d0f1a0105 88
    0x10305001c010340c441c1c0005051074183d5400030020a21030040c030700040014200400017151a00d9403110f08910b482e404080075a8030500e000402104822180a5200c0f4800050011850440350600c01c4583d804000660350441d58240240300002d42280141030082c0411083e05c44014114200050a040a090b00700d0565002c580651500d5070b03000d41203030b4003020505000005042c03040045c0e003030100c0204856000e503c000741c0c040805405a000c0c0d416591780c0c10294002c1a01e030b9152402038402664040d00306c0210001880c65184108020314003100c0624000f259440c1003102d05003035903010707a10850543c00100d001c5030b00d035074100700c0d200c030310312251000b4409985012040da40390031400402c024180d41303c10209100c00d01031006c04e0400302c1625140e46c3d1f244818100741c0c8a86031000340c180487d80c107150001001e084180240c0b8011504620240d442d040607036100c80c000e6100035020394019012000b40b10100304100d52142c0e040e0301030b23084500440e501000340c19545c0e6050300402d100c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 4566410 1250 4565160 4565167
    0x5070809010b0d030809070e0f0708060a030b0105040504060905060a0902030c06040608130201030207140105060423060d17040305060402030106051206010315020d0e0f0106090b01170a0207081b06010b 88
    0x9aa80d1070f906061407a800d810091801d440306402c50341003800e16008aa643d24160f81840243d244400c8094491502e60782d507035003180c445404000a410045c40060903407200d4a0044c0140e01d002d901558010b441035000040f5001c140c2d070342d02e0500d0821200c880c50150f0341c0300c44006508080c0032010504008640d00c9280606025000d014070101810082941c081c5540c82c00459010b64100c0e24000d4200801c51424101e156040d070180c4400c90b0504d0041c0d003004100003c41d25024401d28015002010b01c0e056541d425060007144402c0d05070640f00c10308244501c01000941c00c2c020009140130b00060209840c250040c1800d495883e0302c41c50041c0313503d031146c00246002041c1141560f50119030030b1000190003200c0001390058840303620b1b281d840c101070b44d4034682c070000d40461020030400090021641c2c42c84100b080f50030100d162404076100610341c4010350001000190301c0f41d10001c0c01420140a9154010b564020900c940c00e13804041c0d852010340502005035500421030700811034035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 4567660 1250 4566410 4566431
    0xf061e05060a0605030c07020604030b090c03011e05060102070506040803070c08030406080606070302030c01110403150b15090112020403080c0601080303090a0308070e09040c090c05040308090d051f0507080901 92
    0x40d11007071280c03004003c408001b003a000b290400c2168011600100116102c41d10381c00c11444241098800035100c0c492007c090b20281818010502c50414004804101c403074401d050350042e100007002d240c11402405c001107255075410300640058030040d0001c60311140780e850410b150742e00c1500603400705d03801400100b000c80e50201285a1050b000c1d07400948601003480c05910318050824095007035400c0506054010074100060411603000c0d00c0788084a001c045204021114280749050f00300d20213003004d41d080c060030b50061004e50f1040c540741400c208114150012600705810840e00a480010300105804c0304200160251641c0005141b460500720040f43d03541e2201803005040c08105800601036600402d4640d42031003003c2c103402c20704d00d003074a03004c0400c180714090220700d9880c0140441d0003502c14010381e4141c3e5030000798285001415400c000d00e034010081d08032158440c1c00031510401c40104d07501400950541404102800e0001303002d03094540c01402000940e142068a0a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 4568910 1250 4567660 4567669
    0x6030207050705041d01020301080d080a020306030a080a05040305070905070f0503010b09040908091002010510060207060c020d06060506070c0503010b04090206090d0203070b070302100606080903030a0507020a0f061e0506 97
    0x1400c48400312000620007220070522800e40000925406913941f01000005106101144200071168560340e101d102e5916000c200080b40000e545982d05640100c100d480022106d50003003509403954140b040c146607480d0307106c0c3c2c600101e94114002c8240c4030030901200704c0c1c028108622010450a0041c155818002d4980070340c042c8400307461003161101060403d000844044a005000c050700c4080180308075607020b03000e000f0070b541034907120143c881c1c000341c0d0300e102040c200c040d100a0f0341c82e20108580e070307001c0102240c1020f506469490380d541c80001c090f91850000c290b0381e48100855001d080c541410107086803000e580c2580154241100a001030303032100100c90b507801d0221031003603007282e850001c41c0c0380c668580c00001c0e000c000017031032031f0506800241811000e0800d542c00d01a03107403103a2081307490301d00a8902c680345601c00d101240c6481034580086d60301041602c1101d103a14103035150402819291a4180c2d800d40d03a40183c0011002d1008600c460200514001e1046040180114 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 4570160 1250 4568910 4568923
    0x302030c0313110604060f120c0207090527070e07020601050d1401090804090b030c0604030503030402100e1008010905070c0809011d150a0207090509032703070305060604060603020705 81
    0x20b0301c0d199800d05205080141c001c0001e6104040501425100e54a4090140c0100c0c158140c000124400120f45800840c0b04e020344609891941d01030040d02d49840c1d002c20161001800d00c0b415040f00d03d087d070346040281030a0821184000d40145a014a070484148082402412100841d00108014411502c505074084140c40e4428071304210700580c1b00040303004040100c001024003d0001d800900303001030fa002400901806c03019516103900000030010f06100301d200c02002504107100250152403c8001c05810b0031550800c505410520400904d035031409046200104031044014007103504a132144a0b0b1000850600c0c0d03104141503219030010b8096200304a0401694403034800740c2c1000c2c064030140403140602020707030a1034500001211030308014600401849814800154110a4020140241802409545020f414103040c05000360707000d0002c065101744941800180d2000c00c10301000318001e00150031281011800c01065035150345c841703001c250040c0240000301c0d001280c403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 4571410 1250 4570160 4570171
    0xa020a0305160b09070611030309070632030a0507020a0512130b0c01020403030f02030a080a090201030209030f0106080f0307030801090209040b13020705060f01031221090c03020f010302030c03 85
    0x1140c2c54401c41a0880d0003000c164a004111042110038000d89580018901c01902d075152034107074000342010310b22a56404110303849040d5622a00701041198000c03242d000d0361100c0f000092200c1241c0d10700c18212580d5030310b10f82610110000410030818418826503421001c54800340002d1070b02d544507295141c10b0a40c60740c0d440d160000b0907443c14081000640010014551020340790722007040b040303000750050702c0709a0100d0801058441c42520102c00c90b0381a60103600d602d0040c0d15032845880061454110480c18151701304000582503400308a00c0b20010303070304c000106070706045c4101130b403c214140c07880315031700da20034001180066080070b001415074000200c0107848194080002d0081d002d01e000c6c141d00803000c0c2c00c4120b0280c04a80086c04040c2c00381088030440d80302c01d400c0c09808442440007404000c10880641c0555224840c1024001c0565041c0c00c5100406660320040328038a03441101c0a1400c094200114101070700403518082c0242003c605501e0203c400c0740d03c41c48014003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 4572660 1250 4571410 4571417
    0x3050c0306010e040f06050415090c0206010b19020312040f1205040b07020402090f0909030d0605010f0905060703090e09030a02010e01020c03070f0f120305191a0d03090306150e0a020a020a03 84
    0x4403079481c5c0407a4408401050010414024035130780460200207040140038542c0784d2070903c041c0c800a5800010003d0488120400c40e03480e000c240406400d500c5a608203440441c002004101c0b00e85810310f0746640114020a245e442280f554030300b1803040c1c0702d403412081c140941440304102e000c8020064440b01c03901a50702599403040b400019199074400007509a0000f00c65043c40b104290020181183da2960701c230070001c040d2608015200308290400d0a00000c20290f028482401c03d400039000c143e10a05020780d9032604e81d50300c01c685030006c0795280d542e5480030801101c050b038240100c40141c0c40004c000c518020300004d5564507403068640180c0050226617001c010009848032910b4101c0d0003540b412051202150000c029100075a9040540044a00100054842440760084402a00c0340c21071364010b260040c80031f40380000030b0a03010f0041c2004000080341c608e0048446c01e60040b14074500140c101483d0100c0c102005c1d040600440c410710668107070907000101000b4503134141c02c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 4573910 1250 4572660 4572671
    0x51006030908070501050906060907020703050307030507050102130602010213090908090f0310050a0615020f0615032103090601060804050303040b0612100501051f05042102030601031203050c0306010e04 89
    0x70880380d644110f0300000d10030b42c84c0400300300c0e6098002c00e545014a80885101c1d08076254110100d0340d071040e80c04090815041008000300007400384000b84442c0b0711400c000f40c14481c1588210010400035444400541d4000603d18135428986500c200544203540c401c01402c12152580c590b81d0080d01a0180542c0e80c140c0351441c603517010030014002e0f141c011814481b620300000c0e26400350402d80b00790b01e007a080e40c00409840c50300104886503280011030040c402c3c1d6690780740c034240da586030145c0701d5094000c1603418084000c01040e0315240581c0c0c420340f07596906103c410a860b062051f40400300b0028001c090000040303000c402c80340c11942041028240d9280c4c0030009074002e600b88a04c80c040d106e46280c1358440b01183c1c0059040380d0049601301080c17401c0421a800041450480f00c0010304e04000501080583d0100304200c000e409000c0c0110000c5035002c40c2c135090707082e0020307200e406440c0610130800c0c4c1d140c094540d0200d030020038036085091001c0007170300d040c440e042150b106540f81d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 4575160 1250 4573910 4573913
    0xf0b0304080703020c030d0903020a05010f080703050414030a0305010305071502030403030302030402040b0612061e010516051c050309010605010507210e0604090b01021903080402010c06110414010e01030510060309 94
    0x300301c170f81003d42c0014295055140705100c040c10002c6644012405142a40342c002419030280c06008032801441e101c0f08015660910110000c00c0014021941206c1d0800f542c0090001000680600b100030b403800106941503040c00e40c6807068030360100d0401d100f1a0008140640c2c08402c1d9022290b0600f00580c2340e40300d51000a0103004180f581035000301f070104448503212042070300140515800d6071100082440c1c07100b980c2d9070180144e6803a0101d4400c110303040141e034015003810203480c000c0095a081160000c1f05410341d04240b0a03c500217400031040c480d501d0400c3c45002e006044c2406d000c0e2401100b5030703403140029804d0007006040f003210204030075160b01074015039599900040502e9641e80d21a08100300a05550b84154014450341980e905101c4003c2941030885030581c0b250081b69072543c0c011564083d03004c80c1210283d8544c4000c2c090001c0c250040c1021f0883e018a00c07559540d40300c00107101034852000ca40c105400c080900c09901c84042e0040e095590034500401c030b00c03455 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 4576410 1250 4575160 4575163
    0x9010804030201060e190b01020c01080121080a02061006050a0210020d0905010c110111030108030304060902010c0c0801140f04030e0f0301090503040902070b062d0112091101020105010f0b030408070302 89
    0x168010040c80200008000702c003282940414103c1c5046c6030304110780130090004903940c403c0f4810b960302088805005004a41100790304200061100c40011140e50031a560a1451b070008034414000d64011000c0c04544010060203d01800c0b203440e109007000c202c410000e54500103008514007260340054940c3c428501a0000c01600e50040c0091140300e02c403d400418011031100c00c0300c115483c10882c815514004021a03048030300710801142151541d80301e55009040755081203050203450134032000040e020f9001c60004106210000400c802180d03003100c49107100509548418641030b081000103034100c0540101075400b03403168030003030b00200c000c6030041008410140c87c0d888003040021704108150000c114661144c1c803410b0450b281c1c01c042c454410701d403040d0709248003c2512080c2e413055500058080e01d080515180001240d0120b02c14101c940c02c00c0f09a1b10040304a0703d400a41d41c09009481c010044114140c040c6071400707042c140a0b000c040c000500700140011600c0c10b2510 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 4577660 1250 4576410 4576421
    0x305040c08030a1d0406030f02100203090909010e0615030303071809090b060f01030603080304080306040615020105040b061207050f04150e04050c0103020a050301030201030506040f02031914070509010804030201 93
    0x480c01203c1d51100d814002904a00d0342008041c1c182d11007840e031248600b80f0f40144030480340d02c2403112415030010f508010700c1080b01000101140b1040c042c1074003a41e03510808034019140c1000004040e00300b45061400c04100804418051040300d1503201c0301d49002048a0303200c11a85407080e101c06403220402064040e50b8051303d1898140443c00c0103010481000d50300608044a010342c6c203c0d298030054058032600c0c03002401c185414030014000c5810213004640c80b8ac4001c00000d2200c0d210a00051200118048800141e56030000c01c03041140482c4016040002101c1c03d00188603100b41150b9961118060140244150000d8804035110b41d0802040140e1a40350b61502d1070b04c803c4004002c94080b08c040d2114444c40d40d11a14550007072003103825141c2c460366114950783c21900103601501c0c0c0504040d422a44d110707501426036a4910285000348007142002034001001d01c4000103031a00054000d07144920b440070301070142d030880102c40100c442801c0c4240240e5560038140d00410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 4578910 1250 4577660 4577669
    0x50303090706080906160809030903011107050606040b09010b0f070203060702060402010f080403081803090405040308070e0604080c0d0503130308040303140901020a0201140d060b031005090f0402010305040c 91
    0x400841882558100401c01600356211550351031910b598018501d0f6403854240d40100407610448254414544900a125417007880d5104991070700c0c040a021908481b0f14035004814400045100020000700f400700c1500580c003114181304140407800026828541886401907004000554404400b01d50003641e109a400505884491810b0031000c1d46500040314203d00241001c401080c01c40e006a40c1d560081d50159100c08603030ba950b08030b25510058042440049110921031050316507600e00030741c2d101d01c0c440c1d6220304a80c02c24180192140a4a41e41140f080c04240028401131100140b01b1481c0d4404a998440c4849107082082c01c61080c8411400302c0c140003040070041c040c40000910882e4440d075100641441e044401ca442401000c2607680140c00466044000d588503a00160507411010070340c0b8a800e12000c40601100c06540c02a000c010001c810088107203031501c2d004004140c2501c04544505c0c245130714000c08000200000d05140d0342d00040707402d00c01005003400250 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 4580160 1250 4578910 4578913
    0x6091509041d01050714120106081008010507020f010b010201060506030c0a0905030a0605090c01050a0806150409060e150402040303020d0503100302060409090c17100e0111031303020c030607080109090201090305 93
    0x40c60b0122205020340800c54a0f000414040d40c06840c02110443c1160180404481401440e03420840c003110b1300d140c0905050310108105c000070481000c02e00c41c2c0c80c000c2d6400d400424104051004042c02e40d4800300c505419645010410002521000308403540190326040740ca40d5075502140c05c1e2621700441d0003070380e0103225a9000200b00021940614001c1e1554012140469002d01c01101c0341d01c50009003000048402c404a8002e0504480e0440650300d001703006800d16032160f103010308441880c1c0c0003642c12000041801407442c1402041c0000000c140c806501c0c090454070003039a901d03400c2c2042001c1050000000d403030442d460103090051a80100140d80d6141c2e20703004c040281881f62001d031a0001000400030f024000d4140c4040040083c0f00645140030b054403104008000c190741e100303419500d8012070341e140504180114880c02210b640d40e20310801c41c0c10002d140810b1312149600990145050001e582e402c40400c90441d8001c0e0004100d01405100486a002d425800145607 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 4581410 1250 4580160 4580201
    0xd08061201020c07031a010b070303020d09060e011406090103030e01050f0d06090b0909060103030207180b0904050f061005030703060b01030207051204080f1902040c02070b0403030306140609150904 87
    0x89400070601508686c09884581400c2401ca4405500d41c5028880c090f00501c003041540c0020b030007a005868419000100003034941c20301d40302d0b8015568034224140859555031024144402d4000342181c110106844645c0c15604594000c3c04100070f111013241803100c041098040a00303982c00f214940d1180810620107a035880481d5809440000c1025104207003080018442d00400a1414101d0f601540200f4041b850030031004030300c03444049943c0302a030710f410040c09651642e802443c0141e20400040a140a41c80c81030341c10501c02512010300c1080d00f10042000342d4002a811044e29082000080d08191440050300244209180140139000c3c082030480d0241420002c0d000311145002960900aa0310f5006920340b40c4c08040098104003248011003d0704150b441081c0c004101d0040781c0b505501d07504400000d400c80e910490020792181b0060103e955400704465214000b603500e1030500d5082400180310960400381002e420f2004107a8503001d607200d170041c0c0700d0366141e1310f50b4241 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 4582660 1250 4581410 4581427
    0x90604030212032b050a0c090e07090801090b09010e03120106080601050408010f06030302070b0903030412060902060301240f02030306041a0a0308070b1b0403080a03060b0a02010b04060b09030d0806120102 90
    0x10484248000040b01172801002902d040031600a8240700841981c91146540c20440406900754001c3e0240c030422200070400308142200340f1510603090f004807003155251800090325800e41d805660070310f482d43c0062086501d004490b802c00342c1968443e042114499441400481d200c1c003995015101541c00c2803032180e000180e039485001644e0180c0c0c01e44a00c10380315041d405241c85002c2034950554001c00041000d03110b0284c80d400498401e040c08501600d60340c0004a05030130a803c4100c0814144405040c81d5000914540c080c1045041c411440708403204080d489001c01030100340160303201c02c00d00e10101c81c00b00c02c12241d0140200034615180c1c590a20000c20342041354100c8174005913501041c407100300302042400c01184052004e00c7e040c150b686050040c1c1104244a040c180c403204007003111418423020700f2402c4000d9000240d0400560104025030703203687d004034001c0400b00882c2030309844c0800c0b180700107030150402c4501c1c0d450354004a20030348144c59141e02d05500c0031a2200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 4583910 1250 4582660 4582717
    0x605040b04020f010302030108100902040b040c02060109060f03031b02030106030605071101060b0405151303020301020412060b09010308190e0a0303020a030801150c0314070204050109050105010f0509060403021203 94
    0x6018074000d0b10200000f51400c8010360481c4000e01950709141d0204080c2d20800344690000101548064004a40b424024001c45d0943e50741803440000360b040312005000300342c52445070100030080c9405010b921451501c02512003c901d8524440c40111085080190b440940181c0015548403608026610b05000010450203010000d003110b5401c05000103011052642500c054580c000c1c10b4125407a40b00c594040503a200302510b0000317030904040000540c1d000e1001d0802840c0c494402a6440700e00d1403c04111001d9890440c410001d1030700620124140c08103581190100317030310201d040064164203903004a4102c030882d43c031240f04030001c410180d0210f400c42880384241c451445903601e410550807800801c4c2d515a00090101b001d25000c030344950b9900221030061a03c0e00e1920046401240a880090300301c080c1041e15000100400d50b8050f0000842344090304c2c01c4e5050010000004005100300c1c400a88a800c51a01c006d51103402401150b80800100a6440441800840a2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 4585160 1250 4583910 4583933
    0x70b06211b01021b0904020310020d061706070c020402030603030903010204031401050f01060c0318051309030e030309061602030106050603070206040c06050f0a110709090b0103050d110303150607060504 89
    0x4a9012160360328000702940005400c000111100f00d007002c40c1c00e180400e20070740050041c01a42d152242c1070000001a20724030003050515441103000c141c142c1807504240d00010b604028940a902c4181000b032416881000e031034115604803400f59032602c800b17000a00c0c40c02004071031035041d48005400000c01c440040401c41616040000740b025a6802d00d02d9001c20100340304402c007059002c080300000034410181c0740c601c40c8032110305056060702c3c3e6012802009441602c58200da42d5800c0803418103400c40c802070b00705d8808030000c618100d0204003107030143c0141144104148210140030003195800c0d00000090722002d0035054480c42c283d10300a54684003079900343c5090752c420001286d0345101e901111000301440064502d0300c500c8080807120076a0820b2801c0c0c035409000d0b00410100d26034014582201c0c003800f1003204a50544c10003500b00492050700e1824050418401e85003000e0103c1a203502000d00140c0c1100d08044401180d074a114005005200d07500c0c0004000800c100318075807 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 4586410 1250 4585160 4585183
    0x12050c060a1a0a0810110f0403030c030201021e0a020601080c0d06110405041107060605010c0206090d03170109090b01090b030d052101120302060a05041e020307030203060c0408060901090305070b0621 88
    0x2c0c8040390207540821114850b0400d00720030078504100074270202e401404400d07020341c071900c00186040c05648605185250001000c48098000201056410350401410b0702401411020f0807a0111010001e0400700e002c2500418058559441c001d0310002001506c0041002130418481e03803800c00c02c0302c04107520a5600300c800c05d2420340d01142a5201e09800d9514a5029100903e400c544c001000f0700a070030140304400b0814444140301d80380190850207802015200408104407049190400b0300d083c050300035800d460b151501c0d6420035907000484074410f5245041040c3e03a008444100342c0c80120b82100b0300010100031000255003003a400340504064007a500303130b03036640c0c0b0b94411441c01e07290b09840103040040c50707200b015000c0d070894021049542c8000e044031075540d507075408079090000444985689003008070701080300301d50502c4156030016101008200e021200e68020703003203004091002e0100e80c01f0000080468a410a858020605007100f00f00c40203601c0c04c04550360000c4940 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 4587660 1250 4586410 4586443
    0x60e0c01020d020c0a050904020d0f03030209030d030e06010e0702030c06100e0a050609010302060a0306081203060301060503030a090306020d020705010e06010801111309020304030509120a12050c060a1a0a08 91
    0x40b0040c0340c2c2d20100340307100c8003a801400100118600810041c90317a9010b00142e86c012480f8404600280ca080d6541d06200e00c40c0c0c0f0050703114042a0b01f00360501d80551035200a042c200011003a45910201c0c00300d040d905507a0040c1e00c0760322038800403480c50080004821161081c0000d20000c002480004000c554203d4038041d0141e581040302c5095910594083e07800c41a000d005000500e4024094034940790645400184565204020b503e041036403503101b0780041c1e00109210403400c0c2805614090101038008600c0d207111900002c0c11144170b0712024011560100b14119200c00070380448540c95000002404803610740307480c998903a0002e100c0c03803080758603000c2d4040510312008140c440300388641e140e46000c10300c1d00c44d5400181d80001e10031801c0201c00c20a400d9035640740300d5802e005521003402030554144a16145041d155050600c2043c0102804150303800100042d010317500500d04030020030881c40d106410f190310561340303a032580d000d14540004505507800080c0c2c00c011081000c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 4588910 1250 4587660 4587673
    0x408060a0605130b03010b04061d0702060601021506190816080606010e010302030c070812010f060314040204091103060a0209270106050f071a0405010e012903010207060e0c0102 78
    0x400034811500c00703204482d082500b01101e0b05000d0625440703064042c801070f0012403031a1080c000201200d94641041c40c54070821001c624414542d400101e6214150380000c120760300f00900040c0d036070b4541002c11420040b95000040c61611425102003c0400c0b4000640070313542c41744d0b0504d480e03c1498040c581150104040010b003902c000a82c4d501450341a1141480000f5482c0118040e5100401d1066040750800c80c09000500640040060b2101c44421105650520a100d131586a0b141d100784c08050820754207071009403840d100e607608154121400507081413240340c020300c1d47c801c4c4130065a1500560040080b0203010f074005000c40401102e980d990301488000150880300c1d090720b244001c1107110014018680164000c03c051000300204906040071a17480030310207100c01685040c690018024030080010134001d51441c442400000d002c07004115503020707402c04014003036004080444400503490b45080d030480c0d450f507402010a200b24584103415075900c44003020316134014030512 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 4590160 1250 4588910 4588921
    0xe010501060507020925030f0e0601080102040e0a091e02040b03010c0203030a060b030c070605070903050f030d060e0f040201050d09020303180f0a0602061302010912030206010905060d0506011505130605040806 92
    0x2c0c45140da0400c4e9030045040140b006d4642100240422252060303101e580d0b110500d0000d81c1007106900a04400c0000b583c0c0d28101359242d000150058500b01c401d500f03158105002620080d080318030506081390841c9420204e00005000c3d20800895a400d5486c0440324003a01d603020004611502c0364030300900c40196200502e480ca84012205881d40748001c0c020040042c000ba0000c0703400103038610b08003003510303143c3c0c40319400c102588968003071640c00003031001584004c60003100d00801154510101a00e031020000c501d0307190040c00241001800a0400e4201c0003c2d44800303d03071a0050112a150ba102454200d0968000c400161180d01c498151072083d207001941c54007565032681c0540100e8840f6901c441e90b0031740c0c043d012814801b40d92004212100c2c5204c01c01c0e046406503000300a194500602c6a00322070020300800d000701491031681000c1000010040d0441e140d43c030100c142035030004021222400341c0b04000ca00120035880000744c8542c88800752090303e403144195002034981c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 4591410 1250 4590160 4590181
    0xc020301180203030304060e0703080c01021c0507020a020d0303020d06080105090c040c0207090b010905060307080610020d0c020d0c0302030303090d1103070201140702040f0507050c0708030a050f0c010e0105010605070209 97
    0x350003e51660080001800007001d5800c80c0302150150421144907917101d98440020703400441c0d91008580d070221b0f14010182c1c110105111604841c0720410803420803101c000c0d12684421406030180090306000020980701e5030440343c15100c0000100310603030302d910a0f24082c09041d140c4940601c520300d05a28103107005c1c490100301607015002400154034105041d0040c2c4020040780341480070501000501e620707240300443c416603039692815001d107032860400c08132000f03440c000c42c11035010505569645400103920b8580780d8044400780d02d101d88610301400f0240c1e254000030f4050001005124501d50005602425130140f03840700b00c141c11370140c55640c0c81c01a101e0190000385a6135020380908100e90051403c503002410118925806d040c003482038802c00d58180c4000360001484510000c014040c1ca0301a1a05401841c9049900d0f1402000b9008064160000c690700240c5100c030600c3c00d6120b40071141e45c1c04021300507582e41c1c0c000606682c000c1c2e4400c1c1c5c021601d000004001a10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 4592660 1250 4591410 4591451
    0x302010e060705030f070201020405030a060501210c140f060406030207170c07090906090209070e0a0504060b04060315080a05060a050c0703080a05070504050301060b0a030e0601060806061602040207030c020301 92
    0x190b0b035039032404c51343c5109420546810241c503000030340d58208008219601c0911131400820b014504c0860554544980c455540d40d800d1540c100301c042006001000400841081044624580f038551010b480715000981110032400381c0b5500c102c0c0018006072031609500500b511034091070801001110071917000c030151085a0400c2100d070450341c0e00313011000300d50340200c82007402a140028007072801c0c1d000c00c0011310255062004151032172090103241c82e00a1000001e8a000e80b401c0c05000c5c90318103002c80e140550f0052030240f42d110316140f503071200c448580200500c040812901c101d1010b04040f80c4910090707030126280f60900c00002d005680d13400490b032540c1e43c56030314005e60343e07220513000008260191024007044420080007a80d50341c240900c5000e80329801030a40c1c2c56030203540c050101c07400e0300841050703a080403004210068000030f529612281c161036203a0303120303e01307a50740c00042c0d00c0c504029403281c40410104141948400001e003118400d5000f0410b030f05450b0a8502842c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 4593910 1250 4592660 4592671
    0x708030304081603030227040c0e01020a02120307020603100e0105010e090a0c030209040c03021207020703051b01030f02030a020c12040b040b0d02040302030703030203120609060607080c0718090302010e06 90
    0x8020480e0780910300f005946064400d000b03180050902c46070942d0b80c986444c02c80c15505443c0c440d0089008285402d00c03440d001c548040c1415000319081c10000303910f4007003040000c3d114440390051407030024401e00840e10200d60013480181e491410391828400c02c0c140e40164095061030b140041032650190815030a1420010300015260b42c03200350200252074000407400070142c0a2041c0c0c01c0d00c3d15140142e0000b140306071000340c1c072071281117080d0071600b90091103241103512070720f401c10205001142005000346000200350581d144800103030081c0c0700000c0400c1c0818070000801c41c5c6420700b94090241207481805a80e004c0b01c0a501c6d50640b4015400741801109040104001c0321b15090010100c00030b466002506050b03494000070f080061075030003600580c0000903500228030b507039034015a22210440710b448071410200e01051490003200b400528886000035014500002000840d0040211080406600640008400160030480c4040300551b00b0701c075220008a4020034070a1003030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 4595160 1250 4593910 4593923
    0x6040b1003022d060d0603030e04090206040302090c070c030f020108090106030507090f0e010204080601050a0b040305030405040902030a050106031101090b18010c0201180308090906060306010e1908030403060e0708030304 97
    0x7014018800d03580161402e21002c80840c00c40c1c0043e0044e1113035806030048074240040050583c0c0355090162481e10b81e413042d035100c1c9142069500040c0d031000140c4050720380585000d4a2551017051112840c450320300041e01c2900b000c0741c00410040b80140c410a240e03c03c2e84d40303044e1031700d0320200c2d0340c00e0b1580760000401c10f80100030284865809503100c0480200132100104081c10007000381401c980c8140c0040c08140c01c00001800a8105104420300802181d0702c0503140503c0c5481d056120702850040b103214689490340c0346c095580400800c245d4580140003040340b2036881c5420b0320100c04240200c3d0100e1100070b80003504900c5001a141c42e040603180c5006810907040044030042c50b01c0324102c1c1400076010041079014140ad40e4107014610542100780e89814400811402200c0205814030600c4100204003042e64002402d5209a5065802101c0c00f0701d601210071158640b41c0007101144070100c0d0002c01d00c5101c1e041000000c0030070f0180d42030b941c0c94003403440d10b81c4411100503049 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 4596410 1250 4595160 4595179
    0x30324060e0102070302060301030605070201110f0306010302070606030204050a06050102010c050901020a14010219020304050102070b0306240c1203190603020901150302130611010e01020a1713021206040b100302 93
    0x1018010040340004007014410384540c142c907940040c2060700203030405d482a9581e101088041c98092158684070000600064100740d8615130b4400c0743e202c000c051b01d04158000c609842001070383d4010002441c0c4c0144140864540301300c80304000e1242d4440c4038010341c00d2007a01c0ca03145004030211460620103a0251800103101d032255003901d80400c06600c405e650030040400e503019062030200c00c1860f20b038040c650f5a45004002403a180341d1380c04c100c0440004000f40800c40d40c62000c070b1a104140604030060461404030400303103e0140c800c0900d018003400c00d5045000c040d40c00114403071030048102d0068501e4107101c4000301c849130301009410030314000041c003e260740350f00503007003444203440d01628110040202c0c5a00c00c050b94131240104000c0f02c0c2c0700c02131010a014040c000e40d501d000840c205815035030010040340348407017012a0320a915010919109004d00041c4440c0d4000e400f410402c10090003195407460700321401d80341e03140d501010134420700e40e801c0000300300c0e84c004103031911 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 4597660 1250 4596410 4596419
    0x60605040f03021e060406110c09010e061002010f050702030a11010506010c080313020a030b040b0a05090c06070302030702040221150303073305070f020105041205090604180207030324 81
    0x43c4125501c04460140d07034060ba18403000c0da45c0b44010800380802d95550f10418030350340042e92500d805c141200d840b4001040052020410411403164049800c41c0c08104000204000741d00500c905010b841480c4d041130200501550000014240c1341c0c0700350740e8440c18034a000300c07403401ca4109403032035030001c0c0303580f41d07240003080e18403020355000b1100c1408556480c100340d00103090b020f4036034001c50701a20201c08000038040414502a8404201c0905100070315064002c26107909900ca1000c3c81584d02080700401d2620030016581ca199014004650791181c3d000320302d080708140248140c41c030160f02d0025100d98020800c45c40c2500c400750066003804015960034600081140000366840c43c80900e80710703004004c04075200d001d6841100041d5a040291006041d800110116019a8100814000080c5440841c21903c0c0814600243c949945100050140c410b0780c2c8105d03c007805130640c00b50f0340c031841e03801411918030a4a080003610100b40b0f0342c581c1003c48458074100628030420821 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 4598910 1250 4597660 4597669
    0x30602030606160303050a0f0b03060f0c0f0c0a050106050102030c15130f110906040b090402090c090306040302010605090105010309080d050423100608030408061501030b060703080a060605040f0302 87
    0x1900000c000700902e00f0300260310944620802090700070f8000a4403503041c04400329542c42032102003404594288685903400f404a0341e24130000d003020705520340301e20019140010700030903201d901ca0001c0e0460b6a441c851188240d0340e07001c610301a1429440c100d0000b403550f000108070703210489040e000e0301c603440508501c0b02861000402c010314a50200a688000800c44050a1412840351071116400041c820900c03411150081210b8001c61038006610321650740e00c01e0f0140d1281e41200c26507550750318034500600c24010310b074072660184070390000c1c8010143c044d0070140640718142c0781100c0316a03948004406072240c4080150680030100282d048201840e000076034440d001e41014071000c1c4e51008641000c0903000c00c0c4d40e282d070f08041d0325000300e0b44040c0034200041042a00650406041028280d140d83c406041c2418070343c10301c006840c00b039000c0d41105030703c041e00034001c1c3e464180504029040400895a0000d803502c2c00ea4081103840c091800e640949540880d8074194030706560030700 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 4600160 1250 4598910 4598917
    0xe100603020703030b0d05030706050c0307020703060504060615020a030815010c06020901030b100914030d0f0c0309081c0f2102090607020402030109090203071202131e06140a0803070b01030602 85
    0x143d04242d2182c584411545864401c4c03446940f040b001147d0b200d5050419008640000d4890040050100148142654001340000c00e07603410100001d250340341d62034a13100600c6541d03c0341d004554074400960107580c0104003000600e000c2d8548500300c0d9210b584010201d2034000a00703020480c0000e0001c0480c19607406800024810304000405000100009400c40c1d00302d45086e00060503000240142940004072903507940060780103214a0b141c0203005840e4000c0e041c1010104001030300200d060511a00018004048901c01d844070490310300620010f07900c249000c840490301c16402c0c60b075082d200764035012851103184900302c141d0802a1000e00607502580740e86034443d4081c403441000d030350b45d840198000c00d03000b200094040401d00c10f050a00c00c0304e900407201d003003040a07a1409170700c030f4072002c0c08912140d910001d8005107407043c036852030703072851204020f461a10001140a442860301100040702c12191100096550540d440d542d108100c002007030b980c0e0100c0100300003016a00503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 4601410 1250 4600160 4600163
    0x7020d030f030e15090f0a0b0402190902070303020304020a150e0909010e070810060e07120518010f05070e060901020319020a080c030d050c0405030606010c0302010b03010f05060a0e1006030207 85
    0x110b43c9504030b00503645084100d0300340218521041007170001c0880d0402103602c0150b1120013800b842034651b1241d0500300030080000e0f0240c69400d940c074492070b800c200361f60040c200c0c00130115101c00540c240200290000c48080303000e180440404130309458170b0b94070407031100c0341682d81a000f4070211040c03008151700501514200c0d0740b500c11f0740b503242e041030003404060540701c07000704280c94000688400f60b0345030780d10148240859006001445600c4400a0100c400c040e101207140d448611200884620030006141c0a520f44415484031070065006503000f03070b50903a1010807002c40b84081101e40d03c9684031550245e0710410644403901d40c3d0079480c3c600f400b02401a101010714680b22461158000307882030205400000750041d90304480e03c151340e00090402500388c2081d04042c0800c2e030761400504000c0c1803042c0303504030008043c400d4010303604070600a0000e002240401c6a5800600000c0d03521910070310510300c001ca24000d07041c050b03c0c03240f0752805d000c0180c58502078096000754042d800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 4602660 1250 4601410 4601417
    0xb030414070f1202030105070311040b0c0a02100507060c020105070c02040f060308030c03010312030902010c03030f0f110405010905040c050412050c0a0f090b1002031c020903100501060f030207020d030f 89
    0x140050462145003070302d030080c501100d00f05550a40c520425003100d0740106400c003403500e010000002d2036a1041503409407403844541303a036034002d040740b4a0f01e40003040000170750081400c0d104070310762039012001d00107480c807807030050000804620007a800c2c2c030411100b900000e074079901c0d400e0141c074084d003010300300d984002400141a038503030700c07403440c15802140c400c10346242c0040108100060f501c00300040d054589420001c000c8142d00003400700d2451a030140426403130340302c080e0000840303071720001c1004001e141c200840510100c17242c0300e540251081c2c50200d0214100002e55082501410154030000c0d55103500c3c0504000b47d10081c024034107010343d5203203d0002462200c0e00c1d41b002203005841e009640301c020f1854408039509880f09070800c81e0168104028000c40d180d00042583c041c007603006100c0d201d1940b502034148c004c2c0514945143c0c0f5203d030049810400c0402e5001c40d040c3d494941e41c100b440328010700141c0584c8581400250401000200103000c03a224050108480070f2300d00d0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 4603910 1250 4602660 4602673
    0x6031f0306020f0309060702010b0303040302040203090c040c030b0406060306050a15020f150f0603150a0209060c07030606090b090903040b0904021204060c0905012a020d050303010603050402010305010f0b030414 93
    0x322054120780207030300f43c40d100e85800020703c01225800c00403243d0003841c030320090100e03081c050046a1030340141d02c0f00a00440d004008141fa843c02446200700c4000043d20030002c41c18510f000170050200c134000d45000e98680300e40811180e03c00d00425042d01c001400a40001d46007040000400b00da0078660301c00c40c0656112285419814041e51038044102000d4030014103080c8a10150000007428980c13080c0d00c485181d8a00300030030501103501c5030a03c0c074016241d01c0181d0204056106011071f201107070103004008820403100d0313480303402aa20050300410883d10b03544103228124070b0542e400080703540705000421000703541070000d141004003d0009800d28080b40a02070001106407012500c4c4ca40307074028100513560199461004240902e440b084401400544400d4000b070244624140081c9044060564856481c0c80c010070394013030100d03952982e49034401001000c00381d41c101e00103400c00c4000a09240380102d41d03030545001c099074601c1c44d01c407696240f843c541c484e14001d0f03507402541e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 4605160 1250 4603910 4603913
    0x11a030c09010915080a0c0302030f040308040c080a030305041703010612020310030c0305010506040b0103050c0405010c0c0b03070503161d010507060905010608010c11060f01150207030605132006031f03 89
    0x5140c042d4030f81c000c0385c650014508003080030405642e982000801054418000c200e401012001400d80090305800c0580b00381e103844c10604090030480e0015880c0f4403452200c0e90405030700d54080d51055000d01c40c41c010700c3c1d580000c0300300148030038443c000001741310861100301511240c1c011600a0f00e0100c041c03603007035900d986001c039100326030303100303031a941d660344200315146c1000d00035940c0007242441c04004603c2c00e04200001c501490007824100906140180d00f08032454856401070119909803544034540303100c00034101d0740201c4408542461102050740d0322801101481e0010032450880c0030b4110303400780110340c82e400811040d285103407600464400709030700b0f20035200a050703000000302d50319058070f401408102c6140440025039214404101941204554040c1590f41000c0710640d54000c00d203080703180040300d41015148900e06814007a0b0078800801c6d401616104065003954000b402e168507441141900820380c010710100000b40c9400c4404044460004c01180e041c44003076200d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 4606410 1250 4605160 4605179
    0x50105180d030e01021603200604080a0606080d090f0e0603100c020304060f08040c27021603080105030f07090c0203070c080102040608010807030c03030e06070b0f040605011a030c090109 82
    0x20070000381d0114100300d0201001c0e50b070500885140d092034500400c54203285a82e50f2420712405401c42d29807081c000107055141e42c41c84211001420001e0490700d22503c2410410010602842040e2851140340c40d54000b05008503034110843c0c07440c1d2640f042452501d833400e206480d0013024964140070b0203008100f015814850380c5000642a40215101d504000c0e0240070900e20b1522882800504000c002c00a1016020981520640d101d00001c034050966450003030a1501009002c0034004500900b500080c56026102140a5580ca4203aa60796509150f1204010102424581c1007100b0038000300504c3c1d000701089900d40d104883c5404a00e4640900d0000b19801c085196500000c0400c0b210b036100307100e54003404101024102c090300d541e68041458015100080c103011000d11482c0d103660341c000941e18520b8004410224031703e400502e80da84c510003142e040303494611304000400c81e000e20104032200d4481e4100c07014a076440346503003003401e50410001181000405c81c400315541c0f01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 4607660 1250 4606410 4606429
    0x203030c01050708010503010209030a061808030f0403030c050c03070308040201090b070503040e0a022508090d05010507030c020c01021f11040b0c070905040c0302010309020307050a0b090102010501050a08060105010518 96
    0x11a40c000144074148160000c0040310186d00c40ca119a005009864503941e001c0341205808d0380c886000074528260181e1900e00d0804c1040c09004500040200034030300a0305c8848603c40d620039501002500010102680c4c0e50003003082e045c0e4954003d002e8100001d004103411a00540141014110255203200c3d502c1c0507400040100d4454002050030040c1440c0044950b8010200c444c066041000e41e4051654000320710310388011501d501682003091246000c1110a5080044e0014280c00302038101140a0501034540000007450f00700c281103042d01c0030030301d4400b8410513805000c012481242c01a551128456680f40443d5502c0302e1410801e400c030014402451084900e5481c0c080300f009507400d0880c1503010320030003400c000c1080001004103202c1c00c1920b5090030002001101400440e250180a421081d008003601c4000303d00261034501510302620240c0c028840b5070380780e030b0034000090340c14803e40300395521140c010300270b81d8041d6015281c2808003070700c41c1d80a0f5440b040055040c14 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 4608910 1250 4607660 4607677
    0x60302030d030605040b0904120516080a0305010e0f06030303010501050a030f020c0a050d020a030801051005090405040302010b040e030918040510090f02150a0c030302090604030503030c13060207060e0f0a03020303 94
    0x3d6440e401081a82020f0150300803164089801402e90301d0182c581c1030240e811407416604010740019900d80c007840910328180d907190480a201c0e12281d0200014000780800e0140003820400b40700051500500c540b00241b04180c090040d500710b03440d080041d00d0035000580d0b020181521070340710125440052010b4440c8022035401042901d040c2e0600301d0900070480d154104540200b0305503404030b03812080d0181120015503003070810b0040402c04031400c0c00340b4185a503010341000c1c1404181581504681c529103030490b0100407803003201c1200d07662849072450058000100250011841022400c0a9030103400346d02522002e503c2a41c80030203d8102030011510034060100020a40c1482c2010400010211280d0f6241030700c501005051040c281c4401001c040c2c0005003005aa2690402c2d200115070200c101c07900d034141003400d0022500302e0f04079145010411240090f21078030000c0c0200840c0e00c65254035090125840502c403076a5018130050b43c000007582800030040e1001c10080140d01c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 4610160 1250 4608910 4608917
    0xe210a02011407030c030c0206071b0e060618210a06020703030b0402030405060f0c190206040203010b041103040308090c0909030304020102010c02010606050a051312050708060106020d0507020d06060302030d 91
    0x1048140300240010342e00054000c00b164090000c000082c0d048010b80340c8094243c1040603030701c1414800506a4866194020101561000d05c0c200900c18550180f02782c483e80e09040030319903580018424940a000c0c07440bc1c0c0d491000340ea020060401c1c1c282c2c0700c1401d80c41c544541d104c3c080200300c1481d28940d900d04072209540019400241907043c426209076410894042d4034501306074650a94810303001d44865031100c00c0b44046810842e80404a601c0c0e000340f5880c0031841c020321007019484090855041e802942009191607030780c034041c4110710f4080c040da40c5031800c40d140d6440071074040f04004d02e00c2d83c452107023812200b41035440d81941803080d01014021a07403480e040c4002070035206044002e0056a0418a0a100d13480d0401c090700c4c144200303840c006440308050079162620711803941c1f000064401c40c52040303060003004500309060f1800007003217401d580d0b6100e500302e03640c02c44c0074651400030303209024403170041c07400c0b8121031440c41c0100b2001c20625201d0700001e04040e202210080817 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 4611410 1250 4610160 4610173
    0x50402070c060810030c0308090112050703060806090703030203041203030204090f06060e120303070e010903020405040c030201020708060105060403030e04090b010e0105130b0f0d030216030303020703080a020711010e21 96
    0x50f6400b68000740d0112100916400b294a1682c4030004160103002c01000e041000c0307040c2c21181d1041d0501114141100f406101e5800d11001c0a030050010303000b900d029001d00c06c0050050000051180100c07589a0300851900340b40c0400454180400201102010f4081100061401841c025144080d1b9845d20005026141000c080e0950f41105a0140114a01608100c41d02800f0040d07941c4064103081c0000c1a000000048840740d0711030700000d503c280b608050005010a0f1861042aa80300b81c003254810b82c0c40700303280c0d07555403000d21646600150400003032000a1058000c0100070b10702500116450200d030351115444a800d800020000c1c40c40c0700100010b14042d6040c0742010701101c0308215411a40000c62000011101114050070204549508040c4200154541080c0c03c41078548900d459240c01006580414400c2e070000d13108901160840c0d406208584245a10203400503024180000555022400450280c1d10000d011242004010151003021071820070300d024002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 4612660 1250 4611410 4611419
    0x406020c0f030109020f040b0a03060905030d0c090e060d020a030501020a080a06060906020307080702030a0b13030905040501080a0b040620070204060b04060909110712050309060f09150c04050402070c 88
    0xa151060744051480b0703a061504090141c0c903403c2c04042402d1069801084c54034014010800040140e44020103840c03400e0054800d0050110140c034000451840601c46048580c0080361426882e003d04407586000b20702003210b624200c62018203880c0b002c0c200c0c0041c00e9480e2074480c01c98004050300d00103c1e40160400809201500c11007018010906100602e01d050050007907580c05141c000408095001900400351358007003101e08800d6601c4254200a491315006410b1260504038080340441c112800100c1c00b851b10b070041d40c1c165a015130003400000d00d83d4030b031240d6000000d4401c3c1d8811b99181225858884640503030008584610340b40b030b641d4003140c0306101c00c562130359008520844040c4000d009603540089240119250400c0205209401070b808540510880c18000c22103091900403d52481e0400d01540c841c419000c00d841444d030300c03d80c0010b942c3c0b000703c40f003007100c1e049a012810203070200c042e03481d04030403c02c0d692424161a20085002c0383d00c840b8040e901c5c1070503100c0400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 4613910 1250 4612660 4612669
    0x130605010617090105270f03070302070603050907060e0105070609020306090d09090203010506072006040e0402030f010504030e3006010e09010c02120903030d0501031401060501020c0303070221030406020c 90
    0x783c2104032000208041d01c3d02c0200440b280f400c560400d09840ea0b0641c4041da081003c0113014580845002603a64907002d501d400780d41c498551180d0b0000c00d091000040b800703c0041148412501143c945c1d5500d145400c2c011103043e8440310003151741581da110240090b840c01c01000d8030403410f030402890b04500c5108050f2107400c2e1030380082103036030041005110940303c0721300fa00e0701700d0f0380449411601d8801020080c80440b51440154100b2070110b000030b003200408030302901640c02038042d100d000b41c5000481d402d0300c008880c082c0100d4031803000640d11b41804800f4444030701541d542206001200c445208036280b03071840e100d8503980003c00500c1001e00c0031110503000981d9000800850182a9010392118042d06103072861344c0d004122030703090707031028400c565044040ca0010001517840e854031301002c140c0c2c1590386c3c04a6103001300202d82035000040480d50307108010002c40c20b01030103030700f0007003509000424881040302c003920703027002020100b000d080642025000340c1040f408010601 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 4615160 1250 4613910 4613957
    0x408070606030b090f0601080c0d02061b030301030606060507050607180504061e0f030c090f0209030307050a03020f010b0604140301060e13020103231902040b04030506060a05150307081306050106 86
    0x5e26264200100400c18000300180104e18844282d803203032140c80040c000181c00b03009100c00c10700d1040143c01c0318241e00354048001c5040c1c1c1e2103084200b041540340c60086920703000d900703001041d0740c0c44100070610441c0280d00c02c108a07a10381c04068080d0b6113600c003040036070b50301e03038082d41284032454031018814600220b5540034182c403984c0f0b0404a031850302e81a03004501e80c85803000184d0381e107c040201003419012545805009422650b99801c00c1c50b1984d03803601c0c014000e03401406200c24820040c407041c0240c4024150041240c3c0c01c0c54149960301c0003010007041d80075455940e40342c000501d08801c050051103030720000e1440314101d06600000d025a04100b105003405003500016004610302d94884030f40122000080784907140c0e903417003140002d22642e0044000090b012038000300300200000c45912075101036071404845a41c800500055901511003502c0d0220248001503038144a100700c00d038000ea0620b4a01040c500300d40350035044800030b070010400540505404200e43d09100301c1d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 4616410 1250 4615160 4615183
    0x60c060f090a0b0103080d020d0c05030718060507030e03010b09040c03110406030201141e1306110f190c030611090102011a0901050f060408070f150207060212030408070606030b09 79
    0xe002c035200640e85001c00d086050100030004a408075001e03100754403541c140d40007220090020088541202c40c040c0494004690752000185c0d840070642d001c00001c805c586c12a2081d45034242402a10355042d90340c88250400b41d50599a0780f00c0e01d840d107a0311400c11500a0340940c0c0305000c41030441c00d090b0b031980c0d0780b00700090180303003031460410060740e0006c1d8803180c2c410f005030881e450301c1e86400340c41e01180482c034600b4007600e00802c0685116848403000d100700c42030b81d04d4580f000011078034602d483c0c900074001c8001303a410546040055440003030011480074420740752004e400d030300ca80d100403c0307540a0020110394003012030000619602442020b6503030707072402219810310310440e001130910101401042d020f5020f080301d83c00c03d6101d00c801c0d200581010b106031842640c0707844031282a00e030070340701e95080c1d0000354104803200c0307001042c0e00080e100e10340d020f003404091075031481c809613001401c101c442a80c00c10114022030900e204100c0a18480d00f60002d090030084c01c16860040700400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 4617660 1250 4616410 4616413
    0xc02130902030d05030a020909040605070207080609030d05100b03070906080105011b0204020d090f0602070302240408090109030212060108070b0408030403020907020c0d030f0f050304080901120b060c060f09 91
    0x3100016a8001412070000c940038640b60f0790740c1e03562540210284c0507603450142c201c4170320410b0204110340c9030860351007028294200c814a5548808440d5512010741d2036400e2500100700b604840c00c4582c00c00c40d844002001450310310380c6d94044030841e5501c00c03640400020040c403070500030998400120f9004101c01d103025500c65004001281e0800301042000b0b02c1231340e00217512074140c0b14540203011020b8210f188060a1002402c0c040080d40c4450b00c100d0050081c8494994450041c001c185038840301284000869aa0740e40c40e20030941c03001c1c50280c14840c0034240000140c2e03c1924425540c0c1d861005072416504d059480f80c41c1000a030803c076103000c400d01c024001c903540013054400301d0760112582c0c400e5031650303030086e0300304000103900da174001d0b140c549200180760300420903031360034042075942c00a829500501101d0314002a2001040c0b400200290603130f40d0311030f0780c2466000360124000908141e211002070101e84c005c0c291888150072030010800d84050211070303a58000390010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 4618910 1250 4617660 4617671
    0x4050402070c0503070803040603060e15040903030e030a05030901050702030301030503180a0f03080d0608030405030c0607020a030204050c03090705010810030303050601020f01020309070512010b03120d0b060406030b090709060912050a0c060c0213 108
    0x61680310a00e4000401c80d0140b0313620326500c3f080c544250084003442d103203807064030750b1000c010000504550044500f00503942c02d110220301c4a0744008202c074104c94209016608101d5200c89042c0101e82a2160700da10079000440410031506ca40702072030080d8030883c00789503116586590403094509542c801c62550308144403c018a84001c151241008000c03070303903a03550381c2c4644002021902c0640000c0d400c50315000420401002800c02540105592000c446003d43e40f81c0c01100c2924080382d403c0b4000c82c6401080000030b0007a0411504444c0c14016a094a00000d0031982241c0080794000714a6010040c1000181044444a090103030404000d003c0c41a22802199485501c000120540400007a5121803c00b0307aa100e00480070b00102855a91503455000601070540e05510310320460f03010000c01d40a5000b14607440865500340c42d2004060715109090f00d2a00310140d054981d80150346000340061604185403015000030b855041d0701d007603180107002c00300c0558550f45c1886450070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 4620160 1250 4618910 4618921
    0x106140310060e010501050c0111030c120a060b0910020a0f050303060109080c0315100b0a0201060f05060909010501030507030e011515020a0c0e060a080307050c01110102070804050402070c0503070803040603060e 93
    0x1000b603d41518020b0030107580e210319110702d113401480280400500000c0100900c400080007800a1044032020451580d03580c4402c0709220450344135106429090304204101c0c500c50a0001c00b508507400c541c010b40d40e14a80d5602c913250101d40400003225513400c004100041c2d586c100304a50f0180c84d50800502c0c0c03040090004ca996007400341d040f03201c9400d41000103105500c1203000342d800742006011a0f074a40c661010f010b03028024900843c0c0c5240c2c01c2901c0403e50781001c100f90748040b04018000505c40e440d020066004080103810343c41055142c2c080c94400c00002d010300b500c0e889001040c00c01c0d1520b0105071200c0c03203016034051000c541104458401158043d8a1401039650f95060352050380c4900001441c03018031580a20284d00010070850103110700420000d001500c01c1c0c86821108d81880c80c031038200d10503020000c24500081c041400b00313041950181c903203d48210b0700310b03c050f0784071000203140c82c0482c2e002e001c590307000080910016070315000c4c2a005040c0f04405071180d0038203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 4621410 1250 4620160 4620179
    0x8010e03041d13080a09030308010e0601050a08040201020c1c0c060305070f08090705090a02030906010b040501020709020d0b060c1f0506090103020105090d060e0a0303060503030307091e0503010614031006 90
    0x1011107250380340c5010000c00c258505603d001d400d00c6901a0321541d4600740304001a2080d0b070035200070350203c0c510100000d6803a01c00b44d80305100d04016582c0031b2820b0614202690500d0016000b40e045104030141070342c00f80c981c0c850b02d42c10902444505920a00649000f64003040c0030b03013003141010300700300901ca9450340114407031811200754144001d665490940662400d00d0b0340e802244c1c06552041800701501141c1e0003140100034010076a145a0780354440c0095030703c5584030312401a40025020804010a60f000e4030818542c04008203c0e03020000c00900281c0290b280d80c421900180000540d460400032004c0c1da24140070310030300280c9050000601c014034144000f0341130083c0003035800c00700d903120044240b40c0c55114500300b08082009481c90390b50595450101d01181c9000c9000c103c0e03107000002d4900c0303000140d880c00b03002405c00d6200c0101404607242512540c030030800c082210b580038016100904150b103141004c2e500d00c0c5003010301c1e0860107943c00c8011480c0c0101401014035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 4622660 1250 4621410 4621439
    0xf02040308030c0f0702030a060209030c0a0501080c0a030605100e03061308160218091e01110f090a080102030109090b0c07030c171b060a060f0e011203031103070908010e0304 77
    0xd28420303d91500c100f01105440c502c140b0382c00960502400c900d00080041c00e602500c000d160541c100c8d1021441c0310144080d02107140104c50100b800700c4009003201c5107410007409429590b21300850003981c2e4002040c00c1a07500c4071001d0104400326103008103801c08000607030740b0007185c070404d4004501c9038840000314428554007109109060091006544544120080307550741150403003294a0030105450310360408125400d03480441181090095005000b01070001d0541c03106507140c03d0070b003000c82005503c081c81c0a40c00c4110100009238000003031020714021f00c08100045200540c51800d21101d02c17000b0f0001c41c0105051005401090303000d446202003540c403096008100c13034000c4142c40e02d40141e0340006094018148034411904010804030f02640f40f88074107005054031001403000b4000c0300d00800c1044d0703007080010406554180710244000d0b009040c0002c1da22200c041c11103c0b070384211403c0c00800e060080030000060b091248441100c00240a9801d090074002007494542 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 4623910 1250 4622660 4622671
    0x812071511040314060106020606041a09040c050a0308040504060504020406020a03030c050d0207060b100305010e07080601090b0307031a04020a051605070512060a05010e040201090501050d15090207060f0204030803 94
    0x1070350760800c200a0000c030401c41d00515000300c5400d2095070341c1003500d559608240204001400380e4004203032981003900900000b481859000301c429800a003d010480e40010030a0700c552440c900b0008442d119442514040c40c00f86031616590390514050005585403076000500841c4104010403845902007010400d0507450329001c1000a9203c1b400c80700780c003440c0f0074040000e2001031881c080020581c0030018030001500c0001801c0d05505d0250b0484009200b80820b4503254400207400034860036905d503201405040003008130740c51310084c10150704103d698802080d42c4813128401168610072402c0c07400c01c102e071705601d400c2031000002c08900411200e070145107104004c50701080824440c3d03c025090252101caa041e00801002e0794404064172010400c0340b0304070001c01c80003041c00e9442d201e80d4041e1509003207203140500460300307903005220f00955030ba5500110103202822112010040c050030101588034955820540c045455403145106500c0c41040308000090a90050302e41c401d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 4625160 1250 4623910 4623953
    0x6010e04080d0b1e0f040e030a050c0109050a03030902090603060702030a050c01090204050a060302011106040201020a03050304030509040c02060117030313020d1a0a0203010914070c020906030c060c010204081207 93
    0x302d119a01c6900074100b450030441e407000009200d40c06500045a4900c1c4060084540080c024041402e003c1250b0210544540c40d030420401442c02c01d0082009000d41c108041c00000c00c4402601c6160522408440880010381c407000039405502d0b241340480d412410440141c4518201201c0c065540d00c24100044140000810303206801301c1d080d4804d900054000d0018015807801e143d00c034004242d5400200c3c0400c0c6030351001c0b1100307400011414415a81a0010314200c0c000d0f0300c054415030002041142040800c2161203200c1d20745010b15441d001594005000c1075042c43c100414105910003500f0740c0f64010310030044001035603502880d03407603010788851a01003d1030034000a0100c5180c25145030310119003c0c828107030455030045040b280c0c040380c00c101404a507654620107a00c150385103400940503140e1a400352a1040602c2d0300102c4c01002c54802101070b101194140e001042c00d12626540418100505501804003102035001c40c001c143c1392100d682e4810b400c00025140341a0403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 4626410 1250 4625160 4625167
    0x501080709030203060f09070b040b04030807060b060a0206041e05060606031f06050403060606090312030b03010213030503031603050c03011505040f1e050301051302190504050c0403030207060206010e0408 90
    0x3290281c1105005550082c040d5843c915181c00301c1c500548055417104203a00c07a00b000012041c8440080c1c0c3c05031045212824074042c1703940c80742d03403ca07084a036043d1071640c3c1e2400342e0a15079403407c0003002001455005011030b071900c1e060449904410342401c0410600210ba00c000040c1c0106280354450000c6442c2c0b9103d2701c4025070300303100c860303c0568690102c3c1e60101c049407d617003000141040302d1240c6020304c801600c2d060203c4e145a020b2100030a090f030700b840364036001e6020303800a084e4003001130001400c02030000881c2481c142c480c1e00980300c98200000740310301c290b102c100005600309e144c10706004d9401c040314040304c02d100501c103000300350030b0300a201c02c179062160b001c40d4018080d000800c0c1c10261101025111502d600c032100d4090304a04074005504e06043c001c0d18400e0303101d402c00041284040d001d00ca444203140140c0705c0d00c06440b0102042540d514801c190140c403070034000c00d488600f94a800707450003c094000105641c0014010400c18aa241d112a40030f50300000707040c1c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 4627660 1250 4626410 4626421
    0xf09040504050c03010e06150a03120e1201060b0703031b0207120507030b0c04181b030b040e0d1e020c060306040902010e0a0905090d08060a03030302070201140f12070e010207050108 80
    0x4002c0b56410f803039415401c01d42ea6880750440000d20340d0003001d40129010b211901041080000c0705680710041c02e90141c0d20b51500d0041c081d944020110102512080e8200748026129084520940100c0c8614801290190074968144600000c80303030140d03d0407440722011303803020750344011920400644014100d4440100401070010740025a40102161440c0c100388403081007a0b0010300400700402e6816030741d05001003907401589100c80150702c3c0000320214920013140035104038120160015250075185811303201c100144c07124003a541d654840303070108107112003000401005c40c040841d8000c4002c0243d40c3d03581c80071280c205100711b42c0081c561041e44010b0b6040d48080104661019042c04001110252500100d21450001d0140e4194000c08281038880310320959040390001013950060001030f000303a00038040c80f4014182003108400702c141d16049a4040c046800400f040480c0c1110005051428242c000c0701a00705140ca07495401c00003583c42c040f500c0f8050401600c10301241 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 4628910 1250 4627660 4627663
    0x40b0414060d0c0801150203070c03020108100b04090b01030b090708190603020904030807030501050d0b0a0203070302040b0f09040c2105040c090908071e030c110102010f09030f0e04020f0904050405 87
    0x1907450108140903c800300c10844040e085080034403404188100512011440d00e02c040704a401c2c09510902003400c0906640044445401c01888213a20b10080354020074602c5900c1e002e4001007000c0b48010032070a980c40001000ea0360380e000454080d401000c240f00744c043e04480c10680c051103c514404030100302840f0705001e0300040c0c2c00a07400c16408000c2c0014154444466440340c2e800b91024016643d0b100144144044103040241c184000b05010401130002c58000b0b54016540d80703800340c10b1685480000500f0b80c081060124540030000d000060350619008481c4811040d0500110750301c101600511180030780401405000c0e84c540001d41001140403522019102041c0200120a010b2400603840d9100d0003050300d07400044884c205000700e81503400b140c016419620441d070100d442e69440c48180003020f50130f0643d502d800f40c8010704c20441c400c0e01e2166000c1cad43c0305098070b1010400a0a4103d00380c4084d40903071700401c00d2000130344108089a40b10403050354005465034503400c205 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 4630160 1250 4628910 4628917
    0xc0307030213090b010801080610030209040204060e0106020a03080f07050403110d0602030106180e01030302030f070c050303030c03070305060405010b09010c0201120e16150c0201030b060d05010f0602010c05040b041406 96
    0x102d000340284000410115600c0d4400c2a2580742030304d0380403060340c90791412995000229152003802c400c40c0d41c1400142010089203400a1000c3c10101d8195181d000b41540e14009810020040c0c0c89801c245003415801006141c1000080319650300380d003401d103002406031107a030102600010709000030007030340e890308041d1801581d00440115200e50b1245001040405000314040c5c08242545010807450540c14a65040301c1d4160015441d1109022180841b600300c5042a100116840e40c00241070f01c090000b5480f03101520540b6560303103001c0700044c0403150041c0009004910b8100184690b00a5204031361f444042400c1418400c1241e10048070b1540c8088151101c440c00c00400b20148000003508448142540c00c074026080d0701c0700000989282c1c1d1131510303070001c0c00b071082400140d4060b90103100b180c3c0014020a10f040410034948007071314000c0c1d211031115440c0305010002d083e03080c800d180300002c0c5854401e01e024031345103801505010714028a501080d03801049901c0c1d5503060101d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 4631410 1250 4630160 4630177
    0xc0501050714070e060301140c040e09030c100c03050a0926090a0906080105070203030c0301050603150d03020f0106060c020603041202010204030f0c051908030d0b01050c0709090210030c05030c03070302 89
    0x4859a07152103d01d80009144203540c217500960a110319041d032041d403640c03240d104144007101e90303081c0785c038000d48002c0d00b01025050f120180800c20083e00d00c80400d2000c2951b101151b035000c0b070190f03820803000b002ca81000300074107412840c02b1070b80000100040c6c51481c0a1248000068500701c2d084040c10141c8030701c2000640c400d60f40840092174442e01c4d0010012240004001c200780d690b011026a1640720488540301810f20810043c0070703500d40030000d990030102a60303420359050103542c00b041443c885100d003640545c0c880802c04494030b000740034520141069183c4642040186c1d808030341d0602000e40000c2c940d8031030345864490603100b5810341e0011a00000741c0060b008603410300c01026200c502900d4040d0791001d80701480602c7c601401012150480011840d01f41d00342c001b40001e080c2d40f041141005020850490102c80130070840e4081d101c03441d400030303140407544108503c0040c041580c1080c5420500b42151058000040e02e50003d03a000096650703542e60300080740203220b0400c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 4632660 1250 4631410 4631413
    0x3010204080d09080111190f05070807140d0e03030a05030a1103010312030b0103051b0307020a1506062a020907020a0b0408120601020c0a05040906060510020c01080705070c0501050714 81
    0x5040804607440f4071804216074400300204584a14000b60307030002d01c2072402240307090100d0703000b8180e003911409986d000c1c107119290131401c0080d03e40c0c030700c07581d540705400c1a101e44628030800304d094a0700b44203021151202c2e09000810b1080c01c40825221301030348240b4030034031078080001001d00c15a90088480302846824036940c81d80c4a03c0c009140540780711100d030003c0c1c07500d000c0350342c15402071103900d01540d280c0c10b00c0c28045c51107102c0400d159100800403411400388107111000075031450b2031618122550600442d809007403000052604000d84221082c10006030690440001281003c00940390180d504c0246c035562480c0592504503a880014080c14103001004180240c04000c3c1c400e80c54280c1e0f8951468403200300484e50b40302e001102eaa4000c04c640d004001e2441c2c031f40c1c001d2014510400c0302155242d03483c000207500380c01c003020f41c50158001889154403036a01c002d809074029514113206007070a0a0b88c490707098510007802200e052240c00144d54042c040d05825002c500c070300030350 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 4633910 1250 4632660 4632673
    0xf09060207050d030b030a0f030203130803041703090d020d050f03030702060403090806040b0a0f060807080303011401080103050c0108250e01080108010204081c0302070b01080105060a0b030c180301020408 90
    0x19058009500c2201c05803518010f5102e070a034054404d02421100c050300400800c0c0506071503c0e2030041e040541d104800b940b0040002c01103000015002038004d294450285441d2490468003007400c9030341019550140d0020807078681c4661b0b0350840d560070141c041d208144200c106141117413820542001c003007858800402004101030340004e50502c910b1180e43d40c016401c4d6144000f60f136031803060b00c0081c100030300d6200140840780c8a07440f8403e0706004140100c1d40c560745164040c2050700c40c1e000310585400002c010b220b44242c1d02026454644286007541c81d41d855a11180c1d1540d210800650400005070080381d19000f20601d80c2040340400300700000105520072010305407084262820b804111150000035032800e040c030a441c00c0f600c101c000781c00610f03000c1400c0120220040742d4603081c150700748515030102c0e4503400010b010f0030b446c9000040a0500c0001c00c1001c104550101004410401c100600e00c01040103482c0507850081c1d482d0462196880080c1c0a4002c0d900400e1840c401c11 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 4635160 1250 4633910 4633913
    0x40314150a0603061107020306070c0303110a0507050c09061005030a09080c030705060106180324110309010e070609050904020d02040c03020a030509071401050307021c03090210030b01020601050f040f09 89
    0x1a4000b0b022284152010081003908920700240c901518078040d40c190403a400083e640c41c06205a02541e51080c0b0700054107243c400034200e8150404c281c00d0000030b0b00481e2103c1001010400c3e6010706c5012150601207180440c000703031844014808000c00c010000c000b24401e41300d1900840c100c2540200c40b0303070b2a05580c4100558a0300401400c0d56240309501c00014010701504503103086441800d625100c440c155101c0c42078042008210342c00c3d03d20820200c080b0200e151003805407211340b07a9146a502e00384051400d00703580080c6201c0410382c020040400a254000c10104d04495050701c520101d030781c46000180c0030041015001e50802e050101007240c055269000302550540f50310300700119181c00d048103a03251068003414481b04040091000c0c3c03580a00040c42e4002d002c3d00c115682c001290301070a441c40015a4a1001309403140b00580840c60a500007100070140c2d80ba00300411501480001e41e1000d041c441c0c00c0c0a1914844990b4964640f508802049000300c14188100e1485 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 4636410 1250 4635160 4635181
    0x15090402031e060904030504230303030c130b030603062404090506060102010f020c0304030305030402060d0608070314010c021b06040305160504050c070f0809011106040b010305010c02010b010504031415 89
    0x555500e04000b0440708001055032074408101d902440e0107988443c00c080c207100c1d54a00c4c01040c5080b0310516480c3d405041c1c2244e50400003140702d070010310441a102d00180c0f0800d901c40c0b11a40100101540c240300300701d02740c0c4000801c01d1344201281c2807000c05a10f40f412210306030343d41002450700282480840000e0040001d2040d014890a074002c000441201c0c074460300300e020720b0243c040c00360001c12040010074412809141c12500090003241ba01075003004050480d49107501c03103001500189001c200b032111490035552110b01b81c10081c000380e000300742d00946a50607032400d020020b403100040303429601e401061301c025680c0881158904034180030791032502c100520610788114180070010f42c0760303007000c0282c81c05c1e0769011140340702c0d1164940c0c48415940051070203504101c400c80d01c0c0503c1410403c41b4502550040942840d0355045040c89400d481d4002144000d582c1000c01d00788031640d224040381c08890b00044215100d401d1613003200d007441031600e00001180c0c0e554040c8185040d5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 4637660 1250 4636410 4636441
    0x5030a02070609060c0c0306150b04030b04020a06030b090402040905120c01050603010f061d04020103090c0e070e030d020a0b04020d060c05040f0e010f0902030907050301020313020306060a030506061509040203 92
    0x1e841d21511480c1c1c0c0c4d54041100c0d800c1400300020900b1030b18010800014110343c0058440385880c072103200180e5140e1aa10429800a074010754296108405100c19401c3c0709054802800b10b91070203000491144000ca0721501010300001d0145a407160b0540600c84140a0200c482c0002080e0301c4d91004142400b5000e0035094a101c0e229528016034040303401524440e18003221846480781c12140300041d80380e2450b0700000c10903414581c44849404c009845003c012000d0481c00351014003500741200018440300004446074000d074003418101000c203800041013424294032074104140b50740d8a1001c03401c040c000900040c0f04504020540d03c80c84d41207009001074802d044201c070501d41c0d0303030b000342c2001400c01e00c01c1d4a0445403c440030b000140140e0000c40e80f0424276001c4440255072580070a00720b0380b04079404544401c0b446480821450188030440c0c10503422a8644510742c00c503103e440d00c0788400750049100e0061600c04c1202401c5030300a945808034000c2c400c548914085094004014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 4638910 1250 4637660 4637669
    0xc0402030c0d0614010c03120f0903080f07090e010b0901020f010203040b011802040f06050a0c0c030803071403010e0601030203100305070305070612020a080a0f0204050d0f14030c0a060b0d05030a0207 88
    0xf400c04002050404901c1c40403a412041651400309011144e28260342074007a0030580c0319041e40305d0001b80905403481c0282143c5920941d100c002c9403038440c3c4100b0130244060001410400710394000c0004100248100f4156243c2d98180340d030783c03580480180d00e00031503211050b1081d40040200418170500e801c0d050304960404c58420090800305011304203e1195000e8048040408007040c01482e10890180054000354200041995810748414904200d1070b41f0032912080e0000411869a901c40c030b4881e2074a0300070500f64155414070440880d100c0000f8507072030400da0f0110010b21405642c0a10000454010003500c94071a107906140b61180c02600480d400724003841030320b500c044507034421502c401302650790ba1681625071951103005040c1205103d00583d800740710100b50f0f0384d030301c1c1c0c5007d00305441011148110402e42c03400d054841c1e4402d256540b560007d10901c00300e458040313103800c3d45a0780001c0002d0384803a80742c002401c0301c0381144060180d100109030713414a0b5400090086c1501c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 4640160 1250 4638910 4638937
    0x10306060203030702100c14070507060e04020903060402040207020d0c06080703050c04030302150405011112090708070302030d050c12030103060906050609010605040b18190303030b0904030801170c0402030c 91
    0x1a84409003a40e0700d103c2030380c2c04001a40a60b8a078a00c403042c41e0310510f0444500d10302060415802a814541a0062502a6603070742100c40104039281d00f0104010b1701450035142541002c01040c0003d0301e03a40018000303400749800280d20310443d6280d041000b03200d42c0c8480a414003640740c10300103100140445000e000b092620020918110800d0180c40450341e05078018505250741040441c9800d601038000c841a64844885c0d8401200f50b1000c0c011044e0395040d104c509241c0180343c9443e11005909c1201d560b00051000c4c405a140401d041c0880301d100c0c103100e561600400c3e0328910b0700c50b204040d00008400800040200311042e045002c840380101d1050005803a8001086840032007881140041202040308204400c5085c010302220010060384643c4a4154404210740d65280214104048040c4c0d105000b01601407082c10004e10045d201072380349113401c0d0340c007400c595818060148103928840d600c8040c10000c00c000740500001034800d5440307080851001c01140c01420515101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 4641410 1250 4640160 4640171
    0x20a0318030f0308071202040509071b06050a0b03060109060e06010f090b030106050405040506040501080c1e030a03020609060106080106050702013b03010c0507150203060111030703080103030914150a090905040807020103 97
    0x1241b42600940702030740c01c02001070b56240c98070242510380d892301e201810b4000013040420000300b08140300b654400e01c4403008c04505081c044041600b40300050301729803c014540b14081c4a00d0301008400f550099003820310101da402c20580560b0040d405034001c4c0d141c03407000000420740d664001c3c060b008880090340e0501550701c50300d040009607202400b1301d1019500c07000711400c440c0f400b041c108000415000451140c00d0600e40481d051018000301900564406028000c0d411020403c1d107006048a280884555041407401402c80c801e041001e41044540c1d40981500342c0318449000080e014040d0003101500140c282c142c407842902d03c0d003886546812500c144080c012000ca17100194030503c01481103055002c04402074101410080c104402000c501400c1802000145049402500e0300d4651798550b2400810081d19904801040841c03550300c21040e4030b41c080b04003d0405a540c4180d20380d603a43c50201d40001280c1d001c052681c5c10b04052105020422004201660003a40d00380031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 4642660 1250 4641410 4641437
    0x6150902070b0601031a040203100302030c01110c01050304062d06120c090504140f010203061c02092403030a0507050606090c0304110d020d080a030516020a0318030f030807 76
    0x407030045081c007074524140c2e40c000075031541c840d0f84402001030b0040102d0420170003ca012408903002203619015001a592043c415803a0800503103000030320900e460000c400c48400c1280d00c03080040c4225051040c003002107005c100d1940c000c040103017603c0100300006103913520304200380c0091100303955585181c20300c04030780207201303030031820702e0030740001030050714030310b884404001840c00500c1915402c49500c2502a40842448140441600d66002588905100040001034101301184000d0712045405c0305005898080203241c0c490301c40600340b90901003c0e19000c801d0054144001d0340343c000000c9102c807051f0080701412aa60088007100c0480d55808240044044292581c8075480c00910000340003549004a0300c180500c09800c1d10000c003c0f680c007042008458080444042034040781080c41141d05120301a400144008071401918078044042d40300c0c070300c2d0345000c5c1c00c01843c40e2000c1100c03c1004110001594000c007907403007080701c034180204442c809a40322000a42030308030b0343e103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 4643910 1250 4642660 4642679
    0xa020a090501150c15060e1005040b0108040209040203010e0106082103090604080a02031207090305010b01090b03070309050712050d0212040308041202010e09010b0a0906050c0a03030b0117040615 86
    0x18141c480c1d606880d0002000a0b070142d46003803000c01e040350074194001c4120189a0980a0840204a0700d00c00c1f0070300b41003101521007600380f5508000d001d80e15124200100307a901031051500700d42c040d40c81080c20703199400400e001d04107210a4920035807c01c03e000603443d40000d088040d605101c194500c0074064068174400710301c000d4800354116444200400c001c02c410340010408102c060040300d141c0002d4041402040800721740783c00125507050300800501400307005aa0410f0b80900c2e00c400d006041128450741408081c094200305561141e04008008082200c04050142841c0c6514212014a03100360354003a8240498018040c0861960b00d10f1884000d03603055a0f0310100039400d29081c01d06441e020840080160304110031a0a82455134441001d036a003e0302d1004941c50b5110105000075052000c00d6001c141009010094040034040210784092040e82c0742c50003160300001c120048030301800701029400019200000e00040242907400307003084460f09000c5480b0320396128243e1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 4645160 1250 4643910 4643921
    0x305010305060c03060d060c0504061209170c010e0106030b060f10090605030703021204030c020301180308010e090f0f010c03050709051e01030f061806050411120415050403020a020a09 81
    0x40a590040c0b001c690501e070b940c8061980b007540582189040c840ca03480f21020340d8217042e11030b00452030001341400a241d00984061861402a500744403011413960b9801c03d07540039030107a051207200843c0d0400036100a40104a8000300313007000740121526810042c009840954a980c400c00000b5032a03002b5041c00c2d1006142c0c99056140e80003880e01e071100541e240c2e0b000900c07020800d07600b082041c220840950345140198000d42c1c80b030048000a105046c00c40e00940003406114481c604084002944609903605560714442260b10a840700e0030b90071314044407580e40095070700504618006108056010710204500c1e03503402c0c0419200c180007642c080800380100c1e6000784017025080081521a0950001c103035040c9000901e904a01c0a00b10403911b554001041048600c6607070f0788010300c02e0250034086e00044804101c0d1620880c094442489400e4002c2c801d5608500084c007400860b0604c0c2140f0f1170103c03002c1c84589024135000703454511158040340319025003c0003050000192060 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 4646410 1250 4645160 4645163
    0xb0a0f0602060a05040201050405100804050f0c06090402070203010204030501060e1b09060a03050907050909030c010e060108190611030f01050103180b01050103090804050612060901170703110d060e03031603050103 94
    0x150142e622041d02400240c44011720680c1440340420001480342c0f554500e04482c01c20726543d4a450f400d19281c03003400c190180310120010703840845950927580e501c20827a00c08100889006030380e1091480424064025580041d2065203004000240069040e200301d100c3c0c91040b00300185400310b40c41241c1d050091460b82a0000002d01000190600903030009421105841c01c0340c900703070740c5d80c0005040501d048075117140035040410b04180c0c0050034080c01202001880280950351706018103150b6902e0568001d1400f8174491075400c090020a50004144002e10500340d075032880e10f0011140c02a500384200381c0041e1038400068811065089881c94541d0302c50404120307a460013004402800c0c80107004da82d880410030000807175a6440c40109005d8543ca10200e416140030800c0081c0c4041c160301003040c1800700144c031410389102040300340a69034010903c05005c040600814001c8004010042c1564600011180c9584000000c0c2d4411240d01c15014501e0b0044682181950300a200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 4647660 1250 4646410 4646413
    0xd03090803040b0a0e010903050a02010605010207050f0103091406040309030201080601020102030402180702120c06010306050603060c040b0f09040c02060a11120105040504030c05060a090b0705070809010c03050c030403060b0a0f0602 102
    0x8500010354001016400080084d40441d441035407016190844400200450100c1c0c1c0010b240d48900344c082c0541801028240040c207d501c0c40d01d0081040d402c0b0a2148504040d941d205500410046041565080f01850200e5100c2e261500d409408074a0301d010503404105d0400c00104151b205001b01d83c0700719809000088403424090f01e207400590094409002d50051415080158000328060400b00c907841000300305a52442c10602c0c1100e10150126000b40c1140080140d00ca03241300c1120200c0340035201080c0e403054425428130b814020740700d41c40e6011f8100005485003690001e9603d0098601100c204144d00751552104118858100d0700010b80c203859004111070b140c1f41c0d004603400f50103424105c424100030383d50242400e0089030400c10043c2d9524404050000c0150115032000580c242103140090540700c0034101d020740c514490400c10307003041042c20544070350151408091400c0c1240d4496441c1d1516501034080d0000c480d01821072171000080d81280e80328140d040f1040c940 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 4648910 1250 4647660 4647667
    0x1203050a03060b0a0f0e0f03100203011502071d090c0a08060f15030c010509060f040308070b010806040309031407050306090106091a0f010f030b03160602190201081807080106080f0d030908 83
    0x610903145242000c1b94560301c0000004a03008617103041c000403c5074424080010303942d604000c41e41e104030342c0d96800d110455019110078400304c60942c2c0120740b410039034107000243e583c91034070207850185081400f0790404a455000990b1590004100e40108d040d40060072285c0e0307a801c0380c2000b00c3c005074840c42d4564414540c0d4101b55004a00a040884001d02140d103801e9408142035020361041d40304403149180041c2810038071500145090141c0f499002a080a0400c0d0310000c00240190101420403403428402d180340380c0c8104004402824040d0642d03c1c2494080742c2c49000745402c0c811654814100002e0010941458840039000b42c4000d12007250711581800445d00103a030145c8860a159485868620540c1c08001003181c1002d06441c14081508040c4000e00b00030f2003642070720303a070403a000c00c48005070f8000c5031041d403000c001c4401080f8101d016150501d080e0b801d9002d610307a54600030380400d200c02d011402c4150031640e20100c903001c80030801d085080320b5036054050424039090 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 4650160 1250 4648910 4648937
    0x31b060910030b040c0c0c06030212040b06030a050a0516050303090a0603180501020d0b0406090203040c050105030702030f040e070206010e0906010e04060b040f060501030501050409020105070212071203050a03060b0a 95
    0xc640304100c0321882d180010f00000c8103400b1500322404801c07900c0c04507044400c0601000100d001040160800707107002e60038803003407040f46000c0d000090b200401d088000c3c0000f801580303003003185a103daa045000c4070101e0b081800c049407596500c405410603001c1c1c3e80c82c00b142c1402d001003111800c40e4003801c500c82d001d2500030308030000c040341460309401d44480c507180808644240090f1103081d0454000142601351031080004170765495111410290043c0100030110f180200c942003110001e0074400d80e43c1c0d480c024128218030560051250b160f0000c80c1c04207446000a030040c1c81200eaa0b02203170040d0341c0f61100031202540444192000c3d170322610051110001d074124564000e840740a0200c0d00c2420f500005068039070824441e07108c03e589007000c10540da8107000d1130380184000d89080280003100d400081c50b510441e18040d0040b10004550b945892013045884001e117a200e088c503503218201e25001b04030358030111381500000c1c01d114012400759200341c11100c1e01009600c2e881d6580c1b00d0f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 4651410 1250 4650160 4650169
    0x8070302030c0f0409020a0306050901050106090518070504121103010e0109050303010603091a0c03070206010603020a0f08100b040e01060807050a08070e040f050a02040602011112011a07060f0b031b0609 89
    0x28948140c0c3c100780c865172820300503201d400c0d042018520a03600400c2500d0102c00700c50864605034030080801c01d281c00c04021a41b00e101802d07491003284000c010103076444c400c4c00c4d2071038400ca41c094034240401e500d4080a01c80d80308007103807084100702d00070301c040e200080b141802d0300c0760880d0182003a0010801040304c64042d5000e50f051900c40d005848116918082090b90381341d04a0300030724004000401c000c0e0496043c4407003030160a041c00e0440c1051418040100004103a003c0c02d000d01500c40e000c65045460b00d0b610038028464000c0d0555200d0300c9810fa07200300f40d002c0c0b09a5002c210181c022a03035290103401901d040b48000da03191601642c91441c2111607114148046c0c2c3c20940d2041a00c0070040c0c903016080c45061407030005030381c56243c102d000342100c4008000c950301000c00d021142c4448106803420b41110410f020090600c00c024141c10f003e840340020082843c4d150488242102c15242c0004240300c030101c054500c807800180f41e40c4100d074010914140c0c4000d01f0001c07c0c15901c0c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 4652660 1250 4651410 4651429
    0x20a05061b03070b010608090604034d120403050a0b0619080c0a06092301140307020c0f12070902030901020d05010e010302040501170c100302090d03120608070302030c 74
    0x920a001c603140c04500d907105045500c2404203680d00141c590040c460260480c018030b4212414400a20310b9182541300280440d14540c201c2d41d170075036480a400c014001c0c420082e04c45403c082d000c1c1104c0c10880304200603a0105800180780c0c1d0103010b24404501480000380e404aa4106d00600010b5960b40c0c1ca9230031050000301070f19801035800b084500403032a5180110050700c40b1000401c1d100c901c041c01c00444150590080381001030070354050007654500c0c283c201101100503881401078000000588114000b0044981d400c4004010055003550000340200d0b03484007138a41514240026080c001d42c40800c605214555000d114100203c0210790b006680c040e4114000505015440e464901078900071f03481207190110503c01403095247c98402d850040c600201c1e4120440c240703001f9240c40c1d0720400000c1d032089461301e1811030300c2402901290f112000c01403020711131304034615015200300c0744c0c0000e58202902c0c0400105070700d01c00080541c2034a4000b00100103916001d42001244c90 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 4653910 1250 4652660 4652677
    0xc06090204020d09050c01110f03090d0302030c030a1e050f070b070311040305060405011802031203040303020f0d0507030b09060d15060905071205070801030308010b031503030a0c060b03010207020a0506 89
    0x30303802c02020030000882e10500c4c213124410700240c6040150600010001030b086080031a45130441804078180c108000100c944241040d0b0fa075020325406414180e04501485001031130034000010340d9000e0035072010300f1320044030120711010460500b20f00300b00c5450089400e500640a41008032002240e0410212a8440c800b4980461a42414034041d66107810941c82140c455024505000c20004207004003c00611807131007815060000c2d4002a5440f403400c03000d028012000000315040c50310a80482c0c20b0b856485018035900c903a484481c500402c1d040711a800024607028601d9010710b80340c0c2040f80034020003090503820f000340340c40b844c00610304080c03650301050340c40034006000703421070262510500d066203944c14060451401d074019600d0003880c4000b049907401c014000130340c01030030300d03030664006807013058807a03580103906046412b003001c41591512010a04083c1240c0c00413480d020340b4425a000d00111100405140c02d0740900a4020340c0030100c40360601440c20b09401400740030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 4655160 1250 4653910 4653919
    0x8130e13060e0f07080114010b07020a171606200d02030301091107020406060e0a090b03030307050c01180804050307090209060313020105040e0a0f050106020303070c08090a030212060103110a060c060902 89
    0xb004000a4186060105d621201543c0d4403032000e1428220410300960041c410781e41c00c0ca20b4100c10307a000604180c102e0103291041d4000e030b4200e03003c2c7d107003c004400340001e400d99400e00c42900c881000d001200d420500240c0c000e050200c03005001804540c0c20580c0b11550021030079a400c5c0b10550300500002505400c0404040c020080541d5640c0610380091002d41c84130003002140b50140540d84505410141905040c050090b07090b032800011031354060320350303d011a02e5019400001d8054003a1445140f800d0040d980c80400340009500100100e030422011180700d540c1d030f22601c000380e004c1c2040b803a40c0003609100140407110381c8203503681d090348145050707842e058850b10048000701e025031f02a969103507a20004101c1c0002482850301401150008605500c2c00d10001800504d803560000c0141d02c1c080307100034903034503038400c00005198002c000020300d1000b10344095840409200c255003c5031b0b4040b26201500b091203c4a050726440d80d203241c56010300d603c45901a19203400c00300e812 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 4656410 1250 4655160 4655173
    0x6070b06011d060f0c06220b06010c050307030206061906080429070c0201020c06030402090a0b04060b07050307120c0201140a020304090c02010c020f010515040b0301061208130e13060e 81
    0x2695207610013401c45040e980d034166210010000070030718010004000c25004440024006034a10600c40c0f101e492a900010f08c418554070f0600481d0100c003070324030040c01da00c008515942010f402003200d5110b00001e80c0c100309114403900c000c80020f1030600c224008900b034000400c01203071102c8003500c020414514600810748500342e403110b02107000c565a01c0016050f1004100319a41400403100c00780048410506504141c2c00040700d20740c01400382e0900c00e43c0e602043e00c6a48454020600400001c44050380740c640e035040c016220b074852002101e03181181c8029410007405500c243c085260181c1d0342c4030b03560034140a042070f141d02c45401c0381c055110a2000080c01c0c0080d003e2601e48400391344c00420070b084036010103440d00d09601d11700140b50b414001006610740d9803042d078186e10501110701081c0d5960b0100440e00400a5400002c40c10040341c829034103200d5148014505c40c4001e0b03102041c5607a88119424041c1c0d804c1c1c1c1c0003540300c00c00000c5000844c42d1500112408400001074401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 4657660 1250 4656410 4656467
    0x10c06022104030e010302030403051614060702030a08090106030b0c030c0d060f030201080a0509031c060509010603060302030d0516030509030f0706090815091509070b0d09060b06070b0601 83
    0x1210141d11180160920344102008101503000008101d004001c2c2410341c19810159006012800340c1d500c9241d8640c1504031000a11901e542001c08a140060a4404900b00300c90029201c0d400060604003041200b00032411141052003075104403500200b91403415101c418403a941c60340040d14100c1c1101d014000080300361458415880201a11004a50300364034500c000340c4066001000e40d408546850200006009e0220441d4032300301d080c210032184e9180804d082c0f40249000e07005186c1200e441000800c9491b01580044240d074021003c48040380b40300c502c01c4659216440c500311141402510000000c0d000d0b0001d0080b460005054648580320300c1e40c1c5514040c00c0307521800028250400030020b601043c000d003050307200a10b08544081c41c203032605070303900d560f500b1003495921b080b000010340243c01030181402030034801807459541c52202e041540034000908041c0c0f41d8526028000301d00c0e2400008840366a035101da12882c80d44d4502e8019241d004107100c07000104003c44d0340c20791 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 4658910 1250 4657660 4657687
    0xc0d030504080303090c10030b090601050f040305060c0306030f0303040309050105090d0503071208060a05030c0907031401150f050a080604110417031801050309030d0203060409020d0f060b0108010f05010c0602 92
    0x511400c3c0c1117009020004240e0100b0a41401c0084020145443e09004030050b44402c880d9075070000003824010b5aa004440020441d44103d5002420758001d800512a24a04000040d8024501103003200d10304c110400001c1d8983c8001d440040104041540800c0594003481c00740903982801444031038001055203d803030465001c200f003101c0c2034030041c08400f450f0381c02039140c0d5005001524010961814003001c02d80d04d040c0c0700c030042d01c510090000101076901c203800641d043e6500e403c060f6855650303181840c0d82c0c18036014051000c20b80e03081c00300103030901c9681501c82401c9136039030300d0180741c49100500008085c111140c01020804000102c1c120390010380305401c0e81d452800035980c03825196a42c1d0505c911004045040200030418004a00360010a941341c580031703000c00590740d44031100060000c289150009411045640300c040074480401000007006004285c14071103449913000442e2451024094000315110a400501c22544a0f081c4d90241030312901005291000901010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 4660160 1250 4658910 4658917
    0x412020f0604060201020703110304060c11040b100908010501090203070503040f03020f12040f05030d05070210091d07020105060901032616060207030f0e030601030308191d0705030a050c0d0305040803 88
    0x103e0142c1c6d0002102c10406503c04400007040398040041d40c2031604002d001000e21145c24006051800104020a40ca82d00c60b88240304110004290301f951001148016110003003c0c0700e82d030480d5103085d000003102955130080ba4424506940ca66266941d03d640c0c0f03005010b031450083c4c0842c400d43d4400c101c44c0b8420800341446084010080f611140352800c1108130700840d40001d03004c1d030448103c424a45801006840351164121050303101c0e01c002000440743e8101a50040c1c0300306a541000c80756140d85401000d0081015034001d200f566030324000e003c0329031001c3c400203050100e056400818038020059221000c1a01c110b094908001040e4503500c40d4550041070340c0080e40090030038100340d00f1074038180b024901e508000d072031801503c0000313843d003074144000b40c24884503c0010303a83d114a203000300f42000318004104010070010750400603c2040c0325003e50148150000450140750000c0d181e40c1c0154030800a14031043c3e0407013807080e00100464102e003440b1091002240141080c40035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 4661410 1250 4660160 4660169
    0x2010c08030711070f14030102070503040302040e0f010c0c0b1501020a02100207050603090c040509070f0506031b03090106050906030304080319050f0406020c0102010c0503040209070c03021f060e06030607050412020f0604 97
    0x65424a04020150131802e01c41b001715441b9031301c108443d400087c40030003500c08581d0101c1d0b00040714041c0c507805504058400040b142e030b07546004c420300c400c3d5400809000b683d0b40502d190034010b90300c1c1d0142c04100d83c40d40c1c0001e405030303000803030074001440e1100d40d2100e1a442803055603003c40c1c0c0c0f6404180d40743c1080e00c54000f0b9400020300780d48641800d110703946c2d10203615001044090302d0030802248a0b0301e14090b05d4025640080000c054549548804c80700015000703c969607481c0c2a0507180c02040c00d40038451156005e07070003141c510300e000019901641c00301005107180000c251081d00b000070841034031505114041c0418100700ca844000b800050840c1e4018000104100000a00f16000c2c8281c2c0028001c0620a100142c1c0b5128015603208401c1d00f00043c0c1506c445c00d0581c0340010170700d0002026441144070301401810394202c030040715204400e60711140c659604064a840044440c1400a0340910007000301001c0442c40000c481d002501007007904501401180d26a07019400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 4662660 1250 4661410 4661429
    0x182a080303040b0a050708070509010c080d02030907090606020c01030203060a030b01030b070201060608010609060c0204090816020f030c090f0c0c06010f060f020d020705010c15060f0e0705030402010c0803071107 93
    0x20007040c40381140385160b101031926403c00c0f0501c1e284071b02802d80c00c1c1c0035040804000000c06d2501c1c059016060344586a0b400c50001034035a61030341d4582002e907004483c49003c0b030054040000c1c00c03541901582042e02d0031500502451104100114002d410080c550740d8068044200040481c1c0250b1b07689001e940100d108012500d03000340080d0079945680d0110081000e141c004004036503001c1560400d403181d0f440e00201d40c8103180000740185c1080c1e60094010100005c3d00310820410703403540c9003803a10a0760281113151140007015202c032202100f40303800c108020000b07960b5160743c0e41050390141d03d20744914240f200503001c60740f0f4030009801001c507540c1070308018843d094002043c4131500c1d285200801c0d4605100000035105c0106200e50b9040c070920502c41c1c1c1c1005801943d4550554a60b40c0c00c0244642d1a9a081aa6030181c031480c070640010740081040790780300d1400c0300e104580607100c0d506550900d0b5181d10320f55100404007000c0180800c3e1414a0070310512140008040640 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 4663910 1250 4662660 4662667
    0x2130203041b060f05030403031407050901031104030b0406020702030a05010e0303011a030402011e02070504020f04030201090509040b0c0703120510080c0a0303020c06180a030b0415182a0803 84
    0x3502815110080d06403084030341281c081041000c2d0f1040c12101050085d1600035103a499130b10b0b040d00030b01200761f803884406110780308005016030b2000c007400d0704540903a024040c0c198691034a02040c480c9000240c40700d09200005400700c0c8054008200c0c00780301408540c00821075482d80307401c550078611003518981000004010300321a504180081c2c2070300840962a40c06c3c941c0c0043c0001d607090003c2c4181c0c2407a120811038031402031008100600001d04150764900704a400326005d40d1040c00101d020031011a8041345030b08000744564482da50094140015880d4900d80412030303041000200d04220802c0c1d11620705c00402e020b401d014019281e010700403a400c110400e8103084000303442c24000c4206590810100760b0014122828140560310603650303001540d040072095038100c01e1541c200801e84000802c204a5586051046002d400c3c8042c04009103c0907100b0344075900d424002c690b60b070345003070408149410226800c4144504008400c640d036409103850350942980007601641010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 4665160 1250 4663910 4663913
    0x306010909081314030106050a051e010e0d08030a0c030204150e0a0302040627020a0905010813050105040311010507050f0403020405060a03060c1101050c0408070b0304080c1005010602010b01020c0114070606030213020304 97
    0xd01500001d41002c944000203d0708ac8030200780c01c0c1c00d03280000840c9040e43d0920190300c0c0d025800740b108070200500841c1d1000d40301e08040c01c1d158000d550050a152030700b07205a5805109100340c80070340e013000b072604c0343c005000300080303d2042501c0107260340031000c28030000060b42c42e40f2410f80200f0880c8945101811000d0011490910400c080c18409004100d43c0e44d0f8594081d1414090701c5013420020110b46035801141040600d209001b0302c2580b80c0014401415004034500114001110081c00503a403070b40c0040b9462b003c2d0300c01c60452804140028401407500790070965200340c02502164015a07651100c01c15100c0451205022421a0040f070300401001c1c040c0e5503100c07000e80141d03446c06141a10302035859076203201d10759954030048082410006a44101d40d409810038003200c9050461100107402094284107000c099032a15003482c0c995400400d10b20f06186050b19405502a4410740807a01c50703004140c103c0b80d0f25030b03404001c030043c2d503941042c40450544440043e103c1c0b0f00f9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 4666410 1250 4665160 4665163
    0x102160f0302190e040f05010c020a170f040305060403020a02120c0901060302181003051504020f03060103050402060706020711100305090601170a320304030c050607030306121101021605030601090908131403 91
    0xa8529900315000040f0000105061120320cc100185128105a484010003059242c6000d41c2c1c000400711701414050000381640054402c0c0c1c0701c0e000b1030700920052000d02821755612000201603400c041700b403004000342c0d1300907805021540e40020b40c2c0c070f4030031081310002031002d03020301401004684da40050041d1819401e0f0070082e0343d42c1c280d80844c5052200300200f62035010040c1201d04041d202e00018085440d00d00603508850703401882552039648170b20b050119403c0e1310603038900400d911000f218115100303009003402100d405001d890b0690810845110545c0d5010740060350340303d00d01d028000251102c0301c060800d120b0031640c070913644001c250403032458a942403140d4036a00520051000ca040703020040101e4070201c80860b9142100e2070b060f0042c140651200407001404c103020030a00107202c1064121540036401d032105401036211403448010903020380c1d5010743c04240140a07283c45580400c240f140650180d038240001c00798014466041600440208507040b076141180340bc0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 4667660 1250 4666410 4666421
    0xe06100603060803090307030204050402010e061902010b0607030c0201030504140703110405150a0e19020313060509030a0903030c060e07060203180303030c121801050106020a020102160f0302190e040f0501 90
    0xc1c02006117103403d00a100182d502d03201c601000e4480d030390310b40c007007000c684c010b00c01c07200410400b6080546070980600c13546507231403801a846c03000d5400c2c0f20300c803101c034035007082140c184503815160b83c104c5174540c0d001100100310040c001c907100d00d00c003a080c01c00980f04100c91001944500742400c01003003140e0610055035805001a0424240810f844c80c4a542c0c11820000383e0307151640400355076403070040b44000c42d1b41904105080510010522420381944158684098000c480034422502d0b040c0d200341c0d403440749070041e00c00901100b40510020f0310a4111481030f0340600310110b400f00c0001c842030b08180d140e5020f0f0015030300c0020007408400850b2820b042d281411400b95085290000c000da65a22402446891200381e10000940f80108082010002e50301d150082081e0368548a010350307245514881680076200781c07600100e204102032140c0081d45c440e48800840185141c1c280801c2c00189842051070b10224030010841c40030f90700680388598000d1440d907101c01c0660500508650 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 4668910 1250 4667660 4667669
    0x2010212040803190c0204020403030908060f0402130218030102030a05010501080a020301030803060402070201050c0111031008120702040506120f060402011205060d11030106030807060e060f0f0403050307030e0610060306 97
    0x68081c00100104600072040c0d6010860100ca803126080380c1c072108580080000100a41c05440860003000f8135510818003000e071030419017258011303101d10703115002005080310000c0d44003403504200e401c50400b54026019a4004c00c41144d1415170410000e030a9030030845401045175501c000401940d80e03c00442034206142160451555045840321802d0b40b100070706040c0903640005440046910441c00ca5141040c0310008110382c50701c1c0d204c0300e0700e04d0f8415161600f07010f500b2480461428004074002002c410740411240c6403480d5a4244030140c0701c01444607a00140c80b807000c0c00540c0301444410780e0110501701038141031529100240056801c40003806182c1e20b01b504000715038846c50303246e02160307030082e07040c0b485a800c41001a01405803600000c000e003c1c041103490070006250012071218a00307030192500ba6803640d880b030400040448446504402800105003c00d010328001c541110715490085000380d203c4c5600ca2801405481c800c80c001c011850803c01075606110784000b90 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 4670160 1250 4668910 4668943
    0x3020606190909020f0405040c0f080106120b060d0b0403020106180b0d03081b13030c050607020105030a02030408090909030306090906090a02011107090606050a090e011805070903020603090a020102 87
    0x4290304490101c00100750301a0020150380c4081c8a0150741d10161005800c0000a109114514052030504010700c403e12071a103042001c0c41e804100d0b4541030144000303803038515016002407451034807248519640544901c1d085900800c0c0c04000c0f80c8815075907407140703000c0d400100710603140290244119441000300d584071890400035040640c2d450761440030668161526075916110b240001c8040f09840c58800c1d40142c0000e00c200112181a5840c01107a000c0c0c421014441d544500744009841000d0000b40014010400911200300a0340503603049030203040c2403410300c680c0402142d441c040649a2882d030b41d102000304001483d010380c0e0503910004081c040c00c010700344498980d42d03079010003000905014410701201c5402002300402e400410102c035050056942d1010701901c2c6500c22110040099404540030078182a40e4812038120f4265500040800340d94420b4800200030181c250303401c211010070008003580d103440c041d6010750300792030182002640c2071002a01d0600d0018008021 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 4671410 1250 4670160 4670179
    0x207050613030f0303140a060501110a050d08070c0204020a0314090106050a05010e030f010603030503010f06050306030a02060f0c0105040605010f09091707020118090504060c050c120a02210703020606 88
    0x3199a4480300c8040701d6120f07036801c204280c90f00e0154042c1000310405021a44481c0800104446a4001400721042030b00c40c0c240040380d00d2201500c905030400d020300700b544a040303c070681d030303220703044165118003180792003840689503600040a990020031381e500000d440385d6603c0c00304a04c82c85981d802c1303034009008200851400010405100140c42401e060054031040085541c0781030140000103e43d174002007001c0c940b44e1402608507042805005095a13203842c0205500f03018808603801580010000c1000d031503658204074907980940000209108107100d15203603004240101400742e40700e400007045a40c100351952040e00c080d0b40c0540b50440c00c10340b01e0804150350542100c0000004445a50395414500040c0c4500c41c451100c80c4514122180000302c460142e40141c1c0103038032034041404900400071049442d401059500041e94003e10344054540398140700030024a0010300640c1d0020710840e10205041e40c0070850031120420000b10b10041640c1446419440304044501c0780d034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 4672660 1250 4671410 4671427
    0x60901090902030705090306040b010311010903050622080c0d02010e0a0b0f0604020f030a0209011805010806040905120c07030c050109030804030f03020102041203020a03030c11150c0405060705070602070506 91
    0x81a5000e2281c01861a400408141114414001c88801c034001404a68080c213241c5045030401034248000c0d504500100c00c03070724866204440b20f204498114004046a46801507110308000e0a441071203000c0d42240c01213800110030801400a50056102030b00600190100c0a8291034003400080c0e6242c01401032a00001c41e0503880c95000074811101c801990703181c50104000b4490b00c0340c00c40c100c0d0008010080250200e40050100c3c20f401c1c0d03100780910806051403202a60a401664040f48000002a403d4189640400101c40c098012206862040d05020500b80c0c802500c42a46401c005070900c01d10803500300350402458203280520707440c1d03c0c540720f02c0c040d0b01450000418003440c1d80b00303000c28540300750140c1d8058651481010301d03055052801070b50741c0c60340150480109043c0030b15520401e004418100d42e0b00c0c00c050103022410f4400c1103c0300351100003415054650010702020030b00340c58040c003801445104e540100070076800e0990180c039101c000da00580c400c4204209006 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 4673910 1250 4672660 4672667
    0x602030406110708160315020304080304060b040b040614090c04050303030103030f02010608030301170c0102070b0d0c17010801060806100b0d0b030a14060709060804051905160603021305060901 85
    0x2030846090740740516079040e01460040c1403110075030000c1410320074081d54140a88400741c1c2070301181d2207010941118402103e14000740e010458014000b00c0d030500009003c074405030804034186000500000700c3d2100100002d0441c4d003a030300540c0c02a0071200403211103003040d1a480741c2080003002100c1c141458980041d03a40c2c4414003006003005010f80c0c031490083e000350000d801504000d030a6903100e6031214818100e2102400c1000d1417440b4503d0301d6031a41d400414501d00342c41c0082d180034548500c0c1400c1078083e00412982c00c0420111808005104410b0982280038180741000400c0c2c1924202c2564503008018080701040e01050700100f00780702d0340200b120b01c984034500c80030620105d9007001905001540c8409490191500c0c3d90718500500440d601d4464145511501c904903140c1400300d40ca19402c90b401000ca0f44044400c031515a5002111011240301da402c450711600362050010b00360440b54051804a900458496210740200801c540a00000c1c1c411300d042c07080c1c070703c0000e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 4675160 1250 4673910 4673917
    0x40e01030305070203030705010e0d1709060106030b060405030a0b04060c020d0e210105071e0309030e0607140a050607020607050702011d12010603050309090604050c070605070302090d11030d09060203 88
    0x80c184400043c1450454905206542025030000020400c00c0c0050016945500008000200240c1200c003041c2001d2400949a400340c12544002c000a078208503099000f400658410382d0b01280c14000061a0350f0108841d048841c4124143c4109080c1844d03d401900c09801048041d50030843c01e6981c090f40c40940d41445113001c403605800000078002c0d0110b1071091105001580d401c0604001c0c0280c1c00c080342c0203811942010400080304040801c40032a50340000c0100004c4110804140701e03d03006024204c03060082001210048040d00807503d8240981c4086419800030820005680e8040c05129071104890900e907241c000b999000034000c03000c4941d07211144000c0c0009200303e450f0464110242076003079000300025522810445d6594201d1020307584540b00f10320000d0755500b041c2c02064000d407500c030b42c65801d00e00385035103080140800601c1a410142e0a10060f0203595600000c910003070300516616503051104000d250404000b200c0f5a018003411000422040f81e000046 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 4676266 1106 4675160 4675163
    0x6030503030718050102030403060b0a090c0804060b01030506091801090203060c070b0105040c020d080901090804030c0501110109020303030a0c0c06020a03020c07080a0309030204090f02090705090102010c05040e0103 95
    0x24603586038298003921740160020302003000003034030382e4000107601c500040001d00d00c0c6880e031012000320b07881c1c0c26104001400107024070007481101d205460440c0c80c00c1c0303001d20847c98080d021070a81030002e0014241e500a002c0c2e0700c105184207500040b002d0741e005003580c00c2810031403030012403600a20019520615141d0001481c4c0c40d00384101c104061039030700508036030082c0010941d004400140034000c03a5482e4024a000618104000c0003e944200c240c880194103210005010a4000c0381021280c3c5c945140e8201581c0c000081d40e41c0142c41c01c50100f0000d54034041158a07105c4128010300e900d00204901c003801d07401d500548100311648084030560340d5240c0030707280e450700c0e0303418041d01181900740e042c00541015000364040c1d40c0540c00103603002e126035000c10300e1048116041400110003082458640da82802004890010b038030b055420141004040d10701c02006200 = true := by decide +kernel

theorem cover : BRFrame.Cov 4496410 4676266 := by
  have h0 := BRFrame.cov_init 4496410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4496410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 4496410 ≤ n) (h2 : n < 4676266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
