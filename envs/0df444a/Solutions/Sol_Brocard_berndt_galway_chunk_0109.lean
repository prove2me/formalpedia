-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0109
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:53:25.752574+00:00
-- url     : https://prove2.me/submissions/d304bab2-fb4e-4fff-9759-abfa9e9100d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 19424466 ≤ n < 19604322 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 19425716 1250 19424466 19424477
    0x5010c030507060b131a011806020d0c080f040f0e250e12120d060803030403080103030c0c0f060e03060610022a0904140f030f030103060b12010504060c1d0607060507 73
    0xd045c0d00080c0c81d43c4004500d103080d03c50120b020340d540c0140b1030402201d6003011a04a15044c507034000e6903145129810b5080041c3c0b20703d064180010101114000c140b0780201c076a4a90b201c03070400008980c1c502c0703000006020a40002c01300c10505144070f8070408045582d103700848503d0856580c400082c1c001c0c0e0003640b80729100f0041d02c0421071070328041082031549460f1400d5120380c8007110b1255000d00b405070401c000300400a640140b00d00e0640303905040404030a0020304144035100c42982081000c01c04001c0d000c2806504600d1a4550078030031000c0382c0d140d6481c04140101c90303001400f0b441c0564441c0114440d140307089051000f41c148800201d02740c144035040000d22444081e40c0a0f5610581000c00d00013062040c0009541e4070782807401540780c040444100e584074481448090800c0d6030b41d40c0003000342d41d561482203442e81140c400034005410715082c50710041c0352181b42c1401082080710034880c00403045414464150340204098100700d45034403002c0c090400144094108070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 19426966 1250 19425716 19425739
    0x150111060f10060503090309010c050a0821010803090307090f0e1219020304080706030f020405040203100e07030c051909030b190501090905100b010e06071b05010c030507060b 77
    0x208126403095401c00440710042c02d02507240000c00386160041401c0100c1081040b085200c00030490705008030a00c4c1900d181030b440d0600b94184024500010500000000d03207450b0064240301c1e07035040c00304900e10400142da845050659900c500400144c0542041030204019119940080c009455056000c5080d040014049042540900800404c0c24001c41c852101103001007100c1000800b60000394500345c14103060607651a01403040c40101034031fa0b05031000e5500703603805407001054050025500c900384804442d03040003050055006000d51440000c613407078403a00448400c2016903da1901c1c122485030240c024a001074605800c0c420020800400211240d0364039100f1104000c10080d003401d00032a400c1910740c10307884a812a400e1071360020210744080396581178615141c50000760300c07048000607035203c80d280024642c080000700310034080c4496400c0c0c2200300c00e0485c0d00103413141d450700015030311004682c402030300180b400c0c0040c0d000542198003415900703d00074003204404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 19428216 1250 19426966 19426997
    0x5060409020334060207081506090408070302030403061d0c09070f050d09080a11010c0906050a080907050603190e0115030f0f020603040c06030e06010503100f0204090204060203030403021002040503061501 90
    0x2ca401e64004e0340164030858040001400a10044500090005900d00c643c100540061417001c006440a050010002620000c06000b0022580110361161050019200802c425207006485140070715581c003c980304136806203840f00500b44201090740f142a49080819021166908580980740e4815034451640000c00c2c0d6140143c030748111a95100c41031550341e400e0590a643c081820401480660742040c8003071600001a61b011004924041d5001ea9408044929100c15035020301d410513000002d0010007034000e0004c4e845540030789414008070806948086c225a21400301c60003040c1d15130002e2002404001010070918000d0750009242d15041e00040c81591040d40c045480400c03d280c07c0001341e8150085203890b0120001901c4d46600d0540400d4490b0001000c40d0f000581e5403111060079010356059a0141000032021034607203448000c003039560b42c800e070340030b4001d032089021a403c00841e0b40200c0341901c8000d4003410848d200c980c0e44171045c483e0340740728a050084554950030348 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 19429466 1250 19428216 19428313
    0x30203070e040309080703080a050901020c04060305030c0d051611060712030504020a0518060108090a050a080a030b0604031a0c162409080412080403080a0201020a0201050604090203 80
    0x161206401805442c2001c0c68064152041540003004542107203e08001090052060350200c2c07800742440da64a944c21070040b03003040344210303000d0341c00703450020040180240000a42002e030340380005c45d410000000c80980f040e004c0e01e800c81043c80d0490705101e00041c7c0210010781034036809042142011080c0c1c1c1e52a4a0066041e6040c5c0042d82c3e49081105504e41340d0114002050265518204444407115000002900070215418071070510086204541d00b04214054550890281c84044120f8900024503034412038104001a044c0358500d10701d40303059800c950459038000c40c112400204041002c8110303000800500f4200390900400c00c0a91644014080d102e01c1020803a50300521604407500003e0808210780546182440003000184604111015145103c8548400d5025450203007110300c0b03281c02c01001c0f9240420040c0e00107405401404029000e90024410303503440030184011600d446a003c0e5150340655a0700303a90500181c07001e1840030098034a0801c04803003c140c5000c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 19430716 1250 19429466 19429469
    0x207050601080d0f090e0a0e031b010506040f0510091e05160809060c160f02060c060906010b1207051e0c030c0106051206010e0705190905031e0303070309030903020307 74
    0x64002e098441c10556000c0d40c4c020001c1200d0130500f60140c00e0420741e00f0169402170a004001c2d547d00a9100300e00342c200145d1700161f18680c2e490100d402c0d40700701c840c0644429034034030340510705207044005151280c0c090075104404007460024103501d030035411400b905040070b50110041201c0800441030519018003407141c14098030185c1407602d603500040042c0030081c02c00c0600e8014409000c02a045c1c502242d113410400c00b45441c024046007410b103422540148004c1d44284001080084101c01185892140c1c400b18150b5119a0707a5201c01515842000c945501d480710000000e58400d000b078000d00125104a41c240b00715603007007007174018203501181015450358000304140c03100704400d0060b08060035041d81d154041c500c0c1100700c5682c403001800307490301c0e502560000945032441101034441c080e252800c03121404088540103800c044482c040c4601900601e4821281d2035030096402130a24880c000440ca55030361030030200d0051405100440411001d07440000150303404009250 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 19431966 1250 19430716 19430729
    0x50f19090c0e16090e01050120010501030b0609070804030e0405092d0d0e0a060c02280609060206040b040b06030a08071515080307060f0e030c060403030c03020405030616030207050601 81
    0x90b40c1d4108402038100201e400d0712440d00b0030100020a00c0412284a0041e0440c3d5080c00c2038a02c54000800b21500c003001e401811140750301c1c1c20000402c0c4400000c2560248800707460000081e26205c0040350002422a005408105070461740c02403420160312080d4032071400010360ba1139640d0014002c03810082141e909118040c0c0d0a070422580300241305103401c0d01014108810400401d0020811000b550710500d0184a00c1c80340b204207645850303190540004400100b011040c070f480c03031a006806141c1c0650000601c2c40f40010403001d00005181e0300841e007040400e505591555034003500300000802d820b405001d901c2d852400900f184002d01403071032199201c01516448446240e00300e4410304151088284581c004008000b0302001b200c620036044030010403522800c10b011030151038120380e454040d1000044c10104250042001030180b403003980d06100b02c4902034003c07020b0707000c3c1d401896810313000400451000c5001c07400c2103075440c806003005420601241c68490800400360b1105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 19433216 1250 19431966 19431989
    0x30f090604150f03060504090309030b0405070503030d06060906030207030e040506060d02070c090b0108072115120201080c040b090402030405010b030f150c03041a0907030c06050a1101050f19090c 86
    0x103070074244e05801508080c000c1560200a20303040c548005020034100d100240814880300041424450217010782000340202804883c5d0ba9810100740500421580c894800007401c01c5801040d6948070303008907484242c040e50750303d0180b4902403c100043c94090301c0554405420415501c602440340094503010340103032501840c143c40d1405100c04c2c2ca00c00020f150402c10000c0800424070303000300694109400a00c400d84807854002014002801c0d84520350b41e40d9442038400058940b448a200c9070441d100303981d44000e68079545150110b03070095024102640c00180040d01c203900b0a507014650040c09807001240035010100880e0504401e0748000708075410002421701a02e140444141c0c20802ea11412441d40c649074a45050300040c1580510381c900703216000c40e150000800c07840000c1e541242c89941150b5039008050065444118440c01180188000301d80c0010184034891140852201142d07280c0e0301e8881010012107540c2090403883e0740c1d025a1800710f003070050304101520740f05001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 19434466 1250 19433216 19433237
    0x21011120903070503010903020613030912080406030b0909100c05040302040e01092006030103121806020706121103040f08040e09010203040209090105040f02060309100510090e0708030f09060415 86
    0x2d2608194541d00a103000768100591080003c2d4001441a4041e08801c04100c40c00c0c031a140c1141e411035254005c02003185017001c40e00a10404000500c00c41d0103644040100c24019001c0c848a1141120481d2072508240c6074400714000e04d82054050358001d00d826441c140d203940c001403c5801710030704002c050303554202880803c245142c85a525203002c050503840550234000050151005010003800d41c041800520300240c010480d07025a440311150401c081c0e42c44400007980d1305100c0c03045900240011103408081c0c0110f100b503040340640120101d186540b0780d2901d101c00e1000200440715040200000252450000442d5016032680ca001680ea800c0500400207101405031440c1d0f02645407400740070005401001914105505039011500c0340c5e6221000e44c1045680819000f00da410081004480010980450151800b100c0300700043c480c01d40d0220340d1a12103004100c000ea2080000002004040014060050004042d1441c2c15110b01c00c030007246240c04082d8010038151400b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 19435716 1250 19434466 19434469
    0x9110c06070507080403150603060c032c0703111906080103110108090a03080408250203070603050f0c0c010b120c0103050a0c050a0503060a0806010303020607030e03090901030210111209 82
    0x80d1540000080c5401400c0403401d480b034850912540c03100600c4601c03051009071424421f40c11003401590856410420094039010180150106d5411070441318031001e070f9540850303000403003800b89500c140000e1010790f00310381c5c81c40c48d55003030b010229900c05d186030600d1501c2c2900d401200080e296560300c80ba1254914a050352464007011040350610035404c04000340040000740211815802d85071118480c0c94038180a5031601c0703000045025201850780100072035031003144000c0038030310a80440c4c02d4a61303980f03012000c075035094413640d01614640300031072450828030000c1c040d229120000001d003009080c0010b504a000101d4810480c1c010014001c4150f82502c60164420b0a041d010301403524074441c000c4c914440c0000d01c0d8240000072000c0b402d25101e400906010302015011180d8650b101d090107981c4040c100c402e00002410710700030f80049032000c002d60304148400380180082d40d0071a42005000c80301860b41c00208002c8040c200b0760542c1c1040324226440c101341c45c00c0c5e9200500300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 19436966 1250 19435716 19435723
    0x70806060a05150306040b0613080c060901020c0918030d06090c0c08090d03050c0304030b04170403020901030b040302100615030f060311060304080d060e06010906080403090b0309030409110c 84
    0x3040e19206424418003081103403101c00401810b4002560601c0e0b582d610900010010111112101d40001c0c000c6840b803111004211910240c1d01181d0880e003400f620300040000c0c51086903801401071300710101c0c000035800d04850803904078681c0400f5000f0f40303c403100010318540244522441c0c154441d28108100d8000348117440c4528900c0c60500f050950a490305205442442400b5000d4500c4000c41d40500d403041050395110121201034a58650317890034012010321050310107456240c03018064000103100c2104031002c8990190800111740e20b0f54949051040000700140c056004110342120800000d2040300094090080b100304d4440c0f0343c0200404450100c3c0903500c404d490020305002142d50b8009240b420042141e03d07696a5486203049900703070040c3d90038103410604000c03000c80c454602c540c0852080c0420303610910b9042c0e0f1030004907025330059034090082144007009100091640d801140e01c03c0540701103a1500b56554414001c84080c401c0295000b2008254404041c0007803 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 19438216 1250 19436966 19436971
    0x70e01080105010e030a1205090607050c010e061305060f0904090308070906030c0503060906010e0904060b04050c0a0e28080a0605010f150f0201060302040507080901051b0a0507020a0b0408070806 86
    0xc2c41c04d400310003440c801113655450101c4014152031044041c0719100352142d012a0100b03e4041c00c180d840f0303003440c034000d0307651010709100f24003280c0050a0700646080030010340d000c8145281a1945c17041c942030074040d40e540610321002e4400700030130034000d00b074685001d96030f0300d03906c29034a541241c40c0118008182d005103822581c01c041c00d08409040f0320b584241070f01e03002002114404060380301c003401030b41c1c058054840717160803050450400007032000c103502c0980d1441c000d550605c80c540d908800c4038141d200e002d18000100303038800c04440260a009039806290000f080115244400350f0900366202e0903a6407120005600c21203a09080000c940203060061501c84103031100c0364107044108000c90007099080d01002107140295608e54801d410034001107402078001c01c09401d003100014109101203e80c00d0b078039801c1101260014102d6041450740c500d84268180c1420b0b40c12030112460f6005ca0307420b9911454059010031003a6014004000910100005080c10b900d403404103414070000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 19439466 1250 19438216 19438219
    0x4080d030c020f0d030513050106060203190f0512040c05090109060503160609050108090a080313050d0804051b03010e030c06040516050105030a020a030f0c02031b030301030c120f050105070e01080105 88
    0xb000f0700d10140c0000041c50082880c0f50306002c9055940d1a00101c841f81080101400b42d40c01d042e00000c4180e000700081103082c0ca244d6202c20066414441910040190510840060410805042008c0103444940c2e0030900c1079a0728490540d6580008204040a03044030104031340c1c0341001c00c81450100060b1603d4000102020200c628011000e0409240c0b4860203041c0119500000c2203079405002e841c1169501c44c403925200d00f498080c4104000c2e0702d1381c1c2100c5d584103081d03400c4165401420400e1060360b010b0020900f089101c05141c103800c2c0c020780040c0d007644d205c1c0010040382500744068080c4207c004010311140c506420f14502c0d000d81e514011071440070021f802c0c0182c2e40c3c0401125403144152a025036103c458101c00c5008180401c0c004103603a2510020b4503605a020008080303912840c80120a030f10050080540c4a100030b210080901d13414503020040844142c40d05400140203054191700399080d911598251203044a031070000905180c0407100303940e0040c1005026050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 19440716 1250 19439466 19439473
    0xc0103051e061203040305070f0806090d03020d020f0705010b04060e040503070f0305071209030212010c0516021503040605040611070f020d05010b10020a0b09160306050702010f0204080d030c02 85
    0x1040041003941d002030200a840e584804000500305448074800c5011034400c10707040b40c1d51941e0300c0c01d2464941d012801021070348480348000058045c400204c2c603009018481c064008580284d0f0103900035405124500d042030780a04c00000d44c1e0302d1500140000310f02910000c00c15806c414104011200d00750410008140c490081c000131400000a0b0341d80c41d0342c005200d03c44c0c1d8500e41000d44e214003400c4001806260784801103650998040408400c603403082c4d4803140455070312000c2d6400e90f9040c00035400060401d10003045110091050210014006025511020744144102005038011581945c075241c480003884204504c074426021403201d2400c01a003054810703501c105500420580280c421602c9007600414088c3c20360101e268101d0051600c17212080c003890203915460f0005095803800c00742e00010300003020102e0340d83d003100000f0703030356441d994115900e000c01468040c05c040704642da9107a05080289032403008002400300c0302c0041c0004249900000c003542c00f51a031203408c641 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 19441966 1250 19440716 19440721
    0x60117030316030615020a0b060906012703060606050a0906020c09010501050d0b04020301080a0203060a09030203030705070302010f052e050a1401050702130608070e040b07120b0d140c010305 84
    0x2000841a80d030003034038880aa80d141040458114041c001300c2c1c0050040041d249000c010240d00060205e840c54450a840c400d2a6180420802881c2007181d42c2400310307043c0700001c00348002242c1440d030304070342244145515645907190344080350320035005800030400000c0c00c8081207803c011214014245440280344400d81e40020074107850701031150f50f041c4500828069040000303900410003208024004640343d680d6100850b542d02c50040b0305a000c2d0140001080669005010f0901100d800d074005610b1915240c104072046d50104409030b045550b5120b40181840d807501406010707054070a40e01032410512080c1c10341e190b0b8214a0010300c0350a10504016503100c6503204011100302c98034180e8506021b00040e9990300c2108002903105500001803d0452030702e078001801c0e00c4600d02210301058450750700c900d8506080d1005002c0c0311441000595081c840c4181d0909102c1c03241e00414011014808a080c1c100007400031a1040020030612158140821600d00400000d203002d11050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 19443216 1250 19441966 19442009
    0x204060834030905010e010908030a0b091303050903071d0601120b0f06090301060b040b04080f0a030512060406080a0501050f0601020d090509070e150301030501140402060d09030e031002030105030601 88
    0x1601c445003038405158542c02881c003071010039400f60704000d03100002802102600c0c50485038690045a45003842c902d001c08080d03071800c0400d1501d119100c0381c0096442d45c0c0d0291000e0718030350006541e96130306226000001c40c500c042ca0036503400c00c0b14104280311080c02c2207070000d003200d807800d00c6400242c0d1511010bc80f25540710a0800704045007600c84e5550b800e07604e80464050481130b081014540e500040000c3c07032102c03010050088903078020035241c03010148401280c81e607081d0140640001c906211016a01d0045410590003010080000480c295142511030601c01400c5090b030b210b96640007001141c000340840741794415000d02c00341440c0501200c02070f0401c1c60710301410780540c00500000e00202d0280b05a0b00c1c1c000401448203500740e49010702c40ba030f9903100340030448a95083c076200a104140031110140507a50081c5090308100c81c604982000700030a1100743c0c1003181e00c00c0c3e20015500c0a200102c0b90a400c0b403005230340c80d0f0400c4141841c0c000180e2180d01c8800c10012072100a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 19444466 1250 19443216 19443301
    0x103061407020d0807020f030a0c02030706020106050901140409020a09090b010f0501020a0b04061401030c0306060e070801120501060b0d1406030303040201140a0201020d021204020301051003050706050c1002040608 94
    0x1c04503500309400d4030717120350400301d20303100800340039040328031000450184094221341503541240c03084084815094a1364012802da8107240310b9150000d06000c014400f030480e25007060301d0800082c2000483d6070746900010640c1c4141d51282c0d120300c3e0344401c414103001800401d68007504124100c540e4003460038000039910100158007501c00101c0c8408034040242941000d81840381e1440f03803503415612410150410700007481704a030b100d480e140d000503140c460384031514410b042c6500c2d128130780c5c2c2c0303445c80000591000045c12030741950b0341c0c83c0104500d588500507000c502c0440384005a00e101c0e842040c81034110261405100b60310074010000141c0c0c0c0510550003c00311007280d152104125030040c2c1c064024000f010040307900204060030000c82c07402c00c03035100c1d40c000c0f802400161a50303858035071045614000503005403c21501444140c1c081d03001409400421001c48008020484803007080340c00c1500100e0001d10000d052108240600000b03a80c02540c403050203000d5412840300800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 19445716 1250 19444466 19444483
    0x51510051803010e0c0306150d030507020f031b03010b0d0803150a030c0e0a0c0305060a050405070c0c14090603190605040c080115060810060504090b0d021008010306140702 76
    0x4010000650307080d070340c0d1210303111030303101c080903009000c8040e040d02000d444841d500031940c001c0c07150000161002c00a83d0f580c1d01615009814906081c1c0c180c0c9048400d503201e00310580e000610401d14294984040107041c1808840031108000a001d0078101401e54084816640c400c0502c654800003081041040729001a8590414640f01c18078801140410f802c551000d080daa904080000b5038001c8103038907500c02d0460440800074404032600503011100706a9103250490040e010910117400d091740116006581818101740c1344c0e40e40d5440036101541604991a00c82c150501130819041c04207a40350004021806410400085094036041c2681130b480500440c3c4c0b03420126060140350b02151024222210090100c1d19104031311011811481c030445000514050014910700c120083d224103440d05984c074285098640502d9034042e200d650400c5501140800c0124016500c140030b01540c15100d4941e080c4941c5117044c288110b0700152070204003054440100030006501199461 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 19446966 1250 19445716 19445749
    0x60905060702030f0a030201050601080f010308030406090312020a09080c03010204030f06271406070e0a03081315120c0c0803010303030509150a14010f2105031207120515 75
    0xd45074815400064584151410588264000d92a0203001c3c186d040d001288241d5003a02c070180e0036158501c840e04c80820074440903101c40c90a00100b80042c2858005040050080c41d005103a040107030742c107a003280d01c442c01200124103604010084250140250060540d08038000c6003000e1840d19541c5410015000040c011507a9800c5074403403100a00c0300ca010032032000c9180c1d02c0c40c80a490300241940c04004015014855007000401c8248600c0141c2080400501800c0c00b5610790340e02c5001a40090380e030555440780c2400c0100300d0501115607240090496501c9030955848034200604581c0d1447d6101d0407c610814a100450900d42c01c8904595052400181aa4410381e4140c10f1056580240c02107214100c280018040755400c220300d201d102d43d04d01034490341c0e9101281e4a0b000c0303d20604082a460f00d03002c44900c0345807826042140c0c06031b410703a071810380e0ba603541c0c8080b10b07400c44039100403c80241d14417003502e00600c10681d00c000c41400004411444a000404200a010824 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 19448216 1250 19446966 19446979
    0x3030311040e0403140f030c070506060f01050a030f0902060a0915091a090102010f05090102090a1e1401020703050a051c0f020c040203061206010e04061b0e0603060105120a0c0315060905 82
    0x216013100c42e0b0b008443c6c09070388107070341035032282010071100c0d072607601034035003070303c25128840200782c1c1403509ca031140d6400072058566a240c040547c0081d8040c00d0315044480015aa80d000d910150301e42100600300c0003a555900002c460911014155090308558a0000c2181d0418113100c03513a94400d9a07100c81c0c800903545520781c010031004074050680e155800010b00d09043c04d000f8002815005410404811103015079525200c0030921419000d002d404025450248802c00441d030720000e00420301c032010700c140c94a052b1691030b01032030b11500c035100f120103501074985041e1040031a001e00003010300901d01082d4038aa0088001e503503c155040061140e81e0000201e80a0360303929509045200b00311080c0c0705590307500d1144c0001404111401d50b80f440c103002c0542e19660b42003002c03000c41d103800d0315580c240c0c0c40818140a080d4000421150501a00308010012407103501207042c4a110501404101e4010680c0014141c9604280305001c080d019071003806540d420a460314150759042e01c94 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 19449466 1250 19448216 19448237
    0x20615060d06080a0c0509010504021305061303050a05030a0206070e010503070e03100e01020c0d030209031902191509170309151608030708010b030103110607050a0209090703030311040e0403 84
    0x1103600070810b980c4007074514858010000f0410070381180c100b08032481151180416030307a980c01d0100760301c0382c46100f040280d2540810b100c00d140c020f0141c4140100d81451079040c90b120380e181031a005580209950a90010451820499040114651183c410724105100c00a08000601a400064108801e20090380c0711031004da20104203500e00c54150360030a021403101026036a00039409a503c0318254015501e002c068103010b402120401d66001e001041c281c1c000d81c83e030381980300e0940c500300d9106e40c1e45203080c8411021186a00d000c1d190b00240c02e03040c80456140505028104d500c94060000c021000c1149480d0100c00d1380c05040701501c04150b00d64940350f0800c40c03840f61a40160032000007132030a109220150000e184204484e40343c1c014039903224690303a0060f005c01d10000f80048042e1304021880d040403009028464441c008485145401c0d0740002c40c6550103c4195460354003041040040c580e140c00b80c0303a240340d8035160843c035042c20107010340b9400c0c0e03004001500780090500c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 19450716 1250 19449466 19449487
    0x2130810061d07030e0d091a03060a150e0402070602040501030509060601090909020a0503030703090f0602010e1018051b03010b060c19240204060f050c0a0318080109081902061506 79
    0x3169600020f00070031b4a007940340f014400f5203480028045e5503502c10f010105000340c590340c07004407802030f40010040d03c000d0303203030800c14182600c0e11500c000c20814650101c5101e51214005440f40f10300ca40360150b156418003000508451005060302d05690240080c001c140c0d800000708001c1c6c9020002c003060741c19240c000300d00803c049510240d018070000a04a043c5984070100f0001d83c1c0c01e1030410a05c680d03503a80100c0c01c0c0d490840200c50b050b00903c1d0303103401455141c1d1002c103900c040b800d1640ca0b080c5240e2a0641010500c401c2c4021203251860107101c40d140a01c5540c3c0e040d0000c8804a05060f000300300fa80c1d41d14034007044031f542c1980060695050215a018184034803860944c12001c000390700c2c00040194016202d048041a100394040040d075000c0c100742d490814010703000b04221051500c0c122415050007070807001c030950445011413026030030b005103074185000e01b16550361021015a9040043e20305d079008400c64110390203001920318401401d094051040725004e0b100c0ca030001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 19451966 1250 19450716 19450721
    0x60102010b120a11181609150207091104030515060607150b030c0406080c010c0309080102042903070503070c02012a0201030c031a04020d090602130810061d0703 71
    0x5401c2d40c80340c04156142446200003d10030040c81c0300700804503600c4a00e0090140e03004c1840101054105100c00050440002014812501400b45030641c0d0242d900c4104c8654138034000c0c91100145c1282000f4001039440d8022121002e00c82c942c1e25162515680318180c40340007122600f80d0f400620400300700071740d8844090b108e405030001d01c0407038030443c03d40703851004000140e54140207004030b1030381b01401d00d020f120b05802c464500c0042c3c81c00207204001103800412803030046003800840310340030650f211709201030005010045000300c078a00c0301c020811419008c00d01c00c0d002c80c4070108100001aa40f09098030707005505810031042c060710620040c0e40c0d0000c0c5652214031043c0410002e983c02d00c00025003c6d0150003a03c0c108100d0b40c0a800880917561034000e440c200800001550b081428030341c0c028100c015540400065142c03103561901c040c1d80c4440380c0c09101481d1014244903506041c4079804005220b480704102e10762070961380c00c4503480741c0181070b07486d0301100700020700701d45c040d8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 19453216 1250 19451966 19451981
    0x18050c070611070b06030a03080103060c09090501080f0606060a0905011d040f020d050906070f0c0201120c020319080f040209041a0403050a0f030b0303041217030108071409041a06010201 82
    0x80040c04440042500b071081900f150784141e901e000110007141c00c0381000300d208840385803d50381d0b40f84242e0035071310f610340034012030707240300b03041080460300013032504031902c02d040c0a81a80b502806640103522925450980081e0019108410412408101030f070005500b404a480a00700b804911030204c095030070b141c80900c4c0c0075410a0a000c148201c6d0344180d402403404120000c0100855100d40c50350030364032041103030170401242026500b0618103009020301d2641c1813051410f034248041031140001a44c103818800e0000d640003250000040f0301e40070280300e6408035442d10300880d14000c14000c901c15000781003c1e0042c006440402e00f4001080e10500c20609201c0c0c0c05420f0303050900d401030551b8400b0713046030001005124214420fa00c40d0140400902c80100214100740c10440422440000340d0400c0340d500e848000101c4c128070000f8007440c002d1070910b004d495603518007048164482440c0d22100e04c00c440c410b0400000840d46481c00450701c220a4400342d4a940c0d20300103034018601d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 19454466 1250 19453216 19453223
    0x210020d1401120f0311160906050f01020604120302030403050d15030c090603080306040b010207051203030a0c050a051909080a0b0402030f03042d050603010b03070206090718050c07 80
    0x29421810030400c0d0040d1000c0792074112890526a80c5000585901c0b0b481c24008150003a015000c0f40401d2003503010300141c01d4210283c48502075010440c1a01c0126079000202c03040c1c488108001515090000c4a0081c0086c0040d2207180703015560f40d402040021a40414958040301113002e01d440341045e80e100d61001c035002c02c080c0342981900a00c9040d203100c12510301f40c0c603600210f0f00d0384060281c6811a5030044e161800c540310b030790802015140c0c1d541881d045100b10680090342c2e070b9554480031424850200074507a80c0c10026403d4042e81c8030005018140314003000b44c4035009a010b011100c0300c0e2203104002c11311041c2000d08035603030002c0340d0161529214150101c07041c0300709890160702562084048600c8600121210340e1a40103503c110704440040c010020000c03440150501800e400008520b0800c41c4c0b01c1000039041d42003a04581101c59002c01082400c1c0e0301000815001180c42005250803860300c2c0000d503844a80c0103a8140442d2128041001c510700407040e9401c0f070382d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 19455716 1250 19454466 19454471
    0x1f030c03030e0a060207060c020105090402160b0403030b04060e0105060d060f09020c070806060901030201120204030203010f020703020c01020c0303191209030201090b15060d0e030c0f0606100513030b06010210 92
    0x152428000c1540700d180400511030010080000313400307400040c25004554150300c607854000d030684c00650310b0360040d85007250442c0c1c0801c4a03140307401900501c0501c00e0310a5800540328241410010101e811450800e80241d141650601c200e442c6407c031103044510032543c5958400030600d0040140110307500c049c08090070a28003107011241d0380c019040e4000034500710b4007031a42d6910b80595504060368080d4128500800510242d4440e6881d003202800c000400743c40c0550341d5010a0848401100034006c00344d000c2040d02c10141d040c080c41035194005d10042918000410000340c0382d210381d1000089003070001c4c09488409020740e820041c0c00013520010003d41c01141401390103004107400448000b0311000000700c0d0240d41c0b0300e40c1c07100700308098011820b0458040403c401800054032401c1c075484107100d441d409000421800240101c140702502440c104003061120002c902c0c40e400e000d2000900c10704000c01850f034109000c50340c01c000c03040d61544400b00184d0510030201840b846050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 19456966 1250 19455716 19455719
    0x40f0507020601060f020102040e06040b0607140c01080906090c040f090204090b250503010306020708090306100f06090b0702061e040909050d09050105090907030612050610050402121f030c 83
    0x64002c03a4503412500b0035201d556616100342c0080f0b00303e12480c0075100b140c1803044040342050400364090f0140c0c2e44040d100c0e500c0c21400c0e4841c9600c10109510702d41031035005112039001035922203400c5030800e0302d1000900e0306003400a0340340c1d201c1c80980b000c00d004694400b407400c2c04860a82041034419000b40c4104920b50795800c0100c8a82d03c22184211201c0030002c0b00f040303e80c0d40050382d400074469561941c4c116402d681e1140c000e075004090a56403110103005070081ca94050003e5401581c401003010324040c0350010244502031568030840600a40e0030b1f0070807903030000b6400c50b001c0c2a411550743e85d40b40c0c10404500995040b503071350315515510114011a01c3c129541c03108007268014800c45010507101c000480e86100d060043e280003420070b01944549060000300c00f904408281804a601501c0e000002d10342110140d00340c42075403040051050701c041c0040c1850140c0404d540c00d6180002c40c41840084a20140039041c40050481c00300f42203040080065010b15800307281d520415 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 19458216 1250 19456966 19456981
    0x1c0516030804060c0203070201020604030804020d0b010e0402030705040209030c0103090606090207030815100c030c061d010207020111010209060f030408070f060f051608010603020a090807061e0e06030103020402030402040f05 99
    0x155400c0310220f070740524080384a84818000800e5071049a81640100001d5595940860310b980700684201d030003030200b081c0840082c050604070380c041e01241110b40300b5032400380109454070107144c2c030140c007032441009107150b00d481c04181d41022000a09021032a0a80b500e002401801c20b64080d459851012071b00b441056402071032103010701204161014500008810047d403184841d200d8008501d003407214400180c000e01120b812980207000015800d049000907804078041303940c02a5441c2d50001e030520466070800010002c0d02032440c021404d2076480c001290030b034882c3c04482c40550002000080821107241c0032100460f5002012042d4440c0d0351a22038049d043c6442c21101d0309081c000041e426038018049580c0c0c0c502079030307540707003060b4a000000d030000d6200c403490303c080000c0f100000c12400410010100100403076aa01c1d40d403600034401655004113403505490801c42a151290141d41d20103041e03074190b0b50100ca005a40707459502c0024001e1082c0c40402540d28180401c21410 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 19459466 1250 19458216 19458227
    0x6070206010513020306010203030612010902030105040c090c0905090c0c0f071413050f06061b120307021221060402041e0509130c030b0402030705060c0c0406090e1c051603 76
    0x1254403d8469201803401500c6a205070b00040f50781c10700682c0203000062181c60000030103070100708038000008903001d071600031909480b012030b0280c6030303859908410001c0d1019446418801005494440c908600302000100c01c0303500178200c00448003020a0484c42c5100900c07520001d01c045804035a180c0d41d4625141c0c0ca100380c00c01000740710711060041802200b00e180100c6100c0c3c01d00d01520006a0380d039104201541d00285c900c50b1000001003002d44003140c081010408028500101e1600c0b480c01400007450b042240300ca80134160300601c50307108400340c8241900d401102040010606648032030200c1c00034020780e441610445070301800500480c1d0340d000500c00b41e07901607070062003ea0700c5e100202410544108010003025805034100041440c074050340c0d80003880142919a125500e1000440d150010707080d181c4a03030422001031016182c107214902c010841207200f40080719000b0040340c2c403202c40104808810703607100740d80440d051040301182e01310112627441a06140490500810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 19460716 1250 19459466 19459469
    0x30a0f0f020a0f1211040b010807080c090a1e09060302181f060302090f0a0b07060902030a05150f060108130b0601020a12030608120f0f0a12020301030609150510090218030607020601 80
    0x1641d205c1c8a08444440c00c241c0a104504a81a12002071585480305c003214407540080c581d80d5406070a004100440c1d071045030f45001007a6003561000c90303582143c032128844000381d202d600c60303a15000c001c000684446072a00315040c007000c2040c0c480c1c1d56000000c041d2032240400c40c00030540000000c201c3c00e401d9406814000070590300201c00349003020a000201c07126002da04400c42e8140800030024815802a04042d031024007940c81e810b00580c0c440d860203022151100380e005071042040701c289503c3c501d07144c3c080001d1a28000c241041c00440c11600e1614401408a4102c10002102ca9008024100c3c1d00e540c443c13850310010b80b0425004009045500918440303029140704407001804403800e03903001c400015111407038a1000c051400c2d0940c06516207000b032007540c180310300f5525200c0c03010398002c6000380c60204949225180c0010420184204107907030900e801e061000b099114014441960484400140e0322410680203070b1000a406103400c0d03152203040308001846502061030350 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 19461966 1250 19460716 19460723
    0x2150a170603030415020102090603040b0405060a0b0d0b06010320040807170706030203040201090f0305060f010501050c07260106090209010201050105030706050904150302060c01050411030a0f0f020a0f12 90
    0x21841101100d180d00c00005840c01d50b0305078002c0c442400300c15450311010500315403a000052410744020041111504119010b03540c40c000841000f06024003841001c0e4002404002001390f031940301c000a6072221001e0300074040900140020360700b030f40254404100400b0040e0512400030510008a10300e030300c0380c000c000d254098800c00080c6541e6811031300c008038019402130420241446811402034200a02c140c0c104000070134005406040052010050350244000e08030514000108030400c500603880300e8100130080005011869010030720340207546030740d1112900034140a07000003400783c181c0443c081a510308000001c02a119500500745001c0070f80080c400340c0e0742d03041019100c050030310411002c61400c1084048038030f02580b08030b07040b1030a1506504865140c6d00450070076007049248034580e82d550402d01092020303040c020701c0c07956001c600901e50460b2599a201100032003950003458524a4000d400447d80c4000406018001643d40340710819030b12440003000c02c907d1003094 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 19463216 1250 19461966 19461977
    0x150d060219110d0804060c050415020708150f0f04030908010c09082b05030702030409060b13210f050a02030312100e0f06090612030d02040906090204051804030203040302150a 77
    0x110b420011070b0803850440d140d01ca28901d50703181e45804c8003800c0c00c02100b0040200821010030710b2490483e40c40e400e028140d0050640d01e00304404185801c080129428003100310408218070f18001c200015072104000364010307080c3d04e45140650300b1400b550000751440d420142c0914071700c1d511030b0380d0300b0840304500200d41541c00c1005080a640298644110f040c00d5181904066580503500554000a1034812a890a90341c0c4201800315042500450303c482400a11131140300c0d40444010007034134013521841500410b5505402018000b03c0c4000e2040c40c05900840501c0000d00080407059000340a4a030b95500400d040c0c0c036407020460310010500e0183d40c0200d801d80e255404107102c0d40058506050b192141020080480700050095600c28500e001c0c8620205007440036080c1c0400541c8050780385e83c107099401d000c0e1742c1da0340c20003004544140001c202a5490110301c00420300300103590707010340d1a1420120704503c0f4a80001e9005951182c2000c418403841d40200ba1881c042c2d50744 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 19464466 1250 19463216 19463237
    0x80a051c0501081c0905030712201c020301090618030f020a080901030e1606110c1806060a0c0f11090c090a18020408070e061207030308150d060219 65
    0x8a41c0e00b800f40e48040d9000e18820707450007110300c0c030070400302c005800e11014043c0c0c0c41c000641b500c0c90942010007000d040814220030040305a1554648076a03a400901160480201280d54140c02c0d032082c004414107841c10b0019504d0a5100c001c1c0c55401100c144901901131020180304035440710101c000074802020525203d1020861034121a4010006d528049043e0011000b520443d1b120342c2c03440c0985408203034021581000e0b100104034540310341c0402280d10141c03508080400d00e046002c2c0d1502031002440c0060b1084c5641e020301c04075150342e01c0d1680640211011000c004004100940e076810220a001a840c0b411124000442d40c4000903035603c016180d00303001d0a8905900b1400410041c042211310341d100d050840590000103080035610281c891400704283c2c08124040d000f081400a207007010110400d40d43c1c2002e008220301880d61740c00808981e4014044801007001c41d400c222035946900080c01c250350098819074a80c115503000346402c118143c554000724510303540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 19465716 1250 19464466 19464517
    0x12110307050102281103011a190e0a0e0a0503160c1d1305030c0118021201060308040909020a0b070317150109061d03010c020d090905010b0703030e0109080a05 70
    0x604c1c5004040e040300101c00c11031080e8002e440142c1c01102268031084018002140c0d0700c0c2403049824503500d006031425825000fa05100e164a00e044e40b250b0310406910090048811581d001c0e13070400406c0b01e001640d2600c0e04a110b0800c40400700041a070300000a2841030994012040c0303c1880c01544808106541d41034501d0801001c1000c03000036003480e0340021101d000394030300420a80d0140d000c0d0b17890a04500821800c6806240391013080d850010000419030603c1e03010044004285002000060700f15101e80c2820700a0b44641c401041e00c0384400d004540b50903030b0344002021103002040e200d07810352402030a941c00801501c1c803100380c41800105a04101480341400c1441030316043c2019040c2442240c5a9002d08441582104020340c4405507032400d108040000045a001c2e0442c080d010200400f01c2c90782d544540c2d01603080400500442030355100b2202115810f05000a07048501c620640c050150050040d100e07940202d42c05c0b00c0b00360050010210a04100000996106000e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 19466966 1250 19465716 19465723
    0xc0801060903020f0310020f0711040203220f0605040b01050112060605030a091103120901080a0507020c010e030a0c0b030709050a120807050708030301080307031b050606040c0912110307050102 85
    0x30030880025094034040015081c44040c50811190150590711080c0c1700030032080599021403401541c080d0001000d0742440501c030034000201808440a51070f41c2486c000d0300000117100c1d500c810708815031a00d03072810484d404000700795442e0301c901d0038491442e0038202620030010911449000c161020001e550901c0030740300b641c0540c0c0c4a9200c0d0350568039020001c00050004c440d085900340650f5200c0352155504010081416114002d400d40d1034100100050402d18040d080c02d610508000602c408145c003c1f6000c00390b04400e18161f8a2940700f000040d1802c003200b400603003000035003540400d81d50302e144000c0d84a5800d5072900c540381c4d6921410311000d001f841c882d850007040d1410b014000079625200030106503029504860050751a0800c0d141107501c00c3c0c4c842c0c061540000741d0a001c05821510b0320f9034980406400c1c55442c8020345034252070700001406030744140e58584408000303901681e9042c000c1c20341c5c0f02502005014515260001403030b56661144a4864650001415803002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 19468216 1250 19466966 19466969
    0x1a070b0703150b19030b06040b04090203010302040c08090a0f0809130606081602060c0310051c0b06040204180f1b08041b050a0b0d020409090b0f06060315010518060708030106030c0801 81
    0x200398004021305040d0450041280c0d000b11070340010100000030301c079146940504051b225102d8016640e500d148100022144a05c1c4400103120b000b804200c0c01500100314003906641250300c07500074110701d00d0148003e200740402203a2004402c580d48131860555800f03803099a03036503203590240d0b88683d130f40c03005652103010740d001c0103a0085002801480440010f160040d4a850f20020101d403104000f80b03c0a11840030b81c1802030b00e00d545a028054143c2c54143c00c50010340d01149018141a0102c020144a1510040f000d4648018180d401c8440d40316080380e0340841030031803614840000c02000c2071750903201550460914647c00240d0758109400e0012030360010481510145004040d01d0103401044900600c42d40c00c2c0310000380380c2024000e10103c68455002c001d018074004040150b4108058485801003105004121104040b02c82d445890321003401d0068842188401d0644510f04c5280920781148010072108100001100510b040e0340198609105481c0c2c070580c00c581d8032209 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 19469466 1250 19468216 19468237
    0x20610060309020f060f030a050c040302090f130606140102010e010203060108040b0a0213090506011b02030c04020906040f030602190e0303040302010804050115080304061103030609011a070b0703150b 88
    0x504004004041c0203502452841c0e101500e0302440c040101d000611540154800c00f904800000030400c014904d80300b01c0b82d01c070641900c240d0800b410740d00403501001000f040c1e4100511108042a10868108030b4dc0700c0a66016405200c010303158104030040c000702c085414055800c00249600410040c000d5078410b16043c1d503244c0c265a13490b160310f55551409044102d50360303400c204080380122407420720700c00b03800b0312100891541032110004003108000020802d4140300365620f030005030f5012403d00d1000904681c007503141d841003800100c1c41d11a50303200e50304104048900108011081c3c000e006450040034030303a400703080480710540b0030320f001c2c00d01aa80741d001000240015805103190319080f5000b40000103101c08190480d03980c0102a4202000035800071904201c11540301c0041c0070181c450350040c43c25802e01b40042110f800701070003003c84200605c416a80404000300c1942d2825402600c02c03401403c000700050010004c0119a14200400ba00045548100750707040f680710121 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 19470716 1250 19469466 19469491
    0x211704081006080c150d090b0106110604030e12010b12060714040303020601150c0605070e04110405150a0203070209040803040218010503030a0f11100f0b0d2f1f0f0206 74
    0x20103010401041045e501c1032174610301c00c1c8803418108140788900d08016220320003c005550500101402020001c500040168411420400001e0b481075224075075405c1a44c010114888200c40baa000d01a510880d0b85c10005000b806170243c000000ca0078000c00060301c0b00a00e402c0000c800344e0b00c0384918000075005d82e0101d001000f4010341c0c8160401040128517051852807810b03502c100a6030760650380400054040d00348000309203050702c9034080007003c40c8501880d092030f10020801100503008103c9220002003842c0f0240ca0003842110b0340c183d4001d02e54010343c80e15181a0380b59400c1941c0507806400614030740781c0ca040300001c1040c10796800400a504000014000b12152103074204802d00300403c1c1d04240605503c200700000010720320110200c0e99a4080039207100321142220024401c115a03040c020114450660048110324500b6240c00e4442e441c1c4d1980d8105410b040c0c025800081010210032190880040b45203c412141c0e11021078402600080340c0e15642541c2d400030980 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 19471966 1250 19470716 19470733
    0xc0c0406080a03080408090402070c0803070b1609030206090d140709060503070b09040506130507020d0201050901090f080711100504140a050108060f0d050102070f020a1d0121170408100608 83
    0x21b1802001d883c00c440c00030000b41c6009c4032541d4403240041b16900c00c6120780c0c00170445904110801c00c2c5942e016081c00715400c8403076407100005142c2d902c80c0c400640280e80005203099540c40c1c07001134148041c0c200000109008100c06120344e122034034402c0f00000341c5007200200e110300c3c0c0860750104580348a02c1180c20213106c030042000134000a41007950044804131003404d1090315018042c420803254000d00072498091744040d0954000502640700c80e490312040e03000152112162044803a0483c64081c1c484005140021201c00784400700c6a000300b2044185848030b0303200740140161031a052041d510401b004c02030015014040c0203450200340e0b4100020351030305087c10300e4210104014050b4506418a1b10b4850072a4801c103400d4482582031820f007015800c0c864000c02c000c00f101c0303070000322082c0810440c00c0766140600601012003e5075101c4810304c2c0c00c01c0014110303244c00c0301040e0310011441146030a80d904c1440741d942c1074018025040c40211942c881d29044070544405802881c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 19473216 1250 19471966 19471973
    0x40507031b180c02010b03060108010c0914091605120c03041403090a0902090d02060301290a020607030f11030906010e07050c0a12020304030f06050703050a0b030d1809020c0c0406080a030804 84
    0x209200000f5404541d0786180000c01aa0108107650003070074060000140000da004c0002c2025410703800c41e03070781c4813103000c04840340303803078070310140b5400482e805000310460420742d011543c510070b01410b40c0303c11012409002008290100450040e845030100c2e6480c0703c054131440c6d4681c001d02502d140d0040c54120100b01802d841e8000f018601e000038a02d000801407640007800c660020703088a01150755803802e0380304609800000c10f001d540d0007a0070a08040708148001d47d1144010980d208158031407041c40e180d440ca0f9005100440f5a01038910748034904401c40a640301d1003485a0000800e00502040c1002c0c051422a500844043d0141548901030348804501c001781c9060541184410071002010422401508044510850020504d401c0c0900d0040c10386001030520200d10307103046200400740c0e40015070420071980c203060181b404c3d520500360b200cad0180c00344e014010a50001580f090078a00c04981000c40310f0085404003d266200c0c96a25983c401c02500203020454140200b00030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 19474466 1250 19473216 19473221
    0x17040b040b0406060f08030c240106030902040204030b07050910080705070f050c0a1e0503070f1203030e0105070507020301060b030714160503040b030a0c0314070302090609030105040507031b18 85
    0x20501400300801d6a561700c43c40a01c03041541d034881080303600301041000342c1c0c007803d00c0402c503180030404a4000082c0b9100310b413040204103200e11402d065442600c0760840d03c41d034054030003c5411811008807485c26a10183c920703800840d02d103118030340385248003041d0743c041c0701d62a02a0340f0940d81d26003066102e513904218039003e6602600e09105643c0c101d801d55907521040005041e000e00b00c18038001103020110310440140d00550b03c6a0081142886030010300507410003203800491807030405c00510304080d0020207a400042e00350b54240020003c80310b401100801840d40700350001c00c139030766403940500800e0205440000c0020381080b840c00328251108041c00c103000104003403d42c00d215130741c1d40034507540c042d03400000c510300c022041017a85c8015100e0381c0310a24190906124455012428129401c00189080d052540c00f04e45c900703140d15604181c40112401400810960429041056607500b80340701c1150315450507040b098000c40307000e044008a61128125071107a8114407040f001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 19475716 1250 19474466 19474471
    0x10e03070b0405120709060b120f13030f17040320011a0d020111030703030603030305010510020c04020c0a020d08070203011b050405010c02150a030f05010609050603062107030305040617040b040b 86
    0x8882c4105c500102e00b1001603c902401030500c0c030840c5030340b0440000e4004017444000c005844030700b039410070454014a92640800f2080e8185402c0c060356015107000da9045010300c51050300e64009c0c0003007104260704000025401143ca10720008400d080080e00c5081e541c007054161015038480c25601482d04044244954003407050601c4103e410058458601d1500f01e1a016000241c440008105041d0980301d4580034090603034042d884104070a1011b5039980c42d5440b0f00d40602c0e030003d12840031600a1100c4049554020110600380e5100c0c1401d842940000304141e01c81d52a0503007064a03260030316810354081829403103450500745807500648420f800400141c0e0001220a1950344c00c852010003019015038603100002d42e2809912807900300d580580012003070080c08801800306984a50590342d0200c422030300000c0741d054901d4040e615040c2c1c0105980d8174421140b0100406070000003030015118660f43d03005024030589103102c00050103441c0034180c44011800300340402e504080c0160f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 19476966 1250 19475716 19475749
    0x200a08190f050f0303040803070801090b030a1704080118050d05071a0402030c04050a051005010801050604030b0c0f0403031211030c0d02160c0f05010206090a03020303160201060b040311010e03070b0405 89
    0x212201d50783c10b00c2c0b0b401c691045408550a030800010000714079000b01056001d0204107204225943c94000800d0340c079000e601e03000d820503401d070b181412103a52800403038028003451002481060400f2010007400d0514890458240c020324440e80746091180047d40c41c142e801c01d00c03903d0030452110070792410185c05030069815000345040c002c07860325079001d103074081c07880d0f00c00001d254640000300b0121a41aa0849030400c003001004009969a1200fa20240e94200d801004c194460601d104c40c079100f83c0001c14114a40071400009042e085159001100b02c1d40380c0c107115100030114a030340203100413a021011010f09200100110a4a501801808918079075012196000d61210107a4001c0c0c0e0b4007150700c01e8003514043c00700d541c0c1440b5250304406204000d29a40034160380c0a03440703000c02001c0e241c2d49441036071440c40861003500190b00401d0001c00d402e035601d8490803d024141b010406403400f281d00390740c0724891418000350200865003050704090a160401c1c1c104542d1858066a22 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 19478216 1250 19476966 19476973
    0x4050915011e110d050c06060a060807031a1201020418110706020a02010f060905090106090509071215020c010b0a06050c0604060209010309050f0a03030b010203070b06090a0207200a08190f05 84
    0xf01107500742000030320500c2d002504d0345900d80c0e400070f89003403503c00000d02050148056000800015810206054002460341404a00c59000617124100c1c010441c403201d90083c001800883c0050381980184161006070004280e44885804010140d49060505500408040022a000c030354141d016283c25210b9100100e510300114600d84182c406130b411540e10030b680d4109119403460241305800c0104071404050000e450064000c035180c00282c030070403001c00007034580c000c10040f03c1400034640030f000035411529a8062540c0500030803545042d140640d0b084000490024091010346801320b045000500e00fa613031b642d0760440a5044600341c00c0c10f05844541c000002030051060382d141c203003450014010041305040c01019601050803090541d082000707a04007154203611456806141961064081c0c3c5410348048000d2003000800b402048203001103044080000800e0400c1207000c4034502c0c429070f1a039401c1c036298154280e45094442c4020740060000c1c2841ca866501d442c01202503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 19479466 1250 19478216 19478237
    0x507051207030e0609070b07020f01020304120303090506060109050d030e01020c0d030503041b12030f0e040e0d0f03060b0d050603030c06070207030b0901090b0103020409050a021504050915011e 85
    0x100303800c241040d6041d101094442c1403120000100700522640000c51500801240d460881d03540703d60303c243e14000c0e02640d207120480d044e030f23402041154000c3c0724050300b0b5200b102481c14020001c081c15402100d040c0281c0c00800c2c2c5542c0300344002410364000074031440c00c804140d60f00b5a00c0c8124005e0040c1540540d004c1246250307600c43e80e140b04103000b0744a03d03582e0f00d010b01d8040c24002003080c061002c42d0600f10144480c00e4039013514420198181010760040390003440c20f031940802c80954a5205041c10084e03040450003144c0d91010b46036030b40b00d444002c1505001a02039440502600c095084203000b4124004420b4104580002c4007070b041d01d00d00223455582c47e0405070121401c0004d41d02c5840100100451400b01c1c1e80d021080c032000304041620355481100c80c520611001e841a5118040082801000d102c8803150640c014086138a21f1140711b90700c2c02c190800e01c20b4900c1ba80301d260020391191000403d84030000c0050b034036091003d10181c40502c08030640c110010410102151 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 19480716 1250 19479466 19479487
    0x7080703030e130e07060f09050306040503070f0510050a06060f020c0108070f050c03030705040807120803010501030b1f020616020a0210050307180b04030c240503060301180f1109090a020103050705 87
    0xc154040c040990702c0715038480000310023030300031500341d0310081c003a40c0300800708004150080241e40d041a4050380b0b031810213040b8104031b841e20445c40d600e410040d00d80803c0c82241030050780404200c503005d0700c0302403038401c410138240e848000070415135000c6101c450000e800d0501c6507500040005160508a082201c180401461604125164008580c0c0050709000c0c05500b001918014126006030580541050380c038402140010322815040c15240c140210580e5200000d124a00001100001030503600d090000c4d40e4040c20364001e1480414030610096440c8007090b0101d18136000303040050114404242103500b82c0c002000c174400c000c113160601c104225085550b400621100080c15200c50560400d8071071100e03242c0c0059a1820010400c6c140810030195080c0203074002d0600540302d555102c08a03000d001d00307544e000e0315403000b144900c0810a180707070410482da006030304c4420b02040d00310901c90000c1c070a55490303010380d0001c21100010361103904069401145443e2036418808540c6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 19481966 1250 19480716 19480723
    0x130203061c0803040b010b04030c0603020a03021b06100909170304020f030601030b19020a02060a0504060e07030b010e1509010b0a0e09040b0405010e03030c0d09020f09011707080703030e130e 84
    0x224200c6102c000042400140303c1841ca81c0303070250a1008120340303001c0ca540d5410002940750b1051005140d00032400c40c4605000750b05941031700d9185458690b02c004403500964031030804640e12503008a0103040440c41908a10a150940d035021340e4108020300c07000e00382d240c20303000140100e174014049961411140c40a000084c0254410070a030f002d203007484103e0b41510000322818103038082c0f0520009106541c00102550002202c03280080c0903242d50034000003030903e100401100780705140002040000255100703040380c40010304c0038041e4803107103101c6207606c3c8c070312001a90110b03001d40140010284140144000b548030b040c00c901404400307000c00c07103410b0225025144605800100b1060100070b0046c51600b401440c055495440e010448000074040c1050000501d0b40d248840700441d11030182c10141c0c010000d080c00b010b5070351003c42803641015882040c0c0d0502030031000045078040060700505995040d00d64654403040c02d401c3c414507000e0181880740003900e0b098038181d00703003092 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 19483216 1250 19481966 19482019
    0xf07030302180d0c0609120c1202010207090213090f0209010905060a0e040507030606020c0a0806150105070c080d11010204141309020d05010b030c011106060607051f090308070203070213020306 85
    0x4000004c0a185840c2015013078107125404280490fa4442ca81d000003280038919005591030003a4084c034101c0103000403841d081250700420b108610000740d0300210f0140f030f640c0e03001b119201c460a11500f210012404264043e0384050f40c003044259030180040e1800101500000c02e8601e80041150311120000742966001e17544840802e83d1070900b804101e80c14130030211004029900103000c2c9140c19201a40ca9100910352585420380c008071050a038820300403150290380207202c0d070540e2034076040513030748580c580c0c1e500002266038564088034195040c000e039011101ca136845240202c00d41002d00610a0809039180062a81d40c80c4040050b40c801c200384200500460002075100716120601d4504240800068140002a13a06100b00080007940f59407010003550805d41302e00c0c01e4074000c2c0c03030000c0307110700c003030b020426000094032148007a84005c000034000e6494a5681d100d00c503050f80c80b84070704d5002a41103604082035000703810f025001140c0202002d8880000340354111381000c2e681d00316 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 19484466 1250 19483216 19483223
    0x1050f1801030f20160803010f051804050c040504061d070f080f0a06020904060e0711010c050a1d1507060608060105011412090a0c090903030e030f07030302180d 71
    0x68a40c8909196418854180e003070007401810402200d401c0e0144400281c04402d012a13501c001130042071071841d1084090016500c01039030750712561242c9102840140301c1c02803e00411120f80540c0040344400031040c000e1341c210000d070221a10b904140800707000700038019100140c07070f15644a410304c1c201105125019988016100301400c04805541d40400c50303100102c258010660080c00c071102150320115280d21000069030344c900d8070045009000c82c0ea2000e0002c0100008001401c2e402411020305864000c008102c07120606c08180d6081c000d02d103c000c00102003051405820248200d0304060080040ca00c4c0c0640b1400204091f0382d9000300c034100d0f81c0b50f80301d1008110410040207100c0c0900300c24240312000145210081402d4012995103800b14214200803845d116810310040040c25040581811401d880300301c000c015240d00401200082e10302100e02545110100c282e440a640c1000928a050001c0e00d0480288d000640403e00c0c610800042c1007650780c2c0c8903045881c8030722 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 19485716 1250 19484466 19484497
    0x1051b010c020c060f0a03050a150305060708092b09030501020309070302030c0406061718060703021804050f0601030f060b0c0f06010b070b040f061805030910020c130b01050f 77
    0xc01c0c00090a0018000c10240106424424241103132112000d840f0500c02a15002609a894180300700c003512140c0d2910040241c0b40d04007109015010448921070701441e2603008003038503000081552161000308100c1040b540c0d011002504006c0006821901041c0ca40034164549948486003280c1c02503962080130780c00880200f01b1800e0038002c0300000710080381d00f008000c0c5015000f8180c2c042115802c4019001e2a001500c500304a511102c03110108100700da50b07034600303010050004d40c45280b840d07040750940010a80d1900e80381c011035118089410400d00c81751190b07001513000d031038140c2c80c030380e071282d00e90350041015100b080c06414161506070040c5507840d40307205124206441a00f01d28240b0f141040020045180314042c40c0c1c00550001d5030b44842d0006040c51001401e8000007484946840a20f0030305001e800000b40100d0360003198070120b03180e0100700070b036900e4009420460700000b1504403c04848043c0d4040c600461041c1402d03880c1032640c01030505550302c0000030070f00448 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 19486966 1250 19485716 19485731
    0x3030702030615010e0901080709020309070b07030306030204050a09260403170304060e2e020d090309080f0d020a02100e10050703030b09070c12020c0a080705030c0d08031501051b01 80
    0x1030b808000c01c4030741c117416952104154102100c098030346e651802031100080d00040402c2c2c030180d040210b0f01c000c0c00b241c07040343e40b25400d030314004010341540e00c000e9101d00d0810340803400400300d44c070800f0342e01a404004001000140c0c0d0400c000400084010cc100314011302c0000086481c88000340c1500c1f06030401142e1300d14081c0703408800c0307a40240005855078080c1035203454034207801500035540a0040c0d020701601070390110b9807002e0300c0b0b01800c001d240c1c2e00380490482015044260320081e21000740607500440c1503440f201d039441c08040901d400680c82084904007500f8079004001000e03540345805403180c151040400d00284400c0000800542c0000b010028198188258407451703504890300d40c0b0601302001c00500258811070701401c0c011210803c2c4503403900800c0111600d100c040c00c422a10340e5a01c4010b5103410491141c64002d005030804052a4a1700360001e550461b4400703101030441e1038070300704100203500c2180c2d2941440744c204286901e100a100c01c00d4031045218002040e540c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 19488216 1250 19486966 19486969
    0x907120b151905040807030b1f08010b0a050f0f01050c0a0807120f02010504080901080916090207020a12030c1205040e1003060b010e060406140d1416140a080603030702030615 77
    0x2100301e06188100f00f4284000d0107005c20100741d8a007241e41000440e02c640e03ca40100c43e403060034203910310400c1001007500058644064000c03a03a00a4122404645541e95a0a000c0314030f0310882c074107502095011021442d50302890180c60307011813017021290382c14040ea50311101030b8001841070b00c044001c10103000303070503503c0455081c1c0d0603241d10080c407030350400f0394880050f03024004038a0305129180c4001240c0700010028158100300d021000c059143e55000003000035030000c0c2d8203038062550803201050710b0b06825048070f80d0b5945039803002e0b6450825182d1007200110070f42c40c0c00401004000014a10040d904014014018078403003140d054950328007181281c0810019605008175400078100d99030b142810707241103600c1400c101c4550040c1030196401c13032058020a03450313140b403d401010341c00300014490348035402c00581d8915541e11a0310542c3e82c12610444202510001c00c920410503110b44030321381e005000a0110ba0801c42c140c0d0000382802c1003211880c00040e9414600d2081d03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 19489466 1250 19488216 19488247
    0x20105040209090102070507030b040201050d141803090a0902070c030f030e130b01080601050c07030b100609060908030f0706020d0e010e010606030e070e0c1606140a0204050907120b15 81
    0x101083c0000c40c80c00b0810355540c0d86a10091202074200400000040d00b5a4001c4045034110310a241d82002100c82c03c3c4410704054005540180c2e03c0b01c09c001481194400010407174102c0c00001302064241c901d40a80780d0302079440b952049600b41c60703207500040090024040c00c95014401d0300c2d5a07800508480a005213444151807102034203083c80f2941e091030340c2018000750008000e18140fa0b40e860b20703c00e194a0b00a140d48001e103615104001c00c0300455031000c2c4071090382c005a4581a000c0c0c2d40d42c00494140d4068002c4008940040144141174044000240b80241c03182d900541031040e02c0c66601d046600d0a01c860109035154180b40a0095081c03064038050401030400300000360f008080c0c0d039a2466103028034291002c008020443c034400c2d40c002c0d5080d0941c81220014510b05a24012002c2e000c2c140c081c00c5140082c1000c11100480c5000390307002d6800150040030310340c0d03911100b11102c51000041ca40f03050b5407450280f465031204240c203040c1050b07441b030f081e07903c80c503480301d0711007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 19490716 1250 19489466 19489471
    0x90b03070503090114040f06090c210605010602120f0307031b0e030d0f0e0906040902100c120c120e1f030c090b1e0c01020c070609031a0c09040c05040503010c020105040209 76
    0x1411410b8170800c00040d0550041d005000d40009001485040d0740c905144080055080126103054a44810280b0071251507455035041c0318502c00c0c0f10590381c03903900f641e132900481042004000309004602c044000500a140d01590a03d000701d4011081400c03205200895401d860000e0f010300b9151a541c2002c200f08151141c0c1403420014042e80f030030009146a03044040603128000341408070711580c1e00ca07008901c0e695001860854003004040c0301914100300c09104881d80c0700d071942c49103101c1c2c1c0246425015150441d880c050f00c13805001048400140042040794802e02c400011400140f110050443c1c81ca5a900c00140d0b1044070300300034040403020351181c0b4039a5410440a01d0014551a9410482d1f40303d20b12292290401211703a0701a0292000e4002c031072283c00340000b02540c0c081c5045084034050b20f9a280442c40000400c0d820110444105c000c841c0f04101e1610b141c10142e00080c002580c614205081580341c0300000c0c00d4940d580d01c11740040c0e46601c1400300f5403810508454 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 19491966 1250 19490716 19490741
    0xd08010b0306010c061b05030f010e0f15041d010e10110d020309030706050405071d06030a0201140705010203010914160815010c0204020313031103090d0f03090b030705030901 77
    0x444a6240658844141c800202100d040080c0449014100507440d002280e001380811042007803041c0d01d19000701580c10481d07400c40e0200700640000750b602881c8105c207026060b003030001c195030390780c2c00029a800d032050304c1a250416034610349100900010300d100c1d007040c00503400100b4942e200c9c40d10117181045280d5903403007540c5007200c000032145c051000c6540d100c1c032f00c0a0258999031215200e6007140901304000c1d008a0410381003004000c000314031070043d61400b25286039100400d6850080410045071120b070560310444038080590300038600d0000e0b0402e002102031070100a640c409007660001e81c08003103401e481e07102c0c0030203c0c1c0e210980c155010107a02e5800503099403011780142004030190058020880c40061507405902c20349010050035000303007040d075407400c100508441040490005900040a4444500e007540c004021a0280f02005212100082ca145c98410100c04180d034101e05003c1c200000060807035604014611480d0305444039030f2207140602d6000e080d1451400000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 19493216 1250 19491966 19491977
    0x150c0a03030f060b040e15030a08070302060109110304060e0304080f030414090603030d0b030c060c030a0806120c041d0706021b22090c030215090a120507030206030411040507050c0d 80
    0x1031010003c444c00340d4040720b0606c20702c0c104e50b0700c8005d40a0482c1d52180340c60754040c05541c05920503c0907040c011300382c0034400e6088900581c1ea80e030001c81201c4044c82d170504503038810000300b0046541d83c2c0200c0c600b4005001500d190680d554800c928181401841032145e400101d010010142c3c0000703001c6070740d441520500000e1400800007900c07886407428040c0056580c00481c079040d102040b403a050894050415551a401c03c6803856907500010300410004000724009241402c009903255054a0340c007005120b001180d9013000007600c0b0b014042080042490b640e1089100100080340040c0029009002d040c1005140c4000c3c61108108041c0240c503101050750301d0b10080d0400910203110341900003410b02c11850b0200100700030f6030000c1d5000320043e100c0040016040020440385500301e0344424a1555140b1240d10000113840107003032600400000c00140c14610000c50307005218048a13040c03418171000041c00c0300c03019a5040300041d40422000e0240304200156000d040712130509 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 19494466 1250 19493216 19493219
    0x405010503251a04140307051507021915020f030a0203030106030506010c02090702060601020c0f03030307052104060c03050906042a09020f1306050406080103080702150c0a03030f06 80
    0xc0303aaa802808406221040b10405001e007607020714400101401105100c0741d03007281d00800681180e0000e00030706404160741031402c8450700d400500307442200c5c80901001000b00200c0b004444c15040502c0903a0410944c2030f202c07441d6200d21802c4c901404041d60780c402801209800240f030055079207a120702941c4200032031904240c00100b5641103440500d0045403541e40c0b0340c01200c08080c0200003c0d0070140c0d140621241540100f111449090280e00716540b02c0c900404000880400070165901a0000c00201d44440d01c03503801400a200b20030340100da030059003005030381a00002c80f02a54040d42d1007546e03071542c80e0f05005098101d001d0100400743c84c20300781c86880c01c90800002241c180d400560300c02c200c0320254511500180b2820b1401c544490080d054285198401a80314207604042e0354003050f000d00070000d507016540590344e05410fa03030031680c0d202c41c4c80e0f10060007603a104c1304c1c5860301803201c02c004c002800e0003201507014220160a600c1c01405079040305600142460070202c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 19495716 1250 19494466 19494469
    0x906030c050d0c030b0402010e0d050c04150302010c0b0a060f03030f0e040501030506190b13050108071703030a0c0309021e011206120b060f030f07030c090c0c12090905012304050105 80
    0xc803c10f59801c030f00610750b203444620050310703544825148941c0142c002c101890620801107070707908540740c060301d09001c264103100c0c03608004003040c00024085181d00b6408804580701605141c1d21481c000e40024081c0c0d126120800407000701ea10031030019003030402446615901c490206003111003601e00f80b0180d415a503810361208002088503242c400f61032a48554480315800038014050060490180e0f11a0b1818590281000b400340746403510440342e0015142040c80c408010320f000c841c01640c00d41d110448880c1c050000c20201d031041588030802c0b01e0142e62200481007180030a22580307a070700d4030140009401956a500207910711071070214200803c0c0707121401103c900303601801c2080e42c0c0d502e94000400d0503101140d86509841040400710b02010f0004451040d02d024007060f6141c5640c8541140540d01c0042c844400036039404150310000740110f440c0401c0c08401e04243c00d902c1d0703d401054085400c02d9010361441d4154180905070403500018440b40213106490a010a604110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 19496966 1250 19495716 19495733
    0x2010e01050306040b0a0803040501080105060909041b0305030a1e0c050d0e01110106090203040209090303060307060528120f0216080309070f09140601020c09060111160906030c050d 80
    0x1559051281c00400200b499985a200b01c440c040000d00501c2c2d02c58075460420341e01d0300613006880c04104440d001040c1c9190080c181c0c0c9a03c0d44c002c00010140e41c80d59a901c1e0390b03410784000035200c1200c01002000056082c4081c106c000b00e503544200c800b600703840700e0b0110304010251007000d200002100002052001c2020f2408003400e003865407920030241c004903000c1e40c1074140c0350308552a0050114040b50aa002940100c1c000c0b01d07203415a4445080b041c0c1c0304e00c800d45046070b165000740c00c10806140900064000081c00e480031510441c107490102180c4414074081c4800506c001d0401c401c0c040b614170402000c0070b140a0114146514441041c03a15120903030003410500000c4000b988088040000c200945500000c44680031354508a1802500300d40d2102e4480d400500300244155100052080b03059030014142c002980380c050065401080f03e04504049004e805400d035603028042200d04024120240002a01440d604164a011441d504082d104100070b40601000c01c001a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 19498216 1250 19496966 19496987
    0x9010b0a090816030302070b030f0403140c010c02060405070f1a090a0503030a03090308010927060204050d0c030606090e030a030b01050706060b090f0102012706140f0907080304030201 81
    0x1015000d9403049200310a45003200c440e805800c0324070030070011841810024082e0303021244079400b150f418a850717a07c00a80ca02088a014015502c844001000b01e44181c2c545884210302c908103070302c0c1c08413030400c1c182514008181c51015a21002c1480104202005040700502d01c41081703214490502e0060b24184042c000b0101420401103401e590548e990b41c131200081400034101c9665190081c0060041e100e01042540414201c80002a82142c14042c286810f02e902e00c40100c0e090702004400c03491500050261800d590900010405480d81d0040a1105000750780300125149585084015500250422000716081c13401700104407200105442214a0710300f80401c528074140c004a4140c014900c1c081c1c09141440740000d4580441402440680c009551035443d44400034016820780c2d0f2903150b440c00003d072602d110404031042400941e4118465400401c01070686011100b200001340d40320b1000c1204030080c0001c01d40100802c0001303240210145080600d582c0003e400c08206 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 19499466 1250 19498216 19498229
    0x1806010504031b0504050106020609011104050105090405130804180e0c10081e0f061f14160209040602090a0608010510030c02010e010603030504090606030207020f0409031101020f25020901 83
    0x3d60050300848000f03a41900d010b81800780c42088a507070340c5d0100130340d515401c0d00c4040f01d5520303000d03440d8903440205084038244e802c182c54492504030000244801404005d00d042442d92102501c04001544180180b000304081c070145203041c0e030060490b01c12a680007034501c074581d2180d5554071603a1180021750404500c2420268156503554040100d403144014201c142d20761101d0130410341103990000c0e07038020b41058500e0200b15030003840f02d40310b0840e9444544c0102d03030441c2c1005401c040c0403009148100040445000303640303281c0d0104603406010384084450603004900d22000341424040c8900a01d40c5184c001d4403949040040ba45020900400d0b50070940c88282600165000350409000314107010020080303556a41802040b5412600851905a0910b08009411482070007595041c5800410b81061000d0620410004040c0c2104c224140004015003c14055080c03021300741d590801050290303100c0030944580300c0c01210500d00c0c0007002d19240c2c40c1c00561105060030707054130071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 19500716 1250 19499466 19499483
    0x30a03080903130306090c060206091507020a05061603050c0708030105040203040807020d0b0702010e030f03060402070c05030d110c040e0303040303090203070b0f13050402041d0705040b07060506180601050403 92
    0x260340d59518110f21440210b0510104a1580082003200c6544043c03104c6000d41601096035803240c504070f84601e420380e010b00071a40071503241c00c187c1005050568000c003003070046442c011001c4d0b03910781c1421001c8422400d40c0d080740c04480c03501034060040e5680074030b0304c414040c600111a500c240f150b00040c0201d600030340c0d0200004d0100940b1108036071065400820884004071071b4900070a415108990405c0103500700131b803040c0030000000940c0c1d8000e15003440f00d410b6a42d004207010003500500420b41c3c1e04554800001609d860500120703495009035914100c544c034403120418502254030425501583c54482500c41c1c18401105030ad80050341403801140c0400796000003440d064040e0081e280700703080050696665003203003000700090b002140070000c4d0250340e101008201e0080b481020505a511006a02c0300300082c1042c40d401010350801500b4180ca80d01c00c0c001a4114031700407601d0a0391170050001d00e01e4080444860030241010610b001d150040000313005d8000c07444002c2c030310360 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 19501966 1250 19500716 19500721
    0x4080a0c020904051e01020405010918150b040f06020a030903020f0411030a020702040e0715080903040906090608011a0616020d140109020a080a20010c05010f05070905060702030a0308 81
    0x1441040644a6a500207129084a0603e03040c1035888400300c07402c140382a14000082d103201c035010700070b440c110740b016150042d0091414002c1c4681101d140740410240e03581d40c01c21078040503081c0c10800501036907128252554102a006280030345982c000c0015507000f03202000010fa4001c2d28601134079810707516980d050366079201250140c800007001c02030580002c8100300304800254090000d56008540a0120546c1c10070a035480715020300905000d000008881d10440d0f005084054010b40b8440840c2d01c1d041d6035194800c100e80d0349030008600e42d030310303400c0400403080e0034000c000e4600c443d1031101400c0403582c40024014071408220100e5600038601c88004d5507603849905801030f800080302c5412007940c0480500910010304105c0c403d100d1070f000443d2200000522442150b0f000c41102102d840c0713403a1144072032a40300d54140c104494210402c00044080c044c4514100c1581008034040c109898007422000d45500302c0d80c0128824000f000143e500003401103000c54250500c08944d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 19503216 1250 19501966 19501987
    0x301090c021603050102130f03021003090201020f06070207051806130c03230906010b030106020a020603060d0f03020a03080105060a0c020402030a021b06010504060b0a120e03090a0b09040c0201020a080408 90
    0x4078098050001c80c18040b40010034000190018003a43e1a440c401200041d202e210b14681d040441c0800381d04040b0a07402c05078158025071024104034014011540c049114500c13035468107904071403110060300007010800441c180034600940799800d60058800d5454a40042014010b0450414080c1350300c034503007056154003a60240e54503110161480611b0603200300d030158656010f0f502d2022a225107000000d18419100689058480315800750440e40c0c0d0360b4023040000d0300041c1070654014001c1c42860b0010b0140320b06035851a1080d009000c42000905019001070320580c4414011001081810203180e03000011030600c560480740182c0300e40740d1005140c000e000e591900c00039082d144800f42096074002501c41d040320002c0360706000719516840070340514040c16861101007440c00321550b8501d1101d0300300006689a42c4201d03420441300b1400201903034147d03804104c60200c00107200b0581d09160050440c0100c90703000a43c03a0030380020300240718480090020740070790b1010170340304040e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 19504466 1250 19503216 19503223
    0x10b18070e13021314010f0207060507050106121208150a030213140702030c01060503010c0c080a0c170d0501080613031b060903030605090a09051f0f020703020c12070b0301090c02 79
    0x140b0840c18402c640f00c030480b1110502030410b5020701e034051000c1041a81c510362180384040072280d82a406068817900e001070580f001d8100603007c1b00d00f552607103404038a0007007280010070b6103401102d100c4800c1c1c2107070300f01030105e00f000b804141341da220401845582e83c503540312030300480c0d5050740e4801c07805514900000080107540300c6020510345d10414485013503400006041c0c04003111000b00002d5a642c03080600700c4900c0c007240d0b00401c0c282084080403075030b0031001e0201740402e41003102e0b510529985d442c10706040d1007603900d20b00c400030842180d0607150340710307503400b50003450005c0c112420100f89000485841d607600400300400042c3c006a9695080000e5004582c07141042c4545034003490301801410071401400d001e07800d244000b034a1021140a180580d68006003d001d05084000804080c0010383c05c08540c816140c100d2001038068078801080c51900a5002d0480700820700c00700800101d42200c044c009610128092023103c1610007183d044441003400050a0313813429038240d0070b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 19505716 1250 19504466 19504489
    0x32808040905010b030f01090b030c06090d050a061d0307080714120301080616020109110906012a030806011706010309020f03010203150307090608031204060209060a0e03010b18070e 80
    0x1d414140000040c80f4070a1401542c0903d01c0002e041c20342e0382e00d411140741103c0012002030350640c000e0080ea101410084020100f691020f000c0c030800700401d071205850803510420441d421a560a40e412040205200031903801c88843c0103945404401d07100c0038924064404081c0c070b5100850000d0341110401c002d0800314043c00450f454496070342d40e540d103444000c229202c0501203225070b440c0e0003c1c1d1040c442c140300503511007403d000043c80749040c4030102400078a003d0512074401b128200341d8101c00621070200c030b5120403042d8032292914004016180107803105051107030b0703c1080d0703840e500500201c40c0e1044081c80c000560000f640000b40428200740b00b06901544004144280b000b100c2200890266098044900480d51121200c02f03c0d070161041855941081c40030a4440b905a00413941003070149102509181042000889562090000d400428500752921406060a0240000180b030850715907445c0304044d039075002009802407e507800c10800c003d0702c02d110758805d280000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 19506966 1250 19505716 19505729
    0x140406050a0303020a02040605010905060a08091f0b0a050103050c07082109030702030d08060d15020408070b0322020a03020906031507111905070b1303021302030601030b03280804 79
    0x90720307503c0c240a500c0d4260048168003641c01c0000101d07841d4019a0410100c8001808180ca48021030000300c403030712009489000180141c441302d550f5010041c610052602419500040100801040105480c615400395051509110401c103042d099030050315096500181d00b42c0c4e81d08ad10b512000c000402c0c26000c400c5944114050203082240000942403961081e01240c0103540c0380e420039150201c040f11144c0d844855207a020f00021548102c032000701520303060150403e91a105494248941504a0604070301c020040162006002400005007403176480507895040142d0007007458a17080703000203801450030002041c1c07152410888513990a004007403c0600d0f050900340100501c642c0c041702c5140d0701c9241c84115001101484004910750300034001c4c803803945041001340389a0017040920001b103195680c004096112401640f407010001c8100503501d00e846070000d41102e41003060365010740c2c03040c0c28040b050170502c006103965900e284180802124a0302e040e01162203581c20a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 19508216 1250 19506966 19506979
    0x602150f07050301061202090a0e06090a0e060c070204090206030705070302100902030a02270108030a0f020f0c0121020a08011a09010f03050a0617010e12070b01050906130c110d1814040605 83
    0x22104c0780d51100314001c1408980103342c0d602e0720f0600609841003000f126142d40c02c80408198062041001001c980c0d01c00b1300f0202c5c10003d0360b00052426041224110046a0001044800c060f8140855070505207138403c1040030715843e80220342c0e110300c9000c000340074001414003000d80c40714102110102105044100802e0741c0c461200035200d40042c00841c01140301c1603018005c4074001306082d59000a140d0003080f40195035001110741144100d405424541400301440d1940c1c40c1c1d000a2466100d103440d660f2041d49040c040d002468417417040f87d006c0c0e440c24003072164140c2c2c0c800c4041c2c40c04c408900d404515919000c40c1070b80103181b1a4040081d0070300414510391418019009070f01140c05072403d494451003c0011252170b4824548002c210895a600602103480d1a4480c13580000f400f03018011188c800c061540d08407000303c07142902240c03245c2a501c000d90740406c01c24035611103c0c0340050715447c2442200044a0060050a0050b460304001c0e024a40715584020b004090042c8103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 19509466 1250 19508216 19508219
    0x30e010c0c020307060e0108190b030f060702070f03020303030f09031605010f1512030f050918090606010302041d0603012004030b0903090a06030504020f04060602150f07050301061202090a 83
    0x75226082192049000b40185840003460502990815090382c80603100c001c8039903a04001c4440380ca420046054940340e42d070402e258140c50800440c8198090400149904d040400c4c0180c82c0c0802940070b01802e640c41c0c1c1043c0300584020003545d8101d5082040c460003502c070080024214040e168450301d0b103a10301602074042c808150008424204412010000e01d02001480420788105000b20b014a2034031230981c100180c032a103407500103400313207140003824404440700142ca41c507441c54aa8401001020a0204401d414000950810024201149480d15100702482c180b640001c910105c030ba000d200140454500790400140020310b00c1501850840c03103412051907403c58002510118420720002c1d401580000482d840c9010007000306480034a401c000f20090600100101d8100d01200070340c0440c0d0301d50b401403e021f80031640183c503605003003081c43c00500314001d1042c880c6200d03000030b1000c2c05400400301e03815585c052420358125409880c0d0744010f4891000c0d0300ea0055510170b030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 19510716 1250 19509466 19509491
    0x50a0c020913031407050a0201050708070b010311130b01080a0b0a03060212070906110a02040f1b030501150507020d0305090105070c0e0a06080105040203061807080102040e060102071a0d0507030e01 87
    0x15031154151084d19a4841c8200345a107808042c002e582d8001e050754411121003025600aa010f031491a2145540c0c07450549655245540010283c2c4101c5220b0224880d14070645011200f20800b516000c001b00300e040110400240311140142c158400280e4a0100308100e40b2814840300107180c00100c2076503106440c8440e115007003011180d000010b04c030101c011038514454002c094000828000806201d4840c3d002c100040c002c40c1d8590315515503038242032601040510070300c0300d48621502c00048540c1f401c50401000c00442110404105007080090700680c1c80c41000080d16804d0b1030416122940c850050310584581c51020f841c4401050001070300b41c82481e02d442c82945000c0c400e100c81550382402d6426101c041e14002e505802120001c2c040c071444854212814001c6412a29407d6440070a035003260b0054102c507600103040e40030030400b560100601c034004e029216049480c9600d180010186002e94509000c02c01d032540c01151300385d8803039007001d50078030711880007000513a13810b00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 19511966 1250 19510716 19510741
    0x5190501090509191104120b010303020c010314041104111318050c0a030b01050913090b130309060309020612070f08090706050a0302090406031a0a060f1401050a0c0209 74
    0x10645000490640700841d540c2010481d66000d0b813002c0901041a081400f941c0001d000340300c1e4030100007030080c0b20010704080a05500444540904c000003480d5045040082c1401000c00c0c003d41410708000380310984011000c0c84980c05074105030002d010489420024025001c072903401c40380c41501240034501c00d41d5849807102110051600038094101545105054550455099000318014003601000d00d000340c00070010004149001460400d128001400c0b024508964001643e500d143c10000c000741f005009412000f00c0c50500110700d11685c0040001c40c2c98040e0700201a1240302000441d11200103880140100c0d6041c45414907211400a10351240600840002212040881c0c01c1110204100094400c55a01e551608900480030350195103c040c065410582d903800000104010b0105040c140704034902290107800c0c1000c0042c1643c07180d802c119109043d00701e00300042288158540c0945100382401c2c6d4881d042007105599103a008c220194200c011041045000d00084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 19513216 1250 19511966 19511969
    0xc02030a0206030f0a0c02010b01080112240b03070504110307050a03200702010e010c0b0c071505150a06030507020303010311030a210f030603051009210905010e01020318040e070519 80
    0x304410044e94001b41c90072400c1ea9209084540804c88450040c80300585240200200901400c043c4038116141c02030b808880c0c0c2d000c020100d4942c0c1e121051600c3e85002d00c100301c02400100d40034000400301c5074000089120180c45482032103000076824141c01e0098000d100e0719100f400f054041900f54003400a1079503c02c4108130b0001d140100d442081c0e60007800010240c6401c070b1203450595907140c5050b83c0c03c0e80708500954450b0072300d000810408580d80242c612899040140c0582c0941e200180b00282446801040901d4107000401100e640c0c00019241102d8111900d10305514400004c20b0520520000240400034801001e0301c0c10140780c00d0354846c4032107a60b148a0481384101c402c60841300c1d140170080280c0c0002c244a42642c1d459044840c0560080e68010105e9000c1c215000070040101c841c50003140d6004001c02041d070700301151580c18002800a18503019060019002c0c1070414400c8074411a0b50f1051130041000030401c005c00350602601400c01c5101c0c200c6010508001c6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 19514466 1250 19513216 19513231
    0x4140405010b0309070b09060702120c0924010e0f060310030308010503010605060f0901020319080907230409030306080106090207020a05060a08070c02040b0a06030f0c050405030d0c02030a0206030f 87
    0x14030000060140d214003c8910810300c0c400076040341030400c592914580c0c4006899a4422803d004c101c2c096034841e1040004803030008020444400c2e14014807807003010080c40701d11742201c2c017090150200c1c3c100700c110305484424031304407160300a0880040d907404503000f0407541003070000c4100726450f6140044101500d0103a100c0030810b82e40c4000301401c0e5611030040766000344043c01200f40c50089000075080300101401501e0402210b1000030a58141c8540d0040005800c0010701090701410b01c4204050b020344a402030401d030088030118070f1446c8110480d4092543c508204051500c25407102c4041d00031700c0001c1c0641d81d0b90b80e807903d001e034100c03100c01c0e84900b80e074980000b1240740c0002180c500380d50316141e0034115a54550291040d20550340b090b40c005447c2c070840c0b4401d41e0b40c280d042020b040107841c00a00d204181c540441142c5407142d81038184103040200344a10356001800e02000c01052604403000c20852001c02d0a240b03000000940041c1d0110500c10203006295a080c402c140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 19515716 1250 19514466 19514471
    0x1021e0a0b040320030c0304050f0f0607050a0b0703021603050a02010908030a09060e01090b0403050706020d060b030405061303090b0c0c040e0106061403060d06090303090203060405030307020114011a090a0308041404 95
    0x1105a1440d01d901c46c589110301c1c1584100070070009410150581a2058001013004000c100040f01182c40c40e40311800440d130075004502c146080100d9010394640068451500b103041c074003101e81c516017a01202c14050240000810200140c44c400d40001c050b86902500198032400e040030f011010b0f160b5644100d4020f410300a00b14001d02c0148514220f035134000c080d50049845548041d18542d100c684160b400c10b408008800001c240d03809240c00400c440e40c600780d0303a0b01d001e040a50078450b02512280400310390f41144d2021981c404c9445007640c001c43ca2259841c041400c0e02440d2058500000307800038103260b41c814031141d065004504460150b121403003007586010054002d48401c40b10198464515019980415242d0744142000fa10905000a940e141900080e1604008550448503036000008000b2007940c20b01851890442c41216000307994100300107801c0d088614100106081c5c000300d0100826515420380b40011500035003415036075070312186004507400051071050300590 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 19516966 1250 19515716 19515767
    0x6060e030f030f030105060c07030501060303080f0a02090a1a0c06010308190f1e110303040c090b0a05130c0311070602070605070c0203030702100210020c01090501060603050601021e0a0b0403 84
    0x1c011007190030301000c04000074556828482080110b801610740c140da02d11801101000069091240402550003034884102600c1c02c1107099000d43c0c401407100c84014010b221064554440c030303201c1019110300c1d00a1103005540d040201c0914003c0c400c14600600ca80c2c8000028032910200808076906003a1040c003c1c0c804c0148107842c2e0301455100300780010194103241c41f00c030fa01848400348102440ca00a00000714418400b840c64009650907519040e504d1030401030f8003424400c0191030741080d01d40c2801d45107803200040e418001d44400e000825203c080c0100528400e0340200c0040995070901d41d140d0440b0f060040c0290000503084a20b20700d008040380c21380740500c1b8400c0000e43d00034019403074090503509100c003448804d400385080d841941ca00305905040c60014055542c07201000241d00c2009050460030f650b42c6510050a061500c02403202690303000c24290289421003c200d040544400350715032a00701d24600140240c1d001800340070805500421140d11080d8040910a404 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 19518216 1250 19516966 19516993
    0x3051b0301051005071b0b0a030c090f1703070506090604151103071112030108010c231e04030f03090302031501051e060408030d06050907030603080a030f0b030106060e03 75
    0xd200a008995024007219000f1000c3c03072080000302840b0303201d0400c030b0301c07810700148001c07064007510780091001100119000361429418400c3c181d0300409403910608003450032642484004c803900403140c802c20103c03d1102c0c0fa00b0104103c80c141584001107030000d203040400240c881702c041d00c00300c3d0320045003d83c2c01c0c045541070141e00c0c51628900300f480d20b55140c08c4000d031501400341d207404000380a8000710302000603406010314020a01c110001c600130000540c018070903070298203039814a80030744010160401d01d92054584a115090b41d000041880e5118500140140d51004024100011051081640c4a0000d100b2a4426821075111003541d4091b10925042401102e4010304480450001c00c141401e0032010088041d00700c0e89403e80f00c48000741564000c100b880451615100c0c20801401d0000e009640304090b4541080254295500d081103445141000030805407030b200c00c1d0795203400581c00980c014400178002c0181d580e0b54031000e800300c80e0440c9106e01c64000c0f04003106c0103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 19519466 1250 19518216 19518271
    0x310090501050307090513050d090501020d03020f041502070906031b050102060f040b0604090803010e07140f0706090c09020d090c05060c07030204050c120c0c070b09090f070e04020a0305 82
    0x58a02c0140036040903410035100b0002850020700510528141c2104400491030034081c071000401140e07a084c1c3c8050900001910386103100181d001098410062071007180c10300b1056505481f15a000c503980d141040c40200d00e800c82c5600060003680c0303854400410412803d2580e400412140001110255540016a19040d00319050415204c8690000300004d4000444a5000c030700103000207001030241d00c0300000d64000760420400204d9400521440301e401070750080d0300ea8120b6560354906230710b01c4080d5002c1e00039100e00400c11034844a6035020000b5416100015007001d850464840d500c61a521001d480c12490640ba40c1c240d40401050718140b43d411640442e0840d001404c215285030700b070200801009103c1c04643c401403120100070400070402c0c501070000703400c0c0135445440e605030860601440c0e900042c3e401030304112042c01520781000069100108480b501515524508245c1d401c1d078041c440c4551081c4000340b02c4010940660003580686040d01000782d00303000c001c184d01c05 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 19520716 1250 19519466 19519469
    0x7060e1c05030702120f0d02100f0e0706080403141903060504050c09060d140c070311030405090106120914070303030f05040b0c07110a091a0a03031e02070e0a020310090501 76
    0x315802c10840c1c9000b5051820307040c2400c0944000321128400e04941480c100200e0310680f10042c1c11199603480c0751a120300450100c0c8815042c20040158000d081c03e95402c880d20544085c8401304c000202454000c12001c640e290ba520f00c42a9118101111005502074018900700402e2a0140200b60350405100b443d208942860308986030869003000c00039290050661106110b03120003002d5404030102c030400d402003201030609510380c40c140ca40940160011034090099520a000420044d514404142d0440321a420f10403c1020486100c40191a0b0880c0c040c00b0703000400018903a10b140000c0f50821207001e56001c2000060482009069403070950380902040002e1010641c080300c00e030000e10300746114424040541e0a080c1c0480c040c40c103554040c000b601d41e240b0059540d144420740e01d08620b401213030303024056030035030b03030081c0204040f03440d102c885444103e035000c40d260082104001034501d0201028891074096948d1000c1d6008580141e80820341c80d0000601010764001c3c5070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 19521966 1250 19520716 19520723
    0x40e0f060a021e0429180103090311070308031e0c090910030b010b0301050108090a0c06080c090a030809040b01050c0d0305060423060108070e090f0a06030507060e1c 73
    0x5a525110011000b80d04070540889188140618400c00010352400620082c003448000d8007818101c0100c10115102d48400900e560b071040224880654103041508110700013403c0000320203045007000c031094100b1007010505442080808001e009102c0c02540c03040c1d43c001d91354640c543c40e441161102140686180b220260f007071011031a603107001101980e100e1401520f543c5100d50781e0329946000002a0302084200308000300500c0a07507400556168059010300082c61082d005030303039140f000e041c203105004c1080042d501103a44224880101c03a400c550040c008001aa100d09140400d42d002404d903501ca00d15024440c1c40c07a5000d48156154411f0b0076002d004244040c400541c047c00008000341e5105542c2c001c06602c1d00e05000b164243d0507005a2070300842d00c0d21000142c5041c20240600090146940d0100c24070f035215404c42d54001074a00c220066034a0345c40c0d00d80083c0507542c000411500a0850100c1c01680c801618000d145044808094a182603072a5860300101e131507025 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 19523216 1250 19521966 19521973
    0x2070b03130501020c0303071205010f050616060204080114090106080606130b0103060302040905210301150c020d12020d0915080a02031005030709020d0608030307020c0918060c09040e0f 82
    0x599080d000d20300300441c20b4001c00c00503140c60850344403942158011115030300485c59148030003d0105017171260b40d0150005da80e50101003030070500010058000c03007602044503004500380804001568050398000c00400000b0300805805582344205c0c89001c50320320300250710305240090360300070003c1c0c000d000f12400b030441301e003c5100d203008602402040100300e06240c0c9682c000001a1a01e100d50804039003e44060580c81c02c1410b0b140d40804019420429a100240b0040c08003400913507580c581c04c1540d00f0080300c2d0355018808540c0380d8011403406000c0080e29228010883c6d00482d600c1e141300d94a94844100030b0311094203406042d1001359a000207410034001880e0803885500554024006035004000280e4400020740760030b010307401c0200b9180c0c0104140c0e1901402c1d019001c00740844030060b40c1145080c0e4002903031600c03182a0070307200751000e01c0810252a101d0700340042004801055030450304d44408400700c2c0b507021501c514040d501c0e0000c040078007240032802800303030b8070f007507019 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 19524466 1250 19523216 19523221
    0xe06010c030e0d030504031a0403021c0e0603010b1c150e13051002090406090e06060904020109030b0108030403020f0301150501050309030c25050319031206050303121602070b03 78
    0x11119a040c4000403000d220a100c100e210958480000305580d500c02d68403156207074218500b0064603188000c21803030f000300c80c0381030100007500800c2626664020300c1c0605016024070300c0840d03210349001c0745203400030300000c000308140c10070380300034031000700c0c41a0100c9280d15141d5050045401d9401d0901210031040b00501424807864034050300401d4113880c1d061400c4603525041e09000c6540e82401d003090740022801c0c2117042c0743c041c1000500f4246e1b01040081100600706440c1c082c020080c520a8469900040c216030223202510082d54004000c48065030f15008010354a42c03007404142d1140c0220500e58416103014020320035005441401006050300d414011341e02600050504032250006103c2500e40110401000312615540c80c080c4103000d07138544a1142c040380641006000717420405103866021092002003004680c50320f403210b41c40da11109880001e1595421090b4503020000302081090424008180995a403030100d201c034841080050380e030b48040d44502507901209000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 19525716 1250 19524466 19524469
    0x3050c0a0c060b0105092806020c01021c03110a02030301050301060f0506070213020c01090b0421080f0c04030b0703020d05060f0f01080a0207060c09030506010b04060e062107030902090603070e06 86
    0xc0500f541d01811308504141045000070030305241d00720326030007240311280f01d40043c202c1d03440d105004001da800a480a814a41e0000f5290088640c131160a040d04017a28580d0031b207e0792000200c10080a4440c0d240c090f081d074000e480c1d60084c8035040c8079600b0031101182e195080c0c0c0c03a81085410080216140c51255402c2c03003070300403034001e58804c116400d03c20003400c0321081c010b66101621a480031412480d1502d00981181d00d10100802c0c0c5000c030089411308560040000758002c01486684200c650b202044031000344170f1a003004043d070072b0080c140702202e9003540140c06e0f016180f0368103001a81d1510244064000902d40c02070b4400d00a888503005c1d0f50040b842150440785134030025103010440c0e2990380a40385030781020350020704040400c0061200a00038540074001c5981558a06841c021004045001c02c6285510a440001d05840c482200d00c0d900c081c01c520050b400f0009262000c0041c00400d5401c10680c05000c406c0c0000c0c001d864085528400d5035050018001d1580f42d290 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 19526966 1250 19525716 19525721
    0x60a030b0406030204060f030c0b0310170a080f1206011e120f180213090b06060901030228030e07050a0b031e0a0902100e090106030507050d0504060204030303050c0a0c06 75
    0x34180394105550361000310250701c42e40104005040340d107140d65041446c5103403040e009085a4052480f904052007404034403208228840b085900452004411452081e40d003401c0007280c0310028218140050012821020344018140e82c030003142075255559a21401950005003107281a40e10074220807000a09078021035419103c000c4801c00001c0a2940443c40c0302207589600c4030700c002c1d43c02d05261500b1841d042c0e64201f40c9c600800d80c03e10212076281c1e40c81c8003002014042d1880394401245c0148641d119a040c2c4002000b100c2e0079842111044041d1111504485090b00000f0308244202910002c0041c2c10021190040c10b00d881461610301c00c400b403500301808642260341200d920781403450214130114003507181c200d40010300c03000034410080ea5007920340800d000d200c412140a2400d035100706d0224112074039400c0104035603031078200444d40c61040c1008001e01e00d180c00203200034400aa40900305072031013074404100d25260f0b03c0d0b100c2c076680100340d9404005110446000000b50064 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 19528216 1250 19526966 19526981
    0x10210020d02040f0806040506060d0807081806030a0608070914130503160501020901090e0c0a0f020f070815070206131203060906090504120e010e0105030405070803040807081b060a03 81
    0x318070040c24103481d0302c246460b00d80c15500525056020605001c03e00a0a202c025007001007210301c00840d441039a9070105902030030324060311010340411b980030140309070039109003036020083c242581d03071501034141c40041c4180d000384141403003a0308020840301c101c0d11441c8802c800c40f8000c40484d1342c1d402c2c010800f50014400480d11070006018150304070213511400c018140c4904005070700d45202c04001051515107a002145002010050180d03c1040d5021501009507030b10301f800c844c19800d8000d9240504d5825054424802c0c2d0400180322100420903d10040c2c045420380303400d0b142d515040340d84a006441040c8403103002007800001518881c140701041842d400c000c2400e66640d5013410883d01698030030302070140c03a201000308200c02e95078411300c1c4a00500303040030110305800000b4074040b012a51207040c400004041414400e04103c04001031046a040304e40e926100d5942c40e4030740e080317441182450700c0b410b205814a129010b02d09000810044d01e00360610314281c41c01c4000d0f0110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 19529466 1250 19528216 19528237
    0x4090206070203060403090e0a06060f1805091311030304030201021207050f010f1e05070504090b03010f060305160609030b04060518070f1505042936010c0201021002 73
    0x200714200060b1000d005192069001e0345401c0c4c5124600b082c0107941c6100203048030235030751030001c05021140d0080c0c009080c0d4081844e1440018440b40d1140d80f010f0041e800c0b10303074007001c040c040064962030712121a056520450807141e03010102c1c0145540da0041b4003000380582c000040801300c6110781d10150000038001c404031010071078100700720707403c45400d2011510b0741da80300c0d100c000041e40704803a11240417101c20030820851901c528001e240b40910b02903011401c0d1120800b000c1b6940c2500400c002400d4910100002a600d261490b513400c0800c0c000000140ca911001030000c0c0148014800c8a80001240c02150780355610f00b001080018800c92031034a0120140204c400d08000304070141c4018510701960900340060440030150509903041003140400003449000c407801d100c00030510f0810900151600820300020090040040e140641105c10072090340d00d110070004000c0d00820420148071b641700e03130700044a03040500000070b80036a200315010f41482d40d80d503000b4aa803192 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 19530716 1250 19529466 19529479
    0x6030109090317040b060906060a0e1504030c0806070e1207030210050c010c080a05010807050102100b01020106080d05040504050106050309250f06020106030b060a050a0605070501110304050a110306060d02040902 93
    0x490302c0030b00b030f4014800e40d026520340143c0010403a00741800322200d03801a0703084405900b0080400d0009044152040115005000d5540c2d1420742d150280706403009554041c9510f1201610344448a60710740046440d1400181e00001110031401c041c00e4110f260b04030440a4191a03045400340005060903c0794081000002c010154840e0000e1180740340d83c5040d80d440c00c004d410038040790f5040d50410382040c5020341022604101c160b80000c0c41d0b480404038082d0200f0416620350060b401000740740d00079180750241280420304c82e0b5000d001441a1041110204403e98840104443d1400120f544c60816803241c542901d000681056580c0c04044008082c48490780f100c0d410b0030060010340c0820090b070b444c0c1200340304110203c0c085036481f0f1001c0e540c01115610b0900002c01d40700c1d10744140400e200d0001100814801300b90403e540400040300510f50b0703818146021581e804090303005030b8a101d0300c0d017641030051502080c8a4003840c00202142c004a0181d02040f0003041d2801c0d00b280d0000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 19531966 1250 19530716 19530737
    0x50606070602030f06030c0a051e04090c0b04061124040203010905010c0c1a0405070308031506130e0f07080115120c0f0906050403050307060f020705011109040c0806060301090903 79
    0x40c450b0000303503c038500a590302d0710241000c04c18540380501032161070380308aa080e041070143c0d8030f07030340320202d00c084a42e1001001940b10f81e010038010810350360702900c520400c1c200414140e010800038811640d40b0f0b500c0d030360b10610310307000c041d182c01400c00c1c0921800d100300b2006e54080001a521600107000a0001584e8120303a5109421589503440360008035100070800c4050010444040e51100203255400304949810340d00c00391940780d1800010040940400407441440708098400e0003200040d103055a40c401c0b8070341c985113040d000d1251850740041040000ca0185880a1752030003403040f134542c0500399013050300d1540b442c81031003548020001e65002e11884118107004a182d4071055803110740015650884c010b2404080303400400601504210400001d88008100c408113600244c00207640c03030b001180780d4068815860060320070360170301d010001a81952801450b40881c202c80800c28913090740300540e514202165041d40c400e60a10041142c0e20f05500120080b0f4403900d08444480e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 19533216 1250 19531966 19531973
    0x705030402041e0b01110c030c090709091802090705090d02040b030f070b030f01050306011a090d150f0501080d051603020307150906050601050304122d050315120a0605060607 77
    0x500c3c108a5010203a444454801055030060002c50020310800050028900e43e0400310359500414481c19000b40c04540004015500c02c000410240c11040340604c6034882400070f41a031280501802e82c800d00c5000f001c035a100c0d01031401c0354000b46000e031205e070000089408200043c030040c0c20141e09401307010709000000c1414013298000d891007401664581c00c2401e0040c80c03d201c16080240a40c1c4058014031003000341d448042d403200e514121555650540101040341c241220f40028010031040d02d01013925100344d00044000140748000f00001c0e0303a9044100e9503200b070002c107480403400401c02400849480900901003034020b004407440c1030900d91310000da18002e0064842e56a9035801d40d0710800c540c5025490300003d00b4600141035041c180c41e04d0034030041c002c40c01000d100b09071005000d5810940d000780d1440802c104203404451080350b0152030f941c8103c40785510f0b80c8034a51604480d04c0d289449240c94005040100030b00e4050303039a0140208005030200c3d901030014050f59000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 19534466 1250 19533216 19533251
    0x9040305041d15010201050108060121060e060a050604051509220c060807090608150307030209070f021606080103030f051c09030305070c050c010302070809060a09060f080906070503040204 83
    0x81c5880401c500264034240784504003000c020320f00d0342c1c11641400f0040059502c0029070b14103441003a01d841c3d2a10300f1503500040c20b44031414000b8101070130300713480310b40044001c6103852140c90b1408040c4a5607482c002080125003084950540e2942000310000050804c001d103640e110449099002c490000350b0703008200b900380754804072003c076a120800d0206550000369940c2120541c10103240c40ca0030401d011303201190051048000d191700810742d1442c1d0740c0070421000110380150800c0c040303003440d08000f40141031441200e005482a038800d500442804401d070030850f4070a030388907041642166022507503000710041d01403c0004c140400e00d04400401c01181101e803020100107184e418030301d000340c280c40000302600140035101c5030410101d01d011501c840300c3e2800340790050b6110000e242454550059521720ba030007000210b1301c013410507040313030801042d164183c94040300c10070125011901c6100845e82e0081d1900410f0100301028003407806581c00c24070003000032a8100648090440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 19535716 1250 19534466 19534499
    0x50d0c26070201020d0311090f030109150209040b030a05030d150b04080105040b07030b0312030c13030c09110703020a061503020303030f0105010f03060f0b03060d14060601020607030207110904030504 88
    0x24400c0d000a0303501c1107680422080403003075501c0c00c0a10004100e2040f00106014521030280034591404011400f03507400c0d0f104404440d0302800c500340d51007440f004a0000d4115020050081d8038140501c1c0c418a00014070802c403590050003103141c6507403d00401e0141c900808055076400440e00046000075002024001410f55280001007628190a020040400c09000300c01418074144c220586902c002c140342c0c242a0801803441e03903e07103038015002000d1160500da002c107501c102ca408000c21440c403a2403030490341c0d5027000f800326502050070303080310340304415004002d607001828030000642190807251862040d030450f16500355036038006c00d055901c21642c00c00d1915502e401800190303044508216103c0061034100007140c01c00c0d000d955070914900032010001d401100060840d9101500c80a44541c40546103121410360201180d48070401e44400d4054010400020310252180c0309540c140f581003041200c0e049203820501980c030340c0c0038200b68100a01000f01149100d0003110354070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 19536966 1250 19535716 19535783
    0xc09030c180b090103030c0209060f01080412110f0c090c090a090b060403060507030209030706050910110c030a030c1a04170307030e03030106020f0f070e06060307052101090b040504050d0c 83
    0x443c5c0b20240c41081030714400104598440e050040000046376400101d55a00907840092140060003545c0d013610b505419010007a01c0f481a08021070b811480811a408803500541e07001e001c035111088015894003c285185801c581e100a00308200c001c20b800009014802a00b464a06512900d8103419180100c0719000440e40000303079003226007820082d0000500281ca0054100301411001450042c01111114100003100790401c6281800b84051545190010b045034064a42480c0c0a04440c42e42c100c19a030b0301c422400c601c51040c921108540c45180d0000480712030b40e10804840c45150400303071945040660f01c02441656030001c01c02180a072030b103500182401c8088422803886c00c01c0c2640070030714030b4006400422002080840c1e0030781080080310b80985981d91407208032214026a850841d200b401c00502100d12491030507524162000311341c0910005401d001408107550f001d5900a11075072020f44c40c0e8140300d01c5242d8498145200320b50528002000b1200349001d075000da032014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 19538216 1250 19536966 19536977
    0x903050c060f0906150a050303070c0303140705070b0304030e0d14120903030703031d010207080a0914030705240d0e0f0d08070806010917010507030c09030c180b09010303 75
    0x481401000c001e1180c0c0301c407500c00c2c1480c9030b14010600e83d440d0a406000300324003e078103100e49819a5600c0c0840d20180102804407511803007981010410920715100c00d0b00400c1d165401e1402d0034800104035054140c0000007003130300318a031040d24012688010810b6080000c0525260090398079089102040d500071054000d0382c4103036140c5e1508000707842005102f41081044046401e44012090340c92080d0181000a500c01190f010b041c1000250b08405072603520000d080ea040040b400e0203003d0040c2c0b20366442100320385030010709103070102c2548169413590001000b0000c0d46000d82245580c82c41e01c01221201030b41c1c0100408454010422114850391105009042400704010081d80540030100a0403c00003010300034010000207486030007004a1440004c5903640181400001410005500c4100048140c1940c4c02000181e640d180024144410521424400d007040c50950360440b2a181e042450200e1000c80c5071031442d403404559486003a144c044da901c1e91040c034020f50294440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 19539466 1250 19538216 19538227
    0x80a0f110103020412020906010c02030d030c0305060603060303030f19020c030304060b01050403080703080a14040302011a0a06090605160206160605100b0403030f030f0509071d01060206040206130306090305 91
    0xc151010151041410548140000c210b9401040c400400458041c2c4902200751102c10040b980d9400816002c0e4162049950302104180c0c1a8001c402255071039404100903140c103420000b03a4801990101da041e4403e202045c42c0c03041d04020319400410310415490130308040030740d034400c4c0d8101c82c07084400c0c0d030000310404c0f080c4502c4d1701035841190f400741303001443d040c11030740c80c02c03158090ba80c0c0180400c182c1c00000341000049900c80d40300c0210302c001005d800e04e8240380080c064100f2540b08005c000c294683d0301c8031800c003119801d054440e540c80c0d0014560402c0340031100d90f0028858020301c11200100b1501585441c001403260190030f07200c40342071000034180780065480185c070541c9090303020181008000e001000b03440a0741c0e494903107072203403400184003180038060101000d280c1c1860700040c010440c0c6d000031484c080307400201141000460070815004130b82400d00c545000344c2c12800c002001440c01c40020010001010004144c6a41f40c0d200d0304201d03044014118007144c40040c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 19540716 1250 19539466 19539473
    0x1203131202010e0f070608010b090303041208070b0a020408010c08090d0e01021207030201060509090a02060706020304030c020901091e050412211803090e15060d0906020d0c0801080d050403080310080a0f 89
    0x38541c0c05003032754080152801e400b0401182e640e100c1d61003654006040012441304003c03d84003105c45003a040700300540181480c041e0308000754058810504191b182404441d1000c0c05080e2082c41854034401a200c1e0342230440c001d40b0303c044a82c04990440c02025a0150404801c8002e482e03244e01943c000036110b400c05050005407400038111220703d90010040000603a01c800072507020701d42c0840c0168480c1c89074581640c0f640580302c0c00075813080b10440040341007a05a4070802050300442e01d005803007136141c0111401c540c029103000c0d00100605c54030441e090300401c03810070502e070140f0103c460880503018403021525103580e0b0040400403046010140b503445505000070f882e8203c4085245e0803c03a440400c41070f4001c0c0c0c107901408000c5610350b5441c07006d80c840c060b0250000b070255079600c03400944c14010034034070208901140320480003140504000880401101c610345a0600e81800c0d911a00c02e242c01c004c05003403c1c40507481c008561120180501040944030364800c00d0224041d28 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 19541966 1250 19540716 19540727
    0x40f0e0114010b071113090b0603070f0f03060b01050c100603020a060807210b060a020606040f050906150303040f0e0a0e010c051e0c070e091203131202010e0f0706 72
    0x181d000800d000d02801848071480d0042101d80e003e038000d02107504104803070007107100b901404008202c001c0c40c1511507024040f408540610844007101510360007a2183ea95140040c2580584100d40744003031030134800a16191300000d141d42c4141001420042c0490045140105803281c2100c40d0743c0700c540801c218140304002402a0950b03003002d4101d80b4141400500e444281102c0c0320384607a8030ba4400b0700d140315603800103054000c00741505030344510f0200b000c1c2d40e440301524020700031441d05c400744803043c90340c0c0f2840303000d94602006020f0a4842a200c0c81ea610030740340c400c40d418042084000b82440e08003071420700070042082c2c6445c551400d04d03c040304450050403089141c3e418409001c0c0707a140c1c0308045031082c0900c90508150300801d032000c0440d0f80103815628103a03214219000c5a0a0b400840c018032840901c400c40e01c2c2c1c00082044504c00b8002581c00c80c2d40c0194030b00d500c0b030005100409030060905903200000f840c0446d05c4180d40b40c022415200002500002820700c0400d9208 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 19543216 1250 19541966 19541981
    0x6030603010b041814030306060a0f1101020408030a0206250c08040e010303031b1107050111070e15032401090216060504030f02100b030a060507050f040602031206040c090302060901030209040f0e01 87
    0x600c040c500f18035002001c0349070ac0c07103190009010000607032101c0e03000500500c198003407080c29000840d21903890710030056070f84e030100c2c03c2d0b0009481003100040356400c0238801840400c142da11f4000f800038044405483c030140f806022150b04909020210b003416413100e04a0085000c2c0c1d0b00451010400c0c49031100d440c0400800c0030402201950300200c2120015500d0b0171128288ac00442d03401a0f801400e003420f8094002d2421404650240300355516103200130840707048110300b6035030489001e0030045146c3c0c0c07240401560401c2e03e10010801c01c910b031f174040d04003a2401840a2403884d020f03643c80044036012101100480d811101038040e41d0380c104124800158801400c100c1c01d601c480c000b0f80e64040d08207005115584500001c2c1d48944034800391107103000b207400c5890b2030f151a5640a910394104a03c0c4aa42c01010400642c10b442d0600801100c0703503a61b15001541d60450f0240082c0c0c1d80b240c803002d414940c081103010101e45892040069002950b500014101c00d00300340942541c119 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 19544466 1250 19543216 19543253
    0x2100f0905060103150b040e0714060705060105040f060b03040302010c12060803030a0f061d060108070e22060b071103010b060301080d080615040905160801060e06030603010b0418 79
    0x8011034034001034000681181503d82001c05100c203032070340d020701e034028024074110641c000f0705000007050503400001c0c2000c1035a0002040441d1840030380c013440118090b02c1e07030141061f80284010080382c14a5880b00030101c20800340071420a85801410706290300a80701100140e640f00302014146a0182500072030120844003031005928180a5940c0c0340800b60440010310769641014084409a9200070010b222440c2d0701c56400c000075800c82982c0344115691804a031011002648852103020187c0b2100401031001181001803140c0503038050b40d540668941c203507a01c81c0810404801005003122500c201e207023100600d40c0400381425a0305151255004000c1840180140d04000c914426071624915140300c00d0303070b5510001107004200750750a45070208002400b00306001a900168400c04520881c00001c059902085400c91801d00c41e0700009418003000ba0031903d0410019034100000400204030400d140c1c00050458890001e0101c451500c8000340d001c100c15588044c0800e4030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 19545716 1250 19544466 19544471
    0xe03030a0516020c0f04020c0111040905090a0b04080706090c121b0b0f16021507140a0203030306040e010204170a1202010203010e180a0b09070f050303030c07111f02100f 75
    0x4806602030354a4114440b003500c0740d10303510081c50051b1200e906a0300381c0c01881e402409040380c480d083c0e82495006014400d0000e06003c00035040040014040c0b040c1540000c5003043d0b07650f135446001190700715035421a000c580700c081c049c0c041140712402078003078802e00300c803808850400c0c503194402d5156000c000c481018a0b070410050030300d410043e200540010401d003603459000209981d04001a841c0096004114038084a81040301501401c2401c1c45120b200c1c0507d215208440d03aa50b40c00a00290316a00420018030103003480e41040080c092144000b5081a488605404505002000090309540f203444003c00b48000c50585014000c2240021840c0d0350401044c0e800c3c03408010000c041d41809001a0341a00c0c0c01007011850b070b01c0d00700000e5029810900e4415455500c00c0c810703100810050680800c1915001c0103ca02032100840141d00e441c03450798407680010070079a15943c4c07001c100d242c0c1d458440e8080803102c0011910307074080c1a180d0100791412089900c440d800b4141e4a1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 19546966 1250 19545716 19545751
    0xa0510080a120503070c141b180106050d0603050f1606080708011a0409090308010305010b030c090a0e01240e0705040302010e010e030102041a0c0d1e0c0201020705040e03030a05 78
    0x10b0001c0c40340e15184145140042e62075075050002c0e2880b015210380107010541c1e0840c06580c1100204240840700030401c0101051842d0808001c0280030000030848840d142500400010b40210000c251001d0465008211280d0701e4a03114282131000d1401c00091f0000034044001140c8078018001070401410100c030242800200204082e005020b82a9107580c1c203111100c104a15034140d40013401e901c00c082c4425121441c005204000070302c0200c0b81503081c5220403186150214048116a001400900c51507441440e03410280590080c040c01c1c9560301d004550381070700e0124640d0745140500394180d141c0c034a0f080e00c407e0041d034020440410454180010b000503030740310b40204841c0e0300c2440c0c070510f10081d10002a00902c19503000d829401c8108400c0460b0940d400c0c0079003104840784090f41c00301261000700f80d9010b91450384403000320400c200d00c01e80c924010300c40d454066006204aa500315106c1d004142190040d004070851035101100b0040416501e020701036000d2007200e18102e090 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 19548216 1250 19546966 19546973
    0x7020105010806041502190507060c081504050402130c0804050d02120a030c141911010204060c080708040b030406051510020304090f0b030304030c03021e100f0302120a0510080a 78
    0x500c8044c00090502500351a042c6006a141c3c060751007201e21411410140c2c0b2901c10060102d40c0f14041c12990541004010544240180081881060f5001401110440c12020000204401042244d014060302040b03c1641c0661280840745421912104420b01b81410520700d026401a088411584040303006170300c0c1e551807020380c0e40340005403c000c0b58641c07049a090780c0d05407001c0382c254911040410011050a403040000b1000f01150b1a0581c4441001c0340b15400d0b8480c502500d00800c4007513900400061004004251035800b0f075590b03900f42525425488074a600c01e0b902980c1243d1114107200840d01e00710151154108122500061a540103102a4403401036105a0308180da80b0340c0b841e84904182e4105808441c4010142d0356266103916100024200d680403d074060b014845c00480f1060008507004010440203184c5405090212004c0350314010546007802090f4080c440c05580405401c8914040c40c980e000c04102803816050905000b58a513000f1091540801034200c0403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 19549466 1250 19548216 19548223
    0x11514030606070b040302060109060905010503191703100905160206150f0a0305030a03150b0702090709030b090a03110a080909130503040315060902070302060a0b0411040b040509070201050108 85
    0x854040454080e100e03910a000215039000351080540207106044c00c1100b01640850b006d410384005403010406503440f00307448000c880c824000c160309a801062420404141032880d00341d91403140180825000c0324000000850304242c41d010040c494404c4d050007208018001d0b107511048040c55070442541002c0b009545400140880d0f45880b0394410b0110301e515280e403040c4591a002e0f291044240c0d607440c00d44d0b541d0307100b000071a00003131825007d01100a1140300ea50100e5019140035800c8c440c0344e40030052445005443c00041c0040d4980000c00900203080c081d03c80c2d25510082c10f1403070300c0d0781005454103101030304413240d41d004030101e06c0000342070200761406100e0a031891a001e41d102c45052450600a000c0642248404a000020045000d8941ea0b6518080c10284409a5910038040a81c0a0340310010090780000c030000d100484a54000501d420000380045042460928040d866500c02d402060b84040c0003d02072040e810f0a02115410154a100821013036162080b400e48 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 19550716 1250 19549466 19549487
    0x507050f030a060515120c0306010e060108010306020d0f050c0a090504062904050301020f0307090b04030c06030e0c0a15020c06040b04031707080a030605031e030f0d0f020705070303080115 83
    0x4510741d1070300490030140c1005c04010740c1600107455808980c1152411650b54008000d203184203124000002c1a0300c01a040803034002c24041c0c403145410390a40d075881020750004c42680d143d10341ea03941c1103401541207000c2d85018014215100340c0e5007801c820020b20618003504054001c0c0d040c02d204000403a215880f80d181071580a654100480e2508030403007481c880c40c3d0040703600d0744c004608038a07400d030031000450080180c0d4840882349a0b480f90007064501903840050403001d00700d00c0c10061607009030005011044030300c054070340c070707605a100080041c41c03280c0004090301000360550010a40400400500782403c41d4118149031405006109501c0781c0c1c003005059140750004041c40901400544208903805440c054440640c0d00c0024010803d03132043e030788248644100071042410200c1c0500405000001461800f600c00303203a0034103940f00c3c01182102c103035114070320700c101440f9202a005952040000d8a01c036842c5040003081024180c002038480ca0b40d5618070307208650800000e03103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 19551966 1250 19550716 19550723
    0x1605060a050c030702040203010b1207031e020c0c090106050c010c0c0507050d170d0915051501080702070e0a061e0602070e06060c030c060414030703020c28090203040507050f030a 79
    0x80d9a4100404240d0440c061a00006e4100e0300100c00459078041c414054a8186030100822119541e08030003182503444004840861f4640070f0010400f01030250002c3c4606507021044900200280c0042001200240d00000000d00c01040e890602e9000313000750442e60b82c0c14544103440310440e49580f615801c0710f115881c4a900303e190310000300b000706000d150805035680701180c0c48400c2e41000c0001740c0400c8030100c6105051603d00e00c000807052003024001d413291100b514014161600544408001070525020f601c0b8100c000035003034072000c41482c86456000d03000b0440501d05a140207805441c4111030764455040c01051203c2580002c0000444006c603007100039940b100f03004645507104000c43c49070070707000000307040d0300304400002d032540200c0c81208038050400364401c0c201e803240100c042c02401a0040f0702c0c02c0900b460300740300a2034506c0541009a501a410304c841181c44129588200340e1142c0200c10002406028001440101019120040b68585030790011f40c80f041d0045008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 19553216 1250 19551966 19551977
    0x1603030e0a0503090433060206071d0f0111010905030706060b09150901030906090305030708010b091005181c0507050301050103240908040b09041107050309120c03070b030106021605060a 82
    0x440c85a480800c0070030711342000c441b00ea01800305404104070110014050100544100004109158802c0381c629005400303c021160089440008204030000700311021410400503285045065800384101300403503200c0d200845e0754402614100d003d41c1c1041c0c1c44035445920900145444d42ca5840990b03850503a2402c0c0380350394076442d05c01600185508031000e8112454040120109a0400c00a500419440e02c4034481c6a1303907007100341030f180718001c1440e810050303050103024101d0291003e0481964800c00b844101140c120109d131038101e1a00f84203116035070414404090103414019100948001d80c001d2105604588564850165034440800c205940c60448120403020703502250001e6072190b001a9910b6503585913a001d034101c00301d0707030b031041e41782985c4a0801622901140c46456009015600300144801041140070000301c0c0f1039018090305a09070825682404a10040c2000c20301d10340c1c90f941002c100030f10741040701c9c40e41980b049001d03070240038503a0b0389000e03610901c2592401e03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 19554466 1250 19553216 19553231
    0x10180e040503070b0709080307030c150501050a050f040222150c02010e01080c19030506040f0605100302130807080106090506040903020703083103050c010503040308070503100b1603030e0a05030904 87
    0xc5a501b0181d030b00c140840d0101040910806601101c0384040c44c1c001c0701c0400801402c00880030807250b0a21030194841c1c00500200214208030b80300e148151802400181490808440210658010315603015415481641445061204054484140081c0c980b44d00d00c04085c2d400030303041d0b0420503c0c0b2814441c4800001d002e0701862000c03240b001c0060703100d40c020201c011801501408003035034998420f03800c150304000e4010451040e0b4088650060074281c0003100c01b0402e0340258080104200c00c819008004501c4040030000c84004000c0324000003a21850007100d60202c5201815040c811810004800d001c29400100c07081660340082c0a580e40b45a0b818801d0b03010101c01c4040107880d58221503400072404178000c81c4080700c0c0030390240d80501100070011540c45c4412030b4010040b80c01c0e04080303420603200e070028503400384d1000d030030307104c01516804200178942086a854219001d442040ca04040c0d2601903491105541002800000c0850b5036454aa00407040d806020342d6403000b6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 19555716 1250 19554466 19554481
    0xa08120c0417060115023009120304031b12120e0a060305010e06010201090804090507030b04050406020a031104080a0201030f02120c0a020d05030606041203020c10180e040503070b 79
    0x200e03402091402589410030045908141c3c071104244110a55000444583d141140c00803540000103805a92201c03038003291050003210126404041c0e00c0000c07018803a1140503120340001c6582228814011a1141e2561918141041c40c0912140085038203800801c80c05022400c0100300383d501c41e00b004040d000000c8115075a0301103003191035101d11003544c0023464a415a00150503500820800050307959aa401a420703180141001401c144081008000d00c45159008540001807460081170070b210310800182541c40075541a0b81c03a560014072120a0340d05071095614480c0d1680016092501d4180342e1520b900010401038103060f00d4508112440f40c55a0444000e803036040025111810180b070b44039202e801401d503200142c41041c07481c1c101280690166441045c0c01012036180c41d0603d043d071031441e084010106d09620403d0950398095985c07a0088039000c0e4140e5401b4460740c0e242c0c4000300d21401e0f95002e000f6901c18502071002044001c011900402c1d0040e150040e00c0d200d505 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 19556966 1250 19555716 19555741
    0x5010e011b11010906050a0209030609010b010905150c0109110f040905060a020d0e07090603150902030a1509050d02011e0e060705070c03080c1509150105090703060819020a06020a0812 81
    0x40040c00149000c040098021f550341c042c00c851a426411100755a40d8803404608035282d5026090108201072010820351520503c6228a000c2480315203007400809a68242921940c00080703500103032421000299080180d403010420301c040320b0610001109854a54032a04043d02040c00d0350740005e000b04003190690440903848040c101100c100b02e0790785d180f04c001800c07203000171150700c00134007032040318880c850150b8900300350020050a44144182c2e10642c0390142000e65059603070700c41c1804004154244007290f902052600082100c840044003e1226a0051142a1118504824012616000a101c6501c420b850410b01e07621171041c00c001110b0040390740700034803d01c8000741c0050011800b01c1c002a03001da24a50440c2c50303840355a0841c3e1240c41402c40e182e6a600442c004002074074011000329007040b00c80c140060102d89031041c082c1801e18100c219068480404081400c50400302103500040003a031001c2c00030b05e1002e664007038013803041095812020700a10b011510010500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 19558216 1250 19556966 19556981
    0x30a08010e0919060b09060d0b0105040506040b1903031101060303051204020604170304050915010c0f03051e0306031005070f050a032c0601080f030a030e15090a05010e011b1101 78
    0x34120b4849094515040c009420517034466802080994080303003060034001c0340d1910403980a00803120580c04c103000d00000f0800185056400340d00c51f051107181d61510f08040d460000003501002c10941075080150402c0310050903405580e240003000c1001c26404810740d19103003044401c00300d0540300d50002401d2070046800c1595101a520302c03400004900100900c100c40741945d0001d0030f5078400320328520f81103c08540c5404a20320925150015250612001900f0b00c0380c01c129041aa640948058420046008004c440000400e003d0527103800c22180b81b804101070002e11403490300030350040160a0402401c1c0a000d0017241d40c508150013a0080000a585244603426028201c0091701c10344580381072a40150140c0340000c00d81820108504c10182d010200841c60324a1404003107008180440740a6403174080c84443c484c0c0210702c1c054031402102110010460751003e03050040c01c4039400c00c20914282c1c58030720041240b4141420038980600d81d0700301044582000c480850262900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 19559466 1250 19558216 19558243
    0x80d05070203030108010c0c1203021c051503010b060403120c03020a210e090108060c1b10020307090602070608040201030c1709250521030708070503120702030a08010e09 75
    0x4100400c441581e00202850480e09650000e00a8150081058540402044000d03100100d1400342911041c044d80041090808a0340c0c401801c5101035008411290705442d20307600a14a428144100e182c00d01030502125011124989810b00c0c0d41d07282c070342d081210409103090050316490380b02450300a100c82d82201e41c0010b4000d100c0c00c81d229485112504007482d803404144481503242403403e107e0361840c180c841c5c540082c10b41e511801c1e103000d46c13500320f5160600d50000d58440d2586170320061008021004080034003503100d080001703020340b0254042d0406001c640c00701c1420069103521480994003e80c0a09000940c40c05a000c1101d08081207200007450000540a000050900007581140002c60072030302c1840c001e596083c000c0900d581e105a0398046822400741c0040c8c5d0032080c442c600301c620700085920381a415904c4140755003208070140c605400202c0c040c04000000345846601003400c0c03000e07600e044090580504417a82c180141440c800b403e0000510120b01007010b104080d0741d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 19560716 1250 19559466 19559471
    0x30b01051c061502060403091703070f08090111030a05031b0706090b01050111012c0a020306010902030105090604050610030b011818060609080307141005010b03040203060105030609030412080d 85
    0x8520010707002800c024481c0202c0071483e00c0c03440090903c0454030600540c5c0c10741c0c40300c4226250907400781c102d0400d07061040310780c082000000b0016650b02100600c0ea03210b610155100d9220400250191443c0312003460706420030440d0041c1030b0380c48812240c1c4140c0355013000181100e81d10312240640920031004050b5803a2041c20010b0203540c0700c690741200d800740d0700d003880841003040b000e00f81c40d02d80c0071030880441c09084141d203200c0700900b00c1c501c3e00000c1d4200c4140f541c0075000a85802c0081e480b02c0700d030540c008014480360611104107503101c0020746080c45a8240300b0041085210041c2c031240805075034184603c4260701c1503440320a00c40e40c010b0250200c07070300c902c5000101c0c840720007034464492403c040080c00324001d1a000d421035101401540c01d1a0b00c949032105800d05800c107030340d03660080014803c0c001d80c881c484d540c080c003004d11c440c1c0d03120700d05481494503028040c1c21030b601c2a848102080031500d4000105ca00780e444400b511126901d591074848840d008400110040c9130 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 19561966 1250 19560716 19560757
    0x70903020d0818060a02070e09030f03070809010608030702010905131b1101060905060a0b1803010504110301140f0c070222151a031512070602010f0c05160201030b0105 74
    0x2610340043c00781c00442e00c9641d855003500380f040198600c105400d00000d038010b00010060a000805841e920841c1c49059074501002000c030b6004503442141c0e0000809c0c661400e2102e00c04007403003000b020300f03070040056150000540001e050004248030340d81c400c00b03070300e00426091101c07078020301840809107600105a41040101a1860446201c5950207601c0c00300d00148614075806898042d56002e0f000c1e40e00c85081180c485041d5200ba034000d8074044800103e2800342e20241f04003803145000f103c0400c0d142401104160039501000d828440c0070403040305111901036032403c4c8030f8000e038a00c400aa41e8011a00c040340844903003540710701440480810b410444103203604080300d1103000b800c4031500c20b0f0b00e440c10b80000545682c08415924820700009a22035020141c0d00645880142001e61f8089041596441c6c0f8141c0c0c0c010000503515100000c0f400a81800754120300c0e1101d003031031400e00c056051038201c051030b8840d000c0d0415481e550b030348001d81d0240c4211101025010000b43d80720 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 19563216 1250 19561966 19561973
    0xf03010b120124030c030b060607240c0f0807051c02030c0c0c010f02030d1a091003030806010302090d02130908030108070e0622090206040b0a03050610050c06040b070903020d 77
    0x1c01668484800760f00808841400d03400d5604180420703282d0290500f40703040d0464403102c03a00b8100031300c80e58100000708080c0c0042482174404100fa1003805120107110040ea03040802030300c480d0f4003044103001884c902c1c045840c3c0c101d00c92580c40a010305c0d00c00c0d2104c121101d10810307013040c040b07081005803000043c08005181000202404481c1c00100d505200d4050011940c250920203a140103070410f01c00b101c1107a05540041a81103803081e10104840c034444001110b501043d184e545c540061003c0400405411510031540b122003404d0071801c040242d400300d12401d016503802071080071541002c0119002e0b5500001c03c268200c24110384960b11400c026940314000d006111420401e40001070052030b0480c1d5040c0001520703c0e0080b80344042c0503044002e400000801c1368003004c103000110380312084602815141e520341c0e5005c2107900b041414001c07000e0342c2c5c481003c10800104413100c3e1000001400f9600301d80e001d0515502c0fa40d41001c212080c02d00ca8000075406080d140214050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 19564466 1250 19563216 19563221
    0x1403040b04060c1208010b120405030702120a150c050405040504080f031303090b04030807020402030601090905090c0109080d050708030703060f0306020301140a0f060509010c02090901060806010b03040804050f03010b1201 97
    0x424895034040b0410000404c0c01c2d40e10380001d05c1102c0c0000c20070419000d00b071002d071030301907002403003402101d0424065500090b40c0302d4408648040716404407070008240240c0700d5a41d602407511f20350030400091070800080a520540c0101d500507500c2d20f000c5030410051001320713540340030f8003100300341c8a0514089040c540d100308041500013942d6581d0206903044180700322002c03250700041c9a807912010f5420301c0046d40009018505000034081c0c000f079910014056640b082c40d080300903040c0307802d4280000d041c40d441d40e0041c0c03034584d0107042101400b5810900311141541c100f44015126503030070504402804541c0c00c146a40c186030b010010800540782c0186058407801c0c900b4406503680d1106000685980e8894117000760341d0000d0801c0031324046c500901040b601172402c1c4101d0451600401d84403101500c50610507951404100410081400040c2c0584404244180765090a0b140c060190140d07014151041f0310b4882104c6603541c0c25032101604000c05030420940c08501c1d9400c900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 19565716 1250 19564466 19564487
    0x80403020120060a090203010f050403050c0d03050c0d090c0305030a0c1419080d140f01030606051203191718060c04050108040b06010e03030f03060316060c1403040b0406 75
    0x81016550862004000b4002c0300c41c2c1e0b21542001007040b541c52002c8003000d000d2860301681c15540c1c0394007036034021001c2c2c01910311803402510350035601c901c0d101c1914542034014408038101450b240074001505070240448107011203022000c00c481d880c81c20310150306055a07000070414072000646603030302c5d138110f400c082e100390049020400540400700501d86031140707101e4044445403ca110000001c0550303010f0080302c0d00c00e010015a2105908102ca444602602c001d103410440c4801001000100d0203803002031321081d1200903441884600d859a2405000021707c9030400603841040c5291040420b0442040e600130906601d0804450000042c110098900f04a002e46000142c4d405881002c4404942c4c0681d1030480c01c0c2c0c0c50340c03114044020090081c134100810001c192045603030400c0032b05034494801403295030382d0070003900301854146005c41c120210580400c0c1003021a07040201c0d50f0035a6000008014a00d641210031411442a90001901c0503070100c0c000c070b08203078000c2d400d00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 19566966 1250 19565716 19565719
    0x6080702070609030503031303090f18060b0901050f0304170a030504020406050105030601021e01200301080d2d20070608090105010f06050a02071a0d050a050402060d090c030f08040302 81
    0x300d505840b04800c595100a50102400d640d2080001c03130040000720110700c5220740245070104100340c1762220160b1048956101504404c0342d000c0200c07101040b1320880c0020401c03910080d151440400000c3c1c8580900c02c1c0f00c4002510110001e424000190071440d40d480800100b151b89944542010300149800e560580c0100e1501d80041034a50040040307d0040c00160000d00e8103223412500e00c0c0d01400c048055100554036109500900308e55079940541440162807d20384035070510b03001c5803519105040c1c17441040f0340e0b0404010303680401e245902d10361a201c1c5405001c0321310500140d4414503900703002e001844a40004140c1030340c0101e164400c0d66019a0b42c148152244440f241c00c4c1c1d0403c3c01640ea0001d28145d040107241d00a0b80101008242c600589030401ea603107a02244200f00b030501c8644004000404c030b55030030564400d095208024503020030490910b6004590180680007128440980c1c074950101440480c101c02c000031341e4001ca41e0603000c001ca1810759002d400610040303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 19568216 1250 19566966 19566973
    0x50109060f0f060501050f07050c1003021b01110a050306030a14070603140f150a0b040806060108060d050a03080a020c07080a02031504030c1211010c020105090c0117010e06031606080702 82
    0x31002c005060040900b00c0e80169292402c18091800c0100241e00c10001115644a003c1c0a05141d841d6034202828000094400603110b21810151090502c0c02d0b9080d100c841c0d00d0200541d180c0c1c513201040c3c445001d40b41c54415101d40c1c1d100c4c0031900e080c5400101600501c0001c0704a2154600000c0174000e6036884d81d000c9c01480014404410b01c42401d803145840b9640c001e001424502a944410505010003401d101031280ea0302c1c402102e6900642200c1e1003a0046e13000c2291a51f0020101c54011400340e0768619540030a45849403103520740c2074010100030a000c04208400d500d41c06603807660b07091905403a4884e6403204110344c0c034040c4100490181c0540161000404460360600d0302c0340e40c05854032580d0781c0710f0f41d44000700b080502c00d13030300180001840405256034003486440700343d01041d0000609130030030400c000d140c0480215014104100801c6400a00d00c0c0c0400150442c1d040f010a50040e0f21904006410580780b241f140c40d400400c95030000d10543e0107200940110740603000e4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 19569466 1250 19568216 19568231
    0x31303050706180e0601090e04050102040515042603040503010204080a020a060e060a030905030712110c0301110a030504020a090c05070b0a050112030806040e060c0d0e06090a12030207050109060f 86
    0x1070368000c0040a40c9600046040e40400c1803e1352400f00c0c9a00c04814900740078559100c810001041c04260382c1a980c40e0750104040c4164104030b2a003218641d10b6100c0c1c542031510b045041520140007000f041c4004040804c072504100b0308106660150100800039501c2d151141c000319580c03005c1502c00d038400d420341b000000303201c0d0190803030452168000d440ea52400340c032260250050030340f019044030310b40300c10803106007c40e000502500580513290742e81d89000107954503141c50000c5c6802c80354400d9141c0b54980c0401c8030488200e4500007410308011946540d5400015519807655000703030016802e001080403d15800f03030040203014810fa10f150b5050311180c001104644090261124002c41003103080c011034069400503500c550014001704031885009a4281040000c1e18954450341c000314140c42155a5030140c080c40d031001d1001401706180180c0308940e00d00c9d011801909200300b84c906500802d00c2070b0111144550044000d214286283c130f802c0000703000c03802c0b04007c00c074a08140b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 19570716 1250 19569466 19569479
    0xc06060506090315131703010503060f100510121b0f0f080103080706150e01051c0c0b071401050f060109050d03020d030e10060306020306040e060708010306020d06080313030507 78
    0x39288500070280c000c040c0c0d1105140c4082c4d207210041c0c9800040c01c0001c0d80040040c1e0a01e4079a540c0c4005864050340302c1d4904400e05241050140442c03102c40181ca08120072410540c0c140b00c11900225403400c125000890203035650080f4104ca051064246040100c154800391403040507207240e5a07440e03014a0031701900b281c040305900005400282106c0040000c41c004401030701c0c0803070140e07038005605424940d2401c144102c0d07921036841104614010001c1c3e00c0c04800d032072a156102c100303c448a410680c0c500703502000b40c2c024000d501ca0081205070600c24800402c401440c0030100810031410120003020080b081220f0140c0020274601c004602c5050500c0ca1030462585a0020807481c490400183c01401c1070700c4800046110318411305011806600441700258059040141e03282088014401030f52208004c00742c00e0344c000c0060021141e40301c502c0d281120303080400140c869025012000c082c4c080c42c0d00c010b480e4880400c566142401c8000c654046a11900869000035903640 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 19571966 1250 19570716 19570729
    0xf0f0405100e04080403030f0801030510020f1c0504020102100605090c030705090a060206010e0a09080a2007060e090a0203040201120203150d03020d0201050a0c0c03120905030703110f0a110105090307030c060c060605 95
    0x2000f3301e280c002c6900f55643c012290040c014911204091504044003060034440c1d52500c0318945150075200d500f27000a55806000624484501c040c00b84456424500810014800a8401000700b1000000501054490070640e418440c000740b10042c55555414003c0da07a000070300a80c43c0320416540480d1203d2200d108000350300d5072180f1032504015050303800381c90211104011003141d03401350700c14a1b01d69070188840c00180c802610340301030340f01c141403e106070420010900c034410744c810420301001d80e0f04540d000884a0680601507035030f58071000301041e941d4015040d00e4001800b03001745010076402003400c8041030f0f00e43d4000c202c20f5941742c3d00c0c0426280305080c0c81006c40c02c20618040481d01c1400b1501c0890308000c000b003802e0016561312465613128400c240c002403644811510820800e000188000034644000c11051031140c4820381d01d0126041040e05000d40051a11070f1904c0600c0903c00440d003000d0a00c506540c0c421000d80200b125000031584d0a140000101d064134211 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 19573216 1250 19571966 19571969
    0x81e03070201080106030903020708030418061d160504051f0f0207050f0d0218090a0201090b0405010207060c050a0b0403030f0e0f150c0c0105040c090b0f0f0405100e04080403030f0801 81
    0x169610038584c0d02e0082c0c05d070000c102c1000150110b00541d84041900c0304100020401800c0b07010440006002021074071303049941c10b80100040900d9a00880608880a458240c0004800540305180e09941d0030507102c500c966446603030442d403c8a22003010303240400068891241c0c80d207903400c560803403610803030f1140f140f406466070151030045004142c2c140866480d40151001d001030340110f00f06502e001001c08215018142a8400c204650455a21142e4038008002e0a8150340c1441d08010010b512581e050054004202d0341040210074003100304503420196070408030108070fa003000c0c00d0080161039114000003c00e400e04580c00340c202e80006d1000030039040d4801030b04602c2c9219a00f480f140320042c00b1500c00c120300340184080f8000a200d110b0049110344610702105281c10004003c0d12440314200c2c1c42840b5034440070040361902c02200701c100d80102c80c001003907580c1f101e030795025440302d8000c4480d0055220410082000b0903000340140d03400780d00c03410556405000c04480c0400309 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 19574466 1250 19573216 19573219
    0x1050f04090b07030f020d0e0616050a050405060a050403080705160803040602070e04031119120f02190201230315060405030d0507030905090c0307090503010e120d090b01081e030702 80
    0x142c80010b15154480d034052004005d182001629019900e000c007001c1d50b001c0b140310400c03a01305005000c5d2981c042d100969114083c0c0c2000ca04000041074064a140900e1042c14010800000c044072814459004c03030300519401454252540c040342400d42d40e900f0b814212400d010081d5102180e0041c002050720115401c0340c0c0103000080c2054802c4d0181d81e0042c1c01141844403882803210420b00070b010b03101c001c0110201c840e141a1542c2081c1c80714441d00c40110050295078006040020303400310710607003001080078086403005190b02c0100c0e110b00000407148242103101c295120100702003401940204032a100c0c07480c90b01c6515041002e580308903c47e066066001e61102c90b0240e02500240284600138100356140540c0c5101040b00a901190ba181106000000b00004150030a041c1e070050881034000b04060198a6451039451007940800820b20102154030b00c0c0400c0b541d0459003140d60301c0000103049595914600703135a05001c80946203014a014032500301c01100106503084581c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 19575716 1250 19574466 19574483
    0x20106050312070c05120d02150708040821070309020f03030a0e0123040e0a05071404091e0c050703110c0108040b0a0f0504050313051203040b03180a03030501050f0409 74
    0x603007038003007603250f00030300d000c942220a00100192591395500104142400d81019240c080581d0400a04100420900c5003004042200f0b00041c190b02143e0300f92310a0744613809a5449100c0402074a004100300300d40241c0b003000e9000c2080d0580d041d001300201602c251980894403d841c010140c413802480925400540d10360050006980700d400c00300f03164180090321380502590380d1400d036527580c450b8110f002c0c80001801807155804e018400c25a200e9000d140002d06148100806101e5101d641b051407000ca8032031081080002d03003d08004242c0313440305420088002e08550103010380d04080c1d806d030041a2021102d811010011a4502c01c5160503502e0b80c0a41e40c85503210401c282020780700250305a030315a4a214114424891980110f0203000255104e8600000c4105e007410a500b00d60301448001400412083c000030a55040e80c0698030b41c65126a9a031601115000004040700010700c075801782d2205058055014506840040e5110809444e80d0001d00c4151000710900a11290 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 19576966 1250 19575716 19575733
    0x1807090204030812100e09010203072a03031e050f04050715020a1e080315030601060306210303110f0a080705030106021f0b060c01050907050d0203061501050409060618060201060503 80
    0x5501d0341c8402d922000101201c2549910348007840006d100844942805039030000500c10540c0d0452440c5995580903201d1407501a03040b1503403c06019800002000d2607107561240000d1883c4901c603082e2511008010406464000d00c0e07031004441c1603400340c40f5401118400305190308103400380215560550010581000e17070340d50f008004515010301366502103090707221100040500e001076014110303c011072803240a04078205410700c50180e1004080c50320b0f105c403c0081012040382c0340c0300c0721440d0078144100307045030130143c003d08102c02c00c0d1300952400207000401d1030700c044060104034620b80c1c3c82c52580d5460b01e00a481d244800c1c043c0ca005a88a0382c04502059040708035010f0341018031001207104400c140106195800c5000803c9070799464104000366080d04020007002044119130030074200c0b1554000c40c2e101d01c006001203142c01d2509400070001e900440440d40286510003007040384170fa56150007440700b11120289070490003404030001e0b40700c0c414010903040d118020060f00300c12 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 19578216 1250 19576966 19576987
    0x606120b1801090b041509080f03070f030b03120310050607030c05060703092a0b03010602030904050f040c0b0a02010608030a080405010b010f1e030e03070b040c061d040e0a02040518070902040308 86
    0x1c9106e00640140d9119401b14000400c403034050014107103403082050312070810301806080030f007400c0300050415241403045042c1d5038001581c442042e802440c626170704d441c2d0a10005081001c6d4000702d0f00b1900c0096100304169009448000700c1c0e02a1301500c0071792711889012030696078040380c00b038400e681e940c0d040c030208903440d010507005608040e40080d80325511841401c0e5504242d102e400503800119081c011402c15001d2594020125900c42c1803514045c0e41d4044246050b00501e51007100100301c0c158454000d40c0074002070b02542c422641c4802410070300812082c03003190111419428030070b55191550145203c3c120954a90b03d60040e40c180e0164500162610103500e2410551074021800d50014140300a10665006150400041c03426051110003031a040c4d1002c0200402a00084828503c1d441c140302031510498011410742c1900118034070303102c0c1a0202070340c00740c540b00520403851104040d106801c1096410346034000e540740e86901c101d010300c6c400900744000130000c90440 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 19579466 1250 19578216 19578233
    0xa0c120c0302010806030f01140610020f03040303050c1009151107030e010815060301030606080c0d1104090201050d1a03120f07120c0f1104051303050d090606120b1801090b04 77
    0x91170103022110a0190a80e446003907840081d0442c50a48540050181e03605007000706d5030289116000420010a10002456680c8128440034042150100347d814190b0710900101c084007601c020f00f4003402d08107040440000580c1c004140c07401f8034041078040c140c1050b40c00c0d02c6d4903603003588424516811500055862980080002c0d50600407070900f4504c50741c481020314081c50240b040040e0380c0d41444d4480c0d160800c0300320010310801c0714a60b00390001c0c0d2803000b5490110400d44001c11480c155100582d51801855050140c40d4103000a0701c0c0a035410303441412070400d0071401c49000e00ca820502d41030901c42e0340041e07420880300700080e030042407080312204081089490702540c8040c2e6505d51101c00700441d44111070341000c0c000300e90038505d01030141a400c05411140006210030a41d00a0117900c00d4400d104201e42e11212842d05126140e885900100110410041200b149140500d135160045903503641861040b1251015020144a201d41c00359002c1102c55aa031a6615500c60 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 19580716 1250 19579466 19579471
    0xf060e0405040c0504020403050303040b060913060e01020f0c0c01080f060105070f050309060a020a060e0c060d050a0914070e13120503090a0c14011101140a020a09050a03050a0c120c03020108 84
    0x210f43d0511200094aa1511310040004600980c007441d01d80c02c00d03141c0040d80710005001144110300c03810901c5544480584100c810a51007d800240f540c0b481010901902070203e582d44601008103055911a8020500c0c0b41030341000d070b0f1a1849583c801c0a40c00c1000c00650b015800148140040d000042400c0d00c809600c900a10480e410450030000161955120949120041c1c2104032a0010000131380112020905100081e25051003050b020411501a10080005107900d07600883d2003410300d0352206e030340c41d070700400044684c09801c1c00442c0e445e40c40d481185940d80d810800284944425640e0714811940315290350307090100c1a07000c880c0c541014290030980e009405140000968000d42800140f10490b029010380340b000c0000b4290085c103540e04000c990408040c0d9411407200c101455000f50800401a12851201c0040b984071845401c02034200065210120510100180d5040783ca48100402d103082500d980e4070308a4034465140090080c0e00d020340034801076008544644c1e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 19581966 1250 19580716 19580723
    0x6010e040902060d1e09020105030c03070c0b0103030908150c0405041e090b0a0b0d050601050103050c04030602040e09190515070c02090a1d03070512030604200306010201060f060e040504 82
    0x190300100b900003e0103903100940b03544000d50784d51040301c10502c0c9251074030b0f50a010752200700a003103410f030000b03845071200810b04c0404090000c00034181601070125465840c0c0c0001c11880c1540e12440e0142c0003114501500c1400c0c4102d04d0000081069018128455a1070106103801d0525110900c000b406012080c40700c0d248420b4047c9041c80a0361040d090024092408110207080110300d4800300c911580d41c19020b105803c041d00041000020045e04481007880d0000329592050300c0c40701c09000300d81008002d10700000e40003172a141d014040900645400c1c0946504454103404400701d0344002e1001841500448044c085401501119076405611802c1080500500d9800101c0844049a9995001d69035600b11100c2200c03102142c140041100011031a1a041c0e0300d5031365403088922383c0f0800483d400400280d094803180c0104003200810350144e0504062500d03030400d29081100d18500543c80d0000010f1810b0060480c0802c840b1951220350000311800c081c40040d040c018400d5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 19583216 1250 19581966 19581971
    0xf2e0c0e030a030c060b04090206180f101805030304030f06110f2206050301081509010b0303120103030e04050c0f03060114040b0403020103060e010608010b070c080111090102010c031406010e04 85
    0x10110380c500b800002e94070b81c46a0b643e40c41440c12490b00c2021a140880c1301802149010b14040060310356a08580c0300054444405105e400001d00040c0c82c42400d046154000d445440d082d00c0071034124500000041c03041c10291030f042c0c0c954040c0b564034050b42c400070300300d42d91180c0d8180c0402e40c95400908031200002c1c0030761810841d49503c0440350701100682518007441c02c40e4080c411000c2c6091406442e1501d0950300e9035140c91301d078507a10001c1087d41006100c03500d000c1480740d2409d5000c0000c10a002d03090f40d4484d00c1901c0801c4410b9024401030340131071440010035015180520407184202e1b860f080040c1481e4a000a410a42d00000e001d603050141440c1103080749070004014100900c1e09601050796141144001000d031382d2554814400b201c410401805055000404d413419158242042602d40b0110b00f4030460b450701603806040d080d482c09440610780300f208030041c42082000e800902170a805160120225050201e450350002030702c8000c41c075558403844001c50304a0004002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 19584466 1250 19583216 19583237
    0x30a021c060b0303070c080c040911041802120312090609060f130b010f0f0504021207030207080712050d05090c030c12010212150a0509040c03020d02040f0507020f2e0c 74
    0x3c02e1840e8840c040c150390108003143c0810000e5810884030084440a41b0203011080555951142c1e910440c803107903120360307200da040280400981d44880c180d02d030000c00240c0c00c4800c604045880344c3c82140d9034644108402e001880e40c0341d000800d180200a0200180590703500c1c14002d071100f04001d4445140700e804080c1c5c180104512411481c00f821f4001d0340003c01a01d0100b40c102c0400f06644194003690042c0100328041c1c0e1500384160748080f640c240569980202c1c50b140c103ca08c2040001000701c1520008210070a40c004003604058000381c41c100f0a580320a92526a00d11902c079030b156240c3c1c00042e00d0005070410000006c036800060001505150010003440001503080300e124400790040040c0021503c1e000240070300800c02613035042c0d921706054a03200001c40b20f900020b800342c502c07103902e03404548580d0b0000701d06032a85801005075041100c4025120740c00310803145403621600f95604509014206261700342d520001e050a4580400f1400307602a1803603545000c18411510b00c1c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 19585716 1250 19584466 19584469
    0x5030604050c0102060907180f0204120302030a030612023001020403210f02060117030d11090a09020406050d090203150103080a12060e06060706060503030d09020f030a021c060b 78
    0x805008510031406406507080d0200028a855402000d002c3e65520900c01001044041041c800c0b80c2201240301282014800400710007130b01c103650101c444001c50300c1c03042007816400300c054012807850381d41c1400303601d0755140c0c500c0203408070384000f03076001000c4070060344c0c0349030f03071405142841c0140101ca00a4484002100d401c9030480c0d0f03c143c80d0008100500821800402642c1d03040c40c2c0b990504d50030b00304514500964560050084c010000f09081180c040e0705030400035980100015681030110640c02c0c14520140c3d00400704080c0a00e4100f030000c40d0104080c000e071420780d0b000b076a4484c01d009001c2204000f41c41b50709016601402550f01680701140e00b0b10100703010b0350080e6003880e660714491100030101c0c112919102005484d0010501c510014104043e803c41d00440f102502e60135075080c600e0080150b40d125691511000400600c1c001c0107802000e0b80e94003c540c82002c1d030403070f4014143c545600d038034005c2d0b0040721060041200451011080002c0703006010000c1c850311243e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 19586966 1250 19585716 19585723
    0x2010b1e1908010603050705030607050307080411030d0905040b030d120f200c060a091101080702010e0f1c08061311070804030312050a1505100509152d030c03100503 73
    0x100440210f0b512400c0910074860100241e4005140940007800c252404010003851400050704a0040004500100b0240312800310200070102c0c1c01029601020702101025007030001511405003d60704003000008689008140c1183c0d0700000d440300d0700f40018204200c0010260901b00300e003c40d80d15501c04040b0000c0b41c8065a9107007907902c2440e030340c0c00181e80301494003000620b00007082d82092942c034001101401150241c0c8001c1c2440703006500e8040f03042c0e024001418030840c00c2d02c112601e440d0840c04c0020f034481034224030044e1854003000c0d600121155001198072a400c50601001d5150845840c0d02651450540303180306420100756a684400c603a00960094002071382c190b100e00c862615070701c605504024800c404002c01301180120010003c007034803c9a00c9400ea04080400581c010b0003200d03003181c00104500001c085000103c20150030007040420329010000000300c070b80480c4541c046507168913900450031030f69010a801c83c158002000561303014100320b400551500e042 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 19588216 1250 19586966 19586969
    0xe031e0a02040506060412080304060e030703020c0f01020307051f0b0901060503010f05090106020a02041a0a0b03041b0e01031203020d060b070b0a0b0f210307030c03030c02010b1e19 80
    0xd0103440209004100940c0c001800c1c45101d060100410001401000070b00d6036010b50000d41a904da90391414110020a2200103099040c0400a085d0342015400708035402c543c04125244034103d054140126503030301034100c1c010b1007603001303035025800301004440d401c244001800c00450340c4070400c008591100c20a03804a00401c00101c0103001149511900402524040c1c0d842451503240600007580c070060604041c0c011070340c401e00c00e804520a29561a208440644005041503a038804885242d104840c103565000c80b11250080c40858211200e0031180d2100e9240002e03400c5440d80c44000021440c11003d01da82000000051241030141038018044042d9243d114201800d1103011948010481c4a265141c07a18810709540c40301c40c0c40e81c1c045401d4030b03842c0b0b4106000e03140c981082c1401c45904441e100118000d8101a44900140c0c2c620b1b119960902c02c5042a60040e420780c1d0510f42451b6004424840500440d0410703400019010f5000704000f2420007508070034480c40c13903603 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 19589466 1250 19588216 19588273
    0xb010e19050414070906050f0d09020f0301050c1c060305060c1606050f04050c01090302010f05090607060e030306030f06040201080106080403030f0c0302180609061204050a060e010213060509010f0e03 88
    0x483c3c0400110303603004207100b0000d0025003403c4d07180c01c014030032007860351041d00108a0b500c0c1e6181c0350f010540d03c0e5000048401c100c0600200719a05080441e8081b9070840258041d800c4034040d9210803440841c0201c00440f5840310042003544c85d075010500d0140c21803011030f2496034992602c8004580c02d4010107015100003080620641400e013032503401e0080d20340101e81070001d043d01c02c00060741d1007510103074500d082c1c1c42c00603160b0400c0c3c0c0001d035061040c0c09000e03280314100035101108940c080011806241e00314200c030008030640114035200c4108a40103404203034102d0041284034015202d1540c424401d2030006800c41c458400c50040340d0300d4000c02c3c800640c0c046076030141c58450108521002604039551030814403001c0c000f903440e02c62580310b002540f690001140422904000000455520850a002c0c645050042c14001d401102200d0780c080c404200c0014450f018400702c80013100d041e522005499003440065030107640c9a011580c0503c9090b018000300c0000c100c8840c9213000d0f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 19590716 1250 19589466 19589501
    0x9030c0610030210021605090901060305031309060e0702060a020a0915020c10180b130f0b030a0615020d0305040201021f0e060711070306090201180e190b010e190504 73
    0x45005104181c507841e82d4044c2958040102e030300f285664401e8410481c2c40c01c8603420f10302d40e50324001038050580d9500040a600c80481c086144040c41144201603d0f01e00e10304010144ea01c0c1066001c52606403280000b60304010080740c00c8110a400a0103803003a2070a04041144c0c1da8861800170b18682803111005030400c40d0844580d1904407002564005e0300c0c68000340e4028079600400309580c80340b00706000010001544103a510a41ca080c0000300598141d030042140c0d2002c0540090344101c405a0110380b91020105900d8034214a41c04c80c0d02c1198000e0204400c0000e00380d0040c00040c0c030607419489065820040340c01c41541a03028840c003003001154410030741107100e2510b04003070409010f2041c21035840144a0002070982c00b142d030080e1021511841d5070005035050540c10040c25a07800b81c9403c0840c0d2845030ba00c3d0240501c4c07007da800e41500800c40c000c03001701c40718200414000f805c0d21040351100e01d014103242a9200c42c038898031003920750b15400542200d1048065480200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 19591966 1250 19590716 19590719
    0x40f0b010824090405011b03151701090b07050310080601060c06090204060e0106030b03010608070602030a0f0302040803070819030c0509190506120f070c03080a020a02030d1d010606051201050909030c0610 90
    0x21020340382d03900d041902c2c10184045a449010009452803074098480155030080ad4000021400d4110143d82500078811082606103640300410740d5004556421007039581800c00201d949002503924101d810790f55030030b80703030840607a140d001400b6041e2060381e00c00d41340c04002c030f0780a8507448014001d048546000a200c84008103060945502e648410b0359a08104030401842360080200d40b501074843c6082c1111003000b010540003401941c010a041d44001707c0c84004000a0800030628a5880044410f0011000608400355840d690302c00001400078040b804075800c0084c0c1003202c00c01200b40059032291540e000c0348007030304000103e074091503182061240c80c00d4080304264000c00d00d031070910422880e68802401000015202d08141039001450b003d40d58030034010b41d1000c0380c50640c1070004da80b080c604c10f0803261150b4681030055180c000300141d81405030301103420030145103000d426541c2c0391030204110382c07200900990b001e0004001c8100248820b0000714443c400440f900c040f01c0313 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 19593216 1250 19591966 19591991
    0x8180d0f110c0603130203030c010e031308030c0d0302130305060a090615060f120b10020105090601050f030a020f030a140a0c050f0303070b060102030904020711040f0b01082409040501 81
    0xc0540c0303007018840c0e401409120a4030344902c3c003280c0d40411040d0f0350fa182d41041d440424514441c19108102551801880003500c00011000340311002803030030082000c50b00c03000c0c8c1680700c1c400d43c0e00300b20055008240384003066020380c02400101c1c8568aa0780d05403a0350f5140e003401d0240442c0e61500c695620b030828000c02a0380d01c1651808200000182541820070001415400350100c02ea0107025510103c0600010f090b081104010000341c0508070900c40010040e02030304068400200c80d005850010406003010340b03a078003014030000d00900d04040a60280014030800c070318119014041c03881d50102052030540d0b0840040d401100070612402d250400c0c1f680d03003006d5081613114a00b90000c1c00000e59000041e81c45190b00150b456945443d070300c005030302e5481881052a00a400480e070902401400650190314003001d48050020710b401500000444981004d103d000c50704c07610200d840100b0400039840a05400c400303040d094426000020300c100c0d0300325401c80300c581d143c83e225240d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 19594466 1250 19593216 19593227
    0xb0c0a050d05040501050406080405030d020f0c06060102010b0d0204020f090301060315050601030203010501080103081308060a06090615080412090305120d0b09010803040501030905010b04050f070809060f060108180d0f 96
    0x1d8445031520500342800d141c0002c2541c441c1d8401c803c00c01140a01090502009100b201c0d03500f480144110f5031a0030540c00b8407000d802c0000001e49901034040015140c0d401802002078001000b002103111890b940e00704002500241e020801214092000003905d480034480c50020754051081c40c004880b12000036000e41d180142502d041600502c0104840d98011482c01d0540e07074850070640d02d40410024148544049a0140030248100e00c28406800c445a12601c03d94000c500140034030390700c51010301c05160078107007440d0010708801c0000c2e02203103402d262404002114a4a51442c40da00c4c0c0300c0da86855080d00d510a41410001907044410010b4400e5002d051804d84900c9074a40c5005d40580d04c03401a88601814541c81e5248182004000e40c030500a10600400400c031381d0501c1c1c440b145403680304903001c5021a000c030f03010035906440003611a225030085607960007555103d01c011100071308050560144072481c0c030150362402c1c1c2c00f4048042180f0707180c3d0300c41c17400d881845802043d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 19595716 1250 19594466 19594483
    0x503061906080703090204020d0c081603050108030304020108100b040303020102180301050403090311010306030206030406090302210a0c031b150c140919030b101404021204020d0c0b0c0a05 83
    0x10402440d100c104540758202e0691580081d140c100002c4040d030600110340a4846c4e03c11a940c6986406104069141c00145d03d501505e001c841451121790003801c1541114001e0080309919030081c800a4015840758401d194401d82d06101c0310080c0780e9440c2c07149400d800c16001200541d401050f9500c4444c07005901100e294400c070002c0c009810b007510058504201d600016080004030f081501181c0d001c0d4112100456019000969038506410710074000e0070000000c50050050f1500c00203003421502900401c544a0964546801c118400907920b10149803011401d0000042c00f4200305103441c0d0f15a0714482c040c12106503000040d245450444411101040500c22071002c1c080640e0004d20560b02d0804081c1c44031060305038840c501044050142d44000c000784a00320030000c0c183c0c4030415501c1141c00c3d43c000c642049003c1c8041005230b01503820602202004203001401624059406030000d50042080c8107000381ca4444404c1e15521541c0c103404241e021140520800400704007244 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 19596966 1250 19595716 19595749
    0x902031e07081e16060f03110c0a03050c0c0402040501120b21030304030e03060c0f0c0307021230070f02040906060906030209060a0303020c0111010e030d05040b0a0b030303010b13090c050306 84
    0x1614941401d0001d08070b65041b60b150001c25513101c0d0905000d01c01d900171644c02c00041001c81d060700509240082c00d5034045840c4140b94000c007040c05100307081074004d0b10180c0b2016125004031101080000780204100c0c0c000d01c1c0d0110104210f103845002e8003104245190032000655a01c0c5868200640101d80d1a044140203a021400704640103040a090303440798550070301c07030300e1791181c01b1400c00c1e1541c001c0c2c1c80081c1d031104100c81c1d8030140d10700003e841344c50104002034500c880101e20440340c2401c404001000f2280608114010000c1c40d884041c0150501c0200002403c0d60700c0d8030342c03904446440d0030200705c0b2503880d04103200b9443c0c04150f056014030129561100503080d50760003034031921030b901c3c050f0500000039035000002c1002c1d0400180e0741c03800c0c81241c0d11504517895030000341806940980381c10f4101d201107652018507001d055401e0f00301800561640e440c1601d80c202c42e074802c440000c007811a002003c54244217502520403141034984d1696203d0501d6400c02420107056501c60 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 19598216 1250 19596966 19597003
    0x402090907081b01021c03060f0b0702130906021606050601020f010506060403110604090203070203090a080102090102070303050d0b12060702010e03070f030c080c0d0305010312030902031e07081e 86
    0x104559000042c110742110f180c1d0503d600a02807500060b85410038555060340320790f0800c5143c042d9594180e100d039080711021820032640c65034403412048207104060f0b002e50000710214001c2840d00385500000505885903200500e4104244807000d40415284011500144c03540b00b880469070b4104228101c0b51080c000802460074444000703800e6110b144001041120911403420099072140191030040040c004155a2440e0060000751203a21001d801031203000c4800340410440014402c1c0d4114940623001410858150b403001c0d01c02d0707001240000e11450b21445110120380700d0000c5071030150003600040042d400d140401a003510001c9c4282d000c80e91051204001040c0c00f4254002c425425040200c480502c0c2e042280241c4a16480e01310180301780140040d5140e856440941200d0044660b22510000c00ca0100c0076030b520742201952507032050760702240e050626108000008a0401112202031f17854111138100361722840c4406003441c003000c140d960742005024419501609a051 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 19599466 1250 19598216 19598219
    0xd0915080609090109020310140c0a1d040605030a0302010e010515031504020414041202060c040605040e0a0b040501032006131e030b0910060f08030a050c0102040306140402090907 79
    0x420400c0c00911041c4650704000200c3d4000e10b081d80b04206403a0064260382c2082e001c44203000140c01c840102103405110740707001540e0b0081f10025100142c00351340d110240010288c082300c000c04000300c1c19660046eaa031100184541d010004444000d209400102c0c102890807001c07800c460340103010140083c0d2009085881d03035400324082d4807080c4014803190503520b403030001c200102818a000c40c042c601d25028001072040c107042c1d012060780740d035007120740c02d980e0603480003200d02807407041300e0218070180700901440721211800d540c01000004000b694070940b40004094540a82c400e884d601c8002d102030700c0040300005200000d40c400e50b4450f161104010083d41c00014502c64521002751506070310340040c01d02d00d440d00003141c002e0900001402c11103041502d41143e00b9201d0203862502c2000102d490656403500c0c21a28000007441c1880c0481c13405a40c1035114498003a5103543c00c000210010700345200309e068150840005401d90f144c01e2052106410014140e0030859010020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 19600716 1250 19599466 19599509
    0xc1104051006050319020f19211e0501030320030403031d0607020a06020102030105010e0a03110105070c0305150402040b0306090604060b0303040918020913080304061e0e0d09 77
    0x30701c1151118580f6650f6a511038800d2542d89000c0c528445c4407500008428654a40c1400070341411441010884661140e00b90240c8411007480c6110a003036940340e8a0741c00c0703450198445040720b042c5000f1070000031810002c00d401c40d0350980040b000306142480b0718080c0c1988082c52011080b201005503d05800c54070017500c00810191f803950b092502035995800ca854081c140c0d0082da40c06001030758035a07110800a4080e41003401140e000034030501006002d843d041101c8411a50400c40c00b2418480b03900c0111801c2e03000c00c00698285a41035400400a48208407410081d003a50001d0301240c10725104100964850a99152190b84075400f8014680408941c8940055202038001a41c003c41da01007070460041c0e511000c2c0460ae84801c54021104c0c2c5012034202600c2120f242181c3c1d95052842c2c03500340c412a0f0081c19080c1b01740001800114503920440304a0060001d1640c0c0c0d00d00c140b4900e00380d90840380d0110782a005800030982143e00282031402501c480906520034410111 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 19601966 1250 19600716 19600741
    0x901060e1b09010504030219050405070c021e06070b010609080606120c01030902030c040c02010504060e010e030304030503060105040e07050c0106080303070c11152107021f09020102010b030d0c110405 88
    0x344001c41180c0024101c020381c4c05401185d0081d540a061035442091110400c41d8604c50b034410700d4000c034200300002c0c65440c81610440c0d40c041d80100384c0a18002c61194840900d4034091400f81c106a0802250000c140712b003142c4c1d4000c1041d40d03142c49505007026211802d04a01500440c0517007034084020300c20780c80224440c0404030081c80d0000d400496400024640110f0f504840d41192800c1022106e00fa81900f00d80e115501400e024412501c040242508070307940311075030600e250800d0001c10000b85c89038006603008081454294100341e11144140d07101102625001e01090000078150080360080c001c550041103460041c60441c6000000035184c40c0c0700e40300090020b100620310b101141d031400390f031a42c120030b483d001caa12113a01084070510070107903220340810781901500003440d0703e02c002658114004d0742003c028501039000390001c00351a00a4080381036540780c841d01e4100b0b0301c00b000680310148850345c1d903c41c480124144040030f10f00c0001d90600031414103040061180401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 19603216 1250 19601966 19602001
    0x402090f1012020c07050316080309060f09040204090225110f0103090501020c03040501020f0609030a0e0f1002010219090506040509042105071203200c030717030901060e 75
    0x94503401520720701800d048495030b030590340c0d601e8614804680e6400c0780600007030141c296101601110355000c180c10003a10b41c020755206000903580104099500d42c10941c02402840408a08050511410000017000d82e0041c0c1c00c440540c44d804039505985d692440000d11007990f1514a401800c5116240d040200d0824a0854001c0f5813005035400315034030035486104e0b0f10760440b000315251a403c11000341c07203500601c9124014030954400c80d8002d1004925103000d405480015440c02c24511407c0d039480c1c04103041540c2c85000d03540740700d5194075206107440c080b0859500060740d4081e40001c4002e5810070180c500100702c80d07510244282d403a18012282a1901140c480425070f482d80380000315034034100c04030b0044c0c00e215a448100c2607000800b400e4440e01c6600c00f01c1445c03680000890451320355180301b0034100071071040c4500d1a9600002004a81313800d109482c030b4035550391102101c0c00050901104422400020000727503c0c005c1c402d031300103447c649001c071910341004c0c03500c20020b600c02e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 19604322 1106 19603216 19603219
    0x60c08070203040815040201050913050a0515030601030602030a15030803010303090e0606090d0203030c19020406060314040308130b040305030405010b0105040605070308130206070b0a0b0402090f 86
    0x10090b03c1c1034a0b060310040080c0c030310400325005140f10182c0180c0c18040200202c6806849580441e030800342404000704c1c090130090118421243c004013044048040d41403601c540381e03804500541100d030080c1c0c002d82c50741c40d01c0c0341c1d0f08020700d6100040c0c68007405200e070000410403044043c60407213009403901c0000c9079032101c0da0b21248500720381207039100000b04001c0100c0d14000907000ba1503800582143c1c1004000320115142c4902440f060b00c5401300d01711910110b18040c041c00000c0d0499117024004010741c02c128114019010300001d003031208180000380d1074480c0b02802440c20b5085150060141030604002d0b29942c000c0d0340c2500c8650a1052511055005008640482d1625540c1600d44146520101c9114201030b084001c4a8018281c010169031400b01811160380100000f5005041645031501100d03042c0008038003641c0103202040c101e40d039640d420301c29801d0 = true := by decide +kernel

theorem cover : BRFrame.Cov 19424466 19604322 := by
  have h0 := BRFrame.cov_init 19424466
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19424466 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 19424466 ≤ n) (h2 : n < 19604322) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
