-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0386
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:32:46.497092+00:00
-- url     : https://prove2.me/submissions/fce8b038-4d70-4a79-b97b-ea9fccc8af1c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 69244606 ≤ n < 69424462 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 69245856 1250 69244606 69244619
    0xb09011805030301061803210e12010e15070207030b061503010303030b0a15090303180b1201060305250f1e03020403051b0d170706140a1b050f07110a 66
    0x83d00240a48004609110424045240301c90900c0044961200500340c4060182454601c003400568950040c441e0361080e061043d038500008203503d040d25070002441d0303010400064074104819510041c50f9a0b91814010b04c0f5a001c0f846906480e041000784100b6102c0c81c002c07d408210030424403070907800c044000b0040560603003000042d480101c03803183e8607544846050072030b1500c0340e4184001c18804141080004d000388403520440c00c40b901c28000f02503445003400c640f0783c420900c2148202540c4018014a070b014071a0a812040c02c05a03265030f4002c0382503c210a00308a0002c505010340101c82c0318659101d620120400051210f186809400300c01003d4041c0d081400120360ba030080425120142d050b48c046a6580e4000814401000300180c44411004403049140d0148000800141020412501504482c504020307400c00b51403800d11101800c64000a0200890588044001d60340310b50100580d00004042c1c00b400c0c2d030303075562482c0c000c415890140103260050715017900010030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 69247106 1250 69245856 69245863
    0x4030b10080d020d020d180f0311090c1c050a1805010501051212030714120403080f010b18060d090506010e01091116060b0f060d151703070b09011805 66
    0x1c0718120411201400b00103001030f0b0f115040701c1844d4005900c001c480002d09486400c40000c41004000606070040d00d4054035400c20005800c280c645000300c0484041c182021b802a941c002c02400306181030a007102c14070400d1000b43c203007c5041c030780c480340440d04810300b6910114002d051030303000e01d03002003032803a0440c040c003400d1203101d22420000380c0c0a0715050001c9080f0903c90345146c0654516170310800c041d61840606c1000c0440601c050108600140300d101f09103003c1c0740079488040d110b10f84024503d03235096050f0020310003420188408912001402201802c0d808105c40c0c0782e03165011184c3c58401000b845002801d18807881c4000181240814030083c1641e004c20000d00102000303c0b20800d179403142522141038566030004030f2000c20010741c0011203102c802400310780b00e040313a9400100756401c076100100a0b941d513240c0c0e41c00e56080b001030fa20004c1c40b041016817582c002a00e80281c590040d803201070882d020101c00603101040030350094800310748480d8038054403602400d0442c1c0d03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 69248356 1250 69247106 69247109
    0x180b040e060a050603150609090a12021507030c02030304023102071101020115060e13020c01150602010e100e0708030307050315090f010315060503060108100b0a0e060904030504030b10 81
    0x1002c0d407602000c5a140c2c00d0204901c02c0c02510b809409125854607000d000c0845c0d00106000078a00078544c56000007071040c172003012107c0059005025005a03449a4902e1550107005107051600d400c1345000c2554010084e02d91080c0c044820710000041c109194000c0b002c41d980c08005030080c01d60060b8403031290f07806000f07810f0245048485281d200001a801c0b02ca5040064102041d1988100a818401e46130b032451a5400740020601425006a40051741c001d41c440da04980d4656283c684c0c050070b004852401403403144001d11000700c069282c5a25170354000061003c85440e01c4940f4031100d01000507a00808000040b42c1d80c03450202c1d4000c2150304180d65000c2d03004004001c4450f1880c004a90743d0050054007000700c0e50340d1843c0d841c80322112010031003174520f03503c0315400101c6075000e10140e03008100c0305024068103030108000c1c100f154503941341d582c420446c40e042445035030310034441c2d6035111800355001d480c40c1c0c40d00e00b426200343c0600d078030050080307080404002045690514010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 69249606 1250 69248356 69248371
    0x20d0905040204050f090702010b03010f1a03161202060702060301060c0201090b040501140a022b1115040f02121617031e0306010908061303020c01090807180b040e06 73
    0x4610940340c108000a0344a1031150540c0810150607108192609290050b00214540000100c080011001c6405e481c030000300320044a6481301c10004500d061030303500d40c0e0032703004401130405030300000c400c1e0100d005503004820f400c00c40410000c046450b580116102c164000b031440d0f40369a5208002401e441880c2401c81c0000e107104070001e291075401c003c1e64151201611080d03141c28450045000a0f00030040c0c4008510800080440d4410b0b007800d000d8201140d054840306035010389070017408110380344601000c0c55004c00da243e00060179030a51290025800000c800700d194450002a5008002d0040c0103094040c0c0c11052704100a90300541d011518244070030354030702440c005d5140d1a1702410510501d105180080c2c00641d0280200039a4043d8050501029581c0c49980d2207142c5401211500d5401c1c0303008658006054040040740d020801c00d103001030f003003820060150303180c0c07040c0d02c10b84581d42c00e20001304800340c120780c00c24200390401400402036042400e01e4945d44840503a07511 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 69250856 1250 69249606 69249617
    0x1401050a0b10020c06090d020d110108100e0103080307110d05031b0703020606043b010b090903120406060902070f11010e0d0b0405010f050f010303030b09040213020a020c030d020d 79
    0x7075054140841840150189600540820624003090004a51150740001d600040c02c2510800596649441000540c002c0340368100c4006041c1c00581015005000c0c4288000104030400c6400c00992131075065a40c400004c139104d844011060b580e00d002100c1c2c1e00014001c110722905410381c41405548904030310000440a451004140c140c2c6108501025005030010400140d06040603000f0030300b0039003191802c0e80b03082941a940e44c4ad070101005080c41e0a900c0d03441e0340c03075000824010901600c60440f108a060b0505415840d920301c1510090541d8000381400603042c00019402980141608801559501d040f868a060610b0421508580b0880e070b08211036031301c2d40b01c0c1138695a901c2c0c001e4080035450056445030495250020720032280c40d905c03042c4160444050380280d500401111003511483c1d419441d001c1d0680b5aa103035a40c0c041d941c1c910410000d40d5417500d80c810281080840181d84080d2039008908203210001c03016054072a00e800000744540c0050404a00b260a540c0e1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 69252106 1250 69250856 69250871
    0x61205060c031b03150303041401030f11030103030c030c020a0f1508160309080403021005030117060c03070302180a0b030a0612080a0302220906030b09150403080606071401050a 78
    0x401c680d000644454440316907001c0c084100e1001c0c08015034000c1850b115502d95131382081c0c00203142d0b80c0281c014451400791f00340e44c0045540c160040200c0d0504514041c03040c0c481c05410348100340014030028003002015440c00040c140280c40074880107801038541c001c0c00d81c813400c0140d0711003a01d1141c820f02d0900307030210381003607423081d40080c1c064507401e922405181031240003100504600c00080e00c850804020000043c2c0e243c00b001003000380c407600ca04e034030ba601d0040708240d40003c41e804001c81da0441020404d02c0504c00c0100e0707a00103400e00b401a180c11009034101202c94030050b045d6004159090701086d944601d1002e184104080e400a00055440301914111a41d006400a000d604140030300800680a500070b40f030b6403030000107005401100d002d00541150f4103540820100c6036a03503001e10510181009066028040d480248241070b031542da0040e030700d5002000a4100154100880e040796980803c4420154000d03403803c0201c1e2080100a009140070b450741d002da5443e0440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 69253356 1250 69252106 69252121
    0x20f07020f0d02011409031006090603140a03020c0112060905090627030708030a0b090705040807060509010c0609050f0f0105090d141c27030801091b03020c010f06120506 75
    0x4540b424682c1a50391071641440c00c10903c01d643c10070136030320fa4180248540500b101d14984121401480c5180002c174419255040c00d1214050744900034603079810081e0b2031000b09800244600310144c0a1130010304029460142d0401000300b034004007400c9040200344400d0340340016680d07015510b82c00d085281005540c13010054202c6141641c00c082e0402d01403407022a003403102550b0300c400d450101040303001c1b954001803024402200e00c000410700100d018000c80000304140b501510740d07410310902d02101403001038581102081c008100c15220383c00c00c010480148001101030844408a4441c2c0e1003011445018000440b54060319100341c1000c0c2c803072680f01e0a024102101400126880c080c10418160703001510034403c1c50a00f07482d0117414030b04080d076403800000c4010070980e0001c0c0303820525004144107010303885450400c0c1030590b0003428440c000750403103205000303040042e035414042c1615409892000511100c203841e2000c0028828008050300c0d84091065050f2411940c9603071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 69254606 1250 69253356 69253369
    0x3050402130605030712060e010c02060a0501140d0602070309080d0905040e010506060304031808060f07030f0c0509060d0908032a0703020601120305130f05130b0d03050a0c06020f07020f 82
    0x1243c550b25070311000e0308010308018103140c071030707107a00036000802c1c0c23004048111402d40312260a1640140c1c4070204020741005148912405080b405400a060310050030001d03580030f209890150855500003000350405004060720402043c2035010f1303644402c5106c0026005900ca0301c41e040c0074600304850210824010b1141034030450006000a0a5031940c0d00d0489481507000703c42043c084110801281ca0401080000d124003200e1103103032002c1c60030703841c001d09403020b081103444024104103010320300f2600a070a466080c0b400391a01510780d400e11030302802030701011801174489a400410312040303005254910364601102803110b000c0303907849101014144100e4901070010307000113005000c04900044041ca9035802441c00c2414518040c108800d01c8000e0381c840ca40300f104804c41040a400c4c0905840e460740c82150040280c00241c401091403502c9115000303040160000b208010180950f1b503405076580c011004544400740701400c848a5030041c2410f0303100d0715020105181c14a85031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 69255856 1250 69254606 69254609
    0x102060907030609080d05090604060c0206040c0302120c1201090303051308091504030501020d091e03020312060307030c0b0301050301050a050108150402150c0a0212030406090b0f0d0507030504021306 88
    0x20010711030360b861502c0b20030003010001c034100c40f18001000400c00c80a40c5001d00d0317000d0007100c1c01a08440c246460818100d503e019203a0080d07402502c1000041606030410382d045a0b0150b0b084c0515103158010075050001e04140c070350340328031007070759018600700158404004d6500c03d0724204a191240c00c00c07403440098508004260744410040d10b100d6081c04041c0d1180590810307080d03410282c0301d544040c2644c1150120300201507440c803100d028031081d4203c00c01e9032000d01100003502061510000c0d101c2c82484c101080f1082d010002c036425460400c001d900941e00100007100150b114a81d03030394107a0083c80345d14401d609040100314602d00c0c40c46130b141210035400040007085212113017480b260034000d0090740c0c005804c00340c0d18002d08010008014850074040a401d58021520400c68801c8075049503945552081c402404080c0d0402d1242c070a1700c824801980c0c48880d000005001403180d800c460000ba0704041c01d02404c2d5030140c01240c003503842240c00180742e15018142030210b4006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 69257106 1250 69255856 69255871
    0xc23030a030e0102070e04080918160507110603010e0103050f0313090902040f021801020f1b151903021917011208040506121b03310b010b0a020705010206 68
    0x1185000d0002801803241c08440a018016600702da0f03a1a200100c02030030450341501c100200113520302c058640404c1c0f941c00c8400d01000c00001d410105024440c2c9e60b036800424041c04400030341d28040c4504003c091101c010000e190b00e50b25a102c05e400e054910f001e00c021542803117a00d001c20010000803050700c548000d0712501c082c0003841d00e0b16400141808940030384c0c105655001c2c1e464480940e000414905004208081c543c0406400081c5080c041c21147e0106401c002c13850403071000190821000c55008803020f8946810b220350f15a00ca105204100c0e00741524400021541c0d6090b80142101502890325480c40200160007940c2900d06081500030745200d150040c03065041c904004011a030080e9003c0741000c6d03c403008280268854140c0b002c001ca865001c001d00c1c1107800360458006544080400d08600708500c0b24a803c1031081a402181c02070f9184107a078003800c0740040094540c200ca408a4256920300c080e00c0d4951086c540c450041c050114045070b40c1d4000200300713002e60709 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 69258356 1250 69257106 69257113
    0xb090c010507150e07060e03070602060f0115091e05040c050702030604150f11040e100b090904030c15050f0109090302070e0c0403020a0902180f180c0d090c2303 71
    0xc5540340c410f00034031020854030b215a80d60005200580802029018096549414411407881d4003003519010007030f80000115030191041100305110700c091203044904070882c2c0486411083c600b40c1c2d030390045400200c1c542210749440c1048218039400c00302244c00c140d9003000b48412100d82243c607481040c01c080c1d0581d01c40004200081c00d00403421402c02c03e0000001404a00d004881c3c3c2580c4d810001d15950b400c000c202401482c4128a08a4010080c2e80c1c12460151420b0a40c52581c0101c2c0304081c4512008000542818095141194036603400314006221440c54007143c0000c15007603800c2012010300c0d00000c41c9003800c078864100f01030f802d900206106407600d0880c582a8800404641107401c041c0800401070311014150000303400803d1002d600d80200c0c078113245c25200c1c000b01c103078818001698911040c0c1c030b440790142c520f660782120310300130340c5d80e92168080b0b148a143c100c0c44043d4980310006050044a06062042c0c842803034415590001c188050060608130f955031550542 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 69259606 1250 69258356 69258367
    0x2105070f020108090721060c1b0803070909060b27031506061e0319020a0507030509041104060203041406030103031707090806010f031202060c09060903160803070b090c0105 76
    0x43c020b603542d80e8400c40600c11586102c2e03e0300705140100d140300403118a030b406114000c40400c0058020300c0000050751500482e881c1c0c000252140f041420703400a03120103000808110400d00c100100070261010a0040c4000340c1d44030708020322503101e01070f00c4100d00c2000b0307000c0c2d0508101d0711100a403a1001401081d4036a00c078401c0380900034018240036841441000600e41900e0114880c42c120b85c0d45119944d2241303000d24100c00c100d4214120103405a00c10440c80c2c21a40d0420180d0b80d0080d01803800c242c5540030040464024450000d003401c480344082000036401d940080280300740c407985007030034030950602014444a4003003808020003051b10b200341d50030704078040e5810302da1040191400080c4140c0e00c0f0b04503030074407030280c02c00211800d0750b103024420f002183e008060402501d00c020f25080c41c005581180600030340000b103201d000f0004501041d5981009441070015024195130b0b91140e940207025601c1e2f005c1e003c200d900803c41d6001071801900440c2c007050b1402c060b12500d2804 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 69260856 1250 69259606 69259609
    0x506010509060f090904050703030206130f11010216090f061205060a0e1501080610062606030a06050a09021c052104080105040309050103050c25020411072105070f02 73
    0x9812664500281c0740050000c1e0f1415a10045c00c14000e90103940900141401c500740282483c0008000c46500c000106400002441c0714507122082070700302003010044859000100d0505c800d9000400403900c003904041603008860b44465a0325000f040204039407956144848044007118030080e00c1d9400c81800184c41000380c0c0c110440103004201902c1d20384c40b42c140c882000b01e400b030b0001000c6a002c0c00400508421012064014010a04100050000c28060658040b4406080c00c1c800b90948011807100e80b420014040c2403584030f04280160b103040650790005015500084c0d201d0b1401845090309407c59a0103880c0281e0001d02031726004003009524016501c80e010840c4400c4400c12000503502800e1040b603018500c641d481c81501d600c1c000005040d00d8010301600c5000d20100b0519003101e01c0121461011164054044a0400540005001440361981f101c8090b0400030f010420015030008040c6610540070704420075501c4018102d80a01a0780002042840007a06c840c015 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 69262106 1250 69260856 69260869
    0x227071806200a020603100612090b060118150e1e03030f0703210f0507030c0e0909010906150603060f05060f0304050a020a0b0a09090b090408130e07090314010506010509 75
    0x4182c4078044400801c07207a400718071103500c01c03181031208034540c50042c000150301c458121001c0b885000240b01c6005161a0070f1003900b0b010745003a041c40080c400100400c0c44104803140101410460b4003004041d8850107002c007070101d0072852007002500c540c401054141100060f80e408003a00650a0a840700d600800541c0626015802d210030425a40b400201e5850380842100a495012461400004804059070000380c0744030149420040143d0740c1540c84840300d92501c40840d900d02c025161016141e0041c1076912000c0c0400d4140300741c0036540c124400c04082102d07160340d0104111986e070114070264940300d026045d4044020400d20030401182d10103190050b0090042d02c142e09559400501101c4087d03000d03041c5414003080e00100c007070f004052035004100900003401000081c80000d0304052004000401e20600810303038000201c41502000082c02c01c0c07410451050a1080014140e48440d100c210342c0b40c0c4210300d06080c044418050711b40101c4041c2c580728286450103040281 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 69263356 1250 69262106 69262157
    0x10b19020a1b08100504081905070c09140709030c0b03040201030b04090b01050418020d06050c07050105040317090c090a0e0307061404050c010c0302030304030305040227071806 78
    0x11032240004640100b161010000c0c44000b1a0840702009840d1115075824610903c1c2d561009900d0b00c030030003001c51100401c8030300d280391610b40100503400115007901d940c0940b00000e407034100c050001040102c1107522200001c0180518100340b65a24002222680e0060000a000002c1500c04214100000c1c0245402510506000ca040c651980104088452014081d603182d54410010040c03400c01e40704000012008109196890384d80750049404204ca03180f00030006540d80c00018680c800b510207840c40c1c0340c0d01800a01180c10030342802441195403803c055807100c3e0210200b0b200000c0010130903950700024182d1a46541c401004400401040c0075a02c244e0108200c400001290383c0309050310b000f00f8007000f0b840d50919041092505886000440c10721802c142c514020a40010a07a903015078903103000314a41ea502e201141040b2500201e20001c3d0904c01300000c005101e10740040e2060070640e551003000a810503c040c06a8060b219980c04158100c00b65a0804581c100021 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 69264606 1250 69263356 69263407
    0x312030415090809060705100c02010903090b0f120f060306070318030f0311160c090608060109021812010f1514090405121c0b030714040c020c090916080303010b 71
    0x500f421a0344003c545c0a40c8000c100301c8032604400010782c07101c00c86100c1d0a40d8000248001c10500c80c0541c1c2c0589544894001e0a61054011481604800c0418204d6070036000c0c0202c50f2040c1d080480901900102c1500c0d40c1d40701e4000c0c100082d000310300c280319402000d4001854000d540c00030b510181d80c80080702800d0340400d0b403100d46100c44d42c07240300001d004015041c450030360000041d04080424001682000c1c0700710b0305242c010840078500051880c1511240f40d8010382c0e030a6284e9080007a84c0504841513040020300943c02070550041d13000b40b11070303511858140242a036000440880c030491303018160802c281500e0781b04035400e1105029500038410011030b680b010ba107070040c1a864010109081b008180d60f06101000200750040b01aa1042500100002820710a80701340e01441b640f1035034050b030b65601c641c44000c1d208000300c404030340014044003000c1c1081c008090b21110a58164a1108040c0c00c00007043d44002088034100d43d210120507003082e00802c590b40c0c0352100005900c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 69265856 1250 69264606 69264623
    0xc05061b07060906021234060c09092f0c0307050a0c06020709060b0403080f090901030305030a141909020a0e010902030a180f12170103050c031203041509 68
    0x1034030400412010002c0c0c81a40c0b51005544d04d4488000e1805401c0c0100c044550700610a4000e81e50315805541c05819a4101078511507111030801c0e500500e6140011f07020900341440355100c0e540011469060390b130208400e00c0805213881881b1000f00d031180c002441158201c3e6220032800304000a8440c1c04248820f40303140154030b89615160a0400340107031030705250400200291601040404000d01c4c286900703100e0307107203000c001d06074500540c400a4051600000c019840107211000c450308090020a28141540c40703080c001c00d26002150381002c0241340c510000c08054001a100703125007074003001e20b840480881814006400079507000c03600000380031004070345001d011180a010303040801c801038032803608820390400d45400d220070011451038441568041511225400704042d0007882001e241d14a451085616092000100302840c8100b000401008801305c0c0c202c07540c420840c00c403071110b0108100c400451105980003003440101117007a0000040d01d40010111a0080401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 69267106 1250 69265856 69265897
    0x50306090702012307140705030a030b011e050304020a0b03070e10030911280303030506030606010f0e0d17220e070c110d14060403032a2a03050301030b01120c0506 72
    0x6d40c0a600590340850b801d42001c60f01c1041d4503031600c00c148900c1024030f4940300000c01c0b0703507a4100030a04840c2d400100320000000074155100d89660200070056000d5440c0d0324070f840d1000812124000c0c4040344610b4202900c0100184a0301911440541064000201c041c0c0c5004028401c0d4544c00c0200d60342201289010040b024054190002d40c042d88010440d454004205428030130000d04190500101c0046841002d070701410034a01c0c010103450046640009041401e400000301d14410b02403100000c800040314843c070381c2d0b20244800043c03400061500c86c160090740c1a400c81c1d201d40000d01c04c003000e6000c10459900500e26810181c01144d00403980e40358080501414148c1c1d04403a0311980500c010035034144a0600481002c40b170310540c812069540c5407094070710f82814170400c0318015481e541c0110520600075808104030b036513003036400949405445600244010b4440c03070610b1000207000346401285985195000020140d07141c10320301041005d4125a800c400940c1c901800c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 69268356 1250 69267106 69267137
    0x60d09050105010305210a0c08030403090f0b0418110f0d0209040524030d0e240d0903090b04060504090e0a0b011710020c0a0222020a050306090702012307 68
    0xb4050103140100040c100e041158403c03a0210803804540c400650020402c0580083c0c0c845e069544a03544801540d40e00e0721142001c841ca030149401c980341140601400240d40804100144221002c4103051100460061040b10441c0c0c50001c62629940301004145244040c500c003c01520305008401030a058094000c40c04942e0201d030a40201502c8100d0341c050301c4a1b0b08175243e24198201c00404082c038110b1402080c0c0c40509813103900504012034104403080582d8600c0c101d01d04108141a200e989040004c409000314a0050300031500d2130b603020030500d1300c003070841c1e05072000c0d51a0300703290038500064600201151a00300c203aa005000d44040003400c0032103074600070402d02c105507244064119209060414a010000d8094410481c05042520208403c4032080e0115001c144581005142c0c6095815500071021210b100048201407540c02202960082d0400e0f50166032583d01c541042c1d08841008484220452400403400c2c81462011440ca511642910340307003483c900c041300c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 69269606 1250 69268356 69268361
    0x18240e0705071208070905030303100501030b130f0b0f01080106020601060513050405040f020a050d0b04080d0e030c061005100203070b0604060f0303050c190b0703020f0702060d15090c020309060d090501 89
    0xd100c50005140c6802c0c020406d900080d550042d00c8210081c41c5941084800c1c05003030f4089114281c1419242c80c0c0910040d036a5495500d007042d00c40400740020100000420010810411843c0c422140701704e11180b40d500c6040c505060340c0032074005008603403c080d0141c605800103c01051111480c174001305144c3c50343e005450046116038500c140c0d81d41c083c410043d01481640100d80070380c144c540120041502c005036590441e4001d8240e0b40c0c0d4a07150440800a4000803031294442d101c00190442001c4000841320320409515070203c4156480d00d040100c42c0e00146801e80042e8001d01180000c998801c03c0c50303402c070f50014000100a99243d00001f15080c06e907100380c01103040030540a0603200c0a1000c1400000c11010034055424030360740d029010000034015408055011481c0508020074008440b00103800a00080e2078080550110000e85403141c440f0886005810000802c680b05029915851202d60042c1d420039046805010301c40c0c0003d40c043c2c4a564850501c07801150702032 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 69270856 1250 69269606 69269633
    0x4060b040c0509030609031603030e0a061d010c020607080406020c1606090303020c0607020d030c03020705040614120f0d0309020307180203090601120308070f1818240e070507 77
    0xd803215521003d50004060908000515000c16600f08001d4208600384a201507204a54581000076958032030034120340c40c022000300010005c5140407031715112542d400071701c00a801002d1000f88040c0303071002c00803600d4076030645045000c0f03600e1401260025809401500041c407421040358070f10821124074a43c0c400c50fa03400719002c41c04c803100038000c0c181c2c14003548a18807402d0302c40350f00e00401a800315141441420000c0c0800c0085040d402c1003520a012403c020507000f001031020546030303082c00c0f120000c407090107486000000043c840c16400414207404005d860701c040e050707419510009030f0107807296402c200e9040c010f2800115188810340c007811000c18801000507120310303003465080d1070401e040c0c0028040002d83c001640000f6480100240e015801d40b600c1034080e4078808040d1908905400100d264103c0440003091400c0310245180a80c02d01c4039090096040c020f200700388000301c2426001c012800380d84180040200d40c0102c87c0c01c854285030103031505880b5215505083c055 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 69272106 1250 69270856 69270881
    0x509040e150106050a0f08040c122609010e0108040b0103060507170f100b130b0d0e03070b07030f090203061b0906031003150501080318041d03040e0a050103030206010e04060b04 78
    0x1288170410607a00c10354035031001342541040005410542c03181c5846c0801c621030513405c0181e0b80340110400010039030028141c1c3c0c1c100122805c0e50020003187c02c00381c001000b0765000441c100c04139402503100f410024080c030b0700540703480002d07400c0d601c466018000082081052281c001451080040302201861050030401e0b0760140c0c60400700404201c3d070142e40e01407081c61105004404902c1c4442403600200d901c001421580c030545644040080c0034210743c040d400c1c1c00042000e000b071007480300c3c02c01c8c4240c0321581c0070405070b40c040d0f074000e048480020010350164800e000203940c00c07036100601c0c20588441c41515007090186000118294811a0721803144503030f200d420000c10214542851032051200006e03c800d606000c06146d5a000303001041c0117200c0d10340403815081c1c965901c040403413020a00c003c1e1028400601c010368907441845120f003084108e0340016054141c61150505a991582c0030b8800c9034648011004020009071081e01e80550b01c41c0c0d0715075103030384030320a002e1351341e0300b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 69273356 1250 69272106 69272117
    0x10c02150f0903010506040b0913050a12020a0c090c0c020103020f0d060b0403050c0102010b0112150902030a0c081311100302041e0302090a06050109210c060206040c06030605010509040e150106 85
    0x150b002c1030509680c0007074111381c0a0390600710790804a50754288215841071400001036850784d0070b0f090451404001d503002402030303801380d000e0015040c0d0215030340405500980201244075a0b0380c91910485030000610400900404009001584a60010604a2a0b0b0b2807c607080000303009011088030665031106901c2d1000040410400c90248002901c502d824002000250110000617001c82e540c40390015003142da803114581c40100898402c070140c851300d4821900c0749042c120700c6009045115140300400c4200001402c0b408100d40c030360030020ba000134581e240580c5030381030248040a201d22481031640130300021580c00e4540d51103e40b2904048808081c191860061080c007100c0540103d4005040210a00c4241d81001e504000ca82c4121a4a1802881810511900d80040c42e00400d040e800580c00a0100e41c00104180203e014290b4200c096a8440b015002c0f607640d44145808154180804070940c40c066014000401c0004142c07441003000f4100708140e45001d0300701c00c0c0800c3d0b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 69274606 1250 69273356 69273367
    0x50a09050d0201151403010f05040506150603042003030f0c010b0f0405100608090f10050403020601060c0c05060d06091407110721032f0105160806010c02150f 70
    0x100800c14100840c441c1c0c0000c100d40004440c2c0000c0e0b1800034081c03200b10904c200c0c0001440d8070b09501900c00400401020403c2d403c06240c0591568015921032220025048040e1400e02d003076400c89002d26409140070040410501021034042d500c011100d501d40002c1c045003004601c1a801018611704181c0005500d01c510001c00c0404007865018500491502041110b4a40400d0054054400038100410305551303030000c0c9440c00388a036900300b03424012a030300300085030170315006240260304c80d8003902c030503030380340c1c44120348030382c507440024240e2624000308024038100702c0010440800d0310200417503420f4543d4544419101003410700c10030b000f0f0708020400302d10303032218100260410701009000d46500e0003060304a050000cac10b45075032000320803143d00d0405004440c5c240b01407016591242074004040e41a2458600007400d540d02e0754200000940c0b4010348180c00c2100c52081e407148007160300c61034011100d10101d01422604524408442c8503a403003828058020290302c450747d20303a00c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 69275856 1250 69274606 69274613
    0x801050f0c0a030f0b060c0c10030e0a140a0803091b010509060f0906070210050304060f1b08040c0f080307050c03060103030206041b050a0e06100905030309130f050a09 74
    0x15000241040c0c030104003181801080e1151034111964030760140b501040d01c0405010f003c2c014820401d0702039211100007458040900b02003602c4001c44821204043c0d104140e030815030a0310b65001c041000c50300502c80200006a0340c002d00c01c2c134000d0040c21641148055540c1040035402a1400002640310000d00c41e040c401942040c20840d60a18100f4200700034040818158041c0214000045e080441e07507a000e0b403100310642e0542500185401101c01101c58003a00345e0740203490aa425a003009902c0c41444046e029034000a000305910310b691182c1920304640d2014043c004a40c1e02c1ea90600009030401030300702e1800500841009140e9a0400b0725010b450243e0306090743c0d000c0d401030001000400d8000c0340076130b400341c3c1080048201d61103078101050711a042c0d401103a407003070b40d0040206d6622410a0540c0c880d40059030740ba1068180740d4000d4443c0340710f6206040d410750003007108800500f4002034100320004002004503000c407207280b1b00015140101d5240c00710035660300340401030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 69277106 1250 69275856 69275861
    0x14150304110d08280801180b030304090204031712040602030a0b0a030c050a170c041d01060305030702011d030c12011805030a0201060f0b03270d08040b010609060e0409020307031b0801 81
    0x14030352002d20780c1466a882c1003c0c02100703052003007c07210001000100c081515940102c81a508000c080e2903459444219a1000b500300e0b000c29603040940c00c0c0014211000304085400300704541c000d1101d142d985d513458401070b50009000400a03601c42441c034440d80c5440130f44070051803107801c1890450382040b0900550550071f5108000b4002003503180244030b072012881202c000e6080d100030507051080c2d501e070b203880345804008112643c0380403000414071202001428605100740d07110b045800031080e59411040d03860500940c1600440d4900d5241d00d400a020005080808004190303900500141c808403076601d10155a01d410000b19200041e90a02c5a84007400119a40411241c10f110708107100740001012401d00300150004a6070a404a000c100d03800030f60f400c2240d607140520304006080000940b000c03617040300f060300080b6105025031070302030a5500c65504c2000d02d1024104100292680704000d076014054400c0c003002003074410b103502d9020f4409030308080c90075260403501402c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 69278356 1250 69277106 69277147
    0x40f0803190b030a0b01050f01050702090106050c0706050f09130612050601090b09010f060c0c090c020a02040b0405011206180206040305062215021b06070e01080114150304110d08 79
    0xb20390014030103c80000c00110317401c3c0c15240165180450750f58104016201380c0b00791080654040d01244c00014544c2c1d02c80020400c0d0207201c2c080d200420381c0e03a4401e452a0281b646c1100c001c02c1c051010011500b00104107203070391141d017240410880d80d1020308004a4001080961742900021700600c0302d0304090050400c1200103030b685410303640c50a02d4039100f0218030300034042005444030008062020301c00349040601031140c03080040150b508000307507440500110481c0500d007400c800580c42c0c60180b140074101c92240708803503030385c42503642c50100900c0448103103510035a01d501c0c040d0150b140c080150015500c100300a02090a00324004d10001c11f1110010304451101e00284000441580d0f8000203c9214840540c032054084540207030341e000004500f42c20b09c112410814001c1c1e10584005d002442071f01c407000c2c80d90302d4108030f070a018411185a031300813404080341c218424595001310b62190250701003101280c2c40000040807207130f500301c0950705444040b07446002009245070604 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 69279606 1250 69278356 69278359
    0xc0106140f030601030210021c0c02031509030301090207020301110a05030601080f0112030516060c02030d1d07050d08040306020403110406050102012a030603050313090509030a0c0605040f0803190b 87
    0x6801c8036028000a655440502009010300c6000390b010740403e0080000400301071441d24026280c050160000b071000c0020b0105912a12403100000c2210b030410103458041c0c0400c001071032035607007460b9108002c1e6108010803038040d9a61007580301ea07145180d01800464500b0f5444940d40e0402400040480c04082c01c1c0034448401c0000400000c9114007031102c1d001d915090940e200c005ca46035024041c00d0954014142600780171081d0841540440144009282c5e07447c204581d00e490818000c5003400f074210340c11694082501030140323150910160810758807400c40c85207441e403643d503a18240d0700070303901c22070b4403000d04009202c4e035103814012900640003c4c4002c01608000d00000144201500d08600f12040e40c900c03c0220b141c400d41004d0051a04071045a0755007a10b4140e0104000304c07403249034007407460a008105440000f1080310420a403d650380c1090400c2e549624008100181c0100d03800c009038441403000501c04005140306613502049905071154844045003500c24201c4e515 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 69280856 1250 69279606 69279619
    0xc020106081204030b1504090b1807030302060c070609050f0f0106050f0105091201020d0c05090a06080103170307020309040606050901080a020f0409090c091107120f080103030f140c010614 83
    0x100140703000500b680c04407504000307000d8171516100c01c0c02003441a09041c01e0342180c184541034081c0803c02400b14014075540c440202c03009a0740e044280c03101400c0c0030080058200030301040444180c0000b40603060b00580d40003a400095aa0f0b841c5080c4090400e281c854001e192601807460080c4551030041070b042d40c541d01701c4800600000c1540c4205020548144000c08607001ca0003400d50640d85004103a281c1004442d9005402030706940102181c14801c1100c10408140c2d1761140c2c03000e40c102c0351b02c49800312140c2c0c10050342001c01c3e04010700706002c6200612520507030b076807140150001400c4507160300707546007a01313000140740780d4004202940841c0108883d45001110508a80c200c1da807189000850741d4407031070100682c400560142003081c1c1000000c8401e02c0a07603005245642c0b00d0f03c4032940048041c0002e46941d60340440002c0441d801034010030220b80500a070740f610125034039141d680003684151021176600000b15140c01a03540c1c3c0c500b4411070040036000c0408032070844a6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 69282106 1250 69280856 69280873
    0x30b092103130501060b0c01021e070305040b0a020114070807020105070801051c0302030705010f0b03070602070e06010507020415030602040f08010b03030a0e0630010b090a03030e0f06030103060c02010608 90
    0x80d480c640c803001e846041142203141104081c00400e501060150004501455030f07414841c4e81355020b500b05444a8102e82c00d00b054201d50b040c0183c003211a0141d26480c1e040c101403901407a075200c0c0d000b030803820088d5501ea04d940c0d1a480340400c6100c1c400c103000e1301c40d44814200188002d0031910000d01410a000000005210a0b0b840031201100300c590ba0104001c0e011840c81d00b00c0c114003910304020865801c1400052081c00d058010345945c0805404955000342c0c2c8820403a600c0440e8403441038a20701c030001103046944a00000c0a0141c0058404140e0f54140c2080900740c903401d5100380c0720b40c0d50224062050f548040d0f000c0c401002c10400911028080500198580c440c00708007e0a00200d50744c8030b64540c681d00c007030310000800c00c07800d1014285880010304007926007017040d20040c51610700204038030403860159441000050701c0c00050074150743d01501c481919460303099106815820b8030010390b440c61b00440c00b0318854080404d003035102c03100c040c2c25204a50030000064215a11 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 69283356 1250 69282106 69282163
    0x301090c020102180906010504181b02151902190c11011416050c1909060f0b09211e0f03040302031506060418090c24081807030b09 58
    0x10744e110b10802110140c00d1529058016240303441580d0000030002c0d03e0540c405841101503210036140031a40036807070004445030008036103a105105150003540103940100b101444505582c00e010140c00d60010318144008002012452000c19146d001480512210b410410200a04030710981c0a00305440b4070030603004040c600c2d01400f259489104032901d8011306104d000c0159080b0f4071070260407801040020204181201e081d8010034000328140b031000510050703514190000c8031141100d42c0d040455036000c1100c445080700071240320440c12101d03c800d0712428440740c20b1020001d50911004280c4c80c0d83c503420000c541c50803601e01c0d0002d0204001507200803c03a00c611850140000d100d6641d203a0024040b8000d980252200d480141c1e09050160401d91240011034010a03c1d074140340e5584401c040b0240030030581446c03400c10070300c0c1e20244a0150606540105c0c0d00e41d031020202c803900c2a010b280482c260300030f85070001c4034414030070442400d2046070315074420f80421340042003500c00e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 69284606 1250 69283356 69283387
    0x30209131a09150405010f09121e0509040b0102070905190608060402010c0f030c08040b040611010501050a060e03100e0309090703050708070c0f05070b0301140301022d0f0409020301090c020102 85
    0xc083c5540d6400540006040160079440615500b80d007800800000c2c42c84d0074403071615005c8880000102d51600141491034498007071035900c54140350703502842c10340e5a03400d02c8050b007049240c0e18150310880c03401050450b034074022940300d00c01011407448000900070b1294199440d5038040c2800e034201a080c8030160342e110307884054258115181407001b4200380b03811610540d600c0005000e02c000407402003520031580004000b22140350b03440c55001c40c0c0e0708400c03600300c50080c440d0a0340700075904406c0080600a4000401103030b00141600c2e6807000c91803445080d11205010b1603039581000030780c0100d6151010314079070810450303d4200070703e2a020b1f0000d0080300c40075140350309100400810004014006c5440f410060b840410340e0000c5a0300d144e0360581e500280a1650490a03542821085080c1442607406012501000c424400300400c00c40c00c40e03443c4d812007096114002c0140d0340700444004000c00c01044442d20040ea298503100f040c40031641080703146411a40100300701d0341000d1090 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 69285856 1250 69284606 69284623
    0xb0a05010333090606020a030807020c01020a060c12020f040e0c04120f021219060501170303010e090a0818040b040203090a020f040e010c03090203060108011104060503070306030209131a09 83
    0x103a0100d00c0c00009028508110000c2e4410b400c1c040c2040004224a940400c01f8a0b403640310780c0310095030740c03605901039841f01c0502c4285801a030041b0000c002284090300070213024500c0c1d0030030075048180d109109d02030f40d000d840f00c0c04407460700003410032020442c080c038192302465030301807582441d0804026200400600402803c001314038045032003959510722000c2ca05844940440d01c010290411404c502058400c1c1603503043e140c000001145888540da10380c80410700c00285165030308003181072000040242039043d240c03048022400000d00184000c040c02c0035042d00b0759001c40d406904110586d8041d83e07010f4080d50051040c84110140000e280c05800c0e41160f810035843c5407580400d0082000358010400356080021540740036030180d01c401f43d0b090080d404c0c0d0340f4681e01d503000c1d00e082c3d0f88440c0b0651410601044100083c03885100a50382000c107502e008178145a490b000109000f0b07003600c01040c044100450041000341484040255441807002d080785443d083c00b8407512000c50 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 69287106 1250 69285856 69285911
    0x1080d050d060b03010608180304080d11071d01140a030201140c0111180f040e07030209090304180501062d0c1103031207021204050d021c0b0a0b0a050103 68
    0x11481d0807055015800c00b001520460f030546032250703511000184080302c141c0f84009580d84030f072452688032030080112810b68881c1001003030002e0b00b050007190406078a0400b440c560103410000b1896903e9684524001c0b4040205032001e54100141c80807424500d480752807081c1c00c0c803007003040144d030003014810704d22081c1d003001501e03801180c2007980580710141622403800f50014108000381800300310041c0340754040d1260174085014000b808102c07035400c42418800e60280c1c904000510b81180202c3d4000340d41c0c42600e050954603800300f40c0e060710354090303003a80c251100c005102c1c440d44033703848040c001d040d1440c51040c1104004001080001d141031034040101420030388043c401d8296214406d1000681181e42da0800300c800e0743c80000041c2c8070140140180c005030741c0c6d0010744105440503210300a1171007001e00c00d0355080006c0a4183c0d00e00000e0a41b1803c840c102140b503994016215000c0d072a002701d000c000480400a240090380c01150501d0710704604116900d4440101d20140182c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 69288356 1250 69287106 69287117
    0x70906060f0c061b020d0e1804081b01050406050103021c0f0803061207170d09031e110303030a060302010806040c050d020a050c0709060306050f150108040305041a0306031501080d 79
    0x502c0e040030005030a85a5041c0e2035201ca0f401160319560703000425122000b00b56840c1804003941340100000c150740c85075154070040070000801d0108200400500501d1124011103003c4090182d446094641c225001d90304240d50384010000c2d400c04284030010305c0e001c0b00d5144c0c0e42840c02d82c0c50315042c0d02d9000d0040e0014201200040d0b1030340342c0c942c002c0701d400c0c80c110884084c141e40746201030b24901c4501810b00640603130341d4085141805542d0801c192580400700d408e014241700799101c0805000041626200c00146080c0d0b01e0f40c50601c0158010703c1c030200040b40060a50001501c00d56024086901607880c01c80724040480d8401c003500e03051004107901580d40c0300310160480300c0d070040c0d800d03d4009026165000501000507408101101d2042c1c200340619500d00c0e10b0341d86e6004040301c0b90345c040c2c10414441903e44d882800c2e60780d40b061107070030300d2406c042c1c407a121100f11103088100304d0104400002400b036203240410080843c0d590440041c040b40d0b04108a207520f80c9004000ca400703200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 69289606 1250 69288356 69288377
    0x50705060f070e030a080d0605060712050705100603150506030c0315100911030709080a0b04080a230a02010f0e210c010f02071a01140609040609020c010905070906060f 74
    0xf48aa00d4943e6505002411954100c8440c00c003101d295001800001c15035241203000540d600b0850b00341c401c060b8002c05001d04400d102c000550721944443e80840745405001c04850303c0390046d1159501850283d8048608000ca44807d1800c84002a141a201ea0300212203929541d80001c0c0940c1401503d555290564940300c0340c40c403040c2000d0304150540350a1584602d07500d110742010710f110310883e640d10343c15650340c0d03400c02c0c0d21140c05c1600540841d81d008002000700c0c83c40001042030150f03502d84803081000c080404c14969281070300c0d48980c00d600140c0404a00e80c24051400d1a01c0c5906080040401c0304403c1640c500f0302c50510b1544628451420102084140030ba42c880c000c020000e210520288089000960288004507194202d04050581540401d000103050740c1d04245109002da0311300040040b260810341102c0d60142e02c40c81d02094005060020313000900c9401c0010600340a42e20b002401d1400903040300c00194500002000031a40c01501c04c4440c18041c20584a030340c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 69290856 1250 69289606 69289621
    0x30b011203020703050a06051e0709090b03100c020706021b060a080705070b0106080f1303020c150c030f18100903060207022107080106090204050d08090a080a08030405010507050705060f 82
    0xf115644050201d00411008100b80903050f08401d205543e0f50f080030201c551090300d1001086e4080e07032050300142c54100188100542648940740c1101c0081c21541c01d5010b9074101000e84040865070310050b0402401000050303010096107071044808032041c0034030300254010036090b015400d20301080115010100750041c0c010030881da0400d40102c80c200c00d543c1c5418001d05460000d81d04075000c14466000650000d80c802090040d90780e155001e00318110910003001241c81c4a40700c00344c0c20178820051032030103140c00c0000308440d405001145071076000d0388400104404944c49901e003e110b45000070a040342d400320448040ea0390000c00162203025500200b42c1c1545030200c2c00c20900d440c00310001c80464009401812140d1110090001e5a10f8a0081d0140c7c0114850700ba0403001004130900003407036090141118001c09800c80c100b0954804905190040c00841503410540000601050160070b005850f8060742a05205140140390f54402c2d40d2008002c1c00c84c400c11020307002107141d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 69292106 1250 69290856 69290863
    0x80904090201090e040f05060711030a030902060405210c1c0618020409030305160509012015101703040e0105060c010905010204060f1107290d020d0902090f01030b01120302 76
    0x24200d0b513088000350f440d06140030701c1a5030320341c20107440ea44282070004140754030a6184004039014800a5030900340140b030240c003c1e1040e404201e0340410305000201d1192200400000e407040c003011200117240f0f50302611800c1401021885000b41c4d047d101401d8503403000400003040a500401c0000c0b86015980d04003868090004000d41c040e0425940d00103040c0c1c1500a54002d820910031484055184030081e20180700d41a078090110320010321002c0e003010400a4424001404000e0322005003844201d03240720036080f181501d80261b0034506100103d218044021640d002030b008510741820800c4412000c07405224080c46244c001840350405003081d00010700c210307072050096464070344403c409014105860220800180d91000011000c4400140c04040ba030402c81800c840b03404401200c032a4000d80d00301011290410040d0542c80342c190300c010802e405d403800c800a4581d6013881081a6140080c12201d00400302f0350041c8046002459154110b402c501007076035011a052030203a08 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 69293356 1250 69292106 69292109
    0x90106050a03180b04110405010305120715020406020f150108071802090301140714030f070804020111070807050a0b03090606010f020c130219140901030f09210e01020a08090409020109 81
    0x109280f90742c250504010344502c041e07009034494228007144005540522088820900c40030b0810780c4690310440410300b49000034225240900303c00d1080021039001201030741d05c250f00080050b441001054640c0d101445102001d00d01101040b8036540340c9031004e551b030030103805640758200340442101190044c9a04940400401600074051703400034200340c03244128216001c0c404a81440e05040303141d070040084a21036010221135203070755120018202c3e484640140101e06216402001d0f5812107000c016040051065000402d1483d0501040c07240d824081da000c02c2d0f081500780280310502d000841c41c20752003c401e180402c0d03c0c000c0e11204030300d0614440c810f590024010707425004e8101503a001040040020390303070b0b036051138402c1d001150f810005a43c1c82030040824400c0300610741c07181e0840803000d05111404110040d082c1c0300c610700144000000f040342412460202d80342c641000742d0107095002400a05149241c0383c031000c045110b0041403034451a960080d41046a00840c8680b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 69294606 1250 69293356 69293381
    0x61e1401121406010e030f03070f020d0b0f0108011d060402010804080409060b03010f080f030a03050a060315020909010e1603020c100203010f030b060406050d1b0302040c02031e0306090106050a03 86
    0x801d00320b2842041080c0c9100b501d40c1800501070118682c030130705000841c413854001a00c000c518100c2e140e181e5460401000d80b049034480510711000002c501d00035940c902580f221400c0c807055514000c151030071143c5040c0c0800058001c1c2c061601240004101c6c1c680c05a028280f0704426502d520341510b05104940010125524020010803850843c5000d503050b105070100800200f41c40d001400e070385080304484001c00354020007500b1001440f036048942c000540c100c02148554495035030000742030213003105000d1035a000c22004401e1070220140f80c010020b1200c05516414880c1444901e968041912002e1503000100e08155200401118818082900e001c41d103d58644241c1c5c2c0c5003903243e00c800d94114141d200402e0070ba250503c600800c44400034444042d2040039900c40c1140403c10035041e559515010000002d03884500401942001540c0519510b1080051982c0c1d1600b403001504030081043c41045240c1d10350401150545800e03090160319407000c04c20460107003401c0d40406 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 69295856 1250 69294606 69294611
    0x3010e060f06031e0f0906011701090803010605070b28020c160806010611160302040b01031b0e0a0807050f0d02150c21070f0b070224040204061e140112 67
    0x650709070b6240c070801c1c01d40300c0e52180c544480120781c0080c0406c0c0c0b0030f12604d4106600400820803480a20101006c1d01d600110b00214191100700541d0400d0b40b00d0004542c00082d940104000041c0c0d01e50721503090b454841115400026402d4100403400481c462035500141c0560000340800c084078019491105a10701d030303615000f00702e0b03e445003031050801081d42d10400030901a000f00e00c00e170070750020700d8607016403d203140c003004040c0081d10103490505940390f800d040700e0103500d40604540d00f8281c0780c00482c00408418030440c10100e90002c1d40c5500404020310807079460a00c0b8011482c0c04407010040c0d02154000074926059980b52a18404800141505480b00101b4072031741403290074080a000d610401031004040c480e0030310040501441c171280c2e40000328418661500328201d84101c0c2e00b03210005034004905191030300070b4250110b40f80108021840c040c0290b20141c511001c0c07510010136800d5018003101a44c0c015400c0980c0d080e00f04000c180d00c01e00070508141c140c0e4005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 69297106 1250 69295856 69295861
    0x2030c04030510020408161202010e27060f010e06120a0209030601120302010c091404090501022b0605042702010201021c020304020406050102031306210c050301151403010e060f0603 80
    0x100000e6005226071b148a010b002e0014281e50031410982044441c03d0949110200307440c2c0c0115000302c0b402d04480d900c094900280e5071180c82d1204490451540f111012100c2d0400d481008010380c841c0e02c0d07050400545281e0791034141c4031030307040d20080c284003210144503854040c038880180c001c2100d42a050b1207070303d00010380104c1941c20100c9450190b0000c002c040c2e001003045030590a00e0140d03160075200078000464904083c2d02c10400701c4d020f40001421b02e015002c03100c4134020307800c0d803180400801d03207111120301c00148242c0c8000c120803101040f20412942c061900d0144281c080d01412340543c4001c2c05690003074040f00e40c81d090722144050354001440521340250401c5d41c082e0300a5150000104465000000b100c00e64840f140000000c1860804121240614a001d10002e110091203030001200d45005000e40d031801510b60b5030300c960400c00c6040030204884c1c2544208884203001051041001040300c0c159080a0320001e681c3d81c54101040000c10a0100181c20032000000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 69298356 1250 69297106 69297133
    0x20702030f07090e240709241404060903080a11120d0b121b03120708030405210403060e010213030b01140306100e0402010c050a0b15040207031202030c040305 70
    0x120102603d190000801a00c904543c207103580c2c100d8000600c101c2244900360110b401481e80049610040c5803602c030520b6500c9094941c00c402c07400e0034480c4130100e0041082d50b401e4001c403100c0007140b021451641418608840140000800d10003d4010309000814200d0781d4819080e0000301c8c0e400340308644080016202e0f0802692080c2444c001766440d0440c100c040749050003048800d524107900070108426462040c26040c00781d62006036141c4186044a000c0d14a01c00191608138002c4100e5516031509080c181d04095104092100c440320b400e845c5c010b02d05500701964140c03500300b000000c020b00350b5541540207228483e60101601c80400c000810809c00303c1c1614103075801c00405c000615a11418550703540016a2005102804218180f00700f080b42c101c041d1b403007401494002c00c817483e552070301801c141d0181000d503601200a030403c0440c15045c1e601101d040c41c00c0d02c08515110240e1002800410009064002c15400201085914024200b90340241d60401e06641003c40f0900c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 69299606 1250 69298356 69298363
    0x60105120f0d0f09080607120515030f030a02160b03041217090c0102100c14030403031103070f020705010804120815060409050405010501051c12030f05070305090618070603050406020702030f 84
    0x10386143c00076202c0700b03000c07a40040200d0018021203050f2101146400001030320b5026003c0203009840365071201e0010081c81da402c000501c0d59680540145a940e001c61100030300381020401c60540401c2c003001c08000c4080c01000310781d40190025201032422480500c225485211380b280240703650281004d0103503155000c10f0b1020307084000d0b0200c071221110325080c0c605860030254018040390703650300941040c007904401590300500ca494002360f844416042d558950304195014030000387c0004003d0700d40ca40410504024100c01d00b060003c4d880c1c00e9507401891141940503100b04142c40011414182d19861400f0a56500900790740d161a280c15449000b000101c0b0300342da040d0300300000003d040c00c00c561010844401040301c3c10b50580543c840720505c40c0c0941680f0100741d41e407008035081c11403903c135044c02a29940d82c0443e00b4145001514580040901580c82e80c4404074200c81c240c4400007014401c40301c407800c007c141580c40e03090000007030250341e40c007a4160041418041c400c26020 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 69300856 1250 69299606 69299627
    0xa0e04050f15060303160c0f0303080109051506030c070f0206041503051302010e06070c03021302091002061504090c03020301111306030e0a02130207050f010b040c050705060105120f0d 81
    0x400031940c0d10070380b180070b03038078403800640e96903401d60010041a0110303203005c030200e0744882c012001142d06565030760036689014110f50069000400300300041c03000362003900440f500205103218662035030b160240024428030010b03041d030810460010307541c001c00441d10400300e07005070010080360316583da80300c03503900c3c54018000b1301002078540030000c0c105188205000500e6501030b501c6500340e003901001d01c038656012038406d51340003401c0040000180c0e1140743c00c4d061403d02150150b143d07401c0409000700c62406009440c03c0d90485801c0100780b140b850100c2074205030071500403c00c0c1300c50307050442c894103094001135015401d20180404812103d801482d07855400e2170892105552540c08904503480d012158a00350001d034425405032400e05400da60300204520014500a00d0b90344552904009003e80031040e511070300c200d503007468107209148142a0500b06189803800c03075070740d0a865010500426210304000e40382800211020001c00d51a01c80140403600d07041c07007640e0094943c2004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 69302106 1250 69300856 69300883
    0x7030809010e0108130308090f060403050d0b041e0b120a12020706090602030720181902070c030605040611040909050607090e0720011107140601030506010b090a0e0405 74
    0x1506070308582940300f9624144a16040d2085c0b9200c01116030b011250900044e010104504c1364848072a01d4a10600103103029910a446169031001003004090540d600c0c2c40c04a03100d641341c06440b525040410065507003042040500050760107a00b00024442c502c0300451900500c07a0b85401c0007041911400302954100640881e40f03111f680b15011122407005009036401608184188000650012175483c0e51800105441e180072203201c000c40e600c08191240d103110700143c0d0003031005661904556045032116064190b107082d98a0b220260350a00310304c00148100e076100b0014090220366849010741c891000642a5526071b22003082d40640702d80d640660341406040041848540504a400c003111644880c0c43c03202c0d5118007069074900c030a02c040c00c030f800404d090710703807050355082c410a50340324507070f010701030300c49481c2d0610a41640c6000642161903100c50010f1021600005200741190000d0b03c2460741c44604402003846640c450303000c0151903070040705000c00c0090205114101200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 69303356 1250 69302106 69302117
    0x31b0408070b04050f0303040b2508030a09030e03010606020a0311010908030903120106020a0b01050904020a0902030702030c010f0204050114180d030801030203151501110715030c0f02070320120703080901 90
    0xc40c0c01b05600c9128620506050720003c0218120803035140b80b01c2403035080500e903011203610082d1105421035000f25078031407015903602180010075811880001000d48103800812605042a130040e684803070019020b1309000c02854007000000094005541555020b003c42c0c0d20707418521505a40c03034002a1048040026042c0041201440015408001038200c070000c50145d180c0b80c14040780c0718016000780e0300610170701c0020403604918001940500342550085640d160001081421592006100c034070560041000304070981c1d200c2c1c800071a03200c0381f442065443d075220b024903600c114030a441c0c030f41001000315102c050640002d8114100d82c025415100200d00c20b588403500203208903228034080c203615103508103952095411840400004044605240c0c6a4a65120504160b40c00e8400240c851501021060f8481143e117030000c450300040280300e0840c0d072840030403c00750200c1c1c4840f40c00c20a0320f00c000c0d40e950b64000ba0094001c4207a640e141e480b030030326900c0d42c3e02c6011315501044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 69304606 1250 69303356 69303379
    0x30609020a060c17030405100e07090b010c0b010e0903040f0602161d040803060103090602040306090c0501080405060f130b0403030b010e030703030503011206021e0d0c09050303031b0408070b0405 86
    0x90042c80072243d05035005805001c0c14040d508540b0142d04040c1051364288155511040201040e10810000301101801406110700c1c2180c0c11088c7c82483e01e46a0401c5451520326001860084c102819240c001d0304a41145d0b0303031654128514003542c0e00008080f007036810009080b51b00802c4481c00510003032881410191034800b42c0d49807040102d11440c01d0044580003901207002800a0354003d90149000b083d40386543d1101010707a00250000d8400302c0c0d03581c6071a000c00c8292800f0200605c801e090280b1585425150b660300c0d40b400401c41070754018100d00140101244102c05191503034055445203107800d00d828010000d0501c07160711404a01c0c4200802000e20340068544201c2c1e80c59642c8906c0c1d0380c00c02c001c0052903900c0c5041202d502e6000e018450750a09900c002c401a0a902c4e140d05444510b400c0d00b1100340d0f405160700c032080c010405010702107030720040200da03480801a240d003c14141d040c1d155200502c84c80d400a40d0b1801640000705900c15035600510848008640c00310302c18 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 69305856 1250 69304606 69304619
    0xc0403050106090608031602190e15010c02030a0f022d03060c190c02040204090908031f150804031e0c02040b040e03091905041b0816021f02040f030609020a 69
    0x142c0c00742c0170700102caa1003030160026107181010030034000b03031024000300c5407034080324a280300c071404941215a07401101410040500041104546500303400d29160103120420740120341c483c0f208900280002810711404019503c51500b0584400a40c01c169400c090311600c01030429980c032500c013031083c09140c01103900c001c1039500355000c401400002c040001c00c0c051064030840020b000880c0c1168082c003000804220611520607624003502240d981c92800703203c0c5d8914a21030069200c00080c120b0400d0040c0e040890a6080b0001b0a040030395140d1600d04080e83d698003500b04070412a1504101181c0d202c0d40002301140c664070958041c4290149207040100f0b880400342703884040c0c0d00500c800002450007040e415030614660942400160b241c41c003240c02c0d5814211200b4840c8021006000d54640c800c1901e94440f0140c00020b06a01e4280030007074554800094509400208144a00d51094030758120f0b4001c02144414944150f5a0300d007440280250040c01c3c4d00c50003001000003a81c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 69307106 1250 69305856 69305861
    0x31c020d210b030705040e010c1205010f050f0105071506140a080c09071205161403060a03080f04051216060801080d0f031103150307090c17090c03060c040305010609 73
    0x301480011000c103592100188200402e648004a54180300d60700000803a501c89229804100701d54800120703440c108040f0141059120f11142c0610a26000040020320314188841c0155003045890104403070100004a406004401e000342c01c0c5c0742d4500401c610031a10350b001c403040381e041d918920711240e080c50801401d40e100d030cc5205056049000265001c0c9011813a181d400901c60401400d040c0140300118110380c0111240703039400c59501c40c0c01c800c5a07004401d0501c02d89001d449240b0f10310b84030700410544066840010010580402e01c06862400b6500f9140680300280401034680a40780301c0654500382c40c00d4a105544004802041c4144241500d41c181ca40103030040480307418038001141d4502507a81c0001c105651144101a00302450008601510f104002c0a40340071400d02098204030b8264032111200b498064107812603600039500d01c00041c54111146055030303d10030414140030404102580c140101c40402c140418114040d02c10f03a0700a500812909440300700c071004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 69308356 1250 69307106 69307127
    0xa02060609060307030b0405160f06051204080c0d0201060e0a0509150a090606081011180d020d02030109050607030e0a0b06090a060503030a0201020406110705090c0a020705031c020d 80
    0x68012400103589810724075000d541000010b003c4032101d80e41ca480d8402c820348280c1d42210300e81c11480c8480c50f613030280d240c800060010450580c1e41240781c104003800034460000399480f04a10040090144100c0b00c09841e04080c1110030707100101c0e00510002d0080c0785074040d5a14048404010460101043c40b41a1190b00c41c00018130f540c41140f46c50240c5082e00411700e4013229100c0c0e0b80c0c5400215103015076401450700300e00604c840164001c15000703803586820058a41101440581142c10184d8089030b40404180c500c49040c0101d0300200f40c080c00c2841000e509507080c01c4d5120208103001858a1088966030b40c2085082402e0301c4d01a00e0700d9943e03002421009550000c10350610b401414190004002000060390560360f001003400e582080c01710303c01503540802c0402219030401020507110f0f50790310103030151034240000140107000c09002030641d000d001c640340b85058006c104082c0907050040032250031069091b01c4c41c5030021051442d00050003424111020b0a014826828 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 69309606 1250 69308356 69308377
    0x602071e050607141b010219050705040e070e0f221205090105090901080601090e070b160804181e090506070e01090509010906291e120a060603050705 66
    0x40c8864a044100201604034440039584d003040d2000d142001c4208101c43c0d10f160b0f03a030741e114004202c195800a03080c141403026611003840000c2d0f0010000e14041506016100215000581700b001880464500311080c0c2081724a00b0340001485aa180200ca4141c410b03082d400a145141040e640141d04803100034000800103014151003030034407400b0300041c026010044c500582803800450004a40400c2a40880015040540140b11050b9180520302c4580081801000000d16000f0480c1c00c0b80304000c130307100e060f191140d007510401414004540c0103000342e81c00d0230040c2042070131000080c41000700510032480c03031101106d51006c8a0084071140341d0880c002e002e16540d881803d4904510350f002c2a4100b2203244400b150941c0c6001c1d25501a02035014001401403c0010764102401c0580b0340e080c803810102d58030724203111250202d070003c1d40c092160403550040c0300540380d568040c80e80c12680702201030f4100440c412969000750201c914a54060000d6101c0c0b400950305c07442400360a4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 69310856 1250 69309606 69309659
    0xa06140301050108131a0405010e010b0d080a050f1201181109040b040b03070801050a05060a030203030a030e0705040f0902101d0402090d02030105100603050708010521071e060207 79
    0x10010303580940c01d13a0350b11060031601c1e0006000d0a540b188103a0060300e404d907094030284003c1c001440824811000e40100c2700c0e000f0007512500c1d90002d0020101d1810051080d0380010b070320380c41c030340c415030903146189041c840903a15024038004100d0500c0c024051880c0740c030744150801c000070146000715020f96464581282ca0100040240009801c507126181c2e049a252a4441900d40f0200003070002890220000101810000001000e4800c090705180c4151460103051001d60f50101c11209204600d081c00103140b9200403c07603003860000d070301c01a807040c500b007211180c0314503c1d08402103992089406141c0e0b5001910250350015120324100250654400760003442e05242d401004e001030014580220642c040e4006805c7d074a040f14001c00d6809070110421003140c2500450f40c0019250500700841d605100108194102c0a100051a091458106c0c501a40248109800703002c0700102140b85826034141d41e00c450b031103807003141d005104c0e10341d000074901d200e1031003510031140b41c0358030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 69312106 1250 69310856 69310859
    0x304030b0a0203040501140c1c0e0303010e10090c0507210228050604060605090f07080403050d0902101809020403050c010c0c170105100602010b2d040204090b0a06140301 75
    0x128000f9040104212150365a0b5504084050201c03440c1038450444245215502c060780c000e809901180150115107141c10004680c0301d039070001c4281c0303056610148000942c1d239502030056a419640e070380721180b454517010390000c5031a40800280b0f03078580a9440607000c1d048640112441405046000b00142c00071204c546a2070300704402d000307a40d1a010360313005829600d529080c0c2004002d540881c0c40640c3c0d041c08115504105c8900c030b03880003003e000480c141c40d010304043c00c4480020002010000e00182d40c1d144080a54480002c081d00542864203001620780058030400b8500c1c80440c40c1010384d07a0014920402d0300881e01560b510001416256910900546900c41215030860f40108045404140c18031071000c0c4115040c0c420002040c1800e00b1340120034620059007080c421641401180a83c9450359100d10700300120b154413809802ea0001a150301d8002c080c21103a50160000030001074021194203d0044110111440080c1c55540c9806139000d0f68034113200e4845007000d000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 69313356 1250 69312106 69312121
    0x31a061207050a0323090727020715020307030902010305060d050c120f0f0705090105010e0915010e040c0809060907060801030314090d0b040b18070e0402120106061e020304030b 78
    0x580b481c03815505000c03c0c0417680d024506000d40308803140d0162422940d04020040c842000740390000c0c505103000e034a50f0211102c0c0414900d01200c0c001450795000124141003081c1c48082500e0000304181c11034590030641002409040241801e80c000f1f0305050120366513181114001149a611600501c24010450288043c686080007500101d008d800d01c2680840001e0002d92a2203011002600700c050030841000703217025068101e40e041084031103282c2016151268130075009044071812400000703101004032003405c5500b48980d0090f050103040070405030044d9070f880c01410400142c9800390303120602585d8032440740c07290a001500c500d004102007800f6040e00102910342400251520b821200455107000088004a0b10120786204001c18860841c201a802100300300715402540b482d1502595540000e000c3c568041c18480c003c2800c44d510700000a042003108402400501e0ba5114003510301d01054124600300b03030981141e04c0800c1e1004c021603040d650711191048071501e0303110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 69314606 1250 69313356 69313367
    0x90302041802030d0f1403160309050c0402040b040e1308030c070318030b0115030501050102030405130902090c1c02030601080403030b030a050a050c0102071706010e0421031a061207 80
    0x3108180c400c19101c5500c000740c1c07404d101403c04541d0684615a0f10b105800b0b000b800700350210b400fa10441e00030b00070f0081b0759002100220900c03925140c080b070f418595052450810301c003014011341c0701d0f2002900103180c100301d00240040301c514001c07060956441c1841c03400e6409000b0002440c01c0c00070000900c0c4110703081d02a000050091414130440702022882d107240c110b03030f5041503a040c44044010805606654114110040545024000d55152400103981c900541c081c06200350030001c1101d04000f10f95001107180d85d001000da04503030402c10844d5651303a000720b902100080b001d1640d230f01d20403514001c0724000c1c00180d4030307074041381d0301c6480840c002c1c280992895414054030114001240e41003041600d024020809402549000300c00a458001c8a9002c0380c1e10350030000304805064004a02641100c44e21f0001d21020381e00c5140410448806c20060075840c1040c0b4804048281e043d480050b0048079800f010b22001c2c03025042201a0043e9200304070403081d0000061040c40c8101c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 69315856 1250 69314606 69314621
    0xb040602070804080607020102070b061f270b0405011103130e0c040b0a1806110a060b030c031207020a06080f370516091a09031023060405060109030204 67
    0x140c542d1401e15841d0340c40c0c130381010360945d24840107070b4011034140c05000e804001140c220008035440b0500a9070b0064507000400700c01001014050a010322150385900d0b0310440480500c06000b040744c440d26400f8040b02d540140c0666400111040010004280c0000854031b403402c580903181c0010703240c00d900301e0030340c1c50081003ca60804103110006501c107051000c9e0110245d1601c07a60920302000741e40c80d48540c003603800303441005400301c29444e6203036002c01e103e04043e070000004260b9240711008207141c44c200d911140e405114041c0e00140f088468000303001b10340c0c0b00702e0b2041700640c0d880008650f0b1490654804580080c003001281040b445208505056248800c840b07070404090800124038000c01030300400b48940341c800700b00d80d0b0300f20802d02c26503521090628816030350401885c821701490940700500040000079143d90181c0d800c02501082d20515201401100c032a40703801d16480075070444810824080001140183c030301401a130703205060603512101c49034a1902000051300c1c00f0b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 69317106 1250 69315856 69315863
    0x80d060b040513020a020c0405040609020f040b06180a0b0309060405010b01030506060d240b040603050a05070f0809030d1b020c010905010806130209120d020f01020a080606030403050c07060f0e09040b04060207 92
    0x481f002d2032a15100d1f4090103210368000c1c14001203401f0300d8010f0120000d200d000845c4140c0c40e02c18442c00b143d03602c40c2500c0c1c00741c55040100303440c00650341c00b05441c59996045403664a00110400003400b40c0080c559218030302c240c00910641120710b0041d026510103030b6041f03a00030740034010410524010390011010101c600e41a00222b400c075114001c52114a8101010741100018144152a01801219045800307101c0802c90b9103000c640081c4000c010a40981c100301c0400c003ca503486e070040083d908040f030182400c1201c100a080d4003500e010f8056000300240c040d42c034070512998050f424010855806031900a819500c460800144040081c0240d085941c01d003e00c81260304c414408503d1a0b0038200103106a41c88003401038a0184c41000410b00ca0307004000c00301510b503018400c035401c0074043d10615100d4965180c15211806004089036541c413440d400010401c0e84102e00c03244414050303c8084202d004c11062080041c2e0440d0003501650b010300c08180094030940c000d01001d0302 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 69318356 1250 69317106 69317113
    0x2c010c0f0f030b10030e010605030303060a030602030c0f13030215120a020307031d06010812180f01030f0515010806030307170d0e030c0706030513030c030f0219080d060b040513020a02 81
    0x1c1d00300065040701c5044d640740000c1d0b500d50012100400911401d805000100d000714218074020000a402c4e069500004210781d802102044500080109964a0b546074030010b50310b41c006811000f510203054441a80304000e41403610b20054032203400c4501c0c6203c81c001e840a15a1540c092202035400a030004080542e5a00552804071500210388041040c2002030141c0b0b5240c40c042c02c0c0f0700000c29800c2640001c04006c200301140401701e840b007020a081e100790401c03412100040c1c00500c03043d4140c10710242480c0c200107440603c9050012400400d0300c4031030194030f601c01495900c1c050200c008100b08541303041140000a000064040040c41c19808500000094010342c10341c0c0044001d000d00f640034a4003406515018000d140d803020904c003030040e0f040415140240381d0410944050280004201103944452090040702400c0c0245401402504400c6c500b5288541c0aa427807881414580a00821900f512804540032101c00400f61421103c24051680c000d6004103070751001d520 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 69319606 1250 69318356 69318371
    0x406020c15010315051f290f040603090c05090412030c020105090c0d1104111305010309030e010e04060f060e1f0207060513090507050705010c140a030e0a062c010c0f0f03 75
    0x30865601d110250512503407c90341c3c01c1c1032122000b00070313103c40c0e80e0100ca8401401080c0200d00e040d0140d6003124207502e80071800004900700040442540e130007080d000100700013000180041080040030b0b0790b6a40d501000003c0120404071300321401522110034541020320900550721700a000040900c0c0580d031b00c4156140030900040858481c2003d549a811001c04d96441c107400f00054940100002c2c01c0c144100c8455507001403840100011580c1481001100d0302005c0e00c840d0f204c18040c09800c2412080941c40740806006100c400502500ca40e501d0006c41d8841d074024811284c0d808082d400801045040000954040d000440c80c3c01080c0321410300000c10420394010280966810b486003540c810b2213003002801d50b6a8030507000305100d01244520601c02e020000c4804000ba64900010700c00c440e120300609183c070b00c4c00c001c2c20b041e0030580c4403807404031115085010b400050000788210081900101d00303903010460840e000c1940c854980c80624080d04050064104030300c2e0006007603 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 69320856 1250 69319606 69319651
    0xc150201020d0203040302010b0a0617010b18030106080c130b10050304020d1b0311010c0302060a02030a181a0610050702010806060409050907050a080c091504020702090406020c1501031505 83
    0x2071300700700ea0580050b9182c00d03010302907050814610010340400e180850085c0c41e50b03002c000c1000300c103226096400100003969058440d56030001000040028000c0c420320f983c4400c0c0e01d40e10416003035180d2184000c0d005035003e0750054451400c2c400c0c009005070040d4441c2010a9071582c01c0200180d03003003024a5041400250b4507812501a6101e0309507900c8028254241803103c2d000d45020030b81072280c0070011501094000541da54084c13820720015035660344225800d0040c00822000c10f82d08000e0a4030482085002d41d0b1114240c1407210306055196034281c10403103d900d680c0044808070394100842000b652145414590201c406840310b1300d040c0d0394400300700440d00b0403038082002c3d0300030800520031880c10110035401080740344028141c0503007a100261082c40c0240140710a001411010303000d50701c4a80503601c03195001040c081c003514040c0be01001961110171080c6050080c0410901d80348240800b0b1410b980d00070014151121540d148000106400303481c030a0000c6a845524401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 69322106 1250 69320856 69320861
    0x14031005090a020406090603020a201207060e100213092003011401020111040602151306060807080c010903030c0803040f0c0b090108011410140909011211030a0c150201020d 76
    0x903101800b001a5100e28010009114508a4010707208150042041d8280b40341d000c41c2030010012814410099a040540340e545801d010100a01600c4404a10303882408020341c00074981e152154183c4843c0b035a0b01c40910201c1c03050705000340304000000d2080c011810b65034014151045100c01d080000180d00c102c0280c00d400990207004a51100f003400b4145582c28000c40c88a1070041d59454105410204069100d0265680360301e00007020500045a02454a4181006e41e40204d01048401e032075440e144d849003000e0040a41c42c2c03040f48103101095104411f07840c21290160796400090740180c5d10b5441c2540050000e44103001140d0b400300100d2500030b040d6008108984910341d90303800100c005410040140c0c04083e040704580c101c4025515012055248507025103810169070f980c02c1e0400d00c11b40111029160170500c1c1000104070580c00b8101110910b0007a60700c280402c1260042542d45d08015400502080b0b60040410904002889000d407404642c0000341c205480d01c1c1c0d01504 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 69323356 1250 69322106 69322111
    0xe041e080d0b01021006030c05060703030213080f06090601060509011409040f06061106040512160f0c0306050a0e0c01050f04030503030f061f0c080315060a1205161403100509 77
    0x1125580e0300700300020360701000003991100c5c2d000010b0100e1851611019000c0b40c00744502401110001107130401c243c03180d0704450101000345011400301d501e43d5a41e0340e5650004c0c40214442c4140004152540e1000816904803625680c901d483c1c0040e0a00450b00302440e8200740401c40c2060206d0351460351a03010780f849900360040001040d51038668000d01c1d089000202e0f84240c0c0152040c04041400801c1c1070040c1d48004505a40d03450071126100251702c80a0405407010840d44060400c00004200420460380200310603c01b03626540c680000722184850070b0300050380450190b8100b94040d1000e4110001421005410b05540707884890441e4821541d5440040c511020440586403540500001c6404000522030100d104440a48032420400b800780c020ad4000c4002091b608032401402c00c1c3c4103004e01003c4e1240341d1034602070411003111000c40b080f40d041000041c0c0c40d640c04080045020045d50355001a041c10300c50030322041d0700c0903103441c0b00a0f003200300106130394849454560 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 69324606 1250 69323356 69323377
    0x30f090e07170c07080301090903051e030411042304080c010f0b10090f14031e0d0e03010506010c0303050a020903010c0f0908070302220b031605040509070e041e08 72
    0x2040000c0c03030030b80401c0c01000100300c84440740b02880600007140404040c2c0c0d0641e0380f050000141c188040c2016101402210000007405c0ba991036020000742d0381c10055409144510040102071040c442040700f60350800907140d01345031041c00c0d0143c80484000050750054002d00c0014a05102e0300e030420300b9102c1d500071980d00d080c0c5444080c00c80d420064610142c52a003858500c1c143c40c1042c000d4280c0203018410803080704840b5201403a650f90074000103902c05000142100000c240340d01164542d10010584404550f20390640011820103019491290390705130740307615490f00981d40580007004042c0401144d20782c2482250703042c1d2001d11178450f82c03e410b92140c0c02d0390022198000e0044400350841002600409820070060f150f401001d418001a2601c1d104641550708014005005814511341c2c03610495404840304543c2414034010b031881601c0900540d030711382981a584401a1040c0071001c1c10740d800003804540300301d41540a81c03c144000c02403014840e1100e0405400031403069 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 69325856 1250 69324606 69324617
    0x50d09050310020f04050904030201022118010c05090d060608070e06090717042003010c030203160c15020304050f070315270303020904060b03010e040c120f030f090e07 74
    0xd00c180e150400020400105000c03040d0b242c116050407628844c00f4a20803203000b60200004581018001e4042c1c0c1d801240308a0403000c00000c0a00c1643e14080540341d207241c215100402003500c0030180101c240d040b210740c940701e181403005014400d2229006005403100d907902c8201103a400c0c4107101c640d00600245d21800341c02d051500803c00f15403805000c5d1002d01c0801c98890801c0b002e0420310650058000e205651314840224000b04440307008041139038194600603006003101e80660195014000c0c15062400c0e50340100760940303203020b000001405091a101e8183d412101603002950b22500c80c105540040041650f0649400141d81041360102d0590005501001c00c51081100b00c880c3d2088100b80d4289010b141c5c02c100c58008400b400301600020b6007071141d200c0d03400c4800208035401c0309030f582c0d69640071030094031503095504607020000304c000082d528035054402d080740c60700000095249500340e50f050300c8035601184146c0c280501030400040e43d84d0b100603a24850102c607200c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 69327106 1250 69325856 69325859
    0x1180b040806090d081501050304030c1a0702120a0503041106070f03080402311109120705030115180b13050708070801060915030203180a0309081014060f010309050d09 74
    0x102c030b0400440c40803084c100130355031341044032250542200c8010000c0a09000d0fa40b07480d10b003000c50b0040b510242c0506414100303c40703041c00b500c883c40102d21661203a07090b41c01c00c880e01c00c4945800d1251503400741c00038000744040307800314001c81c1528407a1700000709044d20704242c65031242a901c54040050740810841c40820040d030400080080b5002d084050040c248401d1003510168500c14041d000ca07140c4d561600c0102c1f03048000708840c45400003d0001d4144030030700b80e41c20707902c0550b1300a5a00079400c0214401c1041540c0c8601c0043d2500c0420320880144102c10303540040c56802d46041d40000346002c030700f008840700d10403103006200a680b6091585020f900c041c02001041c2c0c0444100211300c00200300c0c801e40e1801342c100e01c41d02460302507944e86178910003540c4403d003200107241c1c03805903e030382c9010150861800011202008155035046640c00c003a441100c3c400c4000e01d025442c40030010b42d051074503210414280c02c05040001e8005c00a84030b031458600112a45801303e41362000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 69328356 1250 69327106 69327121
    0x1061103070209281e0608060c040302100306030609080903060601020606060d0b040b2110020c100509010212090709061403030406030903020a050a06050709050607020a0501180b040806 81
    0x40440a80005008514000c1280d02041d0012001800e1102d11800d03440c0c145800c10b02d4100070240c203402c072582808a003030300c070281d04542c801540d001843c461030107000041e03002c0c1c081801da1144010900c080e0170149503400344010118400010340c205940c42001100180d8140300d0340010364041d40c0819168080c1c05e0916140c03280c05070400d815580b14004010380d035034450040f54080d124400e0003048041c80340d80481e0107811600105588400c004604c3c0b80964010708681001547c1c0800300c03540f00e5000d0003440101c2c802c1c44611a181e41208940c00810340045c1c00541d04601c0c100300041c542445046502c2c05051300303a030a01d40c290080390040240300071a02518002c0d04070701c000d00f0800e10400c40000c0d0790303100754032450041c542c88040301c0741031500038010881800d8010080e511003000030300e404001424119100404218000d9010580f400e0080680b201d0301c1c0c1c0a08100e6405003001d00544441814011080820300400808141c0d020390401a0005188407401021542407c82 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 69329606 1250 69328356 69328367
    0xc040b041401110109240209060c0303090d0f0f030203070e0303031005010f030b011b0c05060d050f010e06030a17090301020408010504020307121a0406090605180f0304060f0503090a050f03030106 86
    0x2204000f2581c10140c16001280f100c640e0030701c140c001500040414900340d103850010b4003420340c4c5242d01c498007081f0b400038000088011445200001c00341e9005040381402070351011001e941d26800110402d186494450007603004540204050404101100c00a80042d107154001c075407131840341c81100800c0000d942c00c010509505891810240074154400c1e000800701c2d176241c3d01460061051403201028403080c03e54100c05040701802d0207580d40c4a07281c9510203007a098411201d1810b41c0300002880c0880741d00241c2c040c80004001e8004103515840e85110070788030040300012a001004829440d9409100400c02000c103c000440c035403a05004241c00c2c5031240d0300030078000312800c40881c001a06a08601c100c40300c4195100f03602e4442f030500e50001c00c030703403c001404a441e01c000e110401843e0b8481d03001d84000d220450b014100280c856a80340d00031031203290040ba0009500300b503160f01507000b5541c0448031800f01d901b50f04554407002e14120007090854665000080180446a03000c07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 69330856 1250 69329606 69329627
    0x40c050a02010501080f0a02010e0f06030709030c080a031e020c030f0a05060c040506040506031329090a0803010909110a060e10030c0903060506040b09041515030c0b030c040b041401 80
    0x320142c00141034039403910387ca40c2941400241080b403aa500d038881c65071207400e002a682400f030700e213541780e20303120f04040d0404215000566100e522120005110322000502c0c0b0440b0f84d040d03032400c8107405007401d01c2501103d00c140490a500480654103841d440030016103c11290180003803075204800c0c20301da401d1a070064042070301c0000c00c020070f01043c0c45a100711401c0700c0003980c0882e0b4954881c135410140120003a4010305c60808040c00c1e403030b01d40d8403c25100342940d00c0100d0030025280c030940c10b996254620402007500c0d4050004001400c065448804024010102400b003c88504d000030f00034401130704100003191a1054020b01800c0000d0803c080c054503003401c1000521100c0042d02860032440000c0019460324005211030303c0e41e8001c02d517400c00140441c2c0f40b1b030411746000340c609600000d003e40c1e0b080c40c0103045200115a8a64082141e42241c011200c031824001c00b074150b580010655441000c040000092126107640103100800408044440d2100101e00062000300340 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 69332106 1250 69330856 69330869
    0x10501030803040807050f06090d0801060c02010c11030a02030624030303010f09050c0f1801080703110d2a020114010501110d0c030216140a05041e05070e040c050a02010501 76
    0x40000500004280c07108603500035800c520810345601c0c079441e0483c60210101100e00c01c6000317190520403034210004403940400165180d44200d0303a00c8000498039050f4000d800384c0002c0d012501d200200762099070002c2801c00240588004243c1038001c00c2c90404282c0f454550b8003114400e42901c01034007603484902c1385044019603e1940b40200040c2c40304078900556513115074034000300b16040100300c04c40c1c507d0212215640d0719002060010b40089902e055001e01042d045000135103664801d203c0c0c05d41040c0c4900d8198103001e10003040c08000c204201c902c1890400d9180070700450003201c83c00d62109545a80040b030400d03500380f110070388180b060b80014184010305c0d14034180f102020a2240607401540750802841142e030404a01c0c1412184a00c1d824910801010510151155a001320444295004c0e01c3c007035130b039a00b071004a0310b807640380b03400b80b0614080c480c0c00c12031325400194008001d491302c04043d12501000a08403440880c103a8080f40c400507421004d5502806041e004202 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 69333356 1250 69332106 69332111
    0x402040905121c060b07030819061a03070801090516030e0a0b040506010f0b0f04091e02030106020706020f030a021507030905010204060809060708010501020601140103020d14040318080d1d041a0a0801 88
    0x6440c1c4c0c010384023450180c0700a901c00140c1501c013045003140c0e4410001000c40e00f41c001c1d4400002030044419920581e820b0340026006000400c1924050046034020403803006c0c10110385c640514210024210703600030784028024140104081b8001e5400303d030041c1e005001420035945010260038040900754844602443c0500c6a0310b0411000c0060380c04458496402107841d03150740c9040c1c0d107441c05900342e0040071840400085242580001e007081503421540842d0020300241b1100d07a500c0c0626880480107074031920003000340103030114006410007a5400c01003010b00e51a5142401d9030000d0700003c0025154104101c9819810452660001c2150034011002e506280000b920b030350050080750b2240800c6840314074140d10a6049030380e1200d89078000c00c40d204c904c00400910070010740d420b07400281328803440c4a1000c00c0084200440d90800f0003003c8840c1c00c50402c2e41d8003c1040740c0f41d600010b081c5d501c81e040d500ca034021106141e8101c01035101000008080080000c095045907070142c3c0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 69334606 1250 69333356 69333367
    0x706031b0f0903021c06090309050118080d140c010c050d0b1804170c01020309010c020c06040f06030c14070c061e0c06090206070f0b04061d03030402040905121c060b 73
    0x1a004050b0b034041e60780696000b4aa0301046116840031001040001d00440c5041c6070f00041c160f00440290a6440c242c0e61054503503120305503c01c845806020f00607440d00013020210410740100b1014060005140d01ba0341080c030040103090071900d0720f94102d008603000103040c0c0e00381c003410303c1403041e103840803520f00004240105820079038010080c00249a200c1d01942c0c440e170000b0342401d40d80001c041000039940c81c545000e031940a0400ca40d070110252050311100d895510f4044103440641d07800c459418003603031406a080f4054560b02d003814090140700c07900c12004240000040c40c00c0381c024100c84000d01d1501d030000700080ca100c00300c0c0d40304400c500c911b5840140e000080034101078110a000c101c5010b02d000048a51241b00401041201ca02c04004204507940c0c000d50310403400347d14200048044920800511020701580003800e8100300700080052802c0d41c850f08207940600e088896501000840b4045a4402502c001c9400011000103030918424001c1c01c1c0508052404541002d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 69335856 1250 69334606 69334637
    0xe0609071a0c1e010f0204140a090203060105030f060f0d050309010f0e0d0303021305030f0604030339091e03060608011b050304060902060403080d0c020105010b0301060f0207080706031b 82
    0xf440d00350071214012841c2400280c11040940000340350107400d5008560712961044a1941501802c001d14024600d045000502c0002c3c0d1098030b214400c1a141da9103940d4900c0d48035006110018412684080c81582c0305260340c80d00c0000e164480d128600840e2341d0460040090b04a0307072039101203010003040c2c0c035410032288c82c0d264011642035031504025840d0964221501580000c5810241d01131060401d82c41d100400000c003980564002d49082160000c1c40491055091400d8102e62581a40c40b00798a820200c19210300d400d4a064507006080c99140c00100030041503c114196000c0e1131400d043c01441040d21807580242141d0008011141c900080d424030f0441034620f5400340003000c0300190030f02c032154014001e80c40e4002c00c129610343c0c80b803400c6445c0d90002800e40c03000514014604011500510465061f2000d0900403800c40c5e1810804031640b000341002041140240c880014218204000c4440604455280410f203040b01d50407088810070110a20010009003204840c0b40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 69337106 1250 69335856 69335863
    0xa0203030a05090f18010f0f050a1503020c2b021501050904020120010501181415010201020c070314010e03040b030610031e09050105090102070b06060702040e0609071a0c 75
    0x5110281042901c442c1650001600030300b0f06220540c0050f88540d82d0780160170740d040414140e030b80c0e18031003015543d140c8400c014110418016260403900c6100c081c844400549503110400c45685809171420508509140c20b103a8250822030110030640c4080000c0042c0200c1454038050703a1005200d004500620a6828141032240038002c81c0d00c1d1020070250391007011121408010740c0d03c1b0314041940b4081c2d186c0244001d1060301c40030050219800c0b800c40c642c1c0105e819007034a0b05210041d941390105088610a040600a8195982000071540f000700a01060000358029000402c040030350554143c2550034940108401780c2041001f030120005240550f0b0700800d05681300d503c5040c50020a5000303013150400146100d85c0b0200841041040e5000b006480b881040244a152900d01d0401c0c240d01030784200034010b441c07410002d21942400009445800c2c0014008030761044a4664107040034001d54480d00c45812050087c451590a0320b080b05005480c008140d141c035022050003070300c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 69338356 1250 69337106 69337117
    0x50106032a1403071e1a0a020c0103051f06031a030105070c0f0203011103130c2304020903031201170f070b070b041502040602030a0801080303010608040b04030903050d03050702010b030a020303 85
    0xd040489858000b842e483c108090005007040c0c03011500c09203000c19244402c14058411040303040140c1c62900340c1007403490141d13030350725509400501c0a00351210054000d00001841c90603400e111903c40031801c11000380b4000248515100000e0302e05141c0310075558280d110021600903030400c0e080c0941241d004404602442d00503e054003114900c1c80000e0141449030345180c41c108001c018030a6403401c3e0010140c13224481c565040005039203402108601d4024400c05512591442d4540c4a13414150024035240b040142074031f140c4540c1c03801c0040203d100b82c00118100c0c0b8848ac00c40c000c1481000008600f4442c5c1000f030001e24504880340d4007901c65014028a010b40900106040101c19080c00c81d0f03104c0c00800a544646d10703808029500d4000314040030010b2141ca00001d00c80d035000c01101e05891035969050f03441d41e10b0b5110004040d002030800c074100180c40e40008042082170048609610455402144c182041c2034000e003952010340c1043e220ba040148110010f036400011a075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 69339606 1250 69338356 69338369
    0xb040501210f0b07090512070803030106180e0c0301030201080a09020f10021006180c030b060703030e150a0218090f0613060e0907030501050c0309030f13050d050106032a 75
    0x1194a8910b441c0c007020080c8030004203142c0c00700090008054106403c030081c0e03038081c0c40d99500b0070900c500f140e079507220038810340c030441d00b0400040c4405442005951018000e62141302c2c3c0050303440043d0300c3c203440201d0b400c0e40540400f0006004642c1e010f0a041e810141e114070900c0541141d4000070f541e070701c00503080c520424680c95000c42060003440724292442450303908010040c2e6522024003413608445410b0b00c2030f880c009440b045203020f4404d6103401000a404a8104142030b90305034010b0040425040040c800d0780c03c0380c1a0400807020301441030b0114075000da11034101d800184503181105603020712916140f0100b00022040003126540000101c40e00c40190b418100610000c04040c3c00c40c2c16150103080c1041b850707200010314001220b200314000c002690b02c4013940e030014003007a03038400368a800401c040440170301070401030160034503441c0700500d8943c1d80d0000103181c0032003441d0172a226515040304000740111859840381c85a1418105500d07034252140c60210403501e80603c0c2c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 69340856 1250 69339606 69339659
    0x13005010b090c250c05030a0605040201110d0801030807321c0f030b0a090f0203150d0308010e0705121302040c090506040302040504060906020f1b030406210b0303041202040b040501 80
    0x17448222000b007801020041c1c1034407020000c0d410080e0180100711400c2c0c3c0070996016100c1e0a07038400154804482d00c056942c16a26429a0759801c2540d02c0b4403425546082c100c09940040d502c640e5521100310b00035001c9045e219103c40300c41d400c1c40c4941c01798500390703510769206d1a4565000100907506040741c0c035000640d10001d000040003c10389801c401c0c0c06034506103040080d49400d5000f540540100070f422105a1020750410a0b2074009000050000c0c0200b0010014461400c080540100700b50822071309041d90100c00c4040311320215070349015400c45c40031180070743c103140c840c9008240051070301c820b00f00d080c58040303000c2d0710030f510009000e25614400101400380c503500c01d51034940d00402c2036645d98044100c11410790089400c50f4214041002c080d0f022090000c111021100d864490040e443c6614410290008025060000b560b403259500021071350b0a1000700064603921000b0070a101d01c070b00500040341e00c0e000c091400340f460040103000310b840c0c03116a10f5084002080c03d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 69342106 1250 69340856 69340927
    0x7060c08031519090c0e0909070e040606051e10031401120812040803010518190902031f06080c030703020d020d032303040201030e0312013005010b090c 67
    0x450384a07291a9220a07000c070007a003010412004582003030001e00c80544c0d40e41b82421064081201c184425500c1e105554083c540810514035951a0580d002c0c4c09440700003500c5071340342d020410111042d42c0c002e000c0303604442449030380d01c1c00306e00c2001182c1417442c0c1085021400d14007144150010f01035502d114800f14072510400c003001c021900c18201c03d00340d81f10b1f241445c0c074180c1d105420a00400788143c0d800c5c0c2408000034149180c0e20710918084100030609011401c940e0001d1040e0401a40c040c081c4401c09400301102804003103001381c0d82034000424038606900c0c541050708000071544240c01003081000580d03a003940022034150115030600d10700c0043d15054a120a43c41846800991003105050840d01082d000c2c42c8100c0c004e880512002c0b9032a256280c50344101006041c0114409005011184400b404440c840c5240c040d0141c0c00507501240c0589020307034003400c44d0540e44030b400d01d00582c2070400c4c0d81504201d0020300207051140328050a8404180006550452503c8007103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 69343356 1250 69342106 69342109
    0xe06030a090503041712070b190f0e0d0e0307051f05130303020c040501060906081801020d022d0702030304060516020406081b0a080c040f020c010510030507060c080315 74
    0x411510190b120040f030359a1035450301000f80c250500e034903c1c9054016806500b080540072000c8690540d40158181d8540e034031203901c044900303540c2000ca003560303944400e004100c228606c0f40303243c404d01c0c050081410035060310004001144480d9054002e8108620410054841076000303c071804000504600d10300c1c14003012152402114040d00c02d40000820000901d07801103505590312350107550502141c0e032540c070140e039100c41d1841040700081008d07000510782d0107100e4030304145001c48000549400020103100050f41c00004001c0c20352030300541c1015000039440d100000c4140d881110a080c901741b031300040c0d00c900031440340034140800081c003400d24015150040f501d445d4002d00822401d40c45034070381c07951401804a6039070490740e45960b0103007501e0690b1892044031000c50050050380c603160302b4040580036081e44400c0f502e8007404001140c2d4028010103105550080c040c1000910f1810040e1401c4071075031200c03040c49051506c03180410304000451382d111110321401c0e040c0c0d488020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 69344606 1250 69343356 69343361
    0xf0b01090c0509012a030512010801020315010e0f0406270603030f050c240a05060f101202040e040f0b01060c1101080618090102040906060e030d03050c0d09030e01031b0e06030a 78
    0xb08410020207001740104101500800603017621590565074251030707a281c041302401c0384413703651040d44100d5810078284541c402c0c0b011002c082c2001d098a44403c030703042c0100d07041e280070b5000f41107801070184000140340c690451040c0d15800040e420f0241c9032071910701501a41c000c00001d000c00c0000103031440145400c1222000304003075521302c09003104071858402160f003410340c1d40c4d144050414000c2042e510304040c000c9881c010007002e240034640c0d0000150f07445100405000c001c10780a01c00024406c003e00641c52250340100c500d200c0c05042c03481d2441c0c801d841600300c0403d11041c0c074410004110941240380c41c2c403200782011f040c50785075440024541e040300e0315188141c44038101000480003064014104a0740120300502109403240c0c000c0d141c42200d40c204a40541c010350891858503c00d40200d908401448425498540301c1b15a840680d803e8880640108144100c61091960705202d03a440c11446908403140d1200b0b108030080c9468441e0424610402e808408074500c0b4000b503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 69345856 1250 69344606 69344657
    0xe03090a0608220503030f060d0209071218050304050f01021609110702030a0c23090c03060f0604090209010905040203090d031a030d080105030606060307201204030f0b01090c050901 80
    0x815204943c8182440e010b0354070392003220076406000d0400c020901d2810407603040700400303a00a0103104113a4440074200c03070414864212040b842d032541280c001d81d030b26610514065034005e101550b035075820a41480b010001c041c90850440d804400d03260b45800060641c402a80c14016010501403420754140016006100000c0e62500400403180c080000703201080c021262070f0a018014581544422000440305464168200e60900c00103428000203030000d41d4400300081510308078406c44400b18180303400a030801c031020f540c000ac108a40e5a001850306008003012181940f640c580100c0490b118418070400105058448095641c10451550f100482000240c00c0f00c0200ea0f4006000304115828803a107406802501c001c101c01e802c0070003c8900c50b44017626619800204d10310014001040788400903114003a0b50440014421050000d000450050404503038502a5081c0324041d0350040c1c6c00f1a07402480c020f0440440c070b81150588000c0ea40074201105442e10740e40f4034817006e2018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 69347106 1250 69345856 69345901
    0xe190216060c26010b0a0e0a0b0309100b0409030c0b04020109180207021305070e120309180106030e01140c090a0905040609030f020706080c090d0606080304090e03090a0608 76
    0x10040c01d007030b1069102e0f044004918210501664002c0f58940c648140fa02c00c0c003d08659080c10071031200000d0060004034001e0a01401da04162035594024000e550400d4891072170503001300307070044460072041c0074007806e004040343d00b003207010342d95500507050300e080e80c5000340b90586882c0000e003076a00400b40d150080500148910405525007200e41c000e62100004030b11410b005081003031300203154895a44645402d8845400222080003080104880d0009002482c4000c004031000c0c2c0d01e44400004655003114915215541850405814be0743c03c4200c10340c5d681c2c500310103a20989050005260422820020a684c400c5000041030307240384282c204026003824881440304201e4550700600149019a855450074040343e9401c0381c40301c42500c00d94000950101c0880c16056440d40100100da400502d0304842440995549003580c0c0c00d5401398405400228041040741014010b542001030a8005146010b094000050780084540244410448910001040080844100e00c4c192a8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 69348356 1250 69347106 69347111
    0x10e010504111c0206030105090402130906021e030f0a02090d022d0616060f09020d030e0a050a03030206010e07170906010303181410031b0206040c0e19021606 70
    0x3000d080021541c400c2125080c01541041e000244800c052030f040402640d00520182c40d5919040402084400252050781e00c55646031a40c4010241c502c11076025600c103420150301e50740c0b00703000240c550050030401c1954040030400c00031114a013100280e402044401c0058a409100c0c0104180c0d10303041000a4100d50324107215001c50f00420b000960908018036214181e042c81001d0110f10701800c5c501c110031010002020000078466004824840300e400e00c005058032041d00020a40004e80a0507008102041c81264450808001200280a003075482c0c00d8440e10391364009503100340511540d400c0c0701010f00860701c20707441009000e40c900b24560148030141043e566003034070346d0000c0c070040340820100400144406101261202100c07415105885a802a02d0511055850207940d420405030b444c500e507110300030841081c40424466500038601854a840e240c0300400550b0030055807074014100704400e1154104042e070311200d42e8080580c54100b0000810035041407031f02d004241c1c50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 69349606 1250 69348356 69348361
    0xa0f0e03210105010315090b010203090d0b0603060106180905180706050a0e010e131518060806130f02100201020d020d0b0f010e01052a03030403020c03060106080906040605040302010e0105 83
    0x4071008000039292400c2040303502903980e40c10042d02111070000d02040c170080da00404100e0a0340342e500030203290b00d060050301d241120000015002c100e06640865607002c43d5414044982000c112150140c01c1d68182070821050400000702503010a10510004c59102e0b40069111010800801d210f00d801e07000321843d043c1c4400001d0242d03000074000c540015002e80d0741098561080c1c00032004200e0140241080d551070429900107022504d9054480d0f20b49850001450034000c1541100e541c124000001d01c0c40c1810119800c1050180402e03480e1928030800780081203000116294003681114410400000508268007900403c40254403440c4086003070708200c0354603001a1043d490407518140d00c5c15418005440c030060140da25400590140118024090174440c41c2209603d0040909103507040801d42c10b285601c101c50071401608182c0f031051150908010303807030151800d030030700490a28080f0250341c2c0e203c2000704050b22542d11240400d0030b05001794000e061070030701c0100910030351 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 69350856 1250 69349606 69349627
    0x203070206040b0f0708040311190501050907060804050706051e03010311010e03030304110f040207050604050307110603160c0303020702190807080106050f0609030114040b041e08030a0f0e03 84
    0x5000840c1d042d128480c02c0f00005840c2d08194200794481c04564031040010b4445803400c5078050310313864189005100e4502b540d6807520700f0522803816244180004181c92800c00b82041c01c100700da0b807158003840303024810304c400144045000001e072042c0d0718019807140f11601c07800741c1c06000070b20310f50890040000080306009400101d0400c44200380c0b0303545050881d82c418160359201c1120090003080708ae415414441c50700e080c0300b07038100d00010030160034251380343c40f1642040010707030b0221690380c000640c4d50100402c901600000030320880302c0702d0461900354600c2c074800780308081010412000c1c501030790401d0300950603101c603160090f181c203040c100c03102081d401d03020f0f450103401c10a22808000150703c4c08140103c5040d508c024001580c9155050103001c1b50780c02c00e840c070b00e905d95260700b1031056503060300034030910440c068580c062040c1002e044c46000c00c160300701841c8146880c1c03100340b0042640001102d40000d40524009441c4100d400750358003e0101841d83c16440c04001440c6205 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 69352106 1250 69350856 69350863
    0xc0a030506150607020f010309051c02010204080c0301060b03040b06042a03050a02030106090512030c0105070504031208040b060d0609021003020703021b0d02060c07080105010605071406190b01030f02030702 91
    0x107002d020110840301c0701150100229405425402540481c40010b41c4540d0f52082c3c01c0424554400c804030b07102200c2142c60004c1c0844045481c0303006039408181001441404c00a514030541c05900801c410b90600045d000e06100041020f0580f052a1001c10610b85550340070543d000c480c03c4441410043c511034a100030100c40c5011000a401c0501040119555100300d904a074190703220000301310724000c00d101001541049002c00c501007400700400d4080c00b0b009282c4122031650354030b5610750031490311019030b00d0089080c9041103c0c4c030b010000082c00440995400c5003041b101e48170354140348d24101e40a414200710007500040302200303140c10f8540540140c00790350f103e502a1041c8400820098100c51040c8021a900000101d084805420301400804001d990176055400540c1c03943c20441c2581c0d000e03800300c0c0006400044c00024040f031500035151403e5030202400e5141080c515400c031800d4540070b1959015514910200b16138040ea01541004035104c90554a034036240102a49 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 69353356 1250 69352106 69352111
    0xa020604090b1044010f06080906070801090504020f18060f060705061303200304090e031c0b12150103020406080d050708030402010c0b040f1704060504050609030c0a030506 76
    0x90580140d5584446014101c21482d15090841e521030420f862101c40c00041d0003880d00a140440088900801351303050f10049000c0c0441d40d0000d2011890020300401d50700c001016104a50841c00500ca500b96100140c20b045444010020400e6202d40c0002540341c0f580030703070142d400085854071602c0300604003c02846414120780408100f8240b0007448014892050018607a400000000b002010000c900000a50180c90540c180c00c01c81e40f22144410b85106410f5816071010804000c10751140c010440110700303002c00395051005040b40182c0e68007402c10380c14189604c41021601e69140c02d054010451401e00880c0d001c881885050300b5507240a0000382d01031402c2c00e00100e00ca48000613003040e040029560780c0d20380b0b40c0e140c40e10010b035040504101d042000c40d07240304021071880000907011324001d2a003130200740c40601c2c0c181500121341c420b0030401d041c10311041107280c1c0c024040e11f0031200d09a840940c3c1e0314910700040d040501c5c1c00300e62980a91800707004410700c80005201032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 69354606 1250 69353356 69353359
    0x8190203070201141006020c060a0507050703030306080c0402071a0415060b0d1a0a030803060307090501080c041407020c21031b0706080c030a02070c0b03090a03020105010b12180a020604090b 84
    0x81d529034035840b00f842113403400f46c81c003d03034840c03031640100b8108031b8010070280f41a46030241c10240e9540e1030303604240581c1e00c00e03400207440c0c00303003448020000d100c1e101ca02c460460301140f03085280d81d199003d8416003004403603c80912800503052041d020340110f038290b2071072010070500e900c1e0101280c080e000040f000004c02d03e8a10050311112040070450905034008014029061440d90780000d1640300806641e014018058005644103050207801d01900480300640b0745000000140022108551002e42c860200c80060001898000c200d103000c5540c140e9040b0503a076402d03265803620441000e000380c1e071031000244203549540400d0840f0080e1881e4800c1c0d5490301e07a1054100c440050a99007803640300001c04c081218030b907550b801000520700c904000d06070680c5d9500c4604c000d4004464040683c3c01c40c01c0c0100425070b080c813500c0c0c050400043d059040c048540d19200303c44000400c1d4440d00c2ca00c2d6072220b20103640030007110400aa000700801e0340c0e503851384c2e5448040c0815140c9103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 69355856 1250 69354606 69354641
    0xf070e0d0209070c0206220b040311060c21070201030b0a0608150301150e010608160905040e010b0a090b0301180f02011116120b090607020a0b0604090c0f030c06050708040608190203070201 83
    0xc202366440740d04484c1160741000020701344820f40c1e02001055880342205103054426200d80251076551041060756180c8a45052911040c9034000076081d03e8944a885104a40001d02070003010341040d042c942003d440c5ea820b250b051071004c0071900411a402c2e00210608503d103000454840d86220a8160340c1c145e587e9041e0368494040070f80c00c400764130440c0004610110020f11684c10580d0001e8054038000e030021510a040c03201040b03000c01d250f00f01744010307034071a102042c45003000d000d5111404808440c0051400c10354860710700e42c010b4500002d042290391a102d18111000300894840c815030b07040761140c1c5e80ea44144020300611000740485042001c0d0b0000340858401281c8544690340310f4000e070540e030181c2c0d99003001460004106642c03041d0b941c80141d0124403110f584c04081c01c0c450b140faa0b40355056080090801d211540118100301c070400607080052035140540c2c049481c2810301c031103251507070344940a41442100700528003601c04810031425590542200c81070b101e01a226 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 69357106 1250 69355856 69355859
    0x1a130b090f012607170f040201140c03090409080c030f070302070e0c091012020d0e0105090102070f0813030215070b0705040b12090708070e0f070e0d0209070c020622 73
    0x1507035002a1241010f01c115072481c1904114140904003540c80001c03841c10410344210080021003110041c0c07070414120704500100002c550f04801c00d003141c0c85070702c0140e03400c12900004840d82d030311940601e6400707982c0b02c1e03000c403081184900a9038070544c69041603944440c3c1030840c4048642044205400602c24002c0004025804441c05070140380040481450012100c09100f02c000aa42d90042080015000341c1510002c51028101c088030811000c5a540d122151090030b5075405031090040d079104116481c000780aa15400e01d140da13219011640310f2001c00110111041070381d02c041c0d00a0b40350b075108414202014001e10704c0314840c034400c5c40c00d61130380c0c00d04443c50301407402400d0b100e040800c8800088851000d0866002c81c0010403a0451621018620304000e41c030b03070016005041140900c17031081c0b03051240e02d510481600e8040c03501140e03a000142442d0482170301074002c9804034040f58030300d4400c0e1240d01105030040c042941c5d030740c060380d80c00e00b07032000e46c1a0301c54058800900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 69358356 1250 69357106 69357109
    0xe060a15050108150a170a030810210501020705030d05190b0303030601120917040608010603090201020c0904050a0b09031c02030903030609070c050106090b010306080d02071a130b090f 81
    0x111003541d1040c2d450814a03510340c09051540048071245940c410707a840d100046e0400520101e10007102c005001d03090300340b42407401821a64000c0c14035034414210345401d210007a1811582c07060000709a824481c094014104140248180c05001e07005001c00038a0544580700c64010310f00520010405c001c110954a04203c22501c4010075141c0c035070800c0000c00e4456204101c0030030999103003040043d40215540c2c601080b043d40c0301030040031003c0810100001a040714000380100082c1c1000e01c480d10860f80000e440c0c80d003007034000b0b1007a4010808035090000410000e000306612040d02125400c062111565a400c600700041010686001000320160385000780ca0103070007110001c60643e1204010003407248001000f0104002444840c40c000c1b4209000c3d080003043c00200007e502e1050741c00050540d0382e5030300700348003035030040300703070900c06a8001644400c5910f10001e0b000000140e284010107403092041000d200c140c040700c08500c0501c8100106003111080302c0e0041d00801440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 69359606 1250 69358356 69358391
    0xd0f080402101d090f04020406051203071502040806070c0501050603071d0405031207080f011202100311090a060306050306070c05030406050304030c02090f180303090304050613090e060a 82
    0x25402034104040402100a80f8020010003001001103012103850b40e075104080f40306103004484a80c40d4180410070701007981002c0c81240302500341560344140c05075608412a44d24801d00e02c009010101101703440c0c0c0b01c1b422a5064030041c020080a0f41c5071410711100c0200186d203a010265110f52030000407130443e2500280440440c0d44440100c00c001001030785078116150024401d4600307000400a103083c42d40c1015480780701d0f200a4451100c1402c0205003010144016005400e60110088004000d13076a01848400341c03030881d250104903445c090341642141d00450f00007a410500003032000c40c4a9425421000584200f6000c5468654802d80225224000020050728035002040280b0106100e0070046a1150007820502601d00080d400702d07105c64012a24918071200030340034000c4001c110b910500c05007003800c00540c2542400c840c0b581e01d0b84940d10505202c3c040004082c1da011125070400002009030700c2040102071800721070280c44041c115601c819461400c1c01d0800c6002c00b91 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 69360856 1250 69359606 69359611
    0x30c0f01051603090602090603010303110c060304030e090604090b0a1d01020301030f030f0509090c0a02060603010c0503070f21050f010b071707020f1002071706010e04031808030c0d0f08 82
    0x80c03060500c009490b016001000001010394000c0e40030030810003603840c1c02c0c001b0750007948265206028400e48400d054184034040c09094030404023041444046640301403491030310b07001241d21040648038040001e00030205610001c00112605082041e40d82c4260321040c0c0b180a540d80c80c1100c4d1010040880c01c0b44400d0100030110300340104280082031181d140f200d07605040d8200740d0f2811494900103008100100c0341a091010001030184c4401d505004103038020100350001d1281c91140900503107a03000050070001048110342c84584000d01c01c2c000c106840e040360b14020040c2c0f640c0d40004003d003808a64200c0041108800082d1000602085403070060308171214040d5414007440701545588080f00590340145224490b04c000c3d41c1d0142c248840024540081094604d485201c8802c48600d00c81c0d04060b8020314010820300341030700c00c0140c0c001c0e494900341040300083c0c0b800940001590308901124031021070703503810071a40002d0140300c0c2e91640c2ca6600c04001011804c40d40c08404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 69362106 1250 69360856 69360871
    0xd110c1219410d1b02010b01080a200706060e060904120305100816080105010603022104021c03030c1e170402030c040c03090c0801060b0f090604030b0702030c0f0105 73
    0x1224203600d541460b8002030500c0300c101c88000c030201c9103502100180d400544100400f0360f51501e030034100105004004641540301e000034090404000c00181c14130000a20002425482c1c8141d4241c04150a07003a0b40801044001e082e25800d560511400402c010f010711011a4101d5001c144c1910b80b140b40c02e44243e6000980d0f02407140d424208401a020203800a0300400d0401c00110f0004424400c3d40201c21280054144003032030018040e00b1b440040c0d000c002031510402c400300d41c0001d01a8400e40c06060403c020100d07803181d00c041803910103580415208070406c0c1c0420810140c0c503801c4007a04409654803a01c50f040c0459554140c0d182e804501c00211351641034800c480f00500c5038070790b4090300080948640402a0700840c00383c0700d506010b540043c0d90742d01c4113030403c20940c0c202405402c1000c0200b2800e4104238220f040f0303200b0368100148840d0046001040d40e90384e00102c0d03010319441082619076080481f0069565040031440384010301841d505c2c1130307022205202d0984150305 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 69363356 1250 69362106 69362147
    0x40e09030c060403030e120417100b030a030503131b080c0f180601021c02151006080103150f0c0c0b0a0902012001020d020c060402010f0c0302030d110c1219 69
    0x44613503058000f04203983e6802610b00515522080e15403003080940020b0a010021100c40d4240c040c040b42001d000624203510340b458041c11004c0c2d924000303588490258141007182d07803510b038400c038203483d00500600141280070030b850008995080704130100407200c99408440b9100071000070004142c0080304400d13004a2001e00c070300a4140070944080d0803138018015201036501c1e109120600840318040c020242c0e203e903014110304150b01d51402d42c4940104a180c83d42414010010301000041c880681201d42d000d200d08580552503100380342d00162510100a46410030b07030003500d103501058007070341c2c0c1e600c503040040c080700124050510426416580d8101c0c61320042c07984d14490041c4100e1305620340d4240050220440148001c0100c0300d0210020b00040c40c003840018804102c014000c0c0c200501d18180c480025000000e6486904100f03002040c821450040d014a40c06091400091440780021003e48003101000620100c10106e10440148000c80026660769001d220425040d40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 69364606 1250 69363356 69363361
    0x206130314030a020c01050702070503120306090c0a051303050a020108070e030c010305071803051b1503010b071a160e0307050303040504090501020c0604080c06011406030721060308040e09030c06 86
    0x510910080da4008000040142482d840712909801c5400444455016a1192b5000d0200c1d1404000c00c2a841c094440283c1c5940340c0240130400d403c201401044c80c036403021403441940d03030150040d29500141c105065065617603d003001566401c08040076070115840d08040351109100d07170000581000d010740108000d4081400460081500410142c20000100d100f0305061144410010045010f900105030901c5c22001003140c004500c107489114411107100c5010701203044056a0440701a42c02480e1200c406042104602019200504190003400b04000480c0c0707042408152800c1f9607503c01006444900c2450342e50141400740d81e030315503c10f010400032880c0c030360002820584a000003508117030300c0c01c4440385001015107080360b40c0480406c503140701600030040c1c03500601c1e0403480310b81200003340c041541031001401e4001000004040b080c20707a1100c103071a4004103500b400811a2507524101600d907500305001e09503070007101c0000f052200c00f0020541301c0111207079002c0c16140c4c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 69365856 1250 69364606 69364637
    0x9031202160b0907120501050405011409060103031b060507050d0501080304140420040b1803010c09030803040309030b01120c0b040f060c0c09050a02030a0e070605040605070c050a060507020102061303 88
    0x4282c01000c9008a114840c0042000c54480701c011000c0780c4200004591030509140c0741d42540c10308080c1a2511502004000b2181800102581140c0e01410b0407950701260700c45a0310a075003920740190546040c082448a00c0764800001c05d41482099004c015030390f203a150260701d9100e0b0f403003408800716000001110920b46540074190104498402100002e881e111020b881d821030b9001c80ea000c0d0001c61011800020315002c014040402c60081041020441000c1d164014034080586492000300000d000c01d07001d42c10a83c061901b10324a00010760755042d14294000040d00c1c02c03036995180c0540001c11a15240c159401d5442d000109039000d414001d0031103040d400300783e003901e142aa600c1c002445103c43c1c46503070300440d01030001590382e18003490b416041d203a551603a2012640b01d4036041001983c0041901c058500510b030143d40d0740510b0601c1421140c440d0081640060b02c14800203e01d03403c08004c20003d8400c0c3c0036130300302c1c0e0b0b1102c0c0e800c0c40702c2c103001001401160000c030009958 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 69367106 1250 69365856 69365873
    0x30803011e09180515010b0a034a06040c0e06030a1707020406080a0507090506060409060e0a15060f0c080715060e0112110f01030b0607060903120216 66
    0x300c1e80e803010900c40301540c4a1280c4181d803916407081d40c00311601c07045007042c04030510080c00a00030515000ba01545461815052803143c944000101039640008a460010307000c1509682d035400d02c950303810803003030369041e22044101000c0c5c005e4009158014541028000c109140300710381040c001080640742c4440c0c2139003240000c00407503040c003812050318000741e281e5850581d541c04800820b515000140705000c00c40302036410120080d400300707890200040c1c00103040b03c15100c501c00040f41a840b800c000c640c41d0b010360380003d0091070800601040e001c031755508462040e24514010702c00700d4105914020120b90f28000c1900241c01100001c95140c01442d580400034400d080e0b07039250146c6500c468000642c08440880703c03e8448108101704c022410866000d80b030b030703030780c030041d0708442e40c2d46000c0805030104201d40200e10481900d034075070303001c0c0d40a84520345001e45000d40e81c0c0c0c0c05142020041105c054110042407029640d18a203402c14800d840080c40c500b01a220140c1076602c40024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 69368356 1250 69367106 69367139
    0x9070207030c0e1609030206090d0305091e040c09030c0608041b060206040c050303090d02040f020702060c100c03050403050901030906112101050603060a0e1302090709051903080301 80
    0x55120394540080000e0032100307441c0040c00c008124030000e042040580b03660400c0d00d01e0f10000c0007804501413000d41e07140e5084683c4581c0455840300d84407420329056810740204001c895004040c440c40b840110b0521080112180e4111030400c965111118107490108141c00040d10480711a51700384016030042490581080c050300c003d2942a5000d4a81c8000300241d4000d140160002800c1c00100301c00e100d608800390004030065418540d2850126940c007151540180c4038586403080c0c10004222981205c4403a5000351060b5503546c0002a95a41e48901206411846140880d08044503201341b05507805150b01d0b55800e8030745119032004401600d4210811b0f41c070941d44582440541c01d1a00041801241c03014488046d414011141007480070164040c90140e8820002c1010590b0b0b035840000a840e030840c82c412040d1128485203210b1070603814000e42000c00c1c6018440c1d5a42c001c80d032082121011204503140349501d0040d0840e0a42d01e00c40244030440030700052003040355a814020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 69369606 1250 69368356 69368371
    0x12010906050f01290f0403030c0210021b0f060405030a0605010509090105070e1e100e011215031403070605010e040b0114130f0e0304090501090b01110a08130e04120207090b030c09 79
    0x604090001e140070b4046d6020f0341c0101c6c0400c0343c01003110308504240345402c2442e00103001401d04003513a0342d5810003a8041039001c1d4880c03041d140340a130250340d40500b40c502411024003201e85411880c9880c5000704020701409100c2d1541e04009420402c050041510030009580c4000b00030a00300700b400080d0200c50000780d4040304040160405842c5d00400410325040b07a5034090505046a0001d05440107441d84880540d003442009400701562100c400e00b100d921041032400100c01200860440c004c100300281410b0a000002440134518085e16010b03e0003403400c0e0030315980e5103450305890320741318100c1030b08009100d10920b2071569540c81080d107810395100c0403e100418402c0182143c0c0560007020509640768018007450f9200d203d156210798003800c01d0f801c0c2c481016103150b6943c44001e0020180640040c00c1e01c80403544900400c02848001055245401d051416000c01c840d01c2c508040107208820000138011018041d010f140c600140180000500500900070007040050155 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 69370856 1250 69369606 69369689
    0x110c1e15040201050d02160303050903070f0f050f100e0106050108070c1106160f140d0207090e160612050708150d020f0607030801061103270f12010906050f01 70
    0x3417205229000400078403143c6801c01c0005011840d02400700c400c0035041c4a1a64020700c0388100041091021a02070340e04008170403007074030701071602c5032900c00d5807802c950490044064000010015400103d0aa40c12800034090300780c440c40115000d07002260f92000040701c21208074080780750020008102c00000e00107600c0c000070308001401c001d080503800c4178400c10911400051181d101142290309100300064024881001402035035110240650219541d8584011101c0d00003006010070320010b548603001030381d6803904041d280340000c02407640c1d03140c101000502d65a100e0f0b590188606030b08850840000f40c00014003401030000d000c102d0700003a02910071115551040050320001d846507039000300560410074002d01015400020071016402804501341041e0310703d600c0c541d000980042038400c0d0150b540018200c907019200603820000c4c01011000b10501900900440d9004100500c0f017901c0355800120142801d01c2181d070220f05209401001004180d92039141030245540c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 69372106 1250 69370856 69370867
    0x51c0b010e03011a1201020702100807020709090f030206070201110301140406330c080912190803100b0c030d11040b03010801020909060102150a0b060409110c1e1504020105 76
    0xb10342180c80f01c520790b51003041d02100d54036061070452100780324600e00c034001b942003440c50390200344240b202400700d4081c403503e400040d0340e052082190000410906505100890003800c00000086050000b90300501448000429640c01402400e0a4480c141e484510307617880c24004090346403011340e0581c1d109840720310008540c0c5444e0402c03444101f20820b40500c2075890300407000c41c01214141390301400359515059004c00d6103042038900c4058165000716591441803607250500303030708101c850800b0f6841c1d80d840003841b8102020314807415040e15804c0030039032200580013007401030750344007807203a40304100191402001c0c0c0c0200c00101c0480f100d680c10b054450021100c20b41003600078401d160b50100f105015440e0000780740ea00030000f80050f28101c920b0040301501010b004050814030758a40310b031003246441c2c1d0300894004004805041100381c0b0803500d8072040381d200c6e640c103030034501c21105120500c07007208200030381d00c0308024001c021025426031200144407000300140e0500c0802d125 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 69373356 1250 69372106 69372109
    0xf010203070606260d0909150819020a05011403040602071b0603020a02010b040501031e0503041e0e010501020d1224080c0a09050105130509010207020607140706051c0b010e 76
    0x780f40064002c840b000c1491007002440e240d4121481030403421070368000104103045640100349801a03900d55078010500841c5240003410585d81580303d1402e600c50440c410346502d031113000e07810304a442100d401d0343c4107030344400440f06040c4907041241c601100300b010800080c070650040c8001e501c103990094994000c06040001040c0369403000011031340003d80317040c10301d80c280315082441c40205c50810055045440300c500004c6403a04184841008020460a00400b04251401048400c0880180388400b4030b1403002d4500c688241c40000c4100c2001292560001c00c00301700c0c05469940e03424180f442e00141c0400307400304840f411040c0c0c00c41b01c000c1e5960303102e40b12044040c140c200001e00d841c011902c00c2c40b2494025500c16202c40f85024014800c0303594492602002215400001c207450b00c13540b01c2e0a0091203406002540502c0c0003440303c00b0070000c14070300481d644800040d141303415602d4500307440601c03a07038071085400104c0b08500804500d2583c00f21010b0a01807604100c009070000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 69374606 1250 69373356 69373361
    0xa0c06090516030506070203270310020a0c0b0604020906030402060d06030c03082101080304090c022401030c060305060a06031e1406150702180711070f0e0f040b060f0102030706 78
    0x80c901502c04100400384180001000001c0d0810703c1c1e840194541000360549404c2c1016401034800e004410015084455038104490074513590003210841d912910303c0405400c1c40d580c030398200d4194240300002129441c0502c25134181a44c05450a40f45540e140d00304200d50780201da801c2d042d02c0d80c4810110105038952140f0000d548035840d9035aa4440e188404241d0210841c400340002010b10014401e0045c040107807011100c0c8103001041098000c4c07400d90428000005840c00c0740481d020301140b10382d00142842c12031b802170700040d00d070075140ca0040341503c904803191504101140010400c9511030303800040c3d000e2600040c1241c2c403020808900a8404411504070b0301c0c001482402824a40240e6803100c106094060a1a15400360f0100780c180c1d1181f039080100c5112180080d413114002c070408000613510006640040342c49048419441c1d10a0040420201080c000107078603a1303244a20070300568102450001541c1c1d078104009801d96541d02c070300d0441c00244080c9002400c0c50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 69375856 1250 69374606 69374623
    0x3090f0102070807230705090a0b12030d11180f0103090605070206041106040501120f1b0c060b040902130f020d0608070e0a110d020d1401090c030b030706050a0c060905 74
    0x40488a6903098241080b00300c0003603030903070880c2010030503221545c0d960300000c440d41100c03800d44020b80d950303550400c002c00400004808582009180204550740e03e004401400b04401280e000c02411015607a01983c5024007ca4844841e078000d0510f0181d240259542c0c0d41110145008920f01c0110b99071801510400e40c1c0c0040540e000d40e0a00c030400407012206444a0310580b0a01d00f010310341400200246c1c00c0c0740c1f11442d80d603550980311525103c03a40081608140081601449442c044001018a40788801c1554204d260044e82090780c034140c042c160781e50750018101c0380390f440b18000c5030000b05030310a181c01c0b80c06da081140620601345400b54900400150b005801414942a0b458801e07100c000e01019500303140c11203240178840309400341c40c40c450100e0001a295082c42c0303010002800381c02d01c041e411414030300000035042440d4100b440071110782d030340900809540c4018591741c0c041d103000d8040071940a10802031102d105a0b2034881306401601c0209a000721622400e00b0003030741 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 69377106 1250 69375856 69375863
    0x150c0c060d0f1103091207020f090408040603060803030105010c02121e03090a0509131205090d080309160303020d030906020403170909090705011e0302070c060f09050102010b0904020603090f010207 87
    0x5600103102c6041c02407190301200c030241d0481e6480e40c41d10101c0c143c1c131408201854100540d000c100d040540d110710764007018550740540f04c0002c0e8206030038240c009401138030030003000a040a41c0406c903507a0100650781201e4041c3c48120035a0400e6080104204c1e0465040ca058400e88040c0e498080503607054505001c246809940d903110b4800c140500350f40c0c035403c8540600214401c5c40040303464000d400050613040415980f500d250b00b00102c134548146c01200382e0114180d0303910008c2c000500c00450140d1800000c41e10080110400b45d41800503510019000d41c001c00101d14a150090700625400c520907000140b0700358480e42c80c0f008081c0301e400d180d00c1d441004a1071162500702240320b160003015202c010044140b500000074409e061004d1f080c80742c0300700d2040d143c0403a4000d805484149901c000782d43c81268803031000410f02c07440d02c0107902c006100918001010350042c070407a00c3d0b20002904141003617990b81c007401a1540702500e400010300caa14042105600c003031002c0d000c5c40b0310 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 69378356 1250 69377106 69377111
    0x603061a0405100314070b0c070f060206040b180708010e010603171206240c010b13140a0908070c060e01080a050f0412020c0406180c030605150c0c060d 67
    0x1480c040c0080e22440d1158014056458070080c040c10650100354503040340e520414040580c5044003d10341040c0380d641c44540c0c44040420418003c840110300c3c04c00f5a04200c800004056a84504994500c0c05880180100d03107a0f401040c540d4421402655007a00310400710340d485070703503007522500311000c0019030820b80e5920003003070080003030115078800003696200c0b1841c1001d00c1000203a1400700050030841c4200341820f490030181003440907158054034900d1225480301d4400d1506030182030307010500c900c5964166042c034000d061a214071800100701d12420703002e540e25031001c2401810f6005e070a81340204188804000030701c0c0c940150700540080d9075030b003400f00084000902004400340c1610b58207801d001c20408008600112194806c0e0065500c460148001d04140d0a040c0fa9140090b04141445804100c01008860724982250007840170860004c02c198210116207090045582c01500300700b80e10365003c00700024050344440c00040d150b03004a001e0010380e655002e43d42448946c3d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 69379606 1250 69378356 69378371
    0x80402040f27050705010206041a06190305030d050610091e0503060106090608131716021309031101090b0408030a15120201030e010c0e0105130807060203071506030203030d1e060306 80
    0x80d060154600074082070002346400d0a06135188000c007501040d01e0a500300c0d0320b03000541ca0b903440101400ca07540d1070b0104108400d440782849522603100e02511f041d602d040c040454403030305000d19030b1100300080daa1290949818001c0700900154000740e00214502521008615aa0f00780012030003010140c48404034640340500140c5903600c02411035001d02c24040011010030b0486001105c103500030000a0355880005981d94100034600c2000381d088540b080002031010442d90151004900a0b01d440780b4400c1c20700541d130300f42c401040c0020000c0040d1001301c2e0019004a0255070404815034020604440004216a0003455680614141460808042c0c10340d42c25201d10182e80d00d41e07e00038891410340740000f51410060005c410b0400000140082c0e86190641c00d02c0b02a02820703040c0d980260f59100000c0d03a98105c4602a69101ca641510341c071100f04d00e1160b44100d0350301401450a0100b102996030081111140c00510b01a143d903401d860208584551005148240340011390003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 69380856 1250 69379606 69379613
    0x3020f0a030801091508102403050a060c02010e0a05010b0a0b07120e01050c0109050106031509120e0d050709020d0e030c0d030213080105130b0a0204060e06090a0302060d020c060601030c080402040f27 88
    0x60803c443c2d507800c8c40c808a40c00b80041040802c0c09900c041e005a004180e01d003045500724014103110a03a10a5400343c3c0c991102007080640008405120440b41105980c1e11a941a2810b00c40c0000003041450542541000b40e809071126416801c1d05041c203d00786006c1d00605425913540700422a11a50b4840041c010004a9910f101414a4015080060300001ea842661002c50f40400714107000d04141c018980ba520101d101c86401d6000e42503886403561104000e020750800540c0b10007180c105028001007480c008281e0310000b160000a19101403012000d500a40c04860085a00a400745012464070b60900542e801043c40c1200710302c0c1c500d0507041040c2c078004c01a0800814a0040104006243e071202201046000c12030341c4660300c0d203480f00080d00212007a40000e42112011900e60300884003603014141c00350400080d21403541c0c4510044007110032070668100492105c00225000d402d003940310304070961501c800087d03000091503a01c2861400e600301207160643c8403a464080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 69382106 1250 69380856 69380891
    0x3021c0e1e0d0f06060e04020d141e06100b090108130c030218070e01050c210403060c050408010c0503010f0b03090106053106051c030201020906130303020f0a03080109150810 77
    0x8041002c6c40803040c2c205035001842d16040d00e10080d11440507003940e0b59061000303002d43c03401014615024440d9040405e0403a80750300c000c441000f03801200c08070018030358044008603940040140e44408660756600001c022000f08a03909803084c01c040503011006840b00c10314619914602203500f130240c40e04c802e0041c03081456800586c10004141b0104003030160024050b82c41c106071810807071404801c10350a078064003d90b440a0080d40c2043c03071902000350007070020002e580405d4000d010307070450460290794a1200b84107244920b1420402007140002000103141c000481c400041191941c44002400041d4101c0081e405500e00a1890002c8003c450841030380342804002805403502d17042c0056500e10b0b201c0c003400c03403176032043c081c0404061007941140d0828400406079911074a00f40840d032081c2c012408200c01500c507000041c100728500046407590158182e54901c1c881e0700700403104002d00301c18902c960a54034104c2c00130441e00c81c1400002c4c2501c00151001480500c40c103d500e46 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 69383356 1250 69382106 69382109
    0x40902121003020a0501050a031401030f0203060106020f070b030601170c0301090609090203030d0c02070f031b08030310140d020301050c0c010c08070203070b070905130903021c0e1e0d0f0606 84
    0x54072026050400060700c0c2c00d240e04084034400d086c01500d44520520650107400b48000e109000c010b668004801c01030100021091640250300700c03690f6a8861134240c0c2d5407044c00300c0d007a8103a40028410030a03403a03210002c540c001010725004840d50010000f0420a000560b0111207409001c8018440035031140b00c0c07603000742280d032824041e564041d008682c50340704014083c1281911a140240518000c00c2070100528124104600e910ba890800750036114014650085440180c900090540c10000035a400b806896042600301403800034401e850396201445150050454070506016a0b030030300c00e0341c0c030500c034400c035696403610042c66041c211512484101e06000b950700c02d000101d9800001e03101481e600c45d8034064161a5840300391200702545c0c2c0420352280d66908402220b409640040c42e00c60300c89d408a420988000030140500d445400418001400503901c52000d494440c034076007200500a84081d5034045000d01060b03a0444002068504040c03802c2c43c0030801c02f69216a00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 69384606 1250 69383356 69383371
    0x803031905060312040b070f120504050108070f1706010908100207020a08030408060c0c0a21030f0c05090d0c09020c0d02100501030804032405180f0d051c09060204090212 75
    0x246800310044c00e02003074041da001c3c09084100106502c402c01c8242000d007c4000d400010412800300400c0740103125520500078a40041e45183c04114514024048219000d40640790491499543c03c3d01e0014100c0003040c5a04006008100007101c0b4410f2003030b503644080040c0c0c0940d542049005201c852880c0b5070214072190b1040008220000001c2002a00007644840d0780b541c0d402290740e498a06188024080d11100480c100c00401c0c00000c21350b0042ea410603101441700100481c80c2c9401c40d01843c0345030010440c200304c010f81c103103060081c1300d0182e4860552100b02a40300c0c941107040307801c14031140440340e003e50f2010320043d404010025920a501c6d40c24440c560469460550a02461000800c0921840c0070707001c410101d5070315040c5030781c050b000400003482c0105013007010600d0507100110500842e12084200d02c1d0216403504046075a84426191100482441c030100c401814840500e590b0782900d08002040c87c00144000c1c403088901588030104003ca1ba028458013400d1030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 69385856 1250 69384606 69384613
    0x106050f06030c090904051002030705040504150810020c0a050f03040f0e090325020312041d150906030f06040f060621030f0e0d0c030507050306070206040f020a08030319050603 78
    0x7003400c4540308850a084c0103441c1400070b51a5854800e103801281c10080310300c1d40c0040f04200b034250384071020f04220394013118248250301c506e00c0780800c40e403002e00801e40550031803611140c0c1560560000d09005146000719804464140c0340c090500940130070a2580341c01c0000c04010904860360750740040e103017051480d9a00d003001c05903180c0d01d1143d6001182404000501a4062011a810012034a0b000b8042d40c88a90700050340c09181d0f4400d01594501d80c40c140b0f0881d0141060715043c0e40b003900d5003840c482c1004810420040004001420340e94075103d00703181186500d0b014460366000d9481880752250411903842c119054840a402c9540c1f103541c180462030702c1e40d40e08050b50403002d400d41084071111160400442c1c0414031681d0300f58001e01c0004080013080030040190085034001c009440324151200109915550140c6413040160f100c00f000c030300400d04e41c64152034003910013051640c60940c0c80391490f007950400c850a41084c0300307030341ca40010008903025107940540d048019 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 69387106 1250 69385856 69385861
    0x709021207110601062d020601030302160b030402040b030321040302190503190905040c09030203060f04020d20131407050406020a150b03030c06040302011a09010b03060d140106050f0603 82
    0xb6655a401403040e402080001521402c4c204124640e2417004a550011511480c40104011f55140d00070b00c0201c0c014030802001481609c8001c100d9002c0c3c0ba039840d102d501d191295000c0002802d403030300c00c19503d40020441000e0950a0411162281410b01110721013031409007006420705151b00707080c4159210700b050003c0003e00200880d5081c408600c42001510302c2050101c5038100d15402081d0420f1601090b00d141941240060044a00c21000c0340c180340d031781c00113015158034113035002900203041000200018801c00c050105030402e4030346002502000f000050300e0400311010400c5074035503400b4500504590448120392019850410a160502d003420007962100c0b60743d13000c0d25040040031504031420a030740100880310402003c680d1201e180c003a100f03841d0042a80c08030003640c038003132407040300200d81c0c1c001a03c0004c00602c60f4807184c0ca014100c500c6680002c0030181e10800c0060b0403030000e180c1c06010056843e01d0b8000042040c2480300b44074a844503030800d2403080006104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 69388356 1250 69387106 69387137
    0xe01090507080f09010e0f0c150a0801060507050109050d080603010c08150423090d020715020705060c03090909030c0106050405060906210102070503030a0507110d031d0709021207 79
    0x9403e4100380180d80101080d0703a100c00041c010034480000c0c0d0340703d02468174040060180010280b40c1510102c501d5131540003406020b96003032003404080808141003c0040201500410103400380c3d40c0a54004100d1104039601c850600d506044448040342144081c00320b41c0c1401d2141503039521041c10800c40130b0625400007040d00d903812016910540c0c0f030b040348090802c0e036a404041c152001c80b13022400750500c50146034948c00c49900780c1d0014131400c0030010342c00c80d50400385464204c03d40c001d070601e1820001800850740c8146480400d510040200100b65140c0450340d03440f0302c11a001440d25071804950040c29a1050b81c061b600c260b080c03c0500040765a1000c16680246c4101c3d001e2102e50a458440c00c81d145802c0800f01c0d095101144c01400e20001000451042c040f002d001c02c001c0e62513990541c0c0c10340781d0603410f100315444486180c000038003991240c00c043e9008405241002040e420052034104142c0103d040c039034000c180103c0014646e0701068020850f8100800078000410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 69389606 1250 69388356 69388367
    0x20601031707050312060118060909090c050607200301091709150f0301030204050105010516171903020c01050a141518040b040b0a1104060e04020d0204030c0e01090507 74
    0x645959041102a41c003022580c040b14201c65000b0152500c940003100d8041240000301d41c890301040000031282820540c0301c101c0e40c1075840b181caa03410320904143e020001000745450480e004841400003045903510200034064107407007a1303662039803c02103804c2c000c19a03803507aa400d400f90303041ca0203510000e520b15076040c0c0c0300d03010440110345426054000451070742c1410340010b121980000c4c4440c2c540c0c080c00055040c1c034000d07142400b250f42d80308011240c510600b51502056550505000d0010302c2545034441040c10f40000c1a0804101444e440b02048402d1300244c08a41c0c00030341c95500c610b084c0101c1b68001c0800f0001c210140785110041e075111401402240f805245800143c00d030341c1e8011242c01c0f452000708041e200ca203400d10300540404010b031015200c0c80030705000103000b40c58500646804084004819040902e0404240d84488500300019803080d02409024003d0400784040d000440c004d203100014645000c540040000060300040c144c00d0030501085465a00003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 69390856 1250 69389606 69389609
    0x2070602030a0e1f0504030b130f030e030a020907050c0606060406050406110a060f0506011716030b030304050d03230705030301120201031b030b01110105010503072702030a0504061b020601 83
    0x2410100b014981c400c00042c2c050f03c030340e011130460f0045208a80c803401e0340407025100381e174801e0300d03503c4040d166081c005520711040d038001000007c3d800d105c0d00004e817181d00c00558071607020302201d181e1041c96001604e0084c048891800051001c80d006248000c1000b1503a000382c41554010328040c28554024281c0c41640140d030107211200b4502c400c8210200b11000c41c9039088141000440d0480407200040c3c4400d03182140080c0203940240e18804070041c2050050744200caa00c602803a020300e050307015003016010b1540c9030005100c0011503072101c19038040d40c14800d945071115094401c00f00358103c00b00d03ca41060340700d001d1090000244001040307074150750220f000c1500d401501e01c01203029114010340807841c0500c0c00319592005030503800032038240d40300341c030f03100e04200e0744d0000e13503080750700900c200384d4180d02410b410000448412685142c0d00501c0003403506500003c08030100ba0784c070954002406903661030800060080320710581441c0c5040203180700001c010064002e5480d00c06 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 69392106 1250 69390856 69390877
    0x60315050409080c0106080109060b0f010c0b070908030c010b091b07030e040906020a0306030606050409081603030b0612040201140703020c0108180a0503091206010f0303030207020a0306110c0d0207060203 90
    0x44030703280c50500c42d20300f0589404400280c001e01001ea00c035120300b4046c01c2c00310350446206051403400150303868409100004018107a54056503200b541d120400001005004901070043d04000800d891009200405030000c0c0c86c000892000035200600210410003090340c006401c55502d4281c00c0d10002d0110341d01541c140c84c101c292600c144c0c00240090101120041c07505100040d0950360f41e405403c07001c21640503c0c000c0108540d10024401501d11041000b05640c0003080000c14241090402000c0b2070701a01d0001510b421321404502907034000390321585c032035400c03008000843d07901a03640d0f0994203200001c1c0c1d0a144540c0e0b800307941d480171511201d040c00024000142c0c1e002140c504100c1d000304180480d0010601070604603229441644035a001c0c401d0b00c150000704410002d0554100c45802c1681081189162400c50003500000400c9038420081d0b40c001010440501901c40e0070804480081d50b41c0541110701883d10340703400d00f02820f5400c40502008126004010744945408 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 69393356 1250 69392106 69392111
    0x408030f070c180c020706020f071a070609080310090b01080f090a020307060f02070503070e0402011202090310020901080603010b011e110303091f09020a05010e0f0301090605100603150504 83
    0x1850880e241604682000750b103c0343c0303083c40303003a28400c0fa04504090806074081e21b0f0340940701d030030032621594400d0042c4c2d0702c0d52140900300081c48030f040110b10f5204500701c601d801c0c5042c0b603641200ba200300007000d50380d0840200030b115008926041d542c000f8a00c9280c10800d1b101c0c0d4000180c65503400424003400e4400720000100d1214050161101c4c3c103a00805a4240c02d0721180081e24665a0325000e01c01032141c4e48011403603050000c0c0d02401d407040b551400d60300742e07503682c01100c404621001501c5225000d001d081540d481c2045140da00b0801d054003da21039101400041c4425402400144a60b050100c51022641c0020311920015442c1c00d1220240070350a0065620759401051152144800400c00c601284049414070342501180c0c0790240c204010f40030682a40d804850295115085c0001000f0542c000d0f1840c81c0203a50103807400d1507602c001c0c0c00003070845030904003d48020b6120000c114500e2040c0300d07070302c025001d9403c003041a286401c242211282a0740552400f565 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 69394606 1250 69393356 69393367
    0x3060501080a0203131e24200d050c1303050601091413020f0607020901080a03080603030c06060103020313060203070201050114150313020f090c0706060e01050306130224031603020408030f 83
    0xc1d030600b846c040b150402c44e2407800b0340080e024010501508035006514521f003080b45540008071520103583c9501c0d9401d2607052070f01c58101d01c0c00810000d081500080410040d6a5440d02603e48107401075010f41c004c0c00f120340c0b6040e0b80c2004d551035000c00561504075103017000b03541000c01440c1c6260580680340c0070891040c0a000c100d2500c54002c02961100880c000025501400110703c207140d482035446050381d440e03450906a490051881c0748500d90032140010384a540329a026580c41209004451303402c010545424003281e10503504880141d460380c0c0140240800da00b01c180d000c05068a06504000d00401482407901018220020003c0101710340300a66589090104160a0050403000c040c2441841c20740706030310065003158503604101000401044412626040340c602a0207030100d590750120040c6002903080080342d02c2035000c0418103150079084000303801c5071511180d681c1e690034542850b5802062949200b030030180108000c1c4202d000c04000d03522f502c2d0025081c0d40d280d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 69395856 1250 69394606 69394643
    0xa03021f0201200405030c01020303100608090309040f0e060106050430020603011203080a05040320151003020406120c031b0b0d05060103050601110d0c2103060501080a020313 77
    0x10441092003080b48100340c0c4a1610043c1c0e108010800c88104030211403107815038100680e1640000c4a181c84410000300042000900440d403e07603200f80d28609581c0751030010310002d021903050302501185140c3d05d090f601c8203080d0070003449014001a00385070742003c1c5000e02000742c411518444017003a10214190a12040544a0042a19600400d945e4903580c680114240c080124802600091b0240020501d0903015201c3c5a018070b030140d864404c00a9510040c2c200f001d14510300c4001441f030040003003402e1007440c1c2510700841c24503801d4820700786140100701c282d03500d40c1c100680d2482c01d5003001e4005805e00c0d40c50011a42d1141d880c610350070384e410382c40c8081001d90744080310300768001035140d840d14810317480544168800d803010000b68480c4801155030301107000c1d0b881d4075035002c00350b134a0049019040c5001c10074030130b0a00454030307130078010000844c0c084030302c048000c251074050500903580c010700e501d81d10259446007142103240029001082100b050b9028048050008031071520 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 69397106 1250 69395856 69395861
    0x17010b0c01060801060303051909050604150c0b0f09120408061303050d0504050304050103180b0a020d0902030a0803040203150910020702010c052d030901140a20030d05060a03021f0201 81
    0x401030f050003007041d0390707403400c01500700e612118008050034807a070b45801e03815014400d800d050395406860107040c01e080003491401486070081d802c092050b03808144c0e0005003205a294452010500d0444150800a400f140b40121074a50b07259010020b0000f403020610029031a6808909021841c18402242c2402d461511443314418040c0c0c0c180020001400b01c000010001c0342d00a90b002c010b40f8010b088403149002c0c901000500440c40080801c5401c50181c0280ac01020343c414001410241d41d40040e160564030081240c061a02000300020340c507040c05144000003001121350407502e0a442da003520354141c07036500c103440303903002c142c44c0b056900c00c8000513000c603444000c07600e45144101ea6007690900ca123260303030a25081400c110041105c0401614508003041e1a1101591803240510483d40c00245c00b000c1000281d48804401f0034030354006603038030002c80c0e0285079106011500c0c1310685000400c5d0500807040c0100030001620f800c0d40c691403460015481560312411803604a02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 69398356 1250 69397106 69397109
    0x3160b07051b0f160b0d0c030b03010204030c080c0a03051e070e0106080402120c03070e13080a0c05060604091101050d062d05030d0e1e030109030e1017010b0c0106 72
    0x1c0b41c042480b1555011a00054120340007158002211001d01010007944d07640c0d0344900542d400420300307001c62901400c0c6904589205078650a002c07480b4030507840030a08a0300540d20681e0f1981d18a9810443e001c0c0500c50b050130450295009114181036860f0140c1d100e2824091503810a42c0c006020301c044424803480001d0480d103030344556156500e400041c104030040d54141e114042c1300c05c98000c00e2100044035200894040d0113004040e160045400144000410700b4100c22040c68203880052601d00081c40f003804c8070b840c1c4228041190404600d0071400406c4140130301d15101e00b81010502141c07401484c5802441c266941e903400020b05000307000b0a41c003c0c0c110030f64018031480007592007241056002c1001c040c10200c690b0f50401c041c1d4644c000506031f00414540300c2c18541d01d0510a068130348840d6000c1c10f640e010700c0c4210201c0d08650103814164001510040390100d0741c6049190b9444014a5213020550300642d03891100c8605810f11801c060a000000d17100d41400082d0020b00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 69399606 1250 69398356 69398377
    0x307050106150f030c020607030b0102030c03030906041a0f060402180312040510080105150a0c08040909020a0501030b13050702070509010e0f090607090303051c020d0b1203160b0705 80
    0x19a07140d51041025603a5011180494031160f51415118440d00c41c4040741d0074581d0003061103480d01c1c0c0c07080d4004c00c0200a071b40c0c11070108003c1c82c00b00b900c003000254060444640240768a04c0c01d410119850b12030b0210ba007002c041801c0c148100c2d0340c54011000d0b0002e000320303001685e80c5800d041024012051184541e01409000e02403072101c0100000b400c2220420740303200103212502e0208890410090207401e5010381d400b00f00c07505a2140d50080d10700400300d0300700303072451f09250f49800c2c0c0f031a002030f4072a000051302d40c071503c821405c1403040d04005080a007001e02c80c0f5218800051115518614010001d035500c030000b41415108010301c03001001e0141905d00c3c1561180303100304022004507008800b141030000814510040061202d01c01c801076a104591a421954221740b00da00494480b85030400000c071070359030000607100a04107031146407030008200030030340d01780581c4c01e01681001607941c2042c4012131b40c06103800003090f40180e21401070101079a48610982e4140541d14149 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 69400856 1250 69399606 69399611
    0x203070c02120105060319030c14150906010602010f05040f0201121b050904050108070503060a1e0e01020903010b0a050f040e03070501110a091202060a030e0a060213030215041a0c03070501 83
    0x50b0354404040d8000c9006282c180c040e03a280a08480c0310b01003406004400600080c81c1d00c0004002c120b00f5404052102c007882c0650781c0300554100000d018120556030540e881e00200010032241e0340905c02d036207406614650911940c80c042d140e0080e0f2a41070310010707050005248000c0301c40c28455104108602c4c4591820214854146005043e90443c21040d030003645044004035100c200007550b0381c11030300c004004103510341e01c100b803034806041c4c4100d0400182c01c409129045541c0c01f8001c96101c1c6e100c0c1000140c450800d48101404d58844094140c02544480b038240305e2074880948440110a09403400b080711110f0f826500d241d0b204039a07010780340e940703030400644100e400c0c60024200c80016aa0320680c003910342e03a1400b41003207860307002940700004000414006001350001c0503010310050940b01c0d01c0800352202403c0c0d90000480804e01c0801c24028002c51516039000c62a00c081942660f04003410580d018000210751101e00105000108001981c0703a8104110313820641c2c400001d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 69402106 1250 69400856 69400879
    0xa3b090402040b040e0706080c0408070303110c0306070509011701050a090903020703120804020a06050415110a1208070f030b130902060d0603080306040b01030b0d0b09030d020f09030f070602030304060203070c02 93
    0x41036225a1b0900a04001481e40008035001a00308425281030b9440c10b0080e100c82031035540c0982d4443c0a0031803000590150048920aa41d81031210b02d102d44615224079954031000d400041c0b8002041040c240c01050142c0144040c0e00e800c111413042c0c416803400000c0c2c1441a040c1640340400e00c0d400107014031040c041d41ca900d84e5000d00818029482642d0100c2c109032900000e0b110390283c0e00800f13003940101032401c00d409100f1b029a44402007071109484601c070050301e030f18112961815500010500020500018980c00b015080101c4814681003110041d680005901b00c030b0104221540382d9251404501035507a09422120480c180303044c100040c0d9560b1401e100c060300116503943c865032a12440480c0c075400381c000c07400458401802c1250040c2c0554600307506280180070702280780f20078800001403104500c01007a1084000d46c2032902c45580c41d003054500031091040507626040b041c41082603e400000745d94009034402c001580725610180103d0303e032200410083d40c4044580107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 69403356 1250 69402106 69402131
    0x1020313020a050109080a0213061715090115090515090910050a05040b16120903050d0c020d080f0703090812060a1a07030305090307080a3b090402040b04 68
    0x50102a80d100750760451041d40d0f20001500c0c14a501e20038a000ca03000041801c0040c0b07460105800380c0081c41800084030380d15200701c03000020f070044046801d40d0040c002241e0143c151300e000da80c4511003600074030034070084090702d501907141841a0348141e5111004544854800c8144550080e00507214900e50b152001c180c42ea5032038518601c8506c0c2d440d03d40403d00101050082d18403454001034034000944404100e80c0d044404407030f6010802c841d0707036030120003400c49024114581e03000c1d540707060700c403040c103030040e01196490785043c81903611203a52407080c541c00c80d410b554003003403071200c000b05030717807404425000b13008070300c3c0000c01c0b0310000100049006071083d03143d4014a0203890320b545560300c0d0003500480740740c000441011203105003d0b1074000f0744240c0100303900c1a5a001543d040024980d03071010250070601c0e020021074031040d00380741c41040041010511140f28903540c090104080004842c1006003000715001351440ba00044c19900c41d070304144200c04000c0c0003080001407864 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 69404606 1250 69403356 69403381
    0x90a18060812042c0c1305190e010b0a0c08070507080709020307020d02010603170a0903140606031515101b0b1503010603120503040f050f03040501030506040203040302060601080c0c010203 83
    0x41144819010780c040d04d454100010390307400e407407240201a803662140c0030170141035041501601e125650f41c1c0c2001c16103490b203000c40200c142c0381548000358213080484001c0035940507080720340408414001032444030b038044140c0201a400401183e6240345600381141400d4940c2c03c84221485101400110340c040c5500461280300d03d42d090310030f19882e01c00120300361152880003600703010344e00c0b2510f1304541c4420020304010721141030170003156959946000e0108100c0700007a40703c3e0081010005217040038401a018407154000260641c54601940d82ca185200e00d00389004d03105481c819020f040c01003c5900a561008070060001440c901c0c2ca46141c1e0400ca690a041e003240010944030390405004000c2030300c0d4091140360110103824400c40c0c0b20307000244141c6100b07994102020108130180129142c410011000d95a01c03800c040c00581070b100007030100d40c041c03441001080301017940401c2064020109180c6120350b5200c10030368230482d005001c1c19900079440001031001c4540d905 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 69405856 1250 69404606 69404609
    0x9090807140c010c0b07090816050114030403120903050d09051605030a020a030b06060906070c060f09180903050d0614030c03010203040308070e15030f060108060402090a1806081204 80
    0x1c45610803515214000192102c0c08081c1107804216121041000a200003004560020103458a0408039681c1c54406207845000502c892407038100d06400c0c84103591001098a90120211039540707182460b82e4014003040c45031055141180e5210121010544070b241200d0041004610a10417810a410000e840311b1001c44111020540c030f010010725814045209403031030740c00814440c1c042c0d1850322809079102c0300404080d800030040103104019510700c000791030303441e0085601209040c10564050042d5085080c48801c2c405060070030031444101e608001c1764a49185c46c00308079100146801e94031402004a82c0a6003410a140401c0928600c035100c01020b00c100c0032188020701e45000e050803848107480280001d144240003521503400381d5110651400301401c41c011400d014106007119070010b440f00b0381a603403100240955507901030a41608803034111811441e128034100000c0450025104d02d480d0040030100850740140c007980084010029103082d140c2d55041c00d1803160081d03106 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 69407106 1250 69405856 69405863
    0x30207200907020f0a030804050705060c03040303120b0d020f01030f0e0f1507020c010c08070203060a051611030d1d01020a030b010f090501020d0c060e100c0905090610050903030409090807 83
    0x41c0300042e6190300c002403221581640c0000340c80820783d01d803011210b0203001031007510588a401c0c0d0028513030b1036010040c9005030164004d035840b44e08610300100821800496038461a04107206604150740700129541c40b5039040b11800c0c0c01d201d24034010303170150060101e0341c10810318100810082c0c1c800402d0021049507900243c41c00011100140603445d03d0664102d00103a02087e2903c64650040d003101c6d030300d58041c0240c1d906004840d03000a1078003001316400250306448009000c0c1410040c003e4012268003820100007480000900c2c2c2c1e5039026000840c8a0b1a440d4904954400070b14015104001c5050b4020340d511586d4100182c00381c4007251100c1c0c0000c444048032a605031003808d02c4015208140c0c09880c1445020b10121285c1040c03640550368103a44140b103c410407400c00c030200c10a0143c5e400400e01390780b84140509000d50661010340100280410070006a8a0000680c0d11000c81d091003a110400c03c00031918500030b542098030000e180002140c01c0c0516100907101302e911 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 69408356 1250 69407106 69407119
    0xf0f0e010b040c140403020906130f1a03150f0c04050a0e040b01050604030b010302210109061d21030a110a0201020904050c0403020d0b220803040c1d01090c03020720 73
    0x441c18101d0b1031031130301103000c501000248170510040c94a58025500040014440c00810842240060845902c1042d0a44180d82c54201040e20305a1700c0c0038400400741140500001c1d4034000c0c0020410300c0003006e0840c8000700b03034001990002604203031000b42c00090301109015440d603840d050707450025142a14103642d140f000296601d443c1c4c00310350030349900c941100c8a5918503800c0c42031101e1070714000c510340303801444090303020b001c2407007102170850040401140080c030280804040040c402080c5110f40c00911260141c80703021901c800d52512006e4900d42d90766200d0101d80010101a10a5042084000b07604029070b07505402505290720111010403c2c1d0f141d00030b001425109602c00203400200c01500140800d288400803603215540d140621441c1002412003090401251400c8680080100c240401e200034903881d10090034004201d03500e141ca110a0f444000301d130510a84c44491348622540744d5041c82501079804090340700341380700801c1d600b084910a82c080c00d008031601a24 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 69409606 1250 69408356 69408371
    0x1e06011403030d0c0c060203160305070305070203180a0807081005010519060305061906050403060b04090201081807180209120d0504140319030e1008040203100f0f0e010b04 76
    0x202610803400c0d050340010021450f00001100c004040c00501000e00300344552240300e4400301c3e01a0004510800e05541d420170019012000038040340c0b00601a03c04051400781004a069000000c0381d045030622511008282003107000200a1801e170b0b00301020314081c0c0707000090349400010364440d04268424090080f0b0b0b89070818000794003043d400c01c24a0030701c44001007003d42d0007940500d41290024001c0254070306d40040c9698481d0055100d5000140005000c00a0000d81e114200034500100d60601c400812900000c01c0d00c2d501a026880308005041c8080084500300100001000d9800108000c080c0d032880390402900700035910303406800920001848018003140303e4040d80d180b5211079090908040c0358a5041c01d44150440e018402c001048070480e94240c698410503109640e0600552180010b12107552012000b40d001d1114020034000140da011510510040c1c054900186060001950402910050114400f12440e000780302814100c19045880781c0142601d0911808 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 69410856 1250 69409606 69409619
    0xd0e010504051504150203130f0b0907060503040b07111504050106140108240102010209130504210e010c0f0b040b010821180a050a090204090b180412030e1e0601 71
    0x281214000e10700c50011011601c01e201d41c1e1b0141d90850211400a41d0070368250342c805071080002c2d0341c182c0e2030b00c800700c0070000b080d181007007d000988680d00e0202d00f1400c02e680c0d001c462240246c90b002c144160f541c030081184004001802490707201b0f4124041c241403a09015000304001d000b08010810880014811780d4004c0840f58003a80a010b003c1c034100982d01a048038095034250303801e0441d5002c02c550390041c1c5e940041c402400609850000d0907081526080b200084008803810318103025441324480c1a42003070328941d00040038201121594041c0c0b4086058505208005214007861401c3c00144541124914181d4901104681048030b008240034075503101600003800500c0c00300000032120003800e02d6002c0e034040241440d0221500c440000c1c0c03a50b2a69002101148c5c2d001c1810480b9116901030501040ca003901c80c4450902c411200c1c1007003110050002e811410324014030050b4601c40d5001003d804100000d0b01d4640c0700301008005031003260918404c031441240d0011420 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 69412106 1250 69410856 69410893
    0x10302070206030a0b060d0603050c090702010c090603050c190206040201080a06050d11030715050c1501060c02010e0d050f031201080705180a1b030b1804020604050d080d0e01050405 80
    0x19001042c05041d5542c151000c4060f180c2203100d01e0f0084c009214444807800c0500a003800b0303500c1a80038014807a110402d0040785180100304104681c108461703d00401d030041100703c182c49541c6408122566900b050070240c0c8980140d003400140c407081140d8040350702142a40c000c40c400d81e200040f40d03d5090f080002c1e40c07014064281c1c4410709031014400200103441060305248050261000296200c0320001418510511000170a10014034208140b0007400140c00b001140e10000e1555414818010903030240d002c0c000341440550b90450000b65034206868a00b580d1100840e0342d04004407000c0d03a103a801030940110300a072604004074040902140c0302e0150b07000904074100c2d20b00b070b20541010465010f040f1940b03281e6940d0005940c1007409145d1036a040642d200400c1c1460003400740201d4022007080b07505c610a259080c0001030369410115800c8420459151030170388144d0603e400188200641d03c542c55280c411045460701040d0002485140a101590909401002c441e0039 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 69413356 1250 69412106 69412117
    0x30a0f02060a0b06040902091507030f0906030e060606090619031e05010302060a0804080412110109140306010612020c2d030f0306090a060308071b060c08040b090d02150406030b010302 81
    0x140304c94140014002c290b2182c3c040c1103010700040a40d0900c42000061000030303072005506400251140101c80702c1d558001910600501040c542009441ca84401142c0c49020140c0451f204110000d0300380c080c3c2e51010306844c420414404000c0d4404c2e2440400b0f401411200c04e101d070325040b4440300c0c0f19020468802c1d18101c98025200d946001d80074070b022100b103540104200c50786e05040c00045040744401c80d001c5141032041d840e134207000d0021070024161121980c0610022411020005203d0f1004241c0a04444142c10000840044003c0c1032380680242071614000d80300b00070450403140940100a000d4408545100c2d14002289421030b071a84104000c2444401e0200049070f0380d0700b01070520300c1d40080c01900c0020720390b8696a41868540c44074400f40c404240d840c803803114440c4401c4003240101924181918220701c190381e58505802035100d407043d0608049441161901d44503002c0c140d41d54020000c0310440e00c0032502c00d010f90400d0040000103071800b04415415406803007200d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 69414606 1250 69413356 69413359
    0x30605100503040f0206071202010b030c0906031e1c0207180603021809030d0203010902180a0609030807050106050916031b0504090b0d05060a0b010e0901051008070c05030a0f02060a0b 81
    0x180b855440b525010084114040c040360440010411007020520101c800c2044c1c0c00c1c5070f800030584006001c10907141205007400a449a0303000428480c80d43e400080d4619002400e184c1c0c01240040300881c02d003001c0c0b11680e0080d08200e41e482c58492079a012030b100d02620262560f0542d50705007043e070312044032000d000094002c1a002034510502c1c01c0c5001c2c07c1da0005c84601100e00c0c02804d128998140c1e00f080c3c2c403070345c0c8107038020610300310720364072540b0072001e5881c01e40b20843c0e80c84c41d2150042c02c900c4a8400034049500001c4c150042c45800c3d00440701038000941b02c61440d05000380070411140700c03a03600000103490f1081d02c0d122a12100c00016400f41d0039582e0900700750401d65a40010018076600990041007030203141e001035000d000d19480703101030440005043e01d03440000b5100b14800880c0c2e41c404c170349000050000d960f465085442e0021286040307195981c401001751a0360385c40c1c48010341076102c0442e445004652050612079041001da00b1340b5610345441c0c1100040c0c541f00490300b03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 69415856 1250 69414606 69414617
    0x30b030f01050f0f130501060e012405030112020f0a080307050d0906020a0212100f02090a06020106050d2a09090c05040203090d11010207080c031b0a050c0d020d060c020c0103060510 80
    0x6190b40002544c02604000513048401c804102d40d03640f5400c45685078803502580d680000100b01d205404840101004424924103107210302010b07000b80b00b440140101944400305134003600545d1520308516140c42d60207002c8904646d00e9502881d070325000303144111400e10500c80d40380072140c0305d60704c2c03507040303031400c1d0010910b1000c035070300304103e00f00b07000c09581c910710555840e240449445c0c0510340000c0703030132000141e0351031503401408100f070901d8024800350382c10000300f044143c5a0314848140c85811039000e210f007040000002880403114005021315140c41321010035120740643c040804180300c2d0b00340c03070071041e07451041c80240d0000b125402040e0300300c0d1040c0380c00a40603080302003a40102c2030005103041c81c00d65500e03400d600102030003001d82c0e0003c80d00002050240c5d0a105c1d0f00a428002071a420b00a80e40700c40e13507032140102d00c900802c0000291002c40d1241c01e86070007001e074800703024070001102880080d078602c82c40c2c890500082c1840800121030510822840d0b019010781e899 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 69417106 1250 69415856 69415861
    0x121602010f050705030d090c050103180b040206090915090a0e0c01110111040b04090b010305040816080d020a0302070b0c030709061b0206162009070318060606030b030f01050f 77
    0x107403044007808800c1401e10000300840000580240002c0c04c0003240480001011002c1e400c4c00700185216130003847c10325140004031b0003500c016000c11784103070750700089540882c2e8582c40071815500908800c980c11482890078086101c580c5003203c0d1340e00070117542e00708003030fa41ca00095050340c00507030142606070404030001000e0f5124051601900004e440080f50100416210851961003684a1894000c0118003406480d0060040c54940402481d0a01036428141c41c3c580861003460f60241c43c19020082c0c3c0010401144169040482c2d40401103444406005024010b0b500460040300c2000d00c44002030309a104410569010318440c0e80d40c4c000d4542461410b03682480040f40e0840111440f501c1d1000607581c42e0001e2480c0a4020002e402007100c03071401e0790b50711511462058002a00514048544e203684c00c01c940d01150a00e07010030301e2010441c548510004d081c0f0081d052130b0a181e80400c240d50540c015051480017a011200240c885075172590807260103071240203698000320007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 69418356 1250 69417106 69417109
    0x90c0506031008061501030e0d1b060902030102270a14060a020c060f040303021006050f06030a240609240f0504170607090803090108041b030501140108121602 70
    0x141d54022a5100110070b41502e031441c0c14500003007100c200000a441e110901017030759050080d10a4094000d0062413003100943d00035141c0f100c103d0ba25144091880319080900245130000e84000c0d4000d0000c640c0d4080740c0780b070300e01801001c9021031503601c100300c51003c0d14104030114404a842240c1241c0790720708550100132080d071052026204501c10848000400d60b0703004010b0082c41c0f051401591b5852451401074100702d074502840138501d181207400c010075112104d48900b81c8904070360b200c0d075a590710701040c2c0013004110b80d0000e001c1c0ca10305107101401c540e075052100365480d584408031042c1d903841c0100440340168042240c4080c0f035100c0303180002d0250311005540b440034240107082079210246918445a120802e14480c0d0004041c401c006400548520191000c00041c47c80e0040c80030000c1d0420501a10040c100300003081c1e80c50a2040311455600a141d00000130300c00c4075100030440d59450002c0c001e160340c9024a00380344140220803000c490700c8864595002c04450f00070340 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 69419606 1250 69418356 69418369
    0xa1b120315030501020409020a02060105090f0a09031b0c170d0c08070f020d080301030318031a0606040801020a0804050c0103061514300601141c0605060304150e01090c05 75
    0x21401d1040540520101c00910280050005011030b0400142c0314550b1150091400406070b100600500c0c94100740041c0c3c113595103a0540c00380107801302207002c400e1032808481803503030340c140200c52407030411b03a0703800f0846100f60340411601c2c800581c8a8502d002031025803160914540f80c000301b540d21283d1310000355000003924016000d80c3c40440415855004504a603d83c05011901020000010300c02c064004480306007065000c0c0b40c0090550540d902e900e1b4078003903407004071040e01648002a0807540c6040445000d08082d6000707545880704080c2c050111720003502c081b10140900200a55107501c0383c4111421070307540100d600e100300322081c030503904020b1040240501c82c1c02081880310210034007440c1009410b0b8100d08004402a0300d5241550b580054902410083c424a01260300080b850644520400f1105110444221481d00310f0040c00290f1041384c000c030b0040104424010240e00b82d080c1844036250600c45406103401c00c41c00c803100300c1c50050540058100a010508150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 69420856 1250 69419606 69419621
    0x70e13060b0a05060f04080f0c130b04060f150e03030903070e0c0702090411090901113a0507090b07030f0305060f090109020a0f0504050a03080309120f0a1b1203 71
    0x50b100468083d240d0004c11013a500903105042034880028080081c01810003d00000c240503002070310107500c440d4000b500c8001000510b52910303881e84800c03e280da40d82e0388503000400805000f544030030740c0c2e00d0640d4100e01d600900300011401c6400002c3c1542030102c21124040c0e001406090340904000f1115a00030b4040d04c404034845049c0010750058503180410340c000c1e4041d5175103642c00c515420412003103d2004141040e50790511032215025100d00d4251001e440810b04110b072500900e440b03844150b030f00d180300749a4401d000c410843e1550005e6010602880003990703500c0309280c5401d641d00e16480f40c80c5c0024001040314505044907442540a03c0c2c000030018030001d40c005000d000100748a1013078001608255000075404406a00000c00740c24801c03e0b03040650910707262400007010a030317040c800500311400020000300071010900035401700b084d0001041d80c80d20000c0111500c15040f10800d40049291a00f00c10410680780030460341c100e60004418140c102c1d014811070203024813 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 69422106 1250 69420856 69420859
    0x10306051806011d090d0c0222110a02010c05040807140f13060f0906030203120c011506020732040c0306050312090406090203040201020a080901180611070e13060b 72
    0x1000c8010310508010b000b00d9008100d14000c3d00c01540009020300f11101000d460f20540d6031200b54007090303c1d03801c0002d210a05404407000f90890303000c80c00640c03418462040e40c0303504030305c1d1402c403040600195000d40840300d0030394001c10001c00c41240c10395481c496400360f10050391048000700b0001100021090310301030003500c08981200c8400110300342c65040500302c00401d1312204c1c18082e00d41c0c074040d20f0000b0220180c0500ca26841e5801003038444106120121010b9800140041c40e20801d400104070305505040e0301d0441070780d17800001d4031b03000140681080710849014564588180c5903c0b8002c000003140b0501090803440c08000090103215011424151a04000a0340f42d41c14055100c81c220071a800c295100381e10b170300b000304503125504410032580c414814400941d03800101e80034008d0707001045554602d500300041e1a151400301085a000b05141404a1000c1e03000c1c580b440e140d281003003246c02071a1907008440100384126000c0c440fa0410415800105400d0f80041000080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 69423356 1250 69422106 69422131
    0x1103070302130b2707030e0304060c0f0804030c0b0703090902070b071b02030f011d0a0803060d060f060b040302100201200d0e010c020304050a12050a060209041b02010b0315040b01030605 82
    0x10794600c89130b40c141880282180401003000c1c0b590580a10319002440c0d10145140a0a04034003a124507007003503028008000e1028810100120740c000c03100a1b541068000083c9561000d01e201d06600803101100018200da00c0016860041d000b641c005a510090f0030180d541ea000d0100c50031100740300c6e0540d80390150039512000d030b201070184140e0b00f0104400400d0030340c02c0da41da41610250154441500b94007182018011441c28800d581d00000c04846000d0415034504000010b80203106500b081e89251017800103a4a1741540100200e038426140b1628403900c0c1507081c2d080394400922400c0182c007100000d5200c00020005000141e050030b400911624200703251421640a01544c2e00541d0000034140308074a08003078044001d02400c01807140d1000307184d0f0348a0300c03080b0b200d00081c5086e80200d14051240c1c0e4680180322607803150b054941000c801c41c0c60090103000c0445c5028064080c540303031000800400a0700701e11868110445048607403a580d02c0364010500140b098940c0741d0b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 69424462 1106 69423356 69423379
    0x60f050f0d0b01050d0e0601031a090a080f0f0c071a1309050a0204030209240409210e0d0803090d030c020d030e030c0313031103070302130b 62
    0x24407501140e14401e040c0140c4484c0100c882d8846440c1c20038521080410000036414100d07401140c018034001119030508440300004d41e14036801c1d400c803e00042c041a1002d0080918468900c042841d000c8031005003811a0000c2144103140d03000307200b04001440c5440c9a012215121031612458150480203454110704c0328416010746c0c68a520001c4c1200c95550306540055402500000142c502080801000c85412041000e034a2142c0d12602c550b01703040c0b01e903402207079006a99688066103944860070032581d0079030402c1080703004500b031031403034076a48108828644100d210944078140301449908200110051104251031721802c0c0b01110b60004501d0025407803400d000941038041a11182184030b000d0800b00365120001b40100000360707007180401247e0084c00c03070501000100c01019142d940b40d100296220b06c8003242080c5e40200e42e400008030102c010410240304 = true := by decide +kernel

theorem cover : BRFrame.Cov 69244606 69424462 := by
  have h0 := BRFrame.cov_init 69244606
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69244606 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 69244606 ≤ n) (h2 : n < 69424462) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
