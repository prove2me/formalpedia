-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0042
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:31:18.534159+00:00
-- url     : https://prove2.me/submissions/a1fdb807-bd5e-4884-8384-0c28efb8cdbb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 7374108 ≤ n < 7553964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 7375358 1250 7374108 7374127
    0x50c03060405091603021c050a050a03020d022e0603080a0c020a0b0703020712050a0203150709050108010506090108070203040503100204050a0f0e18010609020a020607080f07050703030506040219020703030201050c 94
    0x202c841e405c0d0b0b42c05960700a4000c0c40c1a56805d112446840c00500e9031080390201030a100d0b001c14a03202e101c3c400c0c0e00b560344400320590200d81d41d8070905983c0710124070780380140064a040626050345280c40741e0012802c2c0d031362504c612444e60000d056120128001284020440c589900b05c10054001014114202007003614001d44c3e40380103000340c802001048101c038051101c10400d0070380903503005007100c40000074200c940d544480c050f00d210003c1035801201182540c02815114183e400203083c032070400100100440d1030b00d10140850055000400012516031428081c1200000c4107580c0540c0c3c0d185000288081007001e80c1c00599980300c1204107104056210391107075000711503480c00300300110ba49503403a40148002e41c080b8407a40c1c400030301c841b80c0395008a50320b440b50060ba25224419600c2070403640e02400e080340c04038002881040000d0020780258851074104074003400c0141841009003101400140c0300b80803e0141c0c0c8415000c20030581e09000305540041c0d1241618140314504 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 7376608 1250 7375358 7375393
    0x1e0c030c040c0e0d0203010b030a0305041403010903050a050304020a05030607091e0608010b0705010f020307080109050601030b0108310501020c0d02010902010903060b04141801060504020702030705010f0210050c0306040509 98
    0x83c03600f807044009100d03104c299a402d4002c2080c00e280141514242d031003910780904144d21510501c0e00846604840e2806844c040c8210300c1d04640544440b4036201403040120360303660004100b00d900c001c4400340420140c40c100050740c8140c0b141d480d5080a9410803691929488450703000c03099080c0100c50512074198007582250444002d10714460b11440c6528080380500701010361403000a10110400240d2503208407920b04030303405808100441e8440000450076240b800401d140071490040c013040d6900444190400c2a502e00409641c003600344100d24040b40d10308040540b0141c1d00070030121454441408103180108140c002000a6809507001030608100b41c8001303031000703135201d0b201e05283d01d035500080c0203800808400710480c03412071110090743d440081440300030b40c80d242d00801e4030f041c0f610890301040c0d0002d00900086213480011509654415501411406103482820213000940105030283c5400d00c40f25480c0e241510900c1b003101d00091a150980e80100300c400b00c43d0b50007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 7377858 1250 7376608 7376627
    0x702061317161401080c0c010f050105130207050606010809010207020303040909060c0206090a23030316030e0309090406050406140403030605030d080423010e0f03090a0605030108120c1e0c030c040c 87
    0xa090400c0e041d0f031b451200c50242d01400c01c1c0c5200b15400d040a181190142c2e5006a041e03600c101c0ba02e0f1800f141c007070a0801280a80c0300020301540c02500454519030082d400981d100c5c40000016103040391a90109040da000340e40a40b040702d4a400c645010800700740a032540100f0b0b00d00c010f059500e44419090360f00c6006003c00340103841c0c0f0120880128900178828154a604171084a036a81002603c0e8000962105070a0740007d151040141c0b44400210440d208202c00034011070702e42d112034480200509000c0d10031610079a036119031044032191010282d00c00d82c043d441c0011850310303100a250030710311408996010089074504100002303d81440807101150701d2200d0018988101005174010500d494100b0154400c40c03143d1201d100e03002000b0040010242c402c554001e079134100550ba140070078000e980142d0455211142c0854070710024040240080d0704176010105c110b9a211040c041503424258140c201042410b40b07414100940f081c00a02503808124280c4002d800a00c003044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 7379108 1250 7377858 7377899
    0x150212010303050c030403120f0206010e0709050f04090204060b0706050f010e0a020d0b060c01020d0b0301050919030203040911040302040b01020d05030a0e0705041a01080901020a0503010605070206131716 90
    0xb1039100c881303000030003c1d03401071a880f035044401c903014040003400da01861449800188a004004a6030180c00030700d050080b081526503034010340c100003c01c01c010441503460b41d0095952503070b88003d0303034450003803000a240701122a55118040c0c20a00c0039900700a01c0003d10ba41c0f117100400403d0700c821212175001418174001030f203685031048024040d2652a25460b030051000c41d284103170102c19030081c00c00f4042403d0402c01c0e0b002c4070040c1803d80e1000c5032101c046402038035240401c039014511400314540300b441601e01e05512981060100c5943c0b0480c80c217403c3c40450309004604280c440c0070b0440009000518404142c82c00007403407444014421030f01c694603251054040d641c100900000f8010081061000000010210240000b02c201c0c0e030b0700040030303003021803503044040c0308a400b0042641c0e81c952a503800c164040c0c50300c0e0312840e422030304081d040101205246446840b88041c06030312840e0351508003125416840c00c0c1c555a25507060401e41c130410080c10aa50550b4160f505 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 7380358 1250 7379108 7379117
    0x108070905150405040506070e03070506040603021b07030503040e2802091c0605061005130303080c09040213050f040b1f0201090b04060506030601060f050a12020c07060c150212010303 81
    0xa403108020803809442c0815140c11500f4001400104407020800600c101825070b10304070100004810076946264038801e16411800c100000d00010703200e60004d20401e00750741a08000211001e89151400e0010380c4240c83e550004241030080d0b4012404054102840c80c1101107036120701100e01c00104400100d8120701503000508000070b841d600030a482c20740060803803d00c1e140c52414214080d01003110805e101d402940041c1d084a801002502c145250050250000d1401c559080da00301201408820041c0d2061181803a07950303950008000c0e852003200ca01100c00e00d40006e0192070107560541c0d61107030342440400c01082d10f80a40c80320075144440c00e052200d41c1c0428040e40104603c03039000e0292070300c0100b00b00900c011034010a00401d0164201e030150703039072220106c2e030a410000c203a5000410420048400610070f4030135140c80d60400f070300103140101e031698843ca0300c0825405800030820322107215081c080e00300805500c801c00508203500e40398641da1608500c51050200a00b0301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 7381608 1250 7380358 7380361
    0xe06060d03031b080a05090f03070b041e150b0105030115031503020909030a0f2a03140307020c0109091a09040305070606030605010503060901090203070510050c030409050103020102150108070905 86
    0x5407007500104161241d0240b90f54400d0620031005004200c100c500b864410700701008140c407554001a0310b00c01d0700301000135504000a583e40c6184540700580196016606502080d68201010b04504019841002c148035040c08203421801500d1b590400e45052190920040045444401d0280c000303c0e000d2900040c065603203050007250322201e41029402104507820000258000402420048040c0d02c0305035071200c110408881444000f103045d80301e03650060303400526030031a46504144c584681850a0301036180600d21086070421602070300141c1c00504809a1075801101da4400351201420500c600040400e01e807070212403420121b80a1001600001c040c5845241030715010f80e0f1240042c00003e80e81d00707080000d40400c0c01030030304c240998001f103041d02c44c052050307000c802c1c1e010b0060150f483c0303000104407403424061261802d20504211045007564240003d001800511600040719415400020314061011801103042d882e002d0042c03040020000e800c10483da51182d000c200c6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 7382858 1250 7381608 7381613
    0x1a0d05030c06011202090c09010e060307020a120206010603060605030f01060509120102040605070309092a05090406090e0c0a0303050f07080712020703060b060405010e040203060f120601030204050a0e06060d 91
    0x3144640180c214007400380710004500c1d00d0300c1807013010906008848115441d21000032803c22031003243d0101d0301050844404180a041100c0a0740d4824080d0040c2d64840c031403510b03081404000c031404000141c004070014410560103210380341c0031b4001490700c5415454025009010f1000c11b0080c04280500421540460380e218403000c5c6090031020000c1d92500e6948002410503040000704601043c1030300400b081c0c2d180544914402407030b030300403104040813070700c1028000e0110704025841084010081074141c3c1d16030f0300502000382100c503c00628020150342c010f040042920200307219044081003000030907400401c0c1c40000100240c86030b0364403030603e040841403285060040c0901c0100303030308410141d0042a0301d401c4038015081480042d0007072040017101c1c400c90055038040b488039480d40a20741095405194020005049401060f150310006041c12076a0954810030741c0c01200140300318101801441d4011007441e9040c00400710a00030282c031140c2c020080c902590042e82c4c54010b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 7384108 1250 7382858 7382863
    0x1202011409040b03030409060806010b0c191e05030403020306011203080f060604090f020310060f050a03051003020a080604140304060903030e0301060e07020102040807080706050702060c1002030a020901020c01031a0d05 96
    0xc0020300901710f0741c0d61661503132920301a140620801501d8001c0e4000041d031006070804440032104418040c208482007500e910308040142c82040e0b03081011501048108945004449003850140c00250388543c618130401d850715205800070324901c450f40d060000000c0d0004c7c00550070a45400d10f10280e40c4c0e800c0c011642a002d00c1e806276503428200314801103c0e14440e4000c60142401002c258000340d15504191030800c151000000040c20801009d41018031a07030103c5d070080311a0514404141e543d400251300f1268a40000710140c200b5002c1c03008018116180c441e00042980c003031810310307260190140044201d484080d0030301403d0704145211b40d4080d4000300160032040507108030342c05e113003100a000f90014080c85445200ba00d401194128000803090101d81c0315030f40d12840d00100350700b03000d0b540c0c01030760014030107100e0ba80f40300001e4942c500282d441a48210401030326007086800080c5007104005002d4185031030800103038441c01c140c80d85841a041d065aa075042d183c22407405a1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 7385358 1250 7384108 7384121
    0xb09010e060d0902041a040b011107180603080a05030907060905060301210506090d0f110601150504030c060f080c1207050306010c0b040b0402010305010e0702191401020a0c0507120201140904 84
    0x29482886d040c10344140c81c0701942d8410f602e00c4240ca041201c403084c140190741d901d012140c0d0840d5903001c49030400002603550031200c0d8803061142c0200d035555407030381d0340d14080c5c0084040e10045240070042120320b40041040100425230380c07070072114003881d02c00440c25510040c06062081101f013054905007191016804030344541c06001c4800d5450724203180c0c2d480e03081d04c0c0d140d040010703002d0240751581442028804242d108040c0035050507440d04003252403109144a130744080c020180300c000046110f9503c040e00800c01e54880c00041d14552034010500389000300004061b20082c0100b9105107420b1441d07075401110307410034682e83d0b100d4200503100f40403010342c010200c40340c10040004000c4042400c0d806603100307803428005a601c0f200004580e0b0ba0448a060041e4000e8880ea40c01c641c4110b00b4240080c0180d5511250444280b00346099174000300d484804148a03164000402c00c0403c0000c00420b080c0750b40200e040d503d5030000b0175002c01c0d4040a40040c1c40801d01d40e055a860351f0124 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 7386608 1250 7385358 7385363
    0x170d020f070b15030f06060d0f0b09030315040912080601090b040b041e0806040b0406060f081c08060a05040f0f020301081c0207030206030115030605060f0408070b09010e060d09 78
    0x550301e407001c6192450700340e4001ca40000c14640b600d544a0054140050400d00002c090301c05003880343e49010911282d1204200280d030094000311400010880c074a40036801003d0240c0036560b0ba19050092007085405c4042c41401a440c006c1e442000c107010522283d0001d58601c0d290700c080d140c59004031032105c0c0c1a0050101c11400040020702540420020300c01c41d1045503900c0400306005801003500d0946100d42c400c43d42144000070300103880707020700d194482c2c440da400052498555030410010f111681140086610280342009402440c8035170001540103407078081031528040300800c01a5090707124503406580c441c803141040d94195000682180e186c200215100d42e510b02045959004d044644804070050364607020324a031000c1045000d498004c0c00051459181c4540c550f5440d40160a40c020180c1d40c1e800492a969080b004010604a2858144d02d0328103241e1901c0c100038a5500c0340545c80b03000c100c28029a60043c1c3c21030304143c82142c030b8a442e54150034244014180e00c3c03100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 7387858 1250 7386608 7386637
    0x307020105070809131b0207140d150f0203040609140703052a03060c031801061d070c050a030807090605040e010306090f0501061d0705030f040b130b01030c06030b0a03170d02 77
    0x441c1300b01b44821208411038406508a442440d61a08007074084000d40c0d4441e6040070b05800200c0105094030b441c450b5101602d4000200c0241100128040342c000f99030031940c554443c40d071341081c410ba18150103008502d00000e00090340c03544e41c45030740d00c400070100607085414801d030102c80103d100012120b4540042c044d110a850305101a40c115401122040741380e8020400c20141840c0510404050366160221803c00340c901c0140c51440d43d1000b4000f00030840784600400000d10140410b100061107902c0b8001242070882d000361176444550821410041c00740020494011020b07021411030b071300100005100c201314203108801d20780d0310801900f15070070040002280100541150b03403415003480451650b403242c103c02c80b110b01c01903130104a200d41c0800803c000c074203035028a982120088008420ba200e03a039440040001e400d0303105440b00c060441042101c207400d4010054401e20489008001038210b50b0b03071090300342c285000c070300310400081203101c2c105201d035040300c0c040c100c0640c6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 7389108 1250 7387858 7387871
    0x100504020c030306150403050a060b0d05010e0a060506010309050c0d020402070c08070807090207050a0b0c041203050306030105011a03010303030507090506190306050301050c2205100c03030608030702010507080913 94
    0x1029540f80d0095071000d0280049034080d90300407080d001a6801c1d40c0d4000054440c2400a489400240070441580e584c04407458007450001902442561000800f280160402e00a10f041c22012160001d0100d818503003480b60f10380003c0e50209603008180070440c0d4448146059001182c024001c1d247d0003408200045c401152110300010720301c04644548088070802034403090707030714240c0c007a928008109a0100d9045000a07a00c41c466a40c000c40c0c0d5008a81490360318401e084c42c50025240c19404600d00000f07000703660500f0300070a0b001d0103500400121a84401c41c80c80d83d02d01c01440017808248c1e075800818001441600c1c0395004160040c01140c0380ea1100e41603002c40041c100d480c1d0b01080c178000002402c0d003410700441e44030b20100b0034400c1c101107560791400700040d01c0c1201e80020350511500400d40b50b40e43d1030441484e01d0141d4a40c803244040749800303802c41d0400d2700042203651040c0002e0005030303803040c200c4010680c090b901c2c07512034035114041420040c1403c0100302903428450b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 7390358 1250 7389108 7389127
    0x5010e010e100303080f0601210b090f010b03040206030403090905010f08060f100b0c01020405040212060315010506070206091818010b0904051002070f0b1504060501050c07060810050402 82
    0x16058181c40615003116140c1d1121600344460204510006000c0340c101c4002512240c00450301c2c0354170410605080c0b140628100351005000504042c014940d50342d00b4120f007107810a980395541c8030001c80488102541415440521780c000100000d1198000100040803d403140341c0c113000911100340c041c4070b156158800c6c44510074080c010341070903104210008a6406000e43c40500603800007035000b09980c20026200290351001000d181c0c0766400304070000d80350711030384018958644170104442ca241458820035007030181d510441509180488010300442c4c1d0382408079911a58100d03041e80d56940c29802003101124408034159503100103804111a01d00030a610350840240c4a000f080340c0d486003400c00650380415140540642d010603840d812100659000b0150103008444840e0601650f80d0b6884100900f100e5820b40d000d02c0d01d01c1170003181824043d12014100901f8414217003c821b051507542c0d10464418401003250240101d284031b21354000381c9002e00009407082d9034420504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 7391608 1250 7390358 7390379
    0x4020d050f010b09070c0c17160b030403030e0703150b04290a05010903030801030602030912030c04030303050a0504032c03120304020f030f0a0308091e06040303050606040803040501030e100501 85
    0x41c10840d000b076813443c0000e90040d03c1214003401d03540d0f000c0034882c074082c280f0f001380075240041e542c8401c0a215000c0346046050f001d44803000100a1008465a44e251a10340101a030b400c05e01c524007281c1c8959018400110344504440a0340d4030610700240390041c160002e4050001025400781c0c856484800d12880000d08144500c102025244007482c19a10001103822946901c000f5002a00690060002900d03a4000f035402c106004222a1010b0074202e0800303d560042d90101101f0700300007010010103401d030248035030161001c4002c2041b032505403000303000d5012000031031041103151a91006085903406518030b00a00160840d48881c42030490310000d41d00c203075001e038890320312029035000038a4005030714400c0b900c0070400707481003d00c81d5405440c1c0c0c03103020b06000d149006000b824080f51101522040440407024001c3c9500d0426003409012241d01074019801098108018010b08500004940031a4001e180c0044e140ba6158409800c1c207001208046c85030741407800020380300034907 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 7392858 1250 7391608 7391621
    0x60c0702060f120a06080f070915091b080106031a040207030c170711030d02031603020a120503010e0a05010b0405011101240609080f0601050108060d050d05040602070602071d04020d050f01 83
    0x440b1300030089583c0f1040303003c0c2d503185850200c030000c0e40140010301442c56250171010f050000229844074840d103495100007076410300e03980e1585d0b5605291015030041e50000981d80142041d08042100c1d0a10050041380401c40800e954000c5400061040c1094890584035200304d03088400060100281c0300383ca032281c1e0104c90140c130510186200e4400364a8080b40124190055400851411950038a5501e92004040042c0c00b90b0080340c80d00004070301306108840303000c046541d81540d40e40c108044030250840c0075001903000c1d4a41001405003200400488094a2007420143c1401209540f19409881046400515110004030407000030030081e500b2000c0e140280c40740c1c0d01d03090702d60440369510042540c07140610382c0030400403c2154018010b1541118010380844010030594540c203103801d840340032400005100240030020360303605001c81005044203101030038020385410540e181141840001804001290300403c085640707d01c201681703d0f61041c180c6142031380108005008055 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 7394108 1250 7392858 7392871
    0x1412100e0102030105040f110306240c010504060507020c0f1201020d0603120807020a0b040210050c03130806060d080315030307050a0809030714060307081801020705010b030c06040305060c0702060f12 88
    0x4020540341040d029010b5241050b1108e0307000e6085580711720800802c0c5000d030a560b40e6a24400e000c40c1c202081c42c40c001c00090b5900c03c00820941030030300d40102120001481081150810070340d00c5119980c400d81d5050001086030300c510031240d281912402441081c81c0b20700ca1b24500500042009240801040020311a496a0b10150b4800d00141d8176030100e1400141101090340c0041d0042c9041100860804058034241c0d00b4120340d186480e1856008118034a88148400340412502d00104211030b8401d02c15602e80b188240180d480e049075010180041ca01e04001707207480400ca407001c00c25985241d4100003141e000400504081c456507111020040c002c0c02111400704440352100703100c41c011344000e000030b842c60780e0349041100d03c100003800d8175421041045070201440b000f40050701040d8001d0000042001031081054641003036a40c0907030051b00c00340002c00201d100441c000d68480d81100d05142d0341d1a142c40091058460503000724200700001c0361038400189071070b081c2d620514 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 7395358 1250 7394108 7394111
    0x1c0b01021603110307091104060c03020703020a060e030c061c020306030a05030a05070b0f0106090302010f030b120304090501080604031e0e18010801050603070308041401140a0201021908011412100e010203010504 93
    0x44e1206c5c0d000d41502d00c03003142e80c4038445003040200500d034403992850b1580c501910546040c5512940019150f003030303680c411000900444004ea4991030244000301c0d0600e800c460080c81c2003a681c20050610f064108940b00c00fa5000c0001103064070244440300c8165840f5080c1c03943c8062038030000c1d0064004d01000d588aa080c4400034100030440b0f0a91810384080761610b4201a1556004484850225800104140e1607803125401a2504203004c0d41072000a40919200c500780059801210340503400881340764005820b010110350414000b00307003840d04284104840100410031348846d85001d0086400803c0c440c1d008603801d80542d00e95068444090003846079442d402c040507610b003220b000c09080064200810001d55003c1400c04a00210605215030401c603408611522600010110340c0581d4001079000c107170091461400540c2c588609140d44194100076060994a40a0300854040c00150710320450030401040040008042c10906100180302040010302070f4100307224840c0240e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 7396608 1250 7395358 7395373
    0x10212010905070c12030e0106030804080c010804021f020304080307050304031a16121d03030105010314090606011d04020d06030302060705041d04030e060f030402010905061c0b010216031103 84
    0x141c0d80390244030f02504503551103c04d003400e40d8440c007020200c042040e2003455036444198104000c28003408000703600a414580d2103d03c0d101481d030601c6100240e2604111200c0c041000590351100d5801440342a01c1140303001480980c001e82c03441c4642d030015070303042c4404644071003003080000c014002d80f4801c0318082d518100c1c0c0704000c207148006944011804c5010b0240d03416442c801c01e0144403410360090041000300148820317920f04070b00c906a0300b119403c0000148880c1d41c02d030203038000080c1c0149503442e00749002c8020a4640c00042d200c981005105400a0381e00d0900075500c1030802c0c0010021540c41c03140085140061a1070300c8101e000d4050030f80050310150040081c3c0d801c84840c401940c1052540c03040c1c1f6601081300030b000710b0070f120203000401c0c0562955006003802003506102c0558174185400058607000b8568041845003004000d42c15102c400b141c0054280341a5a9001c00c107441a1801030b401d101d112150079010f40d51002000040c00441000d404070a0030a03000d6030002d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 7397858 1250 7396608 7396619
    0xf0501030203190c020c0a0801061a070206041a0405060d0504050609160302040e030d090507061812060c030b030303070207031b0e040201081003060213060201140405120903010b0a03030201021201 86
    0x9038041101c3c0c41405140c00704200b2441c84180d0400001e41c0d0781c501c159102041c280c400151181c031360740c0141e10941c1d950341d010301040c420696038649400c040a081800c290090b40014082d04c610700a104141141092108001c0042c0d0b00b540d01804009017415240c070f06051180d4001c0800b143e0640d1184190b501250403880041154841d0b004501d182030711882c15a0240b101902a000c100215880100600c1903038040a11a01d00303902d10800291072103d04c1e182000380610000700d03d03400b030044844c100b0040e030505440d0343c500440c2d100030046000058a4801d5008000602c060f0b90540400410440c001c5e84c041101c00c00d0728424600c1c084080e01c0030140c1040000d09005a44075050740c0d201080c003541c02a82c42591100c801c1c40951000c41e201e80e10401030781c100342c1da101c5220050103000d018182e02806a801e81e201302e80302d8806249810f8540c2907881051280e84d0015080000b481040c0b61029000304105590140c41c208100c0c0e80ca10b0006d000358442c1d0280c800e0b031b5003c131001189 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 7399108 1250 7397858 7397861
    0x31401021c0e190c0b0702030309031009020901080706021b01020307050f100f11030403110f0304030c05120a110402030903040e01080726060601080601031d060609010b0a05070807060e1005010f050103 88
    0x60302c540150340d4a0320142401c40014851b0701118050341e06110a100c41c2d5150766003000b0303220301020f10041c01b0805800300c2c81801036451041e00020010b400914003030019560014130b544501081041520b031021001d00141c0c00c5100d82c0a02070311900800341010030508002811a001d6001810201b00b0030800020032012a054817140c1214180100085404680318810100b8000c4074081a15510240800c00a10316441a80304480200d10003d0800440c378101d10241440b180380c50180003201c6455a54183c940e905d1f0700c0c491302c00c5602001144905c0380400940e0040c20f645047c180d5a561644502552541c5601c1644009000100c2c02d103191050525044000c181810090134181ca540c2c0054800310401001c650405540301c8084038008444901e58641c004414042c0c42d07681042d0b8103010110300305070481880302104019284000b980320003182e100c5904030030070b5502d840c428640079020305503074186030303107035100301d110820610003103a11043c102d90010b240c8140780c0ba90340e0010740 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 7400358 1250 7399108 7399153
    0x41b09060b0f070201020705090411010207120305071704090e010509100e0d0507060207060203070e030609010e0a03050c0106030602040b0307181a07020a030b01090911040603020901031401021c0e 86
    0x480070000e01000c2d012052100c050b00d1014414010ba411203503c035030200d84044402c980564174448140c01041403075805014030800342c00340d0700e61006002801c0d280600b180c07040b4040103010b020140344901c01e0080106c29940a4441400240000550307090064080c182c01d448403440c500506c0a00d040c0d107903c1d07202d2400390802c540064107040b0036108041d13803a41c01216098451036000c01440000030290310096210f0003440e11540300c203a407039074149454070b54000e000780c0e46a8900068070080d5440018070b03896581d410304d05181c0d110800c403101d0340980842e62004203c3c50005c10042031300300141b000343d031003513507155109611024110001d0095031414442c906640513070030181340d0404044401045914006400e541d003941c1c0c0c035550345147ca0002d900c6495841d0ba249414010041e100b20118480703c01260180700841c03c6400290180e407061200501c4032800c03403085c2d0050102034043d2400004e11044c84030340b09240c2c1d404000030b003440380380d104104d00488a051103240030304850103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 7401608 1250 7400358 7400369
    0x604030201090b03090703060c0921050c06070201050702040c020a12080c03070c0203010b0907030b010318021f020a05010603050c010807021f020901030e0a06020d110406080a020a0306080303041b0906 88
    0x80d00100d10f85164100c642c1e0000c1c0103031a06000b41c03400840810701034041c41051046540d1070030105480c00c2100f0755507625200b090f52000b105030000c0c902040e80000c0400c0c0e8110215405a81e580c11031005844034071a07420300940042c14281c440c000584c020503050021405603041c80c0038581d501c24200e460031000c6072000c3d08000c0c00c0c408a00340d075115611001d8100c1c030140000880141001c001004080c04958240000e501d0307401900c02940e041c06103a0216030580e4420b243e0f920b041e0300045c08020300481c5a1002e0054540685503544204080c07081950410000c010441e180e081136921303603a4011056000c90704550209403118800155500310b040b400044180041341c207501080a076006c0c0c0d0b0b14504041d103916481030151424455285e03c030340b041d10011703900c41e514a903010a56003100400384042200340070802259401003074580d4400c500500c0141d1b20840316106030000c00198201c500c1a1001004000410854030325a02c03800c402c00901c000801d1340c900c21502581c04500a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 7402858 1250 7401608 7401617
    0xf0702030d1d01050f010906081609091a010909020906090f040f02120712020319080304030503100b1603120501060e01120b03030a05040e0f0709030206030601120507020d0e0604030201 81
    0x30507944001d60340064000000c002d24000d01d004800d5110707003907600580380a40c070341101000400a10085104010042c0500000741840c19040300c0900d801e42814401d0300910307a110905002003080d1040854000c515255840c1082d5849103803800c0200f1580320200e003c0e00f80c1801003441458011000c610504242d502e0f0001e07599a51b98211a903e20620100c1e00102c10306444886800e060040c0340260504c48400d40a8003420f0040502d00800c0d940c011513111400080c52002c00d0003081242e50003034241c01c10781d6486e2a01c0d0110142c5003810751011014030408502d01c0c600303a28103101110002d009654100109290b000208110b800c28800d00001c10115003658000f940100480320450702000c600051801040c2c000c02c1c1140c3c811a0300b00001100050144407030540c3c1802c5a07040350800481120b0fa150040c0041d00700d0182d400080d20442c0044001455a0b10035001c590b911403034004c080c4102e081010b0007a503505050701290b000f245c54a14120054103120050b501107a070169074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 7404108 1250 7402858 7402867
    0x5030c0604151e090512030115081602030405010516020604030305030a1b05220302120a020a0801021804090f0218060a090212040206030402030a08030408070b0105010206061302090315010801060602060f070203 92
    0xf076100061400d681c08030b5560241111107515220400042d500a00342640b01c28850184160000c2c1103010081415420b0441c03003010499541d400019107042d5a0203082466840303550308601c0080c4282886c4c001e5018100080110405a005c3e02550042d07084600038814600b4449104000444c0d050040000030028000500031071200c0322090352000c0341c80140d507242074881d0041010f041143c074089419502481c0741c0d000714280580303403100600790980210308050514500004a40c03010881074807858940c101c0724140b0090000b05680c5690051100702034000c52841c1c00840d401c201c41a520942d0140c0000490240c02d000b01c0d258504113000051003981e0715800c00a40da000908140d0701840703003496400006420100071401517004007103003900c0d01d055160034041100141c100904540001c003d1004680315951b00d4001d0084c01e10015849041d85d80100f490045684040020900240b0000551038419442001550b1850f4250b0300c06e55240c928a0407141d101ba580301d03006034001c01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 7405358 1250 7404108 7404161
    0xb0f010e041d160618120b060121061401050703080f040c0e01030b04020306100501050706240303050d0f0603170903010f0203070305060a050a08030f090d05030c060415 74
    0x18005003000c0b040c01d42c07204a20068403440362401c586500c03404146a603400003072000940014130b01c44510040618040500d050000e226401d81c41918000e100071140004075411381c1c000c2d40f64017010410204000d00c26162003041741d019004610034002003542005d02e01446501c5441101e40d803075003503250009103880318442110b5100c0c009000703403022030f1615000304501c40309480e003a000718010a02c500160415004150a1000c0500105500c0340c152400300810398004060b0340426402c9500055901e050a2401c89a007042d1b400c0b06001800c42c0c040030040507005006004c0e44038220104202c030307100060b65030048525900003c0c00381140303000400c529042000003890b4803a4098008038466001e981c502060341c0046e02e500010070348600800115050118402004210403102c40108901d8500903980346d109100c140c140c2042d0001d24480b0131f4641c01000020940e00c6412a952040c18041c0075032106002c3d00c0484180c0301c0c2c080d01300240f0095020321a0352140d0050790350420700491 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 7406608 1250 7405358 7405361
    0xb131208040302030d1d030105040f03030c020f0105090706030f0509121c02030a0615080c03070c0302010908070501050f010e09070e070c020a090606020c030307150c05040902030702030d0b0f010e04 87
    0x908084509510420002c00180c6040c400180300d071040c0e444901c0c9034688541240307019640380d080203000380e1401c410440407500d004c0d90f00c010b0740d4141c140054158141d04041341061b036000300c0010381c0c1d0f080100380584500002071082c00c5a129030303810800074011003008016a01d00780e4041e9601d91040b903a224114845000510341542c03040c000078004200000600c003131381c001302d5140c03c03115920002080805142c02d01d0b1240b0356114035081c442c9280005003001303280000b4050104101001c1a8602018000d6215078000c0b500304901546905091526074080c01084400100856814000254048184a46602a41c10381014003925803c0c11004003404400a0030b030000c222030b03040c0d000090780f50020481e0181c900e840011030418203140000e8902440c490140f070290380104941d1021584e4041c5611851408181c04100100306003000c03901405681c125500380c6100109118409800000070107841107c00020300c1034903100e500704540c0368250f0002ea404105018401c1d074051405 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 7407858 1250 7406608 7406639
    0x1903020108061f080a180507030303050604020d050a050a0606020d02070b07060f0e0c0a0605040303080109050615031302100507020102060a0e030c01060303020309040b0405130b070e0d05010504020a0b13 89
    0x10b00300d0000e03d807500c2040318030300300c880010740086610b0000740b1030780d10b54034000c142804110000020b1800c071030382d41e11aa5100c040c4005010503a9503008181301ea81c50703030107c848030700c00010140a103003042c8100c18010304046d2001c001c41860004001181800400c00f404480d00d1a0054601e080c6482c80814495220300400c90707071159203035080b0b43c41c81000d202d00b0a003881118011705003a80328500380725070301089030461002c1c4001440b0410000b984100320a040d100b0400c004151604d40602103107103041c01c1c10341150741d00404801c00240541582e41d03c001d1034001c03120002a200120b1041d1010710400b40c01a0068101e80300184440010b90072100641c1485400c9901d1b0100c106065400c60312582c00440040e080010700b280b25181900440401103803c8804001f241084101c020400c0701d6203030010500052007000800356401202407401c01e06024000c42100549407070954000c24007200d049108060000020603c2079403e420350311582100380d0074603402814607500c00041a203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 7409108 1250 7407858 7407871
    0x10030308060321030a0501061e0309020301090b04140c04020a0c0f0c050a17070b04121205130f15020109050607030b13060803040503060a02070201050406050d02190e0f1903020108 79
    0x60107003034008070742d681050f001460070b20201c50303900c034184045e404081c1c035010303480703101081500a001c1d02081d101400d80404d8203954100003564142d10720129015044906014141c205d19a080005002c448003031500030024032070507a5054040101000101d018039441500024440d0024400140c031000454000b41d0091a03101102aa20000508280515000f18900d00019164000780ba01c0802c05900944080007540d0b0070035007001c0740f00010240c1640007a020320101174403a10500c0c00b440c1100c4402048001002800340c41e00740700e088542ca01d1090400c0c90303400e0000c0c81c1a0030310605c51040e034550300ca00076001c981c0781d580c000c038042d01ea00c0c450160f01a40390702032400e160b071803489600020300b145000b55403907900d031404140c10324000a1410701c0c280d004110707160040c0e0b4030a0484040d50300c1ea04026481f507940c130b0311810007402204485940d001450401c0c0e445181c202d412100203680840740c81140c03088908c14080c07030100c0721840600011800100380015805400d210f6030084 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 7410358 1250 7409108 7409113
    0x20402070c0b0901030b0306011206021309020c0a12030203070e150d02030405010e0105060603040f03050a0302221406090a0e04030201110703170c07030509010309080405030109030305011d100303080603 89
    0x3819a200d000c240c46a81d407101020a03000030b074a0300035507007500444019100440190003150300d040800403000107400d8000386041e03800241c0c03146002000c0b050101502c207007203045440d40c203854080d9030f8605481c4010b8510b144140c034101c1e1418800e00071270b485201c0381c2d910304a0b0841e1f910140080a040e51f403038400074203402c1c89030511086891000e18807960050300081000704110f01c403907085a0019052a014040400820000c1035681d800c0c007810f541c0c03614000d940d410300080118024040c0c49541030299950000100c0c0c200d5600c0040800d07075001c07105820000e80f4039002c20109200e010201c0c5e401c111a02420403040c1c41000781e43d94000d003c2e0002003400c0d090300b01d07115110361000d003003100828119103103292044401200c45601c040c500a03001e01d80041e81e10090098082c1b10340d16810191148100010800310b070040d50010f10001d0003c0c44620f03043d180140183c4024050100c5640e81507489220f03a0010a000074099401051007840c10743c21030f05c00703c4000200070040364062 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 7411608 1250 7410358 7410367
    0xf0a060f050609012102070f0b0601020f0d0e030c09070c05060601030513030c0503040509181203070e0904050a050105150f0303090105070b070c0807030302041d01060906051303050d02030a0215090a020d020402 92
    0x5c4a180020483e8038810f0302c0d10040c0c0307402803600300c00b5600041d148504540c0280b1981000ea000040c1410f02e140150416144090040c0c001030f103040c401e2861a60092012003e00c001c05821545074841207110b101900c80556543c4011011110101c4041245c00c05100904001c03d0266140211060107242500d00d082d03141c001045442205941031840701341d03400d11041e0900c4082c440206482280e2403d203156044c050300051190440440303180c0328908540104e003c0080400c43e484d04264171000910940c03800d000c40101310180103e401e0300800010030102d00c145404811244607010507100d240c02c100390381e00c500042d90001080321040c02180e5054402060b002c0d0090288030340710360740142e900ca007410311012000f030500b100800522543c000520003d038215290000b42c44d100e150950301c9000715a5400c2207104507a20241c482d002c0d01c940c542c1c1d82a404001400f006805400f1a07800517140d140c3d6801911048a4031141a0400102c40e001840c081551030b200c0d5000510140c00c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 7412858 1250 7411608 7411667
    0x20d060b04031a0108011503080c010e0f01050702010608030405030d050a050c160302040f05100b09030c06070b04020108011203021b01260103021c0c05040f06030b0f0a060f05060901 80
    0x150740660419036452541059822030204994511070162400c14001e026514240b0102c055a45030341c04010280b12000c295401412400d6001224000040044480440b15500d007980240010f0b505000103500b040c00110b010600003080703904540b800360040680c00c50349001192107800120030101003280c204015120141c0401444101049002400d0011481d51040004035880c442441c0c5d6068100400c011480c080d4090740300c104c80c64244800d42d90700801c4000390800000000d6258483d0011603807509000d00141ca41c0c0c4218800c0c1c03207103c0140d0b02d07001d07651110302d0014001001a480b40d031016001c5020179001b84000f200c181010128a030303000c801e6106522540c00750408407074030780f00100305525110070b402c41d0304000f4005042c17480049480f00c1c81d03400a18043c503401a601e0f01d44c4d95034400d059a1000c0d00941e0000b00200031420281100c035620315042d500001d0103814000089048280b0318003890860303100620081c81c02c00d0900040d1070400e00000721041c114070403a0000788 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 7414108 1250 7412858 7412879
    0x1080a0903030b120304060305010501080702030702011d0a030803010504060e04150c0c0b010612150803070204090f0203030a02030403200a0e06150307090302040f020a0804080d060302030a030309020103050f0702060604020d06 99
    0x502480c0013000d140c40700d00b031100017000c98005a0205040005400602c0501138010007107415054081c68110084541c1c14403101e20120044189074020104a50000a12400720003a6040c0c2c1c004403805d000d0203a54070a0b1030191403091b038024062550a01201407075510982c041c018498060400a23158421030700c0300d41c0d82540c242c1c400703c00f1a06001110124a540384501c039012103e14514880c071505211281e40e490113180d000070b016540da40c8041d000c1c040720542d9065038036030007011a980c8081c0100000c0d01e940003840200c8641004002240706040c11801e11040310501401e450381c80c503e48140040e00031006045560803240c80d05100415041010055220302100d4440340c038cc80b81755206110031a9642c8510a01c0d9610500070561110303407180c00c098000c0d811140e100d40302e0000c49852002403003d50300003541841416405010141c040d040001401e000341c80c2008103550307250307401e0822101120440010780120000a5181c90302c2d40c050083c3d100804400104039485010402 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 7415358 1250 7414108 7414129
    0x314071a04080703020120030c09040207060603030c02030607110c0607020402091002010b0307050d050c01080402010215010e0105010809060403080402060c0f060103050f160b03040f020f040518100b01080a0903030b 94
    0x4a040c640081c0f0a420302d42c09000e28150080c80c0b5001c441e00d1255203500c3c00c2d2900001c0c2c59081c0240c800900241c19650f940c050b100040d4009400b0090310b580c0f480d0103440301406000c124001c3c041c0d0380000e078038513018030f0410507100c05480180109441c2041004490347c8014004c82e4465800c0c000e034501500c0390b00c0c18200e194040d4000241005070320007007500e0110294031040c498029650000c1c001100880c0c1072580403000c0c20049403541360303840180d013132855807400c2d482061041e13000000c1410b02c0201580c102ca4083c0c90303014203601c40c00d5510341c844400302c5015010400f444089001800e0480041c200d14200c1400d840e50303900010b4506080050030b0740140d440c0d501444801092000c184040710f4014152003401301118900f0300808a5804000c0029000107000c0c0c0e040c105544a405103082e070801c006000300400d14159007041d41c5002c0c1045007580920034103a205581440c244252082940141c40d4101c16940c1c0e00700100280000000807804c041e00d540740365109494803d0f164 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 7416608 1250 7415358 7415363
    0x23010306240206061e090403020a0b1501030506040e030a0e0609120102040e060f09150102120307030203040c0506090f0402090604080307050a05010c0206011202060304050705031207110406030314071a04 89
    0x540c1e54140d03010000745800d902605142c404c5885c038649007036903455500c1800c1e8170710782900d594040e40d84a05060342031442000010b007152030000c0402845041495043e000540262810000f58440c201071000f02c03500d100584c0f034164001c00c015522907024156480e000c0000604442c036190342d4030b000c1045601401040c44941e0b401007410b00400345001800341e44564180c60410300c000c80400041d0b83c84001410004119038840201400c50340701b40314401168529216003560780c00c000a0080003540110b500703480002a103000481c0ba49800c0003103c0b8402c00060000c80c4803941c03501080300035400710081c03980c030480812001501100500c0030b00400c900038405000461010300740142034482c64600d4604640024005001e040120600d080c04184c0541d081900e81e034070351400c0d501d40142c64110075454030074840605d4030342a4010007800700e18450003900c90b0210f030001c240019507000d400000c02103501910741204503902e80000c1c2001d9802640d140e03c0500302240030208400701500d0030b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 7417858 1250 7416608 7416659
    0x827040c020703020a140a0501050f0c01090f050606010f0e0f010201020d0e03040e090a080a030902011106010b0a0212040e0a0b0102100c08060907080f070e0a0b0301080709140123010306 82
    0x82040d8506200b07011700500504021403194250240040c0010416020340d6051000c00700e42d0808082d22141a03848207051440208440021402e00c0c0903460481d40c000c443d60701c5a0000103440d54840e2101d0a1800084d4031415017000b541001c0141c7c03882950409811903500b07012413001900c0c5406204120300075034010710f9075982410780c0500441002403140c8210340c00140e01e400015488012980242828a40041c5d0450f551004903018845107003040c0d100d100c2c000011410709100c8000345000110782c0c00f2264081c024100f0b40400e4096441440d0466900340e000840c42003194010004178041407050f40d40e2805082100c0b000c40d01c0038019040050381c52000c0051030b042000c18160001d10783e080c051542e24044641101d500f00c000d042c08100401d00c00d4020007a00c4524101c005030400400c1c0c113840c0e603110b6111031750b0f41c1e10611540320036034280312041e0050b00106103450f040c0c9001c00e1203000002c9000c100c1101202c00b05030030038101a40c501b0f0000f00030311301000c84d02481883da543e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 7419108 1250 7417858 7417873
    0x406060501020c01050a0203030105061e0304030e030c0307050d0b06060f0301090204050a0f12020411091002010203090705010c021005030c1201180c0207050d0f06110a05030a0e0a0827040c02 84
    0x280350040f00c0310401e0500000300a10b89005400200760390440311300b01c590a6441c1c0c03034a202c0c4000801c005000d061103040c048180420917400400c0203513201d009404a908500582007059034078401841083e030880d20f10200080031543d59001142d001001810032460301c2c107914250106035109030300c44001c00c0d601103014800392419020500090903000102280a030900e10b55030242510102c0c001d10a541d1445d0300c8002e05485070544180040042c600c03200d403c1074007400f902070740c03049440c10654054020046000d40c000c00303900800d45d402403c9207280740f800410a43c0e0320790024085240b1010300340004000c0d0810250400d000e01641d941010b07026002e80744c20426542c27a500e17140c4c159005088280001d440704d40c4508034403a0454a03100780000c650610100800300c001d90001c2c54080010000201900000154003d13400480300f00451000514601d4603001d10035002400c003441082040c07860303070b0406105421030080120450b241142400010100e482512a03074015812481 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 7420358 1250 7419108 7419119
    0x120106110c01020d090608090f030406030606080a05070903020d050c030105040812090c1315050607030305040c0b030106020c0402071407082a060901030504030c0f0602120124030c050702030105040606 88
    0x10200d070700e110080c00105203040003214094050307001070144404203c0c0440c0041c0800f034007040125408034211042d130340c0d101d803580340080c00b8003094025078000c5082107001c5103000c502842181d204408542d604240f490540d42007062540c030b0b150058843c3d02c1048002d04081d5030a00c40c0c035000b144074540117941c54003480c2d0081031207032005040b500b854100110803001034031003d010001c4264904c100080708040601c25405408081e08615040b00340800e02404050b0540e20941c0118051300d424455170381e0703441c21a006d900c000d004810068001011465007420700d070f0040c0c89901d20502964042d0318688200515000c2c45620102c4981d0100c00d1402c4080401640c0f10f03c00b0010100e85590003c0c9480031800328420209004c1c10595114000380038188209000d070005540910045040003583c10704a000c2d4100a03c00e5100c418454000640040c952114101801e407042c1e401c0e40100001ea0300f9801040700b185910700f800810009031005a8007807085501c0b0f94441e42c00020740a0600c2d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 7421608 1250 7420358 7420363
    0x150c05010212041709030c0f0a09111b0604030e21010203070c03110f03030f040519060204031109040209040f170c030310080601030201090306050a090f0605060102060c0301050a030609020612010611 87
    0x2000008441c044c10060b14941d41c07008602c2c0300150400f514849840c0d40e00c2400f040392151158040765251385080c410600c940d2034080140248410103284030505008000e006446000c01d03900100418009001c8100d1400c00f00c46140820310071403048056448880042400e9038030480341480080c040d5080c85c810550018117a4055514000003020300c0c01264001d140e0f20b10000d0000c40400303606000140c10004200000c0b03c010180700e49400c0a580d01e890542c0c0a0b4115020840320541d081030042024200310819a101c1e82c0c00030441500c60300c0d680c580c402005101c0c0c40a80d41f07c0110840b00c1603840d4414014011079200d800119a42d16010400d0700c81282182c010724a141c001c04010401750380d01105002c1030f00d4000000203020f44801d0060070060030b5642000f000c0301905621141449150b92100e44510001c0c1c080d90025590981d04a4140c8004d00490303921842d000000d00c0400c085030f120000c450310103009149407840900c82d80c1b0ba1190245d0000f00000c418415921000005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 7422858 1250 7421608 7421633
    0x60c0a03080f010617130c0e041202011a130615050403020a080109020303030402130905060a0207050c010201050402100c0611030406050610030504030c14100e03030108010c050c07150c0501021204 86
    0xd0400302c07455040c1107005107040250341c418204507005e03030082640345010480e03108005a10840c0079242c259246004241310030112019203140c8140040803490310300600a480d41a44265103071241c038516802000141100090070b008000c1c0d98000100b096101c0740001c12002041c0d440f07054581349144100702040c1000d07005409541d050549100040e00c0003c00d407900701d0350451b0500c51017040e00303031a10020720020354003030024442c010610000303c07a150700030607035507001d0002d869400400c0c80059007600c0040d074000b900010540783d0080882e00c19411403082903c5094042481d1403407001d480229081500d0568216a980f400d1040519040c003106e4028956400c040c405450940c41c040c00404242401130000c2c00c184405184000c4140b000c0f1250142c01601000614040e0704103954130740090148120075842c1c8120108120b01480c2601c00c000008001400c41c0c0b42007004021320850300940c19002c0c80303440d0b210340c1b000403828005131481640610ba0407400d45000e0610350f0070601d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 7424108 1250 7422858 7422871
    0x1a040b060c0604060905030d0c030c080105030606030706031104080f010c0206090a15050601210e010605010c05120f040503070306020a0311030402090a0903111501030c050604060504061805060c0a0308 88
    0x20070012085200100700150b101c0c0c0c020030006041311807130501c1c178254480c00c08540100343c9410080102d941c0c041d8082b400504a941d03030100540e032204107144d928101520a01e5140e8400401044100d10030b801c003020440e1207403129030401d6902c0343d2007854007200e0f9985011594613004004401641041850b83c0415514010089038209440c0d0300c07699000b04110501d491344441c0001e0b070503405044081160509503282c6c00c4000d19198013640149240c00406031079508084000030150b102c4c44021518641203009480003000d40f0384040c4081c1d016030310340c0790540c100340400034450b5070074000300300114005c2902598954032010000e003101d02151b08004172142c180309110140c0c0743d0054036644110905400581c640242c1419242440c001d00440c0301d922034814402e2030340291003003040c12284548a103440d499143ca00304640c84c040e90203104001807043c041001003510444c0c0705503284048220444030720340c48101040c0d0030f9000c1081c2c407540b540a182c1d00410981c0c0720714295401003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 7425358 1250 7424108 7424119
    0x11010507080609010b0d0b0a03030c020301060504020408190f0503070c03050c0409030906050d061a040e13020603040f0f02061201050f01020a03140f0903060a0603200a030f05101a040b 81
    0x64602c0c00908112018050007a45880104044e00c00c010359030b20031007125000030b21540a45680386001095808220010cc1c00395003007140002c0c1509140c025542660101300141099a60381080310b1084540c0d49810703143c005529042c0000b01d002400200786081c000c0c15041d031a0703821800c0c050318201d03083c6441030045150070303214400b00e079000510702c0075500c0382e02d401580c940b1042222409001d140d04280105420a0202103440d803110008004403103180640d00704581e58000102440007503440041d4001008000013000603080a1a00034044d01c202c01503200340850742c0101310560070000c0750041200510340180441d1a00c0071111000d80d609100034454071007140d40c020f0440c41ca00051101c03c44010411454400600040d0b030400c0700301070100d41e168a40f48803603078090034151009440c00322601a1651200c007498601403500a00a000e000c8050b103150b81e103000a15158405807403030700034005260a52500d50161501e4941034000989000410500700011104110a20380c400c030b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 7426608 1250 7425358 7425361
    0x108010e04080403120201021b030a030f0510030602030907090c0206040b060d0201020a03030b0a0504020705060604180503040e06040f020a0801050a120c0504050702070308030f0406050a0507020307020d140703031101050708 98
    0x15180c004a0f01900d03032010500c410301d203286070b05074064003901400d208400440304601c040400004058002d089450760188854403056100c081110790030340d80358000d029010360500108055400031604040d0710b00803104d07190366440d404802c81b103113403c516006801000500041c030102050301da411020454910042100310342c0042d40e0b0f000c031031800070b050589405604500c0e58800d00e06500600029005543c1c9034000d140035a1110821911310340b244e4030b415100c4020b02c03031144040103d03540c8000103510349818003803503000d04507000740f5290f4042d0f02d5802011850001d4000340810002e16110f203403da50400040220b9220700d50070034640303138001c6a0000e0118028030076180c1110300681c1e0006540d00c69005c203d00b0300c1030b00e03080034000110010174030010131084880f003481640140e80c100240c1d192802990250fa6059804d03a0059100b4440381c805403500f14210111644500803000010b4038a002e8181881d03555403003078010902e1402607040301c441c00e01410341c0c0b00c800e074541495039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 7427858 1250 7426608 7426613
    0xb040209011b020a0515030f01121703090109060e0f0c01050901022d070602151e06190504050709080f0105040203070e09030d0f0c020c0d030e150706060801020304020108010e04 78
    0x1059000410b40025501e0319480ca0107544801d0002d6020f040c3c003510500070310082600c0907446a1061f1034100d03034000407800029808590f549413001884d8010410343c0c507032a400d000280795800c00740c607421055517140b00c414009009807080303014401c4600050102000e0110300107082501c00c88055052250070001018143c2e4081242711081110b10080071092140c0d510850007440b42c01c138252804d100381d031404a481500000c103c122071410410150040e51200c0c800e44820304540096940580044007003111071802c088140715005011500c41c880540e5000000d0a5901c10380384600410f43c041380501200c0342c280184e580c00f013442e80003805203061560100390385d12041c0c0b040c3c1e1881040400401c41811302481201c0c0001b0f2010b505103c10314031145850000d0030b4880509000d4440d40807862580d0500c000300c41c03081501925448100d0140d032090200e5445683e1282031840002c02c552030006411344111005082c04200050300c910341480094840801a04031a60f1350781e13104100f100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 7429108 1250 7427858 7427867
    0x606080d0314010902180405040501021e0406090605090d06090b07030c03090503030406090219030303051005041a04020c010603020405010311041103090616050706090b1014060906090102030f0a03020403060b04020901 95
    0x450b50131050042c1da50403064030a003807103458170200c2580142040180024000305401800784041f01d00e0043c1c03964000f802100a00340b20746e10a907400300720703518003c0180c02d00400c040c204028004d0012100d000440c0c0d1407100302d401ea40412210050b00f2020701400c3e50b8544142c010418160408200c00d06164071101d07920b000081000701a1034640e580e0808548440181554104d034003c1c0c0003221036120718014016280841d900c00484544c26400a214a03280c000c0340c00405104842c1c0e06252a082d051101030b500421018100359280c00780040180c590344a4030707009500814055250002d42170070070007510780c01c4d604001514014000d100351400d0228096811840d0310b01c150710380c1030180d24140c4950181e00c40c051b00c0ba80c0b03480c41e04028801c281100910804040307115811894450f24041c00300311502180d01c1e00080300744801000c50524400405c2c0e002c2050048a05000f100f1310242d8003980310400000029402040402c1044800d0254941c940b20490342903080c00f40b060300080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 7430358 1250 7429108 7429111
    0x50d051504020f0901080606010e040b06030402010305070203130602010501080c030f0613030c0212031b030a0e1504030c080d0f02070608040318030605010915080a0c030b07020114040606080d0314 86
    0x51a449480841c085555008031900301031005400c0d81071070340c0c0d030b00036882d00d1340b004817070060109a601182522501d80b900c1449641000148118155151500118020000240618150300c0100021800558030130185001480140d0001c100e0750305141003213040c0740b14400b04a010f81e00038103000b0b19116000c295035a1010900400388101a841d080886c0d003480f060390080d4005211841c00910800088018031100101000402e220709100da189940ca100b501c4a000020300c200114121602e881190503521205403c900344c20301d0b449403a501c1024807140e00c0400c2c030f580840131f12924280c1060400003291450300190442c0d03407034010040d10400340200004c0c04c00542e0717005648100e10a61602d40a0350f04890100001e40e11000501e004100000c3c140b00c40c202c08a42c00940014001800018564054014042d25165a8800c00b1184010b000d42c2d056540b0f8941c1d03856104030000301644034501400c004a681d41c608880c1c68108000002a4020541001c081040c10f0482e002c50380e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 7431608 1250 7430358 7430383
    0x3030a0f020307060f02070302010507090b04140105070506180601080312060d020105070c060504140906030d031104080f1f0b0102060403140d020f07060b01020303150103020a1e09030309050d05 85
    0x256412000031030102e00b10b1181000041a0751302d00000009611384a03409005124400d8001300f0a54131005010384803c02c4031b205000c8041810402800b1900b241c01c075072180c14606042042c01c0072111754400b800c00004991482c90824810b000440c403400800c40140100300001c05503282c83c0c4103040040c0303461401401e140c01482c81102d064210b911507400c990300b041d00501c0301c00c0165261100207190b64024481c08030400310000442c00240b800509007802410f0090007000390400d8a0000d074094149220f200200000900000568000900c40b00c00b080c00541d004d0688880706880401c0344442d540b0300b1101c00b900d010900344840e41c000075003a4205800d410860103080281c0c442c01020300c541112042514000300c1c113006010703a01001f130499903119500904c51080c024004aa880c042102c110b03000850880d001d40295000354020220f01d03140e03141070a01c50903210100864140c01b00c0a807000200644010803c1c03644c0224801e0113400c0c1115909520812a21340558800245900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 7432858 1250 7431608 7431617
    0xb0609070801030303090f08070c0503011d15060a17010e0d0801060206060118091e0605010e0102060f19020f0306010e030616050c0304050306010b040311040513060b010306030206030a02040f1403030a 88
    0xc40502c24814400d47d5126481078085030382d01640c0c509103043d4a018400c0901940c01c0050750a01c3c2c0a02008030495a9030070001007201f000c00c015909650031020f001ca54005100c1e25000c1343d6400121074402c0041800c0c00040703a0803203400109454081c450240808011104005001d40c0d5800f16810303030016002d1030301801c02c107002a0502c0c0401c001ea03000380122407502c00d07000c004804031007030022a0203c0ca001002041d030740b5001969020405000b00e40103030482c00c001180a100c03041703890f0300319401c1d48070b0002c01440d21b051401260321480d07268001c480e020007000b2240d0307480b070218081c525041c1c01502541c1040040c03022880d01c100c1c2e540301400808507010107400010001d84006290082c11104156902c013103140c565841800281d40d00c0310700044400d110b051900a081c052510350412140304145c0e511044001c105511020b410580c58140c000096695030002c0e50092000000050752989001085440c0440561100c46200c0399400c4000240d82d01200350f581078940c80c1803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 7434108 1250 7432858 7432871
    0x100b0d0f0203100c030e0601050907020d0f0309020301092d020105090f03010b03070f081606020304050103021c0501180b01090803090609150403150608010b0d1101020106090203090303040b0609070801030303 91
    0x9081c110701d00f4840e040a031901c409156055415080105c51520710000d40d40e250762030f60f0900c0460341040f40c00c1000f503132040c1192808640b25450ba43d880321002d180005006082d0341c000303820340c0c03070480d4251501c020501c3e018401100c00c070619128080c0301a60011701400300e50001e400c1d80075900050340305911409039400152020340008210f040010143c840c01ea40b1032540451444890258903030a06c45c40009409640100c0100000d443d42da80055081910382401100130350300c1069003910f0241c40702c100066001c068002c29002e056400c414490100310413803110f023200d90000082c2d041182e52a020000081e001c01201c58101068032942d03510301000c80800c9c0c44e50b2109070180c4440303200060010502103456200d004c280a050403d000840da1a00154280c039100e80749145c0c40150074a20707200150004c81030040030794040c0004224580d6514014040341c2084482c465590030000130842086100342409074020790417607400440341404080248600c80501009061595819 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 7435358 1250 7434108 7434113
    0x14060f0406090e06070f18030807020103060b03070206071101020403080414180703020901030f09021f02010b0303070c090e03040609090e03070212010905010605060f0a03020d0e070e09100b0d0f 85
    0x104581c0141040000600c0382ca43c0d0400c505583d40e1040b200d020000b000160100325292084082484035200e00a100080e0360031030300c807840c0c1f903132000d4001c134107041d80d86600195481e640c1020754402c400c6070b005000d03280b800004c00f40804184560428559104200a1001806590a039020750317081c41c4036240d0fa10b24850101c2c003101c1c46a40030f1101a481e200812403400c2e403680040c403030300c0700030f0381c0502410007440c0c004000d03030702c0310500294001c03c000d54005200c01b100e00040300300c20040c400440c120700d02c1404a4207507840381e8402e03190b2540c070172000e1143c403289000d0035150111010046d0f103420b2a106000f007945095000303841030349403142040c0c11804420400c0ea42100d4004155800151020b100341d0300038003039000125400d50a00f0800201854006e0a951201100307843c0c1c286040d0703c0c450110001c5d4010040c45121039960f42400801403010062030000c0c1074100f09101040c00c0c0304041915001030f00031007a050600b00f0400703545545401080900e40c5030302985c901c508040c3c52 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 7436608 1250 7435358 7435361
    0x31e090a0902270901050a03030c0606050a0b0408070b0405060f1c050703020309010f0501150f09080303070201050403020609030c0c0607020d0f0c15020309030601050904030c0b0f010e07020114060f04 88
    0x103030700021a540c00401c0442254030103d00300200d1075075408072a40c02c2e10180c024094011400d200303042d0f001a0001c1c01b00042070150080e0351841d0300c0b4510020700282c07120b001601c204825000303110607200104040c0500c20f000c01505000d85486051203040c14070b4000018098032802e00c56440381000400c40c807411071081c40300711000c02d17143c0741f0901140c540120b00030700a410490700d80c4120740c00d241010a450742580b1586042e180b0b00412010720480c0401c06450030102c0101e80d004100e1910400141030300705102841c040d4000740e00102c1c0c1c40c1001d0400078a4170801502c4050913420400104103100b40020f00c407584034009461a41d103c007c0703400003a68a84043c100034000b40d140c4404442000844841201620102c1f021303001d0001000134100c0e6030b409901c1c01301760964050b400510541c90102d50080c0d01030b200703160103581051960380f03400140c9000da440743e071000450401401580381d84a03c040e4403000310710081001c51400c1100385917696024200c107010b5000e250f080b14040d21507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 7437858 1250 7436608 7436629
    0x100e011b0f21090c090207020f0103020c120304060b010f0215040201030f020d09060603050105100e0103260d0e01060e09060403030507091502060f0a0b06030a0b0319031d03031e09 79
    0x3494051240d001c2d4070354200b003d000200d1007221940b6200b82e02003034545d10b62003660803044e0060096051444140010f4000358016914400c00b481784c1803242c0048500c000c01903104030701c10031002c80c04005010003d011503c2c01950b04d400d42d004081c03410281900804841e500030303024640802d000c1240b083c0c10000b03100f402040807140303091000c0101403000b107030401c1c001c8a01c107030001c0100743d60340d11680c005052540204050340803002c0041010650b045103d040c800c140d000f040c000403044091300b110540c00b42c00e40046171500c0d13103c80c01c2d1205081c801c2d68010070b02500c15050701e1a00c62031342500d545006200030189036032000444d50403407003081d56002500c00300c0c036001441090244d01a645d04000c803000828091080000303101e8213214016007502610180c01541940c4403603406202601c41c0902040e01881881603c092581802d5060402140a5100c1c0240e100f039207182030700c1011040b058503010703030700400c08a10303070101e840c0d1921a2410021406626100c4140c0083c000c41d99 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 7439108 1250 7437858 7437887
    0x8040312060303020c030f0d0507030e040209040519060b03040201050910030e030c1005010b0f0a11010902060708040303020c090405070501030b0a090c030b010216080d0509041b02100e011b0f 84
    0x1d8030300d020003007580014080b041d1100803030484000c502045090f82d6600e491031030600c0007030000d00039400064018840a000c0090062001d030800c0c0e8984c0110b4121541229903602e60180c4000014411100d0704c21034010704452a0703e5440c510341030700080d00034411948801c1c0683d60701003069203554869440541070350050003e5940d18405000110303a101d800c000100050340c6003800000c0c0c0340303540c941140c890150f00150682425075620b816198440307805400e40d87c40d500c0c0d0001c4801170303039103030002c12030f4a1080c0440754a490460070020314002444020a02a4821005201c0490f40009400e0100d0740240b9012660281c40790208040c203031103612007243d07141082c200b0890749401d50071001c40c071130080c0e00b1a80c80180c4003400d11121446881030700001d4005c041015000d0348a0001004844c001a0010132074807001903078510300149400030784006070003000c5090080560b80c0161010f190366203000340300300c10205550050306a90b02048000b4000b0083e0040c680c613000b910f05910420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 7440358 1250 7439108 7439111
    0x20607120e010e0d1203110c060c070308010e060112110c0109080415050304080706050c09100906030501090204081b010309080d0c09050d0305030f0c04080d0c0c080106030206030708040312 83
    0x12403190001d072402070200e049501080343c4080c0540a03007003101e219451a90000c00380e017042c11000c2c40c10313401840200d001504040c02000b4450a0403420003d0902804181c034a01c0c0d030303802d640c0c01c00801441040e00b20050244520040c040103070392000170140350112071036000500e1400072100c80c41c14070810400c0d550343d500780700a0302c013840240c10150007151502c815415520103450800c80d86d40c801181c00a0a1a4091069502042066001030342c00224803031f44d213183c80c0c032810000d04010718100ca20000200c0141c02070080306d5040c02034034010801034100350704207401e055006481d03401020890801c9020612554082c2e031194000b07407411a04100030f29900d240341620715002e0b0055802d904040740c0302200000305402d00f0802c42c55425011341e1118150b89600c0300400c86000058070440090f04240710104640b0002d01c24a40b1403111504c0c0c01e00102c01610b04540c1c3c200c80741d800f000d59640342100030405a01e902045070b40c03109035481c12000c9540c0b24a020780c0e100e400324107001001da = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 7441608 1250 7440358 7440383
    0x307060305040b1305151b0301090203070207050a0f030b0903040512030a02010c020606010c03030b010e03031902190c030201121506050405040b0306010f0506090d05120405130506010f050304020607 87
    0x59416601490182d4081c02d28044259696150302c02d25101c005401460781e403100701c0d54144003c0d20b6860a4028401d11107100b10707030300d074489001e15a4000380c0025403410fa000041c4034480d81c04100720f43c000d00081c0e0314a60440d15018402440c01c282c0d100140880900d840001c1c00f0354130074400c990240c40003c1842c001e02c24120011070782e81d0410601e640156181c4010080700f03500014689108a20594508411303103110340d41100580780d442503050520100c4a91843c150b45c1c04d20140c02c0c84d2190304036140900007820380007854196444039907008041c0c080c2c40040810700040031181520380a0038545008090200c10360010700081000303000010302840d0200700c807541300740244121141140c3c14481610074400b015143ca00070b20030944081c0c0c2c501001c001c2414a600030341641180248514105c01c0c040e150181000061240d0000115000501b444146405800d80700458101a070800603480c2036000a003601c01c0c0411a54180180030002074119038411048031591580090820b000307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 7442858 1250 7441608 7441619
    0x7080c0303070207081002070809220903020d031d03030f07090b04030b100902030f01032a08010905070e04030509010c06110c0c0108060301110906070303020909040f0b01090204180b010203090307 86
    0x44034014051a0703024014000881c4081b4168001d8598a030780040d5500c7c5010b480d0020000034170300c003488800302e8842100b0311000202c001c0c850050458081e4016040041d09103400804951400714100700341208090f100b02c81c2c18000041c0d91740054005208002c507100c00c2401d8130007944036403000b044220005804000c0040701030409000b1900040c0120406884404610603800111a503000300b80c02e210041004c5182030b0004141e500210a0025901c0f000742001410a00c0c00d4009902585d122041075042040800911004084210492016007050b96000700244500403000d0704101c0449843c0040c048140c0c0030107a121041d40d80540d664070b41440b0303103441e044221580d03400314044000290103400c044c052284440b4108070003030325002c1c1c44000c01c60780d504402d0007034080507420700c4000d03a29103c04030400d00a03030003150348524018482c40c0c1003200041c16000101c0c83c034014001003021520a0000c0301c0c1152500102182d03100f64000100d10394000d10713010503414030441c60000790 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 7444108 1250 7442858 7442863
    0x50a0203160806060d0503180a05040f06051c05060103170f18120708030a0503040c170303040506100303090605090d050d05090a0801050103020d03050c070302090403050a020f010b01020705040207080c03030702 92
    0x1140e82142c15600180d030307000100581e403112030b08050b100340c0040200200c00a1022074400388880001d100d40000c58590000c2003c072203001d00e0303412500d031f81c825041c8140d1408061021400e000449140c207902000e50304c980c0c03643c506105c002c2085410b480c85055403480401aa4150100c6c542c40ca521040c482d52285000c0c03c3d00600c6034081d1608000c1c072100f01c4d00100c2d0704400d0703030300000c021441c20062030001c65040d8001442512109040b0001040c015100707118425804985402142c880c20581460750030700001402c1680780741464042000003d030007030304060444000e0b08141e51a065035078041382504405150040441c000c9511801c070254015001e09040c100680c0e41c4043ea035202c120260885400703010203540007021221050010303100f50002e00c2e505c600101515031541e52540850002e01091701c044000c00c9010802900c03460741000039405882c0c01c500203020b40b60350500081c0d220802e6010f1a8000c0390005124005c1c401100105c030100020700003103035668a07203204020b4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 7445358 1250 7444108 7444153
    0x603090102160804150206010503030415090807080601380c0a05060a0501060f0504030507090905070905070e0103110702090103020402030a02090a0f0f08030a080105010c02010e040207060603060c020307050303040b04050a0203 99
    0x204032550101140324174038400507215042c0c1d0005001145810300b407915044030350016013003100410900420100d41d0b802c05001c1d05d402006020010b194650402007070032002d003940090140c40040d00c17581444446c0c256070182d040c1c0c0c03d40c3d50100c3d81e80d90040558500f000a82c0c1800340507440f51006105c40303031a540e0b02c020704840003a62050004000a01c088589110b50f02c0301401316440b400c81401482c28a904c680d040f544100c0c00c640d030580d07450303041c20143c441c12100c0201142c1c0c1900180c0301c55030180921008902403200171440c20720190f0004951441c10b00002e03006550100000305070300101e81c1141d0011034024000c002e074599a02e00c603e034402070340c043c0100c19107030080e0004d2402c0d000402e6074200ca03255110074107142c1c00c1c00011034400d000041d0681c10000c45101d43d4040d40c41d5880103200080c0101000703d12a4114106034040d1110310341c00b10110340c1304000c0b0202188010042d6500b190b0710415144454840b030503d20f103080c21031040030358940541c20700000c401250400c0c44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 7446608 1250 7445358 7445369
    0x50a020f0f120604030806102309030a030801060f050903030a14040503030408060a0c08010e0c07020402071a04020f0901150c020609040e0f01050105090105060901110715020c090a020301140603090102160804 91
    0x7110142c0d914028404500d5032846023502103018803200d00c072582e2200300d0304000141092a01410041c0040c0024503044a50000b900414a04401800b0305548480b40c0c0014101d641040c2c1d15048014010070ba5034070030904940d0422406480e1843c840c0d014104a030014180101201d40b40c0351a80070240d25244143d41c2d00198500e0101081e00c12070180001a04aa40e02c0e01d8038006031b40c50101c0c07011140c0c800401240d120b0350030843c0e60006060385902d03045c0d03103980300c40399600c62510f841441801a1002c5180e8851082c0d500108103440b480e06001c14040010728044106900ca0301c00316496001d0b20b08204d6100e820038048000c00c040018176102d403e01250005c1c0003990f41c40c414840c11060a0159030382002007002988080d50003040d002c3e100d44010700c1181e8201d9a0b07440500c0e60000b8107240304006070081040c4036024542a0701072030b04000c0304072086185514084a04a113807062900141c020781021001030f403008030a5040d1044540b000d0360718005900186000c41c05030f171060140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 7447858 1250 7446608 7446617
    0xb030708070501200601050603041509030806090703110414040204030b0103050c0a0b0913020c0a050706050a020d0305130609050709020301030303020301030b01060e0907080a09020d0507170a050a020f0f12060403 93
    0x808104c60207031540e00f4800c81040140200d03034200400d0110340d500080c001d6410209034515a45048841d02c1524074017402a5105162400c1c410b0030011202d9010b05030104150a0040000540d442e00c0d00f11001c544554040f00c105850b84000728029000f540e00141c100250800000305000b408600e44080c03002c04c6a40c00d001ca911010b203800d107401460b41c5550801b50803410421100400e90050001200440449420348090b9407501d180c80c1d440c0e0050720000d00302050010782a60108014446085141030600c05842d00245504806480c03a201600c42038450400c3c0083c01014000c170000b401a2500640d80c03907842c2d04016000c1c4d802172204035003081d001000000c5a0303101d0521081c100318010401142e40d1100c24040f142d0031405082001c0703440e81d440000c1c005070b0f80c4051880085202d2030143c001306181450403004036808910b90320013038100c008034600003400071440e07101300c650440310803040940c0003000c6030300001c1060890350410f0301c02c042a0302c00c80303000985e5485984280c0d00e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 7449108 1250 7447858 7447877
    0x30f090f1204060507030314090f120a021504081b0a0201020705010c03050304020d020a050402070308060405010501020109170a1209080705010b2d060904050c0703020105010503030a050703030e010b030708070501 93
    0x2240d40c0c00c10000721424000081c4010300c581413080c030090000038068a00860700b802d00c94102c0c80000415550225258011008401d17000d1051144641100c81c0d07a000c1070030003820743c44c040c5d1181512880c408500300b0643c0043c0401c035a0406491210403070000094404810844182d84e807103e006044e4007520a0407000120707984500c001510041d8141ea90605540307865090041c1d485c8110b80482c0d101c0c034101004030b65a01d4502c060318699000e07a8a05c006070621000713000489206800090440e41009001d8010410341e001c0c1f00c09102e03014030384c1030751404000c03411140411000c11350a402403d02d50160b0034031003c14050942d55000d4402003110181c1c1000300b12004c81d40d0f504003111b8007511038901e03080c54a40400d1168036035000d04503e01c2c010b00000040c0841d20304880e4a407104002085074001d140d4248141809054103034011440c2081800d0007510f1800342c40c0d4001c007090f03140d2044d029408402c4d009040140006401c0310007990f111a842ca455468a00985002034035004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 7450358 1250 7449108 7449133
    0x402031312091d011a03070e090901090605010f060203090d030c020405070e03010f2007030203070605010b070c0603051302060c0a0203101d06010b0706200c03070606050303030601080f06010207050303030f09 91
    0x5440030f040718807248100c180c0520399100341d4170070707003004091409220048031401c07016103c9003052482000d000000042d07804291411f40e0440d10180c1000440c148403003400c2c04095000000c4901c041030888a840310707071a01e46000c480030100d00d40300a40041c200f50030f011503107802c80c141881c14407040b0001e0114040c51007800040340e00d9541600c10004183c0340803c100f080200040c860030b0b000b0310540b40f81c031f107464480000b500e0b000c1e4440000c0000000707218081c06095100c02c800740023a45814422801d00c100010611003507040068803d20001a50000300c40c2c08100261440b6030140030b0b02c21510700c10300004002c1401c401ca240d00007080d00080c00d101080401c031903044e00d1040c181c180c104015a00c54000411110401400816012100b40541404030b405070000307a840768000e40d5188014503241099400c140d2005000c1c0d801402486210380e0840841c1d40e1010b4034110200c0305940e00760040349081d0300c1d0f9002903050301000080c010100c807c1c0000c0b40c801c4848138101c445891911 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 7451608 1250 7450358 7450409
    0x2030117030703080c031f080606040b01020706090911040e0403020114060307050105032d130c0b0913050604020f070503040311010c080d0b030a120e0a06090503030702040203131209 80
    0x80c0000f00011541c000048030481900081c64000e0900d10300b1100f00d94000480c12040035050300055005e5100c041040440e01d414060402110000c1c405004036a181c810080d261440c1405030300080394450f01882040d05040080c1c80080c4001d007110145800c04c2c2c01c1c044c0c001c140b00012480000b00020015215080010f8200120340060351124038680e100c984c0c0540302d05007000711050742c41074005c08019090b41816403c0c020070984184d801004614034100300c05121b254030101550005000142da181d131688090011515200001b0800b5035510300080c0c02445440004d00100c50041150002e202002000e130064034400d58560412440400054914080b40040200f600908001d4030224400780e400c0362803131420145c100c412485040e503400c101014542c80b40340010704200d281524916001c40010014455400e04010103030815020a4403481080c0000c0c0c0200c0d00000401c084403403504e58054200d4100c0101044030051800c01400e805980c401c00b0454000d00c4a43d00402040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 7452858 1250 7451608 7451617
    0x3080c04050a030201080a02070b0c040e0907141002070302060a0306050406050603090d050a140403030305040b18100b030307081206011d01020307030309031808010606030612020a061b05010905010203011703 91
    0x1402002c600b45958011038845600900b0440c107681c080c00707014001600c0f070510354055080507410f551210306110218020a034004c00d8403455902c0400200645000840318045c0b00c00300f90740e061036402c0814000c0c1d02e414a80d500080d005100059500412903040d4080800d41e64103c4081c00000da585040042e0b5000c161410200383d0440716003a05003034001c0004001280d21400d000c0102c403044040e80107150810751051300440c0e01e0b42c1c10481004001c00569500440c444c05611038642001803641e41d07070740c0c0c0b880d07021350055035494a074005035030403c151200f0551001c080307990365083d040b2140f0f01200c01d481481c0415803a40c8540540030041d00c003201000c0041e8015401c00107281c40403000b402d6601030540500503010020a820340114055070701400c0308a001040b020720b05403006045a07020f9004483c0c01091101d900c1c010b9070740000d080100c0f446840c04501e040000204241c0d414441c0f070300184a0b629012a075010000190055812504c03045140803018000c400720315201d105 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 7454108 1250 7452858 7452869
    0x90c0a0803030a050405100f020a030e1506090702070b04170f07030314090111010905060412090605030a02030a06170a0b06061603030915181b06020709020901020c06031303080c04 79
    0x14070000f040700c443c40d8800d0f5485801801210480c00340e41030841c003103451044c0c00c920455000210203000355018010540e900201a000300201c03803400e210103070400b0703000d014180300301d0520307020600040c0b00b0000c0320003910740d40306040c7e40d440d42d8440741c112000e880c50480503a809004a00c400184001c08c8000441ea090303110050804a20340c128000c0358800c4c1c4040381031000a41c240100d0000c24451030021501c1640140345030304207070a00c03215601c03e40382c0c0001001942d0f9000e2040c5548030046d00d8010702134600c00340c1c0380c2d100c0341883c03809085945c000c003840c0010701600082034330380042c640e40094091610916103460707903070520030b8506c540c940e000003100c1407900300000030b0b2190b40b01000450007500e1030f092624451044905650020350500400c64416000a05214120204881d101c004030900f0080505c0d00c10013035100c10300380c4242c0c1500341d80880c031103207280d00a000024003800014107580c1d403031030300d840340c1c4130a4510031000f03600041e440400140341100450850307040d0341c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 7455358 1250 7454108 7454113
    0x30e03071205011a03211306110f071d060301090503070b01061106010605070f020a0504051501080606070b0f1905010e180f0619021605010605010f170103030804020607120305090c0a08 81
    0x100e049a40c2c0c1e01d4070b61039585241b102c1d020020141c40500d03580310320010300856650340300b03012102d210342e6103409100e46500c030707140d08100d00800080c8040c10282d8039a0464030f079400c04035079401001034010191088054200d000008003030003000413803040f46069070740d2034503072640078404204100d0b0390b40c800b40501004560200459408604483c14001841d440180303c502159144c030701240075114151442e030b88290100e0740b181e03513640c2c00500307041e80b00d44151030702030900c101629081d8204d540035080d10401b808a00105062003c4400e1203a159007c90900b80070a580da002d4244909030100e4002030381c00305191001080d22001b041c0785c550141c01a00616068590602c0d402d6a00c1c0b80344402c4040e40d0b0f003000310041d0f288035420000103150043c40006100b910b0040054002051000c4040400800315004110460000340135410349805103848079042da00c91000c14642c2c800c0420140c01d2241e01c0c2c0710324601b0b6900d50001c500c6884d0040503200d05086a02c2400341c080f001d40a80d0150340c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 7456608 1250 7455358 7455373
    0x20c090103020409111201020c010b0904021804080c03030f010302040501050105031603020306131d0105060909030304030e01050c06040f11030a110d020117040602040509010e01050102030d0504030e03071205011a03 94
    0x14a021380000504034000c603680500d00840100045150b4001d03441510f4594000c11450783c0c01c00f086c0701c0c02040c0c65007950444030f54640b07039000400d00000b0b0307c9a070002200c004c001c85c0c20b0112110681c2c1c5011421021641c0e203080141c07031010060803d1100702e00c2242020004602544a603050fa805600b00071120114600c0c4400107030041e4000914580d08600300301140940030455003e60680450785095444a04142a4100342542c4c0c000b0541f500808801c401c3c0000303248000200c9a2003a0546000c06020400d000102c44602c5680035003061f0303100d40d0b018401403250100c080041035200b180b4600c121141c500516071504003803400501a404203508000c1d030303810440c1c050003141c0d01c14544130201c01400070103130606c6141907406540e00b03640030134107001034180b2002850140903603d6080320190324200000755280301c0c0da40310038001c0351240b000c00d0030140038441040340c03054000c1c1a1400d00d038482d602c0b600c000f4042d0505407519800c0580c1140e421070072480c100003860016000e000e54 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 7457858 1250 7456608 7456613
    0x3110c01090e070e030f030d060e070302070201140306040906020304061d0c011d1807050c0705060403020607061a040609020702030111030915071115060103140108030d0e070902040321020c090103 86
    0x10105401e44c2c10b60540070341c04102e05028400d00080c02c403020707c08000036580c0d06003100c8810b220b4000b010030003814810000c010150781c010b146d0310101182841081e44e26601c035008100900f40f0580000d000c0f0f4004000c2c401006081c1e0070071000328103a40049002d0f5115210555550f160410656001c104c8051880d0020b001800303503070500844c0541034840b0180319140ea001599011244500060400309004a482400b4054a00141422900c4034101404e41e00003542500c0340b150020402035440b400109000c108240401641d0f034000e004015541d80d5000386000380d0700c6108128030a518142c81040c1e803602c504260381c0076944403070092404107100d01ca50881020085e0010f010300a500b80190441501042194082d00c0da800640300c05080080024050700c20b209505221034a60400620400303000001b13071b03988610401404140c0b040c44070107c50802c19140c10012003a800010048244070100842d00e0300c4401001400018960301a0704a0319540c490b181c0c0c90780505140010400b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 7459108 1250 7457858 7457867
    0x90106050604090c02030405060a0203070b010f03020907050903190309062d0c080c0a05010902010e0409030206060613030b01080705210709050411090907030201080709080a080a090f0303110c01090e07 88
    0xa4642c04e030044a103460307143c50002d0081e400540442c00103030310000d400c004000b0f11400c02801450040c46501c422810b5070700085068400420100400c000440c40041c0c1d960300308084846200413401940041d02d050070000e03c5ca50003400342ca0041090302c039181382e42800503107103c01c8402e050510515801c801c03410455400101c41e50650741c00d0000c3c403154420000500514860501c02c2d000040c1002892001500707031160a03a84e5881186016441c402182d000310f0075550000040306c001d40da0720094415a100403006d0740003e07140a502c03c0001c1580c1900251b0102a294112804841c000000708001d844060816500f00c0e150010302c020003003c04103401840c1c006d8824021504007400220210b21403140444000c80d0642c0040c40410030340d6005402c564200000303241c030300465804c0064281d9205000f650040002030002080e2034000e02c2030444500ae481074000100c08140d807402c0082003031740300c1c03c1c0481d01c070b025980d2502c80c02d600400d207040456130341c0780b440d02c1580e81e0a0700c184c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 7460358 1250 7459108 7459121
    0x60702220b060d0f050a0b030303150307090c050309070b0702010f0f140703080a050901052802040305070609060908010c090e1308030a09060b0d03090e0a02090907120509010605060409 81
    0x115a12a01d0040296482c1c0c2e016040404600d100002c5050018512400307440b4003900c04680949404c80a003841e071004400c0380e42c09031804c8011050202c0c60800f00b440c1c400c1c590311000040703140280224505a001d001140a0715200c411100c40d2a15150200072501c11244020301045001c01c01c080002d0003503500407405003584c01c0070702c0c86148414004081d584045801c4000030711140421000543e40d114050300000010000c02252410b103900d61401d0741014642c866005405081205c800c146070115401b07550702c4070503600020391b20b40010349100828003034030001c02c2c035401b4049240001407041d901e06d130410717980e440d012a1400038000c84411000d00010541c14108504501003103c1074001c1d4000e000a6000244100302814207400325143d49050600c508403c002c000d0220350302c1003020003950700c2c600540c04e075510b0702161813000b403055602045c0c0001c4003c00300a08160003000c100c03c1004102c1c020b000755560010a40e0807251309020315540541d041c0b02c144488101c136030200b03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 7461608 1250 7460358 7460419
    0x5070312060f03030e0112060522020d0905070f1a12090c15030a06080f06010501050903100c0f03050109020307020a1101030906020310030507060206090303310302070603050105060702 81
    0x1e1450715002c0e60b4040c100e030b03034100381c2c00703d410001400b141c0d50344880300006004900e107080008504045c0058000070705c1c110b501c44010b075a154417601c006403070f504072400004082c80030800e01e1941e1403c16150404c2e442188402c90600800041c2c0e019100c070038606554002c44007030724003529080200d0040d54090545410f0b0f00c10701c8000320a684451709010070382042104580e0710b81ca4614109070589209402c005e149400160481007840c800080d0b03c1d066070000d003001c0e503c503503134140400d1801c410600a00700c00d6081c030a000007020342280300100c84444a40d4180011703a2250b00360703400e80c8400e032007040069001086610201c0d044900b003040f113100514001c01d0f400499151181603030402d583d41c0002480d4440c0401c00c01c00c0411512b03000381200e00280402d803410742c1080b40c81e40002480c01140360049162101d01007480240c500e20030018a10414034101c1c2420000e6850301207000c4c04004ca07141c0030000c54145408015200c03524ae00412055000306103544d0400140c0341032210 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 7462858 1250 7461608 7461611
    0x30103031b0203010903090f0801020a0c061a06030109050103020f010903050d0804031e030203180601151107030c1401030c081b0705191401240b130e0901021e040605070312 76
    0x1540041c0e0342801001840741c003c0c0d5642c43d040e410202d04001e0100c8e00e40c0205000d038410040103036580c0d08940c48400c0c09030003071800503480403542101c07000c1c48691b2402540c401d00010000c186500380ea0f1049050324001e80300406002401001905c050807140809015540110b09170b40c1407510510b04564407030300c68905010703059101c1451501904005141d803000c03a0300441004502c400220100070030315101001032815516024019200381c01c1606040104210f60044450a90081107403000030350b44003035143c20843e596030400c03240c0b180301071505000a0901e0301d003400300c51003005268052142d0154481c00564443c5000a1070303840103504948034050003102512907203040f403040301e941e401a500010158007000f0141e007121181400700a04480e44d11292201e0030320507501e0300c15942700103d10b9aa903410582d00d550140ac0d039500c0003025030300c44410007182c10b0064000d41141c50f1450a4559882c0103024202c540340204d0080034005035003807010002091080030040c8102c5a0b1000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 7464108 1250 7462858 7462907
    0x90604150c1407140303120601050c01110301030f110301050405060705070c030b010626010602060114040212040c08070605070206030604020a090f09020703080a0b01170a02090901090b01080106050f03010303 91
    0x40315402002c0d041c0c5031500d0368105450030068a04244200204400101c02031481c04220300c1f0312203803020001c0c1000b8100040881c1050049000354000c40800300000904c3e81c4075a5a0300c0c01c0700e60005440401c40715805c40c036000340000c2c201406100c2c09980d0020252180742d984c1c507801c462035000760809031400c03607145500201060f0501d03a000d01800b080c0da11100749100d81917082927090111103901e00c0c1106c140004102c51075000c41d2490544212500c20700b11207041c840054080c1c01044002403200107560281701c01c00c80a10061f5045442903000d0750955907035443c1c1652280038030080039401c82400c000141ca2803400340c1c000d142c008000e05254100540b20b10440120300080d07040403941c142c0c00500c4806141c1c00140096102c959880d09211824200d00024021260b40d81d044e1801c03e4140c0100c0c400314000c2c0c05803051903402402600030307036a540c0401d80140c01076002460105454070000300c0c40b203104104685070119002100c0f07145034a156012034009411030f049584400035940e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 7465358 1250 7464108 7464113
    0x20607050109030206180c0f0a150305010501110c0607110a080a0506060301050604050103050c100207090e28030c0807020102010902061b010e0606011215080a0b040507050105090604150c 82
    0x4025016060180000088092140c41e02074900540034003849410303a0401d0f035080c0016000568601240400e4421020300c120182c08a1044440c5802400010941400742260703241d05500450403031350300366910b542c1c1c18040e8a00586400c070824156402c41020062200852840301074a0342c507000c050008821b90b55600740e21030070402da42da801c0b1a01d0b0840c0c01440441c0c9000d00545400c1207080345d08100c0c81d491661082d584100c0191280c0c0900790041c42021000d001344200b1009040303088041c80003d0008660070707252425840c80948120350001c024140300d600d101d84905240c0d040d12140100000c40d04d038035400341c12480b022811503498010050042e296000502080747e03901e458400035600079940d2900350b81012500c8400c036840141042f04c0d50781d119152040c0b80c003d018000a800d5540c0000700b05501103a040314490b0310401c640382d001c00420030000342c81240920240d8105079212001150140302e4801815408007044c0320a000d07001014a0f1080d41c3d20a600b82200c800c851756 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 7466608 1250 7465358 7465369
    0xe0903120906010f09140406090303060302090c09120f031605010b04060b0405090f041e1b0b0a170c040b03130c0305010203090d02030309030d0e0a0516090b01020115050f060702 78
    0x4071880c07031064100344010402d034496008400054801484140440e1040308140c881c42d000090014003401c1c2c8607611798084c1341c00b96004202a5030081c16100403464102c0c1480c2950340034a01660062800301501010502c000c03999034440d40b00c800280d0b2030b110510207601584204c1c0f50060ba41c65503141c0c01d569444d1350340c0c4a1840213050450a19445a103010100a1540b2000304000d1603880c0d0342c1c0070800064038417803018031a480c1001c803007401c000d0b6606000c00c1640c01030248030902842000e01256002c0c9450140807585215518141e910349413007100c1102d40c9042d1010483c02400b40b0040c0450034503038002e50341c00b8058280350390000c0440d444000c00c031070b0f941e44152856580003080c803590800501124000d030100d40025450b50030441c01040e624403d2894081400c0d69608904880c400300b440b041c8041c5400c00101c50755034019124484040c420b6204a225035481e1204002941d401130182d0740c429038100362141403a500c0c01051003551000ca200542e40304404103d0340c001a92003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 7467858 1250 7466608 7466611
    0xa1a040905070815030a050607080c0d0203010e0a181a0408090607060b041b140d0b03100c0e01080402010503071107050607110a05150f07060b0406030311070603050108070e090312 79
    0x4958501e0f555081011200400703403600c00b0014080e4001400e402c0c04581c00054181c0c00421074501090f141c3d81e04c80405c070040c01001c103183c0300140000000101c004071400e615000d0313a18010200700c07508a01c48828495808540000d101102d0310400d07602d545030b0301c20300d5540280120f4000d4a404000c00005410754000c0c4000c440e03685d41d808690303d80b42000e11034401c0a45001196541401907070030040c1500600740391000c0d43c031100003184c941102c4950022101c2d808044c04640c0303e68085860786000e4030f80106100002070454000d14080d601c100e0700d0311300454068503428a5030311940402c8650106540d8a511b5611800000042c1a00e501c0000c0500a0244010141c03001d092000c2190002e1035600541c400e1101c0071485012008404c2241c0032540f002004560b9010b5030f24140b00600240c81545600a00e0480000107154000c07030107020414030001507a0f0815203800d4254104c8000b80610803065000e030b403041c0b11b41821030f070010f03405c110600b045030b08091101c010814181c90 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 7469108 1250 7467858 7467871
    0x9120302030309010e070605040504090f08120a0f0b06030403030506030a0b0702070602061006050f0a020703081803010b0d0506070f09031b050a080102040501020d05090d050d02010b010e04020301050a1a040905 92
    0x100104003e0108801e00c282072444a222000d08000744ca84a0000c04900942c00b445100781d03541c0b9a01d80800070702c180c4540d40c0700d034000c40407521a40c0004c60152002c00469903541528200031403074040300041d124150003507400411183c1961510b403011001024000c10542e010b10500c502500810034950b10325100d04175550003440d07042c0c1070080007420580040d109903800c44c603620f41030086a8100c01603409607080c2c100d20680301c4c0c510102c2285405046d0313001901c030340c0c0c000a412068842c42c40b907400c0c0c0e0b406e054000f40b05502903d0140034440034a07a1015089400030004039a51520034102000103580702d24148451030b45948420180d8a540c4101440400f61a0303030030012400c101ca800c0d001003110100031070505d07240c030001039216242030180e0010450005002c003629900c404000807143d0700030b01199407504260401034000c28441205502107020030081c441c0304d1403d402141d0590310081d00c620580c5150900d06c0001102c10882120240d40c24030021400003040d1048912818 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 7470358 1250 7469108 7469113
    0x2070812010308130905090607030207051203010f03030f020c240715020301030501050606030c07030f050408010906150f081b03011b080717040308130309050301020f0301030c0f03120c020109120302 87
    0x40d191840c040003280c0960110045c13904000811514140100d409a030100782810007581c0c40c0201e107800303802c040050141080f0541c011002041d04480b095002003628407035143c0000c22100b150007030380d40d034840c0800c8541c84800480444001c0f014400c40c01042c501d01e80303840c0d041000c10340c0c850070b05c908801e8007000e4150340803004005001d02401003941203039058415a1035400c02c40c0c030300c0d21a8410303464003800f84424615000041807140e8100d400600049000700000c07ca5031030010040d00078801d0086401d01c0ba150017054040c080c210510881c0e030600010005d01ca07024541d91820200208119410f56a07a03901e0b0350030241c2c5440041801000d6902c480d551320b4045800781c170285400c005071548003d084200310009400840c090341002802d1002c0c85200c440b494129101d2920b40c00c0070f505540017190361100d00c0c41c034002550580f07215504112119440e8100300a04040c00c1c48080c1402c0d03501c000a5002600506282505c81d0040c035041c2c202d643c0b2042d6240d141e4083c61000c50059 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 7471608 1250 7470358 7470367
    0x15060f0e0901050a050613051e0108030c010b010306050f04050a0b120a0b070507030e0910081606080a0b0f011206080105011203020118020307060f0201020705012a08060901060302070812010308 85
    0x700742840b40551004031001c042006007460000f140951611210614803165290003154604600f00300102169400c04050103880d03840f0184140c603a000441102055030078858840502e41c001d01506c0c080c1c5101030a0080c030f0965580810000e010003400a80c0250384d078083e0070490b80c9540c0ca1a0600c44401002017541c01000e1400b0514842c0080030340c410003005100005c0000e90000340c2e070700100022035a130350682c0c4580d43e0041e07034840079500040309440b40380880c0b08910f103520000700440f40961144a269038440071803405507113062a030340e80c8c0b042c0090038550842d0700900161408001e10040000d1054540940d40d086641c203030002981354200030b00e940b0030154240034034a554114604441c0040388580c1c0400c3d9502421f0250384181300407003440d4a400c0e4800d5040c1c03105580c00600034030100c003007c6560268031684c0b51401c400c920350343c1d008006507070180e0b82180c00f402c005441d030000b907864544101c00035041641c040f01c3c41e0344100001800c6600089440340618010101e4940c1d9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 7472858 1250 7471608 7471621
    0x9050a020102070b0418050705161110050301030804170a0c0e0609010512070512010e0a0f03080f0106050313110d061406040603030507020409080408150a050f1315060f0e 75
    0x38903c46500121805904100901020700400078919401c40381550201d029200e40c1c02c103903514050344840b810b40085201c5d52206000c0c26014400c0360100680c0d10391040c2203201e4080741c03d0f100902010740180c20800c820040f0180141c044d0704001458002d40b004020903969803040324210794090310414040e001803010794500003102d80d00500c000c035620396038110100c610355180c0d1514881c8034450341542c4040c8100820a402c011a0f40385c080b4181d178181c6006241c22b20a8842004090300020310030340c006403681c040750200505031002600d07414115510704007803841c00307901c590041b203003040f03241f600903000d4942189840190780300b601d004c00c45d0305a14641c0c1c03144400080146200314282032042010a400404a845068060300c02054000060030040017510459001400d1441600340341400850701c6041a401160035610a02c4187c40d8035070b000f080400c09880040d05d908020540c0e00000303400b8400e00c40b400c0454070020401e0750340d81000c0e8a08100301c2d889002c0960450040256 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 7474108 1250 7472858 7472863
    0xf010606090305100b03010b150403050d080f01030b07091205010b0f1c03050d0e061008010c0201051b0304030207090203070201020406030b030a030801030f0f080301091e05070509130b0409050a020102 88
    0x25005500c0e00d41d030740310700d15142d440c0d81d0041c07002d04418259880000003a41e450070b4000f0300c1c030400058144000d4402180a8401c00c2d80984400e540707500034505102e2101d03105440450040380004800c4007941d0940e100c40ba0604d2024107a1401d1040da00f400240485e00a0b54541c44c503805100009241c12014050085401c10100312a116003201e2001460000242d0312002c2c901d130701032420341c1d154600400c0000092002007040502031158004002800c0760200c5100f060b12f000d000203115203620901c0aa0a942060380c12a0040c1403245903200c4c910f9a40000e16806402231048a03621550b45510804991094810400503500040c041c00559054001d80300380382421340c001c2140c121142c400030030300078040c040204072000841240701880031280f03c000c0c101d5007020215a0365699000c16800404c1091181c40d2604c2c000420180c0c41c1c4400c1c030806104034101e445852400d42160100312429419410b0340604a9840c56507808a1f02c0d548542c94425201d032004210424070350002a2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 7475358 1250 7474108 7474121
    0x60f0b0102010c0c03050f0a02010e0a0602090a0902040b03060405070507020a0f05010905030f070603021303080301080c1503090604060e010e060903040317030108030403020d0602040803030703090b0703060305031605010b0306090f01 102
    0x1c0c1400b8501342058002035004c030840d42d04480c094041900c4005420b012805042d08184281162103640c0505050014903801011906000c48200c550030390f4400c00c09099008a21901d54805c400340005180d03400c00da00041c1e407040302440c00502d8041e0366030000d90030400c590010701c90402c101600348040d5810281c41c00203400118010810b042600c44420307500d10403402000105078020421504041d01c1c040940c6c0a135a02090307d603240d603118281643e923020112a80d9204080064286250900841c1181d000d9803000c0c000c1c2c10540d640f0744440018042c001e8a002c02d5640c0c3d4040002403c07414000c1c64000c010b40809955914910304004840c000c00c480035000b1080100010804a50700004031000c0307070340c1034503c180410f41c2c50802038001c1c0140e600202190100208010116500d5400f4144180c0310b10788446094440c00d070114204d07469030000400a601c10003910400070701d40b01080e803619104400104a6103d80300109007003080c15141d5624170390080416140c50407003030140d039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 7476608 1250 7475358 7475381
    0x305010e0307020a050f010e030d080601020c0607030c02040b0609030a060212160804031b060c020c0102071401050706020d0f110a090905060105070b0712020301060203040302090f040305030612030403060f0b010201 94
    0x840c00c02c8000c1d00060070a00051080920905012404a103103034010009061080c000a040d1000040e0003600503103034040c2118458018081d1302803114081c90000c041e0f4510580655994803e41072981c2440000c00704aa00313183c2c412420701c102c0d0b51680c2c0400c80c0441e0684150005030307c520b8a10b4207040a140090000c440c040014600390041c3e5603c8402c4c035600076003500e40302100440421440060840c816405842c0174107001005000b0343d000510044000401c0e421648815640d1240011020b080180c1c640018801c1000d080420460780262442c02074481000032103020908a880c100d84c2c4a204203402e41d41e011480c2ca0503640c100c0740c1c400003084956810b00c0300b8a0024002001881030940081c540d81070000415495032182141070724040248008541e20358440c2c41c041d5036600075102c100e200b44c40e94000240c90307900c60350056000301c0d40342d02c0e080d007136403520300402003260424802260313284014031000010401a000300301041e40c007600006132011070740000900751440c1900e40c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 7477858 1250 7476608 7476613
    0x60911040f0e0f07080703020d05040b160305040819020f0a030306030b09010c0903060f0209090702070f08190204020702060c01020301031110030507120507030b150c0105060d050703030c021503040b010305010e 92
    0x1041004181c40c1c2c1e0f0907904c40750707928201001d583c402405034002c0c0150014400c00c14038107000c0204100f041d6140d14000d90501d4028064040b010204809a0354100c2d4010440712043c440342c0c00d84031011350300c51514040c0d4010f9655108005051501e48210701c0030a900180d11100c08000b8821030f05070581e00018104000e21a1150964026081e208107100042c155903560300b0021180c0c4407075043d50000c1c10b0080c482030080c01c007000000d5952840e4010070404044001d03000500d210300141701c0d0f881070342602c4000d10301b902680070040203400941050341c21507410006604104400c0c8000c5000c0c40c89180101140e4030740380103024049040306038030b00906240106203d551038202000121010000402041c0f6903901c900c11000b41c4450982c05400c200c40412200c1c21240400142c0118020382000708501d5840b081004026130100c18050800d8001000600229218403110031140e400502150148c41c5c051102820f598011141581c02d044258018401c000082c001d240550240c03000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 7479108 1250 7477858 7477861
    0xa060f0c05070c0e0408090909060609180a0213090b0a0207050706050309030d09020411040303020a120e060a0c05010209090103030c030e03030405061803071a030106030b0a1a09010201060911040f0e 87
    0x440040c034070982c4c001d0a1403200300030002405c00841c8012a0000c14001d010081182002c2451030b0707554000b03031030301441100032a0000d101404414101c8030380180110092625a01d01d80901941840020340c41005984595004003c9a90360400030300540e400003005030340d222039041041c1000916000a030811104009104400c40004195142c40c51030450006011190b44000750042c0180024900ca1460100300002807680100c2d1005081d8094280e00b4940840d065044840040c0d00003029400030701803240400c818032503114050348a01c90000180303084001400070300e40c10800d0b48110005201c8400c44000c0581c8000803240200050740107504082c01d100004619024500f052800d01111032040001958200580c1d4001c09014040400000c2c04041c5021540e100f40540c8000c02e05140c1d444d0400d09243c20400c0c02c403204000461103210b00e004510110354803240305d86045648904020038001418803611040043d1904405d5450f45882000e412490300c6a2007c04041160360 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 7480358 1250 7479108 7479113
    0x80f07170610030906060f03020a0902030601050a08090c150715110301090c0e040501090203041e0302030d0203041a01060305011505040b0703030209011202030c0315041505040b010c02030a060f0c0507 88
    0x16815a003050003169901c2c2c0c0d5030740c03020b012001064414406030202e42000d00015154512803510810344c1c1c02030fa80100c600380c03a07184a8040e44000e69a49000910810942d01018482d40c1159000307121038094070100310758840003414102c0d4411808084110000d8590100040381109154050040380240901c14142d14140c2513400144200d0055585840b01c460f81d06100da07200082e450302c020f000f003103a0358641154100a4008440880345000f10307120a442004800c1002a00c044d41030b8010b42c17400c51450b40310406501b014000b124140c2c01c10714200c004420042605000e01381d541d030300041d1985040000074960541090640520130200424001c00c2110003c80c0d84003a090305000d40e4402c01440102c071071105140966180510101c103000006003c50b0040d0f01425245455805116081081004880502e45000d4100031030613808c010a04044d08281d082400505213410002d090341c01103070501c08584002c844140c0ea60911808400c0244208034081d141c40c60714500b0070001b81d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 7481608 1250 7480358 7480397
    0xf0506180c0a0302060a020703060e062a030601030b04060b0a02010509070f0503030306060c12070302100f0624020c0315040b01060c05070303080603011104030803060a060302032403010f0c080f07 86
    0x500020740900000540c0c46c498500801101c4c2c019a441070703003004016401b101d078584620303041e00c0c91544030000b0010406103d21400000002d003440710070303031407450700e840c2e005500600384000243e805c16210310300010400b0031038014002603101c3c0c2e000421340d450505902401c000c0603070801890283c405a003400161800070940703a01c0801a9140c82c0d451108203521442c10800d1010003403c03000003d400e07800c06601040c44035090492403024848444181030f008261040b60003022004060020b407506014022001704104012130b005492043d05c00401103410301459461038611182c581050200700000c0c012034500400c4185828001d0140c3c0f81e0b2400c4c0c8036841c40c48003070100880d450105a40d43c2d820b51180881c400340d100c04542c0c4d142d41340360020003a001128100d10030520450000344590080c003c40b4441d0001680c4802140184a030071140146240e03940344e059943c500c3c100004626501c50000131040a40710411303546000907144840c031034024801001c0000f4500003140e6846c05 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 7482858 1250 7481608 7481629
    0x61809030702010e040b04050106050705100203010509040201120e03040f1e05090f07091508040302010c0207030c0902130306021201030c12080a080403021603030503100902180d020a030f0506180c 86
    0x910300404190700400002c5c000d003e8510342c955005203403100001d4180d80100c0104940d9200700192940c0c04043c0305c0d4001240024442c480d0424402da0003d801588914008600d020a08400013a012112084c461840d081a0003080504507900303c2409101c030b400c01c1003250a0100d1004039021420580450340d491809491000352043ca1800b251005005a03c00e1014201e41448042c00d0b1440003c018214031055601341c001d54030300085420018800305846080e04d07000b00d010350152b0f1414220388025032040e00d401500ca6550500440029803c1c00102800c41001024501341c1d41917080c01e04082c81298404005880300c40075400c0081d2980e415a04605201e003004007950399181420707410243c0404070320f0078200396804e0100816801c80091809030003901c011881007501d40700742504078800ea144800c080355a00768140d0003460580c2c40c0029040c4050b102c0040c0b15580d03a01c0b1141605520021229030b0052004c2104411040714507521003070445005000608a203004034041080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 7484108 1250 7482858 7482863
    0xf050a0909021503090604060501050f03070315020c0304080c0102011107150507030603080c010c0801290a050c0a0606031101050403021003090501022106030607090f0b0901090306090b0618090307 86
    0x201c800c001000d65640303040111100c590744494a5480c03400358900741d11010100c0c0c0450381d440c68100042580e041c41e26201150304005002007454608503220110f4406801c0150780010350204015426141e05201a00040000030001c20305214840700280c25244924403900c41c056040c0000c10201c1c0242c602003d98541c10500005d080e00c40c044c00714040e041c6500050030310103000500750052070055101c010990442e0f030310792016980341c90b2000302c2440301c0007072168030785112103601c0b250200400c020188241242002840c000c0604400c0b41040231142094806c1541c41d4410010b000340e800243c070001c5c900b40307070651070a0308541c0091f02c0b040703c1400b070408256a4603980410001d02750704845c0c1624102050807061181c2d03107144000940101c2c1d54900a00440300400c4410b80101078802c140c91a01c4104c0c000c040c2803501c01740441d0404021141003000d645030010110710248145a441d50150489c1140ca140042c18015801902c0500440b421308903002c010310b00801100380c405055 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 7485358 1250 7484108 7484111
    0xc060403050d021201030f060c0f02031b011401060206070e1c0b0403020c130902030c0409021008040804151d0307060503130c03051005010806090303040308040803040302030d051f0f050a09 83
    0x42c034904035802401010131003480601030500110502c40e1541d10703031190a215441c14040c064070410704a411540b060040d1001d07a009110020351040f4a03003c031641950300d000000349245000c0795294000c0401e078000e00140e00001c0c1070008256100c8003c030440d89095544c000c3d0881e02c90114050500501c1014101e20484800300c1d003050320074000f80190b040014003c151134078201041d8802040241e404074420b01c0740c024040e086003004d00480354000d8004180640c18013281c0c0040d9400031006008a8446d00100070114006410002e0344a45550a42d00c60403420b031204c0c03030401c3c3c001040309018071a60010030204001540700d0104c07a40181c019581c149000010b1500c0c0e000015280c10081c031074041e480c252004be059540c4024104c504000c02c030780740c5844105096450788410303180a00040d080c0e03000074002c940014000e5801034072a00c102c80c5801c004110700c00849100b41c0b441c200480582c0d441e200c1135010390800c00d02a08490388980c0c0c110345420005443c441e814841d0940341d9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 7486608 1250 7485358 7485367
    0xa0c090c020f01050a02040f090504020901090203090a080a0504050a050904050d0e010c0c17070e04050a02061602041404020a09020c06011a040b030403050301050a090203041a0a0b0d03090302040c050c06040305 92
    0x251080c4030242d01d0448403002030046042c0800080080d40042c010541301c2da001c19800900a040c40c0a054000c0750081c0c0000300381c0c2d0800b8160400703580000c2903245c440c881e00086000007880c8000170b04000c0d0710703a5074943c1c84900302010414080701c0c41e4815880340b010740301400042032002c5449501c0341c0039070409522050310180140d130b80075000b06000c0c052100d000c0740000d541003644507007414521140300f0b070740d0150f85495a20308004400c1d03a002d013040d88801c00581c0141801401000703060031150524038241c880d5400201039802e9862040c010321800c03001d01c4114100702c000705000d803180d150300b581030200c0d00c2c000705da4032a0144908040d04111440301d500b1000c0c01e0044801134510402200d80d28501800c1c041c20551003031203500d0140d01e8110000500c0d10041c400c1c0c83c000e5501640d04448404240201e00070060007822004c98269110590300c1240e03a820040c0c1102da20a8a5003602d40e882d5004020440309190b1060052002c00c11240c010380e680480d400b6445981420030396181d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 7487858 1250 7486608 7486631
    0x20303180c06040308070b01060201020712050a03060905040501090c150219020609030303040803010e0105040b06030604091b06030b090603030a09060521010905090d0f02030a0c020d0f08070209090a0c09 89
    0x70628103040c25030300700d403000a011050014000040c000305001c0d4a41c14540d903600d1104a080303124a140c09041071826902d09003006100d20000e0112042900e404903456440c4c407ca4402c8410544048a10345e541e8452002003109000e4480000c0442040d204400200c0001c00f0b03444101000d9110045020303112540115500e03030040d103549240240403603480340303400e240c1041c0c160b2007800341e049484681c10000605261501411281c00c001a00a45c11a2510420300010304000c81c404ca0ba0368080100c449480d45171048210018603807942e010500114510502004400151803180650020400c9400054120001c401290341c5440c0c580e079515007c1e1500220211042550000d542041000003451405508040e0080303e1036400d0755004800c0304c005441a009030440c1401607007042c085404818000c40c5110170090002d45074a074141601d9450451a10040c0300407034010740081418002e40c01c3c20400d4540c441e420f08000c240135009074607880e1080b10740d2b2050701031a0382c40710713842e111 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 7489108 1250 7487858 7487863
    0x60316020307050d08040515090d1b0609111009050f010c030c050102040807060e040509070905060a0314010204090b030613060209060403020d03200d050d0b0604030b070e0a0e0702030318 82
    0x20201c3e0024191416080400001028590251415204c0d0b02c01c3c00300b08000d07010f41c0c1d010a0301401c186001002a88141d003800d0b038a5500e420310842030040450020804035030140543c000407071003618000801c11001c0204049403142070442401c0002010041c4810385031042148a204001d00b440e44101d58189400c844444c80103d005000e54004100001d280d41e00092020550b03e041d01c078400e8040303600c01400304680044452240c0c03a03000d44410446840346a0240342c002c08064071321150340762030380c42d003c0304c0344e01c1d00107a0b0301c0076035002808100411261252000c1030204a02074280c0d42001d60310320310b035024401c0c400340a40b079000403141c1c040da84110803500119406442c00d515a009810094a90740e803410064807180852040340300082400f044100701202c050310340c1400c1c038807084a42e1006061b10f10142d5008081040b000c8003241c00c84010303600c9003100f0380c0c8043d00f03030800c3c80502c08a01c0780c3d80d00028201c00090180201280c003c401d45e580030304145041c4004005001c0401d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 7490358 1250 7489108 7489117
    0x2030c04031b0303140903060609060a08010e060105130b0312030c040302040603150b010306150810030605010e10080705010e0603060406030b0a0903110c03030f03181905010e06060603160203 84
    0xa109040d154803002000540b0b21100341180e0203034641c1c0c6100c040010741d410340d600c21500c00075030542041000840d28506600c4554110501038540040390742c0301e0389014211454280711000716030000004100f0380c6003028002e003841c00d40341c1c07003072000d9040701c400701e50364141140c10002c68030804000114011010400d0380d000b550010004e0000580d2400c0400594000b00d4032002c69a040000c00302065019020b400201d47c2040b07040c1a0816509804454900b4054003091080d441458004080f4a9901519001e44407039070b450803882c1410000c000320454298041601d5400000040100340e030040c03e22006004103507880741e52940d8241c001401402640c0004013001100c031b0612645401d00d500c1300351410302c203858803465171215140a40d610009104102d0b41a4010407078901040c484c40c0213160480c81d526022110301014958040c1010031041038200390001001e800703424008240a4031600c1c1c0030b000e0242c07610341007030404207460303120062903801d104481c43da0405944e8030800484 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 7491608 1250 7490358 7490363
    0x30902061801031d0c010509120106090507020f0106060905010503060301020910030c17010e0105150d1b1d090604020c03070602040b07140f03090906010c0b070c0b1003050a020402030c0403 83
    0x841e81c03209241c01c10307511200312602590000346011001070240213500741c9200503a6070700000b00000c01083c401181d8035808800000d0b040300722101ea46902d21003d028642c0603041700c0100ac645441d0500009103002e40d500e07040105030781000e00410115411030b03540d1040e036000f8a4101e64a07500c40005c240079106204007a038108460700f10b0201c0c1e0720b5155000030140c480c10b558001d0480f01000c0054103043d42805401c0381ca80c0701a004001602e0300d1444400e40c001c20803081d80c00d003001c4001c5201201d111142103400c41d2080c40c00704003025400040c115100c0c89010204014400744008149000d00003020386000c5c90340020a1400700d40e0401c244c0e07041c1c581c4150150b50361511030001c4e69264000301c1045a00081d4282200220003010030025050807088008500f07101c00030041000d003c4c1e010340081e040c0308105105002040300100d25603c12a0651540354610080c0d181c0840c0c030400c02040c84403040509102840000c3c0049942c0501d0341e011240540c880e25800030009240c41503a200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 7492858 1250 7491608 7491619
    0x2b0b061503040605060a09020a0203030c0304030c0818090c0304030804021003021b100b04090f031407022e020d0c03140d1d0c030304030803041401060801050a06080708030f03010b0a030902 83
    0x104401c210854008170711540b8103407903125005980342c80e51816401443c1d00200960001e10001d820900c002d005154024041e20780140c1144080e2503c11311944240340d2a90100c0b02c0c10342e1404e00d0704000c1c0150b504a010002d04031b16529094030010b02d12031029200a110703441c244a06200e0074442d8050703034517075405019403030104084145c015a80c0c404200f450903003a8100007545000b894188280102c950300b0007200623401003266000c454490040c40442c01c203007030038001440540c0b1100c1c1035030201088502c3c0c1104c580d2050240c00b55002c403c101d02821503100350220040e1a6200320032101d099414100240322085900b40e04640f806a0750b07540002c2071a2110130003007240c240c009144105440e40558407a003000360141500c92003680805031103603a04101140000d10b907000c14051008007200001840ca13220003559003075507429640f000f1030b90785500b0309018190f0305020303050040c04144001c502e04003061030201c886010521030242c80110101c1c20394140c5001740c0100c425650700528 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 7494108 1250 7492858 7492861
    0x70b090c0406090e0c0901030b1b0d020706020301060806030109030f0f05040e0f100602010c051e120a0506030c0108010302030604030804020d05030c010501062715030603060207050a022b0b061503 86
    0x30f0100410000541e205103115070740c0295060b050810b121b505881c0c10210807102030341e880c085040c001d1100c100c10012200c00b00b082c0581100c1e14400342000b1441020b000d40d40b545015002018540090040c61280c0d140403250345c00a6081070413001194901d041c10180150104410345050103180d00c4006c91550031001c11080110010815200718210001c03210440d4507084228204c1e12000c0301f101c0032480030070210700d00c0f4070494156900d100850144d5450620700980080060b10142c3e140d10750b00d915a400d0180515040c42041805002864204400d6245800081d80c440c0082c00c00317400d1102c1003000c9015502d03040c0d05240382541120450380ea500c56000001d000388002d20400002401038103103c28414404101003034204003852509130b11505013411a02030001ea4070400d001e0590702c4100000154050018007040743c040d00c00342058030000d00601500c2c44229101240e64560000c8d044001a049003400000d203400c00c1c880303103050342e035070000c980c10042c2000c21a202040c00320 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 7495358 1250 7494108 7494119
    0x110a08030301090b0907020715180314100c0c020901050d0516031101120501350703030207080c090f04120c14030a030b0609010c03030e01020f041508010614070b090c0406 75
    0x400010005a045e950441c056981c040120303203400d040d016822000a51407805800203203d02c00013241d4009039200d400d00315a0b04d03561101c1070125000440000c5e0440ca40c000c1c90700703007c1d100b441d4440f1b40705e00b0078443c07034029a400140005414014540300340100001081440710410403c0890580440c65004007900c82c10b0104804240011042c002101291034a101c182e0902a0383d042b9111083c03800c03d14000d4000104440c0085624104180041135880e814108100034585c0110b0081e0050404c1c1070610f00e40a06200c04071940c64080c884000c14060040e0000e070710325a2040d048190700c802c2d1a0b08040845c0c144108043c080c0030380c00c5445840044800c080002d021070800c0da20200212101d5405115417801100d00d0580410301c58102d40c0080390198002c200030303088940005203040308981203d170f00e540054224603e812100d0400084494100d0003e078090001400c002005908250101205206100d0005c00c1000c80602007502090304104010040d100200180320713030b54544 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 7496608 1250 7495358 7495361
    0x606020a0b010b04030201090902071115130b0c0c061303081201080c030d0f0e01020c0909010504150902030a020f04020d0e0303100608040804140114030702150a1503110a0803030109 80
    0x10036080d03401003214000040c2c00540c01c4100c0b01200d81c1a1151544585065211402500104000e0b0f036407809040c440680d03a5515007611174030001c054241900e601041c1018001002d150b042007860311410001445d843c2c0c00090140307051141103c5060b501c0042c144080700743d004940c0000e04049002c45c0c0c0c4101c904034151a107040c4c030171300c4089070403070344680f402c0680e10280c030300607580881c401d100c01108841c451382511107a03040600441e00e1040c100380220b041050110365a0001d80d540310103100800c4500504101c2d100e4030700c0414411446d00303400103501c500c0b00b410000d1280b054a1810407050300d60303406550303490300e4804080194200c5843d003252654401c40b8200282c850101001c84c406008014047c051901b0201c0581030034200b0a800744501c03031070310303000e1305000c0a054520101000f0340015441600c480d40948040c0c4d90045144445c0381000d040c05005606101e480c10000b510404080d046a1300007038078425180c0e090012400351201c0d40c01640090100100203d00a42076 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 7497858 1250 7496608 7496623
    0x1050105100201020a0f0e030309031b041404030f081005100e040b0103020a0c021201090f050f070e0c070b0703060803040305060103020f0108060a0308090310020304050607080a020c0705091801060602 88
    0x241e03a41a040507800c50100d0803445000a074030041020092134980052103120030002200d0041c00312450410401d001034034104079454248a40e9401405183c524102b0780100e50701907503010345210741da042c207076006000f054950504204101a407070005220f440c1051000c0014040a051800c3d014441c000c01450040500c241d280039904241c40c103482c03544207108858142506940710f6002165035800c00c60104805400c030300c0c0c10764807541c44a001c1016039414140c0d0038072510042010012184610b804e01480c0d61080352102803074001c1200c0c0240c02c60840704400d41c4285083c5a075568600c060700105603680008030544000302e004030030000c1c00a02c032816a03000712150000050a80300444442400b1504035400c0b42e5045c0c02040080d540b04040d0144100c010103649040940d64480401c80e0802c54041e030303280c5d1068040c0642c07150020803803604101403140540c03900b400c41704802d5460030749214007030140c144080000c3d10070750000813500d03215100c00020300c00260b581000079a183d00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 7499108 1250 7497858 7497869
    0x3050306040e070f05010e060409020a050c0c0402030f1503010603080301090903020f0a030e0d030c02060d02040905060f03031b150103060501080d05040e01050f01031401080d1101060515030910020a02010501 91
    0x2d85102207a411000040fa00c00f161010004082c00c0e40c208801180d840d8148565150004001d000105e18070b400c03800078101040c00c1c1e80d2810b84032030300c2c03170070180c6807007902500309000702d00c10418061001d00d0014a141d22800d07a00c0d2040340c0031480030119004041c154000ba100c081c02100200740d581d041c6d049140c4550195088540c09510b0301e2515441b81e00d41d40c40107010800341c00b00703c4100e0070800c20243e0214028202075a0607903041e000b26000760700c0551300ca400d50341e00107410f0007454400d211f0030307030000410b8801803a540040808a89d403881a141c54034011a050803032420403000c1040f182140c0000d6060082842d6501c1c80c210340600028000c0b0080c6008184003840d90030b100c0c205a90403155820541c10b050f0f442d007028030008940000d989410540c40c0c1c60428512902c20b00882c0c003d0003200010070090446120042201175915104969a4140340e4208901d5a40c0d40054039500f16546c202541c0351194200039141c00400c0c2e2884489600101e0f01004058040d0721490403941c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 7500358 1250 7499108 7499111
    0x20d03050c0d0e030a0b18010207030e1503040b0a05060a0810060f1a0a1805120a0303061202030307060c180909020109060804150e010b04060b07060f020c03030106030b010201090605040305030604 86
    0x124000c2c41910395000b80703500709425611110381d04000c80d024900c13140e00065422140c100d400c0b02c0007409400eaa00c43c8500b0b0f004920840d01c81c441d9030500c4400002e400703c1c40906281103080c07035900c00c203840748041e241c040c034551103101081c030f60b40d075012010300180011021105030465914456001c0c116601c6088400032415000090f142e115101201a100d4000d4843d807424640301c80598005100da80100520a0303101808540341e11007100c0d00c10191814401450307003902c240740040c151526a002944003080001c907445c01070300c00000742c0300a1a400b80303010504039044031045a8050304880110b41e00705244038000341d40700081d4400c00500307001b87c0c1c600110030f494400645583c102070324010600c1e4500c048000f009401640641060003d5000108858040d900011300b650220780044082c581c0014416040010b039126100ca84a4400410750a00603004602516800144260011325448159003916603200794410649194841c0c020000c5003007600b0001d22a0f00110b89280c0182d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 7501608 1250 7500358 7500373
    0x9031104090213020c01180605041506060e0d020628030b0f0105031311040e01020c0c0f01020a0201080a090b040803040201080709050906010e0310050c13060504180e0307020d03050c 80
    0x181058007039840040d801422003509089207511000081d8000c0c0c031181c0081d56559089122400b598500d041818010240400e4604003402e0070902101d549801c03810242c9010820040503404c03100d46d414215084490f150000d910f030000c1041d92245c4445c2c070102d220140340042c40310010600301680601c96540403c00c40000b8018409540729403181c1a020030014000100494036a80310403520501c16151049441001804a4290341c0b00a0900b040351b5008240001d808004005d1042425000c40e0700b0680220b08500103911070440101c041c0c1005030200c0042ea102034141c00c2189000e9001c1c120301031900d0141082d00407500241c40c00ca000480c09000306000c10310800043c02610030090044041c1d031504401500c042d009010555003500502c400c0b0fa4441030320788140c0f4490002441090307918404581c40782c00da044250001800d000307040c0014001c41504402240c05010805000a040d20300b484d481c40c614003400b20020745c49003808004904142c0d200c0701074080841e4040403148813 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 7502858 1250 7501608 7501643
    0x111033001080304030803010306050a090f0303020901030e0703020a0312050c190201080a0509070b0c0a050f010903080106050f040603090c050301021c0b0d0302030d050601170108030405030d080f06010c03020f030a0903 96
    0x3e9220b98803001c3d0030504184018008110705a1080da0009061400014140d44941da01001046095406d4000c82d60106101410796018019001c006d400710010f80130050a5034009001c9020500020700344a26601004c1c100c58040c00803948100201c030215640c240a54134036021007c141d110403030020f4054030100c2c41c0c480040c01200c0c0904840310182503198244806c8001c29004918100c0c1075116511a900201c0c405210503d003040d261000800d92000d0340c2005001e80c2410f0384040c08001c0204448a115800070042d203040e1100d6103401f0444d80d0850400c43c284452603040310358554030001d010b400441882000c0c11142480100a000d000160410400c0e1250142c80250141c0c0040080709004505648015800b80301410200c081440148041002c4c8109030416141035000180c244184d00e42004124400503480c031b0100441d1030442c0065801e034002828071414403007903d001c8400c050081c04482800c10003141100d03181c2c45209002011140c8a03c000d8030901007004d048000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 7504108 1250 7502858 7502863
    0x3051204030201021504020604050a0306020301050405011a04030f0c0b0c0102030601030e010c0504050f06040b0c0d031a1c030306030b090d200d0804140714010f09050a05011103300108 81
    0x1142c2d01600608007021425503400c601d10350041003240d01210070440802c15543d803034100000f03140550001030701c035810b04c401d00c01190410703000001e180e42c40d4181c480ca00d4200f64125002c2d29844a074010107890300c1e103410700312600c01c0c1d040140c1920000c204210000303c150b0145219400036a01482130880c0344140030b00b2a041c214a180000d1000c02c0107000034100000100c40c03007440904080d10306650703124800c280350000c400360701c40c58211048003240580d060282a03140005142003410800c035090005410b04114800424403800005c1c82d04281800380c6d018000950304000d0395007640c68a00d0409842d95016038a090124903003401c52006000c1c0c0314500c8400d404c2c9c0500030420824000f4098030402d20040c821205500000d00c24130004405010b50002801c2d0142c40c0707000001c0142c00500710114001c5414200070313111100300981d070749540c43d000031202d0030b0030601029031604005504602c5401d0050703100c0100c04d07444001004103985001c0c0c29122080c075205150b40c981c0f54058 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 7505358 1250 7504108 7504117
    0x4030e0f01080a0b01180305030301061701050a1404020705010905010509070603021804021c0c05040501030f0902010804060e0a0f0c0e09070803030a0b010908011401050f0406030201081302042301030512 89
    0x9000038100e0307000408483d002e03808200303400300504000600030b4000c40044103140094004a80c1500003200420a454004001400180a140d201d0203e98140408a00e1800c298425030000d10130451450445413039a50444a0b075640010080c80382a4039800c2590181205030340202551158860002d1410711038800e86005249114025030310144540400020b50490390701000c917481c40750f098804c2c00c103940c820310b42ca404298036001e8a50349000d00240460364030071032444100341020b60250040c0c2c0e0200c2081d900c1070784a900003c03142c5141d194249044900c59004112418903001c000070b1042003481c83c0308071840d000b0590519034940c0041e40d00c03804248178030b112907402800071400e00c80151300840d501a40615210311301a54803001c046c01d49206440e8a100d483d4000e0051049060003048030410340e800340c0c0d05000c01071031580000e040c4a8014420024a560000d01700d04545c0c0310740000d1812a02c4c001194000c000d505200040340b0001c4c0f1040311240300d00100c103001c1808490544 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 7506608 1250 7505358 7505389
    0x807051204061113230a060509130612030302070203060a02070b011203020a0804090e070911120603070e04050d02060a11030408030403120204060504030b09010203010b0403021e040207030804030e 86
    0x521510799a039880050041050804240e520510a04103c0b04002c2c141e0001450f5100c1101c80420000c0e071402110401e41d54524080c498804081c01081e401204481400b10103a450400e1008040e05030030081c801ca07001090f9440340440004141135264010344081c1e0b000300c0507910755454503000a0128410840014002c02c1030000420403d20201868591203001380150b90001055946000a603482504009038480d540d02142d9000c034804c00041c00604440d280070041c000c0c40d2201c2240e00e008415902d80c0c4c4d0010000041e0068a003070255500420558800609a080c0307450141c1c3c550160320005070051040d440007038403441044c06114480060900c242d86581c41d00d80311030f0713070a0740010800c1d002c1c41403c013005403890403144003c000902d00d5540b40c80e103407829490701c08031502025002c0f8142c0e0380103000501c0840405000c5034100c0e81c1c1120031100300d650640d62101c1d000c00e2000f44c035a115101040c5e40041c103800c121601c0c8540c0c465070f80c110007109140200501c180850054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 7507858 1250 7506608 7506637
    0x501030f0201050c0c030303010306141b040b07080909040302030a1205060f0d020d02120c0a060201140a18050d0c02150307081f0e04050319050a020a0303090809130c080705 76
    0x140c4059405400200944003c40c1c1c26205001008004207185034800e078000c451481d0303117100b2001c000d15101c035030541103812150b03c40340141c07112103480a80c0c010750054aa80302c1d0b00145441c10400050200c0345003c0018180050784e203468240a900e0350400380ea19000b190184903e104e5090305071040620614009103100c110f800c040080c4003220b1a0000201c0c4c010ba01e2104100250b43c2d107880c6c860540c100c00b40140900c5e1100801c3c018420016031007003042d0380c100191b400501d94840030b103c0e80b100c80340c2c000195007441c0311415848a166003401614034001d181035407034499840800402564001d4a010950041081410405100031a040741c0007072441004184290303290181455170304802c0b00e426005549a0801d110003400950b01210103520010382c03004207440c032040d43c2c8003c4240741403403400c1480c4014081d4440e80205001810151366040001c1005140304c180c5401c83c202405420800920360500001060560354401c0401d000d44002007a0510610071288511148034a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 7509108 1250 7507858 7507883
    0x10e0105061c0504030306080109050604060e03090306010308090d1502030a06050a06080402090606130b0304020a080d02120c03160501020a0206101a03040503090402030408030703180c0605031008010c020c01020709050103 97
    0x80c0c0302c003c00c00540101e08042d03c460001030307607540900480d1001c60140c07018040c0c034145854807000b01d03414042608115007050105420640c0d002c911030381142d80000780155540a54400101c081d090484024201d0800c1c011200d00c8c02c21070390146104150b4004100300042e201c6c410411101c22500c214400148404001001030030414149504130401078030300c0341828003407028840c20812035004801803460110810003075140c8551510010b096003c0502074034100800000d480b0f0040a03071040c0e0940c0c00040703074200200d003001162207100a40c1c04004000403030f8580716000c0c2d88030509000c0103104410215086951414091044980c120b81ca842c0440709006500401d03040100103450500090122580d15242d9000540c45039108521599403441e1051000d011501230340342c00411700a8180020340014503100c0c079141034500c141040c40d04e07541c0e80740a40035002c0403a003181155500f403249030805a500020300081c0400c0980a0310308150700c0b40e60314001c991007444050141d103507044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 7510358 1250 7509108 7509157
    0xd08090105072303070215030402030a08070305040e07112a0f01210617031602060304020f1009090b0603061e062206030b09060d030305100305010501030803010e010506 74
    0x1006050540c0b040e00c0e804010301c040c03540d407a20100a10203125842c1c04c000340138800c51502d941a800700744000d11925044d81000c2e004640d40361032201700240071080003c0d400c01403500810684002b0204443c03502c0300e44c03030b1aa000900e070314a01440450a4400c09014600407142091900c1c0c0b03c074506c1415550880c1c035002001042c0801c014902d0602500f545241c00501003090600c102e0300400c40e01261030341c03515070b103403144440c07410a1300710603042804840940c070160b1000301002a01241c0039600d9403164000961a502d00d030801d503a000c849040f4100c05c60360400d40d84011222135000400120400c3c1090190b80d2100f00d48455009500d449159401c184028000c1d01c400300c0900541e0070401d8240d04843c42d60b800e481003610b14000c1c10000c00810b90f050003035501807002568555050300744040840d0300000d8a00e00141816100c0001808404a0842c00401160030038020700203540e49052140c2282d001703005502400c4940800821981406811110303004129844219004a000f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 7511608 1250 7510358 7510367
    0x20d0b0601030e010608070312020604050604021311031905070c050304050904050102090a031a070504030308060d02121b0307060f020622020a0b0919080c0909100903021501050d080901 81
    0xc0c002814980ea0b001c0210100109100d2132015004003401042801e0031420403d003d020b244030b0013421540140100800203a021407940d4206030b05440d0606180e124400c0f26001e0103a946a401003200c021040105802c00401d80900ba10440321080085444070441100c4010036101d02800c2548100401c12103810315500300b03503006000700001030401210100040002d10240d10540311500f10342c51121405015002c916000b000f6824018581442d42d40d0140034800024200d40c410620a00403000b5926106180700f440051001034070559626104c41e0b198102c10140964041c2c4549032001c00e0003801410b800c07950285030b400504c1c0f580d4809449048a0500000c40000000c3c120140c01c0140c4841380c108000e800003141c0c468076405c2c65801d015024610b2140d00c00c8280b05010308020a01c4003150b16074070140291103914079175480d030075482d2904000c2c80c0010307035982c076142080d410700d607010442502405080c40082c1460740e80703000700421406419000750464a041248484944c0603 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 7512858 1250 7511608 7511611
    0x303070f0203011b08010305060106030203060f0103020d0e01050106090321020c100e030a03110c040b24040b071b090207120309020d0204060b1c1107030c0c0b030c09010813020d0b 79
    0x100003054000001c01c0d83d4200c071300c141041e5000b0485050051041040600c074190241c0a03e2808600f1403a117800000d0043c24030b0001e190505900103043d01c02c1d00c049800c14030006e400400240103c1d69070300d00c020540348813440300351340000c500e400288021744480120f00070300e1100d500602035a80c42000300500008405100c4050000c1020030888540f01800201e06003030081e19501145070448412508060740810500c0c480e52030300c607042c8065a075040103620720707046007400107201505180c1609054810781d0040c0e007484001142c4803080000030040003001400210003080c02c140d8507208003040c3c0c050040001c1695526131440658144258440c22900d0b00092410322141e989401281c1103581c250402c84034403e0000e81500d40d030040ca100b07801040d41c20a000c00152444024544250051003001800c00241010072001d004406801402800300400c1a903035900300502d044411394400c90f0828041030300580000c00602085035a1280203030098030300401003400389d440c000941c80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 7514108 1250 7512858 7512863
    0xb090111071505070b010504050403080a0f020405060d020403020a0608040f020d0c05040c020a0501060501020304060207180209100206040302010f0203040803130305130305070e090303010819050309090f0717060303070f 96
    0x554440001d5014002c1c2d05450b00c40c1c1c0c140c403199a107503c43d09060060150580005001d103041409000029502010581d4001d14100001440022075403c1c03002130f1107a50300c1680d10448c04a4000d20700e4078143e0017801264801c41d03809014594a18054440d403801715401b4111510500c080805400c00705031603014144182c444444454503080024129400280d520300164010302c80750080101c24402c0101a0000340002d602b0185083c200035500c085500a001c2d00311800c414400e20300b42c568050701c104660060280c80c81d10540c0340020355401c812203068005600704400619441424400c490049410019280c9540e60f04112f032844080d41c200200d003082010010045111140856140070b14490005081c0c540c0c6400032000b00000302911030502c035041000104a20400011403034040300040c1600412441182061400e500824092540040d455000c00640528a1001501c15441621384841c50090048a04410a0101c4089030954400c004481c0412082e0000b00c0d402403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 7515358 1250 7514108 7514113
    0x3050c030f030a020c010f0209060901110106030506180607030b0d080711060f0702090c0307050306120c030610050907020d08131b06030209011101140f07031401060504060201150b090111 82
    0x2441c14180700198400c84082c42003d03030208103045004400c0c050100042001c0c0c1d0305500380070300d50001507118841d00050390305000081800310700b07040081d00042c008541240076240c00d0700d050551040c4019014524031042d02441c40000c40c524081d108496030b600020b011003400c030b0b4040d502c3c149160b01030b21046d201f60001040c512403035501c3c40c0040082c1c80060026a8541003584140304500c80d016220011200052080000081c0e0080a03a64025401c55220440810380041e40f410900b60b94060b0380c050003007000f04104403c0d200c004404a4000391402c14842d42e4050742240c662100b10f0f0554001303074820000c0b4014008c050340b03200c24240505600d11152031880314008005a0f1a402807010913008201c81e40590307009001000c070440404001d200d40c4c1e44510101124140041c1014102c90701440071903071303092113907200c0d0003948400382c0e2825039543c441d40c000c2c041b03030418801c04006608022010040102911145080300e140e0040309040c800d0500c01511500400d5100c40341c0352 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 7516608 1250 7515358 7515367
    0x903030c0c1603050d1b0b04060c050408010906050708090a0c0611010b03010f0f0c0503090601230301020a080103050c031f090201030e030d05010e010e07050702010c1e03020c0301050a150303050c03 87
    0x1a02c82d800035001544114002c0807448000000542014002c4880a030f030300d00c200440c0170100d4104684642d005900c01400126641070580c00da4081c043c40e04507004961902d1740200800400d5404640036501944030103220740e481954072a581c1614170b00c0207050540c0c0003000c10026002d0003841d6804003004001040e00300405000c07070308480600e000008665110040c1184080080c130035440701c40c58518240303146141c042407190741c5038010301c00c00c4030b4031f24001018101d03101d01c1c400707460711240014000c0d175540108a800510030a0203001c20703515401016815503480c80e00054200258039055450203010841a502200418030100240c0c10b0507101e8a0070b000040d810701c01040c02c104014400212541042d00d071705100d03401600040901030007581072000341c075001030680c0c80750381e42441d0002c403161407480c024501a24015081a44080300c800c5c0c04109500450a108191002e6000b04183e82d2a1803425050b40c2e030000703514a006041110901c0440e20450080c2252180002107a1a2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 7517858 1250 7516608 7516633
    0x405100b1507050102070c0806040305040b0a030204030204060308030604050705090315060d050601030507060305070203120a02070f02040f06030b09030403030e10050715020c0c03060105030303010501030207050c060304060e060109050903030c0c 107
    0x90340c442c040446a50f58001803801c200542c4141010103024a2402450301d80380136940038285104600030501040030215100301054070a03011070740a154040c00074000c1c180c0c0e91410038800e8000340d0b001c510560526000402e11403141054032001d5100074003c1c0070303442c6000303031810385044060b210540101d010b00310200460700410816008501c240024501c0c280751001c01811950060600011034000300250018031602e2811540c00409040006a84911382c0c41c000f001c41c402100e0080d00310341401e5110f20032100d203610590449004000000440e03036070716001c2ea1240719900000b804a0342c403024000c51030400c500054100d40c014100649094071036140e0b08035040c0880a54032226800248c910084030040c08034814012065004083d19418040000c0e100d010500905d8101a4046013810501008014085a01034080d084544e241400d08005014246801d02c4224500c5000000a600341c3c3d80e100d8548030f28140701c00340d41591101e890000d9103a220a030340701032a200d1004111034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 7519108 1250 7517858 7517899
    0x10908010e0c01021b0a0608220803010810090f03080c1c1505090708150607020405040510180b0106080403050c0f06190209060f07022205040b0a050405100b 69
    0x9400307581c18014112410020b000a20b40400e010711712110112290343e0401c540c4403803071707008107175412424450501d039600c03050551071100505c00700002480540340b0b102800400c000446c140c51041d01511100c001c05500701e416100c01010003028841355030a440d011030b1060313615070f0b004903100203014a404400c0fa0070051005181c1203e0403034942e6904c00c2800342d00c1001740f4038010002034400b80402c1c5400c1c84081d1860000520507201c00801e895400c0080c4c0d01d2100b03c8001981c001e1040049081c07a0409560315610744010610045c40c240c0101401c900200c0c40452065010480360a00e038207040040b144104094000c80501000f07114480001f4810300041e4400d81071000108103515004845a207100075080c05081d80b03074410422081952964421106c8401001240d01d41d070b5156407012400407101000580320039403841702798403102c0340b081d08182d0003180100c0b080c05464036030f500c180e4102d170760544000705154401d501003000502d254004165011300200003490039013076060920b4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 7520358 1250 7519108 7519121
    0xb09010509130212070f1706010207081e010606020a1205090105160f0303050a1b0509060f031303030c0f0f08060d060606020307020901091103180c030109080c010513030e040b01090801 81
    0x3205a801141c81d03242c2c40444d01c0c0c200d0f400a15031034a00c0c50744035414006001100c140411042038264200040c945900821840000b407a1405c11a5503000a0541070b0340d545078044141e100315420480c000a0507840083c540601175040501208000041c200076a01075100c4140d0364141305c0241306005446104800c02c0c40032a00500c04100c2c0c991a43c0340c02400c1302e03002407601c0d105034503003450290100c11001c5181402c0304642001e990f22151240000c0d803a01915503100c5148400004005401148c043e0f581d1a07503220341c40c28000c0031248441505c030103004d4103448001401c00f0710309882c5144a0096160000c3e00505640c0d00c2072601c1e11b895040e03d400390405400360340001030640c1141031008110b40141500301d810000030b03004020040d82d51101034001110100002c131030000d451400d103c5080c206c070000f002000007802a2074414659040159601a9940f0340000900001c0e1803021901210b0380c07564803042401e1844040000030020184114108440c00382c000c6410b000920600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 7521608 1250 7520358 7520389
    0xe01180b010e1005040c050705010b090103210c020306070c050d0201050106050a0302030705070204060303180f0311090402120a0c150305060907030c09050603100f05060a0507020d0303090503030403080414010b06040b09010509 99
    0x7540d88e1089040c910300b03587c200311901e40140c100c40010004101d14011002c0300201c055404210308038401000c03a1034041c405d40203503142c09081c0c01d2100c010740151035091064072070300903100854503103501a4200c48003403090002080003041401c140900c80c1d801076034003121508242e130501150740c000c40e046520380c0d00110081059000505550202c00400d00020100445030300c003c03a0455441d80024142981014000d00c1008045001c641e0741c03c206000180e00c9000701c400282c4542000e941d81c82c203510030080000382c080c0180c2c2c10706211b80070341031180a0262244400380c4a0500440090002d0200f410401c2101000403030956103400c019406044490b014460090900807140442c1d6650707031246125500c2040320740d603040c1d04030003940c64440c0c046511145901c043e0506070003506031106e008006001c004108420580c1011101d402f07280030309292002000d110a5031403c80e001041e000d60b05c95018002080410b42c80f0f030003000081c4042c98428100340924000c1400c4001d1000d00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 7522858 1250 7521608 7521617
    0x70804170d1b0207080703030905040203310605060609031506190801060f09020c060a0203100308030a050708070801051804060605040c110c010e06030a090303060512010e01180b010e1005040c 84
    0x29000c060fa030401221000d8202140030740003140c95594080e00f0314640d403017114000d1fa0080002240a070180c0a6076000301241c628401c074044011401044400903070008a4031180b07007030b0210390141003260a0b500844000f030014a02c0c1a18010303018a0000018040c3d40e21810b0707841c1142500400c522904020140700002054241c1005c041140310007803030f00402e56082c410b01c90385810380340000e241c0d6081401048010784ea5200c0b2880000035503006d42002e48110780000922481c2441d9501c09846200607030f403241055200d001e0100d0f090142032058030344c08400b01702c1309110783c1c3c2c03201c42c071580041c070030080007401581e00c0e00850b080c0ca400480b100301065a14420400c034090500131360050f4a424600f82c3c0c0f00b01d002a0002d05a030101410340d034551540c0750040002c050182e40302c0c0d4003400004003000c0e000b05400c00002e02034203031a071255559500b044039150380c1c0c10341d9500e000c02c1182d01805108860b800c1111494010300010003070724854850030400201903c80e0700c40d200420315240d6030f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 7524108 1250 7522858 7522901
    0xb060d0606121401060c08040807060917070e011503021306090302090a20070201030b03010911040e0c10030c14030103050601090b1905010f03021209030c0105010806070804170d 78
    0x20180c4246650103860a80c1401c1445a41444001c1c40d10f007415034200d03007000b0811100b1410541400e00454021191622402101041154201c042401107660803080c0c011540001c260040d1208928821124080840401400800b000da078513080c442482d8580141400c041c1c1d1000012100f0b10b41c44040481c41c4140b06000790b04102048540c41001000b00b400404403000200d03c0044030138409540b02200401c4a8085a2007a0400c010701c4000800a0000841c0c80c1820003c002a42524a2155191448143c070b120004940100449802000340d00c04d207600c80d0080d80640140c83c404070030030142007121001003205201450283d40a10014170702c5604143c40c0170103d883c0055881c0c46176100b580402c2e49401516502d2050324428a0003540ca40f0310340c4c506502038000c40410400e900020810006c16030400400340150480c400c0091080e43d0b03940b42680e80341e80040d0b0b4901d00007004880040d000c03404aa0354644010026110301d440c2c040c60084880071600c1c1c560031555002d866030b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 7525358 1250 7524108 7524119
    0x40b0601020f0a03080f0601111e010c090e0406050c0705030705030c010606030b030c041a0d0503090306010501030b01050d05060d14060a050603070501050414030307140d17060d020409060b060d06 86
    0x85501003140e02d420007000240d01684002c0d002070b8005021042644408000035100e074828412555580103080803903a40b106070b05034241c00443c402005100c85c1d882d081221100301d00c1100d42d201101e01c4020b02802e19142c64641001500c40103081c040016010009400001c208200400505014001554171040a6802c840c251a880d500120800d81062146910741d540803450180744002154005400d5849154015170b40044100c0c840d8000400040c040500c6404801044400e108030b040d03491036030300c07a8019800c130340c41e081103240051414844403070124a158009500001c00030700c5560318003440c3d80d80590609150545015581040043c030440e515180946a0805022406810242e04040008040e4020b0340308200c084000c0e42ca91005507103050007129913450b084215401c030340714030850303940d03980240780ca2030400030388104045003110081900c2240642d070010440f0a60b08950780803c0007500c40d81750b040e55000d96a00b200c2c0b1145c0e4860713004012841004401080304d51901 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 7526608 1250 7525358 7525363
    0x114210a0503070b090c0604060e01031b021f020f040b0a0905030703030306090b0409050d030b1503010e040c06030912080c16140c010809071a0c0a060605041a01020a120309020306040b060102 84
    0x41c1c4681555440b4444030446e035901c070401c7d10b0940710b0503e0040e80101411004a0151001500d2030f9503022640b004070000c168082a0300540c0300f031804003200451b5568030f041d8100d20501c001d000343d4180501080c040701c07181c100182020022880e04015644e11480080e05024043e030003100401d640c0d0808103d000314a000d00600540308807820400c900064075201e031640400a0300c0400c155840f00c00d00f559907150b601444202c55200c490903280c0da15412404011074080c1d40035190469507500009840d8805c1c010381d280b6640c041485500380f1020481901c030003502070210300c0c00c5001401007400e0301d500e00030044078150203030b0201e600c04201e1910f91403d140143e0700c0541080410010022224070006a120884182a12400e10309281c1104840707280942511170325103001d11100c8109210b0542c202c9001e07990112420040400d8002926401071480d081ca0b50141c0c11100c3c550700440c0f2107102503684041242004202216168000f9003002c204681c2128411840c200740070b07440d60304 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 7527858 1250 7526608 7526611
    0x509011d06160e031002070602070323040506030a0e0d0f090602071a0a03060b07050c0102010b180f0606090a03030305040c09090f0b15090109090302150114210a0503070b 75
    0x8140103042141071503440680107502580c48039041c014501500e0f034142d01d040101c01c8021042c43c1d42151140414980800a9800040158009501700c1002c010015040d220782c0d09040903140e4030fa2800d4982420300c4020b0300000c10500f0a03c3c1e907440340c4c4182690521081040c0ca4095503107488021054101519040d42d5402260071503000550a011180384c9600c0a180100c1200c2e13103540fa000021012005481c0e1070708001011403011400400b04403001070f842030401000d8009020b1b421040041c4041508147d0003103005000442c0411941c2411146045d0490070141c8841d28020800303021034201200c40e4021000241c0d0f810801003401002030414018019003842445605071a0702c4044140139038003000341800c000600402da48494a881e81c40744c01002520b04600d81d0fa6644000001308540c00341580580612103850051960030315216060716094070741440448100c4051020983c40b039140094107028024510040c61010403810000701e10500007590341d48002e26084203030410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 7529108 1250 7527858 7527911
    0x60f010b03010501020c040908070507030c080d0206060607080a030603050d0507060b0a0501020c101b08030105010e0907021905030c03180a080c09060103021c050a0507030e0a0506070f0c06050901 86
    0x6081c0010700160f84d011034100b141c014102d0f4046058032150401481d180b1800308010312030306c540440003080016641c40c0f4011a0106000c0d82d40c61030100740166110700301101d15680c13141d020040c5030300183c5148040d0020200d145000101981c4a6803118908111503209901040c0046801c1040201e98060000400420384201401c240f8084c00030b990360303e00640192140c80c4d41740b4651003051041c1c0d00001120315051101110094a061496540d0310a0054070700040e507840e141e09031b80c00c100c01c0752401070035203500506a200e40c001040801c40000303041151140810424004d03110010405040c01c009000e00d43c8a03400c00312010803404040c2580070019680280110030300c1c1d5919a10b84c150300c00400c4c01c2c056651405d503011034194051030342c01500c505141c0024490003a80f903522042c4101c0e0a520204501c21000e0216561465a070704000e150f030b40140c0002d014079205148201e00940d03603007420202031020350303540010784404860f4820103a545100000a40c0c003500420707003158a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 7530358 1250 7529108 7529129
    0x605160c020a030201050309160b0418020306090103080307020102041a0406020606090103050a06020307050d0906050406050703020c0304030f0215070f1b180e160603050105120706050a03090602040504060602060f01 94
    0x140355070209920882501c406814800f010001851006080c81680106203000d80006e8000f42c541c040300901d43c019019101c8695a8403211424003419407080f2801100000c119100c582c0c6161385698059000406060440d5007e0000241c01c48206560750f59810f100e20040e45c40303504211780240b41000c0141400d00c034407030020041000c1400840c2c41d8007403c0e088440503940344c3d03e044080d0354603c103058032520030728030340421041441040e9100030b0141c0d125403c1401242c80f0300000f14141c2c0601c1100ad504d541003044100001000e02d22008425880942000c0c810301082441000e1500060002d3700c4090748030340307842c0c100300a00400c60120f101d0400385c0b810090800e01d080b0307460212050544039440e91099072a824500402c80038644001c0007110b81e18443e100c60000300a4074081c494039000d061042407952826178042101c0089e101c069485900301101003030214007400254006458080d400c21000c0b40980360f41c000d0381c015250300d400610490134142001450108140d12020707800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 7531608 1250 7530358 7530377
    0x2030f0601140d020d0b09010b0a02010e0309010e0108040c0b070f060507031b030c0e0a09020a03061a030403080a0902031005060112050609060607050304090f0605010f05030103020a03020d05010e0604060516 91
    0x2030384290540307100b0880f8003c0107841e079102006040040c03e007410110351211524000160303508250300103041341c80c442c1c0d0080c815401e052480c2a9030703014007504503021600c040c0e1421040c1d4403030018198494001c2d09030b0780141eaa85e0800043e10b60188005807580c1c03190035600c0c400d00207103018a9801c4145450200800315012101c000c903403907440b0041007010b46a88040300e09a219200a00d40418010121b00000d582c03804040002d520400d0110007107410000b0010786484100023100c80c200e05002428515607669800b215a000c00429218045948011140c00350724200400010140d03024800292814401c0c00540400900c8070100540b900380402c001d07413500c501c0c0c082c80e00280c040d06c00f6500c1da841031902a08500807074001241140c90302001d503c0d0720707140307030442400c4a2003a20745074000821420111f070144003d020294010156034800c0006081004a900d14036000d140009614012414480c0c201401501e05440c083d440e103041c4281080280c004912419443c2003002e40b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 7532858 1250 7531608 7531637
    0xa0c022d090414010f0f0c090803040306021303120203030601031802030c060c010f020c0c0117010e06130902030303150f0d020102060a1107050703080a03050109060503031b03040902040902030f0601 87
    0x400c640e441249000e0380c07450021808100c019490100b0484041000748140407905d203c1d20000c024130b4640c100d0840c00e20981110107800341c03050f602500c0e00440594075190a40d11840c000e03500102c0c4070305298a51440010124040041880b90000b180c0e000e1540d900b810b000042c165252b5102021802c603091102c407005a4000910200b41c0c1015158591501000a00c80b401070011205051742c09000103a01f081f24400410980c01010098030f4504402e54518084540b41000740a41000310001c0c01c041340d014501410910000780d490302010425420380d601180c1035410540d64101841004210280b0914280c0d40441c3c04410035540300c200c440702600005d59805000d0503100b1a1581c2c1c80c03080e003c1d15502421222000d4101045650300c0340e0340e16106e031241d0701505c7e0550010b8582000070801040f980243c8048410040003142080925030381e442e0340c1c01402c40c8091140c4410800001c00080714000f070801080c2504005880c1e292401d40e200081d500100380504000c02c0900c02d800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 7534108 1250 7532858 7532929
    0x7061b020906010201020f040e0402100f1d030a0606030503030f01080102130b0706020405040908030405010f05150603091501060e030c0d0209010b0c0106050402030a0507031a01050a050f0409020a0c02 88
    0x10465012075405103240c8038407005034020300c100c07000f045a4150004011481c40f200c1e0051900903442a0b900703480c0c01d079039040211001c40f01c910b0200006030b50f105009030070b500b19044550758003200409540c0501244e1340c4103822182d05500441d901e0f00003100300000341c40703442900707401015050029407070f05106c00d00088000c0403501402441e0340e0042001803d10806a0503503000e41006070040148560750700700b500c0b440d082213a08542542c00c002038951848902d024450082015488900380810381d1070410405810041050540d4454292410f036180d901c04400b40c004c0100c5e1300d071554011069014103041141f401c1145018041da40c0841c00103864204000341111248403003683c455000040c117a004d000158041d950003030002c0305015181203140c6c0500e014081a4400700003000342501c9066040d0709a090050120b00c9c06e02c581d494050140e0000c1440704500000c40d41303003a071100702071740032a000040880c0028103050442c90860a144120036228518442030034050f2091110308603 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 7535358 1250 7534108 7534157
    0x801150206271216021507081b030702030601150f030615030507050403061109010801051806040b0d0c0b090102012d090204090b0415050601030c050d05070903020319050706 76
    0x6038902ca00c01511100c41c034041c84112a08000e8110f00ba981d04803c8480c0454000308510591184c648032090b048410401000c60710f00503448a240c5081800e0841c5054a0302496803550f2400e0108000310801170742c082c000c6034003a2031410303c140e840070084180104072002c0022400241407406030b0078000713070030341103155003031040c20b40742c00f00d440ea81e200c070100d03001d00480d44018122402e240024004201120290070104000c0e610034069030ba90301e08000c204c02d14800c000f02c1d08016000802c14034100703900701203141007024009088800303460766401c1e446660340c0d2010405800125440c4aa581e0a001e0410510b42c50409030104200256a01041d4070145000102d4190b50300d0f542d40c00c40d2155040444002c2d041180b11005182c1070401d0312103083c40b43c0800010919080c00150300398064409c01480f0526540e1316810400424070400003040e0141060051000c514030000040c5e0b800c21103880b514105100100903490207250991504c01c0130380048041c400302100304c0314902030100c00030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 7536608 1250 7535358 7535401
    0x6190f050a0518030312070203030105100309080306040504060b03031804141b0a090b040e0702070e09070e040510020f0d050112020105030406020a0306080609010603020f030307020609090c04080109030801150206 93
    0x1c3c0c0500d010700006899072186e0704500c09134013000300c2042000e81c0c01001850403200280d418080f04c1140300c3d030840494030380350401800001c081c40800c0c100d007001d0748010362191040f2070010b03402d0b50701c0000910b5034001003a51140b40801c14014501810b2074011080c914001c41b203403c40350f0402c00e280051000c03060300300740d080f02030100c1d1124100d84201d01444c010b001910501d0350790f07521600440503140c8211018009841240000074900301291901e41c4105d07401005088070904010101c101c104019106a1300c621400070954601405840100342003400190055070b5007130350000001c00d40340164860000d602c0910006405070f40c008045039841070b0b00800059461740490401e50041419800c05002c07407280e20100f041c01c4105500c010241c2c0d008540c2036000c58442c1080607501e02c84c1860094100a01340401d000a02b0400c5085410038902c410365810191076000c0c2c6400c481c4100e00c03c1d030021350904010009034034065055004885c1d00d2014249a01d400742c40d114420301c0c500780f0b4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 7537858 1250 7536608 7536637
    0x50d0503120a020f04030f0b0603060403050906090117010905011a07020310050a18110102011103100308070807060f0906060602030a020a03050901020c0901080106060f02060106020a02010305130206190f050a05 92
    0x1502d410750355044070f88403031000340000d88468032420b000110f10402d040803034540f498400480d07100c1c5400100c0c00e10503035060341c0b610324114580c000d01c40103421554000f414010b411711003801c1c01c410b0318103042c003900600400058540c5881103141c5007088503068030401c1d460402403980541c801203850849000368180c0820a511040180c100512181700448054200001c1243c04c014203101040d02c4510701740d0090107942ea100c04005100e1006031a90004910b1050041001a01300000b134407015000b501ca19007007a045803a1103082e20050006034100790b903030b1191403081000710320400020308594030085003441840c0c41e01035600d480160001d018403038003007841002030303200300108814150003a044880302e5a40314089806010b56008220100d100311340035076000e610002d01031381207030385070360040012210540054000344009049205100300402d400e80140e1a640c0080c104c13140c144144001400c0690f000501c0c400180394841c0c1044002c000070080154050140c2d210302d040c1002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 7539108 1250 7537858 7537861
    0x1b0a0e01060513080a03080402010305060109050d0f05030c03040b07150501060503060d0510020f0706140405030403060903020c0d2009130b180609160618030303150f1707050d050312 80
    0xc03207101e00003541302c40c103103200e2a9110310805602c18a182e01461003030f2001e000580b2500b0040d110000300380145500501101d40c400c0c00b1034041c501e00d282060090b016030745008200ca00c654195031058002c1c0f18800c00002d4032100b000100c3d05400030090407c2030401040d41494002070035440b001c0c21441c41061480c28180500405000d02c480b4801c90020441d503131107008142c01001d411401c0b0a84450b840d100102013000610002c540c422544040075515141c1940c0d280401010303141825001c51196182c800708546400620403c0c140c0031f81070b9001c180c0c00c20100c0711007101402c2e004500500b00c00c81030000d05070245510900440d40000344501712741e00c204c0041c00c112140321403018070703200d04000e20450340c1010800c48180d1b080d403c019054980c07200300540d00e550b480850301b0522882d042c810008a4480c0c0d005200c1140402421003d060b980c800711803c880050300f04415174842d49420f800da10404111820043c0401d461a90200500d9250192280202810034481e80c04040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 7540358 1250 7539108 7539127
    0x6040b0a0b13061202090a0509070504030b040b01080610050a060e030a020a03080301180605030a0303020703030b1002010e01061202030a030c0215030f06040f0207050c041104080f1b0a0e010605 85
    0x88080c010340740100e45240c0303890700b0610714402072a1a10401c0b01040d02ca1919841c541c2d070720f000b102c0348800080d0040354207030f01d0b0205118140b0801000030341008011300000c070006e0a4a070b5041e010305c1c0211550325055040c40d0199082000203082c040440b1031008040100ea100d14550004903103480c1026144080204046400c1a070017410082d44001e0b0711402004114040014605a44103c08504440c1c410071124004807013060240f560302d0342c030516800000900c680c0040880c07038880d25002c40c05080c1c140100301e8003600d18010101503515043c0070f003140c402c00d20814005004403465801e038001c1580100c1e80b9030301f00c280060200700704046140c0564440d1107840a0310030488424540e2450428002480d0740019904140700301d05016000c0e50f412024000d43d9401c03a0404050f0852105010800c0300070824011098202c4c802031100140e01002805542181c001c1603000c0e0141d07840c0c0c05584195000d4180c5406c4c130620b02102d050100c01d00c44103409040d5130107070824a66552030039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 7541608 1250 7540358 7540369
    0x6010b0a0203070c17010b10120203100504051302010806030703080405040207060b0a06030609060605040303080a0c02010b0d060501030203010e060c030408031003060f0209040f051909080d06060801140102010203010e06040b 98
    0x140c0161880320030200001d00320321009100c019401174000204020a80c82041101c0d196558100100041c2d221042c004c40c8005503000b140c100707035003400004144d540d031008071f070588504841d08850700143c841c40310300b5541c1044070668800d80c01c4000d132009030305543d2408068007403405001d0040f68041010030403c0610b03401940c486a0051003000b440d039541070000c02800460160311400b60510100042c00d030f00441c20f03a015291300d912000c00d2a40e445203207100904001e000c5130115034039400f1014468450701103151546000f11404107042d030541c01450b0030f41d030152106c00d03164bc1c040c8042042c2c150759030b4160390700075500210650352510b6400c8800440c40e034075000a401c091504090130b803041c0c0554024005d40b01c054606108048002101c01c0840302c0803188800c50b841981564034070444180c1c402d1a14030301c155034440c20207000c1c082d0310084404680003900410035040042c40804415506d00414240c02d2009500d55130604812030649034001c1d0040740a60740344c080700d92480d2381c0e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 7542858 1250 7541608 7541617
    0xa0c0b0c040503010e0d0f0201060b0301061b0c0f030c080303041a09010b1915030c020c060c210307020f010509030a0c02010c02030f010c030b010201090b0402010804021801030305120601080906010b0a0203 90
    0x200240520000c26544a1b100c0820f0344100b000300d50808080c00c8564018064601112184100c0e103045038030380745080c4d442000319189000c080071600d0182c0001100c1b000c100b4060240c107064003940c58218501650306c0001ca4105071a0341d40180100800034174500718000e07200d00c2544140c1b46c69100d070103101c2d0140c040500d02c0d07540b0150381034480c440f00d00c0c6100c5000440344900b030031403581c134800300c1c05a041380c0324001d4140050f006044010343e90304012004104944821003100c2d040000d2080119141031200000c2c03000020010606c61400e13410000b034220441101c1c000c01840c00c110424541e0303441002030600601010403141419a130061001052664024064a80300c01e04261114028401c881e1002c0100340342418855540d40305205554541d03a12140c0c400c1c080e1902c1c0c00540340050020001c80c0c0c0200d000101000c101400d01c4840d00841c40f903100c00341c0b140c201c00c40107000c20800030503041c100039504080103400c0800062150440c0c1082002139941d00c2111002c0703055105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 7544108 1250 7542858 7542869
    0x3030c0703060207030f180902130504150302030609030f04030204110418050402120c01080f0a061d01050a0e09062403010608060906090102040b030c0a0c020a030b06010305010504020a0c0b0c04 85
    0x40c0803000000d01c80150020b00d03009101c2d035280344105180c0d80041c2d0745044a0b00c3c1a03c010446650140320186095000300081240300c50502415507542000905440e2070130644044030b182d21204000714101001955006030990014500f800c82e851444220360085210180c8034070303200d0360907440c004650011a40a00780580984052040300402c48010f0041510100d00801070304022100c4100d01040c0492403280582d00c1980e903885214103600e032800c016068555050b83c0b03801c000b5003800e01845400300c80040d151303010001d625050801c0004d20255009008c121407110400080703900104c1c2050380b03c000303803984044594000d8808003410310740c00d941d650198609a00454252000504503124101c03460031a05169129002c5909034011440ba184d160300003807000c030340461100d4004e49416411490300204200741600041d0429083d940705560107904038090100c80e5900d401020301404095030700f903182500296005222100003c00640b80b0129500420210000302044400410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 7545358 1250 7544108 7544113
    0x504080a260301090e0c0102030406050706020c0c03030703090311060a0507060207050109080301140a050609010203040e0717040b01150e0109090207030302070b010e0f09060121080c1005061002030c120903030c 92
    0x1a113418603600140301c4040c20b0302e65032258a8101400358800022141a540d01d90383d107074103015980e90745030060340005d00802d40e5801840500c00350f90b02d0420141c42030501a81e900e0701164a10300300b00c42007107858180da070b01801e030800c0244802900300003281d08041d07010200695030390b141d00300a0300510404000500c0d04800200004007041c1c2c4025010f403016048804c25246540c901c03c00030f25104405403240542c00510041018203a80c2a0044e40a4041d081511100082c85001141a50b0498085130b80b00044030040c001c1070050020113090b030311181850002d00081c54000ba1201e040d5200300c401403a00003070030300100740c40303901034895442d8004105403042d40c4502c504c400c0360204845a02d842ca518100041101400061290480d48100101412041c0c02e04040a1902d044d80058641c3c130001c000260310510100410a44121000c000007524104001046106075540704030038215482402443c0460b2004500c0c0c00007600c40b0f071007155465503244086401c50081c03203c00f20260 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 7546608 1250 7545358 7545361
    0x304080304110d030e040f0501030c050405190e01050414030304030207090c020109080c0d0201052401050a031116020906010201061a07030e06030f01061404120201080a0b0409050309100504080a2603 87
    0x42e0171401580d000d102c11501070044c5401e1000c0e20302100c20900c40982a0841e20b401003104d41050b40c400da80200000e02c00708030380c294582c070880984509000d070b600e0a03075450341000700f404000065141c1f44e00008001d149076003420f49000b5900d510307a01640485690b10007404502c10b000b507110202040c0d0110071151602c8480080f540c40300c24031101e100c003550901e00041d525080340748405003060f440c0d200003103420600400458998220034689024942c0d00d107144290503013584054614035100c5620000381031300030b1050086042014002905580c10010b0612520f8641c0c480201a08004d181d10380d210038070380c00d04482c908400b01400707070081c1c40001400340300101c1c0000300c0d050314100e459400a146c800705188459110340d20449100300341910041c001076103d1101075801c000380000100c0c00881e400c00182c1102c40039102291607034000554401c7d14240358030508084030340390809504180c50038170300e03546038118070350001e00944103020580305c03a81d40c80b61280c0b541010694102c1d24fd = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 7547858 1250 7546608 7546613
    0x702010816091505030411030f07030f0201090e0c0304170c0706080606091203030109060b0a08060f12070807050306060301060807060c05030c10020304060b09061309060f09060b09010801050105060304080304110d 93
    0x45900070355042e0b804207c81000145541000200075260b0940080240742d41851034507401e4909041d0b4908034100401500005140f4960b10f0072079025001c2500300a40e00d007441d00c0c14031178890030842000c0c54814188660309203010041800c50488c0c0700c80c203084609649200014500d4803440007041e510203e45895911036a4002029506848000000308402c03030b22501c070214140640c16894000a00f1100000c00c5070401c5040c000030a100034112040c840e4000c1145401c0a04942040c801940195010881c07842d00300031003a00a075003034001b00010b904046000d40c80b400d46000342400e00c012030390640c0410a040088440b0624200c043d034054040050181010313500c00e680655505040404440721482c050034614007480d0000c00480401412602c030b00c019008200d0306541d110b5a0741950004070049001e030f440e2640c41064001001d00345002000000a010303003144200d0303807505d4010702ca0b50300d4080880b9000754010b0041c0d80c580e0f49034500381c13241c26001c1441070707008078819006d00c08 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 7549108 1250 7547858 7547867
    0x605030607030c0906020705130c030906060603020c0705060405060714120a03090309060f090501030507020703051207030305090307080403020d1104090b070807050c06040206160f03050c060a0207020108160915 92
    0x704202596500368034103a8517101241e0702c1480d0f00a0691040ea0070400008604041c0c1c0a41c00310320203030801142c01d44803520307120101e890b1a0300c00804a5000078401c2d40d20801030180c0c0000d080100c50940c10942010045a01402031404c003c2002900ca01c110385640001c00145030400102d0401d075548607504840100034000218044001c500318140103d161030107540d0781c04a441403907403190741c01494400110301070040940f007003056000f03101011006c60400c4c460090290002c0001030350b00d4401d0718000382100c800402002041d0818040400020620001c50b82200c0c1c0481701122914143c0c140415003001c01d10340e456000d03140450080811500318030b8184200015100d900c0b0030340d10800181c0b41c2d84110f041504444d0481d03000207005140c00300c040c0c28024203409101e0402c44055aa48030601e4100d0000d40c08180086500f10a0346000c1103090782c030600a05041d42030000d254000f07000350307801620001100f4880002c2c0000e4501c14000c0e0002440f662440009824884d1400340 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 7550358 1250 7549108 7549121
    0xb0603150a020a031404050c0904140d020c09060102070503060c0f0904020c100c0f0f180b0a02060a0c020312070804020409050102040b18040b0a050111010e0304091407030902130b04060503060703 86
    0x100840c5c01d00030716008040405100a118a402c41c01801401452100304a102000104110f410100c440302510200100b001440c3c3c0710b840c190010036185140b0304c1009003032103008240b1811540081c13003d00c2261000314510f904040009030f842d80740c07215410400d00b503005402c0401d8000d803020a881000c0c83c00011059204109440c0410040c1c088000c2112a20a0018032901040b85218150f02051061100410b00d01100340c0405100c4d0329813200e140141e002c08540c03001640008113102007400c05200704003110030035000540c644204c054003071101f000002c055009001270314001805540315a0040240198400700840d030300d44e1105001d20280c0c001c03407100d40d000c2040b5407141c4e10794141485200d50910004258502107894103004554420035102661943d54031020b2006080780c080018102402c0c003840040f61002051100260701040140340380101410400c0000150f20782100c0c2d0a00e01c20905004070b100b41c4030001050141c00e442d80040d4042c4200c004105140364160b00a4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 7551608 1250 7550358 7550377
    0x301090321140601050901030f020c07030201120e060105010f0c170301090b0303040803030112020d060c02060601030c0201020a0801090b010216090203010312080108030f18060d0603050d0c0f0b0603150a02 90
    0x590aa0009110000c110b40401021100d0700c4000408109658001c0e130162041e403005150100d00d0b10f550150b0030050340c100c4241a000c51380302000c140110340c0c01801104040c0c4030311204000c1180d180c0030043c1d6a803018031485040c0031341100d40648882c81184540c441c140c2100502038020503001640c0b500b98024410204030502e0074a055900c1e2802208540450714980000c42c15642014032181c00d1801c0c6480480c0d01c049404141c0c00090721134040c0700c5045540d600038101320f1601c00005030a443c0010100011a44100304c142d42d0107410000c414103480310003d0000781ca0f24800010f078a0402010b0703407501803922241000407112303410340045068900c1880307880743d08a15840142c548940a0080a0082d003082c0f0081000e0b40701078001d0b00c07140210034034001850640703c0200b200c541c85007422101264440609000780102001100c408a14919215021441d80d849a0048080e01c40008005c140200045112550108001c5807121150f680501d002d061160201c0020752042112 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 7552858 1250 7551608 7551647
    0x7020612010f050a0e040605070e030f010c021203010302030604030e0402040801150305120406051204080f0a030507021507020717010609050106090306050a02030105060f1308030c0c010e030303060d12050903010903 94
    0x46090300b420034000b0110303403010440c40d003240c07100d80d46c7d000030780001072501c020825a0440c011703003641c040095006080900b400020004942d40cac00034101403070320309604525802000100010307100003514551041d0145031440a002c0d030040003c000e4840c590041200e98200f0741c1c111003a0030010f03411801c50748903901300d40202d8107901001209020b20700c11180401d80502020008000e0350303000300d61080c0f00c2c520032072801c8943d400c44000b41e0062030701200003d40c0d82041001080d01041584c117000320080340b00310645000c0340002d540d00c00b1400b4091000c890507024900c01107003504031501a2070000c0e03045c00b1a60311064002c006104512064800a041001140241070b9500c00ca0b416500043e041070b01d030000017512003c965000c10544c3c20641c140210004080750188098140c50006078043c00203014442d000405052209424911070f410400c1848096aa4a19424140c0c1d0740074a24010203074007514150f40c2401408401d5400d0750801a0100030980d00020900752006100c44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 7553964 1106 7552858 7552889
    0xb070f0c08030a0b01030e0c100f020a021503090d080108070b0702010c0c0905090c0604050609040c180303090e071d01050309160320060a050301060f050702061201 72
    0x20f0a6a03029910b007103000c000d40c0d00d13025a07140107104400a01e8002c28040000701502448506801071014810015030703000d00074402000c6442d0018041035402c1e03403c3c080075445500465160a6070b00450b9003450550780030741c4c46981622400c20003054020b083c030710304c2016039001c40810307414400c1c0da880d114000f8181c8040ea1015101c1d00780e01183c1400c004510b58034140090807110300c108010b101c20300064580700155002e40f5011100450850760880c02500c004c200700b040f44038081c1640c9e4020041c5600304040c42c0464004000bc2416699502e00403140703528442c0071460241030b007403000362056100e0006990000740711002d031001c1000c100708680c10b00d03c032903000b180c08020800840f4414001e0903085001d684040d078150b4908130070b94000500364481400313100d0520002c284200845441042a10020340d809031150b0f030345030f46a0041c56403c038030910610394000056078 = true := by decide +kernel

theorem cover : BRFrame.Cov 7374108 7553964 := by
  have h0 := BRFrame.cov_init 7374108
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 7374108 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 7374108 ≤ n) (h2 : n < 7553964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
