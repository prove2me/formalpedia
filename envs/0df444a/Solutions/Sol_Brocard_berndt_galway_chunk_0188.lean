-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0188
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:20:03.952836+00:00
-- url     : https://prove2.me/submissions/f08c1a93-b022-42f7-afd1-ce4a9f8a2fc4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 33633098 ≤ n < 33812954 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 33634348 1250 33633098 33633113
    0x30f060b0a06140706060b03040c0317130918060f020d150302090f090f2d0a0305090105070c0503010c020c150405010512060301090b0c0306030d021b060f0c101a0102060601020604 79
    0x3984c5100c3c0800252651700d40303e440f001a001a80c0a079500940d05400f0f03c1045039821000c8030003450000c8003801c2501041c1381e40640c01c030500038030200070380710310040e040045501d41c8811030541c80740302448901c20f03e54000740250010307018800403d0034804100d10300d803610f072000310035241c015090800c01d546070030110050707841c00740990040e40f00b000780c49800283c05103c200d8128408994000c1940080b2200f001c140300c48410760b120540004800f200000e80180c03c4a08520b02800c3c015121001800c040b1200707d165804150036508013401c000c000d80d400704d00900209000c582c0d010145051b5180d003052030046010301c4d4042042006148800042c04000d00c2e44180001c00124034400130340d85002403040166552041c00c0008818814686410301c400c42d40201103200030300c0c00042c1440409020b01c50011a280507030000149426041c440408680100b00c102c4101c401d121f070380000701801444004442090301580b0385482c0619032001c5007a41c02144144e00a14841d225504c4070395 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 33635598 1250 33634348 33634357
    0x312070206040e1005010f020c09041410020d022503020706030518031801020609010b030705090c04030818030705040b0d03080c0c190203070905100306020f0f0301030f060b0a0614 79
    0x1e03801181880001181850800e04034420482c041c8582d60313103890328001400380a0072649201c250b4000300501c20064480264099200d0303000300c000781d24074007a0f040c89803c10000f107407100741c96400003c034503410359140d80007405c0d1400d04050782c198422011170100800982420001c00680141c1d4041101c0d41c402c1c0c009a41241480314441030f00e080007000e051541e0f0118941030180403070284824815a0140302d1594407988407002840710b80311046c00651a03000c1c03030103031900c9210141c002c2000002c031035041e01c0c0516401042c260303946041d4000c44003881480f0f40c400d4824842c6610109040c02d1034090800821009482d440801e140b03aa800d40d80310100030b00c0002510310030300c40c000609004109a41e141c03032543d1081081c144140c0181414480719420000450b0700b80001d00c0328a24010007060100c0c0d421031801038031400c2804000f0510301c941403010103c414048008400d02131419059500d5502c5a4010006070208406000240c3c0c03031361059401041c055482d0140384d008200040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 33636848 1250 33635598 33635603
    0x30304140a020105070803250c051006050604050d0615081b01170a05060f09011503060f0609060807020a0b28050907050411070f0303050117010b09060409050c100206150609031207 79
    0x45040310200c03240202c50f40c400d0f95400049c014242100c107015042c04440c038022031029050205074200f1300031402c41d01c42c0b80709950250b041007403500f0030b208465000040d4805038429581c1d14a40d55007071540d81c3c5041894190310700c00451a0036580e5070054280005059030107003400000c2c1d8070707103083e0001030400070700c41c0e0703004003e180d038a000703559035000c0032800b804218020741d2420498040040440c1c070517030045528000440000c0c0b201681100b0b050007100d01c41e250400c90380e60b5100d4100d0400d104103100501c000008000d11038540158850340d45110b5910000580400b002001c0500340d810039942001d03190480d080501203804c040c5c0100765400810b0b1006071501e1000c0e03440ca6025030804405800080c1cad20001401904890105c150b4948280300c000d00c800d141007000122403880241801d88200d50391043d10040202c280004441094010010070300c001129101a4407224211400b864a03544020140034500c2c1c12400d0351442140500140411002500e011800c2d83c01818203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 33638098 1250 33636848 33636871
    0x3070c0302040c2313080a02060702040914010216060b0d1a0a02070c080303040203160605040501180305030d0c020706090e0103080c03090307060309050d050f070b27030304140a020105070803 84
    0x190b50f07109100345405004020111381913542c4c0c16440a02c9080c2c40c0160040700a40e040f1841c00700c00750303940c04181c86259170100c80024203c401460070200c401c0840300c080c04154004110401401400408581c002d4002d4005120210700901003103220041a0b2000b01301d02024210f200c140000901c03600c0e40804c0c411001032030500c0d980c03150034201072598400310540d44000304010442c01c050007990421040010090049401d0560140650049000b014100001d00d41e83d1940703855000a14402160030605a0b82c1d255800c40910026000c3c449000c0094401c010b00007070072078840d04000c41290f19448016401e0790940d07441c4580c42c0c2c048a22040144004d10a820390b990301408024001c2c2070f56200020045564074090381844000046103090080501071045130403001000c0b21099544240d48035191b0b540d180300006650001c02c048084000300d2a021b4100440010007140214007074400311301c80c00000d101c03141c0e5548030f44030004d00245040c000c40c1c00249200000d1342e0050390080c0d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 33639348 1250 33638098 33638117
    0x709060e1c14011a0a0f0312030203040c030f050d031d0307170c0d090801050109020a0e010e0102150a020c010b04061a131a04030308090f0304061d060304060504020102070803070c0302040c 83
    0x326401e4441501440c00c1e0000d10504528140c03a080030080000d00c84070269101c03847c51500d424040d100040980c1c014150000002010000b0444101c00555803016403e900b0b0495400c0c0180e80303600034484080820310740790060840c00b203600381301f03040054284000c4d894881d699484049030801d00c14207400d4035009011000c10b4000502501c02c1c01c05155841c0030f052860075001d1070a44a0681c406070041d481003150201e07495101c81030610703030709003802c00070307003144440b030040303103042c510240f1503098002c0304050082c80c0d04150000d00007540c948000b80840048081040110b5406200701c10620945440c4030b1b80381020303040503180888031a54003007016503498500e47e03c40700c1094900d101a110000e414820550444003198008580c3c3c07000703140808d410a5055600d02c01c6010f224284120a21843c038501e1a580d0075203555403000c0d241c0c544900b450302c3c11001509003603c00728054040e00002103980a00007041d00c903095000101508003d22350707028031000300612032681c1d041024400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 33640598 1250 33639348 33639383
    0xd02040b030a0227030d05030903130f05011116120c03050d02010906050f0402031002030903040f0810050c07030c150e031611030304030302030d02090d0c0b030709060e1c 75
    0x186110303111202c000f69403a132000c6081d01324010100700241d00001c25120101c11520005880301540001d410625501c0d166840501d01e14013a41d510101c04080c50031000c24034403c03110b0550b04641080e2101c0c0700c503003801c80c061510b842440c4507441c20156284010000040c4022800d142140a140880309403620303074540c20308202203000020302603912005a5000c000c012701c100b40d4441c26000103e00d490070560300294603007400c00c0c1c48014103034002c808552014020305c1110006c001c14440c00d00c060b5a40c4032034540340c0b4140d440c04681c0614010014146240d01022203d0850307261b900c00e110303030702d1980d0380e001440041c1007a440c0d9507543d080e01150141d001c00081c01d61b4004007400107161a2149801800c0004c62000e890107508140070400002c3d80000503501e200032014005a2503050b41c101140c00e02d46000406000403007003000005881c42c0c3c0e01c4c000d41c0161250b50306c030703000944c5a02c0d060b5012040c0e0070100f03800001d28008502020315841030603441a11031902c107100302c1c0c84003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 33641848 1250 33640598 33640619
    0x180f090c0e01060806060901080609040305130311030d1b03031a0a03110f01020706020c060c010e06130b010b18010c0302011d0c010318080403030c0f0b0a05010501080a060302060d020d0204 83
    0x2a0071400410701d00700d0051003400d4020042950241e0121910382c5009a2039000800c100b80283c21140100520400305041500840956840303c18410101420701c2c1d032414429504040c680c0c1c01400b13402102140400c0500c2482001c1b1308000405040c00f030000c49540032070050282000000c10b800b54241d07403440c9603407800b164200441c000c129043d0186281801c120802d520702a146040d9404084100450307900480d2114400b2421101a91110036444002d80502802410280b045c0070f0141005040f48540c01c014055034004c0c81c507205207a80b100790b08811441013400b90f4000000201c5032888541c89001c45191803440307480040342c00c194003000d04051040007880d13803001e074104101c0c110303144d43e05118001240c03100160300078204416403030304032051003a4040036003009812034410050142d407101d0b6034001503010411751075074034190b41040000c1c5000e0040500044550b004564461440d016100943e50014515841c204200d5400c1000358405109152029001d020018031070168 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 33643098 1250 33641848 33641873
    0xc0f140601060c050f010b03061801020c0319080106030605030a020405070e0409061b0201060302060304060b01050c030a0302070308011401091701110c01060906050123071406070324180f09 83
    0x259103884000654920b4468141404081e864405030b2407c0c0c0d611000c1daa001a02ea50070610031186803010081040855000e407050740010805803200044107540c0b182d090030f00b0f141e05107459440411990720364030110b00f52007242c0b14041d4103500002850002d031600e90f1200d60801900d04020021078a42800705040e102c0b000c005503486903903503082c1c000962105082070101c4205100030425039065500003a05400090400f4001c02d03514400b0320b4160340a04100c40c41840f000d0101d0761240a0a0002030180d800144100c2c0001c80d03d900024003d080c02d00844401e250507114104282d040c040c9520820780d09000d100b000750f4941076034030041207a81c0005d080d0f4540d1040041456814105258155203042c0d01041c100100e142444010643c3c1c1c18060900751a01041955a08801d04101d2640b51200054a806005060501501a03007591104500c17240415240356500d01111103600d0411061140200b141c1290707605440b141943e62240d60100c0809000082503485a203130364a80100723 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 33644348 1250 33643098 33643109
    0x5040e04031e0912140a1b0503010c0e18101706011706091f0603060e03070c14010509010305060a0305010507270f0e06010306030501050a02070614070c0f140601 71
    0x71640d02c1c0c05001c1501c2d1012002040d6400c107290701614155140b801d545080703030017030541031a5030280c2661400a01c903000803e904980d184103071104250702c0e40c2d620061072180321311130740c84e1030821101940107451a00342100014008000540749401c0309003440300080c0708051310f5202c1078010501d0080c0c1d211000c0c4500945005043e01d605000f0088915000c4007401c41c0030394070003410030120b0000003c03900340e0803500c130020b41480b034440240301019041c6c80d007000749800c2c140108519003010000250422038028010744684035650310141c200300c10400304940c00140100105c00c090f50083d0020390304501f02500c2c143d030703040c0c4d29100c030350859509451400010702e03403801c1c034181030b1803025010b211070f02004008984503182c144842d0610000c1e2040d200308007842030014031168003d5020038010340d000002484140b510354003100c0254407080c4104e40d1180385c96001c0c081000c402c3d0040e8440c010544a9030702003120303034032021421110076200300c1c0c422000342c6c0c07018a5044140040307402000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 33645598 1250 33644348 33644357
    0x10801020903010e190821040f0b07030c140c0703020d03090e010b0a050a030c2607090e06030a08031f0608041106070b06010f0c060e0a0201030e060405030909060105040e0403 77
    0x210072810103080d15800c1c211083d0395445039126503031141110244103031160b172003034101b5a2910f0a483c1d4070b0807810082181d81004107000100300074030101c154400441c500c1403004042c0d544c1c80d20383c00c1d4200e680005403200096420211040002542c01c000c00405060004444201c1d507030b40d00280140c0142c0d80308030b00081e812a01006001101c0341aa400341c0040c2c917100d070030f0140c2010300800078021956284101904c541080500a00443c24003110030701c00d0079400007600c0080481c0d90712242c05c4e50000c1c0081c0020030300248940c0f032503103a5401038100802401080040782c45c0c0d0109504007a110b81d00c40c1095203100481125680003400081c0340c0382d220040c441c074060804206500c1c1e0a5507090185038100301d56000241d69a814660040003420a0402c20400513400c8924240c4a1401040b1603e81010b00a44401c0000c501413070a05c00d0360240900142c41c083c050b190b40003a14000c1142e4030030321500a071450561551076100506141580c00e0541c2c941001c3c9489609a80c25404034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 33646848 1250 33645598 33645607
    0x110a18020903010b010c0b040206090d1505040309060906090b030408040506040810050a02030403120c021204081b0d0b01030f06140106050703030e06070f08060a09020f0316020c060d0902030a05010501080102 91
    0xa09082c007403130040000c2400d2172100308055460303000707035800300402c0248215030005000302503a43d250800091650808441c00540c000c0301001c03070082105035006d0b00490058540000c88501c80c2c0100710903202e031a616803204c81d1504c0d540c0c0c541e40d04040c6c403c031055501880081407503106d02c4044e100502d1041c000340545164044c14808031400a0a05458507004104000100340c000e000d00e0103800c0500c00c0001e103c91101c41c2203080980d08004020403860000d40080c61003800140100f221800c840f40f2402240e404003000b140744150341000f40842d41c4c01c00100b01140c51005401303023441c05070307101048050140029280310744003608035002060001c55144240b40c1c0c10301c140c3c02090404401481d040c01c0604001e0100c0c41700e0f8600d1802c008100001075843d4844451400041503160f50540d02c0d45044407184006800c11110900d40ca02e0180010107001e05c0001e4000c20981d01505039858412803001d240c01602140b071041e81c041c46141c4030b4400060091240c580280655000140c54 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 33648098 1250 33646848 33646867
    0xf040906050306070504050621090a02040e0a050d0809010209060406030203040320071503020c0601030b010303020d1805010302070203010e06090105060a09020f040608040201090f08031c020313110a1802 89
    0x31a1640d4000300d009502040400030600d03001822a420384008813800b645407500c0c00c000b06219a1001c0c0c0301d8000f9402d0f5020300881e8400024440d0342c561088030144440c0341e0050020755200c6c4003a07409482c0d0b508c50080c40038014081c190660700001100009440c3c00107800c0401c0b4164401e5110300300103940082000141680655001d038040c003616440c0c2c51802c1e15103540380d5500880d000c0c0384001d103810f200c241a0030b4001d0741112401d900300816140d05607542d06001c51419001d10007a00035004da08280d2441500c102e0311a0345010203100412546418880110003c2d008940200c1c0c15650351034220101502c10403950307100d0388880001041c24502103003440100c54141d841074100e10700600069160740110300075581600c4080c82d004001d40d0352400102e0700d10725143d01003803617003405506c08150b40c0d10110040c09880d142010440300d4490003403c560481c8421a8110880c0c86c0d0980d40000254000c40d002c0042d2708028074003001c285d00da24552324408440030104901c0e0b40e00250300602c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 33649348 1250 33648098 33648101
    0x308070515090a050a320a0201020d020f030d05072c0a170303010b0307180f030618020f010c020111010c03051503070302090f13060204060201021810170415020f0409 73
    0x600a02101c064218a81140e4419681d40800907009040d080f20300b140c0c2080c4914000a1b0319991079030005520b8080036a814141c580c0314817001640140101482c050615000107980460183d4000040d46020b03122102e010051202a1064041040a041c10400d014a58408001c941400980440e680301c4902c01c200e8441e40540c845244551018103c03190f0000c0402641d044544e03001005a40e6a54000308844510300007100c03a800508020010408042958603c0d090720b101311001c000f10441c0c2900c0f009051500c2d0b01c02584001d202445220079486031581018a501c103043c00d03c1d074010b00c12900350966208c40305500c0080d0b510380400c0390314401207614101c41c01094000c0c003025404d5401058644a00500b400c900c00703411008100a189044229002e05400110454a884d1540381c004c2c0030f5480469000380181200c288500c46140624a4800b60065601c2d810f04085010f404145d201c00020710541e19128465604645010305000500078074081510131039895080c40704680 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 33650598 1250 33649348 33649351
    0xd0203060315010501051b07050a06020a030206010f0b09040f0b06030115202a0406030c0306050a060602030d0c0201090501061d010609080c1e03070b0d060602060402090414070308070515 82
    0x1082e1105107401088a40d030404115450680c82e2100e0300c6103481884d290920b0020158080c0350002c04080d400150340750b01041c9004201c0c07103603090340c8050340c2e2140c9010801180d406981c4050004110007091490107500481e503141103107102003620301030000080c0450300240d004110315401e084010b00200da100c42c0e401b51540030a4220b444007412609026950083d010107004030f000d0506410b010100d01035a40005240000c00a200b034944034603110001c9981448102e844a0400c4049402c620b2513029540694a047d0700440c240011500746c403010f018194040c40c259566881c41c14082a0b0a0040d0805001060f05016031f01008401d00000340c0340581c042001c1000961051102c40000b06004200f80310032240c41d000d0540c0d80000c5611001010001a4940b040020024040100ca030241451070001d0108100495035040241d0b180c41d0105c50080d48440b0080005000440b900d40314904e0448600440305440e07180c2e03940744601c0c0d014607019581d0303901c480c03043c2d81c0c02c41c0641c285c0d5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 33651848 1250 33650598 33650623
    0x6030a2309010e120d0504050a05030a050406090506071101032301030507051206090c010806150310030203010c0f0e150c03030c07050d09030f17190e040f06061d0a0302060d02030603 80
    0x4c1000035400030b6941403c0c0a8070500110494440340401d041c00300c104040d5103425005401d5030789d80d03000d803940503005610911a207c0070881140000915240600075203090580203a44190f00510050044000341382a022002c4030350308610844180484001070030340a14402c00003407030b1140c100f408116901140d002c0d4101b50707921410802c82d203400c0108008500340c40c2800c1014443c0c60703190005105000604111910030004001c01410340465441082203900942c000c0000109071401200c065540b24501da0215007800c1d205c40c498240003900348442c80b07850f0103031b40c281980071903100e06691041d101d074075049070007044c03003402d014042c41024480c0c0401c3c106060315a24548d40c1c08018010781001a1000000840056040500104456401034901481590b400c0740a101410070000000744a02440c54000f02c442110040d01c5190142d0f41c0b591604490450300420712441010045c80d403030b0b00074005000000043c0c84a0010300b601100c100000758a034a0700b00c003414038145026200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 33653098 1250 33651848 33651853
    0x6030a0e0f011104141f081e150108060301110405060c03120702070608010e011a0702010c02091009140705091002030906131809030e010507020f03030406052503020c06030a2309010e 80
    0xb5642200c0c50080c246c880000c641c180501c00d6902c0320490b1104040e07840302c000620b4a640c041050f07180c80c81d101541496000d80303600000340c59441c181422241c9000166064800821080c019442d103400604135000d411402c4a25003810f00021452004056820001582c81260305100282d04a103a903400741c003292003410b449600d802c40750303000642ca20304044442107000807641e0669101e0fc601003206900a41129141d0400b5030782d030340784c0314007070301c91619500e02c1c00c2c4640150300c0d42002c110b40986015561181000c100b0020007001003250700007039042d44010494814a5107524001d000d00e03903090100051400d00d00200c2c0c03060030041603817102d800b61400b2800e02c0000c0e009951065010802e2034020348032200c0b403011a520844d01c0e404942e0611000c14002101a0f0000060211800c61604000b03200907182100d000c2e10034000006000d83c002031501019414401d01860b030000401001181c0c0100202c00d00c00d0340c08824402c00a5508204100104da24090040c002c034600356800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 33654348 1250 33653098 33653119
    0x2060705012705210c0d05091201020304020a0b03180106060816020109050718060513020d0b0a03110409060b100c030906050403020d020d0203030903030f09090606040506030a0e0f01110414 83
    0x440030744a03091031074940d00708410540c80071100c3d884d480a0b0340e48418114201c86005d078554501801c5504503840403481106504084010060103001f41c034000c0d540500100349150401d140307519543c00080849480000c0c00c108104046824014580140034545841c4d000c0e08011009400b44045003040105581c1002002800641c0005540c021141e103000c200c0d1440f81e41c003000d9130203000d0550003580d0000483d8002c3d501c055182d80205060359208004000c8000f9080038002c861110744000f62075040da10b1424052810709420034021284907100008110708000700041295188902c52000100c091122004042d000940c00025004505000741498610340c0010000142e0310310090180989804c202e0464400f0401c2d14003c1c0c03001010749448005070341e80f000c0c803030304682482d44c80f0740640c2002ca1590b04090003220141d8802030242880c59540141c4007001c0c10889601d14880d22030a648408110420b100c2c03200034020580300c01d59502c0c50468400700004001403894802c0e5082030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 33655598 1250 33654348 33654353
    0x140703030606020c012606030c030109150e160902160210020309040609050c0406031e1d12040302010c0b1312050a080a020c071a04030b010306050f090c0109091107020607050127 78
    0x100300c5004150003103d01489540d1f04404203003004940d8100d10340540c2400580c108021500071090316050606404002c0d12900320003035541c03054100070f9000c2c598225042400340c0043c5030020040c40e075000c00d400400c180b00b40e001c1044030822900c0c0ca03005030004aa480100c1c0b400340a0780d8001c1c20840c50a002506145003010078500c140d110fa0f909240e0b42e030003241100e035540c5602c648000040b580410024804640310242c40b1180c3d401420300b401400401c00d4460001010b4500361783d010303504d5010a2400d907403007140580000c1c0c20055101390750816035001600c00d03040c1c0d40710408a030b03031803688400303e100d00508030a03005040202841d006102502c1010300004a02d0121401d0640c0c3c0d104460181c4541c0650b881190006031510114034000710034080540c0201d409400348072400140e59442d240040e80f50000c0102107400107404503410880d051281e00720710304020070f5102c0790345008000d41c0040c0c0301c0c1d070042c3e004a41c03d945030f101e66111f100c0d405444180c0241101c000f070b03000d040250b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 33656848 1250 33655598 33655637
    0x40e07060806010f03060806010b19030207080301030b040206270307060305010b160305041802040509010602150c09040b0d0c03061b02030a030c03180f0506060409021807140703030606020c01 84
    0x200350a040156031300109010034802d81040000304040c3c0c0603513040c2c0d6191101d0703d0003a48200c030041280c210400102c018680b080c8202d50160307070442070705402d507421951900c21004019100744d03406501401340da440e8902d1089628481c61aa038110b0200c00080418103081c04400e50141050610f0036004115503c0048119001d03100e2068041440300c0d0140f4098445000c1d54001406035603030600603a00c6c2101d96401002502d40c1150030510031b80c1c3c1e500c012039542c0c07a07582c034000504000001054590801c07101400c0803410007400801d030350900d08041003032184604010364100e5a6240d04005019081c81440a03028500d0b180710244034505002942d02d200d01224603040598602002c0c40b070300c9c4a40c0c0300c00c6070b035450400781740344194050401010300d00500505072824054000810000d1800b4400c8a1115501405105048424207100003061200800520510240584001c224400c54000346038140c46a1000103440d410048001d140064244129040c0030401021201303800c0390 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 33658098 1250 33656848 33656851
    0x11040902060306090604090c0305030403051c020d0f1223070302090618030114090105040605010504050114090406020d0e03041d0403050909100e0115141216050702030601090209040e070608 83
    0x2a40c21304075549492000c5030040850842c0901940595500801000401310040003100d02a10848040008203d001d015a1844c030344e0031400b41c0d102c611300301007681c041d10741d81d074107203526040800003500da580b441403c0d10744421804444000b0b00d41b500e80c148100700b15140d000398152030b04500384440d00012509074400c00340c2c0034190400c0c140d1200d1442e0360940040c1039101c9040c0d41d4420b1800c10684950192100380d030204d500c2803d20b00080b03810f044c5849034170704a5503110740c40c0600d40d0317400040c07240450025200355080e907001c0045c50800801401450091483c1e02c0055507140c3c9007140300c2072981000d441c0c1b0307480c4080761010b10002c0781d40903040e1030f131040782122403509940302c090b88200c0e0903085510114020300c80743c0000030710052203c4281c50300c034115202c1c074148002100002e44607100c1c0c0540102c030800d011005c1640c20070035000140c0001c00c1410054503042c1c0c81d4000030f103045004d034081f1458940000f401d05440c1040d016154007841003d00505070b10307080030400f8103800b20 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 33659348 1250 33658098 33658111
    0x1709030c090a0b150711010e090c0a110a0c05011407030c0206030c0d090501020a0201060e01150e0a03150603060c110d030b030a061404020306090d020c010e0a1d04110409020603 78
    0x180000b16407061000d034007003000d4450060405001001c114046041c1d500700d100240c1d2030b181c40341c2030303c0d8503075004030304801400c1c200900f00c10700341d40c40e000703000e84039008503034008204403820f4004110f840d020007505550380c1c0103681c0c0020b0907142c03000060007038107150010b01c03161500340951340020b50031481c03802240364121192138403a6640380d208003443c003c605400050508017035440052080640c010000d8005540c003e102c0300703407202808107800400b840b4010640f10b40c008086105440b80107114142c0301c0003403c4400a681c0d94440b00b119030305c4461414506541c582c030400801c00785100d00d5480c0e00d40740c10801c0e80780072200415522180000410024580c070f80c000d030120355406001800b5010b81c006410480d519076032121074039801080720201d020f88202004141d00c0361001400080300142a4000d0551088000c01110b4a4500810300d54005400d040003140709070004604424900f007004000005150a09241c4200c401042c440b5000342e10b0002001c003d41c44500c1100d0780102d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 33660598 1250 33659348 33659359
    0x1080718020a0512100521060c130b0c0102030106020c120316050102160c080124030314040306050114010e010504080307060504140a0308090c01020c01080103021c05010501060c1709030c 82
    0x2042030b60151a540305111000d1004400e8604020701c90206170219426214283c81003038400c1114510305034501c10004246800f5400300c800145114010707402058207040c2c851b0320740c003220f645031452100384d0446030888469035008001440301076410800b9040c0d45030100c03140605901014800754892041c02c110100c1010680c46e01c0c4188082501140d2000181c60031803070700b0080500309580c100c0d03070034060605154284902d90140d40e1018040e003980c0d43e1521a101f1141d80b45580076541040d03280b03103a01000c02d06110000111b501031044500a20041482250070b6640c5000104500c4500c20300a051140500c0184138a410000540302c1d9a64030000c00602505c860900f1649101c074603e80c4561481107118010406501501c00380c02a0f0f03401045450002c050001a85c840702402d03200d500041e2004010409890000301303019022101200880b18813103203403505800d442d4241c00680c003040e40d48403e102000003003620201c0105103050468100004d0500090f141c910b03405800f4400c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 33661848 1250 33660598 33660607
    0x7020d140c120c0102071e021f0e10030902030d08042103020c030c030c060a0504050604230703060c0e0103060305061b0c010509010902040b040504020306011503150314060108071802 80
    0x1c004100c458601001499001c0e283c429090455020758000e0300111082e080f100c0503280a0070185071100c000a900a00c420b00d12154440e0340c00024840404280c200403900400c4912030b10b4065011588001941d4013090324100750051515000c00c1380020410400c1c03550400c804145020003c0000c00f8040500e401e407411303c9407041340640a4408590500d01000404449010300000202007409110303050740c01c541daa80e00c0080c100ca00031180070300752350070500008000540049003c1047e81030045012140750044d42e180f8a01545c0b5081220010340c1c440e8101295500080c90400e400d00034070b4181720290441d9601a111140640111002e00c1c03003040c500200050502a1809860060000c00c200c0c42c1c807454603070103000c10700820f0340a0382c41c1c2090b555850a250254a205603000740040010307900e041008503064142c1840c0c00c0805540f80f42c3d240c0c00f85800c0351274200540c0500325510000c4003030301005040240607030040400d580b20280401c6605c200f9461a21402101c01006896 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 33663098 1250 33661848 33661867
    0x30609060b0a0c030f02070803040b0c0705090103080d0209061b0c040b030307020d0f030c0203030720060403021c0c090204090e16060207030311030d060e04060b01030e07050f0a0302060a020a03030507020d14 91
    0x80c87c0e6540c0001c130043c0030216011a440403042c000e4a411003109045a003019907560030701c002480203000c043c201d44000c00001c2007038036079030b0001c260703d03031004c0c2c0070381d10b400c1c00b42d0043c070015482c2c1000600ea0750030085440d12180340a0059503401d810403005107240c01003039400151440072000000f4a8007078111003150500d8010b000d009403254002d015699102024501600501e14024040503100e4910116140a00f800401d44068035800b4003400000d1200c000120002d8040603422101a6003106001c00c0c1d641c00c50000d0001001d400c4800b00d150300c1c014520906103602200000d54402c0c00440c20480c00ba400510903045a03014204030060705000c1a50a09502c0380c0118007500750f050007000036800c1aa4440b443c401d070f004820030002e032906e01004505440365000c50004a5204200c140400e01d40500c03698a403000050207002c1036590396010451039003001d5540000f607040864110149038050044680c410300c18070280c100a0068035000d846501d0400545101c0c030b10101c0c0c0703180e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 33664348 1250 33663098 33663103
    0x60105011209050a1209030308010605030103080307050904060512100605120304050105180303040e0906070804050303010501030b0f040504030c201806010203090a03080c012304030c0201021c030609060b0a0c030f02 94
    0x1503154000205c0c80d0f1078503c21401900da4955403004400080c442d500000d82c42d81300b207050340d050300c2e8461a4641765440710381048480c1e4204150070f55205030f82c0d00001a1030382c3d503048803108104040000d0300381481c1d54010303441143d40b1580414042e0b804211000039a1001008680c113441090030205c2c0c881c040c0403c0f0300007100103241900e4041c400020040780c200f2144105070b129030030131f80c11141160396000044480b81e03010381d4000c005601c00c0c001480a0345c003a420441e5001e801034204015400e40c40d0004050380e00c02e841c00d41c00b16041014100c24070404c0c202d103401d04c807000320500c00342075202030110701d401e10880d1034007080c04090b80208440360700c2442140c1c1c1400c00244070290700c0e9124240342a950380000c0c6100281c0d8a4415902d14800780c400080602400c1106401c0309941e847d14159451514030038124110b000f681e01c1c100c1588a901174240c40d4800c0d560740001c0b0301d400c040021017143c13666044000e0040c0c0c140300d094045940841c0100c070b1640c2c1443c0c00000070b4801c050591 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 33665598 1250 33664348 33664363
    0x61506130b21010909020f030312150114040f0501020601120b010e04080d05102105060f04020301090b070203030610030204080c240a1101050624030417031311010206010501120905 79
    0x15103504030b04000151844950413001040b4000c45024043c0c02c60b45041680d248561060305000f51180d400240e8200c1c0a03540c952103219060512004090400482d03d842c0e40c86a040554000d4041505001650781044158050559104c80c90107041c3d04e07403a6003084440505c15420040f00c000b002034100210a400d607650000242400d2041c1e0400d846050301b242c140d8080d808210300701c03106183c102e00c00758124034501da0708403024019548038a01c402c080780b1b4006201b0b0b40c0640d06d5038810400079800101d000e00c20300c03465002d15200c0c2032144c104401c2140f07010100b8101801800140600880401d01c0c11000c101211100e0130341d4210b0700d0b100c0d42d0004001107054020004540008030340d822004d00005050828020001680d40104100c103500300307554861120007501c8641e002c105004001142c21034001c40d800c103004820300d410070507164400c0725480c0e541414240a00c0400c860701c1c0984108d600d0900143c0515810600001c1c41440c4000c00781c00d0240d15030340301c802030150601c840d8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 33666848 1250 33665598 33665647
    0x80c03150a0602010b03100b13020309030919080709021c020304030e030303070c1109040302070b0c01020d0c0903050f0105060f10090b0a110f0303010e0402010c030e090108061506130b 81
    0x140c912956081c01134020100c110310700340280500d8404a0141c04035101c0c03030405c0440200006503121032403144400a40005207814464401007100b05000c1da1501162851018110f160388080d509000301d03a401c014484d03210304401801445001c421038808003580d040d1100714600162a955507050072102c181c240d40003142c040c0000014017041540c042c045000d10340c007450300e94030748600b80310900051741e0045a015005800405043c01880c0b80c010081110900e018000350800c1c0e00c20450000701c0e4034107a90700c00841e424410401c03c1050501100c1051210b4100810040c6404004640740c242d00c242100d02c81e80e407066214140601400104002d00241c505060701e60400e014094031126038905003030128426503c44c0e0f580000e0001c203c84c140c818601c0700300d0031619103500565421b417191804405018803800365429a40b1f907900d40c81d000380404402000b007030501041010802c5148104140944004c0143c0b042c2d04051007640401c980c0e02581d0f86584500410b00384540b40d441c001e18 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 33668098 1250 33666848 33666859
    0x3182b051902060105040e07030c09020318030a0e04050c0901020a020105030c22090e0303070e1c0602030a0c0f110a0b041109040303090b01050603060904060b0102010e1f06080d080c0315 82
    0x7a0781c001c1e80050f1060503510140e0f402c1000302481601259140f10502c0010816495886d0a00c80144607402071500f11030102c000d1024010700703441050550b0018107480700020101000b01c040c80c0b8260155070342119038800580d02d0240700c0030000b5203e0505010103818854000045007000b4907030022500356880103e1482e41d400c00c00d41d00e510140b2024400c0054203810302c82e0304840d0850120071280105c405071982d000070507428040c445075500c0b81e052880a01c400030184408a0002c0c0000c51080025560003d94081480d42c0584884107030440e607820003400b4454240064000103072101c0c019082942400d580da16840c0c096428445400c0d515001a240400e0208068240c0c000a03011440782000d190b00740c0c0c85805100b1540002c0f83c5c0507502c04141004500441c40b10341c002003a19606100100e0340910505105213000b500340c3c038032010300b69aa460403480384180c0c03080501405a10b400f404911034281c00042c08200058141944048004082002c41164021407404036002402 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 33669348 1250 33668098 33668137
    0x90b0d110c0d030516020708150c04150e0103050a0209010c170c01090b040c0801051302040f1407050715050c09010503090a05060a05010806070905011b0201030f050c03182b05 77
    0x10028044e0400350b5805e1420030301c118008030014004104401504c151400030491003880500c1e10320317650800743c000c8480450800010a00c1c11004100c00c41c040001c0d01d400ca880c2d4a154001012540018103a01c08a481480038032144da03481940180095000b495a41e24024180e00d605954804c2c4180d07841c4c603601c1c0001a00400204009a51040d070180801d600415503810201d401e0b540c6c21918861185001002d00c8014a4039a00840d18240100d40028421100044030a512601503d240b004208041505000c01103c07142c44041743c250320341c3c02d12070f42c18002c4421010340114151346041c400080001081001c00700224500550040300710391041c01c0c50301103003004160078000c0401034081d600001e4903a43c0140c0114080341c106942d00c03166820a140c500090002c01c00b012410561240054050302c40355014242c0640305110b400da54908008403100c10308144001b1406903a0003203600c40b60182509035000d5181481122545501d810406040f03402c4d1083e4017240421458040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 33670598 1250 33669348 33669373
    0x20a06050f0c1603200108040305071a010602071404020c0606010c02060f070308060a060309030e150f130906060807140d1e0b010e0315010b0901050415080f07090b0d110c 75
    0x40030700307003100e0040e1545ca00001c540c480070f000159a2566280c046000c210201c1e0019104000a1075014054040d000843d4030180c0b0201c5640c600707900030b2006910a1078184410307040d9540c40a20220111011407070414214103d03a2030307500003011941800241001c031800d41d100c0c281203c1342860f041c1240d607903950721868050038202007510903038011301601e000451900e000f403141d40c1ca21a09a243c45c0c058070141c80801c80c400014840b0030741c09010038000220412241c070040d100f0b0032414154030b202c084c100f0908100303c2c3d0266010700304000c5110240035503141c11101144104240010060b80c0d24000940b0101071701e9031800c500c3d140d1080044004401086038016800c642090781c5140d580341d508820036589080030500c0070b28001c0e15000401c8101d20150080210b000181441400c0560b42c1c04414012818400100e000c140d020003003000c0ca03c4001c040070351005803030600400030390400d0480396090040c1c1603120011070b950010710164030701038025100d01d54903520483d02e45000c9074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 33671848 1250 33670598 33670633
    0x180303030c0e0a0503030702040506010315030302031b0706050d230708091509030a030513020603130c052b17040b0703080a020309150414030d02030708060409020a06050f0c 76
    0x1a04a07000040c42c8218140c950b140c051140c2e400ca4500400a604105075502003000901c806050030741855038034034039600c01c0400d8407071900040d806070700a03540705c044022182c8844141c2d151901910703000203c0c02d0140035045070507901402100301c0001a148003610410408821010160410422a4080018903070b400303604075110300300d000103880c00b455009512146451050f82d049995800a115183c1524401e84c04282d0001c5011012000f00341260049060780d0720a4880b0100b0b0a400e210035024080c4841d0380c0802044150f0318007a9981065821180c25403489c40ca084214071400200c07010b0000444049803071144404205503a20340e039180d05506544001c7e4110081108080082c0700c5040070300c01c0d240305500309005040002c502c40b2420782041802041250f070035186070880043d0035010001360100d01c6816800607035a0074458805050040020151031096080048000060326515401d904403042800c02035201e00a00034002030a01680030001118440c80c03102c03a0308142c44 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 33673098 1250 33671848 33671861
    0x110a0209010605070c03170d0c0206010b0d0b130c0f1b0206030103030503090c09010f150207030c0b030601110d020a2d080a02010207080c0c04061d010303050a050714010605090a151518030303 84
    0x1170300300402c000c1509c8103090307031100d500344600a450142031080d05145619600b08410300840100203040d04096011954115070400401d4400135620014142815030008000c0c00f2020021401c07601c2d10307030f42c6c1e8002000b034401400010204540070011910680c410480300c24016001021654203603160b4a12a00d1042c00d803180e036444110f4841d21018240c008590001500d0f003002c401c1c01039504044031003c187d8800341000e41088904011540060300a1058615890f0b032540a84417894803410320303019645842e5481da4400c130220452004180b041c004011540354841c002039111204070206034024040c15030041c10821000450b0510310780c0210341e00601c3c10341150b0030072000b5115150450007002040340100c035000c01d0801403021034081d0010704094403a40c5040c524248066031a40d02d1a4070048200125070f442d1203052210b03150220180703520021030f0000b0001007985000b110300c49100c500c50900d00c00c4480300c041d920710344180d48403040036109039240c0549a54034a00140240380 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 33674348 1250 33673098 33673117
    0x8070210020903030306041a130e01050a14040b0a0e0703060e070602030702011b020303091507060e1b010804021f02030d060b04050109030b0612010c0203040303110a0209010605070c0317 82
    0x1030200c51800c86002442a60842040500154210358415050200820741d0f446583c010100e101c00c00c941907611050034160102400502041003d0524511401d44801501112100c2e040080100c0818020030310340790710507000840e003030268440310071806c0141541c050303001c420b026091002c0184542c582010580c80108002c036a40d5603501c042c100c0c5c41c0d001d05900240051032103410305039903d20300400c4e1a40c441c0024103807803411042000042118901c0b465043c2c001e84003007010000e0042b18032641d0740a003443c1000e481c0180e4400d249020b8801d61008640c10b01c900840400c0c00c0d5110005400c8002c0314842d20364024a5050002a6032600110600355101c0d081c2400440c1e0b4104860696040f03c0040e103461055504540d10320074a500c0007000e42d0340050302c104d11f00380d0442090241d5003a5842c0c030380145075900d0844c14020502c10304004e02507240c1e88410803680c0162100380c1464110f07103140c601070352500c40c00e240c01140420349501c0541004158030a681c4210340c103500a260811 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 33675598 1250 33674348 33674353
    0x51303081b06100f050d03090909060e1b060f0d0902330903060703021c14011805060913080d0f06050f01020a1212020405040f090311060c030a1d0d080702 68
    0x25a00d2070b60140703000303081c004c0d10b0b14032003202420000780c20000d40c1c108050340f003810400501c03a20360901c2400c58241590584000380ca440c0926103108003400700f4110030000d4044000e00301045008107009204042e51007141540000302c4000606c1c41c1c1c1d00244100d90b0041451340600f00c1b800540089482d036034601d0300e40d03020706201915490740090898403080750150240829940d6418203030025000300800405450324002c4aa5103a0380512900401c0207000310440c981c0d50400310004e0440b102c840030784140c54078040602c0700c15501c400c58954044074902c10000340298074030740350340725000e02d00426540c641032085800c074084068000c40141c074000c5e54202003220590004a80d41d40040c0d0000d043c502440040f034035600d1090f20b80807141c0b10041030240c500341e614008101180c808680c1802041e075140407a4040580c00440c805111622000810071818020100000ba101c050401c003107081d680c1800001004c1c0c111034480c000d54603103003914010104a000500b681008840b880010f0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 33676848 1250 33675598 33675601
    0x6070b06090903161b080f0d02010b010306080703080c070e010801050a0506010309020609010e030c0607050c0405010b0a02030a18090c020a05100c1d040207060e0f010b040204050f01051303081b06 86
    0x20b900010a8400001040c4210403264103aa142c030854074200e118600c01c411040361000c2031107041000b4400301854500c0c0142004689060000e00312001d407505681054103010341044400400076458043d00d400c900115581d070310040c03015290a14a074070481600e00010000102e9402c194410b80c410820304400f4010b65403240011404c503050100020350260090004c185594030820751608044400350440c1c065400400016056400c0620701315165844810a03d15a04207801464010001c44645a08000344018060f480f4001c1c1c0741c2e01c104004440c42c0200c0300c625121800c0004245050080110b00c040441c02525000200010765452251868006417407100c0d104200741010a907468588850b002041d00c00c0706c907100841d00e5030058003480b5401c00305406115181d110041140101051100918402d080d03a4031407243c9885503105000c2042191070f01034401401210034a0882d6688641e807141d110b00003803941000d0200e40c004508680103995442502452110040c211140e6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 33678098 1250 33676848 33676861
    0x41b02070626070e0405090f1b03030a08100306090f0201180806070c1b080109020108090616030518010507030c090503070803040519080a030e0901060f0e130b06070b0609 75
    0x1240a05070b282448245104080b4001c281d0000c0c2a044120ba15014881c404030000180039500d056840311141c0d04007040c9810842810001401da000786030307010807412020400026140d0240175231038414003280c84000b41003040032114010295900040400c102c1c0410308102c46000c1000c0340481c00b240c8120410401d10b84004000401ca0f1005401041203954222088510304e4055508030350480052064480c0c9580c40d07000d58018015050000402e201540001010407501814040c100e8000d9014018502c01000c0c8441d41c0201600b03000c40d550b161000c1c0e0b8003241c41d0740a0102c0306d80d440e140c1480f0085074190800b034149500b0760340381514940c54200b05030311004140300e02c1d881c1c0e5100700420006400c000b0743e104013103001c40807180500c42d51158054201a500b4004800103059000504a10b15044048a01500141c5041c1d0020001000c0180161103042c0c245446000e8a0310343da40d2159140c2c001c100075260141c0113a441ea050307803401004502055411500c505250f0001072403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 33679348 1250 33678098 33678107
    0x1109060307030602090409061a04140c030103020118080a110102010b0301020f030a050718091e0504021c050708031b0708060609070c05070509040b070314060604180b041b020706 78
    0x14100240030781001861907491030029401011a03076001a2105010004900e152103440e5150000c00262416800c040d01000b0484000c58114040c081c0250300380a5000682010f9030305480c0c0c28200558400c150104075009010241c0c803541040c4114811002000360300e41c50300490b280207030001d01c00d0803c02400c1500741d0284107240b003c6084d00f07000258041090b40c0101d83c000e0003a0500c0303403261100019003490407800307400c000031071903c400d244003030982095002190344642c00f03c10002410309900140800d60f100d503400c01c1829000001805110341030060000070803203202220358840344d440b801c03403007040621440032490180b000d001584200209100303120303030030040c0405401da40d585415a07000d0a840401d40b480d2040700340202e469200d84482a01443c01500402c02500e0b01200c02000c0d01c1f00a846051000000c005000f501d031142410f442c06e84d940c030207651214084011401005100501041d03a04c01d09101c445058510303c01000d10070340408d6400da0b07805a0300e031203003680e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 33680598 1250 33679348 33679351
    0x51e01030c0813061a03070f0f05090f04080702150a020c0306010e010602060f040c030611030f0603070f090b03031201030308012402100e0a0506012d03050a02100c0506131109 77
    0x343c8030600070702900d001400350381c410610040903100710403a0381303a10790210346040341079082075892011000041c800c60680000c0d00c401031000306c404000610b01218407050320072029100400f14000030074007100b1580c8950060305903642c1c01880b2511907812040082d074628082032082e00a0080d440085080320662003c80d0503500a600109040c2d02c802041d011940c038000c10950302285403c0d400b10014210740118081001414207981d200c0c00c0c50900c40c20000301c00340881c1d210b58400c0404004407040001054111159a031002540b440c002003c00d08500c181c04900018600c2c00001004068000a140d416120310412200350480d101d8880f6260785000f006042c0036a1000c2c0c1344250440c0780b03411411140e8410425140d502b00d55554051403c00c0a0f00001458030f511500305501188070741c2d000d80e48030b075040d01a813030103407640d11610f0316804440030180c0100985c901c0b2501040c0200103024007140c0c404110303800b900d041045210040e0011100f03d80054803a140b0054524200c0c8486 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 33681848 1250 33680598 33680611
    0x70306090902030a02011b0c0b0a0e0103151e12050f0d020601030c052103030a06031103121c020403050d0e030706030e060a0504050c04090f020f060a05070605090304051e01030c08 79
    0x208160041500191582203040c107000c4540c030011f2420900242c00031843c40000c200c04400c50381c40b000c640703101070600611000b903241014900740300d001d54032400c03071100c0045580600b5120b02c0c604200e03589c0320080c28a60800f005c10f15034940c0c0c14040100000b03d0403036015400c021340d06406030282080785c61744821b00c0b003e080001c40843c140a14070707140580c100d968031000e11001400c0e40782c0f5052410358004540301107003156036910810038010161540078104500300d0140c01c0745060014111654040d10200c00000e6440503641001001c080c3d0484001d150000111350415134000401054200f44600d4680203000c0c0090000d2a00d020f030040406060b5000302030071459442c02c1150000f440300070400e0703c051042d0356000300c4a490341d00c180108540110040d04021a0754014050110f0840410b01d0041d42c04001032240c5550080a991020b0392140380441d260721034940c198a14021034001c1c65100004001d41d008580c24036128003d110002c1e2001d03c81e100c90b0300c0007920440002c5408 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 33683098 1250 33681848 33681853
    0xf05160b0a05090102010207060501061106181b04020403020604080d09080109020a06050306240909010e0105062b02040605030a0f05010b0f070314031e0a0207031b020d0609080307030609090203 85
    0x810000c5000b080500f90320750b0188001403d084c21030f00ca540075a0f100fa41302e0404290002d400540e40c82080c00401e40c802d1141566242800c04502c40c203940b0b00c10030114240b10310b01d40143c80c4841e91250102c0d001581c00130320054859844101c81c540710902051042e021503410180010100010f000d078402041d0001c2c0210400d601c0c001080e1060b91008103440d92007014001c01c82020b104003d49140700780b01680806031035001c0d02d004d0114028040c2c0291504010700d80040040f0f039201310484a4640d403070420303491440340c9880310b1102c1034500d900585025002290104003980e1060203144502000390303043c032608410580c90002ca5030280550806a031080103070044500860005000e9144689003150f8a40c00d44008a003c81c2c00603512501d85000d4032700d244a0281540c103100c1e0300b1a100c8141107240030303038a13500a410401c040080c00a0b41641c4000074066550710141030704401e402c6074003800050210f180c243c2e5690300032a500c5010901e440d8012036661003911406d0401035003c0d00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 33684348 1250 33683098 33683107
    0x204050124020706051e130305060106020c0d050607051c050903090f060702012a0206160b070f020705010f09050d0f03020613020901090902030705060a0804051c120f11070f05160b 79
    0x80192650404914281540b0f00c10000305840b9401d007c031200045000340050100780d4103010b002070401481c1d46089110f001c1345100500030901c080741c5c15800c00034505042c0d40e5180464114074500c9221511b005c07a46150800300800002d0200c02081c0e00b84045810450440b00300c0208070550107200b001900081494502c110000400b12140003105c4d0101005182041907034002540c690010034a200b03c00400340d5107100b0400395407ca1904840d8a0802c0805a440000c00a59880142c810a41006160400d0441d0103009040140c068080500216000042c60400c41c103521000842140148100310020742240140000300455540c02055809940d11700520320000e00081842170381c0c14021a40000f0310b594809000701200c1856403691202884c1604100f418019013117500508645070b039008110382075100621901c0717251231890000f1341c0d0441540110040085081300c458001c0005140c60a20503400c40503240184108221009403904041c1c4038890103141c4165550b4100900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 33685598 1250 33684348 33684367
    0x30b1308090d050c030106080307110402070b07050f1201060809060a1e09020f03031b010f06180e0a021002011a030f070303080c09130504030e01020a02030d030902010c020405012402070605 83
    0x1185082e0480c0034504603202442d0600009007140d03003661000c4007940c0001031400070010f1440c26140d085030111011800c103038040e2150070320850010400b42c00c11400040c1e003200071440c2800e40d110a807258085078025070712514007812119003660300a20502c900000a50500c003103000d1002403806012219029560062904019211940f8103c1e40080100050581d071b0301c080028103d59102d801184030f002044015680c07c50382c011158141c40ca0810a003408201044544444e401c806148001418620040c035a428951750440007507000c0300040000280707640c150400051103034403400701010f9084070005c0607030303800303440c10011450f07001031800f000841d028401a590119030106568903007018400000c1c0c6c00b0001118040610340d880f024041415031040e54080b000c44280000c246902c16500020b0b0f460481411202c10180c4400d040f0003107921805105402c941c4c042d009004958480f000803c42c00514042c1030314004040c8090100e451000450320700b00c4895071174036480c000800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 33686848 1250 33685598 33685609
    0x109051003060314011e0905060402060d020d110d0b0d1a040309090905010f0608010207020901050f01020c0301020309010c1116030b070516030305010503120c0c04020309010b0306010f030b130809 86
    0x5800030003419038490b070020204100e0a0300c0041c1502103c000102c101c42c50550b4a8000e041400240c481d6180c1030150b0002200014101d40260b01161516141c4000201c0d89004e40b043c0a00f0040c030604003944210300c030070050080d04801120001c1030101051030024481c810103542e001800010a409101004113000191b50350020302a01e00310b081c47ea282c0c580101070b983d10180848490b9502c5036042000032142c031583d030141040400a51510351b641d00099001070307040c010305209215004c000c0280780e000704040745510002400a54580c83c00012641c0200002070780000411610140005105000b01c0d01800f101095800c4021503030030350701c0c0d000d114403000342210280003007045458100201440001c015501c60303540400ca03581020185410640500071185607500280400150341c40c010410fa00d40d004150740040c1c40703583d807440c240e000d401000c0f541c5406000d18000403680501e42043c1006032402507103011400e864007032045150145000014180490900824a00e407410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 33688098 1250 33686848 33686869
    0xc06150105040806250306080c040c02100c0c110901030b07050706090804080105040311030f04090b0406031b060f05031e10030203060a0b190308070b0a0204030803040803070e030c010905 82
    0x1072510034107140e281d442040c0740c00c01c143c80c0c81c5640007420000561014180c40502d014031590715081c064a480c00d1201030381c580302d4003451845262240954040903100308070000e07417444200818409070001c014090304030306442d038060380c07150302401d8451864102211241d04885d40250100e1040c1c2c0c07205001c54850300229003c8448640328039024001c6075850300503201070441c0800010705030034503190140c8142d80c999a05082c03a0802e01c0301100c001c8407401518201c03a02480702185890310b00d00090020030740d98000800807054052400442040c00c2c0404042c4c48150700c5032080c408403a40d0035035190008840c60307a1460041c0b00b031050000e100742d159035007003205a10b006040c5603c0b580021f041207021600701050075a503182441d0b0703e103800207440002c4031901200c0d01c6681c0c01c41c1c131a5000c6215100028000340b00394000314803800800e40c100d40003590401d08217501c9080c0340ca00700704154001d64442002170000d030040e84003840c0200300c0d41031801c1c050311020b2000f0700d410144034001b1030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 33689348 1250 33688098 33688141
    0x4050607050a082703010b010806040e10150e0f01051c0201050d050a15050a050d12050705030705030901030b01050c21090301020d0c02211206040b0616020103060504020c06 76
    0x1401c1c40041c00161070310b0161505507011501000040008212a0000d280b6100c130b05110303a0400007000d4150b6004000d89421500544001c0390307a480300c84d01c0f00e01e082104c40caa510342520309018007200400c010190f000b590340c41440d607401030f00e83d038003d2030041c0b50a0041a40c4a0010366080d90301c8213000585801d010300c10304015003441c10154281c8110340003182c030b00004648507140707050151140c800081c09401c007200d642c0540d500f0000402c0940120b444010302840608a092160a0007841580c81c11139004040380d540719842d261203034681c0c00218441e40440d0070104645110341c01790060340e1b40400060010151009680e101d06c0c00302c4125a02c2003c0024100b04607102903c00703000401050400c5800032071540304256000b0b20741401401c6407801c2000081080f00000c45080840302c1c0003045250b403e41546400d00068002c01071060390aa002ca40017499034505544800c2c400c1c01c40d0b000762000c0004580c2e42040c071042c0e100b2200300b8106604130304002045001e044044280c03c4c0d6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 33690598 1250 33689348 33689353
    0x80601030218090a0b03060604140c090a030f050304030318030203030d0c031e060f0605070b010e04020a0b040e0603060109020c03070b100305070e161d060a170c09030f120405060705 80
    0x20710190103e03261000036551080d1568a51010208600b002c0051071b81000040d902040004144164070010082c041d14140031000c0014a040f00e40e503940fa03004005e1b42d003041d05602410214030317202d42d1340d0b440740c130080b4003180300b41c642600c1c2079080c0040a81200c0d00a0302031454024644280001040000408400d0503070f140c07800c0682021240540b48800001716002035154207000801218044030f03442101008001c00116002400000000b41150b003450303454034850f11548009007012070766030003c102c141c0780800c0c0051442c1040340b680d401601c090f001e0380e1140e600c8030580c48c2a0f02c500420015650300c20841c0c0c03000500550745040c0c0c4119000b0110641075101e5403001d00b451541c0e13005035000c5806c01c06003c41e501c481c203246171002025050155041d0414001103c0d40c05501d203c0ba1f10400740070500070b590038081c003120103208620141180551418550f036501907042081502d0003481036104900c18a040015004040788940d000c1c641032610b444100003441d44410022034950 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 33691848 1250 33690598 33690637
    0xc090b04090b0913081902030904110403120207030c06051305040c02010b19050d020603060d050109060c090b040315090309030602210a1406060a02070302030f06060111030301060806010302 83
    0x210200103000680300c22000442c5181c00a0104036091102400c54001d10043c80000b000050f691130840340010403010640c0040901340e1410703400d41c01401c0403030350000d04098a445144042000910540b0321a0407800f204031a03420b03080f692203a160200801031080c5080c24071540340650058894413000c40685008941c91b980400d00740c0f050800a0000340c1c1d1105001707101031408c0c64501c45c010040054444071240350000007032780302d43c030b0504c0030340201c1000010411a84444a85402d5540c100000340106041441e0000090004544902c00604003240110345c07490744204503000c07280c01507240d6820b00315440f83e800041140e0701d000c4042c0030f01d002d00000000d0090002c0d01d01c507a4a130207800030512407070021248044008007020303083d0b444c040e200c48034680c43c560007982021341074804076180c06003e1401d074603080180c2c0010790700d8030030740c0c9420900c14000540d940c8992405e130380303451620280c2580240d40c0d000a01036040031030044070004482d94443e078041c00c0054070990654051 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 33693098 1250 33691848 33691859
    0x150304030c110a05150c0d021b0904030e0402070b0105120a05030d0510050a08100606050403020904030c03032003090d0905030a150f050f04110312120a09060c020a05010b0405010b07060c09 83
    0x6180c401d010705e416804542150001800d0091003504101c50002d044158845044050111090318007607114040820104042c503100d101820b00d21903000d8411940c1e941507050015a1200900c29144100d28280841080160205101c140325510500031400e00300c0030403248025141c000c0201c8266030301003100240d00e40e26500904c000f016800064600c0155424004c000c5e41d045800000600000700020070042e11100c0381c1070340c040d4151070f1880316906c1e00e00d4101e000d06010540c058084203030000c40440c0d000b10f0780055004145640845d540c10300315490076282d52804e4441e40743c0c0746c0c0020380c50b00003180102640c107405201240001807800240c4251030205e03102a25111030817480c80c42003100300145c0c00301044020070101c000745440101d4102c4002c05110304000b4002c81c400e00008079080f44e41035001026921b0b40040c09101c540c0c0e403900029a1071801c03d906a035651700300001b003815404e0030704c20b6030306880c07448041d1485c0400c04c0e1941c83c00350011540075401c0000d0110300160 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 33694348 1250 33693098 33693109
    0x405150403080103060b091003080c100c121a03151801021803061003120c0501020c03030906190902060406030203150406080c10020312060111150c0306150304030c110a05 75
    0x20640c03280d15468110350460400317004480621802038010400d080c14000e1018034046038804a0f5030100c1c107a0398440c1e0450782c80c0d0a0042c203c41c0204010300702031180502540003081400c1005120000b00300d0f10f5001340014000d180c41c0512550150800d2403183c420802000345981c2c4904030140d03a81c505001c4080203422a48441881c0c2c903000c0b00d0407100325440c0360500c207181c1c0202051038010301203811604c0d2001b0501c0707a59060307070510040323181a00170841c0a4040da44c4200300300c420b50b626480d0402c0101d888000071603400e020801000300100040c1000c0c07081800d543e0700038050318203041c1000d4040d0000c0d070000c1c04a140c20701c00c1d086101440e944078010240075043d1503010300a40d500000078050406401e01c1e0f46000d540041c051a20700c41c1c04001007590022091030301e042d20203518a45c01f070070521280d00384402c030f002c964204010300e1040700042d0301441054412040d1046100d05100b9140415500180007501c820302c5040813800314640c4038000d0100402c1d1142c0165144000b50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 33695598 1250 33694348 33694351
    0x6030507091802040e07020606091815180106081b06090d21021207030c0b0402010302120c04031a070e0d05012904060e0f010b0c070f03030c05010e030f12040515 71
    0x2420b64000074180001c100203c8090f405c40068002003465051000010310000001812000d855084001d100d00c2c0142c104401c606030000200a180380341800304c61043e510090301e2612446600305900090040d40021310b0018011080c0ca031210391500b4142008083d600c207003540396101c100e5070040d1011032180c81d10759070f44126005402d504000000800703814903032882c02401d241c0c4402c0c80a000800e03040424440d0481c1e119681c0340b8207030f0311840160001d00540312000840c208250800c412440481d00904c151b0b0b005540006000c8041d034408041c4401c200c0da0080044d04595080145003080204c030135034648920f00203e40140241550003100869403200e0700210510500c00030385080c107100c0d1002404203000c0c6100c0f1450031414804230082d042c0700b803107441680095400c40d03a40c401e0028201400d51140002c4c02540d4a00300180452007040c41507400b54600802c40700c5540000080307840c4010900025400c05483c00941d40d15443c0040082c1d44030b0180d11000d044031040c1c6001c59 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 33696848 1250 33695598 33695639
    0xa0201090c050603091f0e03120403090b041a0a03060e0c070204060806010803030712020706140103060c0314130201030905120309060907140907030b09090d030f02090a0603050709 79
    0x40e80a00c942803008290036039600c40c50052500300140822804c010400360200314410000d60003400143c160300700100310a0281c010705020100d5890510782854030650300170f0340242e0b6045122500c07424580c401340300344d124031441802c42c0282d0160100103d0050712094a040c1000585c49507920540d02c14480116100c50048400041d07250441c9010300c01d0a010307051210040c000f5605140c02c8a540703110160a18050000f1090020303030001c465011503507000d078040030601c94804e0381c07100c165080c402070204844e140d04242582c10b40c01d110707100d641c044002001c5805000d46a03641c001d102c1c00d007a010161304140d05d98000e00041a010406041c8160b0360329140c41c1d5901c5c01c0000103044c140050408135164011103020000031054442c103480f1098126001d180c191142038060703004140c41990160408518130401c4041007000c900c0d00901840c640301402405c020400e858102c0c810180c4d201e030721000074013042c03048510942c44594009181c2c106516a50f407a030078039035407001d20b08160 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 33698098 1250 33696848 33696851
    0x90301090b01090c0c151d010c08160c020d170d0e0708070b040b030a0b060d050703050411040c0504230303040305010608070504020a12050405070513020c0d0903030801061b0204020a0201 82
    0x40041d0358413403182800f003488515000c1c81c000c0d1140d681100702c41e035010136820b56a4407040c9a250368001c0d02100300310030f001c80000700074100c0d90800c0600001412100b800c81010035100103140b035401201181e036016401030001152016a6841c00320648034803045112401043c4100344840c00306114424080c0b03c5840100000ca20b0b1030300841c0f500c00aa00400456070041c0410440c0c885441e00340c0b9042842e101011641c03594640c08142d80b405004c070000140c50524040c420015019486680101e010300a04140b528400c401e110540d103040550720001441044100213030340c03d201091201c4044000c8280880d040040001e10315002034006440e981d42d24034003001000410009200101400c0d2815030401e0303d410707009012083d20036250b130041d9442d00001420880c0501004025000007482d140c000c0720401c003068000d40215021101600c2902d070000b0385140100700d200c08032076040e03071506026803c0403000c5498611020700c1e018120740d440519801a81c490000d4a0400d045500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 33699348 1250 33698098 33698101
    0x30a050703050d02120d0509011b030c1211040b03090106030f0b0703050108060c030c0703180914010b0403050a0f05010b220516020d1d09010b03040209010b03060105031506090301090b 81
    0x141181007851120f2020155403050000300901c10156040c0c1d8038083c2d032004006801c1ea19008054013400c0010100303501c06600381c8400000c1d94055100340e0054200d036403420340010954801c6030854004c0381c4a0000d030036091008001041d80400110380c03040030302c000828460781e6641c40064603040420111003003500c500401c0185545803047c6401484008018401030501d08480381d103c0c880034040160a10f4000788a1090600590048035494090002e060748290703540c80440c010011103910300d0310008500c000181000442054070140c0e81c0000141007492000c0c2d40342c40c195051080d048481d9500c03070315204866900c6002102e040000000f2000454940707087c240300700c1b11300900c02024044c050804c4e013180b60703001460403c90583da040a95015440601403090a02c4800d48035502c01e682c00000702e62503030f1a20103140071703520030f031f6045c03400e030762241400110382c04210f0713049000506c1480000c0e07005a00d030380c00844241c80a0400e40c5400c0c4007201007801d681c0e01c00001e81c0e40000180 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 33700598 1250 33699348 33699353
    0x703030509060709050a0605031f06050c0c0405040519020a030f05010c03060e0f011502010b0603010f050306060a0b090910050315010312020a0201020604080d06081606020601050a03050c0405090309030a050703 92
    0xc40b07990300c10440d291501d1068202000a12200801e024010422038040005841040c0c3d40811101d25050031a8440c4099559600105190f02459192081b0700641c0d55202080c01c0c079000c2c0a000e036500070060107034004001c1c2c1c1c0c410044ca43c21b0b403c0c0d9003c02c1c141c0c030000105914480b01010f5030b000700000705040104400103000c1d031b5984ea00400b0795000c01d508000c180d400390045581501d940d02c00340e901445d1004401c90150118444e00d90344010000000144100964200400c4900c25400e4175010741d19201005500e15030b92085809118081100c0042d80c40c000391020741c4a800c0039008a5015100e0340401d10341184100100200c0c0802c500500a011341e0034120740035250f6500c0204602c81c010f0f40000e48481c00a0700c01041080c0115140135000d10542204020300282c108480d04440c2020720112000414490080075011303101c00400c803070401305d040b07609403078000c001456070078951010b002c0240002007204200380004c1c0007035180c0d80d4017440003c088500030001040340da400c50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 33701848 1250 33700598 33700603
    0x1030209010b07030516030909060b07020a0605121305030d0903110c040218040218090f011a0405060418060f090204050a08061e0403170a02031609030201120908040b0703030509 78
    0x41c0c20070110102c05208450000768408125940280d0304240c91922140300d19040d03036140c000d0b410a603029810000d010542c0404a005440b15034000c5880d286555070b03680301924a8880e6815203408400d0b0fa000141c040b111156811201328410000c4034609640341146204842c521482140051011803004400207800c0019418140341101e0451411203c00030340690340124421040c02550007190020001c0c1d040c0042d03090804018000750f12034500450441000103003400790078421842c1c08908956124242c041d941500d03400b8210501d000d003012155404c0d0b446402039481c415469040104c0c00700c80003036031b1900400c18800e02503112805c1c50204030249141ba0043c0c607891380084204000005007040b8480e81b412145030000e11501e5508003110030280039440241d0b250904002c0c001c8032010707507004621420070400b001e41c0b0a9001e000c2101c03a00c0705031201030f001418994842c4c080d01445d03848000c10612070380e01a89065907070f6000c3c01d041d4120080940210380d40b00108000010117 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 33703098 1250 33701848 33701851
    0x312080a140106050306010e0406080d0503100909050a06020304051c1101060506160b07090b160209010b0c070911270301050606030c1603170a090c05010c0506011a07080c01020301030209 82
    0x5814041e409981003510040190000914584c10014000341e5400d00b6112030380042c0c05411a1020384417078200701440039145030300a440c1040b446000c035100181d2800988111052594418081c100b50102d640300c0c400a0740010300203035000d0103103002d512a40100c1d20801e01803500725486001602c984c1580311800c5a165510443c010b0000304459014010880021711001e948129904c10315140c42204554020840c0c100d540f502c900026107415452003c0c3d104015144201c03800f01042e80c81c6ea480394258003901c00650740c603502002080c040c40380281c004815440ac26600e460414140d28404080110540705415030296250010010307420280240c0d940703e4810340e545d52540c00d180c0240b1416220750204100441c0e080712000f401c0500c614080e003400341d4240f2140440c0d080ca00451130040101c1042224034403a4043c3c001100d50182c94000da546400c50040c003150387c40c1650782c007620041a41c843c00c18070b80c01c1042c40c00180754031000c0e0040303007a050001a240d604520522849540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 33704348 1250 33703098 33703121
    0x1706040c060f050d090606030803010f0f170a0b04050f031204060506010806060409020a050906040314100506361602061b03040206090a0503010e010f0f0509070303180312080a 77
    0x2d400d5280e11030b56070014103c5401c04100e240006400e00a0705200c0020080c5410040140200000006074075002180c00ca00341c82c51048400340481d600d0b0342d20002d003104448001c807a0b82010080501082c5802d070f40c3e40d8041d004030f080e2a000c010030200d003400c40e44203941e861128902602440207101051140950001d0282081c90542c1010310001c3e08a018611a036060140c000402c3c4d20500d105c2c00580d000e240bc090300007a00c442e103a2804008111505030070703da551140701c3c0c02c51691426409058010a0098007600759036651203030800c2c00c98665035214891074560210201c10550260030300d48600744901b89444155074000340203080c4030003d0102c0d04070f040810000c40d60000f0b40022a50850b82c111061691480001e001c200412800e90010b40d05529080c1036000d140300641010381c407451201800c02081404a14a100705c0307100b138580c198654050102480001c0c00341c0805104807074450f041080040d503d565511440808125100000f14048248803400520b802800403a00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 33705598 1250 33704348 33704357
    0x513050f0705090f0c0d09030f17010608011401020106080a0f02120601030314180a080c1003090c03061119020109020a080114070302160f0602180d0812040201091706040c06 76
    0xd14120000f034040c2000f030110b0009100d80d602107000c80102e80100d90204040d14024000700c010303420041d02e203840c12100000401d500c1407545010b228042c4680b41030340d041c1d468011069092100da135109401080160381550751310000450007031020404051800e02c6031034003080e0104240705100607c10076812400e25540440d0043c80020381011070a034040942112241e21900004080a103030004000d0740c941200c903056002c00d00403000f1a009446040650b20f1340085050311404804540c1d20030400740c25801c1401045c40024000d0b00805508031007030100505001007400342d03035a022061501030000d40e5544c500f900450428121040050001100030004074403606401080d20304010000d000305503001442da440e00d0020000c44540d0f075040a03030b03505040501e1801c400294007002c1d2a00c3c03203c84403e060500352a2284001c0c2d4610381c0038088508054101e1844d0b040c41c00044d00403418003d8661001ca202650403401100c0da821540081c40d031403c0500b0940c40081003600300c1c1c4200b1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 33706848 1250 33705598 33705613
    0xb1317030a050d0209150a030c030e070303090e130803100e0705090603151c03020c040501080106080a030f090506120420010c080d0608010615090e01031109060f040513050f 76
    0x26074001080d1581000340c403c0150350303041c0c83c000044820341e00c069242d81c286008540b0034449540f41d44000007041e42031710108010504071944c103031b555806120060029038454014002481142ca9841c2c02240c445801031180840340d0ba403c070325030404c5038440380403000c5ca031080100c01d61a5542d01d07003003035607814401c3c83c005040c404501d0600c0014101c03440c1c076001c0c41d05003080781c4494600042000074003410b00341d07400f290301d002515208080385c03842c8580e003060008a0b0741039043c071804044440300070013404031030201c0e034043d50601e04680b032200070b00075051000039103520346400400a604001011407040d01d86442c043c214041d040c002006030581c3c0300301c1052070344d070402d08100c02c1b02c0d000000151a80c1c140c090002c00740080360000340c0a542400300004005101c442180c55061a036143e200c00d103502da13a40040345050134400513003400000e1102c0400c904091480d96007241d00600713102c071074403180404502a12030070380d5503512800700c0d695030714140720051010450014000700509000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 33708098 1250 33706848 33706867
    0x6090605070b06210109061b020d1103070204140105090f06150c0109060c0807020f030309070e060d05070e011a04081e0a050105090706080a05091002090105040b131703 74
    0x40d8090300100405412048001c0354580d607030515054000c01440d6404880945103034121806091040e0040b16080d003042090b042d190b0500c03810500c0100e003503008111464815108550b141c001e0100c40b155404100841d44c0540c90390f000d400135541c110ac0d026202d42d4508000e00c41c80c00c0c0f005159680101c079040074044541c2e66041420218100d1004040d203551b280e03210103006056041c8020001454000d61600e46504101d280d4810a82b5400f03503180495100701c1c0d81d40b030384012114020680c1029805000c900e01038030080d600306001a002e6145036480e6902c441c13070218540c02281e1114072040042141c450301034502c2201c081d411241d2820b151034102c84d03555401d06690382808075958110f460464a000700024002960040001d0049003841c41140d41c40f8000e5000b58400104900001910307204607024290007101f0341c0c8020502c040707200540c00b0003508252101c0741000707010000000c21046541c00f60400042181e44c40c410140351140c1ea15860002200110440e0030070303c82c907101c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 33709348 1250 33708098 33708107
    0x403090e071403090304050d050d080c030405060103030c080702040c09050307090207020616060b0d060c030b01050a1e02160801020d0c0c0b07030509120309010209090a06050f150f070302030a020601060906 90
    0x94115102c0c040c0c0e00e03038596031042804c60080342c1005800c480b40c04144810302c500058030900c14456925074901c5e40e20303003803005030703180c802200c01030000d6105000403c0020301c41d001205540380903030368080c00d200b140e5002a0545440a48050005078003013410321892800b40b00400003482440030441c5424102d5000c60742900036072400002c010030421707544060201a0300b10a030240c0005003408010b982c80d1420760001c008104d43c800029207080c4940100d540a4002c03517180285940798843c0045407030786030b440c00400302000507046005111f00c00b54811030802044010706010b500158446040503420002c480d02080303000d00300700c20000e0050104100d0840c0d13070b0304980c6034600419103036645450f5a01d4203004044c09120194000100b20540d04190b02500c41084c00326840501515107404a5003075458a0007450f5100b00d0150050b15a4a0540c0e1480242516055020b08125200c0b0541d181500000010f80c0942c000107021700c1a0740c1d0604c5058007412407420304510042c2443c00060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 33710598 1250 33709348 33709367
    0x3010b01050418150306020708040614040b04090207050a0206030123040207120c0302070b030a0b0108090c06030c091c050d090906080709020c03090d060b03010b010c02100c02190e0403090e07 84
    0x190543e69130a40b05001c442d0140480003564000f03a0a542e21360861030b10742000d81c017605ca0140002c41d5002120030603140001100d040703e40d0030704c040c3d08007030801e0303403040007540120002c0fa01440b40010302c200580354000610300811144c0d496081e9801d81800300702140b800701d14254402c03441040f07a000012260541c22210040610300042135903c14a404e034584101c5400524002c0c1c0040100000711407103030018850400c0a85e01d002542d11186ca00580e541c000c0303044698054407c0c4001010510400c014141101004200203544540c0260f444d108028091007901c1540282100301111600000b0300d60007000b1002041020030304d081c203800d803610f802d4010500c1d00380c0c001a0f0001c82150400540f1001340000b001e40000c00c1080c40c0c440024002115454007030750810804002543c000c0300031750350943d000780169102e11110402100c50b0408104103e80c007441071100200e0b01c446514400b40139003c101d40050041c02c050a01415107001d941c09407542103606010030405561021000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 33711848 1250 33710598 33710639
    0x2190b06011701090506100c050c0103020a031419110c0703030807030905010c02010c0f030c0503010e0a1103130203060a0605010c020d08041205070f0e040803010e0403021903020c03010b010504 85
    0x6026100c1400494a40c1500c009000307516403400008160045240d11041c0607030011a4150842d45c90301c00d0568031041a00b10180481c0c2068040861950280c2c0051001810607d000101c0c007110031009540c0c50410b50303924070303003007041c080c0c61901080304e10800090400448900d428202e030002d209070b0f1a845408002c040100c0b1750017007407045010b0b411031044954000002d12071140f010704001d000b00500c501b070030001100750039105003640c040d200780402211187c3ea6140b0710b0303003454084690501c0141103828056654020301c1d14440d0b42030042d6000b440403d00001104149004152400c01c0c094981c400c05842c00400300000d80c0c04c203602e03010140e070543e0744005080203410044020300881e80411503101031009100100440401c1da4401c1d21803040e0140710341c13a02c1d030300b2030b20809104a900401c9220204010302901410f060b0559200d8031900c103c0e1000c042d0301c03000110218000d042200580e11103181a09207150031b000da928401c4003032034441d040c1072410900c418400c0e000c0705071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 33713098 1250 33711848 33711863
    0xc08040303050c030702130b0109050103050129121906080309011b051c020f010509120f280e0301050603011a040b01090509090a05060a05090706080a09020a030c0f060219 75
    0x1c80c3c0d0300c070109009445010b50010808851112001c020700b002e071007541e14060004507070b040301050070f600900c0341d241a02c84248015514813118003800724074000c001205000c0c014140081d104d151035680d0344901ca40c01400862001002d080d81d500e040c0e60460700010081d0700180000741099038010703030900c2c400e8901c1940c00166044da061041c1807456010701040c3c5402d00321080070300309800044080380d0b041c00f0802042595184d0541ca40c440c24803d01030040407104100074240004890b003d0480071030b8010035001c2941044004030880e4000d2011000482c0d151813050f0070070714003803007115485101500240400b240d0060005441000e21044500c01d968030701c0c1d42e0005920030b40086020301006400c011041c1410482182c1e245691801100d0034420f15000415003802801114041c81c2c6160041c5003450403c481510a0b0744010005e0203542ea076400c1100c0540d5900380c50500640c01850340700d0301c55082850094480e6882d40140c419075020350b00d81d10b10b42c0380c602c0c41c1e40d04c5075070018003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 33714348 1250 33713098 33713107
    0x30504050a0b0c0d050a0c0b07110c04061a09031609050103030f030c0903170403050102040e040605071107030f1401150303030b0102030f030c07020a03050d030e012d05060604080d020105090d0c0804030305 90
    0x1407e44e420442d600c0058203118007982013092060b081020409013044a808442060007000100002d035881401540700c004120848405401488000b40c00e40502c01425034284401ca18480b44100505500400c2d0080e21f5030010014940c2041114540645a00e000d206000d41200050170450441c4401002329555041049440c0000b40075100034690160095590702d55131302d1300729040c0a00703030b4081c2c1e882c62414000c6000a80140c1c81c0c1e25207000c044029100c0c07549503403250f13450280d2850040d140701c0d440c4554042151800c0c440d080313840d019036200a155a0860500804850a032a9581d043d50310030000780303442c086030300c0c1600d40c0200c080800542d620100c0c400b060441c50036030f1000f040c0d807180700103000d501703600b681160055a89071002082001014811110b60300740c8050b480c140701c400d0020385e654146094222940c04000a000c50385401c0e5515041031905235801640801030f5524014400842404d01c0b5500b0350001a15201091100030788840e00140701d0341c400142032280004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 33715598 1250 33714348 33714367
    0x71a0309031e13080304030b0c0c0a0803091009030f0225050607050c030105040c180b0f01030e0109080307021509010e070506160206040b030a0b01030e07230409030504050a0b0c0d05 80
    0x446034020310243e0001c4442e41d440302201d82d650040d003c203da404a40310001404211400d082d609a070440d00c004186440c03050300d50f9601684003815160b403034001c7d549103000d0741d00c80c0d001c1e4005880c42030351428543c0310444030080c2000d000349420001c400001c45000c020032080603000c0c0a82e4401c40341550b5881031031a10720701e03000840c0742e1140c16508140c200700900a222518404584086111b0f0751003412102c0071108942812011542c800300104040c1c0480d4465440160340442560002801c441d5035101c50300a90401c131440c50050340310030146c0400146444a2075000040c3d10000d004131034644803019110625405118003880010a260222803c0c004c280c00c0e19580190216a0740c61711420612155031040b20040c441608099100886500c0307071148012414601c0003904049080c0b404424621100c0e000442d0124020000404c02e0340d19072085074042882500c4a95545103401c007809841c401d80d0b80100d01343c00007440400c07011040428072803000040d5103400c9076520b1820 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 33716848 1250 33715598 33715657
    0xe06070507060c03090b071502160215030603070f080312041704080307020418030804020f0301230106090509010f060e01050c031606060f1409090a02030a05071a030903 74
    0x98028080d403107407120016480350407a4100c1c500c0f500a56440d98903513290100c00c00c03980315011008085c6000081388074074060703003503010306010320720a442d20780b02400c10b03000600300c0c0014000700c0100300000070600c43d880c078081006100500007285001417041c034144000da22405454100c0e003034850450b00050804c0704590703440307224400c009034103903c4a40310540103a494020300c41c120302403482d003076100d814010903c800c60281e992607070b41c0700300d203658507030074047c02800c540c204d41e41564a40c0c1e060f204204140301d80803003005550010551079858554002d0280e18268070450090b10160014003003c0201c05641e01950082e06052101c1105440102c42600c90307098802d01078003020944c508200403040b607902300346000b4001404a9a1035a44821a524091145c100210314204c040300260030f100301901e9114000c3d0301078540302e5030b8035004039003440082c003c11550ba80100c2001d003c12000208100b104041003040c450562600300c201079035074800c551080341c0c90782c10701c0c0e8003520b99002c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 33718098 1250 33716848 33716857
    0x30f02040c0e0a06052706031b090a1206060b030105030d0c02012105040b0a06050f0f030a0b01080a031106070503070305130203010f020c120f07020613080307030903020102010b0a05030d0e06 84
    0x5072100110550381d14009060740c10405140104403131b200c48031003d00719a410b42610404000340403c0c61521072441c1c844444201c4035031582900824000203500740c0c2c1e00b81c0d07210f000b0f1040c13007020000f200e410300d48082120a560000b00c400d10050005000a4800041c003200740c2da114108010070700700d98001601c1001041c10783e044145022130003030140c4200c07500140e0040740f28808040325500d0b41889034050325594040c2940244016140310b000d0b160615540003c90405400d5800c000700e10303140c50413401d9098000d844d05a00c075076100030405a003c3c040150414256014050034204280000e00380c0c40302500600805484401243d92186020b05240b19240d00030001c020307600e040c8141c2c10181d0404c6d400721125014602100c06120007000441e550301c424901c00740d1812400d9400c1001c60740202d0049181c203000b104000c21040c03010401400054001d85078521018070b984002400d41c0d00982c0d4241c00351150640801c0180c8002402050380c031b13543d01b043c1750b9540c0701502141083c00f4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 33719348 1250 33718098 33718127
    0x51303021005091e10260403020a0b07090e0a0b0303121816050a090c09080706031401060309050619020d060e06010207060c050607081e040b06040510030f02040c 71
    0x80040c60001a03a0070100404450205541d400b800e5a292000013030240000302d106900014041c08404d07000b0310800341d207441c500000c1c03d1010248224400c0340711250085900f05d0150348545104000d0000100c2d041d98040a1480c2c610881410162900003600e4003a01a0307690684801c00070780c03180c0d03052003525041c1c0f000c100c441707419180c1900d90041c10700701d10511082134081c030341000a00d4a1518003030b605542c4054a6080111b00c1d14610714001c0012903103850030030983c0e1201044c40c00052114000800440d07030003150703c6810a00d00006100107901060a0619040301e8100003407002c13424541c080107102019031950b200400c044068480c0d80c48810145180c40d0b0085400c0c18503010303c0e801f500007a801c035030722541c694034195844680d0441c05003503540807400042c100ca1060001079482940c6d408410f00614460503c0709029609907000c642c0748000b02c003080001c0c1401d101303140e8020b120300318040c60ba91a44d21b030031241240002c0c02074085d5071260120201c480c05480911210503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 33720598 1250 33719348 33719359
    0xb0406180803030a0f050a060b190c0506010608040303051636240c03052b02041d0907061d1503071205090304150f090906121109040302070605130302 66
    0xe0216004030040c941c010a00038107610b1b10001c41c2101445224400030790b00f400b02c000c0d1401804180c41c2e43d011a000a20320100406076040c00c0001744140100e038000c0c045c5480d02ca149040501c0d000d400d03241c00911020601306042408001ca1340d01c8408852010310a10020035840710340440e107503d503000c180b004d81e01c2e101007403c00110035401c0c540021010041d00320344040c2d84c5041d242200c09810410001d00016802d01c002d040d41d00c0e10b0312100c00c4038a50714041c00c120140c0070411000b41d0300280e020304089e1010601c2035804001c070689056015544102508915080880280117607800034070040d12140e80444264158030f0303402441e41641c0c2e0b003403402c075164030700541d004180c2c04540403044c1e0340c541000d02151001d0800402e840c00d69640042041c14401c5c00e00c01101d90480100c01c0c2d000b081074801001030fa80d2000d01c51400600342490181c07124213030b141448455494900c07881070141815408100210b64040b801900390742c094542681d41d0b403040a52004810215000a075024 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 33721848 1250 33720598 33720601
    0x109020603192714120702090703090605040c0302240a03020a090306090b061302030606070305070206070f1119030503180303040b03010609060909180b0702010f090503030f09070b040618080303 85
    0xf88a1180000c2101e120351621510a01031980b41d5884060a55031013082d0340d01401440700501d000700c2501e034402d415150000d00c024082e21004281d400955045d50030300c60300502841981088030840701d08581003a03080720400c031000724511040c402c0140103000c242e40030840d2500144140b1020008682120040c00382d400705040002202c10700f6182980700ea00803503004c40e41841507000780c9128040050103d03091401c147c6044e01c2ca40d104c1c0404a0384003c081040d2000905e0140f2103107002c50090b0001c000c0c1031041c10034006450501341720a01489081007040002900000803a8805100b40680000a032051f0020a00d140150b8210400b0001d0102c00862196401000030084800302d41d16101c94590b01c00c8448115140c1d00c0994084184a0320044042081c1250b40c0f038012000e840000741d83e1400e072040108441011101315500c1c0c0002080c4056024144010798001e071800d405070a049140a81c00c01c600d103e0f03441194103009071103201c0ca5405040e00ca08800a101c6030302a240c0d40d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 33723098 1250 33721848 33721901
    0xc19050706020601050d050a02010507020a120b090606010201020c030304020409110d0b061e0310050606040b071a0601030501080d0c08040f060309050709020903070b09040e070303020d020f010902060319 89
    0x280d4015004003001842680c1c0001224600011140b11040e0000c01621040105400446240d0322819090340c00c00880c020000300150740510610319180141d100b2810b0b401d108103920709240d40544041c0c1103a006210b08016201e020003120b0f009541214009006c1405140c442d224403810742c100ca0b40141e1025090050221440c00c2c944600c0c02228450307003010700703101c01401140c3c2c1c40e2002901030344114154400c2503880c0d4052900507034010401424182c0d2908041d81c158001e640850706000a03445003011940c06602940d00302c0e2003400d06008640c1000756460b610340b1300381c0e81101044245030350081406205022100a881e485501d0100e20ba10303040090f0282680d108100c0702d074480d0080c0002c03180064426140c200000801400140d8a0b108510b901904640d414540c0070f6036800095458002c10050070000394441c2e000380118405c1c1c008003a00701038000500b1010350f41400103010040e0b590308220b03984044c406020701c2100b24a080d80100408100d210303288a940c801811030070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 33724348 1250 33723098 33723103
    0x18020d0506061c09060905060c0403030f09030807081303081605060a05011d18030a080103150515011413090605180105060706050702100c02030c0f0304050d11030f0105010b070c0b03060d06020c1905 87
    0x1642c2c0a07440780104009901d504135549004fd2001400c074005c01d001c0880004c4280000b01403c0b004881c5030341c8025140c2d1200d24203540b01e8080011b00c40c1c0c10860740380400c1011321000b64040ea40e40300030031403580342541e003210381e10703030303459044460990400092540c102c46040f0140c010300d001c04580d110018148060514202808143c5e0240c5201c04120720094107800b425120b480d4a0a643c010012820300544142c80300c00c4034420800020300410307000d081c0c403030342c0d4000405070124007256003442c4c5402e103d0784401106d09801100c0d1920014805500d07100c086450031944500c000a0543d00c402049040c04000003d5003040c0c0c0c2000003150020382e000024081d843d0207141a01c40c440314100785165684140e1103825000b401c0c40c91084c01003a410b210034100002e000d001c2d01d04000d911281242160001d810900840070040b80944c01d00240090b032001a10203c013940345142040c500046210700903180003024185c00007410464004244098100021440318400700000c00340350054 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 33725598 1250 33724348 33724357
    0x1009030f060f0e0f0c010e0d020d05030a0305010501020a20040902030607020604140a0b0621030a0504060306050f180603011e0f05070807050d0c0918020d0506061c09060905060c 78
    0x290041c2c100780300c00a40300320128241056100040051840c00076817001590703087c1c2d98038011640648002100000350726056825800c0d00d2103500130756070721103c01a002d0120385041c0c0049045600c558158030000c1c0e030202c1c9a092031b40500c00e202d640001c491000a002d8206008020741501510b014400e034a46c0005555000714031a400303015001d06182041540d444c1080c2c005800100d0840201d105030408d9807910000081e09184209040c1031042c1040c5140d1059600c03000041c0001010800c7c16410b10440c005018122441c401c0348000300d0024041c5e80c3c5200c95070f04410b00810103e90165001d42c0441d00f4001103c902591180744001030741c3c0106503d42d0a01d01090421000600f050700c1f0b840c0c8a8420311070f139100d032070400c3c0343b0001e04401808103100600c2803142c260000700320400b8111001c011401032034400769440d51081310040030740d0030241000380104010300c1100001802554000030b18011040c0000c3e900c2214102180030301600840a442805005c080c0f1240402040060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 33726848 1250 33725598 33725621
    0x210c030503071a060d0602031b0a021e0102070308010b090d0c0605090f0607050601030f1104050f0117010e0c12190809031903020606060a0c0c0b1306030203151009030f06 75
    0x18905207510110750b07000f210081300da0960042d059001000004e00c00d50103141c0041c4a90302c1c0c1c403136a0021044032850350348038011450245e030112420400c212160081003e08460001c025800c155540c0da000d41620818002c1e0008020301081e01822382e2103203030710454041e070401001c00d0425607900f009132140d40a801403238040c400302c0e0b4000547d4101a011034501c56441301c02001075a103140c940c421207841506084038415181702c4004501d03aa680a01d6001d0359100d021031131154907040b401e032250316915118102c664100510481c5c0e4440214404035038000c144c542540c1c40c101001d84a040014442074841e10301180da00c02c6080c8010b034000340c0800201902160f2145104004030002c1110040c40180142d12a100060300e506104001c1c1c100b02c030450a040c0340da084255601403d10300c1c1c82d04940a00800482c0306a00c044540c26180001d19990030118a181003041021103520340c07501030305004040d002030b07100b076036445030068130000c541210f0584c0d0214020301e4084040c1000701101d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 33728098 1250 33726848 33726863
    0x6110c0106050a0b07020d030c06090b0f06010815010807050d0501080c01170108060406090804260705010e01020307020d081207030603030212030105011205060109080d09030606060c0c210c03050307 87
    0x300e02c900b441111a81542e182c04103141c102030303669080100000e50f0b4881142080410b44900c0000746080c091241290b12441c0e80100c680362260040006000040030b5604100c580c2e01440007030140702c288408009000e1900f540940c0d18640280c2d00fa2043d61640c9041e03d04e06000011200c4010444d05440f64091742c0350dc102c101510780800581c0828013500b005500800d01280c00241680c0c42076036818859500702c1e00f010b80e03500d510b04100d076200c2c00e21003407032046d454075240350b8800788100400b90609003003800000c0b14482c0000d5032401002d4000740181c0e190004030b000e0002a9050b54500750090100f0326151030071517801030240150788822000741c460721108400580031130341036038143c2d00c041e55100540f084551004001e080041c2c45a41805114103000c60200800d01160701e41c0d8503035449040341c0c1352862610f0005c0b0b403410f60110040100d10f50002001848440845c030882e01c0e2100340645005070408080f1040f81c2812004200e40c0c04407400104104021000d0400e681c001d80c403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 33729348 1250 33728098 33728111
    0x15090616080c1305060a03020a08100b0702010507020307080d050a11010501060e0f12010f09020a1211120f0303040b0a0c02011b11120301260a08030703090201020a06110c01 76
    0x111514140d14004048003151a401c00189103000c84000342c016003180c1040b011500303a0b5000400e215500480262001907000100c064059401007a000e41001110103142e040c00d01d442d454081c80d0141007002070402c000050a0000e640d41000654003608601c0151614596154400780c25544414a407002180c4049459554180180715607070486001d030302d61105407041d010030000869100c003440ba5022010898201c8030700e00910902d450031402003000190f54002d401000a1420203a0001a07005000016800020741e8141c00440c1000103590348d030404091540031509044480c020b800303152101004000074041c2c203013605401a14400d100700002c8040403012801da882c0e1042400701e840410040b044110f1083d480560030440c04006d50318001017084c0d80042c5507000b80d0000d044840c01060300c410502c412150800100340c010b0042258181c0c40d07440411a000080c40c2d0410306950720007200959009003e00d004940c2d0041c4100402580c1486105090b0016800382d183d03580f07041c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 33730598 1250 33729348 33729361
    0x150503010e01030f02060c0106060801050f04050103020d0b090a0f0506070318050606060c0c030a12030506060307171b030405070801051602060a1104170106050f011d010806030f150906 81
    0x48a05071580400010315580c03c54986064003900d9100c200d030086030070401046812400c0c07065001400d160b03620082c255160104020070340e030404070b00c188034510340001000103a48041e0202c0107654007007a405125505e0005c2103041004801000c1d2091441000300c0080007408130300c06201c2d03055602c04100d042002c40900041204a03c4018910380c48203011810a01d800c0d4007800b000c0701d41d4011500b00b40c4034035000c2800c010034020b045560380c4030101c0506200750940980d42c0c0c040ba050359080d00710324005500405040204e040d100e48980c0c00f0b000b0a80e80c82c0c0e402050b50004010200440ea2418249010303685c5100764440c7c02529440c00000c1060031080d81c0030038500d000c45600402d569114031000d40003c04041120602040d03040200042c500480080c02140400e0304000141c072514200c00d10244441c50700849040108082e1a500300742022810403694680070310305450b032a9070380790200780b501410129200687c4500032100e903d1007003480500f8812100c00042d06d10548030300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 33731848 1250 33730598 33730607
    0x1020c0a08121501020c130b0414010306050c0906041a070807080c0d11030f090a03050610090b0109060516050106030206270d0209070f020304091401090c0e03120a12020d020415 78
    0x3928102d0060f0031891a4040f28035000031f0f0318250400ca00d4000034100c21100016044808141c0d0050880d420000108184a503d120b450761265030074540506c0d00004c140012140d00c1103003c0c0810f181000309240c081d000401d01610690765201052075613400050520800c190006110251184900000c291b1294481c00b000e0940d41081002507040ca00034071400002900007a18941c0c100c2800d003800400f081741005851b0085080c24800c9020f00d08103640d10040e1000004c9803810311000b848104081d503800411214900d41215a02c03020751541c2c948903024041507400a0350240000c2950401c424000905403804129404010840080380307050214886400401941c40440b40700014030f0316014101c40c0c4500031851060f01d00e8131b41c4954410040380c80d10000200324650241c01405040b15510850b02d80103a142040241108000c0000395501c1460f1004000c004001c6070310150075014020758402190000c4080d519408040201402900144100343c40300e205002c240c80c0041c0075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 33733098 1250 33731848 33731881
    0x412020a12050702040b0a030f12110c0904030e0d03030f0e0c0904080c0a050604050a031b020a15030605060d0f15030b070c08070b042001050c0303060906010201020c0a0812 76
    0x4a540d1440e02000c80320142c51580045034144d802079120340f0720b14250b41d5140404006140701c3c1c840da502801d004c0c148401c0c414030b041c10a10900c100005007050803000041d00c075440d000308540102c006d0b500c41c42d003221000c081340c0358a5004480028043c04050305a000158444250041040445907000b00e080d41c03038611035051600041c079640418007041ca400018810b00c043c6000b201c86074400b59440070710b0417408841c04e075042e4000e14001001c041d40300d044403a100c0150701c01664040c9040d00028002c40c994414003089105c0c2c1c43c0b5428846010380c000400a090003820683ca60a01201000141031050700d185406454882400e108500b100c4d510001e87c1c2d0480001070456807400c000744c03820f401943c020348000000b489a08002428030740b134548694414445000903d101a00c0501a01d000402c114103021051107c4880c00400000b41e0358030540c225050105c075140e0b040103034028460406085407501800c00000280182600100210050811741041c2c5540b414140c1604009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 33734348 1250 33733098 33733103
    0x11190b09010b0a03174602060703090219030b0907080109080d0f0b0402042c1e061305010f0602060703020703120203040c090507200106030b06010807091d0412020a 72
    0x491020a1005c942655140c4080301e82264409151a00c1d61207605c0d074003400c10003034038060300d000208540710000c8a4000201034041e1a0f9810014030141d9002e921244000d02100030183e98411000c299070b00d842210700c04070b00361741240d90901d460781441500c1700c0341142ca012040c4660b0ba800503038101c0502c20405041d41003540182840104400c03040031744106809403d1050300c0385c0c12400195610320040005003210500c443d00e121484007650111046460710f004841c0b90002041490702c0340b02d1041c01000c90b02904082181e031200002003401007418001015180b603c000030410075040001034003034603155000c4440c0f40d034420008500364811904000c2c0003401100b02103a0500d00c94000c0d5030020301c0303030f4141d8403c1074441066100f141c004941c10300005001d440c82c01c405540745c0c451580042288402400001d055032500ca040c2c4501504481c1000140c2c0c0004103070521403500c0c0c0029040124040141c9003212814060700b50043d201620002d1078004546501c5000050070103146a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 33735598 1250 33734348 33734359
    0x11106071e0e0a0f030303051303090b070602040b030705040816050604140d02120106060306050909060402011b0804060905010e0102030c2503050f060a0e03070b01031211190b09010b 80
    0x1c0c46112880180c0e421024910705115078140e541078207a50703551401c40945008681d0081a500d94103000b02580c50252810130f1070001c0714070420100f94030012041c10b440050500641c3c4800a01e002c0e8000e00c11030f07002c1c00795503201100f884800c81d403040080c01214074110841d5100c4004619808540c00c0612406600c03038001c0104000c220607503148100b031000d00400c40e01c2d500900d500441c43c0c0d0800d003d1089440d9544100c1400000d070180710700d101401c401e03503900040e0720745020031642e0350802401c040d060200c3c44081c50041000a800b500f9815401400340c2d0b140d60342ca02010300b06070154005c15011468244092185505c0082031b20f005540c4c4000801c00d1007071f480f02c05a002d50f100d44186603c615401070220209008004194074240844010700180c074094629000302c81500c04c040351550401c012a9001c10507480c035050640e60400d080041c03000120206541c82c0f036200d02d10803000e02820301101c0e070b013135900031000461600400d1892040d80d00c8050310390032500710109156019 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 33736848 1250 33735598 33735617
    0x90405010617041e080a0216210b0c04030c081006061b0303090c050402040602100513030203070b0604060302100507110103021e03060a0306020c060a0b030303060a061d040e0a0201110607 82
    0xa07803a02072010141050f62480360750003405445d046071550003400c000c809640032032a10729801403602402c100070606a003100c0800380440160007008440910f02500c250030180101d500560418119401580e00c154014070b0341d40d40304452522035500c0c6600c001c0b082d28213140010b40e54040c15205908500304d00c0405018001a07805070001c0c01d100106882d03482e004100400d081c1c48600c010710241c841070f0001c0c919000c1e803402e2401610f50061142c2440c810101d60701e40020b40000543c2c14a0307601c540c240d0184d9a9480108004001607400a5440010b0700c2c0c011034419008001015050300880400480b05180d400540c01ea1060410110b509142250300f071040e200620051604500300419030b0311034660340d4031103405070f801020214000c0e030000c0d028000fa2211521a02550840540146043d450b02034002108444944110302c14006442d08001e54480403003003401c403001c001002007010450050300d4540d14a03040c1c00481c0807841c64104000501d0001450520901d207680e205000f8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 33738098 1250 33736848 33736853
    0x8040302060a0210020d06050306090313060f1110020a03140103050705010e0102010f0203090c03101401090f0209180a0605030303160507050a0c060e011d090a11040b030c09040501061704 82
    0x11984200b05880441c0550100004500058002012040083c84020410074104400c06003040b0014020b100da544c07003080752041c15030780030302007078121010350410b4019414086810744803070348000c2143d010f90003414010041014994060048400ba90360108031039503800031503001c40c2000780009042688071039400c0243d980b1622030f03000c2621041c0300100b8080c00c1408100166003095400d00815004106034040c42c0c1405c00082c00000c8401106001c2e07600400c0e07014121000600807407220903103440329030002a10f1030b012580944405066a07900d108c502c5040207406e04152112901e8608009001615290010541e405680d040b280c0c2d5642000c820820344859004480443da140103c0d42d012010402c030741c281f88000c010b503445030403000d88203100040090500118880750458901000e114644985801d650700c01d0307401c84005030081404110480c28060b551010800c007000004200308006210042c103201c5400b0746040c003491340c80f05e500f541d0031010340091015070324409002402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 33739348 1250 33738098 33738109
    0x18030e0613030209152704020913080304060c030506010c081606140c03160306030519081c1a0a0305060a05040f02150a020601060206160305090705030303010303110c040908040302 79
    0x942069070800d0005150380c0b5408078030010300841714152a100160001c808905000c1c4026000d03501c00002c4900c00403800d6180d600c8a44040c001074000c4a41f000012800855050343c071b1951604040d10b240c07a49454a4410060542d0b40840e4000a040502065095001e00c00d1003500b9940311140c9405c028025200281e00c105141d82640c0407078842c0030b00c80c03031b540394001c1841c001d1261140c042d075a1f2410f4070184000e90b0140c0348410070145014410130215401086c802044643d500c000202c2061a081c0064075000c0c410a20383c032001e0040240c003481c641036002c6582d00c04105880d4440b1480c0714100208034000c1e1002070581e0b08840d0000c1c0000c501640160341c003034032411001c0180c01c16070300450172a2120003c4900c010000040001200390100501ca00410440c4001d0016141c000039041c1407101c0d001496092546810114003551402d00c041300c0900030140841c1c0d140e682d60300f0001d1105480c0003504015000da0600a0101d00701402046011504044894681481c660030300c0b5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 33740598 1250 33739348 33739357
    0x602030406030f02071208011505040b09210f01090302070906060512100e070503011e14060d021605060f0a110a110c031b13020304050c0402070201110d0207030618030e06 75
    0x900f0b0700d0307013040900c0004a082c41c01c07402c0b0554540c2c8034089503041102070403024071a44103840912130180b004100b02d04160048030b01800c0152010508007854803098148075200e118840c41902940100c885c0f0725805600039100d1500a030300f01c90086555200503c21100103020f0580025010403000300b001002c1101507400651b00051458116640c24451400c00402e81e04200000c8000004010038003c14842c01c0b0b19031824802c00c40003e05c1c00b0729030072802000249081c003504010400e0003100c00694140c904020074000102102241481c1c01e903100e240442d99001c449581c9000f0a805089a1045059503107001c9061407504210190585030040d454200d056075108440c0c1c01011903c0510410100c3d0b5060046000c00f100810200800003a0001e1403040780c07441030042101180c0002081c10303a916094030016500c540c5400101d6140201c90b21490040c427950010400d40c550000b00207013100e004400800c14800c0c0c02242c0d54440c500c0032005000a500e141035400c0502e8070030001d1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 33741848 1250 33740598 33740621
    0x1b09230c0c0f0706080703020a08010612110f030603010c0c050c010509041b030b0a06020a0b0103060e0f030403030c020a05090408030a0509010e0d02010905010e03070b152d19060203040603 83
    0x19410040e01d214101d103021003929102d10640c0101e002000305582091240e508482c081c2405d508024003e400201009014840d038410440b600e0508e0342081416808841340b030480300440d03550381119a5034400c1c5030b4400d449050180d0b182c060542007085c03295280940080c0e002c0040c100340c000f0200111156000a41010782c0305960f00c43e5001c2380c09858030f038804030851584001c13a6884000381003210300450b0b80d00040641d000f028401e000141e82c02503e50550750310440002d200c8a8201140e840c01007500c0307a011541c4400103010092580204a16000703078401c030340303d01920b40ca443c14806549020f40700106000ca01303101107200300840303402140e4040004c2c0d0000500d14103c500861801001a00d400b0150350340c7c0030b0202c1030007400c0c0203185115440e83c000790310f030442d55034820745c0c940c3c001006414600c28108802c4415136861070b0540d40c0e580c955401c0d409506240c100d01d80150841c640c014070400d40d507060902e0341102d1b414000215101070b0041c42c01c0a240001c150060700c000c0824 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 33743098 1250 33741848 33741871
    0x303030a0c1403040302011a0108070906030f060e071205090a0f0609050a02191d0702060c1b0102030a0222062012030702032a030a050d181b0923 64
    0x40402c6848440c00f95200318000d078001b140201c10301c00a1030407a9100700e411030421644d42c0400c05040d40000c081400c030303601454001604e40e03004a1100040000ba00000507010034141071014407a445201c002c000241c1180070070030b40e00c4249001da030b944420b10006045540c0403081502040060b0b0083d10828000c1c419600950155400141c1e2254418619001c0e0340d0010428000243c140364410345520f00841644a00c0c141204040e568000080003081011400225400a0038100c4000c107403103000ca000031754990500c0d55915000e50408202c6a08078400c5410701c0010241900c0b4800c11100e80340c61300300c0d5680900c03010000d10001903035589203034440d001d05442030803900401903104820702d6020703546581c240161901c14014041840c0e401d80c1e40a907070415000804000c403107141102e41440e558540404d8503800181100c103140c0c0390401c0040c0d0458080c000301c02950300d401007503880c0081c011a210411101210604009168000000d0b044510100c10107002150031001c1c183c0e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 33744348 1250 33743098 33743117
    0xa0c050907050c0d050a0f0207050306041b0306020408010c1e0c0b0603010e03030c0702180702070b030709050303160204050a0606050403020402030c0705060a060f06090602030a08150a06020f07050402090303030a0c 94
    0x1142c92400d082c0c01580c0d000220001210382243c0d41c00070007e40c00e00040d10142010a203844000b0342c1d00c4602800141070100c1c6ea41c5056040400343c0c448034011944000c0541d00c5680d900011802054519020400302d030308840050710100c04920303070344000318094503540e0302a1005c1d1110201008018032494140d03603200c0250750310280c200040e500c1503180e039500c1c0c0c0d030380c545030f106210301400342007610f0415004040c00c2c405140d80204901050b80c42c55041d40c0d40382d07964440708072a0001990f01054241c0000242d100141e00d03011000e0802600944003480355490b00800101151680d105400c001503013800284010708d4240c000b1500058040200c604240071504ca840c2008800c3d0344400c5242d40c0e400c4200503500412003144014140c90410324145032070104080d44a201c0c4007100300402c060301000518071110488007078203020010703107400c8003540c48500195465240c2e5210404c01c0c0f182c1103000a07189003d008075103000c00094099411a160f003074010014050750100c44060051400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 33745598 1250 33744348 33744367
    0xd08040c05031f1505060a0311040e01030b04050105010e070c030509031212150a05060d050a1506110c030307020a120302010209150d0b03011a1005040503070303080105030d020a0c05090705 83
    0x1e000143c401501900324281d84080c40b08044444030f0808889000c10180e040220742ea03424141c0700544a942004104402c0c086204c084c40d00c2190020044124140700204c1805450450580724134801c10003000b0a0340c9512202c00c100008864400000f0382d402d0b20f4800180c8030340040c1c4010000274085a0112a1f1040b00001c5c0760048408154a02c55140802009035034100155184400070741d841c984a504290102d0010f202c3e1800551299803524041086182554403044101900070050b40d030068a508000b40b030340312555442c6034544900004074540c0d240c007100302c03080aa401041c2030401440c011000c0f400050300802501595421b01928050b42c440071100c00c00b070620501042d60728151904220100c50f00f0710b4042c1e01903854010b0040000c04211041c1d220490100e500410001062108865030322880c1c01c0709406000e00e0320000308158001524605a5104070203903441e1000002c000c9948041d0030b040600300b0004c802d010080b03820034008180c0c0010440c41c0c02480d0020311b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 33746848 1250 33745598 33745603
    0xf04110d03030e06090c0307060906050405040b060715020c070e0108070e040302030f031003061407080c1b01150501080105060a02060c13090c090305060a0b0607120509090f06031501080d08040c0503 87
    0x80318014403a03042002041d510f0b00d020302012028102782d0410044550031310000501d03a000b580079440c002d60b668180c002140d52090241c031122039020900205641440a00c170020350071491101505102d16130700858403c4800c180380341038078030000044c02c00c0d900d800e8403817442c40c002802c19010345c0020080d0709181482d03000154070036550f42c050090f5013031562400700b08517008a00312908004e20b81060244090380300340d685800c109490700007601c6241824064903000008410206650f01e0012459100c051070514081107400c01d03200e40200e80e03620b50501800d48900d0b0074010068000c030740041c0f00342c4241800380800b40a09201050419240e040881c1111341c60003d41000c1051041c003001009010020301c2d43c024003c2c0e17018480940350f04040f81507801101001090031054042c000050b5100344155070481c04010420085402c00c089e45140404003614494041d024814042003040400d05d0b078203040380e180000810f0b4009004c036045500c3c403405042216003501d0810005141e0340d04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 33748098 1250 33746848 33746851
    0xb060604030c03030206060907050a02030712020309040603060e06060f1810051c140115050906040f05040c0e010806040b04060504020112021c0f0b090105010807030b100e03060f04110d03030e06 85
    0xb85c1c0080441c4e0610b0410404d441c0001081441001400c200002002d036002c819100007a038440300003200044500801e80c150b004602c0c2081d0003618140c800014481c1c241c00000058040000342c070702c551244414170920303810034426a0b030001000e4200714010540c4134603081d400300f011102d4412040d211000580055542030078841400c04080088041c400c901c0c021000101404000700403a0401d640114a80c2c0b51912640e031192034081d000500c6911550011a01461221010040e901d0246000d48450320a800b4900d4144884800030485ca100001d10383e001c2c5070011600d404903035955a84d5005040014022810040007401c10050902c042c0060201c8640403440041000092000d8000b01ca41c079403128800d05041c44020300740c9898590046054030420310f40800182e0ba15107050700545140c01265401c19180c0c00369200041d131000c0401a0807a04400b500c656444504803182c1b020300694002c0c24011181006510b5443d01e14405100c151086c02d0120300700e50142c0095003000700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 33749348 1250 33748098 33748103
    0xc061c0209031b0102010515150703030b040203010609030b0703020901080a021b0f0c042711120307030906030506060903100507110a0f03020c011805060d090204020d0b04150e040b060604030c03 85
    0x6403403040c3c1c0301e0b0344c0c0a0191030341c480400000b01001d000c1841c009015494900300c49401e00341c000440c5000d040c030a8100b0a01d50001034800e540d6541c5d1400c0081c000000f5100644180a81001007802e4074400d000301d4071500390503543c006050f114161180003d41c819101a2010204117501044640b8144002502804407001034035001c8620030900003034502c042404c105c01d03014012980321403a21441c0c2c000c810b0350410201d001c400c6082001c50300c15494214144098400031409000301030b880111b11050710106d40d03017032041c0e0319040c003400100d014003c003240e0b0580202002d449480d0150b808940c1c002d0080c500341006601103080117060a280301400c1c2c450a80414001080c9601080076004078042841c00c645402010b00d85c5480040c1e00e401106e20655000564090040e550f8000108139900144110740e46e0b01c1d042004401003020310300c12801039080c400d0452a240089040b2000c644045030001c4e840d07583e0307030b071141900f50b00202183c4e8403550034070000c80803030008500c280181d031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 33750598 1250 33749348 33749383
    0x20a060b010e031b030106080102091c020109031a040c090504260409020403050102090a0b090907030e030f0a0e040c111b040f06030503030718030f02010507020406030b0907170c061c020903 83
    0x3100103041c5821340d010358008d03180e5030380100040b1001d52140c04000601c0340500141144160040c801200c2c0c40702303a070340003074003186412104190a8a10201c0b031802140708074800f0305910307600e040200590b4000c44d005040070b1109500c2c0a01c54181c100b620240036811500507107026220318440c4121303046500140d54581d4081104501420b016040101034009500c4190404500c1c40028020000090103201016210139050049050810070b8811500c0300c02d4945880d0440803100410101307401d14054880c6007000c2c0080036030f81c0103915a164800c1188007034a00d840720855018510417903190f080e1f4105594600014030000103105800c09540310784003a40d0340781840d0500400340d0024001c1c8010980303603030301c1c100000740d00c0b01c0c11070313100a50a090294944e40700e80000b50041c50307550300c090a80d030001c03400c001c1403c4012074805c064907040f0444151006a41c1180ca9a400101027007a401080400c4030b00c010411294500701d0710008108054038140418011a003400082e040d00c0b00c440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 33751848 1250 33750598 33750643
    0xf0a0e0f0730080d060801090303091e050d0e0607020a03050d0807090b03180a020d0c080d0302040b09040e0703050a0c030b061807050c0f01060b030402030706050a020a060b010e03 79
    0x142c4000d000d00ca05040082040a0200801d11035054140307001c1d10052120400040b40004102d41341c000320300500544000b0405a059030401401501d50803070100c41c084102070079071b21850b20003100c8049103034000c4018241640702e10000e07a819100e48a401364812070601c1350000580e80c81148601451041c00600300d0445841381c0a0081400a0900010f2041e40e05041c06070440c0d000c1902e510090350b2403519803201c0803400303141c1442c03003205000c0d4008402c984a14144081400003400301e48016013101c09241a454003101240954043c03191400b40c1000071300c000d45001e4001040c500c581c0401c0d150043d640f42d58051078444103440c102d64503c40c545082090010780380400303500030001d0f180481c1458510b1008480c0c5040113003600e06002e00030480c45906481000010441c01904008200c80ca44603038136041503400c2210100e110303205102010030403610450940d20341c6202c580007400c0c0381103596901c001600c2c2c00742a6038100038a81c814115079503802c2105280084038440b208060 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 33753098 1250 33751848 33751859
    0x9031509030807020a03170c120a1a3c12010b040609020405060d0c140c070509070201091a1306050c09030705030106051302030a060b03010b0a170106080f0a0e0f07 72
    0xc000c8024462419904143e8411780400d403c840c11011034605241d00320141d40d1440026103080c000c41d0421401000008100915544190f20203424081c11306504119011700760304021f40e82c002c0400d5800e2000c10721a506c0f40100404d0414081c601001154244091314100071030700ca55001d005045407a0345925843c82c103818180716450190007090401d500d4a81011b01080a0344208010584480c0c0da444110b882d251080704070003050310748010040d9460400c813a401e41c2d603200902840e8860008003000c60f0309a030051003080030351b0380c0c400814248481400c0541c00c00300030040240c41243c51040798000041d5071403003494420400000313015150f0642d032040c50b01e040b04581145000360714121f4140710300e5507480b81140740d0709655180503a5030b90340e10194102500c0c9035840111704480100c00840c0007007688000e0041c0d49815600e0740c070804030a01301240844028814600480c1c50200030400c100c0000c241c5d580e000002c01c0700410168207101f082458404244080d0328036410008042c0007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 33754348 1250 33753098 33753107
    0x20301090c14090c0307050a02161413090b0402010c060e06010306050f1608010b09010507050105010b030417030106091211090903030610030605060a1110090b06090105030a0b0403030209010903150903 88
    0x10b1415a0540e450780350044003000c25100c050021024008049510321a152003000125000e1604801030f00d03c0030707910150704801010140015101e140306000070020601c243c403407000341e2a08813101041584894005449540c0807040a940b0315071200c503a1a0368076400c1000e84c2c001c600c190000512480d0480f080c15120310080c1c14020a800041c14101a0651007210141502c2480001c1030359810887e0060380e0138800d0f034500500c4e6508085c0002404400780300910301c02c50141034000307241040348141491610090240b00b0208840040c1031190b0102404c0c8a5070079440755040f103408040c803d0004901740c10448407610180d000008004040c2443d0b01d488003040b00da03007014003800b130402001404a005000c10030b070401c01d0b000404514030b801000020a00800740108121000250810390721030356007194402d001b40240c500014260400180c0181c41c19004021030f038a580b1581c0e1f00328044d501401345907040201500e4040081800322940300d207540c20341280054034041c41e107006007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 33755598 1250 33754348 33754379
    0x3030e030a05060105010305130b1603050105150a0e0a050d0605010303030e010212040807020120070302041b080402150f0a050c0601050f01020304030b0c042402071e0302120a020301090c 82
    0x5000ea00180c040c00006400010080d040d01c20900740807803d075032008048407820161160142c850550481400b440c442d2144404ea0208502d560501040c1e0300c403024880c407510030b203541542c08002040750640c414454120b80d0304c541401024041100c0c1c4e9040001c01c5501d0b812015900b040d928001001016018800c1d48031011400d0700035801e0500c10711306100c25100c010310240105200190a1085a00c1221034422041450028004460703981e41482c0c2d9a03001400b040b40603528020314803603080054078545011540d20759401500ea940c40c0e082c800c029403020711036419101c00f0302040c13000000c880098101e00240e541c403161941a44400ca41c54408107030700050003044142507180603641c0c00710445090303030741001da6070301e00d80c50307100e68040e02c0d21a07640035003052410442c40b04d19021003520103119000442d401c0390f80087c1c1f510080c08109411007591945c50a80940400060501048a103041350102094508405a0390007003420745982d040c00711076601603404280305240c1c0045882c3c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 33756848 1250 33755598 33755627
    0x60b090405061903030c02040207060e16050303071e03020703080307050d05010504050906040b070203120106050712020106060206070e0409020a0f0302030f060702030702120115060306141e04020a020312040c0303 93
    0x10703015040d900f030510203404014000a4208480041900199222901292281c542c03140007000b0602400d5000d5890704500130004500e001034040002e0180b40020545d04103e40000e901001120b000b803020214602e0150218154000c400d030000110384035001444c03050b00c40e5125a42e40c0c146a4010608980050f080380d4800c03403070a014400c40b8200081d099901a512000300380440e10342e680241e29500911000500e600708000011400c035510501a1100611031440d84050424081041e402d9a40c41d0051400590050000410b8944030b000c0c500d82600000e4000030b00214180c0200700614402e80000840e00c0c9900c2040045090800110b5400002c00014220030b0600030f000a44038450f03100d01031311820110382418001402980312140c1c6401510103001d0251755148041c0141c002441100d10321070310280c45d4a618109210030414080c00080c410005241010800c0f000b5002059407004512040c0400c541c040010b89a01380228000c0301d2682200d4510724000f842802c164400d03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 33758098 1250 33756848 33756859
    0x305041809080426010218100e090f060103060b030903031b030f04020d060f0f09050d020706020705060f09090106021006090b1f0219030c0b10082509060b09040506 72
    0x502000c184031500f07680030364500a00c00d2414101c111800254038086007041c0d0384a510000b0003003c0300c0310f81c0207503469030300c400c0c0e8265101c510340e07540640303107007621103101c4e03800c102c1c40c600082c48641c2100016601550504000946a4490811480680013101c03400c005a1001040c04140f0100c0c402101c410400503c019207589460110412041400340c0300901401c04c0000c64000c1103040e4001c06011f083d852020046c96081150f5103015004c400400c0c2e521f03018502c0b415080c2d40c800301e002401d40740d8940041030401d20b00402d01c6200e41c054003003030503043e6040c0218102c4d6600e0541d82402046158010403180c1030380c030303101d1040300c405502841001e494230741694504d0b00c44441c0c1c032100c1400a00904030320030402500360300b0205a44000e0718a400c4c1c5e00c2c00d5004045d0002200b00c540c1d40124034080d80c030b03640c1203000b1144050f24001c4081950000402c1401c01d8001c1500301204401d20500341c01140c0d5441c03a440a507403c5801281554201169149042c1818030550364002402c680 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 33759348 1250 33758098 33758111
    0x30308150316060e010e1008040303060803090f0d05010902030a0308041b12020402070204060f0609080f0601030519050a0c090608060901150504180c090203011505070c090c0c050a03050418 83
    0x2107540d01985944075550a10410080354400c9a01030306d50b800714500003400340400600b10080041c45040f0448007200860300d030081c0031880c2040042075408046018040714000c25845040000b1080301c100111090b40d21540c0c4840141c50030310911211622176101d50f1040e0070a480c3c01c0303c4005490b441510707030301c207684010040c40c04901200341000c1d4058500581d290000d0010401911950b042800086040e0707000050055001880c50100c038034420642c0c941c0c5103030101c600d4448400303100c06002a8010b26400c000e42c0c0c1103040c0721400500c82c00c2240d1803c08140d40344c0001d0040b0341c0c86030000c1a0b4858003006400e4052082d641d0083c101c200070820400049001d8088130b85501541d03000c1c958030b0203000c0c07044140414482c0e403180c0110b00306000e9562030f01d506000e5842409460494500e2040451405014205840c0074544c0500d1980b006c1c0e09040b004001020305400c0310003000504d01e161004104c00f07101200070035000380ea840d41d48904201c2c3d02910031140040c45030001e0701e402c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 33760598 1250 33759348 33759373
    0xb040b0c09010c020909010e060f1006031404021c050d0f08010608130318120602070302070506180d03050d0207050a020405010602030c030f0306010e120601051305040f0b06031002040303081503 85
    0x10f110310541541111601c0d0707141c0300d0074403040c01010303075144034126032061905010003001e207185882c0c480d000d03c42e5030095081d2602000c170300741c406903424142120b02c044040350052a200040c80042107400c0d400350003084641e150945070020184410f00030030300b0b101d030008150354410385250140440d1306100c006410500d00c0c401c400b2070419001380421807615056500c2c1032030049154000e052081000003074400c2c50404200a500c011400c60252048040005107410b050707069070824900100e07211802e80010060084140c8d030720904400b081000c01c06560200d41c00e10140c6021401803000704050f000c503106200448106801840c1554014403455180000000482d100983c1c0c848406450361078510050760020b042d600da180c0e000408801e600722035940001d0301c0303040790801c440d100c40ca140c1c080d9141003242c006417005000d01c0c00b044444000704050b00c61440d04400d025040360048000001c90000700d80250f0811800038401c501480400704074480e005106160031800780048440c0d12 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 33761848 1250 33760598 33760607
    0x30303050709090903121d1615030b030601030303110d06030b060307051e0112090209010b0d0c0806100507020312041409010509090a0b1003020301060609081905030d09060f0204030b040b0c0901 85
    0x5080820346031303644a480f6444511140c001f41c55200c0840e01462043d80c0181c041050500409108124901d0707000301d040d00c64040d00d2215040a006080c043e402e41d14200d01512407000b007070000000400581c81c600d800d40c13042d80002c0d4000d01d1040c0442c1018400c01d410812250310007440f81d0f04500e55804e907d11070780103009421200f401e0043d121840700c2000805010307180b04c065072200c0c0032000040d00b141048010080d02c0b00e000c200f006140504c040554052405594050704000e000d08403041c210701940050075041c2c0000e0441e04403042d6618003000991141d0420b5180c98440c4190200c1828002c01013800340074100c1d904c40703081c9045c4a040703990300102c80b4040c009004e5000450045040030845d10045c5801070024030070a621000c02130030040d1a807141c040180314040d5408062440050000b0989a00802451074141c07100e0010b0080c116016003607907403d80d921105c0c51000700c42d01c010802544540d100c100b09180c1800c00c99aa03100040000f600c0080030020300c0900c2e80d20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 33763098 1250 33761848 33761867
    0x40302010e1203180a020301050406050601020d0c1502030408120702030901110c1309020d05100218030303190c0212180f0603010f0b070807060e1b030706020c040905011401030303050709090903 85
    0x41d4074004a0556015444c1c80ca0b096420300061b415520b0311040c0814000c803500440e20428003a02240c5905001d048115402c6a0180f000b9292001485c20483d06002d15001140c00c240030b10303401414902010302390220088240c074110050b901c0010a071038a541c0040c1c11000901522002c0c020347c442060205200c1c40b28906060285a03880c1c8500c0110f40da024204004580c00c2802c542c0c008100e80d141600a511a10413030580354a08501007034545000000c8038410f000c064801c42e0402690713030400019203c0e8105010130350080d8001d03c0c49890b52540a446482c0044c080c86039400c401c8000e0007994200410340e90f00501c0204014000d8052544410040341c00703242e40035503283c02c142041c030081d010300600248400d00701184205075285c0084c0c0b060303000c4c40750320b00d81414800f140205a83d40e05144580310140c0c20840a949480c0b901d9805600028010000881c1c20341c0c02001305460034000340c10440200e66102c0070300c01460740c0058041e0282120083c100f01e4003400740c901070240c429 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 33764348 1250 33763098 33763111
    0x705090105270705120f04050a030e0307050607230607020d1103070b090a150506100e06040e070f030c03020f0f0304060f050907030308060303090d0f08040b0a0305040302010e1203 79
    0x7604200b10014610a00070100c04080050054420b030400b03920003400daa00c075954110f00b004149000c0740a9a5440c00e2050181c3c0c1d1100c010252001d640c0e170706860244500c00c08545c0350086200004468481c9401440218820075600d20404d1659070030001e01100d04000c05002d6024408000540d50002100414400f003810003062415841e1209859031150f804000d0161051409019200d1800194410a21b100d01081c10740002c40c94040000c681d82206c5a551040f0344e0101610071318040c0840c080041c0303001e8015071a00d5250350381400d42d01c000b512240c0004441ca090801001d9052151406e00c43d4507140035442c01c44050f162448900071848441842d104c00000704082000540c000d14145083c5001840680b1701100c150740c8a110500c000c2d000314102500045040c40c0c044111204454020b00050ba010b5107519007a807903801103030003150802401c00c0041242070003000501a40c040650300441d051826240003404d582900600080030350001d48021318980220054950014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 33765598 1250 33764348 33764359
    0x2060304080904020f19030b0108010b0c0f0105040b06030610060503070f02010902030f030408070618030305070503121006090815060f01020a020a030609060509120306060711090702070f080705090105 88
    0x46560810803042d01c00c1d90840c41c0e015100185e01e0780c0e04442c400140000380224151403d50039000841902900c0518000701d001485001c01407007820984c6025042c200c10610486d0280d0455048150859000f41c509580c02284681000760a203000c00c0f000383d000d441841100a40d80c0f0f041009003107400f0180401c030034844a81c219001c500d100354001c2d52002d0b001012100302c21036407a00d03903403654030a0148208901507070b0800704800340120f000b4008000b010280c10038451442c1c604650540010404680070701080194010740a142c814240c045c0003410311181c07038a46400405451a14258424100c5030880021000c1007100c10030200d034814419900110900041d02c0100e08015040300000d51080750072002205004050307105101d264030610040060303032600700c1056074a40e80d0b0a8200404442000001c400d4100b010207000118411202c1003405a502c81c0011074a403030440d000d40040c0d00c400070070800100c00000303040007450000040e110550600003c03038041403050080ea0f0154 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 33766848 1250 33765598 33765601
    0xe1006050a1209050a03090e090f03041a04050d11030d0f0f03052206021317100c05070c0603090b0a06060c02060c0708071e1505040621050106020a0203160f03020603 73
    0x50b00c450704000b440650080548844044c1481d000d403043c0c8080c0603140c1441d0328480016000c441c00a10215513513460001141824030b450924041954442c40d0810315500900000036641c44100845000c103102d540030904104900c4141071421480c41c1100040240c0d884041c110203401c01e0803000d80f41d00a24010449540345641b6040300036165503886907004a04130000c0030302c603156000c1c0c00320000300d004c0e008905695000c00c8048980300e440304d01080d04090307250203491400d5030041041c0d45e80c40c14944d05108460302c0b102c02c1c1c80341c2c0c2e91040d00803a449a40303190400070310b8a607243d800400007404011060030000020700c0d010710741c24001d000310381c001521111480208640402410088101c41e90319444000074201c10b02940000d81c0d49508076007002c070301072040984108601806940c1d03103007410b2038000c04507000d401220752201c84d03003c1418107000d110b43c0d40c040c641c080c01e40b0742c0051040d08114810f01d454800c00d400d074000448404082400852412051101101c0e01242c1040d00d0703 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 33768098 1250 33766848 33766877
    0xf010306050907030f0608060c0a050c0c0312030a150305120913180b0906010e0703020f0c121b0a0507050f0105210403030608030c0a1b09020708040e1006050a 70
    0x10881600065400101042040f0a80390305420256441c0700c4c0040030b200c0d05a6829001d0f656100a94004841c45014410011200d20400c09412101181e904440762081c034030000c2424111020403c0182410000401440344400d024640c0c410174440e803100401d92450303c801e80c90f011400c0d02c002941030300050214540e503400718201074505181c1d2040040a01d803507807a0041034501d15040b00c51318240300002d4110b46000c9a054125213a100e0a00f070f040d80d655004500961210b02a100d01410a100401541c00200044400c00080c3c0c80b40368bc2c1c0303030400c81c40324240c50006143e0a81c42d500c9a400c642c002000030803420101c40050721030701100503004c80165514080d036210000d07c501c616000c441590100740c1c045000780e009480400c440c1d52942803c0741c90344103030780026901c0d0748010b10380e0000800c0d8111200b0400304031404a050316440f5448882a81c0c042c01003038070f640b00049424803095240800c401c0c0c00080c90580c44075514601603010700303140142005141070001d44408603d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 33769348 1250 33768098 33768101
    0x3050c0403060f0504031b0f0f1a151905010e040225050106060e040c080402010804051204060305060f0901030b131703090d020607030513080d060b03070507050606040603110f0103 79
    0x70310ba1201c0240010314510480328010304040b01c0541c001100d405900c10301840031044440140e400400b9842800d00740d49507803810701600391081ba400c9288000c115640521500382d24040c142090303c1c080140c0f10039081020311031001420450000f5050001c0000c2d80e08940c01c180142c506907809a00d84d040c011450800d45044c0900810f0800b008001804020b4194012b200741e5016440c0c441c000340314a018002201c200441c080041030024005c50050340c0221070841c1d00c00c0c4540700700c3d4501c3e1030044540741d01d80c1042e4030482c0440d4841e0144809441c108030f0440f440d0708251811503182d85143c86003241d20902034081514a051800080d080c4060421103440c10703150300b03034607960740e09040400507a1040614480001030181d00b012521541c030902403a80548a4203c1e0314001010a8881140c182d20a0b0624501e15560b0f18000800d134500320065807240f070160711450703283c42e0141031003030414038001d144610661900074280700081408104070034001c0103035010311a0004507030040c5c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 33770598 1250 33769348 33769357
    0x61809050619060f03050c0319050402040e2509050403020d0c0302030c0d08071206050609040b01050903060c040302011d010f030906020c0105100518010b0307050304020d14060703050105010c050d03050c 89
    0x2e008094500000c14080e80088804043c007402d50350401c4907555002202810f80815160181100b15000c0902c0c0500c50b03e402082c3c1080c0002c0002642c2c1c0e2400c20f8003894090f200d001d0b0103048140c001e9141b0743d15803051b441d60003800c552000348100c1c07500d40d800944410082039a881401707410300720320082c94800c2003607442201c0e03100c04841c00e0b2003048001030310409003140c00e1400100740d450f0b03940101442d4001c0c00200c5401034115800c1071907050800c005400c5c2d02003040d0401609020328920ba942c10000f4600034611082007550b1503007140001850f0502d003c41413883c81440704903030b842d10b907800f41d641e2003c419140f50018248449103017603806403080303841070026503092001b44046804040300403000c40b03508a03000c0501106500440109080910580c1400c00003840040c00340d502400003180d1040c8028004402044969110b80107441c17203c07100310041e4091800c000a081c2c151291502510003400d040815051548d1160b80d610401c08028040584403004a9400c10520081e01c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 33771848 1250 33770598 33770629
    0x150907020f0d05180102030a140a03020f0403060504020102010b100f05130e0906010603060501090302031207060e0304030501090210031b0c050708030f070b10030c1a07060c0203070605010618090506 87
    0x81d24421071440000349540c1244900401444138076103503000c0e542c00082141c8000005490703040c02d8190620b150a1550440c0300701c08103140e020000801071402140050000c1c510807403000440c1d040078000242180d07540754a0501809107035821083e01c9070003200c2c0400e103c086d8584590740300c640000d2028580859804032031814122400c1c00700b00c410108180d410f80c0d1083e5010072100c4d548a00444542103070784806505078111413000d04003c08a10010051355000300b4001c01d402c000109514550b500903482074034103035510031403a81103240003400034410504900e4103025111a42510140700c032554401e107011700103004054810820244000c0c0d00402c00e0000f5241c5810f0429450519a07200f14001c80d6245c1040000985650f0507a4107030301070326046600031007824200003901c65801140342148001103c10711400c4000f95680c081c010b042c0101d6805151a1200d80c904a826540103030401402e001815550040c0c4001c510841c508407461100049580d4440c9000704d040038902c280d01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 33773098 1250 33771848 33771853
    0xc0c03050604020f01030507050d05040503090d080409050f0105060301090e0a1437080d090803040804180b030c010c030c150e060703050105060d0902011209061b0206150907020f 78
    0x800e0010200320300b8800d900a4464080720500e58004400302c41c8103c0e0100c0114a0a00030381105201136840241d0041c45007080720710b402540c0c00001e080300d0709018106e6070100c000900344000e102c0c074000e07250030401d2282c400f0392950400c4e0010361203004c140030f58510345135501200723482c0c3e0100300410840c107070704a9800780b000e04c41102015155901c00c4e55000000109a04d401c5219010365582e84112281c2950b52244403243d070343d0703098140d110b806000d00540e111a0302102150041d001540558800c0c00343c10303540c40c40c089494101120039142c1d05280c502d02079800385a07480104c0e940d0720400003480d05d080755186034a829201c2e494100000b0b0100b1001c040b69000b042c6c070690205003418148d004403500d03030b0365645044007590001d0140035004a0140030114111a140d0018400c0e50f205052003415101c034840040300700e4184174020740d81aa00e07020209008107072160945030582045c401b0700118a8540e006020a82070003043c1030098005600042c078961007807103440d40c000c049009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 33774348 1250 33773098 33773123
    0xd210b0409030503090d0c12050310080102030c07060e010e0703060b1504080d0e030f120f090603040c051203070206090906220e0106050f100e19120605010506120a05070c 75
    0x80c000c155070001c8420b00e00311b10506042c407401a0185594000040d448541c5101e082e0301ca9030102c2c0c881d000500b900010f048404e00100b4400428001b075403245030032628903910307090141011310558441000b10809645007403c0d151900402040c1042a20740140c000f10350369400401080340d40c007601090b22027848011070b011441c148085024540400c0907078403a11221044810140c813035040c00e03079000055120b1034150705d6403090074002c0c0200b8041001401e003411268000700d46590b004480841310410350703160500061400d03051007800404140001d5061039410ba0100c1c4461042c040490310403030103140025026501c4643c145014006404402c10850f0101140400341c044030103008515401e2003400b2507a428014620729155400a0503c102c0303202058060b10a8005146a43d0300110038840750754120540941450040c010350100360001c45113410140121001a00101d01c607481c1000015085495045416000014144006455140c4400607901d5060407a0010241104e0030b1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 33775598 1250 33774348 33774353
    0x201504030302011e0513120c020a06080708090303010605091903060216140c13020a03060b030709080c0a08120a0c17040302040b040b01050301090b03160b040f080d210b0409 76
    0x402c04c400c4908035080c0103e100e4600c00c00f00c0c003601e1040710203a601d4010840d01c000824200c80c5414040e02c5541050345818000d60007040740802c5a4100001045030b0b001804440399000d881d483e4044482000b9500350350400307200400e544540030407240f18000400c0d89075000380010410900031980a203045542d6401844030300d2510401c030700181c45034003e02c14400c07080b503c0444c915422a000400840400c010910510000e4002c016250304040e501c0360003252010f0000d000758000c000e1902d84440b841c0c6081840c515181c81d06400a0040c64441010403450394005160417942d07802d101401c1c4c07540141ca40c00c55800c0c00c40b0501818102502c02d013a5100c4003194002c1040d40c0c0207450500c400c0e041c6406100070746030705130455800a5810801040f0b071045a50000798105001401c0e40da420b81d20140030f0b0001e042903046100e82a4002400304480a50600b003800246103100242021403038481000d000c00080c00d10f0300c1c01c0b522203c80c409260040941c00103004c140018800c004079203490 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 33776848 1250 33775598 33775601
    0x20d1503020111060103020d02120c03010905060a06050d05060a02070311060a02040504050903130905060a0b0d06050301060503070b1e1b010903020d03060803031501020a080a0305041205030420150403030201 91
    0xa1000764081180414038002142c004120035060b0b80c0c01a2000d014001660300b400b260503290382440d10b080c0101c440e017000550f8280140780c1d8450144005020508001124408440d03a641c0481e11a078541030000001400110781a03500c244c00110041c0c5551107400c060325505c4e40064502401c1c014031040054099a580c0070b8820fa50003031310200b00607520ba484150742c07842040c40050349020800c80c104820682c5130802a03001c0005004483c5581d5100c0031f0003010342020078003100223516200148143d050174460f04000709021001486030900e0058001c0180c443c58104190104c40c030404445a0310310711781120a0b400300c3c0c1088010300c503201c0d039a8070300a000300e2100b18014019403044461044c402d001d018140c513030000c091455a25520701c4c114ac0c1c02100b00d407484c150702400b0405808524403401400c1c0301c50081d1400300d081c1c600352400a4144040130325480c240201482070001090070590900c02806851100c0c1201c58501000115412401e003200308800d01d0000740403040680c10f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 33778098 1250 33776848 33776891
    0x70c0e090a17030c18040209030d030603020301050703180807020f0a08030c01060902040b0f030901060b07050d03060b0703050306044109030f1204060605040204060c1208040302061504020d 83
    0x203681940041460902c107000510080c0c40d2110012801c0c4002c00c0c0522002080004a41004000524129004002c83c0c00e1008891210020a50710700007007080d0300b028000d9952008451804100b0303030f81a5110500d074540307142c0340908280804525041192650340190b090050002e04c849403850740d8001e2a0b0f41c0e9400420720070450350801c0c400140d0070312540240c9066810005203942009001030078010103402c002c055407007940d26280006503030001c1400501e5500c0c007600142010352a061405002ea030510790104624680c104100008aa40b160540c2d4000108070740104500103402902d4016400600700c5100032103070420044905e00001829003e0044540075071503071595100c6084d0780324022811440c4001c4401c101c40da03059071004841c00d62091003001c00045260300c3c1c4000c41c04980042d000b0380085200420000c09014400004460071402440c1000c41c0340b03050b44e030003500d500021780004203800c2400a483c40680e200d8043c2c481d0205115000c0204802c07428898405100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 33779348 1250 33778098 33778103
    0xc050c03011d011b02060115020102040e0c0c07060503010f030f02030a14160501050705070902090a090e0a0303110304151a180f060306150f0402090d20030c09010308070c0e090a 78
    0x600308451064010301c44902d848240d6a170090952a847d001c2e10510381da808241220455500b0000071807455a4401040d0250900c3c5014a49030150b6a0031285004000c2d0003682c10311400313000401c04440300c60807002c1600d51100048610a8240c40424a80a183c43c03000f0082e2040c281b80b0b0600c610700181032005100c044d010f0346070041d40d86006403150f108404010384540c00000c014481e65561360020641d0030740141c00d0400c50396503411800101c031001811030b1103e812861281060642c580295503000c0781500440d451808d0955440c120600311400f40c00809469110360640813011000c68a2158009040441111500ca116541c0c00700102c0b01d020b6200b40210110302e090500040302403140c01076002401c000e882490401402282c0c21403040c0d0300503000c121074420398a410f08840d60031740c0b05842901e0b407591031031581c8103040d140314103c070300035401142088529950042c105044a4002440903a1500c9500b824000c4050031380218405050486c11b101c03a0080000d94200d5290 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 33780598 1250 33779348 33779351
    0x20d0317071d0109080a0f050a05031b1216030c020112150305150f0a050405031b0c130e0a17070f05030c010b01020307031d0103090c060e01110604050d0c050c03011d01 74
    0x10390880c0195461042c90044d40319646c40041e1200024207090050704205008000f1100401165a01d0345d1a652085031904803003514603007200c200000401070820155100243d4909000c102d00c105d10380c100300003030044c04000d0300362801d4080da40140307500c85515690890912820031380102c1d0300214107441c0b00c00c03a000e100f020300502c0d0005400099500a070f010b201c001c500750300d5010000300600704c041d106035018001042012074032141c01c2c2400440c03004e8903015010300b001c0801040745900705007200c200d216007032542c10a0401d4010550314441c030740c00788003040426000c803a14003540c0180c83c4018a02c0550140010a10500101a048200719140240010320a801c01240c40740500f800007408107002c05e104080e10504410507041500c01031600080e580c0c101c0d00c4022004c901c0740e2017071003c50420100080c07a0350b4081c98200b4900c0b0000000c0c1b056060998400343c2c1c601c01722151b43c04101043c2c50320303401c00c0707810301c4903940000300100240460411385070903108014002c002c0e543c056 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 33781848 1250 33780598 33780647
    0x81b03010522060f050703060e07020a050d20030c03030f0a06030206160204020706091202070b0f040605071a040303050f06040e0c040b03030c061e0f010f03020d031707 74
    0x918050003158491425080007942c2800c03500e8541c402820080c1c4100c428a8568006003035812003446128880c200c25030b80410821318004100700304030b1000d0402e2086402445180c40400c00000c0c0c1c91078800280d281602e0010b01205000c11220100b1401208a020000703c41c402c45800002442c09101d05403960700f11502d914088004031070741403000940084046c8070102e40300000400d076615103800034001504e0010140e99175021100030318002c80e01c09a01c08902e41d071080d0304010000c060300518940b1071821807560005003c50003203102d2413041110018840041022040e60303c0c81500c0104549440381c2007500d000381c00b80000700c4916401103e401c0c00030b03100e40b034680508020342210b403000d013040602c03000c2400082c1481040c49a05803100300b000c02c611400800056201c0c0140050300600d0903140820b11121f0a80a03040e04800c146840040c0000a81680d9903400c4a904880001550041c3e1606484001410f0411140d0022480c100001e207034001204000c0104c1c0943c1d401e545 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 33783098 1250 33781848 33781903
    0x101701090507090f060903080702040f0f090b0612030d0b0613030b06040f060509060904020f0d0b061207050922060204061e081603020708040e0702030d0e010606080c0a0905040608 79
    0x14042d10b489141c1c0041d9940c6c50800100d031210004101007800a4030203d10942d07042c900038261107800c007200c06026640c1482d0002d02c100d214509400400c2250341d0400300303002690f282d99134010b000b102031440b0b50b6a01030038019500d150403544201352084401992030b551703003420441808115010f50050303003090880c0203581200d20840007650402011040e55440728400d02220080050080742c0101c642c001c1800160347d20791403644001d10803240d0343c5240c0341070414840d040a241c403082c01d690388130020500440c2c0d0780c4504940d000810400301c0c005400e2105502c4850781031144d015001758800280070401c903600c001041f07103408079180754000e80110b480b0100c7c1c00d10000c46450709407204962210500ca4800c1e0009c2c103002d8019400d8a0070035443d01003504c1002d0b0156000d40260340001841a0612564040d81524620720002004483c0c0740840c060b0000c400100740c0311100800142e20b010040c01090145c019180103002000318070b0301e400195946110b480040c501070b820b0100007818 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 33784348 1250 33783098 33783119
    0x708090604020a030305030603070503070b0901090f0510050307030b06030106080106020f0d050301260102160c08070b0409020903150708061203030603030706020906071203051501050a020c10170109050709 90
    0x140b41d020302081c2d030f95491502d0071116908054562070303160084080014042d5030421850300948100784084d5a9492a030001425840d000e9001402c1c985010740c04010344d42d1252400c90005020303042180c2e41c9e5903201b90840041101140301648220b0102c004100e07241c1c4002c81605a4415800722440da01d450001140d039800c11400c0040080e200f00010320000d1601850701030202044d002080004840140d5142607070403100c480e020504402d1443c500b4018a424448010310000002e000d400781070042d243e60310311071806100401030300007a20441740d403010000054003001c9411420018100710b4402400c511058039a81e100b02102030101c0c0f0b044c800030048900441004000b907280070881d9580d800a504603c1810f540302105000b50720118100580c0210f0758407840e500012540362007421910382c184094441810414207108002e0783c00e400044203002c80c6012158142110004c050072035600e00c00d080e042002c040920000140c003e5660401c500645103501c0380e0f00601e803200411607 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 33785598 1250 33784348 33784351
    0xd110706111c1505060301030b0a0b06070506010504090804090c0206150f010804110d05030c010519050606090103110408010f02091002010b03030304140c060c0a02010e090705040302040e0106050d0b07080906 91
    0x16906980c03000d5054440348240c2c0a20360410f103000d4041031140d600d10029081e900264003c0c0c0c0c20885034810807071844082e00c0740001044040b5500d40c1000c0103074031820b645440500a80d405039580b40f411105001180083d00c004044522003400700a94a82c0c00035200e81080c0c0b02d144000050031004200e5243c880038449980c2c00603981c002041c0c0d0b641e1112905a209910703074580000c0b00302e6070500429002e000134801078032078000110b1ba5042a48025002c901005021420a861302051000a0752400700302c46400c1002d1170041352203170b002e00300f1800c2c900c00c95100038070642c608200c0b0400e80c0f007503801400114a00f00c4446180707801e0410b0503800e03140d0301203040360f15030410400240001e4003124220000800041110508820b04006c2800384d44002c468000c0c076400780e51084e04560740203420551001c41595030341a1801d015201a1540c056400006e10590310f0311031b82000f200c000d40c0440010003000f000030070404100d0402543d04141902c10a00040512001070240203000440070f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 33786848 1250 33785598 33785617
    0x30902031e03300403020714010201060b040b03040606080304080709050a020301060f0807050c0d0809160e2706040f0c0902040501210e07180b0909070603020307050d11070611 77
    0x451420a2450203005a5988510008a00092103c454003400c0f5000c400510507072180d001400c01c28142202082860038070340000e07045a0624400740590f407400d030191000c5400e4501c1450703da8035540f401c10f003d0b043c1a04484014070011a00040021000592400b101c01070b05040100351200760465090780f109004800104050202c1290194810034840d680441d40785007490420081e1900c0c10308140c0b0080021000034100c50034405003100510082403c00725200c10410342034a030040140a909004014111211503018640000910380c642c042407044c01c0c40030f1302c0c4079261500d0b104404040540d13050b0750101002c0c00100f2442514401c4505844050b160034020000c8000309000d14035108046a41c0d154a440a02c1001e4404100c0c41000d02541c800240b00d0b034601091202c02c0310b8100c1e803000e206140c8802030108050300030500c80d007901c1c100e14003d070703590392824000e4445108180602e030800780f400122030088111070014011030791060509009103417411144896038000c80d0703000e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 33788098 1250 33786848 33786853
    0x6030a12051b0633061c0f060e06010206071409010201060b030c04030c061b06021c0c0f0206060316030f06020f0a05180a0608180712050601170d0801060503090705060a030902031e 79
    0xd00f400f83c617010002c0e01038145454612002180b0014810040d5030003200c0e0b200b030b190b0f101c1c182030040050380e501d01544200e0078801001c951034203520042081088524003503c0c0c0c6000205045980d1007900104003500e04c0c421720b640c0d2401c003c075252140794058441503620701194031020403003510820b42e0b00c00f588c80740130258207080001e40740c90f8000c0d0f10403080c2107121032101801e0007051906004241200b501074a402c0e86246940c10702034180320004007614840e41212580924641e511103485080d240c01440030301c144409442c00f20b009108030a000070041001040389034407694081d000380b03d9002c80e607280041c2c82d0040010b02c402a1440c1c0150004154003070005241e40c1e65100d0800c0500781d00d5002c40d10380580d0380e8522140e54450610541d03454001d94014010344000070607102c0060017010003800c114965a00c01005010180641010403200101056000c081001040c02405000308590760310300b0003407400b900174440190103d00030300541d05262449405109041043c203000ca02 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 33789348 1250 33788098 33788191
    0x170f0d050f03090304090c0c030e060a0f05090d0203190318060804080705010b0411040f08030703021518120d1505060409090c1a130e06030a12051b06 66
    0x741c580503070001030099407184018040000c0d02d01060050031440740a546941146e000b00d410020300c9260a0380c25240604030030890f0640d0070b40c2c8a40013000f8025580b8089498030009400200e4524041c0c0020703500d84607802c040058140300d01c00c45d4082620903110f02001d2000b10601c2002c45001d03201e00c40102d5030481c00103011401c81001800308030302c074100000d480d25203040090102d900d00c00c3c03441421034010a0520513407295030130100c050300b0f03484000c5043c034030b050340d000303688115203030200011a0281d0f01251121000802501c4500344280070740b4040347c800c0400f4407035034000004840089003042a05a10031800340b00380400c1e14006070800e031a00d82030100a2000e0000100100c5840c8081400060b02c0111040740c680d1650b410b00001c2d40d03e00d82da030f540806081003500521002d0020006110142d036000603820500b982c4006800c041020010303041d6800c2c000d6800781ca2103a02078031007141c2040e8002c924141305903e401c030118045919040594011b01440c2c030392110110b403151 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 33790598 1250 33789348 33789367
    0x15050c16030b01171f0c090602010204050907050f04030501140f01120b0103060e03120c040306060f0b04030f06020405120d1b0201021f0b0a06030903140304080904050403050d0204170f0d05 83
    0x3e84c0d00021000030360072603201d248110244607480201100400c405a82c3e42c0c103031454141d00c40c4450f802001d0510003036061604090010b518004c025000f0802c2c0800095030143d10b200c0c1a055030015038002c0f0081083d88000500300300c401100b00c6079010f009400d00000f04411103007885408660b0340042c4a10010b030b085a50300300c000c0064824640d1076200a004202100540654252140700c1d81202d4944891562410a041d1015500000055007810009101c001c54040546048a400c00038000c0e00424030b003000d100034841d98000c81c0e00084d100854084100000a000b045821955103080d42c00c0c103620b1040c00c00c282c05460003401600314400175502c0303040b0426803030414110514001099921000020041c0b15680e00810102c7d807520800341c241904100700d44000020742980e2451440d1540c2e03240301501c60030b41c03800d11855544002c06c060501c0341003610440600fa0700d0440d40c0315211840d079880720705118800d0b0100d20034080c2040c2042000304620540b4516925180d0900304840f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 33791848 1250 33790598 33790619
    0x602030315030304050d0c090c020105090a08090607060c1d0405010501020a0f0c05090403080f0105010504051323010801020705070504181211030703050913060320010915050c16030b01 81
    0x1294041d905120a00005c20203030386801028030340d1842045c65001d102d00e4180b00c00152000441801c09591410f0100160f5000c0483c0c500d03d000d41c020405551050b46038002412070258600107007103c0d00d05602c909030250851084203142081d052000400171843e0304100540340c003405441c1c0160040c58002c1c00080c40c440441c1400340c407903501300d07000715103610200e0f00e503100403501580020f19400500c040c03440c941d600540500b03001e04e041440e00d4148004140020f180003260702c0020f5030b500c9041c580302559081001301c50040d8900800d5565600300060203900804801d540c240140c03140020b592405200f070541c0886050001070789040d0300d49440510040200e607035014880400201a50000248000e0952911a0b1660358550f80f0f07400500200e24088461170f804103281420a0000c202c5038081e01c040ca12040a0504040c107a860048800d0403403076000064000500d020071000d25005005450600d0380001150349104500c800641c1c010103a01c80500410f80c0c0800510640540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 33793098 1250 33791848 33791881
    0xc0d0305040506070c030512030402121501050603041b0303020309030d05040e220b13110d210201021c0203070e09100e07050702100c021207080606190b04030c030c05040606020303 79
    0x900d0003070b2282d0b40e5079280e6074241303c410000081600303000403c10003145823390002c00d403d00d541b0b009184000c2625220300c4c1d0000103010b0309100c0c42c80400040d0802c07000004018031a82044002c951960382c9160180d40c0341c1003045514824011505c0200126100d10280d500301d800c2007607499418ac8410424180e203840200e80c0c159000f0a21403020f01007044054041d000f07900d90001c041201d0707500c0c1010100e000040c4815485200b0390b900440208029614500148030080d008d00c501c101d481340180c0c0280310710044007428507449114002591210381c06184507270550f48600304410080c0c0d0401103500c000b100c000c0305400c039412040c000d03543d2091485904c6001800e00034a800c80c60303000101c0c3c61990450707100c00a0701990001c401c60404c104112502082c0c2c0c4014104a8240400c0c641c1b51f12000704014000c2040c080910208040908501c0c01046c01c51002ca90700e03512030505030b0040c80c0500043c1d66890000d840000c19040c24818a0100c0305154061800d41e12681080c0e18051307413 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 33794348 1250 33793098 33793103
    0x6031e0e030c06040b0412050301030b1503071d010807050402040620010f05090102030618101e0b04030b0924070804021201020f0d050a0e060601051b190201020c0d030504050607 78
    0x140100c2c2a80001080110700803801400400c0140c682032800c0640315066103141820007606000400020f030f0f01c038040703607000321010314614002681d00010070701e0a0303d00d6000007111641c100c03603041c4540011110b80e060340e0f00c50058859868407241071105038802c0d0f11646d0000741440d13498a00c0040c0000308050200c0c2c0c03030000482d01001c2c124400b0199031050b0380b14025030358004240920382c40d0100844c0c4d254481141405407914186d90b4500c203443c1e81d440340410004604407400b410308440708070384002e040d440040301c4e1250345904040954550844001080c0d10828960858030072700c664030400c41e088100c440088580d500c020894009501130801c90708003044580f0301603500800e00281c03030311000305101c460b00d07102e08030b80402c2600c0001d0051303000c030b5142111b0b101040f0404070f0300e10341c060700c00c6c00c1c4a5078400c40402c40d507100b400f8100e405443d6000306108071961203040950100c400303000768200c0e9110440c21041141c0c2454a040060100d0000c1200b08268105031001d00714590 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 33795598 1250 33794348 33794353
    0x20a051c020910120303061712031302040e0f0703050706080405031801051e09010201060b0c1902031f05010e0609070801210b2d0f0a02030a09060e06010503010606031e0e 75
    0x1c2c1c0d03a0030a041d04e104861400c501003038a590b0103002070760115003d40d81c403030702c1c2d078004183c1d1081c0f01c00580ca0b248009041d6000c481d85c440400b40030354959811501895090b4001c4504034850100c1e0541c03a028580021a014000d5110015000b4031076400303140070356009006107207890401c4659a44002e00c2c0d144550501600b80710301c04e11902d880d03800b03e89003103007426181d580390113880009003103e0316600301183c9040180052403400c940090345010590f600c0396803400c00025800000d107008144540460740800060805070a040c00c0c0e000103040b2191001524007e40b6590100050312208459510019401c000104686444003480e400001c0828070b00a43d010800c0e210010107907001c440300c0700e002da2552485060040e81003464901629102c110460b05d00703001c0f041d043d550201601c178080440d004804100312601c175900821425a101404009210340c3c0795045456901c00d03c120341c0f2039440c0c03c90005000d0701038080e401d03000380054050000c4c2c1c0034001c101c00c01030502030090120361 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 33796848 1250 33795598 33795631
    0x403020303070e040e0a12090605040308070f08160606050f011d010327080309070909020d030503040201170108010b010e030736020412110a0605030411030a020319020a051c0209 78
    0x40c01e091040c201c4090052003880000d5085d07e0000d48900c0d1160300c05001c00104002c200080788016064500c142d42c0b10014458028690420720803d005584200f80300c100c0300562201000724a030300c5001100c105903203031002e64450b0310040d00e1081c2d030b50f0340748001d640000000c40e090f58800c0c2e1041100c0d1034025001107515004906801c5018140807040b02c0d401000018020b060b00c080107141c000b44a602010300900d03a4680c00b02e15044c4920100400380140440401c0c1168005e50311a01d4002440801ca001903a440300d18601900c6840c2d031041c0400c624026100c1a81408104331017a100045d9082440310343c186000313074050b0382284482c1c2d10030b01e0004410000c14441d000400040c0620b0140110b00c0c1c0c2e5500b486075410400c4079080344540e03010f0701c04114180c0c014007030300c3d403182d00084100b80d2100d40a0100c0d0a01601902c001e42c10f01441142d00b403419000400d140105000399180c2c810380e901c0340d040c003604c62650030044400e00d00d40300d5004014a0000102c540c40701240e42c041040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 33798098 1250 33796848 33796871
    0xa03060c02010b12070605040b0a0210091505060d0503090d0f020607060b1f0801060f05120916050406081c11060f0a0c0302120105100507020a031109010602060403020303070e04 78
    0x48944a00000c00180d4503480315a0007031070f0800f11602c4801d494009421814600031000e800ca2255206070301105c00d011070a009554001d2181100d48502d8000500184400d4036105c2410705003902180c1c0c42ca49010040741d41c3d820094494002d0b01c0e07001009510340f0880c03000304540e044400904482c0c004414800c80f00581340d8002801d41c95104200200d1022034400800c0b890050180030b915205c4180c465034a0b05c594804482c0c0d04480079400d060400ca042400c044507980304544030100508001001e2102601000811564503d00062441c080a0302d8604104c2520400d03c14441c85500800041400000c01d40c001600c00542d4204000d00082d460062424100c0854405281201032810010b542d440b43c01499081803c61074214500801000d1142902c0b1040c002c05001d000e1100b00e120066001784122802175400400b0108070382d90300d107030030345200c400b0640060269074600c000090240c0001070490159070b154024500b545e941032012903a10b028103102613032158580082805 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 33799348 1250 33798098 33798101
    0x3030515041103040605070c0803070804030c061a0109050103020a02030f0306010c0f0b0105040f020a2001061e090c0f05040e090c0406030510050906090d080a0e1603060b0405130803060a0306 84
    0x5502c2c008050654407480c043c1000c50071641c00528403818020429212000220b0103001c50b91310100071300f02414640c0311420220b50307003a440000140f005183c4142d0401e02c03000c0c1318040340500c1d003da960215040c1c039040118260700078540401c0140e0700500280303007100e003004e014541c0300c481850028a0b80032651034a90143c4041c42c02a103910010400601850615004030f58514014907410340ca045000e45005005502c401440c0b11559200300c504000e45000303411250080a81c5201e062000701502c0300c0c0c848075840b510075500d41529020400c03011034028104041d201c00c0940365941014908803c0502d00d81006112129030b008912101103190350320701c507060185000303200501c01071180d942c03403604644010302000341a40c0034908000961000103601c058100a07498690402d4440c2000f03c006000324489c9510302e80103034102d80660424601c1c4540231640205020700c005a06032003032104031041650b003003118404d82401100825030713900c011030b0007010113440440016942d0303ca050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 33800598 1250 33799348 33799361
    0x40f020406050d06090504110607050a02130e10060308030f0703061e051305010b1b0c12030703200d05180405150f030309031b0a030b0a140c09030a0303051504 70
    0x41c0460350102c3d042a0000c3c0a01c10140500311610b0704210742d0a20f0744945c0e011f011000b800c00d10400d00042c04c2410000141f1461000c2a400ba100010010b1030404040143c01c4545072001741e071081007104c0103401058014401100c0c2c10800040c91602d9101450400050081858080c50707141c010006100b0b440d05c000c1c0300a04803403180c500c14281802c0400c00200c2c8207441480205d420680180b02c500f4500c012500140007881d038030200700c0341b10080d07141005c42c0d50700c405c1c0d031056152040250703905010004204181c4a60356070a0107003000e15085000c02d0b1030741803407843ca51018004d0009540194010403960401c1401c015414541d1000201503460484200d0b218000c514584c4c0d8003410a030160f000001d5046000d1400d0142001c0400c2d03030317026121140b0480030072004683e1096110248602c0240d0b4205207428502d10742949214083c1c28945240b00080004200190019520754151840018000e015004c04002a01c049001d000e0180c503941144000031072004150f5510301c07410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 33801848 1250 33800598 33800609
    0x2403070801090e0a0201120203060a0503070801020702040e0f060402010503071116080c030d1409180903070b0a1109040f15091505010206011206090f0f0609170903030403060b040f0204 81
    0x8000380d070410341d881090b10070401d15019154810f112940050382c002210400c20035403114016102d55400001400903462a803029800d0f0080f213902041080045d002001d806009540a0254400510505d591801c0d0020b40d0b0f0385941080010a00540c0b18400a42e046040c0740b802400710f402c140300f010b0a190802c0801983c81d24400e00c200b21030360050101210300c1c401280501000c09030038001400a0b40f0040343e01403044000200c0c1340c0c043c0e4941d601c0c120705007610101c05020b40f0f0f0081c0a01d540b60b00c41c0d070b810798007141c501c4002480d04819020750040c10a441d40c13040e0400510b0010300c03016010381c4001000d6a42c8813040c452410141507551002401c11050200e400308442c01e410010074025003155045410002c0103021414802101060540e030002001a01d020582403141610040ca0750062510360103480c8201031000e260003241e25640100708032203908100c0104d091691007200d03036060f01604188420030100d109a80700e42000c903406400400c0d03a48442955000300d80c0240c019 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 33803098 1250 33801848 33801857
    0x60301090c110706020c0d05010906090c0303030f051005010c060603060c0f09080303060603010b07080403021905270703230708090d05090112050619030503250f02240307 75
    0x401c41c4081e44041c0070442d0a80c4040a403070b18900303094000352581220b0120350300900d24403544208201c4c0950000d41e030103810081c20404109146020442662107200680000c1d007032801501c1c0610389442400c2c0100f01d01e40d00d107400302d86000015200742d4120070341640c10a907584030000102d089400f468000c00f0066031074403454404142d029000404981060040781e200388108a290340300d81003100e05655450b0a42c6440314800c1c60800103078440c5400c025085003890404580541c440b4455000303a88044400144000d0f0003414102c2500303e0800705100c610480d40070590881c06580304d064a502140f507803000d000d4400c40d5061040c1c1c4180d0318100094070107820401c01e21000e02001d1030359001c6d440d11074038085029000800c1e507030901181d00807040e036840c0401c1441d66036640b0129507001c030304440b0f03038141c4e62414255280c3c2c01c040c0746000300c144140302c2840c0d01d0080c0c41e02014207503800702c0c40c98107520b015000e200c0d240ba04900e070403999000b16144810802c20b204007441c0306400b240c4d035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 33804348 1250 33803098 33803111
    0x209010902030105130e15090f010e0d0909050402030d080907050a08060f011e501012020c01091a07020c010e010807030f06090e0114010f0e180c06030109 68
    0x81c0145d2030040721068901a1030203c02108002002c65a0b001c0b1120716408040c458854101c450704206150071030706800c1d880c0003581c00c41110b000c65882c0c0103e2494a03a42c2105a031140b00005455085400070f6054016084850016000388515a0845041c0080340c10040d00c0f03d010941504294029110580c04101040611b510740078100c0e0150904109a00f201081d002d4040404d0340b940c051101110a051070300e082c1c003504580000e45489541020b12580c04002481c4992841d01c100780307da000d1204842c1c160181084146088091110342d070340c491844007154420300039040b82e2152141075484042c0c0d240411301c083c04065240c0420442e03504581407604010b8544402d1903d100d05004240d01419100c2c2e03004002941d00c803080c1c4c1000f00d01407a4004802005000f603030052402680743c6200c884003110150700045002c000b40042c60745607600d5910001e801b04030351140740510405140041c003131101e03940500c1c11071403015007100c1c2d444038040c0000d01386410036003100022580d18031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 33805598 1250 33804348 33804359
    0x110a020303040c0f0303020d03020a050d050c090307150f050c0a17030915010308090405040203070e0a092607020d0c030c2304090201050406030c050d02070302030306012604020904080702090109020301 88
    0x85114000d1545022030360151780386550103925060301030680d03402e069010031605035450007081140c488421008081201303207040710350134220303821031034101d4043d100e0f4000108541d1030b4a1812044160140c81d81014559800e6003203603c0d13400561240e800340140c0940744001034021010401802481d0700b000d4407441c0c6400039074502a4030b40c42441180054500410200c1d550908441c9402130603030740030544d540c0d1030003c0307881c101840d4001081c03a0034072030070850004220b41c0882e640500c1110502502448008440180c07500742000806404082200000500c1c10328a12401d0324410782e0307682101581d9859a50043e01c00340d10161110003c2d015010030300d600768405d040342d000d045408000c3d01304543c0000741580514052071052580e22041004083d0056007554000345182105540c0e9054602e0700030348036003040d275240b40852075103116560124040b8440c070704450181c00344814155a01e03020000b503514050400e40700c541f4101300300340160b252441302602903c540315001d680c035403600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 33806848 1250 33805598 33805613
    0xa020405130204060804080705010207121d0301060503060621010207080a030e01020310050907030e0105040f0c170303070f0507080703020703021509060301090c050c03030112020306011a1606110a02030304 90
    0x760080c0030a601c104414800c19401855050b005500f003802e054840c40385290007802845601d83c041d00d805c82c4801c0c40d9801941c4180d2211070b40c100c084184142e054004181400e071000303401601d516030045000200e05040c07007141c3c84445180300ba4010889404041242d089134000703401030365441c0b00003800ca00a65014058004042d015a00071031540c500240c0104540a031405080d210b20304002c042070fa81031017604001c24543e4400002c1096040c83d1411040d00000002c0c100c51103448001c0008140d10703105003080804030184040c0d440d6070b440b15000c407130600015481b0002d011041c08142e010480d403001405060788a6002014414254010483c04018848500d20142000c00c1038217840d85803002038031304541c1d00d6440421450070345041502c0f58082e010014009100200001407844401025034170340c14001c0c3c06880c050b9888001c0388001c040c0310342081204a01c100910b02d00c00c2800090110202e028607000109040c1110030300d00580e005c403c51000680c408020b00007400101c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 33808098 1250 33806848 33806869
    0x1290109031403130e0c030402040903090b0a0806030c090f0f040c03080a1110060b07080d0605180a0c0509010e101116081b0306060607030302090910090c080106020c060714060a020405 81
    0x316001c170001803030101d200548902c4000d1009000d603840b002c105080501500c118ac010349407080c801a00d84003801401492100c007162210f1203403259400d07005681c10590f00040c0140c2c0444074445103980c0c1d00c0120400031601a0040b02ca2801185001011071901c40140060220a541e503511201104a07441e1038446c103d079451404603e465420000f007170490b001c450103203521a1055841e10000040400201401c3d80f085030401511480000884210340c605e40c45988625420050380c0d05c2200101c0d144e01448000c54040364281c002100d40340761810a4100703084031880c2c800e03120070180c00c0080c1000d9110303c508030101003114051142038014411101c3c4403150505180c0c004040d207000079503407000644004d029800010302031041c18071076011103281305030150014200342000380c58070b0030604182c850050328500c0d14a02d030b55a684200240c1d812107042c0d60040c52200501d904001e129031102404035002c40c890f012034030000805012036441094219001a00d591600091091444a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 33809348 1250 33808098 33808109
    0x6041406060f01020c041a03070603150f0302010e0d080d0f020301060207050609090103030e03030c0106080a02012706030e030702090a1b020a0b0a05040c05090f0a0e0129010903140313 81
    0x311006110060f90340000c4480d6480401c8070007040405c0e0004003500b00e100d02d1100c081d05401000030208215070560049403103c0c000d0348048540d5540e840490301d0304145404020b00140b1040c0020105103040d40c0f030650760602070301d209071806080c0400c3c002203403d12030f00c0042d0035401100400c1169014401b100041409481c1c180c5000d82080004c1c04030a03050000a05011032013004a1107a18108141d4450104407002003080d903071202034550392025242800ca001400b94a0703131603881c004a82d260301c4417201c20400c5082c86404c02d036041d003b508c42441c031205284030600258025a03201861580a051412030000714006d00303904075504c0521078040c0106540c802000c0c20005000318520030b40c021002d050016a644492030810a1610b2540c03105901003403201c1404800c903018407040e03008401c2031008020300c00c40c26000f43c0c240c440448500201049803018200303480a803003e0b142590205142481940b92255644900c0300c01c100d001311580e0b80046080030850b051520300c07802518 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 33810598 1250 33809348 33809359
    0xe01390203030604090f0503040e0a060609060e010c050c13090c06030c05180609040c030b01020609011a0d02060c0106030302030a080c0313030c030306150e01090b13051504080604140606 82
    0x105141406903882c4006050365028550b1040780d04203000e145940e641240342e000007a80c0e0f445075a000304040455042c0c900703440c0c0c2c2c0c0c40c03d200001e4a13030103508420100c49464444030540d0400c00019620140b0151098540703003d0905a0705203a5102d44244c4804601000e001030102040d0809140c0950701f504010145490b10020383c80042c1c208064450040c0c2903c0c1040c02c5400d0b03180424240c1c026021520303041400c0c028440403180e010781066684807002c1e400c0741c2040d0b680445071030990300c01e0b038080303a40007054034044031a0342489400a420140081c00d502d2601141448090850b0495481600140c00120b00c80c01d08070751010a81d600f01c2e4504804c181181401016950109002c0b0703801414004548205020140641c00c11802040710b105520b500303800310b00e40030740001658843c40f80020307000c4e107020444005000c01c1c3c41c0c24260800851100605050500800e50359417040180a140306010002c0c1d400e908102ca18402c9d445007485d00307080c004061106161500246c9418400c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 33811848 1250 33810598 33810701
    0x60302180a030803010302060309012705060702070315020f040f0305071d040c0608060f1807090605070515090a0606030302030703030e010506090c030a0902041d12040b040504020a030e01 82
    0x280f00141941c1c15650121102942e0f5181d0090301401070a01e0b40d000400f040444210341d00c11201c5604455100b8003030030a070362455858060498840b540c1e400005c0c1010411441003411301d41c580d01070070503c605219803d280c80d8540c0309001c04031080e648220f580f42c0c4074050611074410031409221000140104200e55401c15a0782c582074200e80340a01410001901c0010b001031351040c001010000b400380040020300d00320385900013171a03402c80e44580411054a400a505403080c81191040d54100700135008000c070f412003251101c0401380601c03a691144a807a0000703d510740c41854021440798004656401ca0781c50050242c4805e040c0d00d01c66a45001c040000a031240401e16900a0b00d242c07003d40d803503880d06004030003481200d10294109107070041c81d0b01c42c174400780d10003013800c92074004a60206441800d920707a42e20450003003600984040c8070420441c10107030003030180d05000d41000f1034541a080d03102030071203905040040d1548284004000c0340d044883c54810407031410075009030305 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 33812954 1106 33811848 33811853
    0x1c0203040206093a020d0b151207060206010f08060f0601050c03070309170102090a030816081204020a0501020f0a110303090a0b0c0606010201090f060e1501060302180a03 75
    0x8075001600d148010103034150010790f86680200000c2140401d6569100c6034140640000c000f40c50401c02141c1903034940380c080d01502c82740c1c001040d50303d00c0d15070000e18056060703000a0301e00f822010248091000131407000c5c0d01c10b64864225001c1d0303c40100495840c441c60803005107130b00000c50b03c0420154080a6a0212021581414954030b201c010083c202d10038502016440030302c0900810000306c49401030000c1c125110600c156400c00d070b4541c0e545c03a902c140030840c0d2182c5080200800c41c5011405603028100a100505558942003040e50b500c1d0005003011348040c1808004519039036040045a981c2003002e0711807407a00d95103242d0401c04d6005034468030302a014807030000389154414802c100100303401042507040542580c07103000081001c401481031601603040304d40c1012a100c1151030081440f80d230010383d149515000c04111441c000001ca109a020717000c200701 = true := by decide +kernel

theorem cover : BRFrame.Cov 33633098 33812954 := by
  have h0 := BRFrame.cov_init 33633098
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 33633098 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 33633098 ≤ n) (h2 : n < 33812954) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
