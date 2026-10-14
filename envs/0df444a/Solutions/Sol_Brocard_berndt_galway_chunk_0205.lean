-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0205
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:27:07.725007+00:00
-- url     : https://prove2.me/submissions/614d339b-fe58-4225-b356-9c53cf4e8639

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 36690652 ≤ n < 36870508 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 36691902 1250 36690652 36690677
    0x80d051308060f01090c0e030a060204050a3c0312020703022b1211150615070302120a030906020c06180d0e090405071208030f010b040b071113150e010e0702060c0703 73
    0x2031409c07410540984826500250410951500d150900c00509924901d64140101c1741c0312001c0c4110501c9076042d459038400f00480c0d0201c01706100c2e03405550b0150880e042d0b00c44403d4003e6907458180030032070050302041072002c08a910007c180c0d850301040306076184180d45586c0d60041c1c081030326030346000388141000303000c2190009000c144421091030000340014500001003004004504800078031000081040101003640465251b001e00342500036150784800012080740103140883c0e0103041c2d0703840440d280e1030f00040440c40601407c901b204000d9010120010140c0740e80e402d035030400c04100c0f2182c1070fa016081440b6640d0303000780184c09a5556036688c52284e00d00c50359143c401c0394004030010400c00b040e2405030a85024080c0e88400c07074180790805288040600c180040500800242000c1c1d80041e524007012012000c0d55030800e0050a4085540c001c0e0740c0382e54014054400109030000c1259800c50540718030440450b802040d00b034589032844010399101c41002d03410061000303c0c80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 36693152 1250 36691902 36691909
    0x6090509042109050d050a110103090203030a080402030309040e060a050114030d1b0602120403260402012003040b09030c09040f0308090106050402040e06030d0207080607050c07080d051308060f01090c0e 89
    0x10007014041c4018200d07d280c1840d04540c0540401d031801c3c1810b2500407107a01503200001510a80500c2d401c01214a4a5500000386940200c43c1c0460307000b4201400c4c40d486001c04075252303010b0f070194070040c40641d0320b070911110400c0b04a002641c055100b24054000309200d03180090949a480340c5d0007280d1062038484000341c0e2b0203030000c403003042c1d001002e02040682c0001104954401c59401e02203240806158400c000400340c400703410820403038442d203511800c8081c56098201000102ca58403a40c1d003031400c1d841d400111080384640124400ca10f080c4c1800100184580c1d80f1030303100c20702c0241540d0700341e0710080c000c2c00e110410341d81c0f00d9010070161a5803008102400703100030390003400e1510300d041510f00205a2000d07000c640002004001ca03a00c0081c42507006012030130a607444030024245180345c8141984028a01d2051048880f192078014005201c00344d4414805011903807100300ca1540d81c10b098481c644409048001080300514543c4600710f011054034180e4000340c90f01c80003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 36694402 1250 36693152 36693169
    0x10e0d050c10051306030209030c09010905060f0105070c050120060703090b0606091e010302090405040f030f020609060103060b040902220b0a05010c1e02030f01060609050904210905 80
    0x21206a48240807504442c038045005038080745040c5442d0380f078081d040811070030140f5a84074020506401040d228001c3d070b428840c000e051540a086001a0342e0365400141c0546800d0310318a0142c03815001d808a40d511030401c03514503035001030310124018604030044504450400c0303400c202006400b268039810301d060081074040d41003960041101803c81c2042c404115016010b14400c190401c6102c001da250b141040403c00300c07020540c88084a4900160007038072454180b20b91252600c4d08000800c40c0c031113140d02400d4000d5a03503e0809845038010b07a540e0344252111822a030001c0c00401c0003401c1c80d007080e0321000c8040d00225003581103a001c2042c3d08004a03140f0381d5201090300400c504405407144244e18207049661404480c0380c280060b00c0d80c80280d601811540c0030052101c003441842d00c44034a441d5018080700c000301502e501007402003025000365000101012000070703445c54250200c0e40516000200210302c0c0c1000f0b56000c0744015288200b90031311444a0000030665160b0750b1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 36695652 1250 36694402 36694429
    0xa110d05030d0b090109090b06090c0c01020c07140402070b0f0907090e1e0105060f010c060b031507080a05040827030f0f06010b040e16020708120705060717070509010e 74
    0x2010580402082c1041135036001600302e1402903151807800408500d403071850f59080402a03600d0040e03504c0d60001e150b03251080303560250496000207030744c0b1841c001c00207008048031100300d04070741030b00300c010b00b00002c1e40710b00c0402803d40c52501000c030701290b152064958000c1281c00441c0c00040e990520038041c0d400681e602d2600f5007000c00a40b0721200701405d1100301c250100002c10080c98440002110304503405207160401c041b00c4101e10400440d58000590071500400302c035200003c6c0b01c110007588000716200c0700020151004180c01540a0080d280580d600c00b40047c02c100e170341d080d12040c519048803281d11045200c62f8601c0e50307480520081c2400381041020306606000080c00515041c03040e845a1074480342000100300002c007810003030350040d00c94400030800440d48903080345440300325081100c4034018039001c290549940c2e07004020b400e11039015540c0c0c0c0e98450341c0980d007141c01e2016924400f80d240002170721042c0b0442c002c084c008014103045040b14a03203c0800da04c40c030101c0307 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 36696902 1250 36695652 36695677
    0x70f0b0a02280f0305040b0c090105070204060e010623030c09030102130602060105100504080d03020906070803070c12030911040f0e03030103080d050c04030305040603020a0314041b0801020c0a110d0503 89
    0x20740301d540980c1c86081003074143e40600301400a800c00e07594111086000400b11014080c0115108035030b80c1c030890445015a030010b00034488992120780400f2483c40030301ca494003281a0301c506a10901ca40d5440381202d500314030620b4115a0b40114006c02684115450b50785550308202510315a400a407200b4098007065000303066540c186414070032101039552849080c40820311082020b4840061803048820040c07030302580343c2a01c400803a07e01d009024000b4190f01c000700402032926070003c80c5080160041d900d01ea86ca05034400c3c158115003040e00058200561620b01888600f032681040d0102c40381d003480054440b0b02d41a030f10b41550401e82040707513140000582500300b50b109000369500400301c3c0c8803075440c003440d5079009800307882544504014180c02007024603125010307a00060507109028501629440c0510308411010020050105030684046000c1188101407081d0703002c150351a001408030810a0b110f99004104000382954010540107410000640600c0901403003200803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 36698152 1250 36696902 36696967
    0x904030c14060403020606030703020a210b010909050c010311031f1211090a0c02150406060f060c02010f020102030709170309180f010e130b070309050d02030915070f0b0a02 76
    0x900d130007410054081e009034460740c4132120900259071035160800490b8121a044400c051500720011410301070140c025113034402c03480002502003503d1b0040640c25101d00144d5510452810066044079040000721400000c03e1000844006640b42c0001c81c0300c0c4420445600c0a9440702d000c030800d05041d00841e0801d4044e17000b10070500b01401400c0d01f280d01c0584c03d002c0c9400141000356601342205514200600100210341841142d0744a0006408110705022229440f1000903141800c8050200c0c0007558008060211501c10f10940e400742c00c480d911120360174a0700b0580c24403804d5140c81c01501e404100071841e4a40c0e116a004001440603c000d10107601c1c0c06004440c501105910880000f0000743c200400c1008074000303010120780c45082c0c0341994503091404c80050221b010010700f588159805050250340000150010f90422102c540c40c944211035501704900540400a00c1500b090020b0000035090b07180499201440d041d00604000344040e80d0640c00705141071050070030002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 36699402 1250 36698152 36698161
    0xb0702010c08220e010303050304080d060306090b06030f1b210109110a0e070813030e09010e01090e0a050d0f1205010f051806010804030e060409020c011d0d08060904030c1406 77
    0x240f103000d00140b0f4044c843c009590300d5600c000c0d00b1440b0003840140203000004180852420b29803044000c1c6402c107008110342c2c0e81600e000c5180810070780384180b09114480702d01480c0745000600c0061206245806100d4601d6181880003083c81c0c21303e91a0101c0d00542070301850642445403c81c0390b07008010400e42e1b21031803428000043c1042d0461600140e601040200542d04a616180c000980b540d401a482c1200c0c00c0c100c40a20300b00818540c0842031100025101025026460503943c0c450300801c0304410003809203130b407032082c0d283c01442c94000c0b5255211003030207803144c00e02403039203400e0009801d800f1417610001c860098111007010340e18810140454203159042c001c03c92032242e404101e9050203400070b414000d000300001d08104124480030450b484220903640204102e00c021354451140b540c69074060090190103400d900341d00c1c039034120351003000250003181120545820601c1c1d00e514003070180c00d40300100b00f5010710086001d15000200b0000041c4480340c0450043c011a092 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 36700652 1250 36699402 36699457
    0x60e0d09050d030e131b031401051926060702010c08060108150405041e08040e13170904020418020315150a050702120a03020604150204060503010b0702010c08 70
    0x69410240c0103126206030880029000000c0f4400040122000c98280303032170030051000b900403102c5416020300c109030f036460007640603001441e0801c11121340c483c0c103a03203c0003485140d6040c0710340340c540010705403420401e240031400a42c44a03100c0040d0b60380948180c0e01401d2400341c06446040c0140e645044001a03507074003c1115030800402d103011a610300b00396020002e030601c000d81d01c500c2541d4980218040092a424400c680d810111100e800c00a02e070400d07013240d400900c1400007081489001842e5130345528907411041e540007107003a216130308201c0800c81a4010096294000340d08000215802100981503c0010107281c80940e0301d261900c0092640007507110464080c40241404051140781c0500b40e4001c031a6516040e81c40d241103000084101c040348400c219079010b10b06084080c10f07408102944224003c5150710480c0b1000425107049100b584100070000e0020b000600c24404204001c2c1040c41c01403604800014094546c0e4219902003c108032480b4205c2904a04192 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 36701902 1250 36700652 36700667
    0x403020a0605030406050702070509070f090503011a03060c0328150b0a0e010e0a060c0215040e1803030c0a0c03171006140403020f01051b030409060501030b0906010f0806030a060e0d 80
    0x7406e423000d4449140ba14006c5504100b001d000d20090040008030010041c0c4038603251001403c0c0240240002002d25a482c11342d11030b00070209009010710390000b10200040000c50b0f01a2a4880c44000026240c0800042d1208000c096492003501c4002caa010300d0300380761041c0b01030207a503011140d844000b820042c01c446400c2541c507050040c2d08905030340c6540c402100700c046404a042140d003000d000d20000755802011100d43c040758801003004510f01608981d01c61081854a1080074941900450740c5c0d540c0c08202c4c1e10581203081000309190582c070030018107610078403074100240f0842c2910f501045080c021030ba403c2c80741d1070a05007041099840740d4040c01f590b446d0b4170f680d49458116000b08a01d0981062020305000340050b1401c0d800c584007600e851401b8000742640d4031181c482d0010800707022903124460009040c00c201c000e40e49004103a0600850050b110305185001c4000196203101d001084540d240c002c1c25480c4001ca012170003a8403c084414015000c4200003040150900 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 36703152 1250 36701902 36701911
    0xc06021606080f010306050c0409110c010509030403170a09080118021507020102060a0b1903030c02040b0f10030518030403030c1509080d02030606090a030b040c0b090102120c030403020a060503040605 88
    0x180074103103d0300c0890342242c2810341360800800704980d945d640c4e45001ca80700d203621440205243c9144070025020480103030a260084000074860ba441c0c032607509559004500000d49484e882108910202d258180100610521400c01e46e08031070f56240014210350540842c1c41c1250b041c1800c190442c50410040d150740700c050385400341402e00c1500000e41d206d5008000314981669100405019524000903d1442c2071101802d03c0075512480c0c010210070500608a01a41c00d000180000c1d181c0030b001950030034030150114580d500d000508802410014000f004884680402c1540900003070004102035406074139202c0b800380c02c501e0180c0141b003600a06140192500e00d00c08009207018040b01c0301e10b100d00c44056100d4580c840017811500c03030042410380c00400020300000700710a83d411075110b0303402141c404c02c2c2d0039503c00d0300300018454100031600503045200b00c084203030504406840d10501d050120307401e064580d4040340a01e00e042d0040d201241d0301104110801649001d081c0d0310 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 36704402 1250 36703152 36703157
    0x1170d0906020d0e12030307021b03030301050f0108040201091a0a11031201030b09160e011401110d050d090212010608060c091e0303121006020f0604020d0605130c06021606 76
    0x81a2401c54029112600e4806210801800d8180c410305aa5120694164071759201d042c0c1f580e9091100c1d010395a00e0361220018030821f02d2003070110540c980401900d04803240541402d00b1390a580d00111484c2c0703000bd0089040c010001c002040e44084200d40c42d400c1e84000030940d5a81c24185000f40c44e200d6150310104103a80200004200d5800340110bc9045990100c0784944070340b00d80991500b801c54807408100e0000720b0010000d81801c1804e03070700b4102e55a03c0f0301c0f00c80d40603680c030044620240386005044254000e00b480f00207103105600510160201c070b600041c0701c9481d40d00080040840e00d04a00366691a9031040c02404400d01c00d09030441c00901a8a00e013060241c08a20b00b680c0b011004802c2854034844041140c9040c011071791000041c9200425500d841d0b40420f074025058018400140708486000200d030b031000074601d00642d00200b440b01594250303510680600307001051051040d08400018001600060440c40a000b0075000303041c4503101e024584170f40c500240c5c0407404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 36705652 1250 36704402 36704417
    0x30f051609050901030c0308130905090d030c020c010206070e040e0307060204050109050a03050606040f02070506160f030212191113060e0d0807200a030311060a061a0a021501170d 79
    0x103081b654803641200c0d0b100e8440d80d00c40c411502d010014900c5940a002d8150500017002001080031801010620940e00c003000b44d8140850201c0e620b80152b000c990142e4408804107911602a81040004001c01440031a841406100c410300310b4102040880d61a82c020a05108a6130003240e014090103040c1c441c0c00e060b901d19110150340e040060440c600036a92038014982d81c248036011950340c41e4000301110050300f001d5030040040c2250343c240100144164803e0034025100b4000c86101c205075030f40200690312804060048200500c46001b40346544084111001c440000a007a0a417414401c20704041e01c1c0040103008400c19000e80c40c40b600c101d406c0c0600160021081d1030402d41c0162050854042c1c0c46910300146c000ca41500381c0c0250714600c00010513a0001d0b41850380c00c0c00e00c00303440154449000005c29685c0c280591101c02d00302c1164403c4d4010341c20090114560b840c411210a0715032084040d060030421b030080031007941814080a140c4000700480541503800345003401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 36706902 1250 36705652 36705659
    0x20c190804060f0207030b010b030405010b0906210c0405040b011a0a080c0d0902030f0a050f01060302090f0a1425110c04180c0806040302151306020703030f051609050901 75
    0x185911890240e0b0b000d000310440e24610107442013110f68082e50780b1400c40045e55131100e0f207200841c0c0080354225115800c240c4104c0d824100075524a009807000340584d0140c00707072480c030002c2d00701030008812201c0c811940ca032201d9684030f0040030f00441c05400b0b465207550501c42c03c0341c0454200c4405401111003000340c0829198026a110b42c080c0800f403a5640f51005031610b03501030001003201030743c0340c411001e50300c1d1500c4001c1580c0700d000348203c044511b400e0300c030364100c0d0030f0702e100e803101950100c0b0f03d00000c2d11416001a0444d400301404c1f0001424006c4602c650102040039503055035010716501c80d00c007a00380488007499081c101401c19074075080729400400d0ba20044a80d20b140220b4482040141c0780c40c00e000244240e0360b0100c0c1d60000c032912065030a55a850440d800d030014130402e401d9090a504000555003d584440d80781400c5441e00e0715003002960200700c0440406548640c1080301076018400c0314040c130b454456030040340240c45401001a155078214520a418100042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 36708152 1250 36706902 36706913
    0x90d050706050a0e01060305030a0e0a120201030b1503010f0512061005210a05010b0108010b0421020105071406060111030a091202040209060d0b0405070903201210020c19 75
    0x11106240c0c42500800c00340d50f91609540601000b0040b6406582002da001c42000380220103011075509654645d11060806010450b50300c030181700b180003640d100c1c004d41000d5407081c0c0010740180000b0f4000c1c04114000c51a50b07080b6070090b408102d0007074152109104510b800c01d04130240f080c0c82002054142005040044a035801d4817405100c3c03140c5440d5a2000500c4990449080c1000d60544180400c503007002c50191119915290000714000f00100b00300d044041034800762901c0003d100c42ca10200c0101000d5207540d0841a41400424804c02001481165041d49981d01d8480648540d01f42100054414444a0701c02031320780e08148000800c00b6030004015084402d0701042001c58045400841e000344148007189403c4600080c80700800d0040b41c010a150341c809881c100001d40e0784000031a50305c1e6660000074031a4660607410310000b0200442c040c1d041c0401842448204518400c0038904182100081c07002a008211882d00c1d42c024002d8441407104000c401ca0320501d1035849 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 36709402 1250 36708152 36708157
    0x507030504050312060f0303070812010503010213031e080309030d050601050c0c090a14071d1806060c01060e180601080105070912030201060b0a09090506040b13020903010222030506090d05 83
    0x1003080b0000c0d4200003425551b9510b04074100e00c40040c003035075582c81490030020820348c0b101280b10354110800b0000540c0f42014404c542c0c001d2102207502030000d040da07031441040d480c011480401010b101c40c0803004207010400a600841203e80115a11410b12108034140c410040156062010600c80910500f001081c07006490004441d48801d44daa0b480c03800d00108102c0741c19070340d061400c2003000241030300100000c1d110b044e1084540d040d038881d801000583c4804142c03d02e244203e04011a01c0d41c01d0172000350644000d900c0000c205e0b00d8031510f10050503002168031401c0498110101600300b07000384a07081c00b41c05900001c0c801440e0040000c5d0011201c0e21611080703010340d0034001d05141c0300790f0000002c2c0081846060791402940d000400c001302138011200e1461801d00400c0e0310f0b2601e84284215500083c1c5a17180005040d1007500c0203411072130503c0c2c0c155400308206042d407803603039082ea0710a4903050502280c082c00c5060840c6441c1d8024400e0400b40c0c0024070005070903400906 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 36710652 1250 36709402 36709417
    0x10b0d080306060901140408060f33060d0906060914010b0315010207030c1404050106020309010806061b0a081308120706020a031803020d0e030307020f04020f0f070f0605070305040503 81
    0x3c0c0142d81d0860a8012143d08500103080410700300080b070007003034414002c540c035070140344803400da03004584034640c11802d03c0c4000411100305e6034000d2646030851001e6010000c0c0c2e080018040c0d807c1005140c40c0380c098840c5d20404844450b1f98500a118105e1a889080c0d4000ca030b8480048496040100c0501c20f88005420800341c00c80c6c13449041c01c282c0c07003002010003550344400303003090380c50760707050b0410382d062040c0b031032a00c6182000008225a40f00109540000405030b4426440d5180e500c203000890388400c021002030761561410500014080003841382e0f85205802081d80c80d8120807800c50142c3c40c9400c8181c03540c01002c402d503250562041a00d100c3c0f0380010005070b0740d43c000034080e0001d00d0043e806e82d401150b125610820325070041100f030340b41d000b562112854082103404241c3c8174452000029070200d0020148115820580d0180030b0202400d508586059501c10410b84a0b0700481000c9442c0e0101c10452000c100c510b018558100b94541402d0084d8140750f52019201c0c040c4c0038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 36711902 1250 36710652 36710659
    0x303040b04020a030804060507060f0b011b05010e0f06010515040510030209030118080304150606050d0e0c060408070602120a0e0915041b02190203060c0c10021803010b0d080306 78
    0x80c007140a556610904400540d4000701081e519a500d20020b481c542250380c3c00c1d503842e440c0107200380750300b01f9500401d503134603405a5843c43c440031001000301d03c8500e586000d4866658566a00740204070820121501c11304c5100100240c1d80b50104200130704104050000100c0c40030701c000c0140c0d07240da888a105969090502584509440c80442d006198a100c400d47c050400c011620511514000560299001d240c20080417810341e2108010349030036218020000d0301c2003000020345411640054242d2440c842564540c0c209180014401d4010350842d0141d5000150204403032034041101014030144a4078080c1025546100541560f00300d030b1100f8004c0a410000626420300c2089003030000200400c20040f070180a641c200400070a1010b800261103503400d000b00340080c15207401b50721070740140201a6a5280ca4007180d098002c0144000580700e4043c2c03141da241c01da03001030704420070407480c15001002d05408060943c3c840d264054080d00c0301c001c0d80e01c0444c83c943c0482e91300c540c0c140c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 36713152 1250 36711902 36711923
    0x2070f0b040807050603070516080301061b0b0703020702030f01060803031f06020c0105070f0b01090509010e1b0f030a0b0901051603051e07210905150c030703150e09010606020601080a05030304 85
    0x7e180030703503040c483e8800050041d0010b16907201000700b0034000c0e5044c1c3e8229644c200d2000950b00c2d050380703122404000617000080a40014440034480d80003081268409010b460951401a150509650031600b11341c0c01500003200b04542c0c4030f400004000104c20700c6c21104441881e000d0007075107442503882d0789030400100050450500c42c0720781c401c1140a0707000030458142d6a5505180c0000d00041d46c802c000741d42000340081e000c2c1e10000711040c20004808903040000c1d0325004000005001540e0b0a4050051030010070119600351200e40c402c14a10f00007048610300003c40404480c0b0300a582014140791100303100c0c007008001030701c0350600700849007034249855205c000e030341c40801801c5000300d070b520112045000b12550b4000d801518858021552284200012020340740e00444184509503030520020303c03518806d42240f10800c00307403100010502e842d0703030f140c485401c0102c40d00d5800340e4480d4420404a58100504c5004202c02d00c080c0c02d296a840d9034190b203078231010340050202d0108 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 36714402 1250 36713152 36713161
    0xa0b101416120305010614040323150903120a090b061302040f090b040b01090302011e050409090302010b15190806030c0409050a030909060506031315020a02070f0b040807050603 78
    0x49854540250350000c2c9001c02880e0b00000040c01381000b4060b0200042a40c40590001600502a036042d01d034480f55910b40f0758080c0d041d6001001518115404c240f10b8102c184108401000310140100c0014018640c1e500d200e14003050300c4000580090682894400303080301140080c0d0100f82c000c9022100040b00700c1e28180c0260281c040e40c0c02c01d1052200d001800100141c05910015420030192403e01c54490240d0056481032010b1001034041400c0da0900c4105500c0359484c240c50646c1c9040c071905180d100c1c405d500454400c0a012800b40c2e554540d410a0751034130014100000e50085140303032400e40800c3c10b21902c448824580e80912007454040703041036405005c041c0003028054810029015142420341d40c8005911040c2e02040740140f003c00c9901c414020041500da000d004d80b482d45d22101c0c000300303000b1820f0034155854604c1d81c02c00d07020208680014105031985600419070316042010401501c6203c3e071041c00800707420081000341d03510200f4160221001201c1d03903522a584d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 36715652 1250 36714402 36714427
    0x51b03161b03140a02012c0d0302150408030a0b030109050c060c010b0d050d08070804050c0f031906060501090806061c02060c030706051005041e1509060e0a0b1014 72
    0x482d402c02410310802d8500186200700000d80d40500c2c5000360b03248015841d0440845c130b01c40944101255040c40c15142c1c903035080c245404103500b05da11a1044690014031301804004115040e40c04898440d0300000b8001f000d1207900030b007072500b04120001c001c1401035a81d150b03034581c202e0b000c5274025907001c00d4a0094203801e62001628038000b4024170705021080c5042c60700c0d22101035103080450f25600c080f981d2540326254461280e84e02c40014901303580182c0800109040b050150fa13854031400c14141803232140f42101102140c0700d10001314515080500250400f0300c03680210030b5a520840801c0019560b068400070003c0120041800040310b6001050043c410600d90602c0362000203000360811403d0384c4414800c01c0901c034442070703850311403041205132640f80314600c6899080b440948001c214079400301c1c0000700401059403085684000c11000c1d181507500002110148000300300900819024010104d00d0481c0c40b41e55070030300e0313082c090440008003882c8041c05d80085480c405540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 36716902 1250 36715652 36715703
    0xe0616060f11030c031e0103030509010c150c020a060605010507080f0313051212010e0601051b10060e0405060a0e060a09020d06050a05040c05061c0b0604030210051b0316 75
    0x71061110705942e03191414404d8a030385c0c02500d00d5042600246044520b903020142d40d14181c0340d05a40301c62828109200440c4c500500300020384441080d80b03103604c01016035128540d01d01301c1c00c0c2c029044c41c0c40b080c24010b0031994240d201c40e051240c20004200003983c2a021103841c5000c007000a07440b0f4442040c00341807a41034800040c070038450000e00364003412511024100840000034041d0541c0e807182e100481c1100e040d501d007030100b20b050005807800c1216200201c11209960204c1f03d001d11080e5400341540c205910504442e40700100b4030007440420f110030b90384002094001d210351103c1d8040c1c0b07a500c0c08014400c03002580c0e40ca140c5400c6540c0c8502d0030a0403034001d0f505111a0810441540040000780c2e42110f580350500d00000301421f041d0180c86080000c220400c512030344c10309000001d81350010901740d00020800001c00144c0d116000c030344188a89540d02034a408412140c800103502440c4846803690043c80550369480380200c4840075030741d000b40e054905d91805040001e090 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 36718152 1250 36716902 36716921
    0xc050c190f0512030103050c03070e0f0a09150903110106030f15020d0603080307110d05041202030f0303070203090a140306060d0609152c070e0403021c0e010e0616060f 74
    0x203004500040200c1c03000e20f005181070740e01560503900c201c02403c0401d40e4403205481020411000c181c0010244485003800c41e038418103030300e0040340f400940e0f911024058212010401103e5580a4002c14181e0007643c1110540b0400001c016190464a400c182d04c0b0b8440b60040c040d42000f0101c0e800c61686805540740e29500440c01d00285031207241402280c0c1007100c1c40000140414003c0e41c0240380024080328042864440b02d08c2d0034145120981300f0b103c011800c0c0e070548950814091801010401540308888660107103403245891000c01c16085540c1e400301c0e44c0910740343c100308610365000c1030442c0c1040c0211000404c0071040e2400c1d1000c1c0c041c400b005400201c06001200440d292f54101000811801d407079000303852405160290086419642882c460303000400134010030398412201a005170007070046842881103100034420741000140c8800c005402000d040d55296000070381d02140d0041220b03001d04080d42c0310035894000d0006507000d08540d490729051020024a98002c1030034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 36719402 1250 36718152 36718163
    0x40b03040515040309030308060102010513141f050702060f040b0106030b040e10060905061203040905070e03030a020a02090606030103030f03110d11030f09010b06040b0a0302090a060c03030c050c190f 88
    0xf03103010304018004003000e11094020034890740000b440c1e5031040c402ca500c101f0300002c8000d0810010740304c002c3e0001d40380445074502e10071801c82c0f41c00e00d480c001441140d001030050100390351402842c02400c1010140062902510100500c070005403071050700c0d03064500e54980090840380c0080094040c0a880103003001d14001c201c1c10a9403d141508090160707076079540e0a01061701d402d800d01c07118002d2204400205d820921044c00741d00300c690001a00700000740f03002189200c03c440000d00315030001d0504005a880b4172900300071400e04031010b82e0b0200040364203a00710340c990344000d881450049948806c055807006a2408a120001555004480400c0030410311007000e0b140c1c90281e10035a11040d6409a020001e440036805008400f0302c210042c2100741418601540311020740c000f0f18070342d41856000d01842c0300540724582ca0b00014040b580e40c103892050306047c0a4100c84220221004104081060400d24180081c0540700c1c07038440312400c1c01c00c026500f031880c450324884100402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 36720652 1250 36719402 36719443
    0xc21010b0307170106020c06030406090b0112060606030b010e040e0a061b030e010207031b0c03080304060501090b010c0201020705010e01030e1606020709050105130504020d0203150a0c0e06040b030405 88
    0xa4041200028511642ca142c544035407000c540303014140100c809118540c01a404400b52440c0c0d03041c540302450300b041c4a400089440c040e40c4e5a02120f40320300341c100205407140903d40d1000d02102e4001d240080140d8142044601c0031400001d00c6580d042d111203000b95181d21020621700810801c0c2c0d003240360400c00803c00d104c8252241a600c900380080c1100080c1484e042e0075490006108445440303506442d000d038040d4255a0a24010035a01d005441c410a00328000020404040056202e5031042d440010f846d818103222038115152904c00074100076443c00100c1c01070360001118402c1c0c031400d003040204c05c802c41c00101c003d491400b800383c14501920151003c4021014044402d4600c90740907141a180c48e040d006045030424401d05034021130782c40500340070140780c2c0c0c81590030600191041c02d00c50076a8010900c1c1c01107010813003070506055420010144564802e07403416042500e8482901c0310064001441c0d40214001e14004840000c082801c1020810030880d00c076005140550 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 36721902 1250 36720652 36720659
    0x70f0f030221130303080720030712080f010314030f0c160b0705060f0a020c010e07050a080c090a0e010e07030308040210030e0d0c0314041403010e06010602060c2101 73
    0x2915106598034502e51100412100e0300d006600c0d00c2500c241d400c51501c0c10003400c4c6103450494000d2000343c0702c58140032000c0e0000190252013442d511720103064000455582c40e041c0382046480741800210000c0112050501800100090403641100d4100c50309501c0320380a0840d040c103510410110340501e40b80041c112044000101700705034206d0543e00316080b40c40d031b40c0a0040080c0714032040206540c01400014407618080144580c000507413036001810110b4900c50703d82112500e49aa80c1e403913100d05020080ca1500b4404c0a016001000150074007441c0140810f608460140841c07454a071645402e0140181c2540017000d200c8040e000c4500055890030050108441900e050f406085c9000f020b070040e43c0203004041c250302c5079100500c03000407500408c84620440410846c20000c07464500c002c2c0c0e60000000d44040c050340c82001c0c10703110070001091308480901012441036002540108107131600800d01d25401005000c2881c0c0e074010603078541031040c45024411100608600010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 36723152 1250 36721902 36721907
    0xa02090d0b060406060512010909050703170c12160f0807050a120809030901080c0904061a2109191a0106080a140621101a03070b0406090506070f0f03 66
    0x1076004400c20f0300d040010030740741c41c0216420721402e031400c50b0f800b40340320041000001c0303548200b4140b800354060794103080e201d0795401d0300039102e140c0f82d107071842000c02c3d0000501401d00180715000380c00d85815241c0404120200c010240c3c1e0103015111002804c0805e0030f00c5290011030301d540380e1140589070841c00da8500780d0b40385000c1039010800502c1c4900000d4888400004a81614605031101e0302d09542e5006400c0b1640d004c404441d810645442c000223100d2448c03400050304103110305e12a44c50701515828051038041c0724151088101580e820b00461240104480b481ea02079403643c5401803586040803842900b079201c0d80780e1244070030307000060348961007007a80d0700a003e40702d4148280c81140400000840084c2c55003a03120100c2052031320411001c0170020058040e007800c1d114045050700300301c0222400300854030b030051184000001c030352809101d0074024151101080d410315041c40c0d070041c030503502409141e00540700003400d0320034003c44000c17404d03030503600070401d408450345803500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 36724402 1250 36723152 36723173
    0x271f050a0e060a03140f09150702011409010506010f08010b040b03250503010906050607020a06050a0201140c0a11070b0702040f0b030303040615120f020f150301080a050c01080402030a0b0a02090d 86
    0x24500c545d0000080350740500c803100f01d82d02444646009098804c00c2078105038020201031f0040b01959a1001038100c00001804410f2081031b000c0000141403401c0c01c005130101100a400c40204200400140311202441c0192410303030704064200c0b501d9031b5649040d0800c002c003c0c2d1381583d0362244550f4aa0146a1110041d8180c401d8418288000c69072141803014500940300020b5202c0f41c40d0f8000d11805201e01e0182c20b02d80d500d032001141303003490002e4251060506889030301e07038520001244030001d60004a10700d107040103a00144603007403800030707030404902840e00c0082c4104e4031505000d425006a03000008681d80007030650ba52030501d0f14104004084644611a40381318028002030610500749910b880c00e03411030001d51035400d096080281000540302800da00049517421603c19512000145000e420414001c0030491902d040407803038080d603c01014100010700003000010f0302d0105890b90303907a40c44500c1c1e52442c1c031481084400b03030143e0b80c9055000420440c54000340800c0c20318 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 36725652 1250 36724402 36724421
    0x10c02070902070f06051504151703040609120f060e0309040b0603100603091a04080a0905030a240e0d02010207020a050d081c090206271f050a0e060a03 67
    0x8030303160180e9611071402a4024060003030311010300c101100e00800d07000d40019510508005030029407129060000d003c0f101c0211000003960f000c41750500480c8951001210250809001141030910b001310040c041e02050094181c129040310104013040104ea000b806510b03800001404611282200d00b540d9800a1800d140f00d541022030003550b82c01c12000310b90240c40c41c095041400c0e42072580030390184c0b01100084542e508480240e541d22144072109600892280424594440040701e000385618aa80c110324841e4000010308400210041d011600001c002000c50038002c0981c4d075143c0041042d0410400309000e10078944e405140d0641c0144a41842140c11443c04c0c3d840c0c80500103090800303200207244400c1040314107035000c2c0d07500d42c0d2031a07044858008601540c15602003007154000710031002500003006207142001d6070f11040721041000a40704040700200c41460b0101600f1034240e0081841b000107003c0d9401c9225000394149040c1c007800d125590482100000d005080d07081c2d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 36726902 1250 36725652 36725657
    0x9070807080601092301020709020304032c030307110301020903010507050c010c0806032808070c031e0b0601050306181608060d0503120a020d2307020a0201120e0a0503030108010c 79
    0x780001c082d0b6014407000404d8a82d941c9039907030483c620b090703201c2e8090540c1540605520604c1d8000070034000f240000e43c4600e1090380c030225103090501c131520f0361402e1106813140140b40c48100444030744000098480701c81d0400c110102c000c1001010078028490034100c90740550801041000700b5403c5401809015a40380c02003203620340d400c0301160000344c181c0340b0f1075241e0440028000008164501682c801e40b000e110480d030400180d40e0352407668483c080807500058400410024400300e14182090701c40000e42c06810304113281e803849a0207030010f107220306204002c0027043e0f0075100c0303841c3c00040c0d280040e40d4481740d0070702c010b003050b4a02411031618005514200094414203051141c1c5280030b41c8600203505040301d0342d0201c1901d0f5001440070705010b9083c054103011055501032004101c0407503000030382850b1101c01340e40042d8002041c50b0305541c0029100c00c0140d03842105401d90000c1200c00240d20310000c0c80c1581007810b0360700040c08901c0084004200301c10194020345100d50790380c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 36728152 1250 36726902 36726917
    0x203070905030d0f021b18070f031a01020c0d11030304060206100503010c0206010e0a0b1003021e09010e0607050f01020a350c0307030908040f050405011e03031b0209070807 76
    0x103010403034044c41000f11580040e0001000b110818000c555080e094980083c0101022144907400030110b61045884400080c100c04103c0452605031142ca40800307907131511071584582e01c0c00040c1d9500c0400210358000c4464406880c184101c1c40c848401e0054020180d0351344541e00e4500039074a49065960301c503841d400140004a130326052240340100d18594000d0185a031a00482d01d0710074000400213125645c80b110020300350340c0e8600ae90002e00c0e14544005845800c003c1030081200b00d018500241403400700041140c5a030841e44c2d500701c0310340898900356550028075015041101d0b040e5951455030004c81c8004800da0846003820341c0c0030161171030310b020b150307802c484a00d0545100a001020b41c440e0f004100ca18010200a5521410303904011900607850354030303443e1641c80f660200344c03000c1c0f07090414401c5140c41d00906004000c5400541080101400701030680d65081c480101070140c4112100039801d2264906c000c82500245112100d280c000406850340d0001c880707410008645 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 36729402 1250 36728152 36728173
    0x1306031803020601050904051c0f110c090105060a0201020c0304060302040302030f03040e060f0f09010e1501021f09020a0902040e060906010f020705091b13050a0602120906030606070501020307090503 88
    0x150400c04400c2078056004120a9180c0000d00c02c001d00c015109598501400300f41189480754240712240f000402d94400e1250742141800400111101159064a81001d8040c01d80d99480000c040e065607030031030700242c0e039580c6010185d00920406031400614007000c60001980d80d090b030b001c1c2044a000380d00f51001078110b0b60016031244164001c85541007840f40100b092418840048004624050154130048044200140c3c12071001d900401c040c3c4454800c100d40c04508145100f052002070004100d1050104a1000e91100480380d44801075590045030041d569100c24860040004410444d611a00c84080700e8002c038044814502a034040b8000c00c3c85944585143c030310002d07a0750701a008003801c0401300141b907040036044d2070030ba80c00c1e00050303403803050440e0041c01c8464002ca0080e400920300420300045c586c0340d502c40d90664114003103081d517a00e4100c0441d105400103e03a40c0d40e403950340b240090804d0188560203081580301000308890950801e40c0b0f001a00c1e400c900701d50f44151b0707 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 36730652 1250 36729402 36729431
    0xa090c080f0a11120105090d020712050604020d1e0507030b010e010b03270115050406050a0f0611070f08010507030b040203060a03110d051603030f090308160501060b130603 76
    0xa03000d180e080c0326400507202c24041207540c00510f802860081501c11110501100942034170010740ba1104682c1110b01c0d0b8281142c1c04002e80700050152204414038619240ca60940b02c100040000c2e0152400c0400c2100b00328074004562520a504007101755402200d003482a510a61130104650115408e00042240500038903501c0c100c41181a0640c40c507620340200701031441443c90026a40d100d183d0400e10350704000c3c0a4001e4902102114042c0c0318a854100b0080e100c0c10341c440c43c010a000c020a2020341c01d80c3d8040403c4e22003a081400039291200720140ca414101c2e40000e0000c8650b0001188061040d0000303400390544c4c4d9000c4c050851604100302c100d12090320344079070010040d5020030005198502c002c0211100424507a41d09a41d91100e500b0581c0075201020310815000d001d00030140c01804070139002c0741c28036044c030429045607956992481050400d501500d6400c24a604001c002d42090f0007500e941070149443d59541c0c103844401007020b00420f0007180c03c00b03810081140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 36731902 1250 36730652 36730663
    0x503010f2103050702010201060b030109090c0902030c070305030405071e0e0a0e0304060c05010f110903070602010e030322060908030612030903060f18070e011404050f0f06010203040e0a090c08 85
    0x44000780c00924000d031035a020b44030760784411405ca040d035490341000a03407202034501850081c020418046120b803102c1c80c003e4080c041c0c640001d03100503c14014030203d00b02c072000303888122f40e060401e541c0d26205d504000b860703c01d103981b08020840740c0c01d083c0714840105070404005c881880039050b445803108000707582918103a070840c001c40d502c03e2008000c4c1c2c5124526030900c00d40264000119580341d00c140505079000000d0b01c0e02d4401c8001030035056030404100c1c20b0020131242c8002c000f0749546000b450b0301c81c8805440c1002103121400d07030701e0402d02059104120f15501060410101b0401d150cc140140c20480d940c40c0b00d0304072010144045480881100d011880040103841c2c1ca5403070b12107601c511032000d00402072041c00b10700c0d40d50b800c0e5002c02030300c0c0113010301c140c08000d45e43c982141090348030101c90303c01d40228100014881d9940d031071040071b50440395100840b482d50b50364900403803540c0187d600800d5800d0510b01401041d040039400141040c1c0070304890304007682c0303469050f640d40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 36733152 1250 36731902 36731939
    0x150e0f01120f020405030a05070f06020303190209060c0312010e1308031f03020a06030e0c0d0b0402090601051c050103050c0306040305120903090a06020607110d120506060d06060503010f 82
    0x60607007003a40d503180010b51004030803410b1503000500341600d86011900d81200c9410895640c0d004032402c1c00000325005100000301210b2009500c0c500e004107116a15882442203582c80f182c010503070100603640c45064440c4c0d004000e040300d4840c0c0804401c04001c40c400e2040040b144030750030100f0441c170310b0360b603040c02f40540003445285541c84104510b503044409800c404420344447c90b002c401a650a08100020a000e55002c2802c1c601452118248104d001ca00c40c480e0b0750050554000580398000136600c070f90102c03a07910480d5910310050303595208400c0540325010b00c0110988051825500107411f07070740550125020a840d0005041e511030042d10301801080c001e03c02e42d40c0030f0041c0f0f020746521001c20000c2e282014020004174a80342019000131016030007040c02c005a20358000b03154544240c1c55001000b000403803803400b51180b403800940c50707203168883c0e0000f0420f40342d040c211a10b203c6007203010030299070ba0f524003d0040d0801c4c0030300d25195100f000000344003904c1e0444003605 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 36734402 1250 36733152 36733157
    0x509040b030622060905030408060711030405010903020103150308040b0c06061504052e030c080a060311010302130e01260114070804020d0c060201060f12050606090405100501150e0f01 81
    0xc2c0850841d140100c0d52490301180c1c4c8a40360380341c0d003002502c1807001d40001c1003664010151030030424400380020044041d024101d601c20710041049a0380a6160000c498081c240018000c3e1030f1200601108060b40015040309000580000c1040c024401040740711640815209a91549801c000482c0000c044404a4800c00c2c0301c103209030302d82122644405400e6143d8045140400320700b6078880d0104484240c082941c0c2d407a1441502e41000820350b02007100101040307414155070304c1140710519480000d041540c080b0727401103418000380811010b0040d10072100302035a5507001000e030203000d030b05201031000c0b140100c1207015101409a0248031844001d5022180e0320f0b00411100c00b100200266485082c01d24104007140c01e03030081c01c0213080340c0c0e800032661504101c119102c3c0100f40c1d00c0825070b0605805c4c90804103402107005900006c0c111010900b98481d401c1c207071b29080d600303600d41443d14a000000038402c080303076100e0705441146484032030f0301d40c0c02c0200f00031801c03540c0c4c00780601 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 36735652 1250 36734402 36734431
    0x30207050a1a030610120c0801031118040b071202181503010305190f020d0308060108010803180616081c05060409030c0605100801090516080c060d020705030d0c0509040b0306 77
    0xd181c00080980d690b941840e0404180240081b00c10030b40d52800341d540080364180005000744444505015107402040c0c0f1030283d211a8642c10043d0100001d1010341a00750b01d1011511903840764444469690010b4019922158148821444400000285840348154144200c0180c044a003564100da4004014154881c2002c010348524103d50b802221481011034505005a945a1300790301079500950314418146001c2001600c90401070300002c00a61007401011400168801000c90104064951503260140e8424032510030700c02400c0100300c602d012a5204048105202030340d21400c20380c5080c81384d5240d072001d02089520040001d000540d88803609004255990031441e00001144070411000350f03035014941c21034030740150442d069007202001c040d102c8404a41c000c09841d140c0702030541110300400144031489041e040c83c2c204e41e0007065010600400740191007441040382c42c1480300200d007800c010b01c142d20010b180352040707141451580040c01d001500790701c2640d02522200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 36736902 1250 36735652 36735661
    0x5010e01081204030f05012003090106050306190902150304050f070b04060f1b05010e011a09070f140403081303032d1815051b06190e1504030207050a1a03 68
    0x10040d2170710541c203441d50f40d00e0f81c040c0031450780e007481c00b101ca400e071084003c0c3d1241020340650382580c8042e845644039030f0080d070600c41c408000a18801450500440000300701149201142910007901000344180304040104014024082440140400018213a4400d0b607140c1c0c2d11490b81d8040d5001c2e00000071686c202d000f00c1180548581980000c0c0c40752030b0002d155841c0c0e00c550135070710000c082032010394554520038801d9252045164041404442400043c6071407800104003034034030311420041250b1600c1701802c1009900403200950740090b0025030b18010f03495022141c04941c031086000902c1190300210408105210100020440c3c1070004d6003c800082141c0100314010b1403164402065000980700110164005051480703441e03103034a6007a041c0203d10455040610740090307402c040304014540c00c2e6a107481c48100030ba00d0b00007484100c80f41c04c4074580900b044e1200100c9110b0030510060540005012048030001c80d005070209454400c0c44031a60110140c40032002d10038000304 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 36738152 1250 36736902 36736913
    0x2010f09030308180309030703050706090501090302060904050c07060504060c0f020303070f03020a03060f08210a050a0318140f071d130215040909021905061902010e1005010e0108120403 82
    0x6180324841e81c1c01700c0c1d00b40b01000d0f0009041201c1740d84229959400315508014290700030180b94001d0100f401e04101c0b040c90741d004100c1910801f01682d1140780d441b800103981c01010015500410740140c820000e602d414a0b060008103c0140340328046044c0300c8064600380e20010459205079202e03a00d56000c0046010150065004440c1d01c1050680714003011031050b8038044a4001411400f004154075130f904010100c40c5413810608074811101000001c1c0c0403500441120988042403400044c0e26680544040310b010040314010117000c0c1070105074000c0b0600084403194100c1c10015100c3c0c55a40c0c0300d0f00d40d41042080304c41d03201310910000241000c6000b1007a8440703c0d001525074400ca11106101d6200c1d607109401031450140d503800c40c1c02c154101760005060141c80100206400e5003010001403442c05054022030803440d04010603102a0b100f90040480d0b00c415108980440c0b400d110101c000d403000b4025403401541d403000000d0a0f03a4009120011040712244840c90281144c0b1b48 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 36739402 1250 36738152 36738181
    0x100509030d0e0312060102010216110a09020712020c0109081b030a050607050705070501090608040615050a08030d051026010e03032401030504170a090b030405060402010f09030308 79
    0x5160950005001004074900c4034050502071031414000b4590700c01c100002420000c5000d06401d04680c814090a172006000c4804540e840341c00c00d00c5c20741080d0b803440008100e0307459600800b4101c0c0c00401d5442c100480540380d4a9201010b400b07071080450101c1c0110f0390300415106035046030780400003901c1e1035500755401c1031050201406960f4441c2854440a2034444290780010005400041c28024083c0511201025010174640305500500d0410300a040c0d00c1c0291000e0f2403250303249070048400206003c070900a0101902c3d951410f569504044c1d202e030002c0d005040c242d42800005000a0710864882d015940b0001c44800a4070303e042601c1e40701180d03014150099940d64034040c06282c0200301942c80380701311002c0c110040c1044034045400c0142504002d05043c18141031000043d0101103010394225030385410fa032580d202d010205d4411031194400c0c0c001c00400414407051041c04035a05226074002e07240e00b0009041001c1c12070315192588030203000035100c000810700b1203201042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 36740652 1250 36739402 36739411
    0x100b092a071e0b0103050d0f02060105120a0501050a0b04060f0f030303020307090905090d17090709020c0c0603011205060906280b12100605030304080307020d02030a15020702040b0f031005 83
    0x31851044000301e14840400060310006684440d000f800420030000d0410210032052014607200c0c203000080000130f03540365418001e40c1d10070840c0c101d000c807090a0400000280316080b01c0248142d041010300b00c40180030a80c40c0303601a5050020210b200c1072151301c850111742002545640c4a49151800c400a400c050035040c10000850300002d46401603001d4540101c0b0f514015004c02e01715508054601c0c40105c0f014061402c00004001c003440c004101541128014100580d075a02070070962424856040030072030b07101c00b02100104280100c04070750b6007194840c508a480e6a00ca5014255580404641c2c001c00300c840000074003095200c02d8120701028106120114070911240002a2144540135060500e50b1206000000e07405960103210010013056020b54642030800700351a4484c0b0403c10041c0c01042e94281400454034100405600d6603080f2540c0000001032804110295011030010383c8070fa410510b5030003081c64041e03003100380300c0001401401d181d003171174a40c0d0000d440000c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 36741902 1250 36740652 36740663
    0x40504020a0806071d0109050f09040c090606020a0c05010e060f09030c040e0109020a0501090807030303110c0f0a03080907050904020415031202030a1404050307180e100b092a07 78
    0x400004482ea01004094012841502e412644078031103482020040309445020b070400c04139450400254603000c900c2d40c90389070241c0311003003a83d03103501389464000d02c5544020540b40c134010000a10300d40c0454980f0035148074441e031180d25641d46004488640689400035071118040092940c081030300b100030414914080d02740e5012803c001c1c0000c04070740410741014140d0b5101c5102c03030218900841481e0240c03c00b401d140607514248140903690b04410b0000805250340c403001121001c07454000c0d154955a4441140d4521548000752903d5608990084004c50040e801245e040c0d40086120010350700007619a10203503440d03400b003101800f072905d15a41c40310413410000c4089440c0c01a0f0910f0444540c00442c1d0b43d040307130900189a280020201c60000805000600560380e0104002e01240c1c24422800044190f103841440109450007094016100b035103400d01c000c1c8443d41280340008011a516034a07541e076401082844408052202d08803104440303c0760845d009040500100d50280 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 36743152 1250 36741902 36741919
    0x140603070e04060308090906030f1902030a1704030309090606050a0e120703060218030a120509180a0915090201090303030c120f02030a05010b0f07120c082b0b03060604050402 77
    0x704041000c42c0d00c030b9042515031040001d1480401c0c286114000c0e00000c041e001480d81c182c01000301c0f40c60f00000d140b2081d20380104050340d002d42d40e041000c1814183c01c083d049020410030303045a28260b02c20301c0220003185802c1c500060382501c9106003001c950340c1e81c03521482c00c041c070001102e850844003001036111110030051080c0c0030040100d0005184100e9006a840210b406945c07071081c80303101d0007031180d80030702410800904805c29600c0045081e0600907220a8450000356021000c26580c0c0d10490114041020440054015409182c06501c0820800d031440e4507042c195011800c010303010444035802040000c4c4030380d001c80301c0f01900d40b608031000a000c007104820b0b00c190280140b81c0c56008828443c15003060305c42c07a401030030072081c03151900641c003100030250700078010041c06044a82c0220501c2a005500c0e50384980c2d80b0034409030303543c1d0400320500c41801b8003c60541a6180c0842c02003880e00c0244039102c02a10700400810040da10030742004060100104126000000c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 36744402 1250 36743152 36743177
    0x1101120603150911040b0102031c060302030607030b010f140901110f070315140402150705100905010e0d020c0d11040e150a0f0506150702150a0e1914060307 69
    0x703500c42c0e0302c12500744030000300d04501c040c10080d0203507583d50700d0035200307a18042140701a607070008221032120890786486104881c6130306681c00200143d0384060b425020b91402c105080313900d84d00004961720b090701c41700c0102da040081194146900954a01364520030003010300590300542d400c0b20114050011600c51030030311110b550800c552a401203441c580504842c5101469034003400e0840d083d00c0940d400f03580b900b9000034441640e40b000c51a0042d200050740000d006041c4040300d14224202c0c2c0034402c0a01c6850124020036600500e90990702401c821881094030100700d209903444020305030b0580c00301b50380320500f611031182146d0340c0c440d03a42c40307001554110500c0055018402d11510b10000e00d80781080c0c07800c0d0356000000007922840e00c0d080090310395410280301100821000c43c2a1500018808034a101e06044088000b4200c0852542e9007943d20804030b0103c0101078504081d000311340700001c03580c407545020b8140300e10411903203112541001da0107140d2011807450421a403108 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 36745652 1250 36744402 36744413
    0x61c0906060b1b0f1f0b090403050c010c0305060303091002150403020610060903050d05030408130f090b06030405060103030e01020715030501060912030c0204200d090b131101120603 80
    0x8039910032500c0c244040b581c415600306020035081c11103215800362005000102d207071600c4404881c0da00d140400017802540c601102030b4040f0590010141031143d2a043c5800d004d041600503030700b141403a43c01c02030031902080c4240951802810090015400c0c8544941000742c103103c020043e504510411800707140444800742c206010380d0194000c3d00c501d01f00b40c00c030b07690f101d005600a0400d0003140f040030030014800042540d880445454595140d845c1e80c602062a8400e0007494900c113410141c012500032102090001100c8100c00c041202040c400240324943c04201e9001c1d14940110b4010804a401b55920080202051050307840712500d4081240042c40d4400002000a030b4400c0144000b54004a5110141404000050554000c0d0341c1c02020110401d000901440d203406260408000e10410642c044a1803440b803615041400b4401c0b0081580c0d100079180041000301085018030807511956165800c501851084c000c034100545000c0800c0011112440c2c0c2c0d40000004282d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 36746902 1250 36745652 36745661
    0x9030204020d0905030d0b0102060702060108060106051c0911010206130309030213060b0304030306032009041b0803040303080405060a090503070602160b040b04151a040902060405030703150e0303010302061c0906 93
    0x346d0704800150311000e00c3c00092901d44000c4c10101558000e50060115034070018055045035000e2801542c0c683e102d00892041e07506500183d0720305403c000c884010842c403850020a245403e9007200e136903a54049650b4014260342c03802801044410030300340003504101c1d400498100c0d1020340841c200d07948071011001584100c6098001a0b03646106008000d0300d0360410404000d00e003203055180b802d440004030480f9026000806441d8130344640711100f022003400b0001060040262501c1e0760b5607045c058814803049070101e0f07090040f00000755081c4500e10807039913480c1e0070000442c2030829580e40d840081d0720101d104c4d00c2c10301c2440321810004400003911031140380300e4003035100c10b41458500512001094040c0c055054100b03981d081a0001ca41041c03010710307008490110304a40240081580f80c45281c1100b50540500e10012084c802400b0341d0380310000003c0420800d13110040e126030f449000c03c0c0030003980724a040092122142c0448541158074481080018490303050b030b9034107000c03030303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 36748152 1250 36746902 36746917
    0x32a072601050601050301030206090906030a140d0306080f0715020309090a0c020d020f0303221205130b0c030405010f120c080a0b060705120a050712030b0f030307020109030204020d090503 83
    0x9001046020a41800c00c0c00b40d0ba80180080c204a800c41d411580000c501e40200b068160095143c0c80c005500c954080000046658008440d08548074002c2c810a03202e40b08114000c010a0070560009a001000603800c004603030100082c100482c205002d498074950303500b6101c001c610092102001954034149814081c441d00d0300001001e010071403000e81803c109201c6082590000c40b222200800c0200450303500040e1111600c0c02000a1701044021100022015009036041d0951072050358200c40282510000c495128010a540f14441207884c0301d1103507284080e400510080000b54040c00d0380d84034a00b03050404d8482110003407a00000c440341c2542d0750340050300c29001e01840c4007003842612200c25080d9801460080981c444a58500c10614041c050038170018042000a00ca88140e584d460352045014440c00103c8400501411001000d0361050701c003850030f2402482d0004c100c1d0882941078603442c02591640d02000001d4000701c1400320743c60b454000880c0000c00500044c20030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 36749402 1250 36748152 36748199
    0x30d091406011805010e040b010e0603010f0203040807210203070605131515140306010b0d02070506071107050406210303060f030501050109061703030c07020103060e0c07060509032a07 81
    0x8006a800c100f001d803071060344140301150314001800049195450307040d040d518003103c0c0c080b2940703600700401c0c01401e00042c050120b500c04801e04c010800c09400614940d40501c030520009902c034414491400610621701000d03030310420a0500182c090b40111742e10900b03407804010b0603d200e88603c0400c0141151070301d441c43d034a401440c4181c141184001c0540600d402a6202007103640200c3e5032100180901c5603a0b407404034184480444507011145c00c60307841010340700d4a040100e0089e002c0c108035250001c060160340b402183da0304103849840e048400915403104a01126110700a112620490580405071200804220400c0c1c800042c4d0040d481000001010361500413034ac421519103800103550b1a4000860b0140c0d26070000550382c20010110071243d413a0514401a00241101e500124692113103004001c0c0d1304201602904003180074100a000380d54035240115128490492a1514203000c1040301d00c6102c0d28901c0d0090310070b20003045a09807a15620b0b54501040003410041d034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 36750652 1250 36749402 36749429
    0x50306220f050d03060e070f0309022404060201060504020f0d09020a0e07170a0605010503191404080301050102011a01081b12150a0e15010c021306060206100e0405030d09140601 78
    0x60f2250f1502c20b032802450155100016814901e2004180e0036041189004058036850200d0965441140c00d9080120850414070540d01e004c80102480d00540704810141d464000000f0346801e1500880b41507440e410480380c0345c40303084884140104240081030b42c01800c104c602041648170503100900031403145d2101181c070003a03c03102c8400300e0b90080c125000d4906140c1d0800113a60040103903504141241010000c851129000701c0003401200e070162407480400040c00240541b100c001c0d410794000703034000c1c8170b055002000000e88050401010740003601c00d00001e00461410804a8003d912140c0c08a140511041040ba007000042e2045074100690311600285494104400d1f0014081d10140c441b0b280381070303641480e1841400158905000f0100110405c41d5200c15500090b41d08a030000c104950322544025502e03a41101c48044071000c0d41d4000c42c0016031aa034841c8940c0c0d00c800118500031301d4000d220b0280074107a0044641a18881d00b510030602c1c2071051a01904c6418130450 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 36751902 1250 36750652 36750673
    0x2010f0b03070308030403111c0302090406090e0c010503060339090906130c151206080102070b011502071a030901051006020c01110304081006030c0501050301050306220f05 76
    0x8603488000114032a900c041001c000041800090303a078810b4050503c80358260204000c2414030700212846480d1041d0649200c903069003681c00380101000540702001140c0d1603c4503101214082c0817010101e600c102e040110562040c40219804071014040ea50015215040c070186400111200d82c2c0c0c52441c21801003079002d22440440d809641144c0800c65400c10000031a180c1030041d0100c50204294680d204c01c1c03194022490004140d03684525010000b4500010034051a25140c110700500300794000403000c40500a66891a4221100c02eaa9034685540314902000410402055008030300c1d0002c0e503611a008072140d070107100709a455603031800700001e90031180000d00b07200c80c00300818400d21501c1d50019494091101c00e080c5600a84004e4403210715501503907001ca00e17070303100b4111f100c00e01c9a900d0b081481142d02c00c2401e0002240c8890056805001c24041d454155000100044208101c40481312041c031000c0e65121815015854520030241c803c0c009413400d510000040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 36753152 1250 36751902 36751931
    0x110d0504051618050604091505040503040302090103080306010809010605030c010516060c080403020c0a0e0c0702010c060c0e010909020316050310030206030c030405060a0506030c011101020405040603060b011706060d0905010209100201 103
    0x4541c0108100c904001011007507036600235811500410284256540c00020b08200b0100101c0f0040d680042c9400207a60350317450704584076070044800b98000307500c9401040c003001050241c0301c29140c00a000d05102c01248004495980102d50b1080004001c2e9003035001140452103008e0b4054000c1d0b803402042d01e0641401380c60b200b450500e05009a18040003000101c0e580d049040d080000c1715230340b507030f0707071105000480300c1c954044009081145040d52200030300f5040701d608543d03a0000e8036000d540541d6004105c0890004440c002011803400e1240319045c0d10502c0250b038016003000325044030039140c1d00030401035041100e001c004501d00105000600104015003544140403642c148000d1a081010942341d115140368503052004c0301000400c050000c0d01078401602c3c0160080065a60340c1c01c1140140041c52980b44c04180704840540100c00d4609030076200d040060212032900384140107410040c2020102928195070030711495040d5038511004000b05c11095001285907080791050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 36754402 1250 36753152 36753161
    0xc010203040308130c03032d02070501180f0b03040201090b070c0512010c0207090b0303040e090a061506050403200d1a06030f060c030907030b04120206010504110d0504051618 77
    0x989004031041d50389040001c402204500569074946824001c4a06813400f00d0994580d407a5084907421400c00c10008c610f5001403020304454090b610642e00a00c0c441c100100c4010300c0c019050b030f908a8541c24403124640d07100070340c0c00c1441854152403035650780550f080c503900f0801c8203c0b0908a5110200007034a4401002c0325440c2d4a40001c00c4040d030303003c05c007a50300d44031440390488081d2a0207805a1650b02401a20020300ea40e03502d514051400303500803500d646a444088914a142040325070201d050403944a054a04545800b4503041c110748034030011141055200d600c1018601d40c0c0500e640b035183c1604c9081d44a84c42100034a1003840404842c8036001f01898083c0c3d10110000030f403442c0024685800c8003003100a1650783c0c0300c400c0013508001041e0030240c50b0208580a203c100481c00b1030340c01300000745500b034a195980316002c120903100e40000d03d00312040c3c01c1c080409021043e90000c1e070041d07c0341044603a0301040825101d02c03561a54022804460503c0b06c1010b501c015004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 36755652 1250 36754402 36754411
    0x3050616030c1d0a0b0a020a170c0607080c040306020c03071203020309070302060306040f0c0518010306060f050307030e061501030e0c06071b08060a060302030c0306010303050d0f0209060c010203040308 89
    0x40502c0380000d018002011104202540c0c4180010b11009601940b13410141c100508522032403540e480203c4400a9901c05d0151002c646040c8022043e1a500181000f80e441c403e18910140c441c0c1e0700d41d10f41c01c0b44d1a1001401110307510208000000010360036200815901c00200c000d1526643c060900003802e185507100a01814010810040096004560b59054940c111141500c80d2586804540144207003174034080f42520b444d07501c070400340e0440c0c0a8548000f111080a10060103100110181c0701180302d0800442d0714081c55002150240e0080c4d0f501100502e400162000b200300394900c0c04205941200f00a00c80d0141500e555a050241c01c0b01f2480031401003012114260100b2424829600d011b00b04401107400c50301c18402c4c0e1490000186402e604580c3c0c00c0c141400743d18005e280c5840202d2092080c80713116496800c2c04030701281241d4043d101c2905082c070f00765090014040c1811040b00240c0d0800078080196111000f61910aa90100050300d0f8606071074058610b1202a1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 36756902 1250 36755652 36755657
    0x30403050f0c0d110c150901050a05040e090724020c010e0d020a03080c07080601080c0d0302070306090303150501020c1f1107030b0106030c020f030f0d0f0905150c090603041103070503030403050616 87
    0x10710758109006d0000710307080201b080c030b840703980c44040340011103103405103400c980612100c08040c41000c0c0000941c8405a44014241e25580a0345e81e40304403c0f00c2058240d4005608094580f14096000d2035420101d000090013507800c1641d280d0001e0845a0301e900100c91481001c60358501c0c030b200c00c02200c1c02401e9020014038807541054034a41c0d80c3c40e0780074007003403107080c034440e503102007510074000d50000b594454028041060b89203000f40c060501d2694060103038500d0384000945600c0000c58484000c2c0c003414000032030386581102015040c40840c0181441043d004050b12a101006072a0055000e540000c042d0f5042081c014243c824000784181154000e400c6000f01c01000300881c1c08803040d903540c1540e0780401c0455003000d010b01c0c0403040e080364980840a01030000c007148040090324806089038440c1c0d100c0d80100080d00520078a82d811603010310000d00081c00b21400024117001c01002ca030f0f4165607900000349146d000c2d80040756142c00060500146084641080303282c03002c0e03030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 36758152 1250 36756902 36756919
    0xa05041506030c05060a090b04141f081503010b030f010902030708070b030106030c121107020a08191103030403050604030203040303110303060d0b19020c0d08011703030403050f0c0d110c 82
    0x5883c1c1030b83c0385007240140341c45a140000d01c240c0306409802c6080040081c4100d4a0320f0b1580d5072700441d00c02042c00d200500880b407a054001c8280c41d80141744084060359210050582c0381d140a103005605170303044071034141d980c895040d580c41d036042150140d0340c88c0420000c24017050138818141007130b2050748100b803180d00c500d0302030000c0e0301e44c41c05490545255240018100c11401001c842c2510107420206032540b6081081180c514600700030140c0500990700f83c029960745084d220354499000c0c1c803682c00240c400d602800000c03007892610034401001400c0324103154803a10750904011055070100e0241c4d000060801c2056000f800308900d0014800140d825450404041141c0c071216103002814030811000241d041c032a402c0d0004220001030000310b4540c45440703151581d5a0703081c0d40300390115864100000c1c3e0303500c000c0e14580051480e00051802c50f2903a80d82920a03801003040c80354180030611283c0c0d10040200045a103031302171641c88415601e0300c210814245011540018040c940c0e8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 36759402 1250 36758152 36758159
    0x4090201080402010f0302130b0d1505030705040902010201090507090203010e0a0605031b01020f12180301060b18030307060203151e0306011a0405030609060609060d0c06030203040201050906030a05041506 90
    0x40080d0340b054082c00d20a0180c44094030481c001d11800314600c4460f060100d02141d000704041c042e000d48503502408100c80d0b21240d0f00381441031402d01c541603055200d14010320050503e500600ca00c00e1041c00007044011856503180d0400d0700a07081258203035404401080542203118207141c00095106042000c40c0c100b8020170786408106060000240f0340003204c018036482040b80907e404c00b14401c0e21103550100c1000300013031341b02040c080b2039100c14012400d041d16061085404564030425918034000500d038944400c09145803200d40d15010a004c0350011031054001144107010380450703a207840da542410411480640da04809032900c00541400321034a0005005041d1101101c4540680710366a02c001101c1c40b80b80c00c5641c06005800034802d018400044d100c0c0900c0f0101c41080083d60b81d4814003078040600c01c4081c01080420204000d502d000798000d5400a0040c90701a01d00b44980001c40c007a1392040e680c001c042e80d9240104810b10890b8080d4600298081e030050080518 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 36760652 1250 36759402 36759407
    0xe010506010f2c150a171e0f040c0f030606050405010b16110a0512010f11090603040308090c1f080705030c041a0d0510060215010b04060c0f0b1306060504090201 71
    0x30200b000e080c0c14000030800012913550060080141000030112991640701101c01403010310011051403e1031080001f040c04551840c800d5a511041d00a102005954440300e5244c0746034041c01c20f42e22904203608c0460a0140d01a09002642c003600d400300b041c41c40c040500040719416408030450020620490700d500c0821002800c0998011403c0d0300700030302e02d80009075084103d5008560040024010800b036100c19000100d8241a40030104610a5128000a0280324810f8050752046c01040098000703400b8110070b03a0048003000449210f2080c00002c25140340022103100c082080e25081e000c0c403a0b80c444030043e80030f602d80c60854154100050401c45501543c01034594954415404008a40100c81510b202c080c600000b4025410040c031820014080d42c012140140039801006e006103182060f207038100c3c0c0d08030600f580b910340341160880b040340c005c4004450060311004e641c0041f4404115040c0138100c2d2901046140c011441e2010071500e8a40c040e0340074600b810115000340c0c2c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 36761902 1250 36760652 36760697
    0x30f0e010813020f1c060b030a020d030804030201060e07030504050f0705030c0409060b06040b070c080303040809040903020a060c0503010f0602010905070626070e04050708040b0606090607060e010506010f 90
    0x1000c1e0144081110220700c00915850240540b2641003034a85040030245043c0e021700b00000ea000d45420003410146100307064841d0006140070350481c03804409000040d1040000c0d5911a000e03100011f01c060325840b80c00c0702c654040c0d5040000985500034441805028032600c500d143c5018000c00e801403070300000c00e440f14200326414cc401c0790341d94055400d1000c190005400c81c0d40092032150b50b036484406498030b54201580c00d5070301d100003142c0842d1302440001164000d03a000f4603803d040208540c10040a042c401e40124118042c1210650005500380a07240c0c02c8007642d100d9680b40c0d8181550100700c504030345d01110842e0706091000340401d0010a44105656061403d401a0035584410b886507006000500ca0045060020408116030040c1c549003144c0d803c40c1d09002c1c075126500b04031a84076003520040c12901c16000468a2450194018007030180042c041c41e0801e01c0e40d88031202152114401c040c0140d455104104696078000b298441030141070411200400d4503020300c54180 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 36763152 1250 36761902 36761911
    0x3100914011701060506070c060e06040e16030609050a0605040b01050a08041b05060a050a091703090f030c060a0801050a0504050f0705030403090b07080703090e13030305040204020c06090a030f0e0108 88
    0x10415040c05890b061080d040b032000340030050b01084d542c1c411840e000703010302060701c100c100003140521011410f24000d000c80d0700b100c0d034141403000b00c0c1e00d500e84602c1c0d54042091804c41815170300d440015058003140a40da1050380c5003540080d00601d40000e004c150b504020340326041050070807000c4600c0350000121500190401025500d00c034100015403040d04554002c40d50003040410b100d400c055201000b0141421f540e6103034261190b0b940c18240280981e000c00c14201c1c0c0040c08540d0090907c0a03007030542880040840c1e2514441101050484c0d00c00041040004e11000050002e410605000e90041100ba5020002c0d0300d80003a40103001d07403024088800700400000410103240c410100c8101034803143d44a41d50740c0c205840c218205a10040c0110302141803450002011070340005010700c1010b02901e0b0b10076010a5030380072002403000600407a0320690074094512805001c022051003080000002d00d202e95030303400c02900410750300944c4402c006004103020200d9074040d40d1590003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 36764402 1250 36763152 36763169
    0x7020105071403040c030212100e1c030203132009091216050304081218100e040f02040305101e1b0516050f030319020702030a0807150603080310091401 67
    0x2a03071205c0c64030308080003e0343d00c040c0d4007025070410700400e824040fa40680d5031482903001c1041d100440002c03a01c4044c44c50340e11040c032100c001c0142150340290021503010156502100d800d0b440c5135145001040c4c0503200c00e091010782c200700e1410b410b20705403003070b00000c00c8001048170301491015602c0a101d5075140e032070b03204201c003480d20400004005441c0034111080c1610b100c1040701e1090b0b00c050f0042a8140b907221044006400e81d4100055a45d03054011aa070b1110b440d01c00e40244805400041502403481c0e600308000404a0424003101c4440d02406030080b034410803074540300703036042d5203955811300301d43c5840000a0f00d254a002d0840001f85035003880b61f00c0d007042500010b070903c1c1d0507001500c103008001da141004400480210b218100910f1020783c0c0f1621100018128050004000e40591144a6441c046441c690213001024030900c0d0001c1081d101e54031700415540381d43d1044403900404802e1001c2000c50200b10000741c009000101700f0410002c020300d002000604c210341d00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 36765652 1250 36764402 36764407
    0x12030e07050607080f040810090c05010e1806060702030111071b0807180f0207030c030906050406020c04090f050703080901080a0207020f100201060f06171605030408090303070b0a05040506070201050714 89
    0x45c0305c000c16059500901c904402c1e0380404800e240840007030507811008030780b402d00403c408650b66018114800d00d00c0c0700941003c011030901c01040d24040009056158060000e01c81200180e070300f4010840c6c03d1000ea12100e4a4465518003100441080c032014042070300305500a0098035030006815085941c0d01c8500070074a1110180a4001c29009603090310380d03030001420300c1c00d05410010010105e4070035603904c0000340c0e6a030b00072951409a401141b005811035580b031082444e0503004071000a004846038803c0d6862952028500002139004641c0e007080803070050120b40e0410401a403080b03c1d0b480070b40c0790608a600282000084a820f984a903900420500d800382c400d5207e5405800f8050303440c25226241e40001c2d0100d880c0301481c407400c104400014001052000c1c2c4a01c09004503101c50342591510782e1003000342d810082c0700c00d8243c80180460700c0445c0f20118064028600d03c00006494142402c0281c1000b5004150300d0941e03051100f8042d1550b404100000403030001780810343c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 36766902 1250 36765652 36765667
    0x1b0201050d0516090e0702030412080d0204080607030b0a0e071d030303010807050411070309030206070f05100c031401050f0d06020702030f0610080a170a02010b0d12030e0705060708 80
    0x220103006000e074504400b4500001c0184540c07000c0102c40e04282c540c0c40e200207169490302c9907800c40d04102d81c4040103030810301042000013540200540454429412541480070340c4840c60201e8000307034001407140e03210109001c04a6010302c14659048029240300401ca0b0600d038800081c80c0c80a48001c0030005003016900d1441d0421a064084840007425a0b44d60359440ca045643c6082c0c0d401801d1050780340800178806207091034215a0740319419243c00314014a982c00b04241d6070001e03a402d4030207800341c29000b000540c090040103207a00d000300d800540e401c00c403003005080358001814040340e5a80540140072556038000c0905600303600b00e038a025901005d241602c0079001d0b45c0402909445504c170342c050a80f8010030710342d01c50443c141c0c0b05c0003030581c1c0f1105507a40300c0c090030001d8500206100902a10f560f040300809002405000102c0c4d40313400c00020480300070781036100365082940c20007040c0146a050285000130240b80b0020f201160800c00007511a01c101440101800c6001600c00b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 36768152 1250 36766902 36766907
    0x1209030f08030c0c0703150b0621041b0320030a0c0e0604090503030a0b0f0a0f03080304020d0f030206010509010b12010b0a0c0b0f010515071e060e0a05011505010201050402011b0201 80
    0x3903038030214190917216540e66a103000d490040000300e09009407070500341d8907651414490300780e41110318011940c1e140700b036815104640c01c0c28003410a852019070035108150b502c007092070351002544070303a8444102d0824281c45070500c440c5940182c0c400c0d00b10030b50001c04150303454003080546003089101d540503111300000070020103031007070001c1030703400080100000c0c0420341c0e0146419650a840c0010a250304c5401c10880c0c0201e1300500301d0010f03107a001407000c140c1a0700919402807001e01501824042074841c004002000e400413001a40704200501150070500c1c00c0600401c040140c0034105a42d0010034640c5a46c1406440740408004c211200b003244a1002c640b0a5a001403450280d82040b1880d981c0041b000d025490065003a56040211482d0f81001c0310a0141c004d54045d132900700f90883c0548000408000790b54603611341c07241d0290640140003098429219200001e4031481c43d0301c0c01e1002a04035803116042da4541420003000d40d82051071038444084184024501501500c0103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 36769402 1250 36768152 36768157
    0xb090a0e030c010c0e090601030b01080112031b0b04030f030507021203100e0c030a0c0914130b0301020a0f030605031b090403021005010609030302150403050913060b070f1209030f08030c 82
    0xb8001943c2064424110340340c025a0550100005680f03a407103960703d0000544c2964000e80006000507200001080454845401060458401e1600784040004c03907a4504042c0c840c1102568035440c4442440101900712000c010001c50030b007000d0109150442001e91502c00606254144600000020f500e40e034007141420007a0400409400b0142450080301d1030715017085551080c141c1c64020042d42c0e1038000c22162080704e0004001c1e441821450003400035030030504220310740b4552070300602c9906903420700140a04900ea80e403002040211800001c040d103101d540624000d4008001841d88202243d80d410308800050f2428401074569203412442e0038030a841c0300c00c1481c41e100010a0722540300350404102c13400780e030071640c080d98ae000003100c01d008159801000f2031020000700340142070022005401d141c0319000004e2490362034000d800c00c1c0d8845401210000c20a10070542040403a02030316035070f29080c0c6061111203055130b50b4075158180b02c0a0150400074040000fa0361007080d00308 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 36770652 1250 36769402 36769417
    0x9030c03010204060c02090f0c040909152d09110910030b0103030503010603061706060f0301020705010203040602031f150e0f180f0603011503110102010605090906070207090b090a0e03 81
    0x2c66442c1e9407075600071701c50b14030200200c0c844d01014010442c2c440403281100e018800c98608186031500d081c000394014810b002045400301c2089020030b095181c0c40c41b032480417914002c00b12207113250f15004400d0b2812000484810b070340c64100114041151440a41d41d000f105540c1f442181d00c421f91040440c0c00c4542c00140070080080000c41003540c44009581242d00310784041c4282601c40a6030300d403a070010f8143c80f0703692307006900240b00d030314005074a0071303205a01600051420307e0756100c003801c4e80d10480f030030380d040e40d000024428183c0aa6031208c40c545541800c110000341000f8001340c001480390140003c0101030b04181450380e40d00001c0601155006000030340f990618900c9884012084561408420b60140044e90074201806a502840364000102d508241542d4800d4550fa43c9521039504540d03941c00d000c00c081d1610700000740203e2004c00249100d1a001c68000d10300070003a08030860f20340c21302281c0030840d107036450380c180c00c8511040045040456607c01d00d255014185 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 36771902 1250 36770652 36770659
    0xa0f08010c020105130f0320070b0702030c0108070206130203010f0e10050a0626100203011707080109020105071101110d0e030106120302120309070f030b07020607031103010b09030c 80
    0x11400545810154481c0048035080c0d0001d1100d55a501c0b246408801c1c803101c042c0141c00e4403160900024428a105880440100c5403c000f032000903218615013007068011690b403e4000561409500c2c08004101c00b02409190250301e501c0c00e00030003921034502030075552466018800b548115a000c2d0040640c410b9032040c2044520084020290385030003480c1c00d50b078910b240402160642c00540221400d4805e2103218113203820400f000001d0440c9144184445030280710344c0c1140da00d00500065000b0a4044d1007500c4402016140c1b41c00d000a41c0c1c40100b10f03a02d04002d0400517600441501c5400b500f120440e40020b1000d03005960100e40e401c800382450107a04002034205802c05500041c080e0f05070020856142c031180085146001c43c100900940d2004d42099490140f0100a41c0e2110400c0b0686030081ea40b40c0d80311038564605d0b00202c0d965185802005801ca0b4100880da43c0440103250074007081290540721402d51106010f80d420304040000c05020316242008032030074800d03018 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 36773152 1250 36771902 36771929
    0x706020a05070201030f050411010f020a020a03080a080106020610032a09150909020303030a02092206140301050732030405030405030106120c062a2a0308040b090a 72
    0x12480200180d10200d0100c0c04240303400010301c1a4406d0f441281d200320350040082c488403141400548da41e64450392240e00714820242401c3c0162908900071000358410020251907104061003d050900140c0100046510010030400e1035140380c0703010f5085175000f200f51a01800d40c4030313540070342d1300c96400300300c21100220100003000080780d03108404145210f640000815252200c0300c0940d0314180b4041c0d4160b1017823010815440c2c0710307801001600b0b402414600740407110b0001c4840c1f9000046541c0d0b030655038130030801c071002d901d0130b08109841d8120001c0200f854030081c0503140c0f221701a903552142d4086008561003d2441c03d51017118181505056102d152518016590f940280541350195080402c0050071780031204000501030362204042490b84e007000700896a40d1044c98149444412034050481000130f81000c00c180c60340200c025480c190850071707080000d03c4900340d810030003900103d000c101007413180040d01c0c140c03141440d1403980ea1100200044110001d504118002c80c100d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 36774402 1250 36773152 36773167
    0x70303020408150a060602010c0c020f0414040605040303050f0712050403050c010e010b130207020a090507030b091303030c210b03010204030501020c0a0b01090213030620031305060f010303020706110102070602 92
    0x10354445125131207103142800b009031a0135080b1309a50704420104042503107040c00c40010700e841a00d60000c1c9002500004011032030100c2d0070b81020043d541030720219926018082459410701034180d004026543c420914181958020415440d40d242c07840a075645c0c1c000f190826108400b00c03039a0b018113170000d0040d0801d034041d417402072406c0c4245501c5008107140210340355545000f92410340d90020b1913411030902d00120b440282500401110815544403c000059642d80194038094050419074948041700e40c9005021a0400c1d0060b82c144a02c0f40c074070305840c1d030083c0407440162801a80100c3c4d184030f0000864068020703504000d1603940040740d1a6804000000d02c0c02085000c0c81406006999800a410491051403107282c40400150740c1440460120381146084074290001c000c3e075980041324404441d0000c2d2000458401007469000a0007401c000b00e540000a6460f404813552450743c003e0f6a50000384100b2041c8001044c0003c0c01070170a50664182a80060040d0340d0b8406 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 36775652 1250 36774402 36774433
    0x180a0807050103140709061b020612040605071e050a02070806090f060a0510230409060c0906021906180b1f0611071e03080c01050108060c1905070303020408 69
    0x18900405000a10f07140100004c142c10180c1d00b405911503850310740006040940031030342542c01c40400d103400003120500400503228980101100104803440c0301003401d1614005080c3d990140c003250400c1031200401650f0044685480d03c102901c1c01d0540c2e81d1a000d02c0d0590030321005c0d81c8100003070300446040210000c070200764606200b40500c00e494a9980789801b0328103d0350143d504601c0b01c080a0b10601c41340d210f01612502c0c1c0c03aaa0440503489070080c80008040d10210001140e100e80c40714200300410390084403420203482d60b030001c3c081160b284007800d441070000700c001030440c0c0d454944841c00c000a080c441da0340740d6001662030b00540f80c500428841800140d6112128030143c100024504c2c0c0724a081d144a90310840140603802e1402d412189035080070071040c100c0d81300380d000000019210b4002411100381d090008100c962421209909081d0300a00114a242c001c01c505400e010703090320309103070480d4a030901d1900c40c0403500f008c0300240036a0b0049080740c0700d807070310001d0260f0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 36776902 1250 36775652 36775663
    0x90c08010c02070e2215050a1a01140f090d0803070e090f010803070b071e03050f070c240b180402090705040b04060c05010209030a0c060908030901090902180a08 71
    0x75195022540e0003a6152054136011004071071682c2d08960424204400800c07a803060403019014114143e0300e03100c0400071030115481601ca04081d40c0d61040b0b04d0740c0c4190315041e0103001c0319090030681d15500c05828040f0080c810f09013458060036000a1681e0180d845c0410440c1440d0400751584c1c0700d00e0314880241480380325080c2302d072045541500084409a40c019814143d4803018041d6003050b25a95460039410405001c1302c040c0080400e01424000e00c04030480c0b10f04801c1c0d6004116803d100c03100640450700a0544410400c2c540a80320110340c20800f80c0700da603441311001a43d05188030074900000e102801c06990711000824040040300e511184650103030f07000700d84c85601901c40220680321842244151001004d060208004040c09895180c20039400f0320005807511200f01c00080c24000d600000b21105540ac0320107000166110f10b241000d080e82e00d000310b280049110001e400105a8410102083d40008006141c00120145100b070150007a00c4202c03040d0710740c40e1240d12007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 36778152 1250 36776902 36776921
    0x609130204030c091b0c02010c06060e0903040608090a231009060504060e01150510050903030a021606050901021908160302030a0e0402070f020f030a05031204021807020606040f090c0801 82
    0x158107150b010030110b45d54181088441404e5242c01203d0030b0640c0c010f64003494503400035160306696602c0014142c3c15845258070410088001e03580d21800c258025146500c0900310b24850b510144285000540540380c00d0114560400da245440000f0518240740001120b00072102c80d082482c08401c110360b5070400c60045102d203409008600c8846c01c428200c0341c60621807003204504030070800060500001d0031840c00aa850610701c1c000140000c179141d580104078000060f449142284070908850042001400c0a498568540900000000c0d6610340c000d051310201c1c1242c444200422604038102c520728030190201c01108541810701948a4100a070341c00013144000b16128000d1409100b00c50415500c4202c6060503012030302403110a4801440c1c698240c810b2911042c0802c000300041c0c043e415030391805804518040c4180701424039000401c1440003030070740034440c00f180c003c10826400799064074005203107131541030307981e0113018007030405441002d12a001190140044d004400342 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 36779402 1250 36778152 36778169
    0xa03020a090b09010e060c030f0f0408190b0a1107050a031d0103060e0c03060d020a0f140402041503090c0f06020102090405010b0c1c03020d051602100506060403020609130204030c 79
    0x486035160502c50300743c401c080c04640000c2059030311000310f240507809000c08040800c1143d091000800107166281c1c0010103141e142c0e50082410030185a0411101c0b1442c0c2c20f0710038001110102d940c2c0c1c0c21004001401070300c00d071522403220003d8400e802050301c08840d044421030b40d03407a07070794100545090801c0c00c010040c0c04100201d1070665000b40036100444500808504c100d1395400200711940d0009880168414101c14040c030150340da107140640980380c180180000d552a0090f40502140060002c5005c1e0303005000802440d410140600e603100150700740400c805055207070401c5164001d81003101c020f11009004140e10741e0540c09000c25150035034040251f0f9880c0c3c03100349184c0c020101d0f28085940140030300300e00c040c4804000d41c0e241c065402c001d401c0401003122203007900c504941200c445001072040742a100d5041010b41d1000d10001000c1015007010400b2035018811804042d01070030000a00e540c2c2600c8003c02c3d080c03202c00c2c40404540700c0303480349001e000c41507581c4640140c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 36780652 1250 36779402 36779417
    0x30c1712070f020105010501050703050711090c031008010504110f01110102030c0405090a020405032d0d031a01080105030601060e01020a0506010618060503060a0e04050c04060e0612120a0c050f030a03020a 90
    0x2c0d0b0051250b80c1c140c9030705854003400d09160ba42c084807150701c925000c6581d040b40400200c0e4079186c8100302c6010301c54003900e45807a468a0800b40c0c510400661015040780c0c1407000b8000403648110b07182d01658000c1d00d07010000c0384120700585038802c5500a821407903100100f008036008092020780140e460440d0911040d17241c03066030324141d0007035004040d416080501c403d50700301d01803000e880740743c5450741d52100c0c1401c40070030060504c8284007600000c00d89a9080c0c4121600440c5c0c3da0070709880074240030b01254105804660342d810305002e14002c0c0b01c0c8404850100341e00800451005a6104007100c84968503500f00414040181008000c4096840004209607010301d0aa03442140c0141c210780f07041d403a0201d4009201c8c000f400c00e80b141e010360300300c869664489000b420094031240c1c03c0d56030349081c0482482482005000464120380141d80181c02e50307080072081340c10014540ca4185a1010036042003414070301c0d81507081009100c0010a10390858040c0c026000d0354003c0c1d00d4180c07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 36781902 1250 36780652 36780677
    0x2070501180b09011206060c02090106081312030b030304080c010206010b030408090108100e0406140c0408031801030e0a030c06060614090d11060a0507020909030c0a030c171207 78
    0x580d0885214041c54a1541c5554244110680710028192401e41490040d2000c02500c40010850782079420200000d00c10a43e41015814041613060041645150107001c038545100c901c62040381e0b21400030013004821900ca04501c1c4603410950210700c004003940d0340d890f5a00c624544e640200b030840c9000d030190303400020f00301d100c50301543d21450300414802d1038414403500464034001d0090814262040f50180440c82019800c10140709078810300000801081d0a0f1800094100003410000c5c4640104014400c4d0003020065604c001e100203c4c030071903501d6a00040c0c02400902090380402d100b007840d11824558006100940030b030040d01c1c2000a03036200e5004a80d02201843c8824610000300402c031400e0400740942402c0900400d00d230301881e00303c800003a0b450351245003000b00098020803604254a81000345982140d01c40c0000d5141a120243c050f40b0750703001100240074404aa288141441040a900c160050f018080c10ba51110800480082d0b80415500b010000b43d40c004005d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 36783152 1250 36781902 36781907
    0x3010203060307350f011d070603090809060f04061403040f03050702030a1410060806040b010b0c0c03060412030e0c010e040f061208090111070b0414030a0515010602070501 76
    0x101e000350405405001214202169100b880c04148408101c3c00c81550030340415901402258000d45180800b41662007050a41c280c02d41d109000020b0826114001c41c4820100014480742200c00a040100b0428107505104100740500e540968100c02c1c0091201d401d2681040100150f0b6019100c0c000c80e0f410008040704d10340000c98005003440103042058020078001c1028041c103620080c120340751607070640c0c1c51082c0b01310b21071044c0001c1d500c015040d813204115030194201905041008000d03a2030a031721017103c00d810620503c1c02d580000181c1540e40d20092025540d80c000c040e0031507101d424286850b0ba004040200314100103450200b44880100010420301d50300708050756203c183c44480710802006001d001d81d135540380c580d1540e000034043c04402c5a0940c9a000e819225100c03011000050402107032040e03203940c550030904040c015201942c05507030a40d005402401c40714005200404e20303180c8410301c06400b0f8450000fa50021031550600d8a068416a900751902d156480006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 36784402 1250 36783152 36783157
    0x20c0a0b12070503040f0c030605150402030907060e13060e0f060607020315071209050a050d0503190c0e0607060905100c050d02070c0b1606060501050c03070201080601050d14040c05030102 83
    0x903540d51180c075101040700c49100ba8051600103005403600d40c00b4200e1640c40003105450396204503072039516a410000e1480c45c05c0054030103210180d90035032552401c464900d8031400c05009907010b002076031903100c0e0a40c40b000741009a9111f052010800e10361245c0c0400ca81c18411544020300e01001c0d000501c4900700102900c0841c3c4d0f0140c002c0000c50000c41c5585613070300004061504009400c11140c00c20002d034040c52004d980101c0240c0020304450406604280d000f004100130301c4002c0041c08400511414422504901070a001640c00c900760001c407544503940142c0d69100801080d02c0090041320340c820040c03d4032039000c0b64500000003407104245d412a04c0000d010031000d201c80c0c0344c582c0c0355800400d241071103460460603854580740b080340960804c004000c9680907402d20b9500f041100c1c0310f0240600000d00b007043c108000d0400003035891046403402810451424082402039000e03c0c103407000d03c4d04007030051100030300c0d1603210003100380c003114161801d06041c44002400c2c10706208 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 36785652 1250 36784402 36784417
    0x90301150e060103051b040902040e0703140708040203120a12060f050612060d020a0608070f02060103080405100e0616030206010915031209030503030f090c030606101407060c020c0a0b 81
    0x900900c541d40c2c80006500400c001844085041aa00009522541200018009007240c900010b1b251410304020240c6144010014400d1510f4005032842e28500c00745140d81c006030318946141c43e55a28400f20b4141419505003949142011800381c1c0d4241d0000c540c048190f402000400c007440d510780000411801d10701c0303141d401100410a00340302c080c1d040c0380968041d130050000400025181d0214409400c164805000510210305004800b58080500f00c50000e061008240c035504617100d0110911540c45100c0c41001d04d501400b02e01800350340c5aa890001c0105030070b4903031000140740d45048488000071030050190000100b015070380d604c2402405040d00700400c0309a802c644d50501d0a0110344044001e1108a042c0040064401c000551160500084031421801c005002c6d500e04289510740911a07044a020400280c80b98050180d059056103405608141d040c8200740c810b200e04000038141d1806d103000800440c0d0000392185501500366081212141d59021461282c0154079 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 36786902 1250 36785652 36785669
    0x30d03061409240103090f0803040b0a0204030206040b0901020c191a0415140c032703011811010309050703120f090605090103020a120e0c03010e0f0c0405090703020909010209030115 80
    0x45184201c81c0ea410000701220f041c14005103640c07180d1a92940754103543c00403100b1005c008100800c0008400101d0f4010002801c15810181154000b4406001b107000350700001c100801c031036074641e00c20040050300070310240000c81c40c403130b204001034540304840c040c2c58038440c1c46040074805610b0324800c440840d544210284000052440101c1d5072541444011801c9101401080e152490070301c01010510160204c42246010b540c100072218090149401d02c264581742580000303090480c01448440d0b8040c02d4100e0071a030840c0180c1c014004104090702d103225062000c400c00c50845086e14a000d0030b902e5a06401c0008102201c0103140d07402210005081408581c0c05035000ba00545880c00440c2071501603500e5941e0198111028505203080c80e520074801c0e8000740c182845115849240c8902411441d10301101e41e96441ea045041da9000716a40c0002501e07440c400e03c911400b950b40182940100d0502680b402d0103900404055442540380c601d0030a041c03810320100408540c0302e203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 36788152 1250 36786902 36786931
    0x80d0f02070b09010c020a2a0b13031707030507020d0203070b04030812150d06090819051801050310031b090903020601060e01080f011403010608160602120c03190e030d03061409 78
    0x140061820400180700a420b42580264042a91109e8101a01d00d00c02181c040038600d0f07103903090540f00c4c02142c1e540c0c030100302c0080150300c002c245d1090440d40c40315016500c04031920000d101180c07800c2090f500400340c0900c0440e0100400c82c1d640020b003119920351542c0002d03a10f801030030094010041c0c4009038001003004e6110f000503e96001b2140c0789000f011840d0600312a0400720b20701440c03508a20000030400240d1414241c900c00c10400f00c00400c0c81e140e419450101c104044c25442c90102803d88042d8402042016803802d080c003014110101c0103000003103061402950303030103007030062a010401070480780c181d03948030301d212500c210400030580a21340d00c0c1030b08070501072841007205a019500d65201050f074500402030003052038030a42ea048030861402e04000d00300580c51064603e002c00801030004803110000641c0c0d402441004200706054500000f0341c1c02c0d1041420858141c0204807400400c44e0f0554011403c442d00d0280c400307101803403107040122041007212440d14540c4507 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 36789402 1250 36788152 36788183
    0x4050c0301062a03170702010c020c1216030308010f06020c0907030218090c1809040c06080603031c020406030c1704030e0d08030f0a1b020703080d0f02070b09010c020a 74
    0x285a0b40030243c03081d901e580c90441c08502d4941800800407500b907010442038040303214004540d0034a03641c0701903184000c202205113130f100251618003e0004c04d10a01c2011281a045c01c0b051002c08009030103030400125080c1d03a0318010708843c00c2440748075461944c030040042c0460020458210400006044004c0380d5101030055000390403a0035400b005189104d40c0c501c00e0348a40e500b06002d202c40c021815101c00442c521f100c148240c14003000d0240055405000003d05140120b109a40e000d0900303544580e15500400d1030350240c940c00c001d8800e03401000c2814440260700410079a0035070303070f0f0910141d241c0e144d00f0340e49808004d80035548011384000140105c2d10074138950001c1d03070b002000341210302d0094a80110b99003081e10100d44400441c1e0602c00b01505a00c605800d06904c062440750051b51010081d465504501c030107440044001062080103541c0d911201404141c0102107440e031a80c0e0a007450303080c80803a00d5400b0380d0301e090030703100340a4000120400060791021702541304807803 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 36790652 1250 36789402 36789407
    0xc03030f040c0510080a0e0a0b04080c03160c030210030506180c040504020703030b041413080315040e01020306030106091a010e0609030109051609060e01050603090c0405012304050c030106 83
    0x10010402d0701c0d112241480403d040d0350340c120300c4100300e0b140d40c0c1d2071a06007406400c182c101d4080b002a40400d5010803a9500054008200d0b541e102e90001900340e00c861001c2c070141e055205240c000300d228451b07044540c040040c10f00720766040e04e0007620070075400000d40400f60300b202c0098900583c4a0781c840050f0b00c440c3c089061250384201590300003410b09607640089426a048203038200c01103501e0340441d041034109403080c0d101d11b54201040110b1410f1204c01303007491308081d04028200e020300000040c001d03201300a05807200701001e041080050125003e1078000e40050b0b4103107103e54245500020314000300e000b003000c00c0c01e000c00300159041d20700006641e240c070840c1c040ea40044040c0400d1300d5a40d4284101141c8500a070041d02440c01651504080d0140e503400582d901442c1c07400501403103040c5161300717054600c00c1d1030550b504c0d214080180e107000344545145a0060034000007203100380c203030745401299010300e440d9072120300c5946040005499044418015504051004110051 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 36791902 1250 36790652 36790681
    0x8060a05091513060609150816030b0c0a020106030c0609090e0601180906180602070314030903070201140c0d090807050f0f04050601050c01090317180a1211010f0f0b060c0303 77
    0xa1180c280080c040340d030340300918140d1f000b00761131942c000340541c8104001a4144554261050304503484004203045603600111080c0240410928078408105100124003d40c03003d00510f42154484810703c1e9070300c0300182114051701412002e01c0c00c00c019024055000580135050721355521440d4804640c1756210700c003c000500040c0da00a48864120504034101d14894034001d00410003d60341c1c401600f0080c0004684a00c640c003540010401c104d080040442a00d00e260350901c1c1c204034440d100384900206000394210742059000340600310f8415508600ea800840e108101030b155819911420080e9940c2c90156868100c846005a82d815140c250700055015a050400b01d08050030101041e0031100c200c10110003052544140401540301c445e4030740c1e071260042d014500e45001d600c15180d107503400d407500140003c1040d40c0c940c41281c090011240c5c3e01c0c1885c002005071016602c0d0f20b101a044041041a03060b1812084244a04205040310b13000403d800c011451500c03483c45091010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 36793152 1250 36791902 36791941
    0x1005070e09010b09010e090c030f0c040e07030b10020321060103091505010602060a0501050f0409080d0212060a0902040305070b0a05040b04030501020d0f05070207030818090108060a050915 83
    0xa100e1a40c400680c1e50480c107501a1160360710303042d110b610342c000241a1454480050b80f241c0d4503001006145800c80d02242e03805a038416404185e40c913503105e101041c6c05150407440c070841001d420041c0443d41a4041c41441000303c8103541c0c172a00a02042e6160b1007540009001c80540444400300700344031340503040c1c0090f0107250001f0007182d03136210540000c403010300c00b045040d225801040708036810002c040d0451810b40033004154900400605201000f244540c0240e45840c1582d0034402050280d42c0040d0341da03d001d40d9280d20144a80454000481d0f40c603108645020002c51102c80500c01e44080e242d01c540240803442c01e241c25840c00313411040c1d0b40801c2110070040400d000030800e0291009610600002d6281c26040a50800b41c0301c8482c086000ca0785007600300704c00305600147c030004036900468020394aa51155018480c0008000001d4004007090300006d0301c04c1d00010654898181c801c0100030342d40395001c61988503c01d10101481c49640d14020071000300c5904403e0070407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 36794402 1250 36793152 36793157
    0x1050705071707030309050102030a0f0305040f080d0b130207050307021c0602040b0d0b010e01021b040b040504050a05120406142107031a030312011403070314012c100507 75
    0x31030b0742d00c00034410000406a0030102c80c0c1c120f0a420801c041e001030005025013000d0000c3c50500d400f12500400c8000c20440310000c00d5111004101402094254112416001001e036655040d4035540d8802510903164803070b0089000400e10f0010020340e1003650481c641c4100030718500032203a0208005822510b103c05040e040c00c41c034030800284544014002804c0100170f11b038550305c1500941d0101c0c2c048400c4181800116010103e0f1a0703404145914138100084c0031390015800d8601050040504400841e0094901014801440f000140c0c0c1a4210f00c10012078400d4990064012039a0041d031081030b02090841c1e60041581142d0030142820034003c4a07100a20103080e42d008401c1c1d81c080d140000405d0341c80c0c081e91000b251040200004000c250025880d0401c03001003400540c0c0144144c564410000c584100c1d5903400740040402076400c80301150448942c014501e000f40349111031400e00c4190f454400a2402d13150a460b9500e50901000e84400990340c4c0034038000c0c0000a084004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 36795652 1250 36794402 36794413
    0xc070b120103022205040b0703060501181e0302030a0b010503010b06180409060f1a0111210c07051e04050f06010c0210021015080706030b0d0f0206090904200603090a0201050705 78
    0x50084e48112881140200407440090404443c040c0458415030412410000304181800d604402082c1c4242101c06200a00340004240c00f20700fa5400c40c0c541001390701d40503101006e01404807900c02641600c001310000c024002c600e00401100b4422480201c01c80e2089000c89042840d15900a50020b4002e800110f6002080101c0c601115941308140c00d00031030340c843d05160307940d00134014014284904004d000c0508261242140b180c4e00c0c0003607075000c0f0400642c1085842046c00800010140940340e10000301801c9000d4011040061400d030103145014005054440030580c031b5409500103031261400c0c003401781c081c000e200c1004036210b401c1d403003183d0070041200050f00c14291003405405210486504050005050014a034000d000709130402001446c5507661f20388070000542d002c45e15010005441c0301043c820b01881403402c3d4840880002c000c00c2c03288262241440259410700c1c4102015024100700c000e0005681d14542c95010600c00030040d40188010110107019204942 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 36796902 1250 36795652 36795709
    0x20106031401020c070503010213030b0402061e0406030b0f010507020d061e0b15040e0c031b160516080705011407020301090f02180c0d1a0a0b0c070b12010302 70
    0x107841c0064008695541da50002c3c00e0007500d0401d1051034045d06046000f0b5107001002803140c40100c0c0705020140c014103010002c03c04640c2c400d0300321036107411000001380300400c04141c01505030b0801c3c07052601081c28118880580d1812840d0f4000390301050b15540e00301682c507000c0c0032411450f00422541140e8070902e004080003d224400910b1010b004049408689081407115103103a00c02240341a000500c0706005080b9210007a1368444100380d4102d440e6941e48204035251b4040c641c0c020320003880094274041141490042c04500380c000c1d070450b4211102152004040c041e94840d020294000880600c034541c0700e650b80301e030f0085160040a00b80a4070782c0000e401c46e14440400c5444003440300014003107080c0b43d400c104210803503805030340706840c0202c014801449890814100c00e0b41e1502c0d055030907203c0030303281054650050124003110b511040443c0860340078801028041c4140c94001800c4444c0c0403ca602801c00c0e036000c0801a4a140d0034020a0503141690f01003020343d9160a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 36798152 1250 36796902 36796913
    0x8181f09020d080406020d081504050405030f04030606030c060215010b030a0b130b09090d0503060402031306051602060901021303020d020604180f060506190e012105010905060603070c0b0702010603 87
    0x2010300c1ca008040040d900d61805c10040c0c130300400c442d01141031010740010825042c02e14040016100016500400c280e50b462034500d00318482c10006154a8201040c0841030002d82d030b0004090f0781c03081441e075028545800050b07a956081e6a50596103510a0b40180103500d000c1c030107180c0060441002041c9400721782c0002d03810700ca400d0800700f541ca84e1944500010300c2c00d200740b1500722000402038102051a00c4004106120040c03a00e8020b41c2c002010034074a40801e800800f116070801e0040000b030070801c450b001000461150a0018412400030858415043c800c0f204071a15210300d00f00010f10b075901303000300f499071004180d80c0a41d06000014841801c014284101e02d079103080010403a4515441d082180da540d001356006542c1445013068140c2c5500c4c800d1080c5c100750230079291017415500100c8441280300200a1110b4032104a0308207121540c0001e810307950065005d12407603980d601030103107d0008455020004180c0c3c546c030340101d03048144403a0400494800030620740d4503501c69 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 36799402 1250 36798152 36798169
    0x2040b0f060d0e12070305070f031404030305030a0e06011d0a020d020408060702150103020109060c0501060b1801020f0f03070305071a010b04050906040603020108010504020d02090310060608181f0902 88
    0x6640b4030b4403952240e28208061042010700c50184442604298554800070300602480070001d0108003808030801c1450701603000c094540300c0c030403103c554940d22840c0061980c1c00c00c0e109020400e0404070080c250810204049040c0c03801100c4010310b001c81d050000078401006044c00d04010350070000b2402c100042d0000300041c0055000610715420b0440c0f00900d08400c4040b0700304100c84800061005030390200070a0111170381c9280002050720a402c205005020541c400341e4604000a01c10340c5280000b05544400c000c26001e0783c1c120110030544030f856261482c40540c241e0010000040081e019001030805507000d4400030000c0840802460940b00b800e82140340e0f40e41010504200070302c1c06055640c0d02040a580900c201031445d800a05043e0060188911454002c500a07801f02003d0303054035000c82c0010101c59001c030a04d50510f000742954010780001860f117a0014080c145801e0f258552140448001c0c141c207000b20b400180f16805152244180383e407205c00c0c00e80540d907080803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 36800652 1250 36799402 36799417
    0x3020705030c06010e010e0103080d0902040b100f1107030c060f02070306090503030610020318152208011506020d0806120f070e010f050604050907020a02090a02070c0902120402040b0f06 82
    0x1448654101605c0000280c0140e20050310300110200600018200000366003c240e0300e880d020504060a20015010388000c44019070841000c030405a001c075401180c64115500ca5251119240740b410b50240e203620540c0000340000385c000e00100030b06407042005820703030120740c410b071a0302d00d440e50f440000b990352145054a5950001c010712031185030400d2001c000146070f000071494140b03500b0366001c51040c0c6000302c030b2092840c040c41c1c0b48100d100008075883d282c2d04081e1002d011814107036081c219143c601803000b01b0741c40d001c0b101c0301d8101ca000c0014169143c07070b002080d032048601030498804000600d850f03001640d0800703884404104002400d08500c0c0ea40c00791080b582851a0420b16500503807010881036451081000183c659400f1103064900c2520320845a41c0c03011004e03460140d281c00002c1d00480c91400b08804011941c0c080e181292142c130f0462040399444e11100264080c030789841c0842680071000c600149400d500a000e0340c80007801c440c00721045000090380315040300c1e4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 36801902 1250 36800652 36800677
    0x110f06040e18011104080613061b051921020309070e07030209130b0d0f06021b100f0507080a0b0f060d0906050612070320030709020423030606100302070503 69
    0x3004451407000a0240c410103070400009130781024500840c02c1d903240e00203080d071410907000d140420700b4480c95400c60304c1c03156801e0001c0c03040724104000040c126400a0840013510034081007004555120742c0030382046609800541070018026600304001354000f50115040740b003034800000307000c2c1c001e004003071103a00c964a005854058510034010640c1030702003014446450a4103810355903a850401e044d240e80c01c41c1c00350302241154942540207115011207101c5407503506940c0c03680d0ba0380009a039110214540001c4c0b001282140261f41910010b85050020644c0c440c000f5240355042d60100b2406a0000c184a2203030580c1c0b0041080b40c0d001e440f40d030441c0c60320344001c07100b40b10441c05000c4d00444159030340d50340031403d1174a00d51512a18040100000041c103606440089421049018a0380003030a9500065803407552030000d500a1043c0c5840209001031001002d2290b45414000385019001d0120340e915501000148090b00103000c041c10740c00e120030400700b141000500310a14408 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 36803152 1250 36801902 36801931
    0xa1b050a0c0c0e040b0f060915010c0507030506091605030d0507030201090b040605060f030c0d08090a08060703060f08030315060d110403050601030311030f0a08181506010912110f06040e 82
    0x242400c5d0704041e030041030000f0b50443c54041c44659110010820380c1304070600c40b02424403526000480d03040e168080c001c1c19a104a503404018032401081040c0140c0101081381c8005a00f04800d02021a0503ca4954160411544bc400f0503015500809425109100010703a2104031b9403510380c1210162010b5402e207564508200c1607003021001c00d0b208901c1140100f0600c400100001c441750300c0407a00420301000819131111603110f13006041e01401d600b0098550034036188030000c00a141511407014045c2200700700081100380031040741e025070701403800203000c10021030a00140f03610040300b008201740d50b444c40402d0a12010003510255208101604040d450b40c1001001060100c4441c0b02d107820030405000c0340c0101104880e407616803801c1c46c41c60303547d8000c051041d00c0b603814584c0c1c0e020b0182d0100100c3e5260700d00070162080c0c809890784410b5a44030110174250307402d100001462103000c3d900403001443c01c1d07021400c0b1840001d010600e01900c1d854443d81203070040c1d0b00d040c198001c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 36804402 1250 36803152 36803161
    0x30c090602212110050d0c26030a0503040c050906010c120203040f080703140102040605030a0513060c05030a0c08010501020706081504020a020307050106050f060703030e010f1b02060a1b050a0c0c0e 87
    0x1c040101c002440700706e070f52210400380c58403000010441c610408240a0550b280ba50908850001e02413810031407205407a1903003600440034000358000c850071621840c100001041034500007040030f02460060350381002246141d6515800300200c4501c03441544014000043c109504000f4a4054840705014101c1e003861032402e0007451a00e02c925950a90042c0400d000c00f99025007901e601c4440c0400228039600d0380b4200203803140c044000580001e042910785d500441d0490300560080b03034085000c01c45c03210341c1c401c04c6032821700038022503006030082c03a81013000c00cfc8603101e01600f0440c0f6241c10140088620002004c85e4811800900560004204c90341400000e11074030005190503030300d01c40121980000070712688540d100003405d05540b2f1640705801c9100754005642200b40501c2044011500c05807074010f4401c510311080188035480000f1115031007070240c07022543d02d1584842550400344400d4030700350810000f060420004d80031540210b5648070f03180c0f00a1080044551503401d2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 36805652 1250 36804402 36804421
    0x3020a260303060105031906050303040e1501020606010806300a030f0302090f01110a0b091606182108030f06010801090209030c0f01030212010b0a030c0906022121 72
    0xc0400ea05200d0303400c24010000c15980003002c6039400543d00c1803000410080703010340360050100360001030f054400030801149801c00660b0f000e00910484c0405201207806000490743c0310003c0324114002121800840c1e00c90800341c4109280c1a80c110842c02e0750350980c50250300a0920b40c80c4206550b0010389040c080c1500182c1d64000760450345029442c00c8818030200d1310b030302c0c0854003060410088020900781d02c07100744008481203600550341c4480342040e9110341d907107810890256a142540070400220103020f108903a100e030503c0c20700510101d103031103a48031511504001542001c02504c807900001001d280041d031288021150010301c03401c1600c001010014141c1106500c103104018641c4590340006402c00c242c81e044802100324040840124080e0054158141400861000216541308600080c210b401001d40c0c1c2045929a42d00d0300300d48498080c0305c1c1d8805030b0441c0200141044942108207004000d004146243c02005901e17200e4818050300f000440f512a00b05200d101803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 36806902 1250 36805652 36805709
    0x60d050102190801050901030507031506050306190f0606090902071103060405070608010b0a05190908010f0905060a1503060c03020f0c011d06071b060b030a0f060605060a1704060603020a 82
    0x206071b46e822000e43c1580d50311943c032481c0b4080680b030140700c00c2220581a00903088a806003e0180a4505074180502c42140d407a008001d108681030801289452074201d03407083d40d003111260342e03030b07610100d10b0080c4184c025404140d0540e200c010040d020800c945042141600035480341d030003070410500c0d102c0010075500701070f0071012004808010050103a80d100044c1c40355145800084914441c0d441c2007a500c11245074400caa40b5420b202a8014010050740012940c500800075916a9503c40040e03a04a03500c0190010303e41d02041e1003070001c40c481d40e0110500c10168100146091043d010005c0c0541201c80f200029a44070011010340080030b140f41c0c09543c41c0c0c00002c190500b08828041c04c1e4941c40c044220003440080040c4080c001c880e08000e41081c1c0240c1511405e0880b030506140e82001c518050340d40b5420000c00040c40d0400f417044907440041e40c0c0e6106040c2590301012000500040d20645025031a0300004c07001d82c1e2a030b02168020a0401c11400ca0114006021413122 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 36808152 1250 36806902 36806909
    0x908040f0b03010b0904020c01140117010513020a060507050a08040e0103050c0d03080a0b010219060b0123030105060a0c06050c03062d092502070302040b04150905060d050102190801 80
    0x200028001004100308a03000c0d117081c0c1c10b0889000d40c907500700d20b015a0041c0b00b9003800c880c402c080741000041d445521409401b011101c82c00901c220343c0c03001e0300034440100303131000213421008180c030401c0110301c0b078000b41c01c1c145e22910554180c4001601e8018054025400c213181d101840c8004000700042002000d800207002d51314403c01e600c2c10b8a0140030114010001c810303503070700d814058500f42e10a010482a0301a50303c142600d203141414548010540c0390032807408039003040c00f003050004020000448900e988075009145a0030306050003619044440710310305018071019984005446401114816605401d41d0341d00c80c0b170450100490b104800c8040b1882000501c40860107855201140b05c6c21803050300d002c0065118141c0c416101c52140d83e040c03c141d0b2812900b000080c3d03020460208890084605000c840c860304204004c40303c140c4001e03480800c00318010800016250046540000018028055400c90780c0f19142603a000001542d2110105107021015540004215002d03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 36809402 1250 36808152 36808169
    0x103030216060c020d0204050a020403080f090a081f200a02150a021309090f080a030e07050a15030b010908031303020a080d020a0311010603140604021002030f09060c030d0908040f 79
    0x7a900b0f507000705104102012001e4043c0b80c61f81f000072481d40c075030b40445005591010b5090364642c0d40c10b040c01180c2d00005d9080e44550ba11200004007041d0008014140988062100c0c00c100c44019140d0000c101401601e5200d042090340d0404200c0400d015100100f4103401401801d01410380c06180188000c022081c0948144900143e01072420030120a85410b0140060030100908100e000d00c0d0420703100600f50000020340e030041551540054800150300c108a58000b61500c0c2000001c20250260340246a01e01e00c1c1c642c03c0c244690044000000181019681652900040340c25503220383c81d014811035842200304110300700300745a24014000c3c034003e0881d0185100000317440f880300000140c1008001e94115485507400e501207002175500c02e5448100c002000c1c00603844120450b4140d115881d55120420114000b01c100c903101c000189185150480d514200940c40d04090743e01c505a1006102000040b41d440c814030b41d8890013800d456884520704140031320020a550003d102 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 36810652 1250 36809402 36809417
    0x10b06031305070501140d05130606030804030506090a1e020f120c210a03050a030605090f1609060207150201060306020301080102030610050906030f1e190b0a0e0c0a02070905010303021606 83
    0xc140b400b850987d08205800704011605844034140d0804040d120f002c00b404142c500a000810080a10014000c030783c82007003070351016a10250100d445451408014140c0303603940101400d4000a8844009410701c01010883c41401c03240c04101194900d030700818603540042c01d40c08035403410784900540c04044c09041c6524503010b0f03000381c0e200e0095100c02400e0010116803098098040e8001c10301514015110052a140001d0004107101042d103c514105206000e44880c6600c148581c00903035105800600e41a46090380c85015185400700d00e20443d5626480400015a03500082d80204084400940c4900742042003000402c411084003007880820442e003400354584605480d806044d91520341c0c415034803800540880030788900f00200c2040203600304001c492038501d0040c01e42241100c108146c0300d40e5030a001c000c900c0c034000e5042c03424000c80012140440540180140314140c416601c1d101c3e86e5031860002d83d9003c0c1c00840168104200c06882980c1915039200141414540400e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 36811902 1250 36810652 36810677
    0x20a120806030c091009051815010f0b0304020a03080d0e060f0403020d0203040e0a02070213050403020703150207030903060e010e0703110102060a02040b031303020f070b0408060702060402030d08040203010b06031305070501 98
    0x1003082001b841240720698692001500b000c0788690342c00c0044503043c00707445601a0300312800b9581c000c2402072030b015110440010548009081c10740e40314650190807209480d0468072030b50010b40001c10034043d940c0e207407400118403000510400303002d1001242500001e00701850040c0c00d00c0c0c0489040c004542c0148820006a4003914000d03400c0300030050010b94032141400803e40031102d056000380c1450418040c0810580c0c0090b40c80308032070188a00300960b9034060312a034264403900c140507000425505080c4041000d99000c100d100c4141d01c0006003081c0048286424107034545c2c070a07920426003003016065035805200066001c1c3c4409411443d0a00740071041e082c5000c0646a400c280c0c1e10386c0c46100c2018000c00c00e00405d00d40c4c4d40e040303408041d5948007181c0c0c1540240141e1102e4014140804e052500010381c081c09a94001c003d0616428962402c032000301d001001682d0540d21104001225190500154000c2518601e03040600340c142c2081440d10b0704a500440c101302d64107030441c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 36813152 1250 36811902 36811921
    0x6010203190210021804050105011103070201050f1201080d0807030b1c02030a0501020c1b03010905030a0804050102040510030b0913080f070c05100215090705010915020a120806030c09 81
    0x180c0d140340c1d011288460305181a00704034508800b44038070314009480000c000e0120303141600c011244203000c650500480c2c0e280c20045542080c4821846080c1c2d10a110301e90066004030301400094001303600117030078420b8220b20506991002c0c3c0c41200b0f0358100819100c00c1070351082e900c9038172071301030301301844042c07035a00128035020010040000c40c082001012802c664040c086980215000402903441d00060610903840724503100101821004607105140b090606001d860328864019000e14101b400b2808240c6100b1002441110555400c01001c180307541c03034403201c055611403680c00140e1022840207014100300040c0443c100b180320300382c40d4400214090212411000403021258682c801440c115011102d81c0d040300d43e20464811811070981c0d03001500c40000f809080ca00c0d17a56854040700300c0d49860641c05418002043c0f50001d00401c92111003c8240c1d081070300c103d030800312040c0c681001400e007041c1c2d101e0014044405006c40f40c5000c0008105005003110b1106090406100300e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 36814402 1250 36813152 36813157
    0x2060a06050a0b180a060206060a06110705060912030a05070b0a0b0901050402090109030b0103050a0b10061409060c01051f0906050d0f14030a230306030c04050c040b07060207060c030506010203 85
    0x83c08290740740040d100190700f02c03940c441214494042d0070a00c0032611002d020b529594102c1d1002e001d00507040e40000d01034491000c0800c0003003102c010340700203401d02d030034005260310007142d20b900000d6106540807907901c10802869040c030183d442544800b0140340850007404080c9c000b20000e1b00305200e044643d039805000d581101d07000c5400507a9a020000141d541c00c903a030740045c140c01460000003040c0800031a030a20140d10030b0f11501241d07a103a4a09010601890140030005458041d2540924000034001e2110300c000a00043c2829208a03c107801d5039021a0400f80c50803d05800a000f800c90100c08006000122810f1113100d04107804a11446060362004c0c012100300034030782d000e004400c030182e00403407030f0041941c1d6200340c00000500149180100c005440460148505402c1451000d59028020040c06002000e10110800c009800050112007003040c0421000403400d0700907000748125841041d000d41c0351034603820900111040e00001c2c0090504100800100d03030b13400f104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 36815652 1250 36814402 36814409
    0xd0b0604050102030a0c03110a030c05010b031908090a0905071d090108030703080406060b030903030906130c05041a1002010f0e0303040c03020d050c210606033d060306050702060a06050a 82
    0x20000c00c0e036503007401c040714442a80c0100313180323a001d01c0f14441d0525a100c1000c94890340902d0091101c4400b2109040d81e50003070a40800c00c00134050301a0000030610401058800301c014401d4184540752050481120800e50b040d401040c0603d51032000707022158600c901d4110101e605868941c94400310310303103d204018008040004580000742000216482030015250020115490340380018801e40d076640241ca00b05a58401c2400184000f0700312048400c800ba8010350b0f41c105940343c402848041d04550b006030170b104050f081515060385032141e080081503020f0380085102c40c0041e14a00c01c44aa0000c0740c5140e8100b00200401308d00207601c0041220360544101102c2d4600707003061401c108880d04843c0c0d0151b4458082c10b444c0d00b031981d1820144c04140d05440032510f4003410141d4500c0c1c90b85807810441110072040d100c030070310303010107882c552140111f8403102c10029141d003007216901c0d0012200c040d502d038240300d0b4840d0b0400c4101c4e0b214802810400c000c90600340045c04e800030703920 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 36816902 1250 36815652 36815657
    0x1406091006022116030c0c0801050c0a0c03031b02070f090605031b0112021303020f0d030e100c020a080307060501050a03030903060b010c0212010506030c032a01020f030d020d0b0604050102030a 85
    0x4494100b500d003042100c1d186802008140d81d407410300c0c5170080c0780d202811000d4500b00410400070a0801061103030300e014810000b0070304e1901303e810b0702c240e0306a0303007016042c0e00740360703a495881c040e110306408908001205680070b404004d050442c803110103103140d0071059031945042424000f5480001d52420b50702c5070307198000390440c0d08500481d071407854081003100880c00032544081c0070036141416004d4a20031038204203061580020300c03583c5c07221402c01070009052a0100902424641014011496149081d062004c4c04c2d4002c203008140e207902aa0040e80002039140070302c202481201e000d8201250041060342c5192001000c04500e4040502165651000c0383e0584e0300860136864026405080d80765a52070b0280d01c107000f40301c01c480300ea009000b05880900f00389404120b03001c01246030412100207590045884070143c0e24407a1040c15031144020440c04960100042c00102c01c901d20090b981d0140525520199a0161002c80c0550740c10311003440f40ba0b03008820388229031084d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 36818152 1250 36816902 36816943
    0xf012009060c0f0a060f090506190204050a030807060c09080d050c19080703091418060307030611030108070509010f18060306020d0605090c040b0306010f020f01140609100602 77
    0x800015400c1c49846084446842480c0010030070f40700c00f14402084500807107042080b03071440b80f40103068034280b0030700402c2e68008400243c10000300c1203210b0f01704261202d005040039160b402040013080c203508155410707400030407100c2c1000b9490240c4003140d0020b1600800491030103040c11340e103034080e078540401d00401248540400c1010488064685042600e26241d40864140b1070f0807a170044c40142e0000e100100003180f058404520228140409000d40c10040701a48034016a00405442550306003d10040040418803e0180907000d000302c1000940d0780d450444002c0c0b622044e903200c0c40c06410641c0c01081a10b0301d00b40f0482c02c17204002c243c0c004016800c0541c600034801504002c2c600f0781b02041c440d15054850f8002419103006440482c083d842e124402595402144140210100c04000103100e80d403240502d503400540500440d0130111000700f0340f5084d600a0070741102d49500f040e0800500d0318010300c10075000006407400c2c12415041c05802501c0d094011000e492003101c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 36819402 1250 36818152 36818167
    0x5060702060d0902031209040c031e02090303160b10060206040b04080a020109050a030305010611030c10110409180b0c07020a06140702060301030606050301200702130b06070606030201020f0120 85
    0x19908a1039019900409551b40c40a40085031041074100c01c031810700841c0781110360f0000302c1c042d00c0791103a44d4103031400c40c0e5442e020040c00c02000c0d6111070742c4036400d0702040c0a11104110100c001d214201c0c41102994003e14007100d1038001800598003c0302150301610170b0002041c90091507541064020100581c0e803814484160701401d00c03414018074038070458504109251b8594000ca06883c4699030b100030f2203510680d1155680110000c01500d03400200e80c417000d000e00d56101200b50702104500314206640e401001c0115004402c61039590304480b0b00c41c0741080445c1c5800b03944885a1900d0604100850700801c0d18100140115410b001c0d10403142d0311601e0075042a141e0056005040b1076480d81c403442d002011f0301c451701c11107000b5070038802c0812040d401a21501c0b514000c448116003056010b400b0040210510114000c0d016621a0315800d2500c2c1c00000b05034541c011000403544c40e01d503200081ca048510480804203034540700700d4142c008074414040088a20008080751034441 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 36820652 1250 36819402 36819427
    0x507020d020603070f03050a09151a060706060602070509041a040816030c050105150303070303020d060f15171302040902060d05010e010e07020303190507020a050d0e0f030102040506070206 83
    0x90000c0107944a0008400c100741160720422a201404150b0f80500481c1c4410b82454251210b0000040814500c5c0340d84200c41d103031561182c2c081d10303595481c07520400c0d19100400c100c0d9014030f009075000f984501007808103d404114020003080280d81071201860b040e202d00c6850b0208a02c10082c880c2140042400d0002001c180d03541c0302d042c48490440700c002840c01030030054900302c0c1120b45500b400300141d03d0300d090307802940000002901452410500e07070740803002544034140141905030360b40740c042003901c09420004060000389400344440b81c40820003900401017000c81e050030605400c104000c1082c0750000e0b0545503416200410b00031810f2001441500440810724912031410000198840b04124914103c8400300d80e650110b4568030402c9882c1e1104840d0707030042040e21661a4841c207140d074030041c1d002141d40f066030202c0d1490b5070796506182401c0000b40010301400c014180d41c0c034001c00c0c0c0203082c00045000b103107070900c3c1401080580c01100e0000c0d00c1088c0118030700c0410203 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 36821902 1250 36820652 36820669
    0x50702040b3102040602030901050c070807091d060c0d09020a0306050f011703070308010e06030f010905010615020a12030504020d0807031d0f030601030b07030204030516090e060c0901050702 84
    0x24005282d001808200305a9003030b40c1c50055200856540014407101045019200b203400b0781d04564040d52600e401d680040d02c0c5940809112551071141100c0082c01000602098015140c0c0c448080ba040344441c141c0c035207035032094680900c150420814048001c1242c8126460450309040c0820540210b00000e003445640f41d101404680c2441c080101011403942342c641607910740300c06416124242c13000e8941d24004e207200200410160300050040103e00c90200d64030a038010101c0c0d210303a40541c40c2601303440d0f6030361048415a44515052013402c0d0152141d803180d0205100801400001e5105d9107c0380f460244100d043c580d40d07802203415522000c0d5540050342d0230140c001d80c0d415071440c00400c0001103442800c58144800da40308038915000a4200018000900400f510390844d1035583c0201805004102815420040000000d0782806504141c102c002d040e1a401e83c13405816800381d071840620901c1c243c10003001c118500c82010f0540704120428a0301503207600040c03001c1408070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 36823152 1250 36821902 36821921
    0x180f01090905071116051005030c040306052502010b01140a080a0203070e190602061503030315030c100804140703120309020102100204081b060c0705040203040609022115060109030305070204 84
    0xa019041c4220203e40d200c0801780110f840c01c1e80d010001c040c9403802200c55000684070220f01c410100010404141f150304010f8001c0d03000c000d040110314016201d0300300c10038483d1001d030140c1d440300003104071980c01c48134200c050008107041910340b8000a400400708000204103000681e03021002c80c503880c0c0301e00c10301403154002410310b03845100c040051032042205482848010700c11000044e680304041040e956458801400a60444c0ca400b061808512078001c0c03813a40610448500280302d82d54040c420079181480d07101d04005003850308181c900c1d041c42020301c1d40e0780d611482041002645010385d6540c1c8080728640001c150b101d48c40101e05091b82c1d810082c20047c008940480c50b032074041002484480343d8990902050110b130b09001481c001e82c00d2005850301b00d034004000a0070950001c65025200319400500710440341c2c00a03418480523422490900b2101c10211101c000c00c014060300701010302ca60b52460f19203000002c0900ca001d002c000c2c02c00902007140b90464903180c0100107503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 36824402 1250 36823152 36823187
    0x50d06030c0303170907030c14150414030601090b18130209010906080c030a11040f06030209040305040303020f06040506040305160501050a020a0f0503060a030f0f17180f0109090507 80
    0x20680e0703803c2c0180548424064441914942408a50041c40004010b81140e41c00101010a64030749440700c0c0c03022180a080c190840c24001c50400c0d401c003e80001d201031325001d1000d140c20031403802030503d8070405802843d1282c2c81c2061040341541d07190154072009003001c4c117081e01940c03201600c122840f01a20001c2d0030461100c004640d545c1c96400000c00c1c0e0700528201c07900310042c64100356882262800c09031500002004920f803c0c2015040104c0813813038000c01046141e525404110203803000c84003500080d5002ca801d108050307050052213401011a0000c001a0038162a80c6841d003001900041c18000009525100c4140b60501e8040250300807000b04510b1402d80c1d1090041e500c10200d071000190440c9003127003c90700903010740e0f0007503030007600402000d401c59440c00c0e100d0260f500103031407030142c0510002c0000c08080d008800700c2e000364144c0b5140e01034a80001f6914032002c040300d100300320b201c444e01c1150f46d0100c849412980348075000700c4c00b5200c200e42660200b000c074210058 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 36825652 1250 36824402 36824423
    0x70201021c020307061b090303030507021f06030b0c0c0c0121230601020d05030f060f1509010e0d03050319021312051b030706260a0905010c030e0a0201050d0603 71
    0x6107507008030140c0946400740384103010a4110210202841140024200100d03290500620120b8869842243c0c011410b0040f40e0240c2220060180c0e0341048225461186844c3e81c014030030011403641c510382100808801030304007406400002d0300e5a011500640c1004006006442d50347e00c44141e64405001000341007013900342120b01680c4400010f04600c8a01c0d42000100701294400079030020000702e1507035903900355191004e50507034091000e4051030740401881d043d05407966404490300e41074101e0a050b00d035100310003c0090015031030322242c1886900001c007070201190700182102e501c00700c0c034074a4046410401e5581c800034081e80f04001c00b0005003840104040c5800090320802c02e0045003103481c01804200b50040803c0403040081e010b0304110410404603000720300c0e84025842d60400302d4500e801c409442c0202a00480d017039403032903499500707003814400c0a215007000c03d4041d1034240007007103101c4000b590710010710074000d04210b030018011581c158a44d1042c005554008108c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 36826902 1250 36825652 36825703
    0xa14070609061e0c050306010e090c040e1f080c09040f031106011401030b04020405012f0d0c140a050d120b030a080910030e071a0913020a020f0a11040207020102 71
    0x2c00c1e84072000c451454616061485041303d009109503841085c0583d035902c85480c410741030156035103003c0c0601c041030b08140808500c1c0b1003c0c20300d5620900016050341c0c43c911902c44200209440ba60010450390400c9007040440d45078000000e9000380c00c44000e440a028903d03040f02c555403170740203000003070082c0ba0022412400e03041d180c1e540c20000340e0782031002c1814481004101d1090b4810700d400728800b1200680300190320405800300c14042c3c2000c1e01c0740989101c0300c6081c80c410381d00680005180c008141c042086624890f40c1156030070b00181110003640e5110340d640c491000d500d05c20b010100c02c500c0301518090704001c00d19403011341034640b00902460581c3e20364000184480c407071000d21800e4042d840c82446a0f41541200c80c0c000e010003490400f100700404914584403003550b2080019040b540c54030034854100c44100c0d140182e40d2958204001d0a180c4010f03400c801542190071802c0205440141c540b090250858005944552510040c1d28100c000d148202c01e002c459940c14 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 36828152 1250 36826902 36826931
    0x100e0408030c09121e1002040f0911070b091c030c0206010e100503071d090f100b0f030f060403031104050120070302220f02030106050a080a2d060501050a1407060906 73
    0x1500c0d200c42101110102c0c545404032009074040c0e40202c0802070340030300c2704011405060f006441c81e4500790700300c14070388002a00d40d01051a411154000b003580020340f10040740034840945600b181d12880e041140c1e400010000b503c41c4410701c01c42001001140100743c040f003846403090000d05e00141150360155944bd071414950000702809140c07140640009490404082032100e520f80601c030203007000c2d604408420700280014000260403180c10300300b840081e02c1c10002100d080031040000c0c1510714140c038004081e0f804403656102d508805010400460342c015854000c00c042c050201422544082d90303903441e1100aa10103984803000c1c400341000c848400c4640d03501e64820306000c0c044144404004801da01c0b0a00c20000054000c000c041c1080e44a45011508404c481d80c003c0751554a03100503407010746900c0d500c0400c1d00c1140100749503025052103181d004180a0030001d0522450410250032110b5000100400c0d0000180f50f8080011a5200401d131961080301040050502c02c070f80b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 36829402 1250 36828152 36828193
    0x1020708030c06060f010207030b04030c08070204020301090209130614090603010e0d0804030306210204020c1e0f0c15030c031e010f0603050907030809040b03070b030c03100e0408030c0912 83
    0xe1340c020410a04402c1c1254808a411001c0d682c1013418500c0c1521250380c00c45180881e1740081c2c4501105004040040c0d0361400198000c00d4468805038881e00d1440c20041c0f48103440780c00303000c4a464202c04000801100c80c1080d00e20f00d040328032030070320341d180c1021078050300c0e199a0110250007000c40e641d82e01e5800c0f81003e40154001d82d800c1000d1078940094020500c81a0f03c0d04c01c49190701c4007820018038103500105640f60280050b540c030254180c0c1200350051101258000980242c0802e003a260b90030440110082000c0320350b54441c2820400c2c00c0100c2c44040e04400c800c0c48008001118504003245141c5021403100311090340d981c0d00c22120100a02d2401040000703400c010214240000000c0c0000035a0b42106c08945821000410000185110325509805000d91480000c5269450300074601c0b0300c0c40c0401281c2c0d40e282440f06215048170540250316011404000d0101142104c41a2503005034500503885c0e40c1d1078a400010030703a0101d08651044d51007801c20660001c684400c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 36830652 1250 36829402 36829411
    0x3030706091b060221090105091005040612140604090228061709060c0d060909080c0f03040e0c03070c210e03010c0e0904030e0a0b070b01151b0201020708030c06 71
    0x110716403042d07100c45080b41c0f9001c03c401c450385c0c1c1e4010803004d6a00c2071500743c020039455405041451421203148049040103100c1c1c03000784085207012034100401034203c03224000002440b84104000700010b220341a21101c0609410b015654620b2203000315150700c1c1c503200400d1a1070002618040e045100720900340518011140011510b44c401600c0304601d2042c14000c1040c00040c2131140d6034070645906075000541103040e0140c90b0710001413501c21501c90b0303403030983c040c1960382d03034450000d08c6851900c0b40461801b00c850340f0400c0708011208030a0149a04290000d014035503179210b40b001200c0740302c40e040300607042924840d0442c3d0380c0407200d84030060a4007540c4070300d41c003414510105400c0b070303c0c1d00d83d2402c042481e0030516000d51901d000c0080d8003600ca0300b0142400e24a840210720421104e0300b0000c120707100003a96006119402034224014982064040c0c3c402124ac0e1b4018811150350601c25104c546060300070085a00a0002c0009044040100c94851072052000c41e0744078400e84 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 36831902 1250 36830652 36830693
    0x6011815180815060301021b01020304110a0e0112021519170727090203090d020c0a060c021908160f0f08151b18101d0105090303070609 60
    0x42424038107044210012030301001e020341501c10b5840c1c1d492411800042400750306541c00c11145416071900c8242c1d03291196207000042c0c0301d1601d8070f8002e600200130340303015100b411380480401c0803010fa1482541543c410b0701250940c40c003c0d2000c00c03100035040510644040000c290020555000c006064000c1c202b0782e1551142c5940d00803034284404142c541100094402d900d080e0034051020020a050b803130011343c03010b00b0341d503182d840080b03800070340e56200320f60498807140040319170401030401c107035004881e23029045140980250000f00304e508000e000d00c41e64a2070013030202da58442e240040c80c0312020b5407000248904030050014050082c2c420010750060046406d0791540d01c0c500075120508010711b124000d044a40b1207191008040c1d0044100c811203412000c4541c1c3c0140c40340080912a0064410300030040002d078007000c182d041708003d44850081c05103010012203c03841e1400b030800c40d54030b01140000c03e00314403c03e0005000203080c0801c0b1020040e146105104814460 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 36833152 1250 36831902 36831917
    0x20703030b1e060a0e010e0301050f01030b0c0909060d060912050919121e05030a0207090506121002030606042402010507110304030b0c0702040c0e04060803070c0e06011815 76
    0x1e090411070300980c82d04180c00400500c07180b80424003600380361059010504196900c0c0058400090a4031000c50b8852040502c0900420070070207200101908520710303110301820100c40300007103020110010105442003c00c500b181050080650010b818590420302c20b12895103d8513001e0a903600c40c13240d07240128500c4040c242011010325035a81a618920722503c04980c3d6611741c00815910521304666200c2080481d4000880420080600031a0341d0090800603140c582040300b02c0300d0051420303024070200146d403184824045002003074204407110041e01d17a01c941000c5070441c043d9030031050035004900880000da010180314000e041d00154001d0015580c1d4480031101c81881c6c2c1000c6131113500a11080c4002140c111145030b000485080359401c080c1c8a03000102502c842042c50400b113841011400c0050805010340701c0a060294001d501d00704865030380303104505491192400b0815240e0100301d05a2049020300200c488110f00749a9079030312044018820340020502d000880c811 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 36834402 1250 36833152 36833179
    0x41d040c050d0f110307050a080a0605070c0807170c01021303201804020102010f0f020318030f0f0f130303020d030f05190b030c06030a060e0109050f0712060801020703030b 76
    0x405596034150703c41c8005060303040a03500c4284190401000f03036814006c45901040544500d0103c2005115071401480d0042a82c2492000c452010f000a81002214081c00c0c01080540044480b1030b54011541c18085e81030181102940c09102c64410b900d500014520340305510954448090381c0c095544080ca01c1030500880c2810114140c1490700301c2412102041656401d0340c1c115401401070001040401410b40450200c0d05028800b050303440d4040107001055559180c01c1c001d0003864002145821100c4401d107a65010b0940205008203002822007032006c00607040e150170941c140400c1c0540c6850b803501940303d140c245400390001c2c1c81d09004001150103801910301600c003405c5000c01c40705600088402404000710961b4051080e00510aa00d440d11401584180580c1c04009001c500b4280e5030482010b040c1c0c8004107041c2820203002800d10080c2034140c00103514142045a5440452070501401650344801c101d5403000c9404020b068058000744000841261045801c0d0103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 36835652 1250 36834402 36834409
    0xf0303020f0d080103290f041208071d01030b09090609100c09050114130f0504060b03060a05190f08010b0f03030a1205060a031506051507170a05041d040c05 69
    0x38040702d40d80019a40401040071450614070070a081c8510384152900000310715580b46460004e41e400000e8010550402c41441203014041718141000d25100c151410400d000a000d1b200001c001c000f103541c13042c4200c0e8030ba030003640400015600a0854201450310010107034a6050490344001607002d60105a078085404c1c4c812642c02080703540720580f445041c4001141c40d180c0d60664500500c50420400c1c20020461201c0d600038982ca03600ca4610505000602041c1c4070107601146400c0300c2401441007603620b00b405070050b100d060b10b003a005218411070340304500450740e0103003801940c4000081902d007010340150705c20000a48184428083d201c040c1030307503441580f140301c00040001d4100314004103d508125040000188003603050344c0c51380c484090070703120f07582c540310081d6660001300598203044540005640c40c1c0c0d0091410030003035071503141c60034007450014024901c0006d00054164002c4003910b014045a902c03908400010881c164002002501c0c2900c5444a100740000e031441e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 36836902 1250 36835652 36835663
    0x110d110c0a15030c1103030c03040311030d0c09080309060708070201051b010b09070912030e030102091804020411130e060d14150c0a051e0c010c020714060906070209040f0b010f0303020f 82
    0x1700c28004503e507982d8001980c8007a003000c1c008404000d0601c84c440600e54040014141301d915034200003c03042c07103c0c54060514a110382c00039055400500c82d42009560343e40c140c820b000d40007001d2a659585c00d10040741e842c0f044404441d400840c203c6910b8440c14158041505c0d90820f4554a4107130f110240140c6a0410600c66903400810039000000042c0c400c141c0c0700021140a40050b040492213000604428454100c1d845038005103810001940340c0f500401100780c445004c12460500f00c1c514280b40309400e8003a040d0013440c07103008955140c54000e01100d1440d0404242112100340d5240395444032500d6503050f00500401e000300d16060882d80480d01c0c00c900580b205c80c50002e20300c04420750451041c1c010281c40d2414042d06500041c20300405110280702c2d03020300012820a807141000030100142c65018550a10041c8916100d00c81120201034045803034905594903403034410080302d4405401001d0100c0c8c01d000003101d0480b00c0340c03c01a40c1c425001d807941d418200b41900c1c0d468 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 36838152 1250 36836902 36836927
    0x3150306060f040c0e101106100501020a08160b0406050708090115090902030705030d0f0206100609030b06040207020301090819030b0d02010804170c07090c110d110c0a15030c 77
    0x100000c4404291450141c3c40b4030603011329418001d01206088001036421381c904040080802e0032450981c0005006001d03c540c00a041c500c400a4282400b0000b5561902c2c580000c010340c41c0000c607121005800f4000d041901c3d031000301204249021700e0200090101615544048ad2000021030b0864074107025400c114840085651070103481c10880502910842c8403d030303014000e1510208040e14244035540e4903200e02e032039450340d0000640009103048001000b0300712214140100380106680310346200b046a420560054540c2c40321000100244200c0350002d61641c46c01c0300b410b04012040018210410000c41b40c45c0c01441c11305030580541740703c6520140d1040c8080200300c010741c0144101c9801900900c1000b00c20764100104d40c80540c80380303e645129070b000e01c404011010b01400317203090340b03101c0c4d1400b81c40e1181c110414a40d81ca00d1116000140311104c1000000d00d0420008000091002171090030b910766100160043c0c50500d050100c000707814001041c0c181c601130f0300c001012 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 36839402 1250 36838152 36838159
    0x327090f050f0f130204050a0b01020d1806031d031204050607030605030a0816080c01060503070605040819050111040f09060f03021804020307030c03030806011e0903170415050315030606 82
    0x42e561602400303048084014000c00c0aa000e030340004000da105c1b4450340b4410a25024000b4581c071840d4000ba28200300110182c0410128150402c41c2c0f030404803d8034100c0f41e06003401701c1c08440b520510100742c40d48040406403480701040044e02400d1403000f07d80a28007071000e66441c3d0701c9581d401c80c1920894060190107901501c05074000600d000c000308410004c08556088540032681d4400b4142d10102584006070744440c001e0029140600201c4c0052055060991810f45803049880e229262102d111350207911644010341400001c0d04035009641d1500d00d01c90743d842d1680c841041030b003024014051018030f00040848e5088840300000b06a030740050510811080c1d103413080480030002002203070103000745240080081e47c4020a000650b100e52a280385614181000401d441000c1d481d2000091817002d000150700c1e00928200c00760381e04240e040520700803051036070382c484c403d40d4441026410641924a541769002d40654080c414902c04221000014410907507242000d883c000d51 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 36840652 1250 36839402 36839431
    0x1021305150a0e030a0206040f140405040b04031b06050106030f060503190b04060e1b030c09150609010302130e01050112090b060409150603080c15010815040327090f05 74
    0x81c2c043c0a0061107207120340c004c0c1200d040105903800f00340150016440010b42c410320340424868004203100f140ca2460b400d8030200b24030300d00b503110106005006480a818000b564401003180b9281040680c032144d0444018081540d503107034001c2c0205003010381d4800c0c180c50a280811140741c0800d4841c154004010f000c02c0e0440380e41c0f151581600094000ca40d03c0d95034688501000c8024041d580c1d0141c03080015040100d11041070609002c1488800c902c10010001001226080d6807040c0e40b00d134600365541030f1034120980040c0c000b885011050710344d40041807800510410f120080714107070303403003030342e484904514080c0f8403419292410401041389802c3e000181c1e081c02d25030b0000c40c0b40f070f00031019044044001842a011a09107070810740c0c0d14140000e02c1d24401340d04200c0c5014064610603050000e61401c1c08054032500c547d021080c00340d0440c00810149403050040241c4c2c000890321000c600003890410520b19100d43c800d688901e030910001c0c5103001c01c18800c2a1041003019420079 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 36841902 1250 36840652 36840667
    0x11180105090c090105070f050a030906050c0d08130c03111203030705090402131701060e151309060b0a06020706030609020306060d0c111603020a0b0319020c0c060c0102130515 77
    0x40765080843c00b6410042d0a02449001c00c1c0360400c0c0503540d0f800307400908078400250900a10f074042e00d4100c0d1052100030468660500c50020780481014813503d0120000d440c1c0514143c081c00742c4503c00350007148662004024032000804041e07100390b046400c1c0200c99030942410b51640000c50f0f00034003081051201c5401d030b003860b0300140081d200170b070541c205003625414800c0b0001e4080c3d00060140c4e658035018850107204a410b60781003080c07440c00c48400070034580061030321b51040c00d5600100d9140c0c0030710301c10040780e50401c6c540d5241c02001004016158075009546451074030464002070304150f00001c01d0f40162003241e0040102038072a51401042603900c10203001a401c8040400000030f41c95103500e2003d20010b0222004c0328800b0b02480d20b10300411238104401e4010f204881010000c0c42064181500b9807510039041880150301e480e040a0710b0350130100044140c13504040001581e280c0f003a0194000c1c1141a10340388100c4c020350302d60040c8502d14030a603008180c2c104d002c01036403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 36843152 1250 36841902 36841921
    0x12010504060501110304090908070605090606040e0f030d0b0d02040606021506060a090630020901020f010506090103030c0c050d0308040203010f271e0305130909030e060a0309020405041118010509 86
    0x440650227069400c4c60120303640d82c5c0d9070882e0381c1100c68041030380208044c0305080c5054020130303c503605c2c07290003040480740182c485a228880e4610006280b41d407070580030780d5505d481203840101d81d0003c004200040c0d4031a8040c0d110985400c15204000402c00000d8061808400361941401d00d40d841070185420041c050b17030395210789001030342c9454401ca61540070113400c081c001c5851103c0a00940c881021400280c40c0030442840645664106410400c4a4a401e850f082c1165014507114500032840d080824251440e03400c0f9940080901c1142d005040d01f040718240558426002003249802c00c0307040170111607802018040700024070260310f0720141c600d0507518042c4d010705403400d1403207051410642102c5442e8411000f2881c081400380204011462905c0102200c100910408800380c0d80103104401c000d45280c469680481d842d080d26100354402400298050000c000f02d081c181019040390a1290f810340c40b88042c44031b5421030b000e0000b43c8904039800030b00702083c02d0300d5802a8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 36844402 1250 36843152 36843161
    0x2060307020109060603050f0d03061a0f0f03010e040b0105090405070302060a02030c06040b010501020d0f0c020607060f0f05090c030a051203150603040b090c0405130b0604111201050406050111030409 88
    0x3001190f407a51071610200c0d403584100c0000b1841032009040d076040012620741844182d5000605061030800104450b0719251400c2600215500700269592980e0035022483e003d5145466a42e16020001041080b41012068082e0380225081007440c3c0e80c5504020340c00ca0704403801801d40e040a902000142000d50240008500300c0c015242804400c0107032601c0c2c00c0040324150782c1207000000401055030140b100d91096010703441c00d40030b0061040c05c00303011040c10090007409800d0010307040007404840d034000740c40d010070b6403401e001840c10224003101400c000d82e082c1140d402001985d1806280c001040c01c1c84030361000141c0380b01000701901c111550070080468042c4241889044010341c0d59000541c40360384108040302003400c0404125181c00300c0c80100500551408050001c2414034035107034420143d010089045699038540464090b009c1506200342c640004507507120410440100c0c0d40c16294251400c029044e6194011101300020248a80e180d030010030003405148140d401c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 36845652 1250 36844402 36844411
    0x201050a0818120306040e07030b04110d080a0206070906090503070e180304060c12091202090415020309070e1302090402060a02070506120106020f06040c090c090302150306010801120f020603 84
    0x302c2648201500c40141404400d25a0b980040d40c00410096285002c2c4a00c00c983c6140100400700d9904595907100e41103070242003c0c001e030740c000c0b441001640d81c1801c014002039000c0038181d140d468001d00603523140c2042d1640d01c046141c0c82c5005c5421441142e8130700807284009c00512203145003c0c4058010300c8003414802003083b00d241c89005420081000b0401000d140e036441c0c48001c0380c1e007402c889207408140c04400b000030900702080a4210080c550450741c1e01240c40c094281c90b1840e00494501682903480c554a0010080094800c008103442c0d003100d00d41000c101503039442800206401001e002c3c020b500054120204000d800c5c403034003070a02891280102c45826031150001802070304004030040007040c50100601c2004d40c1404800381c61250302004001a05007030395032456120300e070b00032a2030380c030b40e102c1d00d0740e061501c00c0e0084001160081d1402249540740d080d020801e52045860f14041400300000081c107443e00c100030b072841d98100c42d41d1a0030501617820000319500150 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 36846902 1250 36845652 36845671
    0x90d050709020708040608090703170c0309042d110a0320030c040515090f120111070501090c050904030203090402030406090204150312030b0307050f010c0c032a030201050a08 77
    0x2201107161066403005021403400b41c500343d504c4501d441c81c01880d03900010320413145500510004c0000840fa040080c40094a500003640c45001e035121541ca1801003150181c0d1045c20968100c131143e0642000d0754103044400703141c9000242e030850080584003050141900a5010868550894465400303e95003090325028000300c826031114000c0990025203d8828100e00000c00b04010f2502541c00b1203000c7ca1110311600300381103440001d541c0340c0068900740c0680c407804808d920000f000c4d4003c20050343e8140021b41c80c1c420303a05209008140303081c0d00301ca40311051200400e19240c900c4419109540c15030003107103406408004d000280d040904216500c2e5142c2c00340c2401a5602e0107110104014101980d14079491030034402c00140103484104141454802035061039100451284240e0b1070a4401505400c080b00040320b40c5a82c0328800b40200703240384d0020081202c9098004820101402c48151019200100035a424417610009000c10010006c2409942c0100c00d00341c0d00c84600c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 36848152 1250 36846902 36846913
    0xc04062102070b09010b04150503030a080901020405120a050d030608100c090b0c0a050c0603070905040e1203040f03030c092303010b030f0114010b070c03022b0309030302060f0c090d05 81
    0xd5880e00c1e5160b0040c2c07180c01380341e511001440c4050902d03100e03680b501e45018596240d80303031404e008241c4921482d00350030100038503030000030301c40102501190014400070304034104248040307825684410035005c0846040c020400b0a40c4030303921a001d4007080d6400b282c00b8120f00607101c80301100414500200006110003d000000c005420303101030988007400501034804640d6514046042c90a1810868468842841440805a8803424081c1550300650700000d81c0c603d455020703490407669501c1c0303000800f0000f0404c0b080148010030307d42091f120380c40511600c503103000d058503040c0480c010310b8180e00c0310108411009001c24001103104501800000e100021000400d0804040103240d440c2c81c0e449007402e800340343c240e0b1022401001250345035420016256105448640d0350f12000e4400c0380e25a084440b0504951103c0c1e82c0c4074488000358451982c01d02c0c004d044d60400703200503409405120000741c01801240540d03031103045040e8a05241c01c0014040100c0c2d01882c0a09845600c1034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 36849402 1250 36848152 36848167
    0x10e0c0301150207080706050306130c08150a0302090114130204030203061302010e0a03051b01030b24041d010504060608151504050301110301090c0f05090f010c0204020307080f0c04062102 83
    0x188206e00c09041030b41d4426940c0e00e01306040c02040104042c02d04c06c12442c101d01039006039405541d064000c240c03841800c01d00c5014000086402001d50000307036100220000000d000300113030712002d00340c0209032030291190400149640480c051480f010390076030040c40c00511115141940700442d103105040c020000880a4042400040c1c04d070001c44459000303020210000d900d5000a2084d04024602442030000490104042040d40d80c0342042c10070a1003c030303540341e001c020195000380c441c43c3c0d2050440c58107110b61903801d120a100781070140b0725008020a40502c14801d06109910401c1c84169400c1135a040c05035031002087e0325428207109000100b420382c0c0a000711204200d400c2d071322507140c0d410914850f00711541c0880602c1803040113541c0703c50385a0801c00b51080c145080b50340b50724090210b03005807030f00c403c1480d00a40c450f00c00001c20400b035800c141c22a004027500003400c48280d0340c41905145601c114022800424102c1160f103180c000d003003200c0c3d02207040c40c10015040282 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 36850652 1250 36849402 36849419
    0x4060207120e040e07030f061116030c02090112030c120905031b100c02090c0d0f02040303080906011403150603030c06100305060912090111010b09090a0209010e0c0301150207 77
    0x1808034041c8000752544820704014601030149049902645001d0b1122510795990045513400d40d2800030100f40d01c070f1030030782421001a0140c50011340b040b4500141140d5070714004050502241040744140300b0a80041000401ca101e9440c0c103c0d0316888004a100064481019401c4c4081c01c02d000c10034130a20220300d80d24240507400900d0321068490040c0da82c0142045030300f05000340007030104420520010056903c01441d107800140d40c48806642d1006110301d007015002c1e00c034511070820700000d0f0020402d503015440c01c4c805d400904c15120346988442d00c50121040030701201d0f0b410ba00410741c1d11200d0820318125a080100101100e103450a00c1f0b50443c180b420440d03000c4146202c21000f00280300742444040e40c41003201003d40314a92285030002400e02840000074100102032202420780c0c05c01758000c140d01c0d07400800c4945c003450207000302689c0b0000c0140890003000040000100490b0b00301c00180100a000d40071819a0308040460312000c55120500b02107100d000f00000d9400d8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 36851902 1250 36850652 36850673
    0x1060603091401050f0f040c1d07030e0a021e06090418140613030e010c02031b03010c17010303080606070b0412080601020c0a0315020c071502010c020a03020703030804060207 77
    0x4420385022811420a0500e541c0502a45072401203c0c4d0500341041469421010080d07440b2200d1007120340d46031900d09080103034240c0c41c1c100d90800c402e1100001d50004407440d40b0352088280d550140501420700d41c1e00c6440b8480e050000b90406904103a40381d6003440b445031810030100280c9030905200e001c400040588413500052080380140030400014020280304d811241c0303114100400d03060170080c420184420000c00080c04001080e628984070380c1c17141c82140c0d000d507001022500354081c01400c0d968910240103160348258602504480031034040c2030408004148041c1c202e080b0380c61924190303103400d4020a61a03110b08200b06400008904480362070145018040c503107442200c0340800360080030060501410f55100000d031104503596140c1c04003c3da540300501402d14902c030102c04019003e4a100c030022801031038000300d1460001c036401da4076803213103500900c25000e0b6132601713036203e40301282d01800603001428148040303401209070b9904a8803605c801840d01b08140c69444200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 36853152 1250 36851902 36851909
    0x90d020a02090c160609060b100c12030906050a0606110d090b03071b0b06090a020f2a07080604020f090108060a0e03070c0305160801050108030711030f010e06100602070501050703120b030106 84
    0x564484916081c800d1034030130041240000e852840e40278004082c04ae10203c0039a40040000d00302000c1a0010780c031940044d100e00d540640c0034402e504140c01490b021b0300070780c01802c0000d1050511a216a240025400703c40da003152104850301c0c1c14061421115800280302c2d6040c0400c0d0b50340103030303960038908000300080e000f101da40e04282050400c10070b4022015007843c40050040c008802c4071f43d000c130101da0741c05d00c460440d480044100f441140c0e044201c00c000314454014808e00185069020031042d00c206e2003141c00c195080d00c520100302c43c0344828041c00340a64404400141100c8203070b444a400a0481400c0728206189603485103800356040d0000c5405e03030031040c5011442020449400050708241000f40a550f04096800303540340509203000c0c0c62840081840c21241d282409400c800202d07400c02440000c1da541b981e543c1d2050140c5281240c04400600000c03000c0c800300300c000070380c1c50581d02c06281071402d4408541c0da80c14500c041c040d03e5034920440f15503907002d121741c5006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 36854402 1250 36853152 36853163
    0x1407120509120a020a03020f0309150c10020409060e090118170904150e0a09080a0c03170c0405091303080105090603010213080c04061202060901050c160303020303040b090d020a02090c16 82
    0x483c05d460001e081c42202d18034046181d208ac05622070550350418100f940030307c0c80c008292a07000d03802001d0300d0304104100045000e8400500865440101d41040b4180c1d890b14120185d81e440d962282401c07258801000300303120b4100c800000c00103c80405180f08418241c44650401046000040c12110003221001e51002480d4040000a0040074426400032915004006c0b080b250b4450079014803906d410700b030030449003450b0303041018061a20324000b40281480f022080c544480025020341c0b250050702d126034405000203d1010510107a03800c0d1a505646980d1b15900c0c1c40c0c03d00c4035404003c5c210710b515540a00400c1596503510080d00001d1425100034209815001305000403104981c00c00685501c8180c1800c1c051303200c0e1001c480d0b61020a290042d5111400030019041031140040001d1100b200b1800006069000000c3c5000e540600c4204420780c036069200da40e2025406910790140c0c00001d000409454281540795010450100385c514018541200c1402c0004540f0704850 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 36855652 1250 36854402 36854413
    0x81206030304030b0c07030801150f050d0207080408030706060e16032c01060303090501090f0509060103060b0a0f140903100b01050405030f0708060903161103010b06040b07061407120509120a02 85
    0x28140d014103230314010102d9001c81a000c45c24a000107041d0340c1303950304020901100250f40464280d0366411202e0f802c2d008030341c2980302c64503500d0003920303503009a0382a81c8807410a003001c0344051801074a103001e41040604100b10050a100680c094104441a900e00c0c00450b041e0702035102c82c005028010805183c00001c09a0031480c000c1d080c41401d07000281040f541180903c099030101021105403403044070171103d140e40780790040707014113140d0b0406030402e130001c0b40c4d0000e016008200c0c041c002080e512000502e42c01c2030740c0846940507020201b94141d0100c4c0301c1688030071903940002c010481c103143c100d24182d00c440103e454490b000448446035800a14100000b0300103001594003c01610051f52800308491282015681d511401811001410b121202103503825800400580380c09443c10b41c036982c2c0c03162a0000e9400c0000242ca0040c185103c07280382c80e21400780e0910031795484e111100c10059424241008240081110381203101d900e01243d8140031050280c000c0d480710f03900400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 36856902 1250 36855652 36855667
    0x190501090914120d0504080c030a02060a0506010302070c05010e0a0306050106021e01051608070903060507030903020c03070308031302120105010905040c141003050a02090a080f0d020307081206030304030b0c 91
    0x2c98500d00780c2541c00190080c041614541d44603104603007003d0203001c4085115121414100400d2007902d011110710b03c40000c01e90020b43e0085010743c4101c5412000f00201c0d6140d20066080c0e1141102c001c29151041c4070500c103e41c0100c004c000d160501901c10750348942c903903444030700f06c40d400c0c0c01500c0940c0c080f070710114403100d41c8140000401100b000a2049051540b0118071480d01c440204060102107030015603030318072071803d000c021070704140300b8056401c00000150040c444081d09038010b000303003005540142400201c1d02e0450ba0b104511524650743c28030680c440c10040501244e10101d20b51807c030701c055003400785d640070745803014000501341004d00e80b245001d07005030b00407030b54941c044141807070300e9840c100c518515240c542004110b55a07a2010140280714449210382d105420a8020900c24000500161249003100c2180c06621090f0000d036901c1c019150010141e800c1080082c2044500400c240c2d003000c406002c40b4141a1240e41e49004102e04549003000c0800c08210b00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 36858152 1250 36856902 36856913
    0xa0e0307240315030303050414030a08060a1d180f010207110108060a030c1202060910020f010e0313230310090209070807020303150f06041806050402130303081905010909 75
    0x403071888a503040412007901c8007540e03489101090b20014040c55030b076200003014001071500150b10500214141c3e07a0700d110080b000341c40d44e0000e079105402000805004150358261451180c2d0507030031650700b0540c541c0c900070045800640c004000c1e496005195040000100c24009400c4441c403815240009132032010004121000c02440d80e8441c45807094200041200f585100d8240c4900e044803007440001e50010400c13600c075001401d0b811110a440c170051a03507001c0340814117400c104009115111081303641940e0307806840e140c201c0c00c080308407080110545076440d82c1d200408003401c1d0402c400740c4c800000d00340700310f81c149040c40350b272035107242021032401c14401c981c00348450628240506204d41e009507a408002c06a201c0c1d010803c0864081d80e4515034121183d40d40109072503030300c40c1c440c0c40ba0101e0765840a500280b8a0030100d000c40d15140500a4811510400e90750344409490f50310100c80082025085480711507051840035040e005038003905002c0e02041c500403541441c80c0c40d21 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 36859402 1250 36858152 36858209
    0x504090c08061002151504230406140105011413030501020c0703030f080f040b0a0905010c030209040609050103260d150302010e040c05030c09120a0309030201140705120a0e0307 78
    0x2c0d101150050802100719200003141ca50300550010300301c40c980340320540400c00401c040c00040207620510482c0f404031701c1d0741031800392080f48191000c1c400c1c0110032f480c0ca41005020f00400340451100e01c503408400030107030b01a041416407100440041c030313a00d4031241c0c07ca070702042400445800059060051541000d02640c280500f881d00815a1914820045140c080980007d00c0d41010030042403501a05401c26042542c0004c020081d070003103203070007400a500000500c0d00031400e06c14000703542001c91107043d04076904100d01007096555041140222140000340524000d0f0034000c1d074120745410704c03d40000c100f05d40e001e8070b20070b415400058080000181c003e0311890400c00e00898190340041502c1d003100f01d036041103859944003800a007013030030950b2108090b0b104403e0a1000c0c96481444101124000e0721000072440d0317500c18800340c0d031089042c06131895002c0358206510b455140003c01c040c400501e09034000c21850710000f800e103511588807a406400381c2400404100c000c40e003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 36860652 1250 36859402 36859429
    0xc05010b0a06090f0b0705060720060a020418060302130b061b0a021305070c0206090301020403060504080306090106080103050d0f0c02060a0201091509170f090607050102040603110a17070504090c0806 88
    0x1805d170304110b41c540e1407954840c402405007040100b0611480b40803e98100322001d0544010305403070746c41c0341407880e203c0250013030f10628030080d00744482244030b084540311b8034065036005031800001c4525410608050840005480e402650802c2407040c544546151007028000d81d03c06004943c0040c0108110201c14119403003070a49010248079140ba007002d580c19800c0c0e4180c1c2c98603200d11800f40000d0090240d940040e203134604003420031040201ca400207521804040b03949501d9130b621094200c8401d50300b400020302d030754400b15036502c200b030140742c20241d0340142b0325094440c03504582c04580584c001e0250000907070b44400c4d00c4020403ca001c100505070000300c4003044010580e803030b12040c403e980e050401d400100015034007020f01c0b40710200c54241c0009411250303200b08c18070b4010f00030750191080c0000a442c110400c41414040c204482c23016216035141d08400c08103140180306030b0b60142c03942051041c1000000341c841c0316401600d0358030669880e000700c107140c1034051001d4030100c2c58 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 36861902 1250 36860652 36860669
    0x503070620160b040c0b0f04050307090902130e010b13020d0b03061506071407031202160b04050f1f0e03010b191a09041514090f070c05010b0a06090f 66
    0x12141500c014902e91000c0d400004100c840c1d161424508483c510603082902032400005140f8030380e80d00940100f04072030701a42250b010b40d0b500c0543d0021608aa040250b101201d442ca1105410080d04103c400c8a80c0d5400040d84071000c1e800103816010b40c44d1000e4610b80c000c2054015008144610507090320140c014200d94508941018241002c100d500b911441d4003207066024464414449031110340540103c50900e40c50b4240764051040b41401d05d00180b00e0b41c82c8091071600c02ea5070050440d5000908242407505000c1007000984e5201308294001160b080d06644002c065003040d80303a10100c8c0c5602200d4201e007028103080d51a81d0180a0141c103c1c10410403684405403a0b0508589090b903034411070003441c0512440380d00c1420709042c0e1060800c0c5110744140448110982101d1200c1411940c188455082c043c000074229540808200c0c2d00c400a03038828002e09002c6040341c0301e280001503201105000400c0305016030000780016a10035010300c0703d0045410350700054400003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 36863152 1250 36861902 36861907
    0x140f01060e0d0209071808010507051207050c030304080d0207050703060b0406050f0f040207140607050a030608061003030f05040b0f03040201081b0712050d020c010b0406090c050d15030503070620 86
    0x2500030442c002c60240a6108111080d0f0003440e13900c4031102d068002c0c1261f00000d0100d07007454007000700250407c20003c483c808401f00814490b03401902218180d60401c0081c43c21982c81f0345450307103140c0060b042084100d40030011440044e400348080d901551140c00001103041218041c4422130b0340e540c016600580068406030b00a40e2500040140d034802100c025a8900980c035000c0110148c11071210700b584254030510800d150400050006503003241d0b0200400d65860f00c001d49e13101d00580f00341c0003510482c14140301181c42941ea24054100302d05090345881da8442e034800701940404603481e00003c0c04000d000456900c81c0750160841c01d000c0c0160810102800000c1d914815050000c10b15480356800c02d89450240d825640c03a0680f482003192640f0441d04880d020b03005030115540324501e44103010880c480603109182007100e50b5038a00303007000098401c500c0100382c003000c5042900d55402c8000f00060b800c00c001c101c001c0c8150b00104154030809490300c042c1d070401194401c0384606 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 36864402 1250 36863152 36863179
    0x303030c0207050d02090604150b07021003140f0a1d1509010603030915020a060203040b0f07080c07080903030403021002030d060b090f0609130f0903090503010e030405090a140f01060e 81
    0x206000c84c01010340403900604991a5240060002c1038520400c0d044c0042c150000140d101000e0050440304d40242d1f209d079981808148101c1c100e038007600e0403000500c5008086051100ca000c20a540000d0f0074100140842001400f1806180c1c036280120003a801f448003050f800c6410f19000b50003000c2d1030001e00409086640140110115000d41e030108030b222071082820780d1007046517031500b07034116608540c1c134146801c000c0a100421109a090302110001007403881c2d20420315248940b00603440c46044c005259640306140e841a01031561500c010322000c80981d807040700a04c01c81303c40e80c005541d58103001c207000c0d0903030f0207607409018041010f00c0031205a84505100c0000040100c0d0300f10b5075003c00c3c10010300300d0f034800d2018000c20b13860308000c4013141c0c0c02d44d41300d40509806a20791162160340e540070075080c0c031181034101020382c20900c0100510704043d202e490b004040c4100101d178020002005180300343c003c8448140200400c001086981c2d0080c42c84100c0740810345100400480 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 36865652 1250 36864402 36864409
    0x10170d09060c0305040f12051519090201020115151403040f060e1006090c02070506070c090513080a200313181113030b0702030408070303080c120901060303030c020705 74
    0x44070321a0405020301404541c04040c464012240949130000301840b181e074039900c1080c81d0b41080d000c00c42e41442040541d4210302000d5140521580c00d803007907081484000300c00d6002810341640e007281591b41301c00041188101a01c00f91002d4000c020b02400c020f852a100241104840b20398401d03004030400502020580a0341251402500120081016040361540914003c0408450a0751903d002d4011a80c0f00507074000707215031000c0e43d080324009034581e0100b040d03910030110010241d60140004001007142c507048580d111001c00702d05601e0006503250031920f41d10041c0310074000b07000c000c2c07010028004d0100058001d0040740c0107505204200d44c2c0c0400310001c5001e8103a1490302001c403907110b10000e4001ca200c0740648000c003600c82d24040780c800780c108494041120108407220024015510000c16035003180c0da07000003001c00300d01c0c41e201a01c40d58405000900d0071403040111a01040102807014012240c400000410511b1401c0040c100c40481c0003050454220010400c00c0b5039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 36866902 1250 36865652 36865667
    0x40203011803091e0b0703020c030709060e010e0406061505040306140103030c0308091002040e010e060609030a0f020102011b020a0c050102030a02030901030510030203010c0206041a040804030b0406060e10170d 92
    0x20040c4e0500200c03a103c03031090704120b8107150320000c5002d00000b110001c00da07000c075940c0b03500700301a011198881d0302c0d01d02c2c400c2030352a01e01882003400f24801c010482c58210b5030000c1d41190054400184503621240501c1006c01000244404914005010020014a44545821414003404010030b550640c2d0700244a6400e68001408124100c404903507490000d115a144d02240384c41c1c11560350341d5030100303d41c2e421802d2280781054078207040000d60f64140390040301c003d40001006032140c0c0215640d494074032001c004080c0d0440d941c481e0303859203020a800203603003401720f80d40013003510020614228070440d155400282c1150014080b40200e5900001a640c0e104400d0138041071566503145004121612035102035403540c2031034640802c1c5600446c985005034002d42c0140c1e540103001e40c544600000c1520001c0c048003003040204041444400f965422510400c8085000c0e40e4500d2540b07016041601c1c0b20f000c07101c413050304000e1251030f150a050018070b090040c007260340540b4805040344 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 36868152 1250 36866902 36866909
    0x815030d0e06030702160609080f06070c15020f0304150507020c01020c011103070803070503180a020603041104090b04240b0a0506070309090c031e02161103010e030f0304020301180309 81
    0x5440c0400072409132402406500c00c02c0890142289005980d10301c02024099284030b49101406200351100c41042e01080d443d00c205010b480d600110317440e950b691701742d14989102000e0307807e07800c1c003200441e40741480045005900400c0203510b80c514111000c0c04550000c1c040d5402c0d07500c0040042001d0745c0200f00c1d11110102400c11400a552003040345066108442004003c50000001c2281c1141c11001650007416400007aa443d400b05100641d920381407880082d612003030520008001445060904609030b00c05800032402488646d10060805802c0d201100c117866400000001c0984004008850348420402030220307499400119024001a01800e40aa18002075100505d809170003504001c1a0b188401c0000314104003004005050800700c042280d07840c01d4043d10b11506a00a441013114200203109840c0b15503942c50a150200429140d015520b0311001303030045074140050100c0c62200361103da500c0c501031040500310313050581140c040350038115901020a80c0964800140c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 36869402 1250 36868152 36868159
    0x30f04021012050c0a020606090c0d0f0b0d030306050f061602040c0c0c0303030c080106030c0e12011b0305010906050909060a020307020a0204180308240402130909030815030d0e 78
    0xc80210407030485640500580d540c0206007400c09011280b032a078401001040510703800e0700c080b81c07101c00401442075401c1d92440314294003030099030700283c445d501061091010000000f100782c0142c020034a51004400e00358080b81d84e40300100510b00b0200009240d0318803c446083c0703080c0342d00c2e10b100e61304120b041010780100c0e03035034122a0f1800d0050040724103180e0131450004801e540c918009014101d420b41c00c40001d40e040303000040e2107000340512202c00b106602d03215003400c03d036070038080d0042c05484008419921040000c0704107901c4000d00a91004556000c0f0701d940c10300400d0340036548140c1c0b24030302a00003441000742c0280081085600070004400142e602d0712504022840c100c1c103e800070394490301e0002000d021840041c42036000702e104c2e0300c69541d19a2444811a0240158080784995000381143c6242d90f10b41940240b07440c400d1b501c0d02401c19501c41103410203c8036028002c42c00f01e1482000d10407107402c2903a0400e003d2001b10010182a021040014074004028004501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 36870508 1106 36869402 36869419
    0x705030307020603040b04151b1107060503011505040b040b0c06060405040506130f0803010915080307080405040f1e0507030e0a2307121a01080102030f0402 69
    0x42d0002d181c00c1c19983c4a03199500e84401c0140100c9003040445404039041009202d84118040131403040300b0013540f50040a032140600c44003192156121690411a0319440300c212819a41003034440801c605e803c8100751110f01903038001c0201c044021a020034807070f03401d0010381840c4022108913001d94941000b40000c03079005842c06480e47d001a000180008110840542403900c94145459801352548a442c0030390400c2e000b2401003900c034140280c0b5111050303002c1014040c1c2d0340c0a07514110b619aa000c54030f10403445500d0146440d80700054040b2040e91000064500e043c128003e50380350b510041c001400c0c100c80c6100420326105074016460700009000b440c40fa0f00c81d00d200d440d428000340c000040d490108600c0602d101e0641e01080e5400f5905404003c144145100d555821000d015000c2185d0140c010825030303803040c0b0800039401d050021042e0029019038a064 = true := by decide +kernel

theorem cover : BRFrame.Cov 36690652 36870508 := by
  have h0 := BRFrame.cov_init 36690652
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 36690652 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 36690652 ≤ n) (h2 : n < 36870508) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
