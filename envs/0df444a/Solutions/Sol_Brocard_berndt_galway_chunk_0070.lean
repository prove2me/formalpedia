-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0070
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:40:39.796078+00:00
-- url     : https://prove2.me/submissions/5a0da78a-b369-40f4-ad83-8ece943a4729

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 12410078 ≤ n < 12589935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 12411328 1250 12410078 12410081
    0x3020405060607080304030e040615120c020a0c090603020103050c07170306060c0a030c03080c0406050d050601020708060a0902011403160c080903010c050706050108060106120b060f0d050a0605030106060e04 91
    0x3009a58404000c2108000054130340001e10b000d140a90b1703031800600c407000d081c001107a15940245003281c550400f589840303680000e010144040f280c4001c1812004400242e1a00c0150b510080130060001d0004c00c56105541c8810110f03030003640d041c4407a8807054030039142d51149000140940c1b000380d2000c481d40601c10010360700401c028041502e000720000700c15041186400c8110009606084040145580300c4402c0c0e411160240141d0703c0c0c01c0c50100050041c1c03094a1b1444100e540f204006211a8008d102c1e90009101e0300003994258a0207580000052000320000c07400b00e002e11900706005440141524441d0302c5050b0600a03c484a120650705000c0c45101192251420046200541c07000e020344c00c1080a9600ea1988a008514006c8256001600154a0703603001c4001044001e82c00204180301c0d082060000540c84601004106c448c805d2001c00c1e010f44000060460780d015150380f0035445180703c0d8008202e03407a150303810035080c0c0700b69100c2c19000641240b15040546400d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 12412578 1250 12411328 12411331
    0x225050c0409050102090307060302180409080c0a14010f02130b030a0b0a1512020304110607030203130b0403021c02060406050c070f0b03071701150f0201020904050a020a02070501020c06030103020405 88
    0x1910494105401040c0040e0541e401041e08880e00d03500811600b000d130504000d51030190000d42020750a008551548803540000e002e50346204948840e050400c1c40301150444a5406440040e102e0b115a0307070802c903403034543c414280c802643c0703000000d000079416072094855003200218840141460300c1d071182074540014202d40e9000381c2d00c100804482ea9496503040003481405050100c402e1021005000900c48580742c85c20280100104030003c0c01c9150201b09031181245d8a6845601a06040740b42d40074007540e1140480d1440c2c404120380c140700001d0400c60341b0803100380401d514001800d4040c1040d140b802508100240004c1c02181d0258000c0c00505e0301d0385089032030701070307540300390710104182d5910000452900106116200794041c442c1c101d0944280d03940045545800082ea000380c000c40407040c1007025250386280c0b5103200390101e8180f044020018040b0741804840c2e00003e42c40240f122001d48580c0000242039400843c1e82c10442500821302c1c1e082d13070700c1c603000d000103040c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 12413828 1250 12412578 12412583
    0x6010b1207030e010608060601020c091603050408130e010509060607030801050f04090816020411070f02060901110a031707020c010207090207030302130e0405010b060f07020d03030e0717100225 85
    0x1110743d02c09010900c04d10409004000100051031780741481000a41880c1d1000c0095029004420030800300c80641048582c00010303d113000203044d038580c10030903c0390103400c50000c80a50720400021b4108041400e21303059600c103c92031030880d00c441040000a10030247c0040200e0003480c01000145800c141c031b00e080d450081c0c40031649410f107a88820056000075250304086810141d800705504062041210300701a99042c14504980358843d41c42400500b10001c2c45000d0001c2c05000c140d11900e0042d0740d07003035040100e654509503031078003031711100e100302805075515042000100e00300e00c00108032800610680207881d41e2400d0048504c065440240c0660506400b00152092a11a40c50314401008007034102901414035182c000d0a407448500035500c104818000301c5500070b07150301210381a9904071801c80c8240c00134074054024260a4010300d101e03002d0380c1000188001041c40e05d44502d40d499040d1803007000200100000c900540f184c1c11320786c416815104180d4040c503001010540e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 12415078 1250 12413828 12413831
    0x2040b031906021e04030206030c0703030b040c020c01020f030310060e1207170d0503070503150a0305190203011401150c1a0a090212060403080a0903030b0d050c01080906010b120703 80
    0x200e580c0100c0c07400080301c1004a8031a0350002d01d4480b01c64207800031401e05444012010314051554000036510301010b4079254455000181c48801c03d4081d510480c803025014000f4405d10341d5050001c0e488030145d03121103000d409000c0c0c051020900c040110b0741f00e440c00c504220f05160070a60102d9040003103095051b04417500d45041d444e83c070003c205660040c405407030030300e41300c40a2590440c02c1400f1205e001e024400d0a1080c0600641c102c01500d500842c8510090708144440c0001102103141d54070107401d0b030250039005059480e00201103039600340240c00a0180b00154003240b4804802407140c29185140e184040780c43c07510550000405030b018043e08042145110040c40c0f038541b041d1420700c070081d46d5042c400c2c1103062a1100401c0c241c119006072605213070a84004e029484000e004c1101d840c2c0d5034142d2006c044c06948042e84111010304000b0f807250304c03864001d40c0d600328440b4403408240c01900190801c0d0380014514113075030000214504000f40c41600103040031000d4107900906 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 12416328 1250 12415078 12415093
    0x10e0c0a050c0a0b010f0e0906010b0c0c0a030503180303040302030c060a090f0b0301061103033c010b030402120a030c06020706060b0c07090b010c02010507120e060f030106030606030203040b0402040b03 89
    0x10308104000003c060041212025951402c0d6910100303030135560000d142581484101700490700f02058081c1129058907801c0e5072051054441810320f0008103055030300a052a40c08400d000b00080a401034804ac50301545210142e00b080540c1c0c6c2c015488000e51542c8545006140b50074050003074608000c881c01c10f041c4050b201d6406a48120194000d1040c5d9036021004000340350380710300101c1c000029540a185182000314401d84052140314407494012980b80c00d1105a1410110000324035070100012034482d46c582e0070181440e07100b901c003039204480d80124840c040d1008580502d890340e03d80c45205038044c0f10313625403001c0d41200106451190742c0d1000000d46c1401d80c0c004065a0001c40c014100c0307a404c4c2074020040b03a050046a40c1007010b4000f034100140d0f0004201c032302c66a04a280d1004480c1090811a01c418000300110781200307000c581d10318624003800283d412f81d023103074805202140d120b00c4210300f28003045501410a010510116000d410b05510201034200042c0548025 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 12417578 1250 12416328 12416347
    0x108190602160b0403030c030b100f0c030519080402031507021e03040302090117060f010b0f031b04080d09051008010e0702070801021801021605030a1209050301090609050c09010e0c0a05 82
    0x40c850f084400b0350100361507044003600c5541c9480f0303460191104031b8140c0c02d1007a05d81e0004100d24410300c81001440786050f4050141806a0190380100200d1071002c0b032058100500103144641c1179030300700d00034812600740d0011900385e41043d038883c808543c010308854104800d18000c41c0c1010501c0303040d03800100404001340c1c80d00741075140601013914060b600940026000c514041000f840507004a401c6001800026100000c907640d4142121031140c42e619401220304c83d41141224080703078410300080001e43d2000c040384480c401100b44c2c852224241d82c4009001802c600c00c43d1010016032458014445500e01d80100c581005003481221a900e4407081c07094226805890101802d0b107044005042540e410080791040c10307024440f0600320b905d804042035455040c202c1c0140030120701400c0806080c4035100840003000020001d0010480702d0074802c00a00080000307a91500a10010301c459007081070301c26040380e09000e4401110358030f01100030f6880c1c01081e410010030204000b00c048 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 12418828 1250 12417578 12417593
    0x305090901091d01060513090606081b090705090306010315090209150307050103020903030307200a06050406050c0307090501181a04060908060411040915050a06050405010819060216 80
    0x19109580b030000302c9881401080c12412888550340500740c0c105542880180c4400360f8072209041c0c40b0f040468040d800d482c000015000d0f0347c110004d075204010980101d0251032840310a4020103640a058039220800101c409100d042320454165000100400000d1815002903002d4100c1c00d01c00511040180d0000d94020300c1520aa030400141c6043e0000740d01e414070001e40248402d003021460078210102083e160b000040c860000d0102d8140340000704000000c440e003100e00d0010903100d4440c00d03880d0000c0240802e5406448481ca0200019120703492881141e02a82c041e8440ea00030078941801100c04d000c80c101102403401c41c05400181d0010800303d44081000c0b2246100d49442c1030500080c05c000c1c02d60711810559024005100c0481c40e003000e60380c0381042c10340380410700403880e00389080c0c000018140d41030340c00c5c03034007003042040f030384992190080e100d0480b801d201c82d90740c0d100e02940c0e840e0750460b0100d143d51060034103400a44030b80d008007a48070841c01f03100051825600d4940 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 12420078 1250 12418828 12418831
    0x403030e01081e06010311130801060501030b030601030602090a0302060304030f02010c0e0102031b0705100c060f020a1b03030605060a020c03010606050906040b0d090f0305070b070c1a06030109150605090a0c0203030c0703050909 100
    0x4082a10402d07051009c4202809500c01401d000e180c1004100171000019513030324818170000c0e282c15400281018540c40e0071038500d020b5900a4880390766800c003482c0041c010000008040c00651a000c18176032154441d855000b03010105070700460901c10410700038180c3c50801c1810300c00c2449901c90004031034407481048034003400b0745e4882d4010503442d401c1c03100a43c1c10300849140341c90f1041007841c00050304500f005906440805001d039882505140070380040c880b035000755500500110366004659030002d04201007401c164024000180e85a5055541d4000d1268003076004c4801e00c000e0255070803243c007400c0303485c151079001308406180e0f49038a500481d001100350700180d000201801885400d4a810360131103501c0c600051343c1a03460b100e0001c00c10111910050f0301e03062002040440c0e034250040c4da00c01e5002000580301003043c51000c3c1c014000b500c910b46c043d258603800500040311f244210000442c10390040c0d803841d6212080c51809a04c000d40440c140a001e0000b25202e450700003009 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 12421328 1250 12420078 12420097
    0x5010803120c03090703030f020307150902130506010806010e0319030f0809060103051005040201051201080601080c0f060405091902030c040509130c0302040b010302040801110403030e01081e06010311 88
    0x6503900c10562119090481e4020082501c1c4902001408030003040041c00504681e0540b1346880202000f200403401c61041081c0030700440e600560860058a85a000883c244e10031206800c03007000c601043c074243c0c2c2007111018081803a840000e071581d4001d09440d42603500007402d80381450083d0080810035072a0b135500390001405400600980c1da048020705800c45030030001080e01d58959910ba665607404418400c401c141c6030703404501164058020b854022840758131081e510341e16525401c0ea47c0c1024401c03041039203d045d5600f01c0c80d05210f04004020400a00a1840c180c1440c0074400b90300d001801600401080c80d8640d90002c203a44081d502404207540c40690740d034508001c0140e101360103408040e40c905100b110600141d0f48580000440781c0c1a100440d035044464010703002402103030301c0f5192550814251490000b9220000e10542e40701c2d0707d0301c54645410100446080e14101d9032450311b003801c6000f4a0360709003036041301c0758003540526010800381540d5188101a40004168 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 12422578 1250 12421328 12421333
    0x30102070f0b15031f0906020f03130b01050a0b0313111c0209010512030d0c02070b1308060f09060103060218100f0905030105150103050a0204050607080a080a1503020105090102010f050108 83
    0x500c00e181600e043c1001084000310b0003000c0104103101c62001120221030510741c00c41d6598411010001103406480d1118218014103450b4a00030002c01e0004003420004c5036840201c81c0045080d02c0e1016a1009888104003650b003541c1d030b000b0500828140224003907a0407244410f40c0e510941d16010800d03540314010611415086071807040c044841c0f01030308507034822281c00013a42010703180001a241c44480c070000c00310304030311541c2c3c0c203a0030400c141c1c212500d2680d00244204080004640340d008881c3c10f281100d40e15503c10038000780305642038540c80010b411010040022a01c43d801a2401c3c03c040c158510b81e0403901000140d840754140310000c0403400c080394910f584c0e44c00c05030810003014240e00074481850403580540241039a40b41d281d05241e51100890f0006c0e00c02c0c0c1c169405403101030a46580c81040d81072250250f00080614000038401c1c80000b0800d41c0c1c0b60162103048009042103141e020300390350055865400c00c61010303045658030405580349494600482c2d000344080380c003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 12423828 1250 12422578 12422581
    0x11070c0b070b060907080a0914030c0a05100204030c18020f1801030c020606012a0606030b160306030506010302060904090b0a060512010b030d0c03050714030a0f1e0e030102070f0b 79
    0x104a2102c040c0201a1032240540104202005412400c6140c0c010000c0000060500903481c12204800300789010b2500d52001040e1841c002d100060350341072a900503401c4803500301941c05103001f0b034480c0d070000901505070003c0820410f10342490b00c00302141d6228015041c101c0040c410f0b0321359040b04102c401c1c0380300354107000c3d000c0d944c25106a0b608260144060079080c038080001a001410f0313140103c00c09030a4000d00d0a0229652040d8001541d001c0d0082c8000d607540c1c10454110741066401e0b80420b00d44a1084070003a00a125103001c895110b0068a9980e180d6000c10203a908003400740ca030400d0312503170010000380018441c5071060081000000d4420300b040148200c05c0c054116020943e032600040300741960b0001070003021a4071510b021074201e2024607044440b401b410030020000991203a41300c2a0003008405003080048640d50300d50b1500c100281101c42a004031011258001c0780c500c504c2c0d41900c00d0320108428600600054980348841d80c2c0c41501070a1120151000700c142c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 12425078 1250 12423828 12423833
    0x40806070e010e0301020a1d13050a0c0806060408070b03180a060f060506040f0905090a0807030305161412040302030427050f0c1b0a020d050309010306060201020c1011070c0b07 78
    0x640381400f00c101500214280404400003402e1401010b01008440241c8484400180c0c0c40e00107494030741070a000180714034102824982e016107900e20059005c0b50400d8005040c90508a06480440300f83d5002840007900d80003009055500282203800041e94000110310310040c05c2080a014902c01d000010b0404c10031200c0a04840b0260040d5118043c200400c100c0c00385440741d0103041d01c10400300050b05480d5440c803a4a0150300000050800d500442c4060030b00d0b801d0341c0170318802e00b10000031641025580004a500e043d444207034103a6041c040c0920501e40d00c401080171381c05842401201d203880c0c0c45c0c000d4a50900301c85c1c0c0905411700c401c0380d010815206030303000d1580c019071048040c80a600348189541510f00641c0c1d1848000c0040b01c80c04d5804000810001d030440c3d030041c00c0c44008100d1810400d403250310201722507001c80c1c2442c5000598038414421500c00c0e401c40c0c1c014140385c0c1d48116450303024211501003640e2854050246501280601d4036030b60080180078401ca0b80c0383c0203031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 12426328 1250 12425078 12425087
    0x302010501081209040509190b04030801060f09030303150b0d06060905030703050322090f050108010506010206040b061003090b15030d02010203090a030c0f0507090e01060503010902060901050f040806070e01 91
    0x507000b0301c03450b402038550030100c8004041036519105088401144aa03101c01000e40f42c103802c40010100c16901451036010b002c811003c07030340524000c1c0c0d01e6500c280c1e03c554083c2c03040001c801018002451880081010a11a03440780c800d03c20900079061000c1c2c0c2d202d203c003d040d0807168015030150348ea10010050160400803440060005a020300301c4031b0301e1038642940b40e000d82507000a90f500301601d01e65611046944110241c04042000c011501c280d604a4006000900604415628000114545600004045115581c454501c2c4280c2e61194241315000e0071440248050545405060001a248600051064100b480d00000e0101050201498074405551910940e4410814440b0742c0c00c0104044500c5900f60400312002c0e06180340040c80c000030300c00041d00394040c1c0780010a04440e0307600002a05248400280025621071040500300e45c0d400302c7c001d502403010040300d4040e5010300003614105580200321401d1070354a45815050917411a0080001074001861540315a0030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 12427578 1250 12426328 12426331
    0x2060d1b020c220b010216080106030b06010e09010501050a1403090109020306010b040b0a030504080f120105120c0303030105120106030209090606151804091106040902091203070209190b0a0305030703020105 91
    0x21902d080070081c2c8180c1d031011041c3c2d500c01000c1e04903116103c201e00c60b4020090382220580d854080341c061a07840c0300f42d50090103140012210f074100c00001c070b0313203642c4100b0040241c900c0050030225164070348030041d03800c0d500c10411942400f04400c0402c3d944c00a510103503200720003180000c01c404403184101410206c058000014181081c0070500916921406031482c00112b410006426142ca0410748210b0080d032200c840d0794640001ca9000550324084554102d80069820011401c1189580b45d12001d4982209070568400d00040055150100d41a03084074074020000442c55129004103400d108100c03900f90f441e5211400b804481d04040c07180d458040181002c0300d007440103010f000b00c6a00b1650400a2140791604e514005201c0380760180c01503c00014261a40d541d618080310002e0b4000b1552644a411800811804000e01004031514198024100c0c3d115954802c07003090b8180c0564100014255100c40c401031640b92080441d0180d40a0402580c40d00400d107802400e54a0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 12428828 1250 12427578 12427603
    0x61b0507051009020a030609060c0905030705010e06070c05090903120f061e040e0304120302070803031b0c0c060d020d05070314061011060106030e100209090408030402060d1b02 78
    0x800205021079400b1440d021008100e61000c20b0600260000130b580c46030350340001e01894a8440c0d4041000303600d500055110075562500445103540300308042d180d89040c03089502144a80e07084110500d08200205a021f00c220100300039a9118404160204402c48141c0620f6000090142c00d41c1100c0702810743c800368000c2140c2d8185410000b04103d9088031403a503014211350310380284207a4a6811840603101c0030070449880c0d503601e01e104d0b07095074007644003a009805014801300d078582b0040f040707901c81c45601c95602c00c2c408800c000c640b0340e17078008000100c00e4040c403544032129030340e008003c002c0515030180241c0c8405d81241d0600c12100301030168030502d445d051005484c00c1004801603400b48048030b20055143d41c070035098a2415080480c3d404a000d050004030b1290382507030114140b000e000c07080b100341c0c511a075981d40c100e20801840b80da1007494000001c4c00030f900071008541c02840541414280400810301e0400e0ba141c0f401e400c42403104e0181c0240040350304014240b81c885 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 12430078 1250 12428828 12428837
    0x20112020301030c0e090109050a031d030a0b0f0405150108031201050409170a020703020405090604050d020304140d0804080a0b090c010509060f03090a080318060606091011011503061b 81
    0x501d10b80e11690780c4c60382807250050390503801c0000f40e030101c004c0d8860404035410a042c3c0351440d11503e001080303d0a5003140c0480040e126400e582182000100700c80d640d9809200e00729103441d800785220002c000144200ea09114551194050030480c00c551402080170000540e10350700da0800c03c8541180c141c215600662a008100000c00d1052081d040c000141e80ea007540e46503c01001203007090400e400c041c2d00a4103101c05d0001030b0000081a500c55070141c0d05440078000e2200040762244201d01c034140c10049510301400c59440d0119000d182c3c0e5101e1440289459501ca141504000b00640140c07840a15403040018800013409016032118091034900e180c40c01050004405008078825644c0007140400003400085042202c0800c03617401007003a940724608501d86442c07000303104400a255003e01310100d01141405400d84041e90402804d00d2680d048a01c000c0b10600e2503084000d03a10341d200c0e00ca09a6021030f060024000d14014000824542c000500c4008102e0f5800718070020003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 12431328 1250 12430078 12430081
    0x204060f0e010512151503010312020d090e070c23100e1506060403050601031b0609030b0105190e1005011403060d0807050a06020d09030305070206040201051804020706180201120203 80
    0xd0380d01004442e4520700715244892140c0317a8492141d40c01905075100e94000409945a01c04041321801460480b445104030300344810305268200d80b24441401d010b000b0031003820052000071044094181d02001c1484e042c00b1041e01911007903c8074042d001107002c4500ea903c81c41040e00300900040d04200d0740c016003030000c03081c041e1829a03540c43e02c2c09040190b0361010089421582d808041783d0085801c803046941d1340d42c4a04240b0742e5100207001d500c15040d0301d0000040c146004000900859800c000031202e00c0e881d00c1e00340100c07030503c40303845401c0c5d02c8274942c0030910140050703419000e880041e0084540c541854005001c01420441a242004e07051040101554608602c0b2910542c071140c02c1d5180e01083c43c0244c5491603000c4000e0800c0d0008c510045a11001c1d403111084600030760b8180100e0300d4400781a600c8080680d0003a00161007081403078076030101072040d0005404007800c0180383c140161210002c880c0403090b00c1162441c5100071000355039000345c80d24641d2854600846c0756 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 12432578 1250 12431328 12431357
    0x329090601120302010608161d06060d090303150605030a0e030405031c090909151103060108060108091204030b0405011104180504020d150506011101020a020a060b120f010204060f 79
    0x364003052041c04903582c0a0310300ea508151007900504011315290742280c070001c040d08502c0c0347c4801540203010720a1040845205000607605c2d142e03000b83d00c040c19940c034207034001209001074880200b00b030301450307240c460500815004400101c000c0c6a07a9841903142e082c80048002910381e440c1480407113602c180010300c400c0e500031074084078100c2204075800d0000210300d0262558840380c0d0144c004980b0309400a002d006541110307407440f0804410400020381c0101c00d640c1c1c2400300740c60300c40c00103072183c00080841d4014070741a5004140f42d403c03540d22400c103400480031607116400c2294501c22a809100c1080002d000b4454088203501d040760500e41041c29811036a183c0003007540261342c5400118095440318080281d585400003131070b40c1c2c401e052241c140d001d86400d9130154001400c80300760100501061007580d10f443c0e43c4d80e0103403050038150344486000d00503240517143d121a0441e81ca0b16071100c20820440052283c90015032100c0c82e021025010401d80b0501101340128052559071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 12433828 1250 12432578 12432583
    0x60903090306010509060406030b0c0304052109130f0608100b01020f030a080a06050406030807110303031b0c10020c0d0f0806060d050702070b0c030c06010f0f03080a0309060204032909 81
    0x6640701907408176803640d1585c1c005030140620b540040c0c076a2190005100000007400000c5224601910031141d0b041d22402c003a0604903259461a4102c17141401441403038501840d07003000700300d0700b9440440c00c03a61509801d0304441d00756201403885e901940304600071f1101402550319004007400a815040d0030003418903101c0c0b19480414003085180000502c188506520000260030050070400c2900e442e8984181c040d8030840040c0c5032200c552210348040d00d0008101c900c14910328048181801c0051307002480c5822013022004d06004c1c801106810032510f1000c2c08440303007102e000b001190910200500160700d0241a0000c100c0700000300001d40c0c03980000c464862101020001c0c0b640e54064040b41050010381002d00140c1c0009171040d52190000060100b9000f41c0050f150f099907140d00315652503409116440b0309030544a000c02c08039036110080d02107030950f41808030b11030707103103030703185000ca0380583c000b240e070800c2140404081c80f49410540d0814100000229214141495160f6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 12435078 1250 12433828 12433831
    0x304120507030f0b010602060a0c051602041b0305040c06030c0e0105090415080106060e01030504050c012709021206010503060a090c02030c030309031b1603030c0f05060403020609060903090306 85
    0x1082044209000400c108080006100a60b082845101c58400515044150f41d00078490700c40180b0460001c544e2048207480794001c610a146c40e4640341c10607842c0b41c614010b02002c02a0f034000c0d03598000403186d5594454446140c10565000986031900b0b14000003514038581140040601d040035070301d40d0a80001c5501500c0209080c49503d030b040c5800041c0240141d0f0740104100c09200c00f0010b0400b84c15040341080d41c0054807104e03d440700c10401181101c408880141041d40640e02109440d400344084a4601c58440d02085a8031a1500d150503542803513072000c1005580024102d0841c100801c400360825400d00e002071a5080550006030300300c00034012008526507552001c0315240c020021a85004d20000c1501e03140d24000c8166922178121140d6000090000101001403141c04601440702014010000901d0b5045403000c9451607502042241d003d0000c0c3c40610200c1c0d801c00c103082c4075078030950044c480e5103005c1000e5406d00c500078007103101c60350040c0304c00d02c2c240e40d000c24190f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 12436328 1250 12435078 12435089
    0x4080301030305031306021c0b0102150a050403030b0303040312020c01030b010c11030c03100e0d05090618031608011a090603070308070510050106090311030a150504030c050708010204030317090304 87
    0xf942c1303d40300c0701d09078007a071503a117400100a503100103541060500299007010094170100c41c20030451240c400160f07100c1c45080c582e014000380290010300c201ea42030f030015400ca4007901e0009001c1c034024000ca4515441074105840c0503042d056002000c40e41004100c9007011f007841c0c107000d00c04076800003800c64400288010039000b00c3c482c01d1801c6403820802071218580040448000c03078410a080c60003080c020612070400d002c0c8030020092180a0b000703c4201150180803545810b1009001e14402c100003107803540d140c040c040e03102d1091020099400040c1640030000116405842240b10103c1070320064203000700998070400015540202d000c200300c03034000304920f9503006146072540c10141d907501c600d800b49141500115095511510f1070054a100301040400c48a421007055510000010010500d100403a030800c103820154000c1030b0054420f0030321101031500e03641c4107030171308005d600b041d05181e40c041002c0061591102015120510018800c0c105052503031035180c8a00c40c50044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 12437578 1250 12436328 12436337
    0x90106050f011b06020406030f06090501030506040b07090312120b0904020a091104031a07120509030a0c0f02040905031317030706150e0f1803030f0103030807021e070602070b03040803010303 84
    0x2808210010300440c4a440f0f584180111364032611114064000c01203448480c0e01d5614026001c0303440f80452040138141d9800034000c104c1a6225035400c02a80001400c810400c8840369002001616a0400900384a01a1100d1014110b00f220140c02c4034052725070140b0620740f0506100c05038603038410079015614880d070049640104181d2400d4940710f03a9200503d440c543c400f03001606c0ca6902503160151100d40d488942c05405003e40c2000d4400c1510380801c01e40081000c50350380b0340100114004603110300c0c0030004059040c3c0015007210b1a4080c1511140c00c00506c3c000c41c01a11141c0c24081c0100220070b000400342c03584010703039034014844000c210315514204000c41031282000c140c014007012440d01040c1c500f404018484000030f407807807000304200c03420b4262800c0011003920720507100034403900043c0c2c4c070b16101141c0c840000b9024100750f02600541000701012003491801000c0d07c440180342462901800034034010300d50788445040c803c140140000101ca900c2240c2c110794061a2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 12438828 1250 12437578 12437597
    0x80105040c020304050d0f0308070c03090b0310170c030606010504030b0c03092e05010501030603080a0f0311040e010e010501080405250e0702060a0f0219080c0c150906090106050f01 80
    0x9920f18411500499482444a026a000c111951100d00001031099440103460345543c2c0060b46c0021032110024003003411002c09000c1d004c038203c0a564003030034900d841e83d00b5580d220b060b040f0595103a1190421904108500802ca007802c000d4107810410a1a20302d143c2032442c0c0303642d5020303a07001e80402c02e40714000001c242007600405c00f030b164191844080480c0c0c4c21141a0720400a04011003000c0392a00740400090198024860642182d8001ca03260346020100002100c00c01c12265902c01130554990740801038200d01009403000e825403101c480003650502da07052441500580c8410704015080041000081d008a030201e610b40003125281c54140c0d110800b00344a1810707400182c0210402010020000d5000480b1030150400060400c203c0c010034006d18140d00c50701030152105900c241000c1c420620500c5a41d9014a0500503142000390155009040c4008a60802d5101a40000f80013003420103000359904002d080000f0042c45241070b0101d4541b278003041b0494184020b804 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 12440078 1250 12438828 12438851
    0x70203090409020f030d05040f05091005010e01030f020417100c0219030c0503030703050f06040b0123040b040b0306090a0513020d080d06060f09080f0604020f0d050a12081608010504 80
    0x54404000070720007000e0306c03800005040d00402c0c0303800c90711030b880d07516803594070009503410100e56407030144810308a61040c0c141080010340d04e0103c00445141090342d16009082507103040d201800242950420300b031903c0740c140c04107030f15009107443d0b00c0b02100c0c5021541085540c000840e040d0881d014020a02c04000d64141540c024400e844c002d07103103000004c10004c1c2198141d101034403803144100d840d2040c1d01c0315801d100441c0c0004000501046c4106165403100d104050211005004000320b1464903849032815181c48c0c00c1503001d118034205c003006201c110f1800450196008200c81e00070002840c000040e01400342c21560042c0c0a40107010203203080c4480f9074126007001011080c20300c0b40302d07a10600105040400e00c00040000c15108012030741d81c20205219880c80402001490390392107a8080203400e45602d0304003035011031001d1180c0c001034014009030b1030160140c690301c00035582c4450040c01c0c82e40000d2001004c03841e594201181d40d80c00c90480d0341903076000d80e0300040c4c007006003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 12441328 1250 12440078 12440089
    0xf020a08010e070e0108030a0903150e0102041409070804050304180b09040302061005220f090f030e13050705030708040c0504090b0103060f050106090b0c0a0c0b03090609030307020309040902 84
    0x5410180c41542001c0c1000071035140015520200d515251040483e40e13a00c1c402182c6030300400440c440003070085c43c07041011030800b003c3d03a52800c0d104e000000b50310b21114071140c02ca03405a4440015448202800865894240405503004405040038065441c6c5550703245d85a101340d001e6140c076a01c1c0b440c00150405100c1d48000020040500b180085041c1410042c2d641c1e0003c942a1111098000340030400b400c02c00c204085d41c240c004c0c11407141d0300701089030201400c0144041ea1602d030f5120740705800704841d5240d0500e03481c06900c0d4070414402c43c0040c41496134440c0500d80040f801c20052010391a40441240d6006a4520703050140c2d40f12031030074032009621503200982c41401c0041c02402d000c10400c0d054100c0384141410045030800040c41011f981c002d2051360007103110300c5001c01c02e410b000e40050034000c18a200b51a10062555124228642c550f0400c03210054080100b050b441d40422500b6003000c003c100440c10f40c604880300a641c0c0c460551018002d940350111402192141d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 12442578 1250 12441328 12441349
    0x903080a0314040b092a01080c070c03030504090c0201060b0702010813020301060b09090609040506010b031b0a030207050c12100209030111030106030e061008030304060c02030d090309140901120f02 87
    0x2c1031035090604003414030300889001038079008060b01500c032881c2002036040b448103560031100b404a58280c4010401500c1740344008107100000b400c1004801d0004604011120103980320b80c49040d16030b0700b0481148106e9408008220540e03141c84002c0c807051582200360b0343ca095091925601a40e6080100100a80e61920081d01582481d80203e40c404982d4050481540c050fa01000c455807841d0402501203802d6a000d05240c0008005000c03240710500107650103d50104108000a02c000040d0001c1e0b01014084001030341c045880c004001003400410510a001c480061000320b800359103940300c03e404408003a11940c000398245940d102908840034406002980d00d859613036882014021782190310350000180645000220b1180d19840c40c0016200e01c52300450644d943c0c0d5036a9030051645411400c1544024008280d0200d103502402040c4e9219a44441c4007078034003011008200c1400e181184910080c50050200c403445107051030003a80c00c41900d105074000b50003c2050f8601 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 12443828 1250 12442578 12442601
    0x4080c0f070e0106030c0806090403030c05070b09011406090f0105010302090a0906120b01080303090604030305040303060e130201090b09010212090f03030403080306031009030f0f02190b150904030903080a03 91
    0x1e2040000e00380d40d05010560482d0926281840380629150f011904e04c8804c03940d40780d2000d00b51001c140881e201c2e42c0100100941401c00341e140c902c1680b94030038062402c580701c101c02c3e9112020102ea072214100c0a40d0411400d07140206d0b94213211840800e03001050060718105030b8040f0740c3d40c4141e0395500303a2400034000c8103410007100361035690302c01d8210f44280f01a1160442c1a000040c480d80000c2140c0c480c071940c2c0c018004e1500c0700e58045000d054094410340030940c03148d201140e01005580000c2c010401a019040c05200910001d0423604043d40071304c40c045030510150400d82d801080041014034a101c0c041c5d0303190512000031381a804501c902359090304c404100407007000109002140920000c90072984060080124401611403600e00240080d07181e07071006824a00404900d414801035006450f203400000b042030703080780c80c98481550028070b01420300110fa0303485d28000b01d6140083d0381d810503a1425880151038507c2c00d00c0300a0010741e0010b040e43d0554481e07400380c0742084 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 12445078 1250 12443828 12443833
    0xc03030b0303040906060e0306060f130f090204050a050702120a090302010804020414010b030a140709030605040f120c0309170309060c010f06170606030c01140a021002070602040e01080a0b04080c0f 87
    0x1a01c43d1b00c01017108103100031190080c418000800c0262410b0160310000050041c000180b0400421100000d17040541d40f2207100f03a1608484d000507035641c022144a20310b200b00014a510340450000c2c078003415018002c545034810003070074100c51f51107066201601d0702030900d20101e48851001c64010303d0011000b100c10000c110000c50151401d80045001e2510880180b001c45080c0e40002c00014040e50850f020558030901000000c030281c011542c081c0c005c611000070005e85840710f801e10b12440e803420300081c00310358401c0100f64000c09a90050240304851a140320490017406030381c2d10542c0c800310303c10540400d0780e443c400000d4103c001c48201a00c000e022280c0d807102c0340420b00c482603054120b1405038400241035401c000a00181d031080507554440040c00f4614488590340c0041c103608118040d1350340c0740d40d1012550006082e05131103100010b0b955450f00400c098042010307007000c0c010303421030525080814141c200c0d5942040c1c000d01d00d1552801c09c04442494880e02c08a150a84d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 12446328 1250 12445078 12445091
    0x1003020307052106070309050d08070906110a050f060a0608030304020906011416030903020406091e0c020f06010b03010e060d0503070305030604060e0906010e010b0406170604060b040b091f0c03030b03030409 91
    0x2146c0c55006010124850f6040710b80120705c011080c0da2070380084504000240445d4400c102e03140c0300d0515000105c60000c1034417110f000c11f88940781407014a05149200f0361041048c803c541e083c611400d8000c01c1080f024604600b0f1940c001902924082c1110b810010442a91450700030104202d9420520840b1800b40c00040351502802d42d100c2031005910581c5080400074070b010b418000c0c050aa5103003060402280450542c020090451000700f0003140304c1c40c060713000041000c00203a27018001a069003a225071605c0c1c0410900c2c500200b1850040c0c0c4c0348000349002420001c181e42105515042041d203d81c1da010102d0018403641e8040b080070f00080060028440002c03035a1816502c1441882089030b0320b540ca104018882c82c030403103000a895500300400d0400b01e4001613008180200003003031044e5260900032068009030031080b502040041c0320780b1146444545d42180c62900001c0152071020803c0240c6020410007014080c951a0354040481e95000e00442d4042c011383c10082111 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 12447578 1250 12446328 12446341
    0x1b060a05010608060604050f2206060201050405071502030418020906071a070e1003050408041a0c010e070b0315010306080d020a1406131b0807060503060102061003020307052106 78
    0x642000c1c4038810120381020301082d03c5040140072181a602c01234950070b0041040818002218198540b8400d498140304601030805554002c80c802800c02c2e500110315410942066400d294403a4401001c0d0800103424440040c1c010003501c0803150300c4800b51425540c0790307282c04081d110b503a00031680290000349101c00c1202c2c078407034451801c0c07002e440c05055540d000d2007642c40c804021021541301c100c2565046942d031081d08400e074014402c541042c10a030351151300076031580e8000c01c5280b44c0140440c400f80304007001d116200c40c1260410050180c2d5280800c0e140e402d00c0040c150480030301744040c4040c00c1d80d009400c804010310850303049640407414001d000352240f440b03110480b02148524240da025900c00030b02c1e00d00815081e141a99601c01554a65940501c1d08421601001e804000080d00c00c0c4140f003505c0c010002600c0d1075a582c5441c400082c01c3c800c006000c040485400c050510140e200003c0190035150b05071078140b0520300a05260101244e41c141c1b0038280d1241c0c40403c0708 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 12448828 1250 12447578 12447581
    0x30708040617010503070909020a03060509060105031006060c031b02090403051e090303120403140c060703050702011a100306090e010c0201060803120a050c0c03030f010612020705121b060a 83
    0x4940440d5078280a100b200502c040c0c100c1028450240e155100d002c0c01e12203440c039a070055142030720080011807225030740d554290a17110100c9803403c680e00100d00402c02d0303003400e01000c08a254400c104120306410107501900e242c4c5c40110180410180b4039040c00300307541070b040d802103060f0010a0707240c2914191500801d26400a02007000c0b02e080307010444100d0307030b815094030351a1500501a505041c1c004841b0030381580020819402c201c00d40c010f43c1c0f11450b00300000d0151142c2940504003924186c10041d090304c9000d001c407421a0f00d004205601191003c90164404500301c404041d0541038100440c007038552a04200340c0189418201604d01005620030001d0740c0d4190028009c85035107621940c0c0700d00071820a15030717010003100007441c0c00c55694001603000c01003400d003900f00050b20f2207032031464004582d10318a01d04031b0390040c0003842d0000540c001c060310807482946001181d6940c0d686411701020f5401d03821001107200c801c1c05c81030f030f294421808401000c43c0d1080c45d24100c03040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 12450078 1250 12448828 12448837
    0x14011a0a120c09020706060f060203030604060501080921090402040902071406040308040f0302071a0306030105100605041e0302030a050703300e040b041a0102120a0e12030c030708 79
    0x103214000c003400000c0c0c5403081c0301d000d1031540d4011195240e6645000c26080180d40b00031001c03140c0e1079540320041280d4400c2c0c10f801020700b1040d4015a00c80ca0200309110448040ba04580e051044000410071245800242c028541c0e00280c10300320b00d900e641148152500950710840e902600100e008242103c90380c0c040c2a03514000c2c03010070240203401e1342454850b03400b5100640002c0c3d28900140204d440e080300c100c0314500c64070440700b24075542c40050041384083e0307810003010307030000040c02024a02405169040b00d0013825803041c0c10310704403000d08288601c0c8240030300800c810840c0c00380145c0030059000290340250690f511700c42540f0f004d5031208000e000884503a100d010603050304d03100903194002d0103e0b454201c1c00c07041040345015200c0d0114560316641c4151070b2081084c0c0c0b52600e02334010310448195a001c281d1000c1d00000e0705010320b03920144a4560301380a502c01c035582c025032040311100c0507511029445170041c4001c0c01d5126800d603041261000088540070000180e0091 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 12451328 1250 12450078 12450131
    0x60f0d06051e1503060603040f03180308031602010b0108060d0c05030f030301170a0203031b01020d0e010b1201020711010f020304030602040803040e0606090306010b03100807030609110612070c1401 87
    0x2180780402e030003400300f1280000d9550541040f4140000f4001030314480c41000107901a0400035211044036651031145034540d0012a005c070004030a0000c0d03d001c1c5548262084c050b40000e0145454170000249581c20007040148100388020200d018052070240090203010003030151108620610030741666070340207100d042c924003840c1c28800768144010400e40341e0345074001d0241d0700d4194218085500d10038490300380c40413558204140d05e07071340805100303158040440030700114441c10203404003c05a41c1d551668100c3d64010040380e00080c8140004001a44003400c2014040140c648102d1542c01140c0004290903c005000700e100703c1e0000107481103804143d25850603650742d8080c0417150081100c59a056072040006100c2c03c0c02c07900c059a030200d100e01700d01d03140303503601d603925072802d040c80d442910702c2984c40900c04148400041c1251503204241d5000c0e14204012504042c13504000b0070701c40812810244090400ca42141010155400e550013408415a1a52100c012600402c2c0e44c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 12452578 1250 12451328 12451339
    0x1020c13090b09012a050d050a0e01051003020307090b06030103060905070e040f0606050105070b04060e0c030d1107090501080d0507020102011104061e080108070b0f04090203010e101202060f0d06051e 88
    0x11206248003445c40c1c5408040c5c1c0d60340e050900b44208541d00c0603010180003020f60702d40351041c0c050b500c1c4091240520800f45d54401d01310b00e0780b075401890704080300354202c098040d0a1401e920740a84416003200c0c1101d038040c00002c0c02c0c03262810940c0c101509034000507586035a61041c00f0622000794258503410780a444c0c100039442d41c520064520748a07000d401489100803d00050205000e41c0c003103441d100101058404000c46800002c2c10240e078498128049100c00100405096081040b100604001c0f80c080060754100256942d42d69000300720310042007000910002164402c0d00084003000c08848141d48407038607070f0000f5001e1112410b000c0b110344a4001c2c5408410f10030003485040300e5144010f407a0590800380c5d90442680061076403519540100000240030355180b0066009207511a000c04103820a000d40c20380c03051446d800100100b1000050a0169a81c2c00071229544110051560307107000301c982c4c0101a0080360f110661050142c420180301d100300f2564040000402c440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 12453828 1250 12452578 12452621
    0xb010203031504020702010c12030603030801090b01020a08030405070f030f021f08070e0d0c060819060b0d0b010e1002060702010c020a120e0102030712021b01020a0201020c13090b0901 81
    0x4aa5038002202d640308030708800301ca16501410650300620b80d20780180f503c41d00590345c5485442c54102404414000642e942c0d00c10418145d10100150252100b02014000040da202c0003e40d15000020080c00c0c100000011804003c030800c01d180003090000100011142d69017070407041a01420016800749201c202907401c14130400022050013400c545514016131515001211210290780c5415003244101034804003145009500340000d140310742c0c9482d0725140050040c10941e14038006081883d0801d1030911018080c1002c4d41c0c048540148005070b0041c4070801281d001007951034058103c03d007100c502c039669a0209a07030b803260229030002d006030900c125040f40e030fa201403440174107400c2c014440c00301000d03c40c0c1036401e51400148110303030500010391244401a2001c0510f4000b603400300200490794800b1401c1c90040c80000d0000c0c004506117600044d4541008982e00c40c803501441c03482e9190619250301c03400185805c100044400d15002004900a11000748810f112080c60710307 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 12455078 1250 12453828 12453851
    0x100e1006030e0d091505040905040f17072f0d0b0604061a040b090315070206010e010f031208040804080a030504050f030703051506030312090a0606090b030d05130308040f0306 77
    0x240c4000c103c0e01075a60403004514200458245011400e40b441c104081004001807440c0540074903802640211920400da00d01442c0c4418840e6a12121107401c83d014003407000071400d14170300a00928550b214409200c0306410541c10710105001c4156404042091618240320700301e50510301c03503001070301c003040b24a031904480100108259659032a088040005200d202c45041c0a4070390f450000d011504401081540d5441c1200d00300c0304075006a11000040000107d120550b80c010141507850b003411a04540300c40d05200e009030a800284241c01020034100704080b01103e004007402c00903075640026030b00c4c008041c0c2d07009119a40c406d4041442480851502180316030032280c0c0400240744408954008000d000801001c1c20b505000600c600300c41c06040d41c0e2014810440c080103005002800c0c40c001c41120500d030480c000251400300c290003aa1400101810300d98400d080c0140c40d48201c0a078964079070b01642000b1305030100842c0000f0001e0710007a0100980e480350b14140000381004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 12456328 1250 12455078 12455083
    0x5060609060405040e1002030c0c060a0c050d0b030a060e01060501120b011b030c0203010207030c0204050a050f070507080d06080f0f0303090307020f040b04090b07020c03011107060203100e1006030e 87
    0x5611a540c041e50422080200c1d15007980302c1c440c0044890141d640e01d03001007640320101d800450343c01110010000b40c0102c1c4841c14040d0990004078100e04008000c08804000e0950245c894111042940d91404501c240c2d406c1114508040c0d000e40c0611620544550060281c0072521641d80400c0c00030141c3c4030620f10600a4119035041079561042c0000c81c094100c1c180c4020000580902180c50a0903015071000c0c002052040c1c0a40c0302c09078641207510520040f90700083c9294240b9241c081440220a40c41c1e2026400012901d01161203d455003400c1c5880d21460402851962030440e002404040103e000200c3d0581d003c140c4480d108480311150300c078801295074100c140c0007000320000514001500303140940e4043c0000405101c800041401c640424a055910204a5041007440396040202d401ca141d0150004d0229680210090850780100d9100078140c40e004000141c0540415150394000c1004017840905801d1121176440460f0403802500b00290500904240c6034000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 12457578 1250 12456328 12456337
    0x2010209030705090615090a1502010b01080109091a06010329030c0108070f0807030f05040c0306051807090c02031e0a03140f060d0302010209221506050d0207051c02010e01050606 79
    0x43c000600e0041e00304e40001d12a071047e10780d031340d0094030300101007040d44062069010a20454000281401e0040009042801d050380304161850034901c81d540040e0902d4800719184150311100021038070b4140068000c2c24020050070707800510049944464140788a600c0322303058007507003a0b503002c2295900441d1090340440b145030100780c41c0003e1140700b51180c040658070101c05c0c900011081e04034000c0000751001542c1c103865074040c4420a1003800f5a500c500c0790400c500c2642e1270f0b207480b402c6214544402d03c6105200c05295100741190580340280b007298004a51442d21548104548003c28a5600f11070f161a00003460054001c1c501c1420441c4c207406224100300c3d1406641d1010100030340320301602821400c55400f4002c4222a0b02c8140c4403da80380c11440c5000602c1c01071068a000715060703604c141e108181440410000c680c0c00908449035806e82650150381d61641c0d040841c81d0149007285140c81c031040750b003440c000b07580c198004045400c6031002070082d6241c000801150303014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 12458828 1250 12457578 12457591
    0x9020903060f04020d02040516030b0402040f06080a09020603040f050607020316110d0501020c010603030e060a080402011d090106080708060a080601061101060b0d061502070b04050f04020c06070201020903070509 93
    0x680003241002c0e1159220359402032008203901a0b500075603010409490050301e8900008400c1c000c00b250252301801250540c10058804604080c601504903251810b40d00c904024002c408003c5007080740c40d40c03c440b4103550041d24050380c90401e0b1411400c207080c1502c0a550f54001c484c00710b01158404022180180360403c1290350311217440e110010b006d1003052130076034840070250303080740081c000380054915003020b0000080c40301e24500f00500070481e4414420720400e000c002d02100300c2e4010640d1500030781c0a01c0c060410140310000b05011398510f00c0040d9000b0001c030000581c03103900000e6203104c3e42d40d55a4405040c0c441e1303010301141841310300445540340c00c8540180035441c46240c4108541301c1d00d03c0086103003591114000082d40c4801c01c6100300c640c0b0380e0018060080b2100d803084040030140b0081c00407514050000e90709001d540a0700d40703d50030440380001e0310340e12601501c00b600319580c1035a941c3d00300741c00081e000b503009100c401d009000d2104001424a00414190721699 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 12460078 1250 12458828 12458833
    0x303010302040506130e01050601020c010203120106050f1e030103060b04020705210409050103080a080f0106050901030c1e0306320405070c050a05030d050f01030503070b1005120604060609020903 86
    0x900356030820024080040550360051258400c1d0101102680581d59226502c1c0000094504169000906104a14581d075040d540100464824500001c01907030444106191443e10343c4280b44ca080d0003031140e00000310100342080072030556910360074000c50407244603d00800594000109010a81c0901c00e03001d049a000300788540d500741c1c510034500101d071f840d0300700252610340c403000586c003260020f0700300341e400440104000080c3d41d00030020701e400c4501c050700c49282c0e40c5031020040130752042d140d40904040e150150b008405008002c410b030b03500e00c408030b590502c0c014200014001c042510508070000e07040403c0b40b000008851410001f00201001c2807031041d140c809102c0135000140000b400c2291050491012400501c1446040c0c0d110318050742e80d0740580b1944905443c0045c00c1d06075410006401000042c10020840e900d40d07a120038a44115603641110042c0c0b42c05561200e0381105e203616030004440300214140d4840c1c2d1040e0710400407903072540c1d288012030040e12042030b0180d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 12461328 1250 12460078 12460081
    0xc0509060a0b121504020706020405090c0313080d110309010506040c0503060109050411250309050307120b0a14090c0a0b090904020d150207060903020c0d030906030e01020408011802100309050303 86
    0x31429075640d0f6920400d1039030900810300034040813508980c403440064031003507400704062103545001280703a50400c141c45085411800c040c81c8000c5940c1640c0801065030800190031010792130140c00200c41c9840c1009061b45920b41032081038064441191203c1c421407419801d6200940038009981c000d20301030795400216400d00d0240001030025240c0400b080c2000c1c00500700c56001e404080840c0d040e810008040d0b9142803902509903d0190401031080d08010002c1c40f001a0074403040e22541e400c00307802d80070383e107a42c03140d10001c0c51402c02034102e600c0c421041107a50035001445010500081c4c500b0384130faa540f2001c01c000ba014000e03c103940a40c5504c041009842c00e40d06008541340141e840607048100109154100c3e400b40d40c00b225003e445410441c181074051050044010080d81c0c82002103906903402440c241c902d0061384241a9141c410080805003541900c2c05030540d00002c00c0640c030000b804555041040d08124407900000d00d0043e55288079004000e1242d60120095086 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 12462578 1250 12461328 12461347
    0x20010c050f070302010608010c1808060103030813080d0606020309030f07080715050c06010f030c0501030504030807050a141c0b0105040807050103020702010c0213050103050705030114041106070803040c0509060a0b 94
    0x107a40c040300307040c0c04540d214400030414130720a209441100b0001c0d1140e4000a0713140c61407841104c816400080c6c1f9800001c010408603400402450348281100301440a00540b0b20381940c040c05040428020b05203464004174060f41c00000601d09032800f00d0403a0032001c25a01c1a81e0b03514441d0282c5005604540800c201c0c0580300010f10902c0c1d0000d0500c0781c1001502d071002c030f140032400da000e1140141206001c0044c80315121410f000383c502031805100a00c2c1c01d440c05403201c1ea02818901c10043c0000380c4038400c81c41415183c107104803143d640c07079860308000300e400500c07110300d44484100c51600030000c2682d801481190100c0d5103001c00b0702910362500b001580250004002607040c0108080e400c001a99019050b84240b070951400040650443c00d11500d41802c0d90031950080e0b1508100c0b150081040e00010750007584641c2081c0310030003000100e4031901500d60000c11000d0007000744420013440f490042d044d124166410203403640da43c420400d40c07070071500c198060f14208003c01c081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 12463828 1250 12462578 12462607
    0x2090a030b07020703120801060e010c080a08060609040c02030c0f0a052505060409090b0c130902030604020d050906160206130303020901020c120102090a0f08070b0a020c0a0620010c05 81
    0x18040e0b028010b642d611552602c1d00f9001d054101c1100c4000f540380001441075507003191640d8103a01080c0782c00904240c103540d605525200e91402501805100d00001712180e4030501100c2c24504040c00910004005401c0607603a80c004001d880e4660081a0420001a10008140550941041c020305128078484584c000100313a0348001d02c01485481070100d03041c0c880038000c0005010005000030814410308048407501c4000d0400d0340f0fa0030081082961500b0401440707000e6030003c0400503030307135201d502c0028028030606c0200900d090030501000902e18000c0b9032a44902d54442c4078104540f4445012a11988121806a0f0f056054100c1601083c480e501030f0202d00c0c0c06004442c1840d40010001d15900894041c21005030340024071000d00c0d0400100d850f000300100c40700da100c03a50802114948038038040c06404040000440c4c40c8a00e00c2c0308201c2c0c542980c02c00780409a17019240c90700203190b03940180c820b1b90008518012440041414844c07042c0040c1107507980740c2807203100e000c9000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 12465078 1250 12463828 12463831
    0x5100302070218010603051f060302090307080a030917030306061603030e060f0108010614030307060e0709050c030411010804050a06050912040b09040b2407020409150e06090102090a030b 82
    0x81650070300007100180c03641c20703084a00b030002e402c010003190314000006080d500014142d090030303061005007031031f092010302504013a6039280c04d0240e00c500d42d60003c00d11740503031b0398001d984510031030842d9001d141d001a4040c0686840581e880d901c0d0081e16503550752448151241a00010100158039507410301c42a000c848520a02d80403070032075100c030000303450b040e8162000d0300c1d10705c4c442c00108005442440780e000100446603450f0240240003000075124068420094201034581d88091103000c2c040c4082c001410f0309020800031400c0488080700160000c49007160344003448441c0540540c0203400c0b191249074050020580c02100b0f07070b90000504005800003820740b184c60080c0c1e6540c03800d4000f8101900c41d03144420f0f151900b00c03040106460059100a002d48950410b094440d052400620b1005c1041d06039640e0b030300c10b107101090080c003004d40040c0940d81e01e28418a03002d01940c11000302d00c02200110303012920707111482400c030301c1120004d95010707040c59010030028501c849101d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 12466328 1250 12465078 12465109
    0x510080708071b06021b010f11070f110901060c03030c090326160807050706090302060f0c1018020102101a150f04030b011a0a141803070902041d0603030405 69
    0x10034040d44282e40c4d2509a0300b0562880031032240c07995040c0150f450074414000c940321218800c3c086001c0303299030b0010034415400050400d50542490340c0502006c5680d02245c080064150355503581c2d5108000e20300c010700b11046000034201118441241d100f86528801c2d0fa402480c019510b41142e00f0f00300610110050ba0340e2070300001d105d6a118000001070741c3d40c100b0b018044103075072019246800c40c1855201d811400612003032240500c0503846610903196405000c1081541c0c07205e00c0621185401a52a40396910a00348540001d841410480c0301c0c8010f4401e808850f40b5032030b5402042d00b81c8010304101e0b81e81d000d250f03540080311b11707004901c0509000422a200d117013140d40b1104400652260300195506004000100890210381d00c00c440b0844965140034240460110000c001100d4400c0b107480c0b2071070201e030010203c03030390100074140c0b003070010119401903640d111418041e401512400c420210351290003281c5100701c0b21014410034004000d1494075007042e042089400580a50 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 12467578 1250 12466328 12466367
    0x10801140d02030610050406050a0b0f071e080a0e030f0d0509060702040908030601021209010206040f0213090c0503070603110a1815020102070b0702150601050307030f1401051008070807 82
    0x1030750150b102031091078003c1c4071040c0100720980c1064148016150a50702c9940600c030034460821000c9001d900b03491b080c0b00035078651503035101c50381018200d0907034061b62160300eaa20f040400040004074001048075000c01e40340c111039940303164201501d90035801004803072600303e004900c20b018802c038000d045050000346480d040807140e4000c22304a5040050481e008880041845960340c0c040200188182d8103c8155141174036040000351121009000101071074008456002155201d0300c03406040d1004c07090800c0002e0080c00c0c098901a40d52241901a000c0c020010601d64400d018960803c4203111a061030904179032422124000103840b0030415900c0d540c8040b519400390051610580400c0c2e0000d030300c0b008141081c2d108040080d00840941d40312a07644040d2107034501d2205d81c411001d0070810381f01e9445140c01d601802500c680c01000038034004144181c84500043c80341a52020780700c1400b9074003000380a56400d4010340f80840030a01c0304000030700041c0b0031b4900303143d00c0c141b0103003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 12468828 1250 12467578 12467599
    0x100603020f0c10020403050c0a0f030f060e030a0801030332030a0e030703020307060b01030612030e011e020a0507080109080f030c0d0609141609030305090301060f26030901080114 79
    0x2d00500f09651050345960194000400b0001d20104002d05074040b80300311103d4498900c1c0441910f0751544a2000a007000c0309510300c070003445803c2d80200b02840140040c0c955a264400004003400d07001d002c1180825000000440ca4500050144d100c8030008004421180b8580150801e5500300505102400391103040c4035081d01001c1c03000d07080d40d40c401d400964031904070b880c083c13003940c031010400c2d810035242c41c2c0100901354032588518840c03505070814040c00e400c40c8004030303003060280340d06840c001c0c0103450090b25540e000a0603404140180c01340c900e03407070301d4201890030786280c1040901580d405004800c0311275034141c02141c2082100400b94585440242002c0c04c0d5082680403086059848240b0344680d40c0d6000020f5001083d4a18049541e5038480090440d0820340405000c000c400310300b06101d80c03000d60103903002d000c00c0c00381404038540d90765900c2c0084030142034100c1c503c8004d03050900b491800000780c2300c00ca04c0c140c543d40c542d0b0f0309203022519003605001e00c15038400035110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 12470078 1250 12468828 12468847
    0x27050901090515100605090a0509070c08031801060e0c030402010f1701060503060f01020c03191e0503070302100218010f051201080705040e0703020d080306210c120105100603020f 79
    0x4046000070350310350890642e1030804e0900c0080d039402c1e8891014404200311a80305580c4032030030301003a924100d40c00d00742038031600000c6541e08000b600080441c0b03000070510a00103e940340812405140d10005d00c1401d07200d503141d103500e0a0999500084210501c08900150300031503480c070b0341c8000c918103c0701c0c1841625003041c60b0b4000ba803283c2c4c08114000300b44441800c100740d03100c0c0d5900b001e0004210b40790309080845e50710b01058000450a960203100b02c01013014a407080d00a0003d52020b00d0000041ca0410340e881c0d07803001004402501c9401d94003a40c84920340280c2c0c200307007078910150310815450380042d2400d0744142542400c0080801089800340d9028511038060302d6101c0080200034140401d000864400c0e601a121552041400f000180e4402d001c9910340395000c4d0072a5240e40303400010820710b0203499070240b1000c50002882e004a5400500e4245000d0111250700e03850006500007800c07200d0a560f45000000209018049140a6002468016124040140b40c4020740 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 12471328 1250 12470078 12470083
    0x30d020703030204050103180201020703060209010e0303070506010603140f0705031b0d0507080a0e03031302060403050a03030218040207030e0d02061e030105150405130b0301110301060c0c270509010905 89
    0x1400308402103640890240221350389407180314600d591400d0040e034440c000350000707545e07035246100007448103400003804900b2703034450101d03202e500102070100c80c0c07030b14902d1409585030381090080100107403411003580c86501106000b14043c101c442c096001c2078840100886d0300d548000d00c00171400480034440e01200000e0b030300420320120004000103d034101003034000e18010000d0841240981440c2d64401041c5010044a800001e01e458480d10b120280c030100c0c44500441c2d001030854002d40744010203164142e0003d080042072040c0316000041d64001b0842240100c0c60090001105c4403850303002c0303041290846020790700040140c0d00b400c00f420b04101071840d1904003e080603601000420550070302038842c2510540030f8240710b003094106404100030f00714119190741070948408501020b07803029401100910b8480005694968440201501c8144500320403100d5004103800003408070815070f40f0300280d204500111241d504241c0222001c2c04028014003165542d03105100c1c0041c204 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 12472578 1250 12471328 12471337
    0x30302041205030a0f020f07120f05010203090d020709020a0906120f0203090a02010e04050f06210106090605010f020105010e1302181609140306070305070e0d111201020f07060e030d02 81
    0xb900c01180c1d680d5030400c2c02481c0c0c10a40c2c1d02c81c019540003e401d5000d84801081c48410b45580410f1401e400380d6a007070254850840300c074050041c2d48000300380014020701007002a9011143d408a07038140b40c3e0344509004922509152000145c4126820302c0725070303c940c0c1003402210117402c001c251524403102e05400c990054802d80c40030b9021927040e108650300220842074080d001c4400300003a00e0103800e85c0d01d40710b4008056a01c40d80700d041d800b1341307079011504c0c004041c4600310008200039611040c0000060100c2c0c060240450b404072500c8602a00c14050581030b111110916142030700c91600e007141c0b074803c407442203074040300e440688a41c2490002c0c40c588104414880d403240c113020700401503c1e124290300b188200712500120150a610000707103940e004003040c50000740b151f64058088914a6140c00d06980c00303501c000e41c0c401403003168081c140c0b0184044034001020001c03000c0882c01c0303100e04480116003400c148503050105e86240d01540c1342e400b894007030f6440e041c03000d514401241e11 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 12473828 1250 12472578 12472583
    0x30b0901151e05040501080309040504080706020c010506130903020d0806130f140c1801081503060403020a0507060302090102070306020f0c0307030c05010f0204050f10090b041719020d0305070303020412 89
    0xc03407000441d10841c1114000f40002c0d2401c1141e0750400b04100d46920400e107030310340101e44680101c0c0c100201e4034111050141c105600310f460b019001d007414081c200c1642c0c0c591180d002c40b003082c48911000e1048085465140d00100380d203400c410816a50b45c04010401948010500c14144001d291401583c114040a2000141103050001204102c02000d0f02000d031040007848080c110061880c040c15007403100f400e1800103551104600242c003105104405e40500841c8240b2040540005a40160b140305a05994600d522100308404a01548050900580c00904100b01041080d401410740c2c1c9a980e4040d880d011011030000d2440c0c1c0b00f8031084000841d40190070050010038442c400035408821001e40c81c0c9807a01002624504070040e000f8850090740750500d00e4140a81c69140041c410601c180742c0b103503542d40e1080055511220401d00314025a1041c1034168044000c050440e5802003682c0440e5815440440d000d070030800085040c1642000007003851020003d14024030392 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 12475078 1250 12473828 12473849
    0x809030a0311040f0303230910050906040902040b0309010c020f0706050702040e0d11010e030909010509100302100314010f03030503010618180b040c080c04050d0609060903020106030311070f030b090115 89
    0x1074a5074859000840d40407c0303a0300b441003840313038940e10341e281c0c00441110300042c40d000c1c1d00d8500450000701d00740301c0c55200014642c1700282c0000c4900b42c81d0051440744c2003080007044159440e510503030f12501640d0800b850360700f200a080c4103035400382c0003412049001070b00006080401d180f4407444c0041c80b02180d0701041c01c05d0b02e03015220109000b00785888000c1d50180d1305001c49200420004241030003011301c0b408840c0c0020721007408600e40368006580003440b100d08054a103c001d001040003280d87c2e21140c0c100f5002054842100600c842101c5d4941c4d510741c03071a841c010045452906020486002c00c900d0000050080c11034007030700c4c640311501340c00010b00c0d01c09641080200c0c1c280c28455010b2008580800c044e1780300c01000d4a048030320a4441e0309002081d440c00781e00410b4415401001070349000d07200424103605600100943c1d00c240c075110000010b8050702d640c0d9135607500c00c2c0612691514414000100d084441a030407454080012600c000700c52056514281c1c1a0030407400b42 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 12476328 1250 12475078 12475097
    0x10f020310080d090605030609090114190b030c13020901050706060602030d06060201050f07030b0604090212010e090304440f0616050409020a02150108060403030c0809030a0311040f0303 82
    0x40a00f0b0019106034103ca0400030805031400c000030f002070000070220352083d0018000146041c01c2908005d007190702880051001d4604501c7c50824103952103005c81805152603801201801c1c0029281d48441d4010315009815140b142d099000e0f5001d265502d04102d814440c600005030180681e40c05450302c0c0e0003075a164501091464101c9115901c0b003011a070503c81404140d40e840b00c03199821041c6442c011889076440408030301c440c442e56110b41c81c024030014408a403000703900c2c2d800341a203c0364800a410342e1a09109542d0364000d03800380060030101417542c0003400c0c3c421065160f0030001c002400c00421402c1542c105080e403c000c01c1117145d00a0b04409000c04020702400f540310031404030141e0007400019006042e03004501a0001550f0300280380f905542c000c00082500c5400080d082c03000d907859001c0140c645509540c214003090074040a0f5800c6801418007520543d0644019420203285800c00c80180c400c500d15900d06100400010a4800381448854083c5010361100020f8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 12477578 1250 12476328 12476339
    0x50618040b0406051f09170303090c040501030b01060503060a050607030309020906100f050d020d020a090602010c0906050906030417030702010207050601080c03121c0c03050405010c0809070501030e010f020310 92
    0x2901c090522052145240400074029035079106510080d800007881c9681408040003005c5d03c44880641100003004141307400710014040010046101e156041c0989044102510601081c0c4000b80070080407000748800510a0074031401c081d56010800804046601d5610030229800b42d00c901d03405e80000b07445448510550134080041c68103c80d060700c0020200c445160010f14980040c3c405070304004002500031640c0e5074a8042e5120121414011966440010000350800d08144600301c0954200b1542d00029400f400040301229815124646800e03080f400700725040e80024070896034142c1841c20316240040c0702c4003079446020680c000603618075050078582d00e081c60590007003407984d0064580d00b083e03880206a4030490302082c0b00064854610014083c80d040510b520112114944000c80811745c3c0d06400c00b50280e4042d81c0200441942000d084980900840f030001d22644503034003c11440d4800e030b0018a8001a10000003125072002d040401685d00070341b5100c00b0200e55202c01e120 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 12478828 1250 12477578 12477581
    0x910050f030a050d0f0201020909012405030105060d0b0301020c0d031508030c0c04021605060903040303080105030a030c0b19020403060b04060503060f04020d0f050a06050901150e0103020d02060405061804 90
    0x300100c11402410756800c90b9440c5940c403401107002008000b40d01490710b0540303000350140c134003c0400815101e403568445020400826108001e03440a49605840e01e40250241c02160706890b4050621407070506011035420160040040c1541c0541d8200069060b61105000281ca04900c660380819100a02401d101c0e14101035001402c031754008014203c1c052a0001d00b1001e003070301c196009038403103150040b803620440c039462000e0070b280241010401d4082001c0028010b40780301c0e4560911741c0e600c44050503529020803800501040300b0300d0440e400f141c04510082e6005c003020991070201c0050b40440c000342c0e0003e900840c4c0c0151992100881480c0900580d405014160000c0040d803500012201d806100900068007901c020f030303020410300800e0075004040e10740180440e00701c0b4803030340b5010000b81012078100c0c2c40d6504e48041c00c2c07501d01c0030145150071195192400b2916900f03540800c08440341c2d41e80e040f40d100b0800c000001e01c50312640003400032205014540440d1003581d805110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 12480078 1250 12478828 12478849
    0xe0d0207140303041206060f0608070206010e01050f09040c120602040e09010207080304080a090306020a0f02120310270c0c05010c030207020a030305160c0f080708010509060112050c091005 83
    0x4071100c4407040030103801d480c008161822150300340c40035a000c5685080070700050200750060740010025000100350036400c0103801e400792100d542201d010381c1c3d07140141c00ca508000e015895001c0300c05c0c07052806516003164001d4025014943c41c4070080d0399502d80c49181c08407405c04580a41c3c02240800010031960040c81e44460342400a40c41c00b800781e0b5680c103407403000a00041180c2e1000c00d00a04a80c400c0200d40c01640e0b004004568a0200072400f070f0480b030345200780d000180702e10b42c106030042004405407405540e103502030812060408800e80c130401d040c1c1c000032890061700c150410210500d4001c500c010f803400d032103900e840b0b02c680c00c20b10b0944250138941c1040c10f004219600058944a041208907901894403646480c0c0040d5202c0748056185006020309580400200f050340700c55155604941a0100301e85a5558a9603c182078500442d4010540e80007040100042000581300200403442441590008074802c4000b9440e0442620400c0f21102c280310240b01500f4062000c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 12481328 1250 12480078 12480089
    0x204050907060e0d080904050103060603050f0a12030209150403120206090606010c0201080915010306020301081b030c010e0114030a0b0a06050c0d21020c0309010216080c0609130e0d0207 82
    0x902641e070600c4406410001c11451142c00b552021220109100c04001034a0306800020001c1c001d65a4038208000a440c1c0b82c00309503101d0060035a56040c0681c00500c0152040d4001440111007005a0042d0000d411902c2440e40040c0580d1018005603010001880954480c2022844640e03501c0c00092900030010400309040d4400c00920460381c0c2c0001801803c81c1d0709182400140e6154000f0500b00403201c2d4010000040ca4400030041010070703006581030304d001d00c5c12201e0f15285131900c8072400140c084190b4040e041001014080d51180e410303038049078018148000d00d01000441940168000c8440500c16642c842030111145004001c160042c0848d1600c641042c090300501d6440c0c0d01100341803400d00000d5030061044101c0d07100210a020032400c0d0442d101c88908020341d0322548444d45550050041d07800400311040611103070000d03603404e900103145100c05103080c0f126583c440c0035840d52010b403000f100c400fa0303201402501d504086200c040c01d82d05042c000080d2a004064115 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 12482578 1250 12481328 12481333
    0x308070302060108150f0a0e0d0e010e0103090f020405090106050310020408010b0f060d1a060406020601091103160305091501030f030831060e071e09050103030c0f0c0504060f0302040509 82
    0x500004845170300c0003a0440c01c03151111801d519400704003001000040f0310092a4002d05101d030030303100d03001083e001c4030202c280c072404101d206510045085940740300d00200404250401c2e030f005820b1a51250b513220402100000b292500c0e9030009182002d09564501300b290001824003c4080a01a200c4034101c162141d00d043e000e0700001a03000d0180208070040030350b070307002e18034080309084000720300700d00016000304d58594a0b1480213450310340c2400344800c41804c180c4011a01d01c2c10000b12441900080031410a03041d814404030040d00d409030454445200c1d0aa101c00004464403000c0c0c000d51250303060300c1c101007061402030f181c0751004042c0c03d003c449610000e138080400501d000703d646110f4004a42c42c4480340350400040c00010901174452003607010100b40c0c0502c2c00c11228412016071404809903507648404010f0303640900000300083c002403070b468002000c45185103030481c41900b54941290f01d40c0d005c00c0880c0d01c190f1180c0740102c100d0350204254203140c4a01034200018501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 12483828 1250 12482578 12482593
    0x210801050f04021602060a050703030b030304050109120507090204170c040b032104080303041101080c0a0207050112020903060f1602060103020a050d0804030602030a060302040e0309090a150905010308070302060108 94
    0x100c041d94030398200d900840d000112150078801c0458102c08069004221b40e44480d206000200b182c4c02c40f010450200c1d103403040390046850000180c3c1c04980050b910340d000ca60030490411120084d5502c100c030a40328007072000c1aaa00a4000f90003d054401c2040d01c00030205c2e001c0501d40003004056501851502020202540f00442d5400d410200e00c801d680312201700d034252490328401c42c0e010559500000c070030b000070042401d01100784d110099030741808035200c04d0451030722485001c4940c005a800b0140402555004002e01c40544521410060400c3d00c0301e00400e0400c6011542c3c0c01c0c08840a49c00c0000d8034240c810324800f9500c0500c02041c0c2e80d81907602082030001c042c01490310074041500300404003c0e101003190082d6500600554403420a00316040140c12a0b01040f48120b092000c19004510004245d4102190080c070600da541c0300c460840005280c0c08411403540c40366950081000c90700c034003a8078001c44c031a00c00c03d5a14902030800906200068110000daa00300d0030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 12485078 1250 12483828 12483839
    0x703112e2702060f071506080d090e1b07021801061d0a0e060301020712020606010207060f05030a0903110d2102030103020a0603050613060b0306040c020606010203160c03050703210801 81
    0x1c28414403164107841481e5541034001d1141068065200020039a0829000ba42c00d20001ca03088001110700560403196581c2e1440c000b5603240c2018020040740c4c00541c4005400301c81c0420720f601c10040390340e00c100d1030b0444030b8020403005829a0f1050110703001c003100400c10250b025000f03094801d4103810444e81d50741003030000341e06203100d48600e000c01c0e0664404a14169000c0d4103ca40041e44980c0c81c0681c0140c0c41806501e50388126480d13405400307560b900240e414064050036417450000d07650341c2e255640d4050100c00070128a41d0039410000703040d951404a82042088a5101c1d046443c0d01d40d01c0a00d4400500140d0101075a050485006100401c0141c58964251003556010305001c2400e5071580d01103084032528100c3c003e949802d01d0000a000b070450350045000d0b510070b9030103220450100a0a07a030720030080d20a076005900070406620141490081000001d00c21030700b98103195903e0322414a001140d42003921480301400e601d02031000b400e09010408406424403051a61400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 12486328 1250 12485078 12485141
    0x20601060306080309090405010f060f090c050a0503010303080411130609050c07030507030503040f0503070602030618101401050f0c0319020d08070305041a07030506030c030109080703112e 83
    0x603586c05404a400480c5c104913003900044000307840801c0800c040c0350754400224120000d40300b0301c0102c0c0d14000b1b81d9001588038200300c03854620719844052440e4a5035400f1034215400038015030300002c2c0600260610303500c0512901c40118401408240325041c500100115031000c1d100c001c1062041100200098010050320100c0b90507090607900c1e070f5160300340215642070302e2074010280c0c00f001039420200040343d030103140901710960f08541000ba00c0e01c1490107a4209841c445035011090008211859102028008003007041c5041820003140c0001c400c5d1a800260b8100c0a542010a08044c00e4040362150f500c40c031a10b10040072400c4095101501d0b44101814690070180c80f940081c05002c402050200303090710741c40d5005c400c1c2ca44107000800414041d58032070301c04d0040f0701d086411032505002c3c50039140d0b0801e050b685000f41030b503401d0701e5030b85d405503020001d0f00900c2c00d403014071102d452500511180100308001101d8070182c2210886a903d411602840400c08180100b0f5112 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 12487578 1250 12486328 12486337
    0x5070320040f0e07020a080c1f02070b0604021c0e0109120203030403050f070c03020d11040e032503030b0d0807020108100806070e0f0406120b0f0c0304110a0308190206010603060803 80
    0x14000440d01340c40f5403c00b02d04210138508080d25201002408406007580003170f140c81c069242005200c2c80820031101d210aa12030030b4405000c9a1030500800c07050300c3e140c1e00810106808081210181807040e070050260b696581c52031405956480c9190144500310501d20720300445807002c1c1d4990b282640c2c01400602658005000003400480c0010400421400302405560010451001d003c0d5070300c1c0000c0c0c40000100c842c0e00680c1455220045180e0005c02e071021241705840a40720800d5000c400003800509500035400c06d6151000c1c44200d45945420740e6210340204142a62150f0b180009492940054803105241403100b40c1000107a40224003940c10a1043c41c001103d48414400581e01c85003a070682c030b5000f483c19400180c1d40c03412004e082500740c41410341040a82e68034031030910410040303640082901c41000020300003110100680b40386103009142c1103116440f502e40d10215040b50780c02190102c14482c5101043d0380402c003442c010242468107001d503600f48072690303031079004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 12488828 1250 12487578 12487589
    0xc0304060e03090a080102030a0b100c08030c04090c080103060b090f0408090a150302040303090f0b030106080901060e0c0a0e040603051905030408030d060e0a0501050901030210030b030105070320040f 88
    0x1914070208441410074000c48040b07030b200400d64400207846540e41c3d8000d501c2511a100414908021500107062041942d04101c00b90703280c1801c80351954507076005552008007030b0340404000700000702d01d03403081d445925824503c5d580c50740010340c11032034810b0032101c550039078900c1100400c041000c500e0800c0011075005620040c0340352942440d0011681c0d8181c207400c007000c040000c400740c2000f90b0340b40d400341048034000c6d51749040e02680e41401817104140c40c025600c0040d003c00050040c00d0003408810f800c0b03003180000141c482e03600d100501d00394005654407209140300241845100340e000d144105560740898042194901d10350302e10355154807611422015035000340c044424030106009540007001800140c2e0758803582c03a07684c07800a20890007840300f00d96006003c2048003405100d454180c40d0082c00c12180da90a6400300480c203009980300e1801c160b25685501c00503103007030003490302036904c644001c038550610400e075100060218000c0720b03990106100030005100e80402039400c450 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 12490078 1250 12488828 12488831
    0xd051602040f0207060f051009060803040b07031803030207030b0606030603150601030605030609070e0702060c0304030c081c0614010c0317061f020303040c05060403030f35060301050f0c030406 85
    0x81403000d80e00030703020704d40c0c0190006260501c010fa0b404400d0b084a0300c07d40d000304690800e2611021401d045030154007030300005070f1003804140a603003090030007009034a0003030400c500058030220781000303002d955070404c0340140c00c40d80c0100200000c85100580065089500605518060001c240d541010580c1111604401400325a040e4081d9002d900502006800e0300d1040c40c207440c3d946d94500e40c1e44160309101c12010f000444942c408200a8011441800c4007460f42d2a02d440071603030ac082c01c100c20313919510300b080710681c1c01032405452288003840c20804600701c4e180c60801250740003000070f294140701c00b14080000007607218101880301d0a124040b041d031911f038080420141e40300000c0010f51303042038001101c02c0e41d4000010b0b51080340320f81c2000384101d40b610103014150240b40320040101c1e9050650b0f00381d4900808400c00000d1082c0c0130704040145080f00c1d14618840d4140307144010007450140701d0305040c28003580707034041c01113241c1056900701400342d28210301c0000c01c00342034903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 12491328 1250 12490078 12490091
    0x302130902040b0d2402030708010b031e011202030706020705030a02040515031207050f010b01050306010818120a020105010f060507080703020a0206070804060e0d05100e07080319020d05160204 85
    0x42d0b07165070104910701d001810601e03440c2654076007801d2000454060344802d8414008590034000c46008803803040c41c0b113943c0d0401903440d05031003980c6608045e16110103051011903203085030500d00b41d00e9008190300c031601040c0e02c980e8010302d07062034001d41198045401580081c4440d0b207000440c030280d00e506560018543d65604000c40481c520102e842c5d905008105401615900c0c503005440114001ea044e500c0103c0c090010030700b01c41d181c0e184036020940030310000e800b66000d040e40507070047c041d059500190402c0c0b00700c641448100c0039450140c000c0414908401a42407007600e02510501162801840c10480050058041c0380401003002800282d04810180700340b00c5078140d51740c06030445489a04074981158550094002c0d4400203140c0c8981d404c07a03290a01d841100b080e00880030f03140034078a04649501420828201c0d6503144a09140094509010001002d000d9103012605c00005000d00009080c08410031100c0e042005c20f011014005032800340d58031005034105c8002440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 12492578 1250 12491328 12491333
    0x1305010f0204080601050109090203100506030403030e01090c08010c080906010b070213060303090e0906040b0f100308040e010608010f060909050a090b04210c030503161407030e031603021309 84
    0x54080e0300c2a120925001003400100c80c81c001641c3c605844090302d4884d10a41c40701c100501700c0c003086611800c04ac02c48101089941005001103070404d00a01d808203074030034084011429a10340800840b191126400100305130f000030b00c42c140141c05140b4002420381081540113550300c1040c01003040034880090b2070301c119503131880c054450f40c200a400740415556401c0c05054079196224600c001d440c250005005480c0104e849403040350b2105403e03429031110207010504520081000050b5050300030003101060f03170840a84001d160007100100340b98149400100340b90010b134885401030304401000e1140d240c00c9044201034540b03520001420799125080c04002c0d00e401032024014018070002d220a026030102418103200c103d00d411381810600341e004850f0021400d0307000d4000344051001c01d0602d9000030001150050310318015903540707a2a420001d255010f0401180821100000b0520070700701807000e052080e0b1042c0c9110788081c03540e0082241d141d0070fa0724000c1401d0b41d41400204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 12493828 1250 12492578 12492581
    0x10e03010204240306170304030c060302030103020607030e0609060c0115060908030d0207060f05010603020c060702060c0412020609031504050601060f0917070b042c010503070e040503160f0b0618130501 89
    0x10206c4003e40f10b0341d020f0075017040751207a0080c00280c580700c0c408100860b6230b90090007201e048960140c40c1600d42a11500c0c22629221180c1c1555400301041002181da0764031318002e000052801d0000040c042c1064202003041c0600b644807105200c0382c0305040180041c0401950003051882d1005650755401c0d291010080161011258506140c44008201154140e014040b8080341501b1100c2c80c1d2510001a680d480d012100054556810401030181e23220702e11400c500ca52003d4845810001041e00003800e01c110340d8408024910400c4c01c00040c848108900360050601e8105800e160908004c0100380c60714500410000c0847d0741c02d48042c40504101c030728024051080f400e0b445684504112804810148440b40150608040800c44008441900341250030080040c01c0355403401030080d0300d4440042098446000a2111241c00303040c400011207a0751103203141406d01c20641c540701c0c1c3c0f084000750280e80128a20350100314402034107180070303401080400010f4091061890b1060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 12495078 1250 12493828 12493841
    0x8151602061b0408070311090714030a0e070b030a0516030c020d0807020a050a05030a1d0d110d06020c0105040c06020c090f19060314010b060f1e0702120a02010e030102042403 77
    0x854070f201d00d001c00014407c41e004011089501107405900c00e4855803011184a950501c0555501d841000030070f42103100d84d400320500e0310168040e1400c0559410310354a007600210b490480a0340c0312020032001461008000b600a201800c0c02c00034021201070095071480302003603d900380f0030000f020030192402040308258083c3d100c41100c1d6440d0b0300e072a0070358070b0760090060710012403c03082865001d0004220407521003880940005880c0c0900d44a08581001a265080d002100a0b0540001c1003150008100c0140050b0010030300d4145442e002c0f400102a6000c02c3c00c540128104140e07540d12050305540140c1c03151458007450301c6907113149407204086000c01456900d0083c0000802503020300d1205043c000f00002c000441080c402c0c000b16204841203041d03a00401c0240c0c0500a070206d02c04011084011110b9007049041d07030210307803440704a95041c0030f60703444070140a046681c041078010030160180e000f03505180c5070555190029003d201c52510311000629040c002501c00c0e4040c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 12496328 1250 12495078 12495089
    0x41a180306130204050601090621020f0a0207030b010b120a090203010e0a14010506010f090303030c0905181f0807031412212412010f020408151602061b04 68
    0x100c50504214111510b90030b200e40c400c81c000c03820b00b8002000f170344c003030456402150460740745d0b20198900b4001c0d900500320030302d880300b4034240e003031018070101c42d400c001038841110b0720b40003041044d0440c1844070219005030302c41128500c042005d908003a2000400e04d4004000400c0442e4160b114030020740500310015000b60944182e56200c0140003420444005124440000700a02d0b2100e20045844070000044540130400001341040040d100354803c0040160514041c04038176143c10019103140361241031426141030300403d00c1200b9251102c403501c403040200051414510702100b941e100c0d003840c40064203010009510b0b1260a4080c0015959094040d8a11380d4450002280301010640c000d04014000c582100041c4028540ba401003004a8043c52800c0d0000f00300c2c04200c2d400c0001010300e46d840d501c4002503030300070b0b620340094005003a040001c3d129203445885060041d103001808046440c400140d580b03619500030070304c190841000e00301c0c5c05e900c0c16400c100003ca442140d015 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 12497578 1250 12496328 12496333
    0x201090503030a1d070b09010f020c06040f06020607020604051b040207020402030a060e0a0b031005090a0203060114030f01020f070f0f0503040305100c050c060f1f0b070c0b041a1803 80
    0x10401e6100d41940300c0f03151500c00401006200c04502403095880605d030041d00171403003040140c2d2145600072111158480e010713104561404022a0214881ea04241c0c051120045110001c0c0007090301482100c1e408821031008000340e18080c1c4a683d81d594810540e014810b0403107440d55000d4546804595001d80c014005550b28180308160380c008017114410404140c00c00b10100d885500381e0f004080007084c00800a041070701c100b48010000701000b804803100c510a4411030b400685051158500038141101d10b24030341c00a12060508201c440d0001e511148d104001c2c0110342c0b00da1000303890301c5e150000c40e074441e01c405902e00141780414404d4050300a01c400308001041020000b0808a9041d0f004c40621894400e52405d030b4003402951503800d81038008100255040300e6040d003140d0721452500d0712010b44039690b0f24442241469800c03e44d00160001550720502003010808402840343c0b4108074075161a1031202c030341680c0608490700090300c0014840104000ea0501041c3c0c07071000905 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 12498828 1250 12497578 12497581
    0x2090103080c0304170a02030f070f090203060604030614060405060d031d0409050307060b1804050a020d02031009060902090717161202030712150810090812010305060f0108120901030c020109050303 87
    0xd175549490f0000308074424411072841420541010504104584e901052a030046040c0344040010f900000d0600c5d800210500c0000302107852801505848540c106014103c0d040c60b030305000544100a0000c2d000300542c40d15000001d82c4100d01e08101c2c0300d4481d40080c0c010f0000c0000740507005803070000e0240d10022070076005020b40c1e80e01c280c800c002d088800582001407044034070403064040710f01030800e8100d03500040c00341c14032543c0d40e02d00308c2c402420b0750801d1182400140480302d4200702500c0665a40b403000045080210403150401a1403e00d0819100c0319403400c180c1150080040e0b40322680f003084480e80c1800392754010401c0e646030a0071343d200d25050900800c00f00c2c154460001050400342d4140c801081d154411080d201741c540a07240d0301015615031030207030140032002c503524181080078404222580b4180c41c00385200c0c0c0e011307001c10305004c0400d204050b81038010072042c0d007250b0030f91600710b040741c401ca40c1103680a007408580d95240c00c10513401000c40c030700050b00d01d020010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 12500078 1250 12498828 12498869
    0x260403050301140d0206220504020c01021b06160c1104020d02030604150501080c0702131103011d0112021011010c050a030c02011b0302090a0b0a0302030a06060c02090103080c0304 79
    0x300a581610380d03100080c0e100c290b01a00b0420030404011029410620070000c00103107403444406a01d0070101c00d244088090b80d1200420100d920a00941080340d5002c54848008802105001c0c4001103810042c105e504084500603001901417000009101c0b1544038402004001d0451071825000148211f403103100405241c4c0c0698001c4481d01d20941c50540021111000000080c01380c92040e0b4a1034041d50380d407440f40442e68000d1800b80e03031000c0c1600c5400c00b18441401040079802a01004941380c1d45002502c501412070318083d21038807860440140422005d04000c2d500e8290101c4040600c00c144003000d541715030303819000745480e5003014090000b00750420001d0003600c50558041140090380f210481c00c0711004980208030b80c600320740048006110742c0203003044403c01000340f0406a52040f500b4683d600c801c40d0360001ca500407003000101006807140c43c0080403542004401400c4c164001503110105000082c03000201082007080d01c00104103403009002c10312007602c42d0402c1d80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 12501328 1250 12500078 12500087
    0x4080307030e0d20010b3307050c0f060705100e0c01090e01050f0303091c170405060702010810050a031b080102091e01030b21060a02030c0a260403 65
    0xc48024010030304000055065000001d16110034082ca0380d140d0f101c085603102050b030100b000c0c41050798550b40303481d0603031580d175104000391605191801d902d41d40325614031108801044035040d0200112800d001c40400f15002003004051508216030440707100380c22400244182c01030300d00c00741040c442d10324003010781c010700c2d8001c0c0c10b800f5640c0d08566020441000455000d20305015071600e071b0440c00300412150811081c1c038000310b1001020350b802c114280c408141d680c0107400b8030501c4150301e0b00405007480724852030002c4a41c031504046d4036290070078010803007070b108003070f00241000f00719000240310081726111a000380c030004200d2501583d0b07909000c0340045200c68080d00c285907141001070703901414401c1302c410950280440a4401990001001003015182c816040c543c90324071101d0396627a104021000c0d0030700007481d00f00d51a50460b522f40750840050160541d10320420601c0006418042611210300d96440c0810701d03100b418104044168140303d1540e242c080c03c2040c0400c15400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 12502578 1250 12501328 12501331
    0x170304110312070204110412120801050f060301140a1502010608010b0a05030705090901020706020301180c02010501060203040b0705010603050714010206070c0c090504030509031c090603060317071505040803 91
    0xc518440101414108141e220740002d04a400e00380003c01c4408014281034005c4e100300205555001e00701a90b4007103c0100c1c6049041c1124851070340059080201d03004440c060140c641521039000b090080d002065851006001d4140c11501450301c4410320b5561a00d41006400756211130b010a00030076101902034580d5008040c810b50034000861b40ea820158036910441d2801401094014a01800e008011030080e180f45091f54003000000c02203803035070000314000c1240817100c1c0030f603481c601c031000e04403000034419030116410b00c001001803650001c15141616232041e20103035100c0d454900742c0e00410341940010090f00038007000040f2042c0000c074000301207400ba000d480301c41d03a40c02400c030f60300018100010980100d519013408025550b5001c40d80c007d101e403c045281c000f122002070310701041051a240d05078620300c00b0003412584a09c840009100900302840020b0440e603600d07440c00e48851207560380d080c02103248001d01514401d524410390914208001d0350520b030800e407a05600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 12503828 1250 12502578 12502583
    0x1050106031107020a03020904050f06040b10120c1e0e0a0603020117070807050a1b050703020411090924060a0302030912070b181608011a060a05040b030a09170304 72
    0x7a00716142c40d5a5002000c503140654003d010322400da0541e400c110081102801c151441d216000060504d98810403403070b0300960246000c07048030714100000c0030038045c0d680c010f82e812500180d51440004da060320a0020384555058003e408100784002940800c0a5402012012000018040042020383c8003e040e02e000ba40c4a03007000380c4003210705541075825580703140000c1d014400600860710900162000704070503d480c6a2030100c4080c14404070f01030900940b05508001d1003041149441d100340c0307410300c000c0a1201d04001c0c0090009039104001480c080e10010b000c884501c401c0c0340e1401803c11780e80014070641c0c0700d003981c0e04010b00035001110407150341c2c82444181d0200c5603814003a40d1000c2da111000c0305070303591025801041c4c6a052104042688158012224410030180d12000030300005000001d60490403210512800120240380340994002c112001005912008440941c2d031440d140d1642c0380c8500c50480002c1007861005069003031041d04602084244100031406a070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 12505078 1250 12503828 12503831
    0x80309010605030309011e0c06050103030e040f0513020114120f010603060501090e01090b03010905030a0c1514060d150c0306030201030c1d04150e13020306010e010503060f0903070c080105010603 86
    0xc2e2510b0505a49204800c0c4060105114004440d0200d10852400c04c00c60010701d800d940c040c00b240c1e01e000540e0000e8204a0114030801d1080147e4109441280c1512111007014040340c200700824907a010110b40f0b002e4100042d2294071120400254200c1d00c0600039003880c0305a80c686402c1c45031004d6000e02800c400281489c20002d84e96200d070230001c0170356013042c40c2201e03141d00e8000104000d06050a20396059503c079207103080450010f0000c0d01c10854130b610707a01b51050261034808800444805c1c819031543c50000d454a61804020b00154440000d0b00c500400e458103040014410042050507500303c0d0400c6c401e48500c0f0350640040b01164030030b8800b8004c07180720a0080c0c0d0890043c2002c0541802e440c80c070b581c04c82c41c4c13641040c0d02c1200540c0f80542055265132541940c2d103811160258904a4000d004045080400c281c0f801044c0c1290414455414440020780354071024018108020a1b80c0114425403400d00403218240c0d80002036100c46035980b4416400f9140910800700805e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 12506328 1250 12505078 12505091
    0x302011409060411060903210a20070501080601020a0b010b04051206060d060f06080703080c06010b0313020103020703030b121501090c140c0a080d02070b0a020a0503060f130908030901 81
    0x3560000d0064003c0303600001600000d1305210a1111542000d50300f40d605108080c2800145500348000c2c00201600d002c0e01c0382e80d0703006014054500910b4a001c0559001955500d248202d0082170802c2614424a081c1c03955403107010040f4a040c8140303c0107000074501c800001816191400100115075081d00d14600c01c61450000035146c1d0307821184940c02120124005001a01a51200c0000000c00d007000803925105c10080745403c4280d0000c03a411200080d9a15a90b4000c100300c1c0d00405803100036900c0c0d0302d0030680c044244100100000d05058000c45c0900802d4065000050100c8000d00f1400c01c1145451486580b0010710342e5540180c891280082601003081c05003205c030720502d0712a045081c00f5405108120792046c002a4000d015018120b00010301000050000000b24040517884036070508200c0901403014043c01d41d01841000090000ba0300070b8181c80d0300c400708546825a40c9210381c082984961041c120043c0146032480850420090001550090101c800200100c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 12507578 1250 12506328 12506341
    0x1030b06030609070c170408060402030708010c02070618090203130303050f06010f1809020318070b0304021806181306060b0a05040b0d20070302010c090b0306010e0117010303020114 80
    0x210301c400e8901c1c41e0015070f40380000704040c0c0038030702c5004014403a0a029605000d050341207007203600076030400c8010703030006c206200c19890100900b20140c25500020042c140142da07001e507960b40320340b10740800c0c0034002e00c82e03809441103a540c4200800319582d043d95a403a01c2207100340c44818000c0b084000c285010081100c40d40540c6e00c8612508040c1c544d030355200d95030f1101b0b480d1400d0548284da407d0009960106021025001450041202603c150364251020065906100c1a034014104034141801000050b13540c0e0394401903140420384412459886071008620072002400081600c0140303102884a40c551103540c081510b0300852081000503120b5501c1083c91080d094242d00254040c0000d001403010140102110810400000740d402044480310106407511204001180d4000c15160289a021f000304900034007140b0340f4502403414407103034243c5400043d040034100501c0006007a800c0e402561401c4884001d034100410303a40c1d4900c0c00074060000c03060007100b21582d05010510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 12508828 1250 12507578 12507589
    0x301060e1c02010e0d02040207050a03050403050f0c010207051509090403111002041206050601230301090605060306010909020c030d0203010b04090b03030a09030b04080904090c06031802031504020103020702061801030b 96
    0x1c03038550503901d4860800003402002040b4010b150241c0e8410b50030001d03040001d00400c0b68810312480790301d442d40c0703480ca1400e01e1802c0ac0007506c643e2059403c00b511600580e0303800300e40d61041c2c80040790052910780c4071064101d081e0207000c6640f50821008000d01c0241500055051890203080080b18640001d03148118160702a5200d42c440080b51911568005682030308601c0d4060300601d0010b44840b411460240300c08400305020180701000801404280c0040c007824014003400d0b80c20918500704100000c0841d183d40c411030701400c0c2d01003102c40b80071605008984c2c42848521080d52070b0b5071a08405407807903000d8440c0e0654140f0703002d54801da904003c4217441d07200a4584500075075031319585507903e0582d801842125640c40c104602940c9584520a00075640c0c019010040d0311400d00501604881c41d9408001005001c900340740016540054142e42c0f501481545042c2511240300582c0a070141c12802944a180841c0181803002c136180001c0403450244e0307041c4044081c80d024000d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 12510078 1250 12508828 12508879
    0x408010c030e0c04021312140604060f0515060a0309110d03030b03070602150f06040617010902010e15071104020706020a050d050105010801030b0c07030e030601060908250509090a06020301060e 85
    0x21b0140090b4100704465000456210000b500038065a080b81480c01c0100d800c102040b28201c400307642e02c0381011a8036207a2701c41c10789d01510440030710401d08500d10004030603000e602c040b0020113854002c1c400c10040d400c040e15007400c4014002000084c50307450b0203809021241c0101740640314075000044d02c9840054542500114003180001e5030305c62151014136802c0c0107209940081d1074540001d00c01316140708880144030a48000a10040548001040b100c142280c0fa8810404e03d182c0701000c02d0000c00320380140d540710059071a00c0c810000032034007901507602c3c0508070134404a1111010781c0c0240041450942070b2174100300716078841c0c0065602403400c0c0800351400c80710f040091040c2d071300d82000300305140c0642060034020b05084002481c2c01c4d0242c00c40030004d24400c1c0200303c0e580341003109c104400d410307a180002901001009804ca45114445d00c1c0c441d103d0b0301c010030100740080c850121142e422483c1556030b50385a40016145007141c190703075409509540d175080000f80c101034410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 12511328 1250 12510078 12510097
    0x20d051b13020424031401090204080c090c0a0513030c060207030b070302130509090a060510150507150b12010c020c09060616030311091207050910060e060304080408010c030e0c0402 80
    0x10080e550342d001142c41311100c102d500180340c1d035002a160204807034908907008021040026079140d09151f1018241000b0840e12400740c40702d2024440a101800c0075107400c03d040d403520356100c100710221b902101c43c55500280c03140da01c540300840d046602103415800e40c0e005055a6116441e090012000c9114514134083c541900b4201444035141c02c006460304900c0c1a0101c944034141074550700c2c11100d081d14624006c2e240d0303082c20440001c207054508041003050405504045017900c03100781c00030701c0c9510045225903820080c4d985035555a10700c1c000c2c0402c04004c1100b00b801d030300080d42d9080c0c9150f20600c11644480001c16500d4508100e4160a007041c040c0d051a04c1540e40a6015007003032040040c2c4540203108088040d100c40303181e107000307001c00350082c0202480d000500c40d1211002d0100042801d0f81d01c0c081c022150800d410f002c20f00b00648649651f590b590504100c68019500035000a500300391541490070b6042d0407801100440f03100391a0542d800e001000124404c05400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 12512578 1250 12511328 12511349
    0x6110705060d0605041b020d0203090906040b0d080307020c01020114090d1101020c03070305040302130b09150102010f0603051c0504061209080c060c030103030e060304081204020d051b130204 84
    0x60020341072070720191004101410300861080e03111800242030b220000da1600511002c1820501e11550412a2114101d214000346181150070004502c00000041101c1c0c01603441e044400e01684400d0051103405800a00c844e46a09181a009483d80c00c1101564019800d003080080d4010901803424007804088008040a00171a041618031828241001110b07550030b000248803180c0500c02001100e21a0ba6a0740c0d549046204000c4071444405c0c0b900c440ca483c110ba0340d0aa07454040b042c41d00308801c3c600c0001000b26100c0102e01400d80c0d6001c00010f1800c1c103800000b00b00340000c048440c0e50124400a03591031480c801150b15025070322442001541c80e0070507008003901070340801c982c01d0240c44400e10301070700040300c50702d0000b0030349500c011000d000004000703055201d0314410b058001100c0c9e103450350a1980319807207540624501c2201c040c5c0b000c03002c901155154145004001c2d0301c5000d0303070700d5900109003481c038007128050403234010000000c440850000b07070700c03c80d001d0b03820740201c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 12513828 1250 12512578 12512593
    0xa0501051b0c03070b07060612050703020105070503071707020906030105090c01030b030c040507050406020601150903080f1c1a0a03020a0e060303040e0f15010804030c08030c070f060e01060611 85
    0x700e400d1500000c24a20900e00a10030310210340c1c0c50900442d0003900c00c0604241e0b8901e55840c0c441d0880c1e06d00d900010b86011140c410000066000c515001104e40900e4210b448022904086003580310301c050017404d4000c113007000d03865401c10001620003140200e50400d440d40d9018141401d03180c04580d00d411580210070041c010358081d902031510355a0140498034126600380200d001c40f1404c0e556a40800c4002c20b0402ca040e50410040340540052005110303010400d4038050919082400300801c10f0130302080028407003020400f80c50300c43d0010f0302840885000714240000804280c00c511642030f41410702e0201034102840c02c0400c0300c0d805884070582502d00340300003e01606c00703041c030b036494001000002110100c1815031030264080721101040c900f032103800031317100c1d100302504541800544010400800d8115091010701c0303030400d079603503940d80da40c2d821142944600c0030014a044402808102403003296442107090305041030003000583e8644000740c44100800f5000b800e290700860 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 12515078 1250 12513828 12513847
    0x30c0605100302030a080304020a08070e0a0c03110d0f0507030e060a0b0316091b0c030e04050603030409020a05070b09070f0b070203030910050a021513020d02030a0506040b01030b060a050105 84
    0x6109503489281000d8039000c442d201e0f40000c2c20403800303240076201c0c0301c80801408113501e0485510342c024020f60340141403040c604115200d9501004140d081c400d6910304c0016806406038105000101420510641c2c41224000140003411490044203171a07140c403001035507090082c80741103a40100c920007001e4130780e60044a44007410390208140e406021b010806410180b2003c4104081c000940d00840e1042d0112941442007540015807400c10203141c10a0b804241c00600c6416003600942e808103050b5214800b20b4510301c120384c0b0030900b0a00c0040e5404580c2d03070020180152611a5825400c00d45031000ca0365503803809401042e812201c5540100400d003182c1004280582c4047c040c1c0f424200c001000883c040c4042500c1404103000061400707916506010007201245014000301b0503060082100c05044802d00c0000c0c0920320424015080d03603001c000303401d03100d42c0c414200d9070107181525000320b0140c1d0070b101c215403000c05031020030214540b00c54842c040d10f406a41d078608280b0b110 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 12516328 1250 12515078 12515081
    0xf060906050310150506030405030a0815100818070602030a020106120308060603040f02030d050a0e0306010303021c03060306020412030f020601030206030403050304020607020d08030709050f030303360106030303050112030c06 99
    0x10203134070000c18a034034000119522800d000e9032285016901460300c60300d070110090020140100010380d16040761601c080c0c2c5035201d41d613005a9040a03d0180d03203550303918010207900d800480c1109540d102d20701d07001401c0c2e80c2c0000140144107081c0e00a021a60780c07120400f14258200702e00802040306c41d0001640c40c01d19102079680306014105142c0c000002d500441c1c201020f25210303000241c00000c40e4419640c101207480c0d40e0030700c1503008151940c91510025100c0701c091a415400380c081000745035441d486504084050350300310a085603980c2c0e8a2203048407502a0900880100d00c1400d124146140042507844c100ca03000b803c21855035407155421111740d0700040080741d002500380450030160300d81c921200c100c0780c0b04000300c6036241006200a84400e0b056413045110304600307541c14603070741c5000c0180c035000081c0c07074004000d51000c00e40c4ac18030a183c20001d00d5400648a0182215840c15004201200c1c002c0c1c40400507a40c0700c9020314080c1014410140c04210194440d01c00076405 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 12517578 1250 12516328 12516341
    0x906061b030e130c0309020427020402180a0906060e03060709060c02010c0f03020604060506030712020405060301020415020a02011206080c10110106030c080609070303080429010305010f060906050310 88
    0x2411101064203c1000d90111004804030000203980d803513924085052510400d900d080c002440001c0c018100b07000682040010440203014a4002c00c1e14540058540c10350551414014030140e94191245c203002d0040140e0b10581000800007029043d41e4100403c142c0e00880c1155510002107042038401d03644071401c04801c9041203142400000411500301d031204c14144070b6401b1b0321079030030320341025016181e010b442c6611139000040c04124080c00e07c100b441000d07078151008a525940e0f240007d00900441d4801d6041c08000c0d499210711a41c04900030305028800d03280c5480d415013804155044646502405000d83c2c00519080014508000c1080e80c3c00586c4ca40318188400c103a10690a490309176004507030b1502c8011007031003024000d000b116405500c003401060704500e9610001c0110401900192991a21013a44046000921611501403188038680b05c6075596900d040e600800a00442410742464041c0100c0d801040380540011524010000c1640d00c0315943c00100601c030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 12518828 1250 12517578 12517607
    0x301060f120608030a08070311040501120605030a080d051311010c06060801020a03060302150a05120c0405060414100206040201050904110903010906020403020a080c01091211120105010906061b03 86
    0x24214840502222140100d10143c190000a0750700c0781013000e80034202d254040c0000043c1030030302441c4101d24420805480450f0400d11b090640c49031141d00341c000518068200303640500401e4103030418003181e038004113900034109504110710380d6400350449154401d44402040c00f402410406c180758415176001e01154065400055030070340d105c2c80c0608990014110001003a100d01c010020f518150b190010b0404580c101e0910b0800750341d400070803d118400e01e81d2190913480020500d1050f4000c1587d0142501070460380d0340d103499020540c4095024100700340300e10f08580132042503510101d81c3c00e0090340e041e1a40c9040c505400b040101418402118907201c1c0c00034000c548165400740207a15040740201c10041e40c2d02c3c00e50050000c9003280341c00001d2254000b801050b0243d03070140c0410104e40502c03030086500700d0b880c6001601d14600c503d02c140e20070720840070461030400661081e4102c505194040084550b5054150741806000301c021480c078111030940380110b401401700c0088810b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 12520078 1250 12518828 12518837
    0x806030114010303020609070504050c0904050417070803060406080a0203060c0c2803020105070f0503010b130e0a06050f10051c0605030a0b04050d03090f020f01030204051e0a090903050301060f 85
    0x159181c0c050903030010241d0003680140d10003000e01c60148018400800035080a88060109241c003025207980c0307116103805103000d2aa03800001d014032411000d411130031800301d1516503403848581040e1444e0b81040e00c10621980c81c3c46e2001840d51400924586840d601501a0441d42c1e1010021034058201000d00b4030540940a07080600c8070380700302d5260804144140d0060241007a00b1b00034211440204600e06118161002c608450b40001c20f032411526031070100b60b0703604038208241000215035070100400038401c03000c0c051820515000b007016101d0503265041c0b51042c07001085101d8515285e80408035a040144101e01a890809280c1c02c0700480c0307011500d259038102186c50004c1000342504c0380c900440511040140c14002900c140e8801d01c1e003804903204548450080406060009125203000302003210940d000ba01664000d0900604401e00c03001c100c4240c1a00054044865200383e0001401240303040980c4604080c0c590140d0b036460640e800c000064805499406c404828031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 12521328 1250 12520078 12520091
    0x4030306050a08011a030708071404020f03010602010e100204050105040303050f0c0703050a0b070309080a03020c070504110714031608030a020409020706020d0b0a0608070e0109090c050901081003021008060301 92
    0xe07101e41c1d61040080c007a000c000242045c0e007030440403510910342c010030310a40004004112240b000101e010136140c40f001000700301520080020f000348074aa408941d40b0702e01200005260360194484903480908405680300d203106148030104910490155a0105800388030034404030780300f08098140e80100c008007910340f40680c00400e2030018203500071500c6d80e01c200c180c0002c0099018200d0f8100496080600110180d50740e10401d5008101c2c0540c02c05a0215100d5030200c02000420001c05000d8020000c0d144500d00b0b00c1c005511405003680d004142500d81001200000111214001d03075442048100101c0e540c2ca04d625400035005c044a41d07000d01c0045030890082c802440c1d4544140c80050781d0351109801c40d420f842e49088201d105801050b03003000510341260310319038844854508030350a52045001a90480080d400031002d003440c0410110440c0c1c1c01c48010000030009332100342075503890050140030031105010080d049010080c0c0302d81b055002c0c5c10b009807c22401030020030030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 12522578 1250 12521328 12521339
    0xf0e010504030f05060615040b070206070602070209101a030108060106030e0a080a0314010504020c060403030b040e1009060e030a12020f0702090a0501050a170a0b04020d0c06030b030d210504030306 87
    0xf02c000744082034840d5040241880684c1c45c04803418089002d955001d641010301c0c003803c070301c528041d40001030b01401c4005510320401101c1e5040703ca51035401480b0007400e06054500905080c1c0038090250780c807072020383c200080f03000701c400e0f40e0480740c1d84801000a40c0c204141200582600c5007040003500c07a207a002c2001400f24401340c14a0380c803c1d6030006011006407180c80005906a0046020f903104000c11540c24001040041c3e000d0380505011070305088400125000b4440001d61801070b0245000c417006140381038000711052405a18140140700307030b02940d96201d10840c0006008181d00a1000740f084c0032070307005054078100d061070150500240e60045681c4010460310016019600d0005212924148a400003e0056a25050031880d082c14000c0d90719515100c014001d54500340c0050110f54843d0140d2240303d50000c0c2c00e0700c2c07080e0380c0c000190160490716030b050311034080c001c440d4844500c513500c48448485102c1c1d00c150a0740200b44207900804000e80203600300b540311040402c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 12523828 1250 12522578 12522593
    0x21009080304090515010905130506030c0607030c0209010501030b030304030605041104020c011d06130f0501060512030c01060509070c3203070302010609020f04060813020901120201080702010c0f0e01050403 91
    0x2088403680c0480c00340b0780105020307100c0001c24105814401f40c6c00b414480d40d180c00400400c20b0760855400101e50b1220400207207800090121142d04c1200015200304160303110304601c040070720940710303119144d80317503001075060f101c034200d1041e01648140400c0004c520b061300110340182c0a984650a240c42001c00305044e41d00c890303540b0b28103a440d0500b02000350a07101c07440240e0b06149000d422541408005804001c6003040d0140480e01c0a86400e42407110a6114800924009020744000100b0700b618940740c0e0011220070400754a8408000740c9400c2900c11940b04402907902c0302d800c40100c0c0d07215001214103400104548411820300040308024000c183c1201e180c0c040110f881e45d040b450002e00307540440d0000c0c00140d00501c0048218a298400e8600ba00c01074280b0ba54a50f580749801880e102d010b18010358031000c48400001c152111a171121000360007030303844640b5513a4402099090303d503c0c02240c0c00095140262019040c0f142c0100c00c0600e2051610b85c1c43c2903a0386e00c5001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 12525078 1250 12523828 12523837
    0x80a0507050111070521041502030c0114040b0c0c0607031a0d08030a0e03090f0f03030f07060c09080d0903060b01020c0306090d08070c0b0403030f02070b04050703020913020901030210090803 84
    0x203610510018111040c40b0081080240030780b100c00201b24680303c05d042841e06e41c080d503c5080304483c0302c1ca9540c101540203106a40070255280000c01003030010342141e2102030801d443c152a2100c000c000719469190075404c035030185040c0002041d0507203408104500a109414500341b50b540071901c0d0920036940c021070010b1041c0100b124540302d04100c40b20000710f40c2c904804178130640c0100300000c01c1d0b40b140080300403424011903142074400c8401c4086030941c810400c48a101060026803030040012944c808203545a1540e111b0200c030f501d03034840d10b80d50110074482e00007051202004000041d19500704164060062058881248040e8040303403a01c40c0a40e02e01d41950405000c135035682d94050901c030392007909454050380010b82da880d0031201e03100c06030015041640b6202c1546d0780510b20340413119040c2e441105450b103441d10781012529000c99000480c81502c1c070f031010613109505802c400380003580080801c640c41e4a150308120322044100b011030309102c018100020307401c40600182 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 12526328 1250 12525078 12525101
    0x80307030e0108100501020c1201020909090d0806010801050906040b01021c030f0b090c03040311011e02030702060c03160c0f0b01060908060603061b0a1710060306080303070c080a05070501 83
    0x101000441070000340002c24020265104440d6403102000707107030b034001030402c41700c0310541320281c89000110009001e80b18200d41541c20420360800d0010780c403000107641002c800d0969401040340c56101c011101c942d4203201d06584000b580f008140d0a1a06030b01c1b42000c000d05004403540b042c83d072251900030300480d41955000c03980e50b1440610329030107405910016903003100c00d00003278500400d014821f400040c0029040040701207448005041c250312119801c8181050205050300784491203010394400c0b40c50800502495000c500103a03c50300070380e4000c6006069441c4200808401200c0da03210a00080e03410028190b0303000c01103011424014042d1040f5070301c2d142c02a041400251400b200a07040d90b019a01500070030500c587c5490611004101c1030041d2651010030318002c13078484601c414000c40000c40c0301c1c184000038045907100e10458401d51001d01c100380d6180010303501c1c0c0c08216040808100d0b542580c0c400a8240e00040034041344d01e041c01c034207003403854907558210341401014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 12527578 1250 12526328 12526337
    0x40b0406120512070f0305030702070e0406020403050f0705010905060a09050d05161202060909060d05060a060f0605090916091802030402041b0215100306050c0a0e09100b1308030703 80
    0x3442446024050f0b03040701c1c40502d42d5145400001c0d540e41c0644590070760050104040030011402043c404d0000c40010003140b502c849450410f801c00c10f00a50040c0310454151003000c014200703280e404500710084480584540c4a044d107880d0602001d0381c0148850810000743d14400314680c0c0d46c241103014040c1c0103000030080c03140c1d40702c07015040c85182e0b00000343c03107210480780100503a100d10481d480c3c0b50041c0d4400d5241e44482d408281d018035428801442c0340580c40800200c540b8640c4180d045a10050b042c14546030749032019a11032103981141e64020111400140c41c6220308081500c401406151410a4581d51141041000e480002003031500d5000010f1205516050054013100d0a51a500200020714404040c3d90744040090381d450301c461080c0081c030280403000401004680000c01403180f0b2400c032030800c0b075503480044540d001c5800d80103460b685080080c4643c0c8900320715402018914100f800d046401d03040071040183d49078202c0d40203d4100402d1001d482620b1003901c1d07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 12528828 1250 12527578 12527609
    0x3030103050f0f0a0c120f0609060504050d0c020312090f03030409020301030201020c0a05090f04020102010b0d03080f0a05040b07030509030f190905060a09140a030501060609060807080709060509040b0406 90
    0x2901e5080c05143c1d00c5000d01544002040030110320032072440c000700e0f610044814a81c1d102071510001e5507992010190409142000c0f44050182d680c00140c03081e480340c81982c07444e966000044c1d41280c404100a500755010b0007420702404a131000078845000c0080445914a1250b40044c0c1386a1154000050440d0040010030031941c04208000c0c111008985100d805800e12000c20b04110300180f0b2002c1c20004800403d0959000790300910388010b002d0071142801a1504000e00034890941d85070070464072120000d9142c510b2849480c0c001c40c0c0c0000000c0c269100d04000b1009840050310704505030004202da00c060040d03e8000f0610121800d011200745505500050000300b51a44802d0040c8810440c01c610994018000c0c819180c0303100b5140f0742d118883c0302250040000380c000828039864060080707611a0001c81c1001140cbc0c02c0e40d01c80c0c0c001d555200c0102d507844402d03035000c000f0800049040c0071940c014000380405050103000012648400c1d8002400e580c419444014801d28004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 12530078 1250 12528828 12528853
    0x50303070c03050106060905010509090a112b02090108060118051305070e03010603120f0c05030c06160c021807170a020915070b06150705061905060f0a09020c010209030303010305 79
    0x50170014036140c02c1c035074651490800080d1591041010141c0318503200d400003049000071758007600c06906e044032000d4669840c0305901e48401d040d002034401941100002c00715020150084890440d0187d6410002c0d49400c401520f4004d12140c240c2c10900341e2000110702d5498441c0e130385020900450004c10941001003001e426059074a5110740a6414000240040f4240c6001010300070b8007407030038140303000c00c0910890715000c44440003001800f0000380cc0c1542100003179103a000b56404072142c14a481400016111418020002500504480f0600b804001e6800d805907201460b81030100c1081c512031100501010125a0244615170100300401c41c3d040055001d40390761500030102d441c0031080c0d22140d031001e41c0109202d210749940d00d0881002d10f01070381581d50482d8000212851401e0ac0015a40340104615903104000e103450001445031138040440d05a0400c09440404103e0404100e2006940080071010765990208281c10454400f000114004e60180c805400d402c034454 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 12531328 1250 12530078 12530081
    0x40c050405090303090a080d06090e0601060201050c16060b060705060f010611010603030215070302070203160e0c0906090f0f1806030601060302040f1203030f02040905040c06020303130b040c050303070c030501 92
    0x90b0a800090740107008000320000d00051045030303a82c00c0b80d1080d40351301e4541000c0002d48031580140905505105c1d40c2c3c0d000c1440020f101b41a280c0300e80003444503561b10000180c15018a0550f0b580b48142027400e00d010275081d0b4886101d074030026000074605911600c68501d09401030385e01e1010000c1e000010401580d1044084018600c001c000380308251441c0c600a64038000703100300d000f160740c07104041204903011741d04403803d10f0360240c20b941074442c440014083d030000c58400d0044001d00800021841001c40080b280040030040841c1e00b44120032007800800300030380303010a40055407091640c0c0751b0342d21950500e03251140d2002155151400d00c8c140750900c0810b0380003006043c010300c007d02ca280c0191003000142d5150000c3c01100341e2213800e00328007030280c0c84940310403184000380100b0703184410b800003032007580602440542c5941d40c01089039688021a441103200b5440095040020031442c0c01c02e0b080b40c0108883e40c04a41c0b81c0c40024207550101404032200f141000d005c10070080300f03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 12532578 1250 12531328 12531331
    0x12080601020609030a1404050a15030b030d0c0602090411130302130e0a12032a1d01020c0f0409020a0b0901021b0a09020304030203160c0807050402031306090317040c050405 76
    0x1c1c03014003402e042c40d2004030350b40d0094200490038401060a4000e001d03055206031390040200414800d10541d07540070303c1081d882c0302a02000028142155407540d030800003540075016403981e4400f540150381d9140d03140250807045d001c5904c0394039402c814500c0b071050b034098407801088101c01c821a5107140b04010000c04007400030306140303040022103d040b00000c50700040c01138102c00c40c541040441d800440050810050035004080d04641420b0325a00c06d00f00340c82c4a20254840030306007524090618610b10786000000d00603031080c1c1d81401d840c00c00444035580340c8400f5101042c115070703907030026065001640103004507180103c0d21011643c0d0420000035141032440740d4044505000c0041540000c1b0b5000300444c068001003c0340070075100704100c403c160241800c981d5506241c3c07a00140a5007548580262032240e51400701d22441e20b03108580c021030f44c2c8440c00c1d1103100d55a50792800380c00c821100f80c05100140045050108445c0440351140303202c1c10004401c01e04000411045600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 12533828 1250 12532578 12532591
    0x816200c0f041a0d08070f060504030e1e040f02040302041407032003060d0201050405040e0d110102180d030306030206030a050103050706080601121d0a0b011703070206070f0206070f1208 82
    0x90038041010b02504403070030801c0210554100704401134030708124242d485a24801000180464605001e21110b9800035004601c00d90315038040105440400c4440050011050304c003104c503149403403c80ca040c0d0310840d500c06034442c015080550301c1e00007070100c07010560740820035400710040020071540752043e441c100c9002802e269641610440132001d6000040509005d1803181c00e00c4825603000302c06427402880024020322940b0303403148007203454120368011000411850362036400e8400041c005da8801c50040b9070305100c840d00c0790081000c0c244203003070b0a50074980d80b42c82c0400036031640b20080d4400d038140013010480e54510328143d840c01d401640f000e010001c050050040030fa81c80103580c000c1c0c40c0c95110200f201d02080700b00b10b02080c01700c4412410352103484140c00820403c540340c03504032124418507640c2d0f0003075130600340e07140d200c5c00c0c4000354420741c1041410000b818640e8048005070024080900f4800c455558184001c01504107580849815038441021540f140000d41c4c801d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 12535078 1250 12533828 12533831
    0x60901020c1504030c0c03080d050907061b0c0914090c0d030509010e0a0906081f090b1b0c030409020c060a06060504090e0a050d0906090b0a0816200c0f04 68
    0x80000088640701c10500c4290030302c008030300c408101418419081c41264980050006680582e0303454122401e40c040141e101c034103424036000400c0c02c240401d0440c100c826076240d4284d540c40300300010500f56100002102c440346048001f041080082c855106091000c818420181c00c2401019203025900c1491521030000e80f84030b400001d92040030b403060802c080c205030075100703402c3d80020011130403070704904e200d58500800050f0440001500ca1210036240d11550081620b600810381516011a0041d00101416000c00c000030004500025403000900d0002c0c1452511221079056901507841109800d401042d05940a8014403e581d00300884403c100501490114060014010fa00c20044103941d11998854a42c00a101e1403404c1c80d480002d4910071701c13544002038410445806043c0c006001d40c60b0201f812031203002283c40e02010f41c0c94041d6682d403601da0381900c601642178820104030701c010000d20f02c181030001101e201954540640a1031442c1024825036180481e050b44c0300e42e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 12536328 1250 12535078 12535087
    0x506010210020414040203150411090a09050108060711030408060411101b060e0307081201090c02030a0c0b04110303030403090e090a150207050c0d0804030501050c030411010e12010f02030906090102 87
    0xa82c4440144c44690b00300b5900540c603a9180b42c440c800d400880d00303900741c04c9818500f00c03840e2021604010100134108a84800485803601c1800c01202d90902909200780d003e00b02140c0120b0088019107140d9a0b0842204e24040e118400c040c00c100c415503084441c4083c007a00700c0304600e04840558550102d500d0700000300302100c0d81c07055480004a401038403c0e44d0750000f044506009204441e80ca40e040224250359041440c0410341401d003d120710b90f4484e1a0014208140d8408002c83d841401c0b00d5413215501078068840641908000d00100c034603c441000840310341d1024000b5511690080e11122502407078182c1d0020084001403503225603400c202481d10005140d0f00e010100580d810341c00503203500c141d1500701d1901c2e41905d103003503129400454810030492400d0041043d280b08900a01c5540c44280100001d07010680700104031408450b039202c0c09500c00e840b5801c003804011300103080d10021000e040d08594203000348994642d0000200000c840c0100815a00408000001c5240 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 12537578 1250 12536328 12536339
    0x3050f0402031902030f070e040c0602071208030a1407020d0f080705040e0a06051c05070b0a0e0909010603061a1c0f080a090305030a030c1b02030d030c051c05060102100204 76
    0x440710f1201e0051401c600a011070002e6450811001607040c2400c3c01b2260780b56142c1c0c5e4501d2882c001100c04942c101c03902c01c0081042403001c90000308030b4080030000317541e12095584801044d00700401d02c0c44403d81e10001104941d00c40b17101c8074081d0503260082c03c07005054000050207168040007030401d12405000b8800c1c2c40307500408032002c8070074528048030f09440d0202810f000d401d45034415a84202c0603408070403909590b668864105108000b12011640d440c20307aa0700d41c0c09680c89660208416014040c503900b00640034039802607402000207041900d0740e84407412940001d16101e10000310250480b104d09195011601c1941624602c00150040380e03a805064503d45000804809000c150051074501420481c80550307404401d80703854021600c2d0003001801d00d4a2100300064174881e010030b1541d0030000c0e150356030b600035010b0a802d10981c0c078142c0103001850b020a0400c4010400360400d280c02d1000d2100d4420b140802003110f04091000a01d402801c91800ca02c144c41000100b1a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 12538828 1250 12537578 12537583
    0x20409050105090915010918050f160f080705011d03010c120e0703080901030e0a0b01060507030e0d0c0905060a0308030112140f070603091e0308011509080c04050c0403050a1203050f040203 83
    0x4440380c805000c583c00c0c2c120380c6510004003231054018124030a1400a0100400104500c203440f48480b05110400784d42d1000c181c4082c110388512022a085600700307001310b5100d901c641c103d0480c10142c8184605d40000071908440508000c40000f50f07099540b60381c4007010340207807117000385200c004003041811a15086500c0c45814505410b02d5641c00101da00c0c000e043c0f01c02d104081c1c008810f00720a40e505c0d400600641c0c02410b0460024590031104a29071070039a8100d00d0315600407441d02c0e0700d01c0c101282a0002e0801030650b0b503100b0f005580000004517240021806480299164071104840c1c1c604440d020740840200c2106402008005582000c00500c4804403149454041002807043c20407052400d1404580192448011003400600d600803141d0760403554100c0c00b610320403001180840e6100308a004001941d0000c00405030316291075040f030350300220ba82d082546025981d603600c42c070f03009451000300e52428620104002e082d4241c41081d50002c5215000d16640c9090b600003038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 12540078 1250 12538828 12538831
    0x403090b04051e0301180312060f0806040b040c0b070303020408070905131e0b07030504030e030c062703030403030c030305010f0b0403061a03010203181c090501080408090301020409050105090915 86
    0x484443d81850200654094200e0072110035251611440b505503803c0040c1003882d0820040e40040c2070000000d031540c104130700300003140c49910250540707032030f036603078008103440c014200f524548003030600444c001e0a1600100300161094a00580d2035241c120000c0c104139866025107142407803e1304004c410580c41100c0004943d014015850325000310102d084d00782c4120002524801d0f5100c200147d80c0c1d010b40c0450300903070103a218005462010010503907228030340031340c05811140074408c80750b01c5141c40b018002c031203203200304850b860b07080c5102292071078100354410f60010b08108600801e1581510035540075190400400482d00c0c185129241d26200e544001058283d4a40c0c1800702e18110403022000560024020f40d40c1c0c1c00d100080d020352076180042c00c0d91070b0044421303100301020300404103071a00780c1540f29650403603e8800151072141008000b0f51340310307808025a410554082c4002d001400e21103500051950609040c00005403004080088a41c041c014800b00311101c0b45105 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 12541328 1250 12540078 12540109
    0x5040e0f0f16020a1205040905090a0305090d050109050a03051308030304081c0221010501030b090603150705070609080301091a0d060b010903050102040305030406030c0801061b0215120403090b0405 87
    0x402c2c1c07190707200340c081346024025400500581408062610510740c01710091040301c41e150001c0c0001c0c2c58032101541c8802c0101d900030040780f420000c0740c04500340800e900903c0f0303001d1400000e101c04c0f1a16041c1c03c08401400407800035000040c0400d5a146031000750000d0300e6030000440c00d600e800d070b0710844c040c45902095503212603121034003500ca1005030104d07502041860740703800100242c07440c005040301081c0180360120b030500c0390511103400c28156031842080c009000b410110400b10880100c00009410343d41007110420500011840c2806400c90081c41082c00d00d0380c0398074003030340c000444110071100b101600c0138040c40340e003a50360a440c0c0c040d00f5401031000280310150f8030041e211503001c0d80c801465540040303070010a0240c0480540101e0b8401c4d1014807215090304400c460a4909021b40c0ac040b440b1a5888440e8400244044011502c041c0000d1081d07048186085001d420001c158010301012804001c01c240d4040007a01c020329040210350f042c2402c000028030208201e0500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 12542578 1250 12541328 12541351
    0x32102070e060411091e01090506070b150102030903030c0307030206070512040311030c0703030207050f04020910110a0602070b060a0501030606120203090a0807030807110c06030a0209030a06060605040e0f0f 91
    0x455804e05003d0381101d180c0300000b0b000a104c201310030701000d203c4442c42496404140e410400145a040200499000300e40c40803d42ca041e07920020110000f149607103007241144014412144591800c00c0100707640c11100b4015a01c0303400302d10700203140c004c0080442c0c003001405d01161102c24452003950b504030f40e03d8248003800c1d4071403880c42c6245000f05030190016100342d60b0008281500481c4c140700ba108c0c02c0e914180b418820b0810702c0300b40e204034652160002d6284200c410401e100c0c0d805a4503c0240c001522001d074040d8035a81c05a8100702c10640c1c410300e001c401e020346440d20390010001814203007000d0142ea89407501c007a0541c02106452610644c0000000d010f00c0700a10400f101a070b48442d405446a0050800900300c0504a403648082240e0f101043c07040360300001c071112550780003002286940e171601c07181d0000c0c3d000a48500d17014441c2d11b10140000d0410700600000c4c264030355a203a00c40d854060f42640b00e0801802070182034440c4014172420750781e01c0072010391050a5504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 12543828 1250 12542578 12542591
    0x409030e0d050c06040603020c10050402010c03140702130b030105070c020307120809060703050405090c040e04110103140a050702100504201302040902030601030e0606030a0201030509030c030301032102070e0604 93
    0x2400342c00d014040d83e0741c6070300000018000c2081909580500f0b46400306404490782c00784820324290440e13605940103804126045148400030b80b04104205654884006032800c2c50210b50100e0502a904050015095203c15030558a400c0911409034403030302761300d402280c92172140c011076200c1c0d0040c000c40c00c6052480c2c0d81c240600c15401d00315526600003074500e6540da40756050040c0103800501030140b00760790880108481401d088181e4050300c9541000829075110f03656100c5100e00d221803014141511420222205100012185d00c115130071038000c510340c540300200905180c1c8041405035500e04d0941400082044c502c0c40000d0001074001d1240e603102d010000810081c00211404407880c000140440c000c03080d500514000d100a1f20305108450000c1001c03030f00e4510495a031078169200c90710400c0035606c01d4126940080000c02560725010f140b08445042d98000d80040d199903990b0340780c040700c180c0114150300e40d0f58102c0c4098500d090403c1c12100c00400d0140032144200d07241d05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 12545078 1250 12543828 12543833
    0x1031514030a0209150901060c03050d0c090305161802130e06010215040302010c0e01090305030d0f020c070b03011d0603030418060509090a030906080106200102040902040b03010f050409030e0d 85
    0x42c20700030350f4004201409601e802c40030b801880f241c00100c1405250400c0c0001402401001c1d403070306990b81501c1e49070806214030b001d84003c101e0a0003520170003080900000c00310724240b05007094014000c40c0400220708085034000c84581810500b104a441046100c1c46c9000e468142000e0300d5200c41410956291880100c1c6448138041150a5244180c3c00340003c1640540c41210105041d443c0d4004010981006440107001440068510340040181c0403029205a00901644550301305c01401c0c8a00250b03468a070051541150b0500f6a0000051290425004e03800e8144c0300016001901450040c01080d1240500e20881c0d00f0854211416100005180c121802900c030191958400717103069219030303585031803e030307025408542d20b1600030809501c038844c0c1c42d0503901240c07a00f40600c0720702214459401c4680032014469503007408085050034190004000501d0001c454549075410304440a20400340c950150344110f1038082c800c00013980041043c12582021100c680303406400c2d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 12546328 1250 12545078 12545083
    0x4050903120907080c09060a12020d0b090d020c0301020702010c030c030c02060a03090b090109050705010f0c0b0c0304140102030912031f060f02010b01090e042409030207050f0103151403 82
    0x8050140340501100700300005540000341030001c0324900c204440610440f84280064008140e50355604104242c0d0140a0b403d10003c0380b0b24550300c068500c012066940c0c640c800040b0381600c070700181d50010b941030103409038100400b1403035840882c001c501e0510351780e0019100104a2030f00806000d40044481c05140c040c900486010f500a44500e95503200b80000034002d2030380b04011540702194801041c07069505104041b0101c0d801001420f500b03080c1401902c8510000000a0402801c50100c00005000404060250061121381c0391039050030f00e0810005100240c0c50126a8414010000e44032030014040d00784041c0c2c0124079a5070348a445c15019610703041e00102030295508440050341d075070b0244100c410000143d008200301901000112803880e2584910110306080c6404200490320782d440c0744103184900c0b0340b850383c21000b000054003035905111060700940c0081504009074201800d501d0b0f6240030901e010004c0394110340c800608400c0d50700503460720040e40c043c2c41c203540d00d04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 12547578 1250 12546328 12546337
    0x12110324040209011706040303020913060e010602070b0a05190e0303070c0905010b1809070e0a0303020d020706030605011b0201090f0f03140c011706220c02010e03030c070204050903 80
    0x582000044000c08a1a08090914140d030101d0048500c000000348119401201d4a01201c014002c0d141d0f58441d910704030082d4020500065000305501e5852048101c03a20a540003030419482c000110740c034040d4084d0400360320780d2003170860794010003026010070342c40800c0365220354081d001e805074954a030508940f4414040c0c036068052100041c6e150a020f8074941076802c48410500038095aa01c9201090300c0d80111818408a40e0035880c4c076802600d0030104003580845986005415100002c0000b2400c41c8a0751050b4056004201d541d04002d5042c0f00000241103d414180f002c00d1402000a00d2558090000c40e8024207440f101000c682c40740d05401c0c000c0001c0742000d511aa110440303441007040078130044a2103042c1c194240c040c0840407844408801c4161544046080140311039103a40000030507203a4040644e104501c1c49048581c001c880b400902940059091000803001e400c640803603940c48440d42c0709100304445420076008403001d150b416107020610b521054100751540c001c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 12548828 1250 12547578 12547603
    0xb03040303050609060a050307030f020d1b08061e0601050c070305010e0d030e010e030a050d060b0307030207060b01030506060906070312110903150f0a020307020c15091504121103 79
    0x4140800d240e8560006802158201c40203405900d8020810550039081c0c41103503010f40118604102188004a03442500c500245c040d0b00010150b940d070070740b00114030b07031114203000c2ca0900c04d1215803400c003c1039900c545a4562200205801070070100c2c02c503401800c15040040005401c1000c1c5c80a1294000541c2d11400070711440c981d515401d0344840d0701c4142003001924102d01a84a0035050186595403c008030185140000341c20381150f0a17448034950884203500c0700400a07400c0401030085104102075500141c89840da031a2603803c0c0c035581080e06042600344010304c900da40e2410300719000342c00c00b20b407681e0b0f070740201c0d1400707035550b520002441405074030700002009902180002031003507207805c03400d440c80780d83c080418100c96035042d214070320441c80b0000050b00c100040c1d030041d0b0f0090281c0c01207440c510340360400500402500c00e034041030148007043e2140703a0308000340d030405800880707840340381443d0601d900c6048200481401601c50701214440300d05a071000d1080900418 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 12550078 1250 12548828 12548849
    0x17070b0c0c030a060608102c030f03040305130b0909070f030e06040506060109081606031104090213030b0601030e06040807020a051203041d04030203070b090c0406080601081011071b 80
    0x10b07035814103000402e5a481060300700e01400e47c10103003040d81803007100800c0c04840c0c0103203804140300080c0c0342c03098100c03090030740c0b584170405c50440c0546c4080f01451140340b107070f07540958a03511410003007608061503000d045144411320400c40981d503007103080760f8064154134041c84100784508085000d001c09001404040c0500d2081c0014003e01180d0544914000c3c2c88406150b580d6103041ca82d01c2150904817a6030141c015402c3c01498408e0b0020a0400040c280c0c0a01345903d502e2034104070f90285422400080e02104100308200d11401015440442420b0400250002166854031500000c000402c1001c002521504550f10f01c1407140141c10040c2c0800d1500f090100095034a5126000360408498030784601c07110220403140305482244d05a01550604005a891180303139203001d08115190b000b110014407182e200e0b885a01e00805d40c078001410254980000c0a042041e0751200340d0319036040428061a1304026400c466145034802540341b0030003414021f016050042d90018140360 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 12551328 1250 12550078 12550093
    0x50d0606050d0b030307020d0809180a02031503120403061104091d060f01050a0302010c03030b0312090f0a030c05090702070302090a0902090f1b09010c02060705010501060917070b0c0c03 82
    0xa03640207010700752040c821801000411403c404140d44c034003550100a5000402e2806540043c2908000d00b05018014250a0304041840350400307036068203d81400c4019408401c0080b00b80611005980f852001d801801d00401c641e8900001d5210780d01000d00040d4035a28886010302440d800c4600400c0f10007010844100300c1c000c1c1310600703240d048e511506803081d000810800002400103d040b140b00601031112070303281d0342c01503130141c0c40b485080d800d15503640000d001c2c035102445200c0740c2900c15841a81e03254545c004004120508c401c5040c00782c2c40000e8144002660068000103075203044602e034130b5643c0c0c1c0200032490405550402900000d00c0014096080c103e40c00c401d00451003194000c107299921551002e554004603640803a01641d5880041690002002480b4250041c0b4040da070070046500410010b41c07240707001721800d0f0354a200410040d9030000c0c4050250009121050a070302c210a90943d4480d214041c6070300c03800001075144642c8404200440d205030f030103020356189 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 12552578 1250 12551328 12551339
    0xf040902040902030f1501050304060506030f0607020c1003180602070203070305030a08040b0c0909040201050d140f010806090604082203020d0b0a0b010309050601120305090604090c030b1002030a0c03050d06 91
    0x21307420942e41150031002c01408160120760000481c0c0304a081030b0f40703941c195900e640390100a0440a000b860301030103286042e1030b4040c41130019030300c560150303001172a840c000385043c0400e001c2c280d0392030b4040618044502c80008544190805240c0d004403015072590780c54000030382442031503800280280300018580c0340c040d0b00055007a210b240550210784280d600c500c5125610710502c4203250340512030305d000600640c00354003c5c01680103102000203054903044205004568169007038000103d00a00401c60444200049644130010741c010b009541841d0703461255078001d44c48500204c2c205542c1e03112034030100d2400e10b4003d517001010ba5003007441c3e038140250a0042924401001401c01410441c95400382c0901081554400300820060303280034180810f420840078200d04000d030410181505035110005031025045c01c440014103a10300440140c110f407107200046010350828221540410340200a48508844506281007021000d10f02202e02e485445210030180707161040101c0e0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 12553828 1250 12552578 12552581
    0x604150f0501140c0a03120b06040603050402030c030a0c030609030203090411070b012102040b03010f0e0304140907050307080601020a020a0909020306010504050c0a0518090a090209060a0b0a050f0409020409 91
    0x1114801c0c1ca500183c3d29054600ca07a00b81306860050905a0000131800006481043c40258501c0c49880c005602e807141030000d051948143c1c01500081c0d01c810070311042d464180038224840744210014000130010703695000643e5024030003c1c152030754440407038003418001c0c012501880e030000d20030850b0504000003141550811403007503800300241c20001c903291500480361030b001990f420040d284446c05a00f04405440040380072a0036548407045094149800d005644071808800d01840c0c541f0b09201290064103030140400344960088000e1200203600901100d07000810340c41c1c035079400da55000060740703405249940250081d40c841000610341b071080d800f08280030300c00c13070542d03510340d0366174040100346c030410381d40e80c2e0301d60b4420440222185d01410040c1100071001c00d40400b5000c1f0040000c00100382190300e4040d294443d43e180b0f0031841c05000c4907602c2401100c40501b003070b00b44512107101d070280c00000c0d814010001217404c8809043c0781581d000b09030004007550b50f036807038810410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 12555078 1250 12553828 12553859
    0x190e0103030c03030c02011e020a090305010504080403020909030306060a08130b01090c11160b0c101404031e0801031101050405090c04080607090305030307030513060f0c020609190b060415 83
    0x1400285440d00303540003c0d1042c01014501040039640c00388c040d1220b1181002076000810b0300041c06070700c0d180000094028001e0314401c078003480300540ca40e072850060105540d401040a940f42d0000c001b007001503a614829100344111034a461156581d43d880c900d1015114428080c1446580c4400000d66a200703402c402100d1200d039070760400300c051070b0840f20390311086200d001c0400b031440881800f60000e4600500b580c03920b5030040314000d5203601c03402c004950000003801c6001c401c0ea002c1006151700070341c4c541d20400200340504540e04401c07a00822540c8180001013004500e03959040c1185c0c4900c00b81c8001d00001071015085043c014005a483d1b4000d100b9621240580b0300042d0036203004014500840703800c45d010310b10350364034900c0c00c400901c0001c1610b00f4801c1c0200c19000403400314070401c044039005a40009030003940100192a20000a2948409034050080c85820103004072100d40459488000c00c0c070070b0380340d10b0f0000c0c0203004d00d00d202012001089000141d807101004001c0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 12556328 1250 12555078 12555083
    0x301030b06060c060a0f0b010f05030406020304050106120507090506060a0e15041508220807080a0201060b0403030e030c060903070b0706020d0212010f0605030417130302130903031415190e0103030c 87
    0x1c0107001490b1006480c02700e00301c04040c0c0481d00a10001c1c0210304550002e55000f0700c42c000014545032140c100d10400c06000300c0075107842c0e003c0201401018002c1c451a03401120403500c483c10507170312020040540c00c5172103809000e040e0102c07080361844aa01c040d2005008124502c510201050301c00a106090855412100030301e0f000b03440350b07a00362100e0010600d0390440c42192030040d6545419225510181d0204210740d03031000d00140d01207011002c0d00103140f02e035035902e0880a240003054a0302c00603410283c804e8400304170b0380e607040d070300040e500342240c1c0f84d428181c0d12203c0b1400c0010080c00b0380201d0540003400000e4042816400d200c42905139645183d01c200ca15840d110b086481e40011207004198003c01c1a2a5450a405a0150400c032855114441c49a0348907408280502030400c3c02114007038030f91580c8010581c040c041e03c0582581d81034031480c00d1500d040351140c21050084003d005000751a6000108444000f826014001e2041d0681507540e592600503d00c2c00400003e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 12557578 1250 12556328 12556331
    0x110603180c04061d04050a080406320a031109060708030702100e030702090405100c0e030d021b01051c060f05040b030606010e0f01030914010c02070e01030302030301030b06060c060a0f 81
    0x10900c030319140c4603da01341e50360900d80c5298800384c03442421040d08060401e076050311441e02020001000000140090522507640c071100c04085426120418050a82d1100444908000e855100142c030155612640149000700311000461401c0030039101c3c1d912542d422400005612083c03040740310003140900d00542c02c030303180100c40702c00407402c81c0c10a070062445e0741c100f08600b201625180c054540c00074040c5054403194046915a40220342c2c503010448080307035000408020f03d140500004a1a40950014290000000c0c1042d50320b000e40c0f51a160500030301084008411140314514008240d460504011030381e119810440c03170040c1403054a103e5401c00c03404d006942030110b08140524410f03101c2180c0084030344e04001c0ca2858021095040550300e0080b000480e24160907039a00042c06000066128045200207007425020740001d1038604111004200003a0f002084a044982051414190703031208000112644240e01c2c1001652040c1030500c100d604550b8405100b40452500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 12558828 1250 12557578 12557593
    0x30c0321010b03010b0702010318050106090c09030b0115200a020a0b040308030f0603010b13050609070c05060c090a03020909010c1206080a0213141003150b0901030204020711060318 80
    0x1003903150a1424007620b819100288010002c03000d480e0003a1280301d105040c0490b500e0340300551450341208094098585a44843d0200151869445104204801842e000d48000d042d03455503101101d040c454400940b40415604100d64464070300300725a200b000c9810200028076100c07580c2d4848007440240e224001e402000500c0c400000202c40c21203600580541c119510050303034400300c0360010040e0350955200e0040301c1440d0780301820360b0034401b1003883c00a0307a814040c0c14840d05c1c040003403968041c4600020904040f81000401507403000e0080d404030340e2580560701048801030301354030080d000a0844188000031a043d001030b988020103076604201823039a4030402086d940740740329680c1c40340c000d000e0f1035001d030400c20085801002e408401194220409001c081c000c4012604001d4503800003805000f04144080000444580744000b480346494880000f8428401803000034030644d40050f071841040031850b80d100c81d0b044000c000d6900c1e4038001060440d424032903a048034850280d0320 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 12560078 1250 12558828 12558877
    0x506010305011203050703180815090a0209061203090a0f05041b080601030209060c060f0f090c0102150402010c0c0b0903070e090a02041e09050102090a060c0203150a0e030c03 77
    0x20800c2d0403503042e00c01c00b003c0310185480642d0383e0790011500b901081b0074116032044820000d10103800074803140c001001d490403041100203840d0300140c2420203581000313a840c005641c900b001e082d0084400c41c1e4030702505007400c013414914803800c00e0040c0c01c14a2043c00143c00451210350074102e0b14280d07000e00c1295010303488520340304450034004010803041004111254829409015a88005003c0d80d290a8580c5011440c044080700c40c0c400d2001c40004102051000d43c0360f81e03411070b45080052120390103a6001035103a06141d80c545a19069a5000405583c82681180c0c02d0342d401022100345985c4854140c4c6199115044840c002e00c18900e0001f01d9400c07036411140300d0071600c0098643c00080b0390030803014008000661000d688c1c151402c0308120014455610540e104200041c0d48806440c2480060740480c2c3c0402c0610030911040b0700540c5010540c10420b43d5009103c00c41c1d980c6214842c0024410103692041301d1001050581d507030300700000100300249041103421710200462 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 12561328 1250 12560078 12560081
    0x70c0509040506070f0c0204020f0c0c060c06040b1308070309030c05010c05030d05060402040503060703060302090a060b120a18050a0506010803040f09020f1e030a0e06071706030106030f03020d0305060103 90
    0x740c5004103580e12560004072510710410301c4d50210001440c2c08000410b0f5a00010213981242c4100d0310903e40010310001c0e401001c0014003600c581c2504c50034101400c406d104e584803070005001810008035400000c5022007006c003c1055035500c9050143c4865407400c0080407031210f4003048403d0340300b6800108166000703001c07030080b0660290040d0b02d85401c801d604009420044c11060700f041d000e0001240517074040c03001510800e62580c00040e064078500400403842d40c0504030580c04d034078125060114001010071503c0c488010610412642c8404400400400210442d8803804076040910410000082103044000380510115203140e605c0c1c00d000c544034031851003141c1c440d41504204010400302030b0060041c200210704001d0905180290616044038080c4000500941c00002c11040d40c0b01442200000f05040b0001e00c41d0346030003100580080ca8000d8620040301e10040060907554094008101659012860300000351541ca0302956801c846085c407030200342403c00180465109 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 12562578 1250 12561328 12561331
    0xc0a03050f071e060e030f0703080a0305070306050112021303171b0105010503070e090a0602031302040e0105070807030b03030702120a021806030c01030f24180b09010905190f02070c0509 82
    0x42c3c40c003400c1e80500e001c074182c900520081c8100d4040c015400325013041801400f110700110b00440c1c18554a109216006040b03d03c01808841414545181448283d0b030040415109081d504001a941d150442c010303052003a040e0310050480c90b111602c4508600404040c0507810340781070405507002c08190f01103090721024095981c250303004010402280340c000c07004503046481c49040c1c80104881c1c0d01e9410a0f03a10842d544c94040e01042101411410f107841295000d26a1000811060900180082c561132020381100c0070562038050220550764280b08a44071558000c12034120580e0050140780c907101e0052081e40f042440300da81060341440c1c01070140c898000100500301000c5940010760003801c0580002490681c4e0303078010f18030030745460060701c201f1855a09020000d450b16401e161660a80300c1019103071414811a940c842d2120101c02c0e0545a00d4000802e02c1c0c0d0700e22444d289010340d81c0c10b280329058102601040f409060754014032600c0c0c054401c03814407075143c0003400b100860 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 12563828 1250 12562578 12562619
    0x32303060904080a141801092705070509130c11030a020a06090f06180507140102070306020c01020c06010308070c140303031501090803071518031e020c0a03050f07 72
    0x820700010700000c0340380c8028040c140307250501c0b44000c44020422009900050300340c84078a85841028641581c220941038010000d21105420114003041c0100116908001c00c03146581c4035004210b03030030f0242c000e6443c45800070304a0510314502c41200d102801041031003074081013000b0a20b2a820202004454602200d81c008101e0140c1556803200241440b00064401d545a00030700c000140c901e01035245541202000d41880c0703000d90401a007001129481202074818118000540c7c0e600860140201c9412076001600c0e8180c10b040035001e84111418050640220300001c0100030325100640300c1e0b14000e0401504e81c43d00d03807036802c0c0e051803142d00e501e5040d401400050080307103007011b082d0320440043c0350481055135504e04242c40d40d00060f004035007120607410050280001d134032070b66400c03014032a070154150780c0645010f086440c0c1c40f2842c4c010b001d4542e2016008134000c00000700070b28405000c00300950b41e241001c980764001118012418050010006492a021101903900c2c05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 12565078 1250 12563828 12563839
    0x30d0207060804020a05100201020315040608120d09060203070908010b0609060f0309072403140709050603040606150e010f030b061b0c0402030403081608160302030c0705010903230306 81
    0x7400c00c1810303200034000070412a40440c40c1034001c6031310746680c916540300701d005070005a01ca040007a04228a210050f0341070b4041da140c420308000000e000101c059079211078000841e603c001009030760020f0b000440d800f415550000091140f1264850000800c0398002c8c0e00800480a07040b01300145486211119503201c02c060080e0070413014403000460700b00ea00c2c041103410095072440307408452045000b10720181c10400c0b01005080744c15005140c0e12010f44424140305143c6980040c010021502450b4001c00c3c0200000f000c201c005e80c001ca01900d41002d0408106950000087c401241d0350225400030311500400c101c141d010380110003007080e000b08028240340114104150640d40719203032710036a218034070281c807d645403032000b140654000d9072011038619007420b00154883c00c0c030b0344160801c0744079802c0201100300c210000611242c1460050307030f25159100100c00d2800b90318000380855180050329230070541c01c944041c03d4104400318803040d026410001c1c041d1404206c506030f401c03d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 12566328 1250 12565078 12565093
    0xe121b191401030c030f0903050a1103031e06120604050a061b080118090602030a05010504060b0a140703140c150601030209030a020405040f0c0f09060510050a0e030c0411040f05030d02 81
    0x56019130058020014a481c0000d00c0c1d209041c0c04030305170745510b1001e6010540c00120300d450a80d22103500040c41101000451850800c1403400807443d8500803100b07203c200c0302010900a55500e81c4060300ea651107030440b101c0c3d051904005456400e5003800f01c0d00b41d85001c8a0340e01d5401286034034032068059403501c0019030311309003a4601000104132140701c05035440030050001100d500c0030750b00034000c8140005080d8100b4090204403580c94211982d000ea0901403954a0340c7d02280d006d40c09500e150700651681c4091506803104607008042e400d2518010410016120b0300060300fa0605000f15240381994a481300103400300d10030b081e01c642d0981c2100d041a0007500742500540d1f002481400441080d00641d1191408480641c02819039003000100800100c07240340500000341c84102d40b40d694140c407203403001e40700d4132804c00808144140c240c40084240ea040c09801310115029005022a800c00715014100364002c0c0250fa2405890480c04509403e0000301440c45c2c940d0780d0000d02c0340 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 12567578 1250 12566328 12566369
    0xf0103120806040213090603110307050604140d0609030e21030708070c0503010501081b01050f0301030f0c031202010204050108010803040e01060516080403080405010f03110306010e121b19 83
    0x401c1c0c402460290441c0c0c0030040e60b42e480b015030708010010f2203000d000040d02c504503d0030550002480000b08e1207507000281c1801a50b550030216011203608a01c817154100e0032001003080500103500140403203140c182e04109140e08000d07034099140003100e00b200084080c602001a5407040403200000703074801e024400004074404001d200c1940a222081c6d4440c1c0d8403400a0709403030090300519015001a00d0001030308203403101c14540740b00242442800d10700c540591001034001440058003e100d00e1404a0522840d507041d00d001e5074004580080c0c00c440c03100c3c003078081d40c0103100c1c4900040c8458000105c03034802100343d0781644e0303620100414a9180c21012a819080b0703205904403000c45840803000940001c00030b0001314854955551101c0c034020001d4140e13891600302d1303810b05050007034031018184130004581e0300482c00d00f8483c2d0540460700115541640c06034081d00c00d486841001d00d8403400b048403d100e0410116004a0b5103400301502c801c40340c0c07082c4a41c2142400c44502c2c10fa4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 12568828 1250 12567578 12567587
    0x5040c090e010204030c06020d020d090605070f0f0506040b1005060f07060209030f06090106060914010f031a0603040b040501050112030813030c080a1e0309050c040906020f0a080703050f010312 85
    0x4103920510000341c1080c1c1c50f511840800383c0d6550010015a0084085d27108852301401140c1075440142042c4042c83c0c58600c0181c81e5200e00e810003001d138a4078220490811400780f02c1100c0e401e40050840780107140c03520b0070040d03001c03080e16030701888180c24200040ca4070b05641241d04070020011011b0400b00e2560360600079410050300c81b0350500444040500080f010405588945402e000205403d032034800d0142c54140300e034200c241c2045aa00229143d0398001050f030081149520340010000300119080303140c0708059000700c0d4003210000c02e11050200b880d01007405180a0030082000380d0b40c07541841c03141024890014046002c00700081c180071200f46400500c98000d0030a600c0c0d80072550380d200300d10f611001e820340100d840070f84040d5071594401300c1d0f100340b01d0513030074200540d002c1e40d11a140d40d88516660240705e942c0b00d83c905001c003d0941c040d60191400b0000c0c440d01e030003c9100280584ca4101c614200207840c2100140841301080300e004e0489400ca024160100d000200456 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 12570078 1250 12568828 12568841
    0x307080c0a170f03031e010905061c030203090301020703170108070302090123060c01020d060b0306030304030605180d0503041b030b0a0c031104080a0b011505030c030702010e010908030a0f05040c09 87
    0x141d0b41e0045a01802080303c040c001503200b203840543c0003414141542d2a840c841c0c0c41a003198800c603151204020094440e881ca0a6203007101c01c2d1090350710b00036031800b01e2561148809094040d4004141702041541150039a8002140d0f5030038881142c0e00d9082c92903503400a071001035445202c1c0c00c01040a0003d022101650140f80001490018000700100315a580000b1300c0c800c6581d400650600014080e00c07415002e040c202e01114910b080100001f41e0341d014038040509402d903584045030000400b642500308032050b10042d43c0c3c0010726058007928641080740d0a071019129110003141801442c0c15601c15241d00ca21034680548034090300d81e005204070b2207450245503403045410030405100c006400280008401000000c1442ca0702a04034041a80309040e036044000940303000642007000d6075400f585000d10607841e543c408104901500c3d08610b0701c03110f5403034020745000348068a80218803c1c595207605121400d43e004500f0100c0c0d8040b10040c20802912a00307010031f403074582044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 12571328 1250 12570078 12570119
    0x20307080f04050411030a14010303021c031b03020a110309100507020d0606030507050102070e0c0904050702071a0921060105060913050a050402030606010f090b090409060203070c020307080c0a 85
    0x5030b040c10b0b200d0020500319101c45c202e81c1d401c10404002c000c4c81000c0c034083d119103005c2c0c0d4458081c0c00d51450382c1c040e568040000e201c000a03001000502031191003035201c1d4100401c10710f81c2040038804180302800a50002041800141e100407580c540000c00204881c8100c8000d08108040b40c1c00d001c003221faa4114417002c0780e006010031603050114034140510780186d80910b002e0a81d175450040064642042070b0300040da1451200104900c026100702a203008071029074002c285079036040c0040341040342c07541120314a100c9950b65a014140c04001800c039111301960545a0b005408809148640b44690034030800e034400c9005200e142400009010400d0024100001c981618103405003a280100c84200340e641d940d404200c1907140800c4208d070464020b0070041200d02e1200001801e43c2180e002e41030340b844d030010341d0088545a80e031060f220503030000c00842d22410030b4800101960301d02a42a40329224a030070110742c0240c04070308802d20140c001c18040c07089240040c0c07241d02c41c007182c903c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 12572578 1250 12571328 12571357
    0x2090403140309011a01140306150f0a0302030108010b060405030d18050402071b05010e0d03030b0d0b01030f0b0105010206071b050304080d02060708010e1302060d0b0415060909020a02030708 84
    0x302007481408801075401600d1400c0003149600300444101400000e1503400d43c1089211030382d403443c000e4210201c079044942944d41008540b02502000428800c40381d17052440503000514113005581940030354140c90301500240040754480c020401c19001e18002c0513031640001d240ca61100d0f004400070030f8a0294801d10b150719517911400581240c00111060b02c58000c0900070400240811075203502514090a020303d0311400ba0001c1402c4000c01e110081c249a0780e014510503694407800404c0b40c1d80d80c024880481d80d80c59150410b001d404060045401c004404004180740d030001c0340c046c9c42440c2c1a6940030141c0b0b040009038001000519040d03802d80070410000c10707071040510944410701c12070380007042c403400e00c28401005075005a2220501034040c1091100c0c1d00b0104a82181841e0111136450f100c41c0343c45c90301001082c24042e1650303c01c0ca0000c0684119024034404030441d00c11b80c444a410603a2a10340c00103134851760401c180160020880100001c0381000900541e00351030b06c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 12573828 1250 12572578 12572597
    0x103090b010f0e01090c0e09090102040b031e060f030c0f01050d0509030301180b03030f0a030b040603051e06040c2108041e24230301240206040f02090403 68
    0x303542a0805003a0001c40a6241d54542440f40801440c2460300504030707450100244440c41000508014220010500c120491000705100d0f02c000d4040d200600600d4051507960709000a46c1849101c80b11280d0100541d1000020800c0c81c050748803900d0064041d010b40302400c110740402820b04820000e19041c41001d200180c5407414602ca0644030704681802035983e5410200f495000944220920620074180a4803007030302d480210980f100c071943c507144151110304446082d40a0110188820f4200d41f80c200000140440003654090980e034203840c00c8900d9803030288068844c08115005080c4a90f1500b080003d181280c10310502d100c00c103031038419150301c942d1340c030022030740290b104010340c08040c0c03c801c840090705140348000b0507000344606082c080749007003402920a03501c1598140841ca07406042d440d51481038062a01d5820b1400c940d0340e60f1101d24002c1c2803002e80d00380958408203a08074100345400050520701503134001c1010704e5105c00541c200300000b03000810407410002803a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 12575078 1250 12573828 12573833
    0x100b1e060a02071208030f09060c0a05031005030a050601060305070903020d08030402040207020a0305010c0e0d0308060103050903090301090501090b1605030f04080706140912031005060c030405190906050d03120506010309 97
    0x40810012a124085280c2d4070700340340c64130014800001d0007085c602d810030420711055600c1c01e400c492880845033440f90f00d96031207200c60316804441d5440300d0740601584d0320210402c01f012a6050580b0003a880410460b12365079001c5444011500009402040002c100b5000c41c08030b002440e0300500c02000035241c620340d0f50101d40d41c90701c154030444c3c084c0c2d100d0b0f80340c660083c0c00c034580109894055031a981c8414250310010300080005e0b0001c1d06155568000c2645000c0c2801128105400900248117412903450518000c0c00481c1055810042400208000e60300b00c021319012003d035691002d06544a03000303401450240503100300d034034550400044c030000c1d0a6004840d00d00c07524880100d06840c000c001c4600f8a50340c0460340c40c1484080040110100171440d003013080e194242c5180d0b446039074030842ca80c65031065030031040c0e014000d40b4440d24400071644081d0b003aa000606c2c184001075895040c0800c858188100402041040300e002000f064130340d104a074480310500d030116141c82e407074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 12576328 1250 12575078 12575099
    0x40b120a0b120a03030b010305060f040e0a020312130b0708030c0d020705120307030506040b0319060e011505030f03041401080c07060609020c0c010908150702030408060108100b1e060a0207 83
    0x2c44035000320703040100003e007031503014031030590750107000c2c01e09024500e005000564940c004880d014403982d0307280600040076104009101141d40e016048601080403c800ba03400c6400c403100410010140c0300010402410762001e441200d035000700e400382581c4500311795070101d41041103a544150390030b00c541404590204004009100a07083c11580c3c0c0c20420307402020340300000c055a0044d404c102c00300341c4685000541e115803541803168074900c00e145103009400f0300000302903821150300f00480d40e0801020301901104844040742200c4002440c821441d4403405540b084075050f05820b05d054040c0d50113499400c0c0e0020003061020300d40502ca80d00c8c0c1c01151120740280101c160302086a81075041c0400900c20300d0002403c00c1e0707101c945400c124503a00c24043d02d941042c0030040011402060081098802410307894090301e1b2150b846c4c4c05041d66a01c10318100d686001d0402c10468010709003030044880541c020360903c0d418404000a05c4410b6000340a0001144264100080d524104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 12577578 1250 12576328 12576349
    0x14070305161205120606070209010513090507090e0606030607140703030902040c08040204050105040204080601031b0305060108060f2202190803070f05010f020306010c060903140a020d020111040b120a0b 89
    0x442c0c50f035640307418a00c2d814291440000b01034600a100c00c22060002d40d488002860460b4011174550f0014000d50a415002d4145980020014841d1100109080c921900701c0700300d0a040c44100c41c1d06540d00810540d9a581c203840460104003d03803240f0703241c4140b803c020000203000303007408a50030400d9408030f000c0b54400303e6aa0009503d11342400218501405840d0051104403403d506160810500c0380e20b400062000903c18121101196249071164058100940c3c010307054035819a51034004986807003044601d02c900401040c0000d0034940b10b014410207803205186070b101c203203a180d4284a1003000c900b0081c004012a0240000c00210402c0100001841008a0f0302c22a44500e815400d50b200d083c80602c0c828014000c0140d81e903842104100b8103500a00007145800f21428244c0c1c0d1064550f03000c006421002442d07924580d00020103c42020066008201d4101c00b041030030a00e009901070034080070004c001e020403212111200a40012400c400040e010b03056100141780d4404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 12578828 1250 12577578 12577613
    0x504030504240201110c030a05030a23040302060a0615050a030e01060803071109011220130905060f01060806040908090a0602010b03060106030204030c051e030d030b040b011407030516 81
    0x141c1d03000b090140b81e03082c002c0c10710707418440314018246001301c0482078482c0500380089040160202c000b452000541d00034104040c400015140d0400801c149a00d006504581c1a005440b07020082a41660036119550454107403048086004444031011502c690005c2800c074109a10f841501c20300010030b2043c1c02c001e01140000319602d00203807610501082c0300c0e041c514460490840104032018100a259480360382c41105a15005210003819403c000d1081d55513810000c040060100e8030020303444800c80c0780c022000c684180e03494010880203940c0901424000a2881c000b28200381403c3e00160915807140c10f005060202e0400892040d010980c001c20040c0e450f000d002c10981001d125103805403400f494103500c0c29007103850f043d528900c6440303102e0082040c0c40084101d0b0001100e40c0e440c0342402815a8121a0b42e00c01c01409042c0d007500c4144524903020981c5142e6000c0c0305285150072086030014201000f584040d6616040061805460504c072021140044d0100039001c00020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 12580078 1250 12578828 12578879
    0x7020f21060603070f08060a02070309030c06050702090a0507020a06020a0c0f050d0305010608070e011404150c060e0d0c0609050c060307090609170a02040903030b041812020c060d0504030504 84
    0x140c1501010f2405445a008584000d03410601b4418124040748559000d1122031000d13a5411176441d00315a480035980c40074040407280000847c24951060040036039900803925814aa11392a00700c5088444c07d8610101603804050030100003145c81d009440445024101080b8441140d2583e1907403202001c0e04a4458000030000755241c1d4051065034054030842c81e01001e07915001001070548a41d820343c0078107001c1d8140e0305c0e288404d003040442c2c015110800d0507803480800030a02a0062070340802c112600c40c01c08a00c101c09003400601c4131010070050b510307101d1051071a11110000c0000380d105075084c0c090000946c52a440c1c0078011401072269540c1ea1030705914081004140e0305160300040450400080004141100000c44100080d011100000c9d01c414a1030283c0003031201c0950790341c0140c104100c0c1c00e00122242d00499809000c0c9d0140c802c4004c0260040340c40d100c4001040c1e0340003c0510022004161552200e6800380c82030a0281c9016280c3c012176140c0c06603a03a0705403020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 12581328 1250 12580078 12580081
    0x1908010503100b030a0305161e0201030b03030c030703110f07030302030c0c0103060b0a050c011409070e13080301030b0a0b03120406021603020108070f02010b0d05010207020312030c07020f2106 85
    0x3800c0400c034002c0b07072800035102040a01480c10000f5102d412030324000c0d08001000c00c100c078007a007200301420312003907209404518149000a0000100f8080301041e800710f40f410b00540f0690601204846034182202c016500d0201503503400d841102134248242024070681d80c0900c10701c1c0c0c041000304051800b0350021070304c40042c1c44085150042e8408a54105400d00f00100300e21502c10003580c900c0c2406041c015162810701c00344d10700404c40c540780c20080c18a5002409510a40402c2c100c0a035401004501c0d2156507211840040317a50701080140342000c1000100f010519447c440764000003408400311302500d043e000649461040c4c109050760100004040000300d03010882c004c0074608000d00e6220203807448c0c001900c0d9210051821f01401403110901c1c100a01c02c0d80b03d01c2890500910712114441d09081c0607000350003500b003c9019102e05480c280407488190140ca00c9415145401840d10081d6800d1000b800032840003690001e540c008034685515030340c5400c000003506140240380030f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 12582578 1250 12581328 12581339
    0x30d060302190f140103020702180a0c0201110304020d080c1005060a170a0201030b120a05030705010e0304030c15050f18011407020f040c0c02060f030709090e0307020405040206190801 81
    0x5542e0201c2d500c0302a168046010000301c41024040d00880d14881d800c502401d54610050313000e40f084c184001e5226142d810004c8006496000300c0c2d0050b400e1803010004c0850780314003a0b003282c03102c0c040a82d001c5820310001e4014504000c504c09410312900c3e0440c01c001e204140280303001c481d0f00b079882c0f007140c03503408100d01c07410042d4104000b0080038420400a5405111254071030f41d5081d0040c0c101501c4104c0042262202403d2411f2241100101c03141607890341841d40d101d80124408540c154207122500000820000030303542030780c2c2c10411180e021807400b0000d105038074000041d0418018140801040203800a003d08411801d0108501c0c2044e0303460001400c0302e402c05441045200d080c0030721005601d0b01c03203500019102c03e07540060000c9407803600b580d1084d408040298172440000d50041c4070480c10300558020000350325550340c45500c600180d410340307000701c1030204107500500c0400c0c09403825800c44c0340c10900140c091440c00007448421820070800c4101000400c1403c0e004020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 12583828 1250 12582578 12582589
    0x3011202040c0e010509090a0b03100218010201050403020601120302010609060311030706091a0f0c120a030e03030601120b040e010c03020a02060a021305010c14060a0902010f03050f0711070503030d060302 90
    0x9125000d2602d03c0034040090700181460060034081c50061039504000b60161109900031410fa090040032079804807004001c4c803000c1d6102100108511468654000c02540140520f90055034135030050013150707003400c50040c42ca03520100203801315900d0b1000007c49884034801c48010f5406815040700003455181454a0210650b0081041000f41c0b5010044203200c2072a801c1c80640b42d230602956400c003800401014000d0f052180614000c800c0c02070102c0500310010003406501d91400d11542041c0221291280421a406801b280b40b00c91003000b0300078143d005c51001e1800900020700c00c00307403d02c1c1e60300710342d0301c0140c11012075400110141c50741d404015541d40090440303819890101215a5a4406080d510800e8188201d01c0e20480810144030001c403d00c00c4001c0c2198014a0100c4544016102844059000c680c0c10584840200c0c824007035188030340782e03d207041d803580c0d1290360b4200c462902c036a20840860140140c0071405a40c03e0000f01542c10311b01c0f03404207085095004028 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 12585078 1250 12583828 12583841
    0x2040c080f0708010b0a05070203240609090d020c01030f140403031a04090206040302010e13020d1a031501030b06030f0102030a0e011104060f0e0a05181b04030308010308090a03080301120204 84
    0x2c280000100108506075001d0210b6a42901c0d40c60481d031074050034408686880d484502c144480c1d1403800780c0b4a94980c140004c54440c1c1e004403103044a0381c0b030710001e16440da40c1003a400c00058102040303040c05940130303811580041d40740180c0091908400100464a10402d80717044000030b444030f5041d0300c03e90110b02c001506d4030f002c4504120720019030380024018440c600c002418819041880301c041c0d540c3c00c05040315a07001400540d6200e00c40c110490081030b0089003460356605901d41001503040004010f00c101c6031003100120946d0850300c44000d004c200400c12540f61058030030300e403038000f400e001860040076a584003107280e099403644c031400e665003141100f071048800d00c0b04020481d40900800745005150034a03848411410011602e46010384e08174a802222641507110306200c0505440c1c4074240343ca009003c0301800505c4000548660302c0080c0c0028400300052010030f580d0342c028010070301c00800040d10580c1d2a03a50f100c4540090740101504000700d1141000d5091501848 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 12586328 1250 12585078 12585091
    0xc010c0206070f030b060712020f0304030c030b0f0717100b0703020c04051506040311060d0219030f020906092707020a03020c0102030418050402030a020402040f0f0e060907080901060302040c080f 86
    0x280022031030a004500351f03014841c005008002c00020040480703000380311040d240f83c0340c0301c152a541d46e100e08120900350824413040329040741c0301c0001074024907036040d018001c06480d91141d00c0d4002c2240c0c03038800c445c030103010000000c1e0b800100081d03c000600007400d110780300380c001c2d200031030510b420402142d40c0104000d240082c1c0f5402d8a02542e148400c1b01c1c140c0346d019003030b2482b40b600707040840c51a009460000741098400a02861840d804041c0020591100c0e40c09120203035840751058246e00030b0110464103c0c0003070040c20030f103190a0706507041414041c0318001a58a1640c0003001185007030300c880300542c0000b05200249070341481490319420003030000b1450306203011025010411019584e803400740d07517403011078115901440075884a64008200359121500c641c00501c4c103580c28455000c100e80515000202c0c00da0705445544034410007813081c1c0c10b030390f100f21050301c80b8840100400355070756a0b8400400180c0e940c0c0300c1c00c1101d0030700e9900e41142d854501c103031001e0f02402401c035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 12587578 1250 12586328 12586331
    0x50303181908060609070201110d140a2702010c020603010b0403051905100c0509030706090609060219060510030c03050304090e0f0619020c0303010e04060c050705030301050904080c010c0206070f03 87
    0x184a42d002c00030300d641c0c02000503140b00f2002d0782c81c14022401001e001089001c01c0340006850030041c944c1d0b420541e002054060102c1c0e8641b60f04c0480c5045540c038480050058a0784000302c04040040d8920101850040c141408100c1107640041c0042d40242c105001948000c6418000e1000411800d00fa101c811030210081c0191512041d0b901e00c3c01d92024100140c60ba000d186a01703101c0c4003500e45604024049844882e1201c4001c0c004144501a034000140400800a00148005071040185958802040c166611510f070305015290007845040e44052030900000011040d00740e100095000c1d101a580b110b09114134141903900d00b5101c1e605681c4082019510f410780410400d41020034141800e040249800f00e40b4068002c0ca80700c1040c84c0804000003980f0114030002c0313881284a064100f0403003100c0c2c00b0540c1c480c00780540290180e40148011b2003103041003801e243e080b5005080240c1060518000030382550301a0300000c005801030302c180084ca0b034010b40e4400b58240305040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 12588828 1250 12587578 12587629
    0x806040f0204020a030905030706090b0907030305030c0903190501050109050601080c03180c04020a03060f060906050406050a02010f05090a0b060f0310050606070c0303080405060c18040902030705030318 89
    0x4854120a8006002900c10b550000c0c20640d418040c0c1e000306007443d1710205032502c5a0407404c0010007014140020749800e4001e500050b40380f0800315031942aa0340c10303150b072411a101e0b103100008540103c40d882c0d0700340c40780e0301d8155941145000c00b01901841803001251030340c10000313150309540e4090300700e40c1400318510901c040721076840192603100d0f94244440c00c1100c40c1101c01850302d0416140c0399089440010100c100562541040040c3c84050341c0011115a030fa4808444a51032449a900014028003080c01080e214000410310440548004a030001c060010701040301d006031002c0002da03028840000c2006600f00c660b0703034000e0007110302c4544940e0b21008203803a03911600c2a03100c0c136981c601c00101503645031025240d151303401c6940303815056141e282c00360008600366800d5986100784c03c00a441c824009086501155a070101c21017541181c20a01c0040c0c100000c040340e05006088003c107654500308050401c00b58188400c40403141e0000078400c60712104498054194011034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 12589935 1107 12588828 12588833
    0x5040c031b050a120506010509040809031f0b04141f0f03050601170105040c0b07020105120c04060306080604081806040e070305180604051c0210020c01060906080604 73
    0x1844060655840e402a01601c100c180c130000c02079400540140264100080f0054100703208091081c140211140001d003031101c4e04180c0110000148044200304005001e007405026090301d040000914605842c03820590060581003a08002e45c01203510b0130300801030340c005054074001003c41c83c0d2240b03071403078481e0790a101d014000303a240c0203001424030040c8201340c0210b50000c5d10b03400352441c0126003101a00b0030001681480410b20170000782100b4000914440c202500001d0780d12810580080e044403850b40000d0100c1d80031500708800a091041107905064411020080080071040018128401c030340000412003040c01c280000c60b84c1542115000b000030b900c0b00c2e00f050804403411682c482003102c01500e594020605404102c1882e01448403000304c07807041d204c580b20400e07061f8040c0d0340003503028a8640e659505c104840a02c03031003001d02625000c03025002c5070030940c = true := by decide +kernel

theorem cover : BRFrame.Cov 12410078 12589935 := by
  have h0 := BRFrame.cov_init 12410078
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 12410078 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 12410078 ≤ n) (h2 : n < 12589935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
