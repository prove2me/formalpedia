-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4080
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:30:29.781992+00:00
-- url     : https://prove2.me/submissions/2a75132b-37e0-4d8a-b3f2-6888a2c9a5cd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 733633093 ≤ n < 733812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 733634343 1250 733633093 733633123
    0x3801050403021503041b150f0c020d0b04080d0f0504020f40110d05100b0711060702030a030215100509070815030712050c0f0d0314090a120302 63
    0x11061005071503d000b058540318102481036165100c42c40e02648004285402c4000741919520004851491303210300b503091203068031401440d41c150401203c00ca40300320b00203500a10340484d8800041d40301008564854003410000b400d04101c1c0d05c100b02582e00c0c01c0f24143c002c1d41c40c0e80910095240c0b5101003540c0203400c589104d0841c070390b900e000c040c680da40c80300d60404406008078140100d040070210270a0642c104800c000c42c540882500b80d00360400d40e0070300800c4e454030001078058800304844205403002d61000504000d41030351441c6030714240440301d07a00300c0c00034003c000050700c4c1003010740344dd0703482034016200d84035810714001e94940c0c000300450414400804100926140c5a103040d030490194545034003103a413414000000d80f0807808020f501407080070b0b00050070390840c10041c081107100314143c4107455032040030007050074202500300f42d021803404e800b030001900901c04540b42141d00340411f41010702010000b40e150303506620415071400e03910340603000c042c1d06200400c080d0b01c501c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 733635593 1250 733634343 733634347
    0x1180509010c020a140102070209010b04090507030608250e0a02070210090b0714011b020102190305150f03070f09021b060f04021e06030a0b040b10080f0a380105 71
    0x30b51002555000e1622028091924400f20700484080030340440e040260090310800265a4510a801c10b039071141c400c90502d40e01d0000070580d414840c0c040c3c00115907012008140d50040000103d010f41c041c0003108085080d140341c00200d008204586520440780194016240c2d012801801fa5152520340000c0030482c080000b80070b165041020389440c01c0d04180c0000590450451142c01059036100030006003e401d5284500c0d19415001407900320700c001c4aa008048900c0001e90a41c2d00c26941e511440c1c01d04112030b0f101d410709124005031080700408896285070b54051900c2d0802c4a82c12140d103007500011010440a1180132614050604000500c80c900d002e1003140d9800d00054402486000301d020940401140011700c005c00da4001130405580e8100b580c6488002c00c0480200340c0502d003045080246440c026241c1e105007117441e107803c041a03403110000960000c0c001d0213035200a030389429003110203135a080703000a07496042e00a05e60001314184010007014503611b1260400c442 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 733636843 1250 733635593 733635611
    0x1f1205150103150807141503151c02030a021315063f0c030209190911030405070603110d0c0e0411031b2a070e0106170720060118050901 60
    0x200180140440301050360300c6d41c015000e2000144c490001030340540340c01502200388081d031000b0340000390300c042e0102c0310100100e07440c50b0b056524401c07018010350b058200340d41450160410040c40c00075040c00344000540f80c440c20200c070000e54441d1300b0600000d05006030758030b41070403164a590342d10480c42280d000c045001140c0c0d0921400d0302c80f102071b41141c072401c083c01c119019405554020400810701e8000e466602e00c2440d40c0041489441304490078410450151442c4000700c034052500701c00a06151801d01001b5000f5202851600402003c2003181440d240700383c1c400d0091380c545a95800790303030382c4011b402c102c2034a52014884c9840e21081003805007603010340091076140498050040c0d00e444095955405400070010110030402441d044004000c10105081e001d56a242d80038660345d0762581000c840307101040010031803010a25010074001405180f091000442d0141c001240d0600c4000407404c162080c0c4c44501d104c035021800040910b0340e4004c05a01c030300102c0080082c204 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 733638093 1250 733636843 733636859
    0x12060b030a090c090c0c051c080f040512070f0506070824011407060902120a050c0f0d05011514010e10180915060e0108061f120515010315 61
    0x44050310196201da9649101020000203954800043c201d42d14200502000c240c0040d046010001007151a80900e00c040d400d0404c00c036900501107410396503101d900769107134160507847c880064002e03a280e120b4030252805581c200300050052520451402c0010340052070003624085c40503240c01c003801958030400044034003244400010161481800e00750141c01d80040e583c1e580080a04519000c0003d5480c0501c4000d03000995810700c261152103000000303007003e82c1c4602c2041d00c0280b65410104111403c0e2421001c1c01e03901c1107005100000407000e45e59541d0031100d13044000151002c0f00e4500704958045051601e044070800e090022802d9243c80002d00301445544a000070701040701d050b6607410310308030302c40320262944c031000700080c10070142d8413400a846881840002407007802e000d006e0354815101d841c09954058100d1442218280d81005c1c0c1c001040140e504102d00342c0d800c0c00000c8001e0054034040d25401201c2d220185500c000181500d18106504401c8556020204441c134 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 733639343 1250 733638093 733638097
    0x2090f03010911090712230610050313110d06060e1501050318011d0304050f0a0803090904060f180b01050603041e080f0309010c080a1104030212011d03070312060b 72
    0x3d40e048800c1c0581d0f40e900c0d4419101038a541001d401c882c2d180c10240920a07001c25000940c881200d0045801641d50070100406005860b40e040002079050002c100d21701c1e01c00f03852000d00c078482e84054404500c2d00780800d04024600a007990203940f1407004101c0300017a454415000410403a00009110481c40064210711000c2c05001170200c1050040c031094500f9400700c50b1800001100500c15559006c9060340c0ea0018000c0c240f0a5404904440301c81c945502418100c4000d2406517081100070700820020610040c030590b0669107894003000c606125200c0d5000001d4910b0000c401c9001c503082003c60008140c00c1513014180400070f210104150090041c02111007221182006600f468840080d000b000c0c1e00c0300802002000748000000f042d0401c0b0020041603440d50b0040ea904030118098909521041c0c440e80d03001c12040c80981031401400c0c14280c400e40020921003455041060302800c07000c2407031842e0300041226010141d005141e00e00040b42e484e0180541414a00829514 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 733640593 1250 733639343 733639373
    0xe061e160c172b0e0c0d0f02060a051801081b0a0c0c1514030601091203121109030f07060504050d060e060a02040501021506030606060928050310020f070f020a120602090f030109 78
    0x15411b07071808504001716001d403a0900c5901230001034a545407060b01410b1a040074265107002c400d0440e007250994450502581700d10301000d0014100070540e541100c1d81d83c44102c1c500c0c01c200601d902d01c8040750300d2090040c001d042411107403c000b42e0341c0d600203000002ca1140074483c0d00c0204280304141c0c0c1e1149266003941c0c1c4640c0c02103111403483c80c3c144d80c804611b02c800c0301c00606210b42000c400b40c0460282840e244282c0550703d26a910b00c00707168581000380903e802181061109004c0c40c1042e210645449218201c0000d8142c0c1d2500c0551802d042100c00c3e00f2465000282070049580c180444660030781c3c400c0c0904d1a030300703001c0002074607070400520341c2d8001c042c0401e1494803540c0b4050305011701804003d01d0030480445140000784842c250140c81d0003031040b9403440f1005400c6108a481d650130112807941441c01982c0e40902e929180c1d032007030340d101080d9400440c03e04c044580c2d100d40d407071090a0041e07803080302c50140181070b50300342500323072103070b4903180a40c00071841e0b81c8141c0e220 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 733641843 1250 733640593 733640599
    0x130e09060a14071d1f14040e010e1315090c060c03020a0605070302130314120304080307050d09020409051c0908031605010605060409050105010e10050306120f010e061e160c172b0e0c 80
    0x1a50f40c0c0c00c840cbc28070301d0304000181c220000c00e4011040c0142562040e40d5140c040c9046c3e00001d5210345007611840780040d030007401a40024012800310301981d010940203209890058503001300085130035a0200720381c00075901c5a01c9424000c020003420440d4011845c9481307805401c0d4a42030b2500b072118003000f055002481000120b88082580660000c410558020001c0010a00c503060155840ca690321290010b000800041ca0761240550020404c480100004501e401190358000c0e150300000039046889641341c01010a5507a1148050805000d5241c8000358a40c90240010107180818500a020b9150f0380cac610048250303c00100c951020081c0c0c0c600140ca4800c0034410f18210341502c10441a5103007010300346401102091041c004d64405180301d00c0303a41036000d10801c4850039240a119541c4004500041e00d0145500740356590051800d2a10048510400303a2a079100ca03600305808501c1c02d5400083c8858201c10a80f0180b902c503040050480170098070b6034032a012324580744 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 733643093 1250 733641843 733641869
    0xd0e0601050a033e0906032a06040302032a040b060405283308010e10031506080d17011a130e09060a14071d1f14040e01 53
    0x50740c0448000300e1100301030200c1350390002d41c070041d070404410401100b040c460510140468614900001e00c444000d0080e0050040d044940b40c1030300051084992494000000303100c00409640c00b80038200c0006010a0755a0f01d20b840206c1d81840e040c81140c0c40d9204a1901d0b02d030b2401703a00c0d800300795419a40256080800880d20282003060780501c0401201180c80021021035a054441c1d22586954083c169108010403410802c20f01c2504101c00030001400ba01c004001c0c045406141c81d4001b03c001e244600f02036101d85034060f6030303504046a0b90307036261148400c200c168001c0088124031005c0303240c0b108010340f6000540413803001c10301c58420306501000c92001c0e0340784101b084a10318154406203880c801ea54401c0014040c070101c41c5050b0078011040010003c05083c0600d551119901c400c41d1a0340c0d851071400c0d503040b5402c401942c04d0440f003910803034060700d03814242c0a1545100122003001488004000c02c04218101003084000c0c0602c401c0202d140c410380190305484061342520 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 733644343 1250 733643093 733643123
    0x22060203071a09190606150c080d020307050d091a06030f1f0b0a080a02010e031c080c16031206080c130c1106040c0f050f0f010809010e10020d0e0601050a03 69
    0x14a00612800ca81041d800c050b04c0c0401000303d958003020448081d807900d000800007032001542c0ca0070354217070050081c0c0b904000e14100203400c0d034002d562102481c2851400c10340b540c49208100c60a0240c00c640300342a44200c040b00880c040100791340704e64220b004021004904000b507072150503246055400c0260461202d1500000c0c1d0861081c206020300340b07082c06941c42d102c1d596200c04540003a40440e600d02560199030801091580c1c000c401510300342e0b28800f0840c011104c04500407c00c054000c01030004440391a070050040d03130300710b0007a0381d11345411000ca40c51004490083e4401c10aa92010701007001c19280e0031926030046402e060001030201800d4010744028000d4800b04989025901c1000304201c100e2200c07206444c0c0385002d1190b0240c855090008a82400412039032195a5501c2090f06601c101c00c081d81c03002440c07002055292400c59003d2411300c0414840345010340104100b98031082c2c1c3d01c11200c1c000307a04c1005000c4e035490071010403095440c0d80000380003907880d4030602c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 733645593 1250 733644343 733644361
    0xd0b030615011709100906050612010e0a08130314060a0b0307050a1202040e011d0f030a1b17161b03030c02101b0f0b06030a030503010b070606090222060203071a 71
    0x22828000185101b03000d10280780c41c08500400d0b0499103c2c0c414001d11104100d4500305104406c0614680700051030840d0440d21400400e41241040309110183c008001c80012108542c002d003000306000181030a040c0b00c42244241c07001040c1d154040e5000d05c02c1041150f460b8070400c012501c100300da40c40090600e0000c117001c1c00c40c190f00900c0719070034514a88028180b01d1020310042c0c0070a019200c602103007903d8244c0b20b10403c0c410324005403040c031003c24080b1406884a03003440c494041e039171280c07549422302c00c42c81e0803010740e1100c1c00310840b601000348580c000040c41a0462404018101403d683e00074050b4107001c2c401070701508442c1c5500360403601030a81161880c20350024448205c0b51440c0182d404041414100d81000800300816694100021041c84d02c544c0354485070b00356070810b50001103581119005844003078403000c000544e100d162005043c04030344c2141c10192000c3e10465407481c900540d1141c0219401007100f240070941c040c0790062852400360314080309442c0e549507 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 733646843 1250 733645593 733645603
    0x61014090607030c03021011030105010318020d06050703060f03050703030513270c080f0a020c01021e0301090b030f0a03081b13260c0f04110d0b030615011709 70
    0x4001d80240c40055150141500b00309034480980c82542101d5601d00c0d81c0b0103200907120020310018504a00f070005202940c02074105000500c25030001c90008085a00010020f0180c40c0d402c3e500940c0d02c170705006065506000d5007020300b40800360302d0b11071461596560380e0760001d03100140c100000440d5240d4261450882900100504460a21881c190414003440e1003046001a00c86600d084403c0700c415008a0301d0b284100100f18100707140d99107800388000a58003031905205955402c0006503040328115141c141040e0030486032036141d60500101000b140d1020405511030b5004000700c050200000403121030540d414a0054840d440351a40d02c8120000c651039000d800700d001c40d100e01c40d18050300402044903803c0744901c078040d09000c01200e16000d10501000241c0106e42c00c4425420031001d0030340c2415025000041c18800143c01d20395541008004890103510fa4080710340515007041001e802aa11015440f00a5004000605a07020000c550f40320090030000240801c041400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 733648093 1250 733646843 733646857
    0x1b291807120f17031e06040506100f02100e0109060c030207150b0402070f0f0506070f0f080907050306041a0105030d090e060102070315231605031513050108060708061014 75
    0x2d084d00c81c1491103003030b600c2144507a4a22200030703404000031100e151500519001e03c00180c0301118240c0d141f0000c8401180d0158124290f11403101800e8800392103203c2c503402d107116100000f8a10304a46402c506840b45c0c0350300d050800d0300601000780400c820050030406515088000206142f0701004507000e405901805050040090039200c18000f20711001082c2611490648080340d0f220b0000751421122082014005086000300980b11405000e8464101048508841036030b59030f81c0000e481c004003101d0484580360308400544000740c100c0b0031b06015000c00c4000d001c8030a40e108004003006400d1258440e4248940041807040c1d0007030144070043e5030403084800d1038015001d40200640204c80700683c0c800c85025080c0c10400f0841d0a0f103018200740201c1123204200040b080b1442c2d00068002001182c0d034915000803985c2e03605019000b010801c0022429600d0103030198280b00b0020444014001400f0811496507522803818088250710308020070001c031800445202801948 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 733649343 1250 733648093 733648133
    0x30f0309070806100e06100f110106080a03020304060f08090c10030b0306071d040e0c36010306060509070e13090206121503030a1b291807120f 63
    0x1d051284c0008000c40303003029036400051080c85501d070748091050070010714000c1c0b40018030446611344410710500300084403241c01070022078440d4840d8441c41c02c200b50020101c0c0540e100043c108400d68101c1090b1345103554600301401940b500c401d500d51600713a840a40f40c810264540e0742c8144e107010764040c03410404050300f210030600d8286c101a0100f015411040c0d0041111359106c10315150500450f14808a540b0107401b10700448014040c43c0030200b1380301e000e000c0c0c22140c01385440d061007629041400c1b80050442295144d803c000040f18815004580110a04801c01c00d0301034210b8105803015109403002460441c1c00400300f4000c1c070003604020b40c0000006a0303080601101130b04103002d41c0b036024951002207000c00030540e682c45080c032800c000c2442c081c1110169410b200351502c003503000d1b1824462940103013401403444080f404402c210b800700b0b02c0c184035106400001e105d61808100000300f0078207003040248012503512a078010121440d0b43c0307038402080066050f02c56008150303 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 733650593 1250 733649343 733649353
    0x3032d0f200105011a07050a0b0a11120a050f04120f05090a090212060a03150b010c06050c180306090a2402130801050a180b090109051c081602030f03090708 69
    0x54440d05018040a101d40c1c2c0f54021726004e01d407010b0b02c501045900c03096000c8010008507003d9680c074103881c04001c108140c080d54070310f40180a0701240c0020301001c0040d1104100c103103000003406040701c030007a01c1007025400240801c80010401c3d0694001c5440c00e051160086458800c11240f61040c51122038201c0d09810000801d081c160300a409140e09500f05501145e980d41c0c203111040a0314803000d01900100766090f0103c0c04640e102001104040c0340402e0030200700e0f29072400f500c10030764661500c610001400d00741001d10804943d661181100907254506111600c5a5169814070014100d03540d9800c2d242112104c10380d92103400282100c0941d200c0d40d1151809510f5000e5210f04405035091400040040310144500b840002d00702c030401c503c1d48025118030081817401403607659290340c0c40d4029008034104002c28640c09140d00c20450140117494402002540d01421040100c5c1c40c035503e40080a03004015140003044041c0a9034036030387c50010b07182c6080d2442c1d00646082c010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 733651843 1250 733650593 733650647
    0x50f0f250b0d023403120c08131104060b0403140109121d13050108060a0204050a0e06180108011a0402031303030c05070f050d0f020309030a02060d02120a0603032d0f 73
    0xc3c02c02d0200d0074a0080e200c801100341d5081e40b50064036455501e00c00041c000c030740052729280c3d040d400f030513800f0302a0340100400f00300071010400701c4107690407844407203202003010403c112141c030743c90070180100402132000c0d4225507110045034010082d1711042c046c1d80c0a1349002041d07060108003031070000600d203130951107404040100401080c003c100d00d42c00b500c0b000408550040c0202c40072150050f01194070b1a280091020090a0103030030307503501040340401008010408059603010340009800024411149003820341413400d404c016500450043c401c2100708041600f10404254150502003813025030340004541600c5003001c02003140042115444c113104000840035031049240d01c5418295001c0307501640d4038061030020541c1b6600c040d40900c014100f00c00985400d0100d030b00094209110b20070f0141d0710075000c642c80300c10207a13100c0040061541c001c8440c0e00c0c104048074140d1050900031145203a000c0088003620074081c070b40385202d1181d441445140c0080c50b44020403109104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 733653093 1250 733651843 733651927
    0xf06050a090e180a0b1608010b04230409140d0c0f060f02162a051f020c0a0605091507210c060603030e03070e22050f0f250b0d02 57
    0xc1c191003000c6c5035503031086848001405040200c0c182c4038600d21103401d0078a00b4586c1e0f0ba42d42e1031030740792442500c854440941941ca0b90301402c100644181c07114007020090304c13502c3d440c0c4200b140c0380104020074044c17040e02044c45ca510b103c0c030f040d400000200740c02a091090002a2041f0364000504201a90780201400340900303081c141c00203524a003d25220084070fa0b401d40b400c0724080c150740540100c4803815140903d40c0c160f1000c01c410b00588000421580020f10701c0201075010001140d00064041c0251400510002409200303030001ca05080302d80d143c6482070742d071a668407414600ca0320040c042c00750086a4804040e030f4420010301c119500ea20300101521000c0c031030103000748280c020104803c8298100039100c0c558204c14980c0d034000302c0300e03d4585c5100721002600c1c50300441c80400c18202050062a8000c944403009221601d40c1006620602c245802e544100307040721103042c4207070401601102d0202078a4200542c179241c58242c0700000090117141c62443e8044251003d034031038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 733654343 1250 733653093 733653113
    0x30519050c030606100e011806091427070e19030b06041a011809020a02161a0708030711070807080c040501030b07111e06010f06050a090e180a 63
    0x1803003141075515100346a0149941d0300c10070741ea480c2e4400c89251810500301c0c81000740100c01041454400d20200c1c95130f04020080c0b049030084000940c0c010170034000c030442042c00500c1d481003500c0c41f16804641d041c01d04202001082e204d07602e5100f68002c241c0951040d1405800940c000701000c1c00004121180d81c52486207200448060f820040080c01c81d1406106000031003003070b4611046400300c0780c001110711004094050120507441c40703011441c0d0a5504c00762401e040560000e090a0b01900002e500c6090180d01802c8080d19241000741112080030130b41d4441503100c1c42d4944c4a40710303200705541d2850b80000c80007081c4181c0f00c00103913800300022450100d030050800d85982d9800340c400d201c161341d000d0001401c5c2c07040400c0410304592280500401c0d400303d030070035a00107213560091905840d4105840c440640e000310018443c0200010f1000001e204508055150801409019144c640340342b02d481140391511300012290041c90341e000c0914140701c4240d44158100d46031800500d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 733655593 1250 733654343 733654393
    0x4050c0427051501170c0d02071505061002030d0f0905100f1a0f1003020f072001030501140d05010f0e0124050915190315050a20130305 60
    0x51401c00e004140003592040440c44000410b94920120520f40f00d5100f030304441c040d001b400d1072901040041007003001880034045091045019000e500c072110080025584068181c9210701600035081c145a600001140c480c000c590384c0c0800d15000c488104030040100f9400980715014140340c1d034810800c0f50380700c0e403100070005004200301c81031007500001071501042c007140c0202038003501c06190714001000311801c603680d00c0d01600d81981901807058a070031000084070b0010005c0d089480310000042ea0300c072012021310302000990701d009500340d800f48681203401d000e01c40c147c0340034082c01820f404c0340b0f0141e41106c0080c40384505c51040c850080500003d000400d0b0744842c14480c07400b0181d83c4071021104014131440c2152200060011414402480750b0790101040300d09451034108200384200070b60003200000d00d55900b151002d0140c6400410061002d41f620000c03140d42a90354055160940864007074a84a01c18101010b019244640002d40644210705c2190540c0302e44010154407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 733656843 1250 733655593 733655669
    0x302010606090b1e040306020c06010e07020c0a210c0602030903010b04380a06120c020706140702012006180303010501020703060b1906080a06050d02030c04050c04 72
    0xc00307a4a800031510440c1500071504400400c000002440c1d120700c01c80200d07481c42100303a0b864039a44c2e9803068120fa100514203903540d008000104603604064842c1a0b0100580c000b4060319208140002c08204540c0a0143d1001d003403030b4500320000ca26840100a603034024030040c0c07844d840c0d4a020355650088401d00d84290b09190360861107007080c0c00f0b204004d065800c114642e0700080d8240001d400724004c0030011111000c1507080d241d6488420a030300428040d02c4d00c100e07007a02c19402c2010f541d50400e591042d0340c0300030010002c8650102051900c200c17040300c0b1580303030407041c4012158408640614425100810001c035000b020124280d0302540c01507c1c42d9061030b03d500c2c0381d03580300d000922070140944c0050317034100003140311900070b0010154010801440c0300c1c7d60540648020754690031000003c0c051400708800e142540c814a40646405c070340000c0d4036041039002079503075440e00391000d0203103031288003244250181070247c90142100284480030034040080441c1c9480110340c0000d6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 733658093 1250 733656843 733656851
    0x190c030212270f2e0606120617070303050309030d060806010806090610060e12010509010902040b1801090c0c0507030b09070f121124040305010c02030a08040303090c03021804030201 80
    0x100034580082c0d0414072034854005444a00903402140b0000d02441410711380c10111005900d4001481d48904805407a20745c8400404035104a52041180c0c01500071000b850101c6000503010240080c00208903030745441c09555a0741c540c0e11060540c001c45005100c104d081074804514103201240041c1603807607a40890b440c680d540090701c0e980b14401e0302c0140003840e901c0c200f440410300c100b42e0780180e00c4020f0a00d01c113075900c5903081402c66004a4000b415659260a003004500d05406140b0108000315840c040c00c50103285580000744061041d191401d64510f9044170450090100c0a07016030042c0541301001d50303d0405000310a01160910f9280c05140000b00340c0340c03003080282080cac4080110009611420341d4440780c818005d406103c0e440350951200300d1000078208010210080445e00c0140c440d480d5150082c00c0d00c0d0542c070b1400554109029041080c0c0c1d00c2120710741d2203034240c5000f0031340780c2c000d00f8940c001d00300c940c002a4020140340c8103c1003104096070481c0c025032182e80200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 733659343 1250 733658093 733658161
    0x705160804140414070315120503130902090f190801050f0403180e0402010c061e06030c080705031f1103160f0806060f0705152d190c030212 62
    0x10044881144d4010076612804d00030800c0c181c440e62050002c42502201001d082c0c0e150304091480d86500030080300c007948002400d500081e1108051002130905c50415800c0c2000400090803840e1440080d81c0104901907040303004044404013100100648002005242402c80802858400450b41600450312007007140106103005040e51048a20150340385a80740c450750300444a000000105907402c1c0d40b1505a01d544800034507505c4402d040c0700b0000140680345103001c82c00307003660790300801881e00304490400c0180c8020958040401910b50307807030784240f9401d0740342000700603243c21551030400c040b04024960b52801d5500100541c641c82d916104003030624112013005c0c040341d101c3e80140045c892011003007007480180c80900d10410a482106800031002d143e025402c440203a1361820840e50b0f0440d44890652000d80910364401203c0e0364540b0f1036290a8500392520180c10725652400014041440b990550b1800c4410700058007950a08800c20940350904c0b50f9492801441ca041c05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 733660593 1250 733659343 733659349
    0x1a0403020624040f090c0e0601020724050310030c0e06181003120c053408070303050901050408100516020307021c031830020f09070516080414 63
    0xe40400b10201c103584044008014040602401040402c00130780760040180001e68007110f48000d800040c2d242c0321146801c10009162171403550248401c0c1c2c0190307554590906c1054140b0305400c01504001e036880d240d44841e101d0780c0986500160408001000224200b23815640190062000301e030718856100400101d407101070020780300024040c8002d81c0400010701c42c4450005441e20780d0800f259a1103280d00c80c05d0501e09158256203d40312050f085941401300d02c0e603d480000325812440740214186055950b64034074900020f401d002c40454008050ba100d142110050540b190580b242003184420410240c001618241c2d13070003110b074407000c0070248008207540c040742e0004c10400803c0c0d141c0c1c1c00c0350b02c0680d10358010b800304500c0100f40164600d00030b8581f0003c00c504d11b1a0381d0340d60201782948403056007115050440140d140507850151b505e510000d8101402103070f0b171000c40d48034044103848922504514400040544540c0030074001100040e20440b0703086003481c180e41c0c4480d020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 733661843 1250 733660593 733660621
    0x250e0106052a191b0f05150c0706080c07120f0e010503092a061902011505090a1a1507060b04020a080c0d060b0d0504060b0d0503030705161a04030206 66
    0x804140c03684400c0303440400e02c12480c82d0f03401c1c2500982c11000c021904050301c0c803c102c401d41248020592501c410402ca09003480c807240743d40c12000300c0741e0611742401107140c0c458035644602e404000110004ca1a2800d0341d8007100d24095000d10a0310382c80c800d004002c1d1411020300c241c8804100b81001c0c640d8654010400ca9201b01e452601a1070720359800309000b490351814102030503801842d0f81040c01241c50326030083c00541000da01020f54004110b400909483c1804000c1c9201244c0c248100910346500c03920680000e0b060030082240e40130030f9802c40034100b07107100d002c0e48010201002c0c080c0b0403210b0014008a8050307001444a07003e00828001a4031584070150001809080002c0c124501e50024010841c02a0804103165a40d442d12124035080b09600600b417039504c8042c402000380510a03c2c10342101a901c410446140340c9030341d40ca90000411080c10b200d0001041207110402d182d1110005503c4000c030b05004e5440b03246100000c5d8221001c03000b521500c00803414403441c00803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 733663093 1250 733661843 733661917
    0x1110080106090b0f07050604060902131109060c10110a030c0e0918120324010309020d02060a090b030123120304090c140d050403020c12250e010605 65
    0x1900b01d005071800004020690202c250000d482100303000c2000090000d00115000ea1702420b0086488421401042440d119403044d440900d49458945405d12a420040d140b01500458005450300120a1300381d0500214058032a0345034a0503400b102c9440c640c2c4040c0c4100031f200d590420415030740744003e84e9400c000d5541640d01055076400114104010041c18141c1d0b480582640d03065100e00c2e9a00100e6002520200528400b40480b0203441c080c41025600c0d032082444e0601100c00382c4d0f00401c90090040002034096200020f1060f5243d0003030141e07100a05400c00c50035900c0d82d40d02e2850b81c56980118050b45c24003d04203600c103452500c01c03c0c8030510002d13503024501c2c00d4600160040140300401c004410710134504091784290b4030043c040c007201510350300c020440d440d26160007810140a040001d100c1c54603041f0581e11242c0c0050740120b040b0102944003030a15000611b202c900403d544003a000e8803282002055250340800680500e03c003c540303c41d00c610451410300703201a0001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 733664343 1250 733663093 733663097
    0x13151a0a0206010302060306030304030b010e160503060904030309230c031b0604090e07170f070806150420030907082b030c03060302120f070b3609041110080106 71
    0x210040c0050b2a0146c000c50704903000400302c07490150340340c2e5400c05201c801da1000305064110410802d40021101c1c034951441c032a403604c3e030719510b4a000061404400034102038201540c1d0702400c020032004c00441d00254222040c1d412000c41c840b0801c42c0d6440b000f80d08280a800741e8822a150b001b002c501c1010008001001c40c0d08190030020114020101c1001c100b603a841513903400203424095070b02611a04503d00058295403108881d2686050542da0207441e05901c110304225a5030702a480f241d92001040300e02096148168100e010744102c40400004e1040e000001c0c00b0003c003001a0810486800c1401c0d41c4103e034190044a146201c40e9907400c40c4207143e10044000030340300340e201031101c00d000d080c0003640f9900c1c0c1c0c001c10400d0f41100c401912035405141c0b00c020888c000c001c008010b205c490340796860083c0542c03244586d02c096286690b84440d1b0384201c10809420001500443c2001401c1c05209145c24144070548080c0c43c0170290050701e4120740351815602c6001014182c51041e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 733665593 1250 733664343 733664353
    0x420180a0806252f010e01151e060f1707090e090d0504060302130506040e160c080702040902030f0a06021809150123120f0f0f0f061206011503180b1513151a0a02 71
    0x100050f83c0d01107000c2442801c108071881c0310410700c2c4a08519a0141c0055502cec00c0410b800c1960f4a040403102410854a651210341201d822039401802c403815104285005a19504500500844955290480c03640308002190110f6004220742896104003ca0007840c100040d00d081c0c1521006250180030706098001c0040d4005801c00390803848040d0303c060110b03aa400c00008116040c00000c01040320803c0d000554030345c1917080d84609a100380d100f04c580c0001424500c84089110844c0d0101c03d0601c0091a43c0e9060700c2d411814800600794260640c5980e401c00307100040c1815011a035021019840ca0081403c11810f1681c09100d242841b49258154689805100c01e03001c008107480c3d4844400d00800852080c02e11420b0300a00300b0100b500350b604d04810f0003506807035500004d032030010700c039005c0354011a0300c0e0b00d0a07580103804502061a02034540c4040f4100040d01255a803015040c0740f0941c190114041648003120100c16103d4004118843c0c0006c192040f8a000c82c0180c0c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 733666843 1250 733665593 733665599
    0x305030406081005041e06050114040510050c030307050405010f050a080f0405010605190e010e040b0a1a1c060b0420180a0806252f010e01151e 63
    0x640b03907064201d0941100646441d50300d80c0085d040c0c600322031400451601c100f0113242d030712845004142c0540824200300d5000c98400310039030414007842c810244507000050105075801d0003402100c0001d00c1d22801c0e290341e483c0445001c1c02c1036019100d024005035042903d120460b00c544241c5400382c1807a5201202520b4604000c1a1801d020b04296042d56981c0400201f50341c806002411030f16112601c03410380351501c4408200040141e02552040402004000004140608041e444032035560001110742040038440f144a040c0075010782c00c000300a01d400c1050a001c034010000f280700309001c0c0800020ba000f0f0209641c03420b8600080170b20100061221030b001c40d006041e200800c014628510340c01840058034694080d84800c0c1a60810b038107005d22400150403e403030a42803821041d00c00001c07404001d010b00070300100c4d00350141d80021900340c1390b9000f40c4d662402d07085100090042c0c6190f0800f00c0e00030040080b42c4411381082c0140001c11a400c0d1141c0b1400c010400707450020145 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 733668093 1250 733666843 733666847
    0x21f11060709091a21070b030f0408071e03120506011d010c060209090c2a100b1909021b0c100807210b04180b0c0c010906110c0d090305030406 63
    0xc44150304100e68a100003110003c0c0c0324403042810000450117030441e042d480311445810100b00341c00100305c0740d10400400800d6692182c034280c0080c1d000301c1c250b40c2c03030780b560404440b0001c01056801c00e401691200f0414968080140c1410020001c0c0820550701ca5400660b40e094910b03200720040c42c4801178844c843d6014504401c0514003505016240903001c00011b503050404540e010250340020800c6101000303448a41103200342204261814110300115240d580d0400b00c0d04029116215801c0a5160310ec0000e0100c085d40a80c0c90314800540b1070034010040e4000c884c2c014030850032220910030010000410400349140500001c1030941061412145a13400410701400d120a4450348414000d10000300e4881441343e1000046100401d03040105585c0b411500e08e0555490000540203e0314010035580c1080c0c0054282e50b0780d05c9114042405840504400f50001c0c1c980910b01101011a0006020700071009043d100c0700400c030351069802c82c1d89804082c1c201e9200740020b0103030354 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 733669343 1250 733668093 733668101
    0x306040b0c160807031b0f0b0c040504090f02280b0c1c030504050c011106070f140a0908060912040e0a0204091a0a0b09101209021f1106070909 63
    0x80a106001d034a444000341c8000d5152a5a85086451550008a480926500c0f561840810342c118440c4c42c07112055444003e0702400c04000035201c5001203012600000740002150001c00c00a0402e1040f165031f400c20380b42d4403100380e00982c0180c9003410750040c190003001444031403120381681501007500706030302c03455907070000c00304000d8600c40d101c02554580d50192003003181059641e40031509113070903d0003c1c02e00300c4040d15030b8144240c03461910000003000c41c907282e029031180b40800004078180780071120700160320042c1d1000c2c1000600c503103425a0100000302075130b12240c100c5410340c40703c400b05070391001046590102c519090109203c0c081c0c500341601d400900340c02d00503013410f071110790032801c031103044542207080500800c0f08a12820300d00d102c58014858890701a040c8250703100860b8500e0000c62111041140080e00204401d001d07078841c050640d000f80c00c00020b09411416604c8030400b2000e000085522199840c0c590000018182d1181d0860b07990070800340e00c3c0c1040100a4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 733670593 1250 733669343 733669351
    0x411030702030a030e010e07180e010911010503091f020c06011a070b040317180c01020c011b1505070207060809011b0e040207050f01022508180d0803010603050f070c020306040b 78
    0x21b5502c2e0040d80100d00c8081000d003024000092000100444510641d4115881e10103800c11507418400c4500201b040c9901003028a1800c0c2440b80d543d98540c0d001508041354692030345103003046215100c2602c282035000d040100a280100e40e0f590341c80740d90b451b556410002c100044081c0c100540800603542d0b184c071390b80252080c2006c0d2130f07100ca081c0c98a0724070b0b5803c44001d5a0354004200034a1107032400c21034903179104020b0020309001c0002100003840301d45110b4405145941c10302d5004100000c48241c030240741d45400c030400007400c0030000291205440d04c11800011445808034050744818465510504001c59407100c0b81c0c089100c059414102842d185da6000780e00b40141e4022503400c0c4440801205003800059454400c2400c2d620140b80200310100356840721300d030441c005000ca004030340c149a031207200210104074a40c0001c0590740c0400d001080701c840030000094560301604614001c0b0032064100d40590390314171049400f4a50481c01960540c402c00c0441d012544103400f5a406c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 733671843 1250 733670593 733670621
    0x40f210204020a1403070203070c140a0e0723070209010f0b03070e18040b0718080c090603011b0305072a030e3601171b0a0306090305090411030702030a03 68
    0x1a4129518040054001b00d41a10240e04009600c404008803940403c001e0f2021850688000c509100031a80c03a9405004105070800030340041000e46000e41d072418a607070020120003c801c00714814501c40c6800024040f40140040000481c5940c040c0030003a0a071085040c149046a441081c101c46480707000424640021908000584500141030710b030784183d0044241c10028107000c0e10041664007408507018121403042024040d060ac0801c0740703d45044100c803200401d484440000f03005114a0254011140f86040390504140e01030b00b0441c822181c64551009240d403003d000080f194003000f12041000d0304064000000340101c4414a800340f0182181484440d001ca000481c15580194810109032845a400b10450000a0303175015001c500e42c004a601e820140c0300703a07111089010160310403801c41004407503440c1d40421100847d0051803e0040305814200034000b903000004460099045c52022100100b920085034000c580c16801185001c41c4080114000d00302c0390388080c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 733673093 1250 733671843 733671857
    0x80304080a0809130e010c11030f0a0c2909060a1503120c0605010b04032a210c241d1504080706031b020c0607081b12040f210204020a 59
    0xc815002c070b2243e007101710962400015401800c02000d0400c0e04d0a03054204c40d0341c01088400c48009820080c0c40c855002404c0c07040010b039040c9000108200f00440c20039601c000d0a03940031040800c2c07004a4003950982084d1005901e50340d03400d01c203a441c143c2d54103004000c0c04004200061043c140951400204e207002340400e84181e8414040d81d03000c1c1d20150307464502003402d00c240f100e49030b1001c003860720001d03d014081c4211074044a1a400510507600e00c410300c02500641b070a0220003500038140e10000207490707142c460356281004944a80d0400d103a48409800c261024058041e07001c44845e801884a50320801f101000074501324214400b65002003030000141c2101c04002e4040503024540340840c0c0c09404100c0d210035201c03102b5a1604540c440008060541c440004440c603590704641402c1d6201c8601090905c10740344a041d11030030307100d0f104101d81c0e4806904041c1003552544541c2080580d512003c09501c804084c0300d9984207004074510000601d096030052401d2041420054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 733674343 1250 733673093 733673119
    0x90a020d080919031a04080c06071829090409080c030318031e090a031208012301050d0f0605030d0c050c04110d0c030605030703050313080304080a0809 67
    0x600c05030045104542001022804070700074034090442401c00f442c50201c10a43c54910344842c0440381030902060703114504c0344d010034148504e030802c507401c1900c4102100c4960031b119000501d0095086d01c00d8908030320409011443c810700402880c005120b2003072002d00000c480c00b07045400d900034414182d03c075036580c00400000b503a2002030085020580041c54980c40d01c051005403907800420800d45940040007206c01c096500304850b003003a004000c3c0540c940221901160a010440d0800303000300031140407003680036600554190607510085104011444c0820001034050200d040e2640070840034040300c210706a45a120b488507400214022803459900c0d004281420030703c5594400041c031910103e410304c0317800c10150040d040c00ba54100440005903403903a034540103541541c2c0066882e08400c0e41e4651082d006900a40170040982d0901a524500907540c1c0c2e01803001014040c8480900045543c404015039040300d18001c0a0100c3c040540e4034840799900071401564001000c90b100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 733675593 1250 733674343 733674349
    0x31710080f0705040606020a050a030807030b09090c0f031b09130c081b06030106080c0c070f06050a020c0415030f0c1802070b0603010b0a05040f020712020a0b010602160608090a02 79
    0x18450a25200020b0801c0702d00700b20034401560590381006080d58011582d03003002604c0003c1d030401803505480e001e14943c544c660308501524801d074142c1e501240c0b24003400248a4046103e5420401c22241514007400080c2415110518490b0b400c680405510080301ca41c01c00103d01036000318101081407507004595102e4681c051700d5003000005074088400c058041c1d00002c8501c50212003202c10600310361418400906042e0010011010464042171102c4100d80030040180904008002668031036110000100150080c80404e40107110342d51a4828604181c480e2005002d240b4030307011122030460719000c2e010f019500c402c9402d0424850002500f0400c2d445583c2c500341841005a501c1c48942050340b50070301c020304107a101c1c0c0d240010b05100c41e517680c60314a0850f80305440104002036448250703170003401aa03402812180c1504685100c42e9030110b0502c00c007a1185501c0c881598139a00100d0b41d0b80080110710306008101042800100c0c091020346601415050840704c500d1007075408 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 733676843 1250 733675593 733675603
    0x10c1707030b030c1315060801080613020103020c060c13091404111212030109050106030213090f0f0207060b1203031b180d05010c030513172113031b03171008 70
    0x17200c0010303903901050050340c081142c0080082c030a40c40c010000b541004180d946600d400b070f01c9504040301104200045900079019596081682420b03a1000d241c10300940101c4c1e4000b044c003c0307400f4109000400c200109201d121102d590409021820341c1d640ea03035804420001103003181d44070024610500000c03400300604908003100301c507d95125450b003d20343c07040d1001078001c0014940180048607920f803140c0c002d142240c41409001c2074242c402420704000302020307800c5000d07003800028031405104440c0c002a01e0013205035028940c00411458907502d030301054411482c0d644548418501c15091500a4002082e04201100b681c400300c400144031210794070811100e80c2d44810410602030b40502c0780d958400c40003404d4607c40b00131959800700e62126000e500003c0140820440d82c2c40c140e1032030340f011074000d03901020034030300708076101480c122070841e02100000d40440300c0341c12891038070308c050a045038113482e10680032030310398503400340450001d10001c01c00560010001c0c1041003000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 733678093 1250 733676843 733676869
    0x319021915030e060a0b010806190b0c0601050a0509010b0417010b100215010e01150810051c1b21060f0510031407260c040c050a02010c1707030b030c 66
    0x41c00912102c90a1400e4241a4021700d03036400c00d840c0c0005030346d00d070340c0103a80c0f140d000318200d80035a90b01c0d0246400c0c0002c045542c10411f0318500c08601291050400900181039807030440e0121105030350342c000c00c817410301c09005044804038248030400040d1150011101c41c00900800070910304210b02c0410740307007150700e90f0120041c0d01014400d091035402d4606603000d091041030351300c01c0358100360340701d19100109413a0310100004440004d01c90b003c001403e2001e807400a000c54550a007407034000034003001560055410405118103c1e0241d500000d92208032104014041c20b40c2107004455400030300d141d00107480454849841c0f1224500d28480c5074400c40c0b10300e40d40290681035040c26000341415000740481507100b140c0c1809400c0c00000410700c003c03e10720700c6042c5c003040c41c59240e09003000c8421180d04141020400700d0405d801c90050030700345210f40e00800024000c9413003241c642030001c01c80e100c50100c14020900e4144260040321107684041d0858104800e99400b00f660003000b16 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 733679343 1250 733678093 733678097
    0x8010e032a0307080909060415121505040f020a0609050108011202120d03061809230703050a20010203031e1f0e040201030b06030f0a180209160e0319021915 69
    0x41c0402040c540390900070341020701908c0c10002c9142500b1540600d41680c0684404994101070304802c11000c4034101c40001c404d082c0500c11806c143c0b1f042ea1031440001c10491081030502c10100c4c2c1e40b403203006d004048840582d10f9051503442e00e26180006541070034243e802c000100400c014940003003107100c8148038103940c00203d06140c251144a80c044003242c40105c06e04100120001c00d208000c40003140c3c0502c428049449001c0c4816071800700310350310084c05809085064024052040a5000e081811410405102c040319004984074132049444032403d2400300140880f20f6901c10f02142e004a9095030f54248050403011911015490b510190004103000104802c55a050141514501043d10f5090560900004408103104010501c00d00b8581d00c1c0784041c403c104644010144c541c024007a5000e50030110035070340c03104940c1520100440c0c2d03c0400e040190500259600344100c0116140810303002e07942c20003a044240d038100b8075041c880300101080120820901042114040d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 733680593 1250 733679343 733679347
    0x50d1a070c05010606090317160f06050709050a031214040503010f06150f050412080415020d030518030a030b0301062105010b151206040e0f0c030708010e032a030708 73
    0x1030b25006007542c1da6034105004000342c10500b040060480e030304d0400704805098045465080c02e0108051030005048060b00000a1020240c103004460348020b000d00d1456860300038043d1588148641c1c41550300c4020701c54121400c104200522464551425a0503a07025600d0150340350006401e4504a0b406051401d540d81c604111000b007000c5600c41012290a060580d0411208060a00d00462065140b2002e0344200b0720100300300c03181100e01074030318684c04400c3d050306107400942d542210b864603c0464030b040e0114407504460034581602c0303001c00d001113241c5004000d0407000b4225464466806640718500491101c00340750805028076019000006454a1824041d00750382d11890400d0142003180c0020502c03c1e1303d801218030b5040c1e9046500241c0c0c8400001c43c005110020900b00d60303004003421002030300c10109041500100480464540b1030311140301d5402c07079511129400c080d07482003129150007a00e43c000c80581c10030f401d42081090340e9801805056601100c2c00319460480 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 733681843 1250 733680593 733680617
    0x10050a08070f080f030f0d15090501080d020a051c0c080a031e05091e1608010c0306170a0209220303020d0e0f06060915060705060601021213050d1a07 66
    0xb19140d04004001220090509100c020080d81e142d22424140f14090000043c080c050100030740c000500b8080c8850100300c2407951502c0f000000d000c203004040d0389009090484c00c00300d10004600c00c4c1550080081c02c28914402d96a0307800f03034115a03c0005002280501c0c4010600e41740107001100c109440115510400b42c86200d40b400d42c200d40c40c40003034a00010b00c14901c1000800740d034001120340d22604800390a000a61038480702c68405508941c00c3d880201e285007040d0010418980f1704c1c0c400b8840bc030745036140b007240d21940b9008122a64031040900c005840d20200c4160480c111132091410030740441050007000c2c551060981c0442d40000350302c42450064030907200c3d03400850005c0e0007034440408101e910740f00b014080c240f0032101070000c14820070100b1000c0316042d100404840e6a81880d02e4007a0b00c7e628215019030140c0511454003c080d0f00090456001c00c40303c0318450310680c100703000c00c01c60340300b90b0300300340c40e1340203200c9142c020504002d0a40307014504640300c80011001d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 733683093 1250 733681843 733681859
    0x18090203182a010804030c0303051509070c051c0e0d060e250f1d0c0c010204060206060a0b090d06021608040305012c1902030a051903080f1b0310050a0807 68
    0x82c0b0125180d04000d014410403001c00c0e0300c0315401d42900e603d8a070104254540c44002d2401c00c1301c030134002c0d6004a40380c0510111680005801070f4440c4158140d42118071f08041c801080003400e15240040740c08240d43d00100d28102ca094806036100c0c040000b00f2071a41108940b80024600b1310010400220050b80030307144854038844010440d40c40803619407070900c96000e201010036540e080e0b500889002046160032240280c0324a5940c0c0f900031900d61355034a80096413140203548450089502801c00720344400c80508446401c04058462940c0f150295212402940040c485030031001c036a20302c810001e8a044000d000031400345002040c0c031103014000c6010062801c80785904a0070020030224035190200349200715000c10304d980521144680040b0341800900d001c01000c502a000070490100030049402c810940a5580e10301145e07a848900d0700d1001064031705828001801c0340c0030645441490086520844d01503451114039030390000724140d001c40da0052642c58200303650600c0000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 733684343 1250 733683093 733683163
    0x30908070b090f0118080613030e090702031b100218040f0c0207052202040b0c070b0906040509070c0b0901020a0f05210601020f030d1b1809020318 65
    0x1aa210852405110800041c480f82500d0038542c1030000c00d41402d0013690201441d04010034644040e035145240c0554a036083c500300395402c9001c1824084040b0f014101403010714842c0310140c00451404000d1007580c452404544200c1d14244500880a601602180040e040f0380c10f00c44190f0701104466002c210507201c00818202d1072138644043c96a086a0014981b011544180c420390450141d440080342c2240e62400040e050600006000a0003543c4100800f00381c7e40c0642519a0141c41e649400c08500c01d407064150b00003010f200c103000c00d1070103c2680d0b4108450703092100884100e40d840710500071085910400c542d5001c1090400c4030740003101c82026101c0d41c030b406c80c07800b0881034180b60121000c0b50000e001c08101ea0015099034000c01903048ad84400c94200c0ea00e41d035100c0c41d0003029001c0315409d003102210000d503080380b0340e01a4180118800003450b803003000301d0402d0f400304029000100640e6010b4054034000341e00b0482440f8070860050315050210721040d1560101c0e0002c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 733685593 1250 733684343 733684349
    0x307021c030e040509010212040c05011b170f0c010f06140114160807080403050c0a0b121f050607050105010519080a1101260604050a0b030705190801020703090807 72
    0x14a450503580040d0340444500c8028004a500082c2c1d51190510940240030708080050341c00e166009100134030009200703000441c5c809a031034000b15800c0316640940203446c420014840703603034600d2094003a4000304c09044103505000f003060814020b4150305003507812200d0b132404c0807541c800050001d4074401b0440355000c2806c2c03c04c500740c0d02642c8024800c074801d000129080c81d0542c0c444c03100f045412811070b820a070300028525141d80d100d0800d40d45805c69050740c2e0b4071500c4032880000e1451030b9030301581d001204003040070b4496035410180c803810010540000d24082406900410b440d034134400900045400361000180a60400c030030710440100840d00d06003a05810700041003d038800145403c50140d10503490700748410a02c005898440c5145001265000c034400d00d1130212007a044910720580b0100d80c01d004a071204e40302841120140740030950141c10441d0180139508081c0c090032540d41a08603000c4005030b85003021822600a800b04400042514504001c030300d000708440006 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 733686843 1250 733685593 733685629
    0x30806010302090a0b030a06030b270a0807030f020c130204050901050307030206090d140a0b1501230c031201151815110a020a080123040f030c14010608030702 70
    0x14050f10000042c0d00c2000911070400503444c000001180407100350003482c01554016100250b41c1406103152450240554401c5840c40b82c0301c1d040340c620200020320440c000c6c1c000d4811807070507029450890b02041814003002c294404c6100100300390300c41e558a01d9120020260061721035040500f0400c07824010b0f071126100f030b417100500740050307510b6100712000c51034104d40d54401000300e840c100869030510201b10712580a550703848420f204c2085220b61080c00309070148048440304600556504070b01003508200250048454070b030001d041e000a00c2c03c03e180c14122400c00b03142e895561203281d8240c101005c0d000103d49504811030f0458403e440342d03205840d8101c8060f052444001d01e12150301441c07020010140240c00c079000c000d20907418480c0e0040c25030a5019140c10f15a4003800519841a5981004500303412801d1052a0b500303000b15885118501003031840d85003201c2d1250054000e5420400a4400680380301c1c003413003440000c0214001031900d840960042040700c0854240c4068 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 733688093 1250 733686843 733686847
    0x1003020a030b03060103211e090f0b0310180b0301020c0c0916080a0510030b130c0b0403020d0f0309330504061e03020913051b072409150207030806010302 68
    0x1404004248218075140c0840e54100c501054120785a06444c009400c99101403820b00300c4290313000f444c06d0240d03010120003030300ac0da585440442d40c1c1c0c80308542201d45400142800d100d2384080d940303120340c00d841b01103000c500c004240300024220780c0505882c81841d40000007ca00a04121202a500c480c04681203140300b110800003401d282001442192401da0b2603000488104685e1254406950009002206407900c1506480b0110400c0310946400f602908001100407280d0200c030113480d0f0141c4440c441e070807142d0324102034038032042003142401182c075000700b551a100a500d0459800b075144400000b2820180114200000150307001003100800080c8945500720540b0944075040740081360401c00000700071030013800b9100060317504c0302c84440b802c90180c4042e04409d004a02944031281103046030b0005603864842d0982c01803840f11040da9102c0118981001a9510301c008140441c04000c1950f50105500c1c001d80441c0c1800d0303000c503409041c5030b806052282c0c0404282030841c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 733689343 1250 733688093 733688099
    0x80604050c092a040f0303050c01111903180b0c0304030f021912090b2b050103032304031205030406050604050103032001020c01091101020f1b0913021003020a030b030601 75
    0x410b150310802140f021841c02105454a000b0034104840040840c1005603102a4a0f40f400802d1544020003401c003e6003014100c484d1754050314100c1d0403001803401d04c21400320000c00c4c02d40140c035a03c0940d080d900b0343e40c4040b0001c62072a8081c14801d00503264800c0e80c80c5044c1c580500084c0a116144045522001c00001501d0031285e48881e92504a00e0403160315245d40b008039203403c042e802245010b500412116003103101d010300385411a1044a9030020301545c600080100e90703091001800140003c2d08102803100b00101c48c1c0350000001c01851301c0d1603260344540000041d0303801d0f12030018070000200b200740280d600c106a0024070460301401071794950788009052000c0c070010803401c0200741014418000c1e095040b50420055131000348503420040c1410080c4c100f8004059015010306034062003c0b800c017080e040c0c0e164070740d50600c9507050000000c0c065481c3c0001c0c0100d01c4d86140d414040d000d6500d81c086a904c00c1007a40c0d0160b680c10a0b004011b00307460b00d1120260107130f44400014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 733690593 1250 733689343 733689361
    0x170c030106030b030319031e0e211603020d0306080c090c031003050105130b250e01030204180b0a2115090c09050a050c0a0e011206050604080604050c09 67
    0x480c1107505a260103d403e44070304000034114070898101c61070070420295400103058040e049041c884940803056814100388281d201c064840d11070000c01c50b60019101d001d800c02c1c0e04030044411043d42c0344c546040001450090308248240f80f401d401681c012035102c03c00c1035040c010400502600800307045010010000b06c2c0c2800b030090f0101d1070f620800b000140e00c018044400d00003c41d08a00203100307505010511480705540000c1c161228128540000c00c41c42007071041c529140b02d0094081d0080c2080035045819410304074409040540800c00008d054641c9002c2000807401140002510f80121040245450305680000c1d0b0103011540740078900b030383c400007070800150403a0016045040181d010380080c10050b600809510060202040d5200d19501031031062433a10f104001c02d80302d0fa440d003089409400510000078498070441c000030351041494614003806408081003054841000403c0c1ea04507410003055640488100000d00000b0061410320380030545200e1100d0a04a541d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 733691843 1250 733690593 733690597
    0x30f0304081902060a1d040c1d01030e0601032a08030a030f05060105040501081e16020706020c060d0e010b0301050115030b0402030c16080d020a080708060109060906031e020705030406170c 83
    0x10001440380f209100c1c0086e44082c50600540d8800400400007410328150240c000802151401c80355040015490f80a50203032284400c0a0342403070003050305a185070f565001105604001d200008403002c11098036007103940c044000707446010b0145841e45c0300c0c3e031401030071a101100d040103500d0404d1f0502000d40d82127400c9409882080c0307003500d49541e030982040f807807002251035a01040040300070403012030303108540d00042d0744c00761303081c0c8402c00d40e80c0c88101d91f01c5c1c800d01c0c0f455038026000c0242c59070841055021a600b0030321840045410740004001a0844000341e12100366500680306010f01240c3c140b1030b1101072602214214214180000403000c0703800f60115507a0302140380b900b03807000c1c0320804040d61100c0c4c4090a040d503840002c1c90b8002c046003001d8039140040f84c400b0011422a60040d003050054401c2951000519490000100c000e0803440803001c15404424a18840320a0140018100705000f08001d5503100d242c04030003807402d0030030041c008149281000f880844886e00e81 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 733693093 1250 733691843 733691857
    0x3030906020f1b120703020307080c0117070f0c140d1101150e15060d060f031104021c2d021201050a030314070309090906051515120403020a02030f030408190206 71
    0x213810800d4111041264039004103600065414480c0701d10004d03903410001205502c0e90703803c0c2da40010010010390610342e03c2d030043d250540458003070300d08444118032860380400403a016220600c4001106103a049c00d0407a0403201d480000c1804541e51034424003401040e00074800340403404130b4107240000340802c00c10054443c0f8180d03124a40c040449640b01c030151b482c0401c0d030560030000159500202a001c86d05480104d40c0d8010f01012043c20349058420b075014230a00d400c00403c041c2e288a510802421500341c42660500da810904041095200080c0c9900d1303520000140e03034042a92150140000580c03007140304840d681020300010f944100215521407900c515291150300c0c44c50196103140716508138140d12071800c01c11205102c1c040e00004d004000f003080c4400300d6a40070b800c1c4484900030074403c0c001c803202040420490340d17216041d40c0d4071078080e1040d100c0040040d400682009180c4900f030000798400b1509100c40c07501403101c50029820300f5160784941340701d81c0c0411001d000e291 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 733694343 1250 733693093 733693099
    0x601050a020a320102070201090501110303060405040206040825090e0d030f020405060c011d1612020303040308030403050c0c01020705150a120c0207140d050c12010902090103030906020f1b 83
    0xb602814900c00b1190b4245208540c3d503030b40b5214455000d00142c002e40000c0e00580c005188071200007625409100c0b00d5541030114406540b071a6182401d0001804020340203d802ca80b0800001402c82401d0210781d600400d07001180e84502d1101c68402004000c1d908020380c2c071846c00c1130b42c041580b40001c40d0a40d4200074100400d41501b0701c4844002401203501c0160440c1d00020b01104011043d40101d100c884510506a14001c0d00441709a40f5001452009100c042c265000d1110207541508031180078401070480b031506889903120b10641c4c00c06c2d14110080b45000c114400411414010310346448402c1c801851441d2800002030b100d845d4411b00c0c5005000300041c3d0002044c840d61840d0a60b8005030814080c44c2d444440080d41c441c0b0b80e1040403448018019030302840e00e80080301140b8160404001e00d4a4012102000740208107000014215981c070118100144c03520500d040c000c0d80252200c041036072811101030f0506000044800c030300d0b00b0804c1c0081c0da4801c2414881034a150036 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 733695593 1250 733694343 733694363
    0x2610230321090a0b0a030c090f21171b03070201051603110d0f031104142205010e180d120e0313080c01110d0905220c020d080601050a020a 61
    0x4440740c21449548520340c3c0045000ca0003041455050006010000c80307554108546104450708844145031401401903481541100b04651aa01c58804a880c10040703803901403d6020b66401e94806904102c0d00f00e501d4010803040c0d492000f4050b099107140802020714603121039a80024014414860707550030000500ca10641890f101d00142c4112800d88400c84200110100d07001d8580c5403220441c500007820007603e1103582d503002082c0d034100e503101c0d8208611358901c041000a01c0d402c00c40301c10f0307a05448601c1000c85040030700440d80208072401000105050003244251901c10703004164005030b00410401c4a2203500c040c0c28100511001c10011303ca075005034210341544a18003901e024146a1503000c10048400b1038030188001f003d8803440c00403050451915190b140d030b908035501242403c00204264185a04506040e80905070b5900346a99500c0c041310440d030400d02070000590114006c83c040c1504a140a9041502402c1450800001d801c00035a6401180401440c007050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 733696843 1250 733695593 733695643
    0x2802010507060b0303120a0f1802041d070612060b0711040c2003180a0303080703110f040905060301060f18110c03070b09062526102303 60
    0x480d0f01c40c0d600c001006098a40e82d403010714016400d800291a10400390740b03000402c40c1034610b10f00c541400b9060300748841196407034540822008224444032000d2600121540155000085c4021000f40145031107108680024a07100021581982c102900b00d80d410030001d070103d600005102003140c4c003198003044100145004465032a9881542160042022030015101c00f012004d03010401041c1201c3c40040a1002040280100307840301078080b030301e040007142d442d41c030a070880c2c40404c00c04103500341340ca00e190446022661050303010b107861555540900c0178a1500b806090014101e10b40040c90704d0f814030300c840118920f60080005010b58580003c1c000020000c207680d000e101a00c103483d2542c4a904204d4411002120104214003910001600701445140c88a840010420f10000010100413096407220000150ba1140c0408424118002c0c40001211071244104041c0380c00110301d0098150891081c0b0b05208034034002c80c0400c8841524005800c0401101092540501605d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 733698093 1250 733696843 733696853
    0x4060905010b100c050118081903090f03030501080c031c0e01140c1f020f18030307020d03120b0411030703150b0a030c20070b0f0d05182802010507 65
    0x240d5103280940210041c954070288941001c40c074040c05018100a1003500007d034003020a0b4241940010000720091141010303108001207000c0d050542414001242c0c0320548810f912036840c06d500324002502c0c2c0b030050219580a01c02015400e00039001420425410039042c52200c6800141c2000c110001c03200c3381942c1c3c820704020031001140700e0410703900c0c0c510008e983d44800c1c805d112040e1040000b14020303c0301c1c1d168800ca8203404280781c015824006211041164007440c6100c040d8140310600030400960f5030f01240c084098400c0d21445020b440010650701558a9044040c0c03080e4640718141c441c140d05803040341e81c000700c50b241c005030901c140c2400c000c0d20000e580105141000c0840d80d240c1381d54159110090703d40058848a0700304208801280b4803260003142014260442902000103017010806491280e00300c1480303904140b200c0e540a13040321811103040c144281d90000714051140180002c1204200d00203142210160440704d03100501052a4001d0402100245074410306c6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 733699343 1250 733698093 733698101
    0x20f0717120409020d060b1305040203040c030501140609012c0604110a030c080606070f06050415090302011a04050903040e2a07110405130b04050724030e030306090406090501 77
    0x262500740590349690321071010b00001c1d004540003a0b4210b1400700080340d000ca00c00280c0f0b03031a0461140c0e000ea41414901071001a4101501c1265009200e0380080000b44084c0911008001c180a00d1403240ca014006c0240c40d60060380a03140220440700c2c1c0007100940641e548100c102880503400c0715032034020100c0d004110101000d0141c4002245e83c181c4550716803c8803814406c60f50b0358003d6070716400c041101d42e10030382d0401042d0146e00310803000001d40e40d400c200e81c094040d106107222050b88280c204180c45600c542140140d5590403420200e4038540604854040d06540c204405c0c0781c44400030717940f4400c50251002030b000d00700c00580050b500d841c0683c400c0f00da440032060007a04681c203109031a040004d0484201d5a0710071141c0c1c0380e04041c816144660a40c0e010003100c012540c46000e00d00c1d50190003681d69004114020a40c0c00b9800500c8030305440da0008071054400110740101100d541951a00c2260810820b014041c1c0e108841c044d0070a4000100090600d0345140941c010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 733700593 1250 733699343 733699363
    0x30402090a0b030c0f19060c0308070e220b040608161509030f08040503030d02090102010e0a0512180d03091703090d034508160b1b0105040b16020f0717 67
    0x3180c0f21b4030001c1401c0383c0c005e80c1411550702c83d4a0303029007034a400c40d0503100d1200741018103804c2140d43d008a5035105000a003000b02518141d000a08146a0ac1c080703019100203402441e8582c3c489003910321042e4480c215200240718910212595015051700140500150322016100a49071401001403020900844009041c0102103981e29015600d100d030281d0041041140075503e0422400340c2c01c0e001203090911660f20501401c0034200480c2040100d8001426410070100411410105601c1d0280f5100c00da0380203490711f540c4946441c5a820580c00d810141d45407540051010040a840d112488940b8a915040203000401c00400742c550120700030015a80344221070810f00109076070480500c034900000c1119002c920384030f81d4559646c010007100d40e004a100d810003085080009406007078041c100c4810003680d1021103104900b5994252020349009018009001918200c0343e03400c2608160b5001030403201c0c600281c8143c50310303014400d4541c400450034000c01030500900207a114 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 733701843 1250 733700593 733700629
    0xa0f02060310210201091d04081e0f040f06050f0403110105090616030f0201020414040e0109050706091e0806070807020106050307080f0106060503090d0c030210050c030402090a0b030c0f 82
    0x4043c40d1241e402035030110740d98140d011807080400031034520551101800315004803084009030340c440d40d40380440c0307034412450401c100c205034030031004032007141c0c00401165128903a4281c40e141000e211007250005c6500500506c80b04001051280040c44103440c126a0000000c50b90300014a0050b600c6204010042d584071100080543c1540c50321108807801c90b0085d540c4101024503140c05030300300d11070ba006031600d92503800305445a500d0a9000205032401d180e0020502020035580c0ea4a8080c41d5040384001c40c800c42c3c81072012407a90310030400034880c003240c40d91140d841d002003251290000350a6800300101040000c100d14002d412443c000c01c0301500712a00d15540312580354075480c150360600400d5003001000500180b18109803070180101a020f801d4cd03950001d001d442800308610200c1c19400f0309080c0e20001e801034400c1d82d108010003a0b0180d035034581441040554000246002030341440c0000d9800c1d162070028145051100a03603400014000c0c0070002040e90160581c001e00e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 733703093 1250 733701843 733701869
    0x90e0106030b130c05012604170c0f1204030f080706063605011410030e070608061002071809080c07060e0a080c0f100e120705030f0a0f02060310 64
    0x3449080c0819100ba5601030010f4141075074031800110341000c03d0300c1c0ca81c44140d00b9558071094001d12110456001840781146409c5114070b142100d4481c1c1041c440352440360000340c9034034003803003007482072180d02008084020714150940d6100403840d400b000c4083e00150740401c0440c208a81544407001030181c01d41c0000d0300586035101c483c0220701420ba117120003401c080d8990b0480d02c8601030b01d41a1021a07040c030196005010a200303160704a80101c404058582d20480442c07081400844041c00e490382c1e5001d054500001403240b08661010304804650140700108505403124880340c400c1600040040b400b4031403418030901e98012491035907001d010b010000200e640d0822190a503d1000b51070380c001241d6285a4183c4801c101e12205410060903500132109140500350038403001090f0612030440300780d0601158040c113280711240240d0b07000d05010b00c46407404104110801980c00d000305080c241079920112000b01d81c0c00000d00440c001702c00b04001940c00030914018080100c2288 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 733704343 1250 733703093 733703101
    0x102100509391c0204240608040210051e1c050901150e010b07020f0619020627071a040e0a2405061b2d060619090e0106030b 55
    0x540c1d0340b4400d0050036100001c50409400d03818000e000c2d403903c10306002a410a4075031a004e0001400645404a02c3e00901031981312803901c980b102d8101800055880801d246098814001c0030200080014188841840404200d00d4244001d10154142c0f41405442d200001a16210000d143c08104030a07401c001c100b160403001580101e443c1404219081240343c1d13629030700c4522803001c4c000c1c540c0015041080c0e0f005424508540b92203c03002a080515101ca0340404010b2811103200f0200160007034001c4c03000c420907034007208101c80d4488803e141500a8106641d54030000d512803020114050b00442d02c40000c0002600c00408494410201610309100c4500040a24004010000c502c2040e4014800b900c409a075040d04c0f00030702070302c3c40d294150b0f440034900d90314400803103c43d00c1003901402c1c0e080003054501600308135a01140310340c0f1000007800e60038000001c0196000d00054040d00d07d4911080907017908440c4005030002e8080000712805001d440c0c3d40e04040c00c20107146080c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 733705593 1250 733704343 733704403
    0x2030903010c080a06051203180a030b04050d0f05030121050a06060803070606080a031b06110c010f060801181506080115380903030c0a0c030b0112020102100509 71
    0x20503c44c002c03020040010649540c104128000b480c0140314003940140000a1684540780d406242880e0090030b0903202c560325503a400040030100d8045510b034000d8802c0c0c591071b981145501007135103c142861410f41d03041802a545000300c140103032107600180e102e26814801d090150324003403500030805110b0f4548640046560340c0c0510005c81e0080c1c50103100084640e40450741d2035010790b069517400354503013041039010100d044102e01134518a41d03645003050401c143c00000c14240e030307819002081807045104c000003203074403581c007801059042010741303600c00d8000c0b244460724a40c0803148020341d03054001440c008000311b4200c1807280d883c0a226041c00b5401e10840c9080703a869052025181c40304101080729070446141d40e4228400c0f41c1040c0a0040700b01000d4800040060110b0b400c0c0260322052134a04940c40000340e4092100720001e005100743c000002d4050300104a07a034000c1281540001d5842ca11004a0400e9654031400709400031014040c00302900d50030035044d107280a4140309 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 733706843 1250 733705593 733705607
    0x111e06030a0c08011509060302031909030914030a02030607031112130c060314041e0206030f0f09071a0901091508070e0f1507030c020603150f010309120f02030903010c 74
    0x284070b0106000d038000240d900984910801c10042c540e0700c2c56062403802c1c0d020b41c007079000a04107142004c11412a962240014070030110510300035554819030500d032180d420f2801c540e201c007241c0a5000107800e24096100050b6154014142c3d140005104e0b4028540b140a405244204403180e52145c041c0f100c86400403080521041c021500300401c00e40c0d80e0350036001c440003007409a0800c00003c00103400305e03888070002c552150b900b155403502050590300140050348125261000b041045c000e03c240386d80320004560340146140010b1078981d041410203090b415485400c510311010000d42c41d0166481006118001d01e03c084144c48165040320002d840342070b085030380c0703030004288504810803071400d00500c04080e1000b0300400544240c030f080401c6640d20446041c1c09111b2601070130f00041e226034004510031401340c00c44121000711081001111102900418101418032034242e01045601c6d0b000841100a4140407802d5121213009074294082d010a2036815407030822403420a6801940c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 733708093 1250 733706843 733706861
    0x402120d08060f010c21140d06080f0105070c060209030c04020403030203031509070903080304080f0f0408120711040504150e01020406110a030503070f1809090b060a03111e06030a 79
    0xa80c04260080400046a14188100380502090a10094144500d060b071b441b951503543e842c07405c4a0001c41801d140c0003650701c07080703455940d19581c240c20020f0100500100b050301c0da00034001d2015003032a42d0010030140c103004001d01020f50015032a00582e40c10403000940e00c1e4041d10654840740d82c2e0034041e441c1e820480b203111f4801c0c40540524410b19081c107030b00344204155110450075600f191215520790300028011940010100504c40c80c004106c0040c02408010518503992981040d030041d04010362214038015584040c0018000507003d00400c10700958140c6000405a5841c20844a0f440384a4103111300701d4901013200000e150103400600542c0c0041e120160303425640d0180f80c2c0d41e80b1404e032016000840c14800300e81d03d03d00c1a0702403c03030140d841c5820070b005a41c550711500d81c107490341e000418496035641d2010400840b4882142c1c00310089444800769441c58450784c400600070700c0102d11554070b03c0181c090401c0b18081004509901800403600e900d8489508401414540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 733709343 1250 733708093 733708099
    0xb030c070b01030f06201c0906110705120a021b060d06030c090b0108010b0a1808030d0c080703020702030c0f031218032802090c0d0915060803120f0402120d0806 71
    0x311070030454400c0d401b034403080c4080106036185050381205418044950456140da215611454000c2c007090560280713010508144150a548610a03d44180f40c9211090030701c440322014014148015000b241c20085010180c488518040301b14000500038402c191400e105280781c4000442400702d4599070809a4804aa08002a01058006580d018024800c0c030b43d00301c8040045000e11841002c7d51b140c06042150b5805155445000da1819508440050b040c0d00d540c580c010030a0380d9124a0305030b0050203a05045140c0002074010a0300d62510f410084d0090004116180d9076443c00c124407010600d15800268803000740007082ca003003042134101980b01c0c0c407a41c1d041901c041c03070580c034410403116802e44a840009950b42840000c0e940200001c2d1868828003018410144600600050354807c0310382c0311241170f50850940842d1069000540f5a03807040c840000c250600850701900190b110040c184141e84620001d0110042c0c0c0000703070054019442140314041d040234031386010300c0d421 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 733710593 1250 733709343 733709351
    0x1824020d020102090306131e080306100e01020309040c1806030e0d1b0f050304052101140615030903090d05070e010b0f0405062101121110090b030c070b01030f06 71
    0x100500701e003030380508600c60780d144c2c04c80d5022990050030042118103a5210391010104807000090243c03001074000b4055501a1001081186a180a000510400b0500d041c81e420309032015000079901c3c044c5d0488070b070065946480c500745050045400d107842c112000132140740e045d16079000a0180c0346034034028400340f190303c0f0780d040300d94000e0340c054201910582d941111030516441c1e000f0104d40d00441a5218001000b004c03031144c0f85c0540034201c816140342001403244260107800d0840b684258603040c201280018065290340e030603800b00000c0403400c080c589907210300c607116041d4400c4083d0300d544043c88040c1d202c104000031841104441c00442d0315105680d8a0045409a02c242440044044020801070240346000c8004d0200c3d20110300a80707000c0c0c03200058161811a00780c028545071261004010100b013040d11b101021b0340410355070f81e0101243c4030806010000ca0340074078035140380f0100004070702030b84400c2911007203508a000030000e9651390070040054503480c1415a0b0301420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 733711843 1250 733710593 733710613
    0xa02040509070848030307060501030506071d010c0204061508070f020304210321020405040c0e0f04110c0607030b0f0301020702180a0603060908040501170403080601182402 76
    0x3c1458031020451840c01c02c1403925200d01603141c0e15113960240c0c0440c3e03020000d5000381c80d1400c0020303081036071240d407000400e0350541c2089440c017080100007a041050314003005034124118841048446801e0800a10030b103030030300c005000b8103d2034100c0d403507480480d20b9144240c3c0c0e11080c10750040007282c558102c42c01501c84126101d103d240102030840e021802c950701c5410703c0c1d00d80020a0790082c5440704000201d08007003d0000304400d94961184d03008281403046103068882c440501c121800d203080d21501145c00b01388800e0154101f2440340da80c84514a4568491304100c1381003113800000d5070510703e000314001e0024558060401d0182c481c80700000300d41d040500c01c8402d4a0780042c042181c3d40c007413004040d10464000c09c00704146803944000800030b011801a1080d00744141c40203500d460030701c0d0005084c2c0640150720360381060b00303600f0301011030303042000d2a82180003807030710a41d101c5201d0098414400d1541c40542820110a485180451b4101d1003041c1c0c22a10703420f8820320a2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 733713093 1250 733711843 733711873
    0x60806010305120d0e030a03090311070509060409141e01060506040605070b0a0e12120703060506030a09060b100224010602100513080a1706060f030703020702030a020405090708 78
    0x602408014802d9100b5200c00c064400b0340000303002c1c1e40d000c00d0004a10039105040c101c0c21a001840d5540c00700361149084030406801c464a0b0b649a0b80040040c41000e01c0d04000450b9503c0c05000725010f15901c41840c8240304a81c0d62440844482070115622003000c4406122114170740f5200010075468541e001c00e8a140103011102140c009641c0e285c101851303030711100400c040142100c00555034a102540002400307000c00000c15018015079621420300e290b282c488110014003100401d80380840c2400107581700e00a40343c0060042d40e00180e60607051501d500188408409154000a160500104c15900194420303e540c03002d5407140814401000e0f5051401c1c0a000b40c01c0942c2015000444400041d4040c0d50700040f0785400891141d50741d2554619580520018000a0204000e00c10810041403602d604483d0940f644c80c5841500001d6105a00000d40440d00305600001c10b642959001c100007031400c3d400800c1000242013130314101d9564a4148144150350250840100c03c00c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 733714343 1250 733713093 733713103
    0x2a050105040617102c220b04080f0f270609040c020321010501020601080d080408070201030207021e210c1c21031a0a18200304060608 59
    0x40e589031101c00c0d0100030410400310880c002048080d48400d00000002c05d5400b055040406050440029a0b240c0c0502544600040000c100f004250050007549003480c550103003510603107030048440d1807552900e00e0280801d10540118103000300000c903c021080c40d800c801482440228229030b414080d0000100303030300e00d0780740000c554031140c01c5c0141340550519401017080da462500c103580c46c1110312140c810000b03070046101010507080c58014041075030104162405000f000008001007607181400522416004000130441a0701080d2075045902030703010346213042c1d4002c080c841c0300344007141a40070400d41820301ea071050f010903c4c0d914050380c040661560b10620b0300060041440001f00703001000c42105030444440712101c5440c0c1c0842c6100804903031450354601095602900d107400281690019400e0381c401d4a0032503c141c04a40c0da800d000340851b02c400100c22200c11543c41804010f2491020b607880803a421405107030201005002144514810402000810b4403003505566031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 733715593 1250 733714343 733714349
    0x140d0e150105042f04120515010819030e1203120603060a0207020a1202012c0310053615011e0501020a080d1b0c03121802010c0204092a05010504 64
    0x1011000605003844062048100c1301e0220703500456190a90724000324454410b1003105441c513403c00410064129203024140d401403e1600003451031440c00e817188502001c0c10b102c01030902c402c150701e040840d11503154900200c918101540d803146000400000840b070200e94441c400d0141c0000600b000c0030602c2660b44098000d0041c20b8598100440402004070040080c4d05000103c0400043e07842030039a01e00222a120302c0c0d040410210b40181440c00300800109041c82e0b06040c200301060120040401074002c10404007000c0c030302001c40b40094620311404481130f0f400b0391009400c414600b10201030480340b8401081003a82d000c4080da089010503805140c0c0160040c420340700215203524090020180302c50000a004c0320b1880b807440050070300568040105030f8156803c018941c00148030000303402e520000b80001c400d442d103040c0f1101d001030313002410b0000b20b00100d000d40d00c80380d00140311070390b03c6000b24001c54100025011103220001040c000e0202064011850f5449882030b5012 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 733716843 1250 733715593 733715621
    0x150503071413121703310305031f080706020c010e1522050406060e010f0c05121323120a0b04030302070203211b010608060106140d0e15010504 63
    0x501d9090900f80e90002d80c1e81c034410354440700b09415041d9041c404400550003112110a042d0b18140c88180580c2800300b2285860346040301d0040090119410108403a40300955808000c012840794084d003091600302c1d000704001c0c1c8105400840c5c403e80018240089040907226030b288001d8000821800f9442001ca9615028040c0000c81514541000990381c412a0700025603040f034482001c5421101035a01090014121400b54016942c00c00e150100c0300103d450400716000607a20380e96540c81c000d00d900030401c0030000760494010210200200a015030031484090705007142e160000d516820052184610350f1078485186001d070014210000c641e1000103c3c2050317455440c141d0080d04402401d907014000c2d8941080c4800700108800300e071441c03480c05242c8400c0c0322807440248403005144a28683e1411368140f04401c80042e40f01d04640c600e01d003070080300103804081c1400f40a58081100403a081c10a080e00464010640070400c6034801c1040c6032a1b03a0710000c0109564031741c254000307 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 733718093 1250 733716843 733716877
    0xf07050a06050c280c0e13140a02091602060c1809100b0c0a0606050d0f02092203091805070f0f0e0303040314061302060a030c091505030714 62
    0xd41c0c0e0051014080c841e01c0da100796003049000b8040b0850100c4503410451412103140f819900b0031114100440140800807100d07019840c00d210254403280e441c0130040c0c0b20903540501809180c808000c101c6280d0743c06130006a55081c041024501c0d600300111110150150070300060200025000f920581620300c182c0c5c91800501d0800d00161a1001d0f285c1507414602e20030101e01106003c00a19000c0b035040020500f40300c05090800448603150090ba21444d000038264011400d01401610000c0c0c0403100c012503074441500c9101c0009400903000802c0c001d40a4001c2410341120300c80341100c01060b000c42e6a050800c00e03a004685084640c0c4000c1707074207041d130b42641a120782e440c55920390903410403c40b184090030000c3d185402950048554104040301544030350800e21800341c00c50170045010142810fa50b00107502070041d000c11504140c0d5900307105080600c900900300003080c0d0300c00d0b03c40415501d104000d00c039a1046071828045060b01d40b0300c3c0b00c218415000c83c2d0321502d49680c081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 733719343 1250 733718093 733718099
    0x40b0f060d030806060d2a09230a030606080a0302060601020627010908030123030a030503010512010209151b07051c030302090604080c1903031205180f0f0f07050a 72
    0x28404950250100750803c105000c851040300a5100740801110070411104510310090b407c105101d42c2074a0407410003104400070030a5040540e5420304401c45250700d440007220140100700d040150b5070001d4075080c200000044c17180800708aa01041340a075098501359030300d08005a90f5040181c0d541e00c24501c0c0d100080c0321a07152407240c20b0010279800b001084551080c1c403102d0f03580c0c00a82282c0d2403502455039600c080c940307980b20032140040c190040c04140b592910007a003540814880c150003040d45001c90b0307603040401c5d41110b08404008290020f069401c85413080e113074128012401c01c12510312900c01c0c45940c00030382402100c800411045030340c0c0c6c0d14030480300c80040b481001c40506409000c81c4140c0e546400141010380140b200134141d60191604020700231002681c0c07104401c01075071051002c254846020078915950781408141034950030a5024420202212010341d0301444440000382000403450884030100c0c0c00440780d10b0b10b020000302c1d4481b00f2030310603694001040e00e020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 733720593 1250 733719343 733719347
    0x71203090609060c0806010906020609070509070909020705010b011413031106090a030b0406150e01090218060319050901060b0904090c050303070507030308011202130f0b060c0105040b0f060d03 85
    0x34420140c841c880c0411a81240c0da41d02c802d039020a00407101140e0510100905541d10520800003440d1a100401c2a81809a10307192070380001d0080a004000010024003114061404040100b98200003150f5440950400d61f0007800c2107010f5500141c4640c5a50801c50300401c1034442c495140d1110003020352469507a0324405010121003500000284820f01c105e0b50780f0605980114043c04a0340c00c1441c16203414030440b00386401404039082010300600000004079074603819203050300b40041c0d0f10203ca00e0070107070303298000051366072280000080202d002c900003c242e902080c0ac120501c5143c590554841c00e9400c1405030003550b4032305010101c1241791070340003401c4041c0a8000c4003034050712900400d00f15803003107009580b03550000d1400c10826074800c0d5040d0060002e0303605401c0c1e80e03c4e294000dd201c00c0041002a140d00e840b2044000404171a40c08500054401800e0f25520b0300b0350f40030349019050840b0145d42c40c00748880020710840b8070091803485107200074aa80e01c920815541 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 733721843 1250 733720593 733720601
    0x180d03120f0b062d191215061d09091b12010c020d08092d070e130b100605030c030c070f0b0114011403010918050d0905090705071203 59
    0x9090000b07032035003500325054441100612090748200588146143c070f12007950b5030082c00c0a040142c02c14104005010000f00e2160584c20211034648151501080c407980c00c003901ca801c80e201c0c0d00400841000030b07800e42055031010300031404441817030310848240401401d44012101c840080d0480509802290038544514642e400700070810307c007242c03030f4249950840b621605c034280076900481069a000c0c0d0402e01844e4440c01c8070005160800d18800d000b055016005100b254a40c0421081400f1210610500d0050990030683d15054600f0741300601c1007010521041d502c1c12580e2012588155030036002c0d40958200d0b8503a0b91554850b000038480aa00003400c40707088270b0080c420700d800100511001c1d00c916018000246065040000c0035015005444015041c49554203000b2040020b06007074078112598071800003441e040c419035042c3c00c00244c210043c414010284d8039112140c21410314002d54038260341800b40d680c1c40340405c0c1d81d80e00c40c004000d0000d060344040009290322030f400c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 733723093 1250 733721843 733721861
    0x80606060f1e03100b0304030e15090d0309060906140304080906040317040e0702010507021e1e060703050c0a0210090f2405060f06090906190605180d0312 68
    0x2008600c1c1c402044042c0005000c1c1d42c01c09603003400c2c00030501c484840074008480c041d1110251007455420159800b81203180c001907a00c2c0200c0303680101e40340354882c04082d10090a0003510181c071440e0540f500034080c0d20f55029040201d090704c3c5c000300340644184000384182c0b8024003001d01e141c440d51641800d6400920780c2e035500403403c010200001d020440140c40011600102e1074503507041c1100398814640061560007103a15244c100071443c4c0e40060b1411a010301440380000c0720502c901d1b02401c101684c00c0d845005800001008841c0c14001074051094a290f9420446500e074076240d1a001c2c4201048400182c0c4082041541c83c141c0b648800700c0c943c42030458944c0c1c001581d807000c60041c0c100c4443c1c404c04080410580e1000036600410f988080b080341e043c054400c5442c00107007280030324101c4074002e030841da000640c0e54454008101c1e49040002040c10300d1682c4e000000c002c0c0d400181c2504242032a8003000c122802c11000413a04a9890348460603480e026680c24001072090312 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 733724343 1250 733723093 733723117
    0x10c1b080f040e09070b03090a14010b15030907090e06161b050a0201021209011d0f0d0b100506030c04090228051210050d03110c03100c080702010608060606 69
    0x202507086000000380001c0c148040003020510f0241e14290501c21154450310300c2603010020001e02e000003260341416294403141b058801f5030010a030318010108180398076000f070050030501030741703e4080015600c1890004115001c4a85413089030046d500f8515106a0503030040c0f002c00c105450f8038a50b805042d030680b51101244101801030340320698040744c151190f40281c0984010b42d6814013042ca03a04080300703078843c0b81c40b50b031000023425a1150710030f54014404010f1072081c56074403101414540c0310018a0800c18480c50b0a0081c2e0100c0281d880410f80403601d1000074080c24804280c0380b2440ca403003911400e1610302982c0402030741c41104030044100c1c00e4042c44020b251401032a0960301c80c60f503500741c1c030f07a07454200d048032050000c2c181d08488000100c0030000e42c0e0b0b031454140c40595051816925080d00203a1031032810f0700203000c0a902d0300480d15928880b500700c0e80105428a2a543d03241425202c0d00c100340e08032403080c0074141403174111900042d0f00f401e00d80c00038404180d4078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 733725593 1250 733724343 733724347
    0x60507050c090f0406051006090501050a020c0d1a0f0c071101020a0c0b1e16060207030c2411031302041802192603030402010e06190801030311010c1b08 67
    0x40002e50740d54048400d910b25064901c10301060001c9445000d0b13000841e07044020070340341480c07400b8258004620034641000400200104164824810111b4205d000342400708109003c0c54501c449000070f0182c5110a018040060303c9040c0718140c003801071f04280e07000c500e01000358864040d401c0c40c500055041d1300c510a00c010000d500c01164000074030104840503255500719408076002c509840d6003580c03011051024086d0500c883d07084140a6a2103400141c0d2284c46240a9850f10b040800150883e810048412800c0c81d403204000160045060100142d94035450380c802e00740400e031450307520111b041501c6001410141e00c400a01d00c21207850307042612950b0300140301003006d0020707503004000d95402000700c060007032507102e05030004520b819882128504883d43d81d000003000a4100050b030f20302c0000316150720003110300c104a148000d1160a5440c0409002c84000b03100440010706924082c815015040c0310303420b5200c2480e6207a400003c0c41181d01e03610a10065800e80d800c03402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 733726843 1250 733725593 733725613
    0x406020f0f03090109030f03110318010b06040f0905010e041110030b1e0a0506041508070504050a0b07150506130b0301020c0304120b0106080c030610140a09091b0906050705 76
    0x7000146105100c01d01c0081000d40e40c40c0750041010b140300e2000c0c4140350070301c4181406c9454600640c1e40c4030b940f102c4c0443d46c042d107042000c0d025014426081303401650006001c1121058112204d090340c0ea03400c020701860b43e0700ca2610303084884c11a405010101c48054501c0c00c0d00e405258402d0100c864600403980295400000d1540350b2a03680b03a0340d03c6240035149000601305811200c0c02080304480c03507401d044c0303020700764240404500000d4003040040c1001404032401801581c010742409860707441c003552106c0003454917500404081d90746558a95909207002c82030300481e8803a4402030550110110704401d0306000d0304170307040101e60654080c00528400402000940020300400d9002403c03040d41d414201c0c0c440704103801c00001c00210301c04120901410004613500050192294441d01c0d50160007200c890310080300b41c419011000901c040016806541c40003034401d110001c1001d4210003114116611030102d05401261403880108103407402000a010140c0c010000e035480580 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 733728093 1250 733726843 733726867
    0xf09030623010b131202030607180b0703110105100513150e04062a02030702010f11010509010c020f011e0c1101020f040320210f010509100e150406020f 67
    0x1003d0b08000c965110100326803102e680042c00150040140c841060328040c00c90700803e4446500901034000e20030240c01502d604282080120700420070001101d0f00c2d92001d180007800c0e40d480e161501102c0d0b00f00801308803c3d18102007002c0403030300e00074005c0261006c0d01c0c81240c0940303615036014807450180100001c03d00303a42a40c440c483e52081c18001510307421042c00f40c110380c0c50103020000e40f81018921a4072240c00008403040c031602400c1a05840e11015000c465400c0a9030b00b148095080c0020300095641c150007401c00d08056070250b030f0f12003c200151500300e81003a4080342404045c03004c40c0040c05001d80c0081383c1c007401441c203207100c00c003010300e11401d9900c00781000c404071100040810a00c8818010000703443c2c280518007088448400006004100e2402450207884046400600b0304404100c0502003d00d0b140c020710003450602e2055480c0d05940703c10614650425186150444011840b03102c1c84a62565401081d140c41d183d410081d005646900d400304800c100328070240c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 733729343 1250 733728093 733728161
    0xc0213020f0706090506101217090616051207020102070e1506120402011d130b03010e0d031517070b070f0c080307020f0307060518041b02070807060f090306 69
    0x160080308089103030036031460700d01d291801c010100d6042401f440070511280c500c101c22007419a070003001314200386009501d06481441340141d0591302040024024010042d00095500b10704c0c000c0c5c4c1a2400154180c540d8840c0e885011360003401a00f00720710034443d000030b0b808003e400c20020000c0090014464001ca00154080b1a480e1822a850000c10046680c0103200e4101882901d0207601c2e6648207201040c0700c00b46030700b010060b25403034400c0c01c59180c81c25030000c1085c0c8040c1084414100b040c4801400400128003502da03141c4154902160b030084000000c00404008001021050f141c405da40680e138010000440e04840b1f44002207012079034000c0d03641d02815050004e503556080d248100b100410801c4249802500001d03c02c1140b42d400c4026200c1c0d84400b981c610360440c0b0081c1c001001001845900d1a031000b00c414a820130a5000501900796a601d00445851903108d5000f600d806149401900c0051440f02d424000200315070001c48018908513003c1c007210384480c8644500b5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 733730593 1250 733729343 733729357
    0x30d08040614190b060f07030e01030906060b0405130203060102070303110f030a09061b0c1e03020405090105010e0a0612030c02031e1b090c03071b08370c0213020f 72
    0x18002e00c200c290b001641a00c21155106400c540700341c90318002c120a0305941c05003074405028009e6803035008620b80d02039044411001e52000b07042041a880d00c60b0144d0703603005400b801340200d083c1c094602c1c5c010107074803ca03809011305800821400d40b455808460101d12000074001c01e0089a0b030002c1001000c1002d44000e0011b0348030340000c613003010001050100e40f06c0454500020704600d90b07000ca01d0180001d0180c4406041815a2107030b000c1d21664100790340d03400250001d1604081044221042d030265050340c2d00c2070217005454031540f4540040d128540034a10071510b8000800001a0203440621009407000c1d064600042c41c0b09a0401917440a102010b03040d00b00710300301035016410030007022002c00304907032408013410070a1800c0300c5030100406a40601003030b5001c440d9502d16000042401a51101d012075881c186e00c1c041e010070400380095503038400000340003044080c0c05011441401917182d65600c0140241c0c1d000c005160f8407800c100c510b05542007010154442c1140e00402007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 733731843 1250 733730593 733730611
    0x80703020c09060f130c2001020909070c12050304110402070f02090115050301050603060a030c0906180603051506010e10020f1203010501051c02040f060804050708030306030d08040614 81
    0x41c000c4030380900200300001030801d8030900d914540c1103032641d100e081c440c04400d643e80f030000f00d0502e05e4005941d000b0082d455000d01d01d00241082c0c41c1000150005e111074001a01c001c005034a4040341a1070003442e1780002002c45e0340038941010968400e07005540e2007030144051030202c0c00350030b0104049a006038000e0310503119200301c590a50030014581c90050880070143c20145001007001041400103010310f51003900004041019a0303168a902405980c10001002c9110307502c4400390000c007400e00c203404450115500c1c0041c0700303000c1d103c5c00c82140c2d000340141841603841011800c2d0040002e000ea418442c65065212441e260f90100d003900b000644c00a00507050681003103441d0104080509c840014200b00500c1566406025203c01c90a20844880c1503101d42d11844041c2c061a0400d0030101490700f000104180c2c0292918050350280c4261a121a02c1e00d412589a102c121640c84d015800809813000c01c602c100c2c0c803a6402401020002220002008090032812080d550440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 733733093 1250 733731843 733731853
    0x30b010905090c01050c0a030305060f041e0c0e01140d0e0619110403051e030c0303101403060c03011811040e060306180706080702030915041505030f0c0c030708070302 74
    0x1020b07242c1040805441c500034200b043c188075501105542e1400300f024000c042548550200b01d0a4032900c1c500030129000038030610a8a80fa620100160410280c2600070313103041450700c017800f41c000e05041845100681d10940135008007441900d4030b5219059840210783c1d19603240440e60b07414480f44d0b0081e800614003135804d00804804e90140d4a0000081400300030070441000080c1c4005100380c0f0504120720041008078036043d06500b140100030001409000000800c80c6404907441c00606441085041c5030480303182105040e90f443c0101d80034101a10200014403050310460440100600400c1c008200c030f8a2071a504589501b00d07178041441c222804003800a02d10b0148100703540a2146400c05030300090b40e488160303640358a885814203001d400c2001c00e000c0c0c1c1c420b0044410702900a0f1407a214880f01914110700c5911500c00e0300120032142c02c40003074081c4520304480c0143d8005030b03c50429240c050140d001a884001c10308541d110402202000032280300c05030000500a0300a80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 733734343 1250 733733093 733733101
    0x6130b0d0c080603030409091a09070e0106030218061c0e06040605160206070c080d18170c06060f0d0b100914011d180703150b0105160f020a030b010905 67
    0x10545100c848580d003845805010060f5640b400810f803001c035486101e01107804681400d04010300d520034003805413041c009008100407100d0014003482150600805903c00740c0c0e0b540c07011000c901685401c5241050002e00c416006d280050141940780c2041a0000c0650700700f081c00005c8582845843e2100d420080070001806035920401d9805150070310054622441468000d4490f1002011003003441600035888040c060413800392070541c940c120302040226080c451460601408200840300c3c0e0b80c5c1d001242c81c507c030246080d102c0004009000700785a03211b0004103c11846560181604094420920404130380d14440c41030043c1808400507030f4507401c14201500360340004a1052141c11030760700420030443c1c641044a411020340d00342c800d0300e4650312000300000b80c51040c3c184117807045890200034440361030521580003006880411041e44030500640b01400f0b204e43c01050055107078110008070360342224443c101407004080d46121030712580c60440008081e04540c1d0b10740e580e03200b04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 733735593 1250 733734343 733734367
    0x60f080105061903030513150503061002010e120912150907050d020907030504020d230735010204180b01120510170c030f01091a010f030b0606130b 65
    0x1164014a0039500c0c20700360499004815a80700b004c0c88000c003009000540c46070894480d40414000d440b02c10600104c0101460000342035803c2605c0e043c5c032a018020101520500501c91040a0380b07050001c0c1825001e0b2541140440d00004016034001505030504048000240210540384502c00034041550606a8507186001800d41113180501134510340f081c02f580d550100b05030f02c2000c62401080380c1d910b51002c00c1400510f03a10041c1560701070703000c5000000c1c004115200b2919054200c40e50540c0d0b800d85d0440d181c01c0003006508000048000c900210740440e081c040d4240d00d00c002514156851000c04087c0150742c0106120399910300d10704400f5a8800105920201d006006110600300640010f14102c80d51140c03560500c40b0044240428005019108403840014250344040c044204500d001e050312080c110b070920141200d50140842620415045e0ba034071903920032a007070455884000d8000003608081d44450709005601c1d142482a0b0104050002201186c0e00c030000c41c20701c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 733736843 1250 733735593 733735601
    0xe03011d0a0512130b0901030902091018020f030a0b0105120c1e032502010b1801140105030403170a0902090403091802041a070305091201020403020102071a07061d01060f0801 77
    0x385203000c800810118410441c0030302c1c0719061701c980f10402a0b85586a0300181c009017070b0800025085100202000380681d510111002140e0710400c22003205901502c40c501244540010140150014004a80005400d83c0500301e10714045c10310700c0c5400a90700b009885000c00712294a424100054840c1d41500c0b0122040c1c031048030f40b8800c03400c505003000010715103481804d080e4003001c1429441c5036011b10035048522035020140c2454101700c540c00c8500f1990034240201005089110752070021544a00b0843c1d110350f4042c0d680d080c8a0717483c10503c8903001c00c05085001016100c50807032016907202200d990003180b0989442c14060700d070a00411580d00610021303880144180010003401e0147e85c04031502194100036540d0b2900395280968041c040c02c8403407508000521300200701400d05500030010359000b6022180714a0b511002d0586550b4101c1c0d21365003600003031000700c0005650342c101a00120254007400c5a00c60308502c0a0700b124280d6000600012000004011303000c0d082c45 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 733738093 1250 733736843 733736863
    0x3803070e0a0c17130303110f04030204060527040510022107080c07140f010509160b0304170a030b131d150103150b0301021c0b090f06010e03011d0a05 66
    0x800215503400703802c1c103105a11000300000c1c3d8002c444412141051b04c42d50145400c0d0396618415030300e0b0008041440b0494209020480c000d07440d010021445107410515900d0719582d0140400240b803808040203111440500121254401c50305c20300d021020314000760001445840322020352800c403a0300312101010140100082c04280014004200c4102040322030303072900300f084206011b9280041e0342c54a040c030340214849518100a00003120404030358040890800484141c0032a20383c00d20412511040c0c80081c2108801a0b9204800d2450009010100e40d2810b00082e001060300c08030720a41a419804603605a40d44540c16040026510f811980d030341a030002c1c262a01c503030804104908040c0409000c080b0f62880313080d010981e41c0c00049901c0b801070020354482d4503001c0b00300100301231620b02d140c00900f0090040701a00f09502c0b10361260040608152032520b40704015900c211005501e160076540395000350311080045817050a080e503c40006004c031080d507080080c10600c03d44 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 733739343 1250 733738093 733738097
    0x50d060305191e0c0506070c0305060903191107050121060e09010e01090b07030506120a080a08010602160e0901060509011205071a03070e060903012c013803070e0a0c 73
    0x500ca000701e04c0c1042004141c800035180955034000394141080185000d0388010814400c0c41c0401460701c50110140482002e0a00f040803159440503060b500752070065000b00c000d50041c03100b040b03150710075401a0201003074801d42a00007008002048141d82d0a80c0100050030041c4061218110b403d22030030025208690080003501d10039951807201d500d004d4074000030152104045021651000c00e070900d400c5001040b1010b01d15035140882264104842032400301c2e0a1400010f000b600108a0b01c03000060030480d42c0320320b42007140244a4604c050f0450059660381c0c00d0110729502e442c0c0d0341c24040c1038211400018000c881c500307503151401030340001510036002c00f803503080d62685074140c03070701f00019007828168070074240d0100c0d1481c091220b4070b5501d903090510155624103100c60b1401808040c81c01c00540c2da0341a070302c213800e84003125000006415041005d58241c25843c0303032500c0010460035a082c50074240c1000a141c00e146030031980c80b000c80c0d00140441040036200e030f0700c807050b400c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 733740593 1250 733739343 733739393
    0x31a010302130e060a0e011d070908060f0702031c06090c020102120408070623090615030d080c090402070804081b0a0329010909050c0402030f010501050d06030519 72
    0x16005642101d55030f0701c5161000c24003900410f000e541d40070600b5000d0b20491082c501250f9454608000d40a46600610b891201c5040824600c038811a5890240c41002c1d0090040b909c48500d4044640c3d0010052800c502040c000c0184c03242c1441541c0341000d840c488082003107420140a403085914045e583d9055a20400042200c0000580060b50060304501300946443d480d04080e0702400184214001c140b09854034035040c0802c5900c550700815400702183c860303503940002070542c3d102080c1c0300b5034035a00040d1903004076849050425030111807051210f0810f405400401c0503a00310040c120380100340400e0520480b00b0030010707200c001e00c0751000c0840e01081c01000c0b41c04003015000180200000032400403415990b00840e6241c0078030003910407101d44e50340300340000900c84408200da4600988a07030403042e24150013540d001d210303c00450b0703e41d41d20745001903996500c40c00c1c244000940341d40c03000000c144140700c40c0c015682160450f5505000903e4240c1002c01c6c1d1158410110711b513 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 733741843 1250 733740593 733740607
    0x5040614030a02010f2a0b1305030306130902060309030c1207020f0424081b040902033d050a0b06120c0d02040f170d050c061909060c031a010302 64
    0x1c0091100c03449902800c01a88220114200300d07208100f040c0034001c503170044914001d1000c02448014845401000c1030725071900c4d400528a4411064034000e0081d5200b4001304000745001e00044148440b0880300040c168119400f0030443e400c00c03034a94070300b030b04003045400c8074007420301282640184010f0450710f010443c4d40060341082c550116140281d40c0c4910b00c03044000e440500040c203002082030f8407106a55020020f940b040d6034043c4520b49440f408804160f41850300400d4441035004015000161055940c442540c100a6940c1c0d0507005001201c0c5551010b5152140010050000440d8528010203e9000c0c1c0f00e520400c0d5019040070001d003440451209000e54110305200c540913940d49400e17101001070b014030f4020b4030342180600e000141c0070112203602c100094852060312840c0c100e0b018191164092100c0100b019007207a00094103508107584541c50040e510200003d81100380c0d01d401c000c07900703024043c10201c1e5031000e94114110032a000c601e01041e091074154500303d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 733743093 1250 733741843 733741849
    0x111070303140a05090d110114070c09020703051902060402010e0d0807151508030c011a031b060f07030305150901061b050c10021f05100e04110901060905040614 71
    0x40c50b100055a41000400e4041c0420300c1282181c061040c01012a0191034203810125134800404191a01007401103a600b11403424440640f03220369005102d40e0311483ca07000ca194040d6010300d50413000c01a0401c602203042c5c201010008600f0410f500810981c50644000341100703d015180d41c3c2f08a150385c481c040014030060031944216401840b250340c0303020312101d100107440c2c1070f0b0f8940440e0118001c081203480b000805040072100680081c0101c007444c3e02c40b13400c2d450200d0440c0c0c0d01504503103280354200c3c4ce0b2004040788054043c0c90646808010842642690060300080300000e40780e50502a03c2082d10030300481c500411102d900c8194034000c000390014009900405000f58074502c10b006105007072020b05250b03130000d050844c59000c1214000c7d19031540140e015007103c006020148000b60610a5501c0f03440c005030404900ca08160070416121401003040729582081402c011440c0c42e4452128020032054850b82001d6003800e0412003560026041030403061541c248040e1959 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 733744343 1250 733743093 733743107
    0x1504050d051c1505060a12060e13020622030c0302010f020d0210090c080303010602060711030f0313290603011d0712150c020307031e121a0a080a020111070303 70
    0x1151070403000410520343d800c0c018200019078000c03540614040f40c009091504642210054070035544200002c0b91510305400310402d0503074040410612495041006040c01401131812444400701040100882e001390b04070041d00c2d4000711560402c405042046503005002070b142606e0301e0000c1e122051256074025038079442c0400b112401519501c2041c01d101258000708050801c0350b0540b65250b84880000e03541d46030030354a00e000241c840c0001086a0800710684102c00105030040d403441d00c40c2c19468039186800f00d0180d484540a0208501a0702075424180c0c1003401c0d100040a1407902404040c02c5030703440320013441c941031100f141100340140440c41758191502e034003030118001c4241c100803841454041140200603e000d0100c500c050300000500b030014840d03a0b42c44100c481030910704103451801e20744a8082200341a00e404840c0942c0c00c50340c00f1941590105100c1480000011a0039095901060941e001203c0700c10035540c0c13000200000c03060000003450300350314680d0018260 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 733745593 1250 733744343 733744387
    0x102042c0c0d0e06090303012108040b09010905040c030c08060604030c0504180f201002060703090303021908040c0f05100e030a062a0f09060c02030f1504050d05 71
    0x20380700081400031070078180e100041010b107820488850345088008581d8990007070054004d23030141e4520f0255100954008001180c0d4003100c10703030030b0601d001203811154000064032414007a00c003101051948a9208203900c5a4240d900400e0100d40c070f0f400540080030240c915809000300f0003090011401c2c0e00b03001c2040f101c089d240003821755440800d0340b0210b801400001d00401c086074601042c0035450002c1c01400000d81106c12801c0d00340d00411002000014a00d40540c1160f030010760094003940c80142054024140507280180b001411040110622101d4001c912803000340401d01070f00540400c054810580c009662905043c0051705c642041c442074020003840000c0310b401601d0600141f0755031540410b092040c180000d80c00c01d0326004021030307403502c91a05011840e03014858059070050511340d850303082c07175941080c0341181c0140c42442c040e6058455007443c0f51b248441000109601c080102d002402410b141c903104c0d00b4000340c2c0281c5c03410000d0511a0b18005841d0f07072078017002 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 733746843 1250 733745593 733745611
    0x3020a410c1203040608060609010e010309150606030e011b020606101809020304020108060d0209060d171b0f0a0c14030f0f0c030f0a0b070309031704050102042c 71
    0x408611010186003030700589500d500700418031800e403103410000020340203603007444c0c82d403a403103035900401d0211a0085020b0580083c80d0108a030a2030350207030340800b41c13940c042c4503044c0d48025a801100d06556403540000b00084c0d840710380c501c18020030310071040c0380241441c503440589000d9030000e540b0390000c2c00051062003102000f9000c503004411404100e540030100120440d5540a204002c1d00101c8069012030f88840008003d0300d001250790000690080040e2410b8a40c001806218010010300716808288200e00b100ea551142e0090000b41c4d207120015182440140d19107810940701034484071881d484a2000f10000c3c01d10b1003c035040d44c0703151107040b01007426000040d1518800c904052030502600b28a0b04200ca8081050110590281d046500c20f1205001c0c10303544000c2200c000c0c190440c000041016244a60440b0300d295010b85011154021004820700740300c0b200307903000c031000e0707500242c2000705c400c0b007038100003070444646498a00304000110440060714000e01040c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 733748093 1250 733746843 733746953
    0xb0a03051b27040b060d050d031805030706060501021e0705010f030f09120e0f1f031b0e01020111030c0304020f062101141017061c03020a 61
    0x101030322880c08407003400c081200114040c0c8091007000d9642802640e007030b04c071040240001406030601c20041100340d0303400001482c0d90410b0090880c0102102c1c510804603400c01105c24020440400c05005058000c40001881500e00000607150007100104800c95141503d20310364284804214201184d10a0030a169800d60040c1c044009188500d10b460b28280f4100d00e9174244440e82001007601c404035202d0303000c075030300c00402c20250100002c50740c0d078407020002c1c2d0000103400480f00e400914641d81000f0031015038001d07803651030200d6041c19400250341641c0c0f101c455030b4240140c5d5605c030911280d0515509244009249a01c0b0061029000e00078142480e0f17260f880b0305040301e0103506140d009402c090403810244a86038420f100794260040200c040c11240d240542401a04541546032400365044841d103251984038000c0403c0ea205c940e2081582c00c0c082c080344590040c80c40382d0301400c210500c501e0a40c80780140c1c541c1113400d21400a00300403228281040a155480113004044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 733749343 1250 733748093 733748143
    0x22270c02030906030a0b04050a1811061204080d181e0c0305191a010b070b1306020a05210709050409080d09030906110607141b0a05100b0a0305 63
    0x107031961040040c1560000d20000801c0307105034180d413181a07032920486051113940c48243e020f500b40c0d00545c081c9030b40404002d5140b000104040a008200d0f10041d20301818009048240d02405000b102c0503901c01750002280c032181f0019200f8074074032040c00b0b940c052201134140c540380806d0020342c0c010f00e0004030000004091141405040e001594807600700c1e5070042440c2654480400010780407140714418032880420080c0315460941a00d10305402242000b05644a5000c0244003620307118044c1800c65251003c10b8440c001040b071100c079030312216510580c0500e110b0301c03120380b144072522202e404800d00c002d2980c084882c1048070b80c111400704803052941403240852281c0f5458000c802d2400340103201b010f0b00103880740211403468440480c583c00548100340c0702d0714111a200d001070900090201c40100510103001c0750450282e034241403c50402c000361074000381e41c0c002d0b00d26500102c0d48040c41442402041484801640c1000480340346948555645964081a0023422304055003a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 733750593 1250 733749343 733749347
    0x41e0f2301050907170703050c0904020111010207060207151e020a03180b06030105100b03040f030c0204050a0b0916020a0f0204091212050703020a050702010e0a090222270c 76
    0xe4141919810081100d41000143c0030740d22000ca200d040d0219000c8001680c500c1340c0400c0351021250010090440124290204480d200004108030306001030010803c1a5260034805000d0503440f50b0b00040c1d1303400d82410600404010034106803292410304040303128940b03911541c14020081090b0140c0c031440380d004240c0142002c050105440c803080a0280140144d0701da03494080c020641c000c0006890340044014403005500034420030140401c00720b800241c40e400e000050500a14101c54001c00c0380e4002425a907090342e40301c4031035460740b0200c01140350840342141c011504401c405017084a0900103901d41001e5400900003c0c0c50400d0701c0d042d915281c20901c2c1c200d52190418018440d0b031071f0050120310700c0408130280380385004002842c05019100701c2e442c80c1c4844e10340c2c03402c1168941c01194104a00e60349150481d15241d0000340c0d040300c43c00a8144809008413042c2c030ba11010a540741c00c54000c2e07004240700301c110403c0d03004010100c0e4007500d0307100c03500341c1c0171407100390321441 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 733751843 1250 733750593 733750643
    0x12080d0b120a0b061206090a030f031b020a060f0c0c0b0606040503120c010609050408030a021308120403030e03121c0e150601020d0216060e1c0605041e0f 68
    0x54003030706000c0c440724841004640ca50032840f545048035a407050b01a0150b01c02c1d0b0b0361108031401c0364168408004140840c0c021540510403510300e180210301e8044002c0606d8001c4590b1b1224009a4400c58a002c1080030600030145160b145000801c0503101c940c0004254503041c03800508030416002c040342e42600c07124101c6028000c00b80464800ca94024104221540680c16142c1c1c654a0708101103028429030240c40d0190382c00814035030641c0c5804e28403030000e50055114100082200c0270002d030055041c0003094a015680314007075140c43c0b4508024004484014002d4481d81042418160301110b01050b50800c1c0071050802c83c4961554082c44020104510465114030652280302d040ea0317542116507105035002c0e8240c4461400140d416a0340d05244c10140312105e640e03c07000d2007014460110503d0804e0b00034200301c0114003161480540c208180000d44a0980741d0003008140010303141e00f07904408001209a075040040e0320741d000c24200c1e1400040004c805000c0845114500c03c0d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 733753093 1250 733751843 733751869
    0x1b0c08031501020f011b1e0206010509090a02090405062e060525081315080c0c011d03030709080f0a0609060f021201060e0102030a09090905030f040608070912080d0b 73
    0x20800c4a4800d40310010f4141e86d07850003000550000040307102d0000c0c441c034156603646650010001c0780d00300400c01c514410300400d102010b02c03030f50300000b000d41d940c3c0c203c4a024034000c1d4043c103800c0c1080a03851a0380910713111816001000703802c00c0c80300c1942d010303000c4c0222407540c41c00944030721407400001007050700010141c0411a60980c45070a001e54440205107200110a40d035060700d41e5280c0c8400d10905d00b82814000ca00f948000944962615000b00100c0e8a1100002144400310524510240d01244203800d19031000c02002055600500c03400054000907004006000c0340720035969642521002c010304407503c0b0340c0f40c03008200303030781e0406114107140c20000c0d900c6208140b4504207102c024461840056072015202420754000f00446500141d19aa482c07811818024210094803c0702e07030031965480200503038040e422881c000f030300c0038005541d102031039410901e50040081c406600041c2307071004164000400101130780c00316180784a000d00301007031090624000440b000c6602c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 733754343 1250 733753093 733753123
    0x81503010212010f180501060e09041b03060b19030209010b0c010f0507030e070918110a240f0207060c14160602010b03120c03070b13020a06031b0c0803150102 70
    0x4000890060300d8001c3c0003081d10180000707100420717001403001041c2c680c280700f400040340041c1e542021604000190303940c098001c81c2c00c9481c040764000100104526075105035400c540d80c2e03071a880b8500d44410258840045541182d060b1420354001071054881881064000640064000c011840c290441d0444101c0c0f110104105e141010b00940580a01c81045045000d440c8002c50070401d14812000002c81d02a07049207031101903650041740342624100160b02c55500b402c002100c1038400c6a5124003a084140340b5003290700b4040c00b500381d210031803c1c00300f0364000c1c030030034440d0941c0941800d04140e0490307555555400e010340c04d281840e05070000d88052003100744002c140d41b6015089080541000d0b01141c80e0102014a60a072900038030380d181d0a0358000b04424408640c00140041c1c10070340c4507081031130150075940003841e44c0c0c020354420b40200380ca800580390300f041015400112140b1604100728511070079500c03000c40340b0001700798808075140200391b6030035a44200300384443c03a90301c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 733755593 1250 733754343 733754377
    0x21213050405011403010f1b0f03180c031a0103020d02270c1e090a090b0a0e0a09060506040207020a170f0f16050117073b0f040c0815030102 62
    0x1050060300240c40e50030594000c2d820b00c580094000c0c06407250710700c000b004408c0311084900002040b0350045042c0b0a00c0c04241e200d40e0540318062642240803642c034813589038000541c0c42d528180000803044140d014070741c0c40346801000580c860b06040000d0950403614810343c0d0b0401241000810300c1010000041c21400080201b1040244000c00407800302c86021003882c071142452404a01c1110080b0f41c0007400020200324810964022161302400108801180307511080c3d40c80d0440c600712807a0480c182c0b92540300003800610700c180380e0041408c0e1000d41c43d10130207801251510303825118075489a0710390902000f0307802c01801142c4240d0070b481c0544041c070408100c0284d82e8440b03d640400400c904050008071907000343c0c159808080b43d02038046540c0d030382c000d050750080711503618012540d1071000c2d11001c1000d10381c1d50600c0070030000c1c1c80c0820b908000701406600900034907003d0295185c0100c1e0864503801c192615480204880304a180d00c528201090183c0503101040c3e00070128 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 733756843 1250 733755593 733755599
    0x30609060c0e1c0b341e05120402030304090c02071d130803070c0c06080a140907053a11030303010b030c07020a270b1002121305040501 60
    0x21034026100c0207001eaa100034142c0103510401924074041c800010880c2d4030f960800000038203c00d010f5078405c840400040c3c484c1403042049410031032140941e44541500c4010300322468001c42c1044124200368040d54588011000103005031052080d19441d0003040000901190740c100103d40260039071000070f210008402034040c0d625140c1e400788204180602c440041c141074240c8645100c5d50754900700d0840070041e51a034072116130019140c401002103c201800204045540317420040c01039948010091810075041e204503062020030b00000d9440b50107200d41c1c51000210a01030b91800c0325200141c00f91003c03001e480d0b941c0b0001e02d45090141e8190696582108080a6215401481041e803201c915104142d1644030034026110407010034000b140c0c00b50b203a0301c003508080744090007100d4181e40b112909000110f1010008082050300309142c3c5080c04903010712032014a0965498a000c032044a01030f4490071101a4044051400b0400d20722116803100554000d04c8068420081561 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 733758093 1250 733756843 733756853
    0x5070617010b09060304150608070605181e1005040e010b0304030212030f0103120203130f180207020a0306020906070f06140609090c060306130e06012103051c06030609 74
    0x1003550600090205140c00010b9038480355811208400030060503246160351729524a050820320f03884015241c2e03660f070f5020400c00e10030030040b80549010b4448903241c280700c40c0c9144800c0903400c4600e00076000502e0794a601a58500c2611142804a80c5481c807010a1841104c1a01031680600c002400c0f503000000c581a00100640c0120300950070b50754014510065032110784410b90303804c2c0360740070201d004002040c0140140c1400000d40e2050300d280c1940f1080900c800d03251a00f01e410328000001007040806000090004999204101076007072131800c1e000685085e02e1031102800700c90300000d188516039a11011200000e9201945203d40146810142c00801c41d4845182c8191103071408600c8916040d41e4251040200c0001460040500c00501529410180001e07800107640c84a0007607421450140100301d8424000500480d031409401046989103142c0c02e051072200c01c40b0303142c00309511208a55510541601d4245000c1400103464000d003010350020b08520316040c18081040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 733759343 1250 733758093 733758107
    0x110c030403120f1d060d0e0604050f06010f06230702031f0c2c12030417150403021902030309060703020120040f0509040501090209010605070308010f062a050706 71
    0xd180e0f0783c2d00e902d0410505401d485000460011030b0710100621510031851900310010030348941e00001c042007298911000d5440e08605981c119910740100d105082000d900b04000c0d401032003030031030311840a4500306010700150386054500595050202c580c11144503c20211100c1950150840791203480389084028186c2102e0036903ca19070604003052880c0303205095051507880713040c4c1c0030b20740b45400948085040800c1d48440790041c1c1c404586615415041c00a800203080c0314211601600c2044a41420505055032000b88407140310103000201e980014402d00d802d515a005040030740b01d900000b865030280344c40403070307201400081140c00c055064021400c900110240b01106210b1420f80d4555070003140100d00754014540002c001c0c80c03412074030b1240c05c40c1c066000012014907039000303e00030314030903040036006c038000103418010554411213090040c00c0c032070001103141d420510f008110f0008604901c0f624203080c040345441d0700e041c403c07406906503c40105e6500300d40e40c5002400d10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 733760593 1250 733759343 733759373
    0x90c0d050a031707050406050c1614030613030203041a27090703060e07050f09030a06091a060108011505190320070b04140709020d050a0501060f0210110c030403 71
    0x5001c00c803c5182041c00900524010209511554109803c21800315419044401c4044540c0b04a001540150050124030742c0a0702841010a042c1d45502c0c00741854400050400420440440c01c40c401182d8040103840548a0f0f00e0013409194101084070038407801102028883d1a8104031002c0c0382245080d9400c2d02164240c6140183d0343d0791100c1503044501c944240c0c0401ea000b14002143c03207201d10001e09041d246581c2145c10b00c0250800b180c07030311400c5401102c8040d0394001400500c80802040c500841c1c1c0e1016501c6a450b044000812044061181c030b4508c0c3d50301c0740315116440c014425550070064403005151840308480c1c0040c040d2841b00940e500611543c800810003460b143e007260700080c0c002e01649500c5e2603d03a40c1282048014025a6650042c4080450403165500007480c03201d541481c003203418103100180c00308888060340110140141d10642c880074680100b003281f4a03c40007031001407803045800401040b8030400300406a58000010f0100c00c110580f01d041c003103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 733761843 1250 733760593 733760597
    0x12030a0209040b180f07050417010c141306051e13031202070f0b0c0106081501030b060607050a020f1c05060912030f04110a031a090d1d0603090c0d050a03 68
    0x1c40c43d140810702c140c00c3d0105029032442100743c00001e031034403e803190058000e90546821490180c0d40d030682d03400c4000c03178002d040b1165141c688100a081d44005c012003004c48210300300785000281110303140300c00e180c0d12603001440f00108032811352848117485c800c1c090582c402d409071703100a668801680100903001c00ca43c0810400c0034011010702c00500c9900384c80c03410303500c60b400d603080402194003a04804500101d46d900c441f808030b900b000501140c400c0100d2102100d040d54114600010300c020014002c2d40600800e1041c6808214000345008810350140e03002c074200095000461004203c80080c1041410403550b040100007000800c1d502c6496010240c03900322910702000103003480306071406007040000501145c0458580141c840310340070000c103e0081c081e0b81c1c2d40c80318020324403100800321841c151400c0108400e8284001651000103251a140a489840302c40722460328400d20355000c2c403408000603184140801c0110f030b0003140240b50046204051a110765115240e150880c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 733763093 1250 733761843 733761851
    0xc110406080606031b010512130f08130603090305030109050a1103090706120204081e07180b0414070f120b1c0c09180303050a0b0d0c080106060813080a0212030a020904 74
    0x102107a01c5c488a01e819441607480a2405040c8590000510000781c422010b00e4003000070740d00000d600c91b00d0194a903110307120894407101031102c2000740780c0080e806034041c03600b000e150000182c0d100b4110390540d030b0408800615a250060842d00905511400c81d080910000601a400c1c00006044040f1020382e51007803a05107100390450164000da10590b1071960160440c0c11131078086e06c0020345804412412102d52039070f40d580200343c10003201542ca00807036407014022440d0500d402200f51101d0000408490b5042c144401001d0381000c030304542c2003010400602d246800c080e00001c4600c030b00182004032008641a00103201400c181013220b182e802507400180208850142041c0d030707448032100600d01800c030b4500b0b170043d00c40100808440d80c0d80f070700902041d0f901c00c101030401d1070044241504903820021403a0848526030464024002400c0810a02c1d2400f010b450030450f078000000e030340318280c1800c140d14140d50100014800c9901208100080c884e607400381c0017044007214240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 733764343 1250 733763093 733763113
    0x906110d18080306040902030a06230721020c030706020403080a0801081603030f090905070e030714060403120323040c050f060a0f14120f100501020d0c11040608060603 74
    0x1c0724144403100189500402d1000814a20b425401b6102881c00a8280c0d2030b20b181941d5880c04443d0a04100b0104860b80d510303415110404801c0582d1100c40f6042407411818041400305400c200201501405900041c08103a40c1d80c09000f0b440c1195400401951516117a15001e0b1b50341e0040c0034132500140020000180010380007038913540000b10254810442411610101c0d5815800c0c0761040601450003c001111801441040d00c135032103940c1e40000c28a07020042500b09402d41d400b944000403c240110300d00d61b1100112000c80b50300250204c4034001c00c0c9420340c0030b003030004228403250303038040e44480c0e040d107414030034034070a62091508001450301d4100300a00c081c208017206400180038880000560b00600c8039200c8844142407680000074050400901a80401079516200510314203010030780e01e0781a041a008190704810444090030100000c0d0b83c2c040c003850040400250101c3d0100b440902034498410000192081c820340c1c1c2c8601e0201d81e1050b00790f070000d001e482005100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 733765593 1250 733764343 733764371
    0x711030c0105190e0a05090a090203010f06052b0c08211801081003050d050a11190209100504050a4a1507020c0130020d0906110d 57
    0x75214807900c64050302e10f000655000300c0e00c0c20501c03490150003c11050380856a5940d0301032462090b281e0640100c0c0800e1184103260a560494668044890408105200300d5880507130801c41031076014080d01e2110400308000c013403800700c0030010342600d00a020200d11440046543d848102c03041141a1407000c00e9146590103100317018146002c008000c40d007410b29803080380150307041a421000c800816071a80c654504007200d201114001c1400041c042d042140c0003250ba02401c039598000c1d1168005106500612341d05829000744a581400d0000d502c40c003180449001400e00076004018502d0400d545100510039444480f01c0f081c1001200082d078500c0904100c22800030a0402411842105454503201450000e10000d40200000d4000038035a0f0000a0f10400541d4014400140d14400240062a03502c083c1c07961448044ca920a40c008260460030070503596040043c1c2d80d002072400e100040c55481402040700d81400644140704004002400c000c0102400401ca070700400c07084 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 733766843 1250 733765593 733765597
    0x601080903040b0f070227060109050312090402090d0c18060905070e10020c06130911040b03041e0b0f0106030b06070203071203020a0803250f0804140c060711030c0105 74
    0x140f000541c50411034655a4181070015180241c40a00410354610440c0c3e504003884081700c200703080101c42d442c1000030342d60380811440b0080c1010340c064569000040c004050310310500e1000d17802030b0380029000409440700f850300c41c0503d80004100c0c01d03040e12003070514045044a80c031505443c1c14088045000200c5215050251501d41c40e0039166250410502481d50340003450704042d030048110307002454a07040010032100c1c40300c9106160305418083c080c030849080d035003c40e00b0003000f884117000140c84030741165080360f0402ca0940320044a580103a010440d1560b00a2413450201c0600600d07207d4000c24a060b0345131900c007846200c00400500106005506c0f0203549030b802141c0400c038070001d0700c100741b12441c000c1c41a03c010500b10748542605620076141600361104004030101c3c00c3d404140310612003401450248900c00141c203000f48450b00190000c2c0c105884040c1003641480204008001948003400c211b4840c0752a04064501e6400800d26901900070800020100d62084003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 733768093 1250 733766843 733766849
    0x1212040e0c0a080619080304090209030f0304031707020303070c06020f010e060c0906071104020408070906050d02011d010c1401060e010f03050a120e0301090f1104090b180102090a0806060108090304 87
    0x3d034454050744c4c1c03c41000301d0700b0200380030084841055800450710300c0041c001800940f51060000d83d451301c0c04000e0520f08220703803542c42010340040c8014030010700644e1001c00c601c2c2d50360800c95211159400003904611034140c2c0202031180440e0000341d820340120300e81f0b035101d158000800c01c9070400f040050f158082200c0c0811b81040030403540510f454a075003e00519802800f50311007210041d80072800f20390140d0408c07246607006240c10070100007240215005040d00b03a5030b04c0740e070340c12039030010f0403410000d1403442d80400321000000250340303e400c0c0c40d140c068100c0002c10660007884140c6000300680e000e180100c403241400407038062182082d07001141c1d440001860140c505403160030752034010810f42404c0140403031400d845517809010307481c1854083c84550701c02c00c11f0703403515215984502d01c1c201d009034100140e040110b48804003483c0d004664041a151540003080b4440c0248241d40845601901d0708501094810740010407500c6084281c0f212021070725420b00d4180c2c0ca0007544 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 733769343 1250 733768093 733768097
    0xa03061e0308220305010e0a0b0a060e012705100821030406020901112506020f0c0108100506120103030e0105131208040b12070315030309030b061212040e0c0a 70
    0x40c2c9400c40310b04000ea103a40d01d11140407a0043d0b42c490342c62500752001c1002d5005907038070180c042402d00601c000341d1b6810050801040042e18074211610100c004140714880b03030169540740c82e103c0341e101f0b81403051100e0052070080110b441e01a204240b80d0005020340c3c0d00c68429030361a20b50000e0103030340c04410b14124459046c00c40e5240d81d01e01019501540c020746c1004181005801444000c100703040d9012468209401c0b610504d10700c1c410510703969800f032030465115034151100c262002c22a03c4455400b07280141265440d01c44584840c2210740c071264008000103265010a003505250f5416248aa624040b1881d0098011242c50041030703514986080c0701c0381d04101c9400c41c038542614107445044044d06103a95400c0d402590303081042180100c410b42c01c2003281135a0325109024444031142003010031681140c600808503207070b502004100c941d0b00800b10f40301d42e46c1e9510b0726034205000c100301c42d10a84600004002c42c0c20a1041c10695100300c8040380c9a28104801d0b2164640c071030f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 733770593 1250 733769343 733769347
    0x9110406030f14070f030305090103150302061b1c05090f04050408160c050d050303041b15030f0b03031308150f0f1b161115090111120a03061e0308 65
    0x1a1580344035064100c140703880d103200d13050000518569450070340000710f00070f8071030300e481d25496400907003610f5561300490742e444500e10050006a44a409a8115001114100728008402c40205107011300003038124504100702694007079402d030301400500c80302d88103849584288100d08207120030f40300d06680003041004c00707110b455540025940082c0c202402000340c0c205250f42c0c1c0000c607034a07080c11242902d080d0000002c101c14410100504880300401c5103881902d44d20348015a14401d08200c00b00d020152150340c980038a00c0b69030000d0028010090607265928444101ca20030401240314411550081250880745440c10040d441e1042e030818080340781582e91180c0d01241c503640203100f0300141102c01501c5503864076102c0540032822075510007400380c1c8003074140408805083d0f03003c10b00c1001c02010614034080700c0e0043c1c40103c1c4003820018000c600340e040f906c0c01c20910044008035000046644500154550042c0c402c036080000d441c0c4a20900413202c0c50045140d004c068128001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 733771843 1250 733770593 733770623
    0x50901171203010308071a041709030f0712031101180206030415060e011a2a0304090f0b09070c050d0e040e070b09030c0901030f0b04060617010911040603 68
    0x408144044440c121420703078004040c00250605103030800e81059444d000081050420407400c001280311740429010100307081c1c170b09684d908002502406d24a0b0214801296100070340c0c5080051a07030303105211040d20301c002e07103801c01d1000303042c1a00e00a800203580700e604040c08080610079851180c08100f40d0350315200040e02449026400944122034040d8281084d0210061070b129050103010301080b02180c1e9490220307040318000e81c214003c05070040070040410700c1901900c9200c0d0008407401e5180d400760240c03100c02d00314080d40e401104e0729420601e28952200d41503000202d207640c105d6140714181c44d0b0110844d02d14241c582c00801c80ea110410704495940a6880c1211001004001088405600751000d0074881c496200f02148040841d40f00700342c2c03600780090180d0440955480c99503614540300c008442c034101c00003800c0c100c016008641841300341d40103000544072090580c0ca50f1028401c00500800c084082514101081641c000191606000c0d4070203c903040100d248407108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 733773093 1250 733771843 733771859
    0xc0d270b0714010c23040b070b150d080c0d0509130e0717011517060103120c0c080a020f031f050a090c03030f17060a060e01030f1a0316050901 63
    0x1c0300ca00151030003a00d500500c11010804d00a0b0b030010140e076a240340c44160540c03c9149201c240455190440100384018407a000a540503103100d560000743c603000607120300d4107140c030000200c3c0d051504112503980801c00d105000e001480e1000d1001c0c02c680803000c800d841100d2030f008a10a4650010034115030342da0502141c1c10950302025044240e81042c1d5850000c002c0000841801700280d0351901710411140180001c940d00400c0017002003a0240001b44206860701414040100043c0318031003800d144502c5101c12a040580c000b0315417014907290150650b460032001400c91080e4680c1c0c0c0880c0301c80c100855400b0780246035030008981106510b2000000d49001401003c8155a403001003011810010001e0300550094681001403420440b008204c6207143c8942c41160300e0f0303d8140259500c4d0150725408a80c4c01d403916080b101100030048001e0709030350110b0600d05d4180081c5034503d86203c2010100f006080301200c051040b45010040d10340d0b024401c1d0781c0d00080c13a50040251030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 733774343 1250 733773093 733773097
    0x60804030e040e07060201151203051603090308040311040f0912111507050a09060c030c0206070f0b09030c0d0825020a05010612061a030a23030c0d270b 67
    0x607400502c08500002003043c0140703041c00603480480181e444910040411140003a0f14002d17102c211030380416043c8644025100744902c00100070800d00098120050504c100b40e804061075214000507a900d541c3d003011051101c17000c684620a41c51b050b0301000040c2c2d207101d41d0011687c0509814199108100b0545101c0c0c1c4130b40140e240c40c02030b03c40c0400c066070600f05a501c240040e881d144e032914540c0c100201001850380240003400486a0f81101017900252100c0340c0e150304590259988401c0d1130040405c1c588010024030806455040c0011901c001c4090b00c00300011408444030008000c0c411a0b03150026034824075000e0740072f030a5420500a95111011103251070048688408440e9142402c6a03510f81c88140340e8540315401e5401c00845014041d4000c0e40c5c07588203801d4407030400002e603c0d42c83c0a00020b009400b01803043d51038070b18460f980946d0a06120950b604d490014009c4c83d12001e80c0d40e041d81c005403464081603102441500321090041d0189046c04215050800b603000039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 733775593 1250 733774343 733774367
    0x31e021009060609060b0c060a0f0b06070606050102060a060b1206030f0f0105040309062c01091a07060f20090414160f0516020103020f040308070309030c0f06080403 73
    0x1405800a00250a240d5016800805101e5140000d42519100b0240f08850050f0848044041c0401450746084800201310380c00030301c500800030b01e02080070040c000600225102c1c941242010a102080c4203040d40700f001154402e03000d8401558941b001c41c2c00705ca80a02400010303007810722060042000503182c0b1988500041c0807500e420a0800d0028a459941420789403182e459100f00300030180d000b001c45c00141120b013041410180ca1b50341112103003e000484c0c0040d00780f803840494407030b0711030407403240100740c11400e440d03024103441c900ca41241d000540540f00c036030406e4846d0481004a1040604004915440840007000c01c11400e0041c0d11261850340e01a072241074100003540d646c0321503405540704951414040c0101200508031428115240d41030010500204151780c8581140040007a424600181c0e07448004058202034002da4101030190f400c081019010180c00035130100c15680520300c140344407a41c5030303036030140000039028403000504180082000240100c0e840542 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 733776843 1250 733775593 733775597
    0x30606061210050d0c0f0905071b0f02060c01021e090616030504090515011106091917042c070207030605130f0b150906090403081e04030507031407031e 67
    0x20302c5603588002901108031140640e010305110400300800130088283c00b009281c518000d0041e440c041d01301800d002d01c0c05000031031524921030400100041c09011602655004040a4881d40e83d00c414a000390840ca40c2d49900910049a0700340c4500060700380c6182e140d0061105241205c80503009040340e05e4014128107200c0706002c081886103072405010301c21110124001c0060345035000041118106261055840d0000814080313081d41c041003034041c003c440600d00c00c201c1c0051405801500030107600c1c0f152a0804030b0041010041c2d50002200c007680140c0d52000344441020322140c00009503130860250303204c804100006607158021907030100c40c958903481407904584134240b03890194081100c0350400341c1d0401c80ad142c0c3c0880031b045484000d50b1945014030f051030106000b0103003d00040c0a11202c100003c0c1010341003038100300940a400201c10450505140c09080c64102100031030100d0110440d07c007034420b0502c01d4a8100c0d4050ba602d900c07640200071000032102c081002241 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 733778093 1250 733776843 733776871
    0x1020c0a09180f1a0123060a1110051005120c22090308011701060602031b0f1212010e06030c1e061b0d0309120f0207050d1a060306060612 61
    0x7003c141d0008040385010300035680082a2812504805a00201600003040d2440400300d2440e0010303810401c10069141034858a640e81c4882000303503640d0100e62038001107885030401e152500e2500780c00c0b860044201468154156480708108291030810fa0480d81d40da610801120146145c605400d5540b00e41044200030612240304190003542c00136041903020410042c0100000c1c041002200021039966000304082828810000d480f8864800d07044068449143e0240b0031010030300400f103900c04883c0844103a005120400c06003a0061140c00b0703010200123000048076124a0701c040d200e001d00801034504e40c40c1070020040c0b0806140c002401804991504000940b604002811340e000d1b45908164000c0300b41c1285440e0140c0744d808981054106640d44c4001090202c1d010094001c0b4201031810a1a1100c103d01e4100c0f1940029405001080c8800074040c1100d05040c514003480f0203020f166842d6030925035158000e560342c3d074000f0010065840c1c05e203001d40031160008500c08000c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 733779343 1250 733778093 733778141
    0x8150d02040903030209120c060d0f140405150c040f0b1606050a0e0705040b060906030a0b1e03100c0806060708090904121818050a091704050a0501020c0a09 69
    0x30101d0b0b460b0034003100480d0340024007240340d1500402d41c3c1601e45512008010000e2628081040c5010f0070b06011036554951090382031103145900310101101050802d10030307518003400e080d40d50359844014820b04800800c0840c2030044010129416103844a0301040050701d08842d10314654024680c0c40e4140b95190045400900680107007030003910409404100c1c5400f100307200c0d0030210303140c1c041c5100d03501d444141402c544800741a900000d03011180c15440e070340d41903041c0002d8074841055581c810000741854590110410f04908102410340131600240544e66102c4200e070017030f03c142e0001c80e00b4000028030707900d0f182c001805500e100e8641603041030543d0011035082030041d501100c1d2251544507070214254803d0982031076481d100420015a0729049002c515101155201c0e411503840300c0020b03011000e10340104403002ea00c00da464401c840003040744030f03064005024051107203501141c0040c1661001901040011009117800c5410f85449100d0004100c0076403d00a40400d580c540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 733780593 1250 733779343 733779349
    0x1208040f094811161d0414070305160e06030a080d09141c050a0f030f140a091401061d1503030304030f0e0909190201030b0a0909020406140108150d02 66
    0x100e40c145606440d12140490115145400c1c040032412825104c54044410005642400108000450400101d40c5907446500f13060f0700000001000414504c9018800420001e0004500c0101b100549000c1c04064450305480500c0d007056a1450381640300561220208198500800ca101c03c030880006a176800d95552050300e0100d40c121002c541c001d40006160000701140302600d2801c1307860000c0c50b001150402030030210b00361080008040d560540110003994230345c0083c1031103c0c140d201010714900041104050b10522a04031204844405814242d840501500050390048480c003086401c0000000e0720703501d402801e0004071551000c4040854905000550140d4000e95424083c0310b00c0080150140b8424280700d80107074840b00400035a91400b0505100c9044404a9400388410600048014101c029142503021604410020b1010001e9010000161082c0c400744a07a40d51082e400c0c1646512017041800f08143c0c1d00014410180c417180100c500d03d008102003100d80154001c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 733781843 1250 733780593 733780721
    0x50c0f0f040c0206010e0601090e07210f05040318080a0b040618150c09260c0301150e16090e0a20070506090f030d11041208040f09 58
    0x90b0b00c05a0020380050000070110300b00d5a901c02d0007804c0c1620102d140c171009000c0c80c1c1c802003480c020000d00c06e0401d00c0d104034104000759415400e4a00340b14003004418500010002a58101d0102e44208584001310745a50f50301c2c801c0f00c00102c080c00409035541c403040894000200b04680b13031942d030703a00780d1403d188190746412614002d100e4155042c1511a08500b110341d003e0424003806500729003000700881208481100000c040c0e61000000c08207041c4610b80004811880c0c1c0c107500b050030044020750703850110b800321201d0503a218281c3e10352041c40d02c10600f0305030408000603081101840202c02e1510550b40000100301d00113038030710a90764072490120810f1410628a0000034148082c00810030040750082c034800060500415581400c503541c8c80f602e00c2c1070184d2a158500c2c10202d101c1c481c180c4004205a41c030580b1200028030f0070605550080c02150b130071340913040000c15072a00c01d06c11007245000c09250546180b600612800c0c1c00a444600043c01c40803480440b2052003880c07030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 733783093 1250 733781843 733781861
    0x106080312040311010b1302070201020312011401030f1b0c020312030a0902120309090a050901200a02150c0a0e0d0f0c0608060d05071a070203120405011b050c0f0f04 73
    0xc1e511820b400d10f80340003800c00c4134002c491a01681001d00d03a0b103d941d00e404010019264107100141e840001c1e10041c4d045026080c0301c91841c1d159003000041c004061920300400d003009a03000c0001517601d1f081e24041790101d042503441c40b400040b0861145000311000c00c9240d0009003100c1c3d100183d41c424004603881140c0300c02a0940b01e075444002c5003802e142c2100c0401c80c102c040d50a04040001145d030304100101700e50019600c4502240111600794800085a101030903030b4080c440420751825040d42c401c0000c3e00061003440354800b29200221b003c2805484080805403411042c82d03001c0302c040d843d9403600e907840b9040c0c042400000303108200d08046284251a08542c0501e4040043c080c0200100694003840301304079803d000890112b290343c2502c0142d03150385003440990385480d109000e141300c0290580715024154200c002c1d00700140007283d170309903150b02a2284900011100004000c0000d00a038010b109105c094580003480100b0480040c007034007440300021000030f0075248150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 733784343 1250 733783093 733783117
    0x20603042f040c3b030d02062401020a060c120216331509152c4003030f1104032603151906050406030c0201060803 51
    0x10201c01e1a00b024040c1d201910140e060824618618601d00c00d401008007501c3c43d40b2200604090800b1000403c20f203203224005802c079540f84120f0785000c0d5950106980307103075800c034660700041d411f10340c0042214081e0206034003030304c640740040d6941000f5021091148042c440350a1580a242c4400e20103490000300701001d15490901e81c1c10140a09940590007500c4800741c800d1590300140e840000418400740c00c0700004000f103143c80c5240a149450300660007050420020100700d19510f4851801d130340c0e05a00141c050050114003644900b0401c20482005000c8800140d160150742d4000790344081007a008101c8207050900c1402d903408410124400c1c2c440000c004080c55850701c60b5528129480c1d50804c000e680718072015a56009600c0300400c040c4440303a9000c0c0300b41000c0c030203124080c008214543c490a1003600f900500305041c0c100d46c090000c041303091070710410964484e01102c0c05c0d82c0320b40d8603107400d00c2c0f0101c3c040d00714005444255074a4400004500e4410001450036020345 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 733785593 1250 733784343 733784423
    0xe090408030f1006020c220f0603021905180901090b040b24240d140123090a0c0207031b2c0f100506030901090605070314010302060304 60
    0x2c80d504046548002d404a000e862016000380b1280b5000a02e500c00311004440310f25440804d0f014901814034012901c078072181c1020304020422419401c920b065074421911803e154034402c0144218178020300c2000da01280d24117400c12030100451010390801441800070070310074070685940c41c895400f0758080303442e800fa01c401c00c02d00c011105211840150640030501400300c6075800601c40c40c01c86030b180f41800c00c949011030b0080300b4243c200c400441c3c01c1c00d014080800d481c905425000f10910901540700000d07951407114501c0d0760120340601500529200782c1e5154400440014541030b00714a065204008000c40400c2481ca000107102c14901082040a8100607043e0350b119807881100e80f280e01c4001d52881121215200241d00c064600e00d8956107a80b5500d590300361060551203141c000c0360000030b0002012040d0081c0c807100d40607800034042130700d4960007101200c106020f401c940c099481c1c014801441c0100c01580c03ca40290500342111140d00e05400c10b02c0c0911145400007140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 733786843 1250 733785593 733785601
    0x4080c01180501050601020c0a2d150905220506300d020c010c11060f0d091a10120501090506070809070b18011b06020406020307140601030f0b04030e09040803 70
    0x24015564000745c00c0c03000d0601303040c400c2c01144c00c8115500071049110074403001c415040128803801440c0881c1c000743da803e180c0c0d850002340a10501d0307000600001d10f1148002c142414107440c0038000b0200c80d40500c150048001040000300800340940d40d211034030001e0081c41003404101060444400c4081d044c000790003020351480c20b00b4811010042d5003001c02d03400200e80c0c014403500c800942240d2110a40380358a00058070510031119400042e500101e42d0403040b9800c0c0d440548450320900d00c0c074049898018001070201811680032a0010141c001844400b911031028030308030f44a000045400d40c43ca40c0d03131f00d040c49021216600011108030400400342000c005001c0181400c2140600d8034040c0092003480c103162034045030501800e900e24070b00c00ca41103014000406d401450440d266911800000e44907488400300340c403022880ca040980c0030340c0106105048a5102d102005c090b1016650f9003601d40008005034180b10084107202b415484001d12070780f00e01e115110440c2ea82c50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 733788093 1250 733786843 733786853
    0x90b0d09080427140627010906080d0201050415020a020c0a080a02010207270b01120e010c0e0f130c0c050d0503040b0a050f060108100b16030f020a050d0804080c0118 73
    0x400c610403006160600c0a01341104121504690b04083d0555602c60000c021490107204030081991492503103041c4000050313007141c20780c809425071b20918140d80149501d03050407402d8520941e0302410030305103850140910030059008000700c2e8402d005031008880c900c40000e140d045a42d12969481d008075600301c045680c1445500040c15030006580c10003986c02e01f26500650718041291112aa00d85e0004030682c040d0702a10303146448035100703000001d08985d03401d0280c0b6602c02086c0100d420b6021094262410f0340d0720300f07079814000c0c20703000001156403d40c5000d44130f5040100140406500da07100030400138040d180c05005c43e42c40341c60382d904142c40e0071442d0b00e40040c030f0002003510304010300450302c10035413209030881401d190104546e110143c004403002030b5903224400101e00000e02130401702600d031456a500d070013511242c0001000100903611101b408000a02c6a0000200d40c04128080c541041c0c01c00e000c0c0480702e0421981d101240d00b10b89d01c03c3c3c000100100daa02d8401e04000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 733789343 1250 733788093 733788149
    0x10207020910060507020402090d1b0303020105090a05030706020906041a0712090509191e0504050d030c050a0f0201060e0702030306091b07030302090414180d0f090b0d090804 77
    0x1000212100841c503280143c010310500400100920640c0c0014000380c0700e544118001094981105000b64103d0410201c495031401c075100c22030165081100149038a4004600100815008405540340042c00e070340f00300c0254814415503034440414040400c0030492220804000e4840301d01d1240d840009041454252040c06001c4040069507a42408581c071515040da401c040607001021008030706941010141005400202801c2c0c2c416503c0007400886400290180e4095000d80c0c0d045004c1401c11030694020700022400300e03004018003c5610700c12810b440d00020140b0001a5554aa51081b8107041c0e05581080042e4404800d00c0780d2454190080341d0403800c6190548200d14540c00c0e407034124021504041c040c154089500c080c0e0b601c40c5d411411314010500000c10b118a001a142049000d4460305808030b0f104220507003800034020610802e11880940b03480e89403610305101d5000c1c07a4401c0800d0030104c2d4840e40304400040b9030b00040c00c00703003800001c819600c4030300b803019125403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 733790593 1250 733789343 733789351
    0x1703011703040b0f0d1e09021302030705040e0c0c0d120c021f0908040b0703050403051504020a050909031e0406020f07141212041806091a01120b0409050102070209 72
    0x10341007000200114401003048900e102121000341d5181c030350092001004081c11000500726030341c106c40d06800c008155001c0c144081c03080784d2000300290106d40b03040c200d000403240c003404030360104014461009002003082d8044d000c042030f2440c1ca07005805650a1040da0700c94040490050703030220001424600400d00400d1152008100207400e10060b0400721a07250b03034050b109540c504944080c04545011500138000c1e810900781d0307414503481c000b04241e00510040d2058000c0c3d100101940c0f00c0004242d0080d07030004d110300e40c854180030801000c81005059041540b20030441000700140d0401118200b510052000e80c6a0b894640c0207030501d1519003680407260001c0905108000c000014401103030b001f901c004400840d0b69080307528058400d902c01808440104001400c01300c4d4203004005e10040c4207007071104640e01c0c8107080945040c050004018600c28190320205e520070007140e1074462170300c440462031a608102050483c0d80841050701c0d26500020302c00258100b044480c2d0700 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 733791843 1250 733790593 733790639
    0x602181002060405060103080c0a0f0803220c03081b01090506060a08030a053408040f0b0702030303280e100e070e0109090302070905190e03090d02010c050109170301 73
    0x74610f41551010745500301404001c1c0b00e400c020405514024080185018076680200c0d0700d461030080381445020b54204130349403c1604c200041c1c0c0d94480c1c1a00c0504416250300081d503031941402c5035114181d64002c2650b200c80011100f0320801c03d52024007400380320794000c001170440c1d070800c00d041c082c800d01150401004c9600c00c000d41c20f01184d000089507480d40d403180c0c441702c003000e100d071035804082d45184400e0b50110314400410140410100100300303d0f6030f00203c1410307007603503514900d205004a0f403019506404c28000100c0000c1901d80700a131086071107103c4034801c1040c250030821160100b111140e245d22103a40e171140320095106910744001c03008010000d8924021182c502c00c48140900c0184036190100303001010b00030410300010b8440c3c80300900c214984064003945018410b10111181170034036404051a03d4040112810381c2d20140c0007190040d2150010b4401c2e440e0700740200da241d981c80400c40003041030300121a403c84181030103036641e9450900584041103c0310344140b1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 733793093 1250 733791843 733791853
    0xa090b1305070c060b060f1207110a0309090506010c150218030c030c061c020d050423031e16050309031015050d0302100e01020408010c390602181002 66
    0x29403600158183c1d071540d03000c8004960200100c0214403d80101040700c0019171022540840b481e622400c040e101300e90075a54039034405805d00401b80d450701c030382d180a4007250605c1e80600c042c500329003199500035010304100d03412449035600d40101007038110070140840d0340410700d55820307542882100f101d440c0860061058034480000241ca48420b880018820100084e0802c000f0080d00207180c043d004141d011900ea02c601d06140c00641021582100c1009a40340002004400c07800f4401c2e0544001e401942024080400400a07452082d0a449507103018070014a0200c1400000510680b00b1405542c8500c0101f007810301c0c0012070b00c2e4514403181070828022042c60401d2100c000c50320200c600c0a003203012400c060b0700703100b840c1c3d01030328003d802e022130210004015001001150140c178001c002c01485040b0440d554031110a61459401c0c02c510841150043c514001045940b42d45003849640d80a80d180c00481e4401c01c074600c6000c048003140d804034500b82c0f10480d90b420250010b05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 733794343 1250 733793093 733793101
    0x40b0a08100c030504200d050f0c010f0c0506180c090c0409270303020a030207050607021f0c050304020d020f0d0c1404110703181208071218090b0f0a090b1305 70
    0x5070079071500c500b01c0d1b4110000d801020400e41e501580c0e02a401d80090039a040c00030b0414001d5200c4101e00f5102c2d001c0360168006042141c802e000d4451401d400002825482e240e8011554044d102d03039407524054400c1c208442d851707507540c1039024051900380d02c446580318986000ca400b91800380444510810401050301510007028007003480559052400607030310011118182c0090040002c058468880d000802002a0300083d0f0b44240c00045915641214400090790307058030048910040007680900108006080514a0801b0288000c00201c0f40b0b00078800814903000c070072402070f220507240741e00400c410400d04442004c00001a5401e200640c0f14420803070340c510994200138100403801c0441d01c1e580b400c02c9241002307441844100070030004541410552a0444003068540d5603460308140200c0c1e004403040c1c0810642c1814070311001c0d00d051074103c020319151201c42d402c03500416510303180e0364400d014074000d0100c04c1800106000c224003440310390001017000e29501e074a000b00340 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 733795593 1250 733794343 733794353
    0x506040501050f01050d0f1401170f011a09060a15050d0c1d2112131d0c03090c1c0501050a05010308030a0914030f041d040c0311040b0a08100c030504 66
    0x40b202c052184802041d4690080b80640c01802c158001200d040508000456002a840d01d0b44c1c0c070304c2b84080b08481500d1400704180e030882e00a8454102940030055000c070f40c90a10502990380054000c0c1580c1802c0e907074420081084215040c0040050800200d001c01c05202c0d100d003040c24105032422020480c0c056003d820302040c06407803d03108001c0202203980b0f03005c1412400302d00580810a41d1841c440d905010005900f03c0002d405030284007070350208921800303ea61407009960b40707006403000d4a4001d05104a80e0000c1d01a0350107000b101c2c501d58240d154815000d48925120a03d0f12031802076040c80380c2104c1c1d0190659501d1400e110042012038100029260441001600002c44c548241780c14040081c1c08107815035a4000414145c48500050020b801118180084180c1c000c8000583c0034050008440042000c80c0c140300502c04140c0800b400080c1140141c8000f4445507810000b603051650341d4071070cc61640c00702c688000100824054624a520581428084c1d420705070b0321 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 733796843 1250 733795593 733795597
    0x5070611120306221a03121605071d01030201090e16050a12060b091f020a060203060a03080c0d03060501020102092b1b14091e0711030408010506040501050f0105 71
    0x80001e00c2100440464075607a01c100454022004200302d06040381c03142001c44010b00b40c02c9041002440c1d5a54040809040200d00c6011900307044502d40d103005039231712030705201c09031000041c0d58030b1140180101e0302150f050300c8401400c000c0c0d10703042c0d065031540c80014078034000c2c7e0300103801a050640600c4808440481c03800700e40d9003541011501c811041e402201c141200c16681d21605007040000a005000c0a00811100390140d40e400901d20030048048c6a456091341300c100103900807900000410040d03030140d900160014000141540d80b0f0b2030340f0016400200402000c1d40142130100400f540522480000300000e000a600703181d81940083c0212403918900085488500d00d886040640504112030741e503403040302d0800240030030303101802c00030301401131008180e0000260f102520700381c41600c4c81100c0c0300005415407003402084084006d409000001400b007108a00d1403110428000781020f018040000a5185081c2081006450701a800180502c1409102c0700a036684882 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 733798093 1250 733796843 733796863
    0x320030606121f0204031b0e0f060a09140708012403050a150303090305010f0612080a170a0e01050c0901050f0a12090b0618091b0301020d050103050a05070611 70
    0x3007030055400b95208030390a0042d0040049480c900ca510b01d0041075485a0203801982d0199900700e0050170350003000c1051107032500582c4018815034001940c00403203100c00e030341e210001030642c0444698885601054904140182c0045420b110411031400d510885541c010b1a8440d01800c0c0f41800e0000071505560550301c400415844000040c00c5070359527000020f4224000c254400840d40c0c2e07040003421008540812a225401c08030700210150a6001c1d15080d5a011085014084019078894119a0003c122101440451b1002c8000c10701401b0140e44565103d000200700b4905500a1030b00f1a48001c00d005400801404440f0803a640641621704802902190039a6211420426107103001c884008001103802e000e0710104200e0110704640c00361105582c9100600031909030078016890494003000713507030b2019002c00f0b040210188419000703e8003070300040c41c0468902074442600c000b40c2040c3d6140e40202c99010800c00c1c00c11181004203420f10b0080f00030025003802945441500c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 733799343 1250 733798093 733798099
    0xc0503060409110307031b0e01050906040b03010f060f080118080a0e221406010e010e090a0f0501030615060c030e041a0d051006060903050a02150c0609070320030606 73
    0x696400100a107900c0421042c0f00d004003210f50b06903a030301c0c2450b0300b143c0012118400e0f4003417401c00111b00f11503103ca60305a400c020030341080d83e92030384140002003050000f1150302d5034844141240c921001c0c4103840c080c009000c03015807620b04081c21340f0b00792944640c2071204d0081151600e0b020441c0c60041d20f103c0c1141d464410036000c25400050a48036400103178000441c0d1110040d1158800380c5c0c040e04250f6220400c0d941c0541e07413000103460503602e10910f240842d8a00c8503000b0b5900d05083c0d0190300400d403401c0064003c00ca006401c0842e0001d800c1159a241d98040d21900009482e075000c0040005141c9040084070566000b0010301d15484590300464035000180d251040e01c5c580240c00c81009005540100f800e0700780305549407511100b003c038461829402085440c402ca81550075a500707d030040c103e200d8540d090101c000d0300192010325040b0300780007602c5019811302c11030b400303840020018242c5c0c0d030550404550baa004195481603800e035800400c5855280890401c0d8018130407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 733800593 1250 733799343 733799351
    0x80c0609040f061a0304020108070c0201080a0906020d32060105041509120305030708010f120308190c0f080a0203190509250e060402181315030c0303120c05030604 72
    0x41415000303401d141e04515540d101004c8200c03400030400c40076512980c000da9410f0062780f9030350002d8413803240041002e800101740382c001581e081c449400002407503104800040c078242e007a075907610445070340403a8000980208143d60f0a01c1503200c1940b071000da01c1c0f03545a00c0034104040080e283d4801d62041006182c03c000c103596010340101400001810360b08042035201c01a1714000748a588112550004106a800042000302c803030031642003074070900b20a480c250400c0b5142654100c80081040d10081818220a00701d800ea41c0603540d030346031850f200d404400061400242006034014000300348580306104000b20341d52a00c0078103035105000000040c04e80c407100344082c02c1c49001c0e82da03c010355104405030307901030842e03001a0003214030760000c002c00703920303044100310030780c4a010040603040e8044440403500303140c04a10112400003520b00000d04000400c1400030000b083d920036180c107000c02d0010411316410200000d00c0100c0030710200485255100050300342e00001d48410300031952 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 733801843 1250 733800593 733800611
    0x53d021b0603161214061009060806010513151e031506082703091804084501082a030615120108010e0f150403210b0406080c060904 58
    0x3c440549400155000c248203200005d00740710080300c025250310b4060011905038208640c410062a025510b02d0b64465400740c031070f48011034641c1c00140001030740400c04c0d41c0c00a050030141d4004620483d00f81c03246000c81c4615049500785006600202c81418104101c505c441503080d42c400e002e50310141481a150f4030740000f1030702e114410b0714140842602055021100c60000406416008022110010b02840c402590704841c5000e0b02d00500024040c072032240612000303401d9021500141d1410320102c0c60305c0c0c005142007803940d1144a0050943d50344082c1d5568841c5a0b5540101c4240c98a055080b5005159819135419504c1950400740072000c80c480b40d444011a04212803e10344403a11031254090400e1662002c0c814400c1035860103c00780f510980204403c180e4004000191000c022080c000d086000c9004100b01c040014807115500078105007868415100e180e008001a003109100c06d0200702c42454103c44103543c001068207040c0d035141c00442d00c1c840d20503203000c0b40c902a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 733803093 1250 733801843 733801847
    0x317070912050a020f0a0e0114061c09060c170406050709080d05041e1d06190815061905130e010c12060b040f053d021b060316 56
    0x649400c40804850340705a110240180001c042245600899405190305510700c1003162811880c800c4000c0390508100402110b490106000c030465400790003d0314080d03400010727020181c0f6002c078200c42c1503501c0c4250300c1484041e100d150000f920b28100100c0300d0300201a0382c100000001c1008003810345510010782d01c03d01c0340414000401c001c2003100c4503e080d002010300307241c01c580103004c007014400345101d00003803000380510115014410400390600301e0080ea5902031000034840d03034100f10342e0101c00180311880540740c0c00410b081c0e4050628580d0380e2011103d0a240580120300c80c442039049620400381507403041089403011610114014500000500544080840e800c415442d01d64800030301070700903d1910224502443c00c0180646601052910380240e004401103000261401d00c082e050100202c018030004e189900302008400c022400c6549041410500703c0b00c2d541075041d030160f01000304210320390501d03203404420700c07500c40824041d010080c20700302191080803040405078 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 733804343 1250 733803093 733803107
    0x506030a05030a0507031e050f030405030f041508070e0307150c060f0b010912030f05030c13090b1207030525080d020615010203070b0103030806040b1305041e031707 73
    0x1ea021060ba6241e98503240040c02940001c0d9054001c038449266181d00202400040d581d8001c3c90388440341040d0b0407040350300007500014411030f01840100080c1400503903940240c00144000e0100d18600604004014180d0101030a85002c1c0043c544104000e40c2d0f0118036074007651109031071907418010300182104c000003040409461145021143d420502003034104044080085e00c0b0600d007182d441480036407100c20110091b00140102c40078070700c040e2040c1c0003540c02401c0380c3c6941d41840b207500c801503000344484c0e010b400e6242e51070131000801d08168403107005030381520000d01000c51840d25042d0303c0303005074000c07030304280c1c9031341d03414042c81e1408a0b10102500314101100c00640c054080a5034813042075420b4074070014458a0000c881d88001b084581c0d0035400031980c0c41a03441c41d0307002e48040c00f002c0c0c401a801390310f034400c0d04015191702ca04400038451028022a80d82060f0030540702840f44c1304004008540a42c5402c00030a4002020b81d03d0350451110240496403500e038122820 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 733805593 1250 733804343 733804363
    0x1050727050402031e0906070507080306130e01200403051c021c08011a0a0e010807020f1204030b09030403020a060c02010e12210c0a031101090209070804050607051606050603 77
    0x20a2010061010b184148108400d016480781c45c45512a15510005a501c480c02c4900400080d000c001c62400503c5c030798040e5030405005000ca400460310405004199038207151072200fa0380d0b480421b62120846110000a140c1c00600054505411500d4141e142c4c0307108000400c4102d6511209401603200708040040310801c5c5000182c00842d080d0001c100d0344007889010b400c43e60441c1c5050900c030600040300d03403c28a0307440300e854441c0c41d0001940c01c0c40c80280740728150b00504101f03041d40c8a090001c0c0030748000c1691001da40b41c3c15883c0c00481b078403028181500076481800144016110110084181ca03e142400c4000c09118401283c000f507002d4101c0fa00035008015800061100003481078100909640c515a4035619005000c40d50041c1000003009611130113490020a0103100040950b00d0380800104502109401213000c00700d00352014000901c02c401000107000041c8a0f0030340040062600514145482a001c41e0200d0381e0741d80038200ca80d4850100700a0b6404020075a02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 733806843 1250 733805593 733805599
    0xa05010e121504050604050d0f121e0e07080f0d0207060c140304170613051902041401080601061808060f150a080115060e13050705040b0d060303110105072705 70
    0x10f2426103400380e210081501e08844c2c501c80c07012405581c6000e5920000b0901260b038401c00a050110948000351004d042c64040710070700c2582c80841c0c2400c50140c4017100e078180c0018202145002d00c8140b030f101106c0a8080160000400d01158641c0442da001c200c0707695181490030b40e0100d0501c00b034407078100481d0795098840080d00060f084a03071107c9440c210100c40689441d940c40e203a000d00130100c0320600600642114800003510309103032402c10140c900151002460411b51413043c4c244c40400c0e04a404551700c40001001040d5012046010004c1805080e10343c0919060003503654842c081c0001c0c10303100070702002032020854040e26000f00c07100181095202a51500380320b00a14000107801102c241c806030114000b03015012074a10711001600c1c07400e2002d09500d013a0000c0034050034140402000b000006281031412003e0014201a220b0000c0c40d180f851801404061030305411500d107904000030080e0b61707504000d12408418004056452031040c40c00309001c0d180c220380060354 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 733808093 1250 733806843 733806883
    0x509010b07060e030418061505070b0604050a020d09060b0907050c19140a062009010219111503010f2315040b04030606180e030d09050c0a0902030f060a05010e12 71
    0x486c00003150000401c80b0001e1141440307504608808603a01d2140c0c0034050000c91801c0d0205401d403c0aa01c07030759211a0000005050203c0760f10105d0503504030fa20300f50f410549440030f100c1c00e4601b001c4081d4003d01c1c83d0801a107408030500002d070700d591198406100c6496034625803030900c1807003054078103000c40070f109a90000d101c61030068020010602c200032240407040041038001d004000300e481c0150160000c0c052010000c1d0102e22250300b902c42250341d2240029500c1d46c6450300010140154595031000c1d80303a40c184540b0700e0300020582d03c4010f44c40b0103c280d1801c804051aa03024050000f510009005c03642d40b03e0788a5184203582c45685a202d0024002040c007489074030a0050b114070403a13800090744442c25840907291002d00704c018030303042003207050110402a44600a218414400e4038402445000042c801002c1d0f46c0c0000041d030b400000b001907032000343e080e160340014219211419a030411000919400c56040c041c0c0c0654803800c0e010740c0100c01002503a82580365011954 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 733809343 1250 733808093 733808129
    0x204020c01020c0c0a0807051306090213140418030503040203011d07061701052d0405010e0a0e060106050d091e0305270609040207060e0a1103070509010b07060e0304 73
    0x1030007035210b8a002c241c1402444c04050303640c0b40000204040f51140001040d1080c140410004007d40c420424002030b40d50380710000d8804510300140a40c0c0c8010050f0f000030070310380806402c0d0141c09092051099181281d40c1049030381c1c0709040c0d84d81a800d4540f294880e51184046030042c5185001448041035a2071011224480012404182c5005039140c2000e0744034418850521002800b60603800f0748102036480380402c1962400e01590501c1c00b404c0d601d0314021011501300d56083e002800c11105000420050503440c0c01800b4034124528010300c0c0c203602d40b14000b0300d9070041c8080d410f4080e49801d038074814026640110f0a50800e080380c2c03140d0003082c0349000303405940b2550304c0c401006452001010f220f1000b40301d80024900c080d060914007502442004020362081200316421580c4400394014014104210007485224192402506d6480e07030416140050682c862441030a844006110012505040d19001d941c42a00800e0040d5070240b041c0c1540110303007001c1201e4403840812 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 733810593 1250 733809343 733809367
    0x30a0b060918090c09090303070309080d0510051507020a030213021b1e060709060311120406090618050c040209010c05060c0a08100b0a080703060f03060b0906060307080f13020402 79
    0x4903010f101401c0881d080b1241000611090b920120343e2a541c40e00305000041c1035078040c3c1c00482004c4d21074001c4c1482c151b46240e403c0e044620070f0381c5080744500b00c7c940511040c20420041800c0e100c410041500b000c0a4ce0300040c400c4c880d9000081c000e0309070480f64280c120194045e0361000c104081030703040100408030041d03070b20001c92070030720380301e495080d8081d611030000f090a13402004a543c4508005080090075405040c1c7c1c003191320601f050400ca1401990103041e580d50085201d0940400e191b1801d090203c1610602e4000d803404041249204000500c009504c00c418036040e500503850355003000060b10030081b0b140015120340a00310030044d038494410010070000e030329a10340c102c26031203480d10444000c842d4020030000e0b4001700000701d01c0742e0042c01510b6105070300e0300c1c02140964a6400302045018640e00c00c90300c2d607031540c024080c02e1811001303a030340c030810030f0311443c0c252f1800c6034000748540d10140540d11401d800c03202090412400319100c0100503005841955500c00030840 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 733811843 1250 733810593 733810639
    0xf0112180809030d05091c170d0e07050f010c0f14012a080709060825020a060501080d080f040305070f0b0406051506030115030b0a0312180b030a0b0609 67
    0x103c1c464010b10901504480c000c005860007200060010141140b85020011709454103201c26a40340c60248455000c070b4510781c00401c1454500b4501241010100b00b00364900b40c19504081e110348084080101c0c41d90380311403655031080e00a07102000035180e5003040f041451140d5241030380ac0d400c0c0304003240383d0344591a0100c42d441103800441422002304400700c800c186c0071b81e40d0600040c140d400821425110701c60a40e00400c109004800010b008480c1c101d0b003c903c140e1540c00340c0c200d8020001880118840c42d40100443c2020342145052a40c00410044004019000c0000d914002c43c0a0612450aa40c080b6610220305900300c0910300340b084021800701d9003116240d00300310021340d45813400c41d005c101144d00541058116400e00c01c041880503c50301820040542d41d96038502c25a0350301c6007480040d4014001e90f00080c03001100100301c1c0100400030070700c132400103008000182044044942c003010441c80000e002040000088451144041159200d17500d514001641d09031608 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 733812949 1106 733811843 733811857
    0x40905060105281d060904021b03030408090406271d0a0f030f0804082b0e0607030b0d02060d05150303120105030106090b0f01121808 59
    0x320550000303420103160002c1e000e261220400f55812a4000c1010680c510000e07402d0040c000105044d845040308140c0915030001c0d07030004681451242c1048844100141c0c0d68a00b09414065130030303009508450b10642ca030407000110708015512002042138000402140500790b0340000008203034110a02c3c40701915900c60880200701030112040452250018140310160303410011300c0704151540417014400c9203424440415140000c6d03070010500d1081100c2200411155891014040f0b000d82c2901c0d0308003510361403a05008210140b142626030350030894617002600300130404c80281c50203900640200001c69214605820183d40540c1164031b111400c801c60000c02d2843d80004204400401c06900500c42440c0a0040c1402000100c80512006c8055400112041c01e610101c80c103100b0b88161582c07444038250400b500030700b5001c004843d040c1c0281055405903000c1a = true := by decide +kernel

theorem cover : BRFrame.Cov 733633093 733812949 := by
  have h0 := BRFrame.cov_init 733633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 733633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 733633093 ≤ n) (h2 : n < 733812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
