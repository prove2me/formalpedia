-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0439
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:49:18.621376+00:00
-- url     : https://prove2.me/submissions/317a34a5-ae38-4553-b74f-8bcbb2398130

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 78776980 ≤ n < 78956836 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 78778230 1250 78776980 78776987
    0x1b03190606080327010903170f0c0d08070906030c0905090702010e2d07030b0f040201110102030c0901080106050901020a110f03100c0215040b0a0b120303100f120809040c 75
    0x1c0904507840849450384441401c00c1c904a4a1354400114542201d0307800070340d507208150500690394070501d440c9450311640007141054002400703524400006006a00b0fa4020030802e00701491400d582c3d0b008281480e007400342042505d40c0104c42054200040d000290390030458003412513506451510040c0e8030101d080b03005021290880e0341500812015604800d110219038220100c2040038118114903100a25640c8020f8440148212036031000152000820303001700d6031207801070406582d01c3c18078104480c01c9a00c103c41980c26004003103101a05540e0160b01c80c1c0c0075000600b440e0703250950810003c1e58078100c2450060071000b20b80c81c04450b640368414010b040e880f000c5c04a40c00200a01982e00c0504111f410780381c010b10829480800725012484550300582c3c10030800342803507d880442030060812459200d030800b801800003c3c12480800041d4896402516581c0c015800c0c11640541640b1961003003180f054450989004600c15408468964408a4002450003e03a10054 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 78779480 1250 78778230 78778241
    0x702010521090d020f01061206020a030615030203040c0e010b19020c0604030302030301090f090305041701060302120109033b0a05150a030605031501061b05160303021b031906 77
    0x110038800c010090080100000803100d4840e101a020381710000c1c0c1e5028103a00703c0d0b07414032843c1c0001000e5000c060114003558000d2440d00d40518020960585401880f40b2074010680c0c87c60010394004200b10601501d0f4203844050440308410080f654034084081c4241d00500110031890701502020061440c001c0120180b58040980071545446e600c6c10081e4a81d0402d116145001c0d082c201c402400c0720381e6220304104154541c07a1282014189452503d844406100d442029035a812010000d6911050046610045031001241758107082c6002000c41040240400e00d608085100381506108001d03601c9120040700003400384801ca5400041001d03151360300654020f40c0c44e0056000703400d8060010041100740da01e09000e020394540606603203040303070446003100610b0703080180700350b42c414030f030703200b201d003145049124a001e040e168035041140f0b02c02e01103903418030031b8010800c154042c00424446400c99010012010038100800c0d00c030504200355500341c1e00c0b802c0840d0204441c50380030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 78780730 1250 78779480 78779527
    0x70906032009030a0c090e160506040e040501060f030f020f090f0c090105160305070b0903070804060806030a0c090c020d03050c0a03050402030a1505040201110105073504060c030b120307020105 85
    0x5070a81c1a1b6618510301c0180082480e0350f045c1e00840701c00c50004842840c2d10811a200680715620b4030b0b00c0c00390002c0e600130025000701d9555403075800c0001c081e0240708081001d14040d113040900740440d0300c1001003490f11610124041c0100000300700e400782128031010b6000b0828104190756285490040340d0300c1c82454145c4840c0b844c04401c9000f8140e00402400701544190442d1800da2a030b88061950f9015030300004024400401040c42a148a20500ca401100240850752552800d545002c41c1e03007007641160025a90350000e00a0550b41048210700112007420104800c1c00c1c0070300300c01c04500c1203641c0b000c18107840c2c1c00807270f045480403c008122184c001c200d83c0307100d01881c0502c074007070030043c0d07410381c0064101c0602501d0042c0600c1154040d04068584081d4000c218514808240201c442035401700e98150110f045c2d0070814003590b2045104000008078058404c03005001c46030140f120358051026014032045c0a8000003c6a10702c0d40c090030655182c0030910f0b095460303500040e42 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 78781980 1250 78780730 78780743
    0x6050a170c0d050c040803030c0a0309020d05060a0605061c090f08040b030a0b0603070f03051009020a02030c060901090503030c09040b06070302010c020c010206060a0e040623070906032009030a 85
    0x708450303007110401a011806810400340100d80f0740401d554510f0080f8002c2106170f400030004945c180c600c1e20002c1003a80c110b07003800b2071981a00d80014490148161050b44c19410007410820051031910610010307100071210182020709210038524803e00d90042c1c0c0784107d542e852031a090082a03600700303c00b9030b030102405039510344690a000d05508283c0d41c6412440c200070302e031111441c161090b6846014641d0f101d107207140d10480c2c110080c103406050029020908007001c1000b10b101c0c0014a08082e09070015592021000040c6142c00300040045c181030745084d100000185011081b60b800a039074525803900e90142c10b0004005012000403203030300c0030001640808160f01900413100c08030031a000d8424944c43d0b9801640c03206070403030303540341d0001c07440c0400e0003c95651283e894119000b00800501c01007201d00c0e03142c4c108100e85130341703020602c1403040001c501e038041c0d208170145c42c9628050050076041d40800400d21414031044641c200c0200e0f01c00030b2510104031054034250001c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 78783230 1250 78781980 78782027
    0x203010b04030314041a1c020c01060e06090c120702120403060b090a06030b011811030106082707051003150e060f060313021009080f0319080601080106050a 69
    0x1103140c410365100344401ca01040c41825a015500a00002d95089442410365140c0070410b1102002080d0b120f64100c0b402c43c055176010141d01d5020740302400208664400008001e802c1080c00401c4510003440184030351410400c110702d011840c010303614a45040c001850554079000030a908000e607541c4052102d00300410004140702d43c0f600642140da4007650f0100e110788898800320169003081c04003624511500004220a40340303914101e22203101b0780e03000030702c0d00031031906000036500c280d014500282d01001400300182001500604092030500c15180104104881d1074031a2118810319200383c045841c03501009000390005180c079546103051814032910b48415040b0b5050589103d130044a03902c0c1802124107026041b02e01513410f070300d01c4203401c2e5940d070700300b10385441907600170030410844282c00070311100c08004034410350040303001031510355002c00c170f01d80c0402111120703000400c28030742d06000503079030040f841e981541d1992a04c07544c1e078404c00f0310030340b26002c840d01e642c1c1d100803a01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 78784480 1250 78783230 78783239
    0x20310050109200c102a170c0a090b0c01060b070c081903020703290403030e01050106020a030801180b03030a0507020f040b0f1003110c0f0d02011104060e0a0312020a12091401030e030904020301 85
    0x2c1089184445207041610347c94030748070051900b030701a40c04001b000c952031607000c0c0428a2140090090070200f2400402c0c080c2c0c841c00920082d4100500032501481e082206100d1520140448400401c1c050120703500c580443d00d0003941c90545100203440ca98003d00f1707402d428047c0c10224448040c610340702008505142c40c0003801080c4000160b0300c154030b00300022880c1072010035140a0035030503a54a28840c0d0810a4080d800f020461230802100d60354250322050391410b102600307502e43c403511141e440b0401401400540300103800c3e00c5105515001107980b840ea91f4841c2c2c00d40201781952402e04298490303005034000c1082d41080e05200d1400b00707a0101c9034000090503403a0780588000d82d044009105010303800c0c2c41e040c51881d10f4403070040c030091001a200e040c100110000080001a00f19070b82e0f11403230150300e490b103806401600b103c00c5840922110030007100d143c411524200270003034501112068008512100b55042544034121104c04035800c1098a0030800014400c66580d6520f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 78785730 1250 78784480 78784487
    0x3021b0609010e070810051003120c1104020717180405130201090f1406210f040303050610020c010c11150301050a0b040b0a030207020310050109200c102a 68
    0x2100c21014642c00c00340c0503034504002080d100203d030703d141d0060800600706000c41b00a0240245040071802842c00e0000119460782542100c0c0701540d25000d0320f165141c281a4801d480e1103041c44e000da0f00402c44000004e09250b541c42c14098014010b58590214583d000c101030b031140306032076215017888140070174502c05020800c04075200b62584a0030650710b12a1904100c0f145c864545070302400d020032035440c24408000d001641210f080c0e0080c04c0550000900e01c004240c0d5400c16560070801080308040c0c04d031089603001042111010030507414400002d58600308070822504105100c0d4009040000e81c0d080220f0284c0010285802d0000c0b03021501451b400901c0fa96104850b0b413800001d0181c00c0344122000d4640380b1401c2c45c9890312000f42035010b580f1076a0300f01e8040c407031035003030704181c5116110706030281a502e007021403c9259900c0f80601d0b0b540304612030a0030b100c00c028500d421203000490103004503110a002c42c1071075215078406000d08001c0000c540c40e10b004980c8031106640b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 78786980 1250 78785730 78785743
    0x5030d05010311040e0a080a2703030806040c020c030a0206130308040b0a0807080403020604080a05040b03070e0a060f09030204090f050d180609060e0108180111090a05030a0308040b040303021b 85
    0xd003500c0400503003440c80e540a1b5503015101014040040c108142021140b00d1072640c1094500402c0f908603100d50507403007403040b42d12540300360006903480041c0000c51034503005588201d1120310082141e8250707100000d40350100c80100034850600010a0700b20b0030084001c501c011034001d000315803507556070102c0c80c009501c922001c0b000940d0440000d03490302d0159480b580107030b4256004000c160794036620072003190322220ba04801c0c4a000d00001881050140c001e5104c0c0f0760303030b030707107000b1085110811b00c00800b00c0d0340c00140a004458645920995020322241d085030380455012400d84041d0400f400032010001c0c014100d400b44801100d1040e0b00400c505255011074906071240603501e10086821141c02e0240308002410003200c14043d42c03050411356008400340c0740c0040130200e450589403c5a10350410407641d20008a1103002d03500d000c00e0690010134080d0090a203940d9195002818028024002081c200d400303800708052510030b5060f18881c460300c2507a442c8000700c4201c030664444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 78788230 1250 78786980 78787013
    0x20f040e010509010b0d09050c060a0e090109020a020c040f02070b01030b01060801051e040203070e0307080a0506090c09011a0d02131e03080f0702030c060d020a0f0c03170405030d050103 82
    0x100100e00000d110306280150364103c2e03080020040c2803c050046c1d51000d802402002d54080c4100640c1d940156200b078000c1c01101c1c1203885a0a103040104144400e05005030721003a82c9910507c40003a4054022505651918040b0390004a4030941c0101500a0081c12009044c10801c8030000c010402e090802a060715401e071a07481c216a030710001c22a01c0015411311501c0114840249069824950051604031030303542032015244c1541800309252002a80c41201941c8c003452031141030280034441a40c0241408000c0c0c4140074001d008a0f8071110188100c00304000319681441110310300b0300a950b00d4900b001c106564502107000226410a56405440000350b810400080d10009100d9220304aa900c608005e0501d0001e241d0050250446001a6014060110740c01c21a644140040c140e40d220494010385440100034014040032001e1012400d100f01688101c01194000c400040b4036025a5a104032a035035a00e015425070103040c00c103280007803e1100100412480c00150380b407a9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 78789480 1250 78788230 78788249
    0x9051011030712180320210606040f05090c061e030702060403030f050402090c16080403050d091508010b070c08030c07061103040303120504020105040e070201020d0506090115110c04020f04 83
    0x684d0b44020760907110a80b000405403081e41880d0108854000c0700d60211100c010942140c914044a2443c0a0440e0140440c01e0750031540800c41c0c5450144114200e00c0b0125108000320314000182c1e50b640c00c00f403540c0c1441754401113080002605035411829800001c2041e941e202d0500f00c0020355030319015981100424200304a131900d800b0700307114540c80756400402480554450304c09640042d031010402c3d0058018002100011401050051008500c14401802200c010034002807100b00d40390010341769110741c5410f88240380d038042400c9055418107582e203940d0b1a1540b030001da18040e43c0e809101c16000c04100315070554400b00b017203402c80b02d00b40c03203020081c072501704c90390f4480c0710b0b41c0002800700f0050070b000a001002c640c031842d030240c0306040a9140c951120704031b2080c42021136030040140c0d00080c4245d840b4589009a80d0040d4050781c00d8001941000305004034544280c0d607400820070020021071800104021140d440903001c0c0086644601054504107190310900818280 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 78790730 1250 78789480 78789497
    0xa0303030603170703020309040c02071707030b06060c070317040e0103030e041d0703060b032805070909030c020108100b0a020708060c070f1515150f080709051011030712 75
    0x110105048915441c0d246c2c1c040c1d0714003034005040000500198a0250461180c48004074207516501d017000c24014645001b0b0a4640c610300e840b80003d0002001c15010303d1081c003205480c1c07440002c10700c098a6004c403054860501c0d83d030f00c2446138000d030741c80300e060f08905400000c1410340140c0156011351044e00c0511801c450804550391080c01d078207524445030300480082006c0340d019032000c51400001001c0d00c090448040704608407501d1130318107290381c410340c4120000300441002000c0080c940c0d280305001c10b8401d51809840e58280407406170500c41c00310001000c00380043d4003074002d4041c10052544840001100a540f1005801140c9241c03040d0000b04d181078000c03005075035a840d481514060741c0403280e5240c62440190200c2441082e81300e140350060000c243c442d00d80501501401c0010f01c072901c0d80010320075098150540184811481880f40041c1c3c444011401d807003050391901000c00d1000000c0301d8040303010002d40100c0c00701081400401120807003800c01c480203581c0304800d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 78791980 1250 78790730 78790763
    0x506070c1a01050a050d02010519210b030303010b16150e0d0c080a03020a05040e0c1206010804210e060304060203040b06010809070e060d050a05010501080105010906230303090a0303030603 83
    0x7812803c1c00303440c0c2e1114041000700030324138003c2030208032148103242c02400c014040c880c0507107903110704803a040421346190a20743c0880086028408035030984400f80601c0382c07000701081c0c50380300600428080400c0020b0180c030002a04000000161b40f0140c03c40702c110042c001540144116010b81185004400003258a06c0c4200130380c00940b41c0181b5000d00d440c41c620002d40080d48252030800c2400010b0000264400c0740040c800e1041d23404520282d600c1403d500c1d91a80c0503001880d05060041a00a010200381c90301584c180c0142048500c00c09003c01000c1a1560f0305185030042e40070b40e00204200400402d6005940142d100301c5580c1c42684480c3c0041d2040c0074116000d0300d0660103420100016011074a03480d402900c0a0100120b00703119449007070400d18051811b075035681d151001000006006d118003801042503100030009542801d401030444030000c4512107414500d01191403807a43d061045401d6148004c00502909a803843c1c040d0291102c4c9c84240e5100000c1d180034034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 78793230 1250 78791980 78792023
    0x7021011130b070516080604020102060c0f18061911010e0606131505061204050705030c010e0103020705031303240b0d03030e100609060f0b09010c0b0c070506070c 72
    0x15401c090880c03084009905200000140f40c00026040e1003510803600c3e02540d01208140032000f03404038202420292038a03000281c41d2100290410a8001080102007041300020003540c24000d0000c048220350b1032640001a4240030f18103050040f8030103103e81d005050303006940c106110380300c04001e010310350528200e2900da9400315041070b0044030510321840007054a40c8030300c042a0340740459545039929800841d01c40d4001d03401e29007c80543c44140803d104003041710100070701c0203d000b080a210503000080c046100f4091132814541c010441108100c01441501d04e10051042d00c5001c20740c4e241402c1c4469031032041104403607286150021640b158a00a401c0000000b4142c1502012180e500314000e240100c4142194090b00034450105400350142000030a0b42400114080d0b040405c401602800c96000101c00081001519090b980255105850540000b2120b90703980d07449501c03810703503c02e204000b441c5020301030400034140d8112034807500060081101c000d000e0542800710 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 78794480 1250 78793230 78793237
    0x2041d10061d06060310030602120a0e0d020c0d05190c031506050108181509030301080c01021603080306240a170f010e070302070203060103060b0906060a0f0f050702030607021011 79
    0x120910b80c1500c001012400c080340256040103000e201401c1056484d1940012078001254080c50004000d007030120000c00c0e030103980240307040c607400b801d0000d2200401075650300041041d5070150101448020901006001c03295a10010708241121010a458802d001c0030003070000b280e1030760311908120056040c500c03600060302c906841d410f480761241c54104454904060200300340f44540844019030340703a0306070b60a0261b15200001d5450303504101c91541080c5140c003015045510404034607610048031400d00003102d40081e44030742d030303a16440041041c011410700801e01003c01d134804400d0441a4200400301c04030607a42d0a00100b00410120544240c00d9440745408a0140300500141e6030110b1203641201d0581401440e20700b00740e001c0380c24003609a009803a0070759505581c56403800c02561156005c402104d615240080101000e440712135814110800c1080d403421450415000b241103840e410b400500b21540c03490a200025030b6248103081e0b841c2000e00344081c000b49809940c059 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 78795730 1250 78794480 78794519
    0x304031403151908030a090f0614030c070303060503030c070303031505030d0f0e0a031115070308040f1b0b0d0608070803070602030a150305060a0e03040608040b0402041d1006 77
    0x20794000b0580b01e010400e00e01e0590746049040103994030006413284042008050f000060b440d01d442c201c0c07409a00c51860902a80100107104a50003428112112041142e43c030440c6480465140c5586080807801018170b90041d0707030584400500319151010004658080724829a0103101c030480b07c42d134281103d6414030502c0c0d0582d001203001018580100e15151800714246400b0840a20600c0018a11506540251115002941ca441490500c0b8401850315003070391412600e018281d80c2c0003010000c00401c09414070104492070300400074810210440030b10105521074045403038000c41c0c080c0c0c0d4020392100c0004c925080780000d141c00003140c020116190400a5420402c85072220006035000808805203542c2d80c10710541c0071602160300c50f000d58001d00013841c451508980c540b0445d4032100b402201907005110070001281d100c4019940a81c1c0100801800c0e251440400c2c06445880d40d2000e40080c00403001c00400300000e41011100d220391014058950303181d0b4004110303c0d68012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 78796980 1250 78795730 78795751
    0x503010501030f0b030304060f03050c0901050306060a0c0501020d020c0d02070303091406070c0e04020324131110020d1404080325050304030507050a27240b0304031403 74
    0x100081d6000382e000446040e9119008106950300754000390031613015410920100e804101d283e1691a414400e0b141d0285548501614000785440040c0690200038220b52065400042014aa47c0305036001c0120301c0e4000000d6403a0a0f110617075030080c3d0011054000140719031780304804014800148442126010384800d00600d0824000d41030b0381180070f070380e6900028200300c14000514000313040c10080c10040004591400c0c640b0415040003a444100a100784031150f200480c190f402015980100c0030050310858080189044c0c00490b240280c00da07800902c03a40030180319900401c1800801445d9134800420044810b510704840c0141d02031414140d00034045640240030b005a840c2c0f2040041d20805400c61060340c501c1c0c61540190801c171510780201c1d800f000340c0c0c00e140b08100f0180c9117502d13a048080000ca949482a1524000c9600b0000e4980c41244080d40b11105982142d503030700d080c510314141d19040d075030503a54411fa4007100001c0c50040c441d103500c0c5205054034020075000f00d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 78798230 1250 78796980 78796987
    0x103030309021509012a0b0a090302070b070c1e0b1803010506040c080103020d021207080304080d030912180506040b03062106010312091d07090905010506040512010f05040f150c05 79
    0x5402409402c1e02030424004041458000010450451466100790b029a0f0041427090807841c00a042940d254032a444007901886001d000415941182041c0e4500c401c0d100c507007403240403079100001f01e641d0080c0100c05002514080100ca484110a94070006078002d20882d280d003c103000440f12403070f2411001910a1006000600c0c004203401c20060001300700107181801c000915041802c642c3c408080341e0310004080010102c20f00800d000d001e500e0404124410041d03c0e100300c00012241c440b010172140c5c8800980070000b05160f54094035015008945031916041c02c038489030f00588819106041200014414500c4011480c07144101d8401074035207030746141e460513401d03a440c01c0c0a00500c0145240440d01303410200410744020701c0e140d020605401c0c01500a0056811600007409070340c202401844103440d0507080300c0407a079054410003e040d8048015134010180b142c24003000505100070b100074840115003e2000d6070103649400c0c9504003855043c801ca4081b0518040459000d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 78799480 1250 78798230 78798257
    0x131406012109020604030b0c0a020d0804080a0f090b1603180f030311010b0415051306080d1202040807030b010e0903031e07020c100f02070b090d0f02011205010303030902150901 78
    0x36040b50900c0382c0301030b0080d0b05140d120b55601e40c00c0c10b0219110307455000301040940000d681040104100511814409040d0402e900e518000b031107000491024003800700602036201744241c4000c4010644481d509444041c0745950294804503060705400192810441821028003d59100111894140b05030507103807850b039080d254884440b00c013800079507844c0b00507121622203010ba003003420510400314018505140401c1025a1010702100d1413525048061001d903034006000804400c060800442075503080900c2c00282c070031034101038990302403220000300b0849990043c40c1a181140b11680d1a65144464259640800c4668150480100e007504084802c0100041d81218043c810340e06c0020b000008250f111a21102c034800194446540c00045641440074002400d84ca1000520f8042e250700004c941c003004480241400801c50940421a80610504060b510420f102441036603501d082c00b034002c1052450690103a031102d8440f80085040c02d04072154241c058540c6500700110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 78800730 1250 78799480 78799547
    0x60702090402060d051906061110050c040503100e07080307110105030a0e01051303020609030405011d0402070b0109020a020c0105090102061b0c0a05030310080604030210050406060513140601 84
    0x2070002c0ea081041041100d8200b2054000c40784100303580960411301300d00c6042004c1c2142c4075544044100208900e41a0517490040b41e6642146492413010455444181c405003482c0f1a030f07030000ea4144900c1020041904240e0041140500b440c030a654645540381003083c1c03a4440c099005103c198030040300801903000e00b0185030440c14400e00010550200c8502c0c60855100b80c0303080800d0400f024200e406c25504000269100c0401d002079820310786800c1c000303003c01e88422240054400d004200c1e03c45510346034140e9409a8000842504c5540c0d1242024003d510034007044c0b00502400c2420b8159501440486200c9001a40242060782d82c240c0e00c0c01d0b04000544900a0040c002c03c100c904040080000c0c03484a8020b00186643c1d09005024080310710842e4030401c496003009082101090300420a401c1c3c1820040c008113580e604d03850007200511054100941c80a81a14507030542c42c50356000c10144032040212840540f55000107440640c480c0c1a4041d400140c00b2140982031311 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 78801980 1250 78800730 78800749
    0x181008060105072d1b0501051303020f040b040615110102070309050907020a0c1e091b080405071208040302042306040e010204180905061608040605130c080610060e060702 75
    0x205507904c4807264103c0154840d1007071051810f58044220072241107000d80d0043c0200000c003070900740030307142c145188a10643e0560030b11002e84241194605d0262030744403504201a55200104100840c030740380c00c00c07025100e08400e2000c0010320b00880c0300100520520032100803d406413030b0249100e1400d4204150380340010086c50840c040c030720f024000900d020340d02602621a03011012582d0f076140a10400e02c05041d40165201400c3c20b4948039a01d10001e24182c03224183c0c5011015a921401c01d145040c00390341c4044000c0d500c28841506000486001e042900d100b25802d00590b105451103030324110090800058540b104800308401c0c1c0f410740e00180002c003d42c400941056540c03806a0507400200c145000d200751a1030248040107803c1c0310040d031001c908410b07020521208000141071070f9000b00002d1400e581c4402088803a010301c803a0000c0301d5070000c1d4444907651564805510f407030003541c2c0324842e51640341002c1102c074000c44034142209806400b460422600740c08220683c40c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 78803230 1250 78801980 78802013
    0x6010203070f081c0f0c03060308090f0a080708030415030c020d200303090105040515090705060715020c10050106140f0d02120702070807090c0507060b040b0618100806010507 77
    0x140410402074403c0b01d0b40348a602d400d4030000300045d007102d00c0c00d0040646600e1078000341058940704043c0300154064065456444040e9040c64002c04804c010542400070354101045522502d080083c1700d00c800001442603a00d911009086440003060542c19034200d45040701c05a00a54020030019124101407400b00c0100d0084054100c07465031b480e0b04580c012303601540c45944400801090040c1007021210140c10b1440040145c580110000d45a1500340a103a02c0340e400082d03001d062222024400140d0510000704641e40d60560f01116900c608170300504450038104000040d45074040c0030031985002d9410b40030341c6046030503075490489a20141c404440030340e0078009081d007443c418400c1840741c0c81c103030000c014180c141a03a031854509594000c1c02503e0424100049071544030059841041c0d006101284c401004c0000401511101c1650307504104041440091103004022690150000b52480081d070303244000c080f24400e0044070441d0201d17108018000000307540220907081c11 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 78804480 1250 78803230 78803243
    0x3030a2a0308090d0f0909020304030e060a1805120a170d0c020d02060c1611130c0c0204180809060304030306080607050d1d07090f060302091f090506010203070f 71
    0x44008252550280d0030105900141c0428108054814204200354128405042c0366001e140f80000c01000300805000c0d026449401001041c01c06008a4600b01540c100900158032405449801070140c00071041c6c074805401107038400619030a02c0d00000342a90240809003500c2c1d000c5440e90048541c00c0304028103070803c10000400c07122282d101c0c1803501c0f4020b9010b0a1001c550030402842d0100c0903028000c07415003004904c00c0110405240d140c2300d54805020041007607110005000c1c52151103403080d2441c14203a0b0007900560092403c40e04c0c6100700e6003000104045400c041c40001d4000c0002d104001c02c03c0200e0451418202460b841442403a001c0703090394460105505020003a80d210000c5a0040380c03280003c4518002c040050300c418180401d28003070100304940d070300d01512600601c03503550300075030300e44c0c1d00c03c0d802400295801030041361b00d90828003440b032110070b44035141490034114001c01140211070380c0100d0380110816402181480d1407a1580d03000c51007000403c42c0c06 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 78805730 1250 78804480 78804527
    0x21903120216020d12020d0305010807050126070504050301060608060d060b121009060f050f0610090506070c0303080c070f1b05091003051e070b03090705060403080a02011a03030a 79
    0x507990361307043c1a4850702c5072001c944d1102848101a02d009000001d42c4141811301e401400311440c00145007080300c100340f034220841c0d8600c62100c6980010007140105a05100d4204140300b5042401841101e174160020081c0d95600e1104558003001510950781c0300d54080248804944070fa004685a514000c290000c00000284a140b07800900360b000c18810362a240003c09002c2e481c81507003a25a20404103214600e02100050444d400080c5000d11404589060086085c800c00b500000341a01030308482e900c81e41c900b072003181c1030700610045000a014a00143c00001c1c003800b940d14003036002c413a85004100d140d0790703890000c0c1051103070305440d00540310014440e070360105101e020f09000c0004800710350075070500c0c40c01c0845070300d001c0d204d0043d2102c820366000c000160b1582251191804541c8984841c200d0f42e04117403959011540c00343c0c0c041804424000501e004211880d1150002c0101c0152204403210400e40c1d103034050381c16081806088001c0707006a400b03a48041040102d5800b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 78806980 1250 78805730 78805733
    0xc0603090c060703020a110607020d020909010e01090c170f0607210f0218090108030901110109050a050d0906030515060c0a141609021201121406070f021903120216 72
    0xa0b583c020b84016070059114030074000c20b201418100c0300b54984291040c0b450440720b5004500060b0036118001d00822500002a0341d0450a51090306403402c803000910800b4030b02c2c100114000c03e64050a8010f02101d4155050500c000030300c3c0e04080c285801070321055980301f105440d10b0000e11030201c0e9a55062500410041041c031601030ba000d05543c0c0103071181c0c0d007002c141c013501104015203801070a1150050219050010941d96000750920701210610b402952407030140040b590010224440ca0443d94200040803d51007482d42c042d644695250b9070342e81027102500c4044e2012140000e0040d80c10000341441d030000c0c0700c180c2d0720b04100d03102c0200a036510343c0840220055084a900503524013150282140040f100910800c9029401e080f140754141e4407040041c440c60940994200049040040a82c0060f111400160559020340381001c0042d1400002529910060181100842c0d203c0c0009441c1040140c165448035120503074108003500941c01525402e1020182a49810 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 78808230 1250 78806980 78806989
    0x26010501080403210c080916030b0a020d02130602010e0d0903150e010212041110030207020a05040e070308030405030307030509060906040b060a05041109210604020607060b06190f020109050c0603090c 88
    0x9100014a58039052240f078500b10301800e01003d01440b010301507440c0c48c10030100303806104261700003405540060ba02c9482c0c54407880244210701c021071a01c1030014000500c160194004221400144251458048815411aa000301d01d0100501800301c84540b1044418658030204c82c2e54140c4000518000f0400004035102c00704490841d01d01d0810705c1611a6410f120382006e00d8412142400c1d4140041742d4002200042035002d602c2c040ca654042c0303070350007100400c0880e00554004070100c0ea64217040c01c02989940c0101c0e40d42d0302007030404c00807075111500090300c0f900c14643ca001030401920b0b80d50b2240095100901116070045c8000030210700e90b516441040c4810801c524501d980d605102c050092107418032036181c08009882c0c2803c2910400400c482d64480d904036195941c170b105604d842801810040c109036007243d004907000300c007202d5002c07600018108545807c80646503c8030200d017a100d098200400c05d400c15039400d07882d401c2820145030041e2200d01550400301c007940104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 78809480 1250 78808230 78808241
    0xe042d0b040204060618090e15010f0311120316240f0c0f020a110103090b0f04050111090d1407030f080307082a03060f040c2601050108040321 63
    0x1a00c8262104091200710726107031041c08001c3c00642000c02d03445806804119000e8024858082945e40300d001300d036a4007200740321070348035241400400c806a5854080212400003036020450f458a01c101e2109130526040d480c0000c0060140000c500d4100700189510141c2c89080089401114071000306800c0c11940134180b2040401400001790340c120503c1d00070640e28194000700a00a1905800c205c19501003501c81c143e0f03803c152501101a0b140004034000c4c880c04001600501001d000c0c00302c05e50112035598050f9001f54020312018501c0740d03c03002148140ca2000764840002580300c00020642070681c0e42d204002c00649610550ba42c4032681c20b40c1d0030120841c0c0c0341c00b00000f00010305400c5291a50496244c075841c0540034200180c00600641410590004500100000702207a84100c0310071410540980184110300c0b4501014080081e11140d0712955290407807070a20710036880c40d205040325416500c009042e10340d51820341d0350310907100680803c010301c80c40a03503800082c3e0052 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 78810730 1250 78809480 78809483
    0x20304020f0f180a09030e0a06020d08041b030309090c08010501230d050c2206050f2d04080c090f01050405090a140a020f0102160510120905010b09100e042d 69
    0x10600305c00340e140c020000b00003280305920421a000742400000d80c000780a00d80c000a5040c00890303600ca6080c00c10005d020300e48006401005c1c08008810158080e040d1400c076005210107001c80302c603070002528502002d01489000a8001c008580c51808404031096081c07421002035203844401003285056079011500688403400004026100750f484032548071038840c0740a06c16051702e0030300d07400500c05d100303000c20b451410b500800e4840300100c410001410b080868480d000880c0c200e4100460250014840c2e4038041c0a9a189144a41084110301c2c0c4246004843d40d400c0da82401c003000014034002d07051501510a554840c00010808a00c00180b89498402440000280e10401c203034110102c2e210b50440d000301808001d454841c0c00040300f034035400c4440c860b0a14800d079044640d003040f00c00b0a001141000c0304401805010b41c030032810340f401540c0000c441d5807025401003070b1340554030070a1040c840900005010481400181d0010140124040c10001c440300115a80840c003120 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 78811980 1250 78810730 78810751
    0x90f2a0405040908040515030106050d050a1103040606090e010608070b130b270d0f020906032d06060a03050a08031009060311030f010e070302060c0109050f06090705010201020304020f0f18 83
    0x405000da4541914006e400d17140c01f024440c590740c181038005005006824580030142c0d1140082401c0180713540003008400005800b1540340d251900b85000a00110300c1015459490034640700800c00060007200c0681e1842001450440e00d092101000c0340c0c40307007148201c1d1000e54a000700d1520340c0d41005060550382550810ba00b1216540c0e42c0070030300c0149054a00c1845c10556010004103038070407102d01c280d011511030003166510310103c0d0030061071242c4038400d1030081164442c0105c680c107058181210400444085565803400d1001c0340c049404041c0003030f40040e26406c001a9003a004642c010040c0c1d0743e0308041c80d07a80400c5016101140c0007142c40400c402d448491904080165041445043c4024090b880030700d80443c0e02d03000d0030301010b0b000d458001081200105c00b50000078420b640030003100c02c413140086450b0303140d120584551a03a401200d1000400350300c14000e82e40184e400078484c1030080c64100410038a20303004041c86030040e89410060420781b0380498441d110300300b2401e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 78813230 1250 78811980 78811987
    0xc040b0a0f03050f061c0309050907020d080105030a0f12050c10090519080a0302070203030c030d090209011e09021b01061e0518010302010e0111010c020309090f2a0405040908 77
    0x910190583d14000c02c140401c42d6201c0c00c0221960f10290204800e9490100111444400d414100c910300410f40041e80c000b0203840500409950001d2400b210041360740c2c0c0c2d4215a44c0390400c05456401464000c2c008500c01d91244012590b0a51f2059085c1d20500b421882c0141c403201c040d0904a101e000c11424507540c182180c14401d01b40584020f030602c0302d4400d451404240d589181c140510040101090f5011808000715202007003100c0406824004484e188c404801402016002983c0120f029105800000481066483c0444d401a100300110b14409003071a0a400c02900984d00b203101e15520b460489070307042001c0c130a03200030b00100c041c1d0030b5048989400801424400358401405031007103101d0307003003884848018141035a60900e401948030307038400012a000704041000702425440c03d841100c85d80d4000004251203001a1903140d0301d5030b00d40b07034000001c000c01c895441040038000101c03014521101c0c080403551015203501d900345516000410300301e41e280d0004a60511002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 78814480 1250 78813230 78813257
    0x200313080a15020a140f0301030201020d170f10030b040b07080c0406020a1203020c0303010e01030b0703020723011e060f0b04060207090e03041802071a011d0c040b0a 73
    0x1111102911400c0e00030107490925507226070311030552a10840c1c0060707010841e48403680c400e4200780c500ba81551101d5840792000c2c0c840070400e138420703c0221b015216960318088100d0280940d804690480e480c00d40705607442c00000d0001000c0181505403c0c520014044000390040c0b00701c50242d40101c0300005140b5041001500d8618040c003100324100303080c0810804a580011382c8100280d000b0841340364000350309420380280c0950341408450740004800441e1149a4075403c6048034082c0c40d4084a548590b00b09500301d129010015000d180d401c0094a1311101c000c082c0001c00c1c1c8250000180280c0303141c441d810110011101c025101d441714010404454440400c0f0b0250281071100c41c07a081c60301ea00655205920321a64240720b40712408807907410000d200fa14000d01100019500c0141c071004070b47e00940c44208111a001004141ca0b0030004841d460b0505856180038020200c0324103613801c614842d0000d00000f040102080301140f03400a02020b401000282d032141d107203581700c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 78815730 1250 78814480 78814507
    0xe010504020a084e071505060d020126070c0507150509121009030801170604050c010c050106150903120806030c0f010201021614010f0b03060c0a2003 66
    0x95a0083c020703680b0004805002211008031581c80d403401a00c0b0842a070403159007450080c0f402604070318000760101d6110000716604005002c440d10401c0413810510300076240c40c04840701034a403640c009a41ca01d013500154069482c0036021141d03041090210900c9540132001e10104072558000103107518651800c21204100b01405400104516840f17a040a000101540159596a0304ca1040b42c0081050380c0010301c4140720000f4044400d000c10203860501824005082c0b280400d0a4040200c1c1850400d010a0301d50040e42d0003400380c0884d0703509600444030611040e0b03081d1070555a40740300188a00c2407c101c010720200540b40c0d0144540b0310304040310100f118490707a10512030302c0340c10007100d0350340415104001407040314030901c00c0d111310004074024082c1712001c161150100070044184404207054500c400d240d140244034110401c021503042d01c20010100f47c060b40414041071504100501511850070f0b07502c5c16052030a0b44400742700c03110700704492900c005d400000341c18540c842c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 78816980 1250 78815730 78815749
    0x110102101404030806060705010e030a090803090117100512010606020c060c15070909180203011104030c0506071e060506100e0f0103110f040b0d05090d1d03100e01050402 75
    0x90504003004401c40ca0300002800200040000302002680c1c00003600716a01d14069640464103e0002c201c040d0103107200300d82d01e601040c00700e070214034152400a22004004111680e00d10182d4600c0c0785001c1e030b540342c1e0000c3c00c80505182c1e0540100000440c240d00d4040c0b0354408280e0590000c5030382481c0c0840a030a05581e160598010281048011000c110008032829010303c0c8034291403007681d50010031600c0010326000304608604104405803401034000381d009005000318020001d248004451056902c924030004284100c015000c104500e0810060030840e03000710404544004c0700b10304142d002c2a0329500300c0b000340d9110244411802d100300340961408041c24070072a02c00318540040c1c40389140032082810103031140207003514201036500381e59400c3c0420100a448549850400e0242d41141701418003003407402c000106510710018004908013078175200c80d080c6845080107820480700c0c140c101505072003441c15480118070948280090f900c811300c0005124105031040054691 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 78818230 1250 78816980 78817003
    0xb0304020d0318080a0813090605030615010c02040504030305061f02100203060d0605070206010f050901030c050405090c1e12150408070809061201180c050a230a09060207240c06020d0504110102 85
    0x1e207011800cac081d64030001480ba07042452950b40c11401941d91004a4501c1d001210080d005401d10b010f001c1090b400d0740215000c0d180803150000c03020000c108003c2500545e00074607005912072840540d290850381d0082d500600c003d0b2001004000380c0d10380500340c40b411341348100164000001001916025080f01c0040c14044844c8080d9500d141c48070383c80b0403203d0251a1080b5928400b181c0c00400070032040151a0028004005030400c80e03412003030301c8054001042c0180550405c451031000d01280058480a1009018111f80c41d01d44501886d034100010032a26284104034032a0180c4d107113000380100c1400742030000c03503542c146014640007070031010101c04940d05048495035100d8100b03068490740c52072460321780c1c0c1c4031040c2c00703003112003601d0740d83c0224050000081c0e00159582c04821706042d2213150302115482c540d501c0c442035109581507140641003c00d0210b80e0080c0303201300c080f407800d18040c2d0005400c20b401d07079140c107085070700039a0215403140e0740342c0b0a02010358040c04201d1084 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 78819480 1250 78818230 78818249
    0x3030f100e010510030906060b03090123070813060e0a11060310140d02040509011a03120d110d020307032906040e060103140a02130b0304020d0318080a0813 69
    0x18a403900c12080c160043c05840e102c0d001118000026510039841754200c0d41c0c0040c3c09000556407560034220550003039813885615400c0000a180d0241415040e980440040140580545d2108011501180301402c203011800d0116006000308080d406101c65620504c030180483c12602e15180740c07682c0080b1500f6024050a10030032102c0000b0202e50300403285222340340c06000403071400213552407484580085d0703c5403400301407008011055004403441e60034402c511843d1144041003688d2000081101c0c00450350030405120f01203d41d4110725100307050404004e051600040e10312080e60030840e034017030000350360701e800c40381d0800502c001a0158600c1c001c180560181803003c40c3c0c06224074062008004442001700e402c50748240d10400803005640c4c0f81010904000c0c1169010790b000d0100a25141009900403d00c4061702e811640038030350040c24421f0303a04260360141da103901070b000c0d0303603585825600000455850610543c1900303442440503950300c207803104050b42030352a1030f041072101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 78820730 1250 78819480 78819511
    0x30821090708150c030a090302070503120715021e0c010617150106030605150705031207080f0604050c0901080402030109050d111002030c07020108040623040317070206063003030f 79
    0x4c1442c000c11a5009000c0c2c400100c1c440600c0d0400364076009495200f15051b1203114a0504101e03000e0018248540c446c030319000144a50a5206050f03004214804007001220a10807a03642c64042c000c1c8407807141c80c4004503c144d510300c00040d4500316401c05654540009a84075007603c0410708040c0904041c1c1000c010b0749003410302240b0340e40c800c032120140070480002e0080912030204140c50124003842c104024901d0800350007444044141c8000d0b20b004088808182c032071519000e1300d441580300145160410120800460b003001d00a40300340d800d5540c6411103030125600b03001c403203c20152501c03070151213410071890324504a0184d4100c04007510500611030082280000c079514581c09180c610555142c5080070001005c803210500790940000000b10400080f810b2039034450b6020351101d504100490034414404441200c00100581005001403003a14100a050410032228941a011180c4c0318004282040c0103015810782a440442045101460102000c1e8400a425245c100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 78821980 1250 78820730 78820741
    0x330b09090c01050a030e030414010906030606080402060919030803060f030708070308071a1f050102150a020c0a02040905060405061e07140c032205180103082109070815 74
    0x1210309040c00202e040081c0012007489040c0b003a003040040d00c00c80401d480c0d41e41c0d9520505805d42240c4048180400d00004000416074005c0c03045204484c95074651070002c0e43c881d820021664000c0802540c04030381c40c0b2046001040c42c1540c80c2c09141f0030290300395281410410030840c84c89544002e0300c1303a40006002e00c032980c2c01084c074400b01d90f0f02401c2c045d151801864161540c1e150b01000340b0002080000f040740780c44203c0d141c1051154904143d40b25640c441004a0304e402c070681d104100e001c810400306001b02030540c024021500002c040ea90300044a0340060250740340c3e0402550260301c031070305000038460b00303000f0107421420014118000980304404c004080354010484010702c01c00da00d6015602212000f22080c1d1804d00040d20790303500f001303203d011301407a1f0403500301d424642d001c5010034141011204040c4811382040d10000d960304e541d81d41e068580c0500c4076651000003051050401a60000c005805a40b60401a101c014181a000e07880c10040d0400c1210042d0300009208 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 78823230 1250 78821980 78821983
    0x10303080907050d02060d021605070501030501210f020301020c0709020c010507020a1a06030a0b0a1407081003020603040f0206030f090105070507020904062307050c0c0307050307060c330b0909 85
    0x1d503080d90560700071fa103a4515810510090150b03221161820250000d00e00030800e001c02c140d020355809880822069880342c0c04084503c00024801004030700700f140000100744001064807509100400140c41d00076480c2d825801d205055101c0c14802d42c002c0b0310065407490038020305500600500c0200f5105026450b0131040710043d07240c85042c0d620420101e8a01e0b101408141003171504038255402d0b50034207808800c000d1000800b4074110740f20003000305803954424101c1c540a40c1d0008104500581942c00300a215400504107d0310022000c4100005880307031000365106e03403641e4100e0310741c920b46441c1041c2994002800c0008002e030801111005035541c40240360010380203100015000c40310748900000000c142c1c155900c1030310b12001c102034254010001c01c07840f0030b000d06076070070a40802b09140d40c13940c250041e650f02d504464014007489110742c0715200b51034018044d4800d0761070100e00c0c002c8850007035109100e080031f6242e10009441401e000f801081c00f0191804800c034a0101c00301d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 78824480 1250 78823230 78823249
    0x140d0207060c0602070b0c03070e0102010605060307180e18060f0c04030602180409060b0103060605190e1507030831080c030f0d0b01020607050f0a050d0204170601030308090705 78
    0x1c105000590ba00700302803102d0342e41079903012030b807140c1e89a001c1e080100c10011a5003007210b100d4009100c0780c910715030329441800f47d141281c0d005807120303081d40c40d011001d48120001f9000809126040c1c1c00009400000104503409410101c0c03110307804901143c074aa04000b0002c0c08034288000c0c04060003e0f180380b039011201129003144005844829103440109404c0341c03500c0c0c80358024104400300382408030a40c0003013810002620100304240c3e8a2400703441a00554a402d1999542c00c0f6080d000725001d00c1c62803034110070090200e44602080d03040001540c02040c01030f4001000b01d4104032440881030214000480c41c040b49031844101500c1080050324071850003440000c02044100504504006642e540c0076010b0010780c849001c8610301c4000d110101c1d1075401032241d90080741d81c050280c1c080f14800d0b49150180740c80d00c4c0d03101200340c505a00003849c8a610715400c001c0003d0940e800d00e0f45042da0103125016240a5240d0b0400521464000d024510280c1002c0c000300034658690420 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 78825730 1250 78824480 78824489
    0xe010602030706020a090503030d060e01060e13020d0e0304030305040807062c030717010e011b09091a040f0b030f0102210a060306020c03040306050a020a0c0807021912140d0207 78
    0x4d41d4075941c50340c044803250f40a0f44100d4240c440454581303a8100759800a009803800200044096a40c8100031150b14008a0381140c004034010041c149522040e002030103003402c20000400c07840043d5100e030b40b441d80550b005600040700810184a03101080c0213500060110349415540c00f0844d64222221007822000343c10000712080d00d07030f04662428080100246500105020303950301c0e0140c8107010b002c151021100c01e51a14903940320361000c800581c203401e02196200e102242c24181d06000a045074000300032443d00d558050316143c0e9403801001e03603802c00e101021821850000c245880e02004c04121145a401800f8100190031410409403051204001c1d840254a031100424000c0030960409002c1d1400003c0358910890000020800c2b64802c607801c1100d40e54544c2d08030200c0c0202c0c06034000042a00300483d020501c20005031070341c1030000303002005d0080b414120a80002030b40e400910000800420442403100d52655101000201740140c4019071000200944070840ca006 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 78826980 1250 78825730 78825743
    0x5070605090d140a031103090f01050c0a0e090705070b0a0c08100e070e01031107060e060c18010c020102030903100b010e06180d0507171f14040204050603030c0105010314070e0106020307 82
    0x101d0807849440798000c1c080310060112547d03580e003842103071341d030b110015400305c10300b2582040d01240004c2000400c942d0407608955070301a138540d07038804200101d08046d00001c1008010311200b40461004855180034680d00c01001480300102c80015010b104028544508403001400c2017001102c0820415409050352070004060207140380182d0081001c2d2100780e00706e100208200341005110741c40750b603500b201041100d01580d10062640203510444058014003000310a50004550148800040107441401a2414080c920021034600380300b05010384199611030926540395600701203100f2071818241c0ea043d290a14800c4903c42000c0221680c500800d43c40440000b80203082c040c81c03000d0020002d00c030bc01c1010742580b140ea2020300f404c8800d0f2009001014102c15503d41c410303090490b4142142074000d54964007080b0081000500c0c094240c0803c200c1003425803c02e1240b180030b94840c0c001035034409e0702c80f40044d02c0d01c000754204070200d10305c0078010701c81c241d000000c0e036600720350000b03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 78828230 1250 78826980 78826987
    0x2150a0b01020a08030406140603030301121b0302130614030d0c140c12010203060f01110604020103150f2301170f07031d010e0f0607120b0409080a05070605090d14 72
    0x200100c0c07401044400c01341500e0004806c0c0030030484542c11241e0781c03410001c8041d2240c3c0f101c00030140c80b44401e1040101010f011000c52000a0000d001c80c41d0300c9006c1854420907030303070302e80108074031504000c41c0f62030f40f940c0d40d074003400317000c500106c1c420510005400504812540c020054090340d00d0f000c014080d1203601c5c150103020941000b403540c0988010b000808000c0003544035074040d41046d10b40c00d22032103c0030144d600952140502c8510030400ca001406541c131950019402440750300c1c214240e6000005000c00e514124003100001002c02c1c00442e8807031046e00c240300320458110b803141810040004190f04115070f4103000c240c0c00100c00d40d03500100b0b45511500b07034001e042d440c042c032800f0710b010503c4d0102103406500070780c1c40085500a072541c03280c42c05441c40c0c40710300446500010603000b40e80446110b465601050080c04003400000340002c040d10350417403e801c14030000c2c0000d0360010f03007402082118018260013500300c00040c801e1030b800000c09442603450301100d550300b00010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 78829480 1250 78828230 78828251
    0x3060b090a030b0c07060c050307020712080304030503180d0c060b041404120302121e09011419140a021b010504050a06020a0e1e120309060306120a0611090a0602150a 73
    0x1004585170a43c0c015420000c000941c0030141154104554100242c02038144c006081c00301c140c848550907a00402c0240382d0303070b11503030280c03a07030b800180100c0c1c0f401481c0602c80c0007601c42088040400b210580b00c1444102080c9407090544080c441c1040c000c6040501c00901d00c0310b9544083e0300075a200020490103204075008034001c0c011500e518000007010418441c250405c8044c0c28031007200d16006040da640c61144041c00d0706d01d0003c00c0389401c006a8000388451a04000000400711500341c04103403403441c50340c11040b80b0b00c00da904008260f800200d44051051115130f00303120300a144000e009600e4184c65858403005c3c1e10034060071190b0002240ca01840c4075000c0700085d540001c1c511402c40d144078400c0c2103050302900500c2c0c0507100c00c542000d50440300006a45162000610306842d580d1840148034211844081950440c401c90f0b0f02c7c0000684a03026a000700d40c070340c0c2070680e29621880100700c8100703180d078420300c1507400014903c035018142201695201c1c0d0004404144a03070318 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 78830730 1250 78829480 78829501
    0x1300305031902070c0905070305070c060c1101051006020d1701050d060e03030901240e041103010e0f030c01060b0403050c0f03071a07120e0a031b0906080d03060b090a030b 76
    0x1011000030b03036078400207200040020f400c00c4201511504130080115a641e0302003941140d00c00c2e91303180042a003a014807c0080c107a80c202412012651404401c900814140a03082d41e00c00e4816401305c0340c068100740113040e41027010f032044000b689410081c0001e006035110030200c1c107006460080d82c0c039088040512456401852108040c542165540d1800039015402020b004415082c05070244c5821089980362981c1d4005032a01c21026403840d03219035940d040401e44d080d03015501952101c00c00644454103102101d8900604409190740c3c7c030060710404c3c03c40740150000030207100305003c180049040003407030b941d0f5142c0584991700552041000a403600340d41d94031540e04056041155800d0103880800340c422035200304161800140b4003403090340c4201c0081e180b03640155010108201141c4480d1106a4038003da800004406072103460001c15201c064200d0042030b03004068840c001c5a26204050040c8011b0309901d0801c0b18860014200100c50721010748249141408a440b4850707 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 78831980 1250 78830730 78830761
    0xc0902160c14030709050105100e15040e0f06010201061410111603110904020d0b041406130b090f030d0e071523030108120706230130030503 62
    0x10802141812140c2d00e07451075040040790503955000b130240da440028205e11078003545040c1c4000500880b01c21201e8035084802d0300840070030320751008c00c2c0b0040281ca50340c030340000e10181020243c418410700e481d480003210074070007411047c11607243c100100001141c40100403129201103030b44203890f244854045418083d2182282e90324040d40c500c01200303c00d5001c40340308480c803518220164054040820040d000205d401030b4000c60b0511070100000c80784440180d10030720501800d010248168900b0340b40c01c0c0201c0e16000402c6100b225a0140300c4400c0e81141e008014600401c0e0304030559201c3c5071030b40500b4070403a15140e00c41c500481f0400702032002002514040159600030441c684000344407140c0343d142840740741d000d1725a9005408020f02100e0503541540b006085a6460800071485980f10f4101540d2182e96829100119840d04200d501d000728111403030070b0350354140150904400d04510018040d05071600f02e032404101d81d81d5020040c01c2e01410806e45940d62079405c100c0300701 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 78833230 1250 78831980 78831983
    0x30303240b030109150f0b0f040b030907140d110603060103110d06150c120503060a0503010e0c0405100e0c07051c020d030b010504050f0f040f020a0914030304030c090216 75
    0x100c03000c0784111008015504072032141506010a040b111410039030100c050160741500320204074103010700000c1c0b4000307000030100f4941241c41c090f611032007504c042c0c2013910980d00300e8110341c1042000011300b19030140c900e42e0032541c00351030b0a11641c40030702901d20390030b22078015075002c0000340f20340e1702a5201c0b131250714a5042840e90351504950480040c400d50085d441d10314040111800440d100f400d51003100c9a1101c091520840c0b130440507240e60300010700c0c880d4410700040c2c010505e030f2020b0283c00d00d4090300d040280411a940404c000503980010060105506880e9003000000c82d8130310740503000019124142c1d07450503981003090420381d460301c0c801d105d42840d5908455007640042d09840f0440c16503801c000000c1010011030b11132040303100300344e07001300020304441d107501c1c0c0020844040c10300140001211003500c40d10005a800221131000494241c0c03c0400401c001a01000003050049001d1490b26045956003d00075149000352440c180e030115500201da05480c41140038203 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 78834480 1250 78833230 78833291
    0xf060f170a0c140a0809061b1c0207020d03030203060f100e0105030402040b04050405070608010f05010c120c0c0b0409060b070b1807080a12030c02010504030e011404050d0b040308130507030303 85
    0x41200000140040600380c460096078410440000d5681002c8a243c10030410070200e541e180c50351549110031030855400300341d00227a45c20000a0700503941c0f140c060f0300041c440e03103016071a40b420100300030601140480703550003601d801d0307200c640080d4000c1c000f18204009007803090b280e88a13400428000d150a01001c3c0e0403070f1411041c4018400009115401c44a0340d44d2009803503a2034401500c0c40c0e010321f115880c0410150310041700054840030072541d0140951800108040c1a910348060401481d8000004544001000d2240c4800340c00703102d002c2e19282c1c0301c0702d151180c140e075a9241004024151070315280604080c810203501841420020400d410440303812040350b0134a00f4200325103030a05804203241190302c0504c24018040c2c28801c0750076441d1014038074440401900c3c100b001c144402080c210404c008982940c810f000c11455034004c0051411030710340740ca401351110300080c100100409600307240400007000094280c0580394146400b00d4074039040d20355011000c3d54080301803001c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 78835730 1250 78834480 78834487
    0x9030c050703060501031407030b010506070f0b07120c111005040807060501140a050f010c030f14210717150402090409030804021905031002030c090303040f060f170a0c14 75
    0x5003d11600218182c80c02000c40c5020039602c1c91380c40b0703640c0e5000d200c0280300740d0782d40004020314503280002d8000f6034015143e031810603402d903a49090340d51041fa609800316100c0e03030040b000c040c1c55101d801003504c0c4604000c00d031702c0c5500359103075a40c008259086404503207603400207040203142c40c00e503401160b01c260140000d50710341141c207400500286d0341074003441c2c1c41c441c0001c0030b10f040920b42a49840607103499000d070945840c00c070b0b1141c0d0b120080364180700640120a82003d030725002050601c0840e603c3c92002d400c246091a102d9401808900422a41c141a00400c032044c882154000c008001c14550070900350000c01c01a005198541e44c1c414500114101131540001c90603206a101322030b100e44000d040034070644d0700c00650260382e0b0944d1007400f07a2030361405103600031070f0800182207000d81004400000a40745a03c0340c2c22021640c6480401082520380101c0d031003000780c2e140d0403c140c0c589000500a42c1d2902d0080440c064282c480c010913000394052589220311401d4032964540c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 78836980 1250 78835730 78835733
    0x5031b01050402040b09070f1218030c060501080d0206011418040803040507060908150a0e0a050a0c050f13050a06030602130501080a09050a02010c1707110f040b0901050409030c050703 81
    0x819040b10182d01860410382d208903246008414940302d0302c002c0d25030810503101c0c1002110070070108a004c1da1070b540d40e000750519030008030319500b021522a42d03500607200181c0ca001000d907041a03000009a500480c1f0b411500c50300882c02c103040d00c2c2140c00c0a89442c107600001103030803826035030492911030002c0030b000038851520011446103000c0c60403915040e80d100c10840b58203616103c1c80e41c45030092004200c505e8031150030a070704566000804034104082d808081d040001a810031111507002c09040000c020256950324001d12007243c690858034142c4010840c000540c04203c103a4a50360300004d5880c2c042a88000040c41d0000411501c42030031901400c8220424000d06003c00d41d4000081c00c1d201940c0100c4078100e900001500444809a006442000b10a0b50481c2c030000310300031900c0c5040015025000340b5000b000300d0409151504144481d09094842c4207000700d08001c4140e9454660844540c11103000f90340c006103544c02414101c03803184400100614a0051060020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 78838230 1250 78836980 78836983
    0xd0224040b042c0112051203090109210203070b0403110109030f0905060301140904020102030c030a0306050a0e0912030a0b060409020301050f0d150203041110030e0c0301060303051605031b 83
    0xf620490310100125250038143c034888102c000d2480c0d24003403c45401484980d110010030910144640c0c110b4a468031480e60603186038104440c00301190f91744039a4542400590000022001501d0020300038000780104025107a21132018007420104d840707070101c1d041600c5521542d6a5180101c001c124a1509107801800c112035000780f84001640c4050100300d9240040440341291001c010b01c00600b04040103120801030004c0080c0c1c1580018841207029034018070007080300c2c00043c1c0d400074400740ac0c8001c0011415a5800000184040d201000740c1d0b00d00006601549002c0301c840c154480d0b807030090b5803002d400e1001e9510b401c101d002c500000e40c1c090035000b070350607100102e4001105d0007e4106102c4981c034030000c05401c100c10028404811503140d40150707042400b074a012404290000040b07020440d010002c2c00000e50b8512120b1907a9005000f8103080403400c030001c0c803206240d6203009020f07006140303082c3d01d00654100403004110080084650b01c5030000c0080110105070351403203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 78839480 1250 78838230 78838237
    0x7140a030809010e0f1903050702060d0e0d0903020906040906180308160302070314071b0b03040c050105031017030424020c060a052a010f0204091103060d0224040b 72
    0x2d029503080c44403154944002260303040921005e240180703107002e510350030265548004403040c2e01b804010000c00001d82c507848020841680c0500010440340d0540801c1072810701034100300410000307001010300050381d6003100560080c004507400b04d0420300c9401c1020003490420b4082c0c07811078550740350008040e040b0503180d00c00d01d24005080040031a00400360141d128102c1c00070b0015040901c2c82303406551480180c1a0305000f402052000d0400c06542050160290040c175802c03203022003000304220b00030f840a0007402080ca070940c10740c2404032001d010012175005000101c071411440000030541041502c000300601e00e84040e280d07828182050b0300f00c50305002c400040c000e5080241c07203800d080e0100c2d007040c60695103480c1782c00000c00c040094040301c410064409039105081c403c4c0303070809000311440740e06204e00040c2c0e141c1c82d01040030b003101e41226900000c0c0700c0920410500f42c0c1c407250411131150701601c40b2210302c1110b00d1149c10b1a114803000d508020f0002c10045a040c1128001d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 78840730 1250 78839480 78839491
    0x40c090c1710030c0510020f07090b1002010c12020d0209150306030607020307080a080901150303050910090806010323031809060619140d020301030503090117070203040b07140a0308 80
    0x1d020300c0b6141d011010011908078040034080d0f00d03980a0402c00c0782004803c189406040384140d402c5a11405111030403c1d0069110500040e00e80e030031040c0c4c501d0000d0b01030000740c3d400d0001f04a00d001e003540c00b801d0551800c114800d459030104103401d800800740c048a012250044c10f82080800c440c00000700d0b50001e4031154000c0c400c2c040003c1e95076000004859040750065151410000b081c04212444c42d8000e2501c0455500c400318603488484282c200b00c050b44c42503e5860310f84000d0418441003240e2610041c080080b403050410011501051460540c2d8000c4840c110031a20000d038015182e4558152440d9403200040141d0070010103061001e941c2030440b850199a1900c004120007805950b500c28182c500c40703101c0d20740241c010000541c1402520070110b0402107600300c1d1030100e80099005840d1030708001124510707981c0c03140030906203046209840c480740c100b0906c029540e000318081d0040f080000505503045c01070f0f01d015904109603d4040710b446199600d0001c040500a454 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 78841980 1250 78840730 78840767
    0x90209040b04110d0809130908070309060f03061d040305070c030c06020c01030506181b1b0f0a0512090a0b0d09021905030c061b01020415090506030609010509040c090c 74
    0x8098403451318a04414405030048030386402c000106040041401440d2680702406a6519681c400100810064070b4000d009844d448941450a4006412020f00c1855282011314002052041600040043c42001c2c3c184030070340450303581c41c40c0070b42c4da5218030400504882c098500002c04c1000200400050358803550039a40c00c0c100c03079030040d400c1d5042900e07240d600880180d810040710750f2100b14907900018032004503001e034880009a21042d8014490502e0341c030000c00200309180c008100141c1c1d42c1d5001801000d60140a131105030b12820500107401c4403a030001000302c034954071040c883d0041d200e800e01c0b0766560007500e00d4401c0100403400c4124015407041d001c480707140102100d40305c21184080c0240088049080412040d80d1103001540001c41c0d40d050280701040c070920142002d4005041c120200c500c1d0b285000e01140b880c0d51129104070020402c001d01610b80d41041811640e09668505054640d0314101000c0c01c01a007010401601c0e0001404c02103910a260000fa60176004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 78843230 1250 78841980 78842003
    0xc0503010e2b050912011409010e06010b03010806040803150402040b0405030c01080c0409020f0d0903020a1401020c030d0c050912010515030610060e010c06061e0b09030a110103090209040b04 84
    0x24240902d007001c0c0c10003240803510501078030072142003e8002c441041c058000015103142030b0082c0204220040d29000c800d40e647e10000b422030142041050f0142603241e071441e056615049255030b4900005100803d085030110100d1010350b032852007041c00d0300c80180103548030340d1a00c0444489800c5072254910a01c21101ca540703142d4000c400c0031b400741c6005030130145890b0a280309034010f5803081c031015034040401c010b00540c1300341c24400d0310328040c425800740200410701d050a280d240c403410140c00c0c107644104560103846800100319031400540c058081118090a142603825010304419503400c80742c40e41d02207018038011741c4503d10a1844603500c00d103211580043c075a0f02d55040380d00c550041c1040340c2c144911070185628050311901450300d501d007415569900016240e1075400f0400c2c8407a1151042c4609001c41411000b52204041a909240240c80000d58402e812071000c1c200a4141c60900d001d41d20a0700860100e81d00540149410b060902e0304441c170540885e816134101e091361 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 78844480 1250 78843230 78843283
    0x2210112060b1e040519090b04050c010f0f0305130515090f010204030812061f09030b06060703201212011e03020303042c0405010902040b01110312040c0503010e 71
    0x8000e951808610903000e600d01800f90400e01000700400b40900c40034440034000303103510402e98040ca41c0b80758460f00c4200c5003810180340843c90089052a0342d814007004038003650350343da4400410000308445203800310b1580c4583c62074440306a5820000b500034091091100c04421181e0a2140204140740464030301408201c030550807030156001c001c102c008100020101c41c20202140d5400c20001080c059170448040c220b050041c4403808510045180d0110810078400c1d65a11558008015034085140c0111550000e00711564590041c075410003064032040640410011100380a289a4015584501b0414000c000d01405d04c10310321442c4203204040040c01010765a0801c4981c040c0040d41400e0800c980640d400c02c0140c401121040400c3d4544130021400305400c2c0250701640000801840301c1c0180015940000b0706281401403070b040b400d840d40400811214468500c409000035515945468140485150301030307a4550b0070f090130701e54010320106400d20038065014a103404010b18 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 78845730 1250 78844480 78844489
    0x91d12041d0a18050601060201050c0715020c1221090304061403180d0e01030b040b010203030106050a05090901060908060a15030303110903010f06080115080a020402210112060b 78
    0xd902032403640700101070032a1070341809100d80a422009580700070a100f14822500340300c452240c40240d81c99442040100101e42c1c080c40b5054210301c0000b0080c2c5081a280c640809003240300150000d40784d030014842c40100c3e4144001c0020224000d151640e4242044000c6000c081060500b102c51210071301148048000004440481c1c00e180c903295528161f240c400340c07090f0402407105081d0500e1904128644c08144620382c03420000751604c5854230004800107045078482d10490b4001e52030040b80150682c0c00000752811910316241003603a840c0b511504903042e00985028a82008048002183c1ca640000050041c3d98014007118450765800c00f44c80c050382c7c0f4410019020304141401440403c0c480c1c0c2110285440300b00686180040241c0803e003118454400d031600566640020700441c4002e0003081142e180680700b801f07259003040e9465843d4450541c0c000c0c886c4c0e034000b51072130504041c04038600d2007140c030148031403096035280c180703801c40c1251000c121509444d2035803900d00e0707280 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 78846980 1250 78845730 78845737
    0xb0d050303011a18010f27150203090a03082b050609100f0302090c0c0607081816050d170a05090307050103050f0601030903020c060c0106090501050103020301050d061104091d12 78
    0x50384c20001c03844000300001520b42d145600708980401c200b1004805803180b0280c00c00e0050005480040c030350514110f0700940389060061140c0441d081000b00e100e03582e440c40c4041055035040f03424259558804604c102210066003c008507010b0852003125240080ea84018400c0d4001d4413410580e0b610282c0c444a089800c0c0070b08500d801078017030240094103041c5103103940281e502d11110718243c04040300342e1400c01e084520800290141082081600f1417406407008422800020310b05694014250b0420103c18065280144000c52a120911080032030100e2115646007107582c1d10640c401c00200a644010401030107441200c0c00040d055119108252103420910012549038569000450142c10300050503030846c850350581242d19600e61005042d24801800006101894501c1c10015907005a020b80e061620500042045e80c03a0b8a145005841c0e220078001410b000090101aa60040b13402c043c010a2a1003c80c508503005142c26081c6e00d0145c200b03d4010a8040c84020102e11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 78848230 1250 78846980 78846997
    0xd050102310e0403141917010f06030203090a060c0c17030126160b04030b0a050903030402150f04030b04051917090d05030a020a0b0a0b060a120b0d050303011a 70
    0x40c1d0711002c0203a4028842d12a810078440c0c9000d4151400004d4400c0e91078200d2017640500d20101981d48081542141d01030302c9044140b4840030941d071511a00300c641c04a60b110741028140c00100088002c4010300640f0345080e4005410013030b080ca03540c0d005101910340581290a1002c0c025000706004150082c2c034100c13071030741c80311183c000384031461454401e00b0044014498070640c5569020407010001c450064803c0a01c0e46440300e2641c00e0040c100c0700040c044030301c0d5500d05010701c50000008412030358081e40545d042c45000886058029881c440c20b030400750f001d440450301004020710550f883c0e020350700500c100c1d9806845241283c00e2840d02000003040c10305030305005904205c028001c1c180170b8000400111204500b515100d00f51b520281c1c0e10710068001c400301804100650070076503000140c0301d10421801c001c075030116500b40300d2450200180700091006251320b4042da004140d0000d409080b4002100980c82d03c25620341007030040140078808000c04003010002d28083d5981c20 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 78849480 1250 78848230 78848317
    0x10b0909060f0d050d03020c011113120c0312020c011101050603100b0f0616020306070212031b0c0a1104051b031605070f0c0509010b04051e0f0d050102 67
    0x3a11218104242c088800500c160449419996040481d806000e00f540e000f90a440159035100900300c01c0c0e08554122580866414082c04000040245000700c401900c542560340f0a82c45d20034100302c007400c041607100809101da4054401ca00b0303940803809600203102a00c5818522910f0b98065090b43c4044400300c3c0c141d803003605031b2101c500103a0480789101c4030140c08824050060008503119030300007004c03c0320f0b00c884ca0b01c100085080070888664400c00b203101625003142090390303482152001030030040004503660003814403c6400821030780000002d004540d9010356515001071028240714030070b0f12903031030070000841c1c000303580c102030b400100c00500c07851441e90f032114441d906c80d05600c041c5040101c14041440003500c40080710a00600505d00c040d4001c0c501810031000c0e0405030041e0036013000c1800b08200e2921681064142d0340071610204684c42d680801007031441c80c05680c510340c000034030038801e01444410b50041884100729042c581c2d1071001c1050288400c9242242c21070300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 78850730 1250 78849480 78849499
    0x50103050717190606021b0a0513050c1b06092104120606030501050c03180c06070f021203160303060902190804031b08030105040c030908160f050102070c0509010b09 73
    0xa80100b40c15584a003040a0030708800381c45860050884130980c008601590215004a80c401500b48a0048019080315030740e50050909005c12103540c40c05260040d100c1d140d0740414096110002540e00203c141500d00e85140c03041c86a0790783c0c0b200d05917a1503032107010b641444544000080c0d00c101c07600041c0c1200070716061400c07030824040d0f041c071303c0c058403050342e6106c3c080000745082c0240c600070114564a2074403420508540302c0e0042c086000700c1c41c4c40e40b000ea000c1600e602ca0000b61240b080d04010728000c60819400802c088051002c14014a40800184154545510312401590754000c0e0307030800500303807100a180e0072881035010904207001300303800412601d0720590303c450b44180311f440c200390721080e42a203002c40a803102c03208681070324000c4010b201900345882019004001807500340000302c11512240354500c20f0f10301c0400e070807021442d15824000940c80b401707180740d8404001c6540d540141485c0400400501804e44641d2940b4000501c442c1e00409450541c0b0740200030400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 78851980 1250 78850730 78850757
    0x910020a0210050d060b0c160e0f06131b022404020d120203220302091f050618150c01180302030f03101d0118180212010e0601030302070f0501030507 66
    0x10f20f900600c40d5580b415480d070002250f0703d0545000382904805400040c946c8030082080034103a400c464010030100402c3c6820071880070403a09480360019800c0d03600510b00c0c55000340c00000f03040c1c1c3d0140910506801c1c8040d00358682d002841f40c000848550080800300402140b44281d0f19040d07070069803200c403142e51fa4010603e80c0f040a407440c605401101e1421442480002c200d02c0d4046034848400e406c81420015800c1100404d03620000070308010460041111101c91030702c600d8010769024201c007040310075400c001c155207080030f04401094420b040d49600304080c45940b0003400d20b0300c15401d0a607085420301b503510806203820741c507401850814007001300101c2c0b00d0b040208003000803019508002265100c203801200e450400e4074000d000c540c18403500341c5074200400000310700203103064800315480050401c40700301c2540c1102c608070741080000610f40500b5a83d00c8000d02401440c00001c10150009442400c80d41c2407070b1003505680c0d0300d00041d401c9038022070380038012039800320110a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 78853230 1250 78851980 78851987
    0x307030218060630010f050306150f04020d02041a0906070f030c080f0c061b0d020d060b030108070305060703020f0409090c030507060315150f0f0306080604080910020a0210 76
    0xb6406440034041e6810250800209038401d00040034003920340b445080e10401009412180e2070240c00c02c6241e07500e51b03d10744070100c0d90f80e103002001c4100d54180500141040e59440c03407480c00301540200255110403102c0344101c000c2d80701d40704004002c0310741d901000c108580c0e101901c0b010640141845d050403600d07200c00c00d440c04005021000c200c00c8040010020b060500601715146400c29102c0e22816003104042c1f03010030140c41d40e0080b80040042000c1c0c4040001180c0c0300318450308000d61a0300c0d0040c044000b80020b40c2001d901400040004a450140040c41c00100d03802801100c00b00d880754071043d0100e00c50300d000c150840800304814810020b00da00300c800301d41d01c5540b5110000c2d50701d45810b420710782d80d9000900080d84070590703406144442e017840000307049600b030050045540001d000d480e05450300e82c2441400022105010041c0c040e5200f800100500d80548805103001d1510140a51082c81e0300f601c40c20060b0760b4428105d20000d0800701184e03002e0102c488050700c503417094 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 78854480 1250 78853230 78853279
    0x2806110709060e0f090c06030105040f0209090406091205040501171e040b070f3906090f0204050c0304050709020f09040906051510140d0b1804020f03070302 69
    0x5800920a622002455100c02d1103401c009000740b0300c0e851000d04003110b5080d40c3e1500900490f540e9070048118450301d5071180d0440341103d02c1264001b5203020300c1180c95000c1c0c0a80300205034070410100030001804902c1d00005401e5201c1c4000c80c04a5019007015200d902942c0101030009141c81c0c1c44003814005460705130780099070480d0610300b07448040d9400c86040d00849049403681d081d0824050301d00c1c1c10000c4034580030600e04056004900c0301081c0c14881c8141d01c0840c0d01c104087d54005902135040504016154200030705010680035414401d480c82e44008049004900d0400000c85000c140d0b000d03a40034540c0000a058000e01e49940503010350050301500c00102d0040100c024150b68500c1043c1d144d41c81034401003218a0f0801001c07480125070700d05103009040c610038100b2750307542c000003070311b01041840d840c00e441b03288400003400100069446c0c507400c0001c030200c40048069202c0b40350700c554421185c1c1d1b0034203104c507028140c50300200d00c0000d4002c01e900300000450344c2640b041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 78855730 1250 78854480 78854507
    0x6050309030a0e040e160e010b09060d09060b15031e090a02011103210103050106090b0108072102040b0904050601110703031d18090f0106030201090311130c09052806 73
    0x401c103002c4117074010703041101c1c5c8003c1080981c1d000380100312401c0b04080c1d803070040600850060078009114003184d043d06c0342092100d03010756280484000c02003694071014028501510a41c50843e46080c10502548141d5540121107a8800c440b0164914400074500c01c01d10603020302190b52a51b401503c80b185030140410150106100c6501400003510740c40c01212103410200c4100e500d50309009003141c1c01500400002820303c050303525940d070131a46580d0402424a001c41d002c921000c6000c0c07140d440709002403540e50001034000344030500400900a00142146c0030041911000015a80d40306d1201c9100c0c181c1d00b2910080011030b024030104c0100c1000f990300805007065000c0010710098194070722001d10200c05d810b00c03920860800264813201840b02c0200b100383d0a540002c3c200000c81d1200500944a101002105865590748038040591a241c01d00c00c96016500c041c100f240340d8090300340646400c01000200407190940601015291250800840c0c10118119014501c2a05 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 78856980 1250 78855730 78855739
    0x60e070b040b0d0636020a0804080706061e090e06011511030405061303051902060301050f13053d0909080f0c01021206090601170907080f0a030906050309030a0e 71
    0x1400a00c442c5c02185008400240c07100501d01c1c0700c15404d4018a01c840c0c0c0200d612280d2050003038244030754102d684507400036080503c241d2502c840d8500700002e0595608200f07613444180d01d40c800d0807455404184242d42010b101401102030302050203a80d000244a01d2800780d040120082265004810180e081c5000c0c0302500d180c5038803a404070346251f102c40c0032030985613401042001404014080f83d500d90101c403040c40712600454001a1603408180a202d104140100108ca06507840c592125071501c6101801d020a28007070501c0d440026031b0110507062009450b0580840d841c0562508d00d411184240e4404aa41400d40e100010084458112408001045030000b04440417026040e1450b10200240e641d0010a10143c80460054441c5d402841400b0070301c00b540c2c5c6c103d00c5900920b810034079420a295100000c50f45010070300c0e0310244042c0503050340c0341600003011481051550194a41040040e40c0d0402102c0c244021640c0304041d8009100c800c010f24130a41c0650001d090092 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 78858230 1250 78856980 78856991
    0x120b091902181206180304080d0e0a1805090d031103150109030b01080705040c030e0c040902040b0409060203010510170f060310050c19050406050d1d01020a020307060e070b040b0d 79
    0x1000304000a030710162040044d0720600c104215a034810381c030703201c1050140c2c01031824286442c0040e940c480b5001d41040510001e031220b002d03252204481d0384000c04442c81141d4814110342540c0c0010030040e140d440d01c6003c0c041805454038003e00070b5981e05000e0003030003869541da03a08514120224207603580c3c1002624140000800d40c400c641d41c1c040c0c0250700c041c140181c5440200070860f00100880d000341418118040d60b8840c01086e550244079081d139011030581c03100d100150041c07029a1103190b000e80780412142c02c0c004035601540c1610000c0d61111854089804252031079001425160038034404c0c000001e034464071710f418903608510050201d80799803006500d8003003500d6049410840031080800c440c00481408808080c680035241001c81c641740c148100200350303210301e80c034520f034041d100c1c3c4041d41c9504148408914510f2000003c640320350a20034000e44a034003ea0b03047c2c60304c42c1442a91042e09401240c4542141c00030f01265240c146403c8443ca90b60b0803010010079226500c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 78859480 1250 78858230 78858277
    0xc042d0302030303190605030c0607060209130f0b0f0405040809060c030906040312021e0628050408030f010f060504030b09011d060106020f03160206070f0c06120b091902 75
    0x1000a540101d030618400c507017414801940004450240d0b112511030f5020381d0708044581c035040211aa019006000565035486a40100d182c000d03075030440340d00c01031801c4a1500700d105c040e41b08441102044900c280040011420007081d18000e941c0035100300f40c20061a821071170010028955040301806a906000c84640007410541141c1e2040da0b09060191b88004000e9042c8951001118403040c1003080009134201c90303595007401881030400081051060003420008480e05145843c100024400382c50240f41803c406d4209a8440c904111068004901282d0011100c0300b030310402d80c2e032241410315607180d0b0345600d580034055005655855a2540c04440f03400c10544001e43d02ca40180019450140028500f02000319982d505810a1082003203401080d000c1003d00c0c0d40444d419030f2550307820f060009421a00e040000c09035a00c420740003541c190013000000003018000300400c14040c002d4213110503201c0443d4056821500308540d407074070740006c0c1d0280800b0002e00e0400c2561180c1c0c4c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 78860730 1250 78859480 78859483
    0x602010e302a0105040c0902031006030c05040801020c07080607210504080702130c140a08040f02031606091a04050f01080c090607050307020a09060308120403051608070b0c042d030203 81
    0x5207542c1420a9440394100710078001c540060794010301001004525500d8103000c0541e4107841401004109a195503051581c80c1c030030300c251809040d00c13100841d0389100e0780d0499950740c00a4400e0395941c1c050f01c400525107d00444000102020060030303190040e10b1a8108001803600400031aa052400d100344c1d0096200e030f504ca12104030030218009030b9030303a0032038000d0114000d1500c1c10035407400030080041e03c140d0156286805c80c1d44107081800038819840000d007001e000040b10200c0101235040040c40e45d511200c55400c0781c0b034500460f9a03e10045194800ca440340d8011150800100000e884040d40b0a90b102e980c061218a125170034801c0840010702558016001074031240d00200d848029464541000c070000c2403001d904001c02072a698401f101401030300041c1c0500e081d6000042c007032601a1003294801902c441030030444a002d840c107141560030100042e00e48540140c000b582c01e000c804211342c01d40703008010b01c0c5088080411a0b0f81044441c2c45400c0d002d9003404c4000006072070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 78861980 1250 78860730 78860797
    0x90703061406010810140d060f022d0f040e100b04061d0904050703030f051e04030b0a2022060512090a17090414010602010e30 56
    0x7035011020100d0030200001013452002401c0d1110010002030100020015410403140089007912a92559200b40c1480f5004000340118046501c0c00016640c1c0708400c080140c0345160610000c00600c2003010640b88028000c2042c14021304a0810052141d2400c0900d0b540d400109583d861502948800000d60385403c581e11120124500c21002c0182da03080380000141700e0810780d070300705072850581c40e510707603400e503511014040c8112000300250f800e00ca007003100d41002d80c5140c1406038400240018105a12510060320054a81d6000c902918400d0159410035103425a042c00409820f010030320140d03011580101500c004600b0b00d400003800b80a0490003060551151a1510718500d0b0360840000000c040c55183c2e0000d450b400009031048014086041c1c941000c44c1d11800d203400484c00426400303400d2030001d0525000000c5042c1d054004048400e0401c040c0e07245810384541603002e40c000e0440046013000c075280303070789601c84000000d417020740b140d14000e000c2003d059504441020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 78863230 1250 78861980 78862001
    0x14030a050f0706020d030e10020f1204050703030e0303160b1f0b03040c0b030115080604020f0705010902030d090f0302122d06010e0411130b190302040606020f0304030b09070306 78
    0x4009040400c0080c0d0180105c45008031942800d001c04500e070b1f001c40b070700c8824181e0320024150b408030303000c60303030f681e61070141c40005000d800c0ba494a801c2c01e003801a03a5240d00d1000b20000340030b03046c0c00c1d116801c000c400d40c2d45034209002100e803640490f0740c5401602c1c07402862040f040300018081d90301c00c81c0303040c0c2020080035041d404981d00d0031b260524071080d21598014010700d1104000401a0401860042d8a0343c00c2c107181a05546c0c550b800041c0c064811101112441700e8003040c00d0b801d2040c190302141c1690310071400c45074404000ba030141c1301001d5500c074510704002000301c1000541410204c000d06541424180d0b41d080303103c1001c41200030030b54541440c4000c0c54843c03803464a01c04005490140044001d02c0f040d5240c0369488036020400c0a0449001c2d100200211807140403e40150032030f44802030054504001e2050020b150240520041e48941d00301800001c1050020031880522408a4080c6140c1811900d0b0000c4410300030f400602c042c4212040080885c005102d00800340 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 78864480 1250 78863230 78863233
    0x2040b060d0b1002160b0901051207030506010e03011e02030411040606050418050c0a0c052107060605060c0307020d050f060109020d050906060307090903050909040803090601090506060414030a050f 87
    0x102c042c2050115105040305201c055510040359a01c07100d441c40f20302403c0741d05a0020664490014004030380c2401100260000d441030301080c00303d5260103800240c8281000c1c0d076442c0302001004201400e880703410003031411043d900307903007200c100469800441d44580125520b030011001d0a000c00c0450742c43c0d0707000350001000030405200d40714150507000c50130300104d903041c0140e09014a4400041c031800c411541480080c5281d281004005d015000d480452000c10b000507031281c5800d0700e803591003003d040300c11501d4480d002c5010b190490650b02c00c07040302d00003981843c0f40e540c01d100240e030b01c1070f00030354280c4501501c5502031001003101d923018161102c405038464108207410415240013400601241d0001001c0081c0c40d240050f5403401c441034110701040410882c107040e00d5912681c0241504100e800c0100070601c041c0c00c0c0103501032035416040701c034181c0c1c1c0e922441049980a913507c0e5413003c000c0000300407c1100468a03001c0b180001d00340c3e070785e40186555161804800d4250541075 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 78865730 1250 78864480 78864491
    0x13210309081303020907020d02120702121507020d090e0103020402030603070e041203050105010f020d0f05040810060f0503060103080d09020a080607020c0f100203040902030c04030c060302192a02040b060d 90
    0x114101700a88580000043c0001c01c4041240400651140c2507050082848800805c0e001c0540d610701c03204070001d0a0150a0300c1c0c440c82122668030600380200c80200161050203080c0c00361a1051140304212140e1515008a603401c550801010394000703880c5644c03612900038086400020418100d001e54458114420186440c0c00040d040d6503059103c9414001080c0480c1c900035004903001ca1420b00300e182c042c080314a0800113640900983d0801d00b0107200b981c0904010243c0d41d0300c41030a40c2c2420003492151580c98007090342c4c86409010050030304005100c4180c03840c000341c100003000d034801002d42401944500d074892402008480840040c0e00c40c0b804090310341001041141040e10076150030340f00e41e035a000702950300d10503441600303121940000040c0c0114000802d68000d503900104124055540c4e03076005020750410070704069010202880400d905019402d03d450340f0010b01c6050020310401002c4d1034800a2450003039800940300c0889090569608004107802003204c4c900054 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 78866980 1250 78865730 78865733
    0x30209010504060311010f050c0a051011030603070b1303020d06050f0708090c0904060b030a0c0303090b03060d03030f0b0901170c0f0108010e0405101a030613210309081303 76
    0x40804040c1d00c01c034041c900d000814004508a80300501d2035140030708000e03074004294a0121500d1145002c81e00460141c120107200b0000c01291650308002c0100e41445480355034400201184410344d0450783c5644040b101300700c00c50740480945a9014034140c60040299281c0105031646401da1044840703603500c1080120421031190815000b10f0030780344c10304051524240701c83c0c4c0d40c180100001d2156010b040042d080100503007154210381006002c0d50704c00400c51400c1c100d00a0b144c04202c000c262584400314101c03171400c060768440c0318003c251258103c00ca0f2403d800800700d4000c2c1900c0503490306240c10140c0c84039100540240b000b0710140003404195141d0b5410042c04d4400d0b18070502c2c0402038440700703a9100f140e040c107640683c201200350751120b00e00039241c8a41d07981c080e81c4d440e0504c401c03040c403800c40100762440d6880980c1900d0340740c0d96a0040c00d4403039210400062404010400020359420700c20fe0006a41d1040d0400180501c11511072180c0f40e0005811020b503040d54110510 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 78868230 1250 78866980 78866989
    0x151403010c0c0c050613030507121e0b04020409260406020d0206011d070203190e0a05030a03080f1314011b08040503030103120309021009060e1002060a0b0126010302 73
    0x86401c01145480c40d5582d04030b40d18001c00c0b030745501c1800d00ca4040414901020402c03820080b0055070320004644000e561214107202c03001308418141d40d00e200301100c51000f160180c80d03014020b540129940425a10396017080000d144140041c1c0300c030030286440d020b0102c0c203200c081a1035590480c0907038545240a90007450180c181d07800400310b400c400c00400c0303000c800d100000c0c9003121070981e212480e5101c001c1240303140203203003011162014400030500f225800901001d201c00c0c0a9406995040e1144103043ea54062828002d0005101800003001d5109400c0210340017143c81052020f00b01c055101d4248a41d420000044c15035520841b12030300d5210800d03596518182400d20f04146c0c502921107a403240014070018040d8001405d201903000e120b0f5009181060b070080125500b60070a5200134590724080c0260804201c6010700041c44e0702d400c6c070313030351580e4001c50f8024002640c4003d00c21000d0072404074503d0600021181c02c0088408120009005140340b2241d020150302d50300401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 78869480 1250 78868230 78868241
    0xe0306150a0902090102010b06070c0305160b070303050619030606080c0d020d0f05070b0309010207050f0c0303042601050124142709010b0c0610080606100315140301 73
    0x34080d4650082124251035900c9541c040780ea0031080140c5406040c00181c1c0034000c040c40c0950721120014201081280d428003c2c02560301506c1210400e900f480c3c81680c18900900030401014010b02031940064400e03042181e0200c40909100781082544800c590100d2460b003080307c21070b455070340a2164110810103855883c0c01182d822107041429004501c504c10304100251800e20854100810701c01c0c20401c5000600840a50995a10740342440c1d500035040098104c5180c014070f51802d01030fa10010711400b100c640140550b10342407500000d2541c0013031004441c0310001c82441040d58441003882503900800f040c40328020b00e540128449003140100f008548248001d44000c000031180b100d0540704041d0528015596402071611440001220100084e5112240360000b24200d0400405020700000c0d442c11110640c85a810b0f1030340070f90b00d901030641e0a5203d000001d1241c64a403000c001c0001c9036060019002030664104140e50f402500010259032480e078a166076801d00f440307013 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 78870730 1250 78869480 78869491
    0x1503140f0723090103020a1a0c060a1a04060e0a0b120f070312020f0703030302030901021303032f060c0304150c0905010e0d050705121006080d08010503030a080610110d0e0306 77
    0x1e043c1d43c1181c2c0040d117014250700807605a512402054004201c045084078060560401101c070985081b55008006d0456075040510502c1d22605201150503e40500f00640718a48644030b04c50341c031045a4801007600703824682d406110580304070040c2c00103024800c0c0210406c00545030550442c2003c00d07001140c8414031045611280c5651070703d2030f0205460040d07a91510f800741c0e60b512886156406400364400010411644040010405410107250300749590391701044c810500c0101d410500306c1f138403014000c0064014400260200710044000c1d58058440d003001941d20034000e8111040b2000202c1100116803e040c080c0000e68000e8407212407400e045a201d540142c2c0e599078140c40d20f481e8410b450140902c82c078131030502d200500000f13a1810b0042010080c41e5076443c901d503600c03050200c00801041c4190000708003801d02108550390740b1050384a010140c1c507140103218070900d214000100300b00394030821016060003803001c00800811692612256a1800300309428200041c04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 78871980 1250 78870730 78870739
    0x8070501090b0702010503040f022e0c0804050d030201140a050f0c0702010507200d03120e0307020603070804081e0c0d0e0d15020d060b1c1503140f0723 67
    0xc1002140500c0b411511455820b1901c25202e03121460412030103000114000d45c00716000307918201d03450700b661215080c01400c0501c0c540003001440d043d074221180f81d0015003500c1c010401805541800300102d5102c03403183c4000605000f000c809200d103060162080ca01c103a0325101800161a4400e00310f5070044c60101643d890061640d0000e00b4502c00d4000040240240f81e403043c1158501c0070391041d82c503101802d0300203404c1d110310700144003165403003041d20550f10705103808c0c11064000060710500390b40030b090180b6544880344140c0711000010002c0355244000c00c520601011000c140c803d50000c1d4007107640c0c440a101c1c4819082004204000080116491510450382e45840341d04124a030014940071886000d12200c6000e4459410008015030404000107a07005d040001030a1210030102d030f01074a0302600c0c488e2400da88440e004040030001c08102480460054020700125842d000304444042d681079600e5400d010180c0c0c42400c0380c00791010481c8500c0c40f06e003500c140f020303000c94 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 78873230 1250 78871980 78871997
    0xc0d02041811040608220506100515070206070321020d050a0b04050f0a0b010c0203060f01061107080615130f0606090801090b010902030c070507140a14011e14030a050108070501 78
    0x70082482100034424101802d84905a00460141b43d040034032064102040e035844d41707804504948010302c54860395000301c21080f440d072440380750003007500c0f20b495000785054580140ea0714105e40c2c504c41c0c10184101074030074801000144d6158070042c0704144883c240820b0918000820400b214500e180c054011405d01c000c10080028900da0168000800b01001078031901c40c50049800e004003440c000e4042c460300040c40707424070b4404030241c101d4041e9503c0f11400c404200586480e6002c620565040303500520208904038094015a000d00034060300081e01440040d42441c10344603503000b000400e40c1c0d514410f126203030380040701c42e0181040c1c030024401e0280554504040c0a014071034501155070100208284203407400c03c071040550490100c40718940c54080190a0040d10790459105000b050800543e40c552040f02284508050f16140c02064980801114200030f1030205010824115105003504c0081e201460103050b5108000a296043c600a5860010b44d90072072410302a000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 78874480 1250 78873230 78873239
    0x50a0b07031802041a060408010f0b010216050904020112020703090501090503070b0403120e0d030509031c0206130305041e030c1a0301090e0705100e03070609120204050c0d0204181104 81
    0x21412101c14070b40c150340c00245000d0017440c1104503112070a1075a44803200240014907800305410003d0a1901e208040040680b03a10041e03075900341000c0f102c1c01324018940704001529200c0714490f4001d006051555000c0b488455200c101c0c0c1c00300c602200815041c40090260b541c0c45200e40b009040b003600100102d6081160000c2c96018074407000b0070345032041d0000030300144141202a03c2c0c00015141581c042d64924029215800c110121802803041810807030306106425506010041d407078026203010f40341d40c0f5101450610b154070540c240002080000307410a183c25401e80180c0141c0b4000c0003842c00e5203031107600c207940b0354400c00320303815142040001d000103102100c0c1156107055000404a1a96401e103083c410154003255004000d180f021000ca42c005418400c00e050480a841e1026110b2000307558200040c00746245803010391a9590040c2410750010342c000c682d1004240c02c014070000c0c3d80c020b0340d20a40008400e102c0980b07810700030110b00d000f000c04903c00c07958800d0405040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 78875730 1250 78874480 78874511
    0xe0703020a090806280b03010603080d051302090112170c0f07090203010e01050111010e030a0e040509010c0e0f0a030b040309030c0801050c16060f0504080c0d05040b0a23030103050a0b0703 83
    0x81c3e114170304c54070600c1e020100150315503034031048140c4001380091021554a090800e881d4214100f200620b40c04d21001030000540c1850f941c0c0340b1035004001503400c0c1d0800c41030070300c100503010b412a0603c0000100141c152130311405040c650000000038805000011442824152140d01c001036060050005000c1040c210110906542081c41e2010700d90801d26000c07030241c65030440505080c00000b42140a441d401090411b8061003900c0034407144d101c0b031510500325291440035000003520b03000c6c000c0480c80c5c018100d984000300100a091440d480741c461807940c40c010740c0c0807008240f06040c2042001031401d8503000030001c0c44002c001900d00002d0b442c029200d204429404803c4405c007000400c403c592290b442074025100410061906103070203c3c503a4800280d20705284200c0c80020700350f5120300200c1e800c1c7c5409181c41410441c86c02c20544e52b040d1541c1140c2c2007a01f80c51400300400a003040554025406140205800403460405041108004d84008101420440c0309844a4074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 78876980 1250 78875730 78875761
    0x606031113290102070e01090516020c030c060901030e01060801060608090d08060607060617011d01060308040b0711030a080d050a05010308090d110d0302010204030209070512011406040e0703020a090806 89
    0x1000c1c10014260071201c40105c1c140b0310150468a41c0aa0010000c9640110b035800346100d010248414021044040d4080e07941c2c00c20410b906500d80c0c003698948880d418004080c00b0000303418100800c482a0003001e5a09603034403904800e1060b075441c002084030760790044542d500011080c01070441010b0752100141b84001c000c2c41d16000d480300140700020412070703610240060901034030b04018040b5124089020b03081d45060304400031406030703034010151418411542142da002e00000d00d0a440d2480742070658103d000d06664030030f612110582107031014047c2c03120043c07140049503501c020122061040710400382004880928000060000070000d0046502c880e40c211a000d10800d400e14110440544212405401c600b0001000c41015015000760091724403c8500d211039540d1044102d98074081c1e20304030303000c43c808240100b0824400f10b008018000010780080d10b469140d647c9400015400c0d01c061002a0b80000d264683c41d50002c0d41070050080f0002410f00e50800109019201c1c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 78878230 1250 78876980 78877031
    0xc0c11060405033c01050412020f030a0c050f0609060703060905040209040b3304050109020c1e030906040f05030c090f0c0a090816030b0a050606070f08070606031113 73
    0x413031825904500d0600101d0b0b40901c0c200383c601ca0130350030802d1409030702030502506e040b16600e0311800d81c032424030300106800101480c00e10041d0f042980b209022241c00a0021090f034060041c40d6030342c408508240442c03841038018600500350350030b0a08005045560710b6001c1741e001403501c4180702c0181d50700d0480541254000346141007980303880c51580303010700001d118400c80e241c940755100f01c5c04c1440c0341200300000c002c03542000307a0785c4d9509004007079104040340c40b82c507034002904000360319400089411904403007104480c1880500c83c08030b032003a4020303000090740f8103100d0820002442c04010340d280078802a108040c49040030f140c0000d04040143c0741000c1000003180766030086220b101d00300c00800303201045031100246491a4015000d140c04265113001c008000118680344a000d0303030340a400040d00c06072038070080d0380f1342440600c10190100c408080030002000401d8203400750401550242a504030710383d40310402c00684070146442006800d00348140903d214010440e2400b590 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 78879480 1250 78878230 78878263
    0x102040b0901030c051b0706020c030109050c151902010603020a15020d080c0f07080306030708120304030818060a0e01050603070f0b182d090105030d0f0905040c0c1106040503 77
    0x40c103a56005e8130b07039004407803641c0001c00006042c40300c0080005501e070205c0e40d0a4081c1c402247c001014035003a0340245001800035071099440802d036081c24040c4074200401c0308001c60a10681c0007819040400751140500141c2d1220b2040c02503240c4801400c0041c07114011142c42c150504034040d4950070303010315413030903c488c803800540d40810002c21610802d0855110350340e11b2490f8505503400303400550b041800b13403003025400300f0f503102c0014172480034020850070903042d9030320b59400f182e0203d0024100c0c08140c80a5964840c0342c94100700050050032440301c0841e02c0f0400c000460b0031200c00402c0d00d41f081e80b00020802c10f40400305580030645510506013030380c5113115484601c0c4007480d0038405802c400d0940c2041420900003040211080c0e6489404010000b4001000141c80c000e0007185c0d0303d0340240710b11240d81d90080700340c6a4060002d041829440342c1d2600020202c4c0ca08203210404510300c0c03d94201040060218000140070803900c50b400c0c1810040866521402c0040c02c0541 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 78880730 1250 78879480 78879491
    0xd0b0901091a040b011b0b1801090305070602030a0b040e100c020d09050409060219080a0509070302090c03090a05030a030614030609030406050c1015030b13050c0114130e0105120102040b090103 85
    0x3c5e440345e0082c02c007084469170030400c24545842d044140703503002c9843c00411084c02c000c07d035410b541070190b03110050b0540c0e200c0d800d0040030344801c4000c0d403025118180c0d95655000384042078a450041c040c1b0000704101421904807843c6050041d10b141c110f0301c0d400c6402c025100b210460304010702c0004e4400580e000100000701d071400350f0080c4101c488408120207039039100300c0801d5218003140c2c45800407540903c13140d181c4000325544c41d40380c0e0100a6001e40c0220008940101c05806141d010341c03008120785102e0f00e951269800c56024800260001e501d40c00107001d14102d0141d0003440540540041580785080b0402c40d482e8021809510204200020340781d4190300c0800410900d000e40150400134400001400c1b00c00903804d00c01101d08244200015600d41d07500380649030840d8020018005003101c0f540110303082e01c1c40481d0600903030001e10540c5d809001218001c1d0203420311081c0d180c1c040d4103102c05c1100101d030311441d524403680100f1090000c00394817401d079086c002013070902244 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 78881980 1250 78880730 78880751
    0x31407050a020f150702160305060403030f290f0d020616050717070e0108010515043305040506060408031207050714070501030b0406050901120311030d0b0901091a04 73
    0x100b000710b0f121140350b446502900c42c02840d441400c0c034044c01c2c0c41d400f00c5821014002444c2401c248602c00034181d0707000900090082400380e044807030403030903c0c071000130190031040b080c0c820005401300703540e809006040e00e000d0358209101002c80311207088130840000031081d40015410b115860840d204c0c90807074144101008002c015100250103c0c407404140101c00c602c2003517544455109807084000000c00001e1030b52018030809024250342040020440c2602044c03001a01520800c0d200c003400c1d01003208007030740d80d02c0d0b460070525a4200103000f0030782c64001007201b581d0000e06014400d8200b00401c01407050000704645912100b4140806159a0600251020b00580c80050520f41100d400810721640200c1c400c1c0c1503403402d8904000c0c003003a41d01400201d40040c01580d802c07001d508010f002e43c2900e8503113484014404c1ca003580203261040c6180741190003004801303200036200c451071005450701a148038054580c5800400044841c5c19401103003103062107100b23002c0c940c0d8806240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 78883230 1250 78881980 78881983
    0x40e06060c011d060a05100501050711012604150501121e0b04050307050106060807090519050d05061e070503010e18070602030d151a0d0b0301050403030209010f031407050a02 77
    0x110600f04540340000e0b01c8020200f0942c0320711040f00d0603a086481c3c04001003500c107410981c141550b0040e911113013003104640d1040c0084a0307a86000e07051103170403111030301101c03011180300c0040164042e8194141c10145013802805031158004800d1504000c014801e40c2c1182c401c1d00032264000e42c0341ca0544d2601101000f008102071009040c181c3c1d054100014410004020010380344201c000b0028160360740402c0340d1038030054920381c0004078114010045460085003c00e20000c1c008440f0260079070f1440000d10001c0700017400c5420ba08080104111a40e0a401e40288180407180728000ca1030900703c0200350340b00501801900e22504c0d40414074891101041014440780c00d001c5511680d21500080d5480d00004404c8550909003842031495081c2d40e0a55400c58004545480058118080c51a499002104c4941d551650381c00844030039078090040328040d40c0030f80c500680c4d03240c0c1c1e1000113011070507070200e81041c18104200c006005a0003014594040303207919003d40c5035691307800200d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 78884480 1250 78883230 78883241
    0xc14180a020c060a0b01020d110606010c0510180317010f1205100e0304050a05010c15020f0c0d0302090108131101030b0409020d0b070906090e071404031505060f0303040e06060c01 79
    0xb0910310403401000b0305041564440401004240c089843d00c4100704811650000480c0740ca07011504401e010070260350040c000c06498501c184140c40507080c0b40361007801115041d60840d0000c0d413858101c04203043d0070207108440c050342141c012141c1e60400c058a40b030301e41d603480740380340040030714100c1000e11005011500ac1c1803800e010a101d0040c0851701d441d501e4000e8051644a000e261100040541c066102d00104580c40003079843c19483c0c12031100c1c002d400001348c07081121010000403146c01b5040c456052641c1594900603194801c1d00b0006001c070000800e04052030740414011000714041c080403100c01031007440c02240115610000c180036050000b80250070141c0c500d6900100041d005120b0722982d00d50b5030f50106960f0720070048454454a02c01c01c18251754101c08a04600e1007103021040010000022130300d0a0350340c0d81c0e40e4001292214208110960ba0300c144a16450301182480385031320300320001c504260230900240880d56014221030302c1100c0c00500e4110459081d0000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 78885730 1250 78884480 78884497
    0x106080411041b090503010b01050a021903021905031903020901021f0f060902120f0402100c03140d0e0f03090604060315050303030403050d050606030f0f131704030c14180a02 77
    0x100b051080c0f4020002d03241c0c201d1409001d00c03075402c280003403074154444e0003a5144a00c6950041c12000007852500c9188580da000a404500030540c94504900300756008408003845a030096613104136040304040c0c800500d07507032441098010045000e150313a000650814410b95060200107070746c140440c030300003889000701c181103640c1000400100110715501030214106a400852026030750140380c49140b07003048500030f5203c00089004200079104048030079405119003008007070700100700d80300034a540084070303084031940d203032903a200c81090180000d03252403040320300550400c01068001105409a40106001c143d43c40c5000d009603503031402c0407401400d016041c3c0e80d40e800d00741001410356002c600c042c0462801c10300840c1c5a0300f46802260321801d5007550643c4640c440050080361303440084c1c02c40400e110312840c1d0101190500e070680901100d00d0036685d540e9880c526004000503082c0c2e100310800841c0c064600032030786440c0b0388541101c0942050010320b0740d807400b108000380912010b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 78886980 1250 78885730 78885761
    0x14071415090307050f01050c160804120c150c02060406120204151e08010305070603020a02010b1206090c010503010e0105010305061203030a0221061503070c0501050903130b03010608041104 83
    0x1d0000d140c0010000300b401501910560300c01010040203207003664820b90341461790700410000c0e0b0600c08810410026014450b400c0c9034506130b56107520129100e008141a81c00d0b80407001c040001c1d00d024442c1c41c5482c01603041a401804140d000186035000d00d11a20080c8030224581459218140d4100c50142200d014540d8005c007440780300614042c0c1c113021820035500800c01ca98903a50051010030f040301c2c6d0100003494002d060000440281d0000e280c0101999200d045000590b69807040300410480710344010444c1d403030700480181c5840c15060415040c00010001800303404a50281541502e20a080101d1162940004160020406240000180030120a00669403140d07001407400404884160101600145440e030740c0e5101540e0141d8814064880e0003840c3e03030540080c4d0390061480c00d283d084031040782c0702d980c25940d0031560504550400030389001001407440d607031001341c0604070380f007800c42d0b041500c0501401f20240018001036030320300808405946607049070324403050524 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 78888230 1250 78886980 78887023
    0x21501031202010b01020610150e0603040506060907030c080f090f070f0807050f0f010f030b0301020c0319020706020a140307080a0807090b0306130504051e030a080106140714 77
    0x81c2200c41e00c8601501100550030300d180c0081a42c800100a030103004c181d407880e8249440c0c0b1416100c4032600720b0006040c011100d0380c001166032810701a51040340900d024001c40d1610b8030400c400c0443c0100310703000345890b0400038424158410f50007a8407106107445045946c441a803202e2400e454900248414032403414007048401b403050b00c3d1380840d480042102e10080d2114101700c0d0b01d0717a0b84e802c00b641042603407411418030741c8203101000104030603013000030b501441d0030701082c01d80e40040404140e43e400001c10b170340700c45141f01500180e95140e20260104a003001d130025250034804001501e900c00c448048051444c1c1801101c9550358401100e56441080b11301c080e000c202c00700d0744031012540e0108000ba4280300013013124854080180100d0f80c104035941248010600900f00359000c0c0b20720002081040c0c01014122950700e03140d40210340720a00f071200141408416000a401c20444038403a11707141c00c03c0401d45401030381c8200c009200c006800505807502609988038458072841d00c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 78889480 1250 78888230 78888233
    0x90904050703082703060f15010306090c03020703021605030d2105040b070e090c0d0903031404111f05070602070f0203060705030a06060e100e030a080d0f0506010c11010f02150103 79
    0x1450004e000c03c5207000b220540c208407034200758560318101c512071011a80c000008134640072109102808840505000400c507813561800c400312003061a076500466400902e503420b064040103222070400d502401440e040e414140400d44409c4a02100401e02c8500e60b0344c040700b08103c0c41e40d03002201c201c05c0e0801451038503081c9041400c2d01942c0d01c5011650f054442c4199081041e0701e984100404142c0e980b4220b01d9200d0300c8002e10180c2c01c25420550380d20307060582c80c01040813841c0204d02512662161000110402c403038008001c07160400c12050407042031140c0e8100d400e03909901c0d04210010780310041818824000045540c0c001c1d40740c0680b100b00702d006074201c000346014a0a416040140946621040c1c61080322030002d181d120150801e04403460344038034001c0160360340c0603041c0d4805030100d0f42c441c1401c1e0080601d00902980f03800880c50400002c0c400c0544c4442c007440c00100484d0a5101d10f0040c1a11841860400c82d0090748040068000c01550001143c0741c01300d0009580e69 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 78890730 1250 78889480 78889507
    0x71a07080702220506150703020715020a0203100509010c022a0604030807050106030605070e03060103120201090b090a050c0103062619060b0f010f05030c03041e081b060c09090405070308 82
    0x3211aa44a1022006d40170344040c0080e0607640300310307415002010700d01c2c1001044081000e48009560031840780030822070058509010308020100c1c00c82c00818207060000b9200d0035221448950070071944107100d408595078000c5401c0c1d9110100c54403010b01d050a10020942610884d0009032860000040d0b0350b04100d0305520110850703010f010104965241c8000403034140d56175004140d81644a1b00041c80442c1c080211006034442c02c1c000003842202e85e075101c460020b000c89690159400c840255002c1c4a0240444080716600340303800c00440e400c000664030404a82c0400b064001400070f00081e4000302000310f03c45100801510000078009403428201400c0c451401d00d00480c0f942c0f00301821175018a440000388000394403050b00f10b0b030b100325681c815900003c000b641c50544200580f495154012000c885060050320625a503000041140b0121152480040242e901800402c591800c6240075a191108c0c101c0700000a41c6941c00d00c0e610349107290300301034900b01c1e002590702c445000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 78891980 1250 78890730 78890741
    0xc021c050c06040b040302060309010b0306071d04110a030509010b1c0311030903060f090a02100e01030507090b040b070204060801050a0204030c0806070c0602090102150108030a02071a0708070222 86
    0xc5501168015248482400300501440c071070607403a1071042c40b0600040c40d05502031130340901d0180c00001c640d084e410010345024025a07a110104841b040c14020030003000c02d40350740802e8241c03024055071a410303c00b0f031030500c03903001e610040560751004078000034001e40280c514448010858070b4090030003000d600d2414005002180828100b034000000b4860200c1680c55080c00200036000c6540c40b030520701000c84000b03042c10300758011900ca100c016911800404e2801e076055449041d004403250003d02190790141c1002c06000c0800010031004180004036802d5a2008480c107032102c04510225001d45240d400c02003840d400c0404012140450740d002c2c1045030300a01d0700c0f20550341c0d54800305840b81c10503941040000c800c41c100383c009c1440341d00100040c44043c4110b611803c1d205800910f1480c00380c0206203640c0000440142483c0d04000701006405409401d0100c002d1100c5e05c421248203103d0002d06e0034002080344c01c00e640d10300103685412010380c66140205020100316000030034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 78893230 1250 78891980 78891983
    0x706090308240306070810080a0302060714070b0402060a030e191a07090618230102010507090513051b0408010906150b160c080d05030f090a20010c021c 67
    0x40041107002c8a82c9140035035103080e0300c2c01030081c0c4480d03198100203c402482c010007116000401c00000140c3c14810040c84aa290080e8090034407800c0190004124106e0030203405840401401180041344200b00980c0d0040c0d411284903565812030741e810b4000d003801e01c882c510305019010501c0c01c0040c2c4040245c5800348600011381c65501e01c5504000c94560a403442400100841401c3c000b182c00340548159000c20195500c0066a5445c0081c803411041503c140c000031140300e144000f035809020301600301070182002c95007142400e02282d070398038141c41c0d42040c941d210400300d000c03c0141401d020012203c8518240d850f0b441e416118013070051488229401460a580489007855128030941660354168409240c400d0382d50b02105503440050301a50421140f110001e4141d070100400940c0c9012600c0d02c585030302d003943da80d0440310001406003080d0b030480d6165400090150780100080d080ca281c0860328103400b5001215a200d0a940094100030a1a0080c0540c952640c0c110359070b5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 78894480 1250 78893230 78893251
    0x3160801050405060f0705030718350f25120309150810060e130203071809090203120307020a08040b040305060a0c021b0424050907030e1902060706090308 68
    0x5454600b00740030524400c40c2c07041b00040082c004550041c1c82419130954400d21415010740351511003c038041c00c8000c01294554542e4030603401030f00401400c1c60b54400411000c0500120715607030000f951100c01800007201c5003d804030200d80d02010341045100900b070101c0800d50444020714000d00840114018081c0d020366030340e40c901c046445484028840d14400310500c2c0e28901d03140d030a0b50000010246643e10520514800505100a202a5124080c9643c4d0541d14004a031121515142d041d00072518050802e22904003503140003a000b07144082907852580d903640d17402c80c200d0904000f04030013400440700090000d04407103c1809802944d008100355040c0b511508001e07400c0f548040098409a04003a215441c01c1400419402040c0d0000c0d00100d2203507410480c5505201944000b004c1c0d0b8501c9820034000d41c10301388182ca6004855003410401c035100e000c07405507603c802c088017404129400742454115200c140588580b5075100e0700c144074180c00d918000d8103050303080701c0c00641d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 78895730 1250 78894480 78894493
    0x1c020a03020406120501080a140312070306090e0105010b090910120302010902010f081003230303100801140c0715090602070b0105040e070b041e050307030602070b0c0306130b03160801050405 84
    0x13004007600c1902e040703074031740710050a4402c02a07440111149808421303149500043c0840700820030380d80d0b110352141013941d600040080c18450b69504940b485034800d51160314100044c00043c0d0040102c4104c07078011a2520141e035a000721104100803d50001c80e610b20000700d40313508060701508801407a84c400d0300c4440401400c088210b89800c001c481140f003806501d14200080b0303512403a5139090310842034504048540784068180341d90f006883d00f07400140318a40810a001013842483d08005a849401c1500d04080390a610305008811010300061403a400200a113003956028034481903010b5000d649540c0702d0704045102d00701c24401c3c0c0e8044d906102e10a0b48942c000300d010400ea604160f119800d00703052078032000c4420f80b9150300c468100030700900480c2d103907000c100310f8006502c6003c0242e96107041d0b2805010b00203000d08044d00200040c024040c1039030b0b443e4407003480d00383c01400021304825040002407034024041c05d00308112582c50400308a9407010b4003e184514000c5044454 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 78896980 1250 78895730 78895757
    0x301090612030509010e06090d0309080706020c10300516080702150a0605060c07060905041506030203130215070b011508130305090a24020d090504021c020a03020406 73
    0x262030308001c10050010b0010000c03d945980640042100c006001d0003207401e040b403031030100d145400d02000540104529007010811010200304d2030000d4046440541810412070000c80c1c07044402e01e158105001d00b41070320480c9101c045c14000c411030520840c02166004a80e801c000526055580c29603214881d200d802450303014032946401180607600511450074040102684078038054440c140c0707952901400a0301d0f507144805042080c01800181110700c1c6001c502600c102c0340743e40300e0340c020790414480404840c0e0b9102e65404450840c2005070740c9503604541c030b29284d01c1d0800029840194501d004180c404010040e04650b0710500c18142142d0b00c0340b210000703000281004800151143d000209c00614411720340d41c0d95403090400700c5c14201d54100040c010f030304603001614401034050749804988905500c208900e600c0780007800c91484040802030000100b802002d0081d0f4000800c5141c2c2541288084152031f4000411174459850310380080180d44284603180c0040d0740012043d8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 78898230 1250 78896980 78896999
    0x30c020d020d02060606160204020c010222120201050307020c10090f05090408040506090d05010908090f0904021503090307020a0311031213181e0506120a050304171f0203010906 78
    0x2460b03440282c000302480d581d0b5000300310841e40440f840c403198840c814003090041e01c50303002404042d02c1c10800941c07541150107001080a0074020a0f200c0107042d05803c2100c805112000c00707903550280303030081e030b240da9442c02649001e409105103904003015644120381d00d03a0148040c0181d030400500c04200544e14400c00c0020b44059038086c00d55030b01000b082065280c01c0e0300910040002500140c0c80d450305440f0030342110b003140d100342d0750900001070f40c003030f68a091840a402418122444e45560a05402242c0c2d0046903201e501081840000800c41010080050301d80f5079a0003011000d400d6160301d490721200c0e03e0307403440764083d2080c0166941003d078803c0039512003036505502000d429190889044000100d004600c4a00d583c81a18003203110b18000c01d140012059440421181414800d200da4038481c0518030710540c000b0391503480064030200803501160f401030030181102120881840c10702c501c10201144031020000d1600c0042c070982c018604851000104011b19a81d81d000c28 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 78899480 1250 78898230 78898243
    0x30b0a02040b0906070f0c23010903050c01030b040b13020c0d0903150504030302090a12020a0803030709060c05160f090c021903030507210f0b030a050712061b030c020d02 75
    0x100b1000c1e00c10712001601e8106030000d42641e50041d101c0d0600b43d0215258410019215001801083c030503440301840319900182c01c2d61103e07002c0c81d207845080d00d59142d06855020f40c0b01854101500da11350702d60710341d869800c030001c01174008001007003048030010f161000b580901120b800074014110070541c2d1600500e410411640c109180e00e00c0f00c0c4030f003443c0500404009104030b06247d400c5c8203181c0c464403408548030251656030b000303440b42d881300c5c010031400181d1a07000342810f0f0b10070810000c0c0306501207401400c0f0382c2d0b54245042d601495143c1281861400080d07460030a8a064001500383c0702a01690221521040100103480c404602280c803510302800c55148050860442e00000303101e50f012030b920607010b151410303801103d00183c1a0507002802081400b58848081800240c1d440c441d0300000360044005000c0700c04280d03240c64841c03400340300d95a6030076021405c1805214880d040b41c54007181602e480002c1896806016005240600310100148510000c43c00d1907800060b12 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 78900730 1250 78899480 78899489
    0x406172b09261b040f05060f0f01020102040506031608090307081c0906090308070311160b07050d0203040506100605030411120109020a031203050c03070503061e0d0c030b0a0204 78
    0x80c001c1d000d00b054800c80040d6421080300801c1c241020300780241460a00494840060075503505955440c1c9400f0803050f078240c6050340e01414608070a01440ea500c0308202c1d04c8015007074603504002180e80c0b00503030081c004c1d5400301d60030140020800800800d10701c000d071081c041b103840d5101710f41c80c1e03c202650349010f61840200130f10020084511882244408c0c04512402054045050b1850f84d44440a95400c07950031000305100b8410300110740d400d40512003444d05a04513007401d1030b402101100314224482c50141c500e100c01d01c00304c5c0d1901d108200300d44080c104003105541e24101458079a5507038408458024200001d410003207151031003402101d0145030000d2460f20801e0309182002480155540380403000e660304c029840050322150f0403d80150300900d903220010070f0244001c0c00703445000344029251002041040a80e40d0418180d0ba00080c090b500401180300180c01c00d69200103041455520440101d2403204001000d0000d0702541e01c40d4030401d80c0303915410311803801d0703005074007070b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 78901980 1250 78900730 78900737
    0x16030f0608011d011b0f080a06081e0c010518042018090a02030c030402090907090c0207091d1c0c1707050c0102010b010903030503040c030c060206010f0f03020d02040b0406172b 78
    0x1031003100d140c400c0e0807e60304001d00c41b40008100380d981031500d2510441c03420600c00c440c00c001040c1e083d40700600025000703100070708000d468060503465140740c080da110015031086035a455410307054421110350407415a501500c040e541c4d0000110b640500e140c11039a80d1117290640300040450302c182c0283d034091000080032505507221a401c2181508000b84004498820800c0000301a1242e010348454104650064140242400310030030a60302c542d500c03030505071408440c405807448002003401105045ca0544071000c007440c1021243c0d40141c080c040c280803950503401c0c40030401c090041a0742845081100c07a401c50301001642a20150800310340481c0d00004100046130180c401141e0081c4600c280c03030101d5440c3c1c1c0c0ea401c0d810003079400480040e0300040c0103000344aa13034058030014202181d0024100e601d168001480112036110080c0142d48519550300c85449641203800580958216a540250040140f036510f00801c5104e8541020690b101c900030088084444d51001c040d40d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 78903230 1250 78901980 78901997
    0x2070810061211010e03010f0c03060f05031c0e10080a140c090d030302070b04030305040209010806010f05010e01020a0b0a0c0e04021201061107030f12030e0616030f0608011d011b 79
    0x11a200c0302c4007110402c03d03060051011040714030f9a0288204a4002c1400318000740669980710010121204c2e60820890a81c00d2942403090780c2e8000b6129140ba00e255040c041d54600b826412900c402002030895000318201c02031700d42040d003054409225100c800000c11481640b1421550800380c20b03074110303d800500b0821728200d400c0c01031041c0d813401d00a060144c50203c03e03a4540c0040d02044406500103991082840111301c0c0c251750090042009800418141d4100f807161300301d0b4403040c4242c5042c000078040805c49640203205d8901c4007600114910403e19020701414068450300c446000064040300d80c107001c510382842a110015480ba42400507682024405d88034180d00c48c95103000351046880020001c0c16010a50210310b224006000700564940800340075103600008409950f0031040401210280f01010034050030703010314010034510004442c80c2d004104d1904001c1d8954200041d0400c0302500c5040d10b20b103908417074000c104446000d034404c0c18032000c00d45140f00049008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 78904480 1250 78903230 78903233
    0x703051315180c030f030e1f03090c030f030e040501061704020402070201030605030601060f0813021806041e0209100e011b110a03111806060d09170307020708100612 73
    0x2640310081c2845805840c00005280c2e49501010b840700340d100320b42c8005400e08150806d0b074440c0922900b00f105807611041c6605007420013001e4030000d548641015950380300c50060ac0082c44210b07005541000e500c0042600c5402e0082140300c1554002e400b4a081000000300b15100e0503101c0030181d814984414241c40d143d08110195110880690400d5100e02c00802c3c1613805100d414000c0c0042d40395514040f05103030000c9d00d41c05000313000403907404054803400c002d81c0300d10500320040e12016145108541d80c4600250080c1b140b151400b400344446490100c0740711050b07004010f00d1408640c1240c800c100d40c0d6040b215a851400c11070300055114081c00c0b007100320600da009440784111080740c4000e41410214240304503950060b1000e0712a2a94412a07040403601444941d0025001002d00e28000b000f0070124418801403000c1203a540c074803901442a005a1001d5509520384c4040da02c1c20401f90095507401c403401035001d54010886090110704c0d407842400125800024510710542c082d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 78905730 1250 78904480 78904523
    0x30c0a031e020a0801140405010b2b06090608070807031e0f050d0306061701030b15060706060803040816080601060c05030d0c08011d06090a0b0a170607030513 70
    0x24802206009003440208216500d007a00140c00c0c074100c0b5555020f1258500b100403e080c00440380b03010300880ca001c0041c0005601c1c0c40482c3e41180f06441c1c1c410300642e828011000c210205052088001d250240106200300c0700c0d003080c0212981c400c12100c8664440c000380c0e49580062000805100d1204070020316410342c07640282004d801800300300c040a03180c0c0c4445041151102c0030200003030351243c06025541d000440642c2d200400582e90240750b0540e0307a079180c13221001c0c00c10404405500b14120441ea1030804980c80c0540c0b0a00074070204c1e036100004d41d9030360400e0058042c1806030030038281c1d40101000c8035100305c0d151103004040d40d919007041502c030358541c40c600361880c1c00200200e92801c0400d010301e1003102010740e581c400561520101c1141519542603200781c40c030300d41d814803207150f4411800c1904203031030100c00a00c3c86d1140000850341281584403441e03525401c1d00d101e100d0440441e000d407080e9015103081c802075070380421008a0088040005010a030180251100e080b80d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 78906980 1250 78905730 78905741
    0xd06080f0c0127030305040611030c0a03080a0207020402040305060f070c120f1215090c0c0507050f060403020d030203030a1823010204080a0f060b06040b04030f111807080c030c0a03 80
    0x300e41d00460211102460b0003c04050581068001c0707000041d0070007940f40e1000040382211068070140d03080c550807000c02626032162407800b90400c512070021821a001a0b4100e0b900194000c104660355a5245011900e8030021140110340c90054400a01c08c14001c0c110009140d07402603900ea400240740c0e000350344d18400380c0a04005c101d190344a05d0140031440c49004001ca64920102100074034020071181075402c80100e0604001900411f400003800000f001001d50b5811118111308026800124501c0d00850b170001e50b00c241144442d070b0600d0b40100041d40034407d010010b0001030707440303601011112002100100a00d0b0141c6084121500070700c168103001c95990000f5103481e949400d910300d800d42944080d5540303072281200d0b2080040718031581d5134440c02600c02604042c0341018421302405a0301c0040d0209291035580b03002c1010f5003002c00080ca50050007410006c01c010924200180103c680c000402c88400215019848030003e0320711503016012002d1030105160404c402812 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 78908230 1250 78906980 78907007
    0x614150a08150a0602010e06011e0605160f0c030b0a0b0f01050702030a06060b0c060a050906190f0212161d010f0201110d02030f0c0f04030803060d06050c0d06080f0c01 74
    0x1442d4580034040355540c00d407070b10040c20300d6800415101104013089052540c117a2000c25402c40c07840900c071440615540c07440485409080c4076460b1540e2400305820b0b1901e805000305010128820a0b00b080703001e1a004040d20b00983c458000c5580d80d403908000c4811054001d684103018001031809503103d400245110345c80075083d6901401140e641006444107a0062003100c0c00c081f521118800040003a036600c101141e0050000d4200300302029140c15014042c810241e0b0124908014080103400c0038a100f040210111360b240c9450380810708071201a80d0800203000800036180c00b803486012040b040c0c0c3c03c02d15180400072141b40054409849160b442d200399501d81941940044090000d014050080302015941e0302c0d10043ca003400703000050240b040d482c0140403038a2881712840503501500d13804182640d482c0c98140008440426151004050702d041104210081065401074a0b942c415030718140300d00c40d00c0d900c18030f80319940500d0300500e66010743c1a0030340943c8101c50004000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 78909480 1250 78908230 78908251
    0x5070609020d020a091e05060904140a05030d0209040b0603060a1413050a0203060316150f030e0a060c090b090108130c030807050d090611031e0903010603060614150a08 74
    0x2c01c0315408148080031540c40090f030280d5403084e000101c03508914030102a0b03079000b8204828a49100001c110030400391024010b88207054998000031002c002034106a070701700302226160350b00c01d040030020358080000070340501c1c10101a079085013090425a8000c4200a017400c003000d051030205031500418844d2554488034951000640d15041cbc41542e000e003016140c05a56842d0507030500d49003079904500e602620807a21420404080c03040341c0c000406c846403611200741780800d98102c001d404c01061400b464010200b059040081913172008a01c1c41441c2c644000d819514250728030603029200e03006000c200c0b0303031000496406803c860b80c03400520494001c4001d5440351242ea0300c42e00709042c112625408070003140c40380c0f03800413040d000030401480c2880001c80700b0301c032960302c901030722070400700c292707400700402403190480f4056600c0d0340707400313002003040c10795908102000d810765205880045a041c40c0128a03403d000400080c80f0180708404c131324100011000310b801e200000d1129424 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 78910730 1250 78909480 78909499
    0x30c0901060203120712060b3106120b180601030c0503010501050901030e01060902030c041706041203021602061303031202090109051c1707030f0806030601060e0a030c0305030a09060f0507060902 86
    0x115543c0c7d2051001400811803151345a14250408a01a03007031440400060809d00c80e0f11030b40300705640f00850a940d0b032468072505101000c10998050000035080c40e61011010340000e00010910080740d1240b482660306105030503900354183c2c1e90388003c0c004d19000403010459040d065003e50410304d8640c21080000540d182c5d80d515500c03c98106594801039a000014100074070300485014484040d1400d000d400d06040540c3c4034030784021111841c1c02495008280c1c00600d5240b249c8030000141c02070710055454025043e080b10100b41400b007140403d03003920310949000468400d940600c001a15001c2c0b01604020400c04040624102c400c1d4103d941101c050004005510300843c402c481220251100c1040c40c001d4a406601c01e13010003045010381c208802590005084c80c1110072034100420444001030204040402c1c54002404a0081c000000200440013005068852150345d420280541b502d80440e600d0803030603c404002003080c800d44000c1003140d03001800c0d403403009250040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 78911980 1250 78910730 78910757
    0x80112030903060e0307031101050105010903141c0509040e0a0b0403030518070f0f0501020109030c0611160f1a01030b0703052e080d03060b0f031b03010311030c09010602031207 78
    0x3039a6641c00500004e41000c5032010030150001d0464910b05602340083c00a2342c10840001c000070014400640165105c000c0c48a030f00c501030000105841d101c103485c00700c4030f100c6140507210ba13000d21010b5000341e1910000038681900820f0b4a0744c0d881e03000c2a0b007603071341d142c9403000c8001e8100a0203481041401444250410504014088c0245840014851101d1902c001c240c80301901c0c0e40b000341036905112f03550000980c0000c14904159101400103116410380d04c900559014108203003250340314504070402400b226102d01031002d8403070725131441103261030340c0d48410030390080c84014000d08081d4080784500b402504043d60000c1c0f0f40020244828200e040b00c42951480000001d10031944801401a400d00b405100e0b03442146041c03d00c01d4618085c000416031044004d642d041c41320102c0492180c07039200702c0d585c04240b202640d46889507182d0030300b44140000d800d11203110b072294101016290405404540c12100c0c5500907604087c03c0d0550700c3c00b43e210003080d00c2d04001d504901c60742c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 78913230 1250 78911980 78911993
    0x20306040e0703030e010207060e091f18050103140d0507080d18060923190606050a0e07030501120b0105040e121819030c15050705240610080112030903 67
    0x200a40c020740e10542185d800c0000a81040c0860300290200115489107000545403080c1e00c0303412500d0302070f5454403400c40956051102e10141c20400c070441d411003514280c0b5060f9000941030700e001c0c40d8901c2c80c9400c103001c00b9030744a0f0300c0e51551000c6442880319002003119180039054500345420042205c140c0030142c500c0500c00c1c04000c4582c2c40d91500480c05002d140380c14010240003e100c0c2c02074420340021103540c1c0d019001c82c1d100000c5180c50b1200200304898220000515025064075045503c503600d21707400050490740140002e10b06000040c0c2c0e84202c01211035a07a4100903a13810a900b01011b2001a121000c00c1340c007544202d50305c000c440300002000740300c034041802409035604140003c0040740380c41d25603004e50103a22801c09101040301c0748002d900b29800500f496a210311900700948860044000161041c0a0b22840e40c0c00d135400e44450150701d1809000804450f9984c1e000c00250147c52400301000030002c034010320040023140042d10180303009040c00700000c0d580303a8600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 78914480 1250 78913230 78913243
    0xe13081606060905180105010503070510090801020c0d020d020309060f032e140909060705030910020d0203010e071704060c031d070303080702070815071b0308010521070306020306040e 81
    0x480f0f0142d07074600300114903541e070801100000381d44000f8011545043c00003540c401450050510500c0d41402058805000ea43e1040050909800964840c80540881c80d00d03002420a84800350189802400c15144007008940c01000000c00c01d500700030000c04060131030f030801406201e2146548900c6058941390800340b802d020080d42c02d000c031803414003030b024100101c40303603c45011743c2c03141e0705000d011103021540a91109032490700c1d503201da071142c81c040c1c681a810400ba824003880020340c050031041e43d4002394182c490844c000c040d035441d89801111500b41c0f9841080c00754003400d01080000c0c1745500401c4100c41d05180c08141400c907000c0c0030a05440b0020416410380c0000030810400d500f107920b065000540d400500311061400c9104d0b5201c100b413111480103204c03006d0019403018060400450400846050020140d0051070301400c058420301aa03841600d16198413410581c011205104101e01d070740c080d142c00c901c1c0d0358903400030303400c00751005520613103e1851a601e4201080103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 78915730 1250 78914480 78914489
    0xc0310060309081624020406050304020f010c020a03030f170601050d090501060b040806060406050102030909150303040b03070201020c0705040e030a0302091305040b150103060312050904060308031008070e1308160606 95
    0x85c0c00c03148015404c2c001003103040401c5950b015005100810815800c54142c80c1d005406840e00c14003500c030040100c070f9402041000079442180440b0100030706501c0403000d5194082d039110300241d80e40c40c1141803401c2104440583c00075408102c9030715a05056041009800c1c8034200100e003240c0c5900460026070010340000c1c4c016800a420400540b505004041c0104001c0c0055032030003039101c020601c586001450614448031200f0220855181002158020b01210040d81d8890030000c100a010b580302c0c00e420034003840703800d10120b11450030344103552140040c1c400940c58540700e020309030040d4001d03404440d813003030300c0311b40c02e80d05201c283c01168071540c8986103042a030310703203128001d03110302340e160b0414101458508180b0005501100300e5002c21254207000740c540d000000058090f00311500002c041080c0402480545214200d01d0300558001c20300b1341e0112900c445c51652a030f88129100b402850305c03038041c000420940ac1c01443d4540044206545c201d10741d031150420348016600 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 78916980 1250 78915730 78915743
    0x1a040509030705070905150d080d0f0c03050708070906030b01030b0307080706090e06090f041b1707060c151d06011214030306010e0f0105090a0305030406080c03100603090816 77
    0x2044403c018080c07007410040c04d00c0d04810001c509044820074882c1e41408089800b80008550581c240b01c401c8050301c014540d8103a060000909210040d00540a4000a8000300f07040602251150307001d0401c02d4841d014907507030703440c02d2443c0c94400c40103040c80b04107460502d84d907003048810b11f44060100f680549861802840e005103480d000808090b41d0f640501c954515150603c0143da0b2402446a0400404020982561140c0c14045101c0000100e091051050208001804840c242081c460302070014191041c0a13511102a52034500e96a801800d0204040c0c1c4a141549a40e00001000c00c0e40d00703411803000d141c4100103181c02400c1e08080140c24843c48042d0401c4420044203050940d0038010714214100000060700015480480e1407003403520703c50081e52648a003003940e24500d0000c2090345029502c0c2030007601c991040c058035000030140000a195401050100d03030048003100410444030b4a4240304800070a2202c20455402500b040403941586900c03481c800031a00911 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 78918230 1250 78916980 78916987
    0x60906120604080a1b1703060117090a33180b0405010203010801110702060901030f110a08090606010203070b130501060b0f03071d0109031106040302030601170f0604080403061a04050903 82
    0x72014141c842500c1c034013860310503c0744a00000407801c82200c505000c000c86d0550b101d469001c01620300d03c40b0700c2148076126000000700480c103500003d0421906000e000078208131180040b0098560303044400e41190490144121a03031800c0b5544851603c001d080849140452940d0320480c54500a40b0140d41e141e4001c001401552000c0c0f15409110444070001840c0207410307030101e082800fa1207a0541419964900c6441001d0720313422004d00d4001255410b9620310310b08e44040d200041c1540c8040c0306118900c001090b550000048508a40e007203400442142e6490b4003d5510b55031583c0308031059522201e00140f40017960010f4400d042035000140d0310381c07030621030041c030502241d0b840001c034405802c102907140c3d0f0001c0c07042d810303650010b20f5010f00c810b5250120f841445141e00082d018070a84000040030207404c03200780c200c1840c00c0181c40110401114a5595000c25900905a003004000400005040c0c0d881500c41401050010009481c05c0000400300c2e502120b40300740c10341000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 78919480 1250 78918230 78918247
    0xa020f07050d1103030402150310030203030a09030c050d080304021c0c060801150f1b0606050a0605030105091b0f0306010219030801050a062d0c06060f030b07030902010806090612060408 82
    0x92403c2d0352121440005604618160300020500c41881e40c1c10048030308000041900542400e4148014503000b4081325500c0c2c40f90000100890581d110a0354014088100031825141800203050b07969002405107085403925000c203c1581c41480714004041c600c0c2c40060000380c0020203290040a050701e90a1142d07240c1505400e18180096450b410403000000602e00c054001800718844605e440090b04491a18a0508000d0226070062a032254102d1000141c0035403100040d4180ca5040c0c5802003551203403880e1400402e09086011507200040c02425074040020015544c0290144101e44080d8441d051508203083d0a00094000903014001400103080c81920708000300403500d45228a0f00e0065880c4031211040038204210110348051900130034410003035510510303000711f010000b41f591181074421440451208884101c10b40d00000c10031400791144606250301030310b5800d50341d6180301c2001040d18000b4216076001e5105e1500034003181082014a10441c8581c003660f40c0c81c1140c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 78920730 1250 78919480 78919487
    0xc0312120f020a080939061306020d0504120b040204020403061d0c0a05180703060e0106020a030e060306180c0c0a03180905060a18020d0203090c191d0a020f07050d 72
    0x4080302c259a00038803801704011500a43c451701403008845401300c6c50034080380426010241d60300503502010105100759814010881ca0044031071a400700c6a10246560040d50340303000340e100741110295540408070101392034003445c651040c07008000600d810740729598481198143c813400301c0800000c2581503a1400c00700b10070512010101c0782440c1e42480d040000e1034049081500400001d0320350040b90302d1034040d410010103800141c0305a103141d03844000003503907010314030341c1580002c0c00c180b8803510a017040c60840f4007a500151040c00d220514615081d81090090320200c50070f04108242c0120f00010720204600034800d5a8000059201c5071000c82503602e581c00030a003552801e03060041a9a82c0403290080b5015454211340c0c0311400c4d00b03660001d00a50f0381204c49180004208900688040350b03000305c41c442166540c8229007600c2d030640c401111400b41c0e401940d800d9070310044022030084215888092181b001d071401c103480e1400304841c1c100100031101a44030f248030a40d4141c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 78921980 1250 78920730 78920747
    0x90402040915090605060a0c14061e070504030b010510111209041505240405150d150e06010c080409020a110706050712050a1106270a0c0312120f020a 66
    0x3d01d00c1800714a0600e000a11240700b0000c0d800c0900050745480c000300f2801e844042210400d64055400760302d440303220400c0e84620f180000a030040180000303008103025100381c4013034941201d5a01c40036800d150a000c501c4064840c9402808601c81d40a45411070401151a41e03128010a00d0b8403a40d0020511042c0e40000d9640750103070300900e405008a4403007800700c0c80f400001c040f1720010034107000e164682c24800c54000799003007010340d2140c00740e8074404002002c81080b64001001003070981816114402d41d14085e00e010583c800340801d8030b42d03103c2c48503400c603039004440491030241d989180300103c0c0d0018914202041c108480070005110900c110b20040219007402da1030180b05940b4a4045558101010f044c006d011403000585c5124076840344118980f08204c808500740201d2040100030742c92074019070607400d0051144882c0000c05c100048036444030b6007000303503415983ea00144218900404080014880b0262007590b100e004491070b01241000050b81d80c00c0604000f00000e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 78923230 1250 78921980 78921989
    0x12100609080a0b0a020318030a0203030414010c0c02010806060f0c010501031b03050604240c11010b01020c0612090325050c01140318070b1210050307031a06010302090402040915 78
    0x41010b540d15020600c200c80e000d5100044241c0107940b136803081610811880001d90f5450395100114a80c050036400100850180b4041c05440900c4038400305814241e55200410b0000034640c000c00f580154020a20242c120b40000e00f03040c1803e500240100451b0804918403045a440d00b0042061105000802103216040350020300882c1c110b03100c141c2d03510340c0500000c3c80c04000940e000c110720003600359881c41d100d203413100340f044181c988001000d000300603000d180e1075441e00c049000150300010f400c0c0c03034528002d801c20342044103038991341c180c10000402502d540e000030040c40d0b00900401d2a4424581503901221305110b000e03050a91408010281007410701620b0041160b0318924482a80c0d481007140150458010702c0000250034035240b58400501c816020600480300c1000741c2c5400c0c0314039001040441c400c4d540d8810503944100e070b848050600b041402c0c0502c5c58990810900303a100c0c030107040240c5440503550200d801c9910a0744000300841d518840000c903030b42c490701e5540c00ac0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 78924480 1250 78923230 78923233
    0x21c05010504231b031e0322051806130507020a0302010507050f0405040b0103060e1302120c060f0c1f09060e0c1f03110706141609051002031210060908 67
    0x1040107810f100d68410440800a0401c10302c0c03901c545050754100400050740035a0249110040891141543d03a5044580c0e4170010440e140501924030101d00f0a45080f02c06c001c1042055003809441d8a20341e03000030709107907000109101c945804003401d0141d2402071445034003c00780c050031810f00a003103c5018002c0d004000c0100311540c2900c50070001e48040c2c1d20204c400044076100000181c00034501c951104000b503580700704102251141b08203500a035030082e0ba060a60004c100401c80c0c85010009100f079110506000d20070006600320050840190041c00302c5052154000d42000ca08080000000e0415159548101004030501030313003e140711240001c01e01078441e50009401d680644801c071214070100d99001070068440c1d000b40305140c2500760a0740d9164200c0c00c01a010303103410901007121400c0c0f0030105030b120b001c440314601e5542245e0707108010035090030b0030000751607001001c06046110074442024007264606001c1e020300585100b002844d403402c0700140c0040016404801e85 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 78925730 1250 78924480 78924533
    0xc0509091006021c0210140604150302030a060905070305100203072a02090702010b0603010b0a0f0c03050d020304080d0f050a060503030715020d060b070807020901050609030c0d021c05010504 84
    0x419000603501210314840c038080d41941c00d03082000c914001e81e5042200100c0e080c0899800e041820420840c02231100359001d0101300302119004a009200b072200a415502c440c1c1420003040042e03010b40d0307020744150b054416003a81c0351140d0303250070060481c1c4401c5550000034880c0540d08a24078403261072800c0a00c0c95030000120201c600c000802c10040c1c081c4840c4400a00d10920030b6000140d03400000341501d032a540c59410524141d008145c1100114462b202c158540302d004070007000120303030b01d5682c0e03d00e480b00c4500644040d4002a008980c0c40c1d900f8880b401c80311340d0301e005261841da5544000038181ca800720081082c1d900950140d030080d00101306a001084491304c40312240c01141001699500103d0003090090155138010b101e03140f0301054071000c10020030001e042340c6008540580b0a031f600d883c100110f0f0311800c0d03001e41c1e059205111041c4941061031125103003d000412110151152140c0b8084011850700210b030f069545504200401254000b4419900c98200f0708521 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 78926980 1250 78925730 78925739
    0x50403020a110301060f03030804060509070e130305070f08071a3603040e070206070219030e0112050109061d060d170d020706020a1101110904020a0c05010c05090910 73
    0x464a012907400b400309120310880701d04503102500504014824440f0f140c80d400d9680c18000c0c00400151070465490303043c05c020800070040080c00009580c80311007111038035129440d44007006003410034210103106050040401095200440c1581e0030300a5904560710480c524155402080342a840c0c00c800d1281c5040c0169045130b01e144141006007000c541c0c103d0384010500d04030814a15203410700900c00010041214a081240e490049543c2c1d001c607403030354075200800e91b1900d014102c1c0b9210448180d07014004a4071810b404558140181441e80010343c1071034000c03003601d000341c104242042d101c84007006403041000c0c0c8202a03911007a000e1a4038213001c40054640b000441c1c000d0440810010040700c0302c4c05c0b1008803810800500d40c11582c031a4146030140c042c0d00106007500105081c40c680ca01c0014060092a50491848103864a1710395441e0402c40250007a084010811651100150004809104410203080720781c4500343c0b141c503d101001200034004204100c031464200c420003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 78928230 1250 78926980 78926983
    0x60b0a08030a0c150908130807060e040218040c020318090f04020415080105100302040b060c060f090c04110405090718060f0309020303030709260309040903020109020315060a0905040302 82
    0x20380041c1180f0b841c129581460600c1c21000c5044014200c90318035154007030b4100100040241481c20004640d044219625818181c44250b50300c99403010a010f1101c00b00c2a1800780c1c020100300825200445603212640702150854200d0f10a00780945e00c00039076200c1d50b0f403000a0740700754039000301d600d031426240a8140707160003034018100900581d2070b04c1a466503803950220100150100303a00030000c61420b00c1c140c903284081480309071b020340d2030301070820643d081110440d080048250010a420380701c04081c000c440304010041d441501424085450342e41c1c42c0d014544106100250140d1078030300340010018041406010407060050401a4203ca21074178520032040324202d081a803020104501c040d1301504008030025454000041007044858101d103c80e010750f55481c07180b12040d5405e500d020360f0224000d0007041c1950082c4510700052a01e5007190314050320030700c000724070080c1c44e9010900e010640e4402c00c000c0d111200411960341000b260300c000501c690b12080c000390034aa100607 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 78929480 1250 78928230 78928237
    0xa1401020a0e1c1a010e16020604020f0102190b010f050405041505190905030d0501170a1b0905240f0d080310030b0a0603050f0105010e07110109060513060b0a0803 72
    0x750040c8800e543c2511407503180c92000d41d00300c3c0c0200485908280d00d0803110030448003401942d4604140801103015103485055600011341181c00600840e00c40b0b400304105d821004200c07904510940360090038000800303038209c04051040d040092554141602440061070641000780142d107007100300000f060015002a003544041000000d040d210803601c414a104281e244664140c10b21080710200440000108401c0511503c1084941d032500310101c40f00320703117444090041c3c2c02002c600c0085440c03034800c812030351001880c5c40301c020380c1d480c0d030340d008e0710421207442c801c00c1c2c1144010781e07480a0f22400c6100802d006c079094440313900f06900182c0c402040309000380c214000400003c00100000704183c4c040d54012040072100d140c00d1a800c4040c10150000300d0341401900110150ba1005024040c181d82c0310207e4201256695a01101c00103028003022440359220881030f40401d03500c1c03044600410090001c050071580c0c6d418208103403a08160301d0b074001c0c098036038104103440c40403054 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 78930730 1250 78929480 78929507
    0xf180501120b160201060503070324090c05041505030114010812040303090b16050a14010b0d080d1806020406020109110111060f0601090503010f14060603010e071416050a1401020a 79
    0x107900c03d06020400880c01015580c0200e50940314060000c001e1100b03600c00300c081681030320b030a201c444203400000300c00e0700c40400000380041d411076002d00c401e16081c0c005541c01d840440200301340c40c3d540c3c400a401c1d25400a0f100c24114003040060040200510003920a200714811072890645140c1d40101000c031a4807402101c03d401003800480d2a00041c8012031840d048400c032484150b60b41401c209610070106505000c2d032a00d096014503050400002c52560381000e071f0f403400c0c0441c200040340a040e00d80601040d01e42d14482201c0001c6152018001601c2254000241d8590600d07141c0e860003540701c1018140102ca0320220300cdc1c030303c00150560340041c0c00740d8110101e888040040c0c800c11210341000da850350030503a6845824501d07074061000c09240901d2030025469100a010301c2c1e100a0040700d26541c007180c00101c1c07070341c00381851005000e02d200e010381c60560700808520740740b2106201210395800ca44410024880c142c1c4510031482407180085180c2084500701420000c8003603003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 78931980 1250 78930730 78930751
    0x105150a0e0124140c06010e1501050d0504061401151209050a02040c02100e030d0b12030406080408091003020d0e0106080706120e062502070e0708040c0f180501120b 73
    0x29002d080e120b072149070303d0980180d4100d501d45c2400039060303851344070074010071180e140d455000030b51b0140d4a2000e0181e142044e10784c0384c42c0000b2091404090400140290386d60394461340810a01245890502d0082400d00f080f5034140501510007440990706806070b0640300e0a01030380303402040340421130040b5517074102d500150a5034542803c0e4100f144149c40010018545001c3c43d103200d201100501a0020b0343c20100052103d0004000e0410b0610f024000076030b10a00041c8810341c000d480054000d030180c00e0050a10055100140c01900016034002c0041d4001c03a07455816482c50182a0041101400034421a4201501c032503072428117106000c100041c100343d2810f00356030703076102103810101c010550f0203500d00900c0005540108265064800b6a0b440d00c0c0100148041040001e0301c0844003580644d40300e562040303410341c00140066a0700c1c00300e680001180303030050040318001c20201071509840c64041529000712981688042d0f008141280d8900c001072603204029485245000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 78933230 1250 78931980 78932039
    0x1914010e0102091e130213060e03030c030a0f02030f1b060a0e0d050d020c06070215010e04030e040f1503032a0228030b09060a0606020d020c040b120105150a0e01 71
    0x800082e0510788422548400c0b0f0b1001078900181f514038240b06059500c80e499010980f00400203060780c91080710016021034100b8002c0001480c0f0511182c007141801c2c0c030440e81801c034152480e05143d44000518001d500780e5443c00c41c2d803413509101203a400094010208030903641aa0485d440d02d04800950782000380020300a900b0b00e6440e8150f88640c00d41c0400c4503054a070549020307648114200100301c04d03800100000900b02000c802d00341c4503583c56600d52805a4110040c4005001d8800074826031a84441c030b0000e18803680d1034903170002e501956802d0b03000680e468540520595000203114900e09070f030965000350700c42e0304006480d03100b0050b40340104507040c3c1031010b007816030340c20041c41c4c3c10700803007485800030303000034143c2c011440030800304140c5a54680680c0c4c0d400105400d0005030700824041c0c170b480d103030541c081c80b40003401038803030385d07074a0140b580c01400c580301210b081000541d1200213039078908200c002c0101509100003004000e50503d00100340c030003a13401c81c103043c126518 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 78934480 1250 78933230 78933289
    0x603050703111303030206090f1b0d0206030406060f0b0405010e0603070e03060a050a0b06210402011e0903150507050d020d1503030e0906010315030807051914010e010209 75
    0xa51099100000c2d41d0603081d22510584140351901d05148415001441034601040c0d030420081450404031a80200a1681c4045076203a40d0f041c1d4003092410354040c40030713030b00b240240c0c8900c001103101d1441107400003645401c10540300d200013107581202d510000140014061640c00c0010b2080000c030480301c880c4c0b281c3e40c0c10403c9424049060040d901802006c060143c910030325040140110302c0b41d4000d02c400707400b070414098203003d1059111a091251052901030101d03e22103a50001d0040c98140104284c2d2802100818030100c540030000e1a1400c080050003031024070150360b0040c00c501800305081414008060b03000d86180d2070081c60340002c01c20840001c0354040c0391000402c0001a41c803e07943e007170241070282c040070020b02426a01001614540c428844c0111010b80c01c010f0591b6581035441d248425085208100d9035807041c84101622810251600b16065128580480e07103040240b0010b1309603924900001060b070b0051202c540655034510304850b40d812080e500014500d4071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 78935730 1250 78934480 78934487
    0x1b03100506210706020d050f1c0f0614091605190302040f091d070b031303030902040e16061704060915090602030108010c0c0b060f031203130b010b1306030507 70
    0x107840b1880601c41c4204414001c0000c041840000c48007140c09503005070110f040292500e11451509199034001009040c840e02c0c40d84000c0c00702d00242190008010b1052104003044800c1c0d608042e140c6a103242501c401407810307400855004490f80d8864440c2c0300340d000c000d002401090f42e003940e80a04001c3c8690a0b0b84a581641e00500302d41f561101c290781d0700c0104100900700505620312401514500c0c00b80b2010000c1c0c0d800c03c4504000c0024510340e42c0d84185458840381240032030803d901c030030250015a481d8002c41c0540c405001c041c1c0001801994440c9a02d400780e070010040c413603000705010050301582d0a95900c6600624085042c440d5450042e60905074030032140d078250301e02102c20782403110560256058035540c0008111000790f0742d80136600e148480310000c02c994007a00024032035042015034040e141c00b004d000c80c0e4a861000d0f00a030001d82007181c0400a003481002514181301c04504c202d401044580d0f0380d01e00c0c2c50a110140c12246480780180820305031030303601040b4110320 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 78936980 1250 78935730 78935749
    0xf0504111812060411011e0903060225080901020d180b0901031b080702070603110d020d02070203030408060f1305030307030509030409090302030903061509040b041e0302060402031b03100506 84
    0x1154800c1d10b5152078a1710b0001c0340480d00401450008120070b044081100c1e0610408400910070344445031030501c0d66075114041d40c403210b010300920590880b80d296811008005001403445010300917110348119000a1800020380421001c001803076203484036182d510f01c5d804058420002d03440303594498410061b030241c02c03c41000100b11000c2506a60072603402207601c2e004018940c00e5a0300141d9a8808509031401e420803405d004800300704500950030039900803d0032030300c1003d002d820415150002429a00282e00c840c030180c02c000100b10000005456860f80441c60140c401342e03200040c0c6601e0764074000141500181507545000c1142140308206980052002020a1000507807a00c0d00944076089402d00500a101e144085004405002c0540c41d00070310181024042d580d558441110f00c1d100030b4001c0c0d03052196292103a08444a07625554a0240a40c0040c00795041510603d458210f0110710240180c01c95000021503a4001c2140d401100f020398022909803125000918030a5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 78938230 1250 78936980 78937009
    0x60c03010e2d0106030c020705060f040b160b040c030309091802012615031203060d080706020c0304060503090c0a03020913031407030201050708010b030106140715150f05041118 78
    0x4a04000004e0f0f41031341500840c61012541c0d007540d100550311428815580194040104861403e2105211003a6500c0103400d01c45906048840d001900b034484c2148101c0a5905440c502c102440034418150018456130060940c0c8404100000e0b000c0d03060000d11880c590020f04000c006044c007030702c08a1410303500c03150003543c600c0d180d5182007805101c000c40c024403008900078000e00803241e500c070300080e0a892203001c02504c03504000703005994001440d4459141202c050b6402e00000310b000c482040074202816141c0c072040d60302e040c80075107240382020b050140c91082903005014001601c41700d03440764001c80c00070612010046180b8060311045000125800c911002050305002c2c180d05402550041e4004c3c1c44205083c0d0300c0c0d4511100c180300900681000ca07441000d66000304880f5401002241d000c0e85d07030031303101c466400342100680b030214803c0307a03003204100300600c0800c410300c1c82c1b1401801d04a908221800492840c007166019035040c10354550309000580030035032076000c2c1c1d000000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 78939480 1250 78938230 78938311
    0x30b130501050c0a030e010902031203040f0c080106030212010e0d1112120a05090622080d09050114010803181e090a0f0614010203071401020903030703090305060c03010e 75
    0x18500f1002c03d84036a00490003000000781495102c0340103070b01c103100e0082000d4015000d0500c03185940306040482e807000d042200d07031010081410317001c03c06072a0240701605100d800400c00c1d5140d801000354209401c1c801800e01d91400300c05001c0c80c07030001000700303806900707040c0002c0407201c02a0380ca040c500740000c81107040d0b000017001d200030030100c42002e2041c20808010041070f200c15185a94611301181c07562a60085032005005050502011003800340c0b088204a103840c4d0000c044400703840c0d21810480b51070703444065603060042c4882c1d91501510000004500302280748002d500c1d4050010a01070007244a6400200d0304c06440700f0940840001034960a80c60a00a1101c03004000320030100210520300000404c0d801f0041140a40001059008505080030383d104c000c10003941d240401569942001082e00548050004c0c1c42007900988070303030401501d103007829800c10f0300003001038080c1e0340204010302408078a400003c0d00a0b1483c000c641c0b0350141c1c1000b540c007072159140001440c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 78940730 1250 78939480 78939491
    0xf020408070f1a070b06062505010e06060a090e0a080304081201060507020f04020c07031202011d0604030903080d06090518100b09010920040609080f0a0201020304030b130501 77
    0x5110001914422500d5020300840c0d120f0782d400d44841803000f10451907a0280d401c00042c400302e010f4030050381d00b2140080c042c07460404100e03a803400ba58400ba0194120b12018040c0c0b10900000380309511040c1c80da940078002c0d81c5000c100151909c0b9250080440702e0360744035040ca090701c008102c440d4205038060b403910703070f24142400d01504907040344900101c1004482c00114045114100ba43e2841c0c0d0302403c50121482c070481000702a40024400d01114491044008085003040e2141607103210141c0000401c911030f50701d42100c2d01842c2c0d9500c54036910003024080080c0c0e00652100c21a81c00400413038403004810565809088190f1010848500705400d0100c0f001c020524036503071502c5ca404403410b003490105a041511441088a94044240401008116187d801c108645140682c6140109074601500301c51504190000030001d00d1042e4144803ca90820003400051014801403c05d40856030000390b07a881207000080500751020040361103a00c802803140142c1c1c0c0c0c0540203014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 78941980 1250 78940730 78940739
    0x28020a05030105100201020f0706180b15190b0301030303020703181512050402151e2106060705121308010f0b0f0118030b180f01090219060f0c02040f0204 68
    0x11540080c05107500c515136450490744a540140b0031203401040401100381800041c0e2650001007403140050f915030303a0400450b100040e5940300d510320401452b48151030035522481030010220600a200c01d010040345018448083c103841039034112a4989005607a84040f4035088034914041062030301041c86c1c080380802d205a1505207000e100c2165621001c8071600f90b070310342e42039560944000e500842c40da00080041418003004010b0200d440002d64500b00c585000c2c0c03003a0394081001d190b100139008840000c0c1250030403d080e0020011a007460a0000a490300380e1500d017410300300c92500b80000303101c100002c0503071401c20007059901d00030098900030b1038001024020840c040c501c5070108503800c49441d0700400c0301c81c0780b000c849001c1001e501d041d036440d92890000540070309180703640c80c4100c2c0b07004102040300c1202407411000220b00c0f1000d502c1881460342c00d601005019010b228814060760364003c0c0c0300d01a20481c0d1034000e1441405001040040c11200ca00c841030600001f00443c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 78943230 1250 78941980 78941987
    0x1503070608010e0a0203250201060503030406050304021003050c19030b12010f0605041b1107030b01080a0614070e100e092809020916090504020d0c110601060828020a 73
    0xe0494a80a000000d50341e0b514291030106e200c100c640300044c03682d01e050b4a110031380340300921010010a000000f02e6a0701d03080040e1860f001644840c00080c0000f00304000c6040441c00441d031441d03281000c2c00281009890400603000b080301c051915010a8070000c0700300d1003a000520a01000780c0030300102c02070662031034040d0a14441150706141080c0000805040600c0f446041007004600e02c1245150035100712001d00401d90702c1c564501c5a10408008100015410350080c90240000c041c0180701b46485410b450980c0c0c42e281021007180100180c468002d080c1c036403140c034221044141c055031403a05580e03014100c0707071480d0455665030030460440315603511f1484800d82381143c91112910340c5030312402d0b0760390307400b0082d004110b48000c5480c1c10403000e98000c41000c00d061001d1030030340f5440464107d030008448204c01c20f445504500344150804d413012201d50070f940181c2a990b05080010f0401c07880a80101c02c1034608040150303c018685065022102c9080400d540d503407034100004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 78944480 1250 78943230 78943247
    0x2120706090c0b0a18150f092402060108030403030e1c0506040605070e150a03020306030307120507021003020c0705010e030a0804080a0c08062203050708070c03172115030706 77
    0xc80400d038641c201440b80f10252601c40c0c1115001080d0030301d1803190031b00484110b0308682e4031388188000d02e040801c002040020700048601200c140400904030b01a00038074003075060b440510303960820082840071070303401000956030000507078414202440741e04007903003020f80d1805c02501c98010348061100700616500568021280360703460b00c61101d00802000b04501d0a0303441c41e000100100640c40d80c0d18040d802459010100a05803410003006480d1074030080300c0e980b0310200183c000a266800c501d41310310b80c100032541e203240c1181042c3c17082d02071a81d00c010b64020f4505005104890a44030f9604000c91380100340c2c8a851a91502d9603206503c6e940e68495104480da4004108003007500d12001403000c2c8a071027040101c203411103100304c207804198181da00c02e40421000300300c0c2a01086119005002e0644111003039840c903842e50500034504042e24040c1c0025031020886800748501c8c00700c4807a8120700d4003000d442d040e125905007000c0109180d10464150048840c005407440d04600003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 78945730 1250 78944480 78944497
    0x5160b0f0108070621200c030a02010612020d06050a0612050c040c1b03080403050f030106080727090510090c0c0506090703031b0c0b1b1c02120706090c0b 68
    0x1116402e5440e0002030f507500303200c240301c1d070800c030b40321540901c8581d40342c1c1150850421802c40005404118560b2011b00c1c6e010801e800710305d03800024261002d43c5d0901c035410090607420424007040030a580010845050700748041c0c141a281c1d0007040c1128080d078003000090a154030404036a81507442e041d9150800000341c18807071890000c460405a0143d500c03000b039500050312003400e40702103a5003690301c440041e000342d040042c28040c410101d0b0801001798060200340d1100d580c60724050400030095a030580568890424296514901009221516040e24200000030885a4885512050307180040c4d00210841d403c01048803100707500214102a600e0042040c1d40450361004403c1d540c4005900c030007400120440c0e450b420101901030325180961281500d0f0440c0c1c1e035074600031150380d081205142d01c586c800100e000d104090800c012400000e154194a901082d20354010b5146c400120540884610000310213041040303941c40b29000607444141c4c4c010090300d82580c00c40e6500403105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 78946980 1250 78945730 78945733
    0x90816030219030f02090c0412060228050421020a0905040506010603020304020f040b04020d0c02071707030c0b1c060b03010303080c030906070311040504060806060a0b0f0a05160b0f0108 82
    0x200e40d0700001c0c2c664400007603035045100e208005101c1d44c00e005a1000c0148034a4603a4001d001c0460161281d20203882450f00580c000760b1100c1c489030104d0198a0845411180301c0a00c1c14124003154000050301c0440700300c03100030f016030318907040d60125505e414000207604c401090004940e00c461039100d14021801001104c000380c0c0c81c0c24094080b44401e4402a600c803620088070038031860b25421690000002800243c1080621000701e02500c00000796017026822004041c400e54480010300d90040d08910014a030386407554407161106081c500603888a4480002d100300c40c0f480d400701c803006600394160204490b80d030383c4a00340c2c810f400a0000300c0006101c400803c0e6030840b40700959000303500090191503607440e000e41c16401405800350320001c6440031321001505585511a040040606201900181c0380c403100f0030103211200e03042810b4120082c011040307111070150599268640034140143e07076034a0400010048075946200070142c980190030170200e01c524441c3c083c101c075828070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 78948230 1250 78946980 78946999
    0x6020307020c0a080c090601120f09140a0201050d050403020a080a02010501050a0501050a050d1a03010e0c12070e070c150507020a03030b060c0309010503100f120c0603091101050a0908160302 84
    0x8040107429a00c80c420040d031940030a80021280c80e04214464100c0c0c0141010f00e448120010300340203880c0c0f00c54040307610ad07607108121001e00900c1982061021580780c0500701c1d4182d01c2d80003170007600a481c4450340c80c0341d513080010304060080020b0900c1a800000c60f90700d462084030000d002e000c09025050285100320070004895000d1410f41d114000f01e52900b030b0802c000b00322400001e10023a0070040e990032400c5a05046920280f0609101000080c041c2891844c1002030102d207071848100700801d50b00c0304104100c031041020006820680344d180121300f80b461403d0803030080c070014041142c514944000c1c0005079400058820485110761018400150701d401000303018064541210302070b40041203244031640c418402517602003a101c0e4040780003511034583d0345088006030008810300001621070800d00a00500382c400a1940d4903090000400e10742d14501c0041149500340d052010100b050406140a0203100010b80030300300440d030b210034030130112080e030008600c0300368010b060b640d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 78949480 1250 78948230 78948253
    0xa17030d0614060315041104060f020111131203020f01020d09021c12030207030507060207080403020a0905010510030b030f061f060509030a02010507080f0301030b0a05150310051b070602030702 85
    0xe00c0c85140b5000140351a0465031a10490302415505440e41540141d480a85600b540d03072540c0500302902c080c1c4e0324491809008900a42159050000c5904030780052140b0920a0366448050084d190751407454200d680302071809a107800d0000c1c129451035400400d0707421640713029a100e2800e41740203e84542c1024401580008c05111060002c0e102c0252186c512035010301a400420019100785025854031882d43c403100104d0700210380440d0003840c001410070542c070700501b1a80150501d41b40402c01c07549080000f6201d00c12105118040c9500c030345804c086a50b040c4a0f02002c10a181c060341d140d8a4801120110076039080d04020210f041d09001058440c490f200f0707150325583c00f41c000c010f03501c415001034031141c124401c125a0040200140103900c1c0305140910b000314030a1040e0082c42c18421241001d5510040ca100c4c280d4103400c55254039644c0c0015052800d0100d101c1c0018940c42d40a40c0000e10010346104a1900c14002842020401183e00561094406070b003662041202c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 78950730 1250 78949480 78949499
    0xd0b0a182a0215060a0902030906011e060c03180803030a0608010c0221090a03080c03070c0e0c07020f0a05060403030503090c010206010503070b0a0215070f03050601030c120203060a17030d06 84
    0x302800400140e00c048001818480d40c5107040340c104d0801083c04c0d421550300c403400070981e0b004a400011a030072880040102c8400e8149403040d420781882609109800c0602c01064000c400d403001c0c042101410045014903217034030114000e446d46e83c00f42c9a40f45081d40156000c3d202c02e100b90100c641c60b2042c0d402500740b010a00c40d01c2a49081c04c03211000b00f40d108400c5c403e4110a4107140d0010003a800040000c1d900c4005003103942e140c101441d2941003d0500504038529030b031041840c10f40c2041002060b00c0150308641744203904981d680141150f117404505422a036405c80c1f07400c418005000310504d500440a144294100c134202d4103803450480c012a141c0f030080c4181901540041402d00641c0ba0b62000340980d204e080c1b04480789802c2e112011901c481c0c003603030354201003540e0b6190800c3e11645801800d91124080c00d040c1314081105500800768074031010184651980800400c03415a21540344000800341d80c1c442000b41c43c0e085109070740300e6000120a4010524103000043d05416 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 78951980 1250 78950730 78950801
    0xf050723040e0604020d0203040c0f0602060106090501080a0906020a031e0207020a0302210109030c02121203070c0302070e0703020c0d020106080c0105030405010b18010609050103060b0d0b0a18 85
    0x14045803040c103161801244155503403000d89090b900603000d00180d00703010340394400340d03100d10301420121b80d01c03a2900490310304032103094100404640140d401808020307006450b11080311000c1c45c21004079581da500142c01800a44801401c85000182c09811298140c000351421140130b1094482e50101c075031007e0807880303298002500442800410405464540b000310349110310044203c070710a004003961070845031300410481c00329042c1c5a084055080854841810144000040200c5065800039205074000204184100000c150f0000c04051081c4040390060066000aa00c18144210090081d401c11021000e181c03203040621410184140204411145000058040c0410440044809a000420603100c0b5901c0d4031080c0313100d454412503c12003505040d45c2d09540d5050032001032400c14290321860405040000920846490740100c8012205030500015088150000704003200140e50001c2070800745174040748416940c2b42c002c1c10000d50701081d0140c03002d0038a103c64030500e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 78953230 1250 78951980 78952037
    0x109110319110d020a08030403060507030506060a08220c0b0c010e0a0803041106040506030f07081b0306130e0303010b040306060f0b2a1f051b0a18090f0507 69
    0x11095050008a0030240241200c55002501e608035054451b14140d1a551056008988441d9541c040044050340751081c10340260303040b078040785000344009000700040006401c1c216a551281c154070400c0201301441252503600540a001a42d501c04000f50a50002d14242c1c68550030103c1d81544d132036005c02e46519166005911600b16140c1c0d0712014200d55641c52030581080c403c0002249075542c3d54041d610400d40485482c016181c60040100040400f070316007800000e4038002d14030207849010903a94030400946003005400314030021000909220041030509000001c001301b4070a103800e0042055078002c0c4e9003404000e96a01020f5084683e0f8896080c40907001d20003500e81903500f420790003a090490700c4c001c0b18850403580c2a42885001302d0030805114420b0070210407a402c41c040d8a9000e4a0000d040364811181200f401042c03050104090400c8082d100f01814100c0408091018044801d0108036810044042100400f000d070303840307408a060317011940d12126588202400c4034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 78954480 1250 78953230 78953243
    0x14060301060b0d020a09030c0305010902011806140c0712080705070b04060507110102010b030706111c0806010507050a17030702160308040b07020a0b07080403021002010911090c0702030109110319 86
    0x2448000e1030f5002500002055002c21001c044000080759901c80703004043d5004d400005814241440003402d008501d000504049052410401c103454000c0c081040380c42e510040d80c3d5072500301040041c00c007042074202c00d0103161600701d038000303020780240a015030701c1c4104222030b00c56032100c000b1841c9020354410040080c208021020003d001d20f50748400c02c01c010300001c58440d82d640c000a0400c141500000001a814034140c0b00040c2e04025085003201031008601500c1090b41d0002c050081c02011030b03060080000d40f19042210810040181c03c3c2c00208908403d0b0b91490320365890392041c2d450300010f10a44e019210b0381c1c10311240c0306040740da1243d41c540c685031404404260640007000180d0340400c000c10002000e19400c001000d54510500019540e5815841005440c0102d0841ca804580c5048803d800040709803100758540d0328201c80000e41d41d5103144004440e485020402500355080c030002030200161441c051042400032416101c5011140d90042c2005003980d1000c2c01c81d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 78955730 1250 78954480 78954487
    0x1030210030b15160507090c17040c06080c0c0f0309010306053f03031807120b0a020f07081303030807020d080f06030304030c080307030210020304050d21090614060301060b 76
    0x80c80f280b100286801035520000040001c100d4407554180300303260380407103029a00c40c042c60b0941a40b00fa105008842d00d20760540d41c606254485852046e0140109414800d2002c0403400305500c0200b5070700310765201e40c211403000c050354510325100c3d044030441c10b021905003c4040b51030301e811031110702420440f1281e00314440c00c1c00100c1400008218031320040d0046010702c0702c005041403005510a2407240324203580d0202070105103240981c0341e408090782c0004071104400040680501540001c20f800d0056155100c000240c0850b00ca00000102070b8200021441461140c0d41c800400709c034042d44403040284d840d41c0e400c1e6100c401004500b8000b440c00800100010040300b00d00f40c101802801302ca04003520380e40c41c03c54030949030304030800c00d40c400b103898810103034100900c00d0003446e03154055043d8102035403450354500c90000000d003489843e8800319a03440c0b07103141d04007444402c18014403180700a801c10300018010061074040d41255440081c510382414003610b400c03610b0650a00f4035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 78956836 1106 78955730 78955759
    0x3020609100c0503070e030309060301180507030e0d0c0c08120304050d0507110f0d061514030f0601050904030e04050106030b030f0c06180402040302060301060801030210030b 77
    0x4215003000c20407102e565109050301c1c1c0048180c03e012038100c6041c03000a04501494201d03039006100440001154044100405142034180c10f0802c020f4030b4803001142500e0168207620111781c401084031115074403c0c0c002000b014003034200b041c00d141d114014281004080710400c480000d0100501c0180402803180d05134840090400300c2ca001780340e655030179a900b404040305200700ca0000034031019442d00094440c42c164032480400004200c1d0364116a401c08034007031518000100c135018900e134240000d60a800107078460041c01a0b070310348003c0010714440148101d041242030102810152128002e99000e8042d980b40810b0521102e01454605111441003241d5030b4840c0b18040c1e140c0d10382c281155280d000a422203450200c03440e021030040c0c13041e80c1c00290040c5000ac00012000e0f4030a80080c1070301d200f262050042c840341e40d42181a600c00c044a540c0c86019444c0186 = true := by decide +kernel

theorem cover : BRFrame.Cov 78776980 78956836 := by
  have h0 := BRFrame.cov_init 78776980
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 78776980 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 78776980 ≤ n) (h2 : n < 78956836) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
