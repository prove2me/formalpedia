-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4643
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:16:50.905276+00:00
-- url     : https://prove2.me/submissions/5386b4fd-e3a2-47f0-a062-a9b137199b05

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 834892086 ≤ n < 835071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 834893336 1250 834892086 834892099
    0xb070f060f06210b011202090114030f0a0303061503060b030403030c140d0f0f05010f1809140a02030d05090a090b0406080303190501270905070b031503011514 70
    0x55503801c881ea031014002d05400a02c44206501254003001d5643c09503800311400510070001140b40074035416403003102d40d40545800b50690038110a0f80c180c4400c02c407403941620a0504003403800340200038407a9100d001340c8000a0320b900300a46007a116054140b480141410103000300480e446c50030407070341d0054240c900080c40402e22102224414030900811550f6480410400180c207102e500c00d414200c0b00840420101221410301c0c0c0546900344580c3c2d19064034050100000d410f1952403146544400c40002150000c56036000480580301c000c0300ca01e50700076030050086080030030006000c24603c0c202076080401d0103000800301042400341c1c0da116604c8050010b05070700c031750300003501629044c4c0507071f44c5a01d084240c0308048060015044000d9003130000004110304030724512040800c81290a00050f154407070310001400d80381100f11454490f800000940446080146000301242d030b0ba6070801100b01c0041500795003403140742c89441e000e80701040001c0000075402c0c00c2ca040050f03c1d00b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 834894586 1250 834893336 834893351
    0x9060112170a120c0509040b04050f0f19020310061709031b0f06010305150f1905070c050105040b100b0f0a11070b04030804170f15060f03250b070f06 66
    0x110340301840c40303070451102d44c1003e01540d0701c00e4000029000440003a0b40c10488040803004001c26a5416201809034444d88800b2500c109802655160720250310124030103540d4030002074a0482e40300320b0b98120030086200052000d40c3e40051384412209a0343e6020301ea500b003000c00030352280309405401000451110751034018000900090210813003460694161b0360b920700340261a4107194660b0900c0c0b0320403c00003803282d021205964010054000f0740e00c22004075a013414010140600704605000a11042c01c000807800d002e00b6215511940d8403200c03a0500104c16484c0f000b9a40280020707500601c00c0c0c0580780c0013041640c04210f0185002014003e0984040e8181541d940100b104441c0004011060040300402001143c860181403010108091921070303c40e0b500000b030300003075000912841030b11f041810009400210091441d003c840500001070b141c04c0310075683c0c440020030303c854803650a1014284d40c000309000e80d14185880c80c603540e10074401d030208400400403a1740b6100e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 834895836 1250 834894586 834894607
    0x5040c0909020301031406060a1a030a090f12020105090307031d3c0109060e010c2f10080f01290703050903010b04061a09060d11030906011217 63
    0x400d0320081911420440d501d584070b00704044002c003003481c800c905100d610042420b43c1049032100f021250031540940100f03216010315902a440644402000382c0c442410303801040a601c040300e02c0307070f108030500124506513000290a40c0d60040005819400501a034008603070071a0842d01d440060702d0310540c030020000002901549070001000c0c000e40b801c004440900c15111060200b009070b0344a038407029034144011540014140100030014134000022289940180c500c2c41e580c038851000074141e0900c4022098401d6021490744100c6940501c445609081020310014035000d9403802d180a0301e000120248405030610600021030070000301500070202c0c8644040c0301034100d400722940caa2003401c00a013a60486d00c210340c801e52814801501c3e500d007038420441240c000d001d54034019200c94005c900540c01c034140c1035401030010080d2481715032417807003003805e640d458503003103030701d900b4849406458000160842d0110080003403c01c008185600c0310f450382d012200404a130707500120003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 834897086 1250 834895836 834895847
    0xf0306030114100e0105060f04060c0f141b0a0b0720180105030d030b10030b0114280201061d090115090c020c01050315060c070e04110a081605040c 65
    0x140b4480342400110502c48200c100c004150b0458201a070025840d980756400c02a192080e01017603540700000b0481000042d004130f440c02c0b070b4640200304100c2000c845490f620042d10403802c4c8031000760028903440788030703e03c140c0da0241002c6040d10202003950500114440a100d292406041d0801c50300390303000140d00311074800c0850b110251407840c44a4002d000c8403503901007030103018401d0203580c0076104150710902c90302079140300040150401e003100b2142030b00102482200b00d810014036400901085030228010580b41c00244040b261142103404640d80101d07131040908216414032204000c1080058064400008100100e01950f01c42003001401805e50300c400002540e076180c40000d4540042c0e01824240e003154007658030b100b04034401110640b03c122000e00301c00410702c00c10040390402c00e01038440c50210000b200c03411030f00e8607040c002c0d00c48111012100c0d948001d07480b00075410032400040c003c2c101400101003e400c200c4559013044424050784c1d010f15a1000403035002403040c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 834898336 1250 834897086 834897101
    0xe0127111207120b090a050a032003160606170309090a1e0e010e190b1e011401020118080d0506040f0f02030a1104030803180705100c110609060f03060301 68
    0x40c0202c806082e030f40c45036070150003240c010984030303054250b00003115100003041000d81280d000c1c0141c072503195a0781d030030f941452141c6449450004141c1040c40b00c808100000c00901041c010514140845894002c00755002c54001d25580070007000410620300002080d9402c1c2c181c11a10205a50384400c2980c0040c00200c1d446010715800000d079040f01c42d8654001488040400e000703001400e4041c1c030745e40d44d807001c5d850000a00d50b040c1c070980f800b05220701d000d55080000c1ca50744903105010440c0b4110005001e17000100307203440c44009404a580c091050a200d0344e500080307000002c0450f15809100d006104072020003a49074000180d20340c0d1743d036100031076140c5020410014940e040c80c007040290422100c07844618a4141c0e004022500203080d90100c950100c5490324554600d0f2404509400a484440907803142c00004600c40d030f40c641d802d00b900515661654070144490414000080c1204961070080030b04000030140c0e41c03622011900c03214442044544d0300c0d210f18022a0041040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 834899586 1250 834898336 834898369
    0x9200d02041b09081603020d060b04060e07020d020c09070302090f1903061103010506220317031905151221190e0a05010c0809090a0e012711 62
    0xe0035066040c0e06181c5045102c100781e10381d107440100752a0911141da80400250402820842401c10401450304a0700292254410980801c2d245041d0000c201134400980010600f81008010040000c2d0b0400c41074442881c2803005107680d90340c510203d9070307140d0041c0c640b008040d0001100015070b140c42403c0000690301508101030310400301c80e84144208a804115000c50400000041c4145400c2c20384e416238400804552038014018a001c0884a21207202c4400c954405000800300d1050142c0c0c404407100340e9070041c0da9190003900d00c0304000004800c040001c0c81d14052001011801d4000d10000e64103880304e0786101004001c3c249020f540d047d080c01c2100015103105a500c52007400390031841190710140f1042c46c8143c1003595900c044118043c2c2000b94100f041149612507005440b42c0342c01101000c3c507029403500891000d80040715007040d81a110740b0740761000707076003441507407018590350780554840c10300021058540210a1000340200304003500200c041da45100c0d209442d00710 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 834900836 1250 834899586 834899591
    0x2030c120a030c0203090303030a0225061a1c02011202130f030c0614070b04020607081b0c01090f0b0307030b0a09060807050a15140c070603090b07020109200d0204 72
    0x1031a8445841540c000700d48280043c1c100780c803505650340008103070742d00f00c00001c024509507a9151841b1001390001c103a107035030121402411139040c61114102a0005000740d801181003c00b0303148000c50500342c200c4a42c0600284407014203140d08040c0d0154000b5424a003d410f100320180d82840a4040c03103404091107941c0301c1001800a000d1080c500450b48103204420000c0d0b84c650003600d41c450140c4d0030b07040d10311080240d4400a115102115031082c070040c0b00e5414080d181c1c40b40e000e07079002407452075803d10240a0004900c9000c00070400104000d20b400c00000b4101100c248018071980b05403044210f000c00844c075500e0003908012a0b141019048540240c1e840032804003130036070b0b44a184902d004000e40400d09090103801e036801d84440008050051514410031a0507040c0d0b0101042601414401120324030403d000c0500101269a4007056a281a00300031a1b01d0002401c02000d5a24120a500000356400c44030b446206480007058901c910103000f00b41d81600194000354400d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 834902086 1250 834900836 834900853
    0xe1506030403050d0b0f180f011505071518030c02121f090203010b09130b06010504140105160204110c28020d03090b030a020307120c0e0f150304050a0210030903081602030c 76
    0x8918804503445545c108c400c0e90103990361b604a804250807990590f03000034800b0480b080100e424600f00c18041c076200500083d4140e150f41c0e04801a0300b161074110300046460110006514084112003914600c0d030740601074688803182d00c60144c020f0000c011044607211000c28003903603820b42c050001c2c210003908825252411410700c0d60b1105011000300e621216a60114071070354403030750564096500c0051102501c0e54076000668450b002003070800c00b02d1f01001da03840010780700c900030302c203210641225480d00c07070540268450502c1181003030b880c02848003281c1d2080300c030842c5605400680d01a1000700035015281400c40c0c11500c80c0d040306c8140000041840004442580150b100703510316542d0b41e010310548007482d0b0a480c3c60002081c0016450410740302036140c40b01e1200fa8120000713000030140d4544164942d41d5030407c55040e5110340101603449d055051030702107060404614030b0104008a0300340d0b005000c408014010984131001c440c0d1700c4003c1e0340200308440c4102c0a00c802c442484 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 834903336 1250 834902086 834902119
    0x1205010504020307080d121a040c0e03070e130209060604090207030801051804150c1206030506090c09190c360801020406080a090503130e1506030403050d0b0f 70
    0xd000645040f4003a00c9180000140003001080c0f071041d615480e9290400031541b80d815002809001c80e0750b044da40788070100e031866903031544901e5951708110b403620800c40d0202002c03d4105181c0e03510014954141104201c00450000f000310621070381180e0810054490002185260080d50428807506100203551424507401244450484404591401c0c03599100c1e9060b19103035209640040010303440303c4040e5004060341d017203c481183c0d6071404020b41e0b40064074110548140354030941d100d0b040801480782e1800f0070300042c0c4000d001070710200d0b040d0602c003005a100740503894018103250b40d500c08408200e44500e03035040c2031900a10705010a00d03502c0c050700d050f10078a07034a42d0502c00c00303040340000c1c0800103009540440d03016807103030410303550340144030b401900a00c0d000f224140401c0051141c0c2003542904000501414040000300c2d1900c000d103681c03c8020824031503c03440c410700401c000a0b5105080b161450031811303002c1002400540404c3c0890000e03901240d204402d1104640d84 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 834904586 1250 834903336 834903341
    0x152004030203010609060e0f04051204060c120201090510020904020f04092a09120c0e0f09010506031c0f0c021c05060f0f0103080a050409060f1401020c01091a04120501 74
    0x2a68000c90080028030f5032070145c101114014420716a4081056001400b007404d500c1e9403d5100d4040d0007940d4080b501134082e070700c036a44590007100c049032080a07000c0c1408240e0b0600102d41c81680020080410540c0315180e50b0944246c00c140d065030006a0440c0f503803103a40680e176002c1c10070400c55884030f481d083c00e03602074074210501c0540e4489007014043e80b080b0074417100e40f0a228544940e44003d0401188200009091006841070064038400003000520000c10501c00c0980b00c0380c01c1143d040043c4154250784024107203d1007544000005824041120024a4000a282049820042100c00a492019406501950001d0f000102c840f0000c2c8a001140c000d80c03280341618420342d1242000341c2c0d074642c156814006009030318014000a54058001c010a128178101282005d40c0c81003a0003c1e500140c04c80380612002150400a040c01142c3d443e40c0904240040d0031041d40303d0000811002c054410480d009603540c4000302d2906011045074043c001c0b81018419038491814030324003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 834905836 1250 834904586 834904589
    0xe0a0609090f0603230118050102030403020f0703021302030711010e0105060a09060e0127021315051e0f1612081006020a020904062d0e12030103152004 67
    0x4419081010110304610244605015a45d1204420b40040a0400d10341010521424510030a44d600c024417007891711056210b021040c410400581c1d02d00d0240340090902d660540c900a00c1d0f40b02030300600043c0c0d200049103600c44c0380d0500040c1c890b601c0301c004454080d036150800d0150f502c0c09200001c2c01c02d040d042070f8499030040d0b030b004401c10b59074585081128074078882c52402002190041c0821001c600180b86a407000711011901d0810071250325089a00103022100142c1506030100b1402e00000745001c2021a507080c040d0515024010381c0030800b03801c41583c2c200090014100c03101319580d800303490380c250414240600b0384680307152502c01682c10ba03c0040200f03440000146c40b035814045032500344c6200398040e00e010b009590078040e0b11040034208485e504d4864800c03244441c0c9081040720503580c030400c0340d000d880c0102c0c2140c00310340c040c46081c0da0503000555010070241010040307074112a071114904c0c01c550603400e4020000c001e6040d4480300718031007403030078103500c02130901500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 834907086 1250 834905836 834905849
    0xf0b04030c05062d1b0301140406050105033d061206080d0c0f02060d1103071e0906051c140a06080a020d0204020c070f120b16140a0e0a0609 62
    0x3a5951910382041a8902c400c101a0b1350044820f01d00d041009060300c0c4c90307600044182c44541340e1210a21302c1d4892a042600a1400c6a0a00420400e42c1c909809098001c003000e0038000c3c554109240f41a4009494040c455000e0030300c4030001c401008a50210041911a440c4c2d5078550754448000034100c030720b800b4000d00d1060038070f440490403140215402d4024640ba417160000c02c0c1c4a82c0c1d41025541c1d900000340c4e88004140664050ba0303c1c0c6019130720452907c50003840d62441c001c040075000d182c030710100c002c07040049400d105070540c101c40b04034103860305418096120741c0c1c00c200d940382c030325001a0381003c05400d001314652812000542c20b4040e0308900c1040c4040c0303031503810041d560040580040d52151082d8684005802c140d40100f01d0031032180e058036041a11001c03070040035070b41948052100c0c6095417200003801540640305400c55a40c1d080400b16418000d0b0041c20701c141da001e180b185020008607100502c0c0214000f40c18210003524040d2010340d24440035111440c98420b44 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 834908336 1250 834907086 834907093
    0x91e03080c0f010c0e120c18071b0605040320072d06020705131b08090f0708100f0209060a0e13050c070308150915121614060301080a0303090f0b04030c05 68
    0x104407004c0110700407c181001505150042102c00c0d076400f000319000d0551020304c00c40c071001d4145515400cac40b0307084c014003504007c1081e081628008046c0002982210800c07030920f4540800b445021481a0803508444220f08100c070f41e21900d0217020510240c441c01040e005d900001d500d03030b0040740040481d407049401ca0705c18480070218034103843c441c50804612660210409030b807640a03c000f40d410060b43d41c200d6100c210000e8095142000c0b0303800058044e440b080411400340b03241c0c02800132003400304805505007140c68011030b40320300461042000740f0006e444561155204c41e084000c0107102c41206000c41d040c20400700c0040e905c0000181c0004510500007503003c0c0c090039640068000152000906585005900d11003403859117440390b02c20220f5003c100d030154208644008a2604030603c0f00940c64900c283ca200c104804210380900c5040c0010045940042410701a640d011704000c552800c0515050006c43c0b82d00c1c10080c130442807a01440300340340d4840e001000d0720788074100300d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 834909586 1250 834908336 834908359
    0x31b0c0306070c0c120f14060a1503031b020f060d09110604050f130f060902041e0819050a060204030f0b01230103021b0703050d091e03080c0f010c0e 66
    0xf100c540c003a001000c0c0105400c0002003001c280b8101c44419450b029509264084d8001d5940310040401242c1703151003980240188200d142407445030520261101c201d1590040ca559809018000542640c1c0100001084000203640344d00d130641e0781801e00240015900e00e18810315034010038070a0720655503090110a5a586d42c00e01008840580b14010030041d5942d000c030381000361070307c2e192443c01c0d2103a0319850404018410341c007680c4090241000c0141e10b4a0401030214a824260802001141c0c0441c4003045405000308140c035450200d1a000c1d000f03210340f81021451b218008100804582c400200081409020b10003140c3d90780c41a8906542e0f0390303940035454a04002101520343c03e231021404c4410541c080c2d0f000300046852000c2c910205078102440f03e00b010304585c0161029081654142040c6038854617a01c0070300401050500001604001c05480c5825400024540320300041c070071f5407810b41080003000c0c1c1d84c942c070024050079425500062801d00094100d900841101c1e48 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 834910836 1250 834909586 834909601
    0x100b3d0503040c180b060a1116060f110a0c060c20030601060f1e050715020a0903020607020609031b0f0603041a040f080406031508061902090102031b0c0306 69
    0x3128002c94010b2804000581001c40310710113000c40654000c0c84650300d0424010a40303030000a0000b10610b52502862600302044141c28007111420102006c642d02c0317000c1c4100c2e5041004001c1d5404240f800304903c1c02c450031811314021064801030a050131407800043c0320b640c02618524454441c81c4107107400c0340d40c3c400c8501010010300c2110b0785900480c0060007568855a00104098420f00c1c1c04e07155100c03807079072001c1c0420400322494005074002030f0300c405000030044100040000b100046240ca0b541400007000b082860000034030a001c00180f00f0190741d2800c05a80206070b0046c1a141c080721440140f0540c5010781051301d0050340e0011280005203000c1d41601d106513000900d40d138041c480741403028207040009008603203c6240d0b80411000c2290742c3d016002400d1551000140c804681c01c0000c01b207003607640040c070103a0080781005010780c14220203900b0615130040260301c5142450050341503015031401c4d6420602d4800c071028400e2400075416040c884240c09640b034a0312882c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 834912086 1250 834910836 834910847
    0x615040509150601140d0f0c02150601080a140108030d15031a10030b091e0102070b01050d080c0307140106240f03020d15031101030209012703060c08040b010501080603100b3d 77
    0x400e04ca062b800707030b000140c0c0a500400405074030085074a00000c4a0f6050000c0c055031800a801c0002c1950000c140340c80001424401d0700700281c10060003401240c9145c1d82d4165101c22400b02005082c20080410058800e06540f00060350740528503c40718580707920b03060f56502c03844801c003800030042030301298260307018401c46000d2600102c1c0f4565517805c0401f4001040b441c000115010b50341009030044405041c409442071900c100302c2031180340c0c185407806081d01c4080c0c1209044d180144180c0303400f080e4080c1000f0741000039040000000d9034014017640203000f00380e030f074070203181c20507081c06d5002c0b040400c404160b0b44120950342c02c42c82c045004500324020b10441c130340032615007062484842c541b00d90303043c1e503801301c000c4441c0d68644030380e10101580d5194a42ca800300d0700410500c0200810401c8150141c24286040002c9180c003000190b07840c1c076984e00701c1200030399444001c1c000e07071910201003081c0c05c5035110044071160310250580d980000a07a0400c80e408004001c80d040754400d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 834913336 1250 834912086 834912103
    0x1e090902040213063605091003050307050303040b0c0315220e03090102060a05060904031209020406090204031e0b06060a0908120a180b0708030a02090405090615040509150601140d0f0c02 82
    0x20917142c1c00e400c1c200403d00c0410840642544a555009000080013501c01c10050100900c150007075a203e00701442e0840c1400d40140007411001c0d002d2040040d0b5048a48419a031100e00320380b01219110300c004007031401e11003540e03903401031f40c1032200319200c004002000f4031601c1000e9084491583e02e50f0020000c941080d203410342d01c0800440441c020070b214010062807803210b48000640070a0580c00101110070a502c40c2d40b130f482c0c0100d03042061200c01805150880800e90f080c0c041e01350b00b551101d2860200034000b0b80314000c00300c2c810310924881d900705805030981c8421504040c00c0f168403404150400a0171000140c0000b40c602043d0202d620968210b802004500381058226500c007512600024081030710305078248800e07030142e511401510300a201080c00b4220909058072040316000300340d0401405035044c0780c00d018510350b000070078170010141c07038181b050180c0b00c110040b40d803655116030401d9285404622a0ba9002c43c2e41e00c150ba0740081d038002080b20340070007002640c96040a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 834914586 1250 834913336 834913427
    0x1020c0c03281a07030506041103040b04140a02031e012316030e100605151c02280504080105070e18090111070f020405011e09090204021306 62
    0x9442c548107002016400c50903103140f0505a002d810003040070409410351040b1100000640c889081c0a01414644a288043e840382c040c0d01c0d03d0761030640c989284400c03020f48000e041200120703d0055102e01800a0b101d02c640c01416110080c03401149550518644e00da11070665181003040b0000303540c0c030440300d50b185135800c1d80e00d00c2c940d94144220f07090318190f01c2c0034000d00d611a1001907002d41c0a108020074411080400079155040038144a004100300b03c03501ca040c507040180c0707408500e4441010042000204026948900140280c16080c02c8440080c42905810003449840c940042c05002590721160080107030703035074204044440806440d10241c021314000c14458440c0c0010259580c0440d03484004a041955400e01500503400403e0982d009505120f01f0411468035028490040c00c0170103c08a81700301c10543c0c1c10307151000b031095030700b0a50365035480411500c81d50155107030200d4a00c5168107066481c08003514404c82107480e440807a01300350200015942c21100d20964415 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 834915836 1250 834914586 834914623
    0x150b03190603200109030b070206090633180f090c03030f03060d240c0e03010b010f120605041802040f360b090d1103040e0a110d0e01020c0c03 63
    0x3030603550b0f110111040d60b089041010f00701020000c01c02114210780100d013103a0050903d45065a002401c010000d0102005079460800c00c80c00354000740c1110204c41000e814504030304840000158456a03074035071958610090008204604144d410750303074401d50005090f580840c0a41040540324415100401210241800400e01e03504240401c11141031203032000f000d480f0741c20b0300c101442c180c469080d008020384a40c3c52031034860b801620310000c8501a0000c1c0301f80c80f1340c4800a0143da03641000a020000e25914280c582851500104001e020142080040c840e51030f22503a0070820400c0c06030b00071810020303284510031252113036440c2410303200340c40310207800007018600780c43e0100c0401c3d43d01c3d8680f4060b0f44c1c001c1740007100e8a5000d6554940184891090040c0c05010301141d02040c00c115001070204001060300000172640c4004111030020304070f81c20324000c1d0300c50300842e04000191480e040445000c0b00c015030082400680000c100e6002d48102001c2503500d2144010840c42c411 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 834917086 1250 834915836 834915863
    0x150f060512041112060108010b0415050a052e030b0405090a0c030803090c03060a09060b010809070306022a07090b0406030f0b062b030f0309080913150b03190603 71
    0x10601811983c5071100140b0b02c090100b00118030600e0b100007a04688100e940d83c0c040d6051914103480703030340000c08852a882d00803521b40380000d4085449440707180d0080030781c6d84902c00900c0540100c600e00d4040a4024404540c82c0e071001402401028020347c0150314110225030f86210001745100c583c0d510403010400c0500351340d42e4414940001e4031404a40c0310700303181c140300b030b507400c1c0900c40c400d008800e000907040c03040d42842c205584910051505001b90441032158810002c1400c1066942000d0090707a10b0301450703400000c040d0111011280b5040711620032a4094000c149c1c0d004460000409202d8140c0301c50802c01102c40911005044034050104540060021044942e01600042c210300c0c120001e03050010040c5c81c040c0307501c259280e10381d1004040540042224400d50b540d46420881861075030344130b251602c00c440095125201e5401107800d119050381152028680d0002504203090380c41d000c0010f103400584036001164121421507500720194170641048907040b0b2170080e03c89 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 834918336 1250 834917086 834917093
    0x1b030105060307231b061003210905100f0210020c0c0d150603080415170a051315151a0f1803010908030708070903122001150f06051204 60
    0x7070446100710841c2c00f140e07104c21060140c2040103006202c081d844400c1c07026814800f584d080c124010a42110454040b10a002054640107840c024008941841d940b019540000ba5204681c6600643e40046120300c100b01142d417142445032100742603003c5800982005c0340e0b450070b900820464155542c0840c070100c800b85071507a507156403580074688061002803801e1450307003070fa44a500161246440020b0800c55200940404000300b22078cca45034000e01d0707104000081004003c0c0c500c90702c0355101d0002c0780400742e8400041d004030380e00284041d000810203440c2000f600032106e940440b8400e8120024410300c80c03281100400341e4a444140c03400921a039010200c3d0001c00041410348400001e020303e0392000d00c036a82000d80a03028403034a03460031b014020030044000301000c00300514036508100190307840000112000a50401000510300000440090494800002c10b907600380300081d40c07051440c40c5c442080e038926071100d074016500d841c02a030301032041d1007091900d01880030016000c07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 834919586 1250 834918336 834918347
    0x501080d0c0602090307031a070f0801030b0919030206010906060206091c2105041217010302130908070b06190303081303031107030806011808060406050a02070f0b1b030105060307 79
    0x1d66108400c01400c040c2e41a020038513025a0760401c59404481c048100c42c0c0b034091504036644a0014a080c055109010074010303c00081071100821204100002c10b944150038270880003d504061152210f40c43c06e800c1c002d60341c640a100b885a018a000c1e80443c24600c0450103501c14070040c2c0091202046036115144400c0c0c0c090441c40401c150301c0c0010002400107001941401480840410141010700304490059040c07100042403042e100501220705001103c4241120740403220000071281c40902007025140c18840203158010000e00314041002e40e040c0980210001d44041c2194080050f4034490000d09020160100c0e80850020751808030420a041c1c0c0148a45404181c88845584002d00c60304051800c90200b0701820402440b5680305003c04044d182c0720b0b0b801c202c01d9181407229512400c0c0500082e00080d00c0b00005010480c55804132014203511200c0305094040c0f50074898140d500a580e690314842c918104e54455200038010f40b0306941008010300d255440340b144c140d60 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 834920836 1250 834919586 834919607
    0x1113090206121b0f1312050d12020906070f0605011d1303020c1519031808071a0408030906060306010f0b0304020a03141e030711090a18060c0e0102010501080d 70
    0x403883d620810100c1c2800040015042618500003401e4071801101ca41241981e0660411400003483e4000c1401080b400501d14903014400e040c08814403200a41c07840182c400c2d031044076002030b03002514104000da9840c0309520305000b1a401c100590325860120b9801005403010300070a01034001113908c009101c0f8103001c603c0c1c4a40100d5101030300800110740f038a540422014441c82d40400c941000c171040014440800c0403918003003003645000000d100705460400c40c080d00d0003401013101000c201c9841202c907842d6a070180b11103001c0c50306242c0808c0c075a0048881c80400c1c095a13001c80d00b41e04002400505a130300e641c80944440f42056205003554100610681c0c1c00302c19000b0000202e00544000c4c103401c050180600f503000c110103020102038074080d40040d102e40c4100260004921082100821031600311144401130721344441e0702c03001e40150101750340380c1148411200e0401c01d80c0d80c4840301020b99511169840611030006908030b4109216a0f005a0015440004100e2143ea03403040c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 834922086 1250 834920836 834920851
    0x10f0509061905041505040b030a021003150f1715040b0103030c020d0f062f0d0207050a050f0a0201091e03030806042307080c031303030f0603050109111309020612 72
    0x410b5541d446000409543c15000c1002201d91280e0741030040307042c10701903400134500603402441c00e080c065000ca1034022501076402c0803d0303070741c524030104a0503001004000340200e0f00c100a07265243c18500690120741440d004a6101e49030f040240f808600401c5482240c1041050109a02c1c5890540b0304c0304802200300e0f07005030000f000d140041c00a419001e8618002d03240010b00703100340d000342100240400386419420f911345001004d400040c01c100e546581c0503190144e11584c071494042d2801803445030043c82e9000c1c107900061903640004220030801d000b642d445095a50340c008411500e69119006042d0011020041c80401c1c0640b03209900407071b0180001912104080c803940b8044c0c00f41421f401283c0c481001d01c1100d0b0b07444610b19406c4501c040c40c3d00c0c0b85082a0301c1d5038070000120302c0e004041c10344480c00052070b00d0180d4001002150448000c0c0041c0340c541c949141c01400810030380b48900460408940950300c507208051f000c1d0b5014107581c0c649801008003130320824006200c030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 834923336 1250 834922086 834922129
    0x30906080601120f05060307090b030c0409020d17030609150117041401020703090e07170f0415020a050a0306080609070902030606070f03050d0c0e13021b070f0e010f050906 76
    0x1103203640c80621030351301d04100c140750000c1c8a08062080505010b1290f00c0361000fa414555810556a40400d400e141c041007181e0010305c3c0041c2d48040f40c0800d0036000d004d405501403001401d40100ca1000851145904951810242e03071130501e00c1104554203460b05000940340d41c1c2060654031101182a0072a008001c0c20070305155a600482c2664400c00e000c4000031101242000304403a10301901e900141c690802c01c00e2030510450036091301100030000c114660100c40410306000000b480e1140d88503141d00250354902c1c00480150595002e0381e01d24001928190300000c8260011803154020502c1c80007400d5007a1600140034041d400161155500c4401040100c1c0000c0c07601201e514030501ca6101c00c0e4540e4040f041c14800c50f800c120003402840314003d0f162555568180b110030411604c000300584500d071011018000700315401600801d0f01c1404408580c000f641c6290a0880c1c900380c2c590f181e1aa26101481800b801d03602c40d05800c1040c0d040420000e1802407000c0d2031030103246640 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 834924586 1250 834923336 834923357
    0x12020a0e150408010609020c1f0e0102040635061012090302010902010908010603030504060c0f0516290703030e031201030b0103120c2f0909010608010e0a030906080601 74
    0x3407080c90084106072609400280800201c030702800f600c401003011403000c500b869009100c070f54a0380301c510084040103072654188407010703034a54800d0710242c50040085440720384800c000792203017a40b500b561a42010325100d0b440340d02c0c03201d403540c4000c1d0b48680b102d04181c0c9031801442a40003a1a01840c180801d848100000c91010b02c06e90000a000b5400411341032101d00014001e808590041c140d0b90f41020411b2000c41c0d00141250b04641c0300d45081e003002d480c0e5042c0518220003141005100d401044502030281007040810001d4901c1401c055200200c546031500051403200c2c03c0c1c0302c1c900400c5c081c400102380a43d1110900540b280c0039245803075101c49180f480d51a090304106d844a4002d00107005000b0305031400f9101e4503207030400d0aa0304a1540341c00803042c1140d45001c201c000b001c0c550314070105440c1c01709000e8800103460a05942040040d9034060a0700d401042507075031901d1000c03645000d0005003010b03003e4142d1034020b4180d090880803542c113240103007110b0510030100d00c07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 834925836 1250 834924586 834924589
    0x70327090c05270a08070b070f060b06030f070f0201020c071a121305120f03061201020c0102070302030c0c040504020603010b070804170d0e01020106062a020303070c030303060501080712020a0e 85
    0x409103c0c0b4400c0e82501c0004001450030400b1200c07440d001401c05900140b0103014003140b610855400d1a0003480c08140c00d00381d458030402414000d188c103604260f0100a000c96500700c1d0407081d0180c11551180100070481c000102d00700e004010311000c03507903c82c80c001c2003d1901d00346051155045840b18034174056411110742102c25056403500705001491504006108092048580305640e002809240222041061240d400040e11881c07249160340201d5000d10390950417280c03144100002551a4492410081c0d12604680300e00ca900d4001c3e484064840c0c54644a80c2e8460340c0c1c0200b40c00c0c110b90904440e000b142d02b003a28110780c03420741000049449604000300081142c2004021b010040703040c0d4005200025540215055a040450900a0941000822004d00300c440e448003410b2070384240c1c82080100c0d03000003070f41602000070030b0000e0010810126043e81e020340c40602000b5580d00044403410812204e40d0005074a01c28524040c020a8005098a03031091628802040d141c40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 834927086 1250 834925836 834925867
    0xf060b012109060b0603070c03020c06180f04150b0a0909140c071b0f2606070e0d02100915080609181c02010c141606110f030c070327090c05 62
    0x980071404078014004c08d06c10180e040107003214a000030750f60703507040c2031a00304030903000011a500d59204900d1605400425200c55000c01948040b03c020010101d690b80c03190300d90341d480200050001400c10b0004519100540604041d03c07400390380c0340240b544e946615903000d4010020860b113002c032407040580c40f41142e05000020701804580102d03c6482c041c90f01000c0004802c8112017443d40c122010040b0602198056001803582040342041900c2c9000440c1d0803820f0f44020341c0b240440c1c0444000a500051500075129400481d00c903940042c04140c84040c021031b030055111113000b00054132000c28400e0560300e045054101e8650dc20009160001c010421201d20010b0303640d20b0020403c02d60286400000c0701c1c0b0710510310310b0444441443c4210032714062002d0b21454a41f807035044092a0301046804240103202520344a0804000c00c3c0165800740d42b0590000304020901400800d541301060b45404501140400783d900d0400c4030b8005e4842e084000e414484244065228001d105 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 834928336 1250 834927086 834927091
    0x31918090b10030504031706011412090106121718040c0e0a0f061707020312191103130204050402040b030114090601210816020d0f060b012109060b0603 67
    0x2400003003902898501800484440300b5010030030103041c1420300c00401d4029884000c07a09440c541310405070307a03450041c0c2d00d25500302e07001c440c030080001c1c5218005800c50003080c0078042e01c0b4001d0009a50b910464442c42400d188042d006640556002c8001d00840004100c010000d007007101c0c44103000e0000a04807184c00046001255580b0030319103c1d0b01d8140c84240141079212940d903440c9050910082c00c44d1111500f042202c2900404a44502e00803c00c2d60b1003101350740464445482c000e009448102191130325840224146190101e4025620064030312030f480e50070f40200014130035003c11010b003001410a03038210381d40355801440d94600b0300410500313549a0030140003600b0000e004a1900c03030141c0c0b04103031148031081c005001c40c5290103c800002c3d00704403215140c21524084490340403100c100250301c000c072408001c1c100f2032901444926640201401c0000d00b40350001940c001058110402c400141080030401c82c0f80c0301e83c40540c1c1c0d64028000010702008510100310254410f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 834929586 1250 834928336 834928349
    0x6050d05270d09080313060302030a0207050a1202060124031e181419140c0303161101030606120c0c15140c0f0301050d0f0b0a021b0f031918 62
    0x80042d2514076802a000c84020088000214540b1100340380031045242c007402081d04041c0c0003c00303c3d084290540503901c00c10381140640304201590b181c51844004088450809409a07800010300c1c0740e0918450782d0501d490a14454074541201c0e011070061550f000210303a114042c01d00b5141181e040d00c5500600b900b038420740c40a004c0b85051031348030302840c2034201c00b0551110001c8107440c0d5a00394611074456201904040445e9100c8809003800301344901560140300206900781581c181c092240089030150320780340082000b9500440540d1100e00030700011880d10000e10100034520303808911284d03540c2c41d21660281c010366400b10f990707443d00c070610822901d484d0a44d91900c400040741d50001c1d070455445284c43c81c400c41c0c080482c003051041034451107075100e2480a0002262042d0956944960002130f0362030701024002c02904115400e55040000700c0000215182c00540c041062444d17400440c1803040141001e010b0a044884000c10010100300c21101d00401c4808800503045 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 834930836 1250 834929586 834929593
    0x201120614010311071104050426030a0f0b09160909020d020712021908030c070218010f0b070209160306120309081b0d0f02040e070e040c06030606050d0527 69
    0x18150004081d1a00c01c004c403588908100181c4000683c0300d503a038480308a0649002c105a074590a020f480c14099060131108034a03007461000c2041d034018021413242c0102c4100b00050030a481c2144112200c180036070360064048004100481000488200440c000340b400440f015180c1e020901603800c6000c3c0281e00c5034021440c1f00811001218080d44101c05200512500d880130807042c001e610921400f07041d2900c0040412003c0312060200c644031034001c0c103555200c0740c8483c1d92a40420092249407859031421201245000b0000112240c40e42c006003d04004c5d1107178180e81111414082c84901850381c2c941c80095540d0845c0c131650107040c0a515000c0c41249003080b60750a040200701c08101610210542c01035a540e180703804038010f03810a9065031940300600c0400c004018802c0c0c5181180302c1d540000401c0f040407030b00e16100c3d51051001d15000c070350303a80c425000c0e80d085002e00030214005002040c2000741c140d002c1544182e4903402c0b8040740e851071300b0304900b400d45203051118581 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 834932086 1250 834930836 834930869
    0x902130c0519020610140348280503070e0a0b06091305090c19140303031608040302030f04090605040e0c06190320030601080f070e0d02011206 63
    0xb01c004020403a00406002034981454020b1002401c0030072801010400442c10400340040e8400704010448034007000104140088881800f0029204426032600f030315100f84042c50b0f407801494a0700c010039601030001401c194002110168401d4006200000203101341c000294955041007840024144a403400c04281801e5020503380c44840c42681c2c080e107410044040316480d1821141d9080110000002c2c031a191040340038141109841048d5001c83d5400e46070760140e41161940381100d85141c0741c0c12690411800b49500c0740002c0f540000e0038081c2030b1410110310f01443d40190301c28401e00c141d03460f01c00c80202403038103904260481e000c0300b5070340c00c000e021070b04082c880c0b001c020000c14010490004c0110000d0303c1c51040c442d10b1301d00c1090f03108003113901c2d40c001d070440a004004241c10581d00c613541003c000480c0c0044400c580010010400310f29107203188503055008042d079a5030301c000001c0c030f032040c80000400d40c45c00b00d04100c105030385401e07410f600e889014041d1044246049400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 834933336 1250 834932086 834932107
    0x804050601060311120c19210614190b03090309090c09100e040b0d0503030703051b0702060f07080d0504140724091512050f01180902130c05 62
    0x5005030420b00038075203800300c05002104a1000d80f65154407020400f00140c4d612251000c4502a01c542030b28020010010302c22041d8111180710000c01c90700c00003ea61901d01000002540c1ca41d1203041290a10903071a203c480c10601082650744241c0c00841c2000d540c1c0b003d00c0d82403548100d07560b0f1b20301d1704046100c203814540503d0040c0c100000000841c10500304100191049400101190038094264180700d00e540301e0b604518a000c0d17004102090829190600c2a143c0d4422110342c4000380ca000c00154482409402c0000c0d444102d0704a40d040000950a21000fa805000a90013a4100b4040380c00001c840b40014011000248000304241c00e091400500340c41c2c100c90806002d170401c0d4410701502e01c0580b1134001c101502003d0f19030b1526280c0043c8e550580c590440c400782c4079410342045115802c17030054400301141e5101000350380d540d0040380b80c20319020f0044000708648001442c0b441c44a17a008a400180014a2500d0300d03141040c01c1411600700007000b10201d01c002c50104c613007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 834934586 1250 834933336 834933343
    0x40b09060a020a0f06021e03160f1e030603060e0601060203041202130f0b211011040e0903120115140702040b10020f120403030804080a021614040e0c010203030c090f040c080405 78
    0x447d044850a90031414007034071070340c20864142c00010800040c0c5c841250068414112000440341040307a2035580d10104500030040c203100c1c0016641c0ba401c0c007000b520521400903c041c1201c100f13501a500385402e21000e91001075480800782e034058003001d01480121500c1c4225090200924400503004600d802840142030025049003a440c1c0c030000d404002c1900403034081110a158180001e4102c0017104071159030145030422081c0303040f4070040141c1c4000000081000c1c2070705040120035030383e807000505881d2450111007000200507002c0c0c01c25169001000e0040d4900c001c0c40860100511008038041a18203040c000050748001480000b01409000861400c0c1e240811180382c5802c54030b02401c80640544003d2880c007000510103030087c828040307840ac01519018504a4680d50407042090154201348688200d143c4580041160300000d10388007100c6040e0003560a554030b060086d4101d41008048039005840d610140b8160391ba01d202d0004400da4644a020072428103040c410724 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 834935836 1250 834934586 834934627
    0x9030123130206091908010203040c06020f0f0307080901020a0f050601140d110f1314010515130509100513090c0b1204080a050712080702060c040b09060a020a0f0602 73
    0x940c1ca0300d100c41c805a1111003c84404280c1038604800800341d101c1c1e2105940140d60008850f54400700500c4100302c01d800f0303d50110740260782220000e0515661164030323030201002491f02076100b041180f0006918401506e400141401520817984081d00d400d030f03103181044070845190308507400500c81947c018150001803c0300740d41040f030300d07001f135036905018080c1c50390254880d40e00f1b44101103c4c1c2d0b030340407031544070900190703030511014905000e444903400d0203008551003401494414000102d004094480d141c4a0740b125011191800e011b0100300e40026259603515800c0c1007012405c0d481e64a01c0b5684101d030020b0020f08440142884c5900c105160408a008541000092111040411701c1c503006900b001c480c5941d00e152040c00c0e200ca00c00d4401c003e04554a41d800644031541140702244504165001e46403a42d40304000071000d0711403800741c018403200911003802c103030a000340030301041402401210448165900c0c0c004203c0c08440d000c8078000d13000621000800400e136045003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 834937086 1250 834935836 834935851
    0x60501080d1d0f0f061b0c060705100908090a0303180602030405090703020d0615020f0d0806100c1403031609081c0e030c0901060f0e0a0f060f0509030123 68
    0x5240d0391018102e0400d210181000380e125000c0400d50b400c890b03540d03e51442c080c0c2d900034030035565184580c040c0c02d41842050500801130040d03521013012414a0402c80d040e055100014004103244220510002c0020039819030314014240002699134490b130f01602c010754065102c104501c4245035500101c000e1941000085400a110811003030f284c0d9846941c20081c01c0c100543c42d010a0a0000000c04850340900c04080c0e450b84603060181d00400c46141604031ba205503890800c1e001015100614203440140d005202d03514141d103031794811023a42844510800c402524024240841072071a0415250b100142d030958408880c003e81107800e071001000000f0241851442e40032001d40c8118440040b03800b804603526905183c2e6038148200100750340014812009943c440e01e000b0220f61900750900301040d5034012100c40d502d80101c07800c045411030116040442d04001e01141c1ca4051860340f641405410702106041c0d90b000c5c02100d8070101ca4100340c1c1201c8920038040a1407900c082c1107013 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 834938336 1250 834937086 834937097
    0x31c0506060a051e0c0703060b210318060c0a1a0a050717220506060111030705030a030b030a0c150f111e15190b1f0c0201031404060501080d 62
    0x16034456049403da440504100a408613801c11001403031361284201d48082905010b550000310030080c0690010350307185d4003602e41410800c2e000310980358403036200a041100e6441804034400400c5548a902006e8802801c0c09060545c0328901618100704004102c44d036110302d81d000d8002401d802496548140034a00901c04c905180001400500584a81161031150040041d90190604d040807480c940340b281c00c54901041e41c200301c0e0304c4003c00e94041d40055180c0d0820a410000003064804154100c80070303519200840c44103800421504040e10f4250080d019200c0119111044141c001e1100c41142d0560240d00803000704151300e01d569120502c43c8800914510780d1000402001c0360070035400e4000c902c00f0441d102842d08030b0281503281c0d00c00a02c000c00200322580b14440f18490380f02c03401480101809000c009142c18554034451030700da619520701041910503510b5480d02401810001200302c40c0102c0b204010300100c03029206d5940312001004941d004001c480741841041c0f810 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 834939586 1250 834938336 834938347
    0xf0b03061e04080405060a0206070906020703080412060b2d040203090a0308063d0302070b0c0306040906020a26010609030f1407410d03030905031c050606 68
    0x1010300e00041e840d45100314486241c0080c0801030301e41d00301c8000c0c2c14010500c94944883e41e6009584207004c0342d500d0005803e070000003800c03500010b14202070301d03440a28141407a042550f669000801842d0a580d515105c4420540340d07105c802140743d040740302030884100240e0001c80c120b40c0c101400c1d1034902491041040286850b00483c00c1c4c0c1c0281e13410301c0d14141c103440300c40004a10680c4100c40640d07000308580f91541100078005001078009007004a2441807096140c26001c90051110180031465041c00155111061700300450744064020400510741055490705800c1380c00000c06c2c100801d8031501c03000060301541030f02c007513400c0510510491540c10650020058030240c400100780e080c0c66100041000b15100d007004010036140704850b0750a640c3c0700c1c0082c0d206241d060403800441c45110741c0c0c3c0e040c0200509086500c4540301802482182da905000000e1070300c030b0046c0c5c10980e43d8002070000030804d20080021414000c000300c2c000305c860500804940000d03000e00d01c5400c0c10050b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 834940836 1250 834939586 834939601
    0x90402040b1605070b19031e06080c090109020a02070b03090a0c0b030a0b040917070206070210180e01081f090f08090324040201050a0c1b0f210210030204090f0f0b0306 74
    0x11b103c4202d0442c40d0114000c640100d8013149024042c0704141001d087c440c0101d91000c0c006102d0100c9a4100d562004a90341ca800d80301c120b00c942d65140c001a04030344018440b00740424000d58000300c1a0003203442d0707401d0710307291403000d60a80e030006140001c00009001203400280518072680c00704660400207041d0603a20204404c0c0c1c01406d281c00300c000800c1c00015555554103490f5030a402400c80804200c051200404c001031390450305080c0d425050022403c40b4888080c107060b00d03c4040200842c50800031a08480040080801040340d20781300c0b4200000da440c212442214890a0615154448001058200445232032541c0c96140c4460011100c8214980080d8000342c080c00d05075550081040301700c0301001002030240c0990360025824149441d420201011510768620303d02d0001d449800414042d1151503c4480403800d8084a60161a0000034107841c2d08607814010b00e0030740e071085084151342c08000f21407691680d4617203035000c040550007081d044480403009081107180514 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 834942086 1250 834940836 834940867
    0x181814061903030e2e11060f070c02130c020d02071715040807201c081b072c100e0103081e0304060504300302090402040b1605070b 58
    0x20000d804c01280d108070701415203c034803508150003500843d6140010103c0c0d400c40c1544031401420700001e0a0380340d10300d02040d0100b04d05020b6000c82d0032101258483c07400072940c03142d00e242d040c0c0c0c2c80b40c4891020f00b0700c84840d11075442d4481c2c0d41d40140540c1110540701a00303004442c2d102c1c0036408055422416140e4020403041051240403001c03000d1501e80303080884850182400080c01c030344d219608800c4802d01c0e001c0400211078102d4a0949440d0314083c2c0441a000c9214000d14142047c4480c501e60281c0c0716804064903068130840300d40c3c82d6035001860080e540450400e005490300705148002c80c9492640341e91240700640d80c001c404d80741900720180c0c41d105200260000002281d85810100454410018000c00304c3c00a520390405051000042c002520200c0c0c0d44403440d2003006004400c4d0080105144c0d008812003030180a0090a0740039610241e00c0a5102d41e081001046540005020f0418040418240c2d0380360319140ca0402c0c40c00c00a500051107050050080681c04080c88 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 834943336 1250 834942086 834942089
    0x82503080d092d0b0f280e061f05060a0c03080402010e04110405030709020301140d080c03030408180102070b1b01110c010509071410050a0e04050c0c2104061818140619 74
    0x20583c0b43c01d035640d03071b1210008044071410410b582c0221000d00400030b0844c0c0044042ca150907110410b8207a89904201c030b648100507400b40410401900440441d019001942d8424010705140300e089113140700140c1200e450a5002c0d03102100418140b001d800e0402064000e000341d0741d02180765505101c3c010000442c04040e0b20311400c022002001004062019030f001103a000d81280d07200d003450b24184a054003c021400d42c400e00c2044442155031001442600300c5002000c1c80e46844850140c4040c00106d0500c07001c3c0a41d201c3c0f40b07009120320968001d02000c0c4440000140505101c0d4645080041e80da2040240741c05403c000e4200d5900d504000f40b041004d82402c2e59241c0440409941515140b0941c41e032092074141000b42c00107016008103010381075802911003801c41c0c1c41d000130b5410100c040c1d48001400a200170f008440c010300c7d0f40c2c0001010182041000756446407080310304010b1003080024180c85040c1c80000c000b0342c41800d0b40007481103481c82c40c45c0080e491054040b0916 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 834944586 1250 834943336 834943381
    0x2010614061b0f03041d19150503030309010b03012a0810050d140105011d0408030601030e1209040b010e3007082503080d092d0b0f 58
    0x160002050b0560039103003030160030401928503840c0012051034598101c1d00c00c0070b03081c00c040e101c851140d005001400340b086000a010b1a14010703034030381650041071071100990090342c00c60400f160503030381003026600c82c180050001c40d2240550301498203454035011543c0c4800d14424010890a080c03003412100100c8a25000342c259130f9680c004803412646034045900800710212180c00c3c00207589100703d8000340c1784001d110f980d980f420012445044203844415045818010038005101d8100458010310145400305a042c07050a4045c02d03c40341420401102d600090b00002074205805840070f800340c00d003492000f08441c0004905105d0404020185400e401200c0702d0001010580e042620301c030800481d1f05c865207406e8015501d81d442600000443c0d0440d007515080c6211050b0300c81030781c0d4080d02d00c6080020f149010000303041d45040484179180503c1050f5218060510b0005101618105c05009c2ca08a81070000c842d07603000c3d00c0000f880352103c013048489a611068503c51904 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 834945836 1250 834944586 834944599
    0x604030b0c04090509100e0d090b160b010b04140d0b070f0c05070602030714030a09170304030b04060212070c3504092009180612070f1502010614 64
    0x350940110207910498118943d0f040c0742c10280b01070581d00013080c2980c02c16004003045000c40c0d0303501d25682c0c0c2a00409800010b1440d032000e01c50030721804081c113912088000e19003080d203042d640342055a5002d801c0000500c901140411083c81b0144100320440310613030b006200e210890b03c58808030b4034010b04c94024010100d101c03452042c441e9a42d200d85542000680e0400c1b61a030600170b41341d5000796816290781c0c61a113103503881030750f01108403002c0c4031140d21803d0f07080e803800c01c2422125008074081076203400305100010120304064030301d41c49188240001a41e4484030550203400580c007501c0501007003000d100f400009860202081544410040e100b822601824201c6403036001d40c1090100e0f154010800007210145a000064984603441c01c45c0712841c24515050224040d450032960320940400c50165841d9030110083e030003103005010a0400003a070315400f85850965440031070f1140038100d08211a8120804158001480340700900145141032007540e0450b0608414921600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 834947086 1250 834945836 834945841
    0x70c020d020f041a040f0e030901270b072d060e031c0219050c0d0f0c061b03060906051e01020321011404112b022b02090604030b 57
    0x151040982c201d2940010014090004d00c0302e40201d0081140006602031030402e40c5201e4143c0183c0540c1005440306402141003051205c01151034000040c3c82d642441000005080658420030f21040038044c00c801041d0358043d580f03401307444040c44100a4122004031041850800380c0d0381c0c4104215074001e0300c04214404070046d02800d5101d01000d40c402c80d8403a8100c2c116840c00c0c3d0300a41790f00301201082c41941e80342260151064452024504800c1e0000f6501881181c081c84401003c6007480c03821000c1d4140e1a41e40d08102d0340c003070031013505610400f4010750036941c2c0340c01181e02810300d2450500a480c50078000c2500d41606508945101203880c0d2815040c0e48200190b5083c6020712040d69410701c50401d0545101401307005032100341d004c5080e0113881e410b05015182100502800f041c0c5030220765588034001765101c80400c07581c5032459251059080490010b81015031000740b824081c46012046030f059100d012103890740280c014490040310761390309820758003181d8200c5101070741507 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 834948336 1250 834947086 834947089
    0x34060f020f18090105151c15181d0a0206070501020f1209070602061003110a090e0c01020c0d0201090519030b04080307021501081e070b040e090d0503070c020d02 71
    0x3802001e00d040860100454100000d0548102c06805940c040e00c0194490340c0360f2080c005804128130002142240800c80600400d071240f860860020860100190144c080358241d0000c03600b903030003200300895038104075402d00074a10440c264108110504040d910b0254481c98a45450500180c81030001040d010240002034046903071188562640b2544c5085440100301d41000a4400d0304141c410b104c0d01064450000440c0d600594000c004840c0c4d0616580d00e1480d103683d11060b06401c03c3c0325641c00140851076004180c40d00002c0b9010340344d2006020002072600840d032040611078071400c0800c50150760840481020b03118140c2e2080501032012207442c0300314610303520041c8414802020403080c05011030203140510650350980f06404002840a45011401e00500945801c1311420720b09041e00e07940a03141200c1c81400f42c4039280c2d0b44070b502c6807032908070385e02ca200000d441104106003aa8180440d2100e603085003006821800c2926002b4980c07104201c000707028901c5d05505d2401e5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 834949586 1250 834948336 834948341
    0x705010209030703081903022503170a0c0f0513030b07051e09150909010603020306030c0a17060c1206040b0612090a0201110c031002031e04030534060f 67
    0x400c0805803c59040d10782e2850400300760713406420000d490340421204084203c0c4280203e40803200c2c240400107060036103003004c07070204e04582000c0741800030f40500e240218801c084034500c00d61116000040003103001c48064407244812070403c0400a0411807090004000c4400c481035035000060203506a40792038042d1410310450400b6070401c480202450720bc610510300034109181d0503140202c1c1d180d00169020315600504e2446544654601c005014a5200e0b901460b80184010200e40740c2c0080080800c64030342590700b08030208001181c94100b0703403e040040a0700700032607000780c1c1e2510903480041c2d0690395002e81154815510f4107030641d1156503840580e51010700024071070646050040c0135541e20345080c80f04038003042644200000326032004c51070343c6030a9405005444030510794520140207600040c0480495444d1249031031252482c0c01500380714501c651252540c2d84095980301e14691200c041003c00304640c400105120451042c00d411125030200010440090f1610403001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 834950836 1250 834949586 834949597
    0x2e060317130812040f0e0c0702090601021e0105060a14010c0f080d0c1d0a0f060c15050420030a020a060f11030307050414030c060301120f08120f090c0a0b07050102 72
    0x1070302c56800e0003d01c4501690042086503286150418070b81d954040c10000040220303185282e11106201200240c2440b500300c0b0741c4582c051050343e09052102c2c0700e0680e10b1a00c07510341c6203940c0d55001004101d09001151802511941c2e001b5030755040f000c2d00090031310b000300303000400911204034450b007003217103082c01c2d00c02407500c10505100403240c80000804002c889045107603080800120207070a414a80800d0703050320740d01000501d405003047c00581d02256003480071941b41c40365041364099100c83d4442c4601851281d40010040d400c00f010030400302010718000e40c40791300150301c81c000507a50001600d00700c841034200b80002407403e1906031011121100c59072000e000c00810003408551210080013501c42114016100080303c1c414540c0e1220341c440c01541181b0208010702071000b14441806140c1d210302d240014020301940c0c1c007a02c540221100340000c10800c020f01c10381980e101455603208900d00300504402c0c2080b0001100c030b91103842078030741c003840006044080c003800390111007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 834952086 1250 834950836 834950849
    0x130e061308091c080a08150109081e1e1c09081e0c0405010807150302072a03060e010609110909040809190b0304061b0206041209082e06031713 63
    0x3d4481060180252680c5800c56140c41c00750800c04500381d030356028500034020b0301d0722000204095842c140d8002150700b00401942040d114050300701040311280c600330201014448003a0181090b01307000300000c082040003040034000340c0d10060180c07840000b40c2c451208003103100d41000880d0100200e0030880e194410581181c01c1c00c4c004240e428000130018101c5203e0f5007042c0040c00c000004404074018410024034682d1411492030113076034006140194040e03a140c45c131620640d256280012910403036945c82c451394582000f0890100301c2c3c4a000418400584054a041c034002c0000350103a400a0000385004000714401500e5210780c1180110810040160703100c0c1034566000503065001141c04852032400d1200d400030007220b0005000760031f0256001003a1945440d0b440078603100300900381404000c0703440e030009150340c030030440d47c460300300d0880f50b06090b201d10316070881c8052081416044914108401000003980d0508171052441c81e4000c80c40d02d590a03d1410300c0d00082650000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 834953336 1250 834952086 834952103
    0xf05160804120f05060601141602030f06070e01020607030c0215190216051e0706080a02070606090504020a0801020307091e030f03053103120e130e061308091c 70
    0xa00c100541c0580e480f401d075000320105c801310fa070b41100440c6c19403070008040c003076503505000030540a840c0390303400010f55200070240c2e071101c5510100c0c1490310f0030403281da81c0080da000c1c0d89540710356014401c081c1c1201962409010200340f00c200030350b442a1030380594000c07080d058001514032007400200300742d202404800795600c50b8820528403442da81240184e48a02480c1405041d41440280c14071105078902c1c0903210300b51500c2402d4850320002048000300680130800f100014080744550b1300540039001d00000c072414140180144c3c4000ea8000d03070741580c410400c0c480082d4100c0117400440701c4040e04541d540148804181001c5010b520052800c00b9044088041540040180c84e84803c1c0242c0070382091203020703038220482071041c540381d1002e110b90f20038808144a030904460004060a200106811080106e642954884007010065035a01c0e507000040c03e00380507490308540040d036550014105911044554841c00e1140384c8a19043d524020300003440d94180c201a0760440001c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 834954586 1250 834953336 834953369
    0x13110f03010c0f030b0607050d12090f0308090d020109150c020a02040608030a1404180902042406030e0f0d0309021201240e0f1f0527070f05160804 65
    0x6086039202c2032060f00824105040075030305080600c10f031a200790b0000c0060000035080141541c640610404285222b40c603a43c003e804600300706841406548280c4d500c8802e46400c0e0740c01400c080c400e0500200716410b00c2207100200b41c0103002c00d101c90388000e00010390b41a207078405a00d48160700d0002034006082c0100040d02c180c010000c1d020152403911011505200a083d0952610490213200c1400c1e901c08401c000415065103d101745500c00303400000e03000c001c0545031104051222030700c010181c104200b4017031180d1501456030321358044001821030351145020303140c6401d2640e450904141e5501550380640d034980d0481404e440900300204000140b680541013004250300c001c1000e441246000580f0f40c0f01640070174800e9500c0e51341c2d03a0b02511103407864442c9071144001d54901845411011a840c1e440380b07041c1f150322040d0040100201c5020750149030701500108200144610000045d0f841070308001103400e42c1da00d800610003805090b141210060180e0307008581e194200000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 834955836 1250 834954586 834954611
    0x702280609230703170d110c0a12020309030a080c07030c060302040303260624040830030703051009020c030c1513021c0605040302030d050f13110f0301 67
    0x104000102802d605030103018a0a0030040c2d40c0e001684401001c010034410b041d001e0101c48000341c00c4000d000341c0041b51960212400078426004580f0345a020341004410104014800c0c5507011078051600144d030901c040c41d030000703442c0c40b030700c1174064001a0300017409140d07020144040b40103540d010b260200c0d0700340c175010000d0094005010850100c1c0f00490403055070000e41c24541c9000050701c0900c890340e40c41c1014003480090042945100446e00c0443c4081440d140f070291020b0544000141100c400c42e04808840200464003844000078400441002c1031070310084a038000303814200841c01c2e1300c0f81c444100c001401540b081d500244003043c400f184031404401440c034100e000742202d6140002c51900035030810191081c03481030303c0806020005051000e0782c040e41c019500f142c18403001d61b646032071003030703076805c480440060300001040c40d19510148151500221104480801403401c40042c815220b4200c00103000c8080e10750081d511030b1340d050001d00031028042d00901c03030307912180c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 834957086 1250 834955836 834955853
    0x2090603071707031509020c2a040b0f01052b05040c150206060f10262413090609170d141e040528020a050102060702280609 55
    0x1c2249a80d070350004941c4044c428020040c2864004105054051400c000c4034000c0d4040ca051806a0140c4480c80501c443c5455544034041c460300b240e4482150914204411103e80780c440a2203603142e0f4400007400c0c0d030300105480001d403407440042c42c2c0110030801d03001e26980308040340d0800c50034441000100700645605130200c400e509074200f00c451004200742d031550411200c075500700d0140000b48a8910309400702c525402c0860402c0ca895440004800324180142c822911090f03c001c804e1040f84030300c400c00701400ea0340082c01c0340420782c280c200046c0070180725a40c004c002c3d0345603101181817020541c414100c80b036011510142d00000c005690040380c01c08a140c0580d01e103018442c8440e0358070003100901c281059a04400b41d07030141030300745000c03040c090416900c41c81400f81145200300302d40210252032100078000c00b12034120348100802c20055030403442c110741081090001385d540011b504114550054288510254140c40c0311641c80c2d2050800b40c2024146203900040c0078014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 834958336 1250 834957086 834957107
    0xa090308040308120c090d170706020d05011d0115230c0d1d0102030306090c041806150c0807020409050f030d02040f060c03050307030f1d03030601230901080a0209060307 75
    0x15084c821442d07489010075440c030302415481d0b54014010801100c002001c00c82c004d480d411503080f0701800c15005445001c100c0e0007001c0701d9140266078600600c5889004030402074106081c0c0400402e6605002241680d03030a110415014440b070880c11080c004200750500000d007080800d256210328042190996844141c0c2e01c01003c25803800003064110741c17400c031802c0c00ca030040c0c0003036196803940e5040c01042d01000708000c61400040c4004035000c003041e103081040f0307009105e021440c982406001040c035400000d100041c40614240380000800507010f03a1000c94040b10700060710241d90804030700f041003101000003940030001e5056516034080e409441a62100c1d1100c0c520329840710f105440c0b4000210b8040c01195040c40081d048a1081d045035070507407086100402c0d071303003200c0070f0b0584041d080b451265425000801046060350b44602c42c260141d005007201a861120200603588901c81c20364024100100400010103120403501210181c05025009903902e2030038440052084c40c81 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 834959586 1250 834958336 834958357
    0x308070f170f0406050906090907051905040e01050d05010f051008010e070509040b1e180c01140d09020102070e01080304030203070b030402012c0a030c1a1204080a090308040308 78
    0xd00c0007599151003500a8074508021032548520701400c040301554560455480c40c1c0e4822000c110494032a1960612035005460380d8032100c2d147c00d00d80b041e01c44445503030706010b010400c05201c100000180d0040980c1165000d0340c000e00a02d01b103040207405031021544100201d4184030511410307140030201d80d011100d07441e0003009080400d210986c0c60340c90620681d40c0c40428080401e000c01c009400c0d4640001107059269001c0c98006520100c00d041190203038003d00004802c500311140c14450a4480308003481d0070710f400352042569070f0307583c02414011458036546a15001c11039008020050150114952103205513950316a01b41e640d91090000301e00a0003800f0000802c0310143c001d40740126070507140c196602c1d402942d03003141076a0b07004940c503501038482002895603c0310b00610014501408018054900b845501203000c075103944036860b00c1c101009407a1400c80c000342100d41160348040c3c801d86e02c0c0c0d40c0310800c4407035100700d80019103805400940001008150801413200e00038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 834960836 1250 834959586 834959603
    0x6061b0f1519050603100603030e1e030a060f021204060c0f05130909020f042301080a24060b0c0d020c06042301030e0102070302300a08060a0308070f 66
    0x103840c0c441c80e41c0c820705403044040208010300040603090741d80c110661100003d81100c15050000c4551415110706134010f50215141c034084101c0741c20108140c0c5a040303051012180a80c1102c0082955a500710300064400769541e0b080300c5c0b980041e60100e8001a00401c0d501c0703898105400c1c0040100400201a00400c46510050792035602900c141d8a00e02d1500e40d40807100c61030115644003601008902b02e030701c0410081840340c00c5e0b03254800c480c0ca1101d1a09600410001c940d01c6465603201030300072050a40c014055840051f48916048440200c0c0c4da40c1c0c281c901041d02e20f00c0c0060300241c0c10802e14050b01041c100540d03200000c04042c0450386908850070540b4030f0042c003115120314000ca00c50b07010058030700c0040c2c44588000782582d18040c5000110784c1c1c0b18003506400ca800941045005800140c1d0103031840c040420f000e440100410038541508000c141c03411050311554000b4001d00820100107900c0b0b58410407440300864100000e03644d12015490044020720500100320b9031400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 834962086 1250 834960836 834960853
    0xa05031221070c1514010b03040606060503220c05210d0305190c0905040203090a05010b030c010e01140d0504081c1406060d02040f0803030f0a05070c030806061b0f 72
    0x8420425060150711240c070741e040140156160402c0b010b107411104900540c070303880034001050221141c1d43c021f040c0411119140e0509182400c207440a03030b40194100301c804d00511102605000344414010f80e20301e07807590440c90503e0801048600e603800141c1c0051000341e81d4414040458295124031700c01c5040e41e4200c06c0089003a011900242e0300490001044040040100c04552002c000c140d25414201d007003540e00c0d8002400d0345e00440d02d0041c9500b24050f59001c0103000d00410665007002c4003d400c510b06035200007000700300000e004504108044c400f182846c3d41c42d000301d800e880d00c40a4284440d14141c00c00a245600c03c01e85903a00d076045007100c0c034240e202c038400d02080040384100c003640394541030f0822945410903140e41c0c028a5007044001541c0b03512400b03d00047c034455000e19281d10b815881e030200c1040042500c08414240001c002c2040c0d800350f03003490200d80c1424011001e03110640810854010010003600741240d0781c4400c1c00c08500002e1140c2544400f0007140c0e92034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 834963336 1250 834962086 834962137
    0x705070f0b0d0c0201021e0c010b031b0f01110d080708150d060b03190f060c050f030c1c230703090c0905040204020f04030b04110a050319020a050312 66
    0xa002071085610800e81480b400410400c581c024aa480001e40300260400c4a2842c900324403030448081079001010000303402101c0c42d030a00402541d4042100039140c504801000c5420442e90100210300c40d00400e49407131030a0b030040350b81600043c000c1e07040b030711041210b00340500a9072007507464202040400001600e84801c000e4005691000030b01225803440c0c081e580d04010384204000141d06016030301741e60003d12641d83c0f00c4c03444140198007459900390799060480481394509001020007a04010300481243c8010480750030102c5403030342c1d5544906100451500184842c80381284a050044d030180607070020324800c50080181c545101c01c0e0312043c005604a642da048003c0c400c1074126010441094658000f0341c0c014005840945005190140351005070310940040b5403011024051006216444144010300c440036102200c8003420980004d40d1900840e2040340c02001031120f0b030f81152a1021800007c22020b81220046e00001d003070313a090b5401001205070485028a501c0300d41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 834964586 1250 834963336 834963359
    0x2d02120a0506010c0b071110060f06020304030804061809020d090302010e010b0d0b0c070f03020706090504090b0402090a0f0f09110607170a032405011b0c090e01090203070605070507 80
    0xb40300584501c80080f165907581507003220001c2c40c5c0303402c0c84030f0203035901142001405148000480340c14000741190a042e00703803144050b2500207908541c414030040c000602038600316000c0c0d03800760406018414a820b16070a4504054110105090000c2461071186103c0e801c40103540b4401e40003400740039081c0c103c007400c8030260044241c1c040d5540349014049400900299000360070703102c0082c6002e0064a41c510a101100c0b01280140d000700410002d0035400501400a03010889090002c910603441c0da291100024202a04c03c983e1040400c2e00a81c041d440b0a0100407210410322001c2c5603c40660020b02140b01d082d1026100d60041f280c90740391034421201c0702d030f61001c00100304040d00c00d1052159000014000b003416940d54031401005170800d0080b08540c00e9040b030981c01c50400d0001031030514903032001c0c100e00d50890f1841c1c0019409500c400142c4007070103c00121440d1104119014240128000c0d4041c0034154000c6000e0790312000501d4010701850403103505580d2055183d01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 834965836 1250 834964586 834964591
    0x7060f05131e030306090504052d0a080a030b120f0c04061d06131407121b030c0e09090703032a02060d09061b0807050f09042d02120a05 60
    0x1440001d08a03400241c011044502c00d014002c4c0360000715240c403010140101c5070152800d5400e80c0c0a47d1590455282d0f401c1c1400b440351000c0c11504101241c030000d250b40d003007401d40c001e18106002c40c0004d802e6220350710500c1c05901c010451441400c2c4090003d460b008110a05807182c015814440c802d8140b03030040750f0884842181c02c84401480c0003914040980182003d03078010346160b60018a00c00ba070007071001c0000300e51480c68042c00c00d40409880c0503d138144200485080c0120030310001200300d8441c9400c0740d035080110b0038281ca51001c480310217401c0545507200340e0038000e0141fa05d600040e240140d034400e8584c8284004046610014040c0f00300c400c07403102528164020050030603102800f541006248045030482182c1d071600141c4450310f880c25000002c0d0b00d00c103001c0b154043e02030750b0800340c542051860107206580380e880b280b00d825091402180c8500040710204c080100004080f00c40400c074401c0b40c0d079080410320282d8801c4500003042c81e8100e01040000781107218150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 834967086 1250 834965836 834965843
    0x9050a050d0204330503370c0816051315090b0d02040e0d020d0e0f01112b12020a090e090f0303070c0510050c070314040b07060f0513 59
    0x850751240341e0800016200c1d1284036a0b46019944555588283c84101d05519000441c110031180b410181410301d050b9000500c10b000140907412401e81104140464402c0c03044003c10a8440c811410402c0070540340b940b2444451041580340350405401108140548004940d01c084100c212020401510f4403a004a81a140d00d018100403110031a80245028a0041c024151041e900e03000602121407090003064990080741c00e44010303a50601c4070360760000782403d01c456031000c4140850700310f0700003a07001c6051060500307103031160540c104100032071b4200244060350005020901da07080c200d4100c540c0d2002c104800c102c06011002802580c5c9500c072590745000c0a90300e015001d4555500281c040981c40c01200c202015540081c0b005500c43d29140d11400e000140902e8030314036181071440e1591440e407074103041c4074001c06040116900d03903805280171140e1610100d68000b03a40f00701c1c2d010103a041c030700007191403c020b03454021100103070740000d0802c1350750303110004485010782c0004020f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 834968336 1250 834967086 834967099
    0x30403030b12010c0908070b03011e0302060a0507110d11010c020301020d020a0e120303041a13050f1e01110717130e0a111309020a0905180108120f1218060a0c09050a05 74
    0x40c07124440701e03100d2140010078a918bc0e00c5203a5240c0101d82d0580c0881081e10008400094038400d22044150090300e03803509540c83d403045152070b03c86003d81c03003035480100d0410412107005415503400f50107460f00342ca131400c001c5544000d0108058001541c3c6008140248864483c20001c1807002c0305481c42260031400c4101c40d554030180d15a801c05d4002c0c001703020380c00c4590202001c11000c01c1001100c407501402400d0003001e644880e000e01e80c1100300c5400f80d0b81003000050b603141c4468203a40041e940401c0f0600705100103042c4404600a10805400b1110203400001d80c880c101010a801100401c0c020015200f40459144440c400c84039030310070b40003c200d02000340c0e0391158001c02c40c252080c130709800c03042d4448000603112482c5100110b03450342228010f014a039400e014030301e401d0303180082c0c0a1800c803800307440b02c041d401156410100406250002400148000221700c912030000d419119a8074180c090000188040760200c8002441040007065030300b4001c4031041900c1005094 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 834969586 1250 834968336 834968339
    0x40b010504090f060e060f10030c12030e150306150a080f0709150513050301020408120906040e04050f0c0406081e030c010c0203070605060123030403030b12010c0908070b0301 77
    0x50002500d80c1000444820305010f20042c0410510b220b4069154000c001078411410418055082d40402a083c0800f090380345004100041e240404c80003160300f000d40a8218000d103023019200c840c034500816802c25170000303030040f03100e040d070000303610036102214000c0c0c101d07688007004412400b0b10300140000c01c0c40240410410800104001e600034080e28000e2816501d509040341d88243c02c44040c40482c07404180b201d0b030394001075145d001a03c0d059001314282840d180c4d00355070b58a0004050042000d000840e6910b60701d482003180d010300b0215040e00090f041c54513000350713541c04d0700c02e00c42134900450005449515041c000e00d0115000d0300300600b1103010a01c02c803091007198000320140752000700019900c9540130301a0340c403010308580103951500c1031401d0600940c2c40c0100b0712410403502102104e00100381c0c000101c0302c499610051601e0f5615486d05030010240f80000c0303a800b41c0d50f001e54800a0105400466044015a6031441c0b259656001c1c150340b042c4074042da40c2c040c2001d100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 834970836 1250 834969586 834969589
    0xc060305130f080d1b0c0203120a1407030c080a09090b0316090216050a0c0501110327010e0d060e0c03030316180b0309010207030e032b120f0509060906040b0105 71
    0x2070412420350290000d615104814164030042c08130725105c01164101d2054010343c075082c0040050000b80311002490103102c624000c1c010400b54048604920001ca1503c00341403044c0c0760542840d901401040c0d03900300032600a08141e186204401c0903508060f880e06042c2404100842042a00c92422810b50b003400c2d4804060740110f107003500d0201003a202100403841c10407036240c4807409031f03d0304024103041400043c8000700e2488098456481003001040c01e40040c903244041004040c2c2d2020200c82d480f004954104510382c0c440d82c0300324135900c001d0912107107610140b0841c1b4036108640c0c10340c01071410b0540320b0004850400940c051802402403081c02a080e0004d46400b4402c0000140c0d19040d01421a8009594003109030b9804a00d02080507004040040aa00d0440013040686490607000b00440e000c3d002115150b10502607a1042c20701500a1b0030401c0c081440600004503400f01010080038201c4080340e0034416207002c2a091500411914080c40e045841441240e08050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 834972086 1250 834970836 834970853
    0x40201050306060708160204110301151808030d050a150b1c020c150a05070c05063402160e220807021002011508030306100305060d020d0c060305130f 66
    0x50800c0e81142042181c4c200151807000140b6805c071080c00010b85070072581c0140012142214500c00c82c6100c20001884550400d90b400c000070501c0740340c500c04c0321211400703c1510003200d41c4105500c2c0f00110b449146503031150403051040b40103070802c001000c0407231360250003034426110701d01d141d110400190090303030b00c1c9040c0d921184c06040005442c241804403c5450301c80804820094160004203010a5542900130250400a14901710070b064a054690036102d000140c400541d06071304071915035101002140d1808040c141c2c10b003200c08503020034400b944610140d1002c8070000c0c00c840303020a080541c22502e40c002c85078409580b412242119140c5041c1c000140d0030746501100b031010600581e41c96000702c0520ba09907002180d10030344034088113880d01140c3c10010351074005108001990301c500b000983c3c0e10a6610780403032540c4941e0080b40c4080351b10100a9000181400400203000d1008882011103095640c04c1103240e5442900006000701e400c002000a03030512070074800701d01c011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 834973336 1250 834972086 834972091
    0x40603050a020c06090a03080f041203020d0b0a06090e0c0406020309011b020a03031e0206060328020a0b07030f0807140d15030c0906091104050103050c040e01181d060402010503 78
    0x4a0010320780340c00c843d501c0740f4002080700d0310030440d8441680c0c0c00425a0015050b504141e082c019155181080e0307403402a10304d03214990710300705035000c501051b80c5849604a40000200035002126490315407800030480030460140003034050100010940c8803204004031411208160b0195040000d0f200c011164801c401c41042075221004d1000c40c0969140202035000f980329031600042d904111407414003400020400c0810b42d0040e00c1001455140820150660f07002c617581e0113041681c008201000940d20a006904a172000d1004225a001280145071540c0640c4800e00b40010741038081b02c0b608012140307c00000ca209000c6140b00034000701074600343d41d240b5000703d4601c042c01c0851485207100c1e481910b4205458030700f04030314a03840c0b20751805030035004000c2c06610488051002c641c031903841034034100366603800001c00b0004070f40161006003003120020b13503032540d449056003440001d8002110362503141861100404d00c18a00c2c0e402c034a840040170704402ea4441d001590a81c000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 834974586 1250 834973336 834973351
    0x8030c0403080a0f030606110a1515140a050a1206051905040f060501150801151b050114010510020604030f09090e011b05040e01031103011d0c010f0f0504060305 71
    0xc0c0004400244100c014121001e904d40d58150818035004006095a0f91903004d1000e0254140500e0902ca401007048400359401181c404000300003070040100a000e10300942d402e42c0d403e200e012035044140040700e4000d031401c80d04900a0744c1c4490810841000e54400e880981300304440c2c610000303c298003c19800407201d400000c583c000391401c0000d07550212001c4580c4442c41102104002c0640315050141000d01c0c00380502c00580d030350107002d201040c05680d07441d0288002d2907000305d1051509011519060302c60382130240042c50094042c24440001c0c005480c0244004aa54203010042040b14000f41d8014801d503221520159000300308040c210041103e01c0324040384071411401100c01c0d07100300c84000691440800c14a40c07103072000000300410003074200410441d0a036012074a07810340790031a40207204200703400c0000340140211040001c046490440b1841541000b003158a205042a225044800c0070444200c401ca00a00c05180108100340303c1070058622075802540d00c0601d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 834975836 1250 834974586 834974611
    0x907060f1701060c120801120602090a1d0a0f0b01080a020703030905030a0507060615020327041503150b030601120201090314010e070902090123220503010b03190803 73
    0x200c84007400e006000d800c0f40c40401c0d49036428004001d21008510070200c950316000080d54104070704c00c00c603080400405002c068022134000c80a0b5141c110700720080c68054075407414003100005502c00311800b2540e10144070700d454001c00f00307501d980c014043c65510507511440581d130b8aaa1200003074209410540c10103540304110000540200010076404a60f626980c1d2140040c4c82c000050700d01d0703a006686803080c40085041e440c0d4001054419812003824508002a5204184030700c2c2d003408030a01e0ba00a080402551840c080d0700103041c2624081e035aa002c0c1440c0310101c19050355003001c070311340c0c040d030060004205c05804110101e44251052414150036583e9403188458040c0490100000b81d540d128101d22801c02004018001c1c12088030550a041c0c04000207842e54000c000100d00180c1400b0038118800c07050000c50350040c3c0d07510300b07180022210b84480d4086002c1c0340a018040e40c40d0054840041c1350000d01003641c0c100e101074540f400041684c84405a4102405403d590305 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 834977086 1250 834975836 834975857
    0x30f04080706050103030509031603080702062209060e060907081503030c0303040602041d13080a05070210030f0c0309080318010e0f010b090105010f1b0305090604230303030907060f 80
    0x682c9806964000c41c00b940d25291290402801c050903d0030b0a40ba180c8080c980000c2000024010310644042580440e01e03c0d8a44000801071884c001004800b100c0d60105614042001c401c3d65012000352151403290028070394404040c4000d18100351050300c045040c40b800282c04501041c5d551031140009000d40303060075050300d10140781d604195001c80b51607401260500902d60340101040c8040d05440001441d81058421100590281ca0014009040000381c031002a030040301120107140c0c0c080c02c00c5c070880180c8000107006200c40c00d14140070390304201010403003e00c01e0041c1a60107030003295040c6543c990320741204030505e4a0003118076554a8880720010703200c040c4100c604503800340c000480c1c0c0315842d40400a41401c16040141481014210a5031541d8490100c0c2e16400030980d40103072030803240c14240e03014041d10b038150317500403070008010a001002404034003d00b22549002644448000304040c3c03203000448101415034483c88040126502c54105201c491486041ca0003449 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 834978336 1250 834977086 834977093
    0x100902030c1e1206070518031c11061008121804060312022811150a03020909010f0e040b040606090f06170a0b010501051b0106120210050906030f040807 67
    0x140c41c0100010168102160b408440d081848420507090b8000c2c010744a10318240901900f10b018a00d01800071280300005100c0c02c0d1005c101c40f50303648121409500701414080e10003403210001d484c01400341d0282102080900182d1200070082d5041d030030141211924a850f14180c0b074001c00f0480d0350684885288005a84491082d58040d5004a200455141410101900e09004500c1d480d00c0c041b0803020304060840340440348044981c0c00306c560070310000c02400091003c022000c03000480c45000800d000629099802400685001d8403403401c5a1b0b82c654102d08000400e20800e4100c2d1901c3d070000d400500306040312648503214000000c0c0c410b4480c0d05450440300681c0d040c00303d507a542c2900b8400b120f813020040b04103503245801400d04c03003016551041c5143e018455141030020215a140303480c0c40d0f10f00711956486200000f00078460740c42c211000001e1000e801079000307180103001d007000350707110b80308690030482d001e40901d141d138840c1800c0700e446072001081510b28400901c40b51000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 834979586 1250 834978336 834978349
    0x8090c060d0b040504050c1e091603090b0702061006020a0203031801020304030c0f0306060e3304050a050106080f040506070c0213090c030c0f050d061104030c03080c150702100902030c 81
    0x80380200028001d841040c42803040d0b010541e441006403c90508072348009688925502d42c0c0103002c1c44c21045002807200d4194040c00810000900c80350852003081032040d800104288608100600c1c180c0a941d02c0c0710980e26040f500001035050340082007104a290305211026100788410300c100c3e4a0182d480e1521011304100b40c10200e18070b100c0314030030001d202290140c40c01400700180c4182c55401c282d9145000304e6000c0f050320144403500024030044400455140403442800b6105002034a4001c05110050900b4050b000c04120200d01003500340038030000c0345200303940c05001040c2d00e03140e611041d05d80d441c290704102d0b40003e4071a00504051460700542100c1446034400c0d514203420b602d000082484103070040c4e0342c1614208003c000c2aa40c81001c400200c0c1c000300000349010180501c00305512881d080500102e960b214000104007070380008200500c010070a031707413400281d2000d02100000513210540180d00c0100401e10307281d116800794440d43d20080846074000007017400f00e0074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 834980836 1250 834979586 834979591
    0xa0513060905060909100506041104030c210320121206010806010e0d0609170a020723010f21050c13150f0c060b03070909050c0108090c060d0b0405 65
    0x12825111642001650058010740c0d4000008560741d409600c0e02c050183c1c0d0310820421b0b0801724940b00d03030210700300340c46a5000c02804915805025560342d203e080104109003544260654240450742101c1e24400101250f00d400b40d1540d526040310f1800d003020140c1a0751079040051074000d201c1c15141c14240c03240207104c0181c20040152135440c1c010005012144000d0000d0b060100b04901c401103070f40c0cbc41c1e01e01c00c4000c4e4005000200220113003007001c4110481c0c43d02c0c90790031000056140301542c00061001c1201c0c1c083c0800400316500d030b5040840d1520000c1c1c0135001c20b090085210415018200b961010070100c1111a0307071880b19140e100c01d58405550101b51402c0008100064420340c0c0d404202600c56030f50003100c0c0340d0391110018890300b044040a020001c80c0070086040010760341201c4000080182200c4450f81c41d100a100244400001151103204080500c001540103a50b454401c188490192600012030f005004d090340c080d4000080c0700b55203410a02496031207218450 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 834982086 1250 834980836 834980869
    0x31e070207051f080f010509010b22090915090f110117070f0f02030408150c0c011b0306050f100e01020c030a0f05062a0f0f1b070b0c0c060304020a05 66
    0x200d0303c0b0305008090320700000540390964100c012401480903848080c0c045044a40e40140c1e5a6201a044040d140941c0800d0710041000390804c000102e400c80e0341c0104402a0041c050b0300c0403616400302030b5080b9241110020041280150b1880115456006e01d0090981c18100009649905c00c009102c00340d0440340203010a03c200c900c40e0002c0c2d07001452420030b80f035500042d8501800c010000f43d07036039640780761032500c1d0500500203860103651006a5100140000c000e00101c803000c0c0307104105080c1d03e01014000b91400303000089a24010098007031909002e0101410034802d444202c8800761111003090542c0f1620b16181a10b840c00c1050b0400c0398024501c040140250749003250034294041c003443d0118454079090307850030007850055020311040e21301d0039580d45440094103405002d005148143c082020030440220b03003000700400d04c422254016111466128408410940203041d803520301503010038074900560801038001c42d041070000300014505551540019020740c11014210b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 834983336 1250 834982086 834982129
    0xc0501050706090f0f0606060f05090409030e03060906010501020d0518041a1804020f0d03140304050a06021206010e12100906020405060a12230402010305150402030a0b010212031e07020705 83
    0x6106000b154407c1c44064806403603c4803104025540041240c015400c480e0307c00e642c1c455444e41014018080c200c52100b001d400da50061422000c5552104003d115007030260003005141c0f0903683c0f040782103e00941070310201b030800d10700402c03d1100074441c4100c00710302406440300c08401c550ba41d500003040c0c40000d985031802ca10781171051003520140d5500d100d00030f0201c00901c0d0002038004039440c180b040d200d0603007502ca80e90360030702c0761510329001c00c040c0800b8400240c46003403240c0790b038219119000a81f80c030582c00900c0402e01c0b66507030b01010041416001066030f007078086a15002500c0140c02002c000d400c1036141e2000810540c403040102c0c0109104440c00c1031004010b00481002510002c440740c24200165010110f610b40200000d0406946a0026040454840c0c1811400d14090f0045483e407070001ca0390b900a2800a10303050143c85204903501850000788216485505400400c407207083c1c0181d181c00c0e06c020f000d0103440940c000e00c200800d0341e0301c5801440c405203100c0080c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 834984586 1250 834983336 834983363
    0x10603020a0b0408030306270a0506030d0801030b1305070f0f030201120603020609012a03090518130f0203031c020d0b040c17060d0b0a0609180c0501050706090f 71
    0x100141d0000e00e070b12030b0081d82c4003403100308062507010040d44e0b8000350545031000c0015400d55a075000109006088017800c9541041c880d151039254070440c8925801d40440343c0ca5500302da016640036909200003000f0b107140e0400101c00c8100e109400d1104c6114000712601140c441c201c0400740411034100c00580401500104103560f0701c0340030711030000c201c150f040104500319000f16440d40700781a2424140440028002840441c80044508074100a480700c035001c0c2c09464000c045030010f10a0030f1003a00f1752901005481005100e03e0300502c0c400c050380080b041c050b44d900a9021010400381c0c2c4c940401e104907552203030031501c189818480713460016520141c0c26503403002c03a0140100f6a00682c503142460400980000c840c62110201004080b03095072004001224441c061800170800c130020707400c0c45a00d120a800030001e4869090040c0171a10721050015294030000c04080c3c02c20a450303804114a5000f070340144103050007540301049401403501c4589241200752001c83c6c40c0f034450300c2da = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 834985836 1250 834984586 834984589
    0x50111101a030106170a0b04020604050d050a030206150d0b0603011112011802091305091f050610080402130203040305090411070309060f0c0209060d05240903040308071203150801060302 82
    0x13910041c0410a92195883c0c4105010303d41c0d0340448000105071149410214040d540c0d81c02c262001484002c1018485030084e241c903c0e00c98400d42400c402610a40c00822a4101c4513400c10f00c1241001c0d0206c05542015281d80c481e5401c042d080c15003555881c081c174400c40c10404014045103e50660020391949040c1602000303241014060310828418002041283d48483c1a110a1828903030b01040d0354aa0420050410319101616070300760300703621400c01075001541c0000d0b100b8002111a03003002000803005880051048400a52105182c401071700740890650146030450300a00c2c05505101030030006c14225100354160303072220000481c0d580b0801d640b048500014144520304041400003e400260401c1041d403002440740c603002002400c1500c81400c3c04d4801c1c1e130008201c030060a406c0342031011b2040c1c03d140c5552803d110000140d103c400c0001103804699104c2c04d41e52420100c0d4484111419983c90004101604c420025442000569503a0081c240103800056040d1542c030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 834987086 1250 834985836 834985841
    0x607080c0106032a061719051326120414120d0e010606021c0212180a0e040f030806040b03070e101710090203030d050c07060609090b01050111101a0301 67
    0x104204c0c6682c1ca181d081c0316107540319998040060701c0700d010341895251180e401c0c3c0c008103450440c1101524000c100f082461081148003110781c0118600501c900024804440c1350b04582c0e8028030080c030402212203203026050219038001c0c010102023070180f40303102d009400c0410344030300341d0001140820b001d4600c0380c4078800e036400c07203a06c0300080088528044019485450b4800c14a081d0000a41d51038002c85c001c0c04409400084010410340e64201150b819003100d40c00c20459001e80b00c0d46e20007256244070880083c1c01140c002c0f4210070000040d076000c69840f0300c0100001d40007611000480707080e450070049c14000c2e006290414843e450014107403e030f050400d5100400340b4000c0b401021600402065910000310030031401b0905100c0d074000701c1c1c03452044011036080607203800100401c2c142000050250a84600020b0054561700d00094043c0c80c1e940300041c1c0847c100b540104080e6003c0c1007803203905021081078804100442d0302c100e045038015110403403050f0b01c4920860743d074582071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 834988336 1250 834987086 834987143
    0xa051506060306090708060d060e0109140f0604080f190c0213180b040503090d03020a0b071d1002390a0b03041b0b070f05120301080c0607080c010603 66
    0x141c5015007549000000104540350150040041c4000700c40411070544907100c0486015400c06014443c80481030074460003003c40107030984d0b010b81c0150240ca25480e022514a0321249035000401c3c2a07100d545803c51036a00460b400010b10008000c0004040025200d80390903144070b4654000c0030b1703014014040541e0311000c800802c5843e020290a60004041c10480e8054001d41c103080c06176223074030b002c9107075200b1001c0301644090301c10156402c240d4006001520382d0b10070460f1002980301c440d001e42e101e01c8040c201e400c030745034500001034050038140d4115090340404e01c1203521488407612440c00c40b02d680b06201480344201c0d00c030f9800c0341401d031503007840d00e080648000ca079081c5030100600c0d290102510050036101103003040b8511116602c0e10901410b40c954807550f42c1c0c2c0440c94500002e440140040752180101d00290424141c09015203048031071890251142d9450b0004001c015400b42c0700407900c020040c001c00302071060903c18880a50320a00150403040700000a25058403000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 834989586 1250 834988336 834988339
    0xa0903170108150402181017150601050d06091d0616052a16210203030417030f0f0a02070b07030c0b3310050909070f110a051506 57
    0x546004005440d000200401c0703c200c0307409a0b8080d902c0c0c030710004000f9815140a10102e118400901865400d14420241201d82d640d640d40401c010b8020515101d01020101c65080c414400000d400c650003540203043d0a04903040c0010350719103407400d4500725810140c41d0f070740c28007050300140c4840d001000659008058200014602c07a0307100c600419600c6040d0b51742e46103a1101007492440c0d0f0003100701507407004460702550800400302014030b0a6401500c620454142c0405072a1a00059060340070413991300900170703516240c100b01410180e01c5980c01c1c030042a1004200c030103110070715007011b401c0620352180c055644088103003000740b80c0451500100340481c420000b800009410416842035194010720500b9569600c48812009540d0000442104044040a01181003c0360103032140d070700040390041c0c0702541c1c60504a40b1405007043c5c3c2a0070040240204d80500d01a020010078030314140b400d0542500303040542814000b6004080b40c480d4041002d0b520034692185d0040e81c806d20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 834990836 1250 834989586 834989627
    0x1a0307091103060d05070806090303071b030c1209050d05151f090b040b030a0605090d180e18120406030605120d03090524150d0b0c0a170a0903 63
    0x1a558000c58440034203041d200390344c0281c04c0002c1207400d101c03030001029840c00f59012449c0c207641307603030f2139038811a680e80010303440710300802185d41082c2d800b13011150541d54012034203410341d40340f02699184050040900482c0c440c0010135684051404803ca8400e0025151046204c03003196030000e00a001c0d14041c0e00001060b40d502c6550301008400c564aa400102d40040620f01003030003003071000401a01801040344540500ca03242d08110b0080381c1580c200c401d40e0903940000c0362403481e00040d500400304d11403c10408414600d0900e900310407000240c68116000d008400c2c034004d02c04c1c010700759035040400c00b0003906401d4803940e0000c041c2503a04070260040c0250346038480a01c40b02503010315a0360a04d80f024440300300b0500061380e140426003102824650044108070204490103103040701c15141c00d082a0a00f860a03d00302a4006112072140c0c90340d18420605411003e00c8038100201c1480c850500c040d850b803001c0c0030b20001781c80040d42c1c2210703043c010b040c1106140c01128100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 834992086 1250 834990836 834990851
    0x190c06170411011205070305150301020307140304210809060105060f07031b0b010f14040c20030706050103030f080709032004021204140f010c09140102010f1a030709 73
    0x8000150407503215070b1040900049004220058078070803400c4d580c07107207071074902030801ca4001c0d0194802130180154240204000840008160030303848200c0d20300000844008007104041c41d00340146400c1071140c901c1005a42002c020220080001c84a613030009440314148241d8102c184000d40c007506c41035400510b0300c07080c40302140140c030030000000c0c00c0148031400034030401d03d0201d2500e59190b014000441c1969983c041a012200034000c0d11843c9a040ca071103103a9152074403030001849641e03240c80794048031054440b1903621891030004070a000403c40f00e000a0502d203e11030213503200b030311044003d02494200528819008080c1000e01482e0401032001c1a84071540b00f40440404845038507020182010070040d002d04142c240305a0203180c140020404103444001c0c8060100703040365001511408005c1c240c4e1000620700d00450800c410500496034403420b0810424810300010424010703a07a964411107405024554041040c80b804008134a02402900e00500d00b41c030301070140700b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 834993336 1250 834992086 834992117
    0x907051f030f06260601050904060e030d0c050403030e0d0f14010204120507060f090b0d0515030616090b0a080105120a020a06030203061801080c04050702010e190c06 73
    0x601004001140c1000355451200c50910940020705000c02c0248140100b55580020051300c1c0410001c51143e0f4040349002e1115401c0003502d141200c0340106154100e4403240c0b5410010105900c440a560108104134036019500c1e0242518003a10356540329940c81c5103050060246032441e140502c5009c14030b00140c04505141d91042c0d040d0340000e031841341d960200600714028412641f000b00642079200b08501032020110360003080304c2e0207031500709868810f81e40c204e90017000b50144880e084030902c111402030615900c07007584168040c441c94107100c400b40003e0b00c2c001c1c0868020008c0403050340c01d4a140d41d4002c20b124020101030080d10304040070750750301400012050080b603001d10003143d000320741ea800402031110348036005840c8400442d01c0343c4008003c1d5100f00c44141c0140415110202c440d003101240c981221404030241c0140044003003000040d00000c2c198104540d00da0501840d121010700100640082101c500c0d46000500d1500081d00d0501d98010b0f0140b0043c2e08055020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 834994586 1250 834993336 834993349
    0x1a040b06221401110a060e0c130608060c090a0b0f2b0c080928020d0b250c020607030e060f1c230a0905013b12160f06020a08090705 58
    0x1702d940c012004030f075490400c004540f429000d41c8003181c0c0522044404940c64420b540040c0681790000240d48440d5100d2051000790721600c0015508a40d00d19000c204003000500a0031008841c41090b82c54884d0240d604031070140007404510703030581030802c0c200c28031445100d11100350f4468100000c40b0b1408645094691040506000c0c14183c1100444030443c004c445452400c1c2e8000d1042643c1c03c41810308a0f0140310807a017a4840e550450380e59654203100c00d400c01c101204907910004096015070a111880d00400c0c0c04900348000b880144584c2c6e038418015082c0c030610042c40a85070111000040c10709500b584000c0b403003500c0c00002c8050f055050104805098611a5440040e104c00c1182030003004202c001500c1d95103004946a00a4070491482c402e02c50301008400103428040b0b000340340b101707803031002c11850ba115807002040411480d000d844800480d0349610403421503520f5111340500744030003c40e9410360006210a400b508105400d401c4000764005103641070610010404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 834995836 1250 834994586 834994603
    0x60f120603070b2a0111090910050a0b090d050d030c12060b070b091f061a210c0904050a020a180e0a0b1f0e10031a040b0622140111 58
    0x41c04e81e009140034200c0305a42c0c0c2c00c01040c82c00070002c10000184001c103680d01d40004e84a0380c400d42a10340441c20740242c1d483c41c0004d41d2001003103070701014a40708a03550154031200b07805400050794040300021540034425881c3c40c40f01918045801518103030000c2c8418865912420740341d2a15009000b02c54100301505c920903030020f0000000e8031409040d920700200341040e110403900000a00b071100c1d6a030341015084440910b55100c8501c45202980030602800c015101c89200540008600388d076039a500c190800c2001ba9400c0c90011060046425910201e0f407091049400041201079140c1c00801d0030303061040700343e020780000d050504000c02c0e4071000d884a204291034080d0050305581e10089440820000403807049615001c1c0c10103440ea0032044080e80c8561127010785210403d0284c09010000507008040c946a141d94508100091032030344c4c2c1158000c1c409110030001610b03003590400d8401400034000041d03d03c1c08000322406070064030640e0400c2003c40c038158000304c0000e031009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 834997086 1250 834995836 834995857
    0xf010b0a05160203013213151a150c0d0905130c1403070314070306050a05060d09140304080714090a09050c030d351305010b060f120603070b 62
    0xd20b14000303000217400751448840008045048500c0134403c13001c020f841c035541e140364a071126225910300c8102100d0080e00a0302030f000003105103400c42c01d03440321360103401120010b00c0101103020038180030451a900c0a06008081400043e45c0b07401c04004000741c10210905180c11110a0305240108003905003c00541007451380f160306071103400e8040c9030280401da0f004011241c4a04e48030b080140940141200035242002e044003003158540302e0b00130305081d110040e0050703a2862804041c003203258004240039800e50781c0d5031111000940c900303259000b07501440d4000c6440707500f803c1126042840c26440466405958616101030f601c8443c06a6400701140000055102071424001c0c18500074407170300750b814001d20100f40802d507006403c0da8100d20611180800705400c115425014500300c1030000080c00c0e030200010308050305418400181342c0b01e94000f00e00c4624420100741150801c1712147d981b491301041200003681c44400c0700b54051012002400c1042c94400750001c0307480b84d0344009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 834998336 1250 834997086 834997117
    0x1b0d030f0503130512120703050402090c09011101020c0609160311040b03030c1f110f090918070605070b0a05060d02040b01050418630302060f010b0a05 67
    0x691020714500002808607004802d45000b0145170301084401c0e404081c20340801d84040c0007044050340329109241c4135a41c00360101c001e503103440c1c43c01c1c40a5088841d525041080c48042e0303403c0341c0380a001600700350f6000c0c0018502ca050194105013411403021401c8c0a81620407420070200d642e001c1e1010403c0400e50b0005000d00404010900750700c112801068684515035454402180442c034404100011312410020351480d00f020b04800e11480008c44810b07c03040c4034808581c680056019009001444407144034500c1c07041d95030400c02070b940403601044010440c0000d00121003201035100510700e40c00c100354600000051040701180801074040d654591010314507034003520031103002d840840c9000c4200c1c80b208132900058420141d007103030500241481801c090390320342040300900f00201c0d1007410400c03050f9512203228001c00b0340c04903146810700016440340440c200e81d199242c0a9400303000685060300c0c80841611040c1d00c000007030340040044e07084060380002900d54007154243c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 834999586 1250 834998336 834998341
    0x30207150e030a03120b060403020a050432070311210a0f0204080703051002043002040f0906060509090a0204051f0b0406031107031409041d1b0d030f0503 68
    0x301d400d1071000019540500c0395125100c00c1c550007034048105002400005d00c80e085042092084134025840000d401540001050100b8503141d008012640c20011107215440d48050203051196102000000394404403000d11070340580c140600050f404810341c1252400302510b004e400504c20300323903c030078072a100744011500080c4242c2007540c0b06000440b00790749841c0c58810a0b61a02c03218441220288100d42c50b104884c0c1181c003d07241110901404801801400d0103044c602c10002d01c1d00c0200d0542180c521b500598561040340404a00c054000444000a150040450f4240c0c0c02c45403003001070004021842900040e42014203034150f501103041c0c1c60316264642c603032560b15010145010243c1c400325440074810041c2040743c1456500740022880c40400f10203a1280420140002d40d40d6400181c0035603504c0010041d02001400004842c1441c00b100ca61101c00e01164280c103409c4000c40042d02c0e040c48071180208401183c00080107a007079500600b000c41040c0c4841c00b4030401000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 835000836 1250 834999586 834999629
    0x3002100305090a12022d1f0f02073806060a0302040e0906090d090b0412141005180601050d020409020a032a080102211017010501091107030207 63
    0x224800c1c1680110810b58042c0c03440c5010b9212a07102160704e200e2440c5c150804640001e207085a160049000f0140c900c00382c860303400c5c40b0036000c941040041f16480d010b041e10050182c0c0700402c20f150040445042c9a041c0d4644110310500c84144e480000054a01c48026010304401880e08a00120f5165548946100c0c095005e40642c7e8090081c0c000c0c00410042e4040e00491203d20075401c5409442840f2171040701910600c02c18000c05407828400d000901c14059808522041c15000741008032124802941c03171440c002642c0120f03984540c582c4240034080303011581381c519034100880035185075070400d400b0803108600e00c2030291003281c48203102c4055499103481d140c00365401c0003a05a118035040c00c810090744c100100310300340f50380c25980003950b01710601c01d8803e00b41441c280313159051080c00c1e02d0403920740702a007440f0700c04501303240008150054040034030303000400000104040d850034401b07104507050142040460700d070802c035400009901040c92001d840c0c1080c80940b04074941d0f40f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 835002086 1250 835000836 835000843
    0xe10030213030c0f0e100f0303180b031f050d0302060c1803060901150e010302010e120f100f0f0b0a0b161a061e010c0b060f0307300210030509 63
    0x40c009410543c00b80c40204400a0840500055a55030a5400c4440d110202e5182070b00040744600b2442c0c01a00c103061000904c83e0305d459801c26180d6018596954844458082e1540140c03140c0c0c0701e01000c0a495158404840d48032401442d04a0740c4900c150040e44010f901c982d001040009441c00000300b01030703107122142c40c410681a0140c11201c9516259a035503000f00a5904640300b07485500a00240411085030580c0c1601d5040e510076448001c25414440030076145440c403d42c5014402c43c908c1c1c080c1c0108050f07103001007c0f000100300c42c1c0c01c14004104940e082103a10700f403503040480446058580202c207204070b4200108040e42c034268074114200b05440130800800c01c990160915909600441045000e02001ca0b000d2070641d844412075200462030b0b6210074040303002e4900c0b180c08641c0d5012590f0384080081e000e10298030b140c000017401c1032910340107400c44562089a25118003000a078501d00940205400d6030351910940014089441c6054503100701a243c3e0300141244d2800e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 835003336 1250 835002086 835002089
    0xc06060803070b01060e0613060e030a02030115060909022b0f050a1416081501020f0a0302030a110a170a0e040603150e0115120c030f210e10030213 65
    0x45040e01d071034003a00d00c2d00303d5405900303221340000030b124012400c0b864034140044a42c201d0303030402c03000d07461031070f000c800d44010340e03d282030795814000c1903141c1002d61000e0043d508168035260350988404d040140c0541008000d8008403540361050004a00b141036030800c0c5448a01c80a0707040c1036a51100c0f540c04094110030307102c503003918285014400c0f1031056400c0944c0d106100481d6650700c0e940c261561003640294070003a40002c0c10040440c0070200e6a58110049035010320554181200e1a00c14529011f550142200181d0000500d50101070b0721003502d0a01c928010702a00c40d0205a458a110390040903030903000c000700018050101c140201103403020707101c015100f880503039500d0415124602c814095114404d052003038404504030b042c490100c24540d2203c64060150a00d030000704c1c030b0705c2032410848071034020480c04008036180640d03506400e4403400f1920f0603111407180406034601c03040c2c0d040040c007070001d180894a0b590b60408541c0201c141c5030040c1c07a102040b184010240c0e09 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 835004586 1250 835003336 835003349
    0x601140d060608030304030306060e01170901090b010e040c06020615040c27060315032a0e0f01030c0b040e0412050d0e010f050709030203070902030604020702131416020d0c0606 78
    0x102040010303c440084080c610503406928208a115070ba42c8054940c640ca10f524580001e83c030480343d003002e101c01e003c0035800a241e03000006252040e40c1d2459040b10003030b004403404069007400c12041000c0401303070402502e4184058407a0303003040d440e00d410400159000610443e102d0f80c034451510300c502e40b0144004010f2619020090320351101400902050080e28006030400030f0039089000c4c10039860301140d6010503440d8044680c850560011a64040d206010402c5420006500308140742e800340100d00040c20f030103055240d85041001010940d0111540c0f800a000412031249000c040c1d95100b60803041201c4c40c00c49541040302c241c400c0000703035911140760203c20745d01c12030150720038085455034110801c1140c4860005440001140c44020351651244005102414454018603042840070303102506082c0396070700081011051090703c0740c103640d40c3c10f5100c280804082c001908001d082c1c495080155403040020f4894200fa89458240f05c1d03540c044904201e2030f035101500400c0d1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 835005836 1250 835004586 835004591
    0xa090c0f0e1801120201080702010c09050f19031505070311070206090a0f120311010b030706050a020304120f060f0915110702130209030d020d0e2e200105090601140d06 74
    0x71110703131030021a002d145040e80000c9070f010000f206a0700512480424a0700c684450100510b410200400d802210210b11b030040c01c454400d96894106c41d8550010b135101d9004000c0c0d00403c40002e5007202c1c0700400d800c0426007001c41e03d50f0703408000000c40d240b85805a51042d52400035402060500e4000e074010501e02c503141344001032000d250f40074940154401ea43c0e181c2206a1888040d099036031700000c0c241c3c55005010200002806080100054015070059904180d40c8d1582c0c540820307040c0070180d440c111580c81503c1042036521414910038004401003011001d03546035284820310b05921040c140351342e0000399a6020240d4280c2e5070b010b038010000c582219940400340044e401c060355a5000b44a41010510154000319804840c041c445e581d03022100e044204012242a415900048006d12080440800c02c295989030006d071929440d0182c624242c1000400105203400160b1110b9244c8414070030403450114255045030b01d4100c1958401c100040003407076500000c140100175a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 835007086 1250 835005836 835005839
    0xf03030b031c0f30020a0219060b0a0e15100c0b041b0b07033009050c0114071e14060f06011428140d0203060a090c0f0e1801 55
    0x2644001103c811100eaaa160000d01000301540003804030461044410141c21540c038000246540c0c1c05800c5c601742c548110f403500004100c0300126888250400e5802540702c1c00c8080d4181060107200004100440c40d004d50351502c0d4116009040340b21000c0d51142e0f441480c001c10071449115848403036a04900308031b03018109403070325a5001d5140c1c0c120686403a504130000035115000419150b80507015202e40e18114107030464509060200c0c200c0520408440c000001c0c1d0f051a449200786142c030640c01000c404002400244c4004140704171030182034003c0014100042002d4051118031020400440d04103625140114031002d0601180d800c2d0300c6990100051810314004840c05030302c0a0f00c07078090442108044003002d1081407104a0203d0000e0710012a10070800d152052401d12442c0a95409041c101c1d02410303503114681003404c46401005008552034192240c0000f0b01c00003030b0801121900440241039007280b105000c1c28003007007050000700340c0c8400b032041010100e58000d0345c420350b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 835008336 1250 835007086 835007143
    0x62f0f0d110705030309030a0602210c13090e0309090406230406050702010c0503060f18010f1a1303030f05070204050f01060806030601030327080d05071407030f03030b03 75
    0x9980481c0028a500c0380c40000103403401d0200841d000c42002501922040c0b04c252034040207136020f6281034051200d12090704c480c005559101600400d40351041030341d01c4440d0b0100f150b030304120341c1101113403600d4030b141c2040c0020000200c1f19035042c181c0303040300c1c1a41c1c1d034107250008111554144c4c100f1a182480e00100d17481000b03105200b184100010042516400c00072800ca07030000c0c8030f00b400300f130b0200081807035454040c120000d110302c0100500601d580160810340030b040c0c00e03406603821485204081c40910110182e0b80c0d008004040c5040c24100507204103050f0341e405201c05401d1200d041c003281d00d050712501c106c1d034010790050424441410400c4041c85400400d22901000440c0c000c04902c282c6004203e5904903601661000040c0d4040200d040404c1e4540c1480d01c50a2180303080003a80c4007090151507843c8231706840301500d6400030305050f551a40340100c3c1890941000b603051001843c65807039040210381500d00029581007000200b49040c40004080303560005054001d0305d117 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 835009586 1250 835008336 835008347
    0xc0e0a0801200304030c0b0405030c0f03090f01020c102f03090a060c0f0b060303070b0406091202070f0e0408120406150b09030601050d050115081006062f0f0d 70
    0x40312202c0c24040707088080c26061842c0c0c00156001400100c1e0040d0704004100c05e05c814580184c0203500341c034034180e4021452444e25108000c2c03079503580c001190188813407070120b1400050503820b0000d0505031070301c040025881400203902106010070500d18848003507403441c0c0480400e080c1c0383d01e40e01d251080324407545c0d2a003220307120710310500c0c01040200305103110306482c1c040340341d03c0005001c600c00c0300c0d0703141840c1c80801029950140b0090140b240801c5940002a00941c00780000242800e942d0515881c0d501c1c040c0c90300300a650048038200502a49240e903441112134039143c4e070b08c02d9161490700c61090310481c00041410302c003040030304c404d00400342c0c040545900329540ca07441140e610640585213020384d6031881d0741900940010000c5040c0018000c1405201d2000024040300c0e040c69000200344c55009001e4960000c00190010002c43c842c0e02e02a010500309809000c0566141c81c1c4024a0498544441c001c000da1000a40034100070600c640c484880c165844240c0b0824020308 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 835010836 1250 835009586 835009601
    0x60b030a09060507030b100c05011107200402091e191401030501090b150906040e04200303070f0f050708010c0c1a060102060612030d060608040302010b040b0901090c0e0a0801 77
    0x10403500c2c00020600143c001e01c640d55001b07201610340b843e4804810703800d4410400115080d1130a5484214240c2450076401c01010881c2c460880d0f1741c0f02201e81802c42401041c1c0c2a440c034012481000f00344042d9441c0000e0302042d000144600c59403e1820f0049030340404c40042054204072200004603403465061840d08030400c00ba40c0400031682d8a4800c1c81c1a9002d5118940c0c000342001d40c00300117611480020b110740c0c1d07406071010780b400f0b68800c0328031003194040301c065404030b0721004403c003040e201100b460402e240440045060104a031112950301c9003680c0c00034190109a10107104002c414040c0d4801010708038020002000e202074003a02c20551100b086030380807482104144c0290380340100038001c0106900401180e42c510b0700388000d07000e44070150000340c407043c000c42401000034000d12004d800345940300f505c0b60426140113403d40300c0c171014283c41130307050091b444403030740713074120030504488002001149020350340d00150307100a0208800c0d034010702454008034215105410071103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 835012086 1250 835010836 835010843
    0x3080f130320011e081609120602130e010b1602120105240102010218090c07060c0c021f020c09060406090603051509070f060e1203031017070e040b0406060b030a09 72
    0x45514038007a00e45440c6043c58050703040810031417400700e07420300c501080840900d295402d0282100380c8485890b2500c0141200032620b19400040a1540c4840811040c00900e4502092031813541410080109401003161800e40309001403680f50566541801200c4113503095402008103080403507c042c0c0c40303100140d00d24281c0d242c4000b1f48500b54814030844e5051400240b040980820071800c000305100c0290883c1c1042c070f0140555001b1807102d1007126203001d082d884a254058407071051085000b92694030309016005000001003580d000b00301d051518104440c00800c49d5210340008000300041e80003012030910b804008410000c00280360b9003003209001c2141c1155441200d4039545c0e1000d030044540c00100c0460030000b03140640710740c109000c0010480d40e40081c1d0012114650f03001110000c0740381c240038000b0447e100c0d1504440300c02c001c10700003406c030300d605005c140c5042d0070300a00010049002c1074001024007100c2c0c0c1c001d10141c607281225503500d0400c2d00d50f070390140c049034500b41c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 835013336 1250 835012086 835012097
    0x203190b060a0503130f02100f020106050414040f21020c13091e0501090b0a0c110106060f0e060f120f070e0f12010e061801050f0103080f13032001 65
    0x400140c07509005a9281207a281c0c0c03034520391760320072000340340b901002e0f001100c803400c040c03d030807005a403007103842c0991506564540b00c200e1030f2080000d0a64000340e0155000700e2620400c0c00c40540d800c81400d0348070b070300700c0c080c0300302c810b038a00d0a4810341851103078202c0c0745070310103003424211940862940100002141d880d041c8030040d90074501214003c240c02000302198036204482000290b0358814014090000014101641e440d54024090704517100d240c0c2c1070303075041d940444580001d00c4021007900ca00081010b54103142014000030501e08006043c001c20741c922200a541d424110740f60300f01da11010303d4031000c11400c0080b50003425203214088078120300000d104e1902c1030809070b00790708005144509100140d81070103842c400c603803000c40b40c95498005030790f8500400c02030700b4029815200c164003004036000752142120800b402071522141881e0041004c56141419180c0c03040422500e50b07600e51603221181034142040d403005044442d01304042c810030aa0800102007018207880f0b1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 835014586 1250 835013336 835013351
    0x90a031e0b0a0209030601030f030e041b02250618030c0f180e030a080c0702180604061a0405010e0118060905041a030a12200304030c080d0e010302031504020319 71
    0x441c0261300a500105415502c501b0040001c2040d00302c00700d507014001d0070a000c00002c0080860117980e01b41114844002113080500da0003513040009146401d520061180e5412500b41702c000c4150861140038200000e803140e0304100300585150a0003541c1c8904003201155580100004180e610710903025502c1d01490410350360310f09401110013542e070b4078019506d044500f017016500d0481c05001552a00d506120400041e100e030300c00d00510104090014940c0e107000f400b0041503a0761901300000700311601d50b10000203021182605c0a450003400d05401400b941c6004850840c0030f03002082c2c0140081078001022504003109a007a541c041d101400301c9844000200820a807400049415a0007408080042181d8050785d1400440510b441020703a803810700d07075403071f5845c2c2c04100320b0f8140c00c00074007041081075400d02c0a008084d1500900f664015080300036160701805c0961505140d00000011540048003846407080071000b4011526400c10081241055001c0350803801494a031007007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 835015836 1250 835014586 835014601
    0x1081b0309062d0c0a03090f0c0e07020106081b010c0503032a0702030c09061908010e070503070f060f1704050a1718040218150711010f05030c090a031e0b 68
    0x4086031440b9054411283d925003240f44401548203100000806940d02114000165412500d91440d4003903128002050f00707113007000b091301700c000d890241960326003e0200310365203001c102214006600840340041c032483c0401070ba0342c3c0c0001c101c0100140000400c020244450000c102c900c400140c00030306440a8504a207882441070300c1c40a517040d845219000c0380c07443d05502c0e482d440704020300909000703641d2800d690049200d5410800517a5107811f240c98030f16100704102c00003003904900804901e882d02d000784418840398010801081180c1c10303c68080f034083c810f41030501009195440180c0f50906001d41c4558884071704803100750b1000311964880c42c0403c250303000c800b1621042480a150b00781008000e610600c03041c4100400b240608141c4d80d1403014075440075030403513030460f5200c1c0540342101d209211203e626051008182021121a0b80b0400703807a0f0000001554541d900200000601a00c055500c010040003083c00d0351000224103281c4115058444c01c0d4400040d101c003107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 835017086 1250 835015836 835015891
    0x102060403080c1806032a0301050f0603090102041208070312050702030301151b0c1701020703020c0d0f02151b010204050d03050a2309010905011b0201081b030906 72
    0xd80150008000c030000c10700d8914000003c1c4000020220f0009140c3c1081c804541160411a0031035400302030741d40c1c404042c2c80d07a241c600c0408003c1c45005861903041c240024141d00003c50101d000f901c0200004102000960481c0c000c0c148621000307101005502c0c0204240d844400220300040034401e64040c000c029000d840c1c007800daa0b801175803d5030300744429407a508240e1680703841001948524610482110001c80910718021245c9103103642c10000b8082c2414044844001540c2c070402c00d038130100e5804200c3c061804001c503100342c0d020f01541840201c0344038290700030354000807952048400301180320040a10f12403140c402044c0c031011b085110300303e0160f4840d060700b05541d0000c00f00040d10440040245100609000481c81c01d1000c001040442da0030010440000001b03801003a507800200c001e00818003486c1500d190181c00281454442d80020020306104840c00071a014040005207000701000328080551070345040140e49a032000c064800601c035880c1d03140740751103514119 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 835018336 1250 835017086 835017091
    0x7060f03020903190c18200a2001020f0d150b0c06040f110301140a18021c052107051c1205060a0b0a1e080702150703020702040f05041101090807060804050c04060e15010206 76
    0x41e140d00c3c03851120042049d01601c04001c0b966110755081221206403075000d000b407c800d0035602c1c8000b403c010302d08440c0182d507075242c01481002a0500140300250740001d541684245c0c031a0b05110f8406c09031a050440c10020101203600d0b50030240442c00c40d04041200e02c0c0704174100003061003031f8030072883c103503121031200c40c0d0284d040f60b1140d40300303014103c00d4540f0040030751041381100d00600c0a80340640103a0740125010400720710000c1c0c050b003802010400107000e001c10446100a1801e0395070007078503604099001140990702e42c2c001031007640c2c4030740550000300760818549541d0003c620008100e048181620400382008031100150580700d41d22040c403c01c4150010811041d103003550755400100181000b0030907800300951001a140c60103007110a0078400004266401e080c40c106841081c04414ad90400000700810070508a0010f4a0710440c4c1d2182405505510b50382002c6040984040d400c0e40c00034100710b0001100900800310078415903008043c4407144e0307a210012601c86105 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 835019586 1250 835018336 835018357
    0x30203130f0609061803020409050f240403030b3006090708030a050714030d020711041512110d0c03150e03091507060e07060f03020903190c1820 64
    0x14803044c4604c1d0301030690740320a201c10b9001c030000c0310340e00d50004003500c0840d04211005c0c0c0040c070391140e10071402c01644c101404480301101c4092a040c0d0144400100100b014081540362070707070895a502c8400e184d0301603091107000d4150004a140220640d0100e1550000e004d220314800a055810b0206204042d500c0b04005075140010401c03085801e5004070100b80c401040c465001607500f80c0c100002c098420307820794017603252000c5090104002d500c00c041d05014504115045224225070382e25038007503400d84001100c1130300d080d0401000e1404031150158029003800000030500001040660883c0e00c2141c69000628000016006981d40c0b1200740f0380580c41800441d01a103000640040300d0504000d400b800d11055840e1310080d2183c0109511450700500d50900110303500c0303a0308034518801800c055280c0194030010a0b6101150a1500c400c8040c0888601c2008a4442084020041840c001c6813400c0004c40782c40c014500c04c0f00e00760859052041e4103e148201034240c034000f40d803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 835020836 1250 835019586 835019597
    0x100e0405070b0310080706030903110a150f0b06040f030b060604060c17090607030905100c050a063c0b0f0607030804080d0f06050901050a23041503030203130f06 71
    0x340c070b0b600c01e03140c1c0c1002c0e111008144404e28007040038941000403100030030f076a5030042600074250901030104c5030546803500041d00482005c40201d580340400d54904c2c40ca40707100103880c18a1008100081220482003580050001400a01031242c00e50084c10750703014613040f08260b140c5600b08000f503c60f80c8900e030003103800d03145000c01045690041c0000760082070003640c40c0c4031981d00014996803100804a01007801c41070203004034208015100064141070130203088840858840315580d4490705002400c03581c40e01e91688a6000100484507009030320800c40c01039000006e0802140654440c102140c40e180480d110300b01c1ca41080b18524402d0064252458070105460413180980c006109694900040100302203a0020f0703c86c0d000260b615100000b01030341460100904804d040e4052441000c904d0030900959902c40c022904180f801c00c600381c03a0b4112400410084c0441a0780c0c0d040e0802d007044004241500031006040c0070500000081e42a9110441104816200d0144c08000351 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 835022086 1250 835020836 835020839
    0x1502121503030f030a05040b0a0605010e0f0a05060c0609010b010224060f1207030b0f060306240d12020f070b0a030b0a030f050a141b010807050d0c08100e040507 71
    0x10000c012919014406000d880c030b000318920103401c2c682d01c1510084482c43d60340081006120f02041200d4200c3d88014007030258503c0c080000341200302000c902807052610560740030096481d00200c100402024000a03140d900c01e40069032541002c48203132001c5d509041300c400c06580301241101c80d201200e40d42d020104850b01006c8450200100380681200340c0e80c045c00c1960742c2d1006400c0f200200700e0000c0c005c6604524000f06c40da5000340100801d0702e2403074140819582d02113180365001c0103400e0b02c4440804004084606000031020b4075810002800306070003403114100b0810010052a02202c0b60441d00c0541c89690f078400b486907401c040c4080c0000501c25101c1d401c01d40714070000526000d400e5807691940000744c040f84404980da9401500c5003020803030b6a2021542103c641c00240180c0608180aa841050b2100d2400e04020b003500014001a0080341034130f0015103a41b0302080b109400010141034002e0907a42a002000c4403240000c03010a5020100d1050354407402030070119 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 835023336 1250 835022086 835022101
    0x19030201051902010f050a0c090e040b0406090c0e0a06030204230106030b13020f0a02152809080307080601110102180d031407060b0a1d24030703030507150212 70
    0x4154242c009070855480d0100500e0f0707929240141ca001c1c481d0024001081e1031600703806440d900503075201416031101d050030040800d424980e49548250444d6001c030f8034001c6031419a2181c100c1c0c0c1c20108202c41c44100340940e202e40c642c41142940e01c241d13010410050a01c0351104803c02251a00d15100c00c0c40c401407242603c641c20640603014040c01896840742c400c0034980590704408201103407c0c81c01b288003001036604010f06114200403211012290030107140c0d803110001c10810238000c041c40060002c4004610f5400002c0b480d4010300226202d042440c0000d001407420b4507811b0001712240c092054101c0103108031070302c052070710100c100b41c0881501401524582c602041d001d0200e07140001a0040c0490010050b00e4400c81000442c010000200640c0d00703400d800913003400d0001d100382c40b08107210510494202191580e440e580b40590482805800c074950850340e05805041c2000080580040c05410040c3c45292280d1442d04517115990032401042c2202c41150356003800301d50311 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 835024586 1250 835023336 835023367
    0x1009060b160204240e040b15031c0203040e010306150501020c0a060e130e07060810150c0c05190806090307030207030f1a01060c1b06120e07030204050906061903020105 74
    0x602d004c1c41ca60607141842d88140890f40309a4019198031994000300800c021050400d41d5021801c40161034140741c1407000f1980c0c1d00d035440351400d03006001c500c4001c1410300030416a0010444001c10707520945e100d03e015405010380c21a0000030548680380496550300202c1e07905081d14001c0c1004100620341001200d41e810007042d2035801800c944400d0182d0380c1c09000e030012012006008219441c40e2181c01007099200602c1c4030400120000140000106800d643c43e906516183c1050725400c0ca0400d680000324030f03030100f81e2101060301aa0485e1200c41400011a2a03050984a080d540d5003d203503201d1044581c02070060304080020b000080140d00182400c0d40520107901d00d200502131407014095081c1c01505c04940d4a44180303080101d601251480100400c0d00c4101c40f51030454007415042ca0000080ca1a54481034841420601080700e407008640044c4180040c1c104503404036159070094034400d0003081e00c008180080d01c00110301004480e03044c0d403190f10709a00420080304 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 835025836 1250 835024586 835024601
    0x180501060e0d210f17040209310528080a111609052d06011101090b04110a210b06010e0301050403020c0112060b160809091009060b160204 61
    0x86a00312034801c0140a9000681900310426944528031342800441c400b400d440442d000b01003845040d4420040183c4585540d1500700307644048590050800200411210707401640720400b001c1b6030001c203801c0c0440014182c40305007140703015074203200350000b95103d009000d04000d4503664082042441c1e43e4811680312010440d00c009039110181c2030760500d000e030140c40e44507140b015110001d10081d0000e0f544c42c0e84104060800e4400c810301d0b0300d4281001001d009001c80c0c1407003e154903450340030b0020b4026402441c0c0c000a00c080d145020329101d4400190305007114041d2004050218460340401c4034001c000d5444040c081d0b008a0541d10840303154402007505040110390140c80249403002d024003801030344250082c04501b040000014021000f802c2d000503620704141d030402208018204440ca4070480741c400041030a03180c104000c00d4494620540d40000d540340030010541016080c0b241501c0e81010140700b00d50b40d807043d040c50fa000d854820420001407a40c9a001440e26502c0400c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 835027086 1250 835025836 835025843
    0x161e0b040320060f070213020909070e0319032c011e120501080604110621040c030507240f0815040608030a030906050609070221090613180501060e0d 66
    0x800540d020030109072150480d11013120000c00c0401c80030210f15040d40c10b0500b10410107000c6085c000a0400500c840700050310242c288005400b20510a071010b212514162186a504c614511400c0c1742c010168882d0310b99503107525081c1040301d10081d01581c035051840318142e5605105020004603440c2d0303c000300c1d0313940c0d09006040888140d81d030070900a140c020258a00500210f2801e0b0416100070200365000c07034810b0344100404070681d4400e5200b0341030380d0300001010186a54a2030060240219a080901548610080042c040c000140da000c001502b802c070607904184810015100342d240c4034000408a00c0f1240020022004103030003c030039010040c00864034682e101e90441c00c5030f000e003035000002038a4007100814440c441c051980c210b481611207100a1501585c0252500000104091041602030744c4030304410001c0180c640c4040b004008542c5c5210a8260080d0313407138988102c603a0310412072103844001c444c91091034120340d080e403121038000300c5107004c1100c0c00c024044101c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 835028336 1250 835027086 835027133
    0x6051804033f0507180b070201031e050414011a010e0103022118071202012114060406270e0111040326030408090103021b161e0b0403 59
    0xb0780280700540b400c081c0030b00b0702c07030048603070040c1645403034080c0c42d80141140240105107140c0b03420301040034564001c0381c80c2600c03400d4a84106200490180603100503c0101c00c104607900d00e250011640710f00d011318070030f41c017034048410001d00084c00c0e1034504180700030000f00c00640381110350281040480400052400521b403003400910700c68007240c0203040050810b480c1d400c0143e40364100b84140040c08429005011091034041c00c05080d034810031000781040340402c5904c0c0600c101001c0d00c480b144030842c042c003200c0c2110720b2070162818200c0300e062003a4109440000c1d02c18403044072443d080b1000880fa44103800e019041d90140c04e485030000d18540d45c8a02d1518010068005000910303c10580443ca800a00c2c50b070001c110b201c03402c00032a2460800c14040002e190764100e846e00c000070308015840e401c0c00080707110101c0345011194824094010b005944914801d87c0f00117641815913440d549802c4440100d510310014010401d021004010038130202c1e144aa50040300d101d100c2c00e6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 835029586 1250 835028336 835028387
    0x60d080f0a090501020d050708040515070c030f1209031a04080c15060a050609090a2c0a05070e010b0d0e011b0507060b0d0f150e1207060605180403 65
    0x100110703074400c007007100000c0c40204042c000d640c1e06000d510481001850300d24104545902c4d150000c0c400c0348a40e5126642603034030105110030300030a9030280e58100400903150350f500d0801d80e034045400da00448901150901a80f2482e014204480c1600e402003101d640006205038204001d901c00381003564402814411003da4550030011a130400138121b880e1003240c20b00005214010102c0d030803442c401c0300306010b0074000341c03104d001040d800061080b002c6000d14100640c0030389902c000442003c500d0301d6800744048110000380580020b403003031045400e0281c0d9485a0241c3e250b0078041e0000031241000341000503039881c2c004040c1d5120300310001a0705181d1140050002c100d90702c000b404554007081e40802d04c007041c40380200540c0b003542c94003000042562007000d01c42c00c80030000d01c083c007408110300c40b0a00c0d65001c0c203445c1480c081101c45403030200e1643c1d1840c2d0809502252800c3c10400c001c0b41906083e140411040410300119419031110365055403c54104081c1d1510314440000303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 835030836 1250 835029586 835029607
    0xb040510020a0b090f12071101050304060207170307110d020303191b210b0a062010021e091302160c03060c030e06060d082119061706060d08 62
    0x80c035134011402030004100d4250b911034210b0034246040202041c1410a0001d08089040401c3c2c0d801c00f0b540134a0070541c0e9940d1440c01c003000b4040c0d550080d2100d450102d000c3e00340a001c0d4015405070104c0d4481920001d4124113059550085803085e000580080c40070803440302c03a410100b502d1604000c2d003ca00598100740b516203c03000c070f2155400094003146416640700010300345041104002c1d03024441f20700310300c0c08100509403911a20b82000164100c3d0715030000c44015030010b40c4916020389615102c00d12a050183d0400302c0041030b00300104030300200aa204070111414200050020440302c410246000c0c02504000960380044034079a424000103200307400d0702805140705000008442e02c0302c0c180101100c900c3d555039038440d03100406002e081d0b034070100f6021400740e0096070b440d5212846c9180b030b01c00c0201205000852280a01031240c04802c1180301e025841800d202040015130320482c0c5107410b14021485907040d04090040f900d1070a14a284c50900e030f0282c20000e1601c0094503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 835032086 1250 835030836 835030853
    0x5011407050d0e040e06090c090601171302180a09020102011b020a110a05090f0a3909050d030e0316030f0b1302101d03060c0d020306040e030412050709060b040510020a 74
    0x321004840d070800008403c4034642703000443c3e0445000c0c68400010000c0303017403811400c403000e0b0035441c52035513460b6640215643d59840c0c03081e8a42041c5031003102d080608c0400d02a0010050490155080c40d02c00c1c81761811001320512210b2169009000f58000b81d11080c2d1502801c0751180d130481a03442021031107480300c034a43c1e0b0140c0044941000c1c02c0c0b0344600036008540103038400e412503078071190922000c120010b400840282c05501000080600004195035002c200d40c043c03600103401e04000d0041c55002452400300d11802e4044e210440c410010402c004800c6000c02800100c2e01c2419001103200c0041051f8000b83e1a0a49441c0c0d014640006454588804212000805500e94a000710500840600308030900360000c10403401e01682c0c40800703024441011420a601100007030813981c80d500081e004490030390071b40e5600c2c1d4441d040c0700c025004480094965204010300017400e401203100302c00c00c9510b10b2200c181030600b000704002d01603842401810840c42450440f2000c034510341d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 835033336 1250 835032086 835032091
    0xb03040c0305011b09080d410702030f15071d03070e06031b1e03070b04080102120c041401030b060d052a07080909090715020705011407050d0e040e06 66
    0x3244c015403007022004004201c0481a0840149600a60601408250000840352100b20301d00242c88480a1700b0b41c100302251070b020780340f5205003e0341342e01172807204452000b444203500940980e08404500700501d6a0752070084280135180341e00400080c040b601c1080744040340210750b00c0b00f00d00d10031b80c00c0c0041d182c0521900280198149241440018a01001800010003281d00c0e4219054003140018054080b4003110840005603c446a01e095a05202d408050b20071101502d4650fa1106602c9000b9040311305240d0314460801c021881005042d401d070340840302c1300ca0000d03009001042c011400351042811080c0c0201050044110b15541c83c000d00340f14026900586400403002032003507102c04031007100c10304601f41c2000080080750b0260122501a90300360380c0e14809840f15041d4038501001c0764041e0a003c00a1420740c0040c80d030110341d070b00c02ca480036601c0013481c8882c030500c1c000c903210f5220014100d5100c0824650000d028504201e5040e000600004894116001444c1085001c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 835034586 1250 835033336 835033361
    0x50a020c240c0708030c0d11160e060d0633030c090f02090d140c041e151802071b081f02040b1201051c0f0b0a0b041407020d05130b03040c030501 64
    0x1444407c9059a00515415160310603030b000301400c1c00180c0e07000e2030303c0400e80580d043c040da007000050758a45501c0d11f07080300d0a0340094100300450422001c0464501103c40b4042c00090041c048007400c242c0340c512030160b0307030000282c60020303140c0451000100455000030020a03021f00003000507540300305054041078044d031007184d85174040c80c60b580d08001440d00001d00c10b6241100c252112444140b031f9910240340d26000246022090100d01c8212003250b04c6000780182d91135100c50030049580162001718824441009030005204c8001610800350040b149283d104181240100769181c2c1d2500c0c1c10207840340c006140c1600c1d11860205503200d15441041c0030801700c010040c13800c045081c0130409800300582000040710380d440c880421404500505100c1c1c140b4003040c401046a031190b00e071000d00420030400c81c0324400546459107400c45100c00075010705254040000d010b45c0c220344807080300d0b1101c101420300304501c0d01e480d43c10140050741e61052901c004030006409118441c083c488 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 835035836 1250 835034586 835034593
    0x140a0605211912031d0c060705010902090c04090506040c050d020a111e0c03010b0a1e0e010e01060305130c05011412040c230109060f030b040c050a020c240c0708030c 73
    0xc04070f40244c00c0d95055075900c448101407040030041400301084000d44482e084030007a1790b44800d41000b50140c0350401c800307035001d038151080c4000804d0701c000420440300190401c2c0801c1e61031000b0002110025401d4901041c01048603551403c45540140501485400c20240840d410180b80d803500b507a04002c0116031104924000e005582000b403078002c004110001d00c280d00fa444040303018400e02c0e208140744901602a0b80918452103222007024018941c03144c0e07007942c0c1d078410018201d1001e200c0c510101e032500010a408440c121440305400760000a030001d003520b0719004403540e02460040c0c13141e2010a0214031a85c120002e146030159004c1c181080480b130801c03070f0000c1031074400c0140e0030080340054420070942c0d80009211007110801d040081408201c95001d0b4058840d088030607a1191030440b1583c1202c0d0000301404000c0b07480da0843d84280400c00510000b49010380c220350391101036008d18105a61090010015102000180d82c5501d655a805038915002813908884940 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 835037086 1250 835035836 835035863
    0xb071406010314100b0604030308040c0b0c03070b0723180618030708060412120f2d020414040e12040e0609130b06040b0105090310140a06052119 64
    0x2100304012640040c00c4c2808000081000b00011440e1295100013014800c0000028040c4010709156200030b00c081c0020760f0f900c07117402a600b42c4a038000842124030414032408220180d00c02c18543c115400caa078003010381c04184000e8501c09801203580f01140c0c26030000100c0c45a02d406003c0c01100d024002074039403200c1c0110030542048005d8000350034a9104808200214080020242a41016007440400d100141c83c0300d10150020b80c0010804500f003d000900b41d01b91146c2111607484e10403d08240214252070540c00d0744618801c0c48060110008803141300c1c6455485000070844c968112400c1c100d488011651540107a40440b810341601c8040004c3c1d41809401c0b0359000400004ca413051403a80d80c0c8050070301c0710250141b8040e0340e45800025003a4040c00840b00c4100c0001d0443e0074070a10500701d03070090406902c40c030100f00c10400114500007000c0c05007900b944e44c0140720000c3c0e0724030b290520071001c05560100b07119100700c031210510701100d60003594086028007210540786 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 835038336 1250 835037086 835037123
    0x160608011409040b0411150418050105041107030e0a03060504080d0b0306160c1b09200c0a080f0f03040b07020607020a0c0b070302010623130207020603010b0714060103 74
    0x51940749409015031503400801000907054035800f0362040d40051598000005030000c40d890788003017000f030140307408002000b10b00e01900000112160b101280e00740300b01da80310010720040d11006c18a00304203440900404d40000e000c5c82e2403070050940580390352036240e500d0f02c5540039603406030b400b0f4500010000f01003a10441c1400780c01051442a00100194100084660060685082c1c0d200421500100c3c2008002c841e10201c00303c9580d000d40d034032001d0303100d00000d00140051180d00c024110301144c2c0b214101c94450170b503050404a040908240d00242e20707950a158060444180c162030204214000c510315080554003d03070142ca4880142d14200c48064640b110143c50001554031010052000403e00e4034000c045e10303214410140c8441036450141d0242c04281c1011000784040b4006020841b00c40c0e0300b0079510751089803814004d4402400c0181280b05000d0042d402c0f400400050043c521020001d060161007000a400f443d201000540d0034001c0030f8008440c403d140600d42c0c00030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 835039586 1250 835038336 835038359
    0x71806030506010509211501090c020c1302090a0f1d0f090a060e0c060d1505010f0206010e0709030503070b010317040b07021002150f04050105010b032716060801 71
    0x2401460400304100d06008001a209010f04500035200e41c603038400c42c60244c0040003056143e469200f0840d40c0b034103003250400207058024012900300300d00d017280c0c8011003480007510950642c07014000d11258000200450b02030b52241071420b400035a01c1d03100242c13803000224000020004160b0055007913203c48201d6003481d0340501a140c1200310b48040c41000c141c0480c5c3c0306d0b0810391180000a0a4211520b141d0074420b0640e40541c0c010404502003072110015003003100840d4401e1143e000f240d03240e000541c1c1c0d00f0341d00f113001c50059000c1e40040c0070456404044c982c00043e5420489880d954955031303a407460b030250008541d1041241c004208100302c01e0901c001e03640908800506103810420724024038000c00f50040d114080c9e280c044040d050003800710390400b1290045503401d514042d0180c00c800c92040c0c0e4121110361904000050101d507003c10360340607111540050041c49801801900c005170140000600c40c01074001c0c80058903c8841010001c014507210041158035045144c3c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 835040836 1250 835039586 835039589
    0xc1305101e0c081803010b040e030c060702030a020a030c03120c0f03200d020706090203120417011b0819020c1b0a0e0403050c030702150909060103060f060f0e090718 73
    0x18040042070020003e0001c1c001e8488980c0d190408075141c1e00f44c5400680500002c00881d50000d03d07004c20300101044c0440100a000d10300412601c2e00c1d01d882000721381d24420062108016006500b0b03400c00240306140103521a070092610002c551500b0703980c40100e60345944400003094048640307200c240d405015011040a00341c0051100c00b1020444e0007003482100d1403060056400103001c8108802c0d50310003044550058102d60360240040705403030340c9078014003490740b0f00d41003a0581c03152068140507030307008122190170007460189108026500324501030052034203005e02645200a0b505584041d000030101200108074210148882c0c070342110380b401c2028043d8156100030b2000e42107000da1309802550516200f583d89120000940c114060030381e0080d484080510800030b482c50324400781510b8a4100d58060082e2500c2006604072801403052154810440504100c424040c629084040c41d89003804a192940c280018402c0441200d03040e000c00e04030305502542d0040b0242040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 835042086 1250 835040836 835040897
    0x30d0b01110d02060c22030f020a1e0504110910091403030711010c031704080306040f0b090402010810030b01030f031e080a02090d0605180d030b090c130510 69
    0x101985001c03030000c0d281d0034010030480c110341c00014401103907100b007403410707a07810040001c4080c690b482307117864800c80c1078403101648610002c05d80811103029103001c46004c91080511a10528a42000d01014001004521105440a00852505844159280c4000301c45943e40f00f880034140b4417511400d14168541500907803051001000140c00517070a000d502002f42003107000d0144130b18046502c00034814454003590341c8030080c0020014503002550240350101c90501540c110040f49404036103150b19400e44c8041d121000c0740255001745071040c0c00004001d0b4540015850f51501c45850100b03038411240d00032840c42c00d00a01d0340c00f00424401c85444840d29401d600307644401481040080c0418025a070300203410140d50380d80503a41141d6680c0301c0c0c1300303010501c0d1011a6680d1010403907601b0200d070080b50760901d80d4500c02e20503040a0003006142100d5612040280700841d085651030b2801d1132050030303000c1166035841e02c1e4000380f8121a621000d9126599206d1120740d11b5040c0ca44 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 835043336 1250 835042086 835042093
    0x70b0f0402041b0923060a11010b0f2d040915112113150b0f0402040f0303110312040f140d0804060e01150b0d0e030313020d0c08030d0b0111 62
    0x4003140f64014039503001c4070301a907503000c4090f41c203d584a01c01282e440407a40d02800c005541801f898000e100d501c0002d030600020051100740e0300a01c5040b1076000c041d203510050400003441d000380800045406203da00c03402c000b00b80841d90104c0c0c201e031760091007a18510524411320002000502a8004900c02190110300f00188004030384400303c040280c02d41c2617000d600006000c8880b070346100d01480d400480056200e00b003040700318010295081503d00510520aa81005041c18022542100e000607981d0680500d0f6031811120800c900010100c903000c04c00801501070b031410b030382d640206e00540c0128892180c030705e40080000d26050381c20340c0f44e401004a80710031940160300168010303088000803909920954800b03006020344401000400c180c072102007015001d8001620603002400703400c024651100250590704c1c08101c07040b400a000070400030b001420000b1418211620810700d1030402515030310014215005000003000c0d240c0d03641c00000d0743e580e101002c0d5134107440c1032014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 835044586 1250 835043336 835043381
    0xf020c0c0d050601061b0c0f0510090602070b070f0f0812090f150612150a0c170c07020604030804090b04110705060c0a260a1506050a1202070b0f040204 67
    0x840f61512414440c50003846070400c800003148000c206a003c12651010300001031a071200c000300103004d46400341ca070291140500348001907006030f41f0801070701d0b016002030031b200f460f0450304400380c0e0080c141114154074849811001803c0c2102d41c54110744204400c44e103c20350882d4414400c0b400914200280d0f01c040302448070300401044000340c405146011883c41c0ea40c50000c2900343c40000c5001300c143c0310782e00c0226489207205007440d001c2e24507007106210b0401d081208542040c0821374945115407800040f9001c0c40300320700107040780c600c081c22050a0503900c2c0c4401d641608541c2c444d44c00c290b00c030110b0310001d24180c41140e4255039549026401c0540507110703240d45800c003c018400303000c0c0000d40160780038007c91940c002c031ba400f0220341c091041305c0f00c041404a40107075400c151545c20130244190030140501c110b01a2252540d03500c0c00d20903500c90480306401c04030080e00d00c5641c00c000b414081006101d072148504406a00d40326281050700c14441104c898404120741d58881960 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 835045836 1250 835044586 835044593
    0x150103050903131401030e030315031b0f060706150803070c0906060e21010e01020c0c030708060a1104090903200d0c140106240224010e0a06090f020c0c0d 68
    0x40c0f81080d00e040c03465800b00c240c0b02c00c0c01a40100441aa0100280b102204000040a40d800c030614088011750580704854071200700e9a2000140d40c0402d40d1200d1908101179060500c4005012594001d007800b00d00190f0030b001021200480b40c126002607000001d1203001c0c0144200d5080080440343c0003000340d0707481c2000c02000a4080c2e1252407260200106d450140e5601d42c20141f40e43e801e69000700403003220584050f002b503000c0c800c000010f004004142001f45804904070381100c0c03017117029101ca50f40d2410700c01e0003040e0fa4402111101402d001c042078000b2a48524858148281c40e5030103d407802c83d8240c0500c0b208a000c1d001c0c3c50b4041c10154203600d078000001e46400707500c080311600e250303040302c4224090700d0b00b0b4120014041482004c0601d204989440c2c60140c80e03c0d0f02980c034440f07851907001e0040d04015102950b450f00d00e400401081004402d400d62000e2410b10009250b6207502c418411780f41c4288091001d039030045031400c18010148590800e90004684561414042e80e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 835047086 1250 835045836 835045867
    0x60105090c0901030207110301020f0703141305100306031704240f0309080d090f02090f15060a1b030302220f1502070308190f050c0a0b06010207030803150103050903 73
    0x601d0b0504161300800e202040018a074107521241c0340c0103009544592a80d03c3d00141900101016800030b00701d1b40c12000c0420380e0300c044800d6861000814908641080c060100c40840030904408140c5e542c10004040b4680000750114040d200d0401a90b43c0d1509411080c0030440303411200840c001010a940d843d9003160601c40c040c0e68509000c6046146401d050302d00b03000d00641505c01506111340702c81003107174801040c40c44074802c54500480b03071510054140014030845409200c01100541c0003000c1c5042c03005451200483d25145c1482d0480e022805007000071700a045001c03a8005c1820b00030505641a604502d46c90314461800030f40c540f085040410707607940304440b0091182d007480b4580b18401e0205001442e040800c1c69a1100c01c000c000c0700d443d10311644030b00000c0c1031050b81c0465901c9901110141c1220f080240004400398540411100e000740000781544141440000041e10040165100340403071482c807a042c280c00d00001d4243d51008003007490750781040120744907100824 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 835048336 1250 835047086 835047097
    0xc0108040209070c1b060f0206010f05042a0206251b03090f0311090c0423030c040f0510050312490b010504260a1a09060105090c 57
    0x1151a4120b645910209407000700001d200a44a03003004121240c10155404030b003401c42c1c640c3d0342e4038545100c8002040380ca800c1c0038000c6030403401c0d000c08104468035107a04040b0303200d2146904240100b21002c48403504504070056040580c120384104641031a00c15181c80f00b282001004440c490306030300c0000c003107942042200080460940051052500c20b06906014091903550422030503105e0401400d10300c000400148141030081c00201d00c1c40000055800f00c800c00e107550002042d15101e000b401d0100c40e0800e9130103105408140c14640e4607170003169004440c0140028031070414180201c02e540d61504450f000b54081140c0040d58034194086074805818400c542c1c1042150304d01c0081c00d180c0d0484109501071811000b042800f000c90600200141100010001035851200640e15030045124803509400034a8000c80c2d40f40456050818228202c002e844581101d0781c0c44001061000051070484d032800d4042042c0d60104010103409400201e4074010203141c450f90b01c80907803151 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 835049586 1250 835048336 835048339
    0x3030b09070f3218090c19021f0207140313050a05060c0c06030702160303030c02100b060f0a1407051c030911040921020309030d03060509070305190608010203010501030506030c01080402 82
    0xf80d03100719040e0408040c44003c400070a00c190a01b8048160107454000003080d52243c00304800c0781e46958000655901d0030b110a00010085d07012280d807510080d00411015110f07084020100f0050090030300c0104241d9440b4200b044003242054144890741801d900400d0042504000b140304810000880b0400b0b1745044030342650b20b0303850704002c82c1003001d00080c105032107080da2004810184c0541004101c0f0440d68201c448105e00c0d180d002040e06c40c01da82142d000310040048001d0a66040010613072a401810800b015002c80c16521042e0350000c070060b40e8076002124905403a10000030090844101ea2801740061100ca844000c0b00203140e840311481a65502e60a8042013070306008403286d010603090141308480c1c5030030040d4580d48591382c0701c0d00c680600b0b002e00e44481c0c0207200f0f0100381c40002e0407552840c1d480c40c0c0181c000f094084c0c281c56510b0301c108a0310600f8262400742e5809000e4100c00541c4a502d002c0000d0309441002e004940f003900329812101d000e0b40e00100003076200c2e80 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 835050836 1250 835049586 835049687
    0x1020f03092b051506011b06020a0201021323060301030c05060901120c031b020a050a20100c0201080105040608061b0c03040f0e0105040c051603030b09070f 69
    0x78840300b040003030224102c60448000c1c24036142014024081800f0074031444803075803440fa0740d5404004548041032540700b41d10055040328140045210f81d80580100926030000502d840e5191611001394099984094448680c3e12003a05800f884421215440c00c0240d0703250782194199941d0100c0074405000302d50003050045410881a0b02c11484100c610702d000b1010400d00d811900001c01400160b10810300307000c803a90620202a01c00288500e1150300007001e040c101240342d603020300440c451103107142c5021070703030015840f00ea4030b03442c40419040c00c0752070b0800c4c1c1c02c1d40e520001d40381c2d401c144e01c29807140d0b00e4184200960030b00852010b6001d862629150b01624030001c0030034603801100c9114405110105000c82d100d6481000f0f0030070355032190024002a030303840c4100025103a001d08003d000902c14441d14101003003054a540042d842400c1c003055110341d070710224401078011584000001c0c008808656215041401c90302c659040e03540c200e040116800d1202c48558646081c00c49440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 835052086 1250 835050836 835050859
    0xf0a0309080403020a0b030f012102040f1b0c0c050904030c1115030a02070618050d080705040503030706050a0c091518090905030c1501061b14010f020301090b01020f0309 75
    0x980080b01c014650084c085480030b80c841719040c40503001103c1c81b855140071400080381030314448683c1c4502e2111105a0511051140d00740005014174100d042103403900d51004c0c10030703202440f048055050340350390b907111030f080181002d9401e501d0075800b441c02a100c290038030010941c09886212004e070818020707481c16402c02c01103000028110346521004c0804024014039041607001070560fa070003140140f02c0b5840004d00309507032030318801c0024040c1d4410400040f03a1b502946007a98407011a04101e0708240e61140481e04503880040e0841e00155a02c00300080e445003403259208000c201e1034003d4442d401c010307070982e00d0080b4414410a010400740a01e0384220311404140103442260f03001e1114400e6442c140f5900d4020403101c00c80d5019492001d0031107100c200d1194101d402540c1c40d00038035a01c10941d00203160510100b0f4600c201c000c0952245141c090240b6160720340d41c10301c01079032985008899412070300e41e811708074115080b620650104001c0002aa1000c510880b5014441d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 835053336 1250 835052086 835052093
    0xa0605060f22090c23040905040c0306140a050c0703140c10020706020406020606120604170d1a0f10081b09130f1d030307180503071710020f0a0309 65
    0x100082002142803800c007201c0841d50140039049441c4c00790f580d40719059003a00442c005900724003045182c000100c0c05120030040d200d919049941c00034090300b6208507190b12034403003030169941c0c1c0f11842100110300302800340e00101ca108441e884501078101604103603060381d004041c2c90000f094202c0788280810340040c10030040c008040c1c102d0b0100000c641c0e4010f81d01c1c02101942003071042001600945000643c3c1c0d043c01a00c0c142040d880344082d102c240e80f155180310b0000901003144404500a000c4d42c141d41c2e00382d10641041e090b1924820111841290030841d02503000541180900b40084101c0380903034022441c55082500d011000211401e20498800b032fa0090003031980d440741c00303803000e0b883d203400a50141190251004060220110039001400346201500c800b410301c0d0f00030000a20003910034a0a049240041100518201d6031480020725108094029600c007a50710419444840400c0140c1050111031b10307800d41c10142407440e0055680144035001c01410f80f68860350041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 835054586 1250 835053336 835053367
    0x20304020a1d06210d08010305120406091710090803090607030e150c0d0915060506040b03010b090a08060c040918050d0c06020d0f051e061003150302120d080a0605060f 74
    0x900d460340c4205c403551101030400411120080c80309a8540c000c400c95200b8445d410801c54058031003503103900e18140d15000c25020350642c0c040290446000d0340010142d01d0b00580100d42c2043d00800c5110744034181001c0ca9410491301070005010300d880c0140301001d82c08003140714003044600142d001a69640c80c06071407854491100c00b0458240741400b404100604d0142041d20300340c0c00d03e000c1080640319814840184a01c1c040c1d94202801400104400c0c147d900051030150300c050000c0d0040346e0380f00840c500c1c2078020341c1d640e61031b94004941813101920700d100d440b001c03241d41201c40034184900e03196240c072815003130181c1040060340c0c1d03424001d0107100d40444520744044c0108100344491012400c00600c819202800450214221000c400c0c4880c4180d03401000c3c000c0411400c02054038091700200700a00f219031001d002d816000000d039441d0401e200d03803c1e00060140070901120304004010440c000e0201c040185000d00501180d02c0e008241c0780100b40c100500c699956000041000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 835055836 1250 835054586 835054639
    0xb1302061b071d0c0f09030319080108010b010507020a060503061c2001110c01110705090c130b0315040504060204050d05100f0b0319020a1503020304020a1d06 70
    0x2402500074814100c440700000c260b000c41c0e298403400d000e000102496114a00d5080d590519900c01c01d00481121a8910000703105003000203003180e14202404814240540d8602118404548182c0040092405c03c1c0a049042d25003444c000745044800d60024004003054040c0b8400c01401000040c02901c80d50840b0901001031461140010300603e401407040c1d00d601640a02c982c2c05a400e0b10340c41d401841007141100d9443c0182003108003c0300110b500b00c020120a00803841020070019850716400c0d85540500601c6503001c1e2345180196007580c01907201d522400c1852401c00420051078031112190107916001c03500442c090b1168242900070f03000d190411503000b80d1034400c030400c0020024030703070b204d084003000306004a007410303500d002c21610b1900e501901500290340c0140326000004004548601c000c0002c07464a4481d000d40c803031600d580095101081c1d0000a02c002c3d41b401c1c07104003009144003c1155000440c0c1040c1140620005d0300040c010040003100c50003400c1c0001e1040f0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 835057086 1250 835055836 835055857
    0x7090b030a0c03201c0b0705040f03030201060f06050f03040b19020a0e1206390a02030a0318020f040e0f250801180201080c04080715080f040b130206 66
    0x800140d100c1c1413034480600c01a2210095110003c80d9481ca800c3c4203595410b00040e248030003d124035561580035110300001e00280c10441c0c2040003160072203e4020180c0554000d5000095140c1458821304071101c080e0004e01c180f00043c03000c400341824030001c4070b621550081100049440304446038200d109080f044070304c601d00210340c00340b02079444403541480a4040311082d01d1094250003098032001c1c181c5020021000442e4800c0c001d82250002e045071003010b0707040d000f000c001400080480e8102038104001600000760054900303605025801c8040407070200180340e4215a03000502c3c0821000c0c0c118001c50300c0341c445585040c0144980070715103540d841564210070406800da4040346511600c444130040d00c81c804101d2030740c1485106400c40d4400c043c441e01802c5070300103581010004084040000e030410001c1a1004c0511090300200b85120040301001ca62010203802107200819000c410701401e0300300008a201c0c08862174119141503122003c1d2041400414454450441d801c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 835058336 1250 835057086 835057103
    0x8030f250f140d0801050f06250309061e050d0c02031902061e04170c16080619020c0604022205100e09030a0e010e0f0d211107090b030a 60
    0x40148a40b400b0032001d0410314505461052031010302c10ba0310f0100078007a0b150002c0c0808903540c45401c1c07060040100c034018030104411030f480d0b05030340d0401c060620740480009080741010031840f0b820043c000c3e00c05194000b0f1070b15003080303483d0050860244400c1198001d03103816080c12898004e1003190400000f0310300340700b03c90100d00170107913941320103803280454035010990a00300788003e1000540510303400701400741c1200c5024240d45041c0c005c58620381d400c0c00380751031440c00c4042060300c0c04001e041c1d1101500321450f200ba001201000c0c80d41094031310500410001d040740f580800c0d01a03010342c0c1161201c50368074a00c1038500076202421800340e81d4601e0130b03042c07000101141c01d8400c104e650300e0811321010f40d82c1c50201622030040c08801c802041002407184210343c020319640566a40181514011a1030040082c5068214800966400d4090310320210843e424801c00300c00310f450b500f031208050030308580041e6900400e20680c913031203641d4801d0b210300f580c040c03202c00300b0705810140c1d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 835059586 1250 835058336 835058363
    0x2040e240403051b010b0901120804030b0c1605010c02150105031504051c11010e430e16090501020a140c1011010b09040309030b070207030b0702030a02060108030f25 73
    0x2402e00074403800106d0b07032281e0200310001440021b4000d003520801e90001c1224140751640d912700d032268030044d0a290340c00d8001e2020301d00c3d18003004d1510b81d9440c060800800c2030f01e14400081d06220094001044801e141030051020362000214468400240640d135851035540c0e050035800d03c40000c4101850542082c151060326600100e0781401c414510002c00c8003071f9000100956541058400454060081103001010842030b011b400484442003032034000c08004800302404080242c025118100380c0d5424490401681c0f0850120251030b42021200c8608000011755602504c0d000242945804003015038166410301102c00a440c014145202600c40d21401510340c14000051000c04e40c40d02034090054540b000440f030040385c054079955102c41c1181c0b260070408200400f03200039032052450000c00079404000d000e208059541c013564171854003400c001e08004060b0b0004c1015032091008544a40121040703c00d091841050104040c0c026008900400e4030700708040c1c11038145189 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 835060836 1250 835059586 835059637
    0x818010221060607050c0105030901090606030c03110922082101030308070512011503150e060f010320032701050f06010c03020c010e03010b04061202040e24040305 72
    0x80c100d8002012140d14a5a50005004050151311005003c0794848030900c885940108002d680001110b800490f0850b400c3d2210300942d8800d034012a41c849840c0810814070120301905019101300300d800849a0900c0c42d4001581945e00c402074124025004407030301000f811b1402c4680a228140c0000034074404e010450311960700c24407003a0049208000080c0d070f403a00c22000c03103402404214911000d6403c20b10300c00c1c0030004907461803050580e1003a428401c00d001c4c45040300104029a1140564038101c824000010701e17048246051604004a110040300788503040022020440090380e120b5440d50b074801c0c481804c1c1b807a0071090401c41c00903d002c00701d041d00038a110340c41c009d0a015a68842600441c3c01842c02200034005812010058a656104221081007030350010004281c40300c0000006046410071f07800b01d940d40c1d620400d05021814240120102154503401402400c641a00c181031810311103a081c000c864019000241014064815581c6d0001c1c1c040300090b201a1202 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 835062086 1250 835060836 835060867
    0xa05090a020d23090a0f2339010c020402090a180b0f010804030e01030c030f06120605092d0111190e0a050a09020f0d1b1803020a0608180102 62
    0x610060100f4428001645070140010030070741c001d510003507144000c00113803119130008a400d400000703881e90810b100281080104611804070304110f40340c050010310100030044402101c0c400c00f0140b1858281440720380e03007140e90b05101c0c0d074064034056078480c40c080c00548104d0468115520040e01007000004d41d0409501001c081a020383d1004240914100151200302c01110001c00040c0c40010b003900d294465003001a4000359414040703003c01c00803c0c48015039031103130001d0044030240007000083c060340d030150680000b8170310003800d9121040790401000702034143c540e10300c0c409084141485540b0960240038008032405c0c0d11a11064001d610105e14440f100e1b10500041c03c10710b282140d0300c0c001415500303c0d2402400b122049152103043c0004e5088018013540e02d0034140624080e42c2d41c2401007200401080d83e41d104441e408d003d014109014a500c0502e200200800c1840107880e1459071006481072800c00c000182d46690492840720814001442c1c80c0d400811100003071810704 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 835063336 1250 835062086 835062131
    0x12070b0f0c03010e13031e1101140705070210020c090a06050f09090c040e0a0206120403080109060302030304050108060d06110a0906021902040e0703050f0705040501140a05090a020d 80
    0x1810100c0e45403150048042180000e00403503680141101c040f40e42e040e40040b4400026100741001c10001241c0102840c40107400681d080c08255000307030403900c0722001c0c41403400c000901d030a8081b0600302507000070503901075800002c3c0900c0d65140450015402040358107000080108140c0c400c0c42d1504c280c03000b405561040c40d00451000061700010710f01441d50a10980821b00201880f04043e000c00c4040d040416000382c1a00562a1b0742c0050703291000106000000d00a90312958101031800a1414405901212045203080000c5c001070350003100300e808680092a0480c1161035001c002061003401c404007d0003107290000420034000c01c1009440d400d080c2d0b85840c14400d546103002da840d2b52800c44400b4200c0f5548c88151f0040ca00b5600c80c450b900e40c0c54046460f0940c036940d5541c40c1130000c4542040320f9102010400483c9414002ca0340900700c940600e00c80c840444010031001410b500815205034000030001e4a04032081c3c1c181d800c0075044040030301100c482100c60039400041d6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 835064586 1250 835063336 835063351
    0x5151c080d09031d030a02150f0304050c120a2a08030c011a04060b1c060b0d050412140a03110d060b090319120c050c120c0a0503070f090e12070b 64
    0x703403030092a6004221010340c44d202c1c4080e005d4a00500c10b503082008000440307200300d4242d8014003a02184c440c04402071480f80c0d1289005000d00b40c03040040102c001748103454800030f984a45010750025040080308201ca2000c0e044041018101c1100c034035001c101c41d005200c0c288004140429628015006070940000c18823030780c01c000c600d8209210548040e03000e403a8100380100011ba4801400003041f0007070500d250700004010b9201c01446103070390300c2071b800300162036102c90510080c0a5a58400c6240c86007504100003048046000a4410301601001a040c1580c800008007166030741c001311501c0c155030b4501007259030b03200d100074603142c0c0064002030f000740302d1554880d40c0100a06205444e882d04800c2c0070450054040f412181200c490030708070f4190007a0f41c40c01e901c03030310f603c020203120400c00f00162040540c0c0070144043e440e50740e840248280e1024004000d810700c3e4241e007006607500c4400102e0085008515a440c0000300025005440c4002481c0d0007804209203c01e07008003107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 835065836 1250 835064586 835064597
    0x120601050714060402040f0506010e12030f13090f020307082205070b0a021203060a05090a020d020316030b031605040c090312050c12120f04140109050c1305151c080d0903 75
    0x2241c0300702800c231007080301c4240c00b2814421401d607013490080c030b103a210098040116460705810700341441c401d402845040300718204a0200344401004c0d0700603181b000c407031700f401142145012100103000340b401404221120403819950407411504100340030005820908a40342c0544c3c4040711071b060782c0000003500042c09400c2c0240082000d11044902400700241404829400c05040020402e8080c08441c126a820800e50a4018a50018520034005007103034284d0004842c0010b410364141641d1107100760008081e441011240030f07a0b02d419107100f50780020703c48413200c0c01910700030041d4101404d4126203040741c20310b0b682e11200600801c074001302aa000d95140a45900207406000c0003040929616400a03e500000c000f805500030300071070000c1a11401c07032010a08483d140300c0261181d810084280110b414116410703007000043d054100980e240c000d00700b8112900d42011188240c202c00060004841d42c0490302c00703626000b00016907940511414030340200030b170303440890100c1d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 835067086 1250 835065836 835065851
    0xd110d08010305070b030c0c101d0d080c13030f0f020a0608130303021303061d010c0504030c05060c01110c0c0102100e15071101150302121212060105071406040204 72
    0x620808026040b01da210000b00703005803d115941c881ca400c004c104500050045c004202c41c410200011100c58888000000d2410003500003840800c41d00280b0000640c402020f0550f5190b00411071a484208030a8241d00c0e4048105040d86581203544068060106144060240004d90000c80d4410f072007110b5204149507140810380700310340704a90707508400780200360301e402003802034009080c92104c440180400d10344960b1048100c4003440c112000d030014100d2701a80b0b642d0244954021102c3d41e0170031074207141c60740d502d83d0061a510300a9501429012481c00c4280809402c501c5025524030f40b9507403210b420b40300e02c035542c03100100744500620804003260100141441044540d07110007014007540c2840101c00f40d001040603003640c00700049203400d404114000c1c450a8030100e00707000e442c0700d134a103503004200071382d24400902c40841e00200c09808080c8071030403c5901114032242c034000607507201c0005a465004411307001e000c4c0c0030b508640382103400303010421038410380c0300312010400b51 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 835068336 1250 835067086 835067113
    0x30903070311212808040b0307090e060a210b09061005011e0e0a05090702030d23130c030503030a0603061a1011031903052e260d11 58
    0x490b003142c0300d10526042070400c50481c000c0342e141600344100107601400c5642d0307650f4928140751b00c681e12151a42c10040117012040f41d001401c5002000c4010710282241012000101d9100580c03041800030060318002c04c0c9000302c0d200c035601c41540c0000300c08680d480c00c00340c0c00d1744440303084801600395107681c41d02003465801000b543e440200c810000c98402400c20302e00f558103049030f60090b5444040d001001504d81d4900d00803511808441d0301550300c0b0503596000300103998011014080021108601045c910300c400d142035403184024102124031209c1e1b0800f00703940c080c40d400180030350100004114540300540c00100c1140d10800040003070f42c40a00307800104204600159070b0162120400f15030b44c500c281c4101c0110780e00201603c0c07510042a00303100032801c46058a90100340c40d0b134200b020154031450032039500303640400f8080f20300070004580b40c0d4010041c09072840040380f06040c03140310428003120341a150b4100080314406510900301519070040030103840064442d06481e030491 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 835069586 1250 835068336 835068379
    0xf060807020a08090f0d02130b030d050708180d050709200c060c0c0132100e0610050d020d06180603030806060c0102160f0309140102100e030903070311 67
    0x100b034001501074240f400c4c0d98100038401d03044d0b8490507800250203010402507507034003110181c501d10440000424820a1040c94200300a0400b24024070a05112203008200400211450307086c608a510500f640f0140002c2c14014460b034000d026403088040104120740594008144080c00a80c1100301801440501c0401c2c8100c55441889400c554003103841d0b860014040d013006d410300300000c66550800b103054040d0f210f40c10030b680a41032500e044100803410724402141c100010b4200d0300c140d24100b10b049034480c0c3d000b400290040e44070b0414100841e1085055440c50b8000380015540c03039141180140c0549428010142404800411304030703a0f00c000c1c03080c40104c0b64582c4440301ca80e0b45510070080769400c0701510f10030030b5401b0003d0b4070000e01c800a8090640780700e010381d800c102401d401e000f00401e0094010350070116661948c0340240e0313000200c00300d450000b1540818144610241079040d40600f04205030548240103001c02000040810100108030646128070740d0781c60080c5c4400c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 835070836 1250 835069586 835069603
    0x1203090a0311100f050f011e17100507120e010204140906061b100c030903090311220227060a05070807080d021b010c02060105012006010f06080702 65
    0x400340d00904a000000340502c034501d903159103100550340b556404101c0c64064505140c03c00030f0b60380c1d4420402c00404842c520081c003405070340c0e00c00e80c10132908215000c200c01d83d40c01118000341080101c854080c00030851035540224410382480b81d41010440a41240d085001d4034002c9408c0140825100700c8c1407003980d0445a04048941040c1000001d20481020181c1821740104d000c03c40e0021075407002c5e091301d4400540308000c00c3c001e0102e003007043c116041c450002082509201c040b0010079405449442942c1d004035540f812f0b0b403444030010b15100348890550040c8414207200c00346070703262a800740c4210801001c0303c0302c0c803404642e0922034480400b00d006a01000c203109040340c0501c1507000c1d015540c816034280389008001e03100e00d802a000b248003542c1550300052408641c0c10b40c0c450368401d00b000b040080c0002c5100d0440170b51a5501401071604008a42042d2401901c0440e43c402c0c5542000e4180e4880703586807240307250039220500a01000c1482c0d1400f18001c1480001c4954 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 835071942 1106 835070836 835070851
    0x3050f06040b011a0307030e0a1a011d010e010e09070b03091b19060e01030b0a08070302040c050c0712030e210d17190e0d050c1203 58
    0x8001c608160002c020758140c8401041d1300300400c105890b042105810301184042c12400d41c185030024420b000b81075164005440c1e078545070102c50b1641a01c803081c103003c400070984195603491613020700c030710501c02c0c002400400a0014440c141500069604180c85038aa9511815400c980054543e50b0054012107a541800440800040001841901d8140e10903c2080c1c040340341e07811502c030305000d00a041810b40d41c1603201c0d81c0914248a0000c00d0155265151448540d8403100d5020072030043d880d10800010040c003031016504002d400070f005160650600f081e010009040000403014000940307009125a034070719081360040b901060f010030ba0302406400c1c0e5460201880c002c0014044855001e01c0314444200034a68070480e1078000380c4003425030300c070240001c0521041c0103805020700c516a10880e5403040c020408802c1c00010bc900b40c04c9001041c1c0182d00c030070f40d0301d80e = true := by decide +kernel

theorem cover : BRFrame.Cov 834892086 835071942 := by
  have h0 := BRFrame.cov_init 834892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 834892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 834892086 ≤ n) (h2 : n < 835071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
