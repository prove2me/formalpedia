-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0524
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:15:25.052967+00:00
-- url     : https://prove2.me/submissions/1f84b5e5-204f-43a7-b664-a4cc15fdf0a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 94064748 ≤ n < 94244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 94065998 1250 94064748 94064753
    0xc0b150301150801020c1006050918030f0403061d07050f0d1a0c071202060118050a021b030406020d03050103120c030c060e0606210c060d0b0d0b0a0b030d02121303 72
    0x150b6600800b403402c001030311024405645030418820043c8440001d00d4035030b0500040e40ca080c2c11913042030310807010446002e03840303070301c80c0c41d51203050301e00c40f004c400110b00001000300300d80040c90710088001e015400140010350699440700d040c01055031111211000c41c1c1d00303090081d0103103400e0303000b40350302600d105010566001c0100c040d98108001000011400184602c5948040f040c280a1005140662401c1c103440c58007002c2d0b0548080b40c3d5243c0002c248082043d8054a06030308a20440e1005440311100140c0d480c1c1c024030486000d80141d006c0140041e0003845518100c1f504414400c0c1760b181d5250044a0340100b2150840c20302c0380c1c03c0c07200c00c00f05600b03102e21854034489400400aa0400d01c0800c4400c0800349074403103440300302c421482c4010a003c01c80996510054418984076a8102082c0d0050200c03003840d036410a0348840a034090084044003140196854001045020300c03800a01d51a0fa000322028005680b02440d20801d070074150005040e0f80190100907845130351aa03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 94067248 1250 94065998 94066031
    0x30209090c0d0506010207030b24060307020703060605040209130c050f070c030606050d2604090c03140a0917031b070609050c030c0a050118080106060f0f0c0b150301 73
    0x240c910000070180032960032200c541920600b50854424002081c0c2c491071070744e5030079106000805010721101c640c040740c6840303a0742c1e01c108a10100002c120540740d00c0c081c032000b95550b080313100641b0142e050200001740e5042a00c00c4980d42e120180002c0c00640c1d40e5034001c009008180e62140c10001c08014003003201c0003c5029140603803086104c003845500e1406e02e00c064924a402440c42051300c1e006581c0080c1100d00d000d5170b500c0042800010702d48001d00445d0a502030b0340d009134149400c20644140d0143e0541c02002c040f40c0006100c2101d4440c0458041198918200140206100e1082d01501c04408002d99404401442300011030145290380e01c0080c5c00481c01100c0340ca0b10381003401d04103c0180701540014406170024082c007410440014041c041d24401c15040c0461698102d0340643c0b0800385101402c403c1d002404140c0e17450350000c0030b44a1a000250001e242d12096681040c400e00c0d03403240c3c0d55044100301c40d6945464100b015015150340240d5032540d0303940034501451080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 94068498 1250 94067248 94067251
    0x10204031a060a05010c060c02010603120c0c0b0301030803190209130f1409071712031614030903030708060301020c070609060e0f0604120305070609080912160306020a03020909 78
    0x1903140c0741071014014850908401014148511900e5045002e0100b41d9000c45d18590154102101065407010381c881070340102802e401c0500440808410040d0203034019600c44001c0b481080603140403551004200114002804010240c030780400100f194009920141c21502c544000c1c0145015560800504415500307209241013580f51001121031407940d2043ca214000d000480300d4642c07a1020207a03030cc81209003d01e102b413071080c4082005a0804214640d50034018041056803800c3c1514416501c0307105150140008984a014001c10300444003a41e000b4a4118001d5045846030002074802d01d030000c000355059075003170000344440300040002d00000c0c0103588598148908190000300300b020f8240a00740501c1003003003066101e4030742200f15001c5824041900300d0514161070115a24410071401400c0603007408012024444c101000b42184542190190b01400ca06d07602d140d16008201ca42094000d48410100302180003134008003114505031900502d40030001c4000b8003903030710 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 94069748 1250 94068498 94068503
    0x7030303060320030a020103180602040308070c1a0301090917070c051c08040e04020409050f150a0b010e090403050d0e0601090b091021020d0f02040609060b07020405090f01020403 79
    0x88030714080003402500c210340096050728100c0250b05039450404203a4540700a00d0090400d955105080d40e0b1504201841d18210750207102990b680b6a6828559a02c2d0003034102070361004128040007900c51132500c0f1000300315030f80010107401d40c1c0c0780044110040120036000d03244130013030044540280d1528070080c001c0521411001410f10b04050611400c442402900898251640e06040100384075400341c07421649140c41302c0e051035075180701040c090005140014502d2044900800c081d00000c038204d1070030005401c0d1740d5a81e64402c188a030544180b00341c074034046628001060034a0801c00441ca5009000e420035078540b0040aa00300308641174200100c50719040798005105041142c05040081034080714209524249010384080c031044030710a02d010518160985e420040303001d42c1481c1c029800404a40070000d4600b803010704c1c0c0341c501c3c5080b44a9494109c01050600b041d11550f01031714601000503082106a0b803d00005000140107281188030700e15000d004c4903001d0004101451 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 94070998 1250 94069748 94069751
    0x9090507020a1e210c171b06070e09061804031701120201170c040b0c07080109080315040e060105010e12060903070201022e02070206090a030b090d050711060306030f07030303 77
    0x20f1400c0c0080440c1c02c4c0002448080e40103c0d003001d030300d9440703800f1001c42a0000b441d8514074980c20300c02540c0c1d1141d040c420902804001402250303200104045210740d015031100c1c1b04104080081001d0402e04031242503020320100444e0203c2040d01016541c4584a8148100c01d080300e02e4078890700e520241e100c08840c10902c0020800c5590100c1d00801000b40045805150b003403090102da95800380c5d0184030008c1c2c0000c00c00d500c0040c810800140103226010082080313079400d0400b640380b0703402115200800310000240c40c40341d00f001d02c0707140281c40021001d4130442c0d0801004440000c1d984940d581d02c0001252040c0c0540d50030f002c8030f80600b15400c005e55503803200d840062b0070003c0c1c03060005003c8003c2e000848076480281d00149030b1940b428401640e40141e4400280701d8081d88506035041032030b460300401042000700c00c0300c0c0190020b8045820398440600201d505200d0f0070001005400000321004141c18518041c40c0c0003000142510f00000c0c03007220711440d21400c0d90040d40000d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 94072248 1250 94070998 94071053
    0x91a010b0c0705010e060a0804030c062a05310503100507080606130302100519020604030201060f0f14040e030c011e050610080406020405030a0c031401050709090507020a 75
    0x2a078040202900400d401e00380b4181c50384000c0c0008029000f18500030040c04010800034082500c038011080900f90310040c10041c0480e041c11034500e0010341d00c3c60040303403c05000f43d00081401081590600744101c0f1b980c880c07110580000701c1c205940c00440020013825144041001d40c3c0034442009002c480440008191400312401440000701400b02400f90000b0010b03910004030b4004207809880d0141c5d481183c1d002c19040c211070303a10480a1445040c5500c03003000004030f5010811030700983c0268000d100c5e42c2c0d11400e40704040c000070306c16102000c1701d9590801010420112800508000800010b03070310101c070000a06640c01811100729596582d0002c40039002d084d10b40f030255510280b400c11440c540100070410080c0e4115001051040060000e030800000da01140c0190401800340c81500840345040c1c010500e0714081102c400a1019840ba0315407014400e0600c928410b0b55100da420745065004001088040c001d08110f0044074010404a0781501420707260305818524803009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 94073498 1250 94072248 94072267
    0x2030706050a0b031c02030f0304060c0806030106080c04090602090402030f0124050306010c0204090204151811071401060b07030e1206010b09040216150617060910091a010b 76
    0x85440003000c03142c0c5146403035000381554500040e05400621041c401c2c020807085000242d01d1406041c40f0040218800001c100800c8640d811034100480740c0e444004190310b03001e0400d0309960319809a4260741d40712024440c40d51805800a04130325004160040c50040c88601140a03648100c84010b98082540010060086d507034903018a0000500500741e8041d45558000f0581d21020b06000d04224456a280b8155961540090345580d4014020450460a204c02e0486006507218140b255a144108403110b90114002c43c0500c6c0309045055142500702e55464684628111214010f59030b9058082060441880208050390198460324030200b0510100300d848000a610b186454001c0e000400c901942c02060700d1050a049034056141c0c443c3c0da001a036640d0007508054086800b40340741400100b1294402002d954802080c401002c6000b10284d942e401c099039544040e034002c42e00192644070703039031104000301d100d1410b040060000403641c0092840c00c1e00f00d03901044001510700c65 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 94074748 1250 94073498 94073501
    0x105010503060c0a050409090615141504080a0201110304080303090c0f12070501110f0106090c0206091906020f0921210405040203040f02090a021206010504050d060f180302030706 79
    0xe0180030440b03001c1c44e104c040c01006140f80224440e60500503160300b2060f00704955504070607032840e04036040b0524155a480514500a1644009070141103034000030011606171300101d40a40d807030040140883c5100c1c0d40110780c078807808451600580020b01012842901c240300440c003801401e001000700200c4003003007180821034501c0d850711800001c0702540c042403011a517581180c0007420300f40301e0b803000b050040f81804810306000f0160352038001d0110f1010000d5020380e914141660881d09603a80704c80c00f83d40d8840f24075440202c41c8072020318510005180c0d80041c1030003505480c4540c20014860040780b802428042907200300381c2031410715040000c0400000c1d00c00c00c0d440040305000040391145110a100c0c60003000d01490b00080017a0034800005100c0500e554040c1c03035000300f4540042013000070340000c0402a14058200042079483d803050341035800f0340da00105982032452150751910020500c201e074150344242c03120761905041d14000c0ca0310710f01c540a600603540d1032084e13150100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 94075998 1250 94074748 94074751
    0x106030312020a02060f15041410050d0f060507021005042f06071e05030a090f0e040308070f0c021c030318081b0c09010b0406030e0c24040512010501050306 69
    0x3a01d03510500211030071560001e0100d81100e59070303000032580d4444080e03240c0340a0940342c12a030041d08203071f1021004450080242c0c8150002c2e5003030580e2944640822014030082507001d00b0102601c1e0300c40f804580c1a5101d9030700300005004840c0c084c4048182e4400341d9204031010b6803d2088003102080e40080c40d022880b9100701c0380e000c800d4261000b40045e0040c09060760140c4107400c1130100c440704408283e04460306941160480e070f25140d002c14001e001c4800f50007944042030054800040860060801e80d0013035a250f1031700d80e027969500d002114042818541d442c1048461000800580c403841c0451410800380f10300c03d403d03061141006029200c0b9540514130880e04840000042911130056440b414001c1c03442441040c0251026854a40030000199002c15003000028901c581d0340e005004a541548040c072072400c905500c541c4582c080058a50001008072140790303c100808070100400240184c000c3c141078072200803030203001030300c00807000682d9204c005004a16041044a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 94077248 1250 94075998 94076027
    0x406020f0106081b04140124090303020a0201030b040207060c0203090a051203030c0a180b04050a050105070f020f040228021c0906050901030b06070b040b0c090904081e0c01060303 79
    0x203002d520301d0690525620480a4100c2c4030140403414480f22580c0d80d5045162a80d42c00c60700b40342a0358451105da2541e56144a5015008001b151039a43c0c1d103024850710b0084941580242914003460380055000c0d14011500355440796003080780c10f0000c0c00c94800c88140025640c001c0da12140c00005000d03070341c0c0c0c007904402c1c420b18100d42c81c8841c042001085951001303080c0000d13500d0b1480700d1400e6a1900c00c840c08505122403280700441c50030020400703002201e008035450703a03c2c00d607144010f4801f4400c2020103030002802281c1e52001d8180342d501142c0c98840508018609503c40e1112002c150b07070360400c80c08008082107142c944540c100b18021401444001080034020740800142c03041c0d44a05ca408103005c40814404074683c0039900451903e04003418841d5110203900d00701e081e440c0d08075012940100003001182d200e45075541601d19034180078150450355110394440e15110303004070110f8406007076492404a5614000c2010f8a10400ea41c400070a00030b05601d409055007482c4c82e0310 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 94078498 1250 94077248 94077251
    0x2060a1809022a0a0c180609020f0a030c050408070608040203010506040525090f17070b03090a0807051608030d1109060301050906011e050901080a02070807080a0507020d080406020f01 81
    0x4040c00b540000c4020841030700380d000014071241d06625241031404e0340c1d402800011a0b03c10000300036940c0c4512507920800d40d03a04200302900c80101c00b04a01900c003081802a8040c0136203540b45009920411405105080032818155900d03891880c150f125001503002600040a21045040034040c1c00d03003050301103a007444507181c800716045400c080e805104a00d040c01c1c80042c4015070207100c681000c2d0800883c049091a15012481c60041509090082c0b0f441f514400180b01c1c50084c0641c4c0c0074040070806015291103649900d032190304508000c3d130310750150401d04003a0f4240c054820008140510203035440f00303607100004003101d074038502c00c4888100400c20700f4040e42e142c0d0200e07030640c0d204481402440d00c5000c0125000d100055021156000380503240e41c00c2038000b4060842032038240ea50b0100e030f545501106080c0c0c0640347d402041c070750007409464002043ca070090600040c0c1480c0250074611a80c000403a000d54000c401d40b0b461303400003010311406506215108035003040000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 94079748 1250 94078498 94078507
    0xc0c040212060d1403070f0302150c0301090f060b07050d120b0f04050c090924030705030d0e01020f01060603090605240f0102010f0203040b06270a0c0c02060a180902 73
    0x58108180d0300500b607034414402c0810030700030045001502102e03c00010116a02c40700e81d480c0004210304e40340c006602500c2926403428200750840c600d50f209514a190050859103000c5180340034240c0300d882000c0301078540c0d0000c520480c030700300034150081c001c0c002001c1031625240042c002541c8085502002400e1102400150315014140060031a061b0b5000405940d00031003400c05010700b105c01b55201070050b00f80203c210b10104001200c049a1190088441c6101e003003555a06d141d1040940580209030807441542c002c03406004603903010300545012a402030390440c2143d4040c1c101c800800d41d50b04403201840710910900e544210b040501c07002901c2c03c00907207041c658032102c485100b46018113000d0000d9100303410011400c20396280540d00c90800e482d0925140f841280e145014901e000341c030718080d468010f4000c2654200001080b066202c00b040500034065051401c0700f800340c80141600141c807044010501c8a540e540e07a503800400300801c0f10360070700c003030360010880500601 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 94080998 1250 94079748 94079767
    0x915050708090a0302040f0b04050a060e0612010605120f011104030201050702040f0f02070506060f0306042d0206040e090d11030d0902040b060301030c15050a0c030c030918020c0c0402 81
    0x12191580c1c0c0020001e40c490b510200090103502c2a0781001350080d08102c070040300b4240c15041400820021102804103944100014003281c40030701c0360000b00c41d40007000c031340c0c2410300108030302ea404c14040010038650340302c6002c128440d004421103200c590246681c24141074081c480d1103102c0140b158014034003840c50300001d140c1d001c2c082c800b91040342c0e1200303600040001503101c0c110010035900195241c7ca814100142c6561084a800b8001c180110280d1450300d07010507500e203e6640a50742d10b5103107202200200b020700311140d151001003100c072500c10159039040c000d0001056000c0300741e01c042c03034404aa54100100d0716210010311a690001d9014030001205a90451424020029900c2100d000140160400c0f2038a07030740000d0000004413702c607a07551007000360741a40714101400380b00448102c0f00c6104d032a01c41e000059655041c00c0000c1c0c422208a6080d50107460607203401c1ba11510907840d0286003600c0500740320750000f22f21403034210601c21030380e001300c045070300b14105002103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 94082248 1250 94080998 94081007
    0x6040c09061431090c05040b010503010b0d24150e10140409020f090a06050708040e09100509060618040b010603020c120c030409050108030315040507020c1504060915 73
    0x511410b200740054021900c4800d0200d03103e100070708080056510340c49911040c103000b00410041030310b060b40811800700d5507042074004d10780b801a040e17540f14074584c680119001c90350080c00c00c0b104c082c2d44620b08a54501031151180d440300c2e001501c0c820045280404c25580441d401d0002030070b0041c90380800e1100d5440349101680c9541d98288165910054103040805104036001130802da440400c0c0317003140b11100005090a04410348010b20703180d48948007030b6004d00449000030590202000188803130303034101c3c525a8005100e02c0850b500c40c2d4000940c40241d41049400c50301c3c0341c2c006820403016292942e0b641d202910030a90000141c10181c8500b8000c2e0300c140541000e250700002d070509200c104010009516444603142030326440b1042c00f03562254002d10914000764204000864001d01c0441124002c420507075464205a01c2002480081d100042600043d401030498050240d1196010500b60305901103034166101d08025001d018402140c100c2400c03201d003040d46004030b42c0c20 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 94083498 1250 94082248 94082279
    0x30509120606031b0d14160f1a07082104060c03020a1b0c0803040803090307050f100c08040518160201020a08132d0c060206190b04060503030c06040c0906 68
    0x36400d0013122a040c01c0c0c0441e01c00101c604008000a0403c403000c44162030214082d4600190b101122240310382d100000b0b4840f0a160044500c0c2e0400c2682000ca039803124001810024450540d88d820522401d40c00f4901c603450340c0a0940c51850304040004000c260f22034010b554807142011402c2424500c001080c495004080c0800302e0703a45100d50701030201005000000340000c804603941c0301e4072945650344980011005501a12640c0d001046900c3c01c120000204a07014001c10b1001e04400340c126082e00758040701382c840c002e0401002c42c568490103014801200104241c01060804021003e4424279401e4a1821a44140a208032042c5d000f034440f50000c88000c4003080c2c0661a08040103820405400c120103034028540200c11001d50120803080c490042d1190000700366200010f0742c540d00211160955004a07503165800c00790107502002c0f034180082d0001410359140c1003c030f4a0355100b15160217299001504100c1000030b03440c8044050081d0820a01049240c0050000113840 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 94084748 1250 94083498 94083523
    0xe04050c0912100216110d0317151f0e0409050d05030c090901030f05061602100e0a0b010b04170c03120304030c0b07091a03060a0308130e010303050912060603 70
    0x1201e40d4000d03a02c040803c07108202c02c04107441103544401c50100c420280181941c110b40322500c5d1001c034900d91500301c3d16401c0c000d070140c45e015840ca070082202d002e0180024004d0944070a090700111320340c0c40740500510f2404004260703010340d0440203c043e002c022804804c901c2103051600c0540042d07008111840e4103141d604041c6e4032601e035942a0f248901441c50051f80001b8410000401e0008040c003120009004100381c843e0b54684d20b1803a0030708204a600f040142c0d1000608011104190b400a1082e40304034059a940100301d0380c3e15107107800280d0140c2e401d0701d07000c6001e111811211b045c46a200301c107180204440d04d00c401c0480e4440220f100c004002d0680440002d050501600c51150306c03d9024102c01400d10708540041c3c002c00560081c0c4804a030002151482c40c8032890440b801000020460880d003423855403900041d60040440c82d21841c0c0c0d41a0005e00c402a000e24540614801d48a40791038600c1d03d000d01032420200f9003d1309641e80f00c4014444640c40c00b00c1c1c560010300d07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 94085998 1250 94084748 94084759
    0xa06030504021c05070e070e0307051c0203030304060e06180d0c1a040302060106081608062103030703052202100e03010e0f010506040606170c0705010f0504060b010e04050c09 77
    0x5031a0300001d080c0c03501150048140c695803c06600410001003902c2c0261299244036224648488038100d034040ca003218190780551180d9400d101c41c0c40c00840341c0306a181041d034034010410450340828150b800960b4100e0719991035150b00c5842c1c1405025095211440c2d809164101c9405503120781d40b038030b92005400c1481425200f00d824844a00903820384820b0250a090090406113002507a6030024481d1600090000e0042400b052051614423820096541c6103945130306c0f0b40c6d0030006001c40c1c2d5007415000110000114400c40c80510142d4410043c0d034500060030300c1c00329880ca20040ca1135003c40d01c481d031a110301c800140c0e03a074900c110305c6075002e00e000c800c040b0400020a004041c8801150141c1c840e04620740c0071100d05410061044400b50303001e10115580300416100c01c480c0f0841088005201c03030003d0070b0300321188060302400e4014000030a1092a10f002501103030000d03a400d4403100c0d1202802032055800025240b90f201050318100301501d480708921b03106008440783c00d441030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 94087248 1250 94085998 94086001
    0x20a060302090105091807022b0806030a23060a02041a1e030a02070204060e040206030105130b0d0305030105040e0706200102040302060d0504021002010b220e120d1503020a060305 79
    0x181d10480982c0c0701c010006e0150904810581140358000342c040398440c006203e8510000300481e04d940d0b0201c5c0d0710030032404420401503005001c2c1c90f080070040480c2c1d01032145c0c60004000c00c801d400b0342c00040000031281c40380402c40708461400c0034001044c561b0100d00410081007030410b0110b4041d00b050410300e4540e00e50203180151010130104805170104c480c0003205011031110075600510300785100b01d83c10000d0f2540d540048040740300071134000e907000400b440108010704001140f10000d0656100005845501900143c0e5802c10789070107400091f404070052005003090303c54010b6140c0c0b400c008041092800720b00400e070703501414003201d40000b000c030740300091402501a01c02075a40205101d48030036110060380000c000c121000c0e07124401a211b0308101c3da006201d0b0701d40000707000d46040d12460002c1800071a5202000310241090398980142240c0d1009015a0340700700e8142c00c0490392154071415030415903400c0c000d043c4080c03d00c48020801a0340d18072051085070818103020665 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 94088498 1250 94087248 94087267
    0x4031d0105070b09061504060308030103020405070903050708100c020f0703020105090d06060803030a0b0909060606130b0a02010b090a0606050306040e071707060f1b020405040602041205101404020a060302 90
    0x102d0141020040000300c424041c407004504c086400c0748110700550049003688a0a410030058929511005e00300c14020070042c03003d030500b50031581d80301074941007061810355a5600d04d8540000d540c0a00d8880e04000c10b0840ca02140e4050b540a844507807000348158504001c00716140c0180b480002d0500500184406068540c00301c002c112a070000d90411080f50780701c0031584c880d4821100310100b54074140520402d4580007049031b000d14104030041442e0b82d560380030b2000c035920403240c111781040b225a0000d1b803001c0200007001200c610350700114001d1541014440140c1028201c081600d080010a000c510743c0402503da016904407000b00b4200b40d0b44121600341841170308041500108100780b007070b403114001580011180150b44810900c411164100c9140e00381c8518607002580700305584000d86465002030740c115001d1440140b030969550311000444509400c200d40c80c2e002071341d0420805100f0300c00c090014011200c0c661080c0313040d5000603c0b0301480d0064405042d40418003500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 94089748 1250 94088498 94088507
    0x80a05090c041d031b061602030406120b04091b051e0112060305071d070302030609070c02040e1015050d05030a0503070c020a09060e0a0c0504061101020f070803010509010b0304031d01 81
    0xc6403c0300040d65550320b400800c9060b04018642040c42a21071840800c0792811100707040311900800354042c5061504080702200e2166250761814416529490340b40410354403441044d0483c0e101d21a0011500c09040c4c4803500a662540305900c0b4034041d41c040200840e00d00030341d44c1c84141c00d19129000c00d0440c42458000c198a4101030118407a10300041164284031041400806000346111001e940e1060114140c1c0720450300180c009038078a0200c3c2c081800f48016480d8a4030040010405500e2072040e18500502c90590405543d1259218221003030700f1610a0083c180c1940d00700f02c1d41740c168440b10b641c3d02c101002842000000000103402034443c0000c4d42c2ca4a0b0300905465125a035001d680003d40501c0c0102c0ca05e015141000c90100d060521030003203502031644505003414a0700e00191601c8001c2c0d01102195502080701100e11400c03032009006440c440d010b800d48070b5042c5020310042c104140c0142d1070200080041c800403035080b42007034a01e042c44483d201c2e0251400d100403907 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 94090998 1250 94089748 94089791
    0x60509010c080f0301180203060f0d06020c1219050f030c03180304060f030e0c030604020402130915140105070314030709030204051e06060a081506040b0f03010501080a05090c04 78
    0xa061681c0452074003c481e01c1d003401541251030386500181810001402c010891006680007540110800180c880501b08444079140d808c0c00b4890043c00c0c500324464050400300e100c1c0540b9001040040d070200c400340c082c280400102035620b002401c20040802c5990b8520015007018032400001c80051020f070035200413051405c000c1d4060b42c1d01e8503501c60000d070006e00d58010b080702003030810700307103201401c1c000401e0400d5035001001000552203c1d000d11000394400c40c0e0680300200c080e0004031b01300100f80540d10304940e04401a0b416a485c200010a40090b0880d0310703810060304110803008a03500000c000424036288801c070f681c0b503c809000740c030b059040e0340c8002d420604003006c10414581d581162440d4020b2442154507558984040000e24401d880040d00130490a102241f58444a83e1156040c12001b5060525141e11003c5034015900300c035030410240c00c1c0000050045580c002099500088444000c1c800d030705001d22000d4544000d0341e0024002c95440580c807030051044490344 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 94092248 1250 94090998 94091003
    0x70812060f060a05041d0f0708040303020c0703031101110307050301090c121d011506020a110307170706030e0303070516050c13060609050d0209270105070e0108100b04060509010c 79
    0x2070b5540100c03d00a015a0454031818004008110040d1100d424116015105400d0b034410110719903030702d09042d2001740014000f40e003003550031300141d98450030801c00c40b8040c6000391a0040780f25000008542074401d800fa001c0c058010601c14880030f07603008400c0e603041d10682840030076803004250003240c1003050300c105991070034141514001c050505241038004030305410000e0258404244a007880c404482c812100140d1240180f04080340c0300f000314a9075128002c041d1000e16990383e8140700b8101200c1403404c080d8000343c0003008200e03003502c24094620a8035006c0c40c15480d00d540c5c090054014190240048800f82c00760000f003000620542c0070b0381c10000c0080d46500c66882180300201050700402011865403600840c10b890300ca151941e401740d008080c0b8155903901101e41d40c5142000c0e803a81c480380348440c01903000310700030b006491281d20181c0c0c0d01040085107100040c40305e200500103d809110305003003840051000c10888094614500b042603403480c103c8012180c0c01e03070307e0002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 94093498 1250 94092248 94092259
    0xc050102040902030a0c0c021507110303030a0203190b060d1d0d03020a0908010614040c0c151505120604111207030c090606080907050108070c060f050108060c070812060f 75
    0x2c18403400c03c0d80514014600170b5010080c045a00005990030b2500500c080e5000281106000c030f00705c5210014440a481014a20a88442c02d0302003072864009807840050749801100300071100c140c1d00d0044114101c4101e042c80300194560100d8581d12a0345500d1158a407500b640d0021201c078442e4103440d90081030202e03a122094414014000d4008404500c00510781c01c44c0007524140500078001501c0c02210b003460021807050410002308404a109410302107458060404520600e41c3c420b800c601c036410125110300c0141c02c0746600342003900301d541b06845a1914140d510400280c05520036800712940c415003a03104001000c00140c3c00c8054120300c80c2d030401008111200ca40b00c41101c514007401d0210a4448070284d401c0e15080350814010f0313024413001c0150f5840b40210527004042070418030360460040e250f12040d035400314041c5207200d885200402200d40d0400c00c540c1e2104403010a40d0604c50b40d603407800414803030010700803c07800e814408900703180c3e81c60a041d40c0c100c1c0001c05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 94094748 1250 94093498 94093507
    0x302040c110f0c0a060e011e0e09070e040f090302030a181205160603020a02031918091d120d0b0a050d0b011703040605030613060803130806090c09160c050102 70
    0x140942c1d0f40400502150085521040010b20a4004d400d9190050b4058448003021002c04e8441d11401080c0e001c180304201c0c48050070744480c0c0b20003452078041c00c907a55a03402c4045e92201400251901003402c81c0c4828501441c08010942c003100b6a20303011a1761400a0b80b81c0c0d0940d100c0120980380360803114110f04030326520010084002818465032125800701ca4095584580550482c0640741c071600250b04200308440c8110700707016000441c0200c609041c00026400c01c105038030010b071a0400102c85550b540d91700e0001480303110f80080c1311000300c0146002e254100038001c1a0203201c054803090354481c410442143d580541900150501070180545559103007003c000041007031083d810710465401c4050581240030044405440b01511410b02c0d58a600d001e02c284044050301c40350040d40d0300e00000c00d2045c8148000e010100d180000304460a080c0185141403003405400d00d0255400402d90304843e49030704208c140e00c0141e05000334000b000d40f041c150b42d100c120a800a0a035440000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 94095998 1250 94094748 94094773
    0x30917120406030b040b0f0f13060b030a02090301050f042103020f0304030c0209130f14010b0a08060601120203040b040201030b0613120b0a050f010b090f0a0e070320040302040c11 79
    0x4d00140704520110f60038042a00c040050100e03292000715200d40100084940c5800781c2003840d00c101120b410218001005940c60fa40316505401c291503150a0300c2d0005925074081c40c00340201c0350480e50240b4025020b0a082d5210000d445510000031501e4001059521900740a98191413096081111040c0d403490a1710b001002c0d402034032805c0744250103010104031400c0c40041050036680e40842d502661961540702c4040f03945c0c00140b0009250b40b01e20240f443e54460407030850003800c20200812090410720005001100014141c00e40b00d441841040082041142500d0704960203090010340c000d8050045242e0b4414100c10010040d5400e0b400078010740000507480c0e4a5000d20803e5000341c66080070a0140d50301510002c400004042c0180001c42e40e20f001000d5601000709002410019400403c0d0040459400820b01c18003000c00c00c40d50319003500a008004101c1c00c100407100e4202c030501842405507000180c01141d45800f84402c960003202c02c50201e0350824200c50422a0301d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 94097248 1250 94095998 94096001
    0x100e0102121005030f07210c05120604030e0301091509050102120907030b06060c0303040209062202030a0b03071206182003010e16060c05071d01031101020a03091712040603 76
    0x14441d0074080c4c89411040c8a0110002c00e076482512001c0300401811040b0036003000c03160179247c80a43d591400c000b000641555410480c0f0440c1003010007600a40c40c01781000303802d00c900d82d01c2650090b4107003180354000540300b00d04090340c40a04800007500e610300d400c10a0081c000c0c10a03000c80c0030b036a0010b000c00200300040140443c2d208442000c00da64406040c880503024103180c0151341c1d40144042001450701d50015507201c88060525104140c00d40c91400c40400c840c485825041c1c1d0020910000c20080c0c020030400d40015801040644e00d04420301c60741c5908a180989590395801c544582c03100c0010001000c540c10160103041152049000ca00c09020010706500c258685202190000d030081903801c0c503002e501d00c10003411031410201b9034011041030b00032141030085800100307019a80760401d500025683d0b024100319070541c68480d44006082c0500307030656207c541c8080010303a00800c00400d031150180246504400c0d0920380e4a0403004013031600150101080104400c9d606 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 94098498 1250 94097248 94097281
    0xf0c09080607020304031106090d05011803110d02060708070207230f04050103080415050c010906050702060c040b0406052109100f090807060504020105071a06100f02100e010212 78
    0xe82510030a46401109a035248034900c0000c2c80308150115180c036070700d4010b0180c01c1651015015103104000c0d50380705030840b1040507070100202c0c461120f1106250340b1003244c008034000b81008200c1d8141904000e1b40c0c07400018401c10411140c41d0001b00901c3c0b0a00040c0020409001d582c018000d0b03a90350070b455000710f110210b00440803031490b2070342460315001d41030489420180c00c52078141050f41341c40d06094000b000c202400340c00c204411884009201e41801d0030b018041c0041d840c100004000e00305480070745840c00b110018802403250204a000710342c121244c81c20001c1d95031400d45442c545400314900741340d100940312410400c000c20f003c1020740c00b82504000402c114500000300800300c0da08604041c119502c140400d10008040d580400c2d00140141805410441181d541d04480c1e8407540d1400001000d100c01d0000b20f0608242d101009100f6041c40c081441810074025a681b0703450340b40c000440d071900d400d4441007500b9411500c1d04109107009807083c0c60402600c0c03420409 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 94099748 1250 94098498 94098509
    0x806040506071205100905060613030807050106060f02100b011e030e0d0203070b0a0209060712030906050f010e2a0a0207080c030703050a170d1802030f1903120f0c09 73
    0x281c2c0c01c0b60b070078a10044c80342030310492542108146003803c01e500c40c0000c00004080310340000d010050800210918883c0744025841000c9065444080c1e180050a50750194040c10a001d6103041c04c0300c14a4003c00c070411540790b0450001150440c13100126114a4411000031341901c14803a050002940b41e0865000c01d00848121403d500000a0072a80c034492100301800101500c0d010801c0300000f030b00105004d100003800705082250685581c502d2405200081010960700d6001d042006018000d180c0e202d0030f29100c030f80241d0301d00745c0c64145034080248503c10600c00780052005913080305958440f49545e0008040d01c1d008a40000b030f40d11300d003c1c0140089031041c0c98002d00709180000b0b00c0c0c015264400d01030041c0c00d043d0754a185a04c10a0b98101c207a902c0140000645651144141c03180c00040030041d214040341ca00605080034a8120a0002604142d541c5000c05107400c08003440c2d05d9151030a0b0380400c0400d0401001403046081864100e0308000710514030a901c0324084082c0d91 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 94100998 1250 94099748 94099757
    0x20a090207030c080f0c0c0f060a1101020d06080303010f29030601020a081611041506050a02010e0d0c1511030612030408150403170105030d050a020f010507052208030d0510080604050607 82
    0x3044101700031034010102300d010792216041240c040030318417441040c07206280500003d802d0502104401d02650090740003212150b0000c001000104800c12540d4014400e0038207038000c04080c0c00c1c10706411140d1086200c81c4980010101b007469200f00b02c0608400d42060f201a00c0d001c42400311503000b5031040c000c4e50105e11070140106645803a1041c44007070740d594880ca4101d145060b0b02a100ca4000900c0d01c0d080d5580c88040f25103612050164400d41019a521100e8106640c90402d001390100c40c15403250700d2401c0d40c0e170b00702c000e4034400f22034204604485056000e0203c1c00b038a0f24610940d00700003014002d41800012408240c80d200d40514484d0b04c80e10300446143c080341c0e841450901c10707141c0c5581b001070040341240c003400041c8100b034210b106449620644203425425550305454480028000007106054003040f000c0c0a6030f6006041c00405640c0d02d09082a40e981c0985440858195030728400304034a241c54450350390082019030150f488515007030030419101c890480b505404035 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 94102248 1250 94100998 94101013
    0xf0f1103010b0111060a051e07050d0608010c0c02040203060402070807050c0f0108040309030b060409080a0e0301060911030417120108060a0501060f020a030809120403050a0204060e04020a090207030c080f0c 91
    0x960040412501e00c0c3ca0010050100e82c6d41c82c02003802030315000d4120b01c200b40003803102031082050b6013441d6219401984a0f48d6854194000c4142141d2603644145079a07450507401c1082154882c01850314550111000341e142c0d00c525000170000d100c0d103100100040400540001040001f0544501c0c04d00d00b00c45d410b0103482c0c268019140f01104031801800150003c00500c002214854a80e401c0761000d00000f500308101d40c1c1c2d40803558004403442c00480c1d0461403080302842d0034010300018040844080c845900c102c90104201d0002070002404034200240750303d0403441405c03d81c0d403c000c0700d120112140d40d40d407103500e460340010f07110685c601d4200000420030328095800c1e211803448a0340201645421a20708940c83c0034060106059401241c0884030681c565601901c080c50140c00540a0301d0003510420084400340c6d07103e000c01d50540c50401c80542e4440400404680c041800580c0e1100036140c2224244240200240281d5022403101c080c20254009815200344c1c0c48112143d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 94103498 1250 94102248 94102271
    0x160923030c12030403080309160303200d020c010c02031504030f030b0301060f03030302071515050901080714060a030b030a030c0b06240927040302060109060b07020108040f0f110301 80
    0x303041c42c03400020503ea2082104000042075840151b52190800c1c042d40e141c1d15041c80310310051101640213500081c00d00595000b0782c81a100a1a0041c8450004000c40c140600001c3c0d160030291072110f060000300f14045056460030700040404011242e4800c60f40c0c545890068480803002d00c082d00002c0c90040c5040c0303941014843c402c00d4682c442081800320b0702e5607900f00c02961101034116261040601404042d111034060018184000051a09114140000d10280d070030168490f039620b9102c45c0c03042203100100400d14403407074420380e48955035200400040c4c0152004101c090b8051280050210505030b01c0002040402e2141408500315201e0f03d0803c1100d59449281200e480300702819600e45001c50801003140b01c40242442070181450360312018610032109007400d100107490108820541d0500c81c04d80036100c0c10008000d807605002c0301c1da038203008413040241844015004181409001420105143d130300058041d0650414901401e0511340e02d20364601a6003099400c001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 94104748 1250 94103498 94103509
    0x703030e19031706040e010e21070c0611030c06070c12080601120515090901020d0c0206010e0a1a0303130602070801140f0403030608060403030b0102160e160923030c 73
    0x1003a50543e40d100c00210041c2c40c903400b00c600250240340d0081e036403800d402c2c0c0d6600c00e008039654020010050450350310310110920240004a08480b21100100b060800042202c404001603541c60702c4c01d03113400080c0d4140c640c5036110700f46000e4490f114601c10812180ea11424440c4414850101550042c2400c50b007a40d50309016525107000c64015440300204060590000d6804001c1001824035001c07820003050303050900b0364035a445039400291200042c0850b0250312110300b030701d00c0107100961500c40c2d000314a85002d001c0c0303aa55a261000900c41c0d0082d8001a281000000c040d65a10044040c402e0107904052003000c9c00350050020004a580041c031030107841e8035a280a581d0b255071030000c50400514000c004405140c0d40340d00c0850704000030461030744528400d80300000c1c0c2c94107580000e45050000d10034040340303580b2404180408442407151680041c44407441d11602c00300007105485288c5190001e1102034481220744280030713514941c04000c05000d4041e940259504400e101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 94105998 1250 94104748 94104793
    0x307030501150b04210305130303080411031501060804020303090405010b0c12040501051b0313030b0f0105040612141c03091b05060f0c160f050102060f072705060703030e 75
    0x1c050b0080704100520149030f082c80703117a000d10034503045140c0215150031802000320f0b90401d8000500903010041004025a6110201d0208600421400c0103a0f40d6560030301c24140202000c210951021408544003001038882c00c240040042c404d0790b8440503500fa00d600070a40d500224070800484e40d170481401e4048034140c507010b9480302e01d058514168407011185010810042d44420416001c817031800040c0240a5440b9000703945050070100c0400d42c0c60a07042c1c0000d80b0072031801c0b40404c801604501c190b0901a8002c1c1c200300d00414440d8070600f028105071030150340c4000481052002545039200c90340e043e00c20500f11110355016841c08501140c14002e03a60442c5082081e5404045000302403c1d1a20300c1d14221a1041044004207291440940c040c0d03451050849042c4410f41c0c041c850160700c42c80102c80c0e85e105241c9808024842c44240c05002c2202040143c41420440011401340107040d0141c000f50740c41b00e131460000c004090821070389000d03000d640500e81c4811103658140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 94107248 1250 94105998 94106009
    0x6040c0810120201020307060c0306050109060201020a020a03031d07271503020d14010c092301170a0b300303190216020d05100501120b0a020306040b0307030501150b04 74
    0x821041d8241001000d40068200b000e81c1944030500182d0000746050068040100b11940c02142251070300d80090124500d40c0c0089007036900602001d4502680041c0914900382c01d450042100b56081c40040c0c54600340900091060145800100701d43c00703032241c06a82000001c81c0d502034800004040c04c1190064100040110b5400c84100054509403510960060103000211a80419005d50301d084440c1c0c90011004501c034004100403500d200721440c2c082550304120307400c0c4c100c84280000c0c8ad502c6003040722407010641c08007080c00d8080c42e9005119010010b006441041c042140b141ca107994014155081c0610312003600141401c0031040d00d00075040d484402c80d01801518a01c00650018016030070104010300c1c180c0d02590760900e40c00c1030903004001800410007007110000c2034890503040a0200d4429851500c001040c031001113511044000006807281c45d85c20008024042d5061041c1d894800c1070004414440c0650202c480c22540c0140d0140c005c0d41c07501c00038035501071446030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 94108498 1250 94107248 94107271
    0x50126070c0b04110a09150b0912060114090c0a02030d09031b0609050c0604050907030906090c0b030702010b011b02040b030106030b1608010e04021e0d080408031305060909190204080109030806040c08 88
    0x200070078240c3c0c2d0007401400070014400c07440000003002051804400741e0083798440c0380120b80001c6400c190841d145c10541171800d8514110052502a6072807189107240850f41e551900240241441403103603c00c80860407200c41494203281c2030020103400c103007a050305c00c2c0c0200c02c0350400da490914222000c8035000352a400310340d41c600f00250004c00040100795403844d1660450303800120513401920250402003203458a90074420390007400c4407490101c060510140c940d22041d8104202c4400c000c0a83c115400f0803070b402c4020100b400b4060301e5100a1600901c8814403001310f80c0c54410b1504150555908189680d8490300399084190958002c1d4202070000c000703034a04002c01d0300951030b500c0c014050f5940320034103a0790840b1350b500030b51140616030804103658900d00c400c1c000030700081800700c41d21400d0400103400038400c072101610400c400541c1c18400300c85015990142c500425018001708264001410301811043c001c64580b440b56181548110265015514103409800d581e4034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 94109748 1250 94108498 94108541
    0x50303041a030907090903050a030e06040302100c1b060b011103090612150d0309050102010c180605030910020d0203040317040f030f020a020409110a050126070c0b04110a09 76
    0x421003042da001800485240c0141200496a00b507035014143d5031622a66078141e031914494001001c44a0804448405422003410b21010980c006804002d020b0070003000505031f402c0c200252030361100c040c002c03000881a40c188405101e507036807184401c00401e0300c030010082d0b1050203081c2c80e0310940710711650041c000e1020f542000c000d40c0c441130b8000c120021482c500c0004600242d0b204085400071400a64151818041540e0a02484a00d81c2544c14503d90142801860441040240c02400d00b0840701000044100900f0012402504002c1e02c04650301e01032800c006c00690701c11030b01940410802001862400b14014100d40700c0d680100c007404012060399006c13944140e1124940003144100c01e0a840036a665105241d1900e229100300140b40800109100c6001c41e80d5001e80c0c180b0041280c3c5403009040d105542c0d20514000b28507005a96405c0801c2e6086203031844050413841d0404108000c10086900351701080b80201c404850181d6156482019107142071010ce029200068 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 94110998 1250 94109748 94109789
    0x5030f010923100515040b031602070b040603020a031406030307151508071a03040b040b1009060e0906010906050102120315300601120822060203040f05030304 70
    0x52100350880a0802c0900120103124451401c050080c1c07041c081203505294100040e00c1d1580704003020481048a4500300b034a0000d1100503408010002d01800c0544841000001e1083c0241401360454540023a1a41c0d11180c1c018000e41000340c1d2203003c24608808904483c07010700a04ac1b08900043c020362910801d035030703038007050303501c44049980181d280c9640c098182541d43c031106c081c101c824002c0400d5858400480816509844ca484030304104106010220300300e1240542d009800c510044420f4541d50480c0031b000c1c0890f030008900314078107070020070050042e031a803900800e8031300d041300e10710303600d824400e0104d0704030340304482c05a404101100c6882c410300b400b6507400710700c004403042004080004280200c00c50342c2e90744011202d041c086503101e000c030f0030310034007100b8450000c00140d814200304040c0c00111441c00707082c1c070001140619001912480d21061f044503050f1100b07403e50b5858020303683e50024002d41040b42c2d8101c2c00032800e0305000082c2d40c112607061407118186043e0301c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 94112248 1250 94110998 94111001
    0x60b01030612020112320c072f090a23060a1503090f0b0702070f080613080d0606020c030705010c1104020a091a030a0e01020307090603020a02070305011103010303090605030f0109 79
    0x50b0050241ca41c04407404d0765001c161100c02c40040c00b1b08100030002d80794030a0210050080400100740d04c20700c0310501082c91044018003619024440400c82e0300003c4203012030a40c0016080d901003221410481003c1c0e0302d4104541003400201070070040070b40b0000c100b5009004031081a00000c0040082101401c09100008030101c1d0b8240095045003d498650f180144800d0a544400080040c0181c80c0d40c104980310040c545030182400c031030708284081d038690300302a02040ca006208404242403000070021241c05110f0154104100c95440c000139442d01d2550301c03c503200c1e02a2001c00241d550084415000065001c1590910000d040003040000d402c41f40c0040c2c1000000440414108005040f2a1000b8403044205489103041c00038801a6000c40000001d103034014010300406503040800c1c4801d698403802c0240c0c0b074800c60039040707281c0a80c40d03101408070b6003000d040d0112032840ea0002c40c160380c02036071124040c544a40381a280b910064800071006181c4000401034902c4030f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 94113498 1250 94112248 94112267
    0x601050715051803070605010e01080d052d0d0e010c0302121602070302030708010f05060f0d061a04060b0d050a02070c0303140403080f190206090717010605030601080604060b010306120201 83
    0x140001c580820300c103d4407031443d04500c0c812200282c4d0782005000400c41e003400f060042182500070101c1803c003c00041c40c0340581e00d000d20000e41803561401035182912001f0f10701c10f81081e43c061b02d5048039140e80c00030303000400d000c0000c1d52800c0010000540b0a00031a03070158244e4103003580903110310f001503070081803001c0800c0442c060700d10b0100040c2d60600c0401c0040c066003001098981d4040c00384400c540020b01261302c43c040b41140441c1548480310360101c45130b003152000820490b040d0350022200d03012200c081d0703c18500384003c81d201403000c0140c000360865900800c026915040480124440c800028040f200801010400a031240708142c0300440200f20315030a080d66562a01269040880400e002a8000c546114000244000c2900441080c230050055040c403200054454146000da110b50181b01c0700a040206025045200140405421503a6941e13480c03007086d403250740c140c0c0e040341d0340b506090700a0b04c1d642c460f0044400f59500703001c9640742078043e0341c01560754420 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 94114748 1250 94113498 94113511
    0x9010c0227090601031a2412030f0409060e010321020f06040f0302060601020d050409091407141302030c0a0e0f100f020f062406040e0703060e060105071505 69
    0x8070284100703a021071020310702850141005020550440c503004d000e21841540c0b41c1e210300310070030400c6074400c40d104940404507541505207081c046c5140c0441c04945280025808e06c3c400017541e4002c00c2200001081159052070080049a8640701810307840c0800703110180500c07410342414000d100020710040c20603002070045030f034040b0040701d503d410800100d0f0140e036002444140721060580500020398040b03001d2014001d000085036000e001802540a21244a685c40c8a0b02c0c0801c1121940701168480a804865020f641e40e10144103072a40b030b01c1e110740035107142c000c9180c80503518020340c0d0041145d00103050400010030003c44441900c84c11241e07124030b44060800450f19013180c02030f20340710035030b80d24000359041c0c19019241440c04d5500d0201540810308004004548007011481c100031410460480d101101c00205907000b15009580120310310010303c81c8082c0c05a00040c120b41c1002982c180c030f0750b03801d001911103005441c1c5c080e14040c042c0d4403008483c801944a69804603 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 94115998 1250 94114748 94114789
    0x302030304060e0607060509030d1103070c1211030c060610050408072c0f040605070e0d080304022215050a0305190c260f0604021011031b03090a05030309010c02 71
    0xc0305d41c481e24113032041910141010b401c001040007411000b4013410010f00d102e044860b180d030800040042851000f600058041300740075941c82002d0303200c0c4080b0340c1000904401c490710f451022078156290b500c2507903e18403803101141c1c0c480d440b070b000d2426101240c43c040c0c098411546040f00c1c40303d103080710042c1312013011010380100240700c14030300c1043c0c0a4801c0c3c01609101e49800e203808400c0750805010032061204c1d550204109983d4907072407955007a481141c241d1a51240d2010444c80d91005078504e030000b4103100324140140040e84441800d0980d0200d600c00c03642e4540a114551505000150403a000380749200b0481149010018103948a003000070300941d5205100f00b100302995034a541d164040c0c641d84a00040208220540000c040c00942102d060070f500040313290007100080e5090000f9030010080c0144140309860048941081c56201041c2040ca15a220b50201c03018612804040c0000314550034000140c89600c10182c580040202d026000c00c40c800082c0e408441001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 94117248 1250 94115998 94116007
    0xa050a0e070912060920030d030908070c08160e0c0316120e01020702010806042711040501030c0e090601270209131b02010b0d0b0a0905070605041706010302030304060e06 75
    0x3100c01c4502c15050360b00030303400010710000c285040001c078911801c02286d00e001e030001000560f0750100b0041e590002c40d05002881c0c41d21850301c0d000758001e0308000762440700d4104002850b00c00129040d41b000c9503110410b00555200c003c0c601013204241e8418082a20a10001c1d60f101c4180601c14001005030628003150b07000b607400103050f100018188a596500072500c2c600b1560068a01900200c0c11602800301000c000c0036105080707901c404080c408448030709818180f00c03044000c005144005032051005603141d0901c031028001a10070f24135981908030001d603004c0c001044050503950000030000008100b42c80b4640142416202848070356400c00590000d81d558505507400500609008a001120400e200c1c0010705400815800d41e4140100d882003a594075043c985926400000c1d1019034880b06420310040040400c01801881080d03804180300740c00101520841300c24840c0036130070741503040c055030301d415081c0f10007505540288020701580380100c011860740000503054500f01b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 94118498 1250 94117248 94117259
    0xd0b01110708010c03290402070311010203010906262e050a0e0c0a12020d1505090a0c080d0503010e0406140a0b010f08040b041709060d020405040b0a050a0e0709 71
    0x300311050707000d00b015a44d01e111143c0d007240c040c0a1148802e000b000314000300702010600d90000050083e2140c8110303400101002010b00400064814030600d0008540782d60b1542100001000603005803c03d0400804402c2504481002010325410841c4003406c103000704203403000d01d50701070440914081c0002c2e00700c98514181c2032052a01c1142c10356001700303880c04250080c1d810803405213845401140751312403d010404c00207040940b00395050311065850445800e0402a001282d00c0c0b8084081c102000e2080f0f600002074506041c030701405e0141c032165995110a03030b031000e81c00203c10103c0c3c0d040c0010852310003603461159210f4002c001c04a020706c081c010542d0b040f48202d07040c412640d5200c07a505031950348040408034100041c203148446050a803100c074929040148000c040c1030040070701c6402002401c06031060500090b11080c1c0301c7e0500d001c42d10182d0094044c890149262a6400101d450950141d00440d1009440062401c0c180400c2280580000704200c05010800e10b00194 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 94119748 1250 94118498 94118503
    0x310b01020f0a0f1203090b01060e030a0c0311040b0405070e060706090501110a0306080102031302060d0e030f091c0b0c070f12050307181401180f0b070b0702030309030d0b0111 77
    0x110684500a0400c0e40b4803545402460013107402d4440040510345902c00c000640d034202c0c000d05550f41803c01c0314000c003030000068640b804130071004043e04440300e07002041009c03404000701544000c413424046d201000f07060104451040340d1420009503080121412400c140000b05551409420089005185903c40d5400d54018001700301c5441000508a9500da030700d486503402500510380290f00e1400c01c212034424559504102074481d02000030f142ea00c00e00709a0040400341000001c3e07a44540505040c2c10540d040041d1440c021107460744402072000042c080b042e10036a0200f8101c0441c0c40b18900c0420581010004441c3e05405c0a021808070f01900b058140300071069030b40302d94074a461800204040c0550f02e00c40d001b0303006020240106440d250140700020b0b002e103408004c0b0311031b000c84400490070036407214a42010500740842c2010f0070394001e01c2c036030380a800c4007001c64a4068040341d403448101e0381001c00341c1040c4403414103c5c0c0c9680002001c0d0405140c4141c8800c0300c1d1580c1070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 94120998 1250 94119748 94119763
    0x904020421031b3801151803050d051e0d0207380c0d02070c0305060f010612151503060e1605120603071503050402310b01020f 56
    0x18910034800700d16003059400480d4070050011020415056a51036035200400c04104581215a5241100380410301042c1d0344a02c030b4840d01c440e00b008072542d4032528001c110900300e100a000680015031101300300900d903042c03801c50b07601c80b006100610902004031415000500c0108208a51010304900000d00d0310241c20b07800000e110041ea101c030340d440c16841c2c070407042c503800301444c1c610b0300b001500301c0c6044600c0041c0c0344079500080c070039a500d141e03400303452041d200d42c407a44500c045020401c0c081c002401c0001d51780300c1c07011543c0603202c401000001d202c00b4400c07940052400c03054070480c030607240c00035011203041c2e0340403810690300c2d0b11050003100c0541c901070300000c0d41c400040003070030100302c4683c0c2c004116039203a1001241a9400504c544119800d0003040c000003800318406440400c0b9140040c0b0380b1030006038070382c030706c10754020041c100c1550143e2049200b1000c40c001d141c0c00c102004114240140c0c140040100c01c105840900801111136041d40684903810350f21050912046 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 94122248 1250 94120998 94121039
    0x903030408060a0b0a15030e0304090908031614031501030902060a0309050c090112031b0203060405100b01082202011202030c070204110c032a0706081602010e07050609040204 77
    0x424003882d1200281c07080b1001483c44a1240407041010031551040c01c0c0d86c2c11155401c0c2c5008a10310049050851441c443c03607200745045498515210140304004001d5030040705003139240461b10240f120215071400d1501d903c100312030405c001048001d100b015402032035900605001c5420b007543d800140e01074000d1400c80002ca6290fa8940007088000d100c540015102140c0d40701480d41840051060880300b402e0060502c40601c5541601c2c03011003001c03690056008046072a903107403615115840d005a80c00f80075200d4105040b14200e0760058442d14401c0c6902440c0140492a0004462284007040016414041580c1341105104030900041d0302c503d07404c07031441c1d5492809105020883c0e040810038450410244400102e1840100440380d1070300812044417004090320340d50509101c4480c1d41042c45201c1c14030000350a42e0800f030014800c0314003040d282900ca01b220000e87c00e03103081c965000141c0d0080c2c0400d1140340303040b602414819002030001030800e9140c68802030344a0090418 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 94123498 1250 94122248 94122253
    0x130c0f0e07020c150f1605030414311d0607110c0406030c090504020310231303020703121b050c03060105220c11010903030b0a0801090b19020903030408 67
    0x4021040d030301040a0f0341000310541c0c400c0d402d0552110440032900403450400c01c41c440010b1030011061031100c9840e105034218068958603540c0d1000c200246e14140c801500a01e885c248411904c4103220040141306542e0905020550680640900801851400c98108043c41d40c82410144c420003205104a401e038452000038005000940d25001c442241c00d0f20840c2070840600015044c00b82d6141268117151000ca015100c51000a05000143d402c007082d180c40c0a01c802d90510341501d04170000d000c1101094442d4581c0c804a031b0702ca1a0038100a00543c0c03000c030702000010300107182c607002c02115107040d0000c01141c1d00b0b8204d03c40341e01081038500e54000d5044100c189028021140140000c88040d58a01c00b08030b16802400201650356400d83c3d6107041140d12240115140c6040103010002041400384901d03001d0b0003000701544050181d0000c41022805030014801c4d0041c280e0412209241c0343c0c0c82002030764050350312440b50080681c081c0b0480074551410400f820181115802 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 94124748 1250 94123498 94123501
    0x40327030501051602030403150b090c19030c020a0308060f0310050a0b010516060c030207020603090d020606060324030a0c08030309010c03020a050a052a0f010b04050103020306130c0f0e 82
    0x103101d82980c6001c0c00d02214000100c128040c10b9400004a030101d030f030321050512002c4c501034005002070540504907034000b4204000c010003070300b200f0b005190422081510303000d002002c020880c2280c0a104104015900103c000340c0401c0c000c80e4841c1e80f01d84000d0510600c42c28000c007081c1400f40c010150003182d5120414008009090f0140c49024038081c40c08900300302c406890b914011111685c041d201cae6a130b82401000c901c3c0700f60101d40c080350b0058051650303400d03d12142c0755180e4204000c10014040c0070003058061900908880c02925a498a10304690440400a138075001c0607142550500c281000200040e10b0b04071040c2c000e01c5520302441c2c403031520940080c21344040c40204401c2520410801039055000307010356501c00e100e440d202da1950710012940030b04c1210b001010890421200c0000c420030b00009514905484910013400b10410003030601c800d80d0f40a001c02945600800000340c0780050011003c080d5502030148041318540c2d840680c00710b64000d1300041d050044040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 94125998 1250 94124748 94124753
    0x6060302040f0e0c1503011703040806100303080a0c120f2702010807050309063c01060f110303040201030e031b0703020f010c0c0e090a02060f07031701150804032703 73
    0x6018184017543d1010010414004044c02d903c014012151030a14105100200c880100706450140800d84201c90079414660f0507401d00700e41c00e12046001940c0000000c020045ea03000b401c200034603c0c3c883c0380c80541c002c00c860000d0040f42c4124040c450b9202004c1e00440c080101c0300038149071818000c000740005000040c010382008091105010040041c02030281e000902a070744582511701240102c2150500c050b84078a01c0c080c60100800b504c03080c080403414140303003a4121a45a241c410030744e9852003040d5010030400c41200c3c0c141e003042c800140594001d400950b9010b0185068900e00b26403404a154440501980c1507415032143c1400c1c07007107061800301c9824000d401d01f0100c0382280c450743c40440840c51400f9980709005900049003240354200080301b0501e0340100000d444030035a02e0203d8007504247e400707500240c3c81801851070400c4038044181a1071055105030104804150165942c080c060011010003003186485000080703407140080390740c020520324a000780e2950 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 94127248 1250 94125998 94126003
    0xf050105030105070203030112020402071a0a0510050a12060e150c03071d061608040909110901091104030803040309090f0e0105070503010f0501080402040f02040b0d1503030e040906060302040f0e 86
    0x1850f032420345d1b10070401441541d2410901d140c1855044801580c1e07444c00707261619007064211fa034038403161019018041001c001c1d422081c805c00360910b8000400e070380c44080150f000458484e0814a00801141802050302504144a84000a001c40741d405000044002000c40e00b01c84070382c4645808030030701241d6544080c0130380e00c8800d0b040385800c0b101c1041c40020032a105e04c824020600049540f00e40410980c4007d0700e000306881041008001d909003058040c17900361045891003041a80300220b0b82c00d0852043d200140940000d040c00d00b41150b40d5481070f540040c000344c05002002000084000a80c01002c129182c4803030041100c204031840c4ad801d4800140c092000c0c44002c1c00103000320361081000c02c0c00c483c000d01c1c151803035072103d0004c40d009082090110700c0711400004c010403260150001031031a410690381c100b000b941c0c01d400a441405050100a0002d01c550308000c12625180d0000101ca42c040d0800043e91662580020102c2e1010f04a580c040e946900c421a42c50805 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 94128498 1250 94127248 94127251
    0x130807080405150d05060406050105040b090f12010605040b03030307020d120908070606141f03111c060611030414040507031e1a0d080405301024030204110d0f050105030105 76
    0x187e90038800c16082c04006080c0d8041c50040c8025100d000c2007400e240d0b5140b144a81c01960058804030050344908000f5010b00328602031075000380d0031300c10280d0650800000f201e01c94003656015002d6a082054100c521200031031070b8415050b1a00c80041c0400e541c03c1c02071007000d2061030000340a5213000182c090710f0300c02c14a201d00c6801140e41c40700740b56006010303044280c0058030740022004c00d00404004c1501840c0e200b037019041040150f110350b0003a6200409680c881d448500203040b00480d00c40d503911660060b0802040f402c0900703059428290003168002145080c04103a0110182c43e100d1080404c20b10850007680b0b4a09103201c00c00801c0c0020511001550040341c0c1e800b15481d84501e03882944900da0052054540c104000c1c4039400582582042425104259040b1145215505e949505070030052380c3c9000c02c0700c6000e90100380004451109005484825440c2d42c08010082002c00702941c071004081041d0409062540325010005039401d0000480d94101014035003110070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 94129748 1250 94128498 94128511
    0x304030e0102030c0a060203061504090f0e0604050706230a090e0907030519030c080c0102040905060402070506060d050304080d08040501060f1d061c08090405060405130807080405150d05 82
    0xf040290342d044580210314000d43c9900044050795944079100821200f180e18400a688444003040200700d89690b0b0700141c2600354400c605006955615108988480013034070014001c1e40300303144c208501802520155241c940c1c402d03d9424240e0403c03000040380d4486903864000a580384030070701480f1500a0000e0300483d402c0020203042e415584d4a55480025900e8400940080c3c52a10704240c45800c030004000e502402407a1120a80220325011307400901942d5582d40c01c0000007081400d15109075807003141c106004000c0fa03115101440500f04684400b45c440d80402c000108400e80200864503009076550f46a10742890582031513400c4a03001e810500a00903032003403c008a181c250704450448644020707005c0d107a210350002481b140075040440c000c081000c200d44082c0a00300e03016140f0b40006441c02d12003540c0d040c04100440f041211016070500010400c00301003901100941802031040e1141494540c95800041070a5207800d4054400b000000e900740c5006000d00800c0e41004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 94130998 1250 94129748 94129753
    0x30603070608070c060209130e060f0c360603071d0402190503190903080f15010f0e1201050108160603140105010f051201031506080c0d12091503020304030e0102 71
    0x2d0580c00240388004c0712070040c090036008600f103e2655030342061000b1401216908000c030561240600c2d4450400302c8510000303407110000030f641c40000604881081c0a050001140c20340c110301e1184002210384841e482100012966425603201c16005601442c001c3e103410700d40c2e03803000d404460f64200800304503000d9030050080c040d21102401d400200c6026609001d030700c903610442e58a040d41030481a441084ac2891002401d0541050340c450040349402200b4186984440090898800455081d40020300304103c5a48051003842d4208410400401c020070700c007001c910b52401d4620a8000d943c03140c000d45100d0700140032100c0c8440c014516030409104410620f44000e044440c14881c0d0350600402c841240810b80c0f241048420540640440c01141e507181d05006d00d14000d0440d0300807045103000804903510700005400c64403540024209003030800c460f51111080b94002e0110720500010705404580714281c1c241e0404080110f65005882c4c0c601402d00500a5801365156410354 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 94132248 1250 94130998 94131001
    0x20123011a0f040303080603030c0303010f172109150c06070f1d060306040e0d03090302010f060308181f02060a050f061c0819030204090e06130f0224030603070608 72
    0x440144059400b04d90305403c100d00203540d0400802d04510070800200a10f00000001103284d04151960030181c822100d241190392502c3c0e65a20b41d41e8120b0542070083d4100607080821142c00700000300f4001c5000340500300c6500f500140a62030340c0201300e80e0b60f07a6800980c100061640d018160b1240300d070f02c514004d40030704c3c1080c0e20480c0c3d500c0601c081c0344c0500c200000081d000d45840c5c1000c0c07101050070088540b441c4000324010b004005e1309208500650030115401c4203040c06000b0f803030076a0f80000c141e610300134103106401141032803c9400341d04007003600440300742d000241030140000f001c42c1e0090030491074602ea1407812a40020b12403481c4410100501030f05442d14445008075007440c5403c015040424200541e440c0160403181d00d4016040415840f5642d2607000b5008403412260180074090355540d42c06c0e128034040b1070020140c815140440c01045080b10041000b0740003400c40301e100081c450302800a220001c5024400c042c0000912809003400c00182004040078a08100b45 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 94133498 1250 94132248 94132267
    0x9061813060509010e07020c090732120411030f030a090b040308030a0c09051905010908070501081609120606030b09010c0813140303090616020c030319020123011a 72
    0x10000f060080038603007200c1d60000749415008106c10601361100404031222403800c00c500800060555840c18048555070403000030840c40007902540c0c46881a20040c10584040c04d401c1d04d0380d1004000b03985000c00c10740d40d8030064400380060011504407501a5503038101d0540c000d00010500d920090409000f08020004102ca440c03ea03a00b01401c51340102e5017803440003080300e9119440d003105a005803000094500a11303031407169411600d081c0c0362000119900c5800c607440381c03598411039020541810000d5414903110740c04e03d41a404034105111900e44034440c2080c0c2d000150003c4031015540c480a0041c07090301020340d81e0003840c510080c860350f804918000d143c600c01410024550100d5890341d420404940e80c00d0341e80146031810dc070748038907014100a64403507054900d842134052004550503c2840820b00c0c1074515400b4000758540741614800080c0062864a130354119507841380ea02102103038501d240503550031115494509541082c4040800000c81d8403c0f4401d00c1040005104 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 94134748 1250 94133498 94133509
    0x30405060702010c03030b03070f080d0302190804080d140613230a060e040605150a150f030216030c03020c0a05010e040c17070c1e050a1502090618130605 68
    0x1003250b0a00e49000300030035510742076000d001c0d40c012007036041c014000c0c0482c1640244030004202d03500042210f9004072071803815000ca1160f040740c8200c4140c000d114580c680d00036052190002d2207020514030306013814010078110750890f9400004840710341f0621090b40b8241070f0101003804000d1007000b040c540505c02002010030070380030407620070035140083d047d010b05901460042641916548040c0342c186040e000070070b400c50b6218460000d903c144442c2d030804000078825501080301ea6014184084029100c1490305d0a480081640800006000310a20381c80441c12510071380751940c031480c1070715000e0b0809450700c0c0868041c5103d60320402403a80d01c10a0b06045030000d075400914805001e80c1101e81c1510035490391420344841050212440e8049503851001e0b008004074002010f005012059140b210b01c80900316a100380da0301d0f0007007001266601542c40c0c04080051500192401080d0039401c00f051200358200c14250a401c0c9090269000490ba90006020045581070200064 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 94135998 1250 94134748 94134757
    0xc01060e1008030909060310090c1a03100b0c1e0c0405070e0109090905010e03161202060613020306040605280f03050a031101020d0612120c03022e0f0b030f03040506 73
    0x38451010a400706e020750b207080c45000e02d00400f8000500032a01c26041c0509000801c0c411544040380004255130741005190680c0d008102d4030521040c2c0d20324000041400d6004a00350b00071a0050802030101c0d03100030710701c0c1204078800c400034129803041e0f00100812036a0041680043c04045d5002c240541c1c0d0010340c08056a0010030001160181802d02c80d004004020f1890254131001071104060028894021103a45c410868900c1000c80044102d803a001e01b40c0341250048540101d03514070894580180d0751000c0c2c0640001001562400081c101d54a201e511100c026a1100320b4003030b506070f51110344050502c3c200b850030f0b864615922107907501c0a86a0140030480c03c03680440e90a0300a404840a81003040b04c140402e40d01c401296464079a003810844207564030b00c43c00740c4d10340d0151168107089034240d000b414401c9090080c4500e00741c141500410601104005041d80114922986203144134801e00042e2a180a109144c80c000b00c245800001e60b0040c0010403980e03640d0700846 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 94137248 1250 94135998 94136017
    0x3110f010c020f01050723250302030604030809010b1f02070609180203070909020408010209011b0b0c030c04080a0b0105040606111b04020d0e0c101b0807020d0203030c01060e100803 80
    0x8540ea0001800c0500000d0f02100d0703651302da0061420032060440c8009400440c99941c0c1e8001c88d4002e040d03031444034401c122444000d4040c1c01040000c1c01003401007820542c0804854004110941d0010008092410303080d40041e17904518807245070722503410020640038014908000107010f0070a4144054001d1102c40c0b2040c45400000090701070b8442c60807500100349000c8150344490f01d506469010350008241907001543c0300001d111114210940081416003100041095464030180890582e000414100d1414820800083d480c541040010505c03406056400f04a50400b03040005031141a030000082240710840c43c2d10442c800b080e03014056a1081c40303a181d1081b0380e0003090185c011000c40d10605c0c0c0c070340b00d03c9084c80d80021503270001c40802203902d5255034818482c01c2d51002035000c00003401c241e0403161100041c031024020203070319000620700e805140c0d00e0ba000914550148011161994441300c0030051074242c844940d07000506580090b080c3c50030501d40b150740b8084c02588 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 94138498 1250 94137248 94137257
    0x270302060a0509180105091510140c100204080601050411030c070c0e09030d05060603010b04030803060a030803040f0308061509331315080622020403110f010c020f01 73
    0x107078107880e0040084580f400790242c8211440030482d1500c0740402c009209050050644100048008042601c039001041b0024000d099850140c5401c0311702540407490214581e1080205480010701000003422030102810003581da50b081501040c1851010384c0010300075400c1031005000c40d9064000e40394001240130100b906c40086041000c1128810f40c842c04800781e0101c1403280c0c000000c40180b0710308102d140140038907183c4400f4010144401d03c40c0028011040c4420f01c00034007143c0003503400c00c400400051410351a0740791018250b0055508484651544c0d54a4040681051000d5840b141c102c500034115a540c03001d00050307200301e4840314410035110980c00101c801d040c00c101c0b107840814a0f84001100310462490807039218801c1c000800703101c540d00140d41e1106c04026440c6030055a54464103450349800d0084080380310b141e0709021040009a018005424800b500045020340c42c0d0030f1210550505115141400e0030040d410460800e80e8400545c0b2080103982c0b1202d0203182 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 94139748 1250 94138498 94138507
    0x3030306090212220204020f0a0305060108090c12030c06090706180e01030f02010c050109080a02010b030327062205010e0916140d020313050c030304210c08030307080727030206 78
    0x2601200c94070030b50700086d4130a00c04210282408607075005000d00800300d45082005864040042d22100b40403100c072465544a881c00c004d590501090160f5094500c070b0489081480d0903c0d030f43d0070004120f900f0f881c60343c082e01040103010b501c1070f0312070301502c003000380c80103400e04049a403070340418140006000a10008160303021a44100f50480c20b0b9600701c4020440b417155481d06480c558040040400150b080030105200391402004030381e0040309003030300154140310520100c0c0d90519401d01a561124080c0721900088100405078840c10200811900300141404005002c0b21506000c4c0380c0036064510412110040c541c41c47d14000c101818800b900c45400c0301000716a1050089000a450010091119040051503a0840c0138828420354140803800000d042c0c1e0b90065205009401a29041c4030103900d080c85a0500c6150003100903041c1e240e1100317001440c5520540381c180006101c4020091400d80c00b4814900d1040c040c00301403002002c0070712051060704c06010291240c9030005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 94140998 1250 94139748 94139791
    0x10c0f0203010f1b030606020a2a0303080a06060f0e19050a1202030709020901021b010507080307110d020c010f031d060c040303020c0d0b15030a08031003030306090212 74
    0x104816402640240280402e410241c1494050030030603011014641c40c1d00703805815540a806801c040d5400c5070b0003006014050384418901954402206101304c41007034034003001c8607040f003080003e1402034540301c0250501c4001002211406e41c840e008224841808d00161381e40440c840c4c0c9440f204035644011031010046034407000f0003d42c8665804151800000703a080c0c881604900d8450088040d6005140d54a03200c2060f403113621100b50042e00031000c2c10300580c06c60f49070618111300601d440e6051001c65a12820340707a10a64040d00400d000c0c4055603412401044100d58081c45c80c13000e01940d030390b1000081c1140100a40007428940c80304581c480c01002c459148803c04414000c8612500b0f00404032140b40e4000c1c003041d0018041c619075013046081541a2048150380301c100280d03203a440c80440c81c03a5460b010400d59250160b03a8040011404c00c03005503004a814144050f4800d10314034002c0c0494100e54040b80644d4010300006004640c0030360041d0348901240240007644d5000d6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 94142248 1250 94140998 94141013
    0x307030b060408070806010b070c1502100c030504020910030201080109020a030b030307030503041a0c04120f060f0b010e0d0b130219030309030b06040e0a03121401120308010e090c010c 81
    0x403503415800c8007001c0740000b003801e0b00055410803602880c0c00e40b0005d90700c400e074002d100c0c0b103000741c00790842001e40703010458580c5400d4141d800019a10544813074660f10308401d01510702c11040100002e4544c070a120a514140400b0340d000311180481c410300760304d15400a0b040c00d005200d40b40300158003159080007030303000f5003180111b010004c040d6550342c1254a80030b40a41c1007520113640c0c001500b001d400c144261081100c3c040d510b00c0100a040510f40b0300720301f9100d4034856003212102044194000040c0890040c0d50713904140d403001065050000c40010b2280c0e807840300c0144981e0786c000c0e0f2a008180420505504071801c0c286000304420240003040e001801c0c4d10b001c00c24603803006800030505510007440c0080d0f078030515042600780c4883c82048183c031203105006050b42c100032030a0b00003a01924452100410f801030204114804d601c100d041d29000b6030020f004118031070712000030907500c017000c1409001c003456800c0260800b804482d07981c0c0169503005041c00f25401a0405000d01c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 94143498 1250 94142248 94142261
    0xf12021b03040305061006020607090b31061d01120b03030c03030703020a12060302131508010204030602070611030106080c0f0f0406020a03030605040e0d1b02090103030f02060f06010e0105030703 86
    0x3410860ba81c03a55a407422035600d2008a48484210070200c0300802c0407440800d00368003400407540e510b0a054101101195198800c0c2400e01080c180e00e440901030317280d031304007070030340807600c1034400031010b1030310a016004140c1142c4082203410081080c0805a0b00b040d00110185c5401000082810f04540468078600c1050381c08110380c48007104004c20503515400608e07905a036076030703074201200a420101c02524414000250b00c0701c0c0782003044010800380c0d4040ea44421404901400c0d081e5501c0c080d908a074082d800980d2840e40000e10f400901100d8003c10070240483d445840c51989032510080c020207001e0300407e0211000100c286c07100c50741105813102d8441c5004103079681c56841601030354607100003004034042030030044000342d80c1c07802c1e224200c14407035040d0140c003014040d20170890f070803a102150551b08108002b0054050707110702d85030074040c5109442d0f03802c015201d964042c1c6452401881c9d241c400c003a01d0200070290368401c261522600080c00c01503101c0d00e40740801d602403d04e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 94144748 1250 94143498 94143547
    0x30703060e0a1412030c1303020a2d030c0608090a02040c0305070816080c22260d02030d1a0904030509010909051006050a0215150f010f1202 62
    0x9100e018140c0407004114a46014456103004600d40d482c2007034140c91360000900c04e08400828000102c0d41c0400e5401010415420b070400c803000b5403250300007a40720032144c02c907031440024107050405800704d120648044510500c445201145560b40d0000914541d0090100308030003007022a01c0e52604019074840694028400d22440104541c003e004000848034200055201d50102c2c003007007400260504201616910100e25541d034018410b1a64440c50b0229054000150441403081030302c04990068050301d07891409a00c20f08490310385c1c18110040000064202444e1014034a800104071003a8017138a800c04990660040820a0444181480d480d00800c00808000415138050020007403400c0c00d0700e4800700251505054821907404840807200407540320400d01c946400380003d024004640c0c41103d01c03920034035024201140066403829a0841d442d03600c2c00d81c1d45002c546d0745035001021b28090300000c0842c1c900401c076142c4040b080501e241d0008254200c0d00c840310961800b00b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 94145998 1250 94144748 94144751
    0x1050c0a0f06140114010f14091512060a0819060902040e010b011407020108010e090102070c0b070c090e0c0d08190507050105100302031e1501170f120d0b03070306 72
    0x3221401e080001e07060f51003403580c40c285a20000320307000404d0400742203a0314040c0d45035014440b0b840c00039500480e0041c144031110348107100c071a080e690348a0005101c013541d03002064440e504245081c4078241c01030003161080d012500140552200000c81070300c5642012070418503003400d414014010710800e00040d4129041002c6903862403030541010100400a0780e81c1c2c80303126400221451b107800380d050000d00090513180100315040300f11500c5900031044d81c0c00146000110343c0c030800784c070490350300a810010b400700d03044003030040f40c2c1450401031604032070600460348880d05a680f84d140c007900082c0300302d0401524109002c26a81034a582801c01045090304001d006806402c5030440007084600c3e60900d03000915480c2034807038a6044a60180042846070f404015958600c00314114411261198020510481d010440c0550082808002c0070021a01d4984082c5c00d08a0302c181a68140d800054203030415600174040301d100b200f07401130008148000d4000079060108550024040c0da = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 94147248 1250 94145998 94146023
    0x215071e02060f010608091218040222060804080a1803150f0612020604230907080109050f0606030a02180a03030302120a061206020306010c0f061a1e01050c0a 70
    0x55800242c1980200b071000300a0403c0e0380e0320401110340603401c0b1030401c40c2c0d410001e40310000e10803050250090011003181020300d000e8245c0450304a812408401ca180b05459041e50004040000201c000d0201403600c035906244c90317101d40c0c000e07100d41000541001082030341800c0071002c0c401200059503020444d1207051100c0310948000d42070b206854110140350800008609144192a151555000c2c01d69424289006840040d8075000040c2003d01c2240c1c000803a840d070380e02d4070540d10658403502d5422495042113080d40443e00d005040020210010092144940d2000e040da94040c807000c00250351350403880d00c0c120848164841d1150404200c540200c205900f6070040c1c85020843c503900303801a540d1024500607a01d5900c101c51407026900c080c00e000c140d01d6001940c0c00101810014111310b001e40c0c8a4005034183d4009a4110b0b544001418400e41d581c1c134862000d88040700c44031186850030401a1464a03000310142c180038000591400d20001813040d18811034120b040034070341 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 94148498 1250 94147248 94147307
    0x50a03110c040c0302090f0a0f0302060a1202070605010608070201051b090301020f040909060b1e011803050a03020d020d0e01021c090b03041a06180402040c1407030507020307080d021507 82
    0x1c6c2d00140200e82c8500ca8480d4085e80506003100010300b25440f18450399042c601e10703000c2c800e5641c00501e0b0705003003200181c044c007040030700e9000402c8001e200f03880000f03803507161200050031584081c09580440e410503080c01000c2c0001c0021040504290310308581d91186e6600080c0207104903041c526004a000c500042c002d26103a200051a82c000d03032081c888a24a08104840e044042103030181c011071115103440030b94401d2070500c0d0142066a640c0d110f1a490780c43c0c042c0340c14485c003811801a40f00081caa03180944c1130140307921200c80340c00d01243d40d02405002070744907112812012411801c1c0b42d0052122442518800d00520407020490341c0d904240c10801e809001c108640b00c901614071000c03072001e00b400c0c0341001d542441012415059290b41e0700300030103800030b14584001c00c408101001501c07043e9200900c040c0744240ca41c01d80d680c0d45032040c10705103d82944549084c2d04240d00420603180c01280e0320a8124503442d5000d81691044010ba13048051110340752103102c41e280440c0388 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 94149748 1250 94148498 94148501
    0xf061c06060305060609040c0603090206040504020712030f050610030b130509070f0f0509060d0f0b19050a1a01050d060f06030c020f0a12050a020a02040e010207020108070c050a03110c040c03 84
    0x1e0741c0c040d00641e02c01d0b503103000038091b040c48151402051081000d0b81084028440c0d8840c0e69075620052000745041d41e104001810381e0005802644e07445011408041c0c0b0603098070502116001d004001d0000b4a0704030005010b00707280c0c1d80c01000b0725483d9880354610341d43ea003200c1e045103c5100c00400c181d050018035a55100d041c3e00808100d01c1074054080360522030480394504131000144000150713078803041400b1503403102460889603000030203110000103503d00842442003411419601c85921407a81681c16140058081c100c40d61a14024009000c00134684840e401400c0c200995100200f103801401440c613079000c05a6110140000b041c0b480e899081807620307070b41541c2280c10041525415588500c60b0000042c01c10900868458a1600031006000302c2ca03c1030042d10800d41803900890103030385003d00c041600765400225030045680003a0056041400ba180506a04000303550307103036890001f03840150074000805510071025001308181800f000002d0001d014009c1584030103030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 94150998 1250 94149748 94149761
    0x11091903050f0f2e1b02070e010b0708070515010306020d0e0607020d030c11030408031b060c040504150302030f010606080105010203070b0f090721050709140f061c06 73
    0x100d0500a2204400000d000080c3c0c0b80388040408000d0800d86440303214a1103010494011060405507811001e142c0c00300301e208958825001c00c036030b0114400c5d0403400030700340791060300207940148180d0010f0141c0340d004002d44200d10341c0308120b03943d01c81036810100c1c80e11281098504000701000700210030803100d50050301d16005210301c1800070903814004652112402c40d00a070050f4069074654503114401e8002c08400d40440c106071004244542c80d0b2401c0d540a42c0260321154400202000d0a0004d019101700034481030016000505054141150f580319901c1624411915001c0c59204444034810b604000c5600408481c044403c818403503000e448503105203c007080700c19000150550011041300ea100350301c501318038060754071014808242800a055170440c1d1051020119000281c41c20b4884801065204008007420310720b0a030f8903050458001100042c1444904110700d20b40002c170b0343e00a00c140e0359040069803064046504071072503030840422210315022190620200d0390142c07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 94152248 1250 94150998 94151003
    0x10603031b020603060d06020d090302061b0406080c0c03040b0301030f050f0c030a020d110d0311060604091205030601020a06110a03060b1213140706052205090a11091903 75
    0x10800c200038071042000240640081d40043c2c0c1000010498130700110910441445000c0040c1440308444141c0f08035011032800f100541d00001c107020034421081c480c0c10b00141e100b1000c0c0c4c034140c14480c005000d250050300c1d1040303020000c1200d0320440f00a02c15100905022100d00c0d0722503950f03080925001242c3c1030180c645018218240c5110b1401194040b90880e000c4c0050843c4c041e95801e02c1545074114209a4410341c0744500c08a03155107048403103000c01d0007540c83c0c490160107011010300f003542c05803e640c41b81e8a4500d0110011b8a414040a80c0c0b00e01d40c184151030350b445000507420f051610038018101450400b9070341c0b204803020701074038070549183d5040000e280c442030941c50034820004180c1030700d10441d00256a82e018504480d120b28800c0760b8603c08081c4d8081c035107203405a2034010700080340e40441d20040e00c1404001600758100c40c0c01221100038070b41004681d1121000d440761001e913460342203410324031003000200d8102a202030005030b078107090f1803141031084d140c1c0d0204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 94153498 1250 94152248 94152257
    0xf110405040b01030e061503010b0a060315061b0f080903070303120c0216030809030f01051314060f0406020315060d02040608010b040e01061b06020a0201150f1d090a0f0501060303 79
    0x1052554484d1080002c3d41d41210f00030000c1d074a90322005007c01e42032101a0358551b41b60130740c1070450303211140c030000104519203000c01e1112040943c1c40030100160040c008000d1000c01950545080c0102e480031143c000840f2100400c1038203200105124401c140c6404d071050940020030182d0002c000a07208210039801c2154285428049807602d0320035403014002e203030b80380c01480403400c580c000b040001c4004084469443d5000c81c2c450942e4011101c1c840350fa086010140301b4000a2403840320030605000280100745090180a461080060400f50989a020001a204602c040b00a21030414024012921624070202401c00ba601034002c00001a0054000203904614941980c040da058075525154903030034990308695201c16180c142000c441c813071102c1c0c80441c5403480202610f2505500104003400c0d0284581c0c01503480e1341c40140640101c7c0000c00c003c007441d10b003519098130155842611500d40041d19440e00101d424080c207020045041e0300c04002c815408002128460340343c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 94154748 1250 94153498 94153511
    0x120a020a1505030a110c06010b1305040504020117100b070c08010e0a15090303020f0f0702041a060405010c0f06060602030c0d0e0108060409020a0b030a091a010305070b07060f11040504 81
    0x2030a01c4440141d81c1d40101d8070030f002003004803200780c004c104100da281c41802d0420f0008a82146401c0007a0310071001d190000a40541c45c440300020130b8040d043c165000e10090820350700082503800c51941c0781518490381404244540d5528001c000200004036000b0f07114101800c10100002c4a8451003d01d9072911a945000600200e8180e4006400100c0c07030100721903200400740a00b02c5464205c017015401c00060406460401c003403c001840700503042d880388018814001240c40640d1382c40900e40c1401000d0301242e540c5011034007951000c0c6024000c000b0701c0c0c41d00c403411010717210000380380c00d0400d42e0104040f540000540240e510610841e2103000c400c0c0c400303840e04400c00c1c0c3c0103400104070a00051581c20b10ba0400070340e00384090044103c840d40c5030702c943d500d500203031285402962030709084002e21140242d9040c904482508044031940340d540d640f5543c61562007050380c42d0724080340300014840254040718104500e540180039000300e00c1e031403d0f03465125000745880b651400c407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 94155998 1250 94154748 94154759
    0x60b0a08010e150106020606150d050a020403060c031a0f0f0402030403022d07060806210705010e0108220f0804060201051009050403200c03010f020301050103110c030313030905120a020a 82
    0x2040f00f412943d194002e4111a180c04050210040c110740d009010003104100d200d40c491000e204080c800c017008100181c5950641c90b01c2c00c19200200d034020201818a025103803d0a00701c220103200041c04c680701c1d1451482d0501088144c0e10291000354000e201008100600d6008202c480102013648040e1580711140d00e802c0f120301030080e0704401c40340d00c0300c01c0501480740501e00c86078100700018015400e001d826000c1c484c00034041c000c1e85400b0380100c00208a5941c101e0900c2150000034280190f451404049184102c01e49464400c1c41c60b4400c03640c50184110301844024181e0404541d179070b078688424001e8081e21060710300301810640100700142330105486958050380e03041d562041d00ba11100d0310801c4140003007410b51054000c520b06040b40303aa0034030880390511101c000240c0c8039854080007504481044441c0703591480200060704c0e0061f404811aa0b01c085513200c0c01c0007440c202c1c24201d9a05510b03412640d0001081c031407002c0043c000140703170142c2a01c2143c520140d0303903d51 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 94157248 1250 94155998 94156033
    0x20405061509043603180503030708090105120108010902030c010807020618030f120603011d0703120e0901030305030f070905011d030a05031201090b0a03020d0204020304060b0a08010e 81
    0x7544080e00c4901d06000c00aa07501d0260011500c2c8080f0301c05080400494580c3e210b251005a001c07186224409186041019008030020703000300c442c0395010f01ca161a11011a459100300c100c010208400000c0c90002a8021015103800027454044080e8070360b12105154000e1500d498142d101b4851208c4504a941c414004d50b84103160a40c05000951070310b84e002190035080411183c443e00040c01500c890305406405080781c080c1d15900c19100307090010925086a0100c1c100c1282c85400c0c200307540c03203180001061b03070840743d00540108101d000c0c400c04441d1802082c1905a12101d00800002410740c0b240296029110030710390a180b03520303100c4066030f03413440c9481114049020712401c44003074802241200fa888001400345e6079110400d981d0141968414038070b0402801640005000f208114071540c1d40c00c00e800e4801c02e070058210380000e2840002144001d201d503800000060411500c1d402c211f05001001d8840409191030f000c84502900207503003c56610301c103c55121001e50185c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 94158498 1250 94157248 94157269
    0x901050601090302190801020f0702040e030301050a18020403020a0e04050c1f0c0f0b041b0801060e0c2a06010611070b0904020723030a030c022a010e130902040506 72
    0x58560a110610799401e000f2003a03000000420751004a82c4001070307030380e02030005202c9c21891400c4a0743d100001d104000440744660304020303440d44144014010340e01c0e00c60760041943c107403451024511400000c110081d114941000390002808a0001481c400c40d0f0b00c2d143c059449881510a0a2104028400480d0185081424681c41c0c400340d03007241801800d01c560584e0090140c410110040d45440c5c08a080540d022100380102100300c0d1001200444840084c00005d0024410585041c88013441444040e1901021040004a1403203204c00d1101003007152958500b00320030b45080d0b1290a0710741d40c091040c9000325012100e19040030002003490410f80c1d02c281030a5080ca041d080600001303401080c811100c02c0c0860741c4080e0340da044041c0c0c1004009010000f1695900304c1800102907662820104041d54889203805004c10032012405080040b216506d41080304020300403188601311008007a00315818503d110401d04050308001100c40c029941800580c840d403042c45840f145 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 94159748 1250 94158498 94158511
    0x30106090e1b09010c0f0503031501050c03090103051e10080105070504080304090b0f0d0507090b01030207020f01080a021314030d0807081b04050a0902030a050f0903070f05100c1205090105 83
    0x14040d00d5804202e1000900745551041c9440208140d8030b0b50b070903103201800c000568181d4004006c210ba11040ba6000d0311b6201c0c42843c0450803e03c4c200c0c01641e4900403c92200d041c55250f40004000d00f80e070034420541300c090303030400503010304001340c0611181c007680c018820154207040008445030301807070403141154801002146031030718001d02d4400604414600a07032180350700d10740341010b5940000384105a4000d40c0500181460040e01200f1541a5114141854014010034015988020480300c8445080c01c20401503580d441c0030700000e00c510580f04449546600000c2a5801420342d1405480c609804aa10160154900355030282007107800e180041c009900080b0300c5410124083c01c0c0d814841c440c01d05158031040060780210280c0c22105078964003008000c0c02142d207026480e00851100e540c8491030030003041c0240c503449844030190a40c2003074601841089010070228a5a02850b101003085440703142d4001e00a402200d040140c0c0b5042801040d1622810310510b8000c01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 94160998 1250 94159748 94159771
    0x807050f070b09030408030a0f020d030b060307030c030b04020a020a030e090f010b0c0a0f0b040620040b250b01030b0c03070f0f121401080d090e13140304080102030106090e 76
    0x41c0a40d6400840d690081281d002d80c0400d00001844030020006404580b03059107403030640c2a19110700a00d0002d01d148144105414000f19032019202d000c2142d030400d0280c40e000c100f00c400e21900b5400b920300f0020047d04a440025419403441d400320b02104014400d03503604504010350401c01c10110800d9a10010100c800c800400031848c02d080200060446c660680340304251544400740308202d803542c00c1c1e6225041d40f0400041113032510a00341f44202c0d80c81c1e07001d5a5004480c801c681802a802807480e00f007000990425000c13842c81c0030f000d00d51072241d81e040f9000410715100d41d008200303200c110b501c130390075102142101d034850042d20b200d005965600110400601c804032500199482450280118001a002485850301520189064240d0040c0f6203500d090525890140d2581c908010410035810611031035980c2c0341c00942114082c0f200038504191401c000b601c10a0b60804121179110000300020540c6cac1c1034001c0d6048400a84551040d5a5510000072424104461558601 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 94162248 1250 94160998 94161007
    0x6090b031b0d0503040b030601030e0307030207050613091a0906180613090516050f040902010801090e03040e041109240409050102090d0804030c09090b01031e02100c030807050f 78
    0xe10701c00704030320624500101040981d089070340f140b42c1142d001b5040329805060000800065507014054003000b0f02d14800114030300089a24000c2d11a4103d0080e1031080c0340000f010600c1000c046511f00150004110402900d51100c0013120300c0d26001c81e016004101020000b401d42c5407950610142801c401d80c1d0b240b151f5aa4800c1004d200019140c03841d8084d51050140007140c0d04010b50104641031001040c82c072800d05c07042010180718001043d100f20309044030100180d900a0b696030440b0041e80c80825015200d214082c19801130790419180f60440310704000070b120b009a001410b01405482c145a1610f452810f02c80c110b03420626007200c43c0500c02000c0090615034003d40c1300a0060300014101100080080e894480c850340598502c0004902032040c0501040d024009001c43d82c2e0800c114105980c031b00c100508144809030500c2140342c44000303070f000110100d41d1410b0b03004103801c1c0c004601c03100190500000750070541c002020310300010382250003501120056030113100d40380e061 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 94163498 1250 94162248 94162273
    0x6010e03060109050a110304050a02011e0e04020702032b030e0115270501120b310f1506030b060a0501050d020901170406020415020616080c12010b03010906090b03 72
    0xd0500070b0510405e2a039038000c003002180005001c0c6000754410b2010f44a4100c0304d0000400000c3e8141d400b0706150503c0f000501d000d6003089a0302c21901040c3c40c007584880107400001c1c00d0400c3c00d400c4001c018041d03080880b982c06200340900c0441c10580b020070001c04080b005c1400c907854494112400143c03c201801a00c43c01c03011502d0785404c0f280380200040203c00300c04c065620030b03800801c07850b0b80c0080d030b1000c0002c02012103600a12000a90070ba10100c1044449a8615919442c1c000340c80c0d000403006100480010040f455000703044008810208200d41c00141014441a510503d8000c0400c0e890b161481c1002c0494105940380703400e000b08065118002d60200b00c96505010004c91404c07405924900c804c0d21483c05290b0050300c0718a0103400340071101d1090320000454008804100c07450804400031044a0034a140401d6070707a0310405000309510034450400001540c0500014500503e07900540c142c543c021014008950b9a05444050b12054802c0941c03641281c21100340 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 94164748 1250 94163498 94163501
    0x100c090f051507060209100f0e01020f0703110a0b030c0d0f0207050a060b040b03060405010b040c11120a05040b03090f0c15070210030204150504080106150c11040e010c05030a0506010e03060109 85
    0x41c013800744400514240b504400900d1010030344003000045200418641a065003101841c3c0c0c03092001e00107000404903555aa0361a11154003000f40800561802642e03a80c495002c1e040c0070701340803540d0340c1d41e03030900384181c02054000c1308401500f2800c08080f400500e40034001d40fa080c0b5844001845440c000c0c0d62848043e00c6c01c0140749800aa03900c204841540d402c00c4841c0c040ea010f1030000030150884000d0000791201000424240900069040c08541000441c01c018541401c491503c420f00300c078044441f445503a0080c0480c02e004814030034207000200e0110442d454a008503030b1914641024000c82048082440780700b090700388040c2015081413180c06600903160702c2c0051030725072030303410000100800e050107800044000c01c06203c0074070309110b4500035201014948648001c04c00c001441043c20ba800100b40c86405030150b80240c07515040460f080c14100c0007800385c84242c440040440c2c000701e81c0f2880c10f90515001c50044c2d409540584034140010f0301a200e103a007000d44000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 94165998 1250 94164748 94164757
    0xb030c10080708071803030806090f0c03160201090606062006130323220b07081603030902220b060310060503040309050d0812090105151011100c090f0515 68
    0x24140691121404615148452403c0286d8426201d0000d1400e0400a0041c80ca0000306400010b01d0402c00b032101054054066039404484030700740c15400c0d170b02e10b40120301404852000034201420310501283c0030f43c211003802e164504201003e601d80300c100b20020b903a42c1040e1540c80c00741d502a0b10003c04640b00d40001c110921103407400a10302e0070b941000b44180e520000c0284040d60025100d03207c1300c143c41c6d906000504504800d1800c1c4950f6484002062043c109400b0511030036420103020140281c001c4003c0d84c1c0c000345040c03203800d00204040a81c440c03e1024419483c075008540e011441c150041d46e015091170720424018a05010050b5004d42c80500280e042c420f00303440005265482c00c0914a10300d1181210940300c00240c0344030303a10403801034844103889e4181020000f0003603450f070401d00c0040c000c658001c402c88a4010a0b01d50090340302201c0c0140c066405000030303603103454001c050003141946d80c03404c81c5580e400c4608140511401469805200c1d00c3ca41000079400c2c00142 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 94167248 1250 94165998 94166011
    0x24030106033f020115151d03010902030d081503070e07080c0f0708090909060403080a021b0a0b01031a070203040317043303060305030d0c03150305010b030c10080708 73
    0x2074000c0c1107554403030084020110300580141c5d122030710844003002401441c00100b50b594003984140310255409040c142c22900c84850501c0c0c10740318803186503800d4000d884100d4001e0f054880d072030007034030700202005011114195842100c906200c01c138200000c0020884140040904464841c0c8004580540c4050a590740408091100f08800c01c004402408aa403251180995540c030780380900040c000f00802d0400260000c030f08002c04a5000091030390b02c41c0f280c00c0010707a102500d078030b541110481060031542c50311a00c41240d080220002c0c0c80360680740109018924000c070411040315a0f178080b1410700040e0002d000410000300e0642500210302d44811040f4180742d1074654040400c602086001013000781c014000304890118519211000c09518061020f14103503220140d884c0f20301c8580d1244d01d175542a903000380c18401e6100c21514090f0083d1200301c2d5549003407045c00390181f11440c61103402001e004100a180140c0000c8a180403911201600e80d81d20a05030b41042005201 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 94168498 1250 94167248 94167323
    0x50321090409021e1509030a060b030708161a0c031b0a0b07050703080f0c04060e040b06040b0d06050402250c0b03090d08010504020c030405060708040306052403010603 74
    0x25001a070b00e0b005203030401c070a51000d02015002c4c403410412440202072400815001c200902020b60300c001ca1a0074000ba000540410100d0866012030702c3c0210540c4aa0724a0052020840c00b0354500080e140c126106008444111036122107808042e10071940440c47c0ea50003002181c0401e80b884140c0d002503841e041c1541e070170070540d444070882c08108640240000c3c01c0000e00c0010150415805500403282d061050b6403854a140031034514400c9000e445c007481050750030000c4c6a41c8582140f000da203006401c0035110ba543c0e40146030309420540000c41c102e8200b00c00491181481d01c00d41d03404a031007160311142028008401c80c5e500d0035000e8144c1d030007058003c0120302e00c0012401036010300900c1c002044d4500c50441d00405902042e00a0b07480341e40104140541d84e607001082c0c030300b074500c22641d41b47e481d5460301c0d0604640c4125400240f0460400040040c4a08001d44607101c01f0240000d0090001c03200707080508944179404010200c04001138100d000820f08103207407010b102c03514032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 94169748 1250 94168498 94168511
    0x103170403061802010f020a03050a1808010c020a020901060806090112140d0f20120307021e1605040b090411060c06180d020609150703020403060911010305010503210904 75
    0x200e02003510f0450070400300b0014a0401802196407002d5003000312045440580940c50043d41e0050003441031122010802003c2c816222451940c04451030050000350b00803c14040481d0019440740c0c0080d07000d901c0f4190040001540c1c03070040d04018442c0030018200ca106a08100c600c0c1041d0036000c02c00d441c4542c0c514254940c2910422a181095509898a494240004070020802c4403000074000a4100c503007608031039001d000a0304030569000d284280d480350f0f0362100c22071800c82001c0100d000c0101598072008080400704603804620420303064120a0f035183c1e0107020648a12002c043d030402000c2c00080c01080340401c82c04800746005280cd458101e500b9981490300700140d40e8640c0310b51700e001e0b00102d005010001186108143d001400785844d0003403400c5d4944500d03602c02e5401451010026200e244a64101d4025591080b010840d80081d41844990402c00902c0d050100749040300210301880c0000e140d0044c0b82d0a4284140c40b801c049102c503c1030f070425034402d0b0300aa11940e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 94170998 1250 94169748 94169753
    0x301020a080406060803090d060b030f0a0303020c070e0105031b03010b1203040801200a0e011809050a1d0a031b020a0e040b06240c070e0c07020f030102120103170403 73
    0x18000c106055641400e14100340c288202128042d40c001c80306179104019100a0741c41d0f2400c0203815a401420010304081c0740380200f400e142c903103105e8070040e000d51030b078000426825501400807584100102c5000d1a2200c101d504001c500380106a819801020a03034040e01070b0144c0c0c1c243c0c4540250000c2807031b50b1850046160404130707486076205504003203818445030b8024812411001404140401c0140040c002074045200f004085001c210085250741402d90080c1c40c004d0f84118401040c040203590340f40c912000742000c0c0c60b200d0300b190400b0f2944200521481c11402030381c090001400341001c50f6078040c1d0f10486032880c2d0325030780b075103440032003015a40b0080700d40c000780344135824540185003514004070241e80c01000640305c0e00703403040e13201607d41144400e0106204441d842076503803015068003a2411080f03610401e58000306008201480c5c541c040940b650b14425211801403800041c201400d0703008800780810b41e00924001000410721030b50fa00e0303c20790040714005207130179240d8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 94172248 1250 94170998 94171001
    0x509070e0402130302090a0212041209030209040f0b06030c030d1b0804081f020310030b0a2418060e070507150e0c0a090b01020a17041205070503010509031606020a0c020301 76
    0x104004460070080c10030030541c00d20460071580440b0040e003c514200c50a84240c465049c09400a400c213402c0440b41d407107aa002e1130850010350b400404c0f200003880c0508d000301a101d102042169918201341c0800c141d03043c0001c0c21400b280004000d08074240c0d0784d8030215000d01180b50584081c080701c070003e50220703201e40020000b400303041d0701600340e4078680a8401400d4030720441041c6094410820005694115902c0c4001d40758132240000c455100e281c0c0084c0a0025594040703451248488210900110030f58140f04480054010284400b5415012000c4469034440c503110b850003003000602c0303035109400415865109001e0854608035803055001128014000e10f21264488104529103240492003d8001e1481500510001c280040002d44451000c0307001081c0104040b02e540380d0349041000c1d030300500198000c3d80d1402e183c0381001d951b140390303d101d1035000c1e5107000e0100d03001140c0482280d0302c0c1c40c1d00c04400080d08c141561004001c2d401000843e08005031203071700c1401070707800b03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 94173498 1250 94172248 94172257
    0x106050a030602040801060b04060e0906060f0c0c100201140f0417030103080405090a270201030b030d02010203010e0a06230d0606080604020109060801080703081b071e0e010f0509070e0402 83
    0x2d01c0005032901d090815450869040760069218034034203201c104120341c0c2c891800008101b05030f038540207580700e2101141d118002c060101003c00f8021915480130180001e080e1021142240c0e1078081c840e050f902a0708a44400705070209030b1542c1d0000a07040008074a03082c1c0c1151007440030044881130a00c03228500d800a80045900c010000b07020051450701080c03a80e0442c04e500b20030054038961241624507036020821059200c0c1300110b030f01301903a0281c1d016004840020341590010450184000d000758030900958100301d0b03405010414040c027612502041e0f514203004001045d1a0086001407260416403c503270011a482a007000902103005400080c0614070051a0070b0030030b880003421209d0143c0014041103602401001501c00001e080c008413900300d010540c0c1c0c1c20400c4024280320140452100c003134400c100c4006807145d03a81c00350404824071a09480c18250326003041d0030041200784911410a920110148074900d4002000c0c1d0300000103043c030b00511850080840e060303030403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 94174748 1250 94173498 94173503
    0x51b15040c030b2203030b030708030a030204050127030b04081c0e0f06070f2105040b070914011d060702031209040c05040f0902070f05060c1e0304050a030e030106050a03 75
    0x1c04030082040100509000d90058850802c0d0701400c0103038014484124000314028041540703400342d02d1003685092094402030224a0140c03550740f1501a0098080c4d40300c0c0c03089a0000e8100c10340e0381c04a100a5804190214260004070290b030700e580c68200004002900136100a041044000c01c0144c051303071807044504440c1004603651000b03507074031410021071403d0241150000410030032059408913104041c840c42d41440403000340020f80400840c001040d8009405142000707120a0041c96600d15104507080c3e62404055130329000710f000c042c0e45903c80c05000c59001d41c0701d640c0a010301c6400b405500005011a42060342c0c0d600041d03e400d258074046501d0810001c0c404446082500038020090000e003040c524103450f0280a000700441d42c440d003000340f81e02103448420400414070718444035420508030b500c2805c2008420350030303a0084205501c0a0310110144211000b18001e07241302c0c80d08040075220f6400c45840954040030309002455041d5a0360602245594460b660305d0082c60 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 94175998 1250 94174748 94174763
    0xc150706091b0801050703060501050304030e0913020a030b0603332806051507020f0609060403080f0324010518040f020a020f0601050a050918070f0b0a080a0c051b1504 74
    0x18400409070452380c41c0c0d04103c1c1004020010080403035040b44000c1074644c4241c4910702130340d4401c06105003004000000a40c00808480300000b07110080180a00403403003242030701d03401c0d140f280051100103c0c000c40180d42104000400b40b000c154407141c2d81d8055248440c2c0c0d400004107960a0010074402ca04400c052691000140043d04182110000080007203000f289010000d400003503004070044440da1092000107017081480e101c03031003034500560781f0800b44c5844000d601c44201c450341040702c07101019900403941c0c041040d00300c850440381c58410b07180c2e0f514080303400004a0308440d0f110100340e01b0949400d600b9043c201c0300c2c030007020340300c00f0742d4007900742c1c000d001c02c081341000c074180c2c0410b1003445c4080d0b0500c40d60361900c541e20340203498564040314003c240d900c5141441400e900c290540001c805001503440000d20060a0710003140c0d0b1400381917030f104080c450071034003000c2d4580d00050003401408d08030117240500151025258085861000002820740340001e412142119641e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 94177248 1250 94175998 94176001
    0x50604150203190f091a0403080a060308030a0e070305060703061d0103080f0c0106050405070504031a0106090612020c011a10050c0a1101030b0a170c150706091b080105 74
    0x10409010318044580d09400c19461410002ca50781503e00030914981c001640d00c0c1481c00d40520300d5800118015407045490800c910070840d0083c00483c00c40b002d0300420446400134401d03c8203449400142c81d403040d01e41d411604c60502c01342c0201039400036044a0b11403080c0100109804004142c4582d01e0390381c001c1480c03400c20300d1007880015280c5408601c0f2000c403006000140140007560708550070000300940302c040ba61207242c0585415441030317400c185080107004115034008014801c1d2400b4070304200b10001d600c1c00d020b82c0500c0034800c070030004074400424040b10740705440e0200d40790452000941011a044486400c5420200d14141c5c10440003010b0445802c1c00b01d50320484c0480350911074188000340c031090b501c5000c00a0b001701300e001600019102680250300503512000050b0000c400c40e600c0313440304d44030500040c10034011071040072a4241540f61000c401250003849d05e214908007112959000050940358400310341c038800415100204600c1a603c800c0101250700020519 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 94178498 1250 94177248 94177253
    0x306090503091917030c070614070c082a1513090204150e010f0912290411030a0309050402030403111b010e0f010e0904060e0d02011b020703120e01020307020d050604 73
    0x4d105107500e904940f81c10511220f03c500e00c01050310f8080b1f540c2424441c01c7c0c54000c0302492090f00c1100b070018801c41e645100801c80c1c0d8400901610703200700c4a40c0d1500d0b8440c4e005020718401c3d441204081c0e0003001100755014880100b40642503c02004015102071900c4e5140e12050b40c22036040b15100c60714924000307002680c00380c2007222065007070070000d07500040181c00504800e614000c5071b010001e07141d59001007001c88042e0b0100390b5500e81d0000c3d0b071355030162409150110199425140d01d0002e4030890903a140100303500850380e41c10744404401626050512019400090040e024004540d8103042d05040a00c100c046c888403500040d80100380070310014202e074084400150140b2400b40901015903045a520500385c1030448074403405035501c0c075004019241449100c03095001d4150305043c11901500440f8143c3c0d00b0301e01d403240388504010102c1e82c0c1c2d2103502c0007030044000e8041e44240306001d400348503044203041c4180d0703140003460303008186501d9200c0c00480c1c2036030200d0108010f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 94179748 1250 94178498 94178519
    0x210f1b080c0f040c020312070e090c0a030b0411040e0a0905010c08010f08030306061c1518180210120b10081801110d0e030909040807020108090a020a03060905030919 73
    0x150841c210f400300101a03810300029039a000d1a103040c020070303601201182c600f600a110b08030340c410004000200c1860208545251900a800c14001180c10822303504100e1400b4050309098140c41c0c0c0e00c080c2010301d80701100003441d001400151600b035036016a00e021400078010a58040100d88a080c01d9500d0700c800c1100070700b010f501000301c640080c81440361035600d110448045140809000e2503c3c041c0740e003110020058421408410081c1e43c1d000100c0140d500f101980801801d00c007003081c04054000d0340e00c082409440294084000309215002c0343c09099225510380724100c001884142040204030321003810705440000c89c2601c410860031525221155040700b040c4e800900600c0709110380c543c000d0080c14640340741c0f00e440c0d00d00343e07038034035810410f0780e11a01009041465909082c10302d6a2140d000580590011700a83c00140307140000241101600741c2c041c1100002a20355101d1740000d00d116075088440d0f00003045108060744d5200c0003108221450514001268a803842404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 94180998 1250 94179748 94179769
    0x15041e0314061302060702060d0e0706030b0406120602070f12020a020901090905070b0d110d0b1807050405060313080a121a010206220f0503030907210f1b080c 70
    0x7005912035010456281c03c9541e0745074685074180c030016291440351000811034021001641c1104d85090068000c560b00000e0300c80440d1015281088140c040340e05000a446440c05078032078049281e0301f2800000d027994014413041d40545c0315141c080030780342d80d01d1a146e282c50a203000180d01440800d02546002c8062030f0040c10541400c00c400300a41d074540ba119070b1140b06202c00c540c40868800000301942e00481400211814001e41e07440d1003205000091904901d45402012111007880c1c00940300044240545803d440d5035003007901d00f0301004000c1d4401130207050b002c030b40013100070002817000011f032000c10b015880d80c0c0c000000d40c07410b13a41100c2e0540d18641c3c8894007480ac20100d41d80200300980c22540c4800c506032400307841d00301c0090204848100030705910140d404903007804400310295005001c108251507220b990ba0b038034405040d45100001500e80c41603008d140000f584000e84031183e034880c1071220f5030f855003840f01c2c0f031150190f070f0b11021a9401800c9a00b90516141c24400c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 94182248 1250 94180998 94181033
    0x40b0109060e0f0702010e1219030c08130203010b1003050402030607030209010c2603042603040206040b370e030a050a140a0f110906030106060e15041e03 68
    0x40252626041c02201e5101d0080c015901c080c0c01030f80801d41c080d00c00e400c10245400d649013100e000141201603800d91360311071040c58201d0800e6400d2060001c2c428005d408084e89140da0743d880030b880c0c404060848500c000e4049a05640ea84c98041d141c0e110340f000301d00c0c10081510001254506070052504040c13000303015800701481000403e950303a8004081034030080c1c02028603941c01022006125050f81011030310480040e0100800c000c00c0700c0303042c3c640d2030201145101c100101c0030000052150006450080d84140184824000105080040d080f000c030742c078440d03000d01c0c100341800c50201030304c44110701c050140442241c004950010005900d1190990040c1003250480c0c48864803450080d100800c48021155920500e11003003110b404019001501c00810034070713a20300060501d1410a501c2c2c0103031008000902d0700c2c41d040c0700315002c03529107403030304490028003a0421078151100001c10300d00040c02d20010640d0329540324025030043e801d403104a291400d41c1801c0340c440b029020314 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 94183498 1250 94182248 94182251
    0x1f02190311030721060b130f06050301121e050f010b09270a05030a050d0b0f030a080c031c05040218040f081b15010608090a0b01122108040b0109 64
    0x22003004050120071603030303c01d11514007520740384018480440052240004804000e083c00c03404502410120001c1c1804090203250346c6045960314403d440300031080c420400814824001081036040c8050b18101140c810a060700750320002c1071101c095003083d90815601c99010640e03404002d4001d101d000c0c2038880890350300d28946040b50800d00501100720944116401c4080c0d202d42c2d12504000030981c05070300c60240c948038008128002e00c03d4202020002186003007403050300e0241070242e03140002d1400940500a141e4440d01d82e012182c0c043c44101c07010744810000c5080ca01c0d002551901c0d078005400011400e4142401086440f6820304810648001d400c82400002119000359099407075001013040d46900c908110381c0d100c41c40100761408140101b041c03c2101e01000d08541d41a10610b1301da1030300f25201c03403003072955032419040018140d41810005000c880c3c40340d10219506d900c0340f481a1341c0110600c04107a0305c0351030400c0c0b840104103401c007480200310003440e404d805000e55400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 94184748 1250 94183498 94183511
    0xf070e300f071a0a030b100e13090308070f09051203030108060705030705040303110109020901030b07140a2304030f080c060702120a0e0409061503110907020706050a021f021903 78
    0x1103200d041c0c040d01d240040100c1001138030000e52400b030f0b00094250f150080c640c851002c040e00c0c000c2c0030200200c0380750b40b240420b0303240050211543c0c0300711090540c15540e00441c591390103206544110403004410b00340300303d0490001c1c103581e0b0500d005001c07585e000c01554480d490120184d150031805800c0105011080c020800901d41c07100c2901d00722a00740c41c1c0843c902050980040c018074000b840079420000407400401440192008580200d40c10381d00c01500d2580410041c440d40913001c1640700007203440894014184181c50303114400c3c0540c2c8982c6150a50f01e0750342602c50080384030110340c00c6034045031703917400380000b801a00d602c825140083c252030340c21a103100086210304500581071001c0340d411007010762110fa004150035a0300100030404400f041410800c2444640b01c1140c100d9001040904181440b2046c140941d1058006040c0641814030a4400790810040b01d803c5103c0d0803074010556103071401000103041034180c0140d444259035001c21100c100441c4840c2807508000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 94185998 1250 94184748 94184759
    0xb0604080d02061503061b1204083a09110909010e070f0803030a050c0903070303090504060b0f0304020906181e0105040911040c0e030601030c05090108060f070e300f07 74
    0x800e10340c01a07c0d41c07580210340414a034860107902641c21116500b019a60812040069400c010203c144226001e00140005401d120100190100c01880d107900114140c0034038134056000103910f06e01c5650442c030a41d8024010441c109800ca03441c03502e03603460b14024440c0480034003071000980b0140300040d03241821304420994a201c0900078207111690348000a81d128403a909880307800070000e0075585016070700e040c000c3c04040d0703d004561150341b41810009416030a102203450001722031010906541c0d45408005a5141c01400c490300520201c0910485040c4014441c0c070880f401100c0803d4a0300030345041c1412071050b00114003461034462914045144510034400d0503108480202d886c0000d4a41100c2d058200f07450710b509440b49034000300402000c041c4240503a042034501c031007641eaa911646607156003e0303404c02200c0c1c1c00388001c155041c3c441d01940c5464034001e8008100c40c025040700d00715403409190121500844250703407500c00641840821481901c40004107a81d80c10322 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 94187248 1250 94185998 94186003
    0x131103010f050604060e0d210207081905120904090f06020304030806010e130c110307060f0e0c060a180506030c09030d031b05070f05190c0e040f0204020d0b0604080d02061503 77
    0x440100d0712642d0f60400c01002c0112300c02c00018800d103446003014552401000c0a541d824181c010310b000ba0044040080e200100043e01340c1d8001d4000300208584a508c410019440d405001c03216000ba480703c2c03140740805c0708520b00d02a0741c0d11614006981c0e00c0d080c00c00a003407401c09002e560411040503507000283d5072b0b8001502c500e507919040055044d601c904c0589594210b21100c04281c040419154140030f50340d409200140001001800103502e03821070307d61261040c040440d401f07101806801001c0380300700b4103a24495084c00109a00f0b90f200c1c2e00013801500105c1d103460751200c00083e400c2c01401c041c0103d0a20640300c0c102803080000c02e603181841c50140070030740303c200840841c0a200307002c0108d02040c0100e80100c261001480500c1900c0700481004000751609141c02c000000d440c484004103504c141e800508407031b000c1c1025805c21002e5445121000f19054440d0215070169550500900041010500030300c1800c04194001c1e0800d03030300400052101d00000200c0a142d1400b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 94188498 1250 94187248 94187267
    0x30809150711010b090f063a060b060f1b0106030203010f06030204140c04090e0307020a080a0b09030c03120613050108060a0b0402042610050403050405310b131103010f05060406 78
    0x1180e40022342020343e286810003860400200c0b1003151151a1042c040042006a60900c2d0050038240201c0e21384006010701482100000300350280100b250103600203501d0711603881c02e840a400858016580e0700001d094405100301c0c160201e990303075030800441c505881001c2420030014030910b0b0300d10700308070a2007160003a48200041d05880e03107078030013207110144100d4111340d0340102041c44643d1182161552417111b120200c3d00a00058013180064000105540219003500011807912200c640002c2b14800d000e09042d80000d035200602c05007050070300520340030785402c400405c210314000c0d20b01c4046e25072848413603014038410402405044844605048441d084020150740c030083c80540e21f00d0b0903808800000d40c14602010300042551000041c07044550403140500ba152206d200410a810000800180003000043c900f201c65041c0e0044031002d14010645511440400c59801c1518072050f40700c15100300020040c0844600d4507840380240074107a90080c2454148080a00701c1240c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 94189748 1250 94188498 94188511
    0xf0903021003020702120f0c01020a0c030615031401140604110304021512070507021806010f0c06060b0c100606020a02060a032a0309050705100c030809150711010b090f 74
    0x6841c0c0c5144405030107601251202c550140c200881d0301c203445107058450317262984030070907402030589400c99913200090609010303802c6034010743c44500e5995000002e024400d20340c4070046182e0700c00004521010b5100c0c0b20b07510618004200304110940b4118207000c01081c0700d12442c5041006111001e180f015a5405a41501c0d216402c8101c4030500406018203000c445102180c1000c105000d58004050300c0a548260f0310085402c00b02003000d0007101045617481d00140c0140001b0500510400e101c840321409000c00040a03515417010600035448030b0b20072070360b65215141c90301c031004181c8a810010300039403015100c0d04a095001801500c42ca500348000c141d12903a11002d42d0304460844440c01e40c803401c21500200540c50064054041404182c4e0140100400029207060201c00011590055030b0744420346c620310342d000e855404020f0700c00710031481407510511080c228601c4841c004c089940b20340c5409112000058290f8131544072850103110f0710402d105003441c0510007160401c1d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 94190998 1250 94189748 94189759
    0x9080d1403100f0f0306110301030b040b060f030d02010b0a0b0403030e060d0605030106061706120726010509030712050c061611010603140c120303060108060307180203070e010f090302 81
    0x480354510240102c0c0540c00c40740100b04816400260144200030b80c1003100d01c0fa142c1408810b49101074030f41c29000c244806429141603d00090006984810403076210701c009240c444421150303404685407988c0ea41452000d40e42d1050b40002074a02001c0720f40003003034040001860316003503075002030001c1c07600c1e20f1003406110f011418054520070b0b60003203405854090700801581d0b03605e000082168041081e10490034031158041803a608210f4400d1800c0d110010080c140c2c0c1d0326080711203a00c1c1c645040f000e006461402c0020400c000c1c2070007034900038840480150b0706c84419042100802610714140070902004008000d120803000c95007650046000c0c0700c185511800100036605240803e10480d4154a00517021040203e00100d010000c01c02e202110101000d60080c413017115041e0403840250b50050000a800b580724840160340508090305445440e661040103a400b40030b10000c0104154021080006569105940045280e0300746005d4110b540c803d80f01030040140c0d0302010340141d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 94192248 1250 94190998 94191001
    0x9130c050c0a06060501140a0e01050a05090301140405061e04020d02061b010903030c03020c03040504051e0403080a0b010306050108040201080c160c03020301050603070620071208030709080d1403 86
    0x4500880c140c542015140d002ea503480003031840c182d4024441d82c0940d50105440c07148000c00c110440f81a1214985152988010141d85400554868000b00c240e00200700081051003180e440a029000000914984c090140d00b010319100d410500001d280c01d50340035814200c076030200c00c4040c8c178a82260301502d05102c03018890011444a1284502c800031200b6a40c10003030f84007030154400c1400c00d001c0c3e5000c200e81c0e416041c0c00c4080c0d01c10700000c1c508a0348203020510041c034155200c83e4102288401707008299418050b8070174100d03421039056010880020801c03040c07000314003500b21204801d01c0e00700000750620300081d000100240010f4100407800c0300003075115445000721140b0901c031001c07a150340b11182c03400680301801400120700039420b01c4003242003410000340c21800d540407911182c130615450025525404425840e45500b4421842e001900310007007100012100e0042d41c061fa81c03403420740f074050010901903102c626140d104800c10800907030300c41d5802600c540c0f4200416030301d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 94193498 1250 94192248 94192271
    0x20f0304151d0c090106030203190e0a02040c0504060e040b01090e040c0819060f050609040212070b030a091109010509071b080c07030308070809031605160e0a0e030913 74
    0xd16002d42401d401c078907802c00600c60003800040409841008403081c4540c0e80c0c03038403011001d13400203a460200c40700f09280e42400ca2025508401e80e07884041c8203d800b4080c80d138000605590a01d101d0740b0105500041c01c2c08155130204800c0454070341580c00780516202c640008100b03c0b502e00c16600032100700c83c08a030800907a0103155000b041004201d51000d000f0401030048280c8000c4200c500c0751130710007030005c0017071280030f154444c040003031034000141c0e07603134081c002204100d2405400c00d019001021400d034903c00080c41c014080c51130001810003a03886d00c000400c0302d03417280f02d202e010381c8001001141e84030a80942d0000180c40e0414030310803c821890700501203048014401701c1c002ca00070050040000e000011240295a8009107492b61031b000d0300c40c10001d0740c1b010740a800030407884a8104034040303031341c01d01c0c0d11400071101c1401850355440300d41d0501383c0044c0400301021050000900b03180c010140508000005140b071301021800141d6014150442d01500320340b6002d50718407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 94194748 1250 94193498 94193501
    0xd020c1e0a080a12090506060f03010608070b091801060305010f060c05070302190806010801050708071704020d03110a050f0c0a050609090604140c0a03060e01290903190b0109020f030415 82
    0x601c8903200c0c005101c1c91505c0d10b0310688071807003107451274000c800b4020020f002d89014028030086440e0500a004c0321420104403500c3d60384030600d00c54010001a0480b0418001c04a00d903000b010140c0e000542ca50500042c8020080c00d54800020030250401c414080740300482da150440f40d045607200035145d0109840340001d5400c1e4401607181c004c10b00000791070030040d00301511480340c3d0f41c1ca04c00d150b81e034900140c0b01e0b5454259108d8152242300300207001401c0500020071500d0084c1002003800407000c0005140c00010b010450380c2d6002000600380c00141040100795a6004030b500c83c0303200d0f0810012408601034031030b403548a4440c00c004540c0d542c46560007014000441076072200c441c5801c40039141a940805149000645048070000c0c01841071041141a107000719084148248182005035460003a08940b0240d4401000a40718650b410049601c07022140302c2e100c01c2054660070310000f003901c1684006a514010442841c06d60740380000c07260f00c5540030564910264003160840c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 94195998 1250 94194748 94194767
    0x30506030f030a080f1305120705031b0a030201060f060c03050d1407050c0c0d020d0204200a020a031101061d040305040f09020316020d0206060f030c04020d020c1e0a080a 75
    0x2a600000402c80103091340301d00d02c1d80c8120011003090340b07581c80c0c8880200030704880030000340c619007100c1804081d04240307400400940f4010011a82400c0c804080090741001c0700003c01c0c100d500c02c0a21000b059020301641004288250b501804985041400703810211103000c01001c0001c0081c0d0000311001580c881e0112a1540801100c03074a410700028000ba486400c034041c00303204000103040107182c202410071a182d4060302c0c1213618980c0c1d600b8000601202e0f54019040c61001c9139200c0d4040e002ca01070050406598020490500d09040250904258020242d601d0341451400d0020907410043c2c80d802c03a401c62000f0b0013954807810115894055a00032901090b500710b0005100890f030f070095406011158103404d0007019401c8140c0ea904141c600032400b45e001030000694504d031a074442255600007400307a80c0078001c2400000d0882c0d001c403a1480c5d142d980880d01240141e41000010703c03d5807428108441c0003441c0300003039070320b180c80351004018041c009024010603202d1078155 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 94197248 1250 94195998 94196023
    0x1a120312011214030a0c030827010c0f14072916170415050702012a090b030c030411010311130905070905060f0a180623120703050603 59
    0x51958680480d003200b004104000c0d0f0f000c040c112004040c84502004403001d02c0403d0700d40c000c00d048185d0381915403040c000c044260002d2951030a091504450000c2c01c00c01044200000e440400504003920780e8032207000369010001c000044120810a0200b1191642c0d000800d0b4000710300a4504500071035669103d19945c41c400e0420b10004602d440c40742c140500700394440341003051141100148005027110090003241109084240c50111584042c0c0c00010038400800c1680000750007240030392500c011215030a40385031070350801d15444039600d00034000d802100780c61820f2600d0001200d000c050700240c04040070701000d01840e0b0203a1302050780e0340540d80034540c43c3c080704d0201c4a6503a10a10981103031501380000911000d1290402c2d00c107440300103000c81d00701100c203850000c0a812404d281d50901c2a0080c1c0d2425042c82e40398a2802028561340d0050300c0c0c0d5403c001000d1541c1109040810000b0500a50346003400c80f51503998080070b03514000540b41c0d10500064a04061781c0d501 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 94198498 1250 94197248 94197277
    0x2130602060603010614031b2403010509010608040506041103070e091506060405030d0c06060914071b080403020108131203020909010807080c0d06061a04030201020f011a1203 77
    0xa18160042000e51090380e088000f00901a941c1e150840010b50040500c1d9054100d203100905040012860000032440907040e696800412003441103906e42c800040047d0400200040055281800c01d035400740407185030141c07103030510355200c80c1da0b0400600b0013401100c2241c00500107407030401076640181038420000301c89040c204045030b00d0340c500b000801c1c82d402c251000140c0c43d04165040b90b0840d00041c00900c60301c05400011201a4490001198034035111400059241d030a070191040c005000006a1060304101a01410012041d6501b980c00d42803940c08001080700442990200e030707020300340810780d41d0b41c18094100410301950002c25050480345501410381e030550103014070034002c0d604e14031117989030410a40e4400d1548100c11190344121340361503031401d094298900c001e205440c0407070310945408042e1b408000a640840010f0700216041055680c10040c40890711440310081000301643c514043c8186c809006250183c000701d512004005010800c564082050044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 94199748 1250 94198498 94198537
    0x6093703060b0111010b21070909030504060801060e0d08070203010e01090804150504050a03060c2c0405011409071407050304030b04020a0506040602032703060703060603050a06030b150402 83
    0x14000000e282c0600c0c01400200460b1902e040c0c00c00500c144410000300130b0900c41c4864002006d0b40c100301b40c04403c014280070304140059040040d004000c43c1c1d80c4207460f02da4555040140003490494140c0c005400c000d0101420383e095124400d00b546138580240c0352070768030802400464094401414912140d6291450200c103106240000e4015600f064403054402c2024203821207035802280503507503200407280d10400c00203c8030391050641054034109450000304030100301d4941c02c1a621444101c1c00b20700c91080c01e901d0544956070141c00c00c01e80d04142c400d020030105406290007007000c82800b084500b002c1e9456540030584070482d80c48003c0304d66940d240d10f06900611000c2d60101d010310400400030826140004c10b480695050381d00540c201801034801c40f5070410007120220315548040c600304215103003809880c0c41841d01d0f8401164240c60004000c1c04c84a0042c048100c4a1a090041c0f0000d40125105c030703000640d0500c0c803005c6040283c00240240316840c102e547c2c02c8403040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 94200998 1250 94199748 94199753
    0x609060605060a0801050a0501030905060a02070303060305030412050105160203070210031e020405101707141201170c030712020439030b04140103030c0303090602040602160506093703 81
    0x43c1a03810f0328030581c0c02c007c5050f5190015401e99080b03502c02003007500301c94000350030100700303034042c02c03541d4007d15001c51100d9030381d20740e5070441d032081e04040c580b458101101e03400d214090141c02e401c11381c02040c2000004074018000e40301d01411000910803c41a01c1e540a001c2c803d030444411005a02414514086074103c4400250302c00e2182502071911444801c590600030144036049078100004170b00e00b0742d50120100c9144101a82c021662036092045440c52a5240e4000740a07002040401141121190768140b501e100610710500ca544000070078042141e103d00d8200480341c1c107a07400702d062004641b0400511181d41580e404000b003080c074010710444904495010381086072420030207142c3c40030900c000d03101c100740400348010080c801000041d100760140000c00780240740000301d5145603a20042030383e00542c02040180d01240c1e0803017201070800e104d000284811078166207050b280030040f600d80038210240c0c940c1e940d00400540481c0d20382c0811841d6886c020b90600300a1516403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 94202248 1250 94200998 94201007
    0x108070305060906010303171308160303051003150e0316030f080a06050604050904080c07080718020c190c172d06191d0c040e12070609060605060a 65
    0x1480161010b2198102140c56604007280d1181600e030941e50f1286500c1e0800c9110714004030107080003040d10f5900780408003050100703000d085082e104812244e01070b1820304004003a20b0015003075042d103901c03a9504000041003106007008501404030003040c114201d40103182180581e00c00c00740c80e0110480034208066101404030740c1c8a50035151714015498102c010001c5031031364080d2070b030880c0b801c01052100b440e002c10100d074024407421600b450321b4500304004d4200700031540040642d42c4030240622011506c000d120070081c108490450070040c25100450b40ea40d5003440300d14001c00780700340f00000c3c010184045000340045150511880c8219a1115658102e1008022001c1348082840d4a058544a2070054803481240180034645664002940c007042002000d440d071070b030f00d180300c2c0740084400100444044002e0080d01c4103200c56010320040e2420305001000c00c0c1c00c6070f0142c00500d5290002d0311416038000c2c0000031a42070354603020000301980c0d0015580210041040000d0a502 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 94203498 1250 94202248 94202263
    0x9030c0108100803161b120f0204180c05010e040b010801120309031b0612020711010e040209040609060504110307080c09210d020114010612020c10020406020a03030c0206040f0308070e090108 84
    0x1b2070a8203030a0118001200f100e400d0382c000c011206120f01d4144000c070340040d04904900380014000502512900000400b440d61100225030104051004125a40c2c0200b80350450042c00c1c0d17414010b801c260070000f845418140138000c089820228160241032113150144040d503440f18082a0809000304c0d5002e50845911a0b00c00003600e60001926150450003941c3c0490382c4025481e452004c068015036859884000003034001c0c0d0309000482c007550316809002e0090079030300b9001582505040910050343c1042032042c404078020414800100d034045000c543c000b860002c15a101e9070310750300040b02040300e07110403d20403010050342100000041614426107031070380c00810803503800c2290f0b0398080e8400d2040001154140c2003810b01540181c0040c05e204105d0800d41e1144e40800407041c00b00d030040e8102000503400b19102d030082540502ca0695150074a0000b07101910b041d54802820030102a0000c04000e8000041850f82d40144034038913400e90000d110140d0b0350303103558445654132031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 94204748 1250 94203498 94203503
    0x1103040b0105030d080a0c2706021504050304050111010b0604060e03060702010606020d2f0706080f040c0303031a03150a060b0405100f091d0103060b0102010209030c010810080316 79
    0x200d2400000300d07841d0015a24841035141d031030b800f01c51390b2032000380c1009246a94040c414412140c0301e044000d000442440701004c410004000940d080c1000203140c9640164603060100041b824000840d030004140c40451b503091130300407200011030341090f000d004510103c6030005008035020541680184c0319001c402415001c8a0281e40e9440c0c04a0984440d4810310b0050b8000044001405210300100415a4071602c0d0010800c01000c6204131910510403010300140c0025409000903644038003819000756040c2003098860030540c40d2954008441e100040034036549590040c11140c9619070f01c1064900142541c0145809502c0d40c1c00c0d4090440d00400454a00312006c503045404400750307416500e02a2a040480c4502c41041c2e0722404c407862680305200c80810000ba040c08080203c80600604407001c03101e6514501d0050165070f40003400d9030641e4018040030420340c030000b6001032100024030b0b2062642d2103421004800b10501d4210315980d000c00540c4011900900f08003003034051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 94205998 1250 94204748 94204763
    0x60603050d110d0806010311070506010b03222a090507080417130e0603010204030b0c0c0d0306140d02062104020a060e060a03020c07050603091c03060506070209090c0301110304 78
    0x2c00440c0304588800b00710016001003a01c3c4008200194031075880302c0211032110541c240303414102c1d01c4440c5400001d82c801ca458400000c20001c4415404901d8961803102900410096007a50740320711020402d0300c403640e0712107105910003580005003220a0010044201d00f0805801e104800034200d201c1100c09841c114200c00400102403090004c480d000800c1002140c41941402c0002201300d401401e4560f2564081c000840482c51130783c007007401008007441c1d02e6510340e41c00c000d15003440c0400608070185072034407200300500006c0c416090070045044800c11023641e45440060417a01451342c40140400004400741c03d504100270300540100c0c02110801800c1d540e0f60411185031240d0900700390803580910484005500980203003464000076016078180e6a2590302148541e081290389403620b0303010207801d5111400340b5903070741d00000d01850b0030300070f4a0a040214209101c1d4800083c019100100000d41e44801072101242402004000f881f03802c2c00c0c00507103000740d002520295100ca = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 94207248 1250 94205998 94206017
    0x30807030e150405060d020c0a12020d09050103023108030307030b0a05030a032307060c050304061d0c01050d02090402030a02030402031905060402010c060b090702033604090807060603050d 83
    0x40d0381c07110654044850042420746402d40600740304012303401c41c2080e90540c0c45000001c9001588400343c9050220b156030040101803010a0000c002e188680d20990505104100d065003a050040a4000c0c441d903810503880c45000c030000c00540140039034440200c80c08003105010200b5450303040040d10940455980526035100c2e820561500540310000340411a0000c1000321414900c020380340c0c002c1108009410220240c491409841400c0c0d10b503000540004104170401005200340845612000f41d4080043d8a841e10340340c0c2c4840c1c10913100e040c0301000c116101c120060741c0448111400c090025074490034417801140113504282c5080f0304c24001c55048200385913511040d42d40854000f4002c180c140c503140c0040da02495500c01c103071900d0751a00003424280c0c8503031904600030300455000303641d202401000403142c9060300074444e400c40c0b0030254420990100c14208a00a04219070015540c00d5601c0c215034988180f1400501c05400c1c441c000051010201d4164808211a221501074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 94208498 1250 94207248 94207279
    0x20a111207020f120a05030910020f1b06070503040f0305010b010507030e01030203041e050d03061401080406020310080f01020d1b1b06060b0d0204030c0e060607031206030807030e 79
    0x40d18410158031a03848030600c040e03005490300c0460b1180030b80b80900407005140308401d2141c10418120000c0e182c2d40d00c005a8241170b4100911243c141c1c0384070b44094824410b10035810342e21000c80c0754203c00316000c08251004039694401c2241d8035a503105080f0390b50750356100d00854426100c0e101c01d8519501c0d1000d044415401107040307a01a541c1a80c40c03030305220074100154000d4002401c10341e0003005100d80d140d00d0300084a041540a8064401030443d07010420000702a20403c0d007182d0880481d6024070840b0382d800145d401d400950006c070150301d80e507414040759004101d51384030a40e03910440320300b1110060190f00a155400c0b10030810301c14000901c00011038100a41a900001000b0075668440d406506154a0102d0f205500100f00c0c25550507911090f600510340e9101d800d540010204200a61110741400420700315501034110724240001440c1400303812000b0b8203000c200c0078800710350541e65002c20050b5600000050312a01103080060034090380c034031100e01400102d102d000c00f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 94209748 1250 94208498 94208503
    0x60f03060c0a081302060a031d190b040807020a0f1e0b030106030f0b041e06080111030f07090b0a08070f111b010201060902160c0e0f22020a0306020a11 67
    0x8030710750000401d4900765440000712100750006095034140c19580c00c800300160b0b03492000f0b040341840d41da40031500810710b62000d2421010400c400100c1c0c2c0c03026001c0040701c2051043d10f00d03a243c00041c075507016500c44c245aa602d1080060080d44000500000728141020503401e900341d0780e903951050750f131003c034490a1015a8890003100c580d01414401000000d00c070f07400c180000e40c2e10510110750b024003580800c0a40b5641202481003e01c031400800c0303104000c0c4a29001002174000034400d00c1c3c82681030070754922001d0500d4112600060000c0c000c203028103015170040400e950110340e204510b1a00820307020003500c10074000354034400da032110640300e0700c1188603604d1010040c0130b144644915001c003441b17035203c9003810341d5202e0b040000c43c02ca2620203004020305101007180484180c4c607120010061640183e0980d103002001c1c42000740070b540b1890b0303101005034115102160411401200b898500350025800003da1001004000650300501810f03940340d110303420016610380c0e1458 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 94210998 1250 94209748 94209751
    0x9130c0f05030105030a020f0d1b0512060402100813120e0a0503010e120a030605030f010b0108010b0a080402040504030c020303031608070c02011715060415020c010903120e01020c030d0206060f0306 87
    0xf41d00d5441107102c5005488c01e813419803081c01d80148200089000c55072407040092080d0741100e115480c0500402450500c040410007815075040906802c2c038103035000806d42d110495400040040d07a0000400c00c00f8001400c40c0c2c4141c00045907000c410a4030002000041403584082c0030754a146000102402d05000c2e041c03071010f01c44082c241d5011403c0d1003410503000991480d040540350a4002403c0c0c8081c007080b070b01c001d00100082445002c000000d86100c80691003615000400c000700e1282503030111900303030010b604440100300e98031241402c07141c4646800001c1c0d4103000010901107040801ca50700021020b00d503c40d00d41c0360360b64107010f6603000030544005c1c0c08900c0318000e1503e45008185081d5000c110044450890303410080810150740040d0002504100300c51580300701d45404000b081208402441c040e00507a08550390300e600223620704000b070113102d01860b078401c00b80e00920201482810103000c49a94208c10b43e00259165815a800c0b405440d0000c0c904400d03090110f402c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 94212248 1250 94210998 94211009
    0xf070315090f0b060906070308070e190806070203121302010903060501060c050c0909030f03040212031204140c010909020d0b040216031b0201051b0a0605010311040f060e0c0f09130c0f050301 84
    0x440c1001e60702d407000d443c0a400200200c0c00c00004a903683e045680703013104cc00900702c0d400c00070b03000c460270084101c0c5011000b401c03041c10340d030003888030b64800b20f03154000c660710140d80c0c004004e03000428070041c0c03006001a00000c10366030800002091703896001d00410b40003802081102e604241c1e02c018400c1103841a18200704ca504200108420011a04019070308584003821542a560400c0d03403440c1550001c4050000fa000405c0522086c07101d0412114128541c0300007800303098400b8800644219418452101d0241d0080b8041c50000440c2d40488002003014005540c0c815800401403c241e01021044011030070a00c07503100c0000410000518056044e102c16203482000c500c4501c4c130011130f22100f041441001e46000029809000e120300940c860383c299128200d50008010075201800a504031041c948032042150b00701244183d508101d424032041ea0b00d081b4090800d0043c42407200e0240c004d080040c22141c0300149a02100c1100d005039520200c0c0b00703480504030f52500c001e100740c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 94213498 1250 94212248 94212259
    0xe100b031b0307170c060d0b0a09110304150e0a0501020901091e05060c031c050a050606131404060512070302011b050d05030a02072a08150f070315090f0b0609 70
    0x611100c4410441c1c501c01c0c602c0e0804442c006150f80c0000307038487d07100105a4103800d4441038601d5050600e10711400103400d0b000e0080c01403900c960780c16009070100034406019282c0000d04540220304541c44000d001c03110406444d80080c0c1401d10038040e41c0500072050002c0d0780c50000041c800021035600080c4250070410042840c90b000400280750400c0000d044036003c1040751004110185456403883c80c4000f8020903603251072203a60f021074070b006002030b0084104110a44204035803c6100c02911425408040300c00c030348201007802001603400050b0080f283c8041200c540d00c001505904480c400d903280000e11030626a16554003c0000d402840343d413041c0c0d1b0a0420b50300803006564403400da400c00608002c1280c0b140c2c0304844140c1c0242c01c205e090382184215210f90441c4020190000000522404042d01d41f400b40804008000c03100901643e40881c245030320030380011500720507180300801c02e29200c0d280b0100500b0b058041c141e000d49407100e94181c5090000a07900d001400600 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 94214748 1250 94213498 94213513
    0xd1b090b03120705070f18110301060503070c030201180305070c090e03301603050a0b0105040303080408090d0c140114090108060f0913150603120507060e100b031b03 73
    0x2c0c442040d0404042240d407401004004902002c142c4c20540041c0381c019028a404100d0300745c08800c4613150500e00c91005420030040c172009030080e0480b50070048920301002d40e6406810200d0060400c40d2004030800c0d98403040d8000d05038080003501906000785070203500c0d65601c900c010215050090600700c6a0410700c5003840d052a812080b001e691a620b00f4952101440041d00c40c581c40f00300c0c3c1030025030000d0444030003015450302c5007690000001c0b2003000800340100010b0900e0146100080130400042300003800c22040805480080b00e014103070080c03070b01445c07401890b580030074014610315121400b1700b8940f139849200e4803010004d41b000c1386440e203042c03c0011900510001d280707640000401c2c814040b280c54a8135054840c4150f4a6a080c0c27000e083c0c0f514038010210483c02140c400c0c10442c003400880c0c1090041110310b0302a05009555102c0341c81c20601400f401c11803250709008244007040021680e81001d0014902107041c3d0700303280545001c0b1000269414401500f40d0311441 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 94215998 1250 94214748 94214773
    0x15140a1515090902070c031e0b06040905030d15050117010510111f0b0a0f031104180506010f0302011106190507050c1204140306011202010507020a050d1b090b03 71
    0x4045281c0d950710b01408800d458101c4102a03902040c000c5032200704111040003070000b0071400e0742d28000d5845600d01350310500d441d840103107200604031a1096969410030400c110b02081151101e40c1c4610303040c01001e40c0a00c1c2c51000c15424030403507001c00c032a4060031840010303490000f4140d0b117008024030400000a802100c007014409030154180c850307007908c4000032007440c180c000207500c1102c0c003103000c00b260070910a02d109140d1101c1c6010321080c0c0113000064401e0f10850604905a03800500d1104000c0000c45111342c4010203010380c09120b00100304011035040000649001b0780f1a1030000003000000f40da0b80d0011038550781c1192000900489840309030f04200d4200069141142c14007004000c01410034019400d0106103440001c0e00300184001c0c0070481a1031107088000c1d03c8150b03d46010a000090300d28030090405c0780003d42c03032007159500709048002d4500a02000c00c841254602040410024085250b16290301600007400c1c00c07060040303a0041d1001b5001d4141400400d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 94217248 1250 94215998 94216019
    0x70303091a19060f05030a060908130801050702010b15090d020f12100506030d02060c0708040e010303020c042f0708190804060c0504050a0b1615140a15 67
    0x6481200d0708400c120010305500c0004003580d0085102c8040c02c551210340d0003101d0229031060707000810003402d0700010096a42e01188403000a84c000b10b0204140c2c07202d20f4544020b00c9050000700d10600008404504c0002c1540142d00c038101c0d0303030020042070b03410b4000c200c1800d0150a05020170803003004454039904050000c001e03428406442d85c40e0803d402030008070325000103e0101250340c4449040904480c080c000c1c035400400540140c4403220034120001d48505d070050118070324850014205007040390000c1190000c006101001c3c501d0b5031649402911464040140d074452800c00803049800710018448003585174468221004a13241d0040c403141c0350700b03e80001d80c0c0c0402d0a10101412ba18224544031907450707940d8440d4028a00b03450b00c282110680c0c08030800300700051000344425140d03070880001703490201311142c1d00c1c2c2600940c03280c1c1c0d2041c8614001c0c061440001020303400700c00d0340c1081d0000415035283e4000d998501c00f410044401c149081e140305c0c03101d00820055880c0d00b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 94218498 1250 94217248 94217261
    0x7061704150c020c120102130b0a23130b12070905031b010203070503070b060102071a18060d0618110306090a050606070f050607080a0203060d14010213090605030c030d05070303 78
    0x440c01600d0312540f4143c0011900d14803440040e4140e500024040009807a0358142e00141101e00709c81d03401c01c1c1000b84014800303041c4084010b040e19106000102e9200054152894121240210000740d41c591650614540214403903080500d0940d004c28101e0307004480d590241d81014004109560740024811844100700d01d1040c1075001c10014040402c6081c80201801030142d4022807283c2800400203140500071740c1310140040002508440b6114401c045036010783c5a42281c0009402c03641c0015024868184020403844c688100001c1c1c440f090b005000341c40c0216030342003003850307007041851800b40b00890304683d000c1d407441c00049070390540d40d20194011760b01408482c10001c5564a04601d0a1700910a9880b0780c40b000400c0403a90b03201c062181e03c281d42034410f5040d82460360100c3e5803d0a28a0b0080407651204444060340740f00354142e41200b48205040001c5c6680d504030741008059130300070316002c0d0040c4142c0c515542400243c003e000809035448030f01c0c1200300c4d2001c07402040d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 94219748 1250 94218498 94218521
    0x10e06070b0c04080c1503070c0c090e101104050102060408030703090b070504090c0f020c130e01060e06030115050a0e060a03060903030b0f04110d051503010507020706170415 77
    0x1820300c0038002055a05000070700c60b00032180c4096a0f01d041203406444d00507044070207441440050b134040b8400202c1c1060380c1e00304101d42060032170898a490b08242c0d544054100703da200f45440c070225104800010556401a0140c204004a4080000502551246c0c3c040e1380d0241c1e000b400858002030b4510b0003542c3c84149c41c940091200b0f1035940d000030303000003501ca541c000f40000c1802c0c0107021040c8142d007200d070150305003200300154504020707480740c07128200984590090703280000840c800c1d0300304000a054000003007281c03030348417403518000450079a2071a00030341c42d244000d84601a281054403c6d04c6004080a007100d1401c94004038501c4000c2a50f904000a1400000061114010713400920300c0798401041007001403040c8100d0002c051951803055042404a5040d00d0042c000c55404c9000c00c0004101030b50f80c503040798001c511000d04243c0541c0382100b0804883d034003040a00a0303640d181d41e6001d200c82d1490a00382401000d40d4040e0547c0381030400700c1c1880c141603200014002e03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 94220998 1250 94219748 94219759
    0x50f030907080304060801030314040f0302010f031d01090506060915060705030d020301121a01031e030306051008090601091b030b0f0d0c0503010b09040b040803040515010617090d0c02010e 83
    0x503110400c40f07045820561100b804210120010b10400d13800001e4120410084062942014030b0000b80480c0342180c1c5c400641482281d6890807030f404d100f1380003245600f21110304400140340c0803403144c0c02440c0d000c4096070036014084c04540c0c0c524024003a1401101030140300502e80f5002c42c1000b400b9400460220340500c000c01004140b540c80b8001386008180400c0c91781081e031181c2c00c03c02d04021136000080205421040140300140c1600c942411000301c039401e00c0c421400d545419001404c20340c11195102e0980d541605d40c071503000741301c0e030b115849082c21f565950740c0c1c038440c007000d840913402c004004c08002c4030a400c003a0f01c65400642c03403000060586d403900b54440003184030103041440695091410f08000d010310b0809004015128030103a8088030700d03140c40d44987c468110040d00040000074004046018000200502003500d00d4688403540b00e96034818020300b8400c581560050548880000141c0024000c224600036107181c1d20780f1200c44510703a00440704a240954440e030b000d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 94222248 1250 94220998 94221013
    0x80405010f05040801110a1103070f030807050708070f020f101d0402120a0e0f0c0105032a0c011509140604151a04030c0e101701020906030a0b0f090601050f0309 71
    0x40708240540c1b4907481c1404030030740d910500c1250090215194124243c8a82d104002074800280000341340485650580b41c49182c54540d8202110a4030840d41e002d00351090200e800707000c2c4900c4015104900380300b12890040c01c0c1c046070030b0010b91016254204007050b4400038102e002840c0241135004614010801441c22441505c2c02c001000c1c00d540c0549015a44c1c60203201d1031004000e84080044c5a40081500c0d030140b40c0003c0403071100030040949580045032180d641c2900d85220100300da80510925295492604c28a00070301c0049445003c2081e20040042d01440c0340c0b141c0d5401592441201c0060383d82c503004c3c0006005110f01c1e001c0d01071039140c0001004104001c010310004800303294555518514240403010038451f4026035617400e907400a0010040504251004603500041c48003455541c0b03450550081c0205400203401c50000010040b43d101540d200c0e0140070012509610854030b41c0e800d200d1421001c44409010400030000710f00c2d450804e101440e4480c80681c1220401d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 94223498 1250 94222248 94222259
    0xb0109080a0b1e04060e070603110a11030708030f041b031703060d02030115090f0b0a050d030507080403111c02030607050c0a05030d05180102031003020402070206090a140a060c080405010f0504 85
    0x2146400c07a8143c48546d5100c01d43d40300010144000c40c0102650b140602a03000c00b400203160303600c80e95240300c0c11710030340f406010f6048001b40162341050f1340201e0202c0d200e00e400350300784000610440d8100d400d1480404003244010303480c0304032000c0c3c9420813100e2811100e01d080c031101c00c0c2e1024000f02d41c044840740074440140e509000c1c0340c00c0c0f660700050b09408945854241010748031510910303d0308505081c0366520913207c024078a03003190400c0341c00d0601c004c0e10741001c0e105841401c601170304461002030080700340400000100744491094810401004015041c480c0000c12260000d50507003080000c101d9080c850000f03050511003001c160368040703109550300c910b15401b807000700308031586810820903800e520b10140090114010025891460140c0c0105003c2c5000d0100912855000c60307031105640362541500c05410003e40411345007529441030302c18110180162501c1800c80d44404190380348903409071442c6990001501c0c1c00d150411740151484c07900035501c8801c00100b0b0000003903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 94224748 1250 94223498 94223551
    0x3020a0302121008010b2d010c0b15100302130b03060a050301090f0b070206041214090402070311060a02090a1202030a1203051b030c0a0806010504120302010501090b0109080a0b 78
    0x2520051040c0421501d01081642900c00d0400c03881d104844c1f4280d96400c449120084400c220612407071000d448602100503110a092600003501d426000c00c00c100c0407007043c08059100080490b089803224204420445c00d92081543c81d14803500300000410107848140080c54001c0f20041601a0b41ea0f1141c01181c212103003004143ca01031017040c5070800740041401096004000791000c5c0c0098a415226821012140c1d48c4003010006501c00c0350a045949030182c0d10520f030020030540d920707503290500800240da01e01e0300310302c1401020b001c60541d103164404c8034001000900150390403494184090b4001c09483e0060f81c050003489031a800162035080d103041d86602c607807400100d504081c000100340c465010751003c2451010424801c1d81d80d8028191361034400541b40c07000740c1c1d035035038401220140142c3c0d101030640b5070750041400070150190881410b8031490b8404200c80f8000f440112080c0580e441108401c0c1c00000c0f440c80414507641c4419400b803003007100c66480b121000c05004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 94225998 1250 94224748 94224751
    0x4090e0304030c080102130608040807020907021f0524030703050a0b010e01050612180f030a020f010b09010308071e1a060108060d020a060c111e01020706020313030303020a030212 79
    0x19000c0d0000281401080700000303400015020a0000710b08004200c007031340c0d540842c54001e43c4d00b4041c10b240040c0401c80700404840e425640a0154a940c0c01c10000282d41c840c884031100e89030500a55564840502d00e01c1b880e481552880ca412880018684903c101400c1484083e5003502811501101241c000c104000c07100f0b1182480031515850411158416603040c3c0242d480b40004001010324841c80c03a2015800036599600284100c1c0514840c1e03140c101d0a8080a045000114013826096000300d0414800c008050081c440380300d500381000a03c1c01c09000c002d040e48020f2026501180d284498203000e2100c00c190780c10374000c03c0d101d4140141d80e800400290000324000c10049592010a0781d800c00307030a40b00200c14402039400200c00c0c001d00d004003400c0100c202403450600111a80201507083d001d002e0380d8004505045c01071842c808046082e025201e84000000d025100100721860640010040340c8802e0641d07500720701a502015141003010b400f03019070054414500c4145 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 94227248 1250 94225998 94226021
    0x110f010c090501021002040303120e010b120303100501030b09010306021309091b05030d120209030309090906090115240e040e0115120b060906041b0f021515090406020409 75
    0xd40351915002c0020b00d4803003c01c030b404103030a00604c02000069042020801400301006007c10000d40c819880390040400c418420752003400180f8401c40308401000940c010700520158a104549440c0150140c42600741d4645e04100301c4e500410102c3c100d030303000d040d05544910140103020340d01c01c650070a5890382442543e00c40c02d5034810301c11402d01c0200140050200f03402a00700b1011003000500b248042d40010341b07903240c00080c1040d40380d409100321180a40c00034280000c609003040c0c140c0e0344801c101c1c1c2c1d4408640ca02501d031b0303007a00c0e4502e12401c111000312061802c03460007001d00e07101d6010300340000c00c24444a10030030822507a46006102e01080603900010340e42002c00208000043d041d44000b560102e240da03403501044c414040d40b94081340540721402c0b40d0b00c03901c011800500d40c8043c3c90840b905a484606000b40d40090b0321031013000c0c44e5007102c001a2030080701e145a1075050703914501e80d254942070401316050004489074854000c00005050a80d02c8040c8001d071110702c88403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 94228498 1250 94227248 94227257
    0x18160905092e080d0f020102090a1701050108010b0303072009070c030e0108130204020711040615020601080d0e040e0f010501060315090612080d0b15090907030e0607110f010c 77
    0x400301d107510404000002c1e580e03501c02e580461850409683d0f12102483c050004100300e405034841503600035011203640d880017600c10002c556541c02c03d82c1414018040c0c40a05500385000019208014056561110001805549083e18a03611100002c030344204c2e5909421228007a40c8060391001d05031440b82c1c80c10b17127503441700d5a00341c0b60003030500d420014418180400102844203400f140e4405940107641564016600c1c3c0301810304072242d403128422658020309150011500c1d10110038000c082140e01c0d022201e16036220070080e911040442c0d800c00016403039041040407840d00f40c000c080a240c0e01410303941d0404460300c4182c00e440302600a240444c0c2c40d80c040314098007203512401f0013404451020010503081c0114844d11600d10030001c4c1000001042c0b0203200b814a9008140d000801016418204000d92904400d0780003400114410030022000500190103030180b1142d4145d0403025180c00c1e5144041642d5450220035402d6007071042c49501151280c0911031414441c0b2982c49 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 94229748 1250 94228498 94228531
    0x601120b06040507090b0d020d09060902121b06071a0408130509040b0f06060d02120118090203060a0c020114010e0907060c0809040c0c02090f010302010e1816090509 73
    0x100341100d448040d110030700461800c020844503650143e803000070b80e0307560002c440d602c001c01d1001001901403075502c1c0a1a41c9441003a0302001a1a400000000d10903035144c1c42039a61520243e03221150802c000072410726010522460f850b105006212061080754008150502100c4280f0b00034000c4030211421400081e03041c400300070760004a801400c080300c4001d07051806a4411003080b001038621200803001e90080f9241c1d540d5602038940309000300f5000c6458010300218001c4074002841845460034481200300c01c031006500600c05003c1c2c000d0014031041d15000300c1000201001c41c0820115566aa4242c2e03a45e0020701241c1d000705038040258103a4205004603608080107a03004909000c114111280061000c4040d034031800000c480002e1458014401a0782200c06200000d42c010402c00410060707000c102c0c40641600d0003aa692000042d42c07100344803215006540701c090b58110180029400d90040710310301c0060f9118604006040d60703d03004903500102c1581c0750f0442541040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 94230998 1250 94229748 94229753
    0xd09030e03011116080c0a0515040b180d1409040e0f100b10030c050f0712021e0a021504030602070c080118020a0b0703020a150204050102010f0c091214060112 70
    0xe41c2c00e55603c0c008101d20300035035007445040340c045180c0010544003010901d190264020302c07a030140e10750040709440d1b20003280c01c2d6080c0071550859044480074000004141082e050f4000b41d005404203200410884441280960f1414803050180c0803501040101440540340d500030f959130702240328001c00d101104040c5290604680c414000a100d00d8054500c44580d0340a4100240003614100040d00f0380c00300c0d204076020302c03854071285070304c20002607080104421007032003400344504c41d401d44041110140013030160040300c1000d86295845010390001518200038024404035407038851a24099491342c884041e60004481074540d18500030003008800000c1c010b80303a03407903219a5440c07510381c031550004e200e0b02c090740104c902150021440e02c003014000c01c0000400f5800c500b11458001905650001961003401214010b5083c1411a0709980e02c41c0140180c2c805d0799101c00c0005401c3c2800900d00360521903098443c03c0d06000310100140050048902900c8400940d002d8903c260 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 94232248 1250 94230998 94231001
    0x211110120605040b060403020603090312071205180304090f0207050a0b1b0304050303010b0313061a030d080903120915040302010b011407030c0305030612070f0305010608030301060503011a0d09030e0301 89
    0x6500683c007072030410810001654610301190107680c4c1c1100c0568985d00d80d8040e1070310354040c2d0f02880411180701010b014a464202d1910300d0b0110680380180200c0da6000d000c1c4002d00c65a01c10b84051f03a1051101780440b52840e08100d0320750415100040c14040c0c1a00e5181c94840d00c5401502c480c109a014005030209401d25441d5000340f002c0c0441c9142001d035100780d03692105100c0ca448545002c030100d045030b403c01421403101a00008140041c802c1d451042000c8032003403e8241c464441d421034280024003615185101d485901c01a6003046100000404104401030000c00d45015900740d10382401c3e000060305005502079400018211104c80c009800c80c0c002910b40000881d05200c2080047d03070101070504040d40c1880d0480d146c0c1c440502045008034845081c4810f40a039000c085041c40c0c2d440e010718200c0f03014034000c0c403100c0d13950407480d51030f44828002c10300019010001404083c1d402c0c1c9071100171021007162035240020041d02d01081315031001c2d007100040e403142c80401aa107001d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 94233498 1250 94232248 94232261
    0x4030803160c11061305060711030613080306040c05070f050106060e0a030b0a0c140f07060b0a032006041839140904050c0a0f0921111012 61
    0x8a05000c402c0c82da883d203070459401119080b69100b46000166051925030300204200204800f0304101d44640d03092034040f0ba5000143ca546020b482041c00042c0720103503001065041c81d4001c4d031501d146854040c1488003a001e41e08813074090003010094240050480c40031000c145000388000540113040400c0240120510403015214144a0005002250225a0350364100c0b100100010b4941452a001d80e00d2140c0710b412103542c010081002c615076a1000001c02a1602c01c010801082c0488800c100b291b080f18000a0103a081a50b000d00140b04292080716880781c005003240d080c41da0f91300d645141001c001800411082e01e42107012a4440300d08510818842051103d10280009010f41d841032481004401c0400a0b90201100d015480307004940d40510054030a00040c030300100b12000ca54400503890340090310a000110f40203209036200700590b809040d050803600808249110f95034031400781514a440c4540c400071190b95044d40c65015004151079001e0610b90001c2c29204036041c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 94234748 1250 94233498 94233541
    0x10209030616180f0e06010905100918050c0304020d0510051015020607080c09040209150703120b10030b01170103050610080c0f0d0c031203150b0a0c061a0604030803 73
    0x1043c5040c03215001203042c80c0c040d90014480381c121596076500496060341c2603030000b90490b80c0c4a00c3c03802e29075440303101d00c07094805003c035002c0141415061441241d10444004081000c180b010400525105548206d45400388080f1041198039850352821940c083e5072515601c80d101c0030410460580170b84036404d10f4001c2c00a00510320b8107240152003240024500130380300100007a03072a540c0d0b4959040c0d0321b00c070300d015181c84d4260300140d4071441e1980c40420141d012509007041807181280c07034007074206e292001410008211a16402c00e034080c080e50040c06051000402d00f280c1c1c002141c56226000b5030150000303100300c0c2000c5a0f030214080c1c96800c501c032107410009c1d901c21581c6640c0741d00a6000010b441c02c044031141070070322101086054000030f2040011f102001603c9a140c3c1004030303144071000030600040d59920810880d480b40303480c804043707460342d86880041411603210340082145d075200340604125413000121560300c82d4008492906001c000d0000b2240e03c800090342c0c0d6407 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 94235998 1250 94234748 94234787
    0x4090c0f110a14070306090b070e06070c0b0307030603020409051b030c0d0803060d051b01091202010f080405031317100528020d0f02090301290d05010209030616 71
    0x688006a40d499000e20314014003c078202d42054440034a0030000c1c68000d64204004012405080c80c1c00c001814040e2881c00020f007410311116090301c3e0442c22182002e5200c03058200f031a02d040c648074250340005182d00140341e41e9610000c09a103481c011002c0d09881a40a06001001c150000400c2c54030100c08600a40c01031190a449441307800c3d40c68402d64003d107504d500c0340d031003200007015104c020400400340d008000380525402c1d1403c1c1c1c80c0d02181400d80f214400c0384c0e2643c0120340b65295011011340040d2443c211240400d000e03400c0c864015008406072850202c100595030b00480d250b5000d1101d280300d242c40d0070f000034410710164540508070101030040c1e092080100e204180c007403080e03007800e80c0d0140102440c0401c69048504c0e506105500307004401d0a01c40140007900100003d900035400d045000d4000b0401d010000364030411822000d071220700b15001d01a90006e0090100d9181d9400c0040c3e900c2e44d40c082241c0341c0300d000b0030b201c81c1404020040d0001d20017646c841c1c0011750700 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 94237248 1250 94235998 94236017
    0x501060504050303070f0203012301060f23030702010902060412020f0301020306030604020910090c050316030b100c03090506040b030103020a090204060e09070c1a18072607030804090c0f 82
    0x60350040b048824143d046800f1503a1b43c800e5000190040c0388030304c1480b4200d48854409600140c3c840310560486020341c4400081060584043e0348010301030800d55907101280000b043c0035242c40028542004041c400001c0201c02940070902c00c0e44550090700b03103000e4034103d041c110316044485098105064000b9411400c021011a031344490241c402440362026600058046445107013000050082c100c05028001c03460f64042d2144c1d009941145c100d01d00c840512030703001e0080c0580d100b0301c05c002c1e11410100c0d0407e941201d0401c40c1500440801248200010701c5981e1900504080c190342d0510b5542c0717500d1032042000c2104aa408481074900500041100c260480702140f6004810390b000000c0e551064001c403904400300d6001070a604500300c11201842c4400d180078458468600e0ba018802203105030715598203450f2084400841d04513a1420341c0062030031203d580c4216800855600c10781300d9441c11801c3d0050381000000c0c1380c1e290402ca00c41c5a11050301c014130301d00c0c1d06050880c03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 94238498 1250 94237248 94237259
    0x50a0b09030a080717070f021206040c0b0a050c12040801060e04050607030504020a08011e050a0e1024080c100f080f0601020304090c020724050706050a02090a080a060501060504 78
    0x40798400503000d000518007040c40030178054070740d005091070310300c0420320381c0e50310814601468110214101640a40c0124900b200f5240c0c00041c0d00d070240c0d070481356030910f452a18a4602c0c5076442030240c0010402d090048031410740c4204601c00c02c22178400742c21601c441c2031542c49400c6030996030000003040c1d00c0005200200d00040342450300700846107400701d500d69403400407840e81940365100b42d8180d0722380800c0501030300a185800000018100f820b0142d0b4a48014940907658001c44860a54001c02010a00e45145500c2040207008640e45503900c070a01840c5556200709540c810b00380c940064502e200c0a00d0441c0309800704001302c2c18424085038002000412446005011990303180028011600d141e0003002070340c0060481d00e03800e200c0102c980100a480d00080d2041e0b404070204060600342203680315040203203084071503944600341170907601c844026000c040d28103c8019400c21400c61103880d03074031348440904000360042000c0304051400c001141c60507440310701009400c0c00700b03210 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 94239748 1250 94238498 94238503
    0x30803010605070611030f040c0801150e060a050909030309121204030507141905010506090601021f06081606020d081501050d0f0510080d021c030903021c0306050a0b0903 75
    0x19181c0a1500e1078907a0418a0301100405016104c800484404002c00c0142005088a40d226601c580c2e07001c444c090703540e2000b5080c1c0714140c03280c00380900662418000407842e00c10706640400d00416041c1c4903541c500c041800918151102c0300550000020840b08410401102d08903800e04800e0b980b03400000d4640a0384140040c00c0101003010014104080c40503001418021421110585648194030045841e4002d60884100c1d1203508000008001340b9001c42500d00c1140b06030082c180685594090000c94030541c504003070065603038440400c1921081040c0e400800842c3c00180080c0d0519602925240c0c008815004203d04041000403e002050f1040542c0300c082c01c0c181d448162400840029004030100d0b5002d00e841d040810102000040408044510010a0f00c03440c60417410202d07200e07182a00c1d490008080400b61020a602c01e602c03030b10341140648162090580441d0802e000303019114500340010723480c2e0318103211501c0c113810303484020034114040c0c0349004000f40110341c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 94240998 1250 94239748 94239751
    0x6080f0f0106050703050c06090c030106050d0b010509130503040608071d030a02090907270608060c03010e0604020904020a020601230102101107080a0f022a0d02030c0406030c1401050301030803 85
    0x90421601094000826000b41c6c01d481c1c44007040b5056403040d103001c1c84ea46640c0d20036024454402d60070000002603034146000300c111180d0b008400b50080781c4c01c00c03062001000003c7c08018009503d0b908a00100e40240040c0018000c01d0b80c40810718109080d000b400040c405180c6504005176001e9000d032560700184007251142d05607442c844581da485505801c200c1540d10054640000c880320140300000c01812401d513298000c0d041003000e840700b07149640d40c20b007100c40708045041040184051f170100c01100317601090041000d840c25000c1004502607801030f40781c980241c1e00010050080c0d2160141699035404d004090241d20381d00d00c0c000035603c44803d000d6008190b584c004503035000e0380d840202e0720681e4128580542d101348600c0c0090140c0c40003071105c030040c0903913203a051720010b040801c989000e08003000b420285850074100a96411523003402c0342d241c410340e0040c415a0711903000700d10003140160a110302452a05c0142014885124146410403070204011310005036508141c0707 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 94242248 1250 94240998 94241009
    0x50105040b01050d320f0702070503070603021608070602070b09120906090a080a0f1101021209061602090c0703080a09050601120c05041506020d020703030f0e040908030403080106080f0f01 83
    0x4212480c81200152005c4021003a040e0b030040044032110301403401c90105402075400c940b05035000e41d691074040b0303110316590003080d034107800003c0c0801c0300034441c0c0c000c0d018520038000c440c44400e21f6507444020581c000c040840384540c0100f5640144450810f81c203900c60040700142003484004018242c50b0720078a81c00c6d43c0f1071000070a00e003010761215120b01019040780d90850300c0d801075505101010000110b0201d8845104007440b2549510100c1c010030707803504110300c444c1880280001c00030f1540007a54400e400c500d5908a60300580c0e28107080360700424281031020755994080c1001825450300406407613a0030305100e07000000540c0081c0140c11142d500d620000701d91664070b0040c108910301d40c001c0c0e610504140c1c0090381d08050342c00410440d8003d4003114a11311650707005030b80b26a020321002e0045980e040052000c00d00892800c50400402000001c0503c55a0ba0f80e1355623800c00d44054001402c8440103014454001c1c0310103410100510369568903180c00c40d000c0802c9841400349 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 94243498 1250 94242248 94242251
    0x5010503070c060e0102181f02031b030d1d12120f071b050d0e0d0f0b070504030512090109170a030c1406070c0c09090803061e0310060504050105040b01050d 69
    0x40c03100f031154a600850301c0341088002955540450100e030240021000e41051189a10307604c19003c07124051891061401c881c3c000e5400c0031012811060390384200c851100450008000c09160460306105841610303c4035003448124007280103165103082c46c99643c40d00390300340c1040401031036225680d04d00d07802081240225000c0e5580e1100f200c0100e41c51003940400381c1f0300d0031000e04114000c0b926816019441d602c1c3e80031200384408101186800d000040c240d078a82e9158032021032111000590b218400c0d007026442c00740c1c0c0341d40f10b0713183c40e5511111207010000481c441d601d941c4d1100d8008014110448000c1d15210a071100503110048076600400b40708042500c1410040c1c03011a0180d00703003000003542c2d890310702180003410181020108403a0b5500c10000404c103441c5600c5102543c64005840c2800e5035104401c2c4106100d40b940c086d2500b040205100d12240d500300040340c2280780b94800445c10354517160900007581c00c180c005070310590400c01e1030301141c1d038814280e45410280140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 94244604 1106 94243498 94243517
    0x40b040302130c0807120b06040902130b0301080d0c05190803090708060903090f210d030509011413113303040201090b0706020c060f011503060501050307 68
    0x40f201081c0281c001c120041e109030f01484c0c6145541c00002079000701c01d0002140c42d0441d51202d50096000640d904a07000100c030314200030801007418500719410144900c0c1c59048081c82d460421184480c940d0a104040040851840f100001c50903086250b080c00d01055000315048040e9110342c520010f404000000d10500c00c01102e4051070410b08620f040040100350070304031720b501c203441c10500d20002112200d45061104d8800c02800c0c0440c443c1c001405650b00108502656403511920b59641440d031050241d103c60140c0400c0c080742c119190141500a44002203a0419a400c1c1c0e03040c54070796601c0d00030801c0041c00d601c00c0f24800f0b50010504092208990003400100c90b03410030800024000d0203070480501c90359026080055104290340b414604403038400c3e41210300001041207220051401c82085040e1405002d09810040081d0052102519480070001110b1 = true := by decide +kernel

theorem cover : BRFrame.Cov 94064748 94244604 := by
  have h0 := BRFrame.cov_init 94064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 94064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 94064748 ≤ n) (h2 : n < 94244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
