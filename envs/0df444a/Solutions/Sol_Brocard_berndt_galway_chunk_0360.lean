-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0360
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:24:53.856718+00:00
-- url     : https://prove2.me/submissions/fb203816-7a79-4f2e-964b-4233553db437

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 64568348 ≤ n < 64748204 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 64569598 1250 64568348 64568351
    0x5040f0f060503070e01030f11040f080604230106050a060f0e100e0f010201061d040203060f060d060506011701180b0f06030109020a1107121101051204030e150d090309080d0f0c02060d 81
    0x309d103c0d400c14031600680100352941da0340190100c0c0c20715001418cc5e10031604848008065070615241d1940b2080f4102c01c000b0300d540b9032070b01096980b60784000b200104520341c1e45408080070500f00825a01ca008070452082d40025041d0004691045401400e4070088428011072803035480140c0c011b0929900645013290400040c00450910208040c4118003d4003a13032682d0f41d139081d40c410010700484011303030700980b22205034000c182158086580b05406046c0401c4002c81c1100f0342d00c030440f0036030000d451030b0369000c00a11401c3c4640114404c120042d907001010350304d00c5002400ca40014024403401a50100308514101c1c8500c140000f80503000007900c0b01e00b51544011409507841d500280c0e0441c804000540080d4800c0c4103c84102058560041103034403150b90860780242040303c40b0341d000f0401104500e6200500e8002c00354801840000110a8800e01d000b0740f60038060f41c0180080c1d000103000c004001d411001d290005141c0746001000e246e41c61001030154002c24803101c4005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 64570848 1250 64569598 64569611
    0x708061c081c1802030f12030115050403050609100b0d05030f0d09080d0b010810031e3e01090f090c0c0b010b07060f06060e091008010c05040f0f060503070e01030f 72
    0x41c040f2480910300c0c94001e40a5406200c04010056520a10900c580c1d59944080004001054891510301c00319001482c15070700c0c00b035076604d0b824544017080e14042c0881d00310003070010130310019110700ca80030001602c4001e42025942c440c244c5078081e1f600315400702c071400220100941c06651000d07182c56807019007283c560401903d03c5008100c88980039011408444c00314400621314041c8400b180d0b4491110240141d10b601c401603058050101150f94902c000080c10000c44081c250108a541d00e42a19050500c5019130851145107440310130705000c0014024070030702c41d40c00d140100391200761a001c1002c0300c10380400c0711411244035015010b028440000305840c100c84000303000301c2d8000c2006119032040c480c0d401c81110b6092007000041910480c02d11700c1c0d400c000e050b0b00e1b4815007103c80f071541159070b021802c2c20355070003c25174000201c00081c03e01c55411020400c10140c21901520103030582005005425444040d090070144045050a00c440c1d03882500b041d484c0100d20103060280 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 64572098 1250 64570848 64570871
    0x512040c2c0601093b0109020901020601050d11120307060203010f0e0a06050a180216050606130207050a140f0f0304050f12072108030108060708061c081c 68
    0x4501c0300c100c180d03103280c80c1c6201051042d8428640001034400307801c41c841d620501503081d8104a4017001640d0000a114440111615810611580288802c80016130f40302580e034002170030b0a0b4142c001f075101e80295456000070480810b40189003032821303101d140308a200b102d00c480c40c40c000c41800034407847c00000080381a0408812060848480501c0e2003840c0d11003080d13000a0302c4c01401529006101c0141c10403100f403207440040c510803040d803c0140b500c0000c0420841402143c00c040ea40d540c0000140091410300c04000c120041680b28210b0900f1496500c6d951510342602000d4080c0c0380320703284500028030900c4204a10a0030300700322402a003900100e9601d03030300680316061041ca61a4003069250070481404000c80040c40c0181c4961810b1101e032a805e02c1894441d40b504824030912800040c00d1000154007a00a043c01800c081c50940c42c02080c1c00300c010301d1035000d01404d00300781954520001c5001c0b155a40488425180c0998490741144080d903011080320150034041d00412 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 64573348 1250 64572098 64572149
    0xa111605010305071e3501051011060429070206040b0117031905040b0304030909050606090d030309151d0601090204050307090207030302040b2101150512040c 70
    0x3168002e88040c441c0707659038035050f2018004122413000d08000d0f5208000c80f0341c480e01c4038040c42c14400c01e0400000010001000708240300d00c0d015444c41084e0001401285091058121002d000b407615804c00d24030070003e1502c1d59006440241310b0f0000b0030b540d1143c0c1c0142c05480751a203240000606c00740c81d140b1802581c1f01c4003600c055644088110012403000b29100389590160a0400211324103510100c50208052060a41c50b04001c1e09100200344000c0460007540242c0c0a0f560b20510203040901034030407a01e014080a00c1030340700f002030300d241c3d40742c000264443c0c9406080c00a009180c0f0300340300c030880e580b68544d0843d03146802c982c088050704925902c2e0999034240c0480300d04c3d03a2a812044124480c50085030b40c5035014140c04c11590609400a00da00340c0309207809800d00750360309204c2d80103400c0961b00000340f81c20009030320407445507107803030034014003c0149851041061000107080c4d440380798424080d104034000010144a0003404108c01080c5d21820898194070a00c081036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 64574598 1250 64573348 64573393
    0x307120b062407030e030a0614090c03160608041104020a0201020d0b0a0302011b051005270105010509060f041803020604020102150405060105040c111f0e03040308040b0a11 76
    0x284182c1c034114400316a40844601900300451071032280f03180c00b42903141030700c2505e20210b0a650510802c48140300195182c043c99015036540d03180d4148504240c444181400c0050094500079808210641d00c088590071541c011610f00b81481c507121344960501e55903c0644080d4650087e00019004e50342560550041c082a1800310b020020000504200300700c1c0151b900c1b01a00040062205104000e4503461208d403440c4a4000c41e400018524042002d50300304503540403040c0179145c5160b0b0742216070304101d591401c0c0d00008014560400d00000c070240b002408076401080c0341c2c0320300f1071142c40390f42c801400030282c8c0c442c1181c03032062840c0080d40c800f012a0128014001d00c041060303040381d60f24000340100d80c004041d0510b41e08140602c0010120b00c84510100b110704c2062840070241400422159a9900076202c5040d40804d2044203907103031055030100544c0f00b0402040401d10a800303440075140d4003468955104403006003150581700100300003040d40102000c86c04408069281034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 64575848 1250 64574598 64574611
    0xc02100f0215090303040204020c0f07121202010c09140103020d09080702120712060c05250b011d0c070203070b0a0503010e070c030804030e1c0606080f0703200307120b 74
    0x7a81651071881c40080d900d54143e4060100750710901c0490700500d407a8000c6c200c000b0701c001c11144003402400c011868003116601450599000b80703200d074180f201c0b41825000c1170700980001c0c00720004200005010860f81d2041e042c1000240c150703448540c0c4250100d403160b003100c030300a104800c5079040c08006584000d000302d11514195001d075100690108183c0102da44860294014609035110840a01043c501c9001001390801803402480241e000780700c540c0c40c03400c88a40054219180a1080f03080680114081d401da145445403c1500d490f251755005400d800328039222a410b2011130f1800750309801c40c000f21600400e4409400354008003460480781955041c5051341c40b001d02c02d441e10400c0010150000c4e400f54009030200340148801d40d007103a4094101003026600040e19180d1891617501103840c583c44207030401c18101d08020901e000070203040a004614919070303900310501e091240d8480c0160081556400650b801d000c01001444000140b03412010384e03207802442c0000c204d418 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 64577098 1250 64575848 64575853
    0x1c0308060f04061a0304080f07050a050c030106150e03010e120304030306060804110618040e010903020f0d0e0904030909110403290a09060204081212090316060c0c02100f02 76
    0x2140039850305002d15011903c400610214403450304d10894041d40c00100156940380701041002c0500c00131000501c002801103000c4e005c0c4000501e072450510203000c2c200340c03080c1c0c1015400d2000e5001060f51144031101420b1580f910b40318000420b0260102d850a50700c030303000d25802c42c4410515140110312440c880d80c0e0400c0b1040d00c031841541ca0510590b00648020080c8512034000d0606200404800401d01e04070800ea22440c0f001800f0f4601d544071121541c3d440b00841010190100b10b4a05141181c20180240c81d50340c00000304000d0705110700b5072180d082c001c0822300341402002800051f2060315824080b2502c0390000000c0c0d03500500c01211f81c6290900419004080345200d500305150308807003404917840f41c0241001900d020802515255802c03c00012541c50400c1444a0707401143c0f908e030303158180c558480c003010000070014a2107070010072000341c11034500c25408106541c01200061342c6c0380255000c42d80c2c03414a080094022103401d10b804c41407900011458280c2c0c07281d608 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 64578348 1250 64577098 64577119
    0xc100c14030f0a03020903150703021e070209150a09060b030103120e0306010504020d0e060f2a09010c03031107030801150f1407030c0c03060c02060f040b0a0b1c030806 74
    0x2003403680c03481504030300800000d050240701c2d5503600c03907001000032200080488400f00030708509008490025281031012aa00041030302c824000d13080741030f41002a070440c1d24104007050700840c107030742130042c02e5412a0071560b08802e007036618404c4101c064417622404204107500c892891005030b0080c00141d44195644880110081c030940d1890381034000034024180360307407030801804041d420040c008001142c59039102c0030080d408011051041480300412040c50429100d92240460150260311715504a031410405807070050301103541d818405e02e051020007030b15007000c50080800140c1082c2c80070000600005040c2e000808078144c64032140180c07800d00311a2001e40c0c0c00790075642d02902181407114001c4c44001660090100e240c000e00f002040d1464550396103031055560b42003140d280e0358410141501c240c0c1040031f10340c0881002403112036414180c132581c0704030a00601c200801c58940044001c00d4548401441c48440017002c001c0c3d03811140d00d0064403207942241c50394042e44040340e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 64579598 1250 64578348 64578383
    0x61116020405180a0b0a0e100615030506150304060603080a05091002010b150d02040e090d03060e041a06040f02030910050603031603120e031602030105070309050c120c100c 76
    0x8404500078403044018a28800a81d17242c2009110040045c1415a44d03150840104c0000340510340749005c208200041050034240903a8182100c00001c00c10540381a0400889840d01d0340100d680c0c102d0904407907103030390b00c1d803a150024005c5a0401000b0301d602180c00c480142d0400051310091408944031030420f07c481030300f2800c80d0419110690721401c2c203d4110300021110005005219500314054a800e4603404000c0380b8240981c2c400e1a2540032007184440340340e0621500026054031030104056040549071500000f01621603402001000300104446a4659010400e2400e0510042d500c034030303109504546800c22004070005980c24600001d900f4178002c012188a40c481c0c0c0313034a5210143c0c2d41c80445460000b50145102c2541d10300d442903000d131080014003400521148203540021051040c90f0a443c0701415901c20326082120640000d0008900707590080d4040d50380c0e40125079000740003441e195500441c987c00251300c0c0e0480da45158040c4000c8005402068060121000c02c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 64580848 1250 64579598 64579621
    0x50304060f0b090a0902010e09130311210d0f05040c08070801050f130201020a05120a030c031a0609010c1e05070e04030e0f0a090c0306050307080f0613061116020405 73
    0x140b2840307602800500000d1980c4620340c0c0100d010754010f01d1311642600925022803403884080d1142035031100107a0030705040581c4407600781c03072203031110020748202c080d045c2d0001c01c007c041512800d25074001140d8504c0780c00300c95100e9120011481c00910080c10541040c0c102c811a500414945000c0c0110116074182e05010b040d0180b83c9002540034150b54a140c5010109041d010490450140c0701e092800308008014690b5018001c0c80501c0c0d072881c1d14030025046038003158020081c0350030401c05148141c1c02c0c03401c1d102c0c81d071015540541c1d190312820040b20012039500c8010000300d883c1c503181c40703050001c0400b541c41710320680c201c030842516012031100d502800c03100200046c828552403142400c0c030a40c03801040c98080c04042c08e480d100c422804c180d03178515407013030002940c4490070031581c5000c000d10801080040054681c00d030004407460703111031000380750800341110440c9880403c00c0c19400b0384a03003019220030948a145c2c3e1004242c40118140040c0c0c861401c29010440c111002c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 64582098 1250 64580848 64580861
    0x8011a07051903090816090b03030403050601060305090d03060501050a080411100504080c060f0712050d0912020c090c071e021801230a050d0203100c090614070b0c03041103070303050304060f 84
    0x300d250503a0340d80c40c00c042c0b40050503c01a0230fa4041c00140710000000e40100403488c00b801d0540c4000c1103501c1e200c04101c0c80c011002d08070b0010107050100c1004a640c1200840701085d0551400350398583c1c070f40c14490b00d41c41905e1a62600030b4032001055200c540d120380a032041d80d4a02042d1111640001c04018003400340340c2c60085404800c00140c00010b600e1000b0301480042800d00310b0411110043c110f003219900b101c01d0300c000412101001e4029414070060081d00d60031101d090030707803e114070341d0941c0340034607031005044192411042804184c404003a003a500c0e070003000840146510500d01588031004c0c40307400b21001c40300e10300c1120407800a481070380303624001d480f5000c000c3c50b0104010781840456403d98150050410480c1d038180c290280804007070640c0c50707900982e4030782240100b0281c410f12800a0924080c0050030004411000c01c075004801420760b00c1d2603488500b050700c521240012120781c1842081400420035800a0141d03206a01500c4200007441801030850b00b03a500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 64583348 1250 64582098 64582123
    0x20070e0114090705160209070302040e0601030509120c010b0a0f060807020a110409020105090a09050601113c06010306140c090307050105030a02070503132408011a070519030908 78
    0x240c0b41d002900861145020700106180389600c0314a11816030042403505070152403d0b400241c001138103001c2c045c224a1010340018080ca81002580b424440c1070361600d514125030901d0000001e150340c00701e207003500080340e0040002e203a000c1e065600c05400519109030b1080c400030071b100400241d0b14a0001c506404250f412481c504c0c3c10a80c00410040100304584080b410b00009210100a5450b0800500040c001002d00000c1c01e003071020001d405000d40700c0100010360301011041e11003804c12a000300c041c6800d140f110250300c446003003202d446100c550062049100c0c4400000c14400700390818001b00c841030804581c5529145d2602c40503100da4060207030140c1c403810040020f94404d600075980a1002c00d0014100111a40c0340f0341540c1c8280701040c3e1040880c6001c0c001001c01d082780c440b504200502140084510703a02c0541440c90510071030624102c1e480d6001c4011000c101261140c660000035112074150f03046c0c2035000000342030000e03070001d8070fa200041012040040e11210360304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 64584598 1250 64583348 64583359
    0x70303140f0d0b0405090f0d0f091701090201020f071202060f040503060a06053d0504050301061805060103060302090c09040f020403051e06070203090f060c0d120b06040b09040c20070e0114 83
    0x4041740960b0704c400081809c03010042101c0000400550794007070071407030079038620000c50b83d41032600009250400b0300020454075080507104008156100d800f2625499069a186468841d01c510b0b00d0060b0040e507000d690180a0307441045160240743d4002020b1f2002211001080d0a411f4902c102000d640320081c4d504e5440700410003d105201160702e0540c558030b207000f52401d925400443c0c05d48807194400300f82c0b951001c0326500c444140380502d940c411400c0c07804001043ca1600001d010b0b61003d0000c00355050000f40300706141e1030b81c2d041a5007445d0100029582c940e6a132614540e168422202c3c0000251034041d50250382e600070030303003a02400d602d600850901800a0070454510074190741607500880c1000949000501442850035030031a0781c690307000a038905000d01c02901d1a00e01410700c03a0360200000c1c4110b80c00032042d940407041c01e44000524840074442034952020145514000c1e1440c40c5445801e400d00007800000c0e12501040b01201d40da882e040c111058202040555000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 64585848 1250 64584598 64584613
    0x708100806010b1804060b0c0a0308160507030503090a0c0e0108010515010504090b03100905010608070602010e060a020a03141014120601030f020604031202061506030603070303140f0d0b0405090f 86
    0x10381608206413050000704000b44440d5104c8141403594030041c440d9040740c0044c1101e000707050b0000d000c10f40c0401c3c0c060b00c0100c6e41c2c5c3c81c81c000600b03a11569100500303018001c804901122010000b20744020b600007103c0600503117610000c1c40a0600744240300c41d035800c00340000e44d00540410200311000068560f1803c050a0003e007002420751100456058400c4c00003260301e6402c42d0003410030f0a07000304000182642442c000c2c50800c102500501c040d03a040000e84045d0322400201e00703511a08400d00140c0320181910100d014110f5000601d01d00511141400041000844904211414500c60000000904c800c1c45119440e2150400303041c0c100c140100003181c0001001d12103648001c4c1060700d0151296100c070105c0400030403000040e8841c1041113041c082030810700341d95802c1103901c1820762a001e4002590f440590200804004a82c0c4010701050805810b0b0382803100d1003007806e03880302441c2c40001d00a0007002c2c695841141060045075a00c000441c040207603003001800340c0044c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 64587098 1250 64585848 64585867
    0x150a03060e0a02130518070335070501151a070f050a12090f270c0302040b0423090c07060e03091c03030c0503071b0602090301050708100806010b 64
    0x3801045000d00c0c040c06002102c100590303d000b1582041582c0240c00035450408240c840b11001c45c00140c01100d0307104039403d2000c501c80a070610124400300b1030403a071401c800300fa210154422280d21806041c004244103080000640100960109040000102907910010150b01000752010806100010410500800c021421000007a40941d0886140795031a99a4045599410485400240108800f88081c212401002009008a0602500c05401c40c0e550f0999100c002c400201d489035540d415100c4a40281c040e01c00420860481d80d85890ba6914040d000d00890f0700710307068034130300310189202c80d140900d0260701802c403000072a07003082e450350f543c0002851090500b6800384000c0c0100340b0749650388030b2190780302411482e60002c0d8980c28500902501e1052180c04140401402046100d950100040c890019a8a10041f00201c1c600300f0400911400300061b4242d400c1004021b28180c100c1c4296004444c3c0362480c407140da5035035100b1600e0324002e0045a40b09102001480304 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 64588348 1250 64587098 64587101
    0xb0c090a0b0304050106050a2601140f07020a05010e0c040e150c0f040503060106031b0306060f1404080106260a02010f03050604020903010e011b0201050912130807120605150a0306 79
    0x140641300d00d00008034503441300b00082007483c59502625118620724190000c0c00301d40b40c0041c200b1b940c6e00c402400085190348000d840c030744004004813000300c8540001a07a540c404c024610016400c14000c026500f81c2e448403507203405824507854040d508182a51600210004144001d07242c020410002a29900240d0b0001d5001c0039040200100c14400491150f40520143d0300820860b100020190142401c41801d8508070001500781443c001040084940003480c801d03030300529280601d41c02c1c05c40e032010410350050f9000f5101641c42c02c0c03404512185928012404900c2c1c5481080e0701c1500b090070103036104004c00d40280000d07a10748140d04214004c2e0001074215000800260401c04004040b03421142e0005541d12241e45810811280915402080b03880e40464030080c000c3c0d00c3e0043d111903498a801c1c0180c0b407034880000c0c5d00000900e0300300b64400900030403001e60308806d0750703100c00030020100920b0a80f151442c100210700c0b500580084600c4c0824060300104503185075444030390 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 64589598 1250 64588348 64588351
    0x2030d0503060328060605190e061c1a0f0709050d08070605040b041106090a0b07020a0f0f0602070b18040b010504120803090c01080403140304020411040b070b0c090a0b03 75
    0x3074061140f5144d031503078040152054406030311529158150305100781014019520180d03c0f00b805101404a2403813140310080c2031100b51028041916402c0d04c4a20102e001032040d14002c02248400740990020015420005080c100b040e204008198445003003011113502c007a5040b2010444c40da104200d5802d00d10114440c9a00812209051414a8854070180c0c0c0044400303e4400a1460400080004100c4040704005040d1350480c2407040040100c2d1041d0343c20f0240151407540403070410215035810502c04003404a456030048460307580d00700f07030101501328069400036000710040820358a01c1c003c00d4440340007450a0f001440c0e0b0800c0244802041d503a91001c1c10800100408250000d200807031051103403281065581e246445039505061036119858141001845d40034000401e44c4814140704440006042c03980c0e90301e940c0700181c0207104e441110040c403100844d00003407055071100642401b90040b41c00c124a0340d10b10240084030312564480a91103880a1010f000d480400390145 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 64590848 1250 64589598 64589611
    0x2060c190504030204060603150f06050405010c0215120a0b010c020f0f0d1209090e2d2d01181e03050c0a1103070b04060509040504260301060201140402030d0503 71
    0x1640b4164598011a080e9003071078200c400070a8443d1300c11700040b0840310b81140280141c02401c08100c2c10710500600b41d100e1031040c18100101d03981460103540e90903902901d411410900a40c5e101601e940411058038101d030300c0c1440345d180802ca19155405441d00450b01640281001c1034020b840040044460034441129001031000e50684002985c1803c140707000c3e1541d03102d805001d4a01402541078844498032116650886200d520104c090541d03290200e003c1c20342000040b1811403a03c5182c1b080304504c880d00d006035200000d082c0d000030380b0040142c4880b10005d2044055911041c01c2040848100501965001c000300800b5880d040b100c900d058840c0c40c205151000407c00d0600c0e004089205903103841c9410321010303a900e0f040000070020803000350342c0b5080910740040078200b4003500c407800f4005c2c0d171500005070030001041c440651440000101003421050703403141400f00e4000f4050140503600e030406a800314040300d400c8512495008000f821000862a004c4420b42c01c0038009 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 64592098 1250 64590848 64590857
    0x2030414060a05090c0a0b04050d031704081c090f0b1302030a080d0608070803091c020612060a06020307052d0601030b0403020d03020306030a02010f02070b0c0106031202060c19 78
    0x80c08055081402000c0c040c141044001c03d5500b400c1e80424100010351160a100702c800740030410403000070006131000c0b1041160748010780801d60400b6110040804008070303014807a082044100010741d40601200405941c07170307100741801d5900c400c00301e49501c0b00240503501c540761040c0001c2c0e1000011588008829002c982040e03980c0e01081c0341c5051658111504440410300b402400000d224100007800510020044c152911114644902c58980124069421000e100c1c0c280d21111244003c0d4039030180c0020703614441d0314645d9000c1d41003641c00900c07420707400303400090951000040d540b0702500709001d404000300140c4001c0d01040050302c501c00e0084060740034450080c003030003134134000d50180581800515103450003e00300701340800c400040c5441032060044c00e440000324a0044d03642800c2020300ca4038010781c01e901c0c00c04107a1240d03490395000184010f1411f41034020000701ea02c1000b66030b0102c4008074050741c072204125500458000d040c07050301811030501954020144143c01c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 64593348 1250 64592098 64592123
    0x150f1b030501080114010609060509310b030309011205100f030803040302060f0106090501032c010b040b09070e1903080a0302030105030609070602120c03130305070807060c08030a020304 82
    0x20040846090540000820381d941e004001800080c010184c0348112100c69920a40c140000074040200302d0142c1400c11034046046901070315516208202440880e0b02001024648440400d107444061480403200c0c0c24400c244109080001c1914801c260503100c81910801c2c03410001c00070a03008240d20680300000c07030005441001d0f824003202450280c0c40499a074585400c0180c40d01c040034010721403903000c46004000f01390344184030314140c03002480c0c0071481c3d0017502c0c030941403e405010380c90000480c8041c443d42c68441540000c00c0e0900903034007030040e424814200a200b2000320f0f15000468a9030040d580355141500c2c41d030952501d0521161511900c07516011841d80101d00306101182d80000180024501002829031005c02d4900500b449402c12100035201e5040301d105255151000c030b9001b400340000d005a416440a007020483e8a60303072810050380c0c0b05414402d85425000350600420401c0c0700341440f298640d0042003030341c503503111415030314001d40c4001c0c4240d070604520382 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 64594598 1250 64593348 64593371
    0xc0b1902040f0f03022803030f020c040c08011806050d1205120708180a020d03030b0f12010c030b010f02030a0806040b061602090105060a1e09030b04080c07060c150f 73
    0xa0103070003500340b50b850703c403240e42035206010a0002d2000d00311008a48609241d40c40381200003c8002c1d250302d460459051429081c0582c5032000322a0704030352003802c01c0034150800e644500a1303070403660980c8501800d111458280b03000c40e507060180700e81100c0c0c5800041c01040c41c40302071070300900107803a189180c20178500c030008003080295100f00c0052202d40074011a140b0f5075101a800c060403c2c0541600c00d55640050011041c0c62401400c1c1900d03060003620750798880200703260000d400342401051510301c1600038001c10502c944040483d280a4110303142c2d5205085524080c1740e2a0011403900c02c102d0300646d500b00717004148035401503d80d81d1414041e02c0b81005804c4440074a050700c0e41101140c410807000d110160441400344105100c0001d09651026808003002280200c105620340c84180480d18a80c1c00c3d000600204200010b02003088024801480c2030a00041030303402043e100d080458017160381003006482c02038004045100c0041590040442000b200000981d01c01c960 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 64595848 1250 64594598 64594619
    0x60901022109010e040e0d0809010f020d020c160302030601060804082b06060f09050927030a02161a03071107090e010b0f091602010b04060e0402100c0b190204 70
    0x8152001d24000045a0300b001560810201c102050048038103200e0200b0015005035510303141c40344441080382c50b8010500c005001e61002c180148415415951032141c0b500e100041d6103e44000c0c1020f00c2171003c005c200035045110081a2513005014001c164a880c50880e04041c1c0a0808c0c2c8203800308118018200d0031084100c010010480d01c081d8080b1031032131416040700c52550101060004424002002552042000082d1501200d140070130751540d0701802c501e180c0612104035100d80360180159102c8002025000010460342165004a40171108a4846070107200d040e40c191a98504089401c034243d0286600009070b00d480140044c0c442c4c480d80c50b0045030f40c40304c4c603a00d0341c0f5201185081009e014032002c0c07010030781d105245050000081f4040110041801d249042c4801180d030300980300307402c0146a003500030000d1111584928403021030a0f410746c2d00300e10414200c50240f4020703000d00d400c10545a00400101e200f5038914800d82442c0300422804807516600300000309902c0101e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 64597098 1250 64595848 64595893
    0x102060403050d14070c030f08061309050309030a03091a0703350c0a0e030a0804060807050d0906020a0305010801150509060109030c0306020901080603150112020a150807140901090506090102 84
    0x10b90741e4039010801b8034100500441e00c05501c0c1001c100140003002001d4840c64009802000e0210000582c0b00d4641001411405409540b680c14025002c00d402407691009000c03050718040c040c2c0c2110501125180f1034144941040103000c595002c0d031500400340c0002c601c40070710400b1243c0702100c0103181c00c02c0e03940d14000c44142c80b5807a000304491054503031164403e01507000540c018280401c450304c8202c110f013700d20420b402c1001c00c60000b000b50344140141c0d0001c0c4c00c103d205000c40034452410401a400800d04080028a03250000803049c005000e20b2941c240440c694401c5a424141400300c40200200101d0510809440000000d81032145071001503008078001a02c81d50385200040c034030710340503013107a00c254080041040b00700316406206e4111113811000c40810400c1e840401d55401c160343c003c0c004484000d00e11303504c10340c00094180c07140c1c46564415103400030540b840852801901c007130720b0018080f12414015410b040c1e00600840d40140121004610034a00c03103400c3c4604c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 64598348 1250 64597098 64597111
    0x30e010305130524070903031209080903060c0409111602040f0b13020705010617100f0b040905100b1f030b0d120f110123060406030203070609140303090102060403050d14 75
    0x2000c0d2070440c0503500c1802c860b0810f10030706c1c00011071851920020400201c420900148a40d5161082d04000c141800c485000d07802800b541c0c080e2900ca440e03840640c21501c50707010b16506141e5643c034a282880112205030243e80300c00d40c02c202007a000c0c0802811a8419101e4403580c41000c0303451a43c900c010090502040d42016943d22543d1900d142541c0f01580a507034204034401a81c9844100442c2c404d1203210800c4001401402505015019068105980d90042e1404184070180700c004100310a040c219400144005030080f07060204c0703440000504021080340e10300f0001c1592107a0450800d04070300a140c802c0032500fa45400c98002c80c0030000c00082030706034000d401d81c1c50304907049642c1051410020045442c0300c0b1b00920780ca080c00b0454107501c43c1084001800399a0319440000a550060101c4080ca07461b60400341900b0100d001b10050282003c50310152803030004204c66041d40107078050452a21781e55420340d550b03000520441212903da103101c44040c4c0c2000d904902c69074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 64599598 1250 64598348 64598383
    0x4080c210705010608030403211806090e060307062718092603060d030c05100501060315050607030c0f08031e0f0f0105090705040e010807080c0607030e0103051305 72
    0x401c0d16103103007100c03403642c818101c0c1c1d0014482040030035102da000d81c0584044003041241140c1e00d2104458400b00004049241800e0b80c001003903066004002000703440e0711005242c1540c60b410105507032100c1900c1131000160040205984407820284180319609886000c0e0310455103405103207038110b00c1c0b290400501c60340d5070205410301051202c1900141a81903444400840c070b001c501c020303848020310700ea000c0c00d210b1034030b0303802c044c411400110b0701c0f50840190344e8040d2040d03003108040c10342842804c00184c1031501140d0341064a010120032550010300d6a85806141c0d98259103843c072012041d5160245010701d0783c046540c0c00011841910864958001c0301d040e0050340c1c01400020341514400f1914004000c2066001071100781500c1d8101c0b041011580c81050843e000d20490b042002c440b40100000102d0078000503401082d200e10788140c0b40070100810500c0030a02414201400107164209400825402030340b08a07040340c018051842c08003000e072038962500061000100606 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 64600848 1250 64599598 64599607
    0x30307050c0a05090f0402040902011202030f061e030a0b060402130305010f0515030d03050a0b0406030c050a082a03031b0a0201110313030201030e0a0506010602150708070804080c21 80
    0x510b0b220030308001034482110004050300300b000e80c040340010000c0000740a65a10880700c0256030250306c0718440000107000645d0b803803801780c850003120074050b90080d0003079282c2002862204504564802d200e030018004181065a035200c41c405d24001603d183e40013642040400c2d500040c074070742d5001450080c030004c40e00d030303054070510000c96000405000d070030895828040640d90700440c030701c9101e48092a000c2401c0c1c0b2044200350040160380e42050f4810b1030729000104001040102c0021540708841085941e5070301d000c05034880040c1c003180d60b601d0085404d481100d601c0b4014600000e030010b801c8030704020640f0426641100820160191075004004100071583e104030941c0c09034900c24040c0d0304040408c90400211901400024181038031211500e84a000803c4282e81d4241c000301207408950b92800c019480d15009503000c44688049400603c0c280d004521049c050040e950340c4a80c55a43d40d00d840015800c500312250440c040c20450302e00c00312a40c1400703159452548101542d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 64602098 1250 64600848 64600873
    0x4090b0108030a0207080303011d04062a030e0303150904110d06020306100c080306010c08120708070f02010e070302120f1209031608060c0f070b0114040b0f0a06050a090503030705 79
    0x1800d0103540000c4d500da00400040c410740d512140c6110101481c01c07603608207031312246010005040a0170354843720a0040001d040c841070580c50b981c0318488180c5041140e101c520580b240c80c0d1104880c2074000ca160705141c521503050581d41c19500500500700110a500035a00049000300c4c040c1054070020340100500c0322602d06040440a0000107040030280100301e50741e620664000204524140a180c0c07003104240304c142c00c12200c81e02c001c100740010501c4e00100c045c094100948552001409200d40d034060b5a00501c43c04d0380781007048000b804e180e031540c0d0800510b500c1c041010b1100303016454000f40182c0040240b401e0004c0e04218080e1100c1a500a041c5009410326407000805082d50040056040c045401500f2080240350160f07940240f61a0003802e100e1101e00900750000d031800060000641100c0d80141d02c0b00316018081c42d5005001c05c0002c5170018101035114080850822010307005000402c8032910342d00304042c070903a41e140024156001a507080e21a5003010340c0200c01d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 64603348 1250 64602098 64602103
    0xb07031107032109080706020d150f15050f1801110109110603040302070f030308060a0f030b061e030d050309010c030606050423040203011410050408100b04090b0108030a02 76
    0x141254a031102034200000394800030907505220342898a603101d02100c104410450f604103209083e0400c117030b195a00414a0580f000394811b10201714160b103446c0ea180340b400f043e2a400001c5903039048954a07401d007060940010116010040f400703014040002809000000001d06920700c44102c43c84c1100418100240c6540c0a010006c9010b23403400045070300048902c560000f40c03110a6440585075500c6140c00e1f4540f92450700680c1c0f01c44018040041090384c4900e001d40325003c1a0380c1d21114999900000810610500004052180b04400201e16003030034800034280b00107940c00107810010b074501003428201d42c52605400988000304104c5803400900400003001800e160402c201c91511000900034084ca0091554134111900d04103400d810851310518030b40401802190382e03503901d14000c62a10703000840b0740c1c01040d101d0300207000c4502038000d41d000c4680c13890180200505c400da400004041d070301166540a590f0384040408610101c015070b01030007401c80119540c2c0e4051001a1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 64604598 1250 64603348 64603361
    0x30b04050c0c0c040b0d0314160516060c020d0303050a0b04110705010e240a0213060e272206020a0e09090a020105091e130b040b09010b04030b130501090b0703 70
    0x9003d542400311407117076500c0300b9050b110200d4140c036082000864010f0002158850300c2002d050030004c00c401841442800305030300d10300e107449901c1900026036810341594680102d2201039802a030314092036010034017a800c515800150305500180150079180081d00320340b90502a15480034003c220041005401d1185c034042d07060400042900240d18500c5161544030601c25548043d01d05005c2404010207405407404c0036401000b2500c000d84501c0020560003610007100d01c1002d035506a9030940ea4220785401c449520140f440720340d990b1744550a40d801e50907400d12165a03101c0503050011840f1807002d0008581c590740d905140141c1c42080004031900a001452150800705507000140c5e0080100e408408090312141c1141c00c1001c4d0078818424840750180d04a54a44245d00040910360306c8a000310300201d404004551022040c05040c182c01d008414890030100010300105032404400380e0b210042504441190b001541d9841c03e480d8215001c07100070102c082880645074140c000c14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 64605848 1250 64604598 64604623
    0xf0f0f0c0604140d0f0605090105190e060c0a110a0506040209010b0301120204050601050903160609080d020601050d050109020604240c02030d0e0a080f0610050301021903020a030b04050c0c 83
    0x480c01c0030305100000301c407070316642a45032042d80c03484c81c083c04020544441c00c3c0a1078000508104a281142800340648001c588135200505416201c09600c06640b08811000b80030f40001c202c260b442c2c0008030740f15440b00d1144018021401217407030400f03000300210b0400703603c103002074107442c1030501c10b11034500302c10b0700401021881440140f181102c54000c8151140d012513021509488900061341c85e481030b07500490301409541c803a110320000359080031046404542d0348035038460366100c00e40e03210744240c0010801a0002c10041025240620840c244075001c1c40000500c01d00e141c1c00510340d9131040d44a4410b03041d2030200744d140461000b100005800c0c49045c82c0c110301e4940d600007501d0b0030100d4000e0303007030124503074141e0b0840d281da92115000e049041c1c02c880300b080e95080500d9880108640c1020b011840365008207060170103000b91101900350003400d007443d80c0309820603006904084440e0041503a07802e80c0f004581d40c1d5014103402285290b01a80e80c81c070003c15500e08003041140703403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 64607098 1250 64605848 64605859
    0x1509020f0706090206040312110c0102010e0c06130b19030f0911010503090109150e06010503011505090702010b030105070908150f060d051005040503030106020f0c0d0b090f0f0f0c 79
    0x8040d40003003040489012560104000030300c054188005200c0f0f018540014095010300400d821006c3d40100c511800c8a001d2000c950041c0c0c4054012030076654200d48803030403608464100c3e1001e0401e04060024190410700c9040030f6901c0e2070074081c0d103421249000d078401036a00300d8102c7c841e4161140700c000b01480142409110350544035182030380d16100b0600d0403c500007000a01c1e680080d4885e407032081d40042c0144900314100200f42c041c1400031440c42041c02560700005103880e051090321030400d00880c42140c00340c941804c0129141d4000c01a8042d5501c40114266640d400e20982c0d11030081c0b42c864030001070a0070f000e546894007101d030130307001003045900780111050407894407940448119610b415400240c6005030416030100325203c0c00ba82040103001c208a004070186050740c0d1254212109072548580c0f041da00c481c03a44200d0b40148003804284046061030075420340c4644c080781166001041076603a2482c11080e08891080d5801085410140e01030500a480340002c0403941d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 64608348 1250 64607098 64607107
    0x1060903050c060703032405120304080607140c070312030e0129010302040506040b120702060106050a0c02120d020a060e03040609210c03110414040305121f060201150902 75
    0x4410350b0740c02d03801032418881c550114118007014800d1708402c10b803d14145058040c180380100c01100340d0811300a2512803921107204c450f104e60004140c0d41104c252000a0040b500c40070720580342e82841e4202c40e903805208010003420610304001c1ca0004500c40c8160752015a1426801012242641100f44099042500051404803406604400d01030141d00c0b61301204104001130b0000e00c40c56100c01d401c0107002c00e00141c400050303006030404100660400d022a50b4000040b61691000d01680740460400c0c0107000201c0d201d8800b841c2d0480c409840c84d940501d491515a01c0c19000700840001a440702a40d542004424090781c02c004007500001c604242c01c111015003d01170741d0007200030000c480f40104044072800310315006402d030491002000c0c03513101d0400b41840f90034100194042d5080980c1070f00030160450180d4030582e099554103041c400703a5407201e6000340026201c1075000d0f504030a011568800301c2e0320b410080c0170980002602d610790065010180a090380041c118510611 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 64609598 1250 64608348 64608353
    0x2030604030807031d06041703010305030f030402061b010c02010f1a0409080f0f04060206060f1c0309030204020c0114010b1207050d0f020a03020c060a090c26010c1701060903 77
    0x5846600300c1da2500b0700c144035a440b2035040b0000c020301881c0b0180b000d84496800302c2c100000c207049019500541c1208040080260314145a100c00e02c00244154410018098600920740156030801d01c014207491800010011901c1d000d84200e14030000b6954132540007004940900c68a08113401000c0140140d00400e080959a008000b038a82e010300c0c1c41e00c280700c003000400b90448500207083c544160b22450380d2004882c40d5003040c080e21340544241c00118081e032400ba000d85500100c000e01502e02c0240e0304075900e504079541c090031401e00150500c003100603510342c00500040a5102c2c0005034101c1d4000d010a890501a80246154a400c1007000f042040303010f080d40d0301202c030b0b040407a921202802064011301c1c0d42701d2000c00240c80400c102c41055450b1f0001c08a40c50000c007203038090740b2082c00c0342040701c0402c90020080074070b421080100315903408140301d074500c1d441005044820760b010040d01b901c0384401098001010400400407124641d00880e01404c00c92034450301c0c01e030865 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 64610848 1250 64609598 64609603
    0x6040606050901032c15010807080d05090316090f290405250f0807020309180604020d18051e060a05060604170705030c060c070e04031403070e1503040203 68
    0x30070b04041d143c1c08003031081c0f03800c4136061061101594195419141280b45c854440c14002d02c20b41003800f004000058405001810310b0a44d101c0d54050b0402c2d850b801c43c251902d60186d01c0e0782c0c2d018040c001039918000c5015403010000d009001c40400d800a9490b64402220880b600c1c0c12180c40f14001d03210129007042d00861302003141074070005504c0d00c903c46c040f50089543c014001c110301060500001c4c0541c000c804040048440c0c69401d06504d5114090380c4a0284400b0260001c071802c90f1450165008110141c20400103007005103404c07070755a984c00c151075200c8880075800c51480c0648042040230440800c240c15504480e40c04841d040d0540e40c1c468030007900c507100d440d88074000708803599180f02c1100c00a10b01d8a42e1840082c2c803081400ba1159904e00c40c55201c3c0c05640c000004a080640031908407600c03441c00307091101c0c2444c001c41040c02000c1d00c02e40400c00064190085280c00c400214061000c50310f894090000b408100140d40d02d03c1009a01050014002c0c440140c400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 64612098 1250 64610848 64610857
    0x61508100e03090d020d150b030c0d0b0402040c050906130302100503060d0f021c1401200a033c0506060f09040207030e0316030309050d050606090406090206030f0604050604060605 79
    0x484da030000c6600c41d4000280034416182019200384086030402c0a134480c0c80d8446040d400c02a008d6a0030301c2d10035420030120031242c0c0340241006c80d000c00020010316055106c0c0d1402c0320b003800c0103800e1540810114800381c0200e0b00000420130ba103030003481503203045030712a0a800c109180080c41c52034503901081004030b036000001d0180701850364810031584c0745a00d80d48496040c6030410f019450900f001072059030002012401c039460542c54a0700c0d441c1c00d0724540c9624802c516034514100024108400400e5402d80f45802061120f01c20f166510303640b031400a9118001c1d682040303c021a03c1c0006c01c884001e4181407041000304101c80c2905161000c2c5c42c5e41c0c40d000c03140140c0700e81050805441000f490306d5107581c0b40c0128403c2140001603092500f040d02e0003640d441500c0741c2c070782c0c0c00d1250a60703a024016109074000e01c0050040c3c03401001031680107200d0035000ca03010705c5075401314035281c01c00e640c0f2080100030501085000d040c0b07441100ea11a80446040c05140e00d4404050200d118 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 64613348 1250 64612098 64612117
    0x60f01061e020102040305010c0512130b070c05070e010e07090f080709270c0f0905060307151101021c050a0209010f080c0c070902030105090907060f0e0a03061508100e03 75
    0x4a141d600048074000c0d4140c03001542c00a000307110f01c400c400ca00503c1e5612002c050b0007085503c0c400b094414107003a004010a46d80f00310314420940351380e081a1011681c034101102c407485080404583d06445a0a55000300b00c03928440141c2d04024001030040e80d81c541260740c242010701300c2007144900020341c0c801199810640003a040c00986440c0103442008103000341c1d1054101100410000c0380c0341791000b10741c00d185580c0c60154884002d20150380c3c0540302e440d8168030103401442001c5090b17606502000300c9080140060061174405420398010f802d694480c62a41c07211002041a00d0082a42c003088402046107490880310000e40b000200401030303c100f0002200040c808090344044880001c0400100e685480e942c01c1250042d500c00d0080c2401002c15401040408200103516070640308180c84101211a100a046904400400c540c6500a02061001010481c03034490761001d0005d02c41e20301c1046003000d4400c0d00d44012a101108030f02d03d883c1605513601404001c0c6c4000c03d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 64614598 1250 64613348 64613387
    0x1a0f06150d0c0c14010207020a1509080d0f020d08010b0304140304050301090807061103010302151c140601180605090906030109050313060e090103020f0906120105011205060f0106 79
    0xc4554003400c5690290100400c51140751459400c0300700c0c1c001080d410410b12502c0481e03c82d0751541546030a0b40200500290400f01800d41844010074001003100c998006141074100150b0741c510a514001d00d441041000c075418241340b030350050b0305004c2c006814960741410300b0554074088140a582c880240040d002440741d202d21100008240225030040400038000c0c42003501e1341c1407007002980400412108540f504070003011401e034000c19070303049a400501030401d401581903012150b60003a40c036488403281d10740260420500394405c0828100e22000302c02954541240050800e9960a9203520701400c1000100700d40c0b54080c04035526400140c42410f0319441e182c010901502606200800b14000400d524142c454100a041c1c1180c550360749040042c00d240060010250080c00040e4000442d04019103140c20305911640d0442405003001003114074200071b143c2152020382000540c62503915010382400b41c00c0021640040c01403920b02019450040064500e0780c65410884100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 64615848 1250 64614598 64614619
    0x1061406070f02030f0f0708010606020d080405120d06080d0309080313020312030106030b010f0e09010b0313020909012c06060904030c05060c0a1e0e01030e07090f091a0f06 76
    0x42d03091803840d40368050101c07400c0903000100340e511040400032900c4e251140ca140082c40b154140140ea04940a0382c01038840048a00003c88000d480240141c4061069039414024941c01d40300038642241c0c1040c00144030703414048420b080c40c2178919854205030a085803540410000012a600040260446203048880d8408241890244d4103ca6460080440009889070301900001c07c548400d0780c4051400031400d40a45801d8150f0711420b400090800060042038051002150841000005868440c510f0b60006076400c00031609440a41d440303807001000401d20880024055503a1145d00401d030403403200540e520800101158410a4100080350031705010f140188103094102c4261412480d15209500e0342d980f06810440000d01e455000c0411071124420344184c0c20b42c50f645405c11904c105004501504007008041580e000700038000907000441c0c8102c1d18418001000032131180310506091000d0241c0701c0c58038a00440e48030410238029280d90751280e00c000c0840e170a1855 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 64617098 1250 64615848 64615853
    0xa0906230913050c28020604060c090b0c0d0909112a060103110f0d0b0a0b040e010c030b1201060b030a09030306050a0311090c0408030a1d0405040b180106140607 71
    0x1403070803200c6081c84040c905410b04c104030829200401455801c442c005200d2502e0030f2210302004811018007005820000125000600070f41000003019620b01d044901640c50385200c00007688071100210aa9100d40c01c1e41c0c45150300f0000c403d006007600141000250707008807140301e49120381e021f581d200405c0d00741d031a10440720910307112401a0b2140708a0781d4030741c0c5a00d000e2420041050096120b0312a81c0786446c002d25014040842c8258070100e144240e4481da01e1a4014042c82062141d005440d007600c91143c2c0d60911900d0002c14140c7c2e404185505000c0504c60000c80040d0081550390419a0511000081c003044a401224616000903030003240d0074110014982900a6a4000d134107c00c000309201c400d02d0a800b1941080364544407a840d90881d00da018420761081070760b641c00510a50103400d00410035008249500400d0311810303d10700c00000e080b41da0480f400c6072a011640240080d0100c103a44400c0f0940c2420020002c1d90700b0000055080700c041f183c070612400002411808 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 64618348 1250 64617098 64617109
    0x50702091b03090f01051311010c02031507051210060c020d0813030c0503010e0d0801050613090c08011a0a0206011205100c020606012c31020a09062309 67
    0x11040140ca01c096100d0409890440d100e10210401d00140d40c2440d002c0342c0750740346040815416035801084200d900240100544010156000903a418015440070a240201000c4e905216444070b03513801355140d496000007541c010014110070b11200b0100814840c6a420080f101c8210790101e42c042c02180213031610840c280701d24a60340290102d610070000401c06240502e070195035048000348100a1003000b0b041c0c3e2075042c0d086050005a455004101a0074854010300daa60f0b804c0e20380c500340b5515210300b041075135030f030b151000f000480c05001081195881c030500840d1500c1c0b001502d1804d0100e50000307580c1e803818051200b2240d00008001d041020030480340c8904200c100c014080900d11110203500d40c0300c110b484c0360200d0741c001390070303411100d143e04012a842803240c030012501c0441c0080c40041c0c01004004441e0415400620005964000c0b82101000500303802507074a409090b001450040079030300100a128020814401c489103000700f00444000410500f5203e00c0341400091 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 64619598 1250 64618348 64618381
    0x30705090a0b0414101701060f26010617040507060f09030b090109060e0c0315100e0112030f080712151e080613080f0a020703020a06050706050703060605070209 71
    0x38980381c0c1c000f80002e099011040940c009800882d249809040341c03040684aa00b445007032440340401c160300520460703008031110f020001161500030203e081030b405062520b01444550041d810b0404010008103502c4415403201c114090b00040403801c2170740d1203d5586e070041c06240180b009030144000554450319228008541020b88100c5600b06038554034005c1c4000002500c6042c1441070041d0103800000792001000c3c4050000c115030000c85903002d00f120341c080c11040c0301000c0310710005002c4040000481c0070f09403040b80305421842d640740240003080041081800e00c803080307042180b6903812038125000144840d101054520b8040c50003800304850740c00004010713041a520342e800d00b0941680d07100f501e04420031150562180103c500d0a40b0207094000e1008004002041040b000b9070b02a2180319168012101c5032501c1e980041c11010f016081680011404114001800101c2c0112030b046441c40c102044100c0c04e24400800324450840068040c50004001c0f801d540f5201c261603 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 64620848 1250 64619598 64619609
    0x1e07060f02030f0d050f0114030a031404080a080c0d1727030307030b120708030f0d090206030408031906030201051918080d020709060612090302210a090e0903030705090a 75
    0x182d558110a0007044014017042c0c540f01da6008210001103040c040742640b00d0000342c070040c000e1070700c4455560201c4003980d00141c03441c1c00300414000059111000c20a0040c094480d05000383c644d602a02e0091805c58000c40041c10021900c40c8010400d82260840760400c0020041c00302401c000c90944100b000400340d4000c0501c400401c2100c9650305901940440c8411a4401080900c6468140d610700b11030040300c1c2c094208100c00f0320032700c4100006004552002d007000c00e15000a800180ca603810894080d9440303039002041002050b514440b00c8503806918108001050658000803c0c0d40550041005042034241015880c50f0040310034141140034061071010140d283c4070165280e20b2481c2c3c02c2c9026106440c0301240d109841d026007810740f000d69898980400501c540b15029008a1800b6030643c001c00170750909004070b184007032500d00c055805180c0d0b0740c1c0140340700400c01800b035440b05041846160521008410120441c1e42000c002e01e800ba460754200c8000501220716544203 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 64622098 1250 64620848 64620877
    0x901110a0b01080f1c03020912030c0601030623060405090f1903021612020d060f020a0e0a06210504031b03030608060a020901020d0c050102040b040b0702031e07060f0203 75
    0x31201040a14018281a0b078948010b4134121040101d40310f6032502e07107000445410a22100780c180d854805c0e800342c054100000d020150344041646a1800c6a00035552510940c01a000600a0128600402942d0411000c56400b00540c4034a583d550900c0a000640308035140c00100b4048642084880c07505c6645038140c884541d00d108204400c0403501c407040b40035006104003c41e1076080600c000c4125210907030380140000d50b030b40c00c0043e0064030701c03003c44003907a5403039580510400c544040c00303030204507407241800d06100d42c0821020010685c400010449880040b600200d51403088100190f602c503130101d403603101e62a0648951090005141d80040014008402d2542c940c101c0c0040b158188151340e0651180c6000074164410305407020b0140c1d0103101d600c001e003485a90b0b02c840707050140340018203180d141c1c02c070000c1a502c00d17405140c01302e41c08030306113003540780074040035000402019103120a00c403017002d4161110814810f0000b40f00030301409209003070003481180c61070301c81d450341c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 64623348 1250 64622098 64622113
    0x3030f0c05030f070e1f030627060915051203040918030305070201062403110a050901030b0303180d050f060c18030c060f090109081e061f060302090111 67
    0x1040707500200d51080030501034401241e120707070003108061082c039000303800e10f5016460140c1c41548810181c0c0010704040e03070390000203083c400c40307010300d080c042d844490207070700032050820242a640d154000c00700245c0f405d0602c11808a000c1c2e8100116201a2440550410b04070f5180c2d046001e20b03070080c8100c0342841c800000c03501c0740400005010344262803c02050f104ca2001300c3c01c0311014003901c0000e15400714a03d040d04e01203640300c62034801905c2c0c0400c2c1601107583c0340c00c4540041402c440402e002040408081da094000c001203480d05800640c00c242010441c0c0400d281c560355003034000c00e52404c15105201c02803104102001e001002c0b981c0d9070800c1e44411110f644840510b4a818003840340244d85c134039010480c40304208008003524142902107044100c2c6038401c0002a0600101200c0081e4080303050028000c040c044522074510705036012030480c245880144889405031303417098000400d0f4001d82300070007912403900e401a264081000103031448002d9405039805403107000c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 64624598 1250 64623348 64623371
    0x2040305030715020702030a06020d09051b0a060e030a020d0c0317040f0b070b0a0b01030b090109020c1903050708091305090a030f0e03060a151703090406270903030f 73
    0x6000451140548100f0403144201d6a01240211030700203506800645d004408168036401030f019081c3c1840c80001c039003220f5036805103009414030000742c1014010f03d042c400c0b0f14003e900c03c8003c040c28200071082054050009454900c2200c000f449006100c50b030354203100014044101071039002408201402060100780c486800a108140f0b00f0190902e0115081c50210152440c0f0f030342c004401c02241d01c0c0c01c42c14401420200c07091604041e522030070742d01e02e80c2e03460107901d000b04035030600107035180d178038943d41402c1810b0201c10002e80c2907411000e500196100c0110307440c107600041c00503100d407030031400294600c003d20080f6030a1402d202c10710101c03510100f40324010510030307240d050b800c9140003810b0714030306c041448041d815000440001c0410481e50414035411a0000c4c882c91229203485e030070072031702d07600d04421201740d8070110390000c0300d007060b01ca14000742460b0f04030b40780444580b604045008444140594419480e10141c0017010701942190303102440407030003801040700a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 64625848 1250 64624598 64624603
    0x6011106010e07020a0c0602060a060504020f03071211070602070c0e0403020d2303071701080d120209030309040213060201050f1006050c07080d0c03021603080301150e0306040c03031106090304230402040305 91
    0xa84d80ac0d02c0c070a02c0c00e00c0c00581e929080c802c42d20309081c5451860309607030f1000c3c01a00c85d0052042c010204949030301c0c8050410f4541d02c020700945104810040e15079107103060500035841d140d00320b8252410b0100500020a4001800d048800c48520706510405c3c851480c0202500d00400031030368016000c8140440d294212800c0401c041c49164405e000703a80c0c400700c1c2e030780d03441000b02090080b520304252880c2500242d00203184120001e81128034045040002c90101e0344046182c02c030760510b8002c14090a5828000d02d60400c1940001a5290900d0100d503c1c44241c54400c10382808030000e00b00880b0001808054000c0c400001590603401c1c4141c030252400c01090307400c40050040600710708400284443e007000f529003246102d802e607820041144940c03500348001d0011b00c00460881c00b8160b03000c0003d0f9108901c9400b00c0a009407440c500903200c400c4251070302030142c224034104403c800c40001503408661503412110b80d5103422013480400107070717050030725500180001400b00600000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 64627098 1250 64625848 64625851
    0x6010b07050f120d02070807080a05040f0602120307050307020a0c030c06030b01050c03090d0203160801020409060e070e0f060409050405010e0c1906080601120509010e0606011106010e07020a0c060206 88
    0x510159146108040c1a05440312400850f400141405001c40c010f507440700d5001c1c2221620600f00301c1d1030101e558030340f0303106504405014000164005014496402c20f502d84400501040c001003403e004690700049060100a04000812030007200262140d4800c10003608442e811000303080e1195280e0400c0000d1400f28007030140400d0418030100700551052041b0340ba54111a009581007080030300c1000701d40d00c0140c2c0181e0f850f01c12042e600602c2c0e906409058020100940010b0f03950f40b07480400350544003035a0000c12161440c00c100408240c000c40601c0030131500f01d40070700d50b0302d81580c0003514501454103c0c40c0c0b081d10302410001000415808086d4189407402107412503800f40c410000a16040c250480c0c026004680402006002d81802e81d00104141086e200c1c07041820f00e031303d0440c0c4c03044032843e545a450b0030041e6140d1105106950300710b002880c20410b06103003018001d98400c4188190001c40131f080700054050761007070000e409060342c801204401e040c0d45078002543c0380f40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 64628348 1250 64627098 64627103
    0x7030b06090d050604050f0f1f02120c0c10060506090f0301060801110702120604020a140301020403120e0906010503060f0603040f060914160e061309050d050a0e0a05090c03070302040806010b07 85
    0x51074180c112203100000c1c1121b4140008402002903100055400780c3c2181d0a4070192127a503028058a000c245540483e140300e90b54616400c2c3d12240d040c1020780c0342520340c10071002107515090050180381c0f1a48115a2038400c00e0b02d00b0400c040c55040800d004212541c01a00ba55180407168450031018400400e20305008443e16003414191045050315044180c0740250f00c107100510811201e06241300030900c2d03440080005040640e2516070042c80c5448512000025084943c2840585000040e86420641c2860018203510b80f603404a03a01c40c81507400244216004400101000b205001c0e00d20880d6011009000b090720324a403070345042c690070b600c18407180030304482280315000711204642101c1c801d501c0350409861f40810300050b0802d41c1102c80c01217881c0c00305180410002c10000020385025a074850740c0e0f00c1c008100400d0320003070190080c13292100620030800382c0d95885031190401c41c441101c683d00d40794000103400a108640c13081095000c1d81000043c1403482001070600c150 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 64629598 1250 64628348 64628353
    0xf100603060609020406020303131b0303110d020c0a09090609020a0308040e0f070c0b04030e15030105010e06041505160f0602091c2102030c0114090706140307030b06090d05060405 79
    0x7600e0f42045001e900450054500603130052000070700034518a9800c0506078040c50400d050115402a41c1c2648680c50b041500440d030700c0324401d0110b000411100303241c03007882d101421200d04644009901c0040922403410709a44500581d018000342c3c4d030283c00102e80c006c024440c119038034601003038980c005104403800354002c1000a0051941c42c0d11a62107076046a40301980c100180d0344083c0b041001410a808000c0c04d1502e101242e15054803a903224440c1195450b01c81d07242c40001460480d11400840c01035a040c04100031184a048004290b40c0523420426200d60315010003424807131031800b0140c84082e00340c7c003070300902005a0003418100c0c410340725078041c211648214101c00411aa0082810344682c65403d5240d26440300344c04100c5492041e0f17840c0c500601a07a07425900d102800202a004031000c3c807070524030400c44500203204d42c0c28a50000c418604182455003c000c01c12402c7c161115100c0300302da580c0c0f0b0100c6089080007800032100916605202d95184070032a030480322403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 64630848 1250 64629598 64629611
    0x21503100905180706081312030603080c0f07050d051f111305040612020609040b061303050105010513060b0f090103020f040b03040303050c0309071205010b0409080712080105090c09030f10060306 86
    0x5442225664070035600007c0002c00710040d541c0d0240084208000702d0101680c940700400042c032404e00400700052814000d00c941d01940130003605119607980101c0c41049552007010000b0130102d48140c07010403a007907204c802140c0045240240c860b25080141203c000181c42c555442e0350000c01041d00d00c2a582001440e072210024409051415006540080203122100945c5055000800030380d001030001420032034000e040b10400b00c0345420031110369445030010720140c14411121041c001500f282030049500c4c017518645144654104102c60501c00038601441d40d00a40450b2200800442465a11030b80c1d502c40f0902030300103a4048000034281070110b2283c180740815240601d03a20310107000120326105006150020814040707480355269403003031003a50344620403004c855018404580c0d40e04d040303140044a0080080686060120000c018855a11451800356010b440340500715521021407000910f05021242004194481c84812810f50f50340c0750849800c07207100e50000c0c4440c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 64632098 1250 64630848 64630859
    0x50103060f09150509090c0108060613030b04170301030606080607030606021b040f0207080910030c080414030714010626211902060f0109090215031009051807 70
    0x10340d626441003a04075824808144881115a032152005180b01d6190b000c07156910310110700d6800f400c039280400c64026009446003560405412944408100c406a01e00242c0c112289035403089400090304006d807010000d01040003064280355607c0981454944960b524a0440094416406100754a0042d200850101c034080c0c00f0395030640d030140c0c024144499511140c0011442c4000943e94840d4440d11150200c00d9144000d10b881405070140603995000c24041c0000785201030344510406140072241c8500c6503003c40960b401a0340102c400c80701c07040102515155000d4518060705002c4a1010010b20010542c0702d14103c42c10540040b1040b00c100d0b01c00424108044141d200c150000b181c0d101e00d90046040d0f46280441280c03c203410b02c065112924664212001200c0144e80040f0601c2540000d69540600400078401c05200300407456010a00700c2c0f0296403181343c0307620040082940c81c8078080582c806850480c1040107a0b107000e20200340300d184d007918990054050801e01059 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 64633348 1250 64632098 64632101
    0x90c040c111005070201060b07060f060501050c12030604020c03030f0105090a200307020703080a050307031103010602031902011805060609010605090a060c030e2115060f010507060617030301060306050103 90
    0x80040d804000b80c0b1500e519100c0e008050300c0c00410f18811556035000209004110502500c49180503560008101c010709002c0000c07144c4e103070049410b015084c0700b4002e0000d0006001304605000868503070700d0351900408507000c2d020301c0300c070000d160001004201281c11040001d82c101c900844040c103d035140c0f20000703c01c032481c1c07400d090b03041021034448421400500c401150404c095104540700381c0d13502d4503400002e8100614150008e0000000d11001c1a03041c0030f0852516214440c136460f552515a003c0d58a00c50f802044003a10f12070f0440c4d501040c000e40c8410411040e0350806c02a403001c134906a603c407a021551140b04003007100010403624810700a4170424100a00038814883c11720f0819113070486100030480030840500c595110700d4990181d012080120042d02e8680000320300181401c0500c1d404500101070f01820030801e0f917544144110304100c131f003070034203685c3d800c00e42c10180042c0c03809410002c030480032a0014140d00e140000203604a645607a4208140340c0c45000440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 64634598 1250 64633348 64633367
    0x14010c080703050c0405091005062208030405010c060b0f03011505031902030606090a09170d0e1209120c1c02190b04172b12060b04260105090c040c 65
    0x100d4005045c0002d0041d81032441440c1e411402e51000080b5040d604c1002981c90341c826609029000c00c0f401c4104604a0010000d001919110307000e14102410440000c01024000c800549855100c1212005940340e0890401c0e0700407025000344803003e11507100001012081c41954000d10070b880a0008841d030061603408840da000b8041c0c2419260700d001c20106440107899034000503600e242c004c002500910740070300c007106004291500c4d0ba1002c0c003404121020440800c078580c1066181c40c4000d40040100c1d40d20340340c2107415038040c0740c150581070700d409100340a04e0340024261488203543c21040c03040058103842140d0340c4941400352130410f04841218480c1d0f62030003030280000e004d40780181d2051800c0c2c0e2042c00483d0509160320015000b10346454103ca5109002811048901503101c007043c0b8148001c00c00500400c0c1c5407400a04203072145105481005400400e0703e0017500b1045072088070982a0f1000f0b000c103003419002d035502c419024461074412440c100d054400a4060000c45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 64635848 1250 64634598 64634611
    0x19090b0717011203050f160c0e010519050103020310081209040b0d050604021c0b070825120c020f07060e09250e03010e07120b0a0b060f0c0a14010c08070305 69
    0x100c454012913601034429802c4106022480035041c004a10901102892521902d0050017001c52036407600313100081c00c0e80c060304014014a0350074003090350301001203020000c642080ca801a500e071b03646104250110040e802101c194041c8007403c503011882035010f0142c88600319030800c00c1d040f061082142005034110010119001140000d025180c0240c0c6105104d40140304c45d2204001d40e03035a4080b190040b01c024020a0f440014001c40b40b5940d080e0324421003088801022490318032801a000400c0196040307a4140c40b20b8421003035510a02844a03141c00c084103d59107192030b00c4005e02002821a440ea02078401d401c001040b80c03108005803201d20071903c039401d480c84180003049a000b40c0d1350207041d80564903007890040f0300204202c0305004215080084108101070f19050510740c0001e40300e00c40003030400d0408641561490708607090034041101c4155120075841986003040229079000e000c004020600303550010040d000030200d282c095940f0380255031007800030f60440d0342c1603510 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 64637098 1250 64635848 64635869
    0x109030308070e131d0f03031b030c0c011d1506090c0d0e030408010902010219020109150e0402030c070b160912020114070f0203070f03150519090b071701 68
    0xc1450039000350010f4060542c003400e00c109003421880d00c542a10341e40000b899001e94a003001846560090044404581c1d0134800b9518500340075040d45098107010046403001c100000204030503144040446252810100007400042d20a8403192801284000541181d0081010030b00c41d0b0b00516442d90710a4200802418071078480a1044505411490700c1c4130002d5907406101c4411042000640014043e401c00441c401009200081c1070030658203000f850100d10140340070040c5c3c2c0050194013991503030302d400213669001d88012070303078142d0401c1503d0b08107100105010f800c0000c900180340982c0030700003940c090380b0b40081040c02201d40380c400c8800201c801c90305101c103810041c2c200300e200d801490004414030700410320758610740c000d51044a03110b02a00d404821030506102c200018206204050103103840d5448820084125104081613240d0391340c00a02402071621102c06030952881d403c020b980c20034038080c40075640550391400465809c1c0340c031000c08412056041e060710090303050b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 64638348 1250 64637098 64637101
    0x103080a03020d0207060501090501051309020607080306031501030b1b130b0d0b04061404111804020304060603050a0f0c090e03180a0e04200105070f170405030102120a06050109030308 81
    0x400301c0081d0842c80c07000c2041d540030050100450000c0c0a8940a07100c03080f0001a41d516000030041c442d0b1001403602a031604081c0000e000d80d40303441c25940750350340061510781d0b030741d64160002c2d040ca0010105441c04659490010050000081e40e052080200040406280c040104511450300403484080c01d42070241710f0034010031480d500075240800d100171000c81da001c021400507040e41c0c1d04c0c1e040400a0554080318141900d81406501d419520040b5910328106e01103200180105100403610700131078001000c030b001c00006074400310040d0b400400f40e40d10f1416505d020083c0e1344880c5003d50305101d0000d0301180c40d5040d4440c0841039a5000c0c0103602d003c1c51000c10b05040310301a15100c1c4d02910070003000506052010325544224851910040b102d10150300360b908049210b2442410440e0500c000e90001c0d00000308141d51a40041c20403c400c4080d60041213184500d420054055001164114038040e110350154020440081c040c400306860303000440b9080391610015000450400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 64639598 1250 64638348 64638367
    0x100504080c01080103330e01150b0406050403110609040204031a060a0803090d111c031b0803040b04020d15020702010912031e0309081201060806010815060c0f07030501060503060a05010308 83
    0x114425494446c0c00b03100114405150039085821110303040e055030b51580a81101100280030b400c02502c910f4002508050408a000b0818041d41c00700070800d4003c103c5070a6182c0e105810b50318869030040003556190384929044141c05509540d01c0c46000c007a41c082143d52402c7c0c0c101c2e0381034031102c00003581044184401c00c1180d4034002c0d0103071003100100d003a40c005520f601810340d061041d6103904020440c0c0ea8680240100411800a5070409602c03040c200041d00b14021690841d130010303440d1085446a00026031440040c800041c40c0303c1040c034110003000155006082140e000341c0354004050ba0300c162581c0c03030440414000700000d1150f1400c1d03d5410449803450a0107403140b400040c0150141c1c0c60301400d5200040d4002e4074000003004200207035102d54019030040c1e081c0780a042c5820302c410341c0001c1c444e18005440c031a941c040f035100200c4204000d0820900c910100325400695241052402807146004142c020300880001602480c0c20780217844c12070340c0c44a92185041e80c00d2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 64640848 1250 64639598 64639643
    0x605091f110c0d020307140d0203030115030e06151201020c121303120203040e0c0901020a080903121201030201030605030a03080a05040f0203060f07030e0705010c0b15100504080c01080103 83
    0x70210145620060084410700581003200c10812680342d00107640c0c07003d641c1004018902d503590035000300c1d40320108403008140c1c0401030301e045400e240280941380c010b100c4186c0c0a4419034008034000c0c0708032420481100c045c030360642c04560341958090b210500b133111603401d0b88104a0b01a102e81d01601020036a00090340082415501442081c03100c80d4603607a50031203680c0c10f0b404c9000164000300e020f04c01c10014440c01038012550041c501e250a20310400070b03465022070400a000b407180801c80f41240e48050181000e043c010204c05135403807076000c201101d040400c0c00141c1c00a440c00070081000c0c2000124102050381549a0f501c0c1a030301e001105e0084c1400420880c0e800d903100b840c060058804000b00ca0050444502c1c851081c6041f601c02000c80d1240019845c59030b00c100c0c0c0400203030360443e81d15010720350050444031445d0740d9010041c031240751102c2500d42007603c1482900748517602c000940300b81c880c01e8068411040000004441d40d0100303000c058801058180d0500c0401560f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 64642098 1250 64640848 64640861
    0xc01020309011e11030426040902071109060108070c08040f03080408300307090302040c030207030201050606040f0e0c070c060804170f030112050c061b070f15110a0506040f0605091f 80
    0x1311f0b40a492400362281c000b00c40394000d40c1c80700c00c2d2142c02140480821650741e4141103266815a99072032240b424800081c81300c60003404007001c0c022440d4041c003c0c446040100c07009840e000300500e00c595038030700d403c036840d5005100f084080d004007194482c0102d80c050298040c0b2001460510786080f00f0705402d2001d40c00a8080c0c402d114491070004010f0300d5a00400d484481039450043c1c0343c07103807070802900f552401422248107107400c0000f440f00445002c443c41c1502c60006100010390303200c44030f010309031003070715405001514208400206243e0100c0014400c41c030034220740c0101503038598800c820340183c030070b44101c0300030030300c018002c4004462980c10541d0084003204c2c400c01c0440d0200d0707071550100c42c091040007000c0640042e680020450300008050300300e0202c400510303204050040ca640007451008110390700103403c0f6103003c10091022040d801005032443d500b81460328440d856024501100c00a0074000000c80b140c0e0702165813454031080f140c1f03024101102c070b00c07007400134100c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 64643348 1250 64642098 64642133
    0x408060916060f03140103030905041401051003240801061805060f0f04331d040204090203160f0611011404020f04060b040305010e161d0703020c01020309011e110304 73
    0x907617016550801842c1c1c09082d00071402915180021801e0006000a9500e0400321500e6051120700420254481c091145800300440c0380c0007444803c00b900140401c0803c26401005a48072400030500782010350007a021107603142c040d178140324201c000402c103803041240d483d07a0040250101e42504e06090142d500c607028001c1000444c648034498000fa20308242c00811004004641494031040b841d0000300007030312107a4075110441c036841242d804005802480240034541390404181103441c20411420003140d0880185a085c6e00c1d41c0f0b03200c0c0c01424520a140024005c045030301800d00044c86104500a41d103482c84600d9503450f0240300d8420f0440c0301386900143e039550005498161140600091032159001054072014200451715185280b5460014650409001c105240c0d07502800710242401c4900c5401c0c03561240c105030002d002c0c002c086100c650000081158800c010340c0b1901c6075591a4070050354444044260101319480740016080f048010400704022951f500740c2c1c540e8121 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 64644598 1250 64643348 64643351
    0xe1e070e060a1b0c0302090604020702060403080a030e1f06060c080703030509031b010203010905010603060503060106030b03030712020a020a0e01180506120d0c0314070c0512010b040606050408060916060f03 91
    0x9a08524004540f00c1c0307481a211044c905109108510b002c84042d9003240d01254150f08020080d000a00a4400c41c40020401c04000234401925400b0350403100c5030341003003c00d0701c4604481c08003400030340760031104040786240361110200b89580982c03103103c00103401c801400d04208160798140e00814010349010824131081c003a07519040814a04801c21403024400540c480d45030559000035507006800840505061140a10640d100003886a046558915001c5151100c00b0040782c1180304106000e400113000c0c0b00c05420050b0001841030400d4401e41c1d422502d607680300807500d00100e003030081103c00340d00d400b00d4824807000303070304015085080100b045403c04800d101c0540340c8101c1070780c164045600d056490090603040031410382011211080c281c5890125500e00e116014540203940c0f2450300c3c184404d9450209510101c44088041c004105150b25240068002e80042c800c3e0403a6100d810001410a80b01140101110a0b4016200b5859050810640301c0c0604140f80e0400c06 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 64645848 1250 64644598 64644617
    0x70305090a0b16150b06121005040207080702031c0207090b014b020c130b12010515010306030203061303050f1207090801050f0a020f0706060e1e070e060a 68
    0x1000c0c03600106015041c030300310300580c0f601c5468411226041e0b0003009891038078010020507542c8440d41102e0580082084030030b203950fa50482c1e080d07032035403580100da0440e1000c11183c1c100001365009201c041e0003101100c412051886001e040b03820412803020058100d4a002c009061a94101203036070300050401070280d0700080c201503010340c200807001c56240d19a10344c081208c4680342030030002c0c242a40c2541202c3e08001c00c065a40c0d101c5209141c010740340b04540e400042c5866000c100111700040245141c003043d03503d9a8042d10080c1c1301c0e01d2203001c2400d450404c40d8000c2c81100106ca5026018081ca591490603a06403121048001c0c0e05100301005003204641030745005107651007440c20f0b40100d609104100820003407841d0040d0120340c0c0340c94140039800001c100b0b81a4020a1510003594500c13a040302d10019010300d1100503d81401d01e000801d0344111508070610403007034a600c2218a281d413494450002d1010b4403000080f0b00c00100c4103c40e814420028045c0c9055400e0113513030f1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 64647098 1250 64645848 64645859
    0x302060f0906181801030f12120e010b01020601050a030f061a0604080106080705101b030504080a05060609060a0f030611040509090606030d03060605090103090c12031806050f070305090a 82
    0x320f5118115000c0b999110544000322840e142072031200403441400703001d14541c19503a0b0809a1810700300b01408a0203003004001039148111652400040501c000740107107050041d0f250f028100034940ea071f016004000000c10b4038140101490202c0c0c6d00165411400340c0c8a40b201401450004880040f0004411264115403220340041004000800000441506e080c207100e081005c01c0e0803041c404c0d8544860b49400c5980702c1030b003c1070003910300c0610380b5202d994501943d4901c22035103e0449801180f4155050000110385c0390700c02da80503504540780da0340c0c00c020000c03a00a00e000e0260001d5101800b80301066169200140c001c5020300c405140948560000d9080ae6044404528560001c000c012840c141400b41d100c41030340908040c004242010f41c0508a0f009001c4110b04069a0b00803c00500100d00c2d25800144081c0660035030401550800914a0392600c04a20700100700700703800510180700300e0458400b11b01407402d0500b803d601d903070704640c030341d219881203580700c4031000f8040791 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 64648348 1250 64647098 64647109
    0x40908040308030c030a05070309020f090601020705030f03040e0c0c030a0f050c1005090f06011401110109081201030c060908070605030a140109021306110601031202030c0d0c0317060a0302060f09 86
    0x100c103401d04007602c83c61b155041c0410790384010010700806007002d1030040144c541401d809500c400031a2036203850303960040101e01e0880584d100c2580b605c500070b80c203100d400f408401807081c0d9083c10f5078a00180c1e5500b4010075903100300038a0107400d80c0104200c040c4070748074030742c109100401480c1c0145881c00d020140742c603000c4c1d42e00039403c0741607854052000a140c10041600c007006418003030012036142255081e0706207803d03001c043c1800034803008c1c144560400e50207604001c1c0d00c032404c0c0f601d802c3c402401865048090200f150904100c100100d16a405107100100b2a083d002c000c000560618038101d40c241c0005d022514146e8403035061030030100006920901a000c414001030301e410508004500e00709450b440304040c466400c10300d00d0b5110001c80c0e000d041d2a000f4465507040c40c66074408074618420165004018001c552030403c1c0e003580165130b8400c2c180a951245102030b0030104000301d4000c15a40709900c0b00c0341c0c500400060501c2000384c404960218082810446120081403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 64649598 1250 64648348 64648351
    0x91e0717070315020a030518060408090607061802241603030207020402120a05150d0204020309072402060703110703110c060a080a060e010302011b0c0513020304030e010311040504090804030803 85
    0xf4816900442e82c180c1056041c403603e9030201c904030070049808a101e12554580740003900180600d100012803003010748a40b401c86e01001d602090070020440c805440880420450b00101d21943c4c13001c0184210f04840d50020076100b442942ca42e14202509503001840c01d1809000c8040c540c0030f00000c0d01682e5030b072000c0c012405a02c03072640a1890041144811528021b06160000300404079a201c0d070b0700c03018084410030f039050703c1c0140d581d140d10300c5652410855601c0384504130a410000c0c100700300342c002049c80c2d0b6601602218001e4903111030039016236402c903642284005041c008003011034032408003074600006540c2590080c41c01d840100707000d584480d0700440440c1052050051054091240000a25056100c1c0311a54103542c0000d01106006501101c0900103c1150b000e0109413501c000040000819801d100700c00d40d51400c0c040c0d0405c64058000c20180d580d005080c3d4013901440031242c2d02a01050700d41810081080001c1802e15011f80341e000050001100258070f610045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 64650848 1250 64649598 64649633
    0xe1003120e040506030d020c010804080d0c0c0b07080112080d1512020a05030d090b1e0307120b0414070309080405060c01150b0403150b0d021305091e07170703 70
    0x6841c24018018403082da603014102e40c2c003a0344089140b001850f0302040000744076000746800030581e101c0b420007904500130444000300c19850840020302840d08000701554492142c13040c000c241d91260340a8a0304c102c2441221002d4502d02d042000061001e0010701d07119203941c038001110210324200c48900034035030304041e41d1007c20308016019445c00d540c2101c000c100c120010100880c6a0384014200c446030711030b07450a010041440f0304c4010280c41c000403100c44480c0c1d001c3c1c6920380780a000704004503078111280414500700c00b0002906060041700d0005041c2103001907a52604070044004040b802010780350080d003804082110754421000700552402d40c0d0001c9040180404112490380e0303507031701602c1021420481080061511103c41000041ca07501c00a0701041280c00f0940410f02082d0096100441c0c91025456a989502042c0102495411101441c8120b003400303807841039600302e101036940b01042c100708182c0c1b545101d0f04040101800e8400440c2d80396121800464804610b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 64652098 1250 64650848 64650857
    0x60507020c2704050703140a060f090b0619030f050a03170106020601060c0c09021605010c020102040b090f040908070807061103041a04081608190203130e100312 71
    0x280119a0390400a09016400444800552074020b1050760445110300121801a0000d0310008007403201c00d0111000840e040303142c190030640b4507813005880300b031400d004540d09403a01b90030080d5064640301e64400160300c0300400140b43c55620410104a03072800c1c10000c034044054000c0005046041a10740c254415001001030000614016000800702000414000400f10040001a42c00035010741142c496040610442c0128103003c82c014440b5000604403c0c0005401900c04440280c60600d81f4000c5000b04080401e0282c205d01f42c1c4254850141d0100c01804144010718041a0003414101c00501c00140b20310569070b46900c90304032407410343d0781c00800303d1503c05001003401590804e0403001a024031714602a600c4591504100074032540e0300c40020002030400848404440b00340f034900c04280d02d0349130b0701c1c50140300ea58040c10071401945030360400040d10f01d000005a4881c02a48100000c280d410f18000c0080f10b10300920501003024460000000b1a10030950842420107580e0b4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 64653348 1250 64652098 64652101
    0x106060203070215070b191b0e01020f0c0d1b03050105010320010905010c23010e07090b04020f16030212280f0f05090d05010e030c070909020a0909021c0605 69
    0x42201401c8041080300e44d8480c104203090001ea20903030300a502101d1202da401400c0011900702e4010880210300c8601070302d00103401845250003e801d0000e941c0b0980c2221288030104c900303036480f0460011080c0d044192440040d00003014048105407485840607008000ca56a444d407600750345081e442030320041107031040741c0c100f0b960115189802060a0a2035000745e403508000804200c08100d0142c16098082503c0f10aa40540c1d0752446418201000b484401d00803600b0315290446d0b44a402d1101f8a412051501d600b0f0500aa949013812500c0d51030a10503448200c2c00c00511010088045008610802000c0702c008030103030800d032031300c1500303841a0050036070f9047c05c040d40d000441c8144150019001d800070381c4051421fa1190f83c602c0d149882e0002440425078109415800804a508040f44000c0b44440080541480350818040b5140740c0da4910041086900008010b0f41151400c0c1e814800860b107a0018004584081c02c00080c1c00e08100d000c40b5990802039040ba440b5440320f0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 64654598 1250 64653348 64653353
    0xb060d06090b0909070f140f1e040e010b03070603021b1005151c030f0315180612030f050702010c020d06050103031d0d060c140c0303061504060e1908010606020307 72
    0x140311a5001c42a00005c0c0501e60518540f0025421284252540c40b00a919001c5154455034000c0c4080035024040d9014000501026020140f1400c0081c0c011403410075030b020f255005002e4022842c0303015000d01050f07810888224041d601005040400d10010f100141c0c0c50b0f00100715032043c1c5054800d00007043d0038001000030365079a1005003d84103118180a10a19148906c1a1110603502d030500007003007011b101069014000750b072440704002081d032200160038142c60600300380190f0136090420405454000141e01003407084405400038103084080011140204000c0841900506004404450b25800505512a00381c4200d82c2581c0f01c0c00100105600020142c00350306200c1108222a00e040000c04c00076078049001905290701c849200c0511170142516850071f0032821006070f6101c00703a004080d07070399000b519240c0c010341e410b00c019100218a00241c3c2c00380da00540e24100c00b501c510081003042c1144171290f0b0941c44c5000c400140104d0244107400040034140c000d10385501c041d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 64655848 1250 64654598 64654609
    0x9080613030e04051504090219030b04020f010306080d03090c05040c05180406060c1112010203101a0403020603010303050c010605030304090606080c030618070203090915100306180b060d06090b 85
    0x2d01501490500c0f09220342940d01c22004d51010000360f9000030102c04a0000401442c0e542e120000c000d400480040188840b085030584228001c1e80c0d80c600c880600c6004404440203486601100d4119036510b07002ca600c6a00010b000c03130f02074404040c00d56105d8000808076400000311401044002039144034224128500640d407031001c0b201040b105251a80240c107000401c40c00600b440e5500e035141a541c1d0310105490394081a020086480c0e1406605c1c24080703107600d000f0100b110340350701c1501945040c1042114140c03035015051504503441c5070360035181c2c1d800190f003180065481d131001103890740b420000741c0001e14105c880441c0c12880d01102500b08400500400b0707521a04204010640e01e80400c9440125140200c0c0a07480e61258401ca04500500761080c3d40100e42c0c4040c17004c807401201100740b40d07441c221091651903c1c0b4140c154201d645c0d41c410000c07110407145103100040c0807a44052010302d000f13041c2c6807030301c2c4045401e00225200c541001000d00c1e80c0e91032030111030412 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 64657098 1250 64655848 64655867
    0x30b0c130e0124120b0307080105040f02090a0e19020d14071703070507030210050d1112010e07020a1101140309010204090606090308040506090a030b0405010e10090c0e0402010908061303 82
    0xa03005600035543e8a40288601c1d840ba24840340c441c1ca80c4030f814810f0720104664030041c0720000080041d42401d10b400d12010b01d1000e001e902c1070703504601280a503025486201001d00050740200b6610a0a00c10750310010314031401a0b0b4040ea4032441000407a51807203806503940000400f9292960a010a0a9014510304200742a940c424442c0c000002c20008004085d0780c0c0441e001400982d0309402181c1da0321400b10100f02440c04e003004c001c0740300020000b90610500010010510703270b8950300385415a2000b01d400600503444a029500410001300e10301d03082e64011b01d00b02800039640500ca44840e841502c83c1d2046a41c009410042130000d4032400001e09864504030320010700d5902d49034000d0145009061046000150600350307540c8820f0800d0007980e0080b1740350001e181a0034201e0081c00401074040b224003031030b2114075545030244a001c61656014000031541030400d49000ba150702c000740200d062162080c00030412000c10801030b403007208801c100c84641075451400401d403944 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 64658348 1250 64657098 64657139
    0xb07111903020d0204110f18011d010c1103010209060a090312050c0703080d0207060603080304050d050316080a0b060c0a03020c010c0c050105030601031407120501080604020901030b0c130e01 84
    0x150350500043c0d4415032441005034040b640401d605a1404613801c8601c1181c0c1204409840000c0f80c0e91208800c0e081e06c94201400d0301c0702110ba1610103003065135440700c0ca908500080c061004000014000c020a000b010000b03000181005642c402041311071b406110150b0204000766010030810078482d005030400c101600d40207040404010300e0560358003050000a010032400f20f0001c15a802550586062a422040a000317103650380c100045103510541d42035450340200184219007034007441c116405148007051000030007105200440b40030030302510703256a0a4440c080750503a940d819014140012608010b0605400145006450b1080c2824014140001c410140000c9015030903420200d507000e00740540c2c0e03039442e000100e00500c2882c040040ca06500d000b880700660384890200f41024035610b0811160f601c40c003d40d5514081141c0c0298885e021f80c0050001404158400c1e4010108110050500404e41c0f403a200d401c1c0260810001440303124010440b80407600d00d480c60401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 64659598 1250 64658348 64658389
    0x9140901060e0c1602100c05010b0a050a050d0206091201021b060903250c08060105040b03031c0c090803030901020913050403140a02100501080303090d020319180b0711 74
    0x41c03070a5018140b0030001000303219018008a28600343d00a4003610343c0d032807a40101444904910254003820b00498402c06450640c6040d4160f003060401d407880c2e80944800800c942c0c1e400c2c1c51701d401c00402441c290022a04490709000c00c942580f0b4040a250200c8a150005601d0301074800d480150310410a81c24013659000300c05003c900c020200441b405c000007a0701c0581c02c44001490024110011030b0002c100001da00740000700d1080c0418000d05a0b0401c5900b80581d200303c4040540d64010009400341e0118180c072031104100007079012009050190034502d460a598810440c2903030011035180c0f2a81e500018a0132a41ca81070054a45903404407000308510309258800038103070540031004207804840010001c0b1b4550081000e20305c503142c954014440b942e1696201c5441e600300303450f000080e20402403d203101d0390002c41610f07607802003901042100f55514a041310350a940950412084641a03404111568203000528609000c1c1170040b03580a00441804070365850442c0d40d52010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 64660848 1250 64659598 64659611
    0xf091c0305031f0302031005040308090307080d0c0908100504021005030c0a27030c05030f1f020d09080c0a0b01050a0501050a030209040b09010810060f120303090309030203010609140901 82
    0xd03000010340380c1002c8880b074040301d00d403400c3c2c030300c010740b0000c680001c1e50520402e03a4814020301240c2100307114510982d6040c6054446801b00380c3c1e6806070030001001b072070090041d880c81204a9000d803175180325620f81100015517500e81c00303081040b141a0140c078142c80314204400d505048090b100c844250740740c094a940350a20a040c1d0364018015020200602c2500c07804041c2c4000d014400d02c5e10348440c00c083e05035581c1c0740000d201d00c007520a2038024081c529100b43c402c00086071700f2140c55054240c0c3c1410700b0002d0b2207407000750f00104410755603503910700840b0049105140038100350645d10006000342051030030526000e140582c440380c450110100207100c03d980c02000e603100c20446060140c0c440f0030070030000e005011007404041d0000c160000015101c80001400e0050721000c02c0d0800a642e21003102026001c414010b1010748a428480307800000d00c06d51003443d186000b4503100e603186440394000b90955140c0d030701181e45103845500c1d604050310300c0c58429030072440490003040384 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 64662098 1250 64660848 64660853
    0x150806090d05030412230c0a0302150906041e0b01060f030b10020d12090203030c0a1502070201020d0e040e0d050406020106050a030c17030c0d08070801060f02060402060a050d020f091c 81
    0x14000c00500d908010a0800501d00301b110480d280c908802c45c3e40e101d640b6240351741c000540c1c1d2410f101003600140f04100340050907481c0c0e611128010103a020252981d6079445d1560506030b400d1001e41c00200011131a404080b070860301c01d041c003078400da41d940c005038030350210010190346540c203045200e09026120460f0385500011008440c0a035410140c00114031220b0301002003c072030b04043d40501000440c600d445030085440200b0921902480d62001c00100300d14040b40150800207026034800e0300d14040180c0500c1190500c0040200003184085160900d0340c1020781b000c0c4c042e40400c0001c1810311100d074083c0120809000143c4921400b103165440c0d8102040052007080300c140101c00070040100c00500440e030240140c60102c54964241d240010710609049510700c0000740c100c000480c0315842440603101d103640d507900410a41c3c0b0b50341c00f040581c0d03102018034018071104000803141c4a544c1d00161188240b1494103680b10403e00c024800046c0c0c22008098400070740d41c902000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 64663348 1250 64662098 64662113
    0x15230c0901020703031d180105150304050303012114010b090703020f092e020303070e0a06020d0f0201021b030d0c030513080d0603020a0e15040203061e04150806090d050304 76
    0x4c0303a4161818665180e002d044800e180d001a0b0909074000d50450f080d10002c420b00e50501c3d0480784252600300d0311000c010681d5107580001d031001030058204000401c410a030614102441c81601004509208555070351201d181c001c0c80604030099444d99250a502d00e0140000d642c4001241415803809142111400ea0f52080b01030b0540b0452103e00c0720320002c0d507031040842a070035518208024401c15804080e6a9410440d82140007a610307407500d07200c90401c3d41c580c0c0101d940e503400030110f00682043c180c5015207000300c800d0440d0340c07d124611072034203603044100d48078001601950707603283c1a1440130141e0f402c0a0103a401d150401003400541380001504040740c9411204c40d0381c49681000c41076000d4070447d4406588001e003182d0105030440d403030341464040c0d00d420031800c0c04221680d086c44140c0c0822202d940e44010043c26101010400200c1086403120003040064540c100c21904c5541c103156800c0b8110680c0180108003040804100170580c0030b200382041401d51506955148 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 64664598 1250 64663348 64663363
    0x21b01090909111504080c03030a080a1e060609080613030801031218230409050316081204080702090a14062b0302010b010f0c0209010302040915230c090102 69
    0x1c00e81d5555020040c140301c50140007200c1d40c1d000070072180c0c03407003920007603035256420500806d039250040005010b0343d4513000040301d10106964440040e40e40c0c0b00d943e8000107110107180c2c050201d01000001c00d103007140384282c4015010342d4036222802420481d07858686000103042c1c0c1f01090743d22203400c003c80d4000c00c002c0d0440380d000410301d076032521040302180c0304450210381c03040c24106924040b03441990081c07552210203480340000f01d0310794a00d042100b6502c020b040034066400421441076003154418503010071a0240c4d07072186c5405215800182503400031901035603808400304100c2c04501d00080e42036001110b420742030048070460103007000c1404010f048107114901c01c03a6519140c050030080404055081c3c2248481c00720789040c081d01800006001303a0005902188400109008581c440d00c0550064101d000f10b0303086500f4000200910241a00c6e80104602c01d1009990789001d04844010003022881c24207800301a0851030000283c00103045250a10200116903030014410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 64665848 1250 64664598 64664609
    0x140d020d030203131214010203150f030c0303030c0301090b090c09010c02011e0905030f03040612090206071506050307090203060108070806190f140f01020307060207020102120309010c021b0109 85
    0x4004500315203002c0c1e2562251510300070420b00e00c20303070028a01e9015105003a40b41e001d5001e8005100200383d5940c202e200c02c0303038500c51000c0388aa0740714043c14483c074a602896006412165800140340000e0b00e142c00840b48000c050340b0000c014008031071a0300800071005c5081e5014039460078141319510701c6000f0f142c1024100605a204941513a104401d0006903264406c4140d41d5042500d1004002c40214019607001e0f1045040b0817018800000c1246c0c00c03501107079190010180000310040c05454009010b0382c0c011804c4c4000c074089a1003031050700740c42d0155200001c03540c1c03420091500780003507540829096403040c4200145a6001140d440e841807851a007216076540d000c1c0002d03498030344040961039402400f00d010901c4080c4d01115410755803088142d8030171079410781c2040100400b10030030a0042c0c005104074000680a6006460120b1050064030300e00030255902c0344c003641003101c010310240c0d110840781c0c10031901405840384080301c0f40c1c0c05420448607003001a18007007051152 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 64667098 1250 64665848 64665859
    0x17010b09070c0f0210170c040f1406070c080610080604031704020301090b01090903080f01030302030405131e090210032f0403080a0c03020d0e0108180a021305010906140d02 76
    0x85a0070402002080a59241e0003806499081d008103c000c0c00b40e500c02800041c46c0c0d13882e0011942408684060f90102c46203420b4200005040180c44040341c04803a14442d041f0009200d000c0001d07024200b111301800c1c03032000403c41450141042c0400e4230f11540610015003061041c800400e1744000302e880305010b140e02001154a451000c01d0041c04a4003002e05814002000031644c088a0b40110780c0407070003607a921120703441e1101d80c040c049101303100043c007607401084104841e05181484500b402c00a00000403252500551030440044808213030b42c056548200b40011450100329880300c280180c5000c10141560340c2c4001519086030b41154100180304e90030380d048044442c1103c7c061076002d000c10b500c503241054043c00225040f14220054020401c91540c028410080c400c46550140e441c100191140003810481004001e4001e503240500c0074000090b0319160480884440b84140001b5258545042c0c030003120202c0e08011001c801c411000c1e07d06507190f0300d6080700190121103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 64668348 1250 64667098 64667117
    0x304060815030601030c1d010e0601030509030d0e06010302090a0b100e03010e070b03040203010506010f17060d0212060f07030209010c060f1410240f0e190f17010b0907 74
    0x3240d0032480c030940300711507042c0300300f5002004100600349010300f02c6940e90008600000d078400c143c100c800c001d000c2c0706507400a020004006604c41c3c0c000f2908000c4080541b440d00308601030b60001d960381e120760392000e030744032500400444c104186c51550040146008000c0203031518001a102101c40c40705a04000208aa98203540d03429404038100f54035810864541c550f4444040b62950800c6506034800c0d481c00c000941954000c5184645018040c0d5595030002c145401e584103001c0c004d8422078001041c90b0f008401038440f40401c20301e880d0900d00820803468041028840900700170140d00030140188503000580e60000003800e0700c154001c2022034000140501e100041404111100031880d001050043c40300b90150010241c600350118011031b0644000c82100780b5519108100000d002c0d4101c1c0f00e80c079071080035181a02e680007030041041c0b80c45a0040e0450709056040361000c01c20f0381104220a0809466011410300e6400082c04400d0b0300750009003040d00014a4842800607119 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 64669598 1250 64668348 64668361
    0x20a0210092102040b0901080709020c120f0d0c020c060921031902070902041a03070c0203100b011106010501090314070503030a0e010e040912030b040b0d0b06180903040608 76
    0x84485000d0080d04001d900c0442c003085058880703480d801c10684c00b40d8070780000e0491a09140c2030aa0503a42c0400003411050300d0158481d00075030101140311024094140001110703000d040041c1400003400b12120745500342e460101088413a6404108103547c00340905800c9501d910382907480340001195400d0392246480440d00285490007802a014040044c248100d00010a103480e074010041d421654420b0302c808140003248202d010b11148a1494010b00150a190000540e482440ca19022440d1032440e0f011a20b00260320611101c0e41da12032840003150759001001e03806802c1084000c0007154906800a4006400c40c000a028001290b88012170507904129400050501800b1241e0311212280000c01c51610076100ca030005460f07600fa4201c0d450f16001d000d9400b43c20588401d403140b6030500541c021b040310541c03607170040d0f1140c00c003083c55500d50035041c0f117150058000a09900e8078404012a42410880c00b9034903071005030a0244510340041550241d030001d0910300c0d1f180d03e414 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 64670848 1250 64669598 64669607
    0x7060318060606080106080a060501050306060a050d0c031a04050408030c03040302070f03050106090c0c120809280201020f0312012106090606090b0d0201020312040606030218041b06020a0210 84
    0x44014050307509003440010301ca6808103a00c2e0403600d081e43d0307180c8a034881c403140d0416240707148903c9002400905c081001071500c9001001c140c0110b0074039a00c1d00892400d00c100b940d08140c4076002281d9a240741034112100204841e500c05001c440802c8145000d580f21825030001400c0e51000f0315022001a08140c02000000050100007808045441d1380c0d142c06070103010076010b0554203d0a26442110080c000c066110803e984902062031400810204568409004003514918460b40c00102c800c24a14215a5440c5a10110701010a0140e00000e0301d00018410342080c6640100130703061011140c0c02495040d0340b00f8486810411035031050b6103500c4400000080c104900c1d0000160410401e5031102044403e001401c5c011940d04004000244600347c01c040e0260700200450480c1000701d088881c0c1c030500c50f4800080d865120b030003042408056526183c11202100180300900c041d8660300c0304401c605400140860b8100b5a0080d00e0b89480c1000900a51650311040c02c181c1c040e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 64672098 1250 64670848 64670891
    0x100e0a020307090507020714031e100905010e0f030307120b0102010b10020615090105060409050a0f020c0703060f0203100302010f0e0916080c03070509091b04030c031b08070603 78
    0x1002c407604251120f8041d8010701066507240054407c00304c000a10103070b24116052140310060240480b440d11502000d00380481d06a800241d0090309808864001540309511410b0700420001541c2c3d64118403c07450400c1041c4801015841841000306547e800904005030480610b404905100001e006034013420510a24541c81380c03d0101c2d00c0c203801d90000740244154210f807401018103242505202251a080c001c0c6030b0464810441031000e034505400280c0c00c4a401903000844098041c0d580301241c0116040105c5038000c0c11040003880200d001d030307003800d8503407034021840c60516200c0608085e00e603220007814481c400407100f0480303000d54907401d0710107000741c058401441c00c0703200c1d49504036800030b13084049a102408a0600f0040c101600c1c800d1400e604d6051070701c0340000c100040140028104941c070341085140015041ea2480079000452050305800f040d41d05503c0e044018600c1544480c180d161158820004001300141040455406050024034200000a4030012030b50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 64673348 1250 64672098 64672103
    0x603030f0a05040e310503032a07120807020718090204020706060b0307090b03130b06030703081201091a0a03020f0604080109080403020906010f0f080a021909050a06020d02100e0a 79
    0x41030010481c2c460085c2c404060f155482825401c1034640484010030f02580fa80c101611952040c0005600100c0c0c940502414480081c421800306580f65408912980240022100800d0280904074515005550103410006038000b4084aa042405500003090000029070300140c84074412010354445504695000303411860910450751513151542d801d504c01e854810000d00001c00002c0e030191903800741c034064003000d450700c000705c51706446200380401c0241c100d1f941805103000000c0002e91030002000c80e108642c1a1000f00d40c540b03031409007264200051814a1003501c000c1403250ba849800060560740c0c11250b10213000c1020700802c05902580c0c0000100b503180083c0701050080640191040764400c89005482d5650400112400405d43c1c3c80c4001027549003440900c8135001303481082e407181107510010300b4240340c4c0e00100c0b4401c00c020078900c042203064401303002030b08201852001500e0f47d4002080008500000203568038400e0709400140c3d0383d6404040990319042c00300a84158 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 64674598 1250 64673348 64673369
    0xc0f1209010902090903070c140303040e04050604021009051807030f0e010603052803030b010c06020703080f180d1d040507050307034203060c0504060311030603030f0a0504 76
    0x1421290460090289040c1644130724044000980f25610020442c0c0400b9480602501050f140c031070840e00d4082281c41083c0e0501080c84080384800310000958491030107140101035038107040c010b00803d8549800902c082100702d2505000e15202c070540304498008000b8013118542c2c0d0007008030300400031030f03103022041c60908000c41110001504060300b92800f58040d1820881036a40d1400119032440320010140b401c4060000800c1c02603010042801c411b04007000c0080280d9200c104a03402010101c0210b0070b060148103418421498440c0d000400d4507078494480b9014116507a2001416810303402c00400701402c6010a000c00c0481d4881074004e0010310550030882d401908540088842c0000a860b00440d00700d03401450310001d086c3c19840380f82c035110120184203408072602251000c40c401e8210100000016030b2803003040ca51681d690344403a250350038100c000702600c07a841620b0040b1181070051040d16030f800310454003a01c101d101050703a2254089000c3c0d455001d60350003070407002d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 64675848 1250 64674598 64674601
    0x405012f1906050a090201090510020a0c0306020705150403050d090c08030406170705270103091a0a0b0603100519030c08060105040b010203030411010e0f09090f0f06010308030c0f12 80
    0x722403031541c5a001074400c50050180366200d9920208503805084041d002861a036800c1100c0c0c01d0120001c030500900c0d10554101204a445000346504d00381d00271500300f5400140d61060100034000c20012520910385421142016100140030b8001d058213451100d0740e800401c1d04000c4901c292000515189041d6603c0d2560350b40c1c0904950030041c0c40c806000391501c0001c10f039a1003942104d5905488050880861519610300070104544580183c18035550b04400030204401401e503000340f1b040d44940010340e1600b40710140079a0000020140205014424810940840c415101c280c840c02c0e0b400f10744000422540398618141070340f0192420b00307a9031001c12103000100c1c00310b05032181628248041040720700126039074801110050003078128a81c031120fa43d80300c3d0800200c5550010040703107580c2154000545408000d850145607903000d80b8003460590028008840314460040291800790315545940c125407100600030700d40400005082006140c0b01010707102000c494503180c8005 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 64677098 1250 64675848 64675873
    0xb03100305120405010311120f0703240801060909080708030c090607050c1c0305180307090204081f0e0d0e0a031202150901020301050f120304080303040c18020405012f 74
    0x50383c03050140707500003800c02e001803481c0c0840c1c0c1c00700c412402c0b0020f102d003001d50341d00c80364003280b40703020f0416010161205608107400c4040804000131544034108160814078241c7d9a07801c441040c1d1090a50340d04004070b54002c41c6031981038450b542e4220140940daa59074458400051183d08100c503409080031841206024000840222201c002d4500050220b906050413078140c2000000400090040010301c120740380000480c95007000180845120030344941220050b0780260300034800035403240c481002c4074143ea0090982c50741d1001d804100b140150940c0ca41c4404050002c038041c0801c05002d188aa1500c20011001310707040044024880701c59840207441d00e105070b81302c0c5110302581000c0b44074a401031085034100c5500070b1001c0d000c84c1c44a824003001103200591415240000d000018002c01c0c180000e520842c825849800d01c0d40c140180d22140340d02740e1b801034003001d00c1817000f4009642c0191000003484051f01c01081d600901d0610210ac401c0e811800718141e01509028954 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 64678348 1250 64677098 64677133
    0x3090703170403050f031911070902031602120f07020120120408060609150d03020a050f0c03070f0b0307030b130c020d02010606110307020d05160b0d05070c020108010b03100305 78
    0x1a2881074081e901c906945c00b9495980340141c2c0c5068400104400145100c103001f0031001c01c0c00840441964101c680d00c010400490b08122610a0700c1c81180085144840e41400b100006500940285080842070342400b410740c010010300034180580603010382c1c0128003150b82907070f07080005400c948640c8400f54507148250030610511041d4071442c00072600615000560070302c2400205002c010a03454001004a4403c0038072007a015801940052000300394180306030360280c0c00d450000e011424110301890301e85203065004401e510a0f50740301b4094079030ac0c0d5040381c0e041400c0e89800b003568000c40000801e03c1105080180d222403800c0701d0140c3c010340100310480b008500390001c00007030359540000c0e5040c400c1c18640300c010390000c00c0420018909424885002c9025208403101e20410302c811140406454110200000300400d0800075a50b1034014035a1095451030840c0b103950199001801132070307040c0580d150b006004800200d10010108c40100115007010440d2107088a1164248 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 64679598 1250 64678348 64678357
    0x306060c07031b140d060b040e0601090b03060105010507080315150304200618100512130209071d10030e01021305120c0d03030b01090b040603020307020c030d05040501050309070317 80
    0xc50220f440300d40000c42022804884062a0000d8039502880ca000d960f0030000f071010261441e4455540e20030144082010801079018003141d00001600c1c00b0101d040500c0e10034142d0001d030402500300a6500015000816243c00c05208202503c0e1280c0010000e07100d0f4940782e50319010305401108000900000b600100700744c03050303410b4001000e105c1005000541c410040410510303141c1c615400818148401c04a10002142c81e00d2400c088070403003a8150302c0b0741503401003442a8851904420f51610210058003c2420b04004d6201c01e51440c0240c1d04140804603103104800f90038150f0082c80c0260004565007070400c0c02150b40d0344241880f1007003214680541401360b81c181500072010840000d050004060040c000d03144048280e4048001e0403217140a01e04000007000d0010741030300c0f044050300162100d13850143c0c0368900f980c0020324005c00d040c0301d1442503010103003c4801d41e800004440658000703203003c95982d5200a1100d25002c0c6503480103042e52944400d1100c0c01e45040050b2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 64680848 1250 64679598 64679633
    0xf02010e060a05030f1602070b070f0c0303020706030e0703020f0d1b060504062c15070602030a090327170c090115090605120f130501050405100605240306060c0703 72
    0x10300090701d407086c01e41d026a001014000240c0e104030001e00c00a0132001c0074121440c45003605100c0e1102d40d03503c8000c41415a803045025078070801c0c0034070800d50980965065164110000e000040c6103400050007062452001d502483c5019010014001c0340c1000400c90282c84142e04807461390b610008041c3d0b0f10601c1040005800310100c61092080001c034407044c01c800307000441d0700720580c40c1041171402d404e004440d07407003808008c0c0c140020510300140d403103415448000540b500003170034090200700e503441c2c20401540202e407001140c3c02c3e84007580404d0b03c8403800f03402d81050000b43c02a00d003416100c00c00742c0c000c3e1410000200e4a0868100c2585148070751703624242c4d00d07680c90080e52140210500810544010000284080465007082d40c4c804194004030702000d40755240c0c6400c5400c03c0c0c800741c9094001c00040142c01101e401240010681a250303648141809900d03400304a00382501d05d841d1101c00404030340d559407400190364849140034180e03040030f42c3d40c0c94805048688400c05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 64682098 1250 64680848 64680871
    0x16050d0e0106032102030301030506161701090207140a0213020918010e0601140f03010b161a090c0f010c120903050d1707030612020d03030f0207060501090f0507020a0f02010e060a0503 81
    0x26132402d40f000c03082d03d048985c4a0f00901c040e40310551512004500884807030204503000c814170784c03d51504c840d910300070504130b074006a40380824206a58100c5050052020550001180b2401615141c1c44071890301c0c0f520f00c0041e260404800094001d100c00950a0b1400c1c25510004c1007901460b02258050300c002d884041c001c240107103003640e150103241544440010103000400128490300002d07e00010100c01030040ea04c00c40d03550b01c14000d600310b41ea480300c1c803a1104100240340104079440c840141190122101070f0b890000a103015070502e4000d14405083c0c0a46112030300408034035002d16841019115201041c0c0b4004094140e0b9403401e09034004501c0218021074040d00c43c02096991805024104090303540a1010030700043e8021030806d6522105c00d00c0007076940c80070b001280d100f10030114035949020024001d5440b4100c00000e1103103400d040c8a050758002800c1003041d40d0200d100c1d80c0340b80300c900040e00c0400c030340240c40b60400c600040419405621400a40c030407015101c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 64683348 1250 64682098 64682153
    0x20910033201060804031404080c0a080f0307030c0c030803010602061504110306091005090c04050a050f0d0b07050409050403030e1c020d1407060c030b03060f16050d0e010603 77
    0x1c044100c0c41411290544034440c1e80052000c0d912480007030b0313840390290500004c0501403004411144d88a9440710752560021303c81e003801d80c58418447c100400c0c0880080408410014280b612803160690040c188101d80ea400803c0006010b8003c005580043c85030342c8940e074426000e03403504000c440c078a420141c00d0a00050038606445044080820b50075901d00b590364841c207100304600302a00c00e6042502d02000007070103680701c282c860700c208071307120245480ba4a000e0500200c04980e4024a2186c02d108155600396103e260044460380d8015104000a8881000030703a000d2140d5046441c1c80c50a01041000340754040c1c018410751003400d400c556580f213104032187d45000d90701d14020016000048000b1200b13114070031140388201344217515490316820366221812a803d0880c0c110101c8e403151521803403468144222070380300448040c411107514003449145418851a0b01c8a400d200010408605866144d840611100c442d10000c00c1891b44134240108103902c90303d500c8007031800014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 64684598 1250 64683348 64683401
    0x30503100b0408060103080703120915061406070f0c0801090605041e051507020c030303090a1e11011b0209090a06051b090d0203030f03010603061a16030309020402091003 75
    0x8100ca00700d42c03c2c40080c00c0c09034211707a200203c3e0f504c24507054003005a1740c04117002d0303807046200b9a041c042c411800c010718030500450040581c1e425602c05030720341c0942d8512420b641c581104880c00998400c210b058280e40300d00d450115442c1a4001342c80032340ca000c0c00c010400440e503111a010760b0260351401042002c100b0341011410341a040105140c000d106022651041040040c5d0414094016181d460105d00003180c5590422902c3c0c820301e9100c43d45a0041c407403e803454035083c800340018224140504c0c0ca6204820b60050542810003200d4070308052649854181421096801800030b01c032070504c440050703910307202d141050360740301c2c5898007260308040800302c12a40b5200c50a44907042580b1103041007c5185034250070303605808108024080610f4420046010b03158030707140028003070309108442141d61a0001d904000c40401c200340704c3d4049a494a120240d607041c50040352407450b83c4045406030082d050f90742d80101040e4451200f2a03095041488070102e0342d0840e00041d0f0303001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 64685848 1250 64684598 64684619
    0x6091a030105010f081005030f161a030c03070e0904030302070201030b010306120209040203100e0a051b06033405090102060a0b090408030a0905060f19110f070201020c0a0303050310 80
    0x2c2c032030540800c5428030001c0c00c0c0c0c0d000d210003961203c40084041d0075981d540000c603080c504c09041e5440c00b17410640c11004030400e00021000500145000342c8110034000e07084103003e10001d03060030b549030004000503880360b1140751041c20928000d84811000d0a15140150180d00000c10403030200307041c1001c0c001c041d442442010308480324006510180390141d005d210b24010080e000340d8240c000e02d64940e000c21001c3c041c5240072881c40000b42603805180c2403a605100b040c400400c840c822819000e00c0c15507907081034030b07003104402640360008904410000810103014940761340c1c000e5150346040006400c1030180035220000c0c2c0a90b9071990790044064100d0364906442d1760310502d0800410f0224000c0d001071940102c1c4d0f58400120040151285842c20342c0444017909440d58100c204594100c03074045500300094008400c4c8003000305213880090314040e001c1d070280c00403408a0400256882000748104050014100c0341406032a4107008080f6070040310b40c0d054080c403a106c005a200c080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 64687098 1250 64685848 64685851
    0x2010b010915050705060f0f01061e030c02010905100218010e0607030309050304030f060903030606020a050601051207090914010c0507050709020901051c09020906010e0306011205031306091a03 85
    0x594550a03420704142e605028000200d200204000c0207201c1c0e0350000310100040f82c0601d41c0906003011601d00440b06640600c0140c01810802c40c0400030230103c2031540658400e01000341c1400305443e00034400803030040c40b280c00007400d0b030f10403814119003c00340c0341d0041060702a00540080d0049901e070056a0504c00126015000707107007000b4210120b403180c2e001000c0f941c4a041960300d0b1990301d4841c400111110380c410340c0c1d1903079940f1501c402c054040c840e400082c40c0d54005446c20881d26100c450306c0b0241481800d005000c2140c00c0c0700002014401040940a07020080141c42d0301d5040107145480040c5103d0312a40c6403a010341c1b0a1405101502d221940c000000d00e507185c02c00e00301401941200001e40e060041c10701c0348064070b18a41e44103070103048c802c1d440000c04101c60300403c0a40c100207406141441514401c144d070300d44000c035016040d2454520381d4180010189400d80c0703140715042840500e55071070300000c6906a0303c401210101c80c0b1160290b00c110003065880304180c4030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 64688348 1250 64687098 64687121
    0x9050303060d080408030d060509101d060301060503101a0a0b04090f0609060611070603051b0f07020405010e010e0106020601060e0906041e020418051012050c031f0c0201 75
    0x500000e905481d0129038410483d129100590915540e44c0d403c500d140c000706160281d158868509100d181824030003039601001c0088007040a40c41c104450707040781f0881c00440312240420001402980b405d4103c0c800814003c0c003141c152242ca02c42c1c03400203040007014070306190604900c0c9801880c294200c2c07401d442c20166190b182c00d1800c54150700811032a0001030030f054880341d00041e80e0b02c0390b200d50030003030000d500c2c2e0b28850718080c00c149042c814180c102d1780500d8500000d00c1070700c1401101003488c03102c032802515618034451080110502811100039441828000041450f1009025050403241101c00c2c05940c3d0f40c0300c030010ba88860090003a200000d1444222011500c1c00721007880c2c00c007a0141c03002130140c00a40c00401040c5c82c01c05580100c0fa00020700700304188000000c10200c980c3c1a600b000301d407c1045065400400620032801b070b0310b00028458090140c1805075104141000302103a988480c080c804c2411205104200c401d070b9880e150030f100e03c003801030080c01122030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 64689598 1250 64688348 64688353
    0x5030303010e0c03042604030b16140708070c030c063504020d020a06020714040204180b062503030b04140403051c020c0106030219080705060d0b060d1401090905 71
    0x5607516000f010a4000410680702c240d0f90041d07240d48071b40001005c0c40344400d901c000715941d40c19804c02d105a02c1001c1c0081400100584100c03803659408089001d0380ea00070040d29a40b2240fa0901a640d805400740191501c0d108107400020000114a03550494a0640304c0c102c840c0360041a841c10030511036803501d04a40ca0020301031080c0c2c0d40c0700030943c1c018801461200002000d80104660341d0240c0c01040160703000c854148101c08007811400c02c3c03014115410351515040c080b0b11008000031a1240303401c40e4403030341c041c0d115555031415a420319030302521003e0205442c240406181d4034148055001ca4500f075648042ca050a000f040c1c40449041d9240d1020f85840c2e0302103071107610040c0d240b4400049a480070400341800d00007885000f21100022542c2c0342140100030448501144a000c5031080c7c407420080c4050100f2082c003102d001302c0d0002d8407038165456172000707000c0700340d0042c1d4061000580c103402c00000303500024401c0c8508940c00d40744c0c1c0e02d600c4542e04490f001c44010b03240c0d5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 64690848 1250 64689598 64689601
    0x2121203040210110607180503070308070b09031902060a0501060507050a020d0611040306200301080706050d090803040b0f06060a0c02090406020d06171c050706020d1e060f05030303010e 82
    0x10f04018209408000052a1440ca000c510802480c1420403e07030b010300015403500c06202e00300c07038600040005402d088015103200d52039655807885910840900504003480c03000001c1612209100761107c410149514514071040e03908025142c0078101d40c84402503107040d0020500501c11025214901d90103801000c001c0d44d80c2e001c2010086d1508002c1360341640341c828484101011030090001584118004a2050f200342d0711601082da140300b40f4503a03000e0600040001d118005417442c21600baa00b48075542d05402c0300c20f00040c0410700b40284c00c0d40c90020030722013040002c1c02540e2003010300303a01c01103240c0c48000802140b842446400da000501141050300540f80188040e07410520a0000500d01003403c80300805441c0503901c0000d903103100c00403114003030070b05200042502e450700c01c1c0079030b08040b909030140ca9070040c0c6002800350340c3e000c00d140520280030b501070b2091002c182c60154040c002800302c440070301618042d080e00e0114038100081c2d14240001a00c0c16a00c4905440c5003d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 64692098 1250 64690848 64690853
    0xf060f1006051e13030203010501150806011b06050f09010e0109020105030610090503010e010b01080c030714030402120f070617010302100c05030d0603111c170310050310090212120304 81
    0xb26000802116003034402030510401c1ca1020f07000421804800c0000300030700700c0c0781d40101421501c05a0000c21904054001046040d50000c05564000403d00340081e0702043e4030010324200c80c3d60040101400d2405040c401071010072407100d886800c6450080c08144003100c01c00c0c0c2a9504800000d01041d1f00f0704c041081860828440052681d00340f8000603041d5440700080d00791341c0729040c541c0c00f80e5036410380f01c801035a10003040d55004103645c400a2440c1020b0800401d15031813002c0300c0d140002e0200100d000c5644100c0108120484003048510010071880d580f80c45080300d102d9800890000b140c414420644000b449040b650018420741c81898142000c4e110318070140c1007122140000c01c400f0180d04105e00c201000b07180035184507a020010303035041c440d02808140e141d501660340401c0c00000104134003c1d18409407544403190fa200c2d16001b0861009001c1504050740c14020001c05000d0103850398407404c05d05000b15100032800c859581c0342500c41881303040b0300e074010f0030800c0090007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 64693348 1250 64692098 64692107
    0xc09050406141509060f13080d05070c05040207020111150108250b07020a1a03071202030f070c0507050d08030406050f0603060c0f040f06050d0c030c122703020f060f1006 75
    0x10358100a89040e00c2d002c4500000800d0758414040421030190f011014003423800204440071400300c80c1c2c02c15514001880c3c40c2d00404510602c115842140c0014440c411644122085c40300c0416031001ca0b410080282150488110709010700006407080d144284c94000da00701c641c0e0342c0c10a90796129250542401c081032465441102e040c0d0300811181c2e4001000ba00c2003c0420403003280030201d5881e401c003102c0082c403c00c0a01100e40f01c0d18014010311000000006c0070540209990504210400d0715180c45400d00380c0da0361003168032640001d140400e02c2540030003503110700d01c11801000b45075a1090000216070040d02c90390303013517071044000424210362203000f4038100d135100b901e40d8102941c484400021140f1078020200080d00815082d4000b0304900401c08003800c20b00342481340f82400708000b001c4e170b1410f0a800c0d01e11a16000008100d01d02c1a1002644050b03103c161100b000302420065601c0d590805006041c0c800c0d64005640d014000e04210b005120500c050440b452616000701c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 64694598 1250 64693348 64693357
    0x3010c02011802011b02060403150507030212010b130b0301060201061707030f0b0a09060515010f030605060a1214010602010207031808150408120403200c0607240c090504061415 78
    0x240898000411840941d8808000d04000e600c03440341c1c407250003001084040bd8401c040c003144141030041c050b084800038603402d401c1c152003041c0d1455480d0360030000303069071001040e8480207810000000100d00513a040d000801074558902c44a24102130301e10429943c2c01040c4005440e01481c1100c000004080345e480540090b280400400c0e60302c400d4a4100459206440e440700354100621550042d50700b004284004070650300307080040301e2070140850f016204589014041200b001071100c107074010f40d8410724810803149a6180c0968507203074040e001b540044025408174080c2a030021880302030189407815030700300c00c02400d512070000111542c100ea0250049030b081c001400b4210003084a0f03920144140c2c06943c4640d042d40850702004102c0d801c4026143c0180c201a60041041e103c55046442413540300002c200c1c161441a804e03503010808a0280c000581080c00c01032015500c03240141c140d4008545c108a104c0d0343d50000905110000c0f861a0440e180302500340041ca4020040c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 64695848 1250 64694598 64694627
    0x110303070e010c060513031b0b0a0506030304090509070f0e04050c0f2e120c0207141c0602030a050a090f20100801033c05010f021803010c0201180201 66
    0x140c205100d07682c42040d198100c881b0031180903024500d40916038414414420082c0701c50b040c0b24820b0f1507032200d541d0b00600500ca80f0010351540b02060f00c43e00d0800490b80248a02203082125007032107110540c80781204d205d0700401e5640b50070049610030311882c4550040743d00000420b9179040d00005e0100403e08804660340c0b2840310b040c0d0081a2522007650003800b1102d140444100c000302002030010002e03c0c0031403124038a070000781c1c40c1d6950000380400039244034031184500c8203460b1000800c1d4101102c2c090200e003020014007404c03c400c580185004002480c402d11036036885d0340f40c4804991f05600e0150400766a800200003184903411000c10301d2103c88200401e050300c1c072010440168020900b0000103104100410a0005c103520312070301d03400505409100c101d0500c07203039a510100f00c46442c464000aa0b074403000c005003540010b90180700b10b902903440e00c818007103882e00c500407108120302950810300c1822070b2910602c50200c526414400700882c440907900112100c2103a071045 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 64697098 1250 64695848 64695857
    0x80f0402060f12090607052a010f020f04030c050619080402030a05031605010f0507080105130e07091a0d0b0c070f0506040b090d0804030c0b060301022703010c110303070e01 76
    0x200b0105110200091901c0c141480d0000c07110300740320b1200c518046004111100300f0105102c3d502e001c0401078850151a040e0507490320540c54485207140c0184101548001031a1000031031941880703880000c3c10032a405070034410b030a2642d4406110f410303c54040d0001454482003600c034a01390092803a290004c0c005011220882000d6403450301e0346c0c0c800b54202c01b06000c17040180c01000000d0080050440009005010354280048060f103201c1d01801200d01c1252480c403e0381d03d2801c95400001da00d05405d08a0750744a40d1099038100400e15000b001701c0c15402d0400c030444505041070100f44090307100e81000380ca643c41d00f4036980503410840c0d0888840310851191408100d0030020316014500500c000c08160030314548043c6061840f00b030281c02d11007000104004a0b412103040c2e82e91580103030540c4c1c503039540d02000900a20904407140005d46034002090b262006103041c26008000c00c0c0c0c000c000b00b00c070242c801d840b00000c007034141c40107900800001d0440c0f0310072680d109100006060 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 64698348 1250 64697098 64697107
    0x6010c0501090605010b0d150302030a0201030b010c0501050112060507081003020103020a120609060801060806010e0a0c0c0b040606031101050405030a02060a021e0d08060f0102031e160c0f05030c01080f040206 92
    0x1c03243c0a88000307034061590b00c803010a08480da6070381840b80200706500d11510f4121103140d030b4003194031290140b2019050541c0e4805801060340514003070201240e202c0020015580c5980c00f00d07810090151094442d9450180018a1a4051600680330310303800c201e01400d440c03440c0e00441c00795004000e036104002c0b80c64100944200c0314084e01c4050000004085026418050864210b469541c442805580982d004019aa41d19071800c0d402100300240071905001e1001e003920414010750300101090b91010810083c0300703495001000b600c0c890441c3c60110603400c1e004485c03d0159004081d4160015480c01d001490494000c042d110306030300566013401e84042c643da42d49082907004240a80160a80304a041c0c0d125800b00d0740000102c85900801140c600002d60341d0203000c0049410511340c40e040c2c0c7c20700e8900070a0302da1500c5440428203414481389403e2554628074032480c518004202e50200e0b540c50301186181041c8010303507a030a00d0b5580c0540414526002500c16a0000010030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 64699598 1250 64698348 64698353
    0x110f04020f0d0204050f03190b060a17010c0206150105040504050a0f060320040c050417010603080a0e04050c030408070312090203030a08160c260f0a0816020a0b06010c050109 77
    0x8010305106008802e0061301c4030b10344000e211021404518003486074010340d20381d000341204801e0b12900720307030881a030481903681c03540440e0340503846800040101c030a070502008542015000204441c0c07482c2d080c1c40076911007400820494204041650100b1418172041c17050b400c1a0303100c2070380a0001000440c0c00a0a842c010003140c0340c0307400c01d8900a1440c00ea500c0c10703a40c0300c101001100c10942d010440040080b40041140c01a40103003540c3c441c1219840942d840300b5000740c0c000c0c5800004040d80c4404000307015080e5220049820b010720b04081c0040c03c0e4849100a41c1d10454100680c1c500d494041d55085807405c00350112600d445a8860705040561030400141a14481507100c100306400e004800c0301888040860b0002005441ca0910001806444c01c1031084c0300501c82d184c00c10f03148540000a94020801c4480b403000e8042058120350740c0c480d070414010075021400b40e440d02414042241c955410080c05851960a07001013400365101d41050494070b40100000500f080f16903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 64700848 1250 64699598 64699627
    0x1030209090708070807110712050c092404060b0f0a02070f06080103060e030a020a06020901050d0e0a0311030a08062214010f0602150c07020105090a0306141003110f0402 75
    0x2c0d5030036400903d00c1810440102d40100c0840d400c920030b81044a40c2e040245903484d950345050060194001c01c1c4607a2004000b4100b1000a10140082804015140032181400d446070307452031002f2114003890010040703040600c54603007510540012545007400c940c5001905622040450045200c0c442c0001803614404081102030100c581e669549545142481000e43d00e401c42c11000350b42041002401544c0c002541909050b40040c0c0903840b4213695005030707101c0c016070050300c0c46981407142507071030400c020589106061280c0c031105021560302c18030640c2e0703000f004503002c0410b8440b8040f4409152280d8040c154441d01d0101943d40c4490380c8401055440d16402e0590018402c00140440803026810364050316045c80249142400d0200311809290090020f01840c500045c020056900c250101c60359030300d001e00a290401d80d68a0008020701070400212002e0b0480800310b51681e10400e140c030202c9820400c01c05030107040f50b00304140c4c04040503050750310590802c400761042d20030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 64702098 1250 64700848 64700851
    0xc090909060a0f060b1209190311011b050304060b061606150608070504090b0d060e030a080609010e0a0506012f070801090b010e0702010207150b0414060114090103020909 75
    0x1030400341a15040004092094820703d04543e2400e505215041c40b1248030340e0f050301c0c10300071a4022002142c481080302c6003044101005400d036802801707211014140c1003e00b410342480b441000b040710001c1ca02580c000c03090070800240014100f040828041030054100312016007008158038a01501562408800d80403500100d42064a5140c540000038403206504010308081c101a400341ca06200000c0440c856030046941e00b50f40e0b0000035155407240d4142d4000b05e0390140c030401c280642103103540c0d6aa04013003903a60008401500140c11400d107056407074101c5000c0c0c0c02003041c0b41c5032080080301812001300540c0c1004001004100c1c0500c100e40c1e284102e900a907681031b0711401541d9014200380303c540180040380c2c14042a00c000601041104e4115980d112005441d600d40c0f1000f00e003e881000d10281400c4104d025500c0c0d801d41d50750201c400b070072040310208280c284604080d0741c60300c4110348076408074941040409095400030000d1815103030501d001886d100ba540000340100c1300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 64703348 1250 64702098 64702111
    0x1201020c19050f1b0f010c230c0d05010203040c060c0f03030e010216060204060207080a08090405060105040807080601050a061e120f0207060b0414040b04030c03140c0a06060b1606050c0909 83
    0x40484051000e08100c190101242800e1038190b1a540842d1610080f10b14487c400c0c04010182364400c0b035491100703020030f240101c401400160b45040504280b8080e410548080d1600742c51010001484c901070300c584e13080c0540c490810040d1828a843c113500609060405102079502082070700c1070302e8000508000c0c081c0c410040142c550f07042c000002d2611490b80c006c040c1540c041346030980466850b1b4203448032000100c601044603521140100c0e06d600550380710020030320501d003000c25552004100103059034130580d44000c000b030780c94100300e8414402c4c80500110511000d422401e541c4181306a03201010a13002c003003051445080842c1c100e074413000c8103135101d6070b031500030301c40c0c61800d4051298190024005044181801e4954001c5078030081c00c014240712540106008241c0102c51044280e91405001e0b03072613421403541030f42c46000802d002c5850a06c1c20802003105842031b01543c0050040048040e84491996a00c400178280038000003074200c0f0070f1202c0c109590301c02405070700c00c44 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 64704598 1250 64703348 64703383
    0x106030303061a030109020f0903030304030807020c09040209160519080f0a020f0d091104060e0403080601090812090d0212030d0b04050c090108040606150e1201020c19050f 76
    0x1461428018110349040e045002c03412840e0010890080c40001a41d0541d440502c0059403074241100940c4a4400c00c1240368050001000b00024941c002c5a0580701c2d90440c0c00b030b01c40f40e400c0c1c1020007640c0c2d042120029440310075800400c003026024500e51004000608005140284510324039034549403064441c0700003180541080780e80028082c1e540d03004500d00800f58101644440121018040c40e030b40021010340d540b111030b09100d1042106008602c0c040c00401050b07850f21740040c5042e008540070742c0800c0542000c91000d52040c2c25420071151240044c00c0c03564a10600408240d02c04205a03600801c4502c00f44051395030b58100c0c0c0c030303521120703802142e07110400d004490980f840812424883d500c0c0900b001150f0700b0700412118904424602031045550ba840c191004100b203811282c886000541030200c0390741c001944222401d02101d004420203000c001d40c509034803030034441c05081c0d08507a940d084100f004c0b03042c54101d548940107540c0d0314040d20b00c01a00e03201d181d103024074482c2d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 64705848 1250 64704598 64704611
    0xe15070c261c090e0c070602030103080315030606010219050a1b061206051302070204020c010e06150904020a030210050c1c0306050d0b0609130b0406050414060910020f0409050901 79
    0x1060400124503214019940c0320b110403072180c0060403042da0b41c480d280005012400082e00b0501d03900031140b0306613000c6170031501e0b135031641402c0084c1e400c2180c20581c0300c0d0f00c401003058503203070000b60039204050580c014801c41c0f816904403040c51504007021161071084150301d5000445000489103002c50107408101024078005004085900f51961405c906103404010b0000752102d0800c1c072002184404096175a000d58404200203101d040c454100c0381d40781c08002850880081040c0f40900f66030f0758944035101c4030100b048483d440a603002075011000ca0380c10030050514244040d800e912904056080c4552200c500d410316419040c03030030480715001c1900702e810b87c02d8410000030304400d4401c03026240e41560381c46038400000d0308032813240704e0a03800500704402c40b1400c4e0486136409844601c280c02c04d0302d0490082d25050707908a84e00c10022001044850300040c24603ca0000d18005041310100c221100c0001c2d488810301c0c0060020030040815121110b00981d03001e51407840000610 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 64707098 1250 64705848 64705919
    0x50114040c1a04030b0c0c0a0f060f06080c0d0f02130606230307080a110705010203040c1d070c0c0509010e0a060915090f06080a0c0905070e15070c 65
    0x206003082d004085082c10034258003102d4400c0c44165411380e03501c521950350b42e40740d01140104502502406503681e00c18001d41324204880b11405416242c880c54050040290000801c420349480c0c4c0a0285164040d0030590110b203001e50403840654081c900a0120500c540c0200715000d07082070510788004d8582108000a680c000c0c1740140001d20000d024095003036450914180b07110140031402004584000706007051003503031000303503100341307000031140d6800d030500c0c045000c1e420454040c0d801020340d01c0c0008030100105440c5010345e61442000f000e40d52030784025200000301d5042520b03074644410003c116925568002d901800b20301840700d519203040c0d00c1d21010303102c45400038021315060081e0724154011b50319204050303d2032a1301c085400b007070100300400182200d603c8900688146054181448414403007c1d040c0c0750604e01c00d114035a02e4880949000810a030350383d411082e00075280000010442c041d04245220f018298201c41e503841d50350b80b107040000152812628404c00280c031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 64708348 1250 64707098 64707113
    0x6020a390806010b0715050717010f05091501050f0a0507020a03060b1e0108130213060909031b0309050f060c1c0e03070509010905090f0703080a080105060304020a05040c050705011404 81
    0x141034030354040e8030340343c42651740324002c030b04030b610103c802500c030400300c1c1d6854003c060f600f00081d100b031100271503983d54101e9000940030511901d400b400b00c0c00003123907400550481c100344c0100d061310b40d149800642c5d0042581d41d40161051000c2100c14000100180d644840e0703040118081d00307010030721144040c100040100100c01580307640c0031340038010903542d8018001903404180350311f030200d050b415070010441e0b094844050110052602d5400724038803440350321141c0b0490003640c400c6100a412004500a610440b6024000c55141e0b1010002c40c0380c003902103036007503e019050304d080494001c15a845c08004041c4100000c50803050000b11607441203554800384421002440028544000b0421070001800f94000d4182c94100068514a0411504019040a00881b0303409aa45c2c10f0161180d0845410000003410300e000008541c50050300781d80c0110380081081042919040401c80200881c00b60b901c244501440f800020940038031840c1d00004c2c0d041c11441c0383d403405140191 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 64709598 1250 64708348 64708351
    0xf16150503060a061d030303090d14121302010302070605040c05040e0c180c0c0a03090e1005030c0409030e15090a090c020a03030b0f09130b01050a06020a390806 71
    0x1000c10030140108030699070303002d0a00048490380c1c03c1a900f0600b081c010354a00d19442601103804d84000418810308460019600e0409109660340146000503076000707403501d02c200d800646c1502c0d281c00100e4841424440441d404038814100145030200c25a0b0300303000d07200110f400b66047c8421800403c0582014000c01c1446100540642800c4604500107500141c030841200298008407000451240c03900044800d1401c10004840808060340383c01400120b00e80503864140c0d01d02c401054045d0038046408051f201d004000d490081310b2403050000030700b17002d0b030242e04000d80c1070321454aa4461000a54903804120040e40d643c00002013480060340f801e41c0405080c038504810f01310b620f54082a0445174039070518011030300400d11000a410300803941c0c0843e0341712110301e0520921031040c80f480c0070700302c0c4551095119030b07980e4010000090258440d040140e084000f4001c002616000c0e40c00d403009070503403400c0c5509240d4084002074580c0c1030000b42040300d0240180b2014a0821209 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 64710848 1250 64709598 64709639
    0x91005120a1e05060f04021614010903080412021f0204030611070309030201050f0f0313060b041515050c010603050a0515070c06020c0a02100302030a18170306030f16 73
    0x3888040d00c2c0038100b010320080408540042030740c540c00304d600c07550380360480310035010010070030f5455000d11200840d2103034003800202c45140400e90307030313001e44003040c02020f5485405844100c00c41d625a01e80540007540c1400501c218081e100300340b010f00c0c441141c28040015064801600c03142035203003c0046503684810b0030340c5044184178400000303074040e140f4401d50f642840c000351a01c8414194103124003a002e02c21204100100400030398400610f20171240c1c4d80942c0c0103100310400c040501084440710048448a44079424040c07140c0c148031164864a01c41c503107086803070400d030350801d60b00711403164000b1034150704400e80550500c0020000e20787c141c411200c0700803003410304041c0604008030680004010a8022030944059241848000710580d00500294410804207000034020360040b41c2850f001464249201e031034100010f234011002d130b4000540316040031011005003160304010503030343d454425242500d0000d2002d02508414006402000361083d0070300082416010002406 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 64712098 1250 64710848 64710851
    0x806101d0105120a060212040303060b130902031f03050a0c08060f01061d0306040c0510210b03010b03120a0207050d03050706090206090d050601090c0f0c17091005120a 74
    0x1400151000080c220781151000c60365020642c24503070300c4505202007030308007600349840450180c40c5401207000c6148038074400d0740c04200e960744400540d109030140608614100405000c14401d501480d4010b5800c1900204d44030707000500c0b580040840745164101304d4040c0c029505030810040a00c403000b0140030112302611291500c8a1840c00c15441403288070100300103c41207100301d03e074050045421410150540b4581e117005c0c1480b4123071540c18880d150085102404032240103114250460340c248551145d140340320300000b0500098107924844983c503560b1003c2020850390708010600e0401000980552111411500a0300300041a40254018860864207800190340001218012980b010340052080307110300106801d0701500a446400c041051900802e00c800024841d0407a61040424041c14191207412034030118501040f201280e40c0012880000380c0501d0032000c88075051b0826800e02074000c2c0018109184400c550000c0384000a83e0502d0312521451180c3c4190304800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 64713348 1250 64712098 64712129
    0x50705070201020d0806010c080f0a02100b010e0603090724020601060305250e06040f0305070f0f0e04050a060908030106110a0302030307030c0306090906141302060a0507020415080610 81
    0x20b51105103134034541080052410000b0030903800b415040c0300041d00803484179100ca401e9112010550f1201c11441c000d4400c1e00c154884003c0b46005011060700d042e5282504a81807000303000003904061701d4074155018801010440220140303800783c0d140003000503007901250000c030280c203144040e00b04004050400c0104000340d01c6002910031482080400d40328660b24070401200c10780b0300c140481358072a500080004040000704c920b002601c0c000d03410790f060740d039951584030149001032081c0308141c4c40140c0100b2036960500d10459015029105840a00409583d08000c80c2c0314480101c800120100050000310f0780441c1c01e07621105440000c0c18031444a4501039500c1c0401044103007010349901044c0501c41c4640c025000808ad543c5042c807040e84140342072800740c950100001c00081403580000c031340581800f510340003a178016108a00e44000c41c08121250b601040e0140d070815214914642541d402c552414018410503000e0511404d180142d9516000c0c140c1c00a00116081785 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 64714598 1250 64713348 64713353
    0x1090209010e060f06030601021011130e01120305090d0804090f05090303190b030a020307090c14030403050403061a1f02010506060c070e27010e160602060403030b0f0d05010f05070507 81
    0x69110f40d1320f9200300d50740394036a07845100403443c000c00524800c05040c24112040800107114001d01490103412010410150322400390001201092040040841c0222548400709005400502009002404544491120f81c5a0840300e070300aa02600501e5078400120034090710038460160070000070000745186080903404c0341164504681000310345690b5541c80c0c8125502005244602540034054955442c1c0e10800a0700414074211280003141800c200400c000d401c05046174071850341034880a0600382180c54807002004921700a0422406071401c400e01a664414600581420620012200002520001c0c04d540014064602506051007040e08119000c95110b003030311502d1030103401070341d607a00180035014600b40e4400396056038955180c0182d40c06400031009501c01c202216540844600c0d0f0318600c0c02c0c503104250051304801c0204001a110340c01481015000500700c40e2181c10102c00149031080d01e8901300d40d542e640347c040c0c586040306070281603802000d6042140c00d10040780c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 64715848 1250 64714598 64714609
    0x1030617031c2007060b0312040e09150a0902130519110706050907060305070f050301090515100c0215091008070c1a010503061014040c02011d01090209010e06 70
    0x18000d02c04250300ca19640c1002d8041d5486558000c682e00c98181000005044200309075101d500b0548041382080306038529402c00203841c001d8a2000000189041c0c5032014201c2030781d90140001000e8018141d000902d10103c100840c0142d841000005090905204000c1c0403064510403006450071706041020b28200d5480004003a980d0304000b0030586505051040309114041f002002c1e0b070700d400c1c21f01104c06000030f00300301038030041d441c01c201d152a031030801e544140c06102d42400140d070800050040741c03043e420640d040511041011114a2420b0014400001e1a04400300090f0040502d1055290590b5050040d444c0401e180349400c1c0c9007000f0030400c0d203401840901748001d0030301003034599102e209140e80c442d070020381e4000d142940e000b8203400c0b00e50a10440c0e10030311440380880c168030107441c0c05504940042d4042c40300024601309010240184c6070480b01555a20041c03000060801e6a004100a02881c00000d00f80c1c400d20400805000680040d4841c400c900200001030710350 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 64717098 1250 64715848 64715857
    0x90c1207051b0c030c19030210030516050301050f0103020904090f03080a06140d0f0201090e0901021e0a0804230102030f0601090b0c060105090a0204030f030c030f020c010215070309170403020103061703 89
    0x580d20602c03150181407035101401c06c25403000350400540032402c5105503042d0300240c011008640c2010701141c020f8401c0710f25020031700845601800000b103030034003503020303a004000d0b43c0380251021a800303400b80c4400f8441030a400d82923010862042c20820b080b40320f44612000b4004215002c11880c0c01600812070092174100000c004200940c40743c1c05585c01282c40c0c00040051601440540c940402d40c00e001c0d4100a440c200004011010b10355071510700d0003a500d06118982d02c604041e641c90b2203000090340590b07002d03202d6158802c0e24224000d007e00055128801e103101e03000550034500c00042091200340e2001e21240c0c07081c850004658000b10b8003d045138404c80300544651074440c40c81000740706030340c0f0042c244100c80003002d0402d070b04040000d10310350103515403000c46d0100038802c4c0d8070380e603001c0c00b00d500580001001c2908078901242943c1c0260043c40e00017410049580c851307400ba40c01c03000b60341e810317000840d00300115a031501508020708109a46a1031100f901c03011181da078001d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 64718348 1250 64717098 64717123
    0x11217070305040e010308090f0616020f01110a0c0302030f0703020916051b060a0c110c011416050604111e01120b060d06140414010302090c1207051b0c03 68
    0x100901807511030800e640c054004840d101c0b0195a4030b24012403294044070542d40a43c0ca0b4038001d02251900c0d41c252080e000c003850034450f21603002c0e400c104201060410407414013500e5103036810f001b0f01c01c2210b104150f100305162600241117004251401d004000c03d0b030070a0340010420f00050310703245829500141c2400c24001c0c08015000b0a841d980a00080d2200700e002c19000c113041094000b800c3c1d40540305c0c5000070881035070004000c4035401444c440900c456407010080e0005035104080ca04c0c07450b040e02840b10f0814284075031915408554600c20358150307014800b40401d1215031075007900603850031101e010042110110f00d00d00000260441e9044c8240500138106d0b60740150060110980010701c4103a5890383e03021500c00420850042c44462042c81501e4001c904207403045141d01000701b50601c0c6980e1955007001490400148200d594400c24010046092403a5011034040c510716220903803146a00011400201801141160542d01c00301c0d840e8815100864407460360107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 64719598 1250 64718348 64718393
    0x3120c050703020603040b01060806040501051c02060409050a0618020304020307030b04050a121206120f29100303030b03011812110f0c01020106061e03050a0b1305040302060112 78
    0x12400d0a2550500070795034406900b290001040004011500d050b8a06a03806d0383c440394071a44500080c03108449090044503041600e8001c2039017500900c602624a4510042400c0c1c541502c4041e000e00381c03070b402d2380c29603610350b141c18092040f5840388004e82c04003802d4000440c2185880e0300002e40d200d10902c4007400340740751176010038244a02403041d11001604a41180c540c040400d100400c001074210101500710301e000004502405001449541140c010940b41c0d140c203134945401d8601a101d2441b0ba01c9800c1c80510011401009074802d80304500c2c1c400c229210fa07280d41006000c0c2c4004215a51082e40340a9a0080482d004214031080a4200801c1d807207141305010291901c02ca8041c0c00d9155110b44140366403403203c0001d000d0030400f400e03402444002d0365140c09071283d8009084c0790030300388542c81c0d010403520301c240d2006a028511480100700c2c1c1000b000460304030b51805460040e02034803541000f042c50b40400485005042505040e0188440c80d11280c01c02b01900d010940c801 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 64720848 1250 64719598 64719617
    0x1060c15020d09060504030e0108090d050f0906040510080405061e1801020c0304090b120102070507060503040303140a02070b150d08030a0905150703110406140703030e070b0706050903040312 84
    0x920342d480701480f40d9018108010900b0b1600300a404507403042072050010f44032500107040e255010074a8088268540c840038101031020000c0b202c00d821400109800a0051000184595030807406640d6050661030b070011070704160a2850170080300404e0042130704850038030341106000f00a0304682c080600c01d10900101c0c1a00c886a01910410740d1146540c4804500891400c4840d40308400001c000c8400f01c0c03212a130352510b82d09034090894064050742240c10100301382c2e4090001542c0c45842032400007100a40900b03052004c10041d1440d1440c030790301180c0242040200888c07140c000c0b5500100f1191040103030009540704402031402444460080041629000c1a03009071082c558020203681c0002491010f030501c09400f00e44210000e4141002c01150806400840e400d80e1a141e80c1c1910180240303110b210b890344035080032010141e4034074010109400510100001d006d81450711a43c0742c00500305102541c1d00a0702c6a50280c000304810000555021034407100900e003800c2980c40d6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 64722098 1250 64720848 64720867
    0xa0c0303020c0106030c0f180e03190e0a0f060206130209070e040e01050c030613020a09050d0201121d070608010803030109051008060708060907030b030601031713090c0801060c1502 80
    0x500361170b83c03008103149020310010800300301030b49080081e078005000d1686201890030948068580090b880b1038541c1003003100c0028800101c003001000089802c1c0341010740d008201040e07015003294003841e1121a1a01c040c040c86074180203c0e504101300c01c4142c01016004d03000500c0c10503005c0c060701c0c00e112001d180c200c01d035243c44c1c110a0200c0d00450080202e8035000c1010287d81c0d0040310340d01d110304801c42c0c01040e042420300c00c1e42d0070f0b0030890359020612070408082c481e4400c6881c0c3d0607410300c462468400c2c2600e41600031603481050228000f45204052003000340341001a030003007010b01c55448014000444000203a81c1100c0c0c941c1e8000c1103503107513644c0441d03051001d41c120400500502040151b034a4212090380e0051006590f520000d07620308400b203088801d040382c600d0b4103405c00001040803038080b442e140c2c3d00d1070003500c0e003524024201c0240c40028015a01c0381140030740319101e42070035581003e6160300419080c10329100f0740c00c0350782d208120f04c00202c000562542d80411000030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 64723348 1250 64722098 64722101
    0x3061801090f15050c160b06060f18130c05220302060f180603040506070e03030c0f0c0907080112030507030c0f0f050607030e1b0d0b01030309090e030a0c0303020c01 73
    0x40641d04001c404500365503600f401800c040d58504036180e40303410f08020601d200190b004407a42c900010000051003c1030b540e038121a01800380c04150b012105010f03042002408030b004020500402005650250144080c00303900b808400c070801c00c403494000c815000a800c00b085410425403100c032800d0082c070580321440400c01a8001a401150100b901e2440364002d00040c8840414018400c0450707142400b00002c61100b114024000c1d0403200200d0902c038001e684640300a0001420759060a0018a4440c54045c2030007450895a001c0ba05215403820031044468100d0b00070300e4207410541c14200c101071000341c0518001c003000000036501c810705104901503032401d5445201c0c82d230301480314204480c2c124940501a01d4034000c0d41c01040b50140244290039482c003610300501429500c4a00510007010300023407003a0042000300c01007000410084503903010f10b2290703d50003035550801d0411000c0f1461041c0e5222994400c0100224103600511a410000d82c140313000b5a803000d0100e2100d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 64724598 1250 64723348 64723361
    0x60507080c040608060312071406061f050d06080f030a0e03010b01020d0507080c030d061e0501021b04090506010b03070206100501021c020115060221091305071407030504050a05010e03061801 84
    0x40401002003060740422035010a269041d94454044ae40d40352148810088800c0120700301800480c002001c10b80400e00a0f006400100b1883c58001074041d96021000c3c240701800d543c200468100183c0e80e40d03019007146c0032840100c01940200800c0000c034001075510000d07603803103505000c008607004081080400840e4408017404054035198103c170725084020381124040d40c1800c140c160400140c18901c140c0000448030142c3c0200300b010500c403845054182151102600980c80c3c4034800d003c10b004108041c000e00040700055a20319041c48000d05041025024104400c0000c80402c026079001039900705504100740c101c1c02030041c0f600107030f0046c045d18484408102d40c0c0400002d2854000c5580202c5c0310790741000800390200403403210a90300c178407005154040d40a01d0540d01c04029903001c240d200d01e8900740710300862480d80c425015170f0070bc61011400a0030024061040b410714807076101c002c04080c01c04e18002654000000c0d15110000d11403d8141001c0084a01c2d1351400d40042 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 64725848 1250 64724598 64724623
    0x5060a05030c0c030a0906110a0c14030109020312030601030b03061302040f0f0504050606031204060c060c1103072402030402010e0904030201150603051501020307050706050c0c0418060507080c0406080603 90
    0xc981d942c445c01c5000c0c0c1811820303c100070100e50181c544c552240c20118952584c2039010403031101482c10031144c007090822028410381c06640e0f85c424000140c03020020b4048800c0392043c000d0701c070700d002c000041c1a9000d004045000e81c0025081c000c2241a443c002d100095044502041d000307101c00c1107000a20248507103030403490810090005103d00070942901030042501915101e040d2f41d4141c2100340310b14420100050070310703161440490403641c840e0949000d0f1303203030860707100503407410561a40d00900004e6030701c0d80b0b01410442c8103000800c15420540d0030307542c1c1541580b41540002e0300031b808012809002c2c82e440b000141c2014802c1d4009842c00c1412105280900d0300d078032008004000440d01c0500b02101200a01e4907980004203a546207a80030000303180041c201241100c0ba6003012f103001c2018400c40d8451262540c45000b0100c0b448000704034800000102d04014007a81c0340a042d800038440440240310309100c2820460701070740c8860411500689509021070f1a007440503144 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 64727098 1250 64725848 64725853
    0xc0905031f09060207061b03020316050d0e030c0f010c140d0e0703080c03130e2a040b04060f0206070305040c051509060a020f070605040b07060513020a08012405060a05030c0c 77
    0x404081046c541d00441d50380303030361070601d0310080750800d030580c12031000740d5510740608407400c0c00102103031082004112010000c1c4011644641200c4040d2554001c00801c0800c3c3e00084507030051001e0910820700c1104c0949018082e07a418030f1400a082c0c421001003a00b1192221a04908518104281401144c1c4101d11640d41d030001c0e404a9160b80210f0f83c100118240980d0020306071100c00c0409004025104041c00240c140c0c0c0070422607841c010a49100d1643c045c04001404140f01016100600003500d640600c00600400203090910081c0608149460801408041402400c080066a0b004c0e240b01d000c2142c4000c81e403495015180500c0d601620004400786880d0740401d03e070000c100041c0c229844c081d01c3e6081078816015602511020100070b002d40e00c0400ca560300101e40203c4460038140e030403222500815551071054001d01c4103691070300403441812060a400c404118189806041440d003401c00042031445440060002c1090200124802183c003000f2204c0304021300c2e04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 64728348 1250 64727098 64727107
    0x60a05010f050f010e10080a0e0a0803061909091203060b0a0c022b0602040e0106090305030d0510030f06050405070915031403120108011b050f0a08090c03010207060e010c0905031f090602 82
    0x100601f800400c55800350043d08241d601c10001e000021500a42d940c81002c030b0b81165240028019900d02400c9001c42d03a0001100026601c0e401e03110b441c40c80ba01a42c036620b01c0c2a03079041c02401355455940651417030141000200019a440006640c00d1541160411003003c4000400700340103244009100f0240d911001c1e40041010303da00500403a0f0240c56640c005c0d0b030307030f6038020388032030713601c0d100150480e00200a102600010b5901043d40403041c24804409180c0360f881c1d0200f035034400ca604842056484e03060006002003080302400a000c08282031081e8001040b80355401d024078800104422544600d0020640d818025980f1440c620300b4510071035a52040c64174040c0c2041d2400e6440d821003c0b500a00c3c0612810803105020101c410f6185400081001204c4042d00103010140502601081032904d507020f0008080a5000300130201380d24201c014658210f84031151a00c0600280c5082040343d40c80c085500e410124024250401660304002400064980404014065440000e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 64729598 1250 64728348 64728379
    0x30a0507020a06080702060c070c0e0403021f0c09120606080321010503030301050f0d15020a030e0105090307050a032012030405011401030215070212011d060a05010f050f010e 77
    0x6800300c907000300c40c8504000d980d0305064036592800d88840b03005030003000008801000e0780b0000c00e200c0c0d2188400f405001e60b2190400c41c2c10f1000d540807001a0483e03076120b914014141186c20002612400030000e04100d81c001600301c2c2c440e48264130a604c003205a8509114080d4840300c014a40d52066964400e0b84446d000c00050607521243d050f043c80340c1c00882c0d681400010350b0f0683e03801400d4000400900d00070132070340d10a00c1204458011481140e4545000301307001a0840ca60a900c000c141da03000703c1020340c207441005050b0315130703503205004c000045400094000c050903003500700b092040540304c0e408900d070305110b01c01c100c00c0d2150030030101c04601000c004600c030b039003c5c0d802000182000819910100001c6c0700207984404583c02d065000420003008040491005200380cd100545030080382c2515031048500c4842d01901c1845950644240701280e40301c2ca41400030803440d0304022804004407104d004043c0228034101e45640307207034080c98a805004100034060f40318001300c0d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 64730848 1250 64729598 64729607
    0x3090e150a08011404060f02070203010c2f060604020a09030b01080a03030506041a1203090409060506100804052e0e06070e0411160201030204051309030206220213020408030a 77
    0x34000c450152640600000c1c04440c10710848401e070110700944c0c08a40c40f2601d0b2900903205260380400156801c01035072005030703000d11422507181c20031384426100070040800d0001d01d400304484204104001030800b84c40900104140d40d128008940c010707110800c2000403900a070304c3e600024014241c1800100d0304201c00950480501e02c00d9505001694503a001e01c001c1d82c182c00240d21545219004204003890071450480100e40050101d03400e21038540c0000c0e054902903c0c0941e407455a46050005d54200300f00c004c0c1c04144d213406c203000c050600c1d90300d05036200800c0b009289130a48100c10f030907011005461620b40c65405240134807070b41d503140c502141c83d03030700980c0c03000302190045004900c981028060b00140704a5451040e040c46030b0840b0780b6044240042d012410150708100104d055030b00d1f0003069911b1040404005a4100c0c079144c0a032508401600c1e4a01100c0f1003184003082d0030f00c11610154455042e61100301048035400490068001ca421036502408085016200d441c0d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 64732098 1250 64730848 64730881
    0xf060204151e0c030c02090711010f1a0a0b030c090a0510120c090f1412010e03040f1202060a0e040f0e010905160e0f07050d020307092909010c03090e 66
    0x942d1604558202d0100b02502c1800420500a01290003240743c10054900f81ca401c1e81c0c890441d092074803d810852220500f110008400001c4881d66414070040381c100340e19181c55040b40a860781100d190a10080342000d0200414010003401e0020f204c0c031182c0c4402e0f50a800400d0050401444483e0031000944488c00541c442c0e401c0710326200e55003911900c1481c803441140c520000c0b0b01e9a583c20036011000b0300107407001d41500513141c051107003000107092044042114a0324040c580b298140180c80310000389544c09400c604c8040356540015a0303810003202e030940b0003030400a80400101d40481d02908011400c20826440c4c010700d403603010f030190000c82e006485202540e0b601ea080e840c083c01500400d00802c4481006500000e80c0c43e0010103134182c014045081c0942041c804a40440c180c0c9c0c0708403444d50000b100310004018010802c5030b0300c019031000c0711010911281040482c1403c1c001c85c40c841c0e041004188041c4240b6001b6001a005441020741100ca9032503d0016030101c0d1a1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 64733348 1250 64732098 64732127
    0x4080309010b04110306011209050f0319020f0304150e180702070b070c050111070306020703050909091f020906040f12140d080c07150c09031e020d0f06020415 70
    0x8020a02c95145410f100f641429140b107080340b4155141e00c401190300000c00c203d850f6450395960241030114404125807188000004025991060711950780e610516007580040b0a41d402079811301503811000c425a02a0b1310105400483c2440707510044480c0300d0300e519415040001c5980c42aa00090302502600c00c0c00c058085030a40d5544404100c194480c14401800c503942c5400700b0701c400e40c0f1441030000da0311322000498403040e403a61206401c9901000c0b007200401c000003805122410103901c200d0f8000700041c041d08590300c0030003410000038110200c00359202da0016a03401103070740d60000d0b54080d01400304031802880d120306040d41801106082561034040543c03080b10b2205000a13410541000b43d51481015120400d100c80703142c00000007202e0244050020410302c000700d228440210506a8911315032600e10304000e44807020f0340c000e000f658a08080704c0d00140c1c4648005005231648010360b48802003080c20311030024080d80e0001401e820741e411001c44c2c09070b40484003031104075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 64734598 1250 64733348 64733351
    0x5090705010f090302060708070215030c130e040b0f06150a0908160305150702011811010e04060602030a0c02030c0306040f0b010e06090a090c0317070510050601020a0f15050408030901 81
    0x1541100151000c0030f980c4002035010b0010040c100008440002601e2014805404100844602410111540c00c01c8802c0303001c0040110b0b00480d801d410003172400090051a04015141c140b0380ca44c0e40300b805000b00b10120342c1a601000c1501c43c1c543c082c0048031503810b0b0502e15250b40d40040000c3c4907460074407504900d48034400c0c00003420307030444090701c0460b9031100003080c0003858240702c4070541c04010034140555603a0f4040c808107408141c0c450641c140714400408220188800150443c41c010107801e006030300c0c0942c00c3c44080c1d00003080b524044940c0c10b00e80071a07075107031000071318020981d41125014060001400104070b000070340f500440b4807544680c1c107140e0f221900c10400413801c4070015403000c000d601082c060f581e01d51054190074002d40c54040034944940301d4504a594403800b0848003400002c0210900201384142200006d105038180320070704010b00000e50316408508050854030040744044100f000040307141043e5000300a09000c036140501f40b035641da41084403008001e5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 64735848 1250 64734598 64734617
    0x815310f0515060405010807030204050a0b0918190b0316030503040e15030a020105071b06052a1e1e0105060a06033b06040516230d03120509070501 65
    0xc408864041110b2002034035250515103004011a07902002a000c41c003419401c000100d11901c411036441e0140190b103541c41d5540790b5400a1043c120080700c40605007914031070501400341c01c10b03001c4496480403542c2c08141d840603400043c0c00d2543c19280e004c10396003200000002c1060100181048171040c035000326243d81c070700d4400d62038034500c01d05c035660503003001040000560040000c0c05055004000700240003054040244940c402900300c00c02040002c120208201010803004c1031111103c1e49102c1740c8019145020380d95031807580c2065218a00894181c9410703002c0207403680039110000080c0c00540c03202452402010241c500070b018426550020803014003a004d03100e490010b4601d98005004045441120038840c101c000818103103c121042042000b0800b490140d4000c0e8050f00c400714959501e0ba28000903544510380080300da52882e110307180c5c65105124128010f46032042c525085103411940c1c012010f403000d0031a4a041d040c001d032048002443c406a410a07203030075400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 64737098 1250 64735848 64735861
    0x510030501110f0706150b07200d02030703060506030c0d0609050607030615180803040f0f1502100b0117040f060e010e0322080a03050c0d0815310f05 66
    0x3107115010060b054070200308904d0b0001156a80100640014502c1e218070752a1552903044007540802d80c1503503800c8071a00001c48120000d1040315070302604446015107a002c030b13408203441c1c00007440090300656594000801546051050407840300009091560701022460076100800000905984070300c9841e001424080c0640700d1507040c1c4804011b0741380c4032085a1021589440141c1111903403800355034002074110801c0000d04060a9103040100400d0701345281600c07542c50b00c2c1d11504401c603500d0340342401290041242e44100102041c0450041442001628100c804020312941004804104400d12014440040c0c3d920310440bc14070141071030031000d50a981c500411b803013a81e0410405800d0300c803003400c0207038804014510801e0280d41c0d03419580e4148488020280c0114400043c0c4503070144050000013004140c3d41803080050801080d295041050030040d98041c40455820039864440045807264620540b0b690300c1025241c191b44101800c0f85010000c0941d00380000b1510 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 64738348 1250 64737098 64737131
    0x70b10141503010509041104060602010f0e011b050d0e03030f06040b0a030c12140115150207060504090e0309120c03010c0206060609010f17101a1810120510030501 72
    0x112211620300941c01c43e420316080100d4840007401c11580000850040561070301e40380646401025103400003d584c01914015074203903051000854166450f01c540c54050580052080800c1d000d41e2800c11344810341c2e0410740b0000e03c4400001c06451102000b0003c406081202e814031801080d9803e1080065020900c65013480c81c2c00020004001c0020034007034907903503c2d0110380d0280a5480c91034588030f41123007203003140d4000d0211091158a101c2c2408816000c40a40700901e200b071008103007461402c00010514000d0b070103501c032450385074a0849100c49041044d103240708002030050b559500d0400105070355201070b060a50195080c40400d440f0709002041403841040040c214900c1c03c8851001150002d91540102044c46910b0032007800b0b0003e0303c2003181c85902d810960007007050401c0c5210684c540d80346040501142c04000480f1124002e5031f43c11513200b0143c0c2c008008000c100001c3d690040240710301d1550324500020407001d2420100c030102268040c074001c204c500e60000d0700d0007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 64739598 1250 64738348 64738369
    0xf050306090403050d020906030a060f0f0e0601050f0913060303081003030c0b1812071b0501050d09060615080f010902040e04030e1503010e0412020601140f0303070b1014 75
    0x40e800075016000502203801600200712a14440c0303401458102072500140e42500181c6185070041d40d0340134103104514080d16010f014000900200061030325040019030701e0b200040c666410848089000c401c1d03900d01005551810704000d151000b03203000c941c54135000f403100307100c150009441c401c046550003240344100720580b901a55902050b04494668555074003000e440d0300c011503400c0c2c2c0b6501490303c0520550424211400513580c4d204854104000804680b58080b02001001c1c2800c2059a0f0000700b280d41b0b00682d00404078407040141402d1000f050180d002e11a00000046c2803554242c5c8020b101b44900e10b150400343c190790321840018200e02450140900c00c1c0fa40c4008940440d019800940310b00b01c0042c80600411004441a005c94100780d011419985a100c00d201c00c1044814581192072018030003808190324201281100780010703004140610058121414640c600f401240c540c1138101c00c0f0003e06007421076141c201010144141c011025510001c20312a181940d40003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 64740848 1250 64739598 64739611
    0x50312151318172110150c1203061d0412050c0102130611010b0f06030a020d0b03072909060405120f0114010501020c030a15020a11010603120f0503 65
    0x400c03041c0840401401040d00e034100c80a02d0440340c6400c030018110b100f8000c12888002040da440d46042803a0b190543c00070b41010300600080810007a441208900643c1201c116008542910019072000d40e61001c4100024000c000c840402075009901034100208580403180000c001c031b00d40c0d1303c1050361590306480041c40036803140b0096940a101e480645184001c10b000185890290740a503101050381c0e0f4000004a110a000055051420b11514108031020344403c0710024040d40041c2c4a4403000308800901a0b01180b4200c1c2042a940103000a0324040d0460380074a48410f116400344000690399610704920018182c2240030f40340980b602c40300f001c2c110508041c01c01e01000364032114848600102e214080d140c84010109009503110054404040300440d41003400090034038501021460080d4006080c0100060007225858000c80c031207034006854804000382100c1d0b41504800160440d0b081200200c140000050140352840041d295106925900c440554080c01308039545d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 64742098 1250 64740848 64740859
    0x2070f050111070b131809030e061c0603152003070c020111060a0504020a050a060203030604090f050303040305030a0b01030615030c090b0c060901050106020a1e03050d020705031215 80
    0x41106501620100b0502c942200a42e41c981d51220164601c0350401e109035181310080b41010052804010001c1c1711004124100340411417040d10044c140304040350001c2c0c000e0800041c2c2c1102080306000321030030f1600c91001408000c7d07881c180401004035042034059068903242002c80e0a01c20705812400082d00544003e085640d41e1405036050110b160341681405210b40d003140c940c10082c031850303216900c400310000c0c903401c09005018080180340c0140740a80c8000c0e00910680390000300707480c2d0089080703401260040c000d00c0d200c10080c016200060180c0b1010091108250300305029520416900004120800c9084d00440c2980c2c1d4621804030700c0b2101c44614013000c1e00c20303040003410360000d04004410030fa95111100700e6501418039020660081800d20021300003c5c000d139401882c161001380024441d03a110158000c81e011854001c2c090301c059090101400f91054a402c203841010454a850140c00c200707447e076000100c54110341c5070810000703142112203009144d680034098a07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 64743348 1250 64742098 64742129
    0xa0207020d1412030c0711010203030105130e010e12030411100e011d060c0c03010b03030711100e15030a1404030f05090303090d03090501080c04080a080306040e0607031a010207 78
    0x881c0d95001000d841c44800b2400390002c0000c2d40020840118040c01d94041010fa4034540303400d00c041c080607086801411034108200401459072003811200300c09184807800a0074403195556240148803a0060544501503060004041505940076500c00c9000d45a84050305d100041080b80d2000704160040100c0d045990540701544209115015461401c400c0c00e000d00886001a000341c101ca09200e00f298800550486582420300920042c65000da00031418401c1c2c0c2c0d6070b040411403074103d540d4011550540c02d00c0c03545201c0e0110008541c8040d20f80328010988070b4483d0700d903500c212900032807a0b0800340ca60180d20134141c401d40c0300302c0d01039880c11021250000300701c82d00d912640c4901c0e81480144642d000d01c5d41c0349205c0382c040780c4c429201c5203821840d18001610f03440004103519410301c41400b0810800802081c00c4210690096000b5903968520001034014201c00c541d6150905c6150100b01c2820307010b80c409030ac603060410310384840c514514012681c1e03403114010011880d240d80c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 64744598 1250 64743348 64743353
    0x60a02030705071709270a021315120b06120708070c0510050103060e0601030507030f020103090807050d09050f060d090c15031e0b060a0e04020d15030b0a0207020d 72
    0x18040d60704030307601e0b01e0400e18048035a180c169a51a0829403100f407080300044048151514102e02c0b42c17032030b2848410400d544c0110600f0006904010001102a500010001c03001c0c102c0d1151030014100c601030709095402d980c600140803140c0203c1142c0030714a800340341c194a20300782c070503202d403010070007100e001a07038032a201201c21510180013141404510f0207200c00203542400800f00010301030354001070662640c2080010784100d20030060040c0c0101c1c0050001c07420119a8009507078010803030208510300c0740b004800501000f800640170b44c03404100f1008011b000b161010115030613030349210503151035000304480c400c0300420751540010200801c103400080e640086140c81d00030702c80302000f16076410140013035205500c10040003a0b43e038400104400420041c00501800100d01040908107000110f080e07403144035028001d11082c50a40c2c891541d4a4040720904100300d001880810a40340800021851901044440080790000100703080c0c5144280c5a610f0b8000304003007a800b2954 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 64745848 1250 64744598 64744601
    0x1006050904023114070f05040b07031202030c0d0b01031e0b030c04020703020f120301230301090c060f03061d060915030d0806030c041b03020a091d0f090102090102060a 74
    0x1c0c09401c1041e81020f840312007149450f5801204a98070382e50109141807080f4148400c90002050b20060001e0314011468890b400003d0350180c41c0c00600444d40c1d01454103090b200f50055100d6070304010300000410021810f2100038182461601c3e005002e100c485400540940d02c0b80390b41c16807000001c05d004038524510f41c03c440d04030400a800c2d00c0b03000748204081410b070780c40a841a009680010180c42c03c81404010703002120a80401c2d260130340d41001000f980a42c100720044020085000c54040d41c0d03542035000c1e4070b4180c1d0102820701a10307030751400a010b40e00c600c000320f0b000c2407a0a200060070801750803508542200d03050394480e10380d5840208846118090028290020510b4509d0300545003040702c68201415502e8250103480c21004251078098041112401582880c040c0328040000310040c68103030103d41005a260000b05000f102c1c0a0350380d910110540d1011031407848101950958103000d00c14000100d001503540403100c6081c0e00c01d101d003940c0141e015200044c0ea07078185 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 64747098 1250 64745848 64745869
    0xf01050c060403050415030504030e010c03020c09040c09140405070302040c020a08040e01090f0c080a1109060708090306060d03020a03050f0c060a050105040b01020f250e010e0702100605090402 85
    0x504205090062048a0514140044500314040b8030b0008050040341080310440051021600d410301039460280e0b401061900108000d074140201c0751106402c050003880544810300300580356000742d1800f81450741c0c0d80b0005210b00303a110380c5004801048a201076820074440c50b0400c0007080401d2840d404d100040c42151104800c5004410100d0009200c5000034401000d10103218404c0d54144030f030ee00c045865040303840201074a40780d007210300103411845070f41d40411281000212006014840c00a42c070603201c010b40d00410004102c001c00c200307a000b401c51210300354120f94813a07541000340810440d4501d00a1b001d41d002c003001800003482400180564040c0a01c03c2e42003c8a040318580743c0242910014012070322000144203504141c803410101040c2440200381c160400102d130380c2c031200c41d80f481e0201000c40000181150040298280040200800304400d03580d403552803900310501a1030300d200500404900e03100d41212401040c055032402000da40302a00c0c0c0340e00300202041c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 64748204 1106 64747098 64747129
    0x308090901360618060e07050a05180103090c08100b3a0506040f0b01121112010b040204060207291e0702031605010206070f0806 57
    0x40000d98058003034141c08030490800030400c5000c3c007a0342d0008000e10402ca80003111902407980841c0407aa542c0da85c1d170700a900d130211704072000d00c41c0d030103a00b0004800340195440b8020345409043d810805040008001d44e0b1135403403500c083c81075031006400303401c100b04080341c1013801c1c050008180011030750080481001d15880174010194014511044201180d42e958103003058200e5800d95044011220203180c646031144c615100050121144101d4900010704104103402200007942d108083c000d4042d0340f001400340c17846d40072f2903a84866498016001c010340b1184001d101504495020300400c60510342031000d00c04c611310042e0300810807135241841d5880001c059403070b0b200c08081c03c1c0c40c41442103030184019028a4074003950500807802408a03445400c801c60045134000e8003940ca1664503c6070a503a2041801081c1000c109810006a254500b42405000008 = true := by decide +kernel

theorem cover : BRFrame.Cov 64568348 64748204 := by
  have h0 := BRFrame.cov_init 64568348
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 64568348 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 64568348 ≤ n) (h2 : n < 64748204) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
