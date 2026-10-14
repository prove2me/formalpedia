-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0540
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:20:22.266921+00:00
-- url     : https://prove2.me/submissions/5448ef45-bec3-4e10-932b-6d054232533d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 96942446 ≤ n < 97122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 96943696 1250 96942446 96942451
    0x703080c07020f27311203240608060405070e0307061110020712020708030a08060d060b03150916030201050301031104020403050706020c0a0506040e07140c01020a0c050d17 76
    0x40d1400d19440030484c81d1520300f850400c1c641c51521241d00300700680c80020245074082c400300803805641c10194028804900314030554040c01c9180c1c00c291200ca00c1e882540041c424810f4030303450f21800710100d07411510300f100c50f03400a00010070b1042401518074040c8142038020a0341d04000349420490004207488480c5481100c040c005e094210141c54a01407144000712011040c04555842180c5805864520041050401071144080200d41040000100d841c0300c02a40c070380805a513640010000e08120a410440d001a1185200c40c1c0540301009018104100908140d0b401d01d4900380462804410511085200c22804802c00c05030344c20104481c19241c2200d2000c504a074140049406449564030042642c8544003000913806d0b80425062620300c8101c1d00072075060307502c0c000c004140c0210700502c1001c0c0f103d800031584460185603d5400800308401c40390810b82c210b00c416089801aa1500010456044074074003004000e21000c03000503043c1c10f2000c00d181c1c0040c2c08803241c5000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 96944946 1250 96943696 96943699
    0xc0703020a020118120b19021303060c121107021e1305062407030e03060709170705310c0e0126070e010e04060e07030b0d020909030703080c07020f 65
    0x48040410000400c2004040034100c00c091060754001c0303500d8881104030003114a00b801206240d0140e80c0110f87e4000c5a0504240c10381000a1031b055850300c0c0010180a4100800c1c4005038001d0041ca2070140503071603c1c4820340c20f496480300c1c428010702840508001c2c011505d55940813412401d03030f136000b001100c01180b80800003695600d01005c01d020020201c03c0040c0408056801030180b6151802070046034407c2c2c1e1250069040d80061596030303c0c090b105840030420000e0280b00e102c66802804580c48600d42c210399039903070b40d24086892401c643c2100c4010700d984c400d60b410b181d40c0c14080c0000e010b25480342003000b02c81800340204071451901c5298100b0a0018200301002600c9654102c200c001c10504001420281c1c00505051009a1500e000c513101c00140c0781c9a20785032140070100c60109000580903684d12104a00510f904251b05a00000ca48480409605c1d00ca03003080c4075042c6040115600c041d00d09011b89050340c0207040340300c104130401040c40140c41e0300c0001d4421040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 96946196 1250 96944946 96944957
    0x200303180f0312040c0e01080a060203041b0b1801080c0f09060d020a08040c0618140301060b0c010605090f1501050d0e06100512120f03060103110a030501030b0c0703020a0201 77
    0x886a18141010018140401c2078400031412000d212074a01d611801544915070b1000440d035106001995400b00344a03001c00754206552a1340401c20f69001194070a06c10780c0860666203282191201e000d11682003414440c201160980c00c00102a21106240d502402c100030589404245290310f4864541009403013070010561840c0384d00c070101904c00d03160090030199142d00c00340b0b0000b405090200c800b6a02c1d0452044002500c5000d0102080c0102c180d50300904283d04202c140300024001c10003583d055076807601c00142600403000501015550305c0004034049142c401008040300c009406045c1c4d0280080074000d010200300d0055030a440300307081560b101d28101c10010300800c000d40c0c1c01e0082e80074803820400c00510f14040b22050b10000c41761044200c00341c2e8915640d500c1c88550f10300c60a40c1c1080089000044200590350002052401158240300d0203015200c4d6080844d11101007501c840051003001101000c141d4050341c0c100000d07050030280d4500039646c90305490301a05018 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 96947446 1250 96946196 96946231
    0xc170c0304050d0f0206040905091002040806040b09120d020705070503011e09050709050c09100305070e040905030408011d100b0603130f120e040506030105010509041e050106060801030201200303 86
    0x2030b04c200e41c10505400500f15519141d8500c0e162000d02130443d480744080c00b4005840720000d11500c207603810340e400320307004054070341e02d0341c2d204400103502410109151007411a0f036440440c12800410755144c0290015854440501c1d0483ca0b00e40c103608014407c5e4101025030300d5003600388a00f903a070f401c07031100300bc2084109400c12600301041500048070550901040242c00d400040080038800002e5451141040c1258411000c8400503200342000549605c140442480e040c1c0100301440e0049041c1c80c50503640718611803c544032107019000201d4036130001070800c9018044444040b9500300180aa004180c1c0001c1e10340c0310041c003000480e04c0c01c0003804240205201c14240a07a4001d2030f82507014640c140103030ac54102c41c602d0b14455814980000c54074103040c05441e040341e4002d4642078058403259030b02c04280c07400c4264040402c0524003041c1c0070030800d0061000424081c2c90308407007035045000040048103168400300b2083c0011144005c1010000201c2e0703405415445400c510300c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 96948696 1250 96947446 96947453
    0x2060412031103180606180a0207062405030f0c0a0911130603050907060e1005090d0506070c1e12030c140712030b031507051c09030c170c0304050d 65
    0x100329000c44140740c0b07200881000250341184041c03902e01d0060108444e10783e51100c0070010528102c0f121808103804140204046100c25000740c50302a22441000c5500042d08103020f1030b00c010310495a402c451040380030481410103200c3d5010580340c200240c0501d9602001189040069116010f80140d1350403415001c1d041c101e065031251400c5a05e00103103242da075031004000d8901962910791074002d0301400a80907000d0b94170412044005002d0b04049606c545040d180c94000c0b140f4035821032008007403640024002e00c02e0341d21a400f00d0301c5506200c003944c14000e1600300c20036812554085984665008107500005200840c01d20386404a1201c081640499100b0001c211000200d00e0100c4c2e15020000b540d10800c81c420030396541044142103401c00c0540d10002d50243d2045203a030140458030441c800d4006052032907450230440e01078021680070400300c80071884141c0001d80355915500070041c074122442e499150b00494141411400030308076449201320b00c40c29110f6440c2d080e0302c8003003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 96949946 1250 96948696 96948701
    0x812060109170f0d03060303120e1603080c01050c1215010504180b0405060a030314130512060403140a0f0e0d080f040314071404020306040603050316020406090c0206041203 76
    0x80e02d055141102106440001ca5030b43e0305502d400e480040c0541c00e040c1550610038440c00701141e40560710100c1220500c815440281841050604180100f107901d1040c100030381c03035680041d40700b540011307502c401520031a821581c0190100c1000002000607035102d40701c901d041034001c9070300c17a241c0040e460b059005840038030556128040410b554002c0d03c0c0240c00540c409910100300340e4090007946d903144100280105213001c014041030480340004145c1109102412064020440c1802510344407400180c0f8001034081d000080e50014081100301644040100035013603a01c0c0d1000d0622503071407009005d00809104040030440d010325589511ba4403070064035011900b000386207550703c0980c034401070203500600007940c10f020f92600c00c000320400003401c402100d400c0c21403110340203100c50422001c1d500180c142540a40c49040c040086141031009000464011078006040e00e030320703c14001038402c594040c004152522800740d9407a40c0110300594491b44c000c070074600c044100d0006500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 96951196 1250 96949946 96949949
    0x1031505130212010204080105061207061404180209031b0a05010f1205040515070c2301090203060106032c030306010807020f0d05030a0f1a100215040f0b07020303040812060109 78
    0x140400c030034256001210045d0700502c1528420f0000740a141c0c1c40c001400100e0806071840f01d0070758030200c41048854800c030294040b10b418014440d02e0680c5d220001e1609000d40710b01c004645600003000400d81c03908122002c00224400010303e41c543c43c0800040b18450588203103130520070070030804407495100d04131001d400c075880e28042210f070420341016903603280d04007160030150001a01050715640540c4a4280c0203900080e42c00c0c02d400100340e00c0030454a480d002140643d00c0300c88450050f6811b00040340a00540c2d6000541c2d031000d40700301c078070040c0e03c43e0b0054000910103a203050802c00100440e40d07c24030030300300072400d510b80d44030032840c15106c00c10381e040714007174951041c80081d03110f4001e50052212100601650725881600300840398065514445011100046a1181403001d1400c0d20700103c2e0050741c100b0407510b08a00014601250115507001280340031600308004140c0c401e8000c0513a20045065203400e40d45d00055115003c980a05584020700156885e03200d001d8800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 96952446 1250 96951196 96951199
    0x9030307060501030c0305011d0703060b010c140c0109090b01080109020a0903050304060306030b0a020306030d0c0212030a02060103021206100603020705010b0a06020303060f22020d1506051c05010315051302 91
    0x2941c4e41e8207068420a5003030008444550810300021288060005044110030300038000d00722a5155035140002003010300c04103814054590003500100d01e8164191b07090943c807001412425240d5000184603004541180d04814a032244c0d02e001c59a20075801c0b03040d03d50300c110040c3e4176903540354247c17202d0324190f00c020030600c80002c0116649500d0340000b011244990007104268459108480580c081240d117181c040d070103c52081001449403110b1010240060421141011200002800c41e84a50595809a0304c410010400c5040440c40b17800124540b901034061400d140e800c146010001d0706c01e01c0c0c1016008100002031050a40c030400441d1401848000c50650351030001c0e45036041142e210b0701c50a81e100303c860290402904106840ea0034800d100034032040550894003c0d00059141d0595560342ca0f408107103082e000c945000034202a8540d03a4403481e46042d80400450703600110b4101d181803100400024880b841d1070080c02c600d408000c42c040c1c1d6002c0c20b40301d00c0c0603c42d0019 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 96953696 1250 96952446 96952451
    0x4060302060f13050a030f0209060f0306070c050c030d090512010b0402070b04020111060c030703090302010603050105040f0b01061409060a05070b0117010608010204051c0201090312020105010f290903030706 91
    0x2140e00c40c2d0080010a07203010300220416610800c200074202d242c4405030141c110790031000e005181c10758400e030340b0041c014501f001010303490b000f103860584120748440c04074842c41790304800d0200800604031658012001050340c140c010800400c512800d1080b54040e054140401302080d1003034000a004d004040d2003151075900d43d040003c080103060310f050340401c0b11210310007040780c00482c10074880c0c00c80741905850f60716807800840c003d00c4c8030581a0115542d41101000044003070280f58065809000c0301c0204402c0341c144a0044401a4080380070f12041c490300f41d108803200d4080d1409032034211401e0b520340c1c035141c0c0c041d142031040c4500200b0324080840003240800c2411035003032140c1c1d0164020410240c41d4a1100c0c200c0c1314502425902184200504000a0544e0348400c0350a106240000075a82c0c1c0b91360310308500c070060205d100540d440780d00603c480040034856000610004200600c003881070031520184017a0081000c0b003c0400217030b01c0d861303514204121400194051400c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 96954946 1250 96953696 96953707
    0x6160312090615050414040809010504030611040e06030304030f020607210903030201060504020c1f020c0a031e080708060d030509060c011a0910092c100501171203060406030206 78
    0x803038010103040a50040581d2410408181410030344181039041a000011502c552515290308c11150040011181045803c00003c40001c490f40210900316400c50b07001901d032802e04441d00701a100003484c1c18000d03841404104081032111110140264041e43c1e03a60342d4611a082c5010282c02402000e40d41e045000010740c18258442d00c11004c4900a60080000ba625101080140c0c41801e0521805510001d0304801100070300c0c0c82e0360368042055000615250f420500c060401c6201c41d026804074142440384500c0c4941c090369200034004a14041403186480e0901500300f040161046010707111030b8084008040c021012034499190042c14652250030310f1510902a10b0203a166400e82011402001c0c56030824074004e0740580e010724120341e045030800042c00f00030135021750b0072600785008520310110001d4504c00303c2c4041c9405806000c03102d00644240301500c0041c1d1045a00c1d140503100e036004294085904040c058042801594985400700020080d04468201a41c80382e00002c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 96956196 1250 96954946 96954953
    0x20f07110306090715080a091b030b0114010503040f050708190311010b060a0c0305040b030f040b06030a030e01030c030e070602061602030405030c010c03031811010306050f0616031209 81
    0x340d54008000840c200c542a9403000615074807000d051080035590342e200c01210401c907018040c4541c1c85940e07080001852043c90311072500c02205039121074104200d0000900c1808100c1c442c05001d0849420904aa8030000f0b000030702d1880000c1c40505502e109503c6030041020600065000f8017010049400040e011000351000302d94141048001c109078042c2c16011039018043e149942d0030040c981c5081484610303040d00c104109010031410800100320101d50314502002440c05110030382d041d1009807400c0d240003c01ca45001d803100b8400d81c04100c07440d0009600080840a80e0000e00e008600400c030098194054052130707d00000500030900b0200d10301e540041d032684643d1401901520703081c070320368050340c07a40b103980521a09a00008540390316540224903203443c140c82841c0020f400105c0c00503410402d41e00000403100d44000e14454206907906010304000f03071208a4400001c0402c038000207450380304144190b10b24031141b1100c0c00905001c3c41d07a070040301e1181c40f002c0c000c140503444e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 96957446 1250 96956196 96956213
    0x1510030605040e0a05120c0f1c030b0415031106040509090102070302010b010807020601051009080307031e0509130e3a140a0e03011d060901060905060310050406020f07 74
    0x1d29004500e00381d2451400003001500103503441c1c000010740400c1d014203021011b681c0c00325200182a00c00e13407840ea03900c610200101180c4600b07032200a4288098854000c00b40c0301d10116551085041c5280c030b03030491a480d03441c00d04403540441805120881280850700c9402154041a80040c9110412200c0001900103068951103a4000c008802400c801034500780420b403000401680800c1c0144500c0c240000c03194006c00880c280748421541d00d2002c580f40d5840f4040c03c41c0010480a402c148003010141550501d21103030034103d080ca0240301c0420700c0040c807150403000746034480403003c2520000307111140d619110038a10480140309240c04019100f01a8140ca0300e00083e141403415841c030406002c0103426803044202d2510300d4091040720704090188410b40c0c103558a4881c3c80300030740e0291409a480356002c0142c041031419452507400c4800d80d6004208260a0200300101685c0c04140500c4082c41150005015121420014004e014440b520648180005403800601006a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 96958696 1250 96957446 96957449
    0x40302120304060504090203040f020406151806020a06110706151d0115050d06050619031d0d050310030b0a0b130b060a030c0c0b010308120c0c0c010815100306 70
    0x240c50108020a16810440d60380c032491203100c00042007440140843c04050f001150014010010200c1d40840ca400003400c640060f4017115800c10b01881104000f0781103040c040d122600c1410b190880c5160800207074945030341b200300410a6a40b00350400729030000c40305898030150050410461440071000044222085029000d100207407641c000e005038466600f010b051354a803075001800c03055000c000380c906800c0849007081881d10343c0f1010489858005c05091307200c0344868010f0b4520540303c0040c0869039650081041d043e0071006600781d030b0600041030f0802c0795144c1f806680ea5900c1c070081c0c0d400e100c07550704000e144021a1043c42909940b541008640080468540c40312002e01c50209044814149803190401402d21a000c03030103003c0c2c0e000085403440c90824202c1c180c2036554061805009800444050750045900f0b814201005c00d9540e018110008840c0ba00ca15844001e80e50b2012030b8845041100d04c44c000340310044054030008866078003034070854040002400113405451103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 96959946 1250 96958696 96958699
    0xb0301090e0f061306050c12070210060503060606041e08030a1d010807080c0d0b06030f0103030201241802070204180203100b0f040b011b0506061005190e040e030c0102040302 77
    0x1840c0d8015019040401c42d940243c010a12506640c0081d64400001d480000e00014481c030742231000c0e820814a41404078800c4119a02618140c2d0001030312208503109a0803240c001c1d8048401c0040586516084500380c0c0c00041010742031700181803420101002c0754100e29011f01000c80c00e12900d6030411050050400702c0074020f100c030805100110741b83c0e5000ca54850000d15040c0200360082d140c1c3c001080440205100400c1c441090004204140d0060314501100780e81ca40040082c1982880b454042042c40440078400d4403441d01201090b000c58000e01c2084864070b0488007540b80d96074101c400d11540a4024090a07100e503000490050b1100001e078024003d05441c403180300030f80c2c8200060010020715007a50010030409200081c0b064201ca90b0502c0001003052a00540f00522103c40c40e00c240028031041c5070980c2484610135828000c5803d0190510000ba5100840c003200d1280035440e00d42400c000011100080280082c02c3c07803803055000c001030000c1410f20640013030095a00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 96961196 1250 96959946 96959953
    0x3150b0d020d0506011d190b0102100207080408070b0a0c0311012c0c01080702070b090f060f04030302010605010c030906032301060f08060604060503061309020301060f050108130203190c0b0301090e 87
    0x1520a8184011100b11381200509507c00d582c160030007600e0707010603441003040c41203d1400c01d0411031001268003002066940300000304003004004000c018041c00f501e56885490f05000502d100a0040800d940d002024030511082c12011070600b540000102d107043c40c5c202020300f0107900c1401800c514459074040074014556000c00a50007200320f14001d02403680244212894070441101d1030308034102d0242e0082524840059a079220b8001d0b150000b28501c0d0240e42d103146140281c00c42c1d0941c0c4c44541800b01884d41007010070b401c0851202100c6041c18081050340d201e907840c0c0042030362504284160444000040303102c95000c50350301410101a111010181c8500c1704114150041d071007140d00184003040020703071505151404041800c04014041490401d40c5d0005c1e003507440c2600b251110504003030313081210f9030740190410b0700242c01d1490466610200e030086512048507040026040809800c50000c0043c2c940b4003800030310540001a031a940c640c503680c0060800b0070750f00c4103581b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 96962446 1250 96961196 96961229
    0x406050703021b21010b0607030504180501030221190803061017221e032c0f180a050103030206061f080a0603080a0305010f0f03150b0d020d050601 65
    0x250340d40c044102900004000e0354103e81c0340b0b00c1009550b0241c107000c0c0019506c40d41e4400250300ca8001910005101e601d619031074504054144400d0b00c80301c08082c071803078208030040015890f0690507281800e40ca0b602c6c0140d6403449900c2c2441c041400719021009200340c1220002e1015010185024003821581400101d51848c411104041000103405e80590b1007000b01c1c0400800a007030854284840a03914180441500e405001c00b407110782c4030741010701e0072041200301540811618081084901c2c19060b50b03510042c2e1640441c400700145e801150707088840700490303840300a62460b102d110312002032036152680c25000070704070a120480140c425113003c150745140c1441090030004c0d508001425113104404202c1e034943d030160118001c180d030707900c020010030030680003082c08018a071404541540751600100136100a58804460707100805401d0001075500060380007072a0728030001084000103000021521400454002d600c41c04082c0b12000b00310b0045400b81c120380301d046182c0b9041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 96963696 1250 96962446 96962473
    0xd0203060a15080325020f03030a110601060f0f0f14071a1302032505060f0a0f09181505030708060a050f0609010308030702150a0207050c03070b0403080d11040605070302 75
    0x20b01030503410f0400f1072208600c00c09040ea01901405e0101d000600040300b40300540c02080c1960701907080c040026010080074200403c04000381030041940e0701e03120000600a000041c115072000300004200807030943d0001d8120300c1801042030490000302000c0c0c0c2d403000342c6000601005654480d502c55021140012308211140c200c4030b05035900a4060201c50000c0c0c440801449040c81782002c240ca0529804100c0e600c0f0038010749800706268411545c2c2d0b24681e030b070103054440b80105840400491b60002c1c030004280d40703002000912115801b2406403442640c00641008640119416128100c0c00003a11000042c40600441100c0c05c200040d844001d69640c0c190021101c654200020720300401c0002c0c2c00c0401564810528419202040280c120a001060003a10b070074107041c0d00030403010288881403100441c00581180244502d07071030700c0308211a81c0240d01c0003620800300400c00441079000391304001106042075880c2135807681c40b058007520682110340141d00500c16004c00070201d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 96964946 1250 96963696 96963703
    0xe060402030a060f1e05190b0f0403120903061b050a03021b150105150403110d050a0b010e060a09021305040507050408011407030b030321090102041208040e070801180207020d0203060a1508 83
    0x1c01d40c03081202d05d9030506080300c15560f0352100124030009c2504010010115a2184440c110001c455584070015490350403c070007990410844110b0503c240440280100e40103002c0f04c10180d15410b01503118607a0920b01400850710603616400c0e4010381c01c2021b101040c030700100c2c0c180d8500320782c40301c2d90040c002d4020324a070181b404014080c9041c003500c14058070b421300d25078a045208908031120581c02e0b40d194800365000b0781c020f0444e030141c00d0070300501b4030b80f070080b0f8006401e802c481182001200300600b40025582c4c80b402d40550303610808600464410000c0341c014002010090003d070001d041142d0b00380000300e4904001074540b2540848602e0040111021510080a810320122030800c1e1224900000350203118a994200b0001500305c0852046c081c40d07c0c0511102ca03212450544180d0403040300402400030000703544010b01c0003110382841d403c40c0f0a442d200060702e40380148003181c0130050140000c0e500d4031400e02042801c0d61035400c150b0306140c62110647d0102c0e03032106880d64 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 96966196 1250 96964946 96964969
    0x207060e0706212c010506011b0f030509060a050406030605040c0806040c0e10030902040507091505220806181c03020c0a02090708040506100e060402030a060f1e05 72
    0x16029440c8110300422020001c010320780128400650041102c3c0070401801d8513002002c2480c00b81e0550709940c03031082c40f0f050341c000001c6c00d11381c00480d4402c9e9440c0c8400d90f4224018014104210030006043c8607006583c088840609020364490700c1d0135000d000d94100340b0507100000e09012011461f0b05083c028001242d4080d160f1803455191001000060030000c10244104024062106c0c4e60740e6420211485588894900041a42050050005545009040100313201c1740c400100413480403402030390b210000ca171500689445c02a1607241c01d081d09103695071a01d0001000106003500c01148960040c800c15809510401008102c59244c42000601805c0da500220144020354001d130024013011020700c007030714001c0c61141d001403103400054401c2c00014907103100300300802c803081000c290403820b10b6450041c000c0c80c2804114804200070138445c000d0380c003c808624028a142c00940151030400f0b24004a40d8035003e031144414000341d032058001c680150000388a0804260150 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 96967446 1250 96966196 96966209
    0x207140706020c09070f03110d0b0109170705130e0102040e010e07030c020d0c06020403050d0f09140a030f060209040c0e10030b0616080c10090209010602010b030a0b15030a060207060e07 82
    0x110380d562541c20b41c2c3c0d5481c0107044200381238803115002200440440148003540000303500182220400000501961840c0c00000c18118107841c3c3d4540c0d10000603071102150700071103103240004622002c0b500500a002804595036002103000704101280e1240c0354103891071540c4a802c00c0d9203006d01101034942c0540c40f0320158100c2c4060310f180071302c10301015a04902401d0b0261820f69a580d845140802e01c48800000440c419140b0604a600c070a0b014003e00e022410750603070302040d0001810954007888000c2001d41e030b0000c68030401c06c09405071400c403500200100a9810003c0c4040c4c002e804dc7d415030b51094003850010310b2810b01911403c15180b00c06042d19040011400a601d40b503100b0880507100ca80b024840c242980d0010440e6003d50000a1004550b184191040c002d00c908103030010420740e4104405056247ca0002e401400c1503040100c8a0854039402d4896060805201440c0c0d014002c803140c40060100d550010444680708500400100300e2040456031241035600585 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 96968696 1250 96967446 96967459
    0x1a010e0726150109030b0a021201050d03080609061f08090d0c050c09070903050d0201020405030706051213060f1404051005010302010c06150504050103030c021e06041e090207140706020c 82
    0x70541d20382d401c2800c01140c4181040c0401c00d490f5150b107403038078404880400c08079800142e00400c561151103510300400c0b060b2070840545855a401400994000340214042d044410000e10705507503502c4c1d82c0300d112280b0384031801001c0145800900c3c1c0a4203c4e880c0c0c010348261381c800064a8443c000d032a080c00d8001c805412070307803814000c1100080000c0d1007201009407200001c4040342c01030045a690603001d8000503551841c1400385403c1c55515030181d81400b00601582803030f4160755008a6201e01203018041801940d031070090300800141c0040c149040c9002001e048801414401c580110f01840498011042c1e440b45038041c6c0d5801d020007400500040b075240700040603500b044144800c3d40c603c0c0d64a0584510216003180c009034000e50008140d48e0060055080820380205015918030b0301008540c1d1074008906107100714443d51030401900040d403250b9516075600d04000e030007842015955898281800341c1c1c20000c0c42e4010b50b060141b108001112400018122040940500b05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 96969946 1250 96968696 96968701
    0x312080f090d05070204020f04150806090c090402031009050a06050424050108040503070501110306132901020a020d03080f09010203041e0203210a170105060d05041a010e0726 77
    0x885503130304500412600503809006203621448000041c00250850f2814810300302155980103001c0000a4a55030103643c054040c0241c10310680c0840380d02005c2038801603a039440e41260459980c08690040e002c491801c4148100150a0f401100072900100d60600c800c06129001da07411064901004000d10110002001694010008aa0b120380034600392410114035444903030a444907400da20112400020030400645808030f0544180c0e00e81000800c030001d20078561280003c2c070440c184001010071945d0406583c42002002003880d4060000f8000305080d00e4054540034090758840300346102c0300700040d1850414425070b0711070f075048450503403403800300f143c42422610b00d401d041c0d8140c090b62202100401100301e00020704400c0010641d6141000ca07801403c19000b0f408200b00480c000c00108403a540317410a4032221103000200103201d49544c0751006010302c01d01c503a00141030a900001680c00100019944190440e0300d40c90701c0d4014a0640c211400e60800d15040011b184034003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 96971196 1250 96969946 96969973
    0x4080303010515130323012c0115080102190f080403050717030f1603090302030301031403040806070f09050603011805040501020d09050309040e0c0a03030302130f0312080f09 77
    0x800b200c0c55034a20126140460b541c140c00350707a810540041c0e1b95a0150307003400d11b21300f42024049008a850303400170025020502c1c2d116100d030041c0341481100c4a980300c10011000b40079440750030001003c0203203102e42a80ca02455010307407c403800c0355901800d5004d100c490030780600303a00090340000765112962030351580d500380c0b056004030703806031040245100c5010de040400c0000b1800303240c034150200d90600d003894090710400700d00c0046004150038603a035040029000020f51741500e51289990301000b80e001c0389145540510f0303100b000070340b00e608240100d164000e880b100a10034280e5400e026280c541c0d00303000061000703220b0908440c20f1418445074005541d400560068816000580707043d203048002016a1501c800983d52074000180c1c020862410b031180340c0e11180a0006008941141d00000300d1304038040c400034050680006001428100c00005000a01148050703942c055440e820034040804020311030ba0003040030000132421182a80c0800e91091000d0f00c000c01e01010b0301035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 96972446 1250 96971196 96971209
    0x1b03020c0306071404060c0f0c080303240102070e060d061103091005190911191805010303080c0c160312031811100e06030a0212010b03040b01120807060504050d0f020102040803030105 81
    0x6000351424183d032340f070050001c1c0c1100200c41c01812010300464031703805e002c20b103960381e818010180d400c4000020580c903c3d41c0d801041140803a603802c69848483e82e00d807408140c000e50600801412035161040c00d8840b00f5400018501034010042103401c40c80f44c8240103422214151007203100500440442ca107481100c1c0c00044050f441802e0300b002c5118020701052044c007141b488410321411040e414803696000141104000351030b80010f00180d4990344024000700c001400705105d0a900041d0111016000c20a8134844052020305848055a0307041c070460400c001e650800000b41012004402001c03152440600190080615001480f08104010080c2d43e1410401c040c8111032440f5041035950074061441104075940159481405a6000c00d0300c0005030442c4c50301e40310500521001c100a031002a055444c10500c0e030481c44005d0070705040c03d00414100400305401c000400040107404503046201800c517032185030140b284004188d00381e01940c02548650707030052004114518180 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 96973696 1250 96972446 96972467
    0x415060216231906080108010b01031103040807050a0512090a12050705010f03060b04240810050603040204020c010509010e0105010503120f0d0905030c030403021302120402010e011b03020c030607140406 89
    0x411400f80d800035600440b1018145074030200115180d40d004001c80c40003806039040c040424a0204440c00c01c181036400c150101a10282c000140400d111040100401c078104c04903800a0482d4100d60003454082c4143e480110351700c1c090b0000307c0380019114007180150f507616a01c000035100d864202801180c1564a6440b00c804050b155480017989100100040c40581044100d074400358080382d0400810000000c284d1040116203c1001004605c518a01040d2041140c0d10703507490700d4500005000c0c0c09070390926000d5510300004d015100d481580040c0320100b5550090040303070b0340e4800305502c4400d50101c0c001b5190b0704020807104040d60300c0c000d20031403e102e4000503400358951509031440d0440010b009880c0d20008080c802c0d8a4000c2460b480614100d409510304060000910b1000c00d010740001c2c1030040d44135001034140e004a031602034800300185002d0801405050082d643d051403c2000c0c0207014410100790050710a40c540c0c03000c0751605001503d00b5280c11000c8580800a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 96974946 1250 96973696 96973699
    0x507030204090603030c050d05030c19050708040608040b0901050106020a0602070f080c031b030a0c020d03030f0509011401050303070201050a20060f160e0a090207020a05041506021623 81
    0x82001107608142c0703103d8030028500954130440c2c40c950342d250152a10448400c11005d120040c000c105081c070a140884107180007421544c15200e65500d0180c4480c0213080e03006042050209010a01951110306640f1072400307090f4001d69038840141c060308882083c0500d000507005003400f031010806a40080102d184509c641c507030346ca0090f40b141322a0b81c00240c0c03080c400307410010b608030340505825400b0285c03036182c1d00a14644040b828019200000d07010000b80190031003007030316040c14040c0e44807055615010106000c00c0c6060810b030b900070020102804100c4054500116440c140001a61800b41e4180c4400f4a0b02300250000c1d10052030348000041c10000f600021a0450b10a008081c01604240c0511185003813001c58031840e16080408d9070b04004001d9480c003955a01c00c920740c411100b40c4040141e585549001203940340e0f9040c5c001039002418012b0301005a00300e0f40c5500c048403c50fa090710901c43c40600c54820f519803c1c800c07500d0418050100d403803101c04000409110520 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 96976196 1250 96974946 96974951
    0x10b0d02090a050307090209010f02070501020d0809160906090c05040302090a0209150a0815220b0a050301020f0c0613050703030f050913050906010b07030818070302030609030304031808030904050703 88
    0x150b90f00000e150513002d410042d0782a4010824160a50308040c03511000b60090014114103401c0c040001d603110030042030001046100700120b0f070111402c0c00400c2c002984901005243e40d00e07194010080c200038402d00b03030980d150110f0100080d10600555003a81d60040a004040e04c540904078040e400c01403030039070711034005c008000301c8049442c01400c002d001c076145c8441b00e19042e59141c0702500d0000f48180201052241034000745907102c107001c90342d52101b0000a11100c00c4c00407440300402c1e5045213030158400943d0300414403483d0090007074102c079081140c5180e511079000e00c8400071400f034020a540d00c0b4280500000740200f2840e5291611441c1241c14035811000203510313201080283c51602d541c42040c04108441801000c0c01b5050802d2550b15101c1c890f500101050310040c940c0030060702c1001c0000030300806010b624001d640040031106141040d110755503c1c0d500c1502d0031004036812942040145011728a08001c0f103580c00082d50401908200340300c05000c00030044001c26070b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 96977446 1250 96976196 96976199
    0xb030112080f030109140114031f0e2e11070f02040207080d020d1b0c03030e07080604030f0e01091202040b0d060c020109060f060f121502120403020d0305010b0d02090a 74
    0x2010b034000746000342902540852101c0f030b401084040001e0607084020361040c500d51096007070b2000148035448009d1641c081c0d0258170025584030041400680500700c41c09550f605e646146100390031002044045031a041101901c074070312000b2900b0755088840e8400c0c041c0900c2d40450050041c110026002400c007515003107440e0707541081c60b4000340a00d0840390340822070030808100743c810500f54141100f0315006a200344000038040d85c402e001d0041c109500e40c8181c40c0c080c0720500c00c1400401d001402c44240e401c01d4640540407030300c814000c100107802001d005185620907002c0203301c8000702c117001d9024001c0d400b0700020b411040c02e002c1d04012a284c81c10002803641c42031b134000c9580d55000055201d1189400030940d40000220503c190509d14148200101c00903000b00b00e418031402407840390300c589400303202a044442a40d04a43c0301181c55101e090481d000d0510a0f4031903400c0c1c520920302c074001a003c0741c0080c01091840b403c1802241c01c03106d0558014075240c40020103e10905 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 96978696 1250 96977446 96977467
    0x312150603020a2c1c0b0705040812040605030f0c0712020304051302121602120c061e090706050c0106210b01080a0803040209130f0b160203040b03011208 68
    0x5445501400009900140c4020300c1948000005030b24440c41e5005101103904105000f11240145907132031040300344101e441500350045d101d10681550004100181c1d150508010f08540c2042c03150318168018005006c545030184400c07601600c0050f00e03550709540760122083c3c2210350050030301a10680400610001c40c0c0001a80900943c0b140c1c000c55440d42410240031488011880402c000f500620803001d00c5401c50440c1030380802c10040d504031090000c1002c92402e11050002e036400200011841800e40001c55664412182e504444072420300e980094491030400b2914500e89401c000f00922110348168000d2119003d118008110705c4c1d140c0101d030a81c00040c1039120003100315190385900f0028058105401400590301820b020619a10703107004a00c00240000c2c403c200140c002000d2200401c44000d40c10340201080d102c130341c414601080e00d52800d80e01c1201510ac0c030707050020654400800c903820344401e40078150640e46460088400d01c9191941110543c038188405d540c3d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 96979946 1250 96978696 96978731
    0x9070e0408071403070c0305070504060b16030c02120307020f0d05100b190f05030705010c0305070b0a1b0e03150112110d33060302060306130b09180601080601060801030312 76
    0x2640d006e2404064014610b10f0b10074a800c01c00e901c8540030341d00f011410006040c01805603011669820b03000740300d04403180b8049481941c0306800030b40c0100c1d1900960715800c80000a46001442524001160560a4100148007075048030080050340700c031407150541741c01504134000d010405000a142c0411003a20201d00c4903590700301e0ba20303246205030200820b15080008200508003800c09000e14125514010060701c203080e0040c1001c0022808201c0d0900d81d640400001e10203071000824122181c1c00040c40c1d02e52903042a84648984034100702c1040300120064100c0b000c1c5100c103a220380701503880ba070130586414041544042a0050340c4007080c2c080450a49100c1e45044001d0455805200c01880c1c0e50341303408010015241145c00d02c016181c400480b41c10000c00c0f1440f8100581d00340e1800301800562030303803e41149081d014070048102e10200d2030721141c0312800303a4a950ba20344122070342c0d48009100701400500840c0c01000468002c1c44025200c800b80f8202180403000d0800110310b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 96981196 1250 96979946 96979957
    0x1a040c020c0411030f04031803170403230304170c191d0f060103050414100606170c04060e0a150801031709150901050c01060306020d0509070e0408071403 68
    0xd40c1020141000d02d00d024400c044268155081c10350135802d20890410302000000c000600340845007504180d8101c01101100046070f0005040c01800f029480d903078102c1e0003920044441c0c1c841409404049040e281d00c024040b44a0301c021414140b401c1e6222020001601801c584c82c000c0210605081d01c3e4255004100002d140101c0e0f01c0390315024051500b91540c88407e550300f00b41005205100c04480c214603042003091802143c00d4445084c170100d6484070315125280741c803c03100c8603480e074400380e0494002c0b640d064440201500c61641e0000000b8000c032800c40030002d00704028450203003d11001407074114090442d1403a10744640a10314002004d084201c04030b00035100400800803108111210001c250705604e04240882d8040365100441040030f8442000c0414070798066440b40090304c031501d020324003d02580e0360324249a8001e510008003425860704200003c1c06a6900003640705c200d4005009030b2140e56100d898520759500502c000303c403d8054180303d403180b408100081c04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 96982446 1250 96981196 96981221
    0x608030a1103030709260d08060a0906141504031e060c0e1c061506090f060801051804050a0f110907140403080f090a180b010219061a04 60
    0x40d6294a04100a0716444104010641c558020820001c035558031002c00d104440c0e41490ba80704c2240300340c0d03509015030901e00440000b80300e1150702e20320050f40305990038003031241942e21140e00c98942e2a08819a0441e01581d0005421500e10308400e007002c0705040700040290a50030b09081e10790b50783c003180340180180428660440c0400d0420320040d40310b401000300705424480300704864032001c00c9401e01546d0b10340c0042c0ea40650364000b40700050f0084104404d404410415094032100302401110090007480c001c44001c4c80e01061050040603154140c40c13000740045600d9200300c0d902c505100340144101d811340640030b00c5200141c3e22055a804042c86540101c4c115242c0000340041120020b0071101040003070a003000340540d20307c0888003920780106040e03556101c1610020000c3c422000500e07008040910005001d42c0d01002311000c403c410301061042c245108012662964a0191510010b0010103034500088442c1d0058000780c03d13810342d1a240c5000400010300b21130390104003a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 96983696 1250 96982446 96982453
    0xd050708060604140402120c10090f08030307091e0e01030807140a0209070309060b090907050a090e030a0e010c06050f15030a0b0a0209010207030803010b0711060306100503060d060608 81
    0x520050340c0c18004103a0010060320308000e1038010101c890884c0b10003800c0a4000d445a00c2d07042c00c0004144000b04801001504082d005082c0001c0207018100d03d02c52240444810b02d8003254040000c01200d0041c80503075614040603050510350340c035403144110010448202d000c0001031a8001d60415802103000b03110b010789602407030a00b00d030401c10940c0740c501e19800c80e0501c180103968402c5200d410040b00c1c5030008a000b52480e001000b401d10900c2d0542c0b20b070b41e00d07040040e04000050a801a5842900c100d10000d03a1140d13100c05445007205492000e0b0000d200428246d481380703032880d0b80c441d4145090701d03508800380c94000440c2e1058443c0c83c514a546010404840e042030340003861034905800030403a004032610b504112000c0940030050140e00090310028a0384200050b9000c0c54009800315a40e50b0344800035000350748200b408850280e0303102c003c144d0626018041c5d900c607050141c242e06900c1801c0b41c04030380700c1d40002c0403546d00c000104007000100d0f049111f100041c2058000070f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 96984946 1250 96983696 96983699
    0xf0507050f010f06140306010e0c0d05090102070212061506030703091401290102190614160f0c050303040b04050102040b0a030209120d090e0709150806011812200d0507 74
    0x1400f054840c107400c01503008621000203c415200060814110b0b405070300e02d1001922100c0000d49a44a017071101041c184c01d107418882400300650003454507901c226290712010740041c0e03100c0e03100e9504950845660f4120b043e440c034a030520308025940b100a42c60005010f1010380c0d02c41101c100c00030840207041c5c1d5903440d421a40c0d050706442c082621311300d1000120300720744000001d540390990078403681146185e08440d003c00c4412b400c0100607266404600c02203140802d0131741c0860030380c8158940050718581200211034011080505040e800202841c919550354481d22a1075001620841d0035660800c40050480c4000019000c444029600035aa860300b04003000490b0489502c18402c1d0303000122030604070303504248580304403403821900000300c1d5502c1700c007643e000d401c50f0b10021030ba405480028810070761280c8100c2c46071070241c03214401d40049481142d01e203481405031003070031307014050400007041901c050003100882841c03510005500010100b42c110a02100407280390703120000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 96986196 1250 96984946 96984971
    0x20f06031f06140904020f040e01080d1b1208060109090c052a0c101202120603010e060903030c070f0c030f170a0509010806131b0e060c0304060f0507050f01 69
    0x1d000c001410540f928030f05590308076051644a20440b900584101e41c0001c00e81040d540d140c007900d000700b1210310b41c00c2842d80d65030445078503100b4588001000501c1c004130103134224010442081d01d01c1d0000b114059020041c0410b072084078001e00321f1410301031074000001340058603000d003216282a90381d13125202e244090b04005032900182503130484121000c0d88461680e00001d9600e40040216403040c022000b07000306032000e00c5100740c1c080c00a800019540c1081e408042583d000f110154000c11010801000a0b03880314810f544180c071503003080000c900014a26409400002d00800040c12201259a2905090a099401101d841601c41c1144007400305ca90181803002c20480c140034604404064001d0040c031401042c075040c40902c0703021410b80e80b51300700c1142d5840040b03801000361440c50b801c608030000718251440c00058807164010030b241094020303680100701140080d4209818181d068512000664209040110a20404010420400c80d0b07840c03000e0b4100000445845010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 96987446 1250 96986196 96986251
    0xb0409050706020c0d110919020a090f0b03040f0b061912050606030d020303010b18030609010b040c09140f150714060105010c150e070807060306140a050a12020f0603 73
    0x4980c9100b0140180f110010951b40f8070207400d081070407103850b003076070f550014481810210590304409092012964084141d0002a204103076001c1389202c002e420790301c0014445503c01242c000b007000701c10031080b40011303040079010758024000600b20195018207000d0810b2810065009201e25400c0750502400e1000c140603a6405c20f00540141441c0080b020000c0d40d60300c010b00c1208040c19000a420590701410380020603003241c01001c1d50018107100c0c10030740c0a40003840e101b41c82189441100602a801510079038215242401c40b2103003280f0070000c108002c00352042c60b84d0081030040a0100c0310304407100400d00c00d0b10648065001c43c0200c40076610702034050300541d0602c01d802001a0100d6000c11508560104505011501e800380041c40e5080200c940e01003a024840c51902060480d0150803890980b00120711000441c01c0340e804000784015180f0030150446084c410511000900028174540580007416000440444401051395580b003181c004c0003903078000191624403400c10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 96988696 1250 96987446 96987463
    0x4180504110910121a07020619060f060c0501021e030103050705010206010b18010e0a0626070f0503040807080d05010501020c01170a090212010606030506150a0c1101030b040905070602 81
    0x20b40c0d060b4254500551102d201611500914540f0b290301c128580400031100c15580584214a210780254101964084e40e00c3c9000d440404c08032405000e5035014110304d00c1a0070844141d500105c035500e02d01f81c02695294030b0b100e0155010754081110300d0440d5810303008150288004540303203a0303961450a0082c140025900f010b8115001400100010300424060b0759411502d580c841d405080c5420040e0361504040c1c021582000c0c1413040001d00039081201c6004142e80203a281d20004202039604004a004a400b40c011030340204880100358401c101540d80240300f00300c01c48c0b4240c00c50b101c600d0300ea0844000148002c3c0c5690051000c5d5a06112180e0150000e003814920a480c0e52000304144c8001402d60a040303680f08500025942c42294550282003540000c04c101d41d03e4040040140100300c441310b004200f05c0341181604034407030048030015070b40ea41d59514444101c0d07440220805144039068101a00ca507046201a943c510600038100c0c46035000300f507500e1a004002e400c00000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 96989946 1250 96988696 96988699
    0x21513021008040c031103010f061410030605031002030702031c1b02010203040317070207091404050106080304030f0803070903060213060e0f06030c0a1e1106010b0309031e0418050411 81
    0x2c24003070200040c4c0803141316060301d900010810f500a00b10004ca801020307000300c521806e80c2041c00c00030744c00001580d405030399901914056410000d0500507420341d0820300c0340c5501a0302200c0c580e03990100d142d02668011540c2d10680b49001000c042c050204d00c02c102c075440c000c6540e2240d031221080c66034210306006005000035411440c0c1510050f00000141d000032410341d0030310001680e1a0310a025120140c8800c030410040241d9003200400c2282048030126419840c00a01140c00b80000081d10101ca501c4844040e0104450741d45c0e00403a04040c0401b000e010311002c01000082c02400030300075040203685500fa070709240400050030410441d01e40e500400041138080700c182c8516040380d511401c80070310b05542c2c807603071801180c4042e45000d20403a680f1a420503408100d6110445a528401c50021180365907242e0b2a14219403000b41c5101d2707841d078002c20245c208400d0002c2d001c0e010703407070500c4528142540c5a1102c0d9502104800c1c440c0040c1c0e5540400040181b801c40a030b001020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 96991196 1250 96989946 96989957
    0x2307170c0a09060327060e0102040b04051507051002090316060f120204060e0405042d030e0603070c060504050f070f050312070507030209041707150c0c030906050a0215130210 77
    0xc9034003900c98502500e6561440601541402500f403000da90080104044c0c09002150380d6503030303006440bc4076041402024814002480e40c0031440086006440d26960808040c055408448504000035440007403403a8140c0030300b401180b41810b1540000d0001c00f0140c881903400115528020110004107010740c540e50310601040c00b4aa510109800b8215010b071000102c82d126030401404a00502c0700c911401c1c102000f03c52000c000501085200c5442030b260f41803074040c90000c000740c83c0800c559190000350103240d50740200301c0710780006401c54080c00540c0c000d035940c0e54015042808c250030814000c503076100100182d0508010050100c921030010504180081d40e400f5214a07661102905c84c03a00800414140721040d00c54a03810000c084100381e07180283c0c41c203c41002c440c5c7c44407104291410261060741409000c0451403031358150750b05440d039411b020054a20342c009174516021886000c1000342184081c5e028140143e601c4460b010310403100c0e10420512150300020b0504005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 96992446 1250 96991196 96991211
    0xc07030e0409080d020f04080105090307020117010501050706020f1909170606090a27200405040b0106031d0304230a081902012a020909012307170c0a090603 69
    0x2000102078880da400d21308000350341c0d000c200356050214096500034040a501e88014044030450000050001074800e807a070000c1d88081038642c034940d60003480303124040396003088a400090a541d00030940303050b01a0700d130780c20100e0b001c08800b018000c00d5a06004181074100034080380803868624880007903034400801003458008040303481800301922000d611a02c0d0f103060700d811124044070300640c0200105401c8500070380c2c24010802c1c1d1101c8014104030190031500091400c2c24001c0074401c070340000c26940980d182000450040502c0c40c001a520503414062403080e500501c0207000803c0d03580c0002010184070034814050f42031120343d9034811600c411040040c46d00c0030501d401540d0b1201904c604032015400140c2d08554000701800b02e144030700030000e00030b448202403040c64074000d56401c1801d070784d09000c40c0c0c200c4002180b52102c40c0442c0307105408c1000a000c4d144d501c0b042c0c5107841e00300a41020805111120305460500300c000740131601c1c0300d403280c3c0034103c100105080d180501c41c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 96993696 1250 96992446 96992453
    0x200102030f0a02010908270904030e1905041503060b04090c030318171507050408030429030403020604050c010801050d1b03080a020102070201030608010c0503071206030204050c07030e0409 83
    0x901c51440ea4410071800858001c003654001c0d1720084606070001380e00f50381d95400c03070b8022100076000300000c507084100401b06d204e2404c0028440e8420741d032644454500420700310400000c0c00018070000840c0d01445000315145d01e032030046012014003540304011540c1145088010381e0020940ea501640c074094002d0007251480c07a2150803039415081c40200c030300c1c20404403d000401c58000d11443c0e50482a6100c84100c0042c0c4070413041030441d246072480d1604001142c0c140720318407480c074969106100c140004024480460612410401540003100644003041c2c410740080324140c0158111808200c1072103000d000004c0e0150003440d00409a40c102000640044000c0070040c0902600d03023654950f240d1100c2e41a0b002c1c540001143e80c0300c0041c00b80080c080e511401089000905117800041c0040341406008549100713515582e0841e903032650308403081039a01e03140d099407544552001015031103511400d4062407110900039600c040c0c0382400f07800d6024076621240102c1c604070a10010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 96994946 1250 96993696 96993703
    0x30901080c03040807050d050309010e060c0a030e03091c02011805151602040603060617010915180f03050301050a0e072f07080304090e0303010e13060207060c030603200102 76
    0x20001d0424240c0303944442c10031584074081c002004095100d50011a41104c4c0c00c540a07602c218500d600a0000350300f00a482901d42c081581d034900c07032150505c0400083c0c3d010703030808041519070303100b224140309220f0001600c0c02d4040a95140200300b4080c64030075540d0050151822a4090b0307011040e00d49000c010820508026420040700480800c0d9451503030716a0305101412500100203201075030f1281403803c01002c891169010b9401101a030f964444418020717056566004141400d00542e0f6190220203801a9a081241d440e0074400100004442c42d0400c1d80090081e65229220340c1842c0c02d01c969500b154204100e442c03540c80c20040d845a010a5210012522540c5642d40708009591a201d410200e5801501c90040d0340c1c0105513440b0000243c0200c6581e03d40c14424001d03050815603c1e44002e0050018020795000020050011250528142c501c194801468000d0070344442003140c00c04c0380d240300000d4a49a0030414001203103400204e0341c00004503c0d414022f0800080d54 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 96996196 1250 96994946 96994951
    0xb16020718020a0c02041a030d020c01080f060102030715060608060a03082a031606050606040e0114030304090507020303070f050c070e0c0409020415080109050717041106041205010e03090108 84
    0x40c40358002403c80d2015124156060300c55030b018005000e1244112145141c0010b46000240203118140c882c908aa10000740400341480685445000e5164000521100700c0000e0074207055100070000a40020b030300c41c0c1403513011210340400003000c0d41082e00041c044d00019181c00d04c0340000b4001030021603030540403218482a2106450901c1c604000c10020804203400c4a0074a404007144a000340d054000000c551544555401c00c8070307660784010442140114025091034080758030040c4400400054081c00701d0800508683c141907a03202c18074144d68003100c10400680000c400d000f421a008160114521510300b0111f05040b41180710983c0d031240c900c075213140c0300e624802290160402d00700322405480c45017000d65580b6213800300426803d440442090000d58190000200c9114501c1924010100c0c3e50f07842c10102240401e6080b8440301500540e0a8980c4191181942d6101c800034801415052940f444420746400c2c15421102804200701161300100011090b90380d0107504907030b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 96997446 1250 96996196 96996239
    0x4030f05090307030204180b061c0b0a0e100b010e0306011a0702010302090301050403051e0c070306020a050912101401080706050a020f03030406020d05060d170904090803040b160207 80
    0xa44035107001c40003030700d400859130010790400c0c070700a42c404480c4841c1d00030b41011b90141c07442214913120303c1e041c040744103485130401c5400d0881003014000180740603144c03a04079a50000c0442c0c11110400400e00b400f004170301300c03c03085035503480d80b11032960402c425501010040380544241d61400501402e030720015103855415140000e100d10441e806541509e011000190007084a40740900c2c1c064020303804500301c581c5581c0518a0403c1c2407118004031900491040c0142c4002441c40c2e076410040e4020010752030a00c9401c0c040e2000c3d64a61072601041004204028003503c25001240412035000182500c060b1424000609c0705900000b105d10031a0604d1502541e03610102100300d04002803802c1c100300b0390000005100c01e00c40660060641003401e0710b020000e948074442002100c241c1203800801c00500040200c52040321003020b0300980701c000d007021914511640e00c82440ea40101e90407203060a034407040c0f000c480103c0300078601074400780c00200202070414840801541a1000c0c58 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 96998696 1250 96997446 96997457
    0x5070801092304060e0f0a080a03090f0816060e16030209040302030f030708060f06070321020903070605130801090b0a05071206060c050105070f0e06070203071a0304120804030f 78
    0x41200085841c500d4222800050301180c0b40c205850804040d01d103039500c0009900c6105104130320140e000c10780e45011395001030042c0c602400c080095014000f690b009513194000010681e002c00e1f8018010300358485000c40c000b41c881590724000080360000010000c06520080203d005802c8006280e801d403a011156403882c1d0f030391440c0403480e41c400e41d00da425050002006000415810814907402140b0490b140d8542d84401418402507004210024001842c8800c5520300e0340500b4030558141402003002510380607140c00400d04d40707000780c0d025100060b00051419620005800d020010740741d01c0c4000c0c0440401c940f142c00100d18064010a80385540703101288001c2d01400d00a20b488009007000e0018940e9910080d0903108240d609807030550914000a110510402003440088581d4440040d090007690a01103190043c680490301449110004984105800d5850703890000022a26a8038a03041c50328110a484010205080c022182c05100c00650040032500281c8490300c2d29 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 96999946 1250 96998696 96998711
    0x1080c0f060906071b0b0a12090314030112020103050603061611010b0a180f0509070605090a0305070b0417010603150e0109021201020a0f020c03030d0c090320040b040507080109 78
    0x6040c1c0d1041c078100c99804140003070b0300c1c0104604070815500c210403110188085680e81c07030440c58288a24950f00000440120004424903010390000819900a18040503030340700600310103031191b00030f8200d12461010b2280d83c0e000c42d03a040c0500b03070b4055070507006018141858004d900000c400800020248039a111101c01d0300c000950102e4074060005140306150341e07840405d0144c03c0306903070506540300c1c14125812a041d00c98043c05025200315001004564600780040310160031140d4156440112040f0000204400b005403401800d65501010782d2207162000048046081c2c0b0402c04290741020410030208280300b040c500800c908042c04240040040301c0240103004220000354022451031801d10341582c158080c0110440b9510340109000d50740e20142e945600c91010158198810010103102e076402e41c015400e50307900303170030560007a5849075251444d034001c2e10078050420071a5208451a4a858042c82c880f140050f181088141082000100751031014050240c0300b80e11250b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 97001196 1250 96999946 96999949
    0x1602060f0c100b0405090105090a080906070b0901050703150602030304030e060408010203180d02070b0f070611030a09020301060f060806090402010212130f080f0a0b090703080408100c0801080c0f 86
    0x100e0301e80c1c072211810365901d0b0350585011402000300c002401d000d40d103031000046a8020500c6040e004071041c900034950308903d561861680d50228407100d81100061105d40005001614100d02420448001189501d4038000003812101000400011b0b60741c0200d081008503001700489801540600d480c8049080090101c0c00f24460350340100110341c1300104200d04801c03507110315081c401d4030400f61855001c1c0580704aa40e11518028034042a008020400722445100024013055115070b10101300c5203402c81191105400c121400042c0d661a00350483c2145000c1c40781d58041c1504004d41c2000a080034401407944100404560180d4194004036055a001300940e41e05040d034640000d42e5501ca8002c20102c0c1801441000d80e02c614582011500800210711040590542d0008286004154481e29140300014000c14814040e115000c40030840580042002c1c0080c40020047c11000340b64410440d850b040c881320030400c0c19001070011080103d08001d41c07507000c98112408400110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 97002446 1250 97001196 97001227
    0x204030b0910060f0f12110306100608010812040308130f090204090e0102030103020607080a11060a0203070e0109050f0f1504080a0209090316122606040b0303160206 73
    0x41018000c62040c00802481e00c0c0d001440854403444840107004075030b600c4007941072030403007801010b2081100c0142440071106070020010824051003991090400010100e42000000d581081b032000015070b00b0300569401507411130040810100425a00003105030021041c0650b01008045483c00640c00355500c000c990714a0140032108030ba80c0503265550034020086d40070b4840d040e000303030a142d0030141050041c800e0b207040ba90003602042ca0003103241d44005982d4400b04040301844101d00c1c2407409404104a040d1003298642801030349d0b4102401d01400c2d00c8051410581000301c0312400703200e981c8500c5601c900405007601c0241003a283d04c40050303800c0b03902028450040130040b42c00614144005552a6041c5c021b580b0104240c59030b1032507640700e1080000714408801c051901400041c00c00d81c00010001203071a00408035800090500d40740c410a0b114100380710710481c1441010f20303041c442c90402c010110010361405c608903086e400d8403400340c0c0d4003a00c80e00010400b98402403c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 97003696 1250 97002446 97002449
    0x12070e010b450402030408030a0902060c0304141c05100f0b120c0a06020a030e0609060c0f07050405070507020306160306051503040b01140913050f030703030506090f0c03010e06040204 81
    0x240001e00805440c00707a0380d44070b010042e02c140200c0000a64616400d003071085034017032500595100e141d1382e280c0e0041c0c0090710090034100d8110104001c1c0098052041c400781004d0600380e107021004448420801c4198408120030300040d82081d1890000584001402c580041105601180402108030540b00070701c03040402a40014043e50103006008010504150192003190054005a190f031402c03a074030091810020049100414400d00350f18100c406419030703010003001c6a1500510bd00c405040880781c2103070810795400305000f407059252a01909510600030f03c0e00c1400d18904d5000280e5134031020b0480400c20a804101c003000610941103880503020280603c2c071100c8500300207901950084409440c07101e40c240020810a28810040071010310080c194201a181c0e00c5000c036100034200d4049890341b050b4020b9080c50310061015000ca14001c0d1400075185c074011007404041a002090780405c1000e10b42000407220100782030703d0555500700034441c803554811000c28000e1041c5d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 97004946 1250 97003696 97003747
    0xb01050c0f1501080304060903060b060d0c0c0510050705090603090c060c0304060f140417011410030507170a1b050411191106011503060902041412070e010b 69
    0x10000201202280000c445491445903400a00300fa81c0c2d40e9100ca0b00d90040d40590350014601c51800c101080e0f60780c0110b2020480101028980840010044120f0f00c14807030000c0070800992056041c400240420703900364054800502c01442e00140040161080100c0b0038071650303002c4040750078803104100303100300784001600305595000c421064070780d60f400c10311441000500030700c3c80c05280c034842d0810900890038500710b0f074140b504010b8400601c0761003621a940542d41c0d000384c0c04242c00e800303076000d01900039015003801c01030a509125051071080d4210895401d041e01480ac2d6000c000180c00c6c1103107800c2030300c0d03400d43c1d0200103403080101160b0f40320b103500900300b44032070300f0070810300d40200802d10040c20a450511003509003510301c046818440e910a4000000412110b0100602c0800f4804145000a804c41e181d4001c0b00c00c03038009030803100101807103840c200c13094100b41d800d003182c60308250001c0c510f4a280128151803203e05005080b0041004034182c0500b080303c000b2070610804 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 97006196 1250 97004946 97004953
    0xb03060a0203040b10030b01050105030a0b0901031101020106090506090112030c0506070e040e0f0d0e0307030804033e0607021201020c01050f1602070b0a020a050703060519050c09040b01050c 84
    0x4064120201940081d40e091380c165a8103804101c0c1c1c0d00e1003503102d800312a0310940f2501d441c5e2030000103540d582c000070810190140c803904451000d4ae80c062045010358801c0450b61480710213040028210340042d004086028074003020300c05181d590040150450307401c14070a10420f040b40c64100d84111342c10000a020f845032030240074003650031255142201d00140c17000c1040403090823030103907201d0f41034101580c150040520007454038858080000c1c40100902124140c9580e039482c401c05600c03550050783d0000324042d1016421100007240007a080124400d0f110b0459000030500311412040d2031681308810020b185005c54440340c401d090300b01742c458004c54441584c001d502e030203071104842c00c05c011004480040c000300748104c001c071a4825503a0040c00f02901f441c0d80480d01e5400441000250700ca5212a0400644100041b8000c1c40c800c0c1400300d91400d0041860078541d5200500c15009130a107000c2041c03401f000825102c0081e02200c01185000590380140c8061041c07030b541525602 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 97007446 1250 97006196 97006201
    0x70f060908011802090f1b0a030203040b070305010807091509050a15050402180909100606021b010f0507020405060a0305010218011b03021e0304150f030b090606030711010b0306 78
    0x982005800e41150203160090064514400c0c1034504000e5042001354881d0005005c0b60000c44401c1c030741c0340c2c0306030101900000e40144a95014468001c0b0648c600040e400008000800071140c1d00240c101205080900c074a5050203421901d8007803070b00a0a402c40e40d24091404034800d150a02c03001000b00c0101000b4500340a03402e00098590303070904c0c2e0300c40c3c001000d0001c1d460034248200c400550a1400d03001c0702114010401c02228006054094a0700c10090080050720180c491f17100104aa81c0007010700130348022000c1c42c0d4036203000055040c4071403221128a81134124048480844d2304030f40c000b4081e610300001902d80b41d903075000a0015880890f01144a00a00c0d401010701da0098071503043c0c440140003100b00352990110000e0041e08038018482042c282c01c898003500c0c41300f5500341c0f0300b0310303840f43c0e0a078591410134000b100c0060360040391403214a401d0b104500000c0e500340d4002003546400b201080c143d00c800b400510400c8036480103010b5803102035004581c2004010159092030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 97008696 1250 97007446 97007459
    0x50319090503010e0c01050405060a0c0515010510080c0708161a15040917070203120d14010821030a020d05011203090f12080702060702180406051501080105040b03070f 74
    0x2080c15016181c002c0d0300e01014044c40420000d1040b00461059403440e24090402040c450240c001c91601010f200305c000903d0001002481006d4000056145100303842d8504000c100b4949012228001441220300c280300342803011000f140d08158000210340d9136180419046410402020030191188040005030707000f01d501e000c4460700914644540024240c0460f04200c1105c420102c02800640903d40510340350b110880980022800141520040c3c2d030081e60001d00b030760042c0c0072500919a640c8804000d16a003c8809000d40050030041c46400d1800e41001403a01e1920f2510180401c080006840c00b40d0300d804803002031605060074065075a54101040c8642c00c243d8049002ca040355002040099010003641e0441c0d1104000745174140d81c03038480d4000d0754007a940c00c3c1e8212408100b4034026881e900001e54200c403030050f42c04480d2425080c034804861000e030280500f00841e0700c50804503130344182528191081102d0024680004000107846c14000740c0c84901e9083c0302c40b8001691 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 97009946 1250 97008696 97008707
    0x1109090714030a2c0d020606060405031c0e06030f0901050a0515091f08010204260a110f06072102010b03120c030d050708010311010206240a080304170106050307031e050319 76
    0xc4880c90f001c80340148c4030142005030754000c9000d200e8050f03000311000b19a00c2188150584664140c1c1000642c48511074081038556004a8081c0340351085070007448003840342446802d9001a0707092040105003004d14061a8160950145030320501d002d602044440220a10000d403003214035001c00c48440d503941c00715000c0d402c02e1050881805000000a8110700c40040c03845081a980c00908402c200c5c075510654101e0048111580081100a0400316902d4050003806014020400141c0340442c00314540b070840c0b0880300b94011a41891005c00c0592400039070001c440b035419410545480524494070701d14001e850f8003807609410300c001d02031f4107604600141d060340e001c2c27000f01a20900b45001a82e5841d0b003503410340c519403408825411000d4003000310204c241002021145015039811a81d0301e5034109400540940c55541580c0c8042e600134400c42004000079800303440c9039881c540314024a41500304a9402c2c019643c03055130104902402111b509520030500d44c010b044030400000c12 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 97011196 1250 97009946 97009963
    0x1a0f0402191707030618080f1e04030c0e0a1401061209060c170903040e1b12040c050a0f050a050910170c12191103010e011109090714030a2c 62
    0x2811403400404202c0d00c1042c21a00c0c0080b034012507154603123808521030001c164498840242141e1400b00c003010040442d02c010070055004100d880001c4d400c004031101d990001034440010b035454501a40c8002d0301e0540d00341c0c111002030800754440ca5001c00b401002c0c100364030004000e41d1034134203000300294125046040d4880040650314865503906405907032440b4074040c5809040c01c44000840c40c2e1400c0200e540603a008219050400000b007000307a0700c202041d90b00b103e1802c2e58242c14406400c10301a9000101b0550503241515840c100100b05c031500d1074010240540c034001c001412184c5440c10003001095114140305006e02a41441501c0d1001c90f02014810201c44150210f81500081d000c149880d6490075400c0f080241d0382c0d011042221040203981554036a2a00071aa01003032045820300042140401c1d80c0300003560403c455204001c1c1010103001d41c414030f91265036680720a59500030001000003070080c1d0103844400c3d00c440303c0b01000300522010a035901203100003144000c07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 97012446 1250 97011196 97011203
    0xb1c06020703090e09300304111c02060409050a2a02010b0607050606010c0311010f0203150402130b030903120112050601090e1f020c0106080304031a0f040219170703 73
    0x71070080c2c641c05130b000c0000c0309891480143e07100c4040030303d40403601e1801d20b0a44c0729014403500a80418114280a034200310b030160345102450758403181e503003400801c4010713803c1440285d5081d606140e000448c1e60145014070240b15640d100000e4030000158002400044889039a070003109503142c1403c0b2180c1192203e800550900b01074899072300300358060302c0009510071b01070b02041d40d45100444984110300302c00e80410040e018034051406d401e103c0d01d0106c0c0c03068040580e4914102c40d900d94090304c80c000e020f0041e4410004a00a104a00310043c142c400441403980c0c1e81c0c560f45081440c50042c01484142034418500002d080c14600040700d002900c83c20075519183c1e039a840100440e8400f100800c12908100000a030015462020b0094005480c0d00142800c0003a6907190031240c40340c02c0320300310380d200040520500644a081c1c0b040c20041c4400c014103481c142801000c12480a00003e0050307940c0d41d42d04076084003d50030103002d040d1039034045111b5103a428a03140e0350305440c80183e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 97013696 1250 97012446 97012457
    0x50c03070b0a0f140a0b0a14040207061104080a03090b0c03030601080c0d020d06030b06030c030c130603140d0212161403090d20060c0c011808070e01030c1509090b1c06020703 77
    0x141821f8882078200d41444064040340d6038600309100103984000070440780c0550340c00300e0940c40c45c840c1024002a081e00d00080c0000030b000d14020b04002e610740c100b000d08280900903007407100000802c59520500a1810400c1a26542040340c880c2c01903441c0100105e0000c10305844004a40d0f0107001224014a51a8041c1c1c40c0c0e542450386840c058074840303030180c000c00505181030601e806903600c2082600c10010b00f0540d282c880011102c0c405d5106411600000400320320316a040085885036075a01b030b038440c03030070f484103080e0461481d081034000c0c602c4034881c080355044181031054415090f0007500d00b40c5014090b00e0542c000308401c07080d032040760003410328030320090601c501038a48101c40d2800400302107070708100568402c000200b07180c0c0c4080005001094800c0c3c1407100ca0020301220005680950442c03418000c0042180c001c4070840c00c03034a00242d0f00550058030481100c41070700c1c00042040c1d9900100c7c00b94244408210502c0340d400c130021003040415070007428000d00980d9076 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 97014946 1250 97013696 97013711
    0x507080a0c0207060305060d050f1b0a06080609191a031006050a030b10080706020f0c01030b010804121803150605030606060301090507090510080402010f050c03070b0a0f140a 77
    0x10350444507400c41041c01a4041c000078801c1c18040d17480590401002003060408603180da0302d0b2840c22003444400b18141e00b0034804240f103081440d040c00541c3c00215031150f0340c6810607000501500000309858401c1414101045010000081c0300c03800714518a030070f02c1340314645200103440050318034100e07010784640700d04d001d003804007881901c06030381008040d0490246942c071820b5158001420400f268940c6a90008032041c00304004801006990080c0031203400b80f0641c0340c24006c5a4032044d06060424a942c0c80d075130b81c4200c2d40e0380d0080d0302c44075602c83c03402c080c101120001481118240010002c00c2c012050088445160744142d488010034002681c4900506440341c01c00d89407950000030a100500501469410503a40012180380c10345d42c0950300c00c00210090261081040800d00103000d000070340d60300160000982006084c41807800c054004455035030700c10148080c111031b52100c081040d08041e41c000484a0003038803001d1084010008060745412010340307548001c40d1078141d6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 97016196 1250 97014946 97014961
    0x506010e070509060705120a02070e09070e010e04050f06010f0326030403140c0d0e03010e010c0210020c0f1002040e0702010509030403020f04090b0c03010f0602150103060c12050406050708 83
    0x8000e44121000d60703401e418400280107004168000c0d040c02c9515004000d118907a10307482da8054080c0c20345681c02000c8542c03814144001103040500036800980085809005140d40c100e10350341142c040e0240d0560703039070715810700070b05041c2840c0141c041070091000018502401c901c580302901d000d0074140810300e1450540342090f044c20401c081212505000090129002d5a40d5820034030209800703a142c00c00d940101818400b80f440d80102044240060f9401410240305111040410038001c00109840040295442e48482d41c8044003580010352010350b04001c2c044a400b841c3d0501c111201d03a0780002c20407000c0e40140c060038903d444e10000080c542e9205000b0350740141c03602ca020f9841c0509580a00802512140049801130746641c400400103007012441032050b205082955101d50406410303190080441d44600f086500c01c038581e80405c6034684074141100c0d88003000240f1400c6815007982d142d620440300c60b468502e04803c01c0180429030b04007520400d81d5664103c0d072035403000d9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 97017446 1250 97016196 97016219
    0x20702150d111809061203040b13060c0302100e01060308030108011a030d080109051005060c0a0b06010e060f07060e030c030409110406020a06050603010b1e10031e020a030908070b04050601 83
    0x2429055143c00f00c2a000035a042a0720180e4101c400a49911095110301c10a1451580f0550004000b1034001540c0c1c440301c003042c038501000c1c010b9464056039085454400a50310b9600c1c0b144a1945a43c9078074544d10703400c0945c0320500440d40004060b440c0c0d80c3d1394004a00a05074610041000340c11138000d141d0341d01d40032440303500e440480c0c0c9a105490742400d12410041400800030001c010100b040400c0968403100074040c075075a444002c0c051010180b9100301d4428018003010b0500401c1e4008400030303074480c0140d81c180346940800c80d132142224248040541030030102e450b8240000103229038070b07480c04001407050b6203111000f8007130702c2c140404180c001d100c1c1c1d101d8000140c1014001c00001459500300a4000303200900228201d0514400a0a4400341811300000040183c0f505100d5040140c01904800d000f4201088a204410014a2600c440414030600d4541c00140c5120440c002d50040c42c80d150459030072522400ea038545202501c405580c1554607104020000603c01c1c6041e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 97018696 1250 97017446 97017457
    0x6030b120d0f0302031012110109321c03090e01050a0302090f07110f031209030304030c080d06030b0c0c0f060907140126160f020312040303020702150d11 68
    0xda44480200c2e5085030102c00940001d4014003204504000004200c2e020000b441c44040c0101e28400c058040400050803e1056500602900303988603101510b454580032042888107004408000c01d40212000907646c1001800c1c900b040a4a883d82d4024150300030800801da400046188031940d13202d0b01000302501c03003444002e5000303800800040d9010740b00b8079441c0d0011114140540e2030000c401d01d00d4146018140c1030700580d031005c00c1034089162203c00d4a60040e66182c051443d505158500903c103542240c406004001e0014683c0e04020742da0b4400310003588c22808010240c20310710b03040c0c41f19602424029140340304043d140b0b940b800c404201c40d80142c051f0001445100d140170000601c1440350030101c1e0510104c0809038103005681e006500b40010608158600f0346442401c2009501d030301c0e021002084461080300311001d400008440480b81c02020044459443d4503044000e0301c00c000000b500440c6642c000100c4444001c041c2c40006220340003400083c40f6009540c038680241c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 97019946 1250 97018696 97018723
    0x303130201031107060603080c10060b19021002030103050309091f090b012c010207080a081c110a080406060911070b06030a0c14010e010c032001021306030b12 70
    0x1804080198065804510101100d4000c2030400f07a1303d490350421140c40d0341c0160341c00d080000e200000c030002448a59a0043c418130100305075410010f50a056000e0405006a44500c0d9505091028002c00100c01042c0e009d41d0150742e290307164a0310baa12a00100ca04074040c141041c042514500c5000003644441e803000c0c406055185090f808202610030601c8060610898001c80d07071506003100400e508009400100002d480100000280703001a03a50041c4419080b03003024100248142c012181c1008100c0d981c11002e0100410711001480c41c014150000e440014080102c203401280e100c0c8610300800040004680d100202710a0712031008c415854074000b006000700255588000c0c6070003010140886e09000420380d01ca250b08245c5811031440300458031080c18007076034441e5240300180420b2812901540e200d5030081d0441051060140005a140740c440d03076072107025030554103044016045151040d5990b84094001c00d0000d10040c0548103210364550740800004155140c03a1a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 97021196 1250 97019946 97019971
    0x1505010503103215030105040305300406050a1103010f030f050c09090a11010f0c020f01210608070b0405030c01120f05070e18250203040f0602070501110303 69
    0x90041c002c0240b007280090040d0350501002600041082c1c050100040e280082ca0502810468864004940280303402c9100360f04180030040086d81c80380a640c1980913039034410283c00000d120f5000612074030f0700c51050305c0f155881000188440e40d0001409000d0200041084c060082030341042e030b210900951600b0440301004100040560043c048800c0c00380d4240c40170071071038800003a1150001c1e907008000f9031203441c1c1c000c207200c0210880b0700141001d0070480c607001c0d4500070240030f40284400192041d035030900500c59036400307403140e900d580c2a00359400481d80c50078180040107000034050701c001e500c681540455000b80d14000c179001da560080062020002200044034045170b51901d04291f20785078070810403401d050b1b000c0c0074040d441c03640b02c40800600c03003000d1101103403e0002c10280b0810306024010b00329000500d880c1c403101080d1070390080081c404000c0e49907114580c040e810704806182e0010310b01c0c1c0d001c1410020750718243c2c0d030042c440804003045556400155030900c400318 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 97022446 1250 97021196 97021213
    0x3071d010e01051e13030b0a0606090302090601021906061403070f17120c01052d0f07210608060709060e06090d0605090a03080a11040e060103090209010b071505010503 74
    0x60245000d00b0183d00d000a00d070300d2802e40a0006a04c68012014107501000b18000600c2004610001a0390001001400f080054540b150041101c283c40c8030107402009001c0114400344d10912401840300007a40c100c80ca106082d18041c0014801d81c401d05d100d00b0792241021b076507443c000c04d404085032000304031541589e0a0510401003504000421103003840f840c8240c2004a10b4540a0311401c0340c80000040c0d14a40304240c1104021a05a40301d1849000a00c2c0f1403420003081900f81c102c40400c50070002581c42600a640c4400d80a4180c2e20210401704850b0800000c0d8105009848924003940d400391039440042d902c8408900031100410503a101e40c08184c10312201030700d004800203007040d40c0e0301a00e44804040380e400b500e0301d00c1d282d004071400c441455002390500e5044100a030f0100444848000341c0501c5014900072401d03080d1401d40840c286a102c1c0d00034803482a002401c41c0c05075690764080c3c0089602140b0b040700d8550510a011540ca0041c0c89000d040710b0024003d00703042c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 97023696 1250 97022446 97022449
    0xf05010c05091e0126010603110a0507060f0204120605040203010b010c02030a06050601050906070302030c01050709060207060c020607061104060206060a030b060105130f09150f0b04050108151503071d010e 90
    0x11440442d0300f410000d1400744041c0940b0340c3c00f582e03000a101041a0f0301c01e5418180e00034290f62586200c180700c274200f0400622035550140840c0c1c3c3c080d8015200113020f4981d14074100203840356900c01045442078014400c140320310356101900580c0300b1002042207241b000015501180203010280d41500404e90803800f00d020f0341c2105074401c1d07052410900e8079400100280c02e0b45c108003403d40c0144e00c081405100c2060034410160800d0f06400c2000b01a0b1070545c009548044600940703040041d050200c0c1c0440d110541550001755202c0002e0010f40f004418882c01c0341c00c18480c52005105600101c0c0306424110380d04010340b504140d860440f0f070f40d00e0780195a55880003400718210150f8020005881040c8001d02019000b50390005c1070b102c0490000240240c4590803060004032020700400860003a107048904940080c00c01000070381d5110404034412140c05043c640007810812403141c9215990021403140305a41c9030032a0341c62030b4803072920500300302048540c0824129203194030107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 97024946 1250 97023696 97023739
    0xf030a030c0b1810050916052101090807080316030b0f011b020301090b06240405040e100c0f110303060d0212013e120415060302040203040f05010c0509 67
    0x8000303400200403080c010810b2403858500c41da04d403000002e9840c001c1c8041c03e101403042d4001000e1090b0050f54643c1028002504500000305002e01c482100b0742d8031280c2036003900098102e42d003000760b040d1210600d051084540d401220000401d2421000b0008640e000e80b04040b000407020300f5120008404c180152040d0001c0301c0345440d5246074050030720043e03038240590890f00b442000d2030700301401c0650034884c518242c4030403003403070b04480e0b4200c0d007078000c0c00001e5804643d0308640202e031641010740c16508245e03f00b00c4e1792007003a042c0140c0500480d0041c1c240d521304001d5076211070440005410250b1a4002558416072104d50b100b0a44d015203483e2078a018020f8030f07107000040b10910330156004214a10b124500004511041030000291140403505035150525104d85042440780840c554136100800c018201c2048100c000d08020b0554407010203180d000e0030842d968286801c02d03004000c500c85084446600340403100c40058400c9040d60684800034000c0340700344900c240c0f543d40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 97026196 1250 97024946 97024951
    0x130f020d110904050714030d0203160f1703090c0103020f03060f0103020c010c020a050c010206040506070c1a010e040203071a04050925170708060a17070801020408010b0f030a030c0b 80
    0x541c1005800800301954860030314600680c420380082102501d05006604410b0000300020710940001e00141c10301e0343c01108962018200764002000700c6280e1908102a8a560b14003414000c2d09081c81c100d25058000103502521203881194075070840000110700f6803145032456007502001b80f01203031007424100300d58401440141805804c2c441504809421144000d90110060b44401101428402c0601042c0e6421b4400e01c05440030b445d080c2c5480d6940c00300600400c04100301c7d00601d000b805160041c12000f041c0e030018000c12075075180010a82c014041c3c405a00c203005401c800280d1802c41c241009019201502540c10145880704100ca03440d0002c0c14007160a429010742c0c9920000140220030032091500c8001d003c004001840d0040f100081240c0c0c140a00c5030140900b0380d54041d009400c9440f039448800c0081c1701100101d040058a9008280542c004140820000d0064001e10a580700680f0f1031950f0f00408400c01d6074a0720310880140100304480c0b160304c0880c107080c12076503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 97027446 1250 97026196 97026203
    0xc0706050f0c04091d0d030209181605030c0903030301030605010501080a0c080114120a1b09020406021b0102030c0d050a0201290418051b0901090207030e0603100b070503070b130f020d 81
    0x7080324003660b80705404c2221b290500740000381d000034400c11504c1c03e1040b0a030581c1d41c03d400f004d55890303c841111341e44001d604c8001c043c01004800101c00540800896403d002c0207001c1d25102d5035a4504140588070078000c007400f00c1d10300d02c00507021800c6032085006001072a0f940491a03442c001189807003801181086403c008294a0500c3c2c8400c00c000862a00d44900042c4043d0002a4401c61030700710b840d080840e50380d004210030040e241e800212514241c00075207a00d1400041d01d00141e145108128400b0271902071001140c3d0f0154000018184003200354000303205101042c013a59040f01c0d821a4071302c020400003200354501d81026800903d14a90305620705403604540d0701c0d40c6103040c130088292458441c89060a1145040651015004001c01281541000d010356406031200002c00d50460142c0c4002c03000400d21152005584020100390722131940d100d5190a150303441c2d0b80020b505507010403110000c120004c5d0405004043c890300100e6074032841c111a82000704c49035483c0c1059 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 97028696 1250 97027446 97027481
    0x4305070e09100218040e030f04151209030807020c0d0209130c241803080904050408090a09050f090616120209150d060806010f09051305060c0706050f0c0409 69
    0x9000b2600c0300d01c000c0c000c405040140d20200480c0500304015a0410010b0883c0c1d50030510030591010001400e48060b21140c1d0500700d404e80c0c0341c602c2200c0d00c940e60090010114101030805042c1504903501c1c600440307a039801e5602c03e4010f042881150140c0b00802900040c050001449c5114220740d21140244101e002c40803141e1b40c0c07401c0e00381700310f6a25030a1840c200003000c9804901d40020201001181d600c0f091912546107440b043c210303004444c1e10078000ea031200b001a0400415038111540b412000701103034001f988680080e801001c0441e90f0419407994200411045130001540e01e00c10404044080720f1842c0a82003103483c401004045c8100c66024000c0140326a106d49281001d030a1084149442e1044005a142030342c24035030282c00c003a044000148a030030035604001e0300740c40300140c0110b45a1240c610340c00403090492005800c6004490520100344031040c01440024010f04050107983c0f50040112840341c0c1c19a40050314000c04c0100304000d00d519007041d2410410701c80725 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 97029946 1250 97028696 97028713
    0x302010309060219021b0405100b03070915020114060306040203031b0102070c06050306090a0e1c0c06140105030d0914131409011e020403020d0204020705034305070e09 74
    0x582c00c000740c001000700560041520301100d00c6c0341c4041644950400c40301486907041c000c10300c4c03000f10001e008c1c803410404008000f4103401d00aa030800300405003040c54071480300d03503140001d000707003641481c1c103440040c5038001c107071146000100e441c003c6400902070b5181004240c4ca850003402011440004e55400b400420046014240b03600000c25641e1140b0741c0d0303482c0072010011100d00c000c045840e41d5181c10801d40b420b00c0c0c00241c00b824842d04109401107002d00d040141c42c001c8215100600481c1008030849840782000c7c0ca0798121441034080710b5071403c40c14410fa070162468021240350808004110843d460840c1c9102c001c0030064000068400d0b621743c01100c00f000031aa000c0481e0b442f6000140a00341460f0710401c0780500d00303011814203003142d0004071451200325002e4481e0b0340105510701441010b1048500070000002c0784100300c0c007800b617418200010801580e40780d002a0340c61404501023040740c4000150701c50040d2031a83d0400c10070b0020044c020300140a0fa20409030f5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 97031196 1250 97029946 97029967
    0x903060a09021810090c03230a02040906080f0d020f060f1003200909010b060409020c0f060a090c060f1709070b130504063204020708040308030403080105061303020103090602 77
    0xc1d65000e0055004200e04041c2450a107006603454592220100b41c5420121404070f123403105030869000381244495401e444540d84c8401900580d003201240300d20384080021000300004115212140c00c00c1a81d581040b54102661030350b419081c022415040100040d01030003041441c664050707070046c0c2d0305180548070b84807010300c1c0040800d5842080c0e801040101185401000c20340d11900300c0000b0b001d15a90400464514016841200100b41d004100d11016090602801076940c06101c1159034514103011010040c0030740040c19601080c2402c401b29a0601c03c00010f0b4000c1196151601c0d4041d10046014075443e008001468a009451005c11320030140300041844d03d01c0c04000140c420301740f1003048102c40c2603a01c09192640390481c0300c000880403000e618400c0d500c0c1c101c4401151094000700d13010788600701004100741000500802008030725001746001e603010350b40d0015035a0300c90f800d01c61148184400802d40380320084040005600c00d0b00310286541c031031400907082200084 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 97032446 1250 97031196 97031239
    0x11806030807060c20030406051b011103040c08160315290a0b1809040302010b030312071808120f0409020708040e09011401090c051207020d09060201020903060a0902 73
    0xb4003254002d8942c400030310754941c0700e190210420139516641410400300710303605540384120300c0341006001c004249900900d0415201c0341c1035100d02d400a0055403648040d11130030b07920480c2e00310707000000a140403e2005000901c481c840d002414847e0246007540c8902c1109044554401a0182c4641c42007090b05041900200d644d0311801401099541050400c0040440d940051400c07510a1180001140340c3c810305820b90482658a041c990702c940c10203d01400c074201343c2a0b0544800a0117400c0e000401040714803600c1c540e50741c2e11004038482c000865008541c0b2813008280d0202254100a0000d00c0060845084240000340f0701562010301da8203903003240b4410707101041c01040802090b0721040e0202e42c41072000b40200200303110241017405003141030040030300b050f60b55980074202c24064400c42d518606110498503851800440c000c0d6261045c48091000440071040083c61b24014000d030303a003581d0002e0291616a9462512000a03e0b8420060781d0016082030b1090a0701001e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 97033696 1250 97032446 97032457
    0x5030c1905090103060801110a0c050a17030403110d02060402011805030609030c0622080f040905090c010e03070503060118061a040f0f180c0e040f0504050c01050307080118060308 79
    0x25200c0039194030002c00003400b00c401c0381e400001e40340d040c200501d4081c0300f9642240c00301754060a0401080d41c003820120714022440c1c0008050030740c08200b0010440c00b0308042c5200b20b00c00e60710180c4000041c81344940741da901c03105150143e408180810700540c0968071010010b10040302c00320a2641e61000030f0714003403003503c0400440d040041c4421044600b030001076809102d10008010561201039140303040e030741914001e810017601065041c004d070010803c44000346118001403000e8208150799940b070b4421100e01c140820010544841c540c10f010802c0c40480704000c020f03016907841e0020111103404620a6030704001e940c1c00340842c818000414181d11601084e0791140c46a0078510a00c400e04020b030060003042504410410444600c490314200110089002103134039074807000c055a04542ca00601603115080a00c0402d4583c46039000c203105d0b03030141c4100c1c0c401005000054800d48021755400c800200400014000c150004000300000c0f5608640005d80710b9583c1c80302400c64015 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 97034946 1250 97033696 97033747
    0x31e05030d060e0103060c0e0913030302090d1506050a1206090c1203090e060307210f140c030705090403050a0c1b090204090b03011b0c03030e0d02010b0102060c070c050105030c 78
    0x300050052044510a461000c116401d041400e1046000003d141427801040d01c00340003200d1524504141c46034040e5001d041e0044c10404410341d107407501410300f0700c800820320b0f11240303401130014441c07400c4101e030000ca6a1406c1c0b1404140001e0b00c0c3d06006e00848002590034070b0700183c00080300c14600b00ca07201c80c01e0003030343c07190350450509505104071030020303011602c654000300f418803503c08417021a803030082035461303c09100343c01482c00c2017110040010160a100d1401012500181c000c0b45090454a04405842c0350b6170312802084045d51090310301600183d02880351820050180b21110741c0d0038090400481a4031030080082c649254540100044a402180030020030750b442c01030740d020080890080c414405d030410b580c586020300c00c4500040018050300103040c180280e01600c44040401c0036a20144c1007180c0280c040c00034440614010f21581c2c00051094084a05840300d141d4040103620382c4038030f007000440302034002900d0303108212010040040507900114004500114 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 97036196 1250 97034946 97034969
    0xa08070e0402030613020102070e071b030905010216120f14120a080705090310020f070203030c010614090103122d090602071205060f07110a08040e0a0204031e05030d06 74
    0x4042c03062506214014040600044004191000607a00070801c01c1c01d5a10203400c02c002d80d0f42c0d0ba2000c595560031004001000305484221005145d0b1010982c802e0b80e400781c00b201c600760711005001824081501c180b0142540900103800000c801d0003030040441d00401d085d500c1582140f90450604208410241000e41c000590302d8050303030008016607200070780342041d43c240b8102c440800e8540c41003040000d4215400140d5048000384603013903d003004d8000d01107984440d0540303000c6000b8110f9000d000c1c80c0e5518040d80c0c40c181c0c540030140703d0689a000c24814500c0e0741188040d1298007008140105564440800121444034a4582d1070703200580d03661492294035100c0040d05041094021140c0a02480040f002091703001450300e802c40122481c2e41070a545050007110201d00c05083e5418500030080d200b410f101001d0f0280c07041d100c000201100507104c10500600301d2055100040c2820194400d0801078000e100500011034001c4054a103090240fa000b01c1c100c8409811800c110003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 97037446 1250 97036196 97036201
    0x3110310080d09080a39081605060f03190212040201110610031e021206071409012c04061215020405090f0912190e010c08180a08070e 59
    0x1c2041030396112061818006401c0b0700f400600764454840315070140490007200340e152000310400c510119036000d05e80142021180381407a9440700d9103e0311841500748140d404400303840e103001c0101402c4800040c0002d150010440e5551b6040d040188802c45100e000c0584800d00303906400100400e400c820802b4480786014030002d00041c1c1d41c08922490b543c40201000014002d070f4084e041502d800066030103010403103041c01009010b41100082d00b0004c19260740313601005c0001ca060180c2025100d56107600191140ea0076a401383c0814540001c0403500300c05038407010074610803002103e00700c000e400c1d030510701d01080c20384100340d0000c5403840700e0303072804418004103030b4000a80c0d10f00000300354a058030b841e00142d122100a8030156004844c0008604103800800c4540546200d02c01980d4841d00e10040c01c00c503072079880240e0310128041030610001036104070440550307190310184003814803095000d01220320200c00c6066400042c2c2c1040440e9410003089018000e16190348000300c00e2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 97038696 1250 97037446 97037459
    0x10b030f190c081f0f05072a020402190207060c02030a170c160504060506030103050c0103050702030d0f090201140a080a020a05070209040510060b0f0406030506010c0b0f0405010e070501020a0f0303110310 90
    0x2c0300e05c581848405841c11043c09001988452610b5881440410b5404d921074140307400b04518243c008000c0d40180f0021f0034a6282c43c034100c600783c1000c21902500c0050383e0780c0b00103070fa0a07104900000d40c150080024040015070b030a0600407040714401c03a0501b041c070700c10146803402e0b0401904920301a14104201311034502070064602400c8191695030441d451a62000e41d02c1d04210b09250501d9261000182c0d8a8802c0013036413140c4007800c1040c02658000406c0ca40109490036003a80092407516100c16146c440c40b049810300d50580d07441c50920fa0348c06c0b000000941002812000300201000321348090307601c541041e03000e0f134051400b900083c00002d80200403a0302c03d41c01603950400c01d01c40c40340c8000b410340c03d070b030210340b03560501040da80d90701001210080b00c8400d00514851080307090040e40d00042038428450ba2048e0020400d0b07a007a00e1040e0342c0e5603000c2c480c860041e8062240b41d030024600c000c2c03151500b8400e003000300d8801d41d40492190103410441d803405032000c50f00010044d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 97039946 1250 97038696 97038701
    0x60a030e0d031d0f0a0204050703090803040c0503101b0c14070f08060901060f06120b04020309061506030907030f06060801050705130f0b09060715050c0c010b030f190c081f 76
    0x80003c090b008021180d03000604548902c005031020384581e0b80c5400199215000e6041710549590080005d540c0346440e1a1840356240d41d03001d101d00903c200e0008902c01e841070700c51045042010003d41d0360391943ca42d81100c01a040000403143d2030200700c400316014504020340f4002e4120113280e00c08035801c16441501d81320000701054510307030502d0403c102ea0015501c0403026102e107454000740c03014440c1c0700800580040101c8035005407000040003980305000c1142030181a0080c0d818103007000a208002243c001030b1404441038200000420000340010071582c1e106115040c0460110b6440180e9421504220b5030f513408540000340440c610142d40b105500a04910008413003501c1c2490320b02c0e81c1a002d00d58a06000341c50015102040c4091802c6c1e186d010b11103803805200c1e038500821082000e03000000c03c00040d40c2001c141400601d00460001c8402900034020700d40c1c07880b8604000d00a0304800d406903028590b0140100781d010041c40083c000d01c01d0b248001c221031080b034101d4000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 97041196 1250 97039946 97039991
    0x30c0705060c030c040b0d2c011505210f060108010e0609030a0509040902030c0301060603020d0f0204080a06051009090503030726041b09021303021009060e060a030e0d03 75
    0x1505800f0420070949070810016902600c2444031303401c2d191b0400c2c42c5a08001c1c0000c0c040052100714201c41c10b80e0548050340480b11103c114002800f900b0001ca1030390b04110000d014541d8009160611030701003a41c5101407401d41e2040f901110440c0c0c000310076107800d10748282c03c4001641d4450340c071013074100810400550444040c100540c07803c91807040080090084d10328440c0314940382d2020b0015036038200406002c1d0303c8003c008104036035651030007030025400200c0c080401802c2071905060100b4510945080b20381120140c0051055603850900500c0c0081c6840b00c0c845c40100c1c0400c2007030540c030a82d0030440c07180e00110307500c2c113280201400b5a85504420038200000780300505416091942c9203802c030390710000001c0c1c3c040f610054410340d0714080c0c0105642074404610150440701c031214102c1242d00907904a034103064441c504558010450141c8800714a21203000d21503820540020204140743e8500010210074000ca890f0800d0030b18812480020b0701c52890001031130384914000c0b13 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 97042446 1250 97041196 97041211
    0x60603060106081915030206030a0615050403021309021503010803030403080a0c0e0d14030d06090608010204031205091923270903090604120302010507050f03041101020106030206030c070506 84
    0x1603c07032410440400c800c02c0c00760756101030340342c40d0201c80c2c902c51003081c400c0c0040c640c0207100c030342c89203080c40b41d10009044500c04c1d280200d000188240c02d25004200711030940360050046616000e4407046400035002240081b600400d40c00381c02c1c8144582140038502030f00d9010080d55807410582001445100040c00020500f403414003004181d9030400084107009400341e800302c443c034203c1d040c800c01140c2007010310340d458000081c00414003031460340290b0559000d21002c00001d0b0f12030809600303c0c061400010801b01005080902e10f07402500909002d42c4001e005000292014401c03001087d566031100e0000d00180c86108101c00c2c1203402040600000e5a01c005270071383c0c00309c1c64414440f08004400e442128100400c005050900c102c0b2424a00600003c0d0382d507a07101e104071000750cd4181d058006511345030100d41140c2c4100111000820b00d414003908507210358841a513028818041c050642d941c1c2c040000050729540083c502c502e015020300e58850802d41400d0703041040050440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 97043696 1250 97042446 97042457
    0x9120429040b04030b06010c05030a09170609030f1315090e0f100909020d0b0403020706090602010b01080408090d050601230f090a02160507090c031b0915050409020c060603060106 79
    0x3446101d40082c140e0701200d4024103500d04a8035401c0050321503004105001e040750000040e044985078105181d0f0303044440400c40500c00003440b154080c1c03151030035201103540b03030410400046041074070b03005001701544124072120203d0303a581c5080ca420f840030044402042082d00204145000c11981c95800408119a15558600b0f4042442e11644ca03000303510840c1d40d196501010341d10342100a00d078155101e648511a0306207418040d540e0f4003540701d0140000c19041e800f1844500c107002c4c0c11603561040c2c60307052007a11196928003c07904801700713054000000c1c401400102d4800c11502e07000700701152100d1200c60700d01112010000c003c42d0080d00410903211061040d48464241d160f01012001d00140c6800d203202000c3c012165000000d850741c820703003c0108001074154880785907030000c0c4e1400c20072810400100140741c06100d1480300480c0c8405010000c000c140c10018102c4c44451030640c1c41c0071b4407618128202e0708011840c102c00e0b400141001700500b0204141c07400342001d030814 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 97044946 1250 97043696 97043699
    0x10c1b02010e060d0e0303040b0103060b0102030a092c16090b130306020c01110d0e0106120201120c0909020a05070b06010302040b031303090504090809030c060a020a0b0912042904 79
    0xb8002c000b0300300145014090000d090303002100d07154480c13181c1c10310b18403d90346d403400c00d41845001c02d08280020748642c0d113020090f00040d0b0000040760000d0205071100c00d0698a400b03007118034000c280303080c42200c000201d080d020a0341164040391080711500286a80c0e88508080100302441d69007024448090401907400703080303c0803d41d1403c81c1c2d0720580141c1c2c3d036104000754601500441e0f0320922864000708085800340710541202c9139502c82c0c2c6000300030081c1e450007204074010020102a02064048060b107402c1c1050b50003031541c0c0c0e18242001c402440e910380820040380e100c8550034000036000704850341001b0420740c10301d40001c002d203815804d0a080c00d4842401b80300c0941001c0000c180304001900b05406102c0304402000010310030000c1c05104d080c80c04942c0d01450242e8420701402d025040c0345e260403003c2d60408903007940103200850b01507031403100c3d004008d40441982d10821105031400c507410700040000d0103811141040300c0000403241582031040b03e00d80c41e1400001e220 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 97046196 1250 97044946 97044949
    0x70501031a040e120a090e0606040b0a030e0c0a08070e010b0f0306060a0216090501080d0801061e09051c050609070b16020103021b01061d10060e03030c030a02010c1b02 74
    0x19052444404490000d1966800c810f032a140a03c4c007204840010740c0440c03034205154205400700215a040d4a203100c041d039400080182a118902030748013900b0041c826100d03014070991056a210b0f0390002142c40c4c400307000f03000862150042e071260415612245041c85041840b00b80b190051003000c5c1170a0406140c01c8142c24903010060180c4e000d904003252011036148200804680e24541c56101c1c0c4016403a102200b000e81424054500d80d449500c11056125202d00c2c040c60481d8040c0c0e45d000000d90401918011392509400400b01300300417102c0104903581c4a441c00a2101354107000e481781d0b038001d49040c906042c80100b00c102c454006410410120400703104442d440c082c401d120750107520551006030003c1c09022485100024200359041181105612000c00c1c0d8010b40000c14911625260700b1170b808074100d40c02e80c0901045242007091074040c11568001200043c10340341048001071000785950000c9102a005039112181e450540790000b41864901103048241350710628643c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 97047446 1250 97046196 97046231
    0xb06010509090420030304030f0f02060f0d0c11030a08060609131a010801080a05030f070303060803160c12110d210f1b030815040e070303030504020a0b0301030f0b040807022107050103 81
    0x11000380c01c2c00ac10020f003800b10f559400440306d00350400918191108007810a0070000c007a002a100045924111820b04c21100001910081d0802c0d40e02c20066990f0001800758940021200540000c0d800e41c850b182c10340c0700d00030111200103100202000785580d400042007140e0680c428181d0303400082c50711010420101c02c4461000002c00255a1080545400c0b4000e0141c1d81c00b0804901020882e0011481d80c40020030038140200f080025031070300c0b002801948868031100030190a0884140c000500304080c00441030784c015a070308960300810f56150441c501d40a403000f00001c07081c0483c130540d80d40220801440c4002006d240c4407422103960301512070381c03010b0042695401017400007440d59070b854004501d000c0315501610040c55913817a014000d0301054070101c2c440c1e07400f80c0000c03420166200c2aa4103c9410140c0304145207030707a0321140e01d00d4501400a0f202106e0030048803001d41c440040d22101c00c1c00548034007a0500d192682c19080c04403541002d030406007801d00319100e03000c104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 97048696 1250 97047446 97047473
    0x5010e0105010504090c090302120a051e0c010318020301020f1e090d030c05010608070b07171305090406020706060b030a051f050f0d0203010f0203220b040b0601050909042003030403 80
    0xc50006030f1b402c03011500392207180943d0f00c020f500c8039502c0308440c882000484c00a102c14461070894525140300e82c8044d55414031002d070300321036034040c94440c11300b0340c0b180d0811505117a24806e1160031140d81c0c0c0210382664018050ba2011481c00a643d10342070303007000c0203605030307502c589243c9051441a000140c400b001240002c4c0421012080b1401484420741c0410010150316089a640c0c2d540c80e41106019002000240c400c00c0041d400740251b2080341c4200c40401e64900010311403c3e00789810803d40c3c180c0035100b514025400c0c801c03100083c0040c1710307140c040d06003103002075201d01d0308802c6d107000d4800003002c200c507441c00c50301140c2d400d0441407085006d80d00200d424002d40340b44540030619107600ca607406903140d03090244030180340300319600840c000e9000064600d1f4105004003241d00606000e00010030040405000901142e5112039040d08060149041440c00b0380070400204440811b032410b80304030441c0400309a8031540c81100b00516001680610304003407071921140d0008848 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 97049946 1250 97048696 97048709
    0x15010f0c0312050906160f1715090f0a0608060903040b07150e0703020901050301180b061804060504030f0c08071b0302031e06070309051506060712020c01170103050606190b07060f05010e0105010504 87
    0x140110b000700300b20b449c500b4501c50340542900040d01d02507076024071605003580d01004080c40d02c00b006c2144540411134501c02e059810096190600e001201c24265014003001d540d01c40c0400107014400d4043d010b000851810400140091030031030042004030b00043e88168881e1703161142d0346803005110760048001710342044031001380d5540d41001c01c140c4200c1594500040018030104000c110300c95104600990207907136140c202e40ba1418094035a4210760710b0262080406029040000b20a12200180075544d194100e6119599074086850709c9030f4000103019411480d01300c007103030640c2046400c5d030100301072909001c0041c0a07240c054403650f0078400b481c4484100400110300b5200e100c102d40c0d1096100c40c19080042d90000300946a4105031603039400500c03406071941c3e00000784402e4505030ba030442e0141c20540c0b10002000504091000e0028041107103100010311032b82134902410000e4041d40c000704101740ca0519074400c44a05801074414000d007840140321a9034010203540a8402 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 97051196 1250 97049946 97049987
    0xa080a08010902032a09040903200309060f03100302120a050c010203040501140903011401031b120b0105101418030709020a0e010c060b03010603150515010f0c0312050906160f 77
    0x3e06620880d800e02c98081b0b4a0b0b089400c00c0e400c5010541e1010705011998006240c940088104240700d58a03442650502548a40240100d0703091140c2c800046410000c428201588165264041031450801c0f40701c05088d600400e402d8003d00200388035001020000348050b5151505002c0003030042c402241c0d15664101c000302d55a445501d09502207c810a0480a090707200e69581c42c044007208410480c0c2c19509a0001d00004e0200202407242c01d095807000c085515607082c90203020032042c80c0c07515142081b8190084103030701020714005245024584054041018140f400d045ca03104407588461801407041000d00c1c020faa02c80d41400181c1c600b40791011105002d402c0180203007400d14441d075815440d004002040100b10301ca1030749134030010f14060000390f840c01c110011501b0341c1c03285107010039100e4a140004503c00c0400d900700a11070b04006000801112000086800842e083c4000d03520580c140306081e80d03101507000381c1e903c842c6040e2260440f0510002c103e005c001d190300004d1903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 97052446 1250 97051196 97051261
    0xb090903041509090e03090a0e0106050714012d0605060708030109020a05220504050601030203160509030f100603020a050303072d0501020304050a060506061303120207080a080a0801090203 83
    0x43c0b15003220740c000c205064080c440c0c81c4a100e441900d80c0d2080000c58450b812a6600055903e0744080080c100c5190791602410640799403541803203580942c4042909550360601008240d440001032004500038a54003410525642c80c803004035030b1103130002ea10404003880340c80002108201180d054614403400580c644801080648060054000403070481120081044400305244084012a14104c03424086c903124140150201c1c40169441c5404071087c0d0340084c18603009000425085d180a011a524094500441424428880481074420f622060704000351715020a18130017518084024601c0c2c07580581d10b500d203940c40ca80302000300780408a410008800800130a280e1540c211009558900e0f181c900320383c459a0700d080c2119070a2038a8041741c41414910180d818100c4a080302c0c01e496030464075650440780c0c51032102c800b1441608008120940107220111103144030b0304085445503400100a009032205030004c00300f41d48140200090001032172000340001c42d8128100000304c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 97053696 1250 97052446 97052489
    0x1b11060606070c050603070810090501061706010e040e0604120302030c1b07050604030b1f05030a08030604020c19060c0c020d12031b1101060e0702030714010f0518010b09090304 78
    0x41643d607026960200c004002c0000e880e0304031103454420190001201c0300243c840300135070121002070050000080c01e20403641143c074584076003503801480504200d07509003501400241921004159110701d80c1015090104100010708d03d940f104110341015825441c1203400445640160f41e140c0e00c1000c101c100805103224184941c90240030040c0059940b1a00c1c0d0030709850041041c1c9021b1020f4418101d19000a128000d2803819610002c001c1d048206064403241d0840d0006491940e000b0307402c00c150642c129080049070a546034000d80c0340140d514500b00a41210812407140c010300080c80300d0b0800581d20401d40001696102c1c1d00c4215020701400214024801c201c1c080301c5801042048215140d0400036050039140914001c2c428a80c952443d40000c039021f072007020242e8810301060300062620082008000814000040c100703250300c40c0401616001d80e142d010700c0024184115000b102801219040c0e5803e803104a914100035030400c3c0d80f0b103ea84140d40b4003c16011641000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 97054946 1250 97053696 97053713
    0x5011401081b04180504110a08060c0903031308010b090f04020906130f0c0810060c0b01051c0803070c020a150804021302090a0803030f070f02060103080a03020705060403031b1106060607 82
    0x160004400840c0e44d0045031500600500d800d4a055550342c03150310f0745000c40d02d804907152050b100c0c46e10240c0425243c80c030740c01e402c6401401701c4591501050100a0f070090103105888000c005920000c80c80701103a005100920102a0400243c80d0b0640104009030701c900c61600d42295050b244410700b034101e128954010300340300c40d840220a08001308a0719455000300c81d14000d40c407274000b6101c4035a44440646a01c0700e107240040200c10464010410380c5046809140d003901c8283c41514203001c956283c0c0c081d80e200300e99038400304110407100750640c204040e0381d0026000c00c49240d00303c01da403c5405050f03000000c100034458000312410307104410f119010341c0d0b5450703000761481c806c147d1260ba040c0d1316600200c82105001160800207043e082c800c0074003c16400050b00035000c0c50b400e64446102960284e031205003899002c10000c80010010001244110301035074001500480c000c985200f80314140482100304402b04501c0c80e000c640100310150861801c8504503510a40d91404152 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 97056196 1250 97054946 97054949
    0x3070b0618040c050a080a020307150e032406100215060a1e030605060f09070c0203160e09011d0c1201060f030b0708090607090b07140601080a0605011401081b04 71
    0x90100c01d20a0100700000b01d0b209405661003200e001140a80358103000c1d6594252120203580340d40940e400700980485204030010440c5a80f80034400461040301191404010a4404c1450500c02001031698107441e030b0b440341c124204582000054000b0b0800070350b0b6150400c00b140000c1c81c440c000c59501c1e40e030980301e44010599040c16886a1442d42ca801054641910060b54103d040500203201841d04880303109012034010503004107502c46400485200880c11744c00c03609886404c6401054961500302000100900302c0920307018503001403542c0c2580c1040c0950f12841c0503400f03504200c003401086600c0e84003402d55642d5843d141c1c011810780540801d0344003ca11085950001c014440846280f51050219444281c02900c0b2500669500c5030212055000507150180c2440002c801000421506010701d548019244c10160003134203040d42a8850203035a8071010400081244c2c0317024a41c0140720200aa1030a00e1510b40042d00703c5500074041440e000c5080400c0d007284d1411b806030780 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 97057446 1250 97056196 97056229
    0x4060e0c0a06030b03010501090509121e180f010801081b0109030804030308012903070807030221070207061e03090302210711030c0d02010f02010e0f011401060c0503070b06 76
    0x1d1141d0b10308000d4003c090580300c0c3d80c040d508010000c140181c10b406001c1c0110270700c0c001000d12034001c1000710080d030005039002c4050540800d0122027810b5038800350208551454603071110300b54070f800308000101034840a5041c0325103000100400072011507003003c05580d9000b12250031900701c1c0100c40420032a000100b447d04013003804403e2560140203035040e079809a2424804030318159980401c06c006800c07200000004200188026215450139078000300729050241c100101120781001203a048210140007200030801c0100c02e903030421a000080c83d080c1482080c0319600001c003051040e8042c508818140c540403188201842009405001400c14807010b00c4281425001c104952140c0300655106030b041c0c150640928001ca02c00d441460014026003e0724110381c015101004100091001d5558441c015456501c00307100d844a2844600000540d0030a11148020800810b0b04540c04000d658084800010400412110b210303402c42ea601c1801d60f0748000103000e400710b400307454 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 97058696 1250 97057446 97057459
    0x29030c01031a0a150801051507030c020f04020c06040203120c0618150901020a02010b060406050a08091207150f09020109030305130f080c09150a05040b120303070c0501061d04060e0c 80
    0x40c02c41c4c642030810415000c2551000480d1344c3c3e40c4100b040241e040e074110b41c640b5030100714640010b40214102c6039038610241910300e8454a4100007800c90f0413042290b000c6421180810003146024801201d01c001d00681c003500b0456113070083c42e5501c00041000c2e4200c034000c0464000102c040110300c0c1e410300008a40d4200d0b103000c42155001c2c0d0043d0b2940000b560900525108520700041a0340564041c3c1e610141040800007080f110010085c009201c14007507280500c2204600303500500c01240030710701c1c0e42d495030280c80080007103410400d00005c1c403620300f1131000c0050381d001484104498040c076040c0d4035885142105064101c041d4010303c1070340300c10240001c0002e030106051811713540c01c881b454211f40d164070b00554540c542c0b06149600590440080c021881c2592110442e1100a070104104042c41d0f48100c3c1317140c1c001d4a170b21010a01140c0d0042c1001401d000b1500a8003004880031226061080300903004000039000500650711115060100c401c100b042034500c40c001032a5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 97059946 1250 97058696 97058699
    0x903012c0f07060e0907140a030603140106052404080601030309230105030c130b030a050402120c01020606040902040b0a0603021b0309060a0c0219080129030c01031a0a 74
    0x10424128040c200060580504082007015001c08140e41044031029202c90100740c090504200e0500b200918540500200b00c9182c1e005908080181c4242c00403610000342082c19800c20804003124900c86811580c1411001d000f107495689085501c403003400c0e8001c80304249044886424040c0c0e4100c0c0000e0b205440002040c9544001403008592944000304c84c12942c21412500c0c0e55015804540401d10030004101005c2105000300401d0910f100c00210407612848494003640c400d4036092840c513210301c2400154500600d0b88210300790004010880c41c0700410000c3d4844c0b000030b01080c891940c0340079160541d1039540110808010007003100650a4440710058000d422410120b81c21414071295882032000000c201c0d0b50801e0001c151508040000c00c0803204008140022070300b0007407180b40100ba41904a040c2005005c1c18000400c180c0302900d42d08c0642050f01f00c4000100c0c150903151200d40d2408036001c0402e54003841c0109100d0003050310015403904654103540c112207681d60 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 97061196 1250 97059946 97060001
    0x606070f0602071709010921051615050301210c090c0f02010b0d0b130602090306090a020f0105030f0a05100803070503030411010807050a08061302120a0c11070b090301 74
    0xe00702c3c14410103d03c1088040190b559a0900502801c640440c94242050281150a03080990403412045072507540480d5641d8640c02c202c1200c80f5500319664002083c00110744002c202448056940352443c1950f141c00300b6104015094070070060402260350000c0d050011140090f009040d50365030601044451000040600703c45004003001940380144140749071400ba100d050f5100d40100c010a12611000042092030140400c1160095420050f180154506001d80d9200320003420240c1070711026401800070480d030302e01c2e10318101300081007001404800111080d40201c40c40c5400140380d0707114100381e00f80800a40103064103102c00b161110030044000000c500c00d40c801e440d50480c0e00301c0c1d28015114101c0c10344000c404200184012408244604200d692014008041c1c0a40e9610218410102c1e40001400a5099107003020800400f100c1c1c000c0e80e02c0d441952400100d008000c0c2070890700d50701603004100254400149045480c0c0c0e00750011360301d0f903000361100c4101c00c04821 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 97062446 1250 97061196 97061201
    0x9052a0a050604141e0307080a060e07260a050102040b0d15060806091e0406020309061b0a030e0a02090c040501020607020c01120b0d0c0603060f121101080606070f06 73
    0x414980c41808504004100c50070203600340c80844000000408180748030204100c4c16501e600443c1c0011310040140707604664040040c5d6005000c1c1201a0207007401b6410300b1025100866481151030384456420132040c0200114946ca140015040411494904050324102580740002520941c00850049828046c110003402e0340d219000e000c20072010358540840000380341e4800d400100d200f80000681604204040a6000e0b0032031074001c4200709240c40e060808041940c09807280f590120400c80341c1e031001c00040d034102200300400041c800d1485400b182c0b52003080c0b091002c0580b50403004210400400011003113540c0281400203525003680c0303481c229041841170750f0052140c0700204a1090000c1000000d124040e13650440703000c1d905060001a003082502c09402281015100e0041044480001e000c0e1155039004100245451302c03d05149031039400003951004841d00040000c0c00306200c50241d68000e0a04012680e00e41c000900305d40034600c00074241c140000e40c03071004c100139903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 97063696 1250 97062446 97062523
    0x1050d0212101d06030604030c0206040f15030b030f0c040e01060801022706130e04110904030201060302010305010b160b0705071505060301060611030d0f0f0903170601080709090905 80
    0x30f08180a0a84880c0b1845042692507542541081c5e01150210b48a8644004107500190006190a96540413200381c0d0305a41e01c07a841900d01503040c50482135050084014142c1d00f2801000920010226107440c0d80c6e80f001540c3c852507440c8205510002c00390403d6000b0b04401d00215240c02c012034403a1a40c0504640621032404d10485000081c940281564012216040903410507824035144070b0001e80050301c2564802c2080d28007542942c0c0b40440d45114034482c0c0d0010030307440e113188009403d840301a00b090340c0301501406905011144900c80c0c601c0150407460011090f285e405065841e4880c542010b032446104a05251b0301c10140e4000034001d410035002000126569202212946c00000019403030741c10070006108049d2031508131726000c6c520384400260078240c1400e4181180e01114048011131300042d905130b00f40f0001744205a00403401e081c540602c2c508140d004003c044e0500403003860503921004081884010061110b90f611240c0c5032100b0302d90405208203045120 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 97064946 1250 97063696 97063709
    0x106081b030f010c05074205180a0605041707031110060b0720130e0712080301030b0705071b091a0619030e010c0503160507020306040201050d021210 66
    0x101c2c180c002072848140310350320070307440c6590358507017082c02da41d03142c9800e042c107500004095160703480030380191951540d42d0001d020061910020180110031a801030320b000030910201d0390585d40002c0c480a10200307041c2d00c000e51124000900f0783c1d59160031880b140d03030020408200840400e12004254025003d600000000c404450f8015548604101a00c4150281485d555004d01c0032030004ac40d89503001c0102d810141610344502151004039140d030301c5014a00c5040c03500c64480481101e801d00c92640540426000003c414800b600c0e00c0700710f444188001031448984100040c6618420b00c1540e008a9000f0050300d008049051800c105078190301645003030910300319040c07425005100a102c0111001381c240f80c01c100345007810070342c503038419030a44041c140c590403104140a028802c1e62a840780e03648170710f5101e040034403149805202003043c0c0d1085c000208140409a500003440c41d030300c02c1e42442e055a583d0a0305900d90064054440c40841101c0c40c0418054080d802200d00030a6031407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 97066196 1250 97064946 97064953
    0x5030409090602070b0f250320041d040b040f080c030a03060f050f0d120309140109030810030b061e0910060212070317061c0305030402040f0207021e030106081b03 72
    0x150700700403806c403110030384000c01d40205001c284181d401c49404150010500e5080000b02e103c400e100159140512440801c0180301c0028140011540382c5047d805034540c0c004543c419103130030b9440b004604009031001e00101840d009c0c090402402a040b038888024240c1580d4a5600d00c0c41c0182c0070300039030702400b1052401d1b070704003003084d05041e1450591b100004080307003072000b00c585800104290003406e007420580c59104007404213036004aa00141098000005800c07111414006d00604000e80414001c00350b00c0c5041003c940b01b0b1010136040301040b00d802c00c4007441406054403446101d07580c0307a007000300c0c0c9003009039420000324480105e46140d000d44803c007004008295040c8a2000028041801859010300052441c10640d52054000d0101c15074002e0000a170084100e801e00d003180003500004c204403c43c2824000d045503e14a01d0080d030070442c156000aa00144500c0c000306152490180c584d4580d41c2500103000034038204068420f92030510640000320b8000544043c020710 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 97067446 1250 97066196 97066201
    0x90e0a0905030307030c020f15010f05030f0a08090a03021302121501021504080432061804090c05090118111306050309010e0d09081c120905030409090602070b 70
    0x655401080400c03903018002d14503540da00038050f0018690712201004520800284950240c0100715600281c044905610340b50340c074103000380c40b8542c07036600418080c0e040000841801640001e0011410341d1105107580c40e4103c0ba03000c1480e20386240d002170f60110342400720501c92009030b07005048070700c0c16900c501880c1d83c034103c010300c10013a05040280103900105440d82c5908003a88103d811520039a10780b481c0c181c1e22801c803600c0c00c250242c1011500c0941d02c0400c03120301c9607100000c0e0244180d1305a410182900d0701030080c0305513942000d004030703140d46200040202c062400d10140400410750f01042d40c456502c000114680c40c2e9600c44246400c0c03010484e803a4903c01d0f07600401c51001c80080f03640c03c206084510f03401c041c00c004425900d0f07500f041d0030310400b0311040754103003180c0c4d80d40f074000d80c90942c40034501000d952490030800300520b201981d40340c1c0321004032001c0b5810340c1c0100ea2005586441451403060b41d0100c40d00c1071505c2d0800082040d4bd400800740540914110030305038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 97068696 1250 97067446 97067461
    0xc020105090c06040b16080a0305061906080f090a150f150b0a030207080c07030b0708011e0e0612120d15060801051306090c08041b05010516050307080406090e 70
    0x2140550350040d0f00220612040101018500041140203006030b03240c20032170301640d80ea41c1503411007010350010070344030001c01031141415004402204504050950388a20b0700f40003404d061400f07452251201c449400080c52131000700072046071643c1c4004c0d14008103104908460050500c10b178031001079030809908280402c20010700740c0984101d81002850084042c000358000d52100710100c545a01c00d10681e4482013040c000000150300030103c0327000c20b2502400c01010104141c0000300000090207480c8250040004540142c4002814180d101d454000011f40e0849803041e0700c1003a44030710322071440c44d000d010f0302925000414107028064081180c1210408803001c0c010032001849900c01002207282c40c10000c0700d554210340c0b002403541c1e1508400d40540f00c8030b0041c1f40c04126800207000405c001040b4a52080f8920458512190b040030002000c921170408120740212a41040360140a424400c0320800c035030114040e80d80c4ca6440c0c0010b42b4500741886245800032403600020a41c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 97069946 1250 97068696 97068703
    0x18120c060b0402180405130f060204050a120f03142b05070e0108040b06040f020a0e120105010f0b0304020604080115092004050105031f0603090204150302030309060c0c0406090c02010509 82
    0x10003482100d8504c40045a0060000a2400402d101061410301420700c001c034030680c05d03d055440c0100c2000d079031281031a0a00050900c16844800c05445000158000c80c4507031100c28010f952600c0c0c10211415001829405401880c4041c06105020081a81340002c2800c00c030f0a0700d03005075030a010341c2d88c40d10015220075085103070142c0170031020b00000e07001401d0860905e0344494004c000054040084840000700c0e005054a4004104240e07641185450030600601805030018001e01c071a60416100c1d1004e40458400c5141203440480031034210f544401c152005425180001c210144403d140d03030040300d83c0303407003000b090790302e400c4003042c0c11b000c0c07408030b0311080303080d80d121500d09890100115180d42c0300901507000c0305001ca80300802e1010022240c00100341d00d0f80c012a02e1115070042008856800c101c0a07801d02100707404100585011003507641c0b040d011a100c1c3d0725400c0f1070f6405410503820f13811231070b4494504103001ca01b4951941c41303101c0b1707807010f036008100ba6070742c10824a80c2d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 97071196 1250 97069946 97069957
    0x2010e1005040e100b1207031d030a0e030f01020d05071b030203190509220f140103030305040c030b09030a1d031002090d0501020f041401020607050d18120c060b0402 73
    0x2881c20801030040f51a40038100da040040740320191245581c0f20445240c0f500b10300f41c0c45013181b20345004c0c805001c3c0d250240081400120010484048171245156070324030401040f5401d11000e40e01030910b50b94140943e0b03c009510500a643d981c02d0101c48000030101261941d0120325000b90000c400c1c1c6103e01c0100d00e09078560005c52500400c00c440480070422840207400b04801008180402d44548095400701002d1f62264061071240d003001c60260348071070009136141450810480c005e00904c6952034112a01410002010380751130400309110740c0c5580001d4540d0500d403007031001c1843d00000511307061a850361500c240004075400003016030030041c00703c0e5055014030041d055260a070384c024205400b0090181e1450300165881e1400d980014404141244020804021000f00d040749058803440c01d07c09007009140c2408042c001c3d0046040f610480342d174882030342c2c1ca2170301104100700600b80c00c03032214401002c15a00c010030021580c0401c450540c2840c840010314200790080d00d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 97072446 1250 97071196 97071229
    0xe011410140a03090f080a020708010b121b010302071a010305161212020717010e100209100c0c1d10080c010504030318050607050d020f030313020f01030b04050901060302010e 77
    0x14544a000b94044001d014040302c01d44035094046445400186184000c120340c40594000e40704161901e1f00c05030850f060040c1e41405a28900519001d050005c00c81022078000d1221001c1c0300c8200000480007405000c0c0c00424619104281d042290340030425103041324810b2080b20440f08148042039100002da03c030341e00e4610f001e0441400091034000139032840004a204540ca50f994850605502c403488080d807032140d0359651656000300000f44401e00c102d50f0000b030150320300707800180403e01c0300080c0c801030010000750b04040400c00000501c41d4004200109200300790203c801c140c0d15044505681901918040440024885034042100002c81c981610f4803800c003443c41c0c8007a03880d42c4001c2d90b0307804070a5aa40011a4a942e540d0142c410303507020300000c1c07904070b0003e100a40f818180350419070a0751b00a2040224000801000d9070000780d0648080c403001c0d01520058014140c03040c049035001c1c0c1400c0412001640540c80007045078001d1740d480610440a0f018000b1b051108041d15 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 97073696 1250 97072446 97072487
    0xc101d06091507030201090b0a060e0105041a0d1707060b12070620100509030304021908070605090d0507090e1002091e0a08070803040603060608130b070203040e011410 74
    0x503600800e00300043c0100a003e4000480d0013081c1c1c6e0780b03040b1a4134040b149440e00300d980e510280700040b14040d055016100c103440c20040c0347d507160360030241103007155545403140c551220608100300400743d03440102071070b500d60a0707207480292400401a10390010380301c2c01420742d0f038040020940b000400c01c00301da2042d00e5014800c1070940c2c84480c2c036424030605401d1441100000d044c044041e10846114280ca10302541c3c880c1410f10403c200240e04064400404510f48000c0c480c80ca00464000219109810569518104c42e008640901c0e0924805080c60080070b20009a00815070440c1d955602640d0540300d004001c441c1c00c0040b405240c018a13040b107076014402d5058000c0d0108034007900c0c0300528140c0c00c01c0da1034250500c2c20145030080020307131300301042c20041075406025480207004103080440745841d041500550000d998039000e8600d0144002007070800303009104640c080c01c1600b0b544a26503841da454845c45900c0d80100c1400f546003104288500d910401c2919012100032a05 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 97074946 1250 97073696 97073719
    0x6160507020f10050f031302120a0c0501050307030603051c030b01020a1e02030705060d0b0f1e150405040f06030b010e04021e040f0207030c03030c18060503090c101d0609 75
    0x1404103c250040440003131010801c01400d00401c510090341c072910644240160002079841480381c030942c5084840b5099104140c000000b56980040e002038034401c1c41c0407602c03a079456100b240585280c1c0c0c00981070303005229000e02441c0c008004044032611580b020310400c901c11004a96a40120030054038039010401502100c2d05416910048603000070304a41d400307130701c0e540003900c2a4459411525402d549111140c214203080c0d8081c2d90280c8212108500d0120004404c018125204426449240c20002c1800404480c00c1030b07901410740500104031002c0101000d00c02003030a400305441e0a4241400051000d0920842e2071103a0f6000d4600d00c440c4a05d613451215103606410740355406601c80300c10200400303080c406030030154000d030b441c102400090f050107022240a03601c0d250420800503110640503142c0b01c0d4410882d0301c0b52600b40c0daa941d0704880d05042280004030b1030340c043e83d44076140d6181940180705401244940c0d01400008045c0410400c041c0310309003d0301c1e00507254054 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 97076196 1250 97074946 97074949
    0xe01030506030f0105131a01050d02040f09140d090801020c071a041a0306180402150a090503030307080103150b0307030303021c06080105010819020f0d0201090906060206160507020f 80
    0x4500e0700260068110340425507514929802d488046412408000d01301c504841031101c4e84c84200c07486184000015184e50500b00443c041c0303610408041d0046440303500a4207140100c1d800030303000d40d40003084c030b112001c00c8000c0d032900d6809040501c8009481207901041c00316045c801c40304154420750041012a180020b0611605145070101a40b0764043c030000849031130607a4800000420480343d5643c82c600801000742055101d5503015401c48180e04101c0140c075109054002d07a09142032b11500e406000800301d40c80c1c01290000e41d0103000202c1032100d040d0700004101e050764440c0c4940360408070980702030012207251034101a8141d108590400c003283c0250b0080c110a42590188505983c080b410b00064136039513401103109070b65407401081003800521980d5000b40d04c250071004040708640004103003130503010005200301d41406000c1c086a02900065004000c41a414000560b40354000382d00c803101180c54100c10381148003440d00350741c82041214915036005010701c981c908281c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 97077446 1250 97076196 97076201
    0x9101b0c05031315030e15010b0d0603020a03060b03060601020d1205100803071a070903020a181d0102031006050a12050c310905010f030609020d020402071202070609060e0103 77
    0x106403800d0008000e035002c0d00f0301c02c80d43c11000e815400c12008148800d000700504640b40340e131003c030b07031078006d02285012001608603003411100301030000c80d141c040208400004002d5980002d601c0518410000101f00064002d03031140c44045050b0780b06903079418010398403010392011400000780780c1701e24203e60015650085030440a40c0c0c80031501e02d41c503220704500d190300040003601e4000c88102c00d81101c145200346180d101003e45800c0c03040c00d00e143d02040843c441c5005000101e6240c420405440085a0151030113071004040d041c40c4204031080c4038002d520035112118001005880070407118040c200700c0d100c3c8092981d510320b002801e80721120003410701801104071400304110440c00204205003003804c01e4031804814005002d200d949124041c002d40c080c2c1c852034204001040308504035400d140c00c4a07000400852803510030710002d5858103102400a5100e071001c030784c000c14000d03154168003102c507c0341c00700d4000e180c50700e000755801052440340e900010094030303100410b94484d8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 97078696 1250 97077446 97077467
    0x20d080403090e04030c02040f0209060f0702043309060b03070305090705060a02030c010608060622090206030a0506010f0305160309080408030a0206072a02150702030f0609101b 78
    0x74505904065110350100c40032600130340d4190005080441242d0640c42c04d403007604004410000218903001414010410f14040c003107240154100102d4000150341341e58001e5003154021006613802004140501000b40344070510f0b55040722780005010403c040a0310809050310503810300c203030465036049003c801401000341441054000c903100000c0351b072140c0b0080c1072010802c0c0c0241d40c4941c916507680f42112415840004136500102c107000058a502d08050520003544520350002c12001002601400184d20001d4201c0307400001c0002c80845940308034001c05091340c40c02e4080c03140314000c0b82501d2041e1000032170740c6025550380da42540030781c1c018900d061280301a02c0c2825660800039003590889041d100144c0c11800403c80800c1c0d014541c0d100310421300007600b0030220407900d10b101440107258024050001210180440303c15074042d035250550081c01c440c001015003401325180da0041c2c503100198455002030b104a101180034824081c1501d41640d004007485480032035502042 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 97079946 1250 97078696 97078703
    0x804080906090d12110a150c181401080604050720070e090601060323010b1c09050c010e1212090613030524070818010b0618090108010b01020d0804 65
    0x2c10144005499154800800398024800c105241e52080000f41110003200780c10561900100c20000c00281410b08000920394a01000200080400b105030348030503a408240911007000300c0c00160485070440700300301c0c03031000b0f0b40ca6040ca502d5550910040d42c4c0d040c0d0f070040c0403c0b00040c1543d100140a44101c5100c4415811a10742981c2c0c0c0c4178200c0004d6058a622166070004001840025014064076000000c100945007200307054030b0038030090220602540c104280e001402c409681c48605047d0100780403803204011002151034490b90b10f00300340022601003002c00030720341880d16250f415601c1800ca040090040e40b4000395903c101544901445a172080d0240582c14580e0200d1a890001d1803051008001c0340480070382070100031104160340380f007521070f40081085955001203101d40000065414100d0b000524980602520f1440111604508089110200c604006c45404035207403042d80c2406450740c03034491150a075144174030700328056440207501001040c400c60200342d02601 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 97081196 1250 97079946 97079959
    0x160512011814070804030c031b060207060606022d0a0b07020f010c0203040b07060203130c08060f0105060703122a120b06040f0b03042f011b020312070515070c03021c08040809 77
    0x40203003050f940c4150409d064400a902040c803004000c907510456001d00060b000521540d0100c2c1011402c00c2e109a81c5948038100d00294600381c25003c1041111055000c440c10249140200000b5079907001c00040602540c00c041030b8440150021048606403a5002503140c0703406c4081e00c0b060060740c805400380d0907080728082640045811818644098100800904845e0074043c400c0c042ca4a0182c1026104130002c001e8040000c0c3c21050b0b00140e07061452020544c03442c400900044000509040400c03016146c801c115074652120101c0388065109508000716a007070380038070800b40aa80500c89100e000d0800602110b602103010f182d100b441036444200304c50700d169060080c0e01c48060b520f55041c1c640b2035800155178001c43c049041d8a04000fa4400c0006582c001a56804000d04551a24240028200e040c0001440036101c074102c000707045a09401c05080060000311088420f8005025440d0782e80b007a110301c00e5000c8600c5c012a500c0307581c141c89039100c1c1c0c25160b2000000031703031005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 97082446 1250 97081196 97081217
    0x311011409030303040303020406081f051c020907020d0f0c0b01031e05030406120b0d0c180b0307080f0c0603010e0601080c0d050a0b040b030106080303160512011814070804030c03 79
    0x10b404200441c41a0b120341c0e0f02581366403610034040c100005c0544400385596a015084841c14440a0000100c0380304541c400a00061007144003049000f01c180650005c0300401001599600054056001c103095504c00c2600d00007028102c0e0400d294400c02031018105600400114550044c160700003950034400035254405542c03114a075034001e510036400300c0e03908001080c2a080303034801d00c078103080c080d90980c00001042d9581c0700c03a85d41a0040710b804101801098920703401950001184400107030881d42c40603144d000c21951200403c0c8ac001b030910405d0011440c07070500314162812100b4600014815481c0c403401581c60b030301d0081c0301d110169800c0c40301001c48a4540989030007036928920014000103000240310664045525450103681400020041014000110303a4024008032401480154030030080707030302d445441221900d5070708410010915003101c0962600d00c11680404100c40a07100d810320031001422100440492030890010f0003081c000c12006407610312030303e40545000b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 97083696 1250 97082446 97082449
    0x120b0411070c080105010e0628090f050a06090c0903121209032d0f030b040603060507020706020105070215010608060a090510030240090605010b0702030c09010311011409 75
    0x29002014255400750ba5004108000102072184602400398090040000e2805c6004164110000c184010540080061404500c4400b032001d402402285400b441081d4039030075900040d02e000c0d03076800c2c0c80030301d40b00c40010755404900c1070407114180c03074581c0c8849500d180c4525111300c0c0600040c200340b01d44004400031191117881401c08003071282d154003135910300b941c0501070340109440d180404001144070300c0c5032a82d0891110301c85c003c3c0e146000308003a04483e020034041c0c02c0e10350005003224202000c0c040402c2c0c0100b04076043d5041e81e1300070011990395074000ca95500d030018041c07455124000041c84110300c244001c0c1d501c41da020f090740841541d07440c00c5100302d0b48120341500440b81c18040074030841c80c10001c01110701d8528800312982d20789114461a80f120b06c0c01d042a40040207640140c00c04420ba00140e50068000c0010031803503964035150f03039040e8041d030000c900c24040c54120741c11901d000c030b1f01c07141682e40000f04122101c0f03840c0d00649401e1003203940700c011104188600c4071507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 97084946 1250 97083696 97083731
    0x423070e0a050f070801060914010c05030c0706020d08040b180a02210c0102010e0d0503060307180f0605040903080c030a020d061e06050c0c0d140d090e06030c01120b04 74
    0x280065420000b0710703180500c0303840301c001e60141c090010084c500004101e6180d101c1c02c1c00d000d40c3c1048065184030707198000169a08101040018003d010200d01e130600120089900022911103400391078041c0024603044607407140858004209942000120307120303000c0d06000350840c031241000c803080c08480c0d400050034200310300703403203140e10b454009403482052091000f030424a0080c0000d00c054040d82c1100c945480000b4140c00c00c1000100005110b0381c2d00300581030040110080e40510340e0341c10740450703010309031141c40d019415080140000f481d0030305200c0d564800760503540c5d40c81c1c0c6403a080c0c1c000c519603101520720303c9110340a11211100d103080c1c2c880d0200038054011440168183c261491b140c50440f5130110050000c140b0881490b580040384151070010125021600d0810618000c6240da441040c1200e0f68440c000412a04ea0f070000b4502e020740d00400044005da56440c1d0415584412045003131f800100010031070541c6040c16000810b402a0040001c00c10100803a10b0120 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 97086196 1250 97084946 97084951
    0x204090e0a02030d0e010206040b0408120a02044209050a080a020906010e150304020109170610050406080c0409050304030807050a0312050f061002010b030303090102040302040e060423070e 83
    0x100350403415285007189000c114131440d42e400d0b420b01c4641e01c048440040c5d190040208081d2011407a900080c00704200c40048580010203512040043d0624401c1000290085d01541c1c55100d0582007030703229101c2a070702074484001c1e03c004641d841311550305d003c0071b840c0030b0308104024420500300100e25a03031031001d900d02408504000b408056414010030294820141c2660305002691400c00c8160300c511011074104031070909080d42d42d84651004849845d500d40c013081d55605c4020883d81c0100b00801ca0501a14020403a00f80844d20b90081208807081132060000980c4008207070040d034240b42e003102c40300c140100706803801c2070350780d0b214406950f000e0041112542c1040e0100000c16810450708411038803443c07401c11403481e01447c081d503034001c05801030307106a81c85200c640d1180c0c030035000140b46400c068140d0751642801c4008501070f4000e400200d100c0ea00b84003c1003100900010403d101d02e400c11107944d024102038605088021500700c0a44181c01031b40c4003c2245010142030751b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 97087446 1250 97086196 97086221
    0xf0d030905060112020306010501051c050103120e090f07030c1829120a050606130b09032a01030b0a12030c1e020d0204150f0e0403080f070207090b04020409 69
    0x1003001592800c181010016085681c01ca0340040043d005600d002841c00c0c155042030802954418078031001c11603e00410307544482c4607080c500040308202c0008007075120089a9152820304618510070003940c5c810860342c580c0042c80039800107880c28420380014420140c40d0a01e0811445c404400550f810029004000003580d020f0f4405621641c0c0c0595281111880d4141418056175510990082101405138450300317450f10046003142e61000c08540350f8180e50604014001c0e0f40e0006070005400c90f12043c1d03c64003614050400032071160030501d01d0181c291080a040d410f00200541c01081c0c901036407904040650303c080391281d8603001c000c41c100d000f915070000100580c58128009420340c0004400e260310040000c0040c0ca8854180c0d0416a040f00d01046804011109980c556022750212075451801c420019194904038940360055009588009242c0d440da48103a801c400203841100043e0311541c0300b004002501d40c0100b4280c04014009460540d0b0380170400203941c490f04c40306 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 97088696 1250 97087446 97087451
    0x60b0307140406080402010f1e030c0e01050414130621060c0c050303040320030703270503030f030901110c010c1101051003140a0206030c03150604030c06050a020f0d03 74
    0x11241e0000c1c0a01c0c214800d50080c00e1809041040c02090402d001e4402410300c49a644403803120b500607600e070400403550740801400303184588401400780141d01c5900340031602151500005520560495054807048500324000d42141000d000e02d090741e1002d980b6103980e0b25400030980303141401d1004113494500c00b215040410600b400402ca80c1212040b006200310400700c140007070780c0031060706da00681504003180440000321410f08043c0116110320200d00000030081c3c1059009802d45150443e0f100c4144440c01408001a02d21035442c090523034598414010501074000c404001c6074004250000030820402c1c400c000d0140e071708066452081da0351550340c0481c440f030348a141d440000303061000a0195040c00417207082000180c1c04042c207480c0c00301c071040320400020882041c0780703540a80117035500d03d4404603501c03849e041901c0d1501054084541c03044103140c8181554266600f0050050001d8500b4a0a446640c040c1c84550203600440244001141060040009207103d5403000f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 97089946 1250 97088696 97088701
    0x50601300b0606030901090510061a041202060a05130b030906100b090d0201020705060a0c12050a0212030604090b010906080106050105030412030c0215010f03141924060b03 76
    0x29040600c003040141220401116514042110700c0301c5950401d005854066694880175081c5000d4104c200002e0141e04c41c201c1c0881c0385041545c40320f0704884016020b102c0d48004c000d40c0410a114a1280004240990b43d030031000d0b203400001000c0c01d8181d801c0c0245040b151294010512805600041c152000401000b03040341081c08515800052007203507610580c00c0ca02106070700e02070b42400350b0203120302c6003640701164001c221150140c10000c02d03103520f171907003c03070003e00700d84280c0801c0390b920103140410041540520107940041d02c041d0080c01e00d4450350003000181d900000c00d8a640103445402100103c0c21503d034030f5008c0d054580004c5106801c06124909641c2030f51722950401208008110100301da10ba5100c03041c080c00e14000c50340900c480b000700c1c548099900000100b5001400000e00000724100303010880e881152803c040f0201c0310305203612106180d403100680b0008240010016000c1d0103802d10080030040da00c90802001300f40c407011501d090b04040d0155000006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 97091196 1250 97089946 97089989
    0x130e1501030e0105063006090606040606020307030905090604180f0506060a0609050910080706050c060c040308121801090b01050306060d0f080d060b0d0b040b010e0f01110307050601 80
    0x16485800c0442d074001d01c21400c0c0400400c820a820010101c0c010070351034601c800e4030010039144124502008201c60303160400e008c40c9901c0391019900300340719914201c400030300c890000c000d541585030580c58a0321994078007414481d18480c0100407641c842d03940d0002e03009811910021010b0300c0e00441c15a030b6480143c1c9803e500d4640041e0030103200d0381c82c0308410800d640c0c1c030400000a45600760b1f0f50080644900740c0b0740208a0f5140c12449560080002c041026503000c4060000d03c10030004955054440302c808010718801c5000c041c0903100c04000134104511851030340d9803c428400189030410040d01c04a41c21611881c0341100c41002c040010010341c901000380940201048030303c2d50802240b5034805c0c0d0111804000217003014404140c40d104ca040940c000e00082c040c000815a03507400e0700c0d400400600c10b0812446c448d905c0e094aa042d03551180f1402002e4010207011520160f2080c0c0054a00f1140c1c012800780500c020400407000540c18044a40245613005c490005203103280c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 97092446 1250 97091196 97091201
    0x60c08070e0303030c460801060305070507020103020901020f121b0105400b0106020610180e0c0a1e08060c03040303180c03140708010b090c130e150103 67
    0xc0109100341c2c001d10a018800d1002800c1b21213206081140c00b90040801607140d007180602c50b05404501c2d1900d805800f446412a4028004a010b994482407030b0b8039030f80300791b04569069420800243c014003100006500a1b401082c405070140101d440340462074941d50f291000202c080313040c0e0040482c1e0140c92032900c1a00c54a640141002880700707103040c50511f450318040785841c8244000b86908080400d04078001c43d8601121070b0b00c03c4a840580d0704014507961000e10402e1300500c41c03030000039000107801c165201a54441701c14403505072001d0320844007030513840340500f806020b0f040000390181e44480c5484020010170038440000d401c114002c6c000c000700e03a0301c82a2940c220a042045480c071110032264482c0d414100040d2a10541b00860b030000c40d500070080214085150200c2441054105005c0d8038207040304807a440341c1c0302c160450a803110348200942043d940d8011a40d0164100040c00c01d805281005800c000e0f65018240c0032840262406403c1c5558603500000c5541e150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 97093696 1250 97092446 97092467
    0x5031210060f030204031203020f04080601080a1101080402101202040504050a09060b09040c0e040305040302090f0f09032a0a0519051009050604060b0402090a06081f0b25060c0807 79
    0x1d0501314146860764a448003c510041582c008042d4001741c8a40c0c1c25107040144d13005030072150202e48241d81c480e4406035442800f2a03055803407400b1081105540c0d032080c12001e02c95036000d06001d030f1250001c0c0054680404203512141c08035000c0c0804280d60b2164844c8600c1488000c0340420110180c0c241801140c030105851405450502e08020116076500f083c8421240c05202c81001680d0380c0c02c1c102c070340d40a907800c001c2d400905402448420700c401400c079401a2000a855242d913180c1c84c5e074040e9244100000c1c8031407a0720b4031113541c1300f04000f404290a1070321904281c900512040d0f403030070b0400c80782040c013180100e44031903501c062100410a0461448921808012884450702d9890341e400e8002c00042c441a15100248003945443d019141a07000240c2011242c0740c8445001e0141c4404607188400c07560048203070107120110112440071100140c140a24000200c60201c00c0222240b19920549194519080005900d40f040301c881085664800500d810816001800840d95 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 97094946 1250 97093696 97093727
    0x6010e16050a0f020709020d0b090601030b1305090c150a02011437060b07110d02060a14070203030703030605090603070303080a090f0c030605070f020102160b040503121006 76
    0x41600380c4082a070404215072000105041800512116400c102d140c5600e0b5041000d0301d07800407a64003100ca500f030300150718038441200e00441c0d5070740b41030044088901c95000141c3c0441d4100c00ca20f410500c5134042d50700002494281c41681c050701c008624a012a0340c0c1170b0882c0d40002035840100c940c281305400030506440300f000c070581407007160010602d8008400814441010f01c0e202c00c030081c0c54140992800e854042804055917402800380241c002d000c043d2110042d040c5448030310b1404240007509103900510160400070b01090442d03c4c1d801c0750350300b444511003c00590300540d40401c05040703124401e9601044890900c800d01c16298409030001c0d0190744650320a00000342c02030301640d8018950100054003400908250804009036813025120750344542d004410f10819800a510601143d11021219a00080c2c128201d100303a4404220b4501045e4010f00001c00e510a86a0418060000c981c102445410040c841400c2580e0b82283c114841008218003904008440c01c189035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 97096196 1250 97094946 97094971
    0x60d0212060f091b0a1a0d0903050406020705010503010e0406110705030705010617030720060904180501051e280e2d030f0a1b0303020904050609061e01110a030206010e 74
    0x1221001700390b61000130701501340c8101d585502ca003800124130040c3c64403180000340a000343c01c5207040203402030f802801910014028100045011350140d000c890407a411900a05015078503600c805000303010143ea2494a900200904c17008030b2020030140c125240240000255146800300f0203859402c07a010185140c0c1081c003500000c60300392150104060740e5074002a5040d0b17a154001465803040240c0c003940149001c540c0507005170850040070001e4420380013000381e51940075a11221403121220303200700300201800989100018005c22560840c5c11050040145045884100359164401144040e40c44060840d14820042e54811084100c03c002c0d03040909860b0015910780c03113400312004044a00044040d0200e10031780020510040c40488001c2000881c50024041d6200240c0c5602c2242403601140c1c01c3d281100303070b507401218018146588030301241c081020000169080c1070511100600c924103a10f0240a0703440711610030f9010f4030240d8100131000000010242c46403071060b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 97097446 1250 97096196 97096243
    0x906060f03100f0b0a060201140703200f070c09020711040507020d11030d02040e01090b010e010903030c0c090c02010c030e030703020606010809010f18030e0108070206060d0212060f09 81
    0x4401042e00b007121103482801040781e45216078502d01500c0118001da0300410900e40c00500345034103521551100e4046809103c2d603444941045041e40c1e070500182c41a80e042c0d02c540c0e10106070a000030481410303010f048a003840f81c40d0704c0310b81130724038140e020803074260b000100c201c2000080b030b900c4984503004940c100014140450003c3d5100e500300524414001001441e00f030f801d504009031040300480d100300f95902e64403149600d90420080c0b290310348003400d064a80e9025070181003620503100040e52004500391460318100c0d00c862300c42c3c2040e10054890384020420321110b0003030f0006442c4a030008600c4a050b004014215030b04100c10118a400c180082c000083c0e0126103030381c11201c05d107801d884a07128840c0c0140141130400040c8a11440d02c0780c0c92400782054104c071100c590103030300c51072414000c410040d1203400049496034016042800007035a00d160007008240ca8070b00203080c074041241404001480c040064601e0000d4005600c10003038001010495007814200c510009003c49 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 97098696 1250 97097446 97097449
    0x2070b0d1e450f050f06070c06020306060c01060e01050f0109050d0f02060f34030905010f05090a0b0403021f08060103050a0902030a0309090507090b180a18050906060f 74
    0x1080c9001a01c0800c0c1000e44140c116205140d14080090460700c508440310501454011128001d4410454150185c110320f00716618010803554810811920b84e42408002c945c1d034003000b54401001b442d4401001c1c0071902c03c0107400d10541000d4100c0e00e54010895040c14200548050200c1445040110014080c0555102d610b180e070f10017944424000159a0680b001071080e0140d480c412249040c04a00c1807038071000500118403580e054410400c03070307144446941d002401414030140c007090700ca000800c01544144c1440e164a1080e142060918582c40300141c03c1f001c4a0740003030b288a402190a00c11b51400c01c80b00582c43e07000e0448582040b410391030250a608008001605066681c6d000030700c19207864000e404d045600030300b914001405464044e01c040c1031800740940075841d190004042c076010f04412415101748403030144c1003540500c610000701d164426400c0d0060f8a03a4400280c01c108020b0850348203446210100e05854070a0000745030990080c421442601a1441041c05 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 97099946 1250 97098696 97098731
    0x9050703020d021c0804090b01080f070804080409090b060906010203070f03351e01080a080715020c0304150315091d10020705070801060302150a02070b0d1e 69
    0x216641a201d0001150341400007455108140d9214044c0e4a80c5400102c00c02c501c030300040080c1c1d0007030303030301040b2003080a8011128040102c032000c40c03284c105004100c0c9035000b26030307140d4070038460030b44c4501d03003501c507011001170b9801d500d41201c6110200044c00440e00d09075a50341d034409020300c021810018682c0303403890031048121018060042c2e02c10040a044c11000c06403001040510340302072407410703021b40c400c1c850004445214020800307810080004202840701d904842c080002000d00480b00e4441c070040d580041411030b500e5003404507403082d07020140060541c520112020310740b00d0f8074040f000d0002c80105c41200d0101440d01805044010320800b18500b130b10bc00100001703424035072960755036007a00100c0d12100c0f80c0c418560400e58003650b1b030b001031840b148101d082e142c0e1656282817441c04e941c11400020750108145070102c849440810142407200b481d48100c0f141242d96800c0b0460307035800a0008000142c90300301031540000101000300c0381c0034903400204410208800700620 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 97101196 1250 97099946 97099949
    0xf0506090c0f0c0703021914040501141c1b0303080a060e1821270904021002190b0126070302010509010905180108150103170a0309050f0d0e0301090507 67
    0x810b590041020721840b182000140040c6a0207080380d0703c1240010030b0021036440c244146149180d0a071018900ca0800340540b5048034030b1540d07074800c0701d01e40b0000c01c0620009850b130784404044041003c400b060307010b0504900c61003030309800c0f4020350441c1001014460000c080515003410400304014a80d008808503a000724511000c03071403031074403400d82c1e030a2426100e004103d6074a910030301182d8401d11070090200d1082501c800000c0c64a07900c190418070700c085070b43d503407104238400042d016081c61850140052624810348503050040c00d109640c2e5458440240d4039000740d80014030114006200b0b1080084041011841c43c524a82c02240d40381c600c1e00000b4100080460505842d074040c40d104405071034001d06d408000014841c800c48510320034450680380f4800c446050a031094924401030680b82c001061072521403000c02d00c11010303806841084101640e0f0004400425011700642e44168102c0380038005000170100014071560000700c0c0640302c2d034503003003501c0001480084e5420 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 97102446 1250 97101196 97101217
    0xc07030c0201090315060806151305040f02060d0b0f04051302010e0102030c150613110d0510050d060506010905120703020909120a09080601080d0c02040509010f0f0f0506090c 77
    0xe0503080034401264a04000c0d44000e002c2e0400d980c2c105041c00f101d4002000f91142c0d002224440d0fa620307035000940e805001e1500303800401051200c1880c1400350000d55000b806020100c2c1c0100295011483e15480418902140c69403800c4d00701c039a14000440d040d902a040f0f406000c00d05001300e06103c001c02502e0700030305100081c81340004a9000b44207955581d00c10400f82d4003100c030a074030030454092003240c032107104120200e14a01d9542c0075104030160704520010850130a80e140802c54010030005d401d00c0500c404042e1300140c40ea6404504c0c0b00c10611070000401d560074140000340202629810407441401ea50f0040300c800c0400048250480350100da20f01078646034482c0030340c20b01c4059400c1d0b00c0503c0c400111030f0300480c1c1000601044070100750031240c803681e0310b6805a4460110b0081d1074009030f51403540d58050305c3c064220382d0300040402d000265401d00030610001325449140c61a1010f52154025407080007684a503550184060303c0501440c0f8201078031000921072001d140c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 97103696 1250 97102446 97102457
    0xb010b0c010b0901060e0913030203040b07030c1502070204140402010e2211040602060f06030a02061b0106030b010f0f050f01030c090b1c0507030e0c0f0f04050426030c0703 76
    0x14000305a0940103118a0340e030182c008003455071076800040c118980c401101d400340300c002c40410300b40318003022076070291034065016505140c01c055007003005030300020f002d40402038250400d90100e6060708144090154583d001a41e890300c910502003a03800040010100320190010480941d03000722483c01c0150f0211802100118000c0510740c0302030340b241e090001c0c03600d04164140c0e100e01b204020429101c8035002c0f90714581d40d4210300c410891003110415019009100703003100604290303025000d14800e0302684540710140103101c6085480e654000d4540c000130100401c42d0120320303404140a030120100403080e00c2d080902145941e04994900c41c101a039520400d420148290251790241c4641300d20036607101d404691400303100d101c41344503c805070b00e05130105000038064841c0c0d2406520a4024044c4852890104070202c0425901c442e041010003240805035621841220720640c880c050209400c80b65401d0146958080114030440030030030014441d070003800c80284d90302c160b0b240c50302 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 97104946 1250 97103696 97103707
    0xa05041a0f1302070507080c100f050304020a0e0708071808030301030206030615030a0c0e0a120201080a0f0c110c0a030321090b09100506100909020903070b070b0a0f0204030b010b 79
    0x1040b80001c24820040c80310380f0110340d6804000d0040b07100f4049400e8203040340d81d00c43c043c0c0c00700484004108101030104822129012002d4055070241d940030b030000344031405695480d0200d81e0b484100319008400036030300c1d03010031480c650040040e55000c50f140701c08107017590802c01e400d9070302d10048c08041c1c4200b00102c00100540d1329003c8070100d048110f40e20300d449003000a105400780800b000c020000c80e90000303800f0880e05000203c001100d254910f243e814000340c1d00155418036002c1e0400c05100e40f0340960841c120303e240a442c00204040d41d0304040c9821450f034840c140070403004054400e0150040c01c10100e54041102d58554840b81c83c0b517031100446c0c940d00d800804d00300d02c1c001e001041c91810007020b02d00114003200198000740b401c1c0240e83e607501c10130540c11421841400458681d8005000c5c80c01e0340d50203000590005030464071226260034424040c2d130080070044030707030301c0c0c962003000b4cc0780e10280180a58544c8603242542001d00716501c001c28000140550000304101194 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 97106196 1250 97104946 97104949
    0x6010e0712110c010e070e0c0304080703200d050a1106010503070315060312030f0b010201090209070f030603080d060f27020a210501090b01110703030c0510060b090a05041a0f 77
    0x2110f001c03101d900000c10040c0500120940c81e400036104801c004031b0040000b500080b03c440841e48566484114245400358568054681e1011130b6069003200950031122020711604000c1c04000007999100c480d101c118520005185061408a42c2c00740d4010400410450f24001032400959500040d4071480f803030310b41e0201c00141803550015001100da050b9100d0a580c05600c20451624568030900001d1442c80040e070990389001c800a402540410000302c04522648181160049526011454941d2911003000903000484030007a07607a03070340c403003084000c50020304040101400d000f04c0c3c0803491114142d0400526054038050002d4000981e803a40605c941071098003051621000184840203035040700062109014042c0390601d0000c1c03561180d80030741d0400201d01c0400004128807030a69408a40c002055401107407284641140e000714020640035102c09080030420103600c601c03510040048071011580700c0d034096440c000d40c00301d1803186986828060072064920403540082d8a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 97107446 1250 97106196 97106231
    0x60c092105070620070902041d060a0311040e06180105090a0b0604020a030b0618031212060d0303021204050c0901140907080907091e0b0a050607170d0204061106010e0712 75
    0x4e00c280e40d540128480440d103d04198007500070346074544201e26032103403c844845101d100503546240c0c088010601040080d0b41000c40d190710b00340180c808105459082400751503c41c05590031131180c90310300c3c1c00400c3d0f0b490034030405a118069400070309640e505a12403803201c0e080a0201d17801207070002150001c0d14000c2d085060b8504000d000556034103071603d040b00d610300301020918400c0c069400c905200041d00780c150343d481440c0410401d01500c48008200f03508246180032014180c00b032266400c0905107851041c0b02d180030354064618050b41c403040000008050f048080a400410755850658803041c2c00c035a403100160611140e030751203075000e89244c200310364088081c1d00d003840f900700d00c4100e103030039000114801000103014803044082048010403090241070303001042440303c100441c8031808401c3d481c40301e000c1d52031324102e401542d03403090361301c2070300420b01003005051240c0400700308000c254014011004003070b1031800d104000030401c44444881c10300d55511000039214859003503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 97108696 1250 97107446 97107497
    0x809010c020a0308030906090615060904060302030a030804061401060507020906120d03021804090f031412040b040201120903361419080c060304030c060c0921050706 73
    0x380301c81e41c8503569182c004d0640e401141d0040d040c0c0910008904e00380300005110f401401e44158400f5805082c82c14001c1036005049007a60040e2079800000c05038030184003418113a8041d940303070340c100d140504000c3c0c1581c01001e0301d5200300f1140b20041007a164843d0071386420b03580c100d449c01c40603140c4000180d46004a803240740030602a40c0e564128040d0941d000340300510a216001640c1078040007040112858644082c001c074000c101c8050000e4801d210210a010b0282e440506100f6444201d02c40014100c03000c5400c0709220003803105540e007002c00c1e4410348158207000e01c83d400c49a43e001745813440a0851016038861204281c80311018003c603184c0301d50802c0c122413201503452002c01e2048110b05040380c01520402166030800542030400b2050b29030b00c80042201c0076071003080c800d40f684006c00a0301000103400d280d6000a2143c02681001d80300c0e42e44209071141407500c0500c10000c2c402105025000449010000070f80208108080302c40c5402e01e41808082c6202002070100071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 97109946 1250 97108696 97108699
    0x30102070210020610090504020a03020405100b0c0717010b1e030106030204050a0b01030506010f081b0f0a0201090b070507050a0b0c12100f09020c0c040b01090b0c061e01050a030809010c02 83
    0x6050074024083e50000300b01d84242d044805d81d900c250341da00c02d4401290003c0d00e0227500006080000e00260070160043c44d08a00700e411107100960b40c44000c4085a044881c40203640c0c1c004150400090703a010110340101000702c0000c1200000950000700300000c000d000710380c405440d80300c07508155003c1d4481801141c0141c028003051901e803014000900d441da000718042494070740824455489a041e1800c82c03c020380310506540c0711200d50074040074490b001c01240860030424540040d00d0503005d40300501c40c60b00041840f960600d030131072440c0002040d40040060500100b000300701d0000b141d1610a420502604840d1034820344c0c07800c20b2264500c422a00000a414400101e1428076090226289045044081611101c4003002ea00c6445ea88101d2540300344007200c02e924040d8001000250141048000c035682c0f0070203030590307400c01c111000f0240c002c4010403103020704400c1010b02c47c5620042800701903048c00001406070030680006001d004c00400c00c4500740c1d014810420304d20f0340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 97111196 1250 97109946 97109959
    0x5090403140405031e01050109020705060a02090a03080d02031015050a0c050a0c030f030206070e0f100903120e03010b0301020a050307140d060e0103030f08150607050a08040803040303200601030f020301020702 92
    0x52170704c06a003000307070352292480550718000001401d10020310aaa002036031040c0540441c1d16110034040180d0481284168440c580c01c1c4000005070b4500000c007074400d20310201603200d1034808440b08030007a45038080400290350300c1107400c030250f1040c01c4400c540b64a0402d40004000390a0491500200c80c0e001400480c0c40000401031090341d089a6032064030a50031035109644100003100d40c00c0620000c107401048031000029185002c060003074800c6540c1c81c20000f060b40d20f44901e41400300c8007000d400410000e07881c407041814280a50a44100141d00961030000e6042004001d840000e02c0c43c02008007201283d03040c1407410044885001b2103030300c140503036034841c00c0b828a0303894203201c11404144000010038102d4000c0003130300c0c4a02d010040412440c0e22440a1150341e03445800c007160240500c0010720000fa0046000d800508005070003107490328218034000d0b103078030300e6000394107030080059040790304c40309001480c50305507540029103140b080028404640a8069408025403100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 97112446 1250 97111196 97111213
    0x611040305010b0a0f0e0a02030703200309160e0c0306060403060207030f0306050108040c03080c03070507090c0206090f070b0d0b0d0308101205030f03250905090a05010509040314040503 82
    0x5401042081408643c02c0d06801c0d0f03207085c5441d83c0445403291018141c0300710b00050f480001c50740030f580d000b403641c10040344c00d0442000302220088001030341840741401005101d4001c10410400b8405450b51104441c001e0600513220340400c0014221405400004000340c865240d02040e50b009550040096465946030f1801030442d403143c50b03007800040e03c0c00c680011658842c0c00403d00480c0c2000c1000742c9282552982000d60780140483e003c0c2d4442000014001681040610010500c10300c00141c02000f15400a0900c2c4002d000c1d200c0581c051401110352040100744042102c1c160204650b0b01c1452445140140510314007550344091200e081500b4550000d070650311910820b030f10030481944488100c9509450350602a03c140e10920401800610040085801048100100d10181603400c1240c540d840d00c0e00b20400040c2c0f0000d4100841e007056444036811a50b680010b0096606080c00b1844c41800284043c007008a0403040241504040007240c3c09040c000d0256480a0f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 97113696 1250 97112446 97112453
    0x3070803010e130f0f030212041205240a090213110c0106050a150c0f05060c0c0d030204051509010309120c021203070203120c03040510030c032a0c06110403 69
    0xa0300309109142e521011080040e800c01568594954140d40c41134880383d803c2003d44800102d022403510480c01d500c41d2044915800070082c0c0030f400141000b1080c0f940518451821a0504007110b1601d6540c2e1140100e01042c03820000015502c0b04484200290391061400001c980824403000035456901e4141410200d048180007041c0803c0c0560003400240d503a00c0501c07079400818407a03494080c10020351424250310030405a02158001d48003c04041d4040d06c2c0c25042840545207496034290003d501d030480c582c140101d82e608101410300310300300751030300d00441c2d5406184541818000c4c4001111499a80603034000383e5044d801900b02071404104250190041d004c0721001e0b07200d03001118650f0205a03000044810305540134010b44200d12140306213441c1390f00000c4500256000510000c2090744981105c41e650517130650b004a00c0942c0036070701800b150f203c02807030ba04a4441d43d640c00d00a11324501c0142d5030507143d00d004540700c513441c00c02e10010200c541034440e00220028000051 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 97114946 1250 97113696 97113713
    0x70615382d0d0501031208040209010b090d05190209070e0306060d0f060603030e03151608090a080a02030315030c0a030b19090c061404080c040c110627010b0603040f030e030307 78
    0x682e84924491806c01103200002c2c0d0359a442110025880f60713101d001030040d4041036000d018124001f4089411643d5980e4809042810760028030710104c910004001c15450b080d00c0c1150000c5090924401185030071002c07036158a80100418002e5800070411010000084200d0018640210003080899180e2500070038206200c07001502c01d200d404c20fa080808a040f440381e01503903801c4803030240810790034001d80e019040141519010b000b03c21959020a0100340100240d4102d50f000e1596032400d07180141251000e2104140664404e90680c0165120240c2050940b5007003e844070b010f5503814804080044980f80369500c5504003401c0c0c504000d0700160381c600369145501d0f018000300e0701d404000001c0c081c0381b0070006140e11146e074400050500ea030020492070314a20713040c001800c0280340d50f4500403043d2a881d5003c5136040150a41007224901c0003000c20700b080c000c3c0040c850782c0c400100d60f804080d2019052400010548003018014a0aa4092030014060325243c03841c60070800c11 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 97116196 1250 97114946 97114949
    0x90f0d060c0815030a060507051303110a0f0e0604090813060e12010207120f0311040e15152502030a0305070605060406030c060302070615382d0d0501 66
    0xc00c4011010621083c001c4008004a4802030010003900703045171140006031a02403d03680c10302104215000b0402c4d000c0025002840c0107001007101100440c1c02e000584002d5400401e07000303201e01e000d000b81c2d82c1c04101941c00030340c201c2c1c0c0419141414200400644030314100600080305406000034155002054441020380440d040ca04940414030090300380c3c40360600042021521084440d0198021400754814041500d400100d00d002c8000388503090788103421101001320b855003002800355032441000030500d401d484424a01045210712415070090070658040c0c10010030b440c0c9c440020604c0c3d01c004980c1c0050803200396200604028140d9841480240c80075410000000c4403070810303004038400c485e0b000100c00e020b640382607001c40080d000a5012119030342c4840b055404620704815080107410f000c3c0080f201a250110b095128001e00a800a0000c84010b02c680a40107280155801019a80107441c1c00801c450a201c0454403040107131071908601058450100005511490 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 97117446 1250 97116196 97116221
    0xa23041716050907050c010b0901141207061b02040b03060a0203010f0807030503120c0c06071e020609030f09030a0503070f06061725030f0605070f0503090c0402090f0d06 75
    0xc4541885500e0555a04028018150003c00c3d45012032000c1e44100c0017443c00802c9240000343c48810314001400007503081e032244414821071284490240340c105042a0880d00c43c000515016140c5840905540459442a50300c1844c0b4140b00b01036403900e07000301d07503000002001e0703d03003034600100580c000b90000c0c041c040c2d800e442c00e000440e01510005103101500e801000a50401a8003041aa04030400411181c41684140102c0d0003004040200d540151902d0701c2d804040e0303c40c00091200c5050704900002154091001d201c2d410101008445861076100c01c15550303948000b000c00d10300b4042c0040207260f440000352207018000c4071102d5400780345c41840c043c00410707550800f05040c0b000c81010000950004a9500c00c0c243d22880c5802c00d0702a640007021a4950340d031a501042040014203484d05a200d50030401c28a0b806481c3c0010444203040c403c0c11800d204d89002d5030b580d60400494000c540c0000e494140703603900c0860842601340106240c803190240c0c585400602000780081 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 97118696 1250 97117446 97117453
    0xd0b01090e061315110d0c020a02030c180103080304030c080c03130f05031009050c040e0f071a030f040317040f02090606031b1303120504080f03030c0a230417 70
    0xa0f40740076030a03e110081500306000304201522444844024413520450130f5035110704005804900c0c905006145540c0010780262810301c409005040c2003e21503000306209540c94800258910704d8541410b054a030800a200c1d2250b81e18074096940000c02c680281000038041440380c02608004010500b20074101c3e0b80780c1200c0e59881404880a41c5030044a40c0354000c2103034410781d131200d070b4001d0b00c001d4042c2044583d0384412401160445400c42c120020b96082201210413188042040b000200949030b04980c501d240d480c0c9040c841d0101038070300c00d1010f203071001040905124405014620189a10440e100d091a1034001d0310604008801c90082246c000056018640b202c00c1d03c1c8904843c24804910070b410096603035460b40204050f00c0310300050305002c004a4410050650880c055845640d940e508219219103001c0e840e0059070000d510800c1004860076005d01036032920a401c0c1018081e01e0080c00e204a003910400d030110103115404540004d01c0d0300d000c1026055401a50280c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 97119946 1250 97118696 97118701
    0x20f161101020a0b06040b03120d02090a0509070e0907020c031501150206010e07111204030305130b0a0f0c050c10080a2012040f0b0411010305180607030b0d0b01090e06 74
    0x42e40c0301c484030741c1d019050b501d03e0000900c2c0e03810b1540111349400c8009040d180b01c05910750300600d1541007030f401000342c10343c0422204030905082041d1000b60a08940d00000c82c5044400186400c0f0030030049802640c0b081d000c204105e000300540f05074918000c2c00c1e501035410350600081d500000344101d1620040b440100681540041111416180018500d8200740c1c0c5490341510312102600c1c003024030b071252543c00321000341d022001d00055031080d514281c0d140c551420312a0082c1e01038002e40c480f0602044003010325030708207000c60448483d41c204040c041200e030500c24180000e111029030001d40c2e40240140702d5901c025900d00c1180025070070004015440039812041c02101903405c641c42e420010b9001141005803c141d210f807180000500c200c80325641c0740517420090350300300c92056214038182d80968160080ea03502c10080306102007040c003500820356803400301071f020000781552403001c0304603901c0300201c03d500b490b0400c0b850556943e60b074541d44c00500d80081d41945a0081e0f402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 97121196 1250 97119946 97119949
    0x40c1206230405070905063414060c07020405190e0a03030f1109062803140609041a0c0405120609150609070f0e1201020d0501060503061003050406020f1611 69
    0x550740500031303079035400115501348014006140e100007680610b80d503007401c1c41802404050880b04d00a11804080009a649498415141c0003c20344c128050780004007044508034255061342c243e25012107012030342e519030600802c00943c02e04403451006d82840c0e00a800001c0001d0080e20f10703032003950100603901c0308403000c00480c1c450987c504030300380e0104a05515807a1090241142c010703088201d010302c0c0c8074000302c4000306012150700004242c030fa007100664072440580c20b592168050320340504c41c0ca05135995407080c00c0048007044840000038042007052134040180d501401014009055103991100b0440d42d442044440555500c2041e00300800d0140851445015140140c90f02400742c03182c0105451030141161038808001c03640f441c82e4590b036502121880c60070b08500005a0f15640f40c0507410948030140c104400b84801002070240c035403101900c91242c80010328000465840d5031038100064400c070350b0040b808450108510004403c0d22180c4d41202d4441c1c900904076094030b60 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 97122302 1106 97121196 97121201
    0xd0615120b040b010807060503010302012327031203070c0609150f05060d0201050406030c052107090914180a05010608010b10020c0f040c12062304 65
    0x90511043c4010b8403002400741c0144006090310302d040c030001400354030042c0f00007410800c0107507070303240f4030890882c40341d0548404c2c0d011969035510601c2030103d5560640090204140030702501d03c2d503454000750302d0031851701c2c5801e0503095558452040d560345a9403c015601c1c05c1d1103c040c40009024003120000c031a85040c00001c8148414140c04126080200500e0240070501101c3c00541c2c0c1250a0360304840062602280080c0c1d1000704417003e000c0d070800000c5e680000c034522080d5803c00745505102c0c58042c0e0b5100e10080d0354842d980309407040401403040350010f5401180c018000c1d07003007000c9440002c00407164603c020742d582078211005640110071595455100c03401a1038031042000c54540766100800a000c004000200040c00000f48648100e40d0743d00b54940b5140078103071003007018101440400220ba96001c80350030440005400d264440305d0218080f00c280b4180c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 96942446 97122302 := by
  have h0 := BRFrame.cov_init 96942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 96942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 96942446 ≤ n) (h2 : n < 97122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
