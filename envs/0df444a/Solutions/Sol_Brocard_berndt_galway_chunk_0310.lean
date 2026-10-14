-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0310
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:07:09.626446+00:00
-- url     : https://prove2.me/submissions/0bd379a2-280a-476f-b77d-181d853d688c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 55575543 ≤ n < 55755399 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 55576793 1250 55575543 55575563
    0x3020708100903030605060307020304050d06150b030117010509032502030f03030105091503030406080402011b03051801030501120809030f07061e0f081b0403050717010506030d09060c 81
    0x6001403400e01e403035941d281100d1a5141501802e159050007013000608040c3c42107407a6041401c0000e403648514003c1c54001c049040c804810010180d1000d24080c40c1014001c015a03111085e071307000d580c8203204075141d0495001c00e0f20142032042c41003e024542c4000194509401200c1401e500041034440401001584032a6400358405000703042c7c11030321200c059543c0758140400c0140b036480c0582000c0350340f00c1c00d481401598400004840035a0380c3c90511030703660365841c401280e8204000c40c090b02c050440900203010103402202800d080803400300d42a201240001c01181122024483c04010f04c41d0b5400075008102150000c1c40f003d2400780584003030390400541145081c4495102100040b500c10014680080d1080010020703006454800c1244091a00040c101080540440c44801d00d58400c8841240500101c8000315801002d0740d1150b0f0b980c12002c210010302c2c4a00c05002d508001c0015150b1401040b1107201c4203e64448200c203500307000007107406440c0d414048401d4150 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 55578043 1250 55576793 55576799
    0x4031101020c0f1c08030a0b0108010807030c030312020f0c0601230904021003111305010807090602030a180f03030c0b0105030a030503041707022e030506010f030218061303060c08070516030207 85
    0x94000114810360b507010020031123400c601e000510910050b802203409404c800740520020302800941400c40b034041c50b1a4101ca030041e80000024807800310088240c14002070300d0100740e8404603450b41210542580d40d48030112840b0b03405606c0c00c0b126070042c0c0c084c034180300050061601650140800e80985400111404511001c400591180e000c10701c0080c08400200595a448007259074040788500d80700d11150b00d003150283d668040c400c240024410b162400070248006058207200901044110703071000356403414082d0081e207010702c06072010089140040340b10b0400151045050b603059440038555925610b5024450f0a580c55460191504004034000b40c0d0340c42224907a070001400e0b00445404411012441421110790380ca01407505203420403650307070380140a0354101d9285040140e96041741004148220300c3e01090250b02c02d4012a2400361404800d40c41ca055a202d07000c10800c0b04e44070f0300f003507445850448080d000100d0400ca0070914880c00c0c060305040d24071170300444225580b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 55579293 1250 55578043 55578053
    0x91516140405041103010305190c050d1718010311040e04030804030c02130c020c191203030905011a0102210406031a03010501060302030601170402030a060203040c0e0403020304031101020c0f1c 85
    0x1c50280103440700c0130110041c420301c00d051084092400c6051040030380786401d5640c64011030901d1040034440c081004549040c024980491b403c080c0d003a8070042e64a00d040102049800e420b000d199002910b0016505104e8561108640656040101101040e642e0740d07011105010000c1c0220100070722059000d006803900c40b09808050710260b004201c0700174a8000924000402c80300e5445091075407501c5685000e51f14a01080d5000b80c01e060450781c101e410264094410300500515944ca807541e414000880a806224040380982c2a130324810084c0c424400c80909203410401c00480410040001a01951040f100c150641208602c14243d031000642113074000da1000021980000400080c0d42e8049496031440700320801341c03131030380c10207070003096a41803150720040032aa8008040b50034001710202c010002e000d00040083c991503d440c00949a07006480201d914a100c074a060059600203e4500720490700030b881c0c8950b031040741c000c104421000301c1c41d040c10098a8150f10303010038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 55580543 1250 55579293 55579301
    0xa050316110103140412020c03030c160608010f06050d06090e06010608010512030301030b09010603290c09030a12030b0d06090b060f060706091707050609151614040504 74
    0x40c030551010421852641009001040d2036042141014600500070140300b080b9400c0e04c3d00280c02500d590800e040c4803105a1500414450035907140c40302240c00c1c050a0781c00a986000d40f190000709007280d0342da8107015211034500b80a44024514602014040d9030300c00c0c00a08400280c6020200e58559164203e80c12031f0b004440b00000c541041c401480007582004006006040540700708500c0751481092a45078013040c00f000300201088004500030001c2500060051500031003500421b040b010081120b001448070712191102442000030218013807041510f0407240043c008d480009160764401d00003e42030456001415500e04081e002d5854030740420203013902c12034002840341e0b21401d00710031000c001068940302d4082007001061a889400541c2d141c030340e0000003c81c40007106c3c5402c03282240c4a80d031034403c0032400300b00503003401000079401d802500c0603415030b49980365540c20004502e0045940403141c00c2415201c9004034170844071820404400190b290a00da15940060300307803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 55581793 1250 55580543 55580557
    0x14040b030f07020c010509031f09140d0806030d0c033b1c050a140a0506040312150321090906090c14120a0c170703050a0e060405060a0c020a0503 64
    0x4101c0c0a030030080c44035010802c00352400d0090900b94182444800001e90724129100b10f1000740c03019152101c21500690032941c00c00d40d0010540d4410300b4486482c0b5a40d00010800900003000c41c40130072101c0c103012801d0b0780e1410740c50740c501c1040d003c02d450580e00200d050030103000d04801140300c0b210500e0030300b10515890145813130301c856242d540001c00030055404040b1826840340843c407400068400160151a21fa20030340c1242c01100110644d400c0c800100b002030101c3c0284000c220415501c00381401801210a100300440350705002d0391800c26089000c01403900c0070600109010305204101c14403a81d07490314001c400396843d03044041c10398034658030009206172560300e10220300340c03c03071a05456543c0010ba11070070b201f8a071200010003440035001d11419940c0e5045a0001481200134001704c65030011410a94200504000d0017020204e404041146c0341003000007150001003210303405941c108004140e5a219240e910b0010140c0d03445030350540c405d04140da0001101030011b800c403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 55583043 1250 55581793 55581811
    0xb011107090605210309040b181302090114030d1d1203070203010c050313020d02040b060a09030b13020d06150812130b030108030a030905031e0306100201090503030714040b03 77
    0xc0c2c504000c0c0315a104044103c003030516051684c0e1034201da0008140c030440d21086034045403810400001c100c52150550080040c04901002c1000362414401c3d0401e115209641c004400c1e0b03078904102e006c0040541c1680d6054218441826600340b2132620742114041c80d50000140c24284400606034241d41d901403600b940011444078198a000c2c401c4001c0d02000f41030581c5185081d5050b540c21101600d03000b481442240e04000941d02c55074425080380710042d14240c0c0e21441400042c10400c0280b004542074810000000d550a170500ea200100550243c64184031045580e02c040c050b22070744001d0080da410881001a241208002192120402030001a59180b290086140c420034903000158001400c0004100c200f0002084910300803c0b850001080000c0e4a071507030841c420a601c0c1b540d600007211003001c481d0343c0240158020202218007002010744a40e05900785c400350040500300e0782041c80094503850144180703a009501d5032106514094842c2e03091070070f80d0001d9802d421 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 55584293 1250 55583043 55583051
    0x201030f1a040c0806090708070309060606080907061d130207170a030501050414011e0b03070522030209011203170c07051b090c0a0201021b03091e030a060b01110709 73
    0x182c101446881e0620ba55441e003510720b481c1044c04540c1d0f80c40007038070070002c00403e000044c0f00107129a01c004c00742e80d0300030400e101c813a0382e80a00520451003030b910180a400380840c0001c03002d00a41c0181c603005c213031404400715548074904204251043c40d6440020030b4013044110002940404515400e5000441700c2e42c40321034072403008049880c140c10003805145003041104131648401982811560490720a11040c0d00b0b10100740d110b03000d15408094007400100900050f90f070801d02501400f5000032003406150902200600300107035a10010350048046d40040c0842007155040e14412400381c00d0501401d16080920128000c1c110b514200894011031034804200081c010070001c090f40000200e1064540e4001036182c0380c0c0582518142c0f480040da04403040d000790140d0325003005582c009611050403200071a180d500501c080c0d40704101c0d400001540030b0304000c20300740000015006100704052590747c5001000703060445414051100d21000c0700600c05c001e00d1010b000c4081c0d01007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 55585543 1250 55584293 55584341
    0x3020318060906060609131e0f020f04060509150412110f150a0c0b090a060c08010f060302070c03020d0528020108040f0f02030303070305070216080a0605040201030f 73
    0x100003008529200030080d040308050015501c8005001c0d80c000c4000c8911641c0c032041030000900c3d0740b4040d001c0c00249070610b40b0001e819640402114489408000140050107810083d00101e208040c42000d2600c424801440103900c00e2001e441050800740201914580c03d2003894019002507005541c103003400000281000b0464681070001c507001c1d40d81c140c200c89004009290402c11410034004001e01049180300d00388515020201d01e074101c5050001c60030086441503d90400e408141c07030607400d256981000512441c4440d048408507102146140e0520404034003035880303004160381e80350300c0c6403001c0b001d40c0ea941c404001c0184100e004000150281003440d00b18890740c5d4641c5860089181c4200c0581d800c00001644230b1b900420501c64078500c3d1600d03401110a074600690188408000c008a542d09a40000c1c0214030315002c542066100c030b0b003030104a403010700440b0303919000707462640d00259130f0380c1080e500715105041c0841c062030030382120811283c074020800c0c2042c480652503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 55586793 1250 55585543 55585561
    0xf030901030c0f02030a180f030f020306060108070503010e1e150909010b0f040f020c0105090d0806060412140a060e0304031a0c0909040501110a03060303300c0c050d030203 76
    0x20500d400864200295003c2c50004065100d004024501703007401340c003090844d155620500c04002602c10480d0100380b0356120308284e410404906400c034042e11912000c10314542c0215000b0303201d50b145a42e502e141d41c0c203200403000301da10054108555001e0004034560a84901441c4034800c06800c2100d0401003640d00404c806004050100c000340c0c0d24140d000300d1191241c108a802d078900c141c0c0c01040055400c3c065000910851502801a5181c9800e100d0b06042c0800d481c420250159a00502e54840004120007840f41d40306841c41041950901000241c1c2c00214916901406003902d404144645441060322010342148d007807a000003c040c41002140c00443c040444680d505d0205458000c1d449103441c030403946590710400e2203000080410400f50001c1082c0d64411003410307120310758094040c0140c4490700040f80400d5010558003010881c0d01c2c200480400641d43c031b00602070700315003010000d0440c12210f60411401e4084880841c80c10805803002401c01e0b0340050741c0f482c0c40344030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 55588043 1250 55586793 55586801
    0xb15040507030b031c180905010518150111010e0a0b01060210050402240f1303020a1e14061209150c07030503070e040912080106021204030203060f0403020307050f03090103 76
    0x103010140b51905400340042d450010348120b000700700326000302d0049070f01e2000740c0703051240f0803d401c1d16102440e00452545800e80109040350f00c2a01d0f8600d04281d90351002d0380d0900100e13240c910741c80d085400180c1c40e603c2411086d8000051000000300c00000c06042c0f41800204002524010164001004020350402c51180420300582c3d0401150600c2c2d400034035007030709103408861100c21023950b4029042c4114111560101820140c650301c0c1030003101c08012101901c8203920404400300001246000421903011148078507840340101c5040241694280d0142030a1310381100c410302070fa01400301400007080c02a03c1000081c001003507030a0b4000c0345210018035050240e07500303103c20b40000e0307085411b032504601d190908070707904100b1401207001004c24400141204400f01c542031081600604014140e4805a0a0382ea117008000c16440d154455848001c1d0164403160000d82090107040c0c480340c00911a105a91406031141c952901d080c0c010700100040d6000000c4c5d04445680600c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 55589293 1250 55588043 55588051
    0x10b01020c0d0b0c0f040810063b0901060b070309031716080c210309060711070501050d020705060103030809300307090302060c030406081003050703021207030b150405 74
    0x1842d010050780c83d07034030361100d00009444c2658007080855419030041501c41a50050101c00040360210301d110082c0c2005843c85129180c3c0c0300100040240010105866040000d0180d10701401e00c01c400b03035000c4a40c1c0d10003c10f400299540c0740808661844d005000300324203030181d603648070094258100b00d4071004032202a50003a070010056031a085010182414403150007244c0e240d1160105034842d41015412904141482e030b60046042c2d0600c18040035600400c02e0104032002c9030303a108030a1754040d03603810486445501028041289601c91401400d400140100244c1070020542d29549031907800c0c0c1048001c40d10f0001007140c1c4c03440030010304540010104800d00b800b01c505c12440140e1410700a100c040810000000d801c0c180070b0f4002000655010340b0040e940c00800103070540765002409200006a00c410110340c40d510b03203850749400d40c1d8001003d010727014559401c0101070607164809819901a0344000400300c1c0b0400316561040200307178508010a00410100030440d58010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 55590543 1250 55589293 55589299
    0x2030d0e12010516050d0e060c04061101110d11040b04030f14030307080403110c0d120908010603020303091917060105090702060f060f01030f020d0b01020705100507030c021c05010b01020c 83
    0x208011280c402e01851084e0b000e0982000d07130fa40d04100b035a4402510036000c40710028441c00d814805010b8800c401031045501c551366030025406030995503826642d00b0224107158071018400d070b8034589660b60003001c0111038070426602e095501c4d0b036403281c0c64000382c1c4141c421624411141d414451003c0c0d07480304400501014600d0b518080798081d00e03c3c4400741c0040c0801840201d800c2c4200740070807140d14628070040c2015002c3c5083d10340204280300514000c0c00046000c500010340003814000c03002920b90050266041601d00030610450302100203010740b6117442c040c00001c4050b030040e0004850462040038001560412050069034100540f4401c00c56120504111500d10020980c0380c0007601101c0b5003051032910342c0100c024009411ba01426148001884080843c843c0c2c0050301c1038000380c09443d4016540d070208212680107103415800305c3c50401071440043c0c41340d041908418030040005088101c000382c2c01c4560401d51400f00c6140e95180e01345162580c040182c1f2505402c02c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 55591793 1250 55590543 55590551
    0x12080702032b0b040518010b01050a0518010509061303020307050d0203060703110f04140f092505040905010b0a171005040207080405191a09011d0103060302030d0e1201 74
    0x41d50b8450391a84040362400106a405881c45032051103a030000f42021000500034016400e00414182c4000700308205035a2562811040010a500507002d5521a003259250b041c00c028200508003c500e504a5855041180c100401c58190341c0d0400506142404480ca59452600350320600d0f01e41400740c0c1000344550040399440340141d400044065019240303290210f5141a030f100d140f0a507000720b010303044066002003404141c200074a00e81114424080714008500c065000038010000b00c1510440c0c0000440a16259200d46501000f540b100042c03400624156490710b1850845400ba08180485800082e07811600395129000c0310311000032103401802070401440c20801c0803040d119060281d03401098410a102e03d100986008102c00343c460311500c907a40548000d0300d520340c06450225000381c20210204664842130360103003001030315164105203143c080d00e5640b9511100c1c00e41015151400800107032004e000c16400b83c0c00340d03110318a40030180c20800903000001d594440e07490b0703d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 55593043 1250 55591793 55591807
    0x50c0a0b09010e0a050a09090303050a14070815030601060801080606010f091806050a0e01030201020d11060f06121515040905060105120f032101140f090702010609091208070203 78
    0x5298222803030a042400c0c041600d183ca03501040c2519100da0081d13521a4141c0400101d001c1507401c18562140309590400c5582e5542c2c0f0460115000341868a2a0300c91400008003036500440c041600309004003860320b6400f01610000b46886009d0300071700000786400004004249080008540040003400c0241100101e03106c002c0420100340300d02402150218443c1041401643c4800040c0074050b0814040d070791510140c0d0b094900a110880c01407003141010400c0358800c8030004500d01e41c0c0400b401c4036854800e0300001050f00600303a580d1041c040c4460340c00c094400c21070269140045070000f00c113490049450f40905405030107060203113041c01e00ac07000180c0c0126095055503804c40d2285d404012418820349860025200c404942c407001881c017001c4840038100f00407030301076080304820580c0c8402e100c20951104c0220183c01c00e000c0a200c4c41e2074a0200000c41d03010b0300610000589036919400e01c0e0596a00c00b41c00d82d40e04200d0340c071180c2942d9016803c0b0354052864001541b4103e1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 55594293 1250 55593043 55593059
    0xc0306010c060b0f030109060b030706080405060a050601050903100c080601020d050f0c030708040e010911091e040b1005030405060a050112060c12060603020c06010e270a140604050c0a 81
    0x100700ea1009190395901c81d40c010035030340e80007403110726480090020080c51f215807034218011300050341198400d208500c000a18071788215841c41c4290760040223000c09448801085014000280465051080a00841603e0385040050020348100c0e44004a0b44620040380036081110103811786045411071040720300d400d07402204803500700d46a8001d480c0c0e40c1c400003482c00d055000300d12000703100c0e400001b00051200303104c40310241030301c10016080080d103000040240341481642d4407150810fa00010144500181444141d0742c0d50700507002050354609800000d030012225111b400110344080184800c0c003808201040d840030411074100aa0350524010500b41103100000614150b12812420340c80b40c8294000c202c40001480207100d8603031150006006034000710600820741c89403000015064095000103801800100c45400025004d10780030003540e2115002d070a014403d26034241c000920680f00c200d041c901e200090b0000e070400d80b030b040d4101480b00041911aa400c10000d11070b0a07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 55595543 1250 55594293 55594307
    0x20060c0a0308180106060210050c090d02060a11010f09030e0d020a050d080708130302041406060301050607080403020d08090111010e031603020c09010b1801021f23090706080c030601 80
    0x160181040c0d14250b8072a901c0b404400d18800000103a13508004000514a4001801806040c5038081c00e0010780c1c1c03248541000ca0041e5410140d001d030105007458003500301440109020380e03051400c8440030020862850030b503807110090241e143e43d80c0700b82c0b00a00d40e00846036035805404030ba203010600440d4001072175121050050704d01c60144098518108200c440480d8915a4080711954907086804508101050a80b1040c0d0046003000068080c6c092425425072007101e00501035811a42081705120717860f000110200c504e00c0c02000080b002da582c100000e05454403440f421541e90440500040071261080b603c0c2c40a40e06180b42c407142e0b040080165842c6d5800c50304003020540e20781c20100e1900124961868000020f02e00201d0801091001404203406840c108442c0a81c1c0800480ea80c1001e08044c00c5c4001e041c2c01c108040c540650004900c0907003111041500c0c265048a124040c041a0364010303e55109040800140b80c01420039a07202044140c4036045281c02e0001070124 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 55596793 1250 55595543 55595563
    0x7050d080c0d061508010806040c06080a0f020c06040c05030f030403081809040506040303050709060c170f0a0503090d0311220807031a0109052e0308030420060c 71
    0x10091100c0011107905114080c0e841160039000b0038003545650350b4003180c11001100310751000902d400004070b0310680c0022a02d0081341c5c011071966180d4901103007181c9043c0094440f0282d661554040380284d1103900140100b07205010150030f050505107018400f8007000e070b020394007030341214507544005140442503d0031682c121201c41e5603440400100070040a40340082c940c003244030814001440720004101e0720691084c1c500b0080f80d21884020707111084140315010009644500c58030004807003808100440b000c4545142c10075445c00e03c0c5e00c49035080303030140c140014804400c20512400402c142d544105142c101080315201403002500300e072051101030030403280b4142074a01e11030300c00714920700180088010b540610b1744a1a1107a119043c4000300d1200f1f4020b0000440d5080c0c0601c1014008c10301c0384004c040d8040d030080454a880705201d402140b00000f0400080460700507002503105a10549440d001c01c540c0e100c894080601c4c0300e08450040c0f03028032001d000300c0350001d010008 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 55598043 1250 55596793 55596797
    0xb0403030c030906020301080a1208060a060c060905031204120c0b060d14030c010905010f0e0d0f0513030f021f0e060f16030302040f14030d03050a020d0e060a0b0607050d 75
    0x71081c068154054110140018007091000000040440c000300302c1d01c00c410701c52080722945010b01c4070100c9a90f1400e40d080c40e03100248507030402003180511800902c2d98810800448c00748926140c050540d040074407407404110130032040004010940100c03048101d99400e0441c80519181c403500d460210042a2500071140e440f0352a0034070050707031114058582c2180c01c50b9920700c4083e583d5400307403858500c1211550308040c2141e03204200e42c040c44051003003020041400190700801100d504c54000e00e0741050047c1005400b00040230011450b01844c05071541101e845c1061061001883d916420980540d20f40c1002c012500d80c00242650720304000c545e260380b2210040e43d01c0c461840b4850354124203011400c4681d041513059006401140c01c1ca03240781318401d659010185d000d481c10010a68107404c0702e003190780700c2ca01940c4034030b41024140b03000500708004024094111607a800091940340c0c814420800300c406a4080e295600344196000c0742090455a600c43e6511000c2c400703801 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 55599293 1250 55598043 55598051
    0x1030510020d0e0f1006091a0105070c030b04030206070801140a050f0109052106100308031f260f0703031b0302160f0602060708040f0f11030709021309090b040303 72
    0x80b20b09240d400071207803a90344606039513030300b40c001250f69913030700a02c400c2108007400d0510010b00c01c0c0c40d900c01c882340040c0040e044100100007400449080c0c2c440c400c00c80752814054804004034008042062160388a9001001b231414544406800d04d00145c0c4104040b44110398071003460384800300a072040b12810b651201417400300200680c0da01205401880c7c02080140e41c5115031140b8003582620760105500380e5070b03945c51388840040da405903030001901d402c0080012a170040d481c11002d0110042e0403e40001a940b1010388810f030000348003205142c0000488548198001403060000701546800208546417440d5009000709001201704610070046103c1c81d000d15000b400b0b0740c1800d81080504444003504e07030b5a030f010003142c140605001403080bc000102c04078084c042e2076000e181c01100e25038070f4041d195240300c84000e039400d0450b903040c02d91040e5079164608120b1040508900c200c05601c0c2d60030442080c0351085154440e08107603050800400225140082c21a0072a805160203d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 55600543 1250 55599293 55599307
    0x9070201021c021308070609030b0411040903081015230f0403030908010b04020f030103020418060c0302090f06030402090403180308040e040302011d030d270320060103051002 77
    0x10380240a040c0308a000d44100080c0c82102140d20740c014030394481403c00580403075440380c0d10706035102928003c010103c1d100344401d1000c1a8004050340d030240c4100801242da028010106d07003036803200042140401c014109010b130042403400410040d1843d02c141c0d02d1641c1070040010120420122440c403468201404450480c4406003111148103206020a80d182d50780d140042401465105c0d9401c80e5180400107007032803405008507000007618aa400e03003540d0a40c0c08010080c4492850f8062440c944044400041c0d014010030b14405032540b801602c1d4401075040c0044440380369101842101c0c10810000140c0d290040550015054608451032440482104450400c3c1e60005000300c6130125000480b41001c40c5028400d500ca54024040c00b155211400a07004c0c030314000d403220b50024021080500840e90014081c8100320f281c00c254081c003901e40c0d40e1040341685013a000140340300c0d081c1e400310041c01554801c525031100109400c1d803644c2c4501b5120144c801744519100d0300001e0340 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 55601793 1250 55600543 55600547
    0x6040e03090d0822080318010c0b0a1a03010509060f070c081306030c0201020c0a0b09010212041a160c030e01050f030702010608010513020105070b0601050f0301060809061302010e0907 81
    0x81d481c0801d010b0701090058003035080241c41d030b40204044000c00c50044150490b00c0704070035100f0701200c180400442c2055a21a844607940c014841014100b004518040011807140b0b90341a0007541e9080d000602c0e454200e4401209078030070300300e10303000360b04100c1481070020002980780d0344005003e400c0000390300d03a0030084a18151021020380f103040007062a880c1d10816004900450340107440c10050740039076910507400e1340944008562140c0022003c00b0104a00d100180d0b484902d5100051803c05946105c21204a05550640718641d4454217900c1c7c104541d00c03074581020b45081d203c000c01860304030041001140006c003d0800211407080700715a40a9020390742044c031076100054880c6031020000b8028900e42c801e820341d80d800c0c807010480d2800b405e41c0d40c0b1441a010703529145010143d441c0c0f00140040a0020307410030408002158182c0b00c00030145010301380c01c1d9220280740c24443d100f58900103000d8000b0340f81124400400380144e800a2400704002000c0d00c0c040000ea80300721007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 55603043 1250 55601793 55601797
    0x50d1d030a02010b01020601120803130302010f0e030c010f140115120f02030618070c03080603190b150604050922020a06020a0312020f1606020d060605040e150906040e03 75
    0x56156611000c641d0704411601074000e0b5080030000ea084030040d03a40d41480320b0040e0718036038029003184d8007080411113a401a01120840720300900021840310780d0246204111005154561626000460004000c207428091300c3c1c0b01c51035814040c070689a1640d0900c07110030b0180b0429429940040040c40000d0003944400c803010040720b0300b00b1510541c40c580f170003e5030088500b0b0b81303d0165020094003519000d03251500442c019518040003801d583d0f410b581511001c3c20595040c400d00003140d202958a00b59024030a219550214035400d00000e6004141141c4a04501c0703014140070a205070b407509106039038031000d01d115607880c40c0c1051443c6200218071300b40294010a0b48100480c090b40c00181020549100e656002e040c404107604a208134010542001103000d0100220700e095500304201e9048140502001890080503420100c00c80d8095448100811400300f8208206030710f10040e0340d404000c07006500e07400c0d09418001100345200906c514880c990340c840000c5070541c2002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 55604293 1250 55603043 55603091
    0xf07050715110306090a111b071208070b0106020a1104020f070f141002160f0203121201060f02030c0a080a0507020405040f1403040e0103020d150c1805010f050d 71
    0x107020415407000030380d0302030554011503400d401003002101040381d02c4a1403240c401e410312007100c02410310310307284550300c0d08407901c3c205810184120340d400b0504c00000c0c5018240c50384180002a5a0b030103e240516001c20140c0c8408207640010814402050501d072001c1c85400e0121001aaa00e030507044104690007549401b51810034070320001d50421005041003e9114191000c6074148140d5140c0340c4180d1080e00003511b42c50b25004844400201c035050b1000c440c82c802401d480401c0e80320501180907420050400490308120b90040101c0d5030841582c1031038120f1403014500c0c000200031410b540c1c41c103003d0014440e40b400070768481d54a204005492006038000d1042c001070525041c6000b017200707000410303507801c1e420800c48152924008100c4003255844411040b151380b95400b08601d803048041c081c2e84070000c41200d800042028030031951040744940341c87c640000d45819119001c1c0490300418144210f1260320151a500b201c00c1c0d81450701181d030b0108000070382ca01181d405100c0c0744 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 55605543 1250 55604293 55604333
    0x207060219020a03030501050d030e060c0a020d0501091a040b04030e01050d0606030e15090a0311010209041404030806030115180207142b080c0702040605030d180803030f070507 78
    0x110000c0c41e1141e002c20a01402800380c2e5003445247d894104110400291100007070114103521954041c80c20510081d00d0300000c40010745405c4da0321038020800114010f0001ca031340342d54070020350342085031390521502801205440c0650b2860140d1740c4000050014102800307000440072004600d81c0300e102111260022040706000302ca81e14080034025042000c0c440b1418011203a00d4000803c0e5218114030907112000240340411581c0c03801d90741004a01440400ca540070070041c10292240c0c0183e00c2606621002d0045514250400034100361015204c14842d906003041401d103010003103a11000d4592a1204499084100800200921940d14020089401c5054110b81140e000c07c40024010020402da4172007a180c82100ca40c441c40c402a807070104162801041e04600c0c204084e180e442e1000e400000d005071694002450030321070600005c0050441d004801b00307241302d07561040081241c90011800c41c2008403490810040003003006c0200300001c0b50140502224400a4150340148 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 55606793 1250 55605543 55605577
    0x5070f060626010f1505060c0a0c0b0702010807140301090b030f010c030203010503060c090a120602070f11040c0302090f010f021f02090103060b0304020a0506220b070302160803030a02070602 84
    0x916840714007024012900c0b40b19442c02100070401110b0b03006100445609842c0b10800340c3c240010080141c120344c0c1c510455100d80070b0080c00156a0071620170240c0b4018103000e07114501072000610340d4100508520070030044120300b001d040036500940381036903214000840c841c69441c01080c542042e04548401e59820b1440706d07240f854044c0d0042d4103884080d010f4031800d07a10003d00c4a80c0d803185400c40e90300080e107810704110300000300000c200300e28815035015150418585420304410160708050320101401820f100a9207070500c2051001501402c09600380100400001c5a55508203074003810302018188102c03001c1e01c02d01c1000c10900240c10b044900c00c810050040094010701100d0380842d1a1450100341c80c071f032207401d1f0b0780700d60390062041c0b10036820702d0244403141d0042d9894a0403521445a50302d0396800c01c044800c0900207080c1081d480710200c0c1802454110350040203008007800000620903c1000b00889602c22899071002d80e03120f181e4a00a0000d00c11400c00c0d0483c6903036 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 55608043 1250 55606793 55606829
    0x307030908070c0504060512060c0901090b19020c0d0f02040507031e0605010806011e0c020f0303040b030a060f0302060301090b06040f060507060e010507091a0403050706090e0a0203060105070f0606 87
    0x40000c2c0f0308152481030790204809501c0d64181311108842c001007600c15413003c3c0000d01c0e0b8000460003004c44540c1803400d80c042c5c07079135680c41307070003030740010702c84442c1c030100441d81d252450390400c106a40b2030300440e19051b00c07c880b40c840c0407441c00043c04c080c1c000e0b5141d000203a0300a000c5e800a200d2035010890380d00c0d12428580d55407004103114081c3c540000d58200100c0c003558440d040f2400c009143c41282440c000e180c040640383d0304010350040340c101d50000110503007507500344040c00c02003401c0004660f0380e01e000a00982103480d60b400020b038858605000b4809610754501b070b2070644038040000659401040001072307160196a00400c19000240c44c0450b00c10f0313000029003d072501c2202d00b44500540034143d6401d03a101202e41340c002a401e020208250320008102820a15102c1c603064501522900e40078105240c3d6000400401d900d032108211121141c060254003055904d411804d40c113185000910510540c0703006003003060400402014000c007584440000c20150751b1450490302 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 55609293 1250 55608043 55608053
    0x1401210f140f010f050f0609100806071205010b1e030c0708070c1806060807121e021306090b0306010c0203030c0607110106051516150f0204050901060e0d08030703090807 75
    0x8207840a16281d9420101110f091340c220303002d1140254030b18405124180c1e10502800304500004200008550300d807540019851824071070980079a050340ea4880741d4609045002d400d03602c0c10381c030144501c0000c008021169000c80a2880f1148644111981d240c83c1c0010228240c01400c402508042c000a0000c1c2044101d140000c11220900c0c002030318030403249410021541e0038460780700400c1c81c502c00208c405225031051082c41c2c0d60440300280038a800d000d5500c01403c2055201e01c2c41fa800603196485d041c2908a1400500c40e40c0f611000075402c040414a407070101400403410f02001c4d641070307070856905009031900e21070103804903102440c0c20341c4000c2c4800c451003c070400030752800d200401c640c00c00c01490207008800720b004602e04100f41c11b40040b070688040702035400d80000c00c0d1404030030300c42d80141c003c1c1c800c442c0c0c00543c0f100d04050810000c91810391110080c0038205400010710707100d8113400e0120640042c0e41c1500c81c2d031000d0058010304030701c1c1c000804d24480014080204070b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 55610543 1250 55609293 55609303
    0x5030c041a030a1404020d170d06030c03030e030d02030904150b0304050c010e0f060301030209060301090c030308040b010f06020a060c090f0b030f010806040819020a02060a020a03031401210f14 85
    0x401e54030f06016206420b08000264041510041c2d04418441341410200709010820146140c4c2200c1031407802d0040b25000d01280c1c2c0a400072984004a40310030000d25602112504400104070b001d09081121402c02a51340e106640b0701d00d0046464081a035070f40c003d01481c020040860403401d59407803419180c016252070125242c0350206100803021010380c2804040d80c1d07a1410080d006518503400c5400304501407800a000942c10f640b00c04401c000500208044001503120740c84a00c41c0b420545011512048140c011f2031425101c0c1c01c0c1009102d9001038405202c5411040010b0901c1540404454642d06030300984210401c131140000d000c0740d013400851241c0b0000101d400e003070340c846035080d0700c49505640203440d203d0207102c0300004107140b80b5040080d0380940100c4000c2002a408602543c100e403005002681008040074245038050107074000328608118441c2e544e604040701e10204240c03000b0000c0c1004100340c000c4c400c100c20707000481c1009400245c020704c0e01d01214212f40e07580d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 55611793 1250 55610543 55610551
    0x4060f03060605130306020702040204030503070b09010b01020309010804080a020708120903070503060105030d050c010608010c050705010c1119061103010f06020f0705010801090506041d011d0a1205030c041a03 92
    0x81d1920400080c00c42c4220301342c0300560030704001c0a50b01440c60f2a031a0283d0040041640d016608001c0000003070300800c003d000c42e5100340d05002c080d2521924550843e01c00070b07515415900100200d402503a40b0400e03032544503070312001c00e40d21703200722000481c0781000940141100d40f06600c24a640410720070041c0c81402412011078a10030345913000c2c541c98041c20b01c54680c2591040051400d51406003002e00b888414070000024160b942d01341117400e542090000c00007103400004c0c51810b000007030003028002065814001006204811110350350a003501110b1505110354030414104151500500a00440a02c1c0140c4a503140c0e80b042c0d191329110711414002d0301c00c0481300404081d0200e80c1d1400c07904146c40360301d0f05a107012070490150000800b242e5210b6030340d22542c0c445580024485519400342c80000407001001000208000d25181119410390300070030f2a100040e52500d0035004200d054034025485e034a9071203405460b80110381203070f06981100320b0748510b484103078000356105d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 55613043 1250 55611793 55611797
    0xf031305010e011b03060320011b030306090b040b032a03060c12010f0b0702060d0204050306040c14040e1b010c080a050307020c0111100c20030301030501240e060a0b04060f 76
    0x1102d004c02900740c0484803580b000400c2c0380c3c5020002000050586211443c06406041090186010080300d04040c12002822804203075205024045003500c0d00c90742804000c143c400304540264000045d641d440840450909000e441c2c5108440100705040f810100c40301404841c0603007000191001c154100c0c41403000c00c1c2142c0d400004054111081c1c61046801c43d03002c9a151450300e03000d11201d80d03c40801d410500c1d230204000112500c040107a284228000d0300303541032844c1030181c0820104501c46100f403040d0300b09507184940c1e643c0803c040c001600b10800ea0542c1c4003020b001078400628021010b080048041032024515402c44000e42c800c3c20305a080e41d030305504840042da2003400307c0b070115005030700421800140b461507a019181c1031142e820004c01070148100c0d00b010030315240001c2505500048010000c100b0301f405405c84489404200780e03050f9580c645401c5003042c56214066030b0056410100f02661185d101d0304000d0030341c121610f641c035511850f0140107a0000418240 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 55614293 1250 55613043 55613081
    0x50a032105070c060c1a1501020f0718050a0f051608060411030c0c07081e10050c0304020d08070203061015080105060d0b0604090609050910060b0f031305010e01 71
    0x15003841041151620383c3e10030480030a040c00d000341154505145601201d100060003803a2903441500030f02c2c0c074494403201d0301030f04944010000090401c3c0180c03454409a5100d00030501442d50030740c180c08001403014400080d240c3d03614640310040e0805001e542229482c110620140300d0483e4041c0c0300b400b48540301c00d00c0035100c01c1e050104072032018401e10110901400491496100540106911820b90f001c84400e5500c450046040c240764904840c240925190803010301c402c01c1c0407034140e003d01001c0030846443c00030a400c4043c0f000a100070300c607220b54038500b002c000200d030a613000c40303402504840310740c0342c08140d0403021610380c05409801380900001d0341c3d000c0e2054464034113070ba60242c00c4038182440b0038401d0b0040e2521b10a0345030b00490074817011800480c5031003460004c243c210404540c0382040c208190401d41c2c0002002031aa0a040080c04042d0b400000c540103036141390b4003a60313203076603a40180180d00c604d4040244503500b00000b0343d2000105410607041c118200107808 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 55615543 1250 55614293 55614353
    0x302100c0906090b0c0a0308090f070b0a17010806070e01110312040b06060c0d08070e06032a070507031203020f0d0501080705030a02090f091501091512110904030306050a03 76
    0x501c03d4000c0005c171050641c0035420300000203129104458200c0460403c40712070300d0071200d0480c01d240701a0466900581c01240d0100340941c040d01c0341040c2c20004166401d40c2d414075500d1741c0c6410006108005010781441c5140d01a4414005030085a200f01d06980c2c0321400ca002800140805032003d444060401001c030b07005103020022a0038905068004214080c0d42d000d00b41c404040080200042c4020386070061140e0700c41d1002544070341500260280c020300b180c0c4560484503925802e8142c50300051104900041c0002000740036286c002e2401c03500103400b450114041d10814a0090000e2004a0030540c80d1103541c1005040c1c80102054502c499282d4081c540e450b01c1460029600103071241c00b0854035840851940e401410100554003c01e0344010a401c01c120f003a4080c001907a502c03030300c0f00364030039001241c980a40705914140c10a0b0105442e401c103806119000b8511840f17441021404050084d80160020040600800d050316a05c0c10201018004031056003240300b40c43c1080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 55616793 1250 55615543 55615559
    0x606040803121b03070c0308090f03040803030a050106020f07231012060524070c090509070e0f0103020105070803091612060501050405040f0f030e04151401020703050d0c0302100c090609 82
    0x15a125174000d6603190725001840e2070813214204050200c40d40c900814020b207103079900130b00042c00580002001160313242003002c0716004480051f80310b1000c6401c0070701560000240420084110fa110107001c900c840040c0052070342e000b400440c801c2e07005064900d44400c158000d94100c000200c03c0404000495403001408000c140c0d0301c448a428514801100b09444140406404001d008102c8890010348406010044560540300310825034020001045030680c1400d2940d80520a5001c20400794507550020b4154000c5035030083c4008008000a001120200601a55400030781c00e04209941da9a61951100c40b1010003681c800e800c00001040c0ca080c01e0180a01643d40541e1100d00c0b040e03907881e164185440751000728104000802e00b240e4582d81e42c0074130405d101000c035003060040e15010890b07007840301d440c04150540d000321030100003061012503400703504203d50030300f81000041440d0407800d20000b00c80500c401032a04101c403010341c0c7c1c00400388050f00d01c9500c03540d00c1192540c000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 55618043 1250 55616793 55616797
    0x7260712300201051f06030903030b0d2d120c030c050a0b0a0b03071211210d0905030c0904060c05070609080909010614070f1505040302010504020f04091106030606040803121b 77
    0x179146612002100421200d4880e41c00008164043c1c42c00240c000ba5200008500c0b0301d91000542e07900c034412600050a0900c00d00e40045020070b07031a142e214100795071b81c1c10750002031000c99406120703c0803d82c10601d0701903100c42c54043c0e489030554480382c03e185080004140d042c0d030084d4501c1e03d09601824141000903440382940c040d400c8500a070020341e0b9880c0201220380c441940c2000c11080d0204942d80610700b200443e1505802400e80c402180d080104200c1700c0e64031251213688140c4a80005488205030582c101d07400c07200100e180b002c8007406a445115654000700780d02c0ca007082c2e080034001071740f000d468081412114801940d2b80c50701e0231528010100c030000c4055100700080c0f400204101000d0494911610351201084c440c5200481150000c940a40150751a901004210b01c2d0400c104d0418203c05ca17801c100d00400c903114240b4000244d00d480f40602c1d4004007081003540d811096078010007032103003180c0d5030b0202220303246080760040e0380c0b8019280011034500b4103c140c542c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 55619293 1250 55618043 55618081
    0x9010e0c0102100c0e03100606020607030b180703020c0a0501020403061409060a0b041d0d030b04020f04050108090307050618070e01060e040f060504020c0726071230020105 76
    0xc0240343c9880d010807103000420f0000014014040300654510480d141800380058020815034006401031030104040c3c10240c0003002e0a0800d85021a9110756558141070356604602c40c3e4104443d40c0e4401000b07500901c0380200015092080c51807a80030014150001c0c01628401c01050105003013a150307040220760181c580f82c45681044000881000300c83d0300c20000481c0091001c00d0300317440b0141081240620862030042504402c0351348014941600903012001e1058800318a001040440303210f40d4010f83c0100303410050000e000c01d011080400513507074000c1c0c100d815a01e1a0401e05644030100d0388201d0105d62601402c40d002500c00d1218050904941c10781d25039820307079076808040200404c400da184280c425561034012031641c5403840601440c0303840b10028034007541000d411650752403420b5120710300a009024040c2a580300030a044044400105020902c41001e143c060003034110504a01165400114829986100900d4145a5101a400030010750f144d07542d04680c020a001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 55620543 1250 55619293 55619297
    0x41712030403020c091302090109020a030c11070b0d06031e0b160509040b0d06090813080307050c0402030c0c0a03020c04050702010507080414030c100f0c020304030c14060c030d0509010e0c01 84
    0x3c1c5840e1250400c017441c16489078504030320201c203030286d5000607200f00c0c00b80c00120301d003580450300c81d01311a0548250f111140d0310b13050035084e02400307001c078594881d82c0c0d0259002c56200450280394100e03da4001201550744480703000559009a22250501c401c8107070165108022617022400a050404045010601c50b41d00c60b468204241d05001c0a84501c120440c1c11500740c1e080c1e04007052035032082c04811442a01c40d80e5903021103244c04246050f094000440e550004c000d6030000410015a180ca40c0e501a100940c8075a281030100e146401820380440450082c45110420184e0120703803404100d0088a0402c6a5141c0032001c0382240e0b030884442c07001c541c6c80070125020659020301e00c40c00c0d104c09411a45092075140740075040040d01c3c0e038120b40c1c00b5210b214015804015000b0110f6041e01d030310065041500d1511111981c040512a41d4011400122444000e0b1240011151049030801c1140e80c1d6405044003440204822030b90f11200e0751910781032021801d400305540074400016 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 55621793 1250 55620543 55620553
    0x906080c0a0c0b07090305070b2106040b1509030607110606012d08011805040b0106050f0d0207051005012304050c040e0708041a010f03030c020a03020604171203040302 74
    0x12058000c42503100307a009200b4400c9041090002580a000301c61050381a5078500074014a10704c2d0151402d403998002d011102800e1114082c1161551000505810210480d441329102c4c030000c5401464082e0f5025003214269502c40c18403090384000303024030101a0100c0b92690780e14041114003080c5054a0b00c100d811641c0442c55540c81400b288484120b00307100341c10307422481d0344440c0c0c1c1078001065200c00b040c5004010071514201890084208540d03020500141c6070a48c0c4140c0c0e202e20502620007801004a00c4003030300d41552050b6090f58403c11011940c4c0c416905043d03940b501c11148100110742490f001003030320b0008200581c003210341004d118042c1e80344403042201800c401000e110b010321040c000003803c4900307010414060b428680320150f2504103400e1418201c040080d40180c11110407004000342c90000c0809402c8a40501c1e21148400c3c2c42d100084800d0a0b070750010703600410109000c102c540020405550320941d2100711048401030448054050008441c090056004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 55623043 1250 55621793 55621801
    0x41403030a0c1b091e0614010206010531020c060702011103060409150603060902030d02010203060a1418070e0a05011404030f080408010603060207110301051303031a040e0109020907090608 83
    0xc40c411440600c0f0400c0a0000425243c8031182c00b00d07110903661805521308840c0140e5802d465110b803030054608016101c001500040002c0d6031003034188a00c0d40180204c402090b0b900b0790740803455003004640d50211408100c03841805e0041e4111103e0040f20f4003640e00400e805c20700500c40c4902c0ca20100524504680c0c0b5402088000d02d1080c2d010f4942d0b80c154481b0580c6560705100e8400910b200340c03400908558a070041c1880c00c42070040c0c0c2000d580c4100706014143e41c0e00c10102e0300700c510103007403030b80645240f80215486a008861740100d4591400c10300c6140b079000303c1d011402c410190b034280d168941d55001140c80c00c140d4180302041c4001000280041104200c03c80a5035010b2042d440ca0217a91b240d54500711851503200b6a143c0d5800b0440c80c3c20002510004809008114002c0c001405c0641c9400b200503560785009051507601c00721070020050341c4895101c0c91100500c20001b540045006a001c1e04601104902c02c1c042c00d40064001805030903210141e038125500e08910b80c0d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 55624293 1250 55623043 55623053
    0x40c1415090a08100203090c0901030b010302040203040f1a0115030207080f0d0e03041806090203060117150a0b041509180207030e04090f020a0b0315040b041d03041403030a0c 77
    0x30004964641000c14258045000b0008000101021355140c0c8016540e28010702c0381810f000094801603c00c04a18004201280081d152181940c1d011600180d503a142e501d4403103240c510300d480041041440d6030694585240351100e1034122180c1c05285010902825000c4049110300c0200801c0c2c2d0f40b0500104a0000c1e038507025110000c0d01c0040010b217500410710a9207190805c1c0d1184030300b8006641c00c41032070100c81c01010300402d9002c8081d42141481000600b0581190143d0072030403031603900050120f403202101444608015200b0b14980b6211007034540e1a84c07107401160b404204416120784c0741c501c6048028221411182d04068440c00d0609040c00ba41c0700000940820140d80304146030f542e10751007a0001d081c072850f01c248030072410b07205000c01042540d01518215000384100006c04286805d54807441104840000c2c00120b80c0c030004000b40b400c03901a586200d002c01150030760240010061085d03031515180d08141148600405a4034490142084002240301c030328000094 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 55625543 1250 55624293 55624297
    0x1203070b0603070b0318070602070509040305160c14010305090d0c0803090a120c020f0102060103110f0a120b18010e0c0607080d050403030c031104140f0303040312030203040c1415 79
    0x1a00102034444880d038403c49503006400646048520300750f034003221310b8140c00c201f1021004040500103000c178245804000b59008a006001400344640041c5090920205240f0440400e40c40500c0c204c42c0d40d10703080c4010b10b41c2c002c150713800c3c00300b840c00c80410143c0d02c00040400c0d500080f0354a4032444c81d01031307440c03000c0350704003402020592055440c0e0900080358000e440088040300d50b6804c10300c8a06004000448402c11002415500442c2c0140041504a0080c0151103010b0390300d04c030000714802c04210303d40c843e5030025100450700030502c0100034070b41d105240618520807240c123030320410120940c02c958400c4040e04281d40001d0400c22207043c09000f8008041c01104600e00301050311011505541041350124002541c61001310200d58142c45030104100003400481d00f00741c104002810070a101900c3e0a2080381000001c50301a0380400c200c03005540e02040c0a0000c1010030000b4000c0d400554049518502903078010640124012a01c03102070802071180301514480c948091083d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 55626793 1250 55625543 55625551
    0x604021005070f060507140a02070b090f04050910230103030c0303020412050a02010906020c21071203170a020f0a030e010b0307081f090203030703050c03040e0406050402030105061203070b 83
    0x3014061002e10003103088038062074410350007078501003007030f1034811001000f02c400020050b40490b414001e14000d6640041d000003910381c1042e125654148560000c0e000401d8800d0290b8050308080401503a1040410030200c214101403061004213000e4107155615040401c104164012500c0104082440340c40e40c91a0303036009040c014905500d6001904245605010075900c951240e0360716011942c0c0003504200808503440030b82900c3ca48a40041c179030550700401003141c4400320340c1c101301052080c403051004011038100440c1818440c6000f03468403848401c05101859100001400038945000300d810070049200f05074034010451a00307400a043c5000303049421340d6a200301d1891910104045006003c500c4024600c0e080040380c0504410b4003402e1100c0182e046c2a8200300585000042d110400c4c0d15042c07060325000d018000d5071450049a1190a401132010140030621465600450080340203400a011542d0740c203040c05000d642c00380345d0a1140e84100999004924002e46150300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 55628043 1250 55626793 55626797
    0x120f0403080f09120615120f030406120b0409021c0516090b04180506010608040317150f0f0108011a0906030414070602060408040b0d02070609050c01020706050c06040210 75
    0xa0035200c1c1c442101a03084200440102a00015100303060716103800030f00e00c1d8443c908010700c454504090b1000304980c0d0159401d01038108500c942c40840c000740916041507403003008036600c83c1c4d40c1e59030051810f50303458040c1c114180b60030040c182e5410b050040d40b0006030080c011b41120b2040301501100b80c034440c0c8064502d80540c180c0d56290301c01c004581801003201c22004030306030801d0b00400c411a5040c1c03c0354030000542d12140130000b0350102d031150460b040341c18080026503c60030241d5220b4242c0c240b130b5400d24044810080507000401201c40200000c0d80c0c3e1a11a050800a015004117410720090102c2d407488010031a081b5038010180c041d51600a0141c240703a5824081010743e042620b0895441034211303408081103c00708000300086c0bc141c80140790302d0a154460206e544a01c1c000e04440c4040010f00e441039642c1780e01214809c03075006008000314146406c04a403542c0c505800b02c9e0043c0112135000540d00d100e0402e0f00c035080c02560141c196a2105e83c00c2141c2074941b5824002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 55629293 1250 55628043 55628047
    0x2412090c03120e04060f0e04031205040503041a0a1d010201020d0203040c090b090f072a050109050106050105070305040e1003020d06020d110f07020904150c0905040b040608120f 78
    0x22140c9196100440c41403110101000203102e018080102000c2e0203801645441000c0001480340500c40342210754030341c2c20078640e0b02c0c1c0d8201110000054401843c100c4c0c1440d081c4800c01c41d00100402c00c0301c2007800c400702418034007805040705106070360340140002c10305158440b2510043c04001e26590050000520740313841e5859a000f640c000700c500b502c1c103900c10f4400b082150811b010380f100c4240c04446200303c2d07151a0000640301c4001401703820400818006102059106150f12461145030f00006040901c140c949035000c0e00803007400312142c0d4200b910024141d400748080da42d420f545502ca0a05080c03c0410352a10090002c250f100300340d1036a0300c00005a21403414aa00031800b0350300c09662350f40b56100304401d07501d40c2c08a405492404100b0583c0d4048480c00380c030002d03030317046881103107a844904010440352035140500e0314441c0741c0251000f00700d4000207040111081510240f210020280070041164500d1050624503004156801580c1d980ca900511003160b480700c140d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 55630543 1250 55629293 55629311
    0x6030c08032503410c1c0f0302130b03040503090a0602010b010909110f0310081506060d050402030c040c030207030e0303160803070903081801020c0a0510030f140a0c08012412 77
    0x550100c4801104d48080c3d0001d140e140302c0500303110f01030485040080b80078490316038100062805600850785d80805a01054800c0c071500383d520090001e0081d00c24030354580c20141440b9840c5e50040e25814841c4500d600006061801030007030f03000c6c00c0300503102c1031452441c200034880580002000c081200b0300070010400c0c000100805507004100510910524a050122640c0707040760f0180000c1000d00c0082c1006481d03544c100480702d10402d00031010460341c0f11031012074900200c0307400b115031150815000b0819668140e001d092114000d0703446002800380d034401d141d2a0b00c030b03440a80820b0001c0e01104008205c03108011600082c061a1040e4010b0b80da86a00005401c01032080460703201da07015030a82584d04110914010b6401c44d47c0f40102490700340001c2d09501200300d0501455125010613445e80307010b51081b6201590403030903000314034f44900500002c1000004d0100850b800310008110217501c003040340f42c98518410890980b0410403402d903044810350801003071040c1c45082e44 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 55631793 1250 55630543 55630637
    0x80a0b030a06060f32041d01060915050906030d030504020a030f0501020301090b060c0703030e0402040902030415050f070207121110021f0b0901090203040606030c08032503 76
    0x541c004c00e4080740e180000e45c248000880c418101c445150703441030a43c1510070303c5142114030412699400c481c0000c40b4800411030100c0c0007a40c0d45100750707170351a00200080c8940250414641031700141c00050400f40c4490801450742421707504c940d0564820315180080324065800144c0060008004100c0b403540c0c1d54a2251280034039200b02c5499402100412241041b801140c001c0740040b04c50605116481800c20340d01c2545110140c01c00140b00000c1d01c0345d4407181d04850150914000c159602d18003030802c112480001d0b14a044554a048006030403e410755082601136445d035030141500529140f00141c071055614030580d194160b40d0140803296a42c00f0081075141e074140c001c1c081d8505c480d1600040031200c1c4414950050030505203014903078540c1c1c1101c0c155601d1000050b240e03243c07810540010800d039000280300705403200c0f000c0b511620000140544c007408171071007070080800e9081c602c00c150342d070702d0000d010540305080d01d4584554810100002c840090442c02c3e510a59440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 55633043 1250 55631793 55631801
    0x9060c0c040b0904080702010f09080106030f0b0603030405010516020102030d020d0504110102060615030a0b0a0b0c011104050904020103021602130b0901090c0806012a0305030f0603010903080a0b030a06 89
    0x44114568848048036a2905190081003078480080302ca1240c3d520b40f985489007288100d0308001e04120708100b400002038000c540d0000036000c01c10080001507101d14020000911290041d01c0b404e81603c0054520301e400000c44d0166281a91070328100502c10070322003d4045048000ca055000038441001500c5203440a0910700c204503402261030300306820712200300ca0036144202c0c1150490001c004071078480f0820303805040411482d0b04c0d41c0e1340e03e40e141400141560114968845000c0030700280d09100d0700041c14040b41060000c000a601044d0020001c2c03103a8401d05800070b00300c0000401641c0280d000d40402155030b88411106042c1d9800503101440039036031004010b82c1e4030150b0702039050540f941805030170906001c01004c40100740107044100000c00090400c421011400c48100d00c0c05100396402c503000341500e9a0450614001c0e1480e0412210072002303d600d40d00144207490140501c4030101d070144c0360402c154880f290448003804000000300c0c1c05104004448001070348503c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 55634293 1250 55633043 55633057
    0x31b03020414010801081e010905030c16060201050402030a11010c020a03080a14030405060a0c0221040905150d0201082701020306120616050307140307090501021014040b0a020906 79
    0x6001030350780c1c1c10160100c0809440c10811410080c82d1001409445800038440790b8144c43d03210340710105c0915540b42d60250140441c01800c600000c180c00c0c402042c0007540402c20030001d00e410046d9510b410040f42201c204560196165201700d26000120344c000080081c1e000701032500c10400c1c09030f6004600c2c8045660f004440013007000030031000d0745600116855550383c00d0117020786181800c0c0c55055450601400e40403070f40d41d917040410801d0b03008220b000320704052a121041d5000e815800b0752281d07042403144401980c1480005040b0181641e0540c014107030083caa15100020b03600119503c2500401340380000c2ea0000822017003030780100341e03541894868000075030399203080014042035206910301c007000c9038000800d10012800f1484c2002c06261103181c01c54a96030345141c2101c240c003038840c04503030140002040c0005154407661840584c1d80c20f8080303e400d5130540130140112815040f103c4007071490003010030000350502940540100303128901604004502001134110385c0030301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 55635543 1250 55634293 55634297
    0x4030c0605191e05060a0609090b0307050d050303010f0b040b1804060b1201050a090519110d0903030b2d061e0c1006080d050a050c07090606050a08010b1315031b 71
    0x1200c0b0001041035000d0307030742d0117601651340e103045901c0c0110152804400f4015044541e8660032076011a0b10304010250040000a064001d40102c07424056240e6000780501642c03c10000d41c003061401e074903001c9a0484054030075580c0b900b908601c000b1a000c401c0404541e10503252030300000c0620041001e020034031141159410f19504d4a03080000055065024403000c904000400c8040740d508140e1000710b581d80d07900440d4004454121201034410340c540700540301e1401c4000ca0905030702d580104441d410a407030308400c60f04070035080c8031240500200b035000145201005c20603801c1c800c0140410300c1d200044041071805000188082c5c0c1c01c1840988902c0c0d025941d083c000070502d000e5440100103403406050103841045004009204600044062200005689403500c208200b0800240060f10007004102c2e20f0f07100060050b40141035200002d64160004502507409404865580c40c03103034101070310b19213082c0c41c140000c040f26481368241661180c0c0101c00e081e16954402c1882c00e1a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 55636793 1250 55635543 55635581
    0x603020307090608010e010b21070509040c06020d1103030105010e010c020405150307140d03081503010507020c040b01051201030b04030c0c0f17011505090a090609050303160804030c060519 83
    0x7003001c490854505c071b24400700d181c0c10241070501e9903ca140c480d00c409441001074440400034081c4613441d146250380600d41003010007082000348400c56244409481c150341c01d6510b071240c220780c1101d001d0b0005101d1380d43d40d00200010003441d070003900c004080103810b05006c5003c0c0744e141c001a003110021107070800300c0610114610840d02d400d00940d0086c0400c0c0e000524090b03401d1010400071552160010309104206d004120b0711f4214184580c440700000703000f0320440c503003580c2c000c3d1100f00c2190554082e9042000740c14040d8011002d990801c11400780c800060703803031521380200b0504054026014818440045004181c145030284007a00c2e6449402e002c1078640150120002c20407540d449559150010f02541410000040403c882003150051565115110010002d0420000040c0407900d040303107401c02c01c840030014510450104040580200800206035a1010225001800030391403082c1d000c00075010b40e10440e000208503580c1d1620b0035000312550304a900d445e00040e2000d0307039 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 55638043 1250 55636793 55636799
    0x3060d1e02090601020703080d270c0311010504031109071b0b07020706050c1504020a17060609090a080a1209230f0d0e011101021909091107080703030f06030203070906 74
    0x444a2030741c1d00183c0c2840140005855900d4140301c3d400780c51601e03a0321075200d075501200c40c800e030300c42e0100f01c120041d218070120700039207440c0c841c4801d90701c4210384da031170840d501000c03a602900a0303504490700314101c0724000601a00300300c150400286088140003181d541200e5000e1540803401c2414031030462100e1034140300b80c02914104490b401803003041303010494000007080125004d0407024044520500644a5200060040c6641c0d0040d08292403845005081414009552400341d00140ca441c185070300c901000a03141c080041d0040c110400c10014154000d00c200031803080c25040d0039001800e008a580c4422400074101c040712507181d00c04c4001a450b60341030002c01808102c0800410042482001c00b510301324000c912a030500c070340c80700000150003081d0110744003500c0320740100b03400210540c1c0282a5842901071340450514080c0b0108071044904202c408003600f0041950405840d9a800c13000740c500741c0021200d0580b2070100100584040100780c010f450600c10224100342 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 55639293 1250 55638043 55638049
    0x50c100212010819030f2d0e12010207080412060603020907030e010e0714010f03020d05010b0304030909090503090d0f020a08030309011a0a09020a1103041d090a110603060d1e02 78
    0x82124544c2100402c00000d50b00081d800ca88140f5001d00c1c2c0307041410009410100d004011100340075104102c071992619202c20b1544800301c11a00b41088442440e14611072415608134040c041c001840458204028041501410101c02100c0d01c21900883c510b03482e45d010443d41401500c000010945680c21007801c21802e01440380c0e241940c0000b4a030003480d102c0104111200030406a0500001283d00e2030901d201e90104e500c03844041c5802c4c000c1b5656080791300807a600407501a00000d400582c045030254090050007003042e0008011820000c035482004100300c840b02c41140c00e201580c0134640161280c1342c2d41d000410703054014644915143c0b10450035510480c0c0213060000c0d81c400c0301e030a0703aaa407401100a83e1b00e0f003000181c4a42030010191040c500030981405140300c0800d0019940b0040b9092244513180301109410701d8562203940d9542e0001f11000070030000c40b0f102c0d403a00600b003040c05168400c00040081d030440410b03880310015000750390072080f10804109880d03011343c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 55640543 1250 55639293 55639303
    0x120706020415080610030f0209030738030109051509130201080a090c030602071a1503070609080c1003061203110f0c031b01140d051801020f0a050c1002120108 70
    0x160305810151041d2805000040008200002101c2811f540d040d100f04000d8080e8144c6100344806000c644085458215150900d40c461101211401200001d04440c03100e20020214440904045600390303400c008408000c1c1000611070210964a85609402aa01cac603000c5805030702c000c8180c0c01d09102d14000140350b408014500206282040404400900c4c0b2007401e03412243c204100585600c0d0500c0e00c0810100780304aa80071b042140710a02c2030440c00d1440c1d46c0d44040b0120100c50140c0d689a02c1520031508511034174035580c000315102105070400010100c2d0304041c1e40740025040f6140e01c00c00c620040000c03030903000a9160700c0440281740c8101700c0500f8808a1a0060440c180f0000010340c3e0b824603404800214613640c0d90340c00b010f074000d100401c2c1c2407612281d2305446401e00c3c0300000080604440045016503001084d8200e5007061086581449180041074580040f00b001036401d41c0c0014807000c417a119139140f603d65410684043c001030103d01c02400c1a40d403500036070134609 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 55641793 1250 55640543 55640579
    0x6020a080a020a0e0603040c0b040b03180601030f0b04020d1e030e040b0913080702040203010311130c0f0c050c0603090705090a0203060f040b03031c0608010c0203040b0304060506031207060204 85
    0x150b441004049a0a60440700409000314111052543c95a4910b40b001540b040c07680a07031007040010401049083c0e260018601c10411a2040c0140b442034400b010b0380c403242803001910070203180c0031400c0030640440701d5030303032081c00a41420311820707540e0f9903403c4651800d0201002c60001d09101420154065907211503100d040724140120080940050788600b00904160482e401c0032800300100400300054511150700104119120760756400e01482c15075094000503c503003048144154244114490b80b407034500359a9031040141c03441c04065443c1250410107907802d210388bd0280d62145d503044010351142c84114060701c0803e00d000d0502c000d403c00a01041c0915005104001050b200c0700300c2c1d2110400c080b039000c90b0240c006800b09045104a07041c03c0034011260751240304112603600848200c880940c020440c0f1000c510040762039008901852056800400115001c60307116003050b41c0020000b001d07078028021145e16440746034041b00040b00c1c4a81c000c24100419882108181c200c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 55643043 1250 55641793 55641811
    0x506010905030109080a0c0f080d09060e03070b070e01020307020d12031b08070e0607062c0304030f1214070b09061302030c19050604030503040e01060c02010519020a02060706020a08 80
    0x204c8143d69900114003c4492590802c00c103000740ea41440541d40c003d104003504a80460b44d6000c940c0ea00c000035108031701c8103503000c50401080003060302000046400c0e842e00441d1941d0ba0f6100e40b8002c039410042c240364a41184000c0c800d02015a48040111403154031440d00c0042828002c80d010b000d80740c0c4103000b40010b207680080c1952140c1c01140d1154482c2843c030b0240c0b100416500080c00714010150050120f41c85e10354809185d1202d4150414020300d02503100c5a800060200c1c1581d0f40320b00e0200400d082c3c10042d410000582d981407415000105041c11b403629036036000c8124441e0080402960341140000a04c01d080100340041c0d90040c035401d0620452100540100e03942c1c00031441c44034020240b5a43c10401c1c0100e85030b81c44041e1100034070540c0c1c0c031a80c0303081c0071f0381e40c1d0400d0003075080111100b00000b9185010314521a012039040e1280c5040070140c104540c220712250314290154044d448105005940312001082d40a01c6001d006888000413080100b0303e44000f010499 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 55644293 1250 55643043 55643051
    0xc010302040f15090b1204031709070311060d180606060311030f07031b0e03010f15030b1e181501032105090315040302190209010302012007080105060109050301 71
    0x1000c0280b001c0c03100e050790700040380c03401c1c24007078420120b940c00303102c0d031100280303d10128034000200e0140366504d0242d4043e81e200c9040241c0ca00c0b4450710302c1025164006c850b8807070300041000031300032401c00e10300440c000c00c40e900701302800b40b605043c3c40c60b003921642c182a0141e1240d0421160781f040002910b5180350030028403072500f252005920000d00644c2590400500164000e03103c0e82003e00d00c0440140d684039a41c004160103048141f0b140d000ba031080d420b02035094030861943c400c2c10780b41c03610b0421070b01420340740d503c2e106031454020b481c24001c03c078080390b540c4000c81c0c02d000d02800b40400340541c0b80c0c6000320780741c01801e1581c103a02030010410702c2001000440c5807101c200c0e0251040c0c1180c540c40d410020400d075098400c01001540600401c2c059207030445006240d40e1040d0700035001d5412881d0980c081c954510a4088001d60104200c00144055403090040802c400303a01040100c0326412101c4581c64030341d09a003c441c07540e4492007000300c01e50340064240020b000940c0240 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 55645543 1250 55644293 55644299
    0xa0b060301030305030402060d06080304051201050603120c0a171306050307080c09040e06040b01030606050613060518040504050c01020f0a0f14070b040305100b010509060a030902010504080d02030c0c01030204 92
    0x80040c44180b1000d420800040085415941c81000700d032411048904204090750b0fa4015a81d1250418881c0a00c54400458004152141801010321030400100581011000c0c5d58400c612034114050004442c4507000000340020000c007848000390440c9054192290702250414040c11401e4200304200007090051001164228084a4001c0804901c45071260030b900081001022b044403094200d204880c180428400705d02e0105060720b01079842403140507103c20902800d4403400200e0016440001c00403c0440e2240024001c1e5a0398807001002c42d4500300000b40c1516000e0b03500f9240e43e00200515107866804108611074080d030305001e021a50480c0d00c1c0c000d003001d074021011782440c28a9220520480082c4441400380c4034000c91162250340f13038201581d0380d0003614a0304600310b01c1c040e0300e01c0b441d600a2096920024008280030b24062581000714003500036148200d05101041c030010405440500c0081c404114a42c011034481410740b40040c64a41c0d04104039041c544100414 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 55646793 1250 55645543 55645549
    0x6120c05190c1403040909050105060f1305070e0a0602030c0105060108010b07020603101d090d02030301030f060209040b0a06020c041d0703030f0c05010f0501030b0a050705040504150f08060f0a0b 86
    0x70308209181420950b12402c2c1500f450076001011882c91401400001000308203006640c0c040c40300301d80654020404c0c0da484805103c10341d05920b000321b0303211036810b19249064540e0f0300203071303480400da180c55148070a044000c105240040c5d046480960004982d8601030a404d101d240c0e4020800d02c0d00d60708a514000e90303c600c1d0300c10200301902030007001000814045d101a46000108100010000c05423510000c00f9075140040c0d8441d002c41c010748400211052000090b04e0590390040b81c280e421000d04d03625440250700c64000d80d90403079154040e815a0350b94030b81e13000d4001c0a4940242034101b82c55010007003160480c80c5100800000081d03a4038040e0f400081c07980550398141007900c10000203a071b0030b49100c640800300402e10b40c248611486083c800ea040f880c1200d12442900300692908a1140c0c15640c040fa40400080c005100412961619030010102c245010403400a00c0b07440314001d105588154001c5d070b12503484a0203100194510403421607001060301800c0000c00350170000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 55648043 1250 55646793 55646827
    0x703030f0507120b18130b010b03040302061305010902100203250c0e061c110f09070804030e1c1a130b0c0a2c030c030102070201090312090f06120c05 66
    0x45501940ea41c0c03001d003401e5101c01c02100d80144051701501c4052400558494174086c0c50082101c2d2403a080000080e6005c4e5a015130380103035415000b0b032065070f03600306040c1c00d111031403071043d2159900c0e042103001503190008150a07045c9268003460f513501421803000e42c1c011204001d601e66004020b0800007040e18400244c0650768105820038064940b240000e03100004d160700890f802d000c032003c882c200701440250b100019000d640d80f241618140301040071080085540d400803d070f152001900192049046000c400e400405030300704201c501403640c00040404a088403d2900018183c461801180416510018010a501c0011010303030391821a0a00034009000c40400840d40e520359074080c26001199400d94003141d000c55090080158420070b0840c08140280608012090304d1308040c000c4418042d0107071142000303989590381d005820f941c49802c200c03c1003007811001c118043e002d140740c4020001d6503603c10352070500381944000c486041d00d0b2101440b9042180d040c0c2030410f110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 55649293 1250 55648043 55648067
    0x602030d05040804050a0906030204150b1b01060b0d0e01050f0403020715021c0e0f040209060403080702130e0d020c030601060e100c1e03120209010503040206070302010b03060c0703030f0507 84
    0x3401155640301d0349080c50300b6020701c0c4c10455100703100aa01140709502030348030b242168001c9030140400185100340c1181840c07540903550710840108007042e5040003210382d088a0301100d00001407601d0b514260185c89421200750314001c0380d00c4504a01e14200240581504040345800031071039400c10742d9002e0340e02c4480e8400c41d2500401c2c2d400c8071100c0da0081c855200c540041c4071001d4030f64000c44074010400002c032031006129810210b0344402604151003521031040001d008580303072904685824849401406040703034003a1000182038480324080c019a00c2e80840c0030300820500d426004080e081c8800c110a10b0b01076804400100815580200814180403068541c0c2883d08180c00007214180c1c207407076000e061284100104035030f0300ba01040c0c600c030148c000d9032020701d0100003244090a070310400c2c0089001441c10710104003d458070000500c10707140329000015113141580040382c20004101c4040c4e400c400041641c80600d0b400d405403600300e0500c81c1c02004145060310300541214032600c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 55650543 1250 55649293 55649317
    0x50912090d0309120f1b1503020c03160503070201110105100323010c0e132901110d09060e010305070c1403070b010f051c080706020d0603060e0a030f09060203 70
    0x1140c180d0505020f04500c0014052000703004c2c0341c03e0780c0c508100c2d42d41044035000300d80481101032560324151166910300103881d54590050446004142c0c110041d401c4100840348138002000640c500081503c0006480e074443c0d0081c50715032009000241070030000d038071082c140384d0400301040300030000311a0400580b1b5000110b0350b1250070040742c104a544040705001d880d0761070b11030340c8142981c101204005024046a4000e0f0709007a401200090b40c16124803850140001010448801d00340ba0521102c00018508914412a01c0c0c03d032914181c3e9645502010420810040c4071241d400068040c0d4680b00f03007801d001c6803c00342c0c4010300741c0410700f0340079080d003e01010034101413200b40300301c403685a080111421696183c06000311121540d1251502c2603403d0048007808003078260203e4403840d0002c403001d0400c0c9103a12a0780181d40f01410800342569150004400902107214a140314904031005220864a03031a01a10013414000c0740814001c21785800c0090960000884100c90540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 55651793 1250 55650543 55650559
    0x6240d080304021509030109050105060a050f0d060f090c0f090f0605030d200d0315050a0807060c0302030906030a0b040e1c0c0c150c030305071707180515090405091209 74
    0x203982c1c1d0013054064507076140c0d499420400c0902c14804150002401032404507428415070340d88a08112010015512454001404402e5076003c100c0f550701601d07203a8141d45c004154400b85544940184403141c01c22a602080780e00b00317001d90006c622a069040020300c00800c0303154100000207550355000c2500c2c2e02005800640c004036621000c084010018422081312002c0d900f102003d0003402e1070903403c80c4805680c100c0003030b0034a0900c603940112948200501002c0e030602c0d00c00c56502d45945025015031100304030074079042c1c591400451146242071000107078038500404000075500d40c542038001c95400850ba550176044038020214a020700750409480c10040c07854031445d50f10055020350f26165030b241c180004242c0200610580c1e80c441d0790200300643d030380c00c01039800410300110200d040c020240064065400b40b248107820702102c1b003d8081c1540d41d440000c4806800261145100102080003486c0c0c0c10300303004181e000922500a0550f80f482c464083c0401c1c012465a1427040b690 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 55653043 1250 55651793 55651819
    0x61409070c060e03070b1b0702120708070906080105130201050405060a20011b020a0b0103030516050d03150501051c090213020a0f0f08040201020c0108070201060806240d08030402 79
    0x1d462120681c41e4050014801442000c101075103030f070450601690046010000101c500340c191900c0d681c0c00c03c0c55013946050068540038480041103581c200c80780c41c8640c440105032804200565070044c012100f010580b00c0c1000c41960075180c000d41030500c100e480d00c40c03000040c0c0c1c0110540d002d5a000395442601d4440108003112003400084036a468031f003202840e5002c000040d002038032050582a54100241300c001000c0340d40d042580b0000c0c0208005c000144002841540184600300419108100c074140300d45134141001c601d13072a0385d000300c1c2e658148aa810340513008400020202401c100d41420990b0300040c05400c08545a000318030350742d07140a02150345403c2400c1034442c5640c1c04644643c1034681c0a040102c0160000d0040b480b010040108144a032130124442c5034181d014010036001c04005680c0e0f404003504503002d55480f808040360443c1d080011511543c12680405041e03000c0c0c440350000085820303440d07801030130307900c807104045180c4004494001d03078191466112580 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 55654293 1250 55653043 55653047
    0xe0f070e040222030c0b070f02011409270903250816050105060118152a0506160206010e010b0708040906120204050f06010c060504020a15020303040506090106140907 73
    0x1207030035988100c00400e403c01007090b40003000f58030b0540788a21203c0c80318507102c0c0e003001d926000e03505c0c00420b110075110408006504c030720301e0000a0105440c1c3c0f541003503840c50001741ca0440b04080c10b00000150407071607201401a960464015113101d020350b181c41900e21300900108601c4a000516040c000441401c110514084516400032050890011403080c580342d406050140e660500060782d001d141c0c1c4c400f4400801d103030204c0d0196100036500c200f4856041d25103c02a41000803070b180003480001c000c564015a103400d0320b224a001d00403e00c1c1c00440c0d441d2800034540c2440c2158450001030201d03610706075066054590b10000c26032252058a443d403180e2003a07801154550381400c1e40011141d55203401681401c0c400c44062129640e08043c0c83c001541c2240d115000035414080340001c6005a070140ea002800584000e0380311f0f44032560005080a12018140107902c00010081400000c0c800c3d2608400315500a010451818503030440301c2075000c20781c5110b02d1180010880c428 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 55655543 1250 55654293 55654297
    0xc0c090c040305060103080a030b0312070303050714040f051807020706110709020f03090d0201110405040f0906050c091201090f06020a12060b0405030f01291c0506100e0f070e0402 79
    0x183d000e01241c115684915225900da000280b8410100c0d0a000e1050000e141c080341f40d4000150385000d09003000c000e0349045000c1c020140100060050882040b0fa505203c90010005029244181002c6610313001c240005c14800c4038003071272070740c00480c06d014066a012070710104841c3da902e001801c0044a000840c00c102c15640414a009d2000544159036840c2d4005140b1400990080d500200600c0e5026801d039004411125000101008180658070b01a405038204158a40001034003010300d80c0c0e0740e01200d5050f224100d81c582c012442147c68900303012500c000f603d001d00240700c94604c0c1d60f62154445028500204400d0b0041107883c461403060400c8001001c0481c0309002032a1b8401915006138402e0180304d00a01030300c0803101000d541400744000400034101100d4411030703140f404c90045462101c6103640403200002c071a90003002090b4245d40140210090b08860030003154140340700581d544100507400150041100b407030f440c1c2c41400ea002c947d60a14030031500c50b43d80010024 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 55656793 1250 55655543 55655549
    0x3021008270606010f030903021507030f0501080114060a06170601030912080118060b0d0b030a170d060f05030a0209180d080405010c020f1009080403021807140c0c090c04 75
    0x500c0240c0c01035a00500300141581c0070b210b00b070300e41c43c0b061203485d241202510080b00c0040d0150707004840c0c1e10341410041a01a601944c286800280107420050b0841911803ea00c000c50aa440e00300c0da42595411000042d0030000441700311400c18903282014160034081c0510007007010140000410a0f4001c1e00b001607c0b0703610500c01d0070018140c1c0009040c14500b80a51080940c3c00e0801030b840104a1144078142c4100c14211400c10420403d60009418407010043c4c05000301e0240c10001840c44a1300c401c140c182421003512400100002d01c11500c85600890304070f82c003e003041000380c9000c00d126511580541d004404d6a495032481482d5800e10000407000384123001300e01815541c401c100074042c9100d60001d101920070154220398519100c034201a854000c0391140c10f0717800c055032182400a1240d070340242015a260000741e050072890120318030f080341c110304004845900c00502e04000030310b1802581803408200455640b200e100710090b000b5010140820200401c840580f001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 55658043 1250 55656793 55656841
    0x3030c021809010f1a0132030112140102040b070305130506030a0f050f010503060601050a031e061d040b0606090109030204020d06080607020703030503040305090118030b1f03021008 80
    0x300b0300b0000c0d510340c020034540e00c1c030022083c40c0c50304054013000d0004d00b9407030001c0143d48441e40180c950186201c00d645040a1100c000110f248055150a41802650092160041e258403003101810800c0580401919002480e40b0401c0280015805001620320f2140c06103440c41e211810055030000c811220742000380d00c014040100040c1000780d030003c0c00800c1000c0014021a00e584c518030120000071b000300d513816040a00001c02c594032442c081c00410201c0d1502140e40c41407659003082503000f082401c1c507003a48030101446410580201c460f03031046804008da4aa1a1075110040440b102a200b00d2080d0b4001a40c091241e1040c440312000c6c580041007150340f424407a40d000002c00c1240b240ca12030740620400507007128004600710003200d4168880c04e16555499808890301c0e48504c1e51541804000042401c1001e98201ca510203944a40244900c500b8003440d4411401c28400c00035110080005041c00140c803614402c0340b200e6824140041c3c1034039001c003041411a00510b030f10314 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 55659293 1250 55658043 55658089
    0x51c05090a030506060411070507090905160b030708090f061603090b010f0e010f0305100c030e030d140a020a020309100e150d050c03060f01080417220605090a03030c02 74
    0x42800f2000c180d490203400304490801c000b2180e40612603030390041c80005016a0131201c0300b048060160303040036400c14840c20a454a0104101100291900139044400c00c40004800c00818a402505994010030020000c06540c00102401661114000d01d844602c007140e505501c3e42d180641c03c0361040780d9001019a58075a1180c9500e244800301d8403c414080341c40304000101102c039007412030280d0f070308000603240040491030010003a0904001410806030b9588110000c0305061014000514222502141e040c2500c941850003103400707420042c0c220710421031512070940000c00c865407800c05032418241002c0c4910180c94040311085083c0e042071415109901c0100010000d01f40ba0441c101e08111a448107000b1146074002100c00301d8111408820b00280c43d0b00401d0000c0e40039201380c0540941124051484000d41c21511818821396009a9044502106c2e80b4503003000c0c24040c031b415811301c0d80b003000059250b480307444042d05100000c0f418030150b4450000c4e40344041d8200044c0c02e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 55660543 1250 55659293 55659299
    0x80708251101110c0c0d0c030f08070206030103030f1206140405100801020304030908060f0402060708030402040e030a020703060b0f03031b07080a080307120623010c05012a030603051c05090a 84
    0x1410340c4c01400d0a420b41e00904801c02e889180880039000c0e0300d46c001505242041c155078030141080314204d003e452100e401c1c0004001070359002e0095001e18800c0c2e4500c003104034504005032100640300b600c90350150800c0003e018412402048000d045001c550120701070703c42c8441000c07012816044034503154000403c0106040e0402d081c2c100b1607405074119000ca54920701010220030080e10002c1d40300384100303e0070700840ea8030009180c106000400c00103540c1c214440300fa285a101507010005030b0000b110400c00d21405120b4034003d21426290302980030017000001780c80344074a150740032005180960340c80b01480d082001c44007a117150303022900c0c29600c0e4280001c0c2c0d03030411035895001540c04c00b040000c02c0c1c2c26000c0c050441e2480b440340381c50b000100320101020302c0c83e080d100b41003001c0d440701c031000700740c003400fa4840182444207500300d1050100c010212909030030f01d000b0705042c2040001c00000702c00160f505e20500d03c0183c42c84072906400b000301ca2070f11980c45101e500100c000008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 55661793 1250 55660543 55660571
    0x15180f1808190206060a2309010603050604060602011e020a09031203050a0621020402030615030a0c090b0a02060105090408070501051e0109090c14040209030706020a0201080708251101 81
    0x206520040b070318941e85100c0381d21904a03520481240d1040d00003110842c100b00c06103c52050b03000740921209503840c0c0c842440003180d0183d00c03d074400740000c0d44031000e110300f900b01417040c0005010184000d1080d19004401c91103100c1031b0100303903d00240d00054025440c0d1190400c0307000b441d408034003492100800c42c00140a01026a04a10101d00c2c00c44000bc014000c031030301c44403100d039022210001c050981c00b000025080100b2b50b907002507409000d0002c185000b40114410040c0d01000035045072041c000500d4020720703401182c18400708200b81c001040d00015120704640c41103030070008079665441c040b0301d607004500c0300801a600701802c0c820129100c111486180e4a81c00d110140c9a9840f1702601c2901d0700c00750007500205c0f50704401d100c88103252502244101d40035001500d00180c500c0030a10b8240d465102c0001600031240c04802c42d03038801c0348182c014846142410b80c40c240520101c5031041408640b29999a800030754080050061104901d074a1800000300110070b9041d481c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 55663043 1250 55661793 55661797
    0xd060e0703050406051e2707080a0c0b03010612020f09040905060609060f130f0207051c0306090920030c04020d0911030102031018020c0d050403030315180f1808 71
    0x3c212003242c1080c0000b06e120446ca4246880e801030048400c02036121a503420140003020007081c4407464821000304400f80b01007203c80010050200100041d00482c10003070252803998008210504040004000c1e00d07500000b407002507502001c00503174820320a024036869101d010040c0d81c00c64200704450041c0200810803921a100940f01c203802551410100540c40422811455015084406105801c00c4e140e020b009402c071101b00061400c1d1403601c0c3c42d0720308019044140c40c0d41c103402d046400c200e03078140207910080010503803d01c100d140c5651094080b0703000d07070389004401c2c1608801e081c2965080040404200d40500115600d001500710040603000381c2c4002c0e10f031403051a001c10864281482280d12525801e403800c0f03420781c2003900301c0150306200048140b20580074004a0070440090100580241054644680c1d540c035603d0b000e002c3d51049004c2920703040841c0300030024010b103200c0085103100d0340385c4002110101a1400c0300200710307200100400c0c58000341e011003001641c1c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 55664293 1250 55663043 55663051
    0xc0106060309120f2007030203060c0406020d03060803090621010b0315030c0303120705071a1503150c030604140a06050312070309060c08040e1906080a0203070b0d060e070305 77
    0x4110041c481610b90f066400b024011803c3c00061035041c0904c2c10304c041505640c803050b03c00801d440516a403500028070b000420758100c00c24503c005402c102403501003080303440202b0281024032169141c502801e40303a002d0300c140c1c18020140010403296a01c02c005500c1601031814183e41e0341c80d40c4034114a003ea4104660135890b10708002c407480914038000402180d0500300030002d5103000c461220040005201a00070424840c00707010403000110508510350060b00e400603001b40390b00d0900c42550b2961881103140c0e01a0300102d40f06280030114121040d4000f44080409540e9101e98011030001c125035010503925410550500c03d04440310740120045035030443c200c6a004101031144205807241d80001070100d8a400d40801c84a4011900e511144d4043d815003070900303039160907203c41e01808443c0c00789403224001124508032200d12031a40a42421802080c0c0b451103503022036a6050240100c50711100003180e9200303c0016074200c3ca0141040341e685007200e0030882e8019003d000156 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 55665543 1250 55664293 55664303
    0x6030201030509070e0103110301060e19060e0106051b1204081b011b03111006141021020d020d02040f0314030a080609040311070602031b060609040201050a03020c0106060309 77
    0x408940c082400188910a54401070344c5c0c42d9080e40703140c0d6802140c02d403024030f60b500341d52140d80000d10303940e81004840c410700c5140e00004c007484006891a0480c0e48540280040030000d0006101455000d01941c0741c104411012000700704644041d82d10b072014203420030311044400103011800a4000c500b6840c1248405807016901c0314103c01524644c4c00d542200c400365426500c8800841e204050000d03c03681c1c202c0030b944240f8550071034501550042d82110041d841102110850790600940b110910201443c0c101c00c0769200e20060801c40b03205000382c02001d40c02103014480c01d0b4007541103403011000d0920440d0b507584d45000d0b1070b0b01c07040d041c0b02c252010307142c0c6c2140c80720945001c030445a0582083c1e540421a5440c4010006200301c0500150100980b6503c0400394820800c11b890251107550010754444011120303401000401d803801401681110051040544545c0195500b01e542400c09688821941e0022402801001541c454075030820b000021216015489244030034060 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 55666793 1250 55665543 55665551
    0xf041e0606021504030f050307090b040e0412110606040902130903110706030b090615091009080c0a03021804080705010510030204060506070209010302120c28120c09050403170a0603020103 83
    0x1c00c185040760780f00301d40c0600412052503042038102e2286c0005c0d80e014a4908050b0700e0720b83c40f2038120925411640200e240480d6074410300c018060002c400040c600100e141c04c460081d20034600d141c1350040504064003542e12010180b08550320205c44552081203003400308814211030400034036420900b508000d840c051044c0100c0d03098864050000306010141628486847e0303503080c07000c1d00c8130b9955a02800c4006004a49165403101c2c078999485220303940700c1d01304508050507181814000320b03ca61152601610410058445080d075509000ca0b6800c021101d0350303542095100342c071805034010040d510300800c000708001c40030203d000f544c0c02034074200302e425200d4082c4035081c0316900b03000e076100d10110010001071418040c0240c603000101e00343c0c0c5080d400394006c43c0104414003060741c0b040c8603c03d40d048a008100c07041000900c5001c0340810b92101c5c41c0c850140c0c2d103541b401032502450310388001609040c01105020114000c1d04841216890006401e1004000b580000c0307000900f4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 55668043 1250 55666793 55666813
    0x309050f0a030e0a1a0901030603080a1e0c15050402030c0a15020c12060a0f02130603050105090c040303200712050604020a090501050604060c11040c050705060703020a0e0f041e060602 81
    0x642841c20540310590700317a0b88988003090300381007942c0003289400d04243d181c085c080000b41c406805003044908a80342c4100c10b00d150344a140390314103043c400d101000441010f1078081035840e01903600c900600180020300e5251800828100300d0603041b220307041045c0c1c11000904480381000700766038201c664281c2e014842d2038002c010340d0103410010940a83d2051011132034580d050b07401003203c000c420700300600e41040303030b80e041241c40c1d5079601500200e692400104094144420301a030300509818859260500307564002d41003509462004190b8664441c80205000c3c0800c109005011420b8803121180c45525007240d5400d400c940803405081c00d40c6002410400c07901480d4141c2c2c0c0000c000c14107150500c1d508135070840114806481d00140c0c18100300705500c07a442a060b1060507550707526502d0710181401c078a400b8019010800705841004240c249640c44a070f00c956100c4106c40d01c100d422200030010740078200382c64000360ba41b40400340c4860301040a50014045828030740903540c0400f2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 55669293 1250 55668043 55668049
    0x50313080d0204170604140c0906190509070203040f05030a050703150e0109080403050c0103060503120c010204030b0108010516020c06030c031306110310051504171f0603020a05030606010e040c0309050f0a030e 92
    0x103031231070850781c2143c802c901141292402a5485015140d40e440503d60242e07103000080c54008242c40000142e000001c05100001020840780d014180550003013000d8031159850701d070f942d0090b1001500e9821000c1d0241d044012903000310312aa1410340080c032402045003003031003030765001c2d210031502407058414100c1994040c7c0103d1040b96001400740c00c1e80122480a40301990000ca18259075542c200008800078070b51407400340c00380c80e0040000885141441c807003900c458224016500b9940600403501041d581c40c8122540070031505115500e07602e0380e10b11075803141c40d0850010030303160508201c84c1d03401c44420059441b030054101c50724002555030061144014840100c1004120100000e100d10120900006940b40442048400c2c49041d000007100136111203080184607500c504003002940b600e80b00d070a0143c03a00f01c0182199042103000a01801c0d100d40080e80220b440c0d056054915000e580b00c0b1880359000001d8400e01500c2441c039030b0700c818810204901180288070f024407581 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 55670543 1250 55669293 55669303
    0x30c14090703090b190e01230903040b0f09010306030b0703050411100203030c070c080607050403020102010f02030108100c12020a170108070506030a020304060930050313080d020417060414 83
    0x390085051040d41c0c852440703507510031060b442104041500e8030704e50030b1015824460540c0711009007002381a15214400d213040e840402900303c80e038a80c03080c8014000441200215030b441c0d90700503544d599503845240107030041e081c107a00c050802c1c01d4120411078200e8054014a12651080c2c50040e1110715410070082c07003081c68540e0400585c014000151000700d110010017100d8013078900ca116aa54a034810b500d8540115041070010b03202003010011035030240111300940c2803404080d4155030410140e2990b5034002249590410380700c03400740150b24021042c241302085800800d5548410000014203103002c0703c4012050190301400010301c100003c212101a94001000b00b8038503129005d0f034001030b400151040d215280d0b5401040000307451460303c04001c401d002e981d01d203030000e0075045048000700c0041e50401c1c80010003c001e1402d02c007003040c04e0481d0388460450740f00c088030700000c0001d001d5a000420315245040d403a03114042c1c0000c50350b00c0746100d0015001128001c0007110342394 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 55671793 1250 55670543 55670561
    0x12090b1605160204021b0109051e01050121060e10060f0509040302190c0f0306230402010206010506130506160b1302090402040209040e01050705040f06021203010b0c07030c14090703 80
    0x1e842c03014480030042c9007030340082c52007240480c4080105e0840c045403908540c2224021a1203a000382100840700e214540e2044d030035441c00001300010341c07424400840c00ca101d5905541200b0b0414541410031880c0d5101141d0500e440c01100d030a094407006500c0144042e0040004940355100c1c000340c689050b00a15200e42c0c2d140e400781c0000d2040d03040e504451a440001100c014207428000309030343c0103803024000110b0180c003000c50524070051454080c60325040741400d180c01d1060400000d40d0300012454112070b0107941081d9214055444500300b1034868000d01da01c44400200d6488160b05c1030078442540340140c000e120140c40f544044100c9040284009400000c0000041c016141070b030b0242089020241021030003490349a03903242120301c101d401501048000c1010301842c00302007030031809045180010710060119014000703141c00140309142000100007100008444140000340045500c000151051034580000c0000d040250001030300074986580001c101901c030707024002030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 55673043 1250 55671793 55671817
    0x105010f08010218150c060c03011a0a0c0227090a0204050c0313030309060b04021b0106080c0618030115080a1703070c02040504020102010b130605040c030203071d0112090b1605 78
    0x7406840c101780700f0b0380043c003201c0c4e0050000c10f205010b5400800d218052048030004035640ea25810601c496000300d2046108205450091008800c4c640d00188203128141d01140c11740070420b81600f42c4e103003c642400803c4841134813a018091601780004900106502c00c88040c000341e902e00c024034140780411143caa0f0754039100150304020901950112110602030300000c150300744a080481c042c1d9000c0d0294002c0c95441014160070340400307125080103040c2040140040000360000501c403800b030001b40b4076601c0c280c1943c0d06e4141c1c0d02548400720940c100e01581c00c210b0fa03202c040a4454101d42826034009808540302030074510510205e9104501c00c1c1c640e102c00c001aa0240402003400400c12415996100c0e4003e10a9a407401c1e096080e40d15802d010942d2420706040c40107940d4070003071400c14140103106001d0141c0c0c000a20103180036455900c07074100000c101c0100c3d03e01642e8000b140041b49801c800340c0520240d030f0700162043c01100c002000c4044040000c0f02c1620466180940d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 55674293 1250 55673043 55673077
    0xa0201090b070219080a02030c0111030a030203060609030607050d0f0615120f0f020a1101060b0f0a0302090904120e011806110307050d080f010f051005030402040f0e0105010f080102 80
    0x412403103480040c0c40c8083c00a0138070420151a010340551541e01900550199805241c0400c11441d0420640c29184004c0c60081c6080107803000b56603490041c0c007140b0301850707004000681c0e55181c40ac25604842170003000c880742803c0000d00640507910950244031714508104040c40c800f20140200390841b1b032151098098001e11001c12948801c180c00081038070354603185112503c081134001e51039504090880140d4a82d5001809081601542d908400690400710100169071100007680e1442c0d1244220343d555070700000040b0020310070801c8040d440b02403c0140000d104800640860403101a120403449811078401036400040140d1040d0783e51761082001d200f100e01c130300040044400600304a90520030079a0310303503040808081c000e4000400c02002c02c1800c2d200e074001a8014120780c40e03c800480c0c10000800c174000600d45030301b02800800030115085442c1c55100700d01007400541c0410040070410b08083c040e24083c46000ea035002d480c88042131809061003152480071182803e09 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 55675543 1250 55674293 55674299
    0x106090e10030312020d1a030d11120702030a080a05030103150b0904151503140c0607030f080601050909040f050f0c0105070f05071701060f060f022e0906020304050f0a020109 77
    0x913070b60b10b16a00040c120075004c0c8000340c0076407818080c070840c050384049203450708003218003414503005a10450504020071038108070601140490042e00340b446410200d036a0b004c143c004685800c0c04031000412103840011500581640040518142c0c1d1103505c042e210020b1710301c04601a5107a4507800c983c0461910003040000fa41030400c0348426111441c0420800151040d40043c50210f920580b083d03c2d031818a01803101c0140301c051200101124110b003803101c0358a000307050002d1202500c041c0411680801c041d40c1c05901a13034110a00180300c50b08501d82072418013402c119004044800b0303c64081500c2031020003040b005001c2d83c3c180d40d480d00f03056258941036041010180291428090a14042140302000e082c40c80e641d20108008504540341c490680c81c2e0210035031040003084946c80e89003000e1540860682006100c0d000340d0209003c4100c40c114000a00340c0080d0041c038034100b040c504200140d000746104602490641c0d0b10b040c28542c1403500c0e81c0003c0d5001740098201301040c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 55676793 1250 55675543 55675547
    0xb0a030809090a0e010f0b0907020601060801060c0501140108010c0215010b07060515030a050303100509060904081b1c020111030907030305030a090507060e0306090a0b0604090807020d03080106090e100303 90
    0x15540f1429000003c5080c1c07124650080c21a880381d003c2c000340c140c48000c8214581000501c607a00403086100804030f07585045001000c0e5030040c0a4081001804101c030014031800b5008101544191092111623580d1034503110300800c10880c0900c0903000300c8038808035082d54040038504075041c1c48411840d004981e03950400422006206154202d4101c07804440b9403001c02c034001d03180d8401c0300250b6590070504099800d04545030700c59489a031214040001c20340303440c0c03101f942250f0b00c0110f10340c0722503100c100101040038140c901c4030540b00392203078483e040105030f06086c000700850300204444e205550000445100452b007280c202d0348001c40800009200f00c00456000c0c1c880000020042c00d140d41b000c0c200003d69104000064132041c1d0800b59203414840c040c3c10504101c001c04400d0480d40c2c0b054441c000c0101514855aa604150f105200442c82280d00711a0300414507582d501c8285000381000b8828028480051030b14440410210b503511005406007581c2846080c40511350394007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 55678043 1250 55676793 55676809
    0x608030a030b060c0102181903150e01140a2007051c170a06050406060201020315010e01020f03040e07030506010c03021b0f040504050a051c08010506030711031204060b0a030809 78
    0x25500000100319100d0a044c0031300c050880300584510041c40850418108111451003108407207512525a1003000055a03403507001840c4d0b0800c1d440410015054009a80144440228010303042e03825410407043c02001d6101e00d14891040004456141c014900c2e00114050040001e0441d44a40c1745144610682c07000a0f050110301d140c40341040b050188040301c007041c01d9501d500c140d03031208000c0c0424503145c01803901400082c40214118909184221488480411070302d05001c1e0004100142da4800c2c031039a000040c035041140e945568032075842d07030303c1003088515400181c03800d404a12590711805024003015003607170040150004a09500800000703c541c0c040e0702c44203e441da00d02a45860052512540c02800581485850343c03c0c035500b000d02101d2800b2542c08018801000250000d400c141512400e8950a880f5940d8000c00d4407000b200010240044c0b10205094624140b207a20991040344199800d2000700178040070300042001d240002003c68000f448502100e00340041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 55679293 1250 55678043 55678061
    0x1202120d0e16030303060501142511040908090307170d120b0d1103100605060403080c0109020a0e010f060903030801140102070e09100b0904080708030c0d0c0e03060a0608030a03 78
    0x309482c0c140003101c1c0000382d54415a0f000f10042512000100042d6030404403a280c0051800c83c2c6615050346030600d002110a130480340290086251202010b0050b020343c10b451072200a01b041042e80f510342083d0000340c20251603184644038004000c00d40801032001b03503800f400000000d00ca01418118161410301038442c405126030795401d8002c1c030760340d0346100412955010303000a680c0e00050b082854100001c0400b16961241440030030040c6440722421039003100d41245074140c444c01240c2a65015044258000e0741c07100034420041042170044401e24100c410921110a9840d51000c05580d64000c51002401280c0048010000020b090303181028102052054844103511441180362400303050320b00010661101c0e10f1030340031450138400c508001c202194045000d10301591030003064410580014441d000200100e00701c45030901c2600e802c0b00001c0410b000c1c88140d520020404045c03101014442d101e8175001c283c003d500e5100b03c0303041c1d611002c0590702e0013020341070680c003030981d0107 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 55680543 1250 55679293 55679321
    0x109050c010c110d03090806060108060f060901020a1a190b0603010501030e0f16080d0e03030a0c020a1203020607030c11060f06010207030516050a15080415020c06131202120d 77
    0x140d0f41001e60354680c2040c500301e200b0340700c040c90b1900b0064603503c0d29400400080c14031420806000c66503440e007841d445510021201c03580d650112100407420001440c5000345a03071860030300a00c140b106c4036402c0384144030455644c2e00c140449100783d01510030115101c0d8000d0810401400342c1d52094020864071250b0b6003c440c4101203640c115454504c0100300c051039500070f90000e21054105008200401c901454910600004000003d44074800c1104810038408006c242004540f242801f60b40107003088403851040c407095080c081c0d200d440c204c03000d00001c1d2034641d5001c0518081c809043d0b0082c0d54200401050f907031685024036410000c1c3c4a981988660340d0000001601041207d132150a110200e02d20350f07180205011000445400c011000121203002e1558998015402d40e80107802c421500d02c808503202000b4024421178908404a0050004015140b1402c106003c0c1c0b079407107001070b0a05041001700880c2c4902c649c807000e4030801c200700000080b551440c0c020316040c007885 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 55681793 1250 55680543 55680563
    0x504031a060f18010302042d181a01030203060a060b031504020904020d0603050c04110f0703031401062001050907050f0406090e150106090b0409020d0f021303020f030109050c010c 79
    0xc00c00080021080781d4814030f0f160300c584018000c50401c0d00401c5807000c429000112000c0c4110041c0e400e04a4002506641da565550b4014010030407140264800340c001e540c1d02c40c1919503044442d40510f090100741c0c002d00c40c0d003020a504c03440501c14101114100100d6a046850702c0d0308610f640d01c040c24000b903102e5000d0100b0240e076a114401801045500036001446d07a18510b0198101240388405510462070080c10040c62040c0e101103a0000108080403aa1800c0d00c1ca425401001003c1203003c013004208000301c0d00a8000c0b038a6070f12084103500600c1580c07195440b19090790022180b07400f80d504100c4041089040c05180050100c41c01040807074215290442c207012202540395817441c5a1009d683c100304000f0490300c841c00f400031450602020760900c9441c55151140740700b0703070140e60740c0042c010843c1c80495000005080f503900d019541c0e010f90f0300503004036400d64003040c1c2c03080000c1c0d00b1a03440c1746014440c80f0b2500368007038081c0c8071070b10b8140e005480c85610000181d40e0b4001c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 55683043 1250 55681793 55681819
    0x8010b0316060c11130902130c020a0215040806150102010f0e030406050f0904020d020a0f050405010f0804080c100e0705061303020607020d0804060c030908010504030206010b03090712080405030d0504031a06 91
    0x1904d182c589450fa0083e800104c46811f4010041107030903680109002d02c3c9840560380c4c00a80c0410803c3c81c41d5015900b0541c010000c60701021710340304da50302c0340c0014007443c418030070aa0100000c600850101b40d00038017400301d540f02100100c401c03c0b1280d1030380c0c1d40304020420034680a14007404142404410503800d10f88590f000c10166840307608000201540040e4068445400ca1602d004114030344c40d043d81013904007400a00540100c1003d2401e001c003100014003000224400c40c0c0c0991034400c01c0c2c07401d0070300c40c0101c403016080c12811200d00d03004000d0301040d035050960985040b6000341640c82c5150345980c0a01001d0342c01003500341c2c0c000314038141300c001081c0c1d110024001800c0c56035496044800a00340142490600d40100309564180400c2c0004260300250550540303222075481c50741c0303846401005180c02c410f6800840c92120740d0200c0402c6c48a0740e00035008540090f0103032500700c4141c050450301031160b804001d0803103c108070f6007060441e51061403644528080c010981d4010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 55684293 1250 55683043 55683049
    0x10203070906051c0c1b0605060312041413090f1208060d0b0a090203070803030f191a040b040f0c05040e010b04050306070c03020705060d020d060501091a1602100908010b0316060c11 80
    0x780c2c0301503447e02e40380c0c0d0a10201342010001d942d00c80302c2d01003400e030400303080140c10340d0700e1135158005901c03480d00030052100200c034907841790700c1031503005001054540b01454114842c1c40d0049040c1d010400000000b0081e041101d042c10391603074440c1104000e99108040344e07008104000d810380c1c0600ca0f81da00811307034002c1040114003514400030008610715014103858015603d08210f0742c442400c04401c00c46150300301414043d840000c07207000c50480c1c000008500188218039144c60500d040c07408081290b50044014403d4a240710108295603032503001c400b625104910500c9c0d015403001e000a40480c1c424400207004070312074419608050780d03880c009109504800e43c1d140c1c0c40c0d9400640c1003001d034402d1003007d0040c002070810002036442e180c084104103030b8003405104081c000080c1c001503001c560110325051540203101e20036400c84448000c042d200140140c0c1010340c070b09190703080540742c000741c0004101005d0420305110360a102003211605280e180440d0800a0001114502d40d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 55685543 1250 55684293 55684337
    0xc092c07080a050a0219030506040902061603031b0c0212070306020a081906080c01200601031b0f0503030702040c0302090a061e03020f0304020603130501050702010203070906051c0c 80
    0x100ca903944000900308000c45500720399000d01005199441000b0800c0504050321a00000340618100080e25640d19008034018040c40c1c140254464030005499050301010702845100c0c1e0301a540400c17140140d00306003169400300e52030100204208046400040c9094900c1d6144044000107440c0800da036903130b45500743c1e0003002800c4041415002089001c06154070548100d40c924641480040d1400c0c0c00d451303c0e0051890258100600d140001441200300c180b90b10a90b0a82c1044907890340c0d40b410188400c40038040d180b1040c01c00c0c0c240c00503aa03020440444d0907214018091407404100d98200002090b0345200c1c43c05054003072010021b266503112248000b014107868402c000c0b042511444035400c2c00c050712406052041c810924004001d44c20f603507200e98103440d41560b946500390030015280b401800144650b00300010450303503947c1034014500582880d00c5210202d500d910042d00c2d18001d99160341c51000601c010080d480185402500b40d400040c103004c1c6c4081c40640e000c840320 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 55686793 1250 55685543 55685551
    0x70506031e10030b0a0c080109020f0f0412030305010503210a030e0105150103060f1206150e0705040806060d1a1b040303020313090b0d030c030219050a12030c092c 72
    0x1054041c42d04100748095107110b80e0388035045060800904c0702c0b469002d004194180288034159a011610240390700080044032407180c21144090b44441e910180c3c40002c00381824120700003400c0200009440c100010300075540c00d100406140e10441c82644043c4ca6081811101c042584840940100200a1042c1c03402041e0300542e84220b004201d0000d015103280d03034070501e002c0700700c00400c0004982c103070b400c0c2d12441e174400808221025036116a41c022a940e82001c4110744040e410f100c03566407c4001042102c08960945031070341e039070100f0000345100034000a80f01c8014001150403881040420603402022810805144542100c4044243d080fa40084015034000666070410351110100c0e000180750302d9600303014081d10b0303001041d00044080c5d80207007402502e83c0b2501c00c240c000d000344030929403200d5a682c0400300c00c0c11310540d80e059200050320350000062151282d127109004151080441d034a501a034185409044807202152010389180368110780b45800081c803c649085000e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 55688043 1250 55686793 55686811
    0xe010c06020d0506090f010f03020f0a090c02031e0901080105090a0f02270a0501020a030c06060b1801030c02060f0c0a120e03041d07021b1309030302030a0b0d0203070506031e 77
    0x115181440900032400000341c03a081c441b200c801c00402c90710360070200c24815242d0590380c00e8145240c031000325818032010303040040c42505003224188250740c00000b80c50300e114500c240c60907866100b009040c25110f1061120300060f02a001032000b0704000c807499130889800c500008030354004d0f8281070200e0708a0102ca00315840b034552000941c46d03000f50101032a8200f2100c05003018501000030755500a461802024042051800001d000c1c0702d9011700000d02100c01c00303d03620304d600b00c09914048507040515010070724102c000c0e0711407032000a900348178201c0b04810842545403d1110141070300100098001c0000c00c00b40401405803078010703103913008180c100035902c490603d4140ea0300c2c0c0402c001401e110300e05400070004155400690300140c80c5c20a015400c11034100d102044540580c4002d0f010b40c281007044890816915500442c41210104001c2040b20796810402003d00744626000c0e41c96801180284803d252070002950080c04d40c801203003120081d661107415500080720f0700e080d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 55689293 1250 55688043 55688051
    0x80703060509130204090c031b090c0201020c120c0c0a0b28050d051312020d0206060103060b040b090d0209131101050c030d0908040b07060e0f0309010207060e010c06020d 75
    0x650580222005450102c2c0c281c481031428440c01c0410360070540000c0e128944940000b824403c0d04500d890103180c020b0944501c400150303270b00010328115440703080c01d480d10300310003511014410f00c02c0c2c1c0c8400380302c038004d44030059800e05415000d401840b0035030041d004c4e0754203100d2030f550b4404207a001000060b2105071038080c1081d628084912000e0fa0403401c50260b00c0c64240da9521104031084c120107440002600c0d01d42c81d0421003e1a69404003d007980318070004803041d02c0d00000c580384141c0843d400c90f107080e5030b10340044040e030707045108800042c00c06002c14408404403030060304001d0000b90226000070030640000d625400c05903403038451003401c0c0c0f80500901840e0008403203404420b00341b103032421000f003985640c0c82c03050440c10708101c0e980351030503400c02c46108100c0e070051403110340594032210305007803ca0017807200309103440c441d10401251940960010090b280b8010058014111040c0b9003d016103000c0c040602290402c40302c035039070100084540c400b5100c902001c0b10001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 55690543 1250 55689293 55689301
    0xb0d0b0307050103021207052503120507140a03050c090a030c0e010509040314130308031602060907080d120b04060308030406050f0103050c0103020f1306080403090b040b03280c08 79
    0x60400040b03410050406004204040c108102c0608140d000b184500e0450380d40c0c2149807400522010450301c031000d0502588606040c590310849a80c01005c08610030040c0362190002551501d62815840e40b00100c18469020094020362106a102c842c04c0f03a01403034a0340b0701d00020880a01604210b8074442c072018240b01040045100901401007520342e42118200760f00c1c09041545480d004510b5014001000400400e035a403080d8011079000110a807170341407014211100c940782c0c0e900013005110b040002190720b940041d054045036030741400340103a00c1424004a50240e03100d2441030590707498000769403140d2514800c000c015400340100903200c0c06c0c289814401d464000d03055100002407900140b000c144046a49102000700b42001683e4965000ca44211402012101c100c5e003e020800026103036000074080c0d225501c20340e50264103545030300d00d060301801140100380c0c08800030300c001480f0115001403c820140341080c507038905040b09284506583c8606542c400084001c0140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 55691793 1250 55690543 55690549
    0x9050a050303100f06050403080c210306040c02011a09132a0501080412030c0207050a03121e0c02010e060c0105101401030903020c04090807020a090204080d0503010509041b0b0d0b 79
    0x5480000c0c4c000d640300b45482c600030441c1c00341e400040d2101500181344209400200301c42c00e02d0910340340405a803c41e0341c90304070701035130030485031180100c0c01c0900481e0f84a106126842d5100380c400c08406041050000340071702194003c0805c00040b984106c01800301d282495144140c40d4100016600140c04642c06c03841e00070b165001606100d11002400005001c0f071564810022203072030001035440c0c1d0742c6012840c140c0d140c0e0200380c0052000700044140304010540751442c81e219240c58045100544035807100320032041c0700070001001c1e540e4120041d0b00c102618040c1d2240201800c0c248580881c0c03aa00311501610b140300d4004020b002040148181f80b102c41d03601c04242410401141075403000707501c0c1c0680321581e6105550703c0610008000030107095804040c2c010b0701107206191543d1207000250310a0254101500c5407118511013188118216816108003400d8050281c80b15627070205c00102240305c1c20b17144446c0072004940c0e1034000000e000c1b189080603021680c03030921424 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 55693043 1250 55691793 55691821
    0xd0b0a1e0c0f080903090406060e12060106140906191101140105010212030c13080a200f1201091506140301061a0309010b09040605040b060f010906050a0309050a050303 74
    0x84018041c200900c60106a400400c01002c0500301d0800c1a0301c3e944001e1140e0442c4074900125030301a14004001c03401540c49084643c14040c1030361170403400308102440540d5544248a150009091100b4100c680c010713040280240000241030542000d00520003903621107484480103000811450000103035240074003550343c460800c04000300c403030b5041c800003d441d207202e07585510811100202040382071281d8021030f82c05840860349103076405c0d11450142d444a6060105844200f0502401703220100c2604212030082c0c00241250446500401801004050b010455046568940001002c60000c0c242c0c40f5024801a000003103980c01d003034402100c4606d044039140079038540b03070003070044550100b040d60705440540c200e940c49a031281001409488172803280354020b04020300740420400260000c0d8001c3d8816030711f51840366a183c052201c440d4080c001c41d40026214a4100320050050004106101c0c261030f000c0b8240c0301c5502c9280c6403100d0418100c2c3d250740004200540c01e070304421 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 55694293 1250 55693043 55693091
    0xa0218061318020315040605010f030b01090503030309011407030b0a171009080a0215060a14121005070801080f0a02090c130b0304051216030f0306080607020f0106150804110d0b0a 79
    0x1b40c00c00c480c6041c400001c0500305c46040741028035903145030940181c5c1c001c4c41020001c00001b402c49030790b441c00c138400f10702038460300c40110102225400840c00040c0203000300300608401900500c41103141c5040c24050400e4001e401000340140c0e0084c50300180d0030700030708155901406801d95030304001e400081c90700100350102e40ca102006030500c91150303122102c0301e040b10000811540c080c1150340c005502088030303540110340c600c210311000c1766091481e089540f14510b162108002c6a9a071403c413500d82c0c0700c04c0414412600702e40001001494009003050308001a0708440b030a02602e034080d1070398203080790000000d07a0740102c20030003005420083d00c1d0554000c2d5028608265007174800410045000300c0c01424445c0740140062054400e0303012000401440088941c2414042806512802090141b285a500709003004c9001c44d4100d00e00b01c0041607c1d070b146211540e46071600e0400701c0040b00440d510800c0c01c00c080c0041011000d10900a2200e28400150300300744449005010000780 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 55695543 1250 55694293 55694299
    0xd021308100213030b0403020f0a0b0702010c080f07110c030f0604050106050a0e04080d020d061202010908030a020c01140903010603030210060806130f02010903020406120b0a0218061318020315 85
    0x245202c04101540040b030354440d14400c00c5e5101c42c40c00f42e08003070083c02910310a21031142440140b1149100150140030160020444604120401c42d1900c1d000c0f40d055510f5180503010614507442010154043c0c6003100030b45140348241c1c00000e0520304100541556940007000344024030000303101d01001040c0c21507168000c0703481d240048624000050015001c5240803e007614182c5a50301104c0c007200301400c003042440d48440740c060206034a400e00307a0000f1141c00003c01d2111001081740c0c0c60b0801e5070001c00402800800440f20b030800d10300c0b016025a402c0c041c19206450900800010b144641c001e400400741200400c411215a070788846a254412001c0c44a458101200c00d6040c0341c0148030203032072841a0005a907000c1d0b03507900c020b4009152400004080102001c0101c00720707c82c41c145c0712241c0355201030900303a024031140b4255012503010601fa003803800000404a10000341c0c3c60244050765410002c1c150f910f500d80381d41d003042e000002c00003188006110013050240407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 55696793 1250 55695543 55695547
    0x90207140c0d02010f0e04051806060f010e040903020c030709050108190b22020a03060b0f010206010e070c02130e0a021309030804020f060d02160b180604080703050d0213081002 78
    0x1c40c000a5940402e8203010381032208200090300803a01c580400e4151080103001404242810858031080e4162551100c01a01030140071800500d040c000b195008a8160340e01c01c00540d03141e00b04001010544021000d5120b002602407150718184046070040080980005856140c00303c41c5040c107107000403090008201f038042800190070100540d400501000316010f0f02d809007081422422407824000e540044182000010480c3d07076001121008001c0c0d138884103585140c401607075103050a0051200c2e0542000c00035071500c6c4110100d04007a0300043c00650395801d480c12110444841c01121841c0344c106080c1c071019418103600c00010315054500401510701d05840003880120301a100a120341c1d01c41c00301382d03400e44d11031044d0f40d020015180215031310207003081e6051044042200032074014603590700041d19404440701c8080d50740030030313805001e040e6980e03600e0030116440740c58105c0034080c041c030a0600c501075510150020144034900300d4122400c2c805050700e070052407040501c4e62401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 55698043 1250 55696793 55696813
    0x402100f08070e0604051c2913080f190e0126100503030408100e1c030908070c080604060f0e0a0609080403020603040804030b221401060803030109020714 68
    0xc0020311a030b0110107440c1c001d4410501c600000da02e4070071584801d42c0014161800c185020056500380c00c3c3c5031080c0104a10181000100070959011100c0c00110000060025910b80615602c010001c3e1203041118070742980600313070280b01d03017200707a035060000071880d500d007072054000c8443c00700c00c14242400c03100500f2540c15840883c2049000251054000e40070602070007140b40203002a1000a05503615141c540704075070340c1d0350314100e11032111900707101503485006804594042581031841000d80e0010080c40141c2c007400446608079848481080400040350800c03a0580140801001500c4141020b0038200151000014416603051a184140758a90720000d05811103c0e441403010400b0031082c10302d9170990055070300180d0070900010401041007000b0300100140d03840350508144a0312010255600301c00407900080049440e40c442c000450a034201111115180900100701e403a154418581150020f070700c03200c6403a80104036081041180014450000310340300080c00d5400b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 55699293 1250 55698043 55698047
    0x12090206031501171801050a020c03030105010f0512010e070809010c1e1101060603050601120204030c05060d090f150606020c03060c2104030c02040f020306011413030203010908030402100f 83
    0x200c09005010072560b003102400c99a4015501a07013500e50703400201c5601d2514090b0603514038040f8800c1c2566501e0040010700c5400617101b036401d41415a07004608603801d001c010b42d030480507051803d0601c80180218a590111000d20034080d110303404021505003001d101c013074162500507101085030f07418025241d40326903016080692500002c80c3c41c4038418960b0340140e0704075080403500710095081103000308440e034050300203600482e0300f80d90b40b90020001d80352580c00c90056000040454082c560300300464134100001c4c021101500c1400996040c0f0741da6a04400d60000004840c3c021014050303440914680c0706200040c511030010741081000a00040d0311150b00070048030070f400000c910020b20f40340d003c0035038000d2014030f001155542040d00340544800701d1003008034865420616110781c418624000e40c0d00a01041c0c454800703100203240320100e1030300110b281042d40041c0b00700000140e81c0034040c1a440e13600521405540341001d005010040d4074900c400014891071f040c861011075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 55700543 1250 55699293 55699297
    0x6060702030c012303040b0f010f030b07050f0904020d0b040e010c08010504020d06030f0c0302131802010e190f03060c080403080420150c0607020c030c01140717030712090206 77
    0x540c01340b0700311112001d00c00d0710300204045802c241c50301e12000310070132040080191085014014044141180307a0b684e0a582601d10103500000309612000808503000501900191036202903441400341000c6858012070304a07041a012b1081154403805486010f04013481030081148143c1c00074840b049540d000609480c906200c0d8134010340e80000c0a402e0740c0803e9010ac00907541c0860100c460b0841d0b810001048021030105910650030710310880b201c8849032050151120105c09084c25092280c0c005642403000d181e8a61b410899a110051281e00c10020441c041c000e001d00d5444014154240282260b00312248001849684010701c00070179001030803181c2c400d6215540c600b602603210300d00c1c0b90050803400303100d40080010300c5000c9441c05540140a41d2051601200c106a4034820308994902c80e2100254054010812248407544180f0341c0c43c40691144d81d245140019540da0304a02c520b1100c00049141c1020040c000c04a90100c441d00c1c44030f155031820300650486400046181c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 55701793 1250 55700543 55700563
    0x1c180911090f2103030103030809060412050d0e030a0f0314010311090405030c0d050306030c0102011413060b09010602030a090b0a1709010b12010e120304051002160615030201080606070203 83
    0x80e1401003401d16641e9815043d002e00b048112220025035400c03a43d4996640c000380400c0b00800c04075400a44d42110000b5600e00ca541c0100b40c19500d04041c80c01078500b503204411360b48480341c075100910310003001000104010001981c5051416151075401021696131041780c882d5030643c0001000441ca00d494554048502141c0c40c085070f844500c1e0191079032140104a02040c00340c9e070956102c103a00a00954803804090b4181c075010400480124201c4104002100c05105201c2c04100300410304094201054400c0c540082d0001039800020301c032407400da01110050380700145001e4020340c8105450000c0005604244c1001c1140b000a00107280004014510303030107100000701395441c01d4000408401d005440b02000460300750b40103000c1d010ba02e04580491007203001d4000300b00161000c0300e1007103401202402000d201000a10080d5010800d03032a80004200242e00100300c2e17600c1001d0300901c1c8001c08824080c610b100240c95204000c1031325214031424011a80540c40200340d030200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 55703043 1250 55701793 55701799
    0x80601060f09080109061401050f0904030e01030902030105010b03010302181302040207020a05090f010801060609030506130204141602060c0306010507020d080d0e0105040c080a0201050406111c18091109 89
    0x30344481c801d01100c12080300c0d804035000f9820b003000c90007401010360000d01c2c40170003000d05d00da41d40e0300d500901c4120080003aa507a04409054001008030344203031013420b104101450302043c0c00d611130300000d0a5a100380c1000c01c0d1018008010411031600704c4d03860540051075038002c00d0614003d00911b81c00c4030a2040a4040c40d0000703102021542c2e5594403501803c0010640b860780c0c104400d0419030034109005a08556185c0341000c902d05008074040b0003101e03401700085c903040d920642028200c5440c03107012a001500e848007040f20003e0400030b03510500003841c901c0d40d807001e0b00070b0003484c100000d0032503009180c1c208207000c0300781da002c41114002a010350b004000a51305140c400407911922003101840d500d8109100800c00040d04001d024901454510031440c0c1c07a490740540f1595002130003404a4002c03c07080011383d000b0456000c003e005401074501807134a864000405400d0070b9400c00002d802d50b000d11040c800403d84040142411080810804680e00307200005032068010f9184 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 55704293 1250 55703043 55703057
    0xe15030a030c170f19030e030a030b03070806041a0f0103020907051e190305090c0120010204081006060813052104090f090203060a1413020303070609030e010210020408060106 77
    0x18404000c08203030b0380400c022583d40e0b640c004005103c1d45034010b41889941c00d40e0342c0c6030341d20b4a0ba1281c01030008002d01c0b400650310744081000290000d200c00001c03660103001d4603d000070703070300d0003806040e1096024160350100c10128030580c441d00400241000603008641c4010b2001d82c48040c42142e0200e498204140d070380420010b5404041100d5428050845001500a05e0410680c0c20000314120780e80f401e1044d0340302e213505942c4404200d841503000840400018070741441502c211008030700c280000616150b240d400a60030003100001d0f1062003500c5080c2080643e500c040f10b150300415031100000c000c0800d6039081c2e25006200e05681d281602d0f008121101c28a80040b1002016440410040850030b804c080c40036203420303081a4840c0c00b8070750009150304041e014070900e5012503140c01d40696140c000d001c000c190421820380c2c16110a02c90f041c0025840c1c4164101c0902a07100c0108401e040c900081c40c1c4056031824a000742c3c0184000c002440340011554191100c40c10718003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 55705543 1250 55704293 55704317
    0x30207030509030d0225050d1b0812120106030903120e16090501030320150c0409020d0506150c030711011803110108060103180b0403030b0303040806010e15030a03 72
    0x32402e00800e20b41070380c03602032018041c2c50300d034000421541021403101505900044020714002e1800140300b00c42d00003110030583e80c005951651100000c0310440c00e81a0820744507407503545801e61b80d84031100f8000e400100480d400188503801ca0041034140317418000d203200e660f00244080c182d150a1220191074000c1c0400b03500040c0090121003580c150b90888156442c803143e00602003e100950104500d11112800c0b0740c03083c110607040c0c7c001c200c01080e0011010911f0660110020000c50041200f84408103003001140018408264118808269400c0500800400c1c02030f41080701e941e0345003001044070442c40801505d44194020b42c44d241c001d03008100503549040d01d543c003551000142200031013000141c0c1347c00d180c1e81b203003a130707070503d6036501c0034019402c0340c00c91002d02e54510344401d620000203180400d0645d01c28440c1c51f0205142111801003880c640068211042c50b8010702c0c01405180c0700c040549034080001460303210848410030110f0f446000f122006401c10200c0c614036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 55706793 1250 55705543 55705547
    0x140c070b101208070b010f030b1b041703070201020606190b0c030408010e030d0c08041a0a060503010c03020418050c0a0507110a1409070f02031c090b070503180601030507050103020703 81
    0x400610500c03240341201c2e1040d2a10310441d40c8805402c4510030003880c00452112a016142d4003900c4c1d02c041c02074170700d441e01c0710710740d00220703145600005158017044003240240f689440190804040c3c0d000790313204c90b418030003e400d20034000e1405010b05412800b081d100c00f451104201100c10900c0780d40d5a5101caa03d015040d4496500301100942c20b01d01d600c507078008000700402d02020b940300300b08100d81c500e28044038542010b0320003a11501c140316241112103100340506030808920080001c0c140c0c1e41350080b0b401c0d18202d024610110358046010405440710055003031a01d2a1300104101d40e141c401d90002c0940250302c12780c0208032012620408001c042c5501c0724101d00c00a00d0842e005a44030001091128600c100741d011315014400300d0b0445005102d400500f1003581c015504044241c034000301011140c102c03840b1040e0301c4410240100b98002c0600d405900c196440d50340c0e901d0301113042540342b03e50340f543e04007550242004001103400420040107462003481c0260366207400e4101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 55708043 1250 55706793 55706821
    0x5090a050315100605030c03042a03080307020106050906030a1122150e0601020a030806030a021e03071a071b0302100903030201050612120901050c0f0102040306140c070b 75
    0x215a801d4031035090148001c80c01c20240910403c1280c0d5120100c0d921070754219520701099030040c0202d41c051012400103144030305200fa400402060700c20002943c182c00e03003102d0350380783d00a882c40d03940002400485607083c080d040150409031046500c40c02e019000c2a45d40c0d00c6200013428241051100c1708903580e5030580d040094128501d50300e003007082c580d48100103081e031401c6480041d05070000050f00200c2d0101f103601c0343d84160060311581c4460780301030700e01000003000079070b15008100070301c40141c2e50010444030b00a940d18408600e02c03140002d040c5006600d4002e0034807603120301d9404904a0417002151055507102c50303c2e00c180864402e0340721308203034141c00082d030041c041000382009682c0440b068080f01c1c0a50700074405502c0303250600c05c110500c406581410307008000015051b00080380140400079040c98032501e48903030080346c81c4c20005502d001040c1c076500001c0030010301c0314034010780494190f0030201505c641080c02e00e550320781c4100b01d8000c00c0d40d50503000054105890b126 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 55709293 1250 55708043 55708049
    0x6010314130305130609060207060905010509091009090b0f01080307050d0e040b060c010b041508330708010806090d05040e18010510030c0803070804060c1b0312020d0e010503010605090a 82
    0x15100c021301e440c2c4501030b2070040c0c0e5004000040c468820006401d074030900143e070031580c0684035585024481e90034495404c0c4001e044000c24030158030002244425845030b61403041c0644101d600a0404024800d8100010381c04a4510392041c072261000c50004502645040a42e0802c2080c4200f0107000c680a41941240c02c5d0f805031012405144d10300d010341184910b14000c0364100300680c00c880848a00b103400c2d00601903a43e00454015041c2649800703204003000703202c0d41d07032803000540500d00c01c004c40c01115840001889003004002c4088200155030b003003008440038205400c20740b0750050030380c013861080281003070400020461410a202d0450400003000000f40103519020b0301080d000101444102d5401c25501e0300015a43d2001c030959401607030060700d02d40b4107480d101c030482d200b10203031900350764561910202540f0440c0c05054680114032034a161295406d800702e0107403e010840351b0103c14007440c00c445080503a8400b080342e040d6240c50030074a45400e0444003154032080f484d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 55710543 1250 55709293 55709317
    0xc03030708040326071b080a03020d09060905010b0a06030b091b07171b0f060601030b1206010305010603060b270903130b250302030306010516080703120506010314130305 75
    0x580240c2c51300da441c1c0b003900c1001140c64009a29480382c4100c01c80350741c08071000c2e086400600c4070319521031107500105040c0075810004521000c00351612022507120040488590395541161038080c1492030000000b00401c0c01c0c1080000089408100c10501c0100f4001d5400d00c0100002c00d01d95942c0c041d656165040440c8266001003040101c1e02079104010100d11100c84021800d4025000180302c86400403e00203010561035000c0150080c102d0801115402406019184401d00c0b040103003e001394020380020031401c0ca1420054105c03110012481d004403003005d9440101014100c9a00300031188400540c141c0c0c0c3d946003174a080d405400500305c0d0180c0c44450011365003038668054070003c2c0641059001c205000100718035007400c8103800501580003440018060360151000e80003868980d00c4004043c610342c2d40d000c903036a11210044002c5202c4d01c0600354003540311b2007580d9000c239003800c042114118010401a07084001030200220000a08480d410540702d4000c0d502441c0c030350 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 55711793 1250 55710543 55710587
    0x30c0302100c0b10030b011a0708030702010b181e04020d02010e060c07300c0e09100c08040b150a050409140106031203050c09010507060207020d0c0906080f030c030307080403 77
    0x10700560302600b01c00340b20a42d10008146d00208031205644400040081240081e5240540559414103907400c01480d103070940d56520301c00d01d0030b925003601c01078500b181c0c0c0c8110392051500c58ac07000141d500c42ca422035407041c0394401b000010b81b20380390031010040e024202000703087e0100c400911a4880d0300c8c0d000c082c50080e842c0020f41a100c1c201e02202d00e0082403003243c0740c02d80b40d00d09204050b070b0125004d040c000b000c1071b040003182c03007000e4401d804c04031500548a000300311081001c03e645a200001c80080c50407001c20080c00048580c0d55040091071801c0300039020000b000400103c2c1030b0040c03c0c1b15968801030303242084114086100c2c00d4a40700000d2003182c1c1c1d64108a0003465051146c000402d00b0240003481d5080c00c070044410b03400c0161141410221030343c5030341c0003d4001c000100e8000000009000206184030003110051048110208116090110003420182c44800032a400da20511002c5150030300441034a42c000604d141c61a0180e903075060407540001c2c036000079182c80200d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 55713043 1250 55711793 55711801
    0x10c02190206090328050106050607050613030504030c0b04090b03010b03030f0a0504030210210504020d0f0503070b250503040f06021606020f07060614030606010f0e03030c0c090105010504030c0302100c0b 90
    0x904015042486c0104000c019541c4d44509115480c8102900181160462800030300000c00900101101c240285425070078562683d0392605d070150302c2e0308a011f1062000c04c0c1040300c10200d014000070888164001d00c03080001402203035076800780380318500e9600f0002c0355824145204da010b484c000c50b0010803010700310451003005064903003807851404c000781d070b20400026168614021503000301e81c040c010b44a4020f00b40c540c0d000c1c0340114002161103000070020311011503c500002400743c00340c070140300c1110071040051880d002c440040c4006018040c010000401e10b446490040c0c0e941100d4056a1500ea508911079410300c6102c00820503071000c80d600d1442c1c18075030040c1442c00d02c600300c10402c00c1c0d1118201960340c03130021600c5d17a25512560004500e0b502c81d58441e94070b0040380c00d0211020140d6000241150041c0210300303c2d03503100f02c01c0700102e031801c10000d500506003804c1107071401e07040d030300d8008040b1002c3c040603026042001c0182c007014820f40c80c175504503820510100360341c10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 55714293 1250 55713043 55713103
    0x18280506100527060c0a050601050111010603050303060603090c0a0303020a030909060509040221070e0f070f021009080909070302030a0605150702010305040218100602010c021902060903 82
    0x240640e09240a118244265a8014040c0045950b01200442403d404507203000051100245845030340340c101c60b06010b0341c0d00800d02000101c0b080c80c4180046d180540c18100010f00070f0b03602c03d03007034155a81442400c001103440030040729003164064a019a40b55241c0104900d000140d103219a0410203a0000006040d4042413044000e0302c21b03a5154062540c0701080b9003031303855900401d94040c0b000d601080c01480c101d24070b840700d80c58200081c44181d031803803c4582003800540c0184103072410b00040210390b01e220304030980d100c0d07001d0800c02011900043c00030341e24250100003094003940e6184070001e00c00707403030181c42031a10000d140958600d040d02004000e50419201c002080381030040c0403803240340c4290440840d180003d106170900d89190011005002c2c0a402660054443d03014120080042070019100364428400c4154207803a01500a0849130804a000c003190042c24214403243c030b070000048509034040340c13459100c2c0940c50020b810030307179601c0110802106107005c01d00b00c46 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 55715543 1250 55714293 55714301
    0x3241f020303160302071101050306010e210606040c0206010605070804080304090606020c09091b130f02030612010504080a031a03060103050c0a0f0311040e0a0f0602040f141828 78
    0x4444243c120803903072032a00103406038010000c000b040d007140207548141c25440f55000d554001c0b014034220b40190728540c0420b00300005030001c0310306021001c01940441c0c01c10855141c0010040c2c8003000481000c010082d25054107000300d400300880010501d0078051010300741d401800f1030905aa0b0350b04d0390340300304038003c18591064a001d4000c01402403002e20349101083d104210040150001040440c03603a00005600070b00740707902c0302c2c48401d11003a014003480380101d4544d40350700041c0c0c0d03030802208029610724100200318180c0c1c105420440065030000540d2089569410086080721220a0650f8080141340c00342d034051003a0400001880000152003151103815209a048503442e0250320420000c40e01025011182100d0100007605069111008000e10003050364041c1d03083d5916001e8200c03850800799040344d0042024000f140c620a03100c80200a031030012a005650400030502c0340700b80c2d60b040c1d0303c2080e1900006910102e40c11907000308003030b0301142d0002e110313042031090010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 55716793 1250 55715543 55715551
    0xe04080c031809090d0f050a02010603050307110f0901080a060515040507121a0307050d0804030206070f060b010509010e040f180503120a09081b0307080f120c03241f020303 76
    0x2030000500030851340b001c00315060411800542d1a02460448104140d82d1540010815002c5668800000000c1034080c0080d003403a030304c01c0c019183c0c2103028000300704840d81c41a81c50392154038401c00420200900080704014140d01801c049041e5aa81c1a44410010b0310052540c1007418101040305584d480441203c070b44180b440c042141015042c42494004000c10340d968041c1d11030306042c041440c1c02e00101c4000740c8a801c0c8a40b82540302c0d4040750840c1c00c658001c03a88441f60a47c2d24003000302e90300400c104d00b00203203001420704910f400001e004101141c0c01500851380c03280c050074950140e800c402e94041e02c41d20b440c151f82003e4a4115680d40c4a104c40311911502c180210f4a1a880c82c015625030b00c0d004441d160030b0000d102204024020354522100f01c9110400c02d4200103440b407005420220610503007207171500309003900b2820300c074002400c04c60109410403c00c070018000d9040e616445028581e0022915070f0ba001044691100d001d0746894490b170b202803013054a5001005501c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 55718043 1250 55716793 55716799
    0x150f081506070501091401020a0e060306030a1e03090b132d06050d0e07060e090a1b0c0201110a0213020a05040305010e0106080d081b0a05090411030109060512070e04080c0318 77
    0x106c55000c440c454201c1c0a190354210029001d03100941140c074060020f1900100010203980a240349030f56000c82215a0710401f442082e032807100e041c103154004124100900310400c1d102e1400000c0c414510b1041224060410481a20801254900b82645991914a42003240e0075900b41d103484019043d5041401c0d980c0005d400e00f03a085810403000309404003280c8a945a2040910300c19040080d030810040640017541d669880034116100601650210841c2c20346958828026a0000424002159188100700d0b4030a0160a00584480ba250201d00500400050711a460654221458800ca81c13001d4415801d284190780701d500c041d4002c108a0354110101c510110a0440c1500c42c140c0454070602c901998900150b880d100707001c0107005290041c682185400e072450005412110341c0006900304c2a400710045c403031400c180c407505d80a031000716800c910f180c00c81e0b800d141e507038100e41c042d02e10210711460205040001640980d4610341101d4192038889414240e070703400d00101020490300c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 55719293 1250 55718043 55718063
    0x5010b03150406030803072d05040609170a0204020906040f030c0906050102150a02031806040b040506090111070f06090c03150c0e06091002031c02030a06150f08150607050109 77
    0x3201e10b4079200300380c11a0b0740502070743c1c115035544001b904e42ca1042105d400d404041d034800c2104215507110180d8010a094842c661540d040550042080f010380d0001c103150520300075103c51441000803000c1c4407035811900982e4450b02040031503414011548030742e51340c60f1171241c04820059003200800560300c0c0207808200c0242c0d51001281e0f10040c0c0c1700100440c000d00c1d0041580081d194006560081102800000707024103500003a1804100b194161903c205240074801001014003070542c00c0039600c4001e01041440c0405030a05d0303c5070380e6008010f01d405903400f504102c0d00350400e89000390000c00d010481c90b40c0f42481c0c04603111000c0c4e04041107242c00f81030081d85000c1e0103000340c2d103007000e400203042400c401c0c10710004e00303034078001c031000d62005000928003080d14100d0082d2407040030a01503100d04201c0001019038200c1d17040a0000250002ba2441072603210452650194107440c1c0b40e60152241c84086d006044a03980c10758009070b0000d400810720038150010942644604040740c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 55720543 1250 55719293 55719331
    0x20a170f0423041e02032205060906070e06040501120e0f0307060e01020412061d030a020307060b0a0602060c0307030e0a0309060e01080f0604020702041e06180603030e0105180405010b03 82
    0x44103c03070101301c44690440140228445030955a8065a8001c041c1d064030144102c043c0c1c1883d1004240200450341540100200802e50308140b00fa5a002a4281840e6045100440c00500e0030b00882c0200e504000d000400703401c040c9007039040808464882d000ba964201c0c0701602e0345440303600c424802c1e1921410705101d00c4012105200301da04407002d40700851000301450360380502a2844c0b50910f0446000619030046041041c40100008031072500103640e40c00c480e107454000d41c0c550441e810b1040c0941750082084540100d5075644c0309609460075030380c81e952500e060340101035908809481d0f2084181e070400301034005480400780e4119840f209601c1c207103c030045030440c2c000c54070103040710001c0c00480c982e4145500a0400c0c18802400413800303403452182640c40350303125484200203a44540c810040030042c0601401d006840c6102030002d541503441c05441107016200300e07410410006900d00c09041c942c541c603040048018024485965210369a40054000741e0707940080e02d82d074518007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 55721793 1250 55720543 55720549
    0x1201080309030703110402070b01090b19050907110a0507030503070308011211120c040f05010603050f0f071b0206070b100504060e0f061207030c03050d0807020a170f0423 75
    0xc1c03140158000d00508070682107903644207540b1082c1c161180c215800340000d500050000e0b9005010301035145001034147c0f408400c2105842907450400410240d000d0180072036151700001513030007030342400d000484550403110309292500240303014045000790540802000001300013084100d02175941c51003940d880d03e540f1101c102601e1002025001c1c0c00118403c14101802002811041c3c1c400356200030100802003400c0c0c4955541d0041000e507103000520120f40c1500c03c0c10742140303074443d40003034903d020300082d2411003000d4602400e00c032034641c440f203d0284152240034103da002d8101d6884507483d20f030080e01d0030b00036100c0c00e0201c000d620000c54541001c0c45104101c5001d5400d2034019144e05402240740140600b400390032402c1e0304800090750001304507600055100d034410681d41031940c1000742c00c000000c00c0c10740400c00c401050145103a40000c03824541c1f9048203881e92501c0e10113488170f400d0b1107000000e503002000030038005121f11004081a1003002a0031180c20055110010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 55723043 1250 55721793 55721797
    0x4050105010e12030c01061e1512090807150b010305090309220902060f0d150518070c021c0b06030a03050a120207060906020306012c0409020f040501080312010803 72
    0x103424005902c00c4910750310380c50080400c00700c050350401502d02e0090a0b0b02503d080d6841b9400091091000156000c41c4500e0302c1c501c54000c10700d1141d1a00045507540000f00b49507054008400e03100e481c0c3e94084c0c1400300081c111207440385d1041c0001e070800120481c0e000034024011000e40824584070008400e8440401100d000c0300b001400507811007000b15400130380c00703180c40209880c035664940ba9030042c0c940000070316014550201c0583c0b11500c01402c402078803050f000c0b240354051040070422154444044007040e41d100b40d80004807075507800c081140c19800710700d0040d5103ca0405404100c02f07005a40d00c1702ca06024103804086035492500785642c60303010110041c0011070401c0461485441100c80088221017410094504041600c518069500802c02540c0c01a80001032046d90740e005068600c1410340c0c00c400c0b90120403040fa10038002c0e01d100705654040c50725504448110341c4e881522076500030307004200f0400b80d41c48001c038958076041404400031032140d160001c0744d00100001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 55724293 1250 55723043 55723049
    0x203130521160501060308030f01030c0b0c0316031b0c0501021002030405030a0f090f08061909030903020f01050702031203090c010203180d032f01060603020909150609220b040501 79
    0x200340b40844503038154001c034030071110982d825561190040000f4043e038000314002e10702007003003640b03039415410b099010803059403002d070b0504420030141032101c801105503001920300e861091650940703030030300343c40024141c0150303559003980340c87d1001000303000d101c15801e850b070a074200d8120042404c89082241300a07240a80030740d1052003551007240c0305020b9400320140d603145c0180c8255455203000c422900c550002c0caa941c2080e41040310840712010780322400701400308103001c1c140312600c000c1e0081079a0300029000f500580200b12080e402202210030b100d9014088810065064002c940e03c6c0e0420380b145030b803600070046100507543c0300009680489040003c40710711401024208100080480421018070100c418044000e8141c1200c01581110101007640c1d0140c001840908403482a0807560505106200c00e44d0a5140c540c2c100d580421a5009809001000380000700c07213015400e4440c5c0d12042000c4074011030082c0080d41085012034031000e100c040d00d000100025624240 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 55725543 1250 55724293 55724353
    0x40c030c0803070c0504050a140a0203070e18070806040e0d02031206091605180a060c0506091605010c020f0a030323070f1e0b011401110c0d14030d02031305 69
    0x134410300491400781d02c55a0002d48104002514002400810351300080c112059100341350b0100800c0b820b2504106400018141100e038071413882c1604160a00b002e1025094600704201200010040e84959101c0010082c030700044450703074142203a009659034000e00e0401040b080960104149042c21165103025a04240969480c840001021a41c0d41c101241500e401c0d0000366143c41c0395103071b1000f0a4050302d42030b0b03114890440c1c541061850700178003034510145540070360b181c03000018104102e4402e5170300911700085000d0090000038500300ca541c06c81c2c3d5020794055400020107811000d00c0001e031110300d07010064201e0840440c02079004101c00601040307989124540020442180c0110300c101708112480490204e4540b802e032440241c018965031059074000d03295941c0c0000c84106424610b800070b12490743c801004c00c158000031b00004044c180340c801102c4540c0c2e0300340162501c54915607c21512440c19907100300c0c0890620070242c41c14000c00b4241e210b0b000c41c1e40300b10b540c411050 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 55726793 1250 55725543 55725563
    0xf0f0609091a0904060f02040308070209070c020108010504090c05040f061502030c0c040c0302120a05070e03010614010507020a0902130501090b120708060a080a050a050c01021501050d060b030303040c030c080307 93
    0x2e0a015005500070000c40d045a039a0341504e040c8449031000d0006140150704154030307003500784140a0070000141c00720040c0711000c0c04590050380e22240303441c151401518046002045071a215030711843e682c2005078800c1c1001d0f02052165020307406981242c0e441f0304803c2e074260599000b40e03100c3c45409142105c0384c00481c00022241030a4000f103034282310030b00c0c00515140c03403011240303481d25054030080d1809840d4000e2011856004050300700b0701c98100c0007004411300c1c060043c001440e08100448c1400400710f5420250344c2c074981d0080090040c0d400a40d910381d100c21340300b80d1294081c0691408aa150480400d01ca11300d00e05a071800c4510310403014084d1940e260648811400420712036012524410200c0c1d00c403818400c029200d4030450003442d10f8861460524281414400d0650441d0700c050f029041100043c1426070450f0000d843c01900c190150500300054000d40182d190544400010b0004000034407a030f1400f180c3c0203030f0482284070f8039003401c1d50b100d02c52000f011b401c0b02a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 55728043 1250 55726793 55726841
    0x6110715090305150403081e1602030f07030801180504030206061201061d0604060e04050a03050307032703080702030405030307080f0909011818021011070f0f060909 73
    0x2440003a480c030000c00d08044a425a599a400d45070204054807141d0800c07800003130008064002d030342180c0080b90b40641481040c8c0000e1740c81082e80f4000d0248888a80c0002d0b0544014002e20840d0a5051008910303035a400f0b25042c05420a902807244480342d101002e600034014003a846654007599141c3d0180600d074035404208108000c0c8200f1900c142d5581300750010f0321141c580d0090141880066822240345040004c010840b134a0307920024444007043c04000002c1c0b00401e2403541203a02d400d28688a072a108000c81c001d24807801e070030245501104420406842e00c8281884081c442d42d40c400c078964458004030703121700039031265542581c8103220703980000d070740075000d44000710590b84030b1410074449400065510a0070391044840103407141041c5034a1426004600d81c1d040705002d0440c000c0300d10b81c08145100010f0440c8000c01442c1008281c543d9000e221507002446403900307402d83c0f00c1d11044030905501c400d01c6101c0c081440d04200003507000b10350180469000f08818103814881c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 55729293 1250 55728043 55728059
    0x60105041401090e070b040f06020c040e121c0501030311060717061302070606062703020a030303020d020903010c080a0c0c08040506030702030c0a0305070605090a0c03060e0102040b030901020c0106061107 90
    0x200000c0032424170700030300d00c010501ea40c61a015000401d0020400c1172818941100a81003806602c800340c003550404031002144840020036140b45040c10448a6030303941c505500e2200c018070364401c00c1100d403c000000042c15845201d8000c03c8524509885194850800035103920348030080340c0c050a40000d00007082c0e4580b80480c1550131607000c402624001c0c0c40d5448004840c40c503000320b40860600a0940b6100103810680e80300329036480b0b00445984d06540000d000d1040c5480300400700741d00003510554100036a0140d84e031030800500240301c42c0c0380690010b0003440040703400d940082d00d44031810f490244140b90000340300f5005050289040c2c1000180301055200500c400c0a5100803c081c0303411036420071550050702e0095403041d071100943e16140e401d86102521140c1d00d07900440c001d80114654a080d0021242e0103032001034412081c52400e07019025662000c105450040108101004103400409000c0740c000c00812215488036015200004e0134078100710558042d20060150b44 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 55730543 1250 55729293 55729301
    0x140c0c01050d090503070c0311060c0606060703090503010905010b04051302060f070302070f0602060f01090b0f010c1412070501050f0c0313030201090b010303020a060c0e030d08040f020a031406010504140109 91
    0xc001c41d008118450f0984a03280b4540c4848021034400d40d07004410001d20000c8080356190314012291149081205c560f0030750b895401820312071241e1800102ca1007018041c1101d0b400400c00a002032140401c01d0820f10f0003010f404440a00450400c00050415020a0750074a10282e0081506080280141c0d0418843c0c01070700089055101c1c07814089006c28502d49044010b10701b5500420040c58100d04100b4480810b9010907142c0d41428001d611655900e410046604420710380414a4000e03410315481013040d50110900600501c41c81e0031072583c1c6c090081191a00400080c0190380383d8000c0d08020880403200c42c00c1d2000d05001003100c400248200c1c1050314041c0c40041035400550701c0350124107401f80c0c81240544e021003800c4080190754068a074000400341032510382e0100c0040882d4485034010100310800002000003000c00144059141c11a60050982440c06480303150144419481c070f580d4015510605000141524140c0034100800f0301d40740d0003034030592804034000050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 55731793 1250 55730543 55730557
    0xc0f090f30050601090b04020403030c021c0c0602250501020a0213200702130501030206040603020705030c0106060905130b060702100314043816120c02030901140c0c0105 75
    0x2140c1e020000d5144082403030038003510140103201414440d450314101008540041d240c40d4007540c0180006c00100340c002240014554050f00c0700c01030201308280365408040e05403030042c0340311082400402c00d5a40000d000301c15450b404009800030701030040c41081c0450611416005a001198040060512146c0c0080d811020000401c40c041031032030000514041c881500e00644010560310309604e00004099681003030a90208140e50440d0041a0544685e01810f01031613000600e00003000b104104403000810448001c00040ea2910710003000000c60340b040c58032400e101c002c14150031001d44104500c0e0303107004201c20f142140070350a2240d04a220b040c1300c0c05055503421040100c0d170550510f107124502c12240009101469100c6540035203507084101d003040b0000b0060550541c03032a08090300200d0f01074540100c040c400f001103612103039402a460000c0d0400c1240d4549a03000406440b0b10b1000340c071401c040022407103140c3d1a500540d04803070601c4d0b2004000c11815402600100f0300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 55733043 1250 55731793 55731839
    0x1050f0a0c021c0c02040501050405040b01030201080705120c09101d01030f0e1b09070921060b06040e01060915050d0e0102130b1c110a08090a060f0c0f090f 69
    0x5884003d11070500800720b1071030b0000850000e00c1c1140440c03900d0b200745070240504840400c42c904090b15a54081201408028180201c00002c034072003d0213102a0b64525504000001a51400880d400c1e8550043c0c0c40c42c0e400799640d12010b60185005604c034400100c1c0241d088544081240011009000e52516109003183d440c000c400728081c091003a0a100035641c0b08a003501706284080c4400031400a00b103030100700380c0c071009002001c1700d0001c3c846120f0540e860101628903a08020000300300010080b0361018002400141d82c00c10782c0101c03812240e541d1240c3d00032135134032004d0001d0301d00c040114a001541c01c200038419040e991380000c0100701114001400c0c2030003405869890070540d004056400c070045012002d01006640c510350300d41e86058280004118081090818000da034048010322110f80c001492001c0108040b0000540100041c00601d1000212400400340d0100d884001409001110507282c007507001c00041310300e60b9001003511450b00480c400c501e0703101840415 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 55734293 1250 55733043 55733053
    0xe0304290d05010e040210020105010b0901080c040b04080604050f060f04080c070f090207110303160f0503070203060c030a14010305030d0c0306030807030819050c09041a030607030b010f0201050f0a0c02 89
    0x9514500761144a001e0000641804c9240c00c042c01086110710710b6540071411a0304020040c040e840c0c03e0029079961a1080c280719206855498400100303000f1600910800400490000307007a6600195040c0143d0084003520000d403960340c400d94403040d0884882200c0e00c40080803c00045086000782940031144080c3e5841d0307525564040c06406690340001c12003a0007060351000c2c0300c0148101d01d5152800c0340210b10781b008514050a00c501c51042c00f40882c6200e001c01020b122050084030560740e401001e5403494074003100306121940064541010303841c9845052800000c1c040c030200c3c184c0340c00000460506030383d40c8001d000b0740420740c405420141c48031000000141d00e0400f500c08103200303403030707a01a616010090100c086110030b4114102401e00040c40450702c41041200c4400909883c081135030118129000c8804401403c4507406128545c10000482d038198085041883c003641c1c1c5110b400644041282a12802d4484410044612012407610240c1c0e5220b0004201e01d40160341c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 55735543 1250 55734293 55734307
    0x20616050904060f08010c02010b0906012105040303060e06100c08130e130317011a07030314130b152b020a0608071e0c030c0c0b04080a060e030429 65
    0x30b002c0d1580740e4403403c1c0301c280c8908244207448080c003507400508190b04c000c00201040400081c80b985000e481d0b18140f0a00c001800701c1c0d00c0010342c00481d05012900c092250f8100351400400900c5a0300c0f540c1e1541c210400810410b00d80712040c4112001c0999404110080580b610700507940218101100480c0b02100001c800010211791413151215030101c540d11130b01410042c00090b2a000c15402d119000001030000d0020400d030700d00d5411420b504c070f503140c241d24513040e401007112546949103000000100a0200f2444040c04103041c855090500581ca45806a03803a5442022916a11107180442c0942031210251502c11000640009804135440c603001b080d814485600f000c00021040c80070012003c1e040041d82950743c0f0034092a164548111100922440b0b038400c00804202c0c10024100a0064030035a04009e0400380c404c6654403540c2d603011a54030781108404480003410400c8900a030640801a0750489010442551001003459219003201802030070b0b030030800400f40110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 55736793 1250 55735543 55735549
    0x1b05060f090304170f06060102010c14180904121103090d15060518040302010e0d1403060301060b0a090602011d0712030c05030d060602100603080a0309020105070501020c0a020a080a030206160509 86
    0x86024005103001074174542e40e803120b006080050081c111415a07040c88203520249600ca80038002d14040200030319181c2c204920f4010030100380700e00f8a0f5220f015034062000740144900350501d0502d0507140e4180100440d03d9084d128021b6911240c0d10500300392001005c1f4249082c82004e1105c2e9103c00103507182c941d40021140c0c4031080c1c12012840d01c1204200c1050303024803520707d0340e00c5c0320300003032508003520a40100140c8c0f440230310149140c2e02002246050724250401c0c03020323003040c88406443d10000b500081550b440313031098800542c2030050005041082d4030030340d1030001008001e481c146092000341c03403000c11510400ca01300010101510041801840a00341c4868040c1c008113059160400c0203240c805420500000c05103030130820030008200904a644a180364100442d40000b2400161a640540c07400a410b039400050040e041003130101d09100000c3c400c84010107070079141c0404d507a0720800c00d40c0040259001c5804207040c1124100340b900c41207094038206107400846004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 55738043 1250 55736793 55736819
    0x30e03030114030601080a05030913090b04030216061107150c140d11010c08070f020309060c010c1b0803010b0d020c100f050a091e0c0b03161b05060f090304 69
    0x4042c010400d0040b0110580c5024060701d401032030000d0007021584215100c890f101e00c03c0c0c20700d05100302680481002071200640001e0012500081d01c1142481d10381006500d500702407241000108c0e0038140410858094101c1c545c0000405005105a508003044040b400404d076281d0003d0000110a10000131054607041e9a80b2020002416a640ca042005040700030204d40107481d9906080c1c1c01d802e020ba001e07940540c041d5141c500391000e000b030311a0587c15032042d91291504405c0c000361418003c901508818040d01d0582e59010301c0113546017030400b07401d0305058002d080c40000c2004101c100c0b0107001409403403810400042ca807240c503446551510b00c03001e00c1c00354813584941000000008030b02ca03583d80700680c82d805100e90022541d444601d40d039500c42c03e0415504020481080c891407841308400350030309e00c05255032030074800d003070190b0072140d41800b0001507411105015500608020380781c8081e40407004041540350284104000703c4014140c02c494402848005900c14070480 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 55739293 1250 55738043 55738049
    0x16090c030e0d0c0201020601301103010c090e060f030628060602010b03121c110c010501170708010c0801050603040201110102030a0213050609060f0307030603060c0e040c020c010e10030e030301 85
    0x124240749100f644000390501005034000401e0641c20445254000e010484401d42400f43d102403644c44140b0385004d240300c11804440c0c503050340c03810901d42003a94200844074180d5811404a034000ea03035030020000b02c0d8200110003601900164081155070794140030082084542c12a2002d0300c10210001508a03a0194001c10060391601280703583d50070b091000008140d025100d66150070b4445082c6001ca0703246046031041541d0729a400c105044140c030540d1490200c000003401556034400e041070301001f501026440500511000140c1514144925110002d4980300c04140744e280804003e0f95402c024801e906200201004164031031013031000354851400e039100181c80711820300081c11000384a0304400e009140c10000002540e4545040d21101551038140f42c0c0d50342d54040f03040740903200660000b0030460801524074200d94100c1c07405007004009031010810b909000200320303030701c1c43c05203815030109001450a242c2030424080b062031542c25410003156540005295500c3c5d684264 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 55740543 1250 55739293 55739297
    0x22a0d030c060b03010501050f0d0203010b060403050319020609070e0915090106090605040b06040306020703140706020703080a090f12110303090a021801060905040207060b0301020703080a050916090c030e0d 91
    0x2900c24040050b24070900c00c0520068000300015810070f070100380590241e281883c0314400740043c0340119503094004640340d079006815140c07229640e161080d030340d4001c04225604190010080f2108510000ba002d20482d0200c0013800d9041c5800300300d10503244007030079800980c0141000082d0b0302240e02c1850f40a0120a40001912482c0083c044221109a044544241c0c200780d07290031166030b040e05031003c0c0da4000100698642c000c1c0b40c141c0b048603a10701340746082840803540303400b400100d9015200c3c450181d19034082d9503a604491808603411180000d1000c86180401404520200310344401a541820104810320203a25450310710303001103454045e50f130700060014046042c0840903003040788150000f2400f6505016001d80007000500441d0300071035000c20800140324958000e090000d10144c002c40d550b4803541801003403c1c2d02203c459054900304000300b0007a60002440e0031508034491205d01c16542000a00c1001d014030710080c0d42015143c00e44001711807800d0040740c03245a030315 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 55741793 1250 55740543 55740557
    0x123090616030f1e020604201c0b070c02130507050903070306051005010201050408031603020409020a0c020103060f12030c0606171c020d0504051c120504030b0f0601022a0d03 77
    0x70354010583d0b10380344d514403c00b41d00255003c4c00c0079000a030480d002603001500c0d054240707800400c0e425640750b809440d80d10855000401c4840304088017900c4010340940030b0100241d54840042d2020400755034000d40116200c034211054111a501041e0000054034080745460f130201c000918092090b0010b075605c0b80e50f5401d00c1506840200d20380001e04e401c3c00280001e14090700c1c0c8401600009141107401030030040129240380c400c1d81150041d03c42e0040031034580103d0f110003014030071164400c034003181c600784020540511501c1041d0803540507081358a0031020395130b402c641800030004203c1700d0300c0d03d402011130f1082101d1341802e40d003e0818010044001612003025801581610780015908403800d2049156441011681602c000381c498007a224528400d6030404891110041c10360040c042120041c184c1c06002801140e00400c1c0d0444e42c1d07120710b0354102a506094440502613807201c0ca200350b1030000021101a12604504510040800c0001044841000f160110006101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 55743043 1250 55741793 55741817
    0x61306080d17041e0809060f03220503030a09020f0909010c021603050712081b060601110102090a140303131e0806040b010504050a0605040e0f0705012309061603 71
    0x110600000c0a102044060181070403e40c4540800b032203a0900e00c14030000e500e100b4014401400120790301000c011f45030603500c0c0486880e61407542c0060343c5420342000d80d8640c104641e043e00801c0b50380240c01c400558556112619100c00403d01100c04a800441b00004510f10b075481407001032081030020004035a0019903200241004680a080146903103844010b002140740060800182c4902d000420305d4228182007194540c090300d6020005603146c00002180000e001c10058001e02d0300f80c07105180682c050303585900340e00408190907003006000000308508064261814070140000d030030383e451b0403c4081000d8a05460f0b405c40a40c004100034200800e420700062000100400e40c040c05ca5400d003591009040c10301813150314402c41c0c0fa01c000c201c0b0082194844802460028400c1000c18520f0101c143c40300305060000c0340d00e00401800140c0b55000c0c0980c204040c03103880c1e86803034141031071041c2030182c1c100c8011550003070300034489440d80581f5100380c41c0a00340251500441995 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 55744293 1250 55743043 55743047
    0x30d140105010804050712210207060e0a08030909070908060903090a090203010602100902010324050423040807050c040f0e1606020a06020c16030311060c030601120203061306080d 79
    0x8040e800700303041002d14402c1001040340801c05800361800c5200000300106e0130300b40134a00c00e5001a210400640b4044501c1c02160002000e00171904291140c1d8140c8071180100400c400c41d510580a041d0070400c407054551401d2040d083c0c1c0100b040c10702c0c92441c1d80303a4480b203240c050101c0f90081554000240c03803c0c1c1c2e18024280000a01c0e20990651542d810508001d442e075400c0300424020607161a5034408580c080e80088032540c044003c6003180c84c1001ca52100c0d0003046201c0d5602541c0340001c1c0706078066000c501102e403051040c5020045455036501c090f840e60018609881b90b01403503d20121564450042051b07060360411f002c00c040845801c00d82c140303448240785d2400c440d1049000c100c6030342c0105d12024442d4200c000162a88c41c1e482c1e005003001c25880307509091039800407002c4201341d00003903d580d83d4110307882159116581c4401120080c07006030784080c042126000d0481c2415965001150b1001000c3c00030051802e1010320f8030213880b0b41e40c118110300d070004070b81189025 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 55745543 1250 55744293 55744331
    0x2060f0a0b0a05010807030e1002040e0a060302030c060a0309060204180b0301090201210603060603050604030906030c080f0a020d090809040e0c06180a0b120a0b0306040b070e0d05030d 81
    0x10811450070070901c030920001800d0a4018407a65041c40541c80000c1c0f112402580f14010302200718098410030703582048840e00079400f601440c90201080f00108401c25000d00c00d00040e40d50260041483c45010410030602c0e400580c0307260101030b00e440ca00d2001075554000b520060000d0004404000e00d10036140084e110f140c0c0000d400b07607160a0303103800581c1e846030324071040d08010002010f078007520010001c0942a184c0002e450755042c03d40000c1045000500144164026501c0402050f1100021410340c1c21003452100051081d03000701d90030903000101d86401040080b401881e042091030008191807a8200680b00c140b004101e40c115410540540e6411901990240c40c1c2001d00340b000a40a005072010700344e41c680c6a0307130184c4064444200c50b60240940c080029110300704030380030040419003210461551420580642010308001a4035401544d000301c2c04c001642d100130003102c2a50707074040d41c10703880b469806181000c0b410920045c18048040600400e0354001c43c0c0c0c9071000c074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 55746793 1250 55745543 55745551
    0x2007081507080f0601050901050705070e040c0b040608010513180b0105090108070f15021f020c0c0f0108070c050106120602071106090d060506040f02030112020f01030513020111150702060f 83
    0x441007402c208000c5503a0048101d52000e400d00344151541035140041740d05003e00d10000b0103921402c00003081803100320244900c41c510441d000300480307131212040d2030503004a2080601280303d800c014003551600c03010702c0c0882c1000001c0090340b00182400440203020300541035402c1c1d40010014042030a012201ca8094807000e8028803550785852440b403e2140c080c070400c5038032803030f1008601c0128404d10071201614007031405000203c44400d00000258440e0343c0301c160070310410403c1c1c9034501f044695003185035016145c001c0b040e5504401501ca1915850b422103080d540c0d0ba50118061640d401d44400e2940500001078554401d441e00194000080c0380e401d2045009001000305952aa2032210b41c042e40090007141d15103800f000f15002c1c101680340040018008000403c1400742c10a014408c503000701d0310203983e204180019012104107a512900402c50303d501400954000d070120f07003048604404441d5004c642c0d810741c0640710419110800180c04c5001800b00e039016846000f904 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 55748043 1250 55746793 55746797
    0x504021f0c0f0c080d0f0e100906080907030605131104060503030301031704050301111801180b07020607080a090e090d050301031e02040606052104050d2007081507 72
    0x1411500362000752244000e00340040ca05806036846800f04442c031003000c4000c04000085031007000d0420005403015031000c00c0f030320001c0c410500c0500c1c1ca240820200c18002c10a46545400d1070a02d64125080e1000074000c48141c4035940d0000005042849018840c0d1580c074152908082285080a01180e14400040c80b4030b0070680140030750358000c0100c070704580c0d10200303c203482d000d1903411140c1c90285921044d07040d440c00b90b100e00b40c0f01e4004010444900e140f220124051031041c0156030b030b60406406030220600c103420501040c65050001c112460005144034101525641c55407600d40c000c040800000703c000b10b0800c40c00848800c2e0076044121040036180c01d4040c804020b00c0c0307000c144000f81c601c4403000404c0d80e41c4101c40074424101c41e00030380b090100f26160b01c8068038542c004203585001c480211000e03151030110340c20070750082d9803180c05041c407580059402c41d1140829032211085a0303c65401d04030102e42000741d81c005003805000f5010303402d89005540340200f0000d0003401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 55749293 1250 55748043 55748089
    0x9160311010908011b0309020a03050d0905040617120a030207020415090e030705120d0603050303130c090c02070b030c04180e0d080f070c050c061201081209060f16060f050402 77
    0x2429020344054145d4800c0700d803a000440400c14000920400c4e05a80058024001d0030101130405920286035016102c06032410300000d680c9510020f9010340903043c440311030300701440f41401131103d9001000030704024038001d4201500c1d0b80014040310728110440303603100300b01710040250000500801d045092180095070406400b6101c2d41d444808050410728080c0d000505a05106059030100f4059600a002c40380c0700d00d88890460420710350003100b50350130034200c100006c0c5005140280701072070066501034840c061902c0704000c02d5420203003080c040c0110038880800e40300e90410306091031100c4000042190030040402a040000400c0341004000c00001004011001030003004d400c00d16a19004281d0f035654100203041126910032207074070440009141034000c2c440a25541600c03007040036900300705010480303c4c0b2144100000603030031080511800102c0480600581400032040c8e041e6030105420b55151411222035080d40084070b540e03202804107504041d44850035030540050401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 55750543 1250 55749293 55749311
    0xd021513150507230106120b0601022e02032703130503030306010912030c020330030103030903140307050d0c0303050601030614040f02090a030501060e0c070305040e0916031101090801 81
    0xc0902da04051813450700d07400d6a0700ba0004070400d5001030003c00d17495003080c0805a40d8940200780309000c0c1c1e0b245006102d1000c403007201081915051641280210707003048480c10b01030685000c0d4100070312180740074400c0a0060b03040e1a0994a02c003020740f25101466482c3e640380140e01441d486d42d00807601950041c400c014042e40c01c10101000e03202d400c201501c0b45a020b207800ca0b521200158025014028400c4481d10120410034000c0c0c41800c07907058140e20070f8803100414050200740b00c0900050501c49042011940c1c04401e00596030404044e20300c0c0c1031040d160303640780c800c14001c4c880015400c0c00c0c0a4041c580c0c9132080c640c01000074078085c411180340c980416050780c00d55618030b105541d5144a420001c1d82581180e42d9240090724550b05c0d6962410641c2c000c002074802d00718910034950001b1589100130f4116500b032a8540c03074040c1441d0a00c00715620040f0010510141c511469251aa43d49940c5481c0c03001144035462503003940e00d43c0c0c1d00051100807144e00c50310380c5a0404070a2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 55751793 1250 55750543 55750553
    0xf01060203030a0b0d0c0f140603090606121213090b0102010207050c010e06120a020903060601140409090c05030109140c040b06030103060b0f0612011a180d021513150507 75
    0x507074010030f030400086168541c1600203820f1703a5548400802610710800300144151040c4010011102480c038401c0340b01d00ba01c820f0003020321084840d83c800ea00954000307101850700d811208400791925044a440703034080042c4900f164031a02c2070100c000c0300e102d0b00704a660041d0103103c40d6103400f0b20081d405d000c1c40340e039440c1e5107150014005043c818483c1462000d80c07224401ea4240608480748803809090080c0306000a500c240d12240c041d010703020000b03103994003460780c800b0305010302c010301440c0618143c0f02000618920004031140c5ea018040010309560901030707007500501030640380300144813074581c4900c1d11280076200d902840c10601030001666600043d01c0c1126000303800030554400f01e10009188001180f083c540c0221302242c00480d5410266442c0c0c140e520171368022503081c1074030140c0d12140c02030204254400c00c03d0503100312181003840080000c10310281c20b4465209840e4440ca40540252000d04c1119101003020024140e0000d03103101000c1581c2012840d0071b08039114 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 55753043 1250 55751793 55751797
    0x4020418030f03050901020d0609020705100501030804030f03030b12030d05012103030e1009050f190c061d0a0801140612120708090613050f040b0901050d0c05040504050708060f01060203 82
    0x182400f410b0b5102c001544081d070a4046480d80030602c0820040b00c0e4450310310400a42002800399001d22803000f040080d41b00a102c5c41c0d040c2c0b500441ea160600c0c6c0b541d525001c105200c410100d0408d600c039012410a40c452a484a034501c8010300034507281d80150b00500210390050b8081c4c0075100c41d005d40340c13901d681c00304030380414150185804542540180320759407501c5502d00345000c5040ca4480184103000c008140b00c20b52080d10401e840c00307011170100e161542c03040c01102034401c10228008201190165078500503541480e100e9103200034121001a0b03121826a2107402c0720f0351101d10302c9901850300707881c441d8880300807103030404010313010070b1160343e542030040b00904c028400140c0c0c003040c03103202000c0c1c7e11448001001c965603584290449215025580f080710b004860000d60340c200c0d0b10303040c041c0007104603010b010511140e18010030481c1c1d01e156040c0c1038892540400b00841c04d512180103a910581c080e4008210b00f82c58a0341300c91030440c0060260b2546611040103201c07469001c41 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 55754293 1250 55753043 55753067
    0x605091b010513051008070f03050103080d0203040201030f05010905070f1b2a060e0a081b0906060705010207060204051008040506040f140f0607020f0c030703140a080d02030402041803 81
    0x60702d5615498000303010110010107421841d401031141c1c41e44d10015a010350034a11500c42e41c0e07900c1c0405028000f058007552800c0c000102a074106026603d0820310540c060b561103030051401003582d40c1e0300c8040070200c0c0c0d02038200e5440244c1750070400020640114040030080321614110402841080d1101c00304c036080306000300f158480020341d00e0b0740c0e10642c10054011340891905901e0341d58520001d44901c6c3d400751840d000d010401350018240714003040c81c10f907842311003107001c90101c03c01c0204282002c0003004075500800034802140030540920180100501c0b8500c01030350b0f00d0034a01000140d08040e1030f140d040041030020440003410100364180c000d41c1c080350203c4040083d1070500c14118941d02009580c3c4542c2c41e5500700c501000941c80d0082245409030303001070420740d6000781c65039000f4100c42d40503840300d07408000041d0300c0040070b4807603580401511039403585a580c20440b5844101074000440d004018030041d45010310840034061010248064000f01558011301002c505074 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 55755399 1106 55754293 55754297
    0x809070501050c100b06041802030402040605090c040b0a0c0206030f0709050303030108030a0c0c05040216061a0901050904110909070806010905070507080f0f0706090605091b01 78
    0x1a08030b0740b424072030b18090030f40c00501c5004138001e0b15a13403840c180c00020400c400103811007c608680307600c040141c1d0160b60390806004100590310560400ca03c90103415040c0b204110340c0310100c90482e401d00c1c2c1000c0d101e481209040e43c02c034041c600c01035000540001007058078101c4a01c0c443c403503402d54840c0c400e425214011305690b80024020032505a008000d012801800b1380d40034549144980502e61440b5124004a410f0381c01500026083c001d0140901302080001d0040ea4808000c10140486d00000328001824062062040600030365114004c50140310100e100840c00c0c11015040710321500301542800d43e00e212911968055004610010869017414000d05006440a50301d15007071203142e84500903598004001c0003a041f03410860f200981409030f026007030041c000c0d2000034200c103240c10001d0039608018100000c94011f00b1014600e500003481c02c415843c028 = true := by decide +kernel

theorem cover : BRFrame.Cov 55575543 55755399 := by
  have h0 := BRFrame.cov_init 55575543
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55575543 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 55575543 ≤ n) (h2 : n < 55755399) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
